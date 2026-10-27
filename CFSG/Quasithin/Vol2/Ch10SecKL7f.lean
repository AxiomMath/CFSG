module

public import CFSG.Quasithin.Vol2.Ch10SecKL7e

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KL7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {W : Type} [CommGroup W]

theorem ext_act {g g' : SL32} (h : ∀ y, act g y = act g' y) : g = g' := by
  have := eq_one_of_act (g'⁻¹ * g) fun y => by rw [act_mul, h, act_inv_act]
  exact (inv_mul_eq_one.1 this).symm

namespace Coord

variable {L : Subgroup (MulAut W)} {U : Subgroup W} (c : Coord L U)

include c in
theorem exists_inner {x : MulAut W} (hxL : L.map (MulAut.conj x).toMonoidHom = L)
    (hxU : ∀ u ∈ U, x u ∈ U) : ∃ l ∈ L, ∀ y ∈ L, l⁻¹ * x * y = y * (l⁻¹ * x) := by
  have hmem : ∀ γ : SL32, x * ((c.π γ : ↥L) : MulAut W) * x⁻¹ ∈ L := fun γ =>
    (Subgroup.ext_iff.1 hxL _).1 ⟨_, (c.π γ).2, rfl⟩
  let α : SL32 → SL32 := fun γ => c.π.symm ⟨_, hmem γ⟩
  have hα : ∀ γ, ((c.π (α γ) : ↥L) : MulAut W) = x * ((c.π γ : ↥L) : MulAut W) * x⁻¹ :=
    fun γ => by simp [α]
  let xU : ↥U →* ↥U :=
    { toFun := fun u => ⟨x (u : W), hxU u u.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  let F : M3 →* (Fin 4 → M3) := c.Ψ.symm.toMonoidHom.comp
    (xU.comp (c.Ψ.toMonoidHom.comp (MonoidHom.mulSingle (fun _ : Fin 4 => M3) 0)))
  have hΨF : ∀ z, (c.Ψ (F z) : W) = x (c.Ψ (Pi.mulSingle 0 z) : W) := fun z => by
    show (c.Ψ (c.Ψ.symm (xU (c.Ψ (Pi.mulSingle 0 z)))) : W) = _
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hF : ∀ γ y, F (act γ y) = actN 4 (α γ) (F y) := by
    intro γ y
    apply c.Ψ.injective
    apply Subtype.ext
    rw [← c.equivar, hΨF, hΨF, ← actN_mulSingle, ← c.equivar, hα]
    simp [MulAut.mul_apply]
  set y₀ : M3 := Multiplicative.ofAdd (Pi.single 0 1) with hy₀
  have hy₀1 : y₀ ≠ 1 := by
    intro h0
    have := congrFun (congrArg Multiplicative.toAdd h0) 0
    simp [hy₀] at this
  have hFy₀ : F y₀ ≠ 1 := by
    intro h0
    have h1 : (c.Ψ (F y₀) : W) = 1 := by rw [h0, map_one]; rfl
    rw [hΨF, map_eq_one_iff _ x.injective] at h1
    have h2 : c.Ψ (Pi.mulSingle 0 y₀) = 1 := Subtype.ext h1
    rw [map_eq_one_iff _ c.Ψ.injective, Pi.mulSingle_eq_one_iff] at h2
    exact hy₀1 h2
  obtain ⟨k, hk⟩ : ∃ k, F y₀ k ≠ 1 := by
    by_contra hall
    exact hFy₀ (funext fun j => by_contra fun hj => hall ⟨j, hj⟩)
  let f : M3 →* M3 := (Pi.evalMonoidHom (fun _ : Fin 4 => M3) k).comp F
  have hf : ∀ γ y, f (act γ y) = act (α γ) (f y) := fun γ y => by
    show F (act γ y) k = _
    rw [hF, actN_apply]
    rfl
  have hker : f.ker = ⊥ := by
    rcases invariant_eq_bot_or_top f.ker (fun γ u hu => by
        rw [MonoidHom.mem_ker] at hu ⊢
        rw [hf, hu, map_one]) with h0 | h0
    · exact h0
    · exact absurd (f.mem_ker.1 (h0 ▸ Subgroup.mem_top y₀)) hk
  have hfi : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 hker
  let θ : (Fin 3 → ZMod 2) →+ (Fin 3 → ZMod 2) :=
    { toFun := fun v => Multiplicative.toAdd (f (Multiplicative.ofAdd v))
      map_zero' := by simp
      map_add' := fun a b => by simp [ofAdd_add] }
  have hθs : ∀ (a : ZMod 2) (w : Fin 3 → ZMod 2), θ (a • w) = a • θ w := by
    intro a w
    fin_cases a
    · have h0 : ∀ u : Fin 3 → ZMod 2, (fun i => (0 : ZMod 2) * u i) = 0 :=
        fun u => funext fun i => zero_mul _
      show θ (fun i => 0 * w i) = fun i => 0 * θ w i
      rw [h0, h0, map_zero]
    · have h1 : ∀ u : Fin 3 → ZMod 2, (fun i => (1 : ZMod 2) * u i) = u :=
        fun u => funext fun i => one_mul _
      show θ (fun i => 1 * w i) = fun i => 1 * θ w i
      rw [h1, h1]
  set A : Matrix (Fin 3) (Fin 3) (ZMod 2) := Matrix.of fun i j => θ (Pi.single j 1) i with hAdef
  have hA : ∀ v, A *ᵥ v = θ v := fun v => by
    conv_rhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    ext i
    simp only [Matrix.mulVec, dotProduct, hAdef, Matrix.of_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (Pi.single j (v j) : Fin 3 → ZMod 2) = v j • Pi.single j 1 by
      rw [← Pi.single_smul', smul_eq_mul, mul_one], hθs, Pi.smul_apply, smul_eq_mul, mul_comm]
  have hdet : A.det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hAv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    rw [hA] at hAv
    have h1 : f (Multiplicative.ofAdd v) = 1 := by
      rw [← ofAdd_toAdd (f _)]
      exact congrArg Multiplicative.ofAdd hAv
    exact hv (by simpa using hfi (h1.trans (map_one f).symm))
  set Θ : SL32 := mkSL A hdet with hΘdef
  have hΘ : ∀ y, act Θ y = f y := fun y => by
    rw [act_apply, hΘdef, mat_mkSL, hA]
    rfl
  have hrel : ∀ γ, α γ = Θ * γ * Θ⁻¹ := fun γ => by
    have : Θ * γ = α γ * Θ := ext_act fun y => by
      rw [act_mul, act_mul, hΘ, hΘ, hf]
    rw [this, mul_inv_cancel_right]
  refine ⟨(c.π Θ : MulAut W), (c.π Θ).2, fun y hy => ?_⟩
  obtain ⟨γ, hγ⟩ := c.π.surjective ⟨y, hy⟩
  rw [← c.coe_π_of_eq hγ]
  have h1 : ((c.π (α γ) : ↥L) : MulAut W) =
      (c.π Θ : MulAut W) * (c.π γ : MulAut W) * (c.π Θ : MulAut W)⁻¹ := by
    rw [hrel, map_mul, map_mul, map_inv]
    rfl
  have h2 : x * (c.π γ : MulAut W) = (c.π (α γ) : MulAut W) * x := by
    rw [hα]
    group
  calc (c.π Θ : MulAut W)⁻¹ * x * (c.π γ : MulAut W)
      = (c.π Θ : MulAut W)⁻¹ * (x * (c.π γ : MulAut W)) := by group
    _ = (c.π Θ : MulAut W)⁻¹ * ((c.π (α γ) : MulAut W) * x) := by rw [h2]
    _ = (c.π γ : MulAut W) * ((c.π Θ : MulAut W)⁻¹ * x) := by rw [h1]; group

end Coord

namespace Hyp

variable {Mb L₁ L₂ : Subgroup (MulAut W)} {W₁ W₂ : Subgroup W} {τ : MulAut W}

theorem mem_C_iff {c : MulAut W} :
    c ∈ Mb ⊓ Subgroup.centralizer ((L₁ ⊔ L₂ : Subgroup (MulAut W)) : Set (MulAut W)) ↔
      c ∈ Mb ∧ (∀ a ∈ L₁, a * c = c * a) ∧ ∀ b ∈ L₂, b * c = c * b := by
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hc, hcc⟩
    exact ⟨hc, fun a ha => hcc a (Subgroup.mem_sup_left ha),
      fun b hb => hcc b (Subgroup.mem_sup_right hb)⟩
  · rintro ⟨hc, h1, h2⟩
    refine ⟨hc, fun g hg => ?_⟩
    have hle : L₁ ⊔ L₂ ≤ Subgroup.centralizer {c} :=
      sup_le (fun a ha => Subgroup.mem_centralizer_singleton_iff.2 (h1 a ha))
        (fun b hb => Subgroup.mem_centralizer_singleton_iff.2 (h2 b hb))
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

variable (h : Hyp Mb L₁ L₂ W₁ W₂ τ)
include h

theorem exists_decomp {x : MulAut W} (hx : x ∈ Mb)
    (h1 : L₁.map (MulAut.conj x).toMonoidHom = L₁) :
    ∃ a ∈ L₁, ∃ b ∈ L₂, ∃ c ∈ Mb ⊓ Subgroup.centralizer
      ((L₁ ⊔ L₂ : Subgroup (MulAut W)) : Set (MulAut W)), x = a * b * c := by
  obtain ⟨c₁⟩ := h.coord
  obtain ⟨a, ha, hax⟩ := c₁.exists_inner h1 fun u hu => h.map_mem_W₁ hx h1 hu
  have hx' : a⁻¹ * x ∈ Mb := mul_mem (Mb.inv_mem (h.le₁ ha)) hx
  have h1' : L₁.map (MulAut.conj (a⁻¹ * x)).toMonoidHom = L₁ := by
    rw [← mem_normalizer_iff_map] at h1 ⊢
    exact mul_mem ((Subgroup.normalizer _).inv_mem (Subgroup.le_normalizer ha)) h1
  have h2' := h.map_conj_L₂_of hx' h1'
  obtain ⟨c₂⟩ := h.swap.coord
  obtain ⟨b, hb, hbx⟩ := c₂.exists_inner h2' fun u hu => h.map_mem_W₂ hx' h1' hu
  refine ⟨a, ha, b, hb, b⁻¹ * (a⁻¹ * x), mem_C_iff.2 ⟨mul_mem (Mb.inv_mem (h.le₂ hb)) hx',
    fun g hg => ?_, fun g hg => (hbx g hg).symm⟩, by group⟩
  have e2 : g * b⁻¹ = b⁻¹ * g := h.comm' hg (L₂.inv_mem hb)
  calc g * (b⁻¹ * (a⁻¹ * x)) = b⁻¹ * (g * (a⁻¹ * x)) := by rw [← mul_assoc, e2, mul_assoc]
    _ = b⁻¹ * (a⁻¹ * x * g) := by rw [hax g hg]
    _ = b⁻¹ * (a⁻¹ * x) * g := by group

theorem decomp_eq_one {a b c : MulAut W} (ha : a ∈ L₁) (hb : b ∈ L₂)
    (hc : c ∈ Mb ⊓ Subgroup.centralizer ((L₁ ⊔ L₂ : Subgroup (MulAut W)) : Set (MulAut W)))
    (h1 : a * b * c = 1) : a = 1 ∧ b = 1 ∧ c = 1 := by
  obtain ⟨c₁⟩ := h.coord
  obtain ⟨c₂⟩ := h.swap.coord
  obtain ⟨-, hc1, hc2⟩ := mem_C_iff.1 hc
  have ha1 : a = 1 := c₁.eq_one_of_central ha fun l hl => by
    have hab : a = (b * c)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← mul_assoc]; exact h1)
    rw [hab]
    have hlbc : l * (b * c) = b * c * l := by
      calc l * (b * c) = l * b * c := by group
        _ = b * l * c := by rw [h.comm' hl hb]
        _ = b * (l * c) := by group
        _ = b * (c * l) := by rw [hc1 l hl]
        _ = b * c * l := by group
    rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hlbc, mul_assoc, mul_inv_cancel, mul_one]
  rw [ha1, one_mul] at h1
  have hb1 : b = 1 := c₂.eq_one_of_central hb fun l hl => by
    have hbc : b = c⁻¹ := eq_inv_of_mul_eq_one_left h1
    rw [hbc, inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hc2 l hl, mul_assoc, mul_inv_cancel, mul_one]
  rw [hb1, one_mul] at h1
  exact ⟨ha1, hb1, h1⟩

theorem decomp_pow {a b c : MulAut W} (ha : a ∈ L₁) (hb : b ∈ L₂)
    (hc : c ∈ Mb ⊓ Subgroup.centralizer ((L₁ ⊔ L₂ : Subgroup (MulAut W)) : Set (MulAut W)))
    (n : ℕ) : (a * b * c) ^ n = a ^ n * b ^ n * c ^ n := by
  obtain ⟨-, hc1, hc2⟩ := mem_C_iff.1 hc
  have hab : Commute a b := h.comm' ha hb
  have habc : Commute (a * b) c := Commute.mul_left (hc1 a ha) (hc2 b hb)
  rw [habc.mul_pow, hab.mul_pow]

theorem map_conj_sq {x : MulAut W} (hx : x ∈ Mb) :
    L₁.map (MulAut.conj (x * x)).toMonoidHom = L₁ := by
  have hmap : ∀ L : Subgroup (MulAut W), L.map (MulAut.conj (x * x)).toMonoidHom =
      (L.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x).toMonoidHom := fun L => by
    rw [Subgroup.map_map]
    congr 1
  rw [hmap]
  rcases h.map_conj_eq hx with h1 | h1
  · rw [h1, h1]
  · rw [h1, h.map_conj_L₂_of' hx h1]

theorem map_conj_of_odd {x : MulAut W} (hx : x ∈ Mb) (hodd : Odd (orderOf x)) :
    L₁.map (MulAut.conj x).toMonoidHom = L₁ := by
  have hsq : x * x ∈ Subgroup.normalizer (L₁ : Set (MulAut W)) :=
    mem_normalizer_iff_map.2 (h.map_conj_sq hx)
  obtain ⟨k, hk⟩ := hodd
  have hxk : x = (x * x) ^ (k + 1) := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = orderOf x + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [← mem_normalizer_iff_map, hxk]
  exact pow_mem hsq _

end Hyp

end CFSG.Quasithin.Vol2.Ch10.SecB.KL7
