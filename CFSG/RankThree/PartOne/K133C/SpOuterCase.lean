module

public import CFSG.RankThree.PartOne.K133C.SpModel
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartOne.K133C.Transport

public section

namespace CFSG.RankThree.PartOne.K133C

open Matrix CFSG CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartOne.K133
  CFSG.RankThree.PartOne.N143X

set_option linter.unusedSectionVars false

variable {r : ℕ} {K : Type} [Field K] [CharP K 2]

@[expose] def trvSp (w : Fin r ⊕ Fin r → K) (a : K) : StatedSp r K :=
  ⟨trvGL (formJ r K) formJ_alt w a,
    mem_statedSp_iff_isoGrp.2 (trvGL_mem_isoGrp _ formJ_alt formJ_transpose_two w a)⟩

theorem trvSp_inj {w : Fin r ⊕ Fin r → K} (hw : w ≠ 0) {a b : K} (h : trvSp w a = trvSp w b) :
    a = b :=
  trvGL_inj (formJ r K) formJ_alt formJ_nondeg hw (congrArg Subtype.val h)

theorem fieldSp_trvSp {w : Fin r ⊕ Fin r → K} {τ : K ≃+* K} (hτ : vmap τ w = w) (a : K) :
    fieldSp r K τ (trvSp w a) = trvSp w (τ a) := by
  apply Subtype.ext
  apply Units.ext
  show (((trvSp w a : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map τ =
    trvM (formJ r K) w (τ a)
  have h1 : (((trvSp w a : StatedSp r K) : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) =
      trvM (formJ r K) w a := rfl
  rw [h1, trvM_map _ τ (formJ_map τ) w a, hτ]

@[expose] def trvSubT (w : Fin r ⊕ Fin r → K) : Subgroup (StatedProj (StatedSp r K)) :=
  ((trvSub (formJ r K) formJ_alt w).comap (StatedSp r K).subtype).map (proj r K)

theorem mem_trvSubT {w : Fin r ⊕ Fin r → K} {s : StatedProj (StatedSp r K)} :
    s ∈ trvSubT w ↔ ∃ a : K, proj r K (trvSp w a) = s := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨a, ha⟩ := (mem_trvSub (formJ r K) formJ_alt).1 hg
    exact ⟨a, by rw [show trvSp w a = g from Subtype.ext ha]⟩
  · rintro ⟨a, rfl⟩
    exact ⟨trvSp w a, trvGL_mem_trvSub _ formJ_alt w a, rfl⟩

theorem isPGroup_trvSubT (w : Fin r ⊕ Fin r → K) : IsPGroup 2 (trvSubT w) := by
  refine IsPGroup.map (H := (trvSub (formJ r K) formJ_alt w).comap (StatedSp r K).subtype) ?_ (proj r K)
  intro g
  have h2 : ((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) * ((g : StatedSp r K) : GL (Fin r ⊕ Fin r) K) = 1 :=
    trvSub_sq _ formJ_alt g.2
  refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
  rw [pow_two]
  exact h2

theorem fieldAut_mem_trvSubT {w : Fin r ⊕ Fin r → K} {τ : K ≃+* K} (hτ : vmap τ w = w)
    {s : StatedProj (StatedSp r K)} (hs : s ∈ trvSubT w) : fieldAut r K τ s ∈ trvSubT w := by
  obtain ⟨a, rfl⟩ := mem_trvSubT.1 hs
  refine mem_trvSubT.2 ⟨τ a, ?_⟩
  rw [fieldAut_proj, fieldSp_trvSp hτ]

theorem centralizes_trvSubT {w : Fin r ⊕ Fin r → K} {g₀ : StatedSp r K}
    (hg₀ : ((g₀ : GL (Fin r ⊕ Fin r) K) : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ w = w)
    {s : StatedProj (StatedSp r K)} (hs : s ∈ trvSubT w) :
    proj r K g₀ * s * (proj r K g₀)⁻¹ = s := by
  obtain ⟨a, rfl⟩ := mem_trvSubT.1 hs
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  have := conj_trvGL (formJ r K) formJ_alt (h := (g₀ : GL (Fin r ⊕ Fin r) K))
    (mem_statedSp_iff_isoGrp.1 g₀.2) w a
  rw [hg₀] at this
  exact this

theorem goodAction_sp_outer [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : 1 ≤ r)
    (hinj : Function.Injective (proj r K))
    (hZ : Subgroup.center (StatedProj (StatedSp r K)) = ⊥)
    {Ē : Subgroup (MulAut (StatedProj (StatedSp r K)))} (hE : IsElementaryAbelian p Ē)
    {σ : K ≃+* K} (hσ : orderOf σ = p) (hf : fieldAut r K σ ∈ Ē)
    (hfin : fieldAut r K σ ∉ inner (StatedProj (StatedSp r K)))
    {P : Subgroup (MulAut (StatedProj (StatedSp r K)))} (hPĒ : P ≤ Ē)
    (hPin : P ≤ inner (StatedProj (StatedSp r K))) (hPc : Nat.card P = p ^ 2) :
    GoodAction p (StatedProj (StatedSp r K)) Ē := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, hr⟩⟩
  let Inn : Subgroup (MulAut (StatedProj (StatedSp r K))) := inner (StatedProj (StatedSp r K))
  set f := fieldAut r K σ with hfdef
  have hPe : IsElementaryAbelian p P := CFSG.IsElementaryAbelian.of_le hE hPĒ
  obtain ⟨A, hAe, hAc, hPA⟩ := exists_pullback_inner hZ hPe hPin
  have hpowE : ∀ y ∈ Ē, y ^ p = 1 := fun y hy => by
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p Ē) ⟨y, hy⟩
    simpa using congrArg Subtype.val this
  have hfix : ∀ t ∈ A, f t = t := by
    intro t ht
    have hct : MulAut.conj t ∈ P := by rw [hPA]; exact Subgroup.mem_map_of_mem _ ht
    have hcomm : f * MulAut.conj t = MulAut.conj t * f :=
      congrArg Subtype.val (hE.is_comm.comm ⟨f, hf⟩ ⟨MulAut.conj t, hPĒ hct⟩)
    have h1 : MulAut.conj (f t) = MulAut.conj t := by
      rw [conj_map_aut, hcomm, mul_inv_cancel_right]
    exact conj_injective_of_center_bot hZ h1
  let ψ : StatedSp r K ≃* StatedProj (StatedSp r K) :=
    MulEquiv.ofBijective (proj r K) ⟨hinj, proj_surjective⟩
  let ι₁ : StatedProj (StatedSp r K) →* GL (Fin r ⊕ Fin r) K :=
    (StatedSp r K).subtype.comp ψ.symm.toMonoidHom
  have hι₁ : Function.Injective ι₁ := (StatedSp r K).subtype_injective.comp ψ.symm.injective
  set AG : Subgroup (GL (Fin r ⊕ Fin r) K) := A.map ι₁ with hAG
  have hAGc : Nat.card AG = p ^ 2 := by
    rw [hAG, Subgroup.card_map_of_injective hι₁, hAc, hPc]
  have hAGfin : Finite AG :=
    Nat.finite_of_card_ne_zero (by rw [hAGc]; exact pow_ne_zero 2 hp.ne_zero)
  have hAGe : IsElementaryAbelian p AG :=
    isElementaryAbelian_of_equiv (A.equivMapOfInjective ι₁ hι₁) hAe
  have hpK : (p : K) ≠ 0 := by
    intro h
    have h2 : (2 : ℕ) ∣ p := (CharP.cast_eq_zero_iff K 2 p).1 h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2).symm
  have htop : (⊤ : Submodule K ((Fin r ⊕ Fin r) → K)) ≠ ⊥ := by
    obtain ⟨i⟩ := ‹Nonempty (Fin r ⊕ Fin r)›
    exact (Submodule.ne_bot_iff _).2 ⟨fun _ => 1, trivial, fun h => one_ne_zero (congrFun h i)⟩
  obtain ⟨x, hxA, hx1, v, -, hv0, hxv⟩ :=
    exists_fixed_in_of_plane_matrix hp hpK AG hAGe hAGc ⊤ htop (fun _ _ _ _ => trivial)
  obtain ⟨t, htA, rfl⟩ := Subgroup.mem_map.1 hxA
  have ht1 : t ≠ 1 := fun h => hx1 (by rw [h, map_one])
  have hσx : (((ψ.symm t : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ =
      (((ψ.symm t : StatedSp r K) : GL (Fin r ⊕ Fin r) K) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := by
    have h1 : fieldSp r K σ (ψ.symm t) = ψ.symm t := by
      apply hinj
      calc proj r K (fieldSp r K σ (ψ.symm t)) = f (proj r K (ψ.symm t)) := (fieldAut_proj σ _).symm
        _ = f t := by rw [show proj r K (ψ.symm t) = t from ψ.apply_symm_apply t]
        _ = t := hfix t htA
        _ = proj r K (ψ.symm t) := (ψ.apply_symm_apply t).symm
    exact congrArg (fun y : StatedSp r K => ((y : GL (Fin r ⊕ Fin r) K) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)) h1
  set x : GL (Fin r ⊕ Fin r) K := ι₁ t with hxdef
  have hW : ∀ u ∈ fixSubG x, vmap σ u ∈ fixSubG x := by
    intro u hu
    have hu' : (x : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ u = u := hu
    show (x : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) *ᵥ vmap σ u = vmap σ u
    have hxm : (x : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K).map σ =
        (x : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K) := hσx
    conv_lhs => rw [← hxm]
    rw [← vmap_mulVec, hu']
  have hne : fixSubG x ≠ ⊥ := fun h => hv0 (by
    have : v ∈ fixSubG x := hxv
    rw [h] at this
    exact (Submodule.mem_bot K).1 this)
  obtain ⟨w, hwW, hw0, hσw⟩ := exists_fixed_of_stable hp hσ (fixSubG x) hW hne
  have hxw : ((ψ.symm t : StatedSp r K) : GL (Fin r ⊕ Fin r) K).1 *ᵥ w = w := hwW
  set c : MulAut (StatedProj (StatedSp r K)) := MulAut.conj t with hcdef
  have hcP : c ∈ P := by rw [hPA]; exact Subgroup.mem_map_of_mem _ htA
  have hcĒ : c ∈ Ē := hPĒ hcP
  have hcinn : c ∈ inner (StatedProj (StatedSp r K)) := hPin hcP
  have hc1 : c ≠ 1 := by
    intro h
    apply ht1
    apply conj_injective_of_center_bot hZ
    rw [map_one]
    exact h
  have hford : orderOf f = p :=
    orderOf_eq_prime (hpowE f hf) (fun h => hfin (h ▸ Inn.one_mem))
  have hcord : orderOf c = p := orderOf_eq_prime (hpowE c hcĒ) hc1
  have hcomm : f * c = c * f := congrArg Subtype.val (hE.is_comm.comm ⟨f, hf⟩ ⟨c, hcĒ⟩)
  have hzfin : Finite (Subgroup.zpowers f) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hford]; exact hp.ne_zero)
  have hcnot : c ∉ Subgroup.zpowers f := by
    intro hmem
    have hle : Subgroup.zpowers c ≤ Subgroup.zpowers f := Subgroup.zpowers_le.2 hmem
    have heq : Subgroup.zpowers c = Subgroup.zpowers f :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hford, hcord])
    apply hfin
    have : f ∈ Subgroup.zpowers c := by rw [heq]; exact Subgroup.mem_zpowers f
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 this
    rw [← hn]
    exact Inn.zpow_mem hcinn n
  have hcomm' : ∀ y ∈ Subgroup.zpowers f, y * c = c * y := by
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Commute.zpow_left (show Commute f c from hcomm) n).eq
  have hP'c : Nat.card ↥(Subgroup.zpowers f ⊔ Subgroup.zpowers c) = p ^ 2 := by
    rw [card_sup_zpowers hp hcord hcomm' hcnot, Nat.card_zpowers, hford]
    ring
  have hσinv : vmap σ⁻¹ w = w := by
    calc vmap σ⁻¹ w = vmap σ⁻¹ (vmap σ w) := by rw [hσw]
      _ = vmap (σ⁻¹ * σ) w := vmap_vmap _ _ _
      _ = w := by rw [inv_mul_cancel, vmap_one]
  have hfstab : f ∈ autStab (trvSubT w) := by
    refine mem_autStab_of_forward _ (fun s hs => fieldAut_mem_trvSubT hσw hs) (fun s hs => ?_)
    rw [hfdef, ← map_inv]
    exact fieldAut_mem_trvSubT hσinv hs
  have hcen : ∀ s ∈ trvSubT w, t * s * t⁻¹ = s := by
    intro s hs
    have := centralizes_trvSubT hxw hs
    rwa [show proj r K (ψ.symm t) = t from ψ.apply_symm_apply t] at this
  have hcstab : c ∈ autStab (trvSubT w) := by
    refine mem_autStab_of_forward _ (fun s hs => ?_) (fun s hs => ?_)
    · rw [hcdef, MulAut.conj_apply, hcen s hs]
      exact hs
    · have h1 : t * s = s * t := by
        have := hcen s hs
        calc t * s = (t * s * t⁻¹) * t := by group
          _ = s * t := by rw [this]
      rw [hcdef, MulAut.conj_inv_apply]
      have h2 : t⁻¹ * s * t = s := by
        rw [mul_assoc, ← h1, inv_mul_cancel_left]
      rw [h2]
      exact hs
  obtain ⟨a₁, ha₁⟩ : ∃ a, σ a ≠ a := by
    by_contra hall
    push Not at hall
    have : σ = 1 := RingEquiv.ext hall
    rw [this, orderOf_one] at hσ
    exact hp.one_lt.ne hσ
  right
  refine ⟨Subgroup.zpowers f ⊔ Subgroup.zpowers c,
    sup_le (Subgroup.zpowers_le.2 hf) (Subgroup.zpowers_le.2 hcĒ), hP'c, trvSubT w,
    isPGroup_trvSubT w, ?_, f, Subgroup.mem_sup_left (Subgroup.mem_zpowers f),
    proj r K (trvSp w a₁), mem_trvSubT.2 ⟨a₁, rfl⟩, ?_⟩
  · have hstab : Subgroup.zpowers f ⊔ Subgroup.zpowers c ≤ autStab (trvSubT w) :=
      sup_le (Subgroup.zpowers_le.2 hfstab) (Subgroup.zpowers_le.2 hcstab)
    intro φ hφ s hs
    exact ((hstab hφ) s).2 hs
  · intro heq
    rw [hfdef, fieldAut_proj, fieldSp_trvSp hσw] at heq
    exact ha₁ (trvSp_inj hw0 (hinj heq))

end CFSG.RankThree.PartOne.K133C
