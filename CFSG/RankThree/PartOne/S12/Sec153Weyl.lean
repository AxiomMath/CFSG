module

public import CFSG.RankThree.PartOne.S12.Sec153
public import CFSG.RankThree.PartOne.S12.Sec154
public import CFSG.RankThree.PartOne.S12.Sec155
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

namespace Sec153

section Data

variable {G : Type} [Group G]

@[reducible, expose] def commE {E : Subgroup G} (hEc : ∀ a b : ↥E, a * b = b * a) :
    CommGroup ↥E :=
  { (inferInstance : Group ↥E) with mul_comm := hEc }

structure ModData (p : ℕ) (E : Subgroup G) where
  θ : ↥(reflectionGroup p E) ≃* Equiv.Perm (Fin 5)
  v : Fin 5 → ↥E
  perm : ∀ (w : ↥(reflectionGroup p E)) (i : Fin 5), (w : MulAut ↥E) (v i) = v (θ w i)
  gen : ∀ x : ↥E, ∃ a : Fin 5 → ℤ,
    x = v 0 ^ a 0 * v 1 ^ a 1 * v 2 ^ a 2 * v 3 ^ a 3 * v 4 ^ a 4
  rel : ∀ a : Fin 5 → ℤ, v 0 ^ a 0 * v 1 ^ a 1 * v 2 ^ a 2 * v 3 ^ a 3 * v 4 ^ a 4 = 1 ↔
    ∃ m : ℤ, ∀ i, (p : ℤ) ∣ a i - m
  refl : ∀ (t : MulAut ↥E) (ht : t ∈ reflectionSet p E),
    ∃ a b : Fin 5, a ≠ b ∧ θ ⟨t, Subgroup.subset_closure ht⟩ = Equiv.swap a b

end Data

section Split

variable {G : Type} [Group G] [Finite G]

theorem nonempty_modData (hMod : KFU5Mod) {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (h15 : Sec15Hyp G p A c L E) (hF : Sec12Facts G p A c L E)
    (hout : Outcome152Five p E A (lieGenerated p E)) : Nonempty (ModData p E) := by
  obtain ⟨θ, v, h1, h2, h3, h4⟩ := hMod G p A c L E h15 hF hout
  exact ⟨⟨θ, v, h1, h2, h3, h4⟩⟩

omit [Finite G] in
theorem central_of_pow {E : Subgroup G} (z : MulAut ↥E) (k : ℤ) (hk : ∀ e : ↥E, z e = e ^ k)
    (u : MulAut ↥E) : u * z = z * u := by
  refine MulEquiv.ext fun e => ?_
  show u (z e) = z (u e)
  rw [hk, hk, map_zpow]

omit [Finite G] in
theorem pow_of_pow {E : Subgroup G} (z : MulAut ↥E) (k : ℤ) (hk : ∀ e : ↥E, z e = e ^ k)
    (n : ℕ) : ∀ e : ↥E, (z ^ n) e = e ^ (k ^ n) := by
  induction n with
  | zero => intro e; simp
  | succ n ih =>
    intro e
    rw [pow_succ', MulAut.mul_apply, ih, map_zpow, hk, ← zpow_mul, ← pow_succ']

variable {p : ℕ} {E : Subgroup G}

theorem reflection_not_mem_pCore (hp : p.Prime) (M : ModData p E)
    {t : MulAut ↥E} (ht : t ∈ reflectionSet p E) :
    t ∉ (CFSG.pCore 2 ↥(reflectionGroup p E)).map (reflectionGroup p E).subtype := by
  classical
  intro hmem
  obtain ⟨y, hy, hyt⟩ := Subgroup.mem_map.1 hmem
  have hyeq : y = ⟨t, Subgroup.subset_closure ht⟩ := Subtype.ext hyt
  rw [hyeq] at hy
  obtain ⟨a, b, hab, hθ⟩ := M.refl t ht
  have hall : ∀ i j : Fin 5, i ≠ j → ∃ (u : MulAut ↥E) (hu : u ∈ reflectionSet p E),
      M.θ ⟨u, Subgroup.subset_closure hu⟩ = Equiv.swap i j ∧
      (⟨u, Subgroup.subset_closure hu⟩ : ↥(reflectionGroup p E)) ∈
        CFSG.pCore 2 ↥(reflectionGroup p E) := by
    intro i j hij
    obtain ⟨u, hu, hθu⟩ := exists_reflection_swap hp M.θ M.refl i j hij
    refine ⟨u, hu, hθu, ?_⟩
    obtain ⟨σ, hσa, hσb⟩ := exists_perm_two a b i j hab hij
    have hconj : (⟨u, Subgroup.subset_closure hu⟩ : ↥(reflectionGroup p E)) =
        M.θ.symm σ * ⟨t, Subgroup.subset_closure ht⟩ * (M.θ.symm σ)⁻¹ := by
      apply M.θ.injective
      rw [hθu, map_mul, map_mul, map_inv, hθ, MulEquiv.apply_symm_apply, ← Equiv.swap_apply_apply,
        hσa, hσb]
    rw [hconj]
    exact Subgroup.Normal.conj_mem inferInstance _ hy _
  obtain ⟨u₁, hu₁, hθ₁, hc₁⟩ := hall 0 1 (by decide)
  obtain ⟨u₂, hu₂, hθ₂, hc₂⟩ := hall 1 2 (by decide)
  have hprod := Subgroup.mul_mem _ hc₁ hc₂
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(reflectionGroup p E))) ⟨_, hprod⟩
  have h1 : (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) ^ 2 ^ n = 1 := by
    have := congrArg (fun x : ↥(CFSG.pCore 2 ↥(reflectionGroup p E)) => M.θ x.1) hn
    simpa [map_mul, map_pow, hθ₁, hθ₂] using this
  have h3 : orderOf (Equiv.swap (0 : Fin 5) 1 * Equiv.swap 1 2) = 3 :=
    orderOf_eq_prime (by decide) (by decide)
  have h5 := orderOf_dvd_of_pow_eq_one h1
  rw [h3] at h5
  have h6 := (Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 3) h5)
  omega

omit [Finite G] in
theorem ModData.pow_of_commute (M : ModData p E) (hEc : ∀ a b : ↥E, a * b = b * a)
    (z : MulAut ↥E) (hz : ∀ x ∈ reflectionGroup p E, z * x = x * z) :
    ∃ k : ℤ, ∀ e : ↥E, z e = e ^ k := by
  classical
  let _ : CommGroup ↥E := commE hEc
  have hrel' : ∀ a : Fin 5 → ℤ, ∏ i, M.v i ^ a i = 1 ↔ ∃ m : ℤ, ∀ i, (p : ℤ) ∣ a i - m :=
    fun a => by rw [Fin.prod_univ_five]; exact M.rel a
  have hgen' : ∀ x : ↥E, ∃ a : Fin 5 → ℤ, x = ∏ i, M.v i ^ a i := fun x => by
    obtain ⟨a, ha⟩ := M.gen x
    exact ⟨a, by rw [Fin.prod_univ_five]; exact ha⟩
  refine power_of_commute M.v hrel' hgen' z (fun σ =>
    ⟨((M.θ.symm σ : ↥(reflectionGroup p E)) : MulAut ↥E), fun i => ?_, fun y => ?_⟩)
  · have := M.perm (M.θ.symm σ) i
    rwa [MulEquiv.apply_symm_apply] at this
  · have := hz _ (M.θ.symm σ).2
    exact congrArg (fun u : MulAut ↥E => u y) this

omit [Finite G] in
theorem ModData.eq_one_of_pow_mem (M : ModData p E) {z : MulAut ↥E} (hzI : z ∈ reflectionGroup p E)
    {k : ℤ} (hk : ∀ e : ↥E, z e = e ^ k) : z = 1 := by
  have hcomm : ∀ τ : Equiv.Perm (Fin 5), M.θ ⟨z, hzI⟩ * τ = τ * M.θ ⟨z, hzI⟩ := by
    intro τ
    have h1 := central_of_pow z k hk (M.θ.symm τ : ↥(reflectionGroup p E))
    have h2 : (M.θ.symm τ : ↥(reflectionGroup p E)) * ⟨z, hzI⟩ =
        ⟨z, hzI⟩ * (M.θ.symm τ : ↥(reflectionGroup p E)) := Subtype.ext h1
    have h3 := congrArg M.θ h2
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h3
    exact h3.symm
  have h4 : M.θ ⟨z, hzI⟩ = 1 := sym5_center _ hcomm
  have h5 : (⟨z, hzI⟩ : ↥(reflectionGroup p E)) = 1 := M.θ.injective (by rw [h4, map_one])
  exact congrArg Subtype.val h5

theorem ModData.split (M : ModData p E) (hp : p.Prime) (hEc : ∀ a b : ↥E, a * b = b * a) :
    ∀ w ∈ torusWeyl E, ∃ s ∈ reflectionGroup p E, ∃ k : ℤ, ∀ e : ↥E,
      (s⁻¹ * w) e = e ^ k := by
  intro w hw
  have hIW : reflectionGroup p E ≤ torusWeyl E := Sec1322.reflectionGroup_le E
  have hwN : w ∈ Subgroup.normalizer ((reflectionGroup p E : Subgroup (MulAut ↥E)) :
      Set (MulAut ↥E)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact Sec1322.conj_mem_reflectionGroup hp hw hx
    · intro hx
      have := Sec1322.conj_mem_reflectionGroup hp ((torusWeyl E).inv_mem hw) hx
      simpa [mul_assoc] using this
  let cw : MulAut ↥(reflectionGroup p E) := (reflectionGroup p E).normalizerMonoidHom ⟨w, hwN⟩
  have hcw : ∀ x : ↥(reflectionGroup p E),
      ((cw x : ↥(reflectionGroup p E)) : MulAut ↥E) = w * x * w⁻¹ := fun x =>
    Subgroup.normalizerMonoidHom_apply_apply_coe _ ⟨w, hwN⟩ x
  let ψ : Equiv.Perm (Fin 5) ≃* Equiv.Perm (Fin 5) := (M.θ.symm.trans cw).trans M.θ
  obtain ⟨σ₀, hσ₀⟩ := sym5_conj_surjective ψ
  have hconj : ∀ x : ↥(reflectionGroup p E),
      cw x = M.θ.symm σ₀ * x * (M.θ.symm σ₀)⁻¹ := by
    intro x
    apply M.θ.injective
    have h1 := congrArg (fun φ : MulAut (Equiv.Perm (Fin 5)) => φ (M.θ x)) hσ₀
    simp only [MulAut.conj_apply] at h1
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rw [h1]
    simp [ψ]
  refine ⟨((M.θ.symm σ₀ : ↥(reflectionGroup p E)) : MulAut ↥E), (M.θ.symm σ₀).2, ?_⟩
  apply M.pow_of_commute hEc
  intro x hx
  have h1 := hconj ⟨x, hx⟩
  have h2 := congrArg (fun y : ↥(reflectionGroup p E) => (y : MulAut ↥E)) h1
  simp only [hcw, Subgroup.coe_mul, Subgroup.coe_inv] at h2
  calc (((M.θ.symm σ₀ : ↥(reflectionGroup p E)) : MulAut ↥E)⁻¹ * w) * x
      = ((M.θ.symm σ₀ : ↥(reflectionGroup p E)) : MulAut ↥E)⁻¹ * (w * x * w⁻¹) * w := by group
    _ = ((M.θ.symm σ₀ : ↥(reflectionGroup p E)) : MulAut ↥E)⁻¹ *
        (((M.θ.symm σ₀ : ↥(reflectionGroup p E)) : MulAut ↥E) * x *
          ((M.θ.symm σ₀ : ↥(reflectionGroup p E)) : MulAut ↥E)⁻¹) * w := by rw [h2]
    _ = x * (((M.θ.symm σ₀ : ↥(reflectionGroup p E)) : MulAut ↥E)⁻¹ * w) := by group

theorem ModData.mem_of_pPower (M : ModData p E) (hp : p.Prime) (hEc : ∀ a b : ↥E, a * b = b * a)
    (hE : ∀ e : ↥E, e ^ p = 1) {g : MulAut ↥E} (hg : g ∈ torusWeyl E) {a : ℕ}
    (hga : g ^ (p ^ a) = 1) : g ∈ reflectionGroup p E := by
  obtain ⟨s, hsI, k, hk⟩ := M.split hp hEc g hg
  set z : MulAut ↥E := s⁻¹ * g with hz
  have hgsz : g = s * z := by rw [hz]; group
  have hcomm : s * z = z * s := (central_of_pow z k hk s)
  have hzpow : z ^ (p ^ a) = 1 := by
    have h1 : g ^ (p ^ a) = s ^ (p ^ a) * z ^ (p ^ a) := by
      rw [hgsz]
      exact (Commute.mul_pow (hcomm : Commute s z) _)
    have h2 : z ^ (p ^ a) = (s ^ (p ^ a))⁻¹ := by
      rw [hga] at h1
      exact eq_inv_of_mul_eq_one_right h1.symm
    have h3 : z ^ (p ^ a) ∈ reflectionGroup p E := by
      rw [h2]
      exact (reflectionGroup p E).inv_mem ((reflectionGroup p E).pow_mem hsI _)
    exact M.eq_one_of_pow_mem h3 (pow_of_pow z k hk (p ^ a))
  have hz1 : z = 1 := Sec155.scalar_pElement hp hE hk hzpow
  rw [hgsz, hz1, mul_one]
  exact hsI

end Split

section Weyl

variable {G : Type} [Group G] [Finite G]

theorem kf154Five_of_mod (hMod : KFU5Mod) : KF154Five := by
  intro G _ _ p A c L E h15 hF hout
  classical
  have h := h15.h12
  have hp := h.prime
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hEc : ∀ a b : ↥E, a * b = b * a := fun a b => hEel.is_comm.comm a b
  obtain ⟨M⟩ := nonempty_modData hMod h15 hF hout
  have hIW : reflectionGroup p E ≤ torusWeyl E := Sec1322.reflectionGroup_le E
  refine ⟨reflectionGroup p E, ?_, le_rfl, Or.inr ⟨M.θ⟩, ?_, ?_, ?_⟩
  · have hset : {t : MulAut ↥E | t ∈ reflectionSet p E ∧ t ∉
        (CFSG.pCore 2 ↥(reflectionGroup p E)).map (reflectionGroup p E).subtype} =
        reflectionSet p E :=
      Set.ext fun t => ⟨fun ht => ht.1, fun ht => ⟨ht, reflection_not_mem_pCore hp M ht⟩⟩
    rw [hset]
    rfl
  · apply le_antisymm
    · intro w hw
      obtain ⟨s, hsI, k, hk⟩ := M.split hp hEc w hw
      have hsW : s ∈ torusWeyl E := hIW hsI
      have hzW : s⁻¹ * w ∈ torusWeyl E := (torusWeyl E).mul_mem ((torusWeyl E).inv_mem hsW) hw
      have hzc := central_of_pow _ k hk
      have hzcenter : (⟨s⁻¹ * w, hzW⟩ : ↥(torusWeyl E)) ∈ Subgroup.center ↥(torusWeyl E) :=
        Subgroup.mem_center_iff.2 fun g => Subtype.ext (hzc g.1)
      have hwz : w = (s⁻¹ * w) * s := by
        calc w = s * (s⁻¹ * w) := by group
          _ = _ := hzc s
      rw [hwz]
      exact Subgroup.mul_mem_sup (Subgroup.mem_map.2 ⟨⟨_, hzW⟩, hzcenter, rfl⟩) hsI
    · exact sup_le (Subgroup.map_subtype_le _) hIW
  · rw [eq_bot_iff]
    intro g hg
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 hg.1
    have hxg' : (x : MulAut ↥E) = g := hxg
    have hcomm : ∀ x' ∈ reflectionGroup p E, g * x' = x' * g := by
      intro x' hx'
      have h1 := Subgroup.mem_center_iff.1 hx ⟨x', hIW hx'⟩
      have h1' := congrArg Subtype.val h1
      simp only [Subgroup.coe_mul] at h1'
      rw [hxg'] at h1'
      exact h1'.symm
    obtain ⟨k, hk⟩ := M.pow_of_commute hEc g hcomm
    have := M.eq_one_of_pow_mem hg.2 hk
    exact Subgroup.mem_bot.2 this
  · intro z hz
    refine M.pow_of_commute hEc (z : MulAut ↥E) (fun x hx => ?_)
    have := Subgroup.mem_center_iff.1 hz ⟨x, hIW hx⟩
    exact (congrArg Subtype.val this).symm

end Weyl

end Sec153

end CFSG.RankThree.PartOne
