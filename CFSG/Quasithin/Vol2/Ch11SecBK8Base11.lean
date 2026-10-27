module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base10
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base6

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

theorem exists_semilinear_of_mem [Finite K] {x : MulAut (W6 K)} (hx : x ∈ normD K) :
    ∃ σ : K ≃+* K, IsSemilinear x σ := by
  obtain ⟨σ, Φ, M, hΦ, hxf⟩ := exists_semilinear_tens hx
  exact ⟨σ, isSemilinear_of_tens hΦ hxf⟩

@[expose] noncomputable def semiAut [Finite K] (x : ↥(normD K)) : K ≃+* K :=
  Classical.choose (exists_semilinear_of_mem x.2)

theorem isSemilinear_semiAut [Finite K] (x : ↥(normD K)) :
    IsSemilinear (x : MulAut (W6 K)) (semiAut x) :=
  Classical.choose_spec (exists_semilinear_of_mem x.2)

@[expose] noncomputable def semiHom [Finite K] : ↥(normD K) →* (K ≃+* K) where
  toFun := semiAut
  map_one' := (isSemilinear_semiAut 1).unique isSemilinear_one
  map_mul' x y :=
    (isSemilinear_semiAut (x * y)).unique ((isSemilinear_semiAut x).mul (isSemilinear_semiAut y))

theorem semiHom_eq_one_iff [Finite K] (x : ↥(normD K)) :
    semiHom x = 1 ↔ (x : MulAut (W6 K)) ∈ linSub := by
  constructor
  · intro h
    have := isSemilinear_semiAut x
    change IsSemilinear _ (semiHom x) at this
    rw [h] at this
    exact this
  · intro h
    exact (isSemilinear_semiAut x).unique (mem_linSub.mp h)

theorem card_le_two_mul_lin [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {E : Subgroup (MulAut (W6 K))} (hEN : E ≤ normD K) (hE : ∀ x ∈ E, x ^ 2 = 1) :
    Nat.card E ≤ 2 * Nat.card ↥(E ⊓ linSub) := by
  have : IsCyclic (K ≃+* K) := isCyclic_ringAut hn hK
  have : Finite (K ≃+* K) := Finite.of_injective (fun τ : K ≃+* K => (τ : K → K))
    (fun _ _ h => RingEquiv.ext (congrFun h))
  have : Finite (MulAut (W6 K)) := MulEquiv.finite_left
  let φ : ↥E →* (K ≃+* K) := semiHom.comp (Subgroup.inclusion hEN)
  have hrange : Nat.card φ.range ≤ 2 := by
    refine card_le_two_of_isCyclic _ ?_
    rintro _ ⟨x, rfl⟩
    rw [← map_pow]
    have : x ^ 2 = 1 := Subtype.ext (by simpa using hE x.1 x.2)
    rw [this, map_one]
  have hker : Nat.card φ.ker = Nat.card ↥(E ⊓ linSub) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.1.2, (semiHom_eq_one_iff _).mp x.2⟩
        invFun := fun y => ⟨⟨y.1, y.2.1⟩, (semiHom_eq_one_iff ⟨y.1, hEN y.2.1⟩).mpr y.2.2⟩
        left_inv := fun x => rfl
        right_inv := fun y => rfl }
  have hcard : Nat.card E = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.card_mul_index φ.ker, Subgroup.index_ker]
  rw [hcard, hker, mul_comm 2]
  exact Nat.mul_le_mul_left _ hrange

@[expose, instance_reducible] noncomputable def actOn [Finite K] {E : Subgroup (MulAut (W6 K))}
    (hEN : E ≤ normD K) :
    MulAction ↥E (Option K) where
  smul x p := act ⟨x, hEN x.2⟩ p
  one_smul p := act_one p
  mul_smul x y p := act_mul ⟨x, hEN x.2⟩ ⟨y, hEN y.2⟩ p

theorem exists_fixed [Finite K] {n : ℕ} (hn : n ≠ 0) (hK : Nat.card K = 2 ^ n)
    {E : Subgroup (MulAut (W6 K))} (hEN : E ≤ normD K) (hE : ∀ x ∈ E, x ^ 2 = 1) :
    ∃ p₀ : Option K, ∀ x (hx : x ∈ E), act ⟨x, hEN hx⟩ p₀ = p₀ := by
  let _ := actOn hEN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥E := fun x => ⟨1, Subtype.ext (by simpa using hE x.1 x.2)⟩
  have h2 : ¬ 2 ∣ Nat.card (Option K) := by
    rw [Finite.card_option, hK]
    have : 2 ∣ 2 ^ n := dvd_pow_self 2 hn
    omega
  obtain ⟨p₀, hp₀⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card (Option K) h2
  exact ⟨p₀, fun x hx => hp₀ ⟨x, hx⟩⟩

theorem card_lin_le [Finite K] [CharP K 2] {n : ℕ} (hn : n ≠ 0) (hK : Nat.card K = 2 ^ n)
    {E : Subgroup (MulAut (W6 K))} (hEN : E ≤ normD K) (hEl : E ≤ linSub)
    (hE : IsElemAbelian2 E) : Nat.card E ≤ Nat.card K * Nat.card ↥(E ⊓ dgSub K) := by
  obtain ⟨p₀, hp₀⟩ := exists_fixed hn hK hEN hE.2
  let _ := actOn hEN
  have : Fintype (Option K) := Fintype.ofFinite _
  obtain ⟨p₁, hp₁⟩ : ∃ p₁ : Option K, p₁ ≠ p₀ := by
    cases p₀ with
    | none => exact ⟨some 0, Option.some_ne_none 0⟩
    | some c => exact ⟨none, (Option.some_ne_none c).symm⟩
  have horb : (MulAction.orbit ↥E p₁).ncard ≤ Nat.card K := by
    have e : Nat.card {p : Option K // p ≠ p₀} = ({p | p ≠ p₀} : Set (Option K)).ncard :=
      Nat.card_coe_set_eq _
    rw [← card_ne_pt p₀, e]
    refine Set.ncard_le_ncard ?_ (Set.toFinite _)
    rintro _ ⟨x, rfl⟩ h
    apply hp₁
    apply act_injective ⟨x.1, hEN x.2⟩
    exact h.trans (hp₀ x.1 x.2).symm
  have hstab : Nat.card ↥(MulAction.stabilizer ↥E p₁) ≤ Nat.card ↥(E ⊓ dgSub K) := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨x.1.1, x.1.2, ?_⟩) (fun x y h => Subtype.ext (Subtype.ext (congrArg
        (fun z : ↥(E ⊓ dgSub K) => (z : MulAut (W6 K))) h)))
    obtain ⟨A, M, hAM⟩ := exists_tensHom (hEN x.1.2) (hEl x.1.2)
    have hsq : x.1.1 * x.1.1 = 1 := by rw [← sq]; exact hE.2 _ x.1.2
    have hfix₁ : act ⟨x.1.1, hEN x.1.2⟩ p₁ = p₁ := x.2
    have hfix₀ := hp₀ x.1.1 x.1.2
    have hx' : matAut (tensHom (A, M)) ∈ normD K := hAM ▸ hEN x.1.2
    rw [hAM] at hsq ⊢
    have e : (⟨x.1.1, hEN x.1.2⟩ : ↥(normD K)) = ⟨_, hx'⟩ := Subtype.ext hAM
    rw [e] at hfix₁ hfix₀
    exact mem_dgSub_of_two_fixed hx' hsq hp₁ hfix₁ hfix₀
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥E p₁)
  rw [MulAction.index_stabilizer] at h1
  rw [← h1, mul_comm]
  exact Nat.mul_le_mul horb hstab

@[expose] noncomputable def dgMat (E : Subgroup (MulAut (W6 K))) : Subgroup (GL (Fin 3) K) :=
  (E ⊓ dgSub K).comap (matHom.comp dgHom)

theorem card_dgMat (E : Subgroup (MulAut (W6 K))) :
    Nat.card ↥(dgMat E) = Nat.card ↥(E ⊓ dgSub K) := by
  let f : GL (Fin 3) K →* MulAut (W6 K) := matHom.comp dgHom
  have hinj : Function.Injective f := fun g g' h => matAut_dgHom_injective h
  have h1 := Subgroup.card_map_of_injective (K := dgMat E) hinj
  rw [dgMat, Subgroup.map_comap_eq_self (inf_le_right : E ⊓ dgSub K ≤ dgSub K)] at h1
  exact h1.symm

theorem dgMat_sq {E : Subgroup (MulAut (W6 K))} (hE : IsElemAbelian2 E) :
    ∀ A ∈ dgMat E, A * A = 1 := fun A hA => by
  apply matAut_dgHom_injective
  have := hE.2 _ hA.1
  rw [matAut_dgHom_one, ← sq, matAut_dgHom_pow]
  exact this

theorem dgMat_comm {E : Subgroup (MulAut (W6 K))} (hE : IsElemAbelian2 E) :
    ∀ A ∈ dgMat E, ∀ B ∈ dgMat E, A * B = B * A := fun A hA B hB => by
  apply matAut_dgHom_injective
  have := hE.1 _ hA.1 _ hB.1
  change matHom (dgHom (A * B)) = matHom (dgHom (B * A))
  rw [map_mul, map_mul, map_mul, map_mul]
  exact this

theorem card_dg_le [Finite K] [CharP K 2] {E : Subgroup (MulAut (W6 K))} (hE : IsElemAbelian2 E) :
    Nat.card ↥(E ⊓ dgSub K) ≤ Nat.card K ^ 2 := by
  rw [← card_dgMat]
  exact card_le_of_elemAbelian_GL3 _ (dgMat_sq hE) (dgMat_comm hE)

theorem two_mul_card_dg_le [Finite K] [CharP K 2] {n : ℕ} (hK : Nat.card K = 2 ^ n)
    {E : Subgroup (MulAut (W6 K))} (hEN : E ≤ normD K) (hE : IsElemAbelian2 E) {y : MulAut (W6 K)}
    (hyE : y ∈ E) (hy : y ∉ linSub) : 2 * Nat.card ↥(E ⊓ dgSub K) ≤ Nat.card K ^ 2 := by
  obtain ⟨σ, Φ, M, hΦ, hyf⟩ := exists_semilinear_tens (hEN hyE)
  have hσ : σ ≠ RingEquiv.refl K := fun h => hy (by
    have := isSemilinear_of_tens hΦ hyf
    rw [h] at this
    exact this)
  have hrow : M 0 0 ≠ 0 ∨ M 0 1 ≠ 0 := by
    by_contra h
    push Not at h
    have h1 := hyf (toAddMap y⁻¹ (Sum.elim (Pi.single 0 1) 0))
    rw [toAddMap_inv_apply, h.1, h.2, zero_smul, zero_smul, add_zero, toAddMap_zero] at h1
    have := congrFun h1 (Sum.inl 0)
    simp at this
  have hsurj : ∀ w : Fin 3 → K, ∃ v : I6 → K,
      M 0 0 • (v ∘ Sum.inl) + M 0 1 • (v ∘ Sum.inr) = w := by
    intro w
    rcases hrow with h | h
    · refine ⟨Sum.elim ((M 0 0)⁻¹ • w) 0, ?_⟩
      rw [Sum.elim_comp_inl, Sum.elim_comp_inr, smul_zero, add_zero, smul_smul,
        mul_inv_cancel₀ h, one_smul]
    · refine ⟨Sum.elim 0 ((M 0 1)⁻¹ • w), ?_⟩
      rw [Sum.elim_comp_inl, Sum.elim_comp_inr, smul_zero, zero_add, smul_smul,
        mul_inv_cancel₀ h, one_smul]
  rw [← card_dgMat]
  refine SL3Pair.two_mul_card_le_of_comm_semilinear hK _ (dgMat_sq hE) (dgMat_comm hE) hΦ hσ ?_
  intro A hA w
  obtain ⟨v, rfl⟩ := hsurj w
  have hc := congrArg (fun z : MulAut (W6 K) => toAddMap z v) (hE.1 _ hyE _ hA.1)
  simp only [toAddMap_mul] at hc
  change toAddMap y (toAddMap (matAut (dgHom A)) v) =
    toAddMap (matAut (dgHom A)) (toAddMap y v) at hc
  rw [hyf, hyf, toAddMap_matAut, toAddMap_matAut, dgHom_mulVec, dgHom_mulVec] at hc
  have := congrArg (fun u : I6 → K => u ∘ Sum.inl) hc
  simp only [Sum.elim_comp_inl, Sum.elim_comp_inr] at this
  rw [← Matrix.mulVec_smul, ← Matrix.mulVec_smul, ← Matrix.mulVec_add] at this
  exact this

theorem card_le_cube [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    {E : Subgroup (MulAut (W6 K))} (hEN : E ≤ normD K) (hE : IsElemAbelian2 E) :
    Nat.card E ≤ Nat.card K ^ 3 := by
  have hEl : IsElemAbelian2 (E ⊓ linSub) :=
    ⟨fun a ha b hb => hE.1 a ha.1 b hb.1, fun a ha => hE.2 a ha.1⟩
  have h1 := card_le_two_mul_lin hn hK hEN hE.2
  have h2 := card_lin_le (by omega) hK (inf_le_left.trans hEN) inf_le_right hEl
  have h3 : (E ⊓ linSub) ⊓ dgSub K = E ⊓ dgSub K := by
    rw [inf_assoc, inf_eq_right.mpr dgSub_le_linSub]
  rw [h3] at h2
  by_cases hlin : E ≤ linSub
  · rw [inf_eq_left.mpr hlin] at h2
    calc Nat.card E ≤ Nat.card K * Nat.card ↥(E ⊓ dgSub K) := h2
      _ ≤ Nat.card K * Nat.card K ^ 2 := Nat.mul_le_mul_left _ (card_dg_le hE)
      _ = Nat.card K ^ 3 := by ring
  · obtain ⟨y, hyE, hy⟩ : ∃ y ∈ E, y ∉ linSub := by
      by_contra h
      push Not at h
      exact hlin h
    have h4 := two_mul_card_dg_le hK hEN hE hyE hy
    calc Nat.card E ≤ 2 * (Nat.card K * Nat.card ↥(E ⊓ dgSub K)) :=
          h1.trans (Nat.mul_le_mul_left 2 h2)
      _ = Nat.card K * (2 * Nat.card ↥(E ⊓ dgSub K)) := by ring
      _ ≤ Nat.card K * Nat.card K ^ 2 := Nat.mul_le_mul_left _ h4
      _ = Nat.card K ^ 3 := by ring

end CFSG.Quasithin.Vol2.Ch11.SecB.K8
