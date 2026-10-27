module

public import CFSG.RankThree.GF2n.Stroth80.Step710Vanish
public import CFSG.RankThree.GF2n.Stroth80.Sec710Family
public import CFSG.RankThree.GF2n.Stroth80.Sec710Point
public import CFSG.RankThree.GF2n.Stroth80.Sec7NormalizerOmega
public import CFSG.RankThree.GF2n.Stroth80.Sec7SingularFamily
public import CFSG.RankThree.GF2n.Stroth80.Sec710Lemma61

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open QuadraticMap
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem comm_tg_mem_conj (h310chi : Stroth310ChiStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) {g : G} (hg : g ∈ M) :
    ∀ w ∈ Q, ⁅g * t * g⁻¹, w⁆ ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
  intro w hw
  have hV : Vt M (LB M Q B) B Z t = Ut Q Z t :=
    (h310chi G M Q Z B hc n t hs.toSec5 (Or.inr hs.omegaNat)).1
  have hw' : g⁻¹ * w * g ∈ Q := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hg)) w).mp hw
    rwa [inv_inv] at h1
  have hTc : ⁅t, g⁻¹ * w * g⁆ ∈ ⁅Q, Subgroup.zpowers t⁆ := by
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hw' (Subgroup.mem_zpowers t))
  rw [mem_conjSubgroup, hV, conj_commutator_conj]
  exact Subgroup.mem_sup_left hTc

theorem step710Vanish_generic (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement)
    (hZcard : Sec7ZCardStatement) (h56 : Stroth56NatStatement) (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) (hnom : ¬ OmegaMinusNat hc t 2)
    (hnatSO : SpNat hc t ∨ OmegaNat hc t) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK4 : 4 ≤ Nat.card K) (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι]
    [DecidableEq ι] [Nonempty ι] {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
    (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) (hX : AddCommutantScalar X)
    (hN : ∀ A : GL ι K, (∀ g ∈ X, A * g * A⁻¹ ∈ X) →
      ∃ c : K, c ≠ 0 ∧ ∀ v, Q' (c • ((A : Matrix ι ι K) *ᵥ v)) = Q' v)
    (hW : ∀ x y : ι → K, x ≠ 0 → y ≠ 0 → Q' x = Q' y →
      ∃ A ∈ X, ((A : GL ι K) : Matrix ι ι K) *ᵥ x = y)
    (hnat : NaturalRep (ι := ι) K X (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t))
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hH : ∀ g ∈ M, conjSubgroup g Z0 ≤ LB M Q B → conjSubgroup g Z0 = Z0) {g : G} (hg : g ∈ M)
    (hΓ : ∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) :
    ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅g * t * g⁻¹, v⁆ ∈ Z := by
  classical
  by_contra hcon
  push Not at hcon
  obtain ⟨v, hv, hxv⟩ := hcon
  obtain ⟨φ, hφ, hker, hact⟩ := hnat
  obtain ⟨hnorm, hn, ψ, hψ⟩ := hact
  haveI := hn
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  obtain ⟨T, hT2, hfam, hTk⟩ := exists_vanish_family h34 h310chi hZc hZV hZcard hc hs hZ0 hK hX
    φ hφ ψ hψ hg hΓ
  have hall := alg_sing_of_family hK4 hQ hN T hT2 hfam
  obtain ⟨k', hk', hTk'⟩ := hTk ⟨v, hv⟩
  have hk'g : (k' : G) ∈ conjSubgroup g (Vt M (LB M Q B) B Z t) := by
    rw [hk']
    exact comm_tg_mem_conj h310chi hc hs hg v (hc.Vt_le_Q t hv)
  have hu0 : secVec ψ k' ≠ 0 := by
    intro h0
    exact hxv (by
      have := (secVec_eq_zero_iff ψ k').mp h0
      rwa [hk'] at this)
  have hQu : Q' (secVec ψ k') = 0 := by
    rw [← hTk']
    exact hall _
  obtain ⟨r, hr, hle⟩ := exists_point_le_of_singular h34 hRoot hc hs.toSec5 hnatSO hK E hQ h3 hX
    hW φ hφ hker ψ hψ hg hu0 hQu ⟨k', hk'g, rfl⟩
  have hZL : Z0 ≤ LB M Q B := fun z hz => (hZc G M Q Z B hc n t hs Z0 hZ0 z hz).1
  have hZ0g := sec710_lemma61 h56 hc hs hnom hZ0 hZL hH hg hr hle
  have hxmem : g * t * g⁻¹ ∈ conjSubgroup g Z0 := by
    rw [mem_conjSubgroup]
    simpa [mul_assoc] using htZ0
  rw [hZ0g] at hxmem
  exact hxv ((Z0_le_CN_of_34 h34 hZc hc hs hZ0 hxmem).2 v hv)

theorem step710Vanish_plus (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement)
    (hZcard : Sec7ZCardStatement) (h56 : Stroth56NatStatement) (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) (hnom : ¬ OmegaMinusNat hc t 2) {m : ℕ} (hm3 : 3 ≤ m)
    (hP : OmegaPlusNat hc t m) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hH : ∀ g ∈ M, conjSubgroup g Z0 ≤ LB M Q B → conjSubgroup g Z0 = Z0) {g : G} (hg : g ∈ M)
    (hΓ : ∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) :
    ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅g * t * g⁻¹, v⁆ ∈ Z := by
  obtain ⟨K, fK, finK, hK, hnat⟩ := hP
  haveI : CharP K 2 := sec7ctr_charP hc hK
  haveI : Nonempty (Fin m ⊕ Fin m) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hK4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  have hnatSO : SpNat hc t ∨ OmegaNat hc t := Or.inr ⟨K, fK, finK, hK, Or.inl ⟨m, hm3, hnat⟩⟩
  have h3 : 3 ≤ Module.finrank K (Fin m ⊕ Fin m → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
    omega
  refine step710Vanish_generic h34 hRoot h310chi hZc hZV hZcard h56 hc hs hnom hnatSO hK4 hK
    (ElemMatrixIso.plus hm3) (nondegenerate_polarBilin_quadPlus m K) h3
    (addCommutantScalar_statedOmegaPlus hm3) (fun A hA => ?_)
    (fun x y hx hy hxy => (ElemMatrixIso.plus hm3).exists_mulVec_eq
      (nondegenerate_polarBilin_quadPlus m K)
      (plusPair_orth (K := K) (n := m) (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
        (fun h => Nat.zero_ne_one (congrArg Fin.val h))) hx hy hxy)
    hnat hZ0 hH hg hΓ
  obtain ⟨c, hc0, hcv⟩ := normalizerOmegaFor_plus K hK4 (by omega : 2 ≤ m) A hA
  refine ⟨c, hc0, fun v => ?_⟩
  have := hcv v
  rwa [← coe_quadPlus m K] at this

theorem step710Vanish_minus (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement)
    (hZcard : Sec7ZCardStatement) (h56 : Stroth56NatStatement) (hc : Ctx M Q Z B) {n : ℕ}
    {t : G} (hs : Sec7Hyp hc n t) (hnom : ¬ OmegaMinusNat hc t 2) {m : ℕ} (hm3 : 3 ≤ m)
    (hP : OmegaMinusNat hc t m) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hH : ∀ g ∈ M, conjSubgroup g Z0 ≤ LB M Q B → conjSubgroup g Z0 = Z0) {g : G} (hg : g ∈ M)
    (hΓ : ∀ z ∈ Z0, ∀ y ∈ conjSubgroup g Z0, ⁅z, y⁆ ∈ Q) :
    ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅g * t * g⁻¹, v⁆ ∈ Z := by
  obtain ⟨K, fK, finK, hK, b, c, hirr, hnat⟩ := hP
  have hm2 : 2 ≤ m := by omega
  haveI : CharP K 2 := sec7ctr_charP hc hK
  haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have hK4 : 4 ≤ Nat.card K := hK ▸ hc.hyp.q4
  have hnatSO : SpNat hc t ∨ OmegaNat hc t :=
    Or.inr ⟨K, fK, finK, hK, Or.inr ⟨m, b, c, hm2, hirr, hnat⟩⟩
  have h3 : 3 ≤ Module.finrank K (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
      Fintype.card_fin, Fintype.card_fin]
    omega
  refine step710Vanish_generic h34 hRoot h310chi hZc hZV hZcard h56 hc hs hnom hnatSO hK4 hK
    (ElemMatrixIso.minus hm2 hirr) (nondegenerate_polarBilin_quadMinus_of_finite m K hirr) h3
    (addCommutantScalar_statedOmegaMinus hm2 hirr) (fun A hA => ?_)
    (fun x y hx hy hxy => (ElemMatrixIso.minus hm2 hirr).exists_mulVec_eq
      (nondegenerate_polarBilin_quadMinus_of_finite m K hirr)
      (minusPair_orth (K := K) (n := m) (b := b) (c := c) (i := ⟨0, by omega⟩)
        (j := ⟨1, by omega⟩) (fun h => Nat.zero_ne_one (congrArg Fin.val h))) hx hy hxy)
    hnat hZ0 hH hg hΓ
  obtain ⟨c', hc0, hcv⟩ := normalizerOmegaFor_minus K hm2 hirr A hA
  refine ⟨c', hc0, fun v => ?_⟩
  have := hcv v
  rwa [← coe_quadMinus m K b c] at this

theorem step710Vanish_holds (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement)
    (hZcard : Sec7ZCardStatement) (h56 : Stroth56NatStatement) : Step710VanishStatement := by
  intro G _ _ M Q Z B hc n t hs hty Z0 hZ0 hH g hg hΓ
  have hnom : ¬ OmegaMinusNat hc t 2 := not_omegaMinus_two_of_cases (by
    rcases hty with h | h | h
    · exact Or.inl h.1
    · exact Or.inr (Or.inl h.1)
    · exact Or.inr (Or.inr h.1))
  rcases hty with ⟨hMi, -⟩ | ⟨hP3, -⟩ | ⟨hP4, -⟩
  · exact step710Vanish_minus h34 hRoot h310chi hZc hZV hZcard h56 hc hs hnom (m := 3)
      (by norm_num) hMi hZ0 hH hg hΓ
  · exact step710Vanish_plus h34 hRoot h310chi hZc hZV hZcard h56 hc hs hnom (m := 3)
      (by norm_num) hP3 hZ0 hH hg hΓ
  · exact step710Vanish_plus h34 hRoot h310chi hZc hZV hZcard h56 hc hs hnom (m := 4)
      (by norm_num) hP4 hZ0 hH hg hΓ

theorem step710E_of_inputs (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (h77 : Stroth77Statement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement) (hNC : Sec7ConjStatement)
    (hK : Sec7CRWStatement) (hSch : Sec7SchurStatement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (h56 : Stroth56NatStatement) : Step710EStatement :=
  step710E_of_vanish h34 h310chi h77 hZc hZV hNC hK hSch hA hPts h52a h52b
    (step710Vanish_holds h34 hRoot h310chi hZc hZV hZcard h56)

end CFSG.RankThree.GF2n.Stroth80
