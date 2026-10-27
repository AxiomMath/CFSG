module

public import CFSG.LieType.Chevalley.ToralCentralizerQuotient
public import CFSG.LieType.Chevalley.OddRootPairSL2
public import CFSG.LieType.Chevalley.RootDiagonalTorusWords
public import CFSG.LieType.Chevalley.TorusCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenWeyl
public import CFSG.Timmesfeld.Orders.ExceptionalWeylData
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
open scoped Pointwise commutatorElement

theorem eq_one_of_pow_prime_of_zpow {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {x : G}
    (hx : x ^ p = 1) {d : ℤ} (hd : x ^ d = 1) (hpd : ¬ (p : ℤ) ∣ d) : x = 1 := by
  rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hx) with h | h
  · exact orderOf_eq_one_iff.1 h
  · exact absurd (by rw [← h]; exact orderOf_dvd_iff_zpow_eq_one.2 hd) hpd

theorem not_dvd_of_natAbs_lt {p : ℕ} {d : ℤ} (hd0 : d ≠ 0) (hdp : d.natAbs < p) :
    ¬ (p : ℤ) ∣ d := fun h => by
  have h1 : p ∣ d.natAbs := by simpa using Int.natAbs_dvd_natAbs.2 h
  have := Nat.le_of_dvd (Int.natAbs_pos.2 hd0) h1
  omega

theorem five_le_of_prime_of_three_lt {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : 5 ≤ p := by
  by_contra h
  have h4 : p = 4 := by omega
  rw [h4] at hp
  norm_num at hp

theorem fin_G2_cases (j : Fin Tag.G2.rank) : j = g2ia ∨ j = g2ir := by
  revert j; decide

variable {K : Type} [Field K]

theorem rootChar_pi_single {τ : Tag} (a : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    rootChar a (Pi.single i 1) = a i := by
  simpa using rootChar_nsmul_single a i 1

theorem rootChar_neg_eq_inv {τ : Tag} (a : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar a (-v) = (rootChar a v)⁻¹ := by
  rw [← neg_one_zsmul, rootChar_zsmul, zpow_neg_one]

theorem rootChar_pow_of_pow_eq_one {τ : Tag} {a : Fin τ.rank → Kˣ} {p : ℕ} (hap : a ^ p = 1)
    (v : Fin τ.rank → ℤ) : rootChar a v ^ p = 1 := by
  rw [rootChar, ← Finset.prod_pow]
  refine Finset.prod_eq_one fun i _ => ?_
  have hi : a i ^ p = 1 := by simpa using congrFun hap i
  rw [← zpow_natCast (a i ^ v i) p, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hi, one_zpow]

theorem zpow_det_eq_one_of_rootChar {a : Fin Tag.G2.rank → Kˣ} {x y : Fin Tag.G2.rank → ℤ}
    (hx : rootChar a x = 1) (hy : rootChar a y = 1) (i : Fin Tag.G2.rank) :
    a i ^ (x g2ia * y g2ir - x g2ir * y g2ia) = 1 := by
  have hcomb : ∀ m n : ℤ, rootChar a (m • x + n • y) = 1 := fun m n => by
    rw [rootChar_add, rootChar_zsmul, rootChar_zsmul, hx, hy, one_zpow, one_zpow, mul_one]
  rw [← rootChar_pi_single a i, ← rootChar_zsmul]
  rcases fin_G2_cases i with rfl | rfl
  · convert hcomb (y g2ir) (-x g2ir) using 2
    funext j
    rcases fin_G2_cases j with rfl | rfl <;> simp [g2ia, g2ir] <;> ring
  · convert hcomb (-y g2ia) (x g2ia) using 2
    funext j
    rcases fin_G2_cases j with rfl | rfl <;> simp [g2ia, g2ir] <;> ring

theorem eq_one_of_rootChar_det {p : ℕ} (hp : p.Prime) {a : Fin Tag.G2.rank → Kˣ}
    (hap : a ^ p = 1) {x y : Fin Tag.G2.rank → ℤ} (hx : rootChar a x = 1) (hy : rootChar a y = 1)
    (hd : ¬ (p : ℤ) ∣ (x g2ia * y g2ir - x g2ir * y g2ia)) : a = 1 := by
  funext i
  exact eq_one_of_pow_prime_of_zpow hp (by rw [← Pi.pow_apply, hap, Pi.one_apply])
    (zpow_det_eq_one_of_rootChar hx hy i) hd

theorem g2RootPairs_det_check : ∀ u ∈ g2RootPairs, ∀ v ∈ g2RootPairs, v = u ∨ v = -u ∨
    u.1 * v.2 - u.2 * v.1 ∈ ([1, 2, 3, -1, -2, -3] : List ℤ) := by
  decide

theorem G2_roots_eq_or_det {α β : Fin Tag.G2.rank → ℤ} (hα : IsRoot .G2 α) (hβ : IsRoot .G2 β) :
    β = α ∨ β = -α ∨
      α g2ia * β g2ir - α g2ir * β g2ia ∈ ([1, 2, 3, -1, -2, -3] : List ℤ) := by
  rcases g2RootPairs_det_check _ (g2Pair_mem_of_isRoot hα) _ (g2Pair_mem_of_isRoot hβ) with
    h | h | h
  · exact Or.inl (g2Pair_injective h)
  · exact Or.inr (Or.inl (g2Pair_injective (h.trans (g2Pair_neg α).symm)))
  · exact Or.inr (Or.inr h)

theorem rootCharKernel_G2_cases {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {a : Fin Tag.G2.rank → Kˣ}
    (hap : a ^ p = 1) (ha1 : a ≠ 1) :
    rootCharKernel a = ∅ ∨ ∃ α, IsRoot .G2 α ∧ rootCharKernel a = {α, -α} := by
  have key : ∀ α ∈ rootCharKernel a, ∀ β ∈ rootCharKernel a, β = α ∨ β = -α := by
    intro α hα β hβ
    rcases G2_roots_eq_or_det hα.1 hβ.1 with h | h | hdet
    · exact Or.inl h
    · exact Or.inr h
    · refine absurd (eq_one_of_rootChar_det hp hap hα.2 hβ.2 ?_) ha1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hdet
      rcases hdet with h | h | h | h | h | h <;> rw [h] <;>
        exact not_dvd_of_natAbs_lt (by norm_num) (by norm_num; omega)
  by_cases hne : (rootCharKernel a).Nonempty
  · obtain ⟨α, hα⟩ := hne
    refine Or.inr ⟨α, hα.1, ?_⟩
    have hneg : -α ∈ rootCharKernel a :=
      ⟨IsRoot.neg hα.1, by rw [rootChar_neg_eq_inv, hα.2, inv_one]⟩
    ext β
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · exact key α hα β
    · rintro (rfl | rfl)
      · exact hα
      · exact hneg
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.1 hne)

theorem weyl_G2_ext {w w' : WeylGroup .G2} (h1 : w • g2a = w' • g2a) (h2 : w • g2r = w' • g2r) :
    w = w' :=
  ext_single fun j => by
    rcases fin_G2_cases j with rfl | rfl
    · rw [← g2a_eq_single]; exact h1
    · rw [← g2r_eq_single]; exact h2

theorem rootCharStabilizer_le_kernelReflectionGroup_G2 {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {a : Fin Tag.G2.rank → Kˣ} (hap : a ^ p = 1) (ha1 : a ≠ 1) :
    rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a := by
  have hp5 := five_le_of_prime_of_three_lt hp hp3
  intro w hw
  have hw' : ∀ v, rootChar a (w • v) = rootChar a v := hw
  have hrot : ∀ X Y : Fin Tag.G2.rank → ℤ, w • g2a = X → w • g2r = Y →
      ¬ (p : ℤ) ∣ ((X - g2a) g2ia * (Y - g2r) g2ir - (X - g2a) g2ir * (Y - g2r) g2ia) →
        w ∈ kernelReflectionGroup a := by
    intro X Y hX hY hd
    refine absurd (eq_one_of_rootChar_det hp hap ?_ ?_ hd) ha1
    · rw [rootChar_sub, ← hX, hw', mul_inv_cancel]
    · rw [rootChar_sub, ← hY, hw', mul_inv_cancel]
  have hrefl : ∀ (g : WeylGroup .G2) (i : Fin Tag.G2.rank), w = g * simple .G2 i * g⁻¹ →
      w ∈ kernelReflectionGroup a := by
    intro g i hwg
    refine Subgroup.subset_closure ⟨g, i, ⟨IsRoot.smul (isRoot_single _ i) g, ?_⟩, hwg⟩
    have hwα : w • (g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)) =
        -(g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)) := by
      rw [hwg, mul_smul, mul_smul, inv_smul_smul, simple_smul, reflect_single_self, smul_neg]
    have h1 : (rootChar a (g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)))⁻¹ =
        rootChar a (g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)) := by
      rw [← rootChar_neg_eq_inv, ← hwα, hw']
    have h2 : rootChar a (g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)) ^ (2 : ℤ) = 1 := by
      rw [zpow_two]
      calc _ = (rootChar a (g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)))⁻¹ *
            rootChar a (g • (Pi.single i 1 : Fin Tag.G2.rank → ℤ)) := by rw [h1]
        _ = 1 := inv_mul_cancel _
    exact eq_one_of_pow_prime_of_zpow hp (rootChar_pow_of_pow_eq_one hap _) h2
      (not_dvd_of_natAbs_lt (by norm_num) (by norm_num; omega))
  have hinv : ∀ i : Fin Tag.G2.rank, (simple .G2 i)⁻¹ = simple .G2 i :=
    (coxeterSystem .G2).inv_simple
  rcases g2_weyl_cases w with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  ·
    have hw1 : w = 1 := weyl_G2_ext (by rw [h1, one_smul]) (by rw [h2, one_smul])
    rw [hw1]
    exact one_mem _
  ·
    refine hrefl 1 g2ia (weyl_G2_ext ?_ ?_)
    · rw [h1, one_mul, inv_one, mul_one, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2, one_mul, inv_one, mul_one, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  ·
    refine hrefl 1 g2ir (weyl_G2_ext ?_ ?_)
    · rw [h1, one_mul, inv_one, mul_one, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2, one_mul, inv_one, mul_one, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  · exact hrot _ _ h1 h2 (by
      rw [show (g2c - g2a) g2ia * (-g2u - g2r) g2ir - (g2c - g2a) g2ir * (-g2u - g2r) g2ia = 1
        by decide]
      exact not_dvd_of_natAbs_lt (by norm_num) (by norm_num; omega))
  · exact hrot _ _ h1 h2 (by
      rw [show (-g2b - g2a) g2ia * (g2v - g2r) g2ir - (-g2b - g2a) g2ir * (g2v - g2r) g2ia = 1
        by decide]
      exact not_dvd_of_natAbs_lt (by norm_num) (by norm_num; omega))
  ·
    refine hrefl (simple .G2 g2ia) g2ir (weyl_G2_ext ?_ ?_)
    · rw [h1, hinv, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2, hinv, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  ·
    refine hrefl (simple .G2 g2ir) g2ia (weyl_G2_ext ?_ ?_)
    · rw [h1, hinv, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2, hinv, mul_smul, mul_smul, simple_smul, simple_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  · exact hrot _ _ h1 h2 (by
      rw [show (-g2c - g2a) g2ia * (g2u - g2r) g2ir - (-g2c - g2a) g2ir * (g2u - g2r) g2ia = 3
        by decide]
      exact not_dvd_of_natAbs_lt (by norm_num) (by norm_num; omega))
  · exact hrot _ _ h1 h2 (by
      rw [show (g2b - g2a) g2ia * (-g2v - g2r) g2ir - (g2b - g2a) g2ir * (-g2v - g2r) g2ia = 3
        by decide]
      exact not_dvd_of_natAbs_lt (by norm_num) (by norm_num; omega))
  ·
    refine hrefl (simple .G2 g2ia * simple .G2 g2ir) g2ia (weyl_G2_ext ?_ ?_)
    · rw [h1]
      simp only [mul_inv_rev, hinv, mul_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2]
      simp only [mul_inv_rev, hinv, mul_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  ·
    refine hrefl (simple .G2 g2ir * simple .G2 g2ia) g2ir (weyl_G2_ext ?_ ?_)
    · rw [h1]
      simp only [mul_inv_rev, hinv, mul_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
    · rw [h2]
      simp only [mul_inv_rev, hinv, mul_smul, simple_smul]
      exact List.ofFn_injective (by decide +kernel)
  · exact hrot _ _ h1 h2 (by
      rw [show (-g2a - g2a) g2ia * (-g2r - g2r) g2ir - (-g2a - g2a) g2ir * (-g2r - g2r) g2ia = 4
        by decide]
      exact not_dvd_of_natAbs_lt (by norm_num) (by norm_num; omega))

theorem exists_eq_HSL_of_conj {A : SL2 K} {c c' : K}
    (hu : A * uSL 1 * A⁻¹ = uSL c) (hv : A * vSL 1 * A⁻¹ = vSL c') : ∃ t : Kˣ, A = HSL t := by
  have h10 := congrArg (fun M : SL2 K => (M : Matrix (Fin 2) (Fin 2) K) 1 0) hu
  have h01 := congrArg (fun M : SL2 K => (M : Matrix (Fin 2) (Fin 2) K) 0 1) hv
  simp [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, coe_uSL, coe_vSL,
    Matrix.mul_apply, Fin.sum_univ_two] at h10 h01
  have hc0 : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 :=
    (pow_eq_zero_iff two_ne_zero).1 (by linear_combination -h10)
  have hb0 : (A : Matrix (Fin 2) (Fin 2) K) 0 1 = 0 :=
    (pow_eq_zero_iff two_ne_zero).1 (by linear_combination -h01)
  have ha := SL2_apply_zero_zero_ne_zero hc0
  have hdet := det_SL2 A
  rw [hc0, hb0, mul_zero, sub_zero] at hdet
  refine ⟨Units.mk0 _ ha, SL2_ext ?_ ?_ ?_ ?_⟩ <;> simp [coe_HSL, hc0, hb0]
  exact eq_inv_of_mul_eq_one_right hdet

theorem toralCentralizer_eq_toralRootGroup_of_le {τ : Tag} {a : Fin τ.rank → Kˣ}
    (h : rootCharStabilizerSubgroup a ≤ kernelReflectionGroup a) :
    toralCentralizer τ K a = toralRootGroup τ K a := by
  obtain ⟨hMX, -, -, -, φ, hφ, -⟩ := Chevalley_toral_centralizer_root_generated_quotient τ K a
  refine le_antisymm (fun x hx => ?_) hMX
  obtain ⟨q, hq⟩ := hφ (QuotientGroup.mk ⟨x, hx⟩)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  have hw1 : (QuotientGroup.mk w : rootCharStabilizerSubgroup a ⧸
      (kernelReflectionGroup a).subgroupOf (rootCharStabilizerSubgroup a)) = 1 :=
    (QuotientGroup.eq_one_iff w).2 (Subgroup.mem_subgroupOf.2 (h w.2))
  rw [hw1, map_one] at hq
  exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hq.symm)

theorem map_conj_rootSubgroup_of_mem_torusGroup {τ : Tag} {t : ModGL τ K}
    (ht : t ∈ torusGroup τ K) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (rootSubgroup τ K α).map (MulAut.conj t).toMonoidHom = rootSubgroup τ K α := by
  obtain ⟨b, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  exact map_conj_rootDiagUnit_rootSubgroup b hα

theorem conj_mem_rootSubgroup_of_mem_torusGroup {τ : Tag} {t : ModGL τ K}
    (ht : t ∈ torusGroup τ K) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {x : ModGL τ K}
    (hx : x ∈ rootSubgroup τ K α) : t * x * t⁻¹ ∈ rootSubgroup τ K α := by
  rw [← map_conj_rootSubgroup_of_mem_torusGroup ht hα]
  exact ⟨x, hx, rfl⟩

theorem map_conj_rootPair_of_mem_torusGroup {τ : Tag} {t : ModGL τ K}
    (ht : t ∈ torusGroup τ K) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    (rootSubgroup τ K α ⊔ rootSubgroup τ K (-α)).map (MulAut.conj t).toMonoidHom =
      rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) := by
  rw [Subgroup.map_sup, map_conj_rootSubgroup_of_mem_torusGroup ht hα,
    map_conj_rootSubgroup_of_mem_torusGroup ht (IsRoot.neg hα)]

theorem conj_mem_rootPair_of_mem_torusGroup {τ : Tag} {t : ModGL τ K}
    (ht : t ∈ torusGroup τ K) {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {x : ModGL τ K}
    (hx : x ∈ rootSubgroup τ K α ⊔ rootSubgroup τ K (-α)) :
    t * x * t⁻¹ ∈ rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) := by
  rw [← map_conj_rootPair_of_mem_torusGroup ht hα]
  exact ⟨x, hx, rfl⟩

theorem torusGroup_le_normalizer_rootPair {τ : Tag} {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) :
    torusGroup τ K ≤ Subgroup.normalizer
      ((rootSubgroup τ K α ⊔ rootSubgroup τ K (-α) : Subgroup (ModGL τ K)) :
        Set (ModGL τ K)) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff_conj_image_eq]
  have h := congrArg SetLike.coe (map_conj_rootPair_of_mem_torusGroup ht hα (K := K))
  rw [Subgroup.coe_map] at h
  exact h

theorem mem_torusGroup_of_conj_rootSubgroups {τ : Tag} (hK : ringChar K ≠ 2)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) {u : ModGL τ K}
    (hu : u ∈ rootSubgroup τ K α ⊔ rootSubgroup τ K (-α))
    (hup : ∀ x ∈ rootSubgroup τ K α, u * x * u⁻¹ ∈ rootSubgroup τ K α)
    (hdown : ∀ x ∈ rootSubgroup τ K (-α), u * x * u⁻¹ ∈ rootSubgroup τ K (-α)) :
    u ∈ torusGroup τ K := by
  obtain ⟨w, i, hw⟩ := isRoot_iff_exists_smul_single.1 hα
  obtain ⟨e, he⟩ := exists_mulEquiv_rootSubgroup_sup hK hw
  set n := canonicalRep (coxeterSystem τ) K w
  set A := e.symm ⟨u, hu⟩
  have huA : u = n * simpleRootSL2 τ K i A * n⁻¹ := by
    have h := he A
    rw [show e A = ⟨u, hu⟩ from e.apply_symm_apply _] at h
    exact h
  have hUα : rootSubgroup τ K α =
      (rootSubgroup τ K (Pi.single i 1)).map (MulAut.conj n).toMonoidHom := by
    rw [(canonical_weyl_root_transport τ K).2.1 w _ (isRoot_single τ i), hw]
  have hUnα : rootSubgroup τ K (-α) =
      (rootSubgroup τ K (-Pi.single i 1)).map (MulAut.conj n).toMonoidHom := by
    rw [(canonical_weyl_root_transport τ K).2.1 w _ (isRoot_neg_single τ i), smul_neg, hw]
  have memα : ∀ x, x ∈ rootSubgroup τ K α ↔ ∃ c, n * xUnit τ K i c * n⁻¹ = x := by
    intro x
    rw [hUα, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hy
      exact ⟨c, by rw [pinnedX_single]; rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨xUnit τ K i c, mem_rootSubgroup.2 ⟨c, pinnedX_single τ K i c⟩, rfl⟩
  have memnα : ∀ x, x ∈ rootSubgroup τ K (-α) ↔ ∃ c, n * yUnit τ K i c * n⁻¹ = x := by
    intro x
    rw [hUnα, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hy
      exact ⟨c, by rw [pinnedX_neg_single]; rfl⟩
    · rintro ⟨c, rfl⟩
      exact ⟨yUnit τ K i c, mem_rootSubgroup.2 ⟨c, pinnedX_neg_single τ K i c⟩, rfl⟩
  have hinj := simpleRootSL2_injective hK i
  have hconj : ∀ X : ModGL τ K, u * (n * X * n⁻¹) * u⁻¹ =
      n * (simpleRootSL2 τ K i A * X * (simpleRootSL2 τ K i A)⁻¹) * n⁻¹ := fun X => by
    rw [huA]
    group
  have hcancel : ∀ X Y : ModGL τ K, n * X * n⁻¹ = n * Y * n⁻¹ → X = Y := fun X Y h => by
    simpa using h
  obtain ⟨c, hc⟩ := (memα _).1 (hup _ ((memα _).2 ⟨1, rfl⟩))
  obtain ⟨c', hc'⟩ := (memnα _).1 (hdown _ ((memnα _).2 ⟨1, rfl⟩))
  rw [hconj] at hc hc'
  have hAu : A * uSL 1 * A⁻¹ = uSL c := hinj (by
    rw [map_mul, map_mul, map_inv, simpleRootSL2_uSL, simpleRootSL2_uSL]
    exact (hcancel _ _ hc).symm)
  have hAv : A * vSL 1 * A⁻¹ = vSL c' := hinj (by
    rw [map_mul, map_mul, map_inv, simpleRootSL2_vSL, simpleRootSL2_vSL]
    exact (hcancel _ _ hc').symm)
  obtain ⟨t, ht⟩ := exists_eq_HSL_of_conj hAu hAv
  rw [huA, ht, simpleRootSL2_HSL]
  exact (Subgroup.mem_normalizer_iff.1 ((canonical_weyl_root_transport τ K).2.2 w) _).1
    (torusElt_mem_torusGroup i t)

theorem comm_and_two_generated_of_injective {M G : Type*} [CommGroup M] [IsCyclic M] [Group G]
    (ι : G →* (Fin Tag.G2.rank → M)) (hι : Function.Injective ι) :
    (∀ x y : G, x * y = y * x) ∧ ∃ x y : G, Subgroup.closure {x, y} = ⊤ := by
  refine ⟨fun x y => hι (by rw [map_mul, map_mul, mul_comm]), ?_⟩
  set f : G →* M := (Pi.evalMonoidHom (fun _ => M) g2ir).comp ι
  set f₀ : G →* M := (Pi.evalMonoidHom (fun _ => M) g2ia).comp ι
  obtain ⟨⟨m, x₀, rfl⟩, hm⟩ := IsCyclic.exists_generator (α := f.range)
  have hinj₀ : Function.Injective (f₀.comp f.ker.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨g, hg⟩ hg0
    rw [MonoidHom.mem_ker] at hg hg0
    rw [Subgroup.mem_bot]
    refine Subtype.ext (hι ?_)
    funext j
    rcases fin_G2_cases j with rfl | rfl
    · simpa [f₀] using hg0
    · simpa [f] using hg
  have : IsCyclic f.ker := isCyclic_of_injective _ hinj₀
  obtain ⟨⟨y₀, hy₀⟩, hy⟩ := IsCyclic.exists_generator (α := f.ker)
  refine ⟨x₀, y₀, eq_top_iff.2 fun g _ => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hm ⟨f g, g, rfl⟩)
  have hk' : f (g * x₀ ^ (-k)) = 1 := by
    have := congrArg Subtype.val hk
    simp only [SubgroupClass.coe_zpow] at this
    rw [map_mul, map_zpow, ← this, zpow_neg, mul_inv_cancel]
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hy ⟨_, hk'⟩)
  have hj' : y₀ ^ j = g * x₀ ^ (-k) := by
    have := congrArg Subtype.val hj
    simpa only [SubgroupClass.coe_zpow] using this
  have hg : g = y₀ ^ j * x₀ ^ k := by
    rw [hj', zpow_neg, inv_mul_cancel_right]
  have hx₀ : x₀ ∈ Subgroup.closure ({x₀, y₀} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have hy₀' : y₀ ∈ Subgroup.closure ({x₀, y₀} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  rw [hg]
  exact mul_mem (zpow_mem hy₀' _) (zpow_mem hx₀ _)

theorem exists_conj_map_le_of_not_dvd_index {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} (hH : ¬ p ∣ H.index) {P : Subgroup G} (hP : IsPGroup p P) :
    ∃ g : G, P.map (MulAut.conj g).toMonoidHom ≤ H := by
  obtain ⟨S₀⟩ : Nonempty (Sylow p H) := inferInstance
  set S := (S₀ : Subgroup H).map H.subtype
  have hS : IsPGroup p S := S₀.isPGroup'.map H.subtype
  have hSi : ¬ p ∣ S.index := by
    rw [Subgroup.index_map_subtype]
    exact fun h => ((Fact.out : p.Prime).dvd_mul.1 h).elim S₀.not_dvd_index hH
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q (hS.toSylow hSi)
  refine ⟨g, ?_⟩
  calc P.map (MulAut.conj g).toMonoidHom ≤ (Q : Subgroup G).map (MulAut.conj g).toMonoidHom :=
        Subgroup.map_mono hPQ
    _ = S := by
        have h := congrArg (fun T : Sylow p G => (T : Subgroup G)) hg
        simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h
        rw [← h, Subgroup.pointwise_smul_def]
        rfl
    _ ≤ H := Subgroup.map_subtype_le _

theorem not_dvd_index_torusGroup_G2 [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : p ∣ Nat.card K - 1) :
    ¬ p ∣ ((torusGroup .G2 K).subgroupOf (adjointGroup .G2 K)).index := by
  classical
  have : Fintype (WeylGroup .G2) := Fintype.ofFinite _
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hcard := (torusGroup .G2 K).subgroupOf (adjointGroup .G2 K) |>.card_mul_index
  have hTC : torusGroup .G2 K ≤ adjointGroup .G2 K := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, t⟩, rfl⟩
    exact torusElt_mem_adjointGroup i t
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv,
    card_adjointGroup, finsum_eq_sum_of_fintype, sum_length_G2, mul_assoc] at hcard
  have hidx := Nat.eq_of_mul_eq_mul_left Nat.card_pos hcard
  have hqp : (Nat.card K : ZMod p) = 1 := by
    have h := (ZMod.natCast_eq_zero_iff (Nat.card K - 1) p).2 hpq
    rwa [Nat.cast_sub hq1, Nat.cast_one, sub_eq_zero] at h
  intro hdvd
  have h0 := (ZMod.natCast_eq_zero_iff _ p).2 hdvd
  rw [hidx] at h0
  simp only [geomSum, Nat.cast_mul, Nat.cast_pow, Nat.cast_sum, hqp, one_pow, Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one, one_mul] at h0
  have h12 : ((12 : ℕ) : ZMod p) = 0 := by
    rw [show (12 : ℕ) = 2 * 6 from rfl, Nat.cast_mul]
    exact_mod_cast h0
  have hp12 := (ZMod.natCast_eq_zero_iff 12 p).1 h12
  have := Nat.le_of_dvd (by norm_num) hp12
  interval_cases p <;> first | (norm_num at hp; done) | norm_num at hp12

theorem orderOf_rootDiagUnit {τ : Tag} (a : Fin τ.rank → Kˣ) :
    orderOf (rootDiagUnit τ a) = orderOf a :=
  orderOf_injective (rootDiagUnitHom τ K) rootDiagUnit_injective a

theorem toral_centralizer_cases_G2 (K : Type) [Field K] [Finite K]
    (hK : Odd (Nat.card K)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K - 1)
    (a : Fin Tag.G2.rank → Kˣ) (ha : orderOf (rootDiagUnit .G2 a) = p) :
      Xor
        (rootCharKernel a = ∅ ∧ toralCentralizer .G2 K a = torusGroup .G2 K ∧
          ∀ S : Sylow 2 (toralCentralizer .G2 K a),
            (∀ x y : S, x * y = y * x) ∧ ∃ x y : S, Subgroup.closure {x, y} = ⊤)
        (∃ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α ∧ rootCharKernel a = {α, -α} ∧
          toralCentralizer .G2 K a =
            torusGroup .G2 K ⊔ (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α)) ∧
          (toralCentralizer .G2 K a : Set (ModGL .G2 K)) =
            (torusGroup .G2 K : Set (ModGL .G2 K)) *
              ((rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) : Subgroup (ModGL .G2 K)) :
                Set (ModGL .G2 K)) ∧
          Nonempty (SL2 K ≃* (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) :
            Subgroup (ModGL .G2 K))) ∧
          CFSG.IsQuasisimple (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) :
            Subgroup (ModGL .G2 K)) ∧
          ⁅toralCentralizer .G2 K a, toralCentralizer .G2 K a⁆ =
            rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) ∧
          toralCentralizer .G2 K a ⊓ Subgroup.centralizer
              ((rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) : Subgroup (ModGL .G2 K)) :
                Set (ModGL .G2 K)) =
            (Subgroup.center (toralCentralizer .G2 K a)).map
              (toralCentralizer .G2 K a).subtype ∧
          (Subgroup.center (toralCentralizer .G2 K a)).map (toralCentralizer .G2 K a).subtype ≤
            torusGroup .G2 K ∧
          ∀ S : Sylow 2 (Subgroup.center (toralCentralizer .G2 K a)),
            (∀ x y : S, x * y = y * x) ∧ ∃ x y : S, Subgroup.closure {x, y} = ⊤) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hp5 := five_le_of_prime_of_three_lt hp hp3
  have hK2 : ringChar K ≠ 2 := fun h => by
    have := FiniteField.even_card_iff_char_two.1 h
    rw [← Nat.card_eq_fintype_card] at this
    exact (Nat.not_even_iff_odd.2 hK) (Nat.even_iff.2 this)
  have hq5 : 5 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    have := Nat.le_of_dvd (by omega) hpq
    omega
  obtain ⟨e, -⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) K
  have hTcomm := (triangular_borel_structure.{0, 0} .G2 K).1
  have hoa : orderOf a = p := by rw [← orderOf_rootDiagUnit (K := K), ha]
  have hap : a ^ p = 1 := hoa ▸ pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := fun h => by
    rw [h, orderOf_one] at hoa
    exact hp.one_lt.ne hoa
  have hX := toralCentralizer_eq_toralRootGroup_of_le (K := K)
    (rootCharStabilizer_le_kernelReflectionGroup_G2 hp hp3 hap ha1)
  set X := toralCentralizer .G2 K a with hXdef
  rcases rootCharKernel_G2_cases hp hp3 hap ha1 with hker | ⟨α, hα, hker⟩
  ·
    have hXT : X = torusGroup .G2 K := by
      rw [hX, toralRootGroup, hker]
      simp [rootSpan]
    refine Or.inl ⟨⟨hker, hXT, fun S => ?_⟩, ?_⟩
    · exact comm_and_two_generated_of_injective
        (e.symm.toMonoidHom.comp ((Subgroup.inclusion hXT.le).comp (S : Subgroup X).subtype))
        (e.symm.injective.comp ((Subgroup.inclusion_injective hXT.le).comp
          (S : Subgroup X).subtype_injective))
    · rintro ⟨β, -, hβ, -⟩
      exact (Set.insert_nonempty β {-β}).ne_empty (hβ.symm.trans hker)
  ·
    set Q : Subgroup (ModGL .G2 K) := rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) with hQdef
    have hXQ : X = torusGroup .G2 K ⊔ Q := by
      rw [hX, toralRootGroup, hker, rootSpan, iSup_insert, iSup_singleton]
    have hXset : (X : Set (ModGL .G2 K)) = (torusGroup .G2 K : Set (ModGL .G2 K)) * Q := by
      rw [hXQ]
      exact Subgroup.coe_mul_of_left_le_normalizer_right _ _ (torusGroup_le_normalizer_rootPair hα)
    have hQX : Q ≤ X := hXQ ▸ le_sup_right
    obtain ⟨-, ⟨eQ⟩, -, hfin⟩ := odd_arbitrary_root_pair_SL2_p_components .G2 K hK2 hα
    have hquasi : CFSG.IsQuasisimple Q := (hfin.2 hq5).1
    have hperf : ⁅Q, Q⁆ = Q := Subgroup.isPerfect_iff.1 hquasi.1
    have hcomm : ⁅X, X⁆ = Q := by
      refine le_antisymm ?_ (hperf ▸ Subgroup.commutator_mono hQX hQX)
      rw [Subgroup.commutator_le]
      intro x hx y hy
      rw [← SetLike.mem_coe, hXset] at hx hy
      obtain ⟨h, hh, q, hq, rfl⟩ := hx
      obtain ⟨h', hh', q', hq', rfl⟩ := hy
      have e1 : ⁅h * q, h' * q'⁆ = (h * h') * (h'⁻¹ * q * h' * (q' * q⁻¹)) * (h' * h)⁻¹ *
          (h' * q'⁻¹ * h'⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [e1, ← hTcomm h hh h' hh']
      refine mul_mem (conj_mem_rootPair_of_mem_torusGroup (mul_mem hh hh') hα (mul_mem ?_
        (mul_mem hq' (inv_mem hq)))) (conj_mem_rootPair_of_mem_torusGroup hh' hα (inv_mem hq'))
      have := conj_mem_rootPair_of_mem_torusGroup (inv_mem hh') hα hq
      rwa [inv_inv] at this
    have hCT : X ⊓ Subgroup.centralizer (Q : Set (ModGL .G2 K)) ≤ torusGroup .G2 K := by
      intro z hz
      obtain ⟨hzX, hzC⟩ := Subgroup.mem_inf.1 hz
      have hzX' : z ∈ (X : Set (ModGL .G2 K)) := hzX
      rw [hXset] at hzX'
      obtain ⟨h, hh, u, hu, rfl⟩ := hzX'
      have hcz : ∀ x ∈ Q, (h * u) * x * (h * u)⁻¹ = x := fun x hx => by
        rw [← Subgroup.mem_centralizer_iff.1 hzC x hx, mul_inv_cancel_right]
      have hconj : ∀ x ∈ Q, u * x * u⁻¹ = h⁻¹ * x * h⁻¹⁻¹ := fun x hx => by
        have e2 : u * x * u⁻¹ = h⁻¹ * ((h * u) * x * (h * u)⁻¹) * h⁻¹⁻¹ := by group
        rw [e2, hcz x hx]
      have hup : ∀ x ∈ rootSubgroup .G2 K α, u * x * u⁻¹ ∈ rootSubgroup .G2 K α := fun x hx => by
        rw [hconj x (Subgroup.mem_sup_left hx)]
        exact conj_mem_rootSubgroup_of_mem_torusGroup (inv_mem hh) hα hx
      have hdown : ∀ x ∈ rootSubgroup .G2 K (-α), u * x * u⁻¹ ∈ rootSubgroup .G2 K (-α) :=
        fun x hx => by
          rw [hconj x (Subgroup.mem_sup_right hx)]
          exact conj_mem_rootSubgroup_of_mem_torusGroup (inv_mem hh) (IsRoot.neg hα) hx
      exact mul_mem hh (mem_torusGroup_of_conj_rootSubgroups hK2 hα hu hup hdown)
    have hZ : X ⊓ Subgroup.centralizer (Q : Set (ModGL .G2 K)) =
        (Subgroup.center X).map X.subtype := by
      refine le_antisymm ?_ ?_
      · intro z hz
        obtain ⟨hzX, hzC⟩ := Subgroup.mem_inf.1 hz
        have hzT := hCT hz
        have hle : X ≤ Subgroup.centralizer {z} := by
          rw [hXQ]
          refine sup_le (fun t ht => ?_) (fun x hx => ?_)
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact (hTcomm z hzT t ht).symm
          · rw [Subgroup.mem_centralizer_singleton_iff]
            exact Subgroup.mem_centralizer_iff.1 hzC x hx
        refine ⟨⟨z, hzX⟩, Subgroup.mem_center_iff.2 fun g => Subtype.ext ?_, rfl⟩
        exact Subgroup.mem_centralizer_singleton_iff.1 (hle g.2)
      · rintro _ ⟨z, hz, rfl⟩
        refine ⟨z.2, Subgroup.mem_centralizer_iff.2 fun x hx => ?_⟩
        exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨x, hQX hx⟩)
    have hZT : (Subgroup.center X).map X.subtype ≤ torusGroup .G2 K := hZ ▸ hCT
    set ιZ : Subgroup.center X →* torusGroup .G2 K :=
      MonoidHom.codRestrict (X.subtype.comp (Subgroup.center X).subtype) (torusGroup .G2 K)
        (fun z => hZT ⟨z, z.2, rfl⟩)
    have hιZ : Function.Injective ιZ := fun z z' h => by
      have h' := congrArg Subtype.val h
      exact Subtype.ext (Subtype.ext h')
    refine Or.inr ⟨⟨α, hα, hker, hXQ, hXset, ⟨eQ⟩, hquasi, hcomm, hZ, hZT, fun S => ?_⟩, ?_⟩
    · exact comm_and_two_generated_of_injective
        (e.symm.toMonoidHom.comp (ιZ.comp (S : Subgroup (Subgroup.center X)).subtype))
        (e.symm.injective.comp (hιZ.comp (S : Subgroup (Subgroup.center X)).subtype_injective))
    · rintro ⟨hker', -⟩
      exact (Set.insert_nonempty α {-α}).ne_empty (hker.symm.trans hker')

theorem odd_G2_split_prime_toral_Sylow_and_centralizers (K : Type) [Field K] [Finite K]
    (hK : Odd (Nat.card K)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (hpq : p ∣ Nat.card K - 1) :
    (∀ P : Subgroup (adjointGroup .G2 K), IsPGroup p P →
      ∃ g : adjointGroup .G2 K, P.map (MulAut.conj g).toMonoidHom ≤
        (torusGroup .G2 K).subgroupOf (adjointGroup .G2 K)) ∧
    Nonempty ((Fin Tag.G2.rank → Kˣ) ≃* torusGroup .G2 K) ∧
    (∀ a : Fin Tag.G2.rank → Kˣ, rootDiagUnit .G2 a ∈ torusGroup .G2 K) ∧
    (∀ h ∈ torusGroup .G2 K, ∃! a : Fin Tag.G2.rank → Kˣ, rootDiagUnit .G2 a = h) ∧
    ∀ a : Fin Tag.G2.rank → Kˣ, orderOf (rootDiagUnit .G2 a) = p →
      Xor
        (rootCharKernel a = ∅ ∧ toralCentralizer .G2 K a = torusGroup .G2 K ∧
          ∀ S : Sylow 2 (toralCentralizer .G2 K a),
            (∀ x y : S, x * y = y * x) ∧ ∃ x y : S, Subgroup.closure {x, y} = ⊤)
        (∃ α : Fin Tag.G2.rank → ℤ, IsRoot .G2 α ∧ rootCharKernel a = {α, -α} ∧
          toralCentralizer .G2 K a =
            torusGroup .G2 K ⊔ (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α)) ∧
          (toralCentralizer .G2 K a : Set (ModGL .G2 K)) =
            (torusGroup .G2 K : Set (ModGL .G2 K)) *
              ((rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) : Subgroup (ModGL .G2 K)) :
                Set (ModGL .G2 K)) ∧
          Nonempty (SL2 K ≃* (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) :
            Subgroup (ModGL .G2 K))) ∧
          CFSG.IsQuasisimple (rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) :
            Subgroup (ModGL .G2 K)) ∧
          ⁅toralCentralizer .G2 K a, toralCentralizer .G2 K a⁆ =
            rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) ∧
          toralCentralizer .G2 K a ⊓ Subgroup.centralizer
              ((rootSubgroup .G2 K α ⊔ rootSubgroup .G2 K (-α) : Subgroup (ModGL .G2 K)) :
                Set (ModGL .G2 K)) =
            (Subgroup.center (toralCentralizer .G2 K a)).map
              (toralCentralizer .G2 K a).subtype ∧
          (Subgroup.center (toralCentralizer .G2 K a)).map (toralCentralizer .G2 K a).subtype ≤
            torusGroup .G2 K ∧
          ∀ S : Sylow 2 (Subgroup.center (toralCentralizer .G2 K a)),
            (∀ x y : S, x * y = y * x) ∧ ∃ x y : S, Subgroup.closure {x, y} = ⊤) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (Module.End K (RootModule .G2 K)) := Module.finite_of_finite K
  obtain ⟨e, -⟩ := G2_F4_torus_coordinates .G2 (Or.inl rfl) K
  obtain ⟨⟨B, hB, -⟩, hdiag⟩ := G2_F4_root_character_diagonals_inner .G2 (Or.inl rfl) K
  refine ⟨fun P hP =>
      exists_conj_map_le_of_not_dvd_index (not_dvd_index_torusGroup_G2 hp hp3 hpq) hP,
    ⟨e⟩, fun a => (hdiag B hB a).2.1, fun h hh => ?_,
    fun a ha => toral_centralizer_cases_G2 K hK hp hp3 hpq a ha⟩
  obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  exact ⟨l, hl.symm, fun b hb => rootDiagUnit_injective (hb.trans hl)⟩

end CFSG.RankThree.Chevalley
