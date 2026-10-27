module

public import CFSG.RankThree.GF2n.Parrott.Section2ClassCover
public import CFSG.RankThree.GF2n.Parrott.Section2Cases
public import CFSG.RankThree.GF2n.Parrott.Lemma15
public import CFSG.RankThree.GF2n.Parrott.Lemma16
public import CFSG.RankThree.GF2n.Parrott.Lemma16FusionSubgroup
public import CFSG.RankThree.GF2n.Parrott.EqualityBranchLift

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.LargeExtraspecial.Timmesfeld (IsExtraspecial2)
open scoped commutatorElement

section Helpers

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem exists_sylow_centralizer_ge (h : Tim79a.ParrottHyp z) (j : J z) :
    ∃ K : Subgroup ↥(H z),
      (Subgroup.centralizer ({j} : Set (J z))).map (Subgroup.inclusion (J_le_H (z := z))) ≤ K ∧
      IsSylowOf 2 (K.map (H z).subtype) (H z ⊓ Subgroup.centralizer ({(j : G)} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := H z ⊓ Subgroup.centralizer ({(j : G)} : Set G)
  set C : Subgroup ↥(H z) :=
    (Subgroup.centralizer ({j} : Set (J z))).map (Subgroup.inclusion (J_le_H (z := z)))
  have hCM : C.map (H z).subtype ≤ M := by
    rintro _ ⟨_, ⟨c, hc, rfl⟩, rfl⟩
    have hc' : c * j = j * c := Subgroup.mem_centralizer_singleton_iff.mp hc
    exact ⟨(Subgroup.inclusion J_le_H c).2,
      Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hc')⟩
  have hCp : IsPGroup 2 (C.map (H z).subtype) := (isPGroup_J h).to_le (by
    rintro _ ⟨_, ⟨c, -, rfl⟩, rfl⟩
    exact c.2)
  obtain ⟨Q, hQ⟩ := (hCp.comap_subtype (K := M)).exists_le_sylow
  have hS : IsSylowOf 2 ((Q : Subgroup ↥M).map M.subtype) M := ⟨Q, rfl⟩
  refine ⟨((Q : Subgroup ↥M).map M.subtype).subgroupOf (H z), fun y hy => ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact ⟨⟨(y : G), hCM ⟨y, hy, rfl⟩⟩, hQ (Subgroup.mem_comap.mpr ⟨y, hy, rfl⟩), rfl⟩
  · rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hS.le.trans inf_le_left)]
    exact hS

variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

private theorem no_conj_z_eq_of_mem_uvtJ_of_mem_vJ
    (hv : ∀ x : G, cosetJ (z := z) (vH D) x → orderOf x = 2 → ∀ g : G, g * z * g⁻¹ ≠ x) :
    ∀ x : G, cosetJ (z := z) (uH D * vH D * tH D) x → orderOf x = 2 →
      ∀ g : G, g * z * g⁻¹ ≠ x := by
  intro x hx hx2 g hg
  obtain ⟨j, hj, hxj⟩ := hx
  have hjH : j ∈ H z := J_le_H hj
  have hxH : x ∈ H z := by
    rw [hxj]
    exact (H z).mul_mem (uH D * vH D * tH D).2 hjH
  have hqx : qH D ⟨x, hxH⟩ =
      (⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩ := by
    have e : (⟨x, hxH⟩ : ↥(H z)) = (uH D * vH D * tH D) * ⟨j, hjH⟩ := Subtype.ext hxj
    have hjq : qH D ⟨j, hjH⟩ = 1 := (J_mem_iff D _).mp (Subgroup.mem_subgroupOf.mpr hj)
    rw [e, map_mul, hjq, mul_one, map_mul, map_mul, qH_uH, qH_vH, qH_tH]
  let y : ↥(H z) := (betaH D)⁻¹ * ⟨x, hxH⟩ * betaH D
  have hyv : cosetJ (z := z) (vH D) (y : G) := by
    refine ⟨(((vH D)⁻¹ * y : ↥(H z)) : G), Subgroup.mem_subgroupOf.mp
      ((J_mem_iff D _).mpr ?_), by simp⟩
    simp only [y, map_mul, map_inv, hqx, qH_vH, qH_betaH]
    rw [← conj_v_uvt_QA45]
    group
  have hy2 : orderOf (y : G) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj ((betaH D : G)⁻¹)) x
    rw [MulAut.conj_apply, inv_inv, hx2] at this
    simpa [y] using this
  apply hv (y : G) hyv hy2 ((betaH D : G)⁻¹ * g)
  simp only [y, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [← hg]
  group


private theorem no_conj_z_eq_of_mem_vJ_of_fusion (h : Tim79a.ParrottHyp z)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3)
    (hq₂ : qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hcomm : Commute (sigma1Nine (z := z) D) σ₂)
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    {σ : ↥(H z)} (hσ : σ = sigma1Nine (z := z) D * σ₂⁻¹)
    (hPH : ∀ g : G, g * z * g⁻¹ ∈ (P_H D).map (H z).subtype → g * z * g⁻¹ = z)
    (huv : ∀ x : G, cosetJ (z := z) (uH D * vH D) x → orderOf x = 2 →
      ∀ g : G, g * z * g⁻¹ ≠ x)
    (hcls : ∃ x₁ x₂ : G, ∀ x : G, cosetJ (z := z) (uH D * vH D * tH D) x → orderOf x = 2 →
      IsElemAbelian 2 (CJ z x) → ∃ j ∈ J z, j * x * j⁻¹ = x₁ ∨ j * x * j⁻¹ = x₂)
    (hstar : ∀ g : G, CFSG.conjugate (Subgroup.zpowers (σ : G)) g ≤ H z →
      ∃ h ∈ H z, CFSG.conjugate (Subgroup.zpowers (σ : G)) g =
        CFSG.conjugate (Subgroup.zpowers (σ : G)) h)
    (hNP : ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers (σ : G) : Set G),
      ∃ h ∈ Subgroup.normalizer (Subgroup.zpowers (σ : G) : Set G) ⊓ H z,
        ∃ c ∈ Subgroup.centralizer (Subgroup.zpowers (σ : G) : Set G), h * c = n)
    (hQ : ∀ x : G, cosetJ (z := z) (uH D * vH D * tH D) x → orderOf x = 2 →
      x ∈ Subgroup.centralizer ({(σ : G)} : Set G) → IsElemAbelian 2 (CJ z x) →
      ∀ X K : Subgroup G,
        IsSylowOf 2 X (Subgroup.centralizer ({(σ : G)} : Set G) ⊓ H z ⊓
          Subgroup.centralizer ({x} : Set G)) →
        (∀ k : G, k ∈ K ↔ k ∈ X ∧ (∀ y ∈ X, y * k = k * y) ∧ k * k = 1) →
        ∃ B : Subgroup G, B ≤ K ⊓ J z ∧ z ∈ B ∧ 2 < Nat.card B ∧
          (∀ a ∈ K ⊓ J z, ∀ a' ∈ K ⊓ J z, a ∉ B → a' ∉ B → a * a' ∈ B) ∧
          ∀ a ∈ K ⊓ J z, ∀ b ∈ B, IsConj (x * a) (x * (a * b))) :
    ∀ x : G, cosetJ (z := z) (vH D) x → orderOf x = 2 → ∀ g : G, g * z * g⁻¹ ≠ x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x' hx' hx'2 g hg
  have hσ3 : orderOf σ = 3 := by
    rw [hσ]
    exact orderOf_mul_sigma2_inv_of_commute D hσ₂ hq₂ hcomm
  have hqσ : qH D σ = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) *
      (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)⁻¹ := by
    rw [hσ, map_mul, map_inv, qH_sigma1Nine, hq₂]
  obtain ⟨x, hxc, hx2, hxσ, hxE, c, hcσ, hcx⟩ :=
    exists_conj_mem_uvtJ_centralizer_of_conj_mem_vJ D (Or.inl h) hσ3 hqσ hPH hcls hstar hNP
      x' hx' hx'2 ⟨g, hg⟩
  obtain ⟨hxH, hqx⟩ : ∃ hxH : x ∈ H z,
      qH D ⟨x, hxH⟩ = (⟨u, u_mem_A⟩ : QA45.originalSubgroup) * ⟨v, v_mem_A⟩ * ⟨t, t_mem_A⟩ := by
    obtain ⟨j, hj, hxj⟩ := hxc
    have hjH : j ∈ H z := J_le_H hj
    have hxH : x ∈ H z := by
      rw [hxj]
      exact (H z).mul_mem (uH D * vH D * tH D).2 hjH
    refine ⟨hxH, ?_⟩
    have e : (⟨x, hxH⟩ : ↥(H z)) = (uH D * vH D * tH D) * ⟨j, hjH⟩ := Subtype.ext hxj
    have hjq : qH D ⟨j, hjH⟩ = 1 := (J_mem_iff D _).mp (Subgroup.mem_subgroupOf.mpr hj)
    rw [e, map_mul, hjq, mul_one, map_mul, map_mul, qH_uH, qH_vH, qH_tH]
  have hxJ : x ∉ J z := by
    intro hxJ
    apply uvtA_not_mem_QP45
    rw [← hqx, (J_mem_iff D _).mp (Subgroup.mem_subgroupOf.mpr hxJ)]
    exact Subgroup.one_mem _
  have hHc : ∀ m ∈ H z, m * z = z * m := by
    intro m hm
    rw [H_eq_centralizer] at hm
    exact Subgroup.mem_centralizer_singleton_iff.mp hm
  have hxx : x * x = 1 := by rw [← sq, ← hx2]; exact pow_orderOf_eq_one x
  have hzz : z * z = 1 := by rw [← sq, ← h.1]; exact pow_orderOf_eq_one z
  have hHN : H z ≤ Subgroup.normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  obtain ⟨X, hXS⟩ := exists_isSylowOf 2
    (Subgroup.centralizer ({(σ : G)} : Set G) ⊓ H z ⊓ Subgroup.centralizer ({x} : Set G))
  have hXM := hXS.le
  have hcentral : ∀ y : G, y * y = 1 →
      y ∈ Subgroup.centralizer ({(σ : G)} : Set G) ⊓ H z ⊓ Subgroup.centralizer ({x} : Set G) →
      (∀ m ∈ Subgroup.centralizer ({(σ : G)} : Set G) ⊓ H z ⊓
        Subgroup.centralizer ({x} : Set G), m * y = y * m) → y ∈ X := by
    intro y hy hyM hyc
    have hpg : IsPGroup 2 (Subgroup.zpowers y) := by
      have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hy)
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
      · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
      · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h1, pow_one])
    have hle := CFSG.GroupTheory.le_isSylowOf_of_isPGroup_of_le_normalizer hXS
      (Subgroup.zpowers_le_of_mem hyM)
      (fun m hm => CFSG.GroupTheory.mem_normalizer_zpowers_iff.mpr (by
        rw [hyc m hm, mul_inv_cancel_right]
        exact Subgroup.mem_zpowers y)) hpg
    exact hle (Subgroup.mem_zpowers y)
  have hxX : x ∈ X := hcentral x hxx
    ⟨⟨hxσ, hxH⟩, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    (fun m hm => Subgroup.mem_centralizer_singleton_iff.mp hm.2)
  have hzX : z ∈ X := hcentral z hzz
    ⟨⟨Subgroup.mem_centralizer_singleton_iff.mpr (hHc _ σ.2).symm, z_mem_H⟩,
      Subgroup.mem_centralizer_singleton_iff.mpr (hHc x hxH).symm⟩
    (fun m hm => hHc m hm.1.2)
  obtain ⟨K, hKmem⟩ : ∃ K : Subgroup G,
      ∀ k : G, k ∈ K ↔ k ∈ X ∧ (∀ y ∈ X, y * k = k * y) ∧ k * k = 1 :=
    ⟨{ carrier := {k | k ∈ X ∧ (∀ y ∈ X, y * k = k * y) ∧ k * k = 1}
       one_mem' := ⟨X.one_mem, fun y _ => by rw [mul_one, one_mul], mul_one 1⟩
       mul_mem' := fun {a b} ha hb => by
         refine ⟨X.mul_mem ha.1 hb.1, fun y hy => ?_, ?_⟩
         · rw [← mul_assoc, ha.2.1 y hy, mul_assoc, hb.2.1 y hy, ← mul_assoc]
         · have hab : a * b = b * a := hb.2.1 a ha.1
           calc a * b * (a * b) = a * (b * a) * b := by group
             _ = a * (a * b) * b := by rw [hab]
             _ = a * a * (b * b) := by group
             _ = 1 := by rw [ha.2.2, hb.2.2, one_mul]
       inv_mem' := fun {a} ha => by
         have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha.2.2
         simp only [Set.mem_setOf_eq, hinv]
         exact ha }, fun _ => Iff.rfl⟩
  have hKX : K ≤ X := fun k hk => ((hKmem k).mp hk).1
  have hK : IsElemAbelian 2 K := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun k hk => by
      rw [pow_two]
      exact ((hKmem k).mp hk).2.2⟩
    simp only [Subgroup.coe_mul]
    exact ((hKmem b).mp b.2).2.1 a ((hKmem a).mp a.2).1
  have hNXK : Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (K : Set G) := by
    have key : ∀ n ∈ Subgroup.normalizer (X : Set G), ∀ k ∈ K, n * k * n⁻¹ ∈ K := by
      intro n hn k hk
      obtain ⟨hkX, hkc, hkk⟩ := (hKmem k).mp hk
      refine (hKmem _).mpr ⟨(Subgroup.mem_normalizer_iff.mp hn k).mp hkX, fun y hy => ?_, ?_⟩
      · have hy' : n⁻¹ * y * n ∈ X := (Subgroup.mem_normalizer_iff''.mp hn y).mp hy
        have e := hkc _ hy'
        calc y * (n * k * n⁻¹) = n * ((n⁻¹ * y * n) * k) * n⁻¹ := by group
          _ = n * (k * (n⁻¹ * y * n)) * n⁻¹ := by rw [e]
          _ = n * k * n⁻¹ * y := by group
      · calc n * k * n⁻¹ * (n * k * n⁻¹) = n * (k * k) * n⁻¹ := by group
          _ = 1 := by rw [hkk, mul_one, mul_inv_cancel]
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨key n hn k, fun hk => ?_⟩
    have hk' := key n⁻¹ (Subgroup.inv_mem _ hn) _ hk
    have e : n⁻¹ * (n * k * n⁻¹) * n⁻¹⁻¹ = k := by group
    rwa [e] at hk'
  have hxK : x ∈ K := (hKmem x).mpr
    ⟨hxX, fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (hXM hy).2, hxx⟩
  have hzK : z ∈ K := (hKmem z).mpr ⟨hzX, fun y hy => hHc y (hXM hy).1.2, hzz⟩
  have hzA : z ∈ K ⊓ J z := ⟨hzK, z_mem_J h⟩
  have hxA : x ∉ K ⊓ J z := fun hm => hxJ hm.2
  have hCJle : CJ z (sigma1Nine (z := z) D : G) ≤ CJ z (σ : G) := by
    intro y hy
    obtain ⟨hyσ₁, hyJ⟩ := mem_CJ.mp hy
    have hy1 : Commute y ((sigma1Nine (z := z) D : ↥(H z)) : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp hyσ₁
    have hy2' : (⟨y, hyJ⟩ : ↥(J z)) ∈ centralizerJ σ₂ := by
      rw [← hEq]
      exact mem_centralizerJ_iff.mpr hy1
    have hy2 : Commute y (σ₂ : G) := mem_centralizerJ_iff.mp hy2'
    refine mem_CJ.mpr ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_, hyJ⟩
    rw [hσ, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (hy1.mul_right hy2.inv_right).eq
  obtain ⟨a₀, ha₀, b₀, hb₀, hab₀⟩ := exists_not_commute_CJ_sigma1Nine D h
  have hfus : ∀ k ∈ K, IsConj z k → k = z ∨ x⁻¹ * k ∈ K ⊓ J z := by
    intro k hk hkz
    obtain ⟨hkX, -, hkk⟩ := (hKmem k).mp hk
    have hkM := hXM hkX
    have hkH : k ∈ H z := hkM.1.2
    by_cases hkP : (⟨k, hkH⟩ : ↥(H z)) ∈ P_H D
    · left
      obtain ⟨c', hc'⟩ := isConj_iff.mp hkz
      have h1 := hPH c' (by rw [hc']; exact ⟨⟨k, hkH⟩, hkP, rfl⟩)
      exact hc'.symm.trans h1
    · right
      exact ⟨K.mul_mem (K.inv_mem hxK) hk,
        inv_mul_mem_J_of_isConj_of_not_mem_P_H D huv hqσ hxc hkH hkP hkk
          (Subgroup.mem_centralizer_singleton_iff.mp hkM.1.1)
          (Subgroup.mem_centralizer_singleton_iff.mp hkM.2) hkz⟩
  have hCJx : ¬ (Subgroup.centralizer ({(σ : G)} : Set G) ⊓ J z ≤
      Subgroup.centralizer ({x} : Set G)) := by
    intro hle
    apply hab₀
    have hmem : ∀ y ∈ CJ z (sigma1Nine (z := z) D : G), y ∈ CJ z x := fun y hy => by
      obtain ⟨hyσ, hyJ⟩ := mem_CJ.mp (hCJle hy)
      exact mem_CJ.mpr ⟨hle ⟨hyσ, hyJ⟩, hyJ⟩
    exact hxE.comm (hmem a₀ ha₀) (hmem b₀ hb₀)
  have hdvd : 2 ∣ (Subgroup.centralizer ({(σ : G)} : Set G) ⊓ H z ⊓
      Subgroup.centralizer ({x} : Set G)).relIndex
        (Subgroup.centralizer ({(σ : G)} : Set G) ⊓ H z) :=
    CFSG.GroupTheory.dvd_relIndex_inf_centralizer_of_normal_pGroup
      (inf_le_inf_left _ J_le_H)
      (fun m hm => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hm.1, hHN hm.2⟩)
      ((isPGroup_J h).to_le inf_le_right) hCJx
  obtain ⟨B, hBA, hzB, hB, hidx, hQB⟩ := hQ x hxc hx2 hxσ hxE X K hXS hKmem
  exact false_of_conj_of_fusion_subgroup hXS hKX hNXK hK hxK inf_le_left hzA hxA hfus hdvd
    ⟨c, hcσ, hcx⟩ hBA hzB hB hidx hQB

end Helpers

theorem parrott_theorem1_equalityBranch
    (hF : ∀ (G : Type) [Group G] [Finite G] (z : G), Tim79a.ParrottHyp z →
      NormalizerControlsCenterJFusion z)
    (hder : ∀ (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      ParrottEqualityBranch (z := z) (D := D) h →
        ⁅H z, ⁅H z, H z⁆⁆ ⊓ J z ≤ J1sub (z := z) (D := D) h)
    (hZ : ∀ (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      ParrottEqualityBranch (z := z) (D := D) h →
      ∀ j : J z, j ∉ Subgroup.center (J z) → (j : G) ∉ J1sub (z := z) (D := D) h →
      ∀ K : Subgroup ↥(H z),
        (Subgroup.centralizer ({j} : Set (J z))).map (Subgroup.inclusion (J_le_H (z := z))) ≤ K →
        IsSylowOf 2 (K.map (H z).subtype) (H z ⊓ Subgroup.centralizer ({(j : G)} : Set G)) →
        Subgroup.zpowers z ≤ ⁅K, ⁅K, K⁆⁆.map (H z).subtype)
    (hJ1 : ∀ (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      ParrottEqualityBranch (z := z) (D := D) h →
      ∀ j : J z, orderOf (j : G) = 2 → j ∉ Subgroup.center (J z) →
        (j : G) ∈ J1sub (z := z) (D := D) h →
      ∃ B : Subgroup G,
        (∃ k : ↥(H z), k * (j : G) * k⁻¹ ∈ J z ∧
          k * (j : G) * k⁻¹ ∈ J1sub (z := z) (D := D) h ∧
          k * (j : G) * k⁻¹ ∈ Subgroup.centralizer (B : Set G)) ∧
        ((∃ g : G, g * z * g⁻¹ = (j : G)) →
          ∀ k : ↥(H z), k * (j : G) * k⁻¹ ∈ J z →
            k * (j : G) * k⁻¹ ∈ J1sub (z := z) (D := D) h →
            k * (j : G) * k⁻¹ ∈ Subgroup.centralizer (B : Set G) →
            orderOf (k * (j : G) * k⁻¹) = 2 →
            ∃ x : G, x ∈ H z ∧ x ∉ J z ∧ orderOf x = 2 ∧
              x * (k * (j : G) * k⁻¹) = (k * (j : G) * k⁻¹) * x ∧
              x ∈ Subgroup.centralizer (B : Set G)) ∧
        ∀ x : G, x ∈ H z → x ∉ J z → orderOf x = 2 →
          x ∈ Subgroup.centralizer (B : Set G) →
          Subgroup.centralizer ({x} : Set G) ⊓
              (J1sub (z := z) (D := D) h ⊓ Subgroup.centralizer (B : Set G)) =
            centerIn (J z))
    (hstar : ∀ (G : Type) [Group G] [Finite G] (z : G) (_h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN)
      (σ₂ : ↥(H z)), orderOf σ₂ = 3 →
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) →
      Commute (sigma1Nine (z := z) D) σ₂ →
      centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂ →
      (∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j) →
      ∀ σ : ↥(H z), σ = sigma1Nine (z := z) D * σ₂⁻¹ →
      ∀ g : G, CFSG.conjugate (Subgroup.zpowers (σ : G)) g ≤ H z →
        ∃ h' ∈ H z, CFSG.conjugate (Subgroup.zpowers (σ : G)) g =
          CFSG.conjugate (Subgroup.zpowers (σ : G)) h')
    (hNP : ∀ (G : Type) [Group G] [Finite G] (z : G) (_h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN)
      (σ₂ : ↥(H z)), orderOf σ₂ = 3 →
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) →
      Commute (sigma1Nine (z := z) D) σ₂ →
      ∀ σ : ↥(H z), σ = sigma1Nine (z := z) D * σ₂⁻¹ →
      ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers (σ : G) : Set G),
        ∃ h' ∈ Subgroup.normalizer (Subgroup.zpowers (σ : G) : Set G) ⊓ H z,
          ∃ c ∈ Subgroup.centralizer (Subgroup.zpowers (σ : G) : Set G), h' * c = n)
    (ht : ∀ (G : Type) [Group G] [Finite G] (z : G) (_h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN)
      (σ₂ : ↥(H z)), orderOf σ₂ = 3 →
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) →
      Commute (sigma1Nine (z := z) D) σ₂ →
      centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂ →
      (∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j) →
      ∀ σ : ↥(H z), σ = sigma1Nine (z := z) D * σ₂⁻¹ →
      (∀ g : G, CFSG.conjugate (Subgroup.zpowers (σ : G)) g ≤ H z →
        ∃ h' ∈ H z, CFSG.conjugate (Subgroup.zpowers (σ : G)) g =
          CFSG.conjugate (Subgroup.zpowers (σ : G)) h') →
      (∀ n ∈ Subgroup.normalizer (Subgroup.zpowers (σ : G) : Set G),
        ∃ h' ∈ Subgroup.normalizer (Subgroup.zpowers (σ : G) : Set G) ⊓ H z,
          ∃ c ∈ Subgroup.centralizer (Subgroup.zpowers (σ : G) : Set G), h' * c = n) →
      ∀ x : G, cosetJ (z := z) (tH D) x → orderOf x = 2 → ∀ g : G, g * z * g⁻¹ ≠ x)
    (htu : ∀ (G : Type) [Group G] [Finite G] (z : G) (_h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN)
      (σ₂ : ↥(H z)), orderOf σ₂ = 3 →
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) →
      Commute (sigma1Nine (z := z) D) σ₂ →
      centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂ →
      (∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j) →
      ∀ x : G, cosetJ (z := z) (tH D * uH D) x → orderOf x = 2 → ∀ g : G, g * z * g⁻¹ ≠ x)
    (hPH : ∀ (G : Type) [Group G] [Finite G] (z : G) (_h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      (∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j) →
      (∀ x : G, cosetJ (z := z) (tH D) x → orderOf x = 2 → ∀ g : G, g * z * g⁻¹ ≠ x) →
      (∀ x : G, cosetJ (z := z) (tH D * uH D) x → orderOf x = 2 →
        ∀ g : G, g * z * g⁻¹ ≠ x) →
      ∀ g : G, g * z * g⁻¹ ∈ (P_H D).map (H z).subtype → g * z * g⁻¹ = z)
    (hH' : ∀ (G : Type) [Group G] [Finite G] (z : G) (_h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      (∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j) →
      (∀ x : G, cosetJ (z := z) (tH D) x → orderOf x = 2 → ∀ g : G, g * z * g⁻¹ ≠ x) →
      (∀ x : G, cosetJ (z := z) (tH D * uH D) x → orderOf x = 2 →
        ∀ g : G, g * z * g⁻¹ ≠ x) →
      ∀ g : G, g * z * g⁻¹ ∈ ⁅H z, H z⁆ → g * z * g⁻¹ = z)
    (hL15 : ∀ (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      ParrottEqualityBranch (z := z) (D := D) h →
      ∃ B : Subgroup G, B ≤ H z ∧ Nat.card B = 5 ∧
        (∀ b ∈ B, cosetJ (z := z) (uH D * vH D) (b * ((uH D * vH D : ↥(H z)) : G) * b⁻¹)) ∧
        ∃ E : Subgroup G, E ≤ J z ∧ IsExtraspecial2 E ∧ Nat.card E = 2 ^ 5 ∧
          ∀ w : G, cosetJ (z := z) (uH D * vH D) w → w ∈ Subgroup.centralizer (B : Set G) →
            ∀ e ∈ E, w * e = e * w)
    (hcls : ∀ (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      ParrottEqualityBranch (z := z) (D := D) h →
      ∃ x₁ x₂ : G, ∀ x : G, cosetJ (z := z) (uH D * vH D * tH D) x → orderOf x = 2 →
        IsElemAbelian 2 (CJ z x) → ∃ j ∈ J z, j * x * j⁻¹ = x₁ ∨ j * x * j⁻¹ = x₂)
    (hQ : ∀ (G : Type) [Group G] [Finite G] (z : G) (_h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN)
      (σ₂ : ↥(H z)), orderOf σ₂ = 3 →
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) →
      Commute (sigma1Nine (z := z) D) σ₂ →
      centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂ →
      ∀ σ : ↥(H z), σ = sigma1Nine (z := z) D * σ₂⁻¹ →
      ∀ x : G, cosetJ (z := z) (uH D * vH D * tH D) x → orderOf x = 2 →
      x ∈ Subgroup.centralizer ({(σ : G)} : Set G) → IsElemAbelian 2 (CJ z x) →
      ∀ X K : Subgroup G,
        IsSylowOf 2 X (Subgroup.centralizer ({(σ : G)} : Set G) ⊓ H z ⊓
          Subgroup.centralizer ({x} : Set G)) →
        (∀ k : G, k ∈ K ↔ k ∈ X ∧ (∀ y ∈ X, y * k = k * y) ∧ k * k = 1) →
        ∃ B : Subgroup G, B ≤ K ⊓ J z ∧ z ∈ B ∧ 2 < Nat.card B ∧
          (∀ a ∈ K ⊓ J z, ∀ a' ∈ K ⊓ J z, a ∉ B → a' ∉ B → a * a' ∈ B) ∧
          ∀ a ∈ K ⊓ J z, ∀ b ∈ B, IsConj (x * a) (x * (a * b))) :
    ∀ (G : Type) [Group G] [Finite G] (z : G) (h : Tim79a.ParrottHyp z)
      (hN : ((J z).subgroupOf (H z)).Normal) (D : QuotientData (z := z) hN),
      ParrottEqualityBranch (z := z) (D := D) h → H z ⊔ pPrimeCore 2 G = ⊤ := by
  intro G _ _ z h hN D hbr
  classical
  obtain ⟨σ₂', hσ₂', hq₂', hEq'⟩ := id hbr
  obtain ⟨σ₂, hσ₂, hq₂, hc⟩ := exists_commuting_order_three_lift_sigma2 (z := z) D h
  have hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂ :=
    hEq'.trans (centralizerJ_eq_of_qH_eq_of_orderOf_eq_three D h hσ₂' hσ₂ (hq₂'.trans hq₂.symm))
  have hcomm : Commute (sigma1Nine (z := z) D) σ₂ := hc.symm
  set σ : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹ with hσ
  have hJ : ∀ j : G, j ∈ J z → orderOf j = 2 → j ≠ z → ∀ g : G, g * z * g⁻¹ ≠ j := by
    intro j hjJ hj2 hjz
    by_cases hjZ : (⟨j, hjJ⟩ : J z) ∈ Subgroup.center (J z)
    · intro g hg
      have hmem : g * z * g⁻¹ ∈ centerIn (J z) := by
        rw [← QuotientV.centerIn_subgroupOf_eq_center] at hjZ
        rw [hg]
        exact Subgroup.mem_subgroupOf.mp hjZ
      exact hjz (hg.symm.trans (conj_z_mem_centerIn_eq h (hF G z h) hmem))
    · by_cases hj1 : j ∈ J1sub (z := z) (D := D) h
      · obtain ⟨B, hconjB, hP7, hx⟩ := hJ1 G z h hN D hbr ⟨j, hjJ⟩ hj2 hjZ hj1
        exact no_conj_z_eq_of_mem_J1_minus_centerJ_gen hj2 hjZ hconjB hP7 hx
      · obtain ⟨K, hCK, hKS⟩ := exists_sylow_centralizer_ge h ⟨j, hjJ⟩
        exact no_conj_z_eq_of_mem_J_minus_J1_cases (Or.inl h) (center_le_J1sub D h) hjZ hj1
          (hder G z h hN D hbr) (hF G z h) hCK hKS (hZ G z h hN D hbr ⟨j, hjJ⟩ hjZ hj1 K hCK hKS)
  have hstar' := hstar G z h hN D σ₂ hσ₂ hq₂ hcomm hEq hJ σ hσ
  have hNP' := hNP G z h hN D σ₂ hσ₂ hq₂ hcomm σ hσ
  have ht' := ht G z h hN D σ₂ hσ₂ hq₂ hcomm hEq hJ σ hσ hstar' hNP'
  have htu' := htu G z h hN D σ₂ hσ₂ hq₂ hcomm hEq hJ
  have hPH' := hPH G z h hN D hJ ht' htu'
  have hH'' := hH' G z h hN D hJ ht' htu'
  obtain ⟨B, hBH, hB5, hBuv, E, hEJ, hE, hEcard, hwE⟩ := hL15 G z h hN D hbr
  have huv := no_conj_z_eq_of_mem_uvJ D (Or.inl h) hBH hB5 hBuv hEJ hE hEcard hwE hH''
  have hv := no_conj_z_eq_of_mem_vJ_of_fusion D h hσ₂ hq₂ hcomm hEq hσ hPH' huv
    (hcls G z h hN D hbr) hstar' hNP' (hQ G z h hN D σ₂ hσ₂ hq₂ hcomm hEq σ hσ)
  exact eq_centralizer_sup_pPrimeCore_of_cosets D h hJ ht' htu' huv
    (no_conj_z_eq_of_mem_uvtJ_of_mem_vJ D hv)

end CFSG.RankThree.GF2n.Parrott
