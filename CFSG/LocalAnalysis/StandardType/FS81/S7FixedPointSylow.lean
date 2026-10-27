module

public import CFSG.Open.LocalVocabulary
public import Mathlib.GroupTheory.Sylow
import CFSG.LocalAnalysis.StandardType.FS81.S7FixedCoset

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open

theorem card_le_three_of_fixed_point {G : Type} [Group G] [Finite G] {A Z : Subgroup G} {β : G}
    (hA : IsElemAbelian 3 A) (hAcard : Nat.card A = 27)
    (hAZ : A ≤ Subgroup.normalizer (Z : Set G)) (hβZ : β ∈ Z) (hβ : orderOf β = 3)
    (hβc : ∀ z ∈ Z, z * β = β * z) (hAβ : ∀ a ∈ A, a * β = β * a)
    (hF : ∀ F : Subgroup G, F ≤ A → Nat.card F = 9 → ∀ x ∈ Z, (∃ n : ℕ, x ^ (3 ^ n) = 1) →
      (∀ a ∈ F, a * x = x * a) → x ∈ Subgroup.zpowers β) :
    ∀ T : Subgroup G, T ≤ Z → IsPGroup 3 T → Nat.card T ≤ 3 := by
  open scoped Pointwise commutatorElement in
  have hA3 : IsPGroup 3 ↥A := by
    intro g
    refine ⟨1, ?_⟩
    rw [show (3 : ℕ) ^ 1 = 3 from rfl]
    exact Subtype.ext (by simpa using hA.2 (g : G) g.2)
  let f : ↥A →* MulAut ↥Z := Z.normalizerMonoidHom.comp (Subgroup.inclusion hAZ)
  let _instMul : MulDistribMulAction ↥A ↥Z := MulDistribMulAction.compHom ↥Z f
  have hnotdvd : ¬ 3 ∣ Nat.card (Sylow 3 ↥Z) := not_dvd_card_sylow 3 ↥Z
  obtain ⟨P₀, hP₀⟩ := hA3.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 3 ↥Z) hnotdvd
  have hP₀' : ∀ a : ↥A, a • P₀ = P₀ := (MulAction.mem_fixedPoints).mp hP₀
  have hfixP : ∀ a : ↥A, a • (P₀ : Subgroup ↥Z) = (P₀ : Subgroup ↥Z) := by
    intro a
    simpa only [Sylow.pointwise_smul_def] using
      congrArg (fun S : Sylow 3 ↥Z => (S : Subgroup ↥Z)) (hP₀' a)
  have hsmul : ∀ (a : ↥A) (z : ↥Z),
      Z.subtype (a • z) = (a : G) * Z.subtype z * (a : G)⁻¹ := by
    intro a z
    show ((MulDistribMulAction.toMulAut ↥A ↥Z a) z : G) = _
    rw [MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]
    rfl
  let P₁ : Subgroup G := (P₀ : Subgroup ↥Z).map Z.subtype
  have hP₁Z : P₁ ≤ Z := Subgroup.map_subtype_le _
  have hP₁p : IsPGroup 3 P₁ := P₀.isPGroup'.map Z.subtype
  have hAP₁ : A ≤ Subgroup.normalizer (P₁ : Set G) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [Subgroup.mem_map] at hh ⊢
      obtain ⟨z, hz, rfl⟩ := hh
      refine ⟨(⟨a, ha⟩ : ↥A) • z, ?_, ?_⟩
      · have hmem : (⟨a, ha⟩ : ↥A) • z ∈ (⟨a, ha⟩ : ↥A) • (P₀ : Subgroup ↥Z) :=
          Subgroup.smul_mem_pointwise_smul z _ _ hz
        rwa [hfixP] at hmem
      · exact hsmul (⟨a, ha⟩ : ↥A) z
    · intro hh
      rw [Subgroup.mem_map] at hh ⊢
      obtain ⟨w, hw, hw_eq⟩ := hh
      refine ⟨(⟨a, ha⟩ : ↥A)⁻¹ • w, ?_, ?_⟩
      · have hmem : (⟨a, ha⟩ : ↥A)⁻¹ • w ∈ (⟨a, ha⟩ : ↥A)⁻¹ • (P₀ : Subgroup ↥Z) :=
          Subgroup.smul_mem_pointwise_smul w _ _ hw
        rwa [hfixP] at hmem
      · rw [hsmul (⟨a, ha⟩ : ↥A)⁻¹ w, hw_eq]
        simp only [Subgroup.coe_inv]
        group
  have hBZ_eq : (Subgroup.zpowers β).subgroupOf Z =
      Subgroup.zpowers (⟨β, hβZ⟩ : ↥Z) := by
    ext z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa using congrArg Z.subtype hk⟩
  have hbZ_center : (⟨β, hβZ⟩ : ↥Z) ∈ Subgroup.center ↥Z := by
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext (hβc (z : G) z.2)
  have hBZp : IsPGroup 3 ((Subgroup.zpowers β).subgroupOf Z) := by
    rw [hBZ_eq]
    exact IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers, Subgroup.orderOf_mk, hβ, pow_one])
  have hBZn : ((Subgroup.zpowers β).subgroupOf Z).Normal := by
    rw [hBZ_eq]
    exact Subgroup.normal_of_le_center ((Subgroup.zpowers_le).mpr hbZ_center)
  have hBZ_le : (Subgroup.zpowers β).subgroupOf Z ≤ (P₀ : Subgroup ↥Z) :=
    IsPGroup.le_sylow_of_normal hBZp P₀
  have hβP₁ : β ∈ P₁ := by
    rw [Subgroup.mem_map]
    refine ⟨⟨β, hβZ⟩, hBZ_le ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers β
  have hcard_le : ∀ T : Subgroup G, T ≤ Z → IsPGroup 3 T → Nat.card T ≤ Nat.card P₁ := by
    intro T hTZ hTp
    have hTZp : IsPGroup 3 (T.subgroupOf Z) :=
      hTp.comap_of_injective Z.subtype Z.subtype_injective
    obtain ⟨Q, hQ⟩ := hTZp.exists_le_sylow
    have hcardT : Nat.card T = Nat.card (T.subgroupOf Z) := by
      conv_lhs => rw [← Subgroup.map_subgroupOf_eq_of_le hTZ]
      exact Subgroup.card_map_of_injective Z.subtype_injective
    calc Nat.card T = Nat.card (T.subgroupOf Z) := hcardT
      _ ≤ Nat.card Q := Subgroup.card_le_of_le hQ
      _ = Nat.card P₀ := by rw [Sylow.card_eq_multiplicity Q, Sylow.card_eq_multiplicity P₀]
      _ = Nat.card P₁ := (Subgroup.card_map_of_injective Z.subtype_injective).symm
  have hP₁le : Nat.card P₁ ≤ 3 := by
    by_contra hcon
    rw [not_le] at hcon
    let B : Subgroup G := Subgroup.zpowers β
    have hBP₁ : B ≤ P₁ := Subgroup.zpowers_le.mpr hβP₁
    have hBcard : Nat.card B = 3 := by rw [Nat.card_zpowers, hβ]
    have hBne : B ≠ P₁ := by
      intro heq
      rw [← heq, hBcard] at hcon
      exact lt_irrefl 3 hcon
    have hBcenter : B.subgroupOf P₁ ≤ Subgroup.center ↥P₁ := by
      intro b hb
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      change (y : G) * P₁.subtype b = P₁.subtype b * (y : G)
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hb : (b : G) ∈ B)
      rw [← hk]
      have hcy : Commute (y : G) β := hβc (y : G) (hP₁Z y.2)
      exact (hcy.zpow_right k).eq
    have hBn : (B.subgroupOf P₁).Normal := Subgroup.normal_of_le_center hBcenter
    have hAcB : A ≤ Subgroup.centralizer (B : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hh
      rw [← hk]
      have hca : Commute a β := hAβ a ha
      exact (hca.zpow_right k).eq.symm
    have hAB : A ≤ Subgroup.normalizer (B : Set G) :=
      hAcB.trans (Subgroup.centralizer_le_normalizer (B : Set G))
    obtain ⟨x, hxP₁, hxB, hxcomm⟩ :=
      exists_fixed_coset_of_pGroup (A := A) (P := P₁) (B := B)
        hA3 hP₁p hBP₁ hBn hAP₁ hAB hBne
    have _instComm : IsMulCommutative B := Subgroup.zpowers_isMulCommutative β
    let φ : ↥A →* B :=
      { toFun := fun a => ⟨(a : G) * x * (a : G)⁻¹ * x⁻¹, hxcomm (a : G) a.2⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := fun a b => by
          apply Subtype.ext
          show ⁅((a : G) * (b : G)), x⁆ = ⁅(a : G), x⁆ * ⁅(b : G), x⁆
          rw [commutatorElement_mul_left_eq_conj_mul]
          have hconj : (a : G) * ⁅(b : G), x⁆ * (a : G)⁻¹ = ⁅(b : G), x⁆ := by
            have hmem : ⁅(b : G), x⁆ ∈ B := hxcomm (b : G) b.2
            obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
            rw [← hk]
            have hc : Commute (a : G) β := hAβ (a : G) a.2
            rw [(hc.zpow_right k).eq, mul_assoc, mul_inv_cancel, mul_one]
          rw [hconj]
          exact (congrArg Subtype.val
            (mul_comm' (⟨⁅(a : G), x⁆, hxcomm (a : G) a.2⟩ : B)
              (⟨⁅(b : G), x⁆, hxcomm (b : G) b.2⟩ : B))).symm }
    have hker_range : Nat.card φ.ker * Nat.card φ.range = Nat.card ↥A :=
      Subgroup.card_ker_mul_card_range φ
    have hrange_le : Nat.card φ.range ≤ 3 := by
      have hle : Nat.card φ.range ≤ Nat.card B :=
        Subgroup.card_le_card_group (H := φ.range)
      simpa [hBcard] using hle
    have hkerge : 9 ≤ Nat.card φ.ker := by
      have hprod : Nat.card φ.ker * Nat.card φ.range = 27 := by
        rw [hker_range, hAcard]
      nlinarith [Nat.card_pos (α := φ.ker), hrange_le, hprod]
    have htop : IsPGroup 3 (⊤ : Subgroup ↥A) := hA3.of_equiv Subgroup.topEquiv.symm
    have hker3 : IsPGroup 3 φ.ker := htop.to_le le_top
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hker3
    have hk2 : 2 ≤ k := by
      have h : 3 ^ 2 ≤ 3 ^ k := by
        rw [← hk]
        simpa using hkerge
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp h
    have h9dvd : 3 ^ 2 ∣ Nat.card φ.ker := by
      rw [hk]
      exact pow_dvd_pow 3 hk2
    obtain ⟨K, hKcard⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 2) h9dvd
    let F : Subgroup G := (K.map φ.ker.subtype).map A.subtype
    have hFA : F ≤ A := Subgroup.map_subtype_le _
    have hFcard : Nat.card F = 9 := by
      rw [Subgroup.card_map_of_injective A.subtype_injective,
        Subgroup.card_map_of_injective φ.ker.subtype_injective, hKcard]
      norm_num
    have hFx : ∀ a ∈ F, a * x = x * a := by
      intro a ha
      rw [Subgroup.mem_map] at ha
      obtain ⟨b, hb, rfl⟩ := ha
      rw [Subgroup.mem_map] at hb
      obtain ⟨c, hc, rfl⟩ := hb
      have hc1 : φ (c : ↥A) = 1 := MonoidHom.mem_ker.mpr c.2
      have hcomm1 : ((c : ↥A) : G) * x = x * ((c : ↥A) : G) := by
        have h : ⁅((c : ↥A) : G), x⁆ = 1 := by
          have h' : (φ (c : ↥A) : G) = 1 := by rw [hc1]; rfl
          show ((c : ↥A) : G) * x * ((c : ↥A) : G)⁻¹ * x⁻¹ = 1
          exact h'
        exact commutatorElement_eq_one_iff_mul_comm.mp h
      exact hcomm1
    have hxZ : x ∈ Z := hP₁Z hxP₁
    have hx3 : ∃ n : ℕ, x ^ (3 ^ n) = 1 := by
      obtain ⟨n, hn⟩ := hP₁p ⟨x, hxP₁⟩
      exact ⟨n, by simpa using hn⟩
    exact hxB (hF F hFA hFcard x hxZ hx3 hFx)
  intro T hTZ hTp
  exact le_trans (hcard_le T hTZ hTp) hP₁le

end CFSG.StandardType.FrameRoute.FS81

end
