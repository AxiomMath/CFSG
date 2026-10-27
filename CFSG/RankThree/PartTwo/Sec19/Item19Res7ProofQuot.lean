module

public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Item419ThetaProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec19.Item19Res7Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Sec21 Sec21.Item211Proof

variable {G : Type} [Group G] [Finite G] {K A L : Subgroup G}

theorem isElemAbelian_map {Γ Γ' : Type*} [Group Γ] [Group Γ'] {p : ℕ} {E : Subgroup Γ}
    (hE : CFSG.Assembly.IsElemAbelian p E) (f : Γ →* Γ') :
    CFSG.Assembly.IsElemAbelian p (E.map f) := CFSG.SectionRank.isElemAbelian_map hE _

theorem card_le_of_isElemAbelian_quotX (hKA4 : SectionFourHyp ↥(K ⊔ A))
    (hO2 : CFSG.Open.pCoreOf 2 K ≠ ⊥) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    {B : Subgroup (QuotX K A)} (hB : CFSG.Assembly.IsElemAbelian 3 B) : Nat.card B ≤ 27 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, -, -, hScard, hSe⟩ := exists_lift_of_le (L := K) (A := A) (T := ⊥)
    IsPGroup.of_bot hB (by rw [Subgroup.map_bot]; exact bot_le)
  rw [← hScard]
  set P : Subgroup ↥(K ⊔ A) := (CFSG.Open.pCoreOf 2 K).subgroupOf (K ⊔ A) with hP
  have hPK : CFSG.Open.pCoreOf 2 K ≤ K ⊔ A :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left
  have hP1 : P ≠ ⊥ := by
    intro h0
    apply hO2
    rw [hP, Subgroup.subgroupOf_eq_bot] at h0
    exact (disjoint_iff.mp h0 ▸ (inf_eq_left.mpr hPK)).symm
  have hP2 : IsPGroup 2 P :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).comap_of_injective (K ⊔ A).subtype
      (K ⊔ A).subtype_injective
  have hKAN : K ⊔ A ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
      (hAK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
  have hN : (⊤ : Subgroup ↥(K ⊔ A)) = Subgroup.normalizer (P : Set ↥(K ⊔ A)) := by
    refine (eq_top_iff.mpr fun x _ => ?_).symm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    exact Subgroup.mem_normalizer_iff.mp (hKAN x.2) y
  have h2loc : CFSG.Open.IsTwoLocal (⊤ : Subgroup ↥(K ⊔ A)) := ⟨P, hP1, hP2, hN⟩
  have hrank := CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
    (by norm_num) ⊤ h2loc
  have he3 : CFSG.Open.evenRank ↥(K ⊔ A) ≤ 3 := hKA4.evenRank_le
  have hSp : IsPGroup 3 S := fun x => ⟨1, Subtype.ext (by simpa using hSe.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hSp
  have hk3 : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(K ⊔ A)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top ⟨hSe.1, hSe.2⟩ hk
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 27 := by norm_num

theorem partTwoE_eq_partTwoF_quotX (hKA4 : SectionFourHyp ↥(K ⊔ A))
    (hO2 : CFSG.Open.pCoreOf 2 K ≠ ⊥) (hAK : A ≤ Subgroup.normalizer (K : Set G)) :
    partTwoE (QuotX K A) = partTwoF (QuotX K A) := by
  ext E
  constructor
  · intro hE
    refine ⟨hE.1, fun B hB hEB => ?_, E, hE, le_rfl⟩
    exact (Subgroup.eq_of_le_of_card_ge hEB (by
      rw [hE.2.1]
      exact card_le_of_isElemAbelian_quotX hKA4 hO2 hAK hB)).symm
  · rintro ⟨hE0, -, E', hE', hE'E⟩
    have h := Subgroup.eq_of_le_of_card_ge hE'E (by
      rw [hE'.2.1]
      exact card_le_of_isElemAbelian_quotX hKA4 hO2 hAK hE0)
    rw [← h]
    exact hE'

theorem isE27_aOne (hA : Late.IsE27 A) : Late.IsE27 (aOne K A) := by
  refine ⟨isElemAbelian_map (isElemAbelian_subgroupOf hA.1) _, ?_⟩
  rw [← Nat.card_congr (aEquiv (L := K) hA.isPGroup).toEquiv, hA.2]

theorem orderOf_piX (hAp : IsPGroup 3 A) {c : G} (hcA : c ∈ A) :
    orderOf (piX K A ⟨c, Subgroup.mem_sup_right hcA⟩) = orderOf c := by
  have h1 : (piX K A ⟨c, Subgroup.mem_sup_right hcA⟩) =
      ((aEquiv (L := K) hAp ⟨c, hcA⟩ : aOne K A) : QuotX K A) := rfl
  rw [h1, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]

theorem piX_eq_one_iff (hAp : IsPGroup 3 A) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (x : ↥(K ⊔ A)) :
    piX K A x = 1 ↔ (x : G) ∈ inSubgroup (aschbacherSolvableCore 3) K := by
  rw [← inSubgroup_theta_sup hAp hAK, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [Subtype.ext hyx] at hy

theorem exists_psi (hAp : IsPGroup 3 A) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hLK : L ≤ K) :
    ∃ ψ : L →* ↥((L.subgroupOf (K ⊔ A)).map (piX K A)), Function.Surjective ψ ∧
      (∀ l : L, (ψ l : QuotX K A) = piX K A ⟨l, Subgroup.mem_sup_left (hLK l.2)⟩) ∧
      ∀ l : L, ψ l = 1 ↔ (l : G) ∈ inSubgroup (aschbacherSolvableCore 3) K := by
  have hLKA : L ≤ K ⊔ A := hLK.trans le_sup_left
  refine ⟨((piX K A).comp (Subgroup.inclusion hLKA)).codRestrict _ fun l =>
    ⟨Subgroup.inclusion hLKA l, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩, ?_, fun l => rfl,
    fun l => ?_⟩
  · rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  · exact Iff.trans ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
      (piX_eq_one_iff hAp hAK (Subgroup.inclusion hLKA l))

theorem nonempty_imageTheta_equiv (hAp : IsPGroup 3 A) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hLK : L ≤ K) :
    Nonempty (↥((L.subgroupOf K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K))) ≃*
      ↥((L.subgroupOf (K ⊔ A)).map (piX K A))) := by
  obtain ⟨ψ, hψs, -, hψk⟩ := exists_psi hAp hAK hLK
  set f₁ : L →* ↥K ⧸ aschbacherSolvableCore 3 ↥K :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K)).comp (Subgroup.inclusion hLK) with hf₁
  have hker : f₁.ker = ψ.ker := by
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hψk, hf₁, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · intro h
      exact ⟨_, h, rfl⟩
    · rintro ⟨y, hy, hyl⟩
      have : y = Subgroup.inclusion hLK l := Subtype.ext hyl
      rwa [← this]
  have hr₁ : f₁.range =
      (L.subgroupOf K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥K)) := by
    rw [hf₁, MonoidHom.range_comp, Subgroup.inclusion_range]
  exact ⟨(MulEquiv.subgroupCongr hr₁).symm.trans
    ((QuotientGroup.quotientKerEquivRange f₁).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)))⟩

omit [Finite G] in
theorem image_le_inf_centralizer (hLK : L ≤ K) {c : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hcA : c ∈ A) :
    (L.subgroupOf (K ⊔ A)).map (piX K A) ≤
      lOne K A ⊓ Subgroup.centralizer ({piX K A ⟨c, Subgroup.mem_sup_right hcA⟩} : Set _) := by
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨⟨x, Subgroup.mem_subgroupOf.mpr (hLK (Subgroup.mem_subgroupOf.mp hx)), rfl⟩,
    Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact Subgroup.mem_centralizer_singleton_iff.mp (hLc (Subgroup.mem_subgroupOf.mp hx))

theorem isSubnormal_image (hAp : IsPGroup 3 A) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hLK : L ≤ K) {c : G} (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hcA : c ∈ A)
    (hLsn : (L.subgroupOf (K ⊓ Subgroup.centralizer ({c} : Set G))).IsSubnormal) :
    (((L.subgroupOf (K ⊔ A)).map (piX K A)).subgroupOf
      (lOne K A ⊓ Subgroup.centralizer
        ({piX K A ⟨c, Subgroup.mem_sup_right hcA⟩} : Set _))).IsSubnormal := by
  set M := K ⊓ Subgroup.centralizer ({c} : Set G) with hM
  set C := lOne K A ⊓ Subgroup.centralizer
    ({piX K A ⟨c, Subgroup.mem_sup_right hcA⟩} : Set (QuotX K A)) with hC
  have hMKA : M ≤ K ⊔ A := inf_le_left.trans le_sup_left
  have hmap : (M.subgroupOf (K ⊔ A)).map (piX K A) = C :=
    Sec4.Item419ThetaProof.map_inf_centralizer_eq hAp hAK hcA
  have hmem : ∀ m : M, (piX K A).comp (Subgroup.inclusion hMKA) m ∈ C := fun m => by
    rw [← hmap]
    exact ⟨Subgroup.inclusion hMKA m, Subgroup.mem_subgroupOf.mpr m.2, rfl⟩
  set f : M →* C := ((piX K A).comp (Subgroup.inclusion hMKA)).codRestrict C hmem with hf
  have hfs : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← hmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  have h := hLsn.map hfs
  convert h using 1
  ext ⟨y, hy⟩
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxM : (x : G) ∈ M := ⟨hLK (Subgroup.mem_subgroupOf.mp hx),
      hLc (Subgroup.mem_subgroupOf.mp hx)⟩
    exact ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx), rfl⟩
  · rintro ⟨m, hm, hmy⟩
    refine ⟨Subgroup.inclusion hMKA m, Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_subgroupOf.mp hm), ?_⟩
    exact congrArg Subtype.val hmy

theorem zpowers_eq_aOne_inf_centralizer (hAp : IsPGroup 3 A)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hLK : L ≤ K) {c : G}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hcA : c ∈ A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hO : ∀ l ∈ L, l ∈ inSubgroup (aschbacherSolvableCore 3) K → l ∈ CFSG.Open.pCoreOf 2 L)
    (hsec : ∀ a ∈ A, (∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L) →
      a ∈ Subgroup.zpowers c) :
    Subgroup.zpowers (piX K A ⟨c, Subgroup.mem_sup_right hcA⟩) =
      aOne K A ⊓ Subgroup.centralizer
        (((L.subgroupOf (K ⊔ A)).map (piX K A) : Subgroup (QuotX K A)) : Set (QuotX K A)) := by
  have hJC := image_le_inf_centralizer (A := A) hLK hLc hcA
  apply le_antisymm
  · rw [Subgroup.zpowers_le]
    refine ⟨piX_mem_aOne hcA, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hJC hy).2)
  · rintro x ⟨hxA, hxC⟩
    obtain ⟨a, haA, rfl⟩ := exists_eq_piX_of_mem_aOne hxA
    have ha : ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ CFSG.Open.pCoreOf 2 L := by
      intro l hl
      have hlJ : piX K A ⟨l, Subgroup.mem_sup_left (hLK hl)⟩ ∈
          (L.subgroupOf (K ⊔ A)).map (piX K A) :=
        ⟨⟨l, Subgroup.mem_sup_left (hLK hl)⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
      have hc := Subgroup.mem_centralizer_iff.mp hxC _ hlJ
      have hone : piX K A (⟨a, Subgroup.mem_sup_right haA⟩ * ⟨l, Subgroup.mem_sup_left (hLK hl)⟩ *
          (⟨a, Subgroup.mem_sup_right haA⟩ : ↥(K ⊔ A))⁻¹ *
          (⟨l, Subgroup.mem_sup_left (hLK hl)⟩ : ↥(K ⊔ A))⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← hc]
        group
      have hθ := (piX_eq_one_iff hAp hAK _).mp hone
      have hlL : a * l * a⁻¹ * l⁻¹ ∈ L :=
        L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAL haA) l).mp hl) (L.inv_mem hl)
      exact hO _ hlL hθ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hsec a haA ha)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← map_zpow]
    congr 1
    apply Subtype.ext
    simpa using hk

end CFSG.RankThree.PartTwo.Sec19.Item19Res7Proof
