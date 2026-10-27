module

public import CFSG.RankThree.PartTwo.Sec6.Item611ResProof
public import CFSG.RankThree.PartTwo.Sec6.Item611Res4ProofUPlusTools
public import CFSG.RankThree.PartTwo.Sec4.Item413FixProof
import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
import CFSG.RankThree.PartTwo.Sec4.Item413Cases
public import CFSG.RankThree.PartTwo.Sec6.Item612Local

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.Item211Proof
open CFSG.Assembly.RankThreeEven (projSL projSU)


@[expose] def Item611CoverCase {G : Type} [Group G] [Finite G] (A L : Subgroup G) (c : G) :
    Prop :=
  c ∈ L ∧
    Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) =
      ((Subgroup.zpowers c).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) ∧
    Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 ∧
    Blueprint.ChevalleyExceptionalModel ((L ⧸ aschbacherSolvableCore 3 L) ⧸
      Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) .G2 3 1 ∧
    ∀ a ∈ A, ∃ (ha : a ∈ Subgroup.normalizer (L : Set G)) (l : L),
      Res611Res4.thetaAct L ⟨a, ha⟩ = MulAut.conj (l : L ⧸ aschbacherSolvableCore 3 L)

namespace Res611Fix

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G}

omit [Finite G] in
theorem center_eq_map_zpowers {Φ₀ : lBar L ≃* lOne L A}
    (hΦ₀ : ∀ l : L, (Φ₀ (l : lBar L) : QuotX L A) = piX L A ⟨l, Subgroup.mem_sup_left l.2⟩)
    {c : G} (hcA : c ∈ A) (hcL : c ∈ L)
    (hZ : (Subgroup.center (lOne L A)).map (lOne L A).subtype =
      Subgroup.zpowers (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩)) :
    Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) =
      ((Subgroup.zpowers c).subgroupOf L).map (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) := by
  rw [← Res611.comap_eq_map_zpowers hΦ₀ hcA hcL hZ, ← map_center_mulEquiv Φ₀]
  exact (Subgroup.comap_map_eq_self_of_injective Φ₀.injective _).symm

theorem thetaAct_eq_conj {Φ₀ : lBar L ≃* lOne L A}
    (hΦ₀ : ∀ l : L, (Φ₀ (l : lBar L) : QuotX L A) = piX L A ⟨l, Subgroup.mem_sup_left l.2⟩)
    {a : G} (haA : a ∈ A) (ha : a ∈ Subgroup.normalizer (L : Set G)) (l : L)
    (hal : ∀ y ∈ lOne L A, piX L A ⟨a, Subgroup.mem_sup_right haA⟩ * y *
      (piX L A ⟨a, Subgroup.mem_sup_right haA⟩)⁻¹ =
        piX L A ⟨l, Subgroup.mem_sup_left l.2⟩ * y *
          (piX L A ⟨l, Subgroup.mem_sup_left l.2⟩)⁻¹) :
    Res611Res4.thetaAct L ⟨a, ha⟩ = MulAut.conj (l : L ⧸ aschbacherSolvableCore 3 L) := by
  ext z
  induction z using QuotientGroup.induction_on with
  | H y =>
    apply Φ₀.injective
    apply Subtype.ext
    rw [Res611Res4.thetaAct_mk, MulAut.conj_apply, hΦ₀, map_mul, map_mul, map_inv,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hΦ₀, hΦ₀]
    have hy : piX L A ⟨y, Subgroup.mem_sup_left y.2⟩ ∈ lOne L A :=
      ⟨⟨y, Subgroup.mem_sup_left y.2⟩, Subgroup.mem_subgroupOf.mpr y.2, rfl⟩
    rw [← hal _ hy, ← map_inv, ← map_mul, ← map_mul]
    rfl

end Res611Fix

section Certs


theorem Res611Fix.cases413 (h45 : Sec4.Item4_5) (h41 : Sec4.Item4_1LargePrime)
    (h413 : Sec4.Item4_13_forwardFix) {G : Type} [Group G] [Finite G] (hst : PartTwoStanding G)
    {A : Subgroup G} (hA : A ∈ partTwoS G) (hrank : 4 < CFSG.Open.pRank 3 A) {c : G}
    (hcA : c ∈ A) (hc1 : c ≠ 1) {L : Subgroup G} (hL : L ∈ lZeroStarAt A c)
    (hCA : A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c) :
    (∃ e ∈ A, ∃ m : ℕ, 2 < m ∧
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 2 (GaloisField 3 (3 * m))) ∧
        KFacts.InducesStdKind L e .field) ∨
      (A ≤ L ∧ ∃ (K : Subgroup (L ⧸ aschbacherSolvableCore 3 L)) (_ : K.Normal),
          K = ((Subgroup.zpowers c).subgroupOf L).map
            (QuotientGroup.mk' (aschbacherSolvableCore 3 L)) ∧
          (Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸ K ≃* projSU 4 3 1) ∨
            Nonempty ((L ⧸ aschbacherSolvableCore 3 L) ⧸ K ≃* Blueprint.NativeSporadic.McL))) ∨
      (A = Subgroup.zpowers c ⊔ (A ⊓ L) ∧ c ∉ L ∧
        (Blueprint.ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .G2 3 1 ∨
          Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* Blueprint.NativeSporadic.McL) ∨
          Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 4 (GaloisField 3 1)) ∨
          Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 4 3 1))) ∨
      Item611CoverCase A L c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hA.1.1
  have hAp : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a a.2)⟩
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hL
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) := le_centralizer_of_mem_thetaComponentsAt hLc
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩))
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hAe hcA hc1 L hLc
  have hq : IsQuasisimple (lBar L) := by
    obtain ⟨L', hL', hLL'⟩ := hLc
    rw [← hLL']
    exact LocalCores.isQuasisimple_of_mulEquiv (Sec13.thetaQuotEquivSub _ L') hL'.2.2
  have hΛ : SectionFourHyp ↥(L ⊔ A) := hst.toTheoremFourHyp.sectionFourHyp
    (fun htop => centralizer_ne_top hst.toTheoremFourHyp hc1
      (eq_top_iff.mpr (htop ▸ sup_le hLC hAC)))
  obtain ⟨Φ₀, hΦ₀⟩ := exists_lEquiv hAL
  have hX : SectionFourHyp (QuotX L A) := sectionFourHyp_quotX h41 hΛ hAp hAL Φ₀ hq
  obtain ⟨E₀, hE₀, hE₀A, -, U₀, hU₀, hU₀E⟩ :=
    mem_lZeroUnion_iff.mp (lZeroStar_subset_lZeroUnion A (lZeroStarAt_subset_lZeroStar A c hL))
  obtain ⟨hE₁, hE₁A, T, hT, hTc⟩ :=
    exists_eOne hAp hAL (Late.isE27_of_mem_partTwoE hE₀) hE₀A hU₀ hU₀E
  have hc₁ : orderOf (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) = 3 := by
    have h1 : (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) =
        ((aEquiv (L := L) hAp ⟨c, hcA⟩ : aOne L A) : QuotX L A) := rfl
    rw [h1, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hAe.2 c hcA) hc1
  have hT' : T ∈ invariantPiSubgroups ⊤ ((E₀.subgroupOf (L ⊔ A)).map (piX L A)) (piOf 2) := by
    obtain ⟨-, hT2, hTN⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hT
    exact (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hT2, hTN⟩
  have htriple : Sec4.IsTriple413 (lOne L A) (aOne L A) ((E₀.subgroupOf (L ⊔ A)).map (piX L A))
      (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) :=
    ⟨maximal_aOne hAe hA.1.2.1, aOne_inf_centralizer hAp hAL hcA hCA, hc₁, hE₁, hE₁A, T, hT',
      hTc⟩
  have hrank₁ : 4 < CFSG.Open.pRank 3 (aOne L A) := by
    rw [← CFSG.RankThreeEvenClassification.Helpers.pRank_eq_of_subgroup_equiv 3 Nat.prime_three
      A (aOne L A) (aEquiv hAp)]
    exact hrank
  have hπc1 : piX L A ⟨c, Subgroup.mem_sup_right hcA⟩ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hc₁
    omega
  rcases h413 (QuotX L A) hX (lOne L A) (isComponent_lOne hAL Φ₀ hq) (aOne L A) _ _ htriple
      hrank₁ with
    (⟨e, he, m, hm, ⟨φ⟩, hfield⟩ | ⟨hAL1, K, hK, hKc, hiso⟩ | ⟨hdec, hdisj, hiso⟩) |
      ⟨-, hZ₁, hM₁, hinner₁⟩
  ·
    obtain ⟨e', he', rfl⟩ := he
    have heA : (e' : G) ∈ A := hE₀A (Subgroup.mem_subgroupOf.mp he')
    have he'' : e' = ⟨(e' : G), Subgroup.mem_sup_right heA⟩ := rfl
    rw [he''] at hfield
    exact Or.inl ⟨e', heA, m, hm, ⟨Φ₀.trans φ⟩, inducesStdKind_of_lOne hAL hΦ₀ heA hfield⟩
  ·
    have hAL' := Res611.le_of_aOne_le_lOne hAp hAL hAL1
    have hcL : c ∈ L := hAL' hcA
    have hK'n : (K.comap Φ₀.toMonoidHom).Normal := hK.comap _
    have hK'map : (K.comap Φ₀.toMonoidHom).map Φ₀.toMonoidHom = K :=
      Subgroup.map_comap_eq_self_of_surjective Φ₀.surjective K
    let eq : lBar L ⧸ K.comap Φ₀.toMonoidHom ≃* ↥(lOne L A) ⧸ K :=
      QuotientGroup.congr _ K Φ₀ hK'map
    refine Or.inr (Or.inl ⟨hAL', K.comap Φ₀.toMonoidHom, hK'n,
      Res611.comap_eq_map_zpowers hΦ₀ hcA hcL hKc, ?_⟩)
    rcases hiso with hψ | hψ
    · exact Or.inl (hψ.map eq.trans)
    · exact Or.inr (hψ.map eq.trans)
  ·
    refine Or.inr (Or.inr (Or.inl ⟨Res611.eq_sup_of_aOne_eq hAp hAL hcA hdec,
      Res611.not_mem_of_inf_eq_bot hcA hπc1 hdisj, ?_⟩))
    rcases hiso with h | hψ | hψ | hψ
    · exact Or.inl (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv Φ₀ h)
    · exact Or.inr (Or.inl (hψ.map Φ₀.trans))
    · exact Or.inr (Or.inr (Or.inl (hψ.map Φ₀.trans)))
    · exact Or.inr (Or.inr (Or.inr (hψ.map Φ₀.trans)))
  ·
    refine Or.inr (Or.inr (Or.inr ?_))
    have hcL₁ : piX L A ⟨c, Subgroup.mem_sup_right hcA⟩ ∈ lOne L A := by
      have h1 : piX L A ⟨c, Subgroup.mem_sup_right hcA⟩ ∈
          (Subgroup.center (lOne L A)).map (lOne L A).subtype := by
        rw [hZ₁]
        exact Subgroup.mem_zpowers _
      obtain ⟨z, -, hz⟩ := h1
      rw [← hz]
      exact z.2
    have hcL : c ∈ L := Res611.mem_of_piX_mem_lOne (g := ⟨c, Subgroup.mem_sup_right hcA⟩) hAp hAL
      hcL₁
    have hZL := Res611Fix.center_eq_map_zpowers hΦ₀ hcA hcL hZ₁
    have hc3 : IsPGroup 3 (Subgroup.zpowers c) :=
      IsPGroup.of_card (n := 1) (by
        rw [Nat.card_zpowers, orderOf_eq_prime (hAe.2 c hcA) hc1, pow_one])
    refine ⟨hcL, hZL, ?_, CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv
      (quotientCenterCongr Φ₀) hM₁, fun a haA => ?_⟩
    · rw [hZL, Res611Res4.card_map_mk_of_isPGroup hc3 (Subgroup.zpowers_le.mpr hcL),
        Nat.card_zpowers, orderOf_eq_prime (hAe.2 c hcA) hc1]
    · obtain ⟨l₁, hl₁, hal₁⟩ := hinner₁ _ (piX_mem_aOne haA)
      obtain ⟨g, hg, rfl⟩ := hl₁
      have hgL : (g : G) ∈ L := Subgroup.mem_subgroupOf.mp hg
      refine ⟨hAL haA, ⟨g, hgL⟩, Res611Fix.thetaAct_eq_conj hΦ₀ haA (hAL haA) ⟨g, hgL⟩ ?_⟩
      intro y hy
      rw [hal₁ y hy]

end Certs

end CFSG.RankThree.PartTwo.Sec6
