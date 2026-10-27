module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229L34Row
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z5
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZB
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.OrderPrimeConj
import CFSG.LocalAnalysis.RankFourTheoremC.Nongeneration.Planes
import CFSG.RankThree.GroupTheory.SteinbergCEMutualSupplementResidual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs (isConj_of_natCard_eq_prime_of_sylow_cyclic)
open CFSG.Open (pCoreOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.RankThree.PartOne.Census3 (IsoLie)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_l34_not_dvd (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (k : Sec7Core4 G) (hp3 : k.p = 3)
    {H : Subgroup G} (hH : Sec7Core4.Config k H)
    (hF : IsoLie ↥(CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H))
      (.A 2 ⟨2, 2, Nat.prime_two, by norm_num⟩))
    {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r) (hsp : IsStronglyPEmbedded r k.M) :
    ¬ r ∣ Nat.card ↥(H ⊓ k.M) := by
  intro hdvd
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' r hdvd
  have hyo : orderOf (y₀ : G) = r := by rw [Subgroup.orderOf_coe, hy₀]
  have h6 : Nat.Coprime (orderOf (y₀ : G)) 6 := by
    rw [hyo]
    refine (Nat.Prime.coprime_iff_not_dvd hr).2 fun h => ?_
    have := Nat.le_of_dvd (by norm_num) h
    interval_cases r <;> first | omega | exact absurd hr (by norm_num)
  obtain ⟨hyH, hyK⟩ := uc22ine229_l34_mem_pPrimeCore hG3 hRee k hp3 hH hF y₀.2 h6
  set K_ := CFSG.pPrimeCore k.p ↥H with hK_
  have hKM : ∀ x : ↥H, x ∈ K_ → (x : G) ∈ k.M := fun x hx =>
    k.pPrimeCore_le_of_not_le hH.not_le hH.two_le_pRank ⟨x, hx, rfl⟩
  set y' : ↥K_ := ⟨⟨y₀, hyH⟩, hyK⟩ with hy'
  have hy'o : orderOf y' = r := by
    rw [← Subgroup.orderOf_coe y', ← Subgroup.orderOf_coe (y' : ↥H)]
    exact hyo
  obtain ⟨P, hyP⟩ := (IsPGroup.of_card (p := r) (n := 1)
    (by rw [Nat.card_zpowers, hy'o, pow_one]) : IsPGroup r (zpowers y')).exists_le_sylow
  have hfr := Sylow.normalizer_sup_eq_top P
  have hnorm : ∀ n : ↥H, n ∈ normalizer ((P.map K_.subtype : Subgroup ↥H) : Set ↥H) →
      (n : G) ∈ k.M := by
    intro n hn
    have hyR : (⟨y₀, hyH⟩ : ↥H) ∈ (P.map K_.subtype : Subgroup ↥H) :=
      Subgroup.mem_map_of_mem K_.subtype (hyP (mem_zpowers y'))
    have h1 : n * ⟨y₀, hyH⟩ * n⁻¹ ∈ (P.map K_.subtype : Subgroup ↥H) :=
      (Subgroup.mem_normalizer_iff.1 hn _).1 hyR
    have h2 : ((n * ⟨y₀, hyH⟩ * n⁻¹ : ↥H) : G) ∈ k.M :=
      hKM _ (Subgroup.map_subtype_le _ h1)
    by_contra hnM
    have hg : (n : G)⁻¹ ∉ k.M := fun h => hnM (by simpa using k.M.inv_mem h)
    refine hsp.2.2 _ hg ?_
    have hy : (y₀ : G) ∈ k.M ⊓ k.M.map (MulAut.conj (n : G)⁻¹).toMonoidHom := by
      refine ⟨y₀.2.2, Subgroup.mem_map.2 ⟨(n : G) * y₀ * (n : G)⁻¹, h2, ?_⟩⟩
      simp [MulAut.conj_apply, mul_assoc]
    have h3 := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.2 hy)
    rwa [Nat.card_zpowers, hyo] at h3
  have hle : (⊤ : Subgroup ↥H) ≤ k.M.subgroupOf H := by
    rw [← hfr]
    exact sup_le (fun n hn => Subgroup.mem_subgroupOf.2 (hnorm n hn))
      (fun x hx => Subgroup.mem_subgroupOf.2 (hKM x hx))
  exact hH.not_le (Subgroup.subgroupOf_eq_top.1 (top_le_iff.1 hle))

theorem uc22ine229_l34_normalizes {M Y : Subgroup G} (hY : Y ∈ calC M) {X : Subgroup G}
    (hXY : X ≤ Y) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hXc : Nat.card X = q)
    (hsol : Group.IsSolvable ↥(normalizer (X : Set G) ⊓ M)) : M ≤ normalizer (Y : Set G) := by
  intro m hm
  by_contra hmY
  set W := Y.map (MulAut.conj m).toMonoidHom with hW
  have hMm : M.map (MulAut.conj m).toMonoidHom = M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer hm)
  have hWc : W ∈ calC M := UC6S846.calC_map M (MulAut.conj m) hMm hY
  have hne : W ≠ Y := fun h => hmY (UC6S846.mem_normalizer_iff_map_conj.2 h)
  have hXM : X ≤ M := hXY.trans hY.1.le
  have hcomm : ∀ w ∈ W, ∀ x ∈ X, w * x * w⁻¹ * x⁻¹ ∈ pCoreOf 2 M := fun w hw x hx =>
    uc22ine229_commutator_mem_of_ne hWc hY hne hw (hXY hx)
  have hWV : W ≤ pCoreOf 2 M ⊔ (normalizer (X : Set G) ⊓ M) := by
    intro w hw
    have hwM : w ∈ M := hWc.1.le hw
    set w' : ↥M := ⟨w, hwM⟩ with hw'
    have hcen : QuotientGroup.mk' (CFSG.pCore 2 ↥M) w' ∈ centralizer
        (((X.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M))) : Set (Bar2 M)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x', hx', rfl⟩
      rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq]
      have h1 := hcomm w⁻¹ (W.inv_mem hw) (x' : G)⁻¹ (X.inv_mem (Subgroup.mem_subgroupOf.1 hx'))
      rw [inv_inv, inv_inv] at h1
      refine (Subgroup.mem_map_iff_mem M.subtype_injective).1 ?_
      have h2 : M.subtype ((x' * w')⁻¹ * (w' * x')) = w⁻¹ * (x' : G)⁻¹ * w * (x' : G) := by
        simp [hw', mul_assoc]
      rw [h2]
      exact h1
    obtain ⟨y, hyN, hy⟩ := uc22ine229_exists_lift hXM hq hq2
      (IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])) (Subgroup.centralizer_le_normalizer _ hcen)
    have h3 : y⁻¹ * w' ∈ CFSG.pCore 2 ↥M := QuotientGroup.eq.1 hy
    have h4 : (y : G)⁻¹ * w ∈ pCoreOf 2 M := ⟨y⁻¹ * w', h3, rfl⟩
    have h5 : (y : G) ∈ normalizer (X : Set G) ⊓ M := ⟨hyN, y.2⟩
    rw [show w = (y : G) * ((y : G)⁻¹ * w) by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h5) (Subgroup.mem_sup_left h4)
  haveI : Group.IsNilpotent ↥(pCoreOf 2 M) := (UC6S846.isPGroup_pCoreOf M).isNilpotent
  haveI : Group.IsSolvable ↥(pCoreOf 2 M ⊔ (normalizer (X : Set G) ⊓ M)) :=
    CFSG.RankThree.GroupTheory.isSolvable_sup_of_le_normalizer
      (inf_le_right.trans (Subgroup.le_normalizer.trans
        (UC6S846.normalizer_le_normalizer_pCoreOf M))) inferInstance hsol
  haveI : Group.IsSolvable ↥W :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hWV)
      (Subgroup.inclusion_injective hWV)
  exact UC6S846.not_solvable_of_mem_calC
    (show W ∈ calC W from ⟨CFSG.Open.IsSubnormal.refl W, hWc.2⟩) inferInstance

theorem uc22ine229_l34_eq_mul {M Y : Subgroup G} (hYM : Y ≤ M)
    (hnorm : M ≤ normalizer (Y : Set G)) {X : Subgroup G} (hXY : X ≤ Y) {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hXc : Nat.card X = q) (hq1 : CFSG.Open.pRank q Y ≤ 1) :
    ∀ m ∈ M, ∃ h ∈ normalizer (X : Set G) ⊓ M, ∃ y ∈ Y, m = h * y := by
  haveI : Fact q.Prime := ⟨hq⟩
  intro m hm
  set Xm := X.map (MulAut.conj m).toMonoidHom with hXm
  have hXmY : Xm ≤ Y := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (hnorm hm) x).1 (hXY hx)
  have hrk : CFSG.Open.pRank q (⊤ : Subgroup ↥Y) ≤ 1 := by
    have h := CFSG.SectionRank.pRank_le_map hq.one_lt Y.subtype Y.subtype_injective ⊤
    rw [Subgroup.map_top, Subgroup.range_subtype] at h
    exact h.trans hq1
  have h1 : Nat.card (X.subgroupOf Y) = q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXY).toEquiv, hXc]
  have hXmc : Nat.card Xm = q :=
    (Nat.card_congr (MulEquiv.subgroupMap (MulAut.conj m) X).toEquiv).symm.trans hXc
  have h2 : Nat.card (Xm.subgroupOf Y) = q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXmY).toEquiv, hXmc]
  obtain ⟨g, hg⟩ := isConj_of_natCard_eq_prime_of_sylow_cyclic
    (fun Q => RankFourTheoremC.Nongeneration.isCyclic_sylow_of_pRank_le_one hq2 hrk Q) h1 h2
  have key : ∀ S : Subgroup ↥Y, (S.map (MulAut.conj g).toMonoidHom).map Y.subtype =
      (S.map Y.subtype).map (MulAut.conj (g : G)).toMonoidHom := by
    intro S
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have e : X.map (MulAut.conj (g : G)).toMonoidHom = Xm := by
    have e := congrArg (fun S : Subgroup ↥Y => S.map Y.subtype) hg
    rw [key, Subgroup.map_subgroupOf_eq_of_le hXY, Subgroup.map_subgroupOf_eq_of_le hXmY] at e
    exact e
  have hcomp1 : (MulAut.conj (m⁻¹ * (g : G))).toMonoidHom =
      (MulAut.conj m⁻¹).toMonoidHom.comp (MulAut.conj (g : G)).toMonoidHom := by
    ext x
    simp [mul_assoc]
  have hcomp2 : (MulAut.conj m⁻¹).toMonoidHom.comp (MulAut.conj m).toMonoidHom =
      MonoidHom.id G := by
    ext x
    simp [mul_assoc]
  have hn : m⁻¹ * (g : G) ∈ normalizer (X : Set G) := by
    rw [UC6S846.mem_normalizer_iff_map_conj, hcomp1, ← Subgroup.map_map, e, hXm,
      Subgroup.map_map, hcomp2, Subgroup.map_id]
  refine ⟨(g : G)⁻¹ * m, ⟨?_, M.mul_mem (M.inv_mem (hYM g.2)) hm⟩, m⁻¹ * g * m, ?_, by group⟩
  · simpa [mul_assoc] using (normalizer (X : Set G)).inv_mem hn
  · simpa using (Subgroup.mem_normalizer_iff.1 (hnorm (M.inv_mem hm)) (g : G)).1 g.2

end CFSG.LocalAnalysis.UniquenessCase.UC22
