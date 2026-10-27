module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S206v
public import CFSG.LocalAnalysis.UniquenessCase.UC22S206t
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
import CFSG.LocalAnalysis.UniquenessCase.UC22S206k
import CFSG.LocalAnalysis.UniquenessCase.UC22S206n
import CFSG.LocalAnalysis.UniquenessCase.UC22S206p
import CFSG.LocalAnalysis.UniquenessCase.UC22S206r
import CFSG.LocalAnalysis.UniquenessCase.UC22Sec7K2
import CFSG.LocalAnalysis.UniquenessCase.UC22SigmaThree
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall2
import CFSG.LocalAnalysis.AGLEmbedding.BlockThreeCentCoprimeOut
import CFSG.LocalAnalysis.EvenSmallLie.CatalogOrdersLie
public import CFSG.LocalAnalysis.UniquenessCase.UC22S206b
import CFSG.LocalAnalysis.AGLEmbedding.SporadicBetaSmall

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.Quasithin.H13.A7Blk (ptPre ptCore ptCore_le ptCore_le_ptPre coe_ptHom ptHom
  ptHom_surjective ker_ptHom)
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeaf (LieOrderFormulasInput)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Sec7Core4 StronglyEmbeddedFive)

variable {G : Type} [Group G]

theorem uc22s206w_pRank_aut
    {X : Type} [Group X] [Finite X] (hZ : Subgroup.center X = ⊥)
    (h : IsAlt X 8 ∨ LieModel X .PSL 5 2 1 ∨ IsSpor X .M24 ∨ IsSpor X .J4) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ 2 := by
  have key : ¬ p ∣ Nat.card (Outer X) → (¬ p ^ 3 ∣ Nat.card X ∨ (¬ p ^ 4 ∣ Nat.card X ∧
      CFSG.RankThree.PartOne.StrongP.HasNoncommPair p X)) →
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ 2 := fun hOut h' =>
    (CFSG.AGLEmbedding.pRank_top_mulAut_le_of_not_dvd hp hZ hOut).trans (by
      rcases h' with h3 | ⟨h4, hpair⟩
      · exact CFSG.RankThree.PartTwo.Census.pRank_le_two_of_not_dvd hp h3
      · exact CFSG.AGLEmbedding.pRank_le_two_of_hasNoncommPair hp h4 hpair)
  have small : ∀ {Y : Type} [Group Y], Nonempty (X ≃* Y) →
      CFSG.AGLEmbedding.SporadicSmallData Y →
      CFSG.Open.pRank p (⊤ : Subgroup (MulAut X)) ≤ 2 := by
    rintro Y _ ⟨e⟩ ⟨hOut, hs⟩
    refine key (fun hd => ?_) ?_
    · have h1 : Nat.card (Outer X) = Nat.card (Outer Y) := Nat.card_congr (equivalence e).toEquiv
      have := Nat.le_of_dvd Nat.card_pos hd
      omega
    · rw [Nat.card_congr e.toEquiv]
      exact (hs p hp (by omega)).imp_right fun h' => ⟨h'.1, h'.2.map e.symm.toMonoidHom
        e.symm.injective⟩
  rcases h with h | h | h | h
  · obtain ⟨e⟩ : Nonempty (X ≃* alternatingGroup (Fin 8)) := h
    exact (CFSG.AGLEmbedding.pRank_top_mulAut_le (by norm_num) (by norm_num) e hp).trans
      (Nat.div_le_of_le_mul (by omega))
  · have hst := CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) h
    refine key (CFSG.AGLEmbedding.not_dvd_card_outer_of_psl_two_of_five_le hst hp hp5) (Or.inl ?_)
    rw [CFSG.EvenSmallLie.CatalogOrders.card_eq_lieOrd_of_classical hst,
      show CFSG.EvenSmallLie.CatalogOrders.lieOrd .PSL 5 (2 ^ 1) = 9999360 by decide +kernel]
    intro hd
    have hmem : p ∈ Nat.primeFactors 9999360 :=
      Nat.mem_primeFactors.2 ⟨hp, (dvd_pow_self p (by norm_num)).trans hd, by norm_num⟩
    rw [show Nat.primeFactors 9999360 = {2, 3, 5, 7, 31} by norm_num [Nat.primeFactors]] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with rfl | rfl | rfl | rfl | rfl <;> first | omega | norm_num at hd
  · obtain ⟨e⟩ : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M24) := h
    exact small ⟨e⟩ CFSG.AGLEmbedding.sporadicSmallData_M24
  · obtain ⟨e⟩ : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .J4) := h
    exact small ⟨e⟩ CFSG.AGLEmbedding.sporadicSmallData_J4

theorem uc22s206w_kernel {Y B : Type*} [Group Y] [Finite Y] [Group B] [Finite B] (π : Y →* B)
    {C : Subgroup B} (hCn : C.Normal) {p : ℕ} (hp : p.Prime)
    (hC : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥C)) ≤ 2) {R : Subgroup Y}
    (hR : IsElemAbelian p R) {m : ℕ} (hm : 4 ≤ m) (hRc : Nat.card R = p ^ m) :
    ∃ F ≤ R, (∃ j, 2 ≤ j ∧ Nat.card F = p ^ j) ∧ F.map π ≤ centralizer (C : Set B) := by
  haveI := hCn
  haveI : Fact p.Prime := ⟨hp⟩
  let θ : Y →* MulAut ↥C := MulAut.conjNormal.comp π
  refine ⟨θ.ker ⊓ R, inf_le_right, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := IsPGroup.iff_card.mp (hR.map θ).isPGroup
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (hR.isPGroup.to_le (inf_le_right : θ.ker ⊓ R ≤ R))
    have hi2 := (CFSG.SectionRank.le_pRank hp.one_lt le_top (hR.map θ) hi).trans hC
    have h := Subgroup.relIndex_mul_card θ.ker R
    rw [Subgroup.relIndex_ker, hi, hj, hRc, ← pow_add] at h
    have := Nat.pow_right_injective hp.two_le h
    exact ⟨j, by omega, hj⟩
  · rintro _ ⟨f, hf, rfl⟩
    refine mem_centralizer_iff.mpr fun b hb => ?_
    have h1 : ((θ f ⟨b, hb⟩ : ↥C) : B) = b := by
      rw [(MonoidHom.mem_ker.mp hf.1 : θ f = 1)]
      rfl
    have h2 : π f * b * (π f)⁻¹ = b := h1
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm

theorem uc22s206w_centralize {Y B : Type*} [Group Y] [Finite Y] [Group B] [Finite B] (π : Y →* B)
    (h2 : IsPGroup 2 π.ker) {C : Subgroup B} {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {E F : Subgroup Y} (hE : IsPGroup 3 E) (hEC : E.map π ≤ C) (hF : IsPGroup p F)
    (hFC : F.map π ≤ centralizer (C : Set B)) :
    ∃ c : Y, F.map (MulAut.conj c).toMonoidHom ≤ centralizer (E : Set Y) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfc : ∀ f ∈ F, ∀ b ∈ C, π f * b * (π f)⁻¹ = b := fun f hf b hb => by
    rw [← mem_centralizer_iff.mp (hFC (mem_map_of_mem π hf)) b hb, mul_inv_cancel_right]
  set H : Subgroup Y := (E.map π).comap π with hH
  have hHC : ∀ y ∈ H, π y ∈ C := fun y hy => hEC hy
  have hHp : ¬ p ∣ Nat.card H := by
    have h := Subgroup.relIndex_mul_card π.ker H
    rw [Subgroup.relIndex_ker] at h
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp
      ((hE.map π).to_le (map_comap_le π (E.map π)) : IsPGroup 3 ↥(H.map π))
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp
      (h2.to_le (inf_le_left : π.ker ⊓ H ≤ π.ker) : IsPGroup 2 ↥(π.ker ⊓ H))
    rw [ha, hb] at h
    rw [← h]
    intro hd
    rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp (hp.dvd_of_dvd_pow hd)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd)
      omega
  have hFN : F ≤ normalizer (H : Set Y) := fun f hf => mem_normalizer_iff.mpr fun y => by
    constructor
    · intro hy
      show π (f * y * f⁻¹) ∈ E.map π
      rw [map_mul, map_mul, map_inv, hfc f hf _ (hHC y hy)]
      exact hy
    · intro hy
      have hb := hfc f hf _ (hHC _ hy)
      have hy' : π y = π (f * y * f⁻¹) := by
        calc π y = (π f)⁻¹ * π (f * y * f⁻¹) * π f := by rw [map_mul, map_mul, map_inv]; group
          _ = (π f)⁻¹ * (π f * π (f * y * f⁻¹) * (π f)⁻¹) * π f := by rw [hb]
          _ = π (f * y * f⁻¹) := by group
      show π y ∈ E.map π
      rw [hy']
      exact hy
  let φ : ↥F →* MulAut ↥H := H.normalizerMonoidHom.comp (Subgroup.inclusion hFN)
  have hφ : ∀ (f : Y) (hf : f ∈ F) (q : ↥H), ((φ ⟨f, hf⟩ q : ↥H) : Y) = f * q * f⁻¹ :=
    fun _ _ _ => rfl
  obtain ⟨Q, hQ⟩ :=
    CFSG.OrderReductions.InvariantSylow.exists_invariant_sylow_of_coprime p 3 hF hHp φ
  obtain ⟨⟨c, _⟩, hc⟩ :=
    CFSG.RankThreeCoreUniqueness.Helpers.pGroup_conjugate_into_sylow_within_overgroup 3
      Nat.prime_three Q ⊤ le_top (E.subgroupOf H) hE.comap_subtype le_top
  have hFQ : ∀ f ∈ F, ∀ q ∈ (Q : Subgroup ↥H), f * (q : Y) = q * f := by
    intro f hf q hq
    have hw : φ ⟨f, hf⟩ q * q⁻¹ ∈ (Q : Subgroup ↥H) := by
      refine mul_mem ?_ (inv_mem hq)
      rw [← hQ ⟨f, hf⟩]
      exact ⟨q, hq, rfl⟩
    have hwk : ((φ ⟨f, hf⟩ q * q⁻¹ : ↥H) : Y) ∈ π.ker := by
      rw [MonoidHom.mem_ker, Subgroup.coe_mul, hφ, Subgroup.coe_inv, map_mul, map_mul, map_mul,
        map_inv, map_inv, hfc f hf _ (hHC q q.2), mul_inv_cancel]
    have h1 : ((φ ⟨f, hf⟩ q * q⁻¹ : ↥H) : Y) = 1 := Subgroup.disjoint_def.mp
      (IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ (Q.isPGroup'.map H.subtype) h2)
      ⟨_, hw, rfl⟩ hwk
    rw [Subgroup.coe_mul, hφ, Subgroup.coe_inv, mul_inv_eq_one] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  refine ⟨(c : Y)⁻¹, ?_⟩
  rintro _ ⟨f, hf, rfl⟩
  refine mem_centralizer_iff.mpr fun e he => ?_
  have h : f * ((c : Y) * e * (c : Y)⁻¹) = (c : Y) * e * (c : Y)⁻¹ * f :=
    hFQ f hf _ (hc ⟨⟨e, le_comap_map π E he⟩, he, rfl⟩)
  show e * ((c : Y)⁻¹ * f * (c : Y)⁻¹⁻¹) = (c : Y)⁻¹ * f * (c : Y)⁻¹⁻¹ * e
  rw [inv_inv]
  calc e * ((c : Y)⁻¹ * f * c) = (c : Y)⁻¹ * ((c * e * (c : Y)⁻¹) * f) * c := by group
    _ = (c : Y)⁻¹ * (f * (c * e * (c : Y)⁻¹)) * c := by rw [h]
    _ = (c : Y)⁻¹ * f * c * e := by group

theorem uc22s206w_E9 [Finite G] {L M : Subgroup G} (α : ↥L →* alternatingGroup (Fin 9))
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥L) {i : Fin 9}
    (hLM : L ⊓ M = ptPre α i) :
    ∃ E : Subgroup ↥(ptCore α i), IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧
      ∃ x ∈ E, orderOf x = 3 ∧ ¬ normalizer (zpowers (x : G) : Set G) ≤ M := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hb3, -, hb1, -, -, -, -⟩ := uc22s206p_rel
  obtain ⟨hE₀, hE₀c⟩ := uc22s206p_E9
  have hinj := uc22s206gEmb_injective i
  have hβ2 : IsPGroup 2 (ptHom α i).ker := by
    rw [ker_ptHom α hα hker (by norm_num) i]
    exact CFSG.pCore_isPGroup
  set X₀ := (zpowers uc22s206pA0 ⊔ zpowers uc22s206pB0).map (uc22s206gEmb i) with hX₀
  have hXc : Nat.card X₀ = 3 ^ 2 := by rw [hX₀, card_map_of_injective hinj, hE₀c]
  obtain ⟨s, hs⟩ := uc22s206d_section (ptHom α i) (ptHom_surjective α hα (by norm_num) i) hβ2 X₀
    (by rw [hXc]; exact ⟨4, rfl⟩)
  have hsinj : Function.Injective s := fun q q' h => Subtype.ext (by rw [← hs q, ← hs q', h])
  have hT : IsElemAbelian 3 (⊤ : Subgroup ↥X₀) := by
    rw [← Subgroup.subgroupOf_self]
    exact (hE₀.map _).subgroupOf X₀
  have hqb : uc22s206gEmb i uc22s206pB0 ∈ X₀ := mem_map_of_mem _ (mem_sup_right (mem_zpowers _))
  have hq3 : (⟨_, hqb⟩ : ↥X₀) ^ 3 = 1 := Subtype.ext (by
    show uc22s206gEmb i uc22s206pB0 ^ 3 = 1
    rw [← map_pow, hb3, map_one])
  have hx3 : s ⟨_, hqb⟩ ^ 3 = 1 := by rw [← map_pow, hq3, map_one]
  have hx : ptHom α i (s ⟨_, hqb⟩) = uc22s206gEmb i uc22s206pB0 := hs _
  have hx1 : s ⟨_, hqb⟩ ≠ 1 := fun h1 => hb1 (hinj (by rw [← hx, h1, map_one, map_one]))
  refine ⟨(⊤ : Subgroup ↥X₀).map s, hT.map s, ?_, s ⟨_, hqb⟩, mem_map_of_mem s (mem_top _),
    orderOf_eq_prime hx3 hx1, ?_⟩
  · rw [card_map_of_injective hsinj, card_top, hXc]
  have hαx : α (Subgroup.inclusion (ptCore_le α i) (s ⟨_, hqb⟩)) =
      (uc22s206gEmb i uc22s206pB0 : alternatingGroup (Fin 9)) := by
    have h := congrArg Subtype.val hx
    rw [coe_ptHom] at h
    exact h
  have hx3' : orderOf (Subgroup.inclusion (ptCore_le α i) (s ⟨_, hqb⟩)) = 3 := by
    rw [orderOf_injective _ (Subgroup.inclusion_injective (ptCore_le α i)),
      orderOf_eq_prime hx3 hx1]
  refine uc22s206h_not_le_of_commute α hα hker hLM Nat.prime_three (by decide) hx3'
    (c := uc22s206gC i) ?_ ?_
  · rw [hαx]
    exact uc22s206h_commute i (by decide) (by decide)
  · rw [uc22s206gC_apply]
    exact Fin.succAbove_ne i 0

theorem uc22s206w_false
    [Finite G] (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma)
    (hSE : StronglyEmbeddedFive) (hK331 : InS3.K331) (hN : uc22p20rNativeGriess)
    (h82 : F08.R82 (UC6.dataOfSetup4 hS hU S)) (hk : (UC6.dataOfSetup4 hS hU S).k = 2)
    {L : Subgroup G} (α : ↥L →* alternatingGroup (Fin 9)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) {i : Fin 9} (hLM : L ⊓ S.M = ptPre α i)
    (hKM : ptCore α i ≤ S.M) (hTK : S.T ≤ normalizer (ptCore α i : Set G))
    (hF : ⁅((ptCore α i).subgroupOf S.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥S.M)),
      CFSG.fittingSubgroup (Bar2 S.M)⁆ = ⊥)
    (hNc : ∀ J : Subgroup (Bar2 S.M), IsComponentOf J ⊤ →
      ((ptCore α i).subgroupOf S.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥S.M)) ≤
        normalizer (J : Set (Bar2 S.M)))
    (hout : ∀ J : Subgroup (Bar2 S.M), IsComponentOf J ⊤ →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (J ⧸ Subgroup.center J))) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨h3, hp, hp5, hp4⟩ := uc22s206v_ranks hS hU S hσ hk
  obtain ⟨C, hC, hCn, hZ, hcase, hKC⟩ := uc22s206v_component (UC6.dataOfSetup4 hS hU S) hK331
    hN h82 hk h3 α hα hker hKM S.sylowM hTK hF hNc hout
  obtain ⟨R, hRM, hR, hRc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt S.M
  have hR' := hR.subgroupOf S.M
  obtain ⟨F, hFR, ⟨j, hj, hFc⟩, hFC⟩ := uc22s206w_kernel (QuotientGroup.mk' (CFSG.pCore 2 ↥S.M))
    hCn hp (uc22s206w_pRank_aut hZ hcase hp hp5) hR' hp4
    ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRM).toEquiv).trans hRc)
  obtain ⟨EK, hEK, hEKc, x, hxE, hx3, hxN⟩ := uc22s206w_E9 α hα hker hLM
  obtain ⟨c, hc⟩ := uc22s206w_centralize (QuotientGroup.mk' (CFSG.pCore 2 ↥S.M))
    (by rw [QuotientGroup.ker_mk']; exact CFSG.pCore_isPGroup) (C := C) hp hp5
    (E := EK.map (Subgroup.inclusion hKM)) (hEK.map _).isPGroup
    (by rintro _ ⟨_, ⟨k, -, rfl⟩, rfl⟩; exact hKC k) (hR'.mono hFR).isPGroup hFC
  obtain ⟨EG, hEG⟩ : ∃ EG : Subgroup G, EG = (EK.map (Subgroup.inclusion hKM)).map S.M.subtype :=
    ⟨_, rfl⟩
  have hEGM : EG ≤ S.M := by
    rw [hEG]
    exact map_subtype_le _
  have hEGa : IsElemAbelian 3 EG := by
    rw [hEG]
    exact (hEK.map _).map _
  have hEGc : Nat.card EG = 3 ^ 2 := by
    rw [hEG, card_map_of_injective S.M.subtype_injective,
      card_map_of_injective (Subgroup.inclusion_injective hKM), hEKc]
  have hF₁ : (F.map (MulAut.conj c).toMonoidHom).map S.M.subtype ≤
      S.M ⊓ centralizer (EG : Set G) := by
    rw [hEG]
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨z.2, mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact congrArg Subtype.val (mem_centralizer_iff.mp (hc hz) y hy)
  have hrank : 2 ≤ CFSG.Open.pRank S.p (S.M ⊓ centralizer (EG : Set G)) :=
    hj.trans (CFSG.SectionRank.le_pRank hp.one_lt hF₁ (((hR'.mono hFR).map _).map _)
      (by rw [card_map_of_injective S.M.subtype_injective,
        card_map_of_injective (MulAut.conj c).injective, hFc]))
  obtain ⟨A, hA, -⟩ := uc22s206r_calC (UC6.dataOfSetup4 hS hU S) hC
  have hΓ := conclusion76_setup4_k_eq_two_of_calC hSE hS hU S hσ
    (UC6S846.sigmaStd_dataOfSetup4 hS hU S) hA hk S.hp 3 Nat.prime_three EG hEGM hEGa hEGc
    (lt_of_lt_of_le (by norm_num) hrank) fun X hX _ =>
      lt_of_lt_of_le (by norm_num) (hrank.trans (CFSG.SectionRank.pRank_mono hp.one_lt
        (inf_le_inf_left _ ((centralizer_le (SetLike.coe_subset_coe.mpr hX)).trans
          (centralizer_le_normalizer _)))))
  have hxEG : (x : G) ∈ EG := by
    rw [hEG]
    exact ⟨Subgroup.inclusion hKM x, mem_map_of_mem _ hxE, rfl⟩
  have hx3G : orderOf (x : G) = 3 := by rw [Subgroup.orderOf_coe, hx3]
  exact hxN ((le_sSup ⟨zpowers (x : G), zpowers_le.mpr hxEG,
    CFSG.SectionRank.le_pRank (by norm_num) le_rfl
      (isElemAbelian_zpowers (by rw [← hx3G]; exact pow_orderOf_eq_one _))
      (by rw [Nat.card_zpowers, hx3G, pow_one]), rfl⟩ :
        normalizer (zpowers (x : G) : Set G) ≤ rankThreeGamma 1 3 EG).trans hΓ)

theorem uc22s206w_s20_6
    [Finite G] (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma)
    (hO : LieOrderFormulasInput) (hB : ListBNonabelian) (hK331 : InS3.K331)
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor CFSG.Assembly.InCatalog)
    (hN : uc22p20rNativeGriess) (h82 : F08.R82 (UC6.dataOfSetup4 hS hU S))
    (hSE : StronglyEmbeddedFive) : S20_6 (UC6.dataOfSetup4 hS hU S) := by
  intro h1930 L hL h9
  set D := UC6.dataOfSetup4 hS hU S
  obtain ⟨hk, α, hα, hker, i, -, hLM, hTK, -⟩ := uc22s206b_by1930 D hO hB h1930 hL h9
  have h3 : 3 ∉ uniqueFourBeta G := three_not_mem_uniqueFourBeta hS hU S hσ hk
  have hchar : S.M ⊓ centralizer (CFSG.Open.pCoreOf 2 S.M : Set G) ≤ CFSG.Open.pCoreOf 2 S.M :=
    hS.charTwo S.M S.maxLocal.1
  have hLM' : L ⊓ S.M = ptPre α i := hLM
  have hKM : ptCore α i ≤ D.M := by
    refine (ptCore_le_ptPre α i).trans ?_
    rw [← hLM]
    exact inf_le_right
  by_cases hF : ⁅((ptCore α i).subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)),
      CFSG.fittingSubgroup (Bar2 D.M)⁆ = ⊥
  swap
  · exact uc22s206k_false hU S.maxLocal hchar α hα hker hLM' hF
      fun p hp hsp h5 Y hY hYM hrank hQ => Sec7Core4.normalizer_le_of_stronglyEmbeddedFive
        (.ofUnique hS hU S.M S.maxLocal p hp hsp) h5 h3 hSE hY hYM hrank hQ
  by_cases hNc : ∀ J : Subgroup (Bar2 D.M), IsComponentOf J ⊤ →
      ((ptCore α i).subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) ≤
        normalizer (J : Set (Bar2 D.M))
  swap
  · push Not at hNc
    exact uc22s206n_false hU S.maxLocal hchar α hα hker hLM' hNc
      fun p hp hsp h5 Y hY hYM hrank hQ => Sec7Core4.normalizer_le_of_stronglyEmbeddedFive
        (.ofUnique hS hU S.M S.maxLocal p hp hsp) h5 h3 hSE hY hYM hrank hQ
  exact uc22s206w_false hS hU S hσ hSE hK331 hN h82 hk α hα hker hLM' hKM hTK hF hNc
    fun J hJ => uc22s206t_outSolvable D hSch hJ

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
