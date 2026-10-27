module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT8Abs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT8Front
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenT7Proof
public import CFSG.Quasithin.Background.G64NatSec
public import CFSG.Quasithin.Background.D2Coprime
public import CFSG.Quasithin.Background.B4ModelsWitness

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_T8_iSup_subtype_ne {A : Type*} [CompleteLattice A] {S : Set A} (i : S) :
    (⨆ j : S, ⨆ (_ : j ≠ i), (j : A)) = ⨆ Z ∈ S, ⨆ (_ : Z ≠ (i : A)), Z := by
  apply le_antisymm
  · refine iSup_le fun j => iSup_le fun hj => ?_
    refine le_iSup_of_le (j : A) (le_iSup_of_le j.2 ?_)
    exact le_iSup_of_le (fun h => hj (Subtype.ext h)) le_rfl
  · refine iSup_le fun Z => iSup_le fun hZ => iSup_le fun hZne => ?_
    exact le_iSup_of_le (⟨Z, hZ⟩ : S)
      (le_iSup_of_le (fun h => hZne (congrArg Subtype.val h)) le_rfl)

private theorem s15_T8_card_sSup_eq_prod {A : Type*} [Group A] [Finite A]
    {𝓤 : Set (Subgroup A)} [Fintype 𝓤] (hind : sSupIndep 𝓤)
    (hcomm : ∀ U ∈ 𝓤, ∀ W ∈ 𝓤, U ≠ W → ∀ x ∈ U, ∀ y ∈ W, Commute x y) :
    Nat.card ↥(sSup 𝓤) = ∏ i : 𝓤, Nat.card ↥(i : Subgroup A) := by
  classical
  let H : 𝓤 → Subgroup A := Subtype.val
  have hind' : iSupIndep H := (sSupIndep_iff 𝓤).mp hind
  have hcomm' : Pairwise fun i j : 𝓤 => ∀ x y : A, x ∈ H i → y ∈ H j → Commute x y := by
    intro i j hij x y hx hy
    exact hcomm i i.2 j j.2 (fun h => hij (Subtype.ext h)) x hx y hy
  let φ := Subgroup.noncommPiCoprod hcomm'
  have hφinj : Function.Injective φ := Subgroup.injective_noncommPiCoprod_of_iSupIndep hind'
  have hrange : φ.range = sSup 𝓤 := by
    rw [Subgroup.noncommPiCoprod_range, sSup_eq_iSup']
  have hcard : Nat.card ↥(sSup 𝓤) = ∏ i : 𝓤, Nat.card ↥(H i) := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm.trans
      (Nat.card_pi (β := fun i : 𝓤 => ↥(H i)))
  simpa only [H] using hcard

private theorem s15_T8_exists_enum (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hs4 : s15 D.M V₀ V h.isElemAbelian L = 4) :
    ∃ (B : Fin 4 → Subgroup (MulAut (Vtil V₀ V h.isElemAbelian)))
      (m : Fin 4 → D.M) (jidx : D.M → Fin 4),
      B 0 = barSub V₀ V h.isElemAbelian L ∧ Function.Injective B ∧
      (∀ j, B j = barSub V₀ V h.isElemAbelian (conjSubgroup L (m j))) ∧
      (∀ μ : D.M, B (jidx μ) = barSub V₀ V h.isElemAbelian (conjSubgroup L μ)) := by
  classical
  let f : D.M → Subgroup (MulAut (Vtil V₀ V h.isElemAbelian)) :=
    fun μ => barSub V₀ V h.isElemAbelian (conjSubgroup L (μ : G))
  let S : Set (Subgroup (MulAut (Vtil V₀ V h.isElemAbelian))) := Set.range f
  haveI : Fintype S := (Set.toFinite S).fintype
  have hScard : S.ncard = 4 := (s15_Core_s15_eq_ncard_range h).symm.trans hs4
  have hFcard : Fintype.card S = 4 := by rw [Set.fintypeCard_eq_ncard, hScard]
  let e₀ : S ≃ Fin 4 := Fintype.equivFinOfCardEq hFcard
  let s₀ : S := ⟨barSub V₀ V h.isElemAbelian L, by
    refine ⟨1, ?_⟩
    simp only [f]
    rw [show ((1 : D.M) : G) = 1 from rfl, conjSubgroup_one]⟩
  let e : S ≃ Fin 4 := e₀.trans (Equiv.swap 0 (e₀ s₀))
  have he0 : e s₀ = 0 := by
    simp only [e, Equiv.trans_apply]
    exact Equiv.swap_apply_right 0 (e₀ s₀)
  let B : Fin 4 → Subgroup (MulAut (Vtil V₀ V h.isElemAbelian)) := fun j => (e.symm j).val
  let m : Fin 4 → D.M := fun j => Classical.choose (e.symm j).2
  have hm : ∀ j, f (m j) = B j := fun j => Classical.choose_spec (e.symm j).2
  let jidx : D.M → Fin 4 := fun μ => e ⟨f μ, ⟨μ, rfl⟩⟩
  refine ⟨B, m, jidx, ?_, ?_, ?_, ?_⟩
  · show (e.symm 0).val = barSub V₀ V h.isElemAbelian L
    rw [← he0, Equiv.symm_apply_apply]
  · intro i j hij
    exact e.symm.injective (Subtype.ext hij)
  · intro j
    exact (hm j).symm
  · intro μ
    show (e.symm (e ⟨f μ, ⟨μ, rfl⟩⟩)).val = f μ
    rw [Equiv.symm_apply_apply]

private def s15_T8_fixPts {W : Type*} [Group W] (U : Subgroup W) : Subgroup (MulAut W) where
  carrier := {c | ∀ y ∈ U, c y = y}
  one_mem' := fun y _ => rfl
  mul_mem' := fun ha hb y hy => by rw [MulAut.mul_apply, hb y hy, ha y hy]
  inv_mem' := fun {a} ha y hy => by
    refine a.injective ?_
    rw [ha y hy]
    simp

private theorem s15_T8_mem_fixPts {W : Type*} [Group W] {U : Subgroup W} {c : MulAut W} :
    c ∈ s15_T8_fixPts U ↔ ∀ y ∈ U, c y = y := Iff.rfl

private theorem s15_T8_card_map_conj {A : Type*} [Group A]
    (X : Subgroup (MulAut A)) (α : MulAut A) :
    Nat.card ↥(X.map (MulAut.conj α).toMonoidHom) = Nat.card ↥X :=
  Subgroup.card_map_of_injective (MulAut.conj α).injective

theorem s15_T8_blocks (D : Data G) (h1217 : R1217 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hL : barSub V₀ V h.hyp151.isElemAbelian L ≠ ⊥)
    (hV1 : v1Sub D.M V₀ V h.hyp151.isElemAbelian L = ⊥)
    (hs4 : s15 D.M V₀ V h.hyp151.isElemAbelian L = 4)
    (hγ : 3 ≤ gamma15 D.M V₀ V h.hyp151.isElemAbelian L)
    (hcase : Case153_3 D V₀ V h.hyp151.isElemAbelian L) {u : G} (hu : u ∈ D.M)
    (hu2 : u * u = 1)
    (hsupp : (suppAct (wConj D.M V₀ V h.hyp151.isElemAbelian L) u).ncard ≤ 3)
    (hfix : ∀ E ∈ suppAct (wConj D.M V₀ V h.hyp151.isElemAbelian L) u,
      conjSubgroup E u = E ∧ E3.mQuot E (E ⊓ centralizer ({u} : Set G)) = 1)
    (hus : u ∈ stabTil V₀ V) {a : G} (ha : a ∈ V) (hz : a * u * a⁻¹ * u⁻¹ ∈ V) :
    ∃ (r : ℕ) (B : Fin 4 → Subgroup (MulAut (Vtil V₀ V h.hyp151.isElemAbelian)))
      (Y : Fin 4 → Subgroup (Vtil V₀ V h.hyp151.isElemAbelian)) (J : Finset (Fin 4)),
      T8Blocks (Mbar D.M V₀ V h.hyp151.isElemAbelian) B Y r ∧
      T8Action B Y (actTil V₀ V h.hyp151.isElemAbelian ⟨u, hus⟩)
        (mkTil V₀ V h.hyp151.isElemAbelian
          (IntMod.mk h.hyp151.isElemAbelian ⟨a * u * a⁻¹ * u⁻¹, hz⟩)) J := by
  have hV0 : V₀ = ⊥ := by
    refine le_bot_iff.mp ?_
    have hle := s15_Infra_le_v1Sub D.M V₀ V h.hyp151.isElemAbelian L
    rwa [hV1] at hle
  subst V₀
  have hV := h.hyp151.isElemAbelian
  have h125 := h.hyp151.hyp125
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h125.pairFacts.le_normalizer h125.pairFacts.le_normalizer₀
  obtain ⟨⟨K₀, hK₀L, hKcyc, hdp, hnat⟩, -⟩ := hcase
  let Kb : Subgroup (MulAut (Vtil ⊥ V hV)) := barSub ⊥ V hV K₀
  let N : Subgroup (MulAut (Vtil ⊥ V hV)) :=
    Mbar D.M ⊥ V hV ⊓ normalizer ((lBar ⊥ V hV L : Subgroup _) : Set _)
  have hL3 : IsElemAbelian 3 (lBar ⊥ V hV L) :=
    s15_T7_isElemAbelian_of_directProd (s15_T7_isElemAbelian_of_cyclicOrd hKcyc) hdp
  have hLb3 : IsElemAbelian 3 (barSub ⊥ V hV L) := hL3
  haveI : Fintype (conjSet Kb N) := (Set.toFinite _).fintype
  have hind : sSupIndep (conjSet Kb N) := by
    rw [sSupIndep_iff]
    intro i
    rw [disjoint_iff, s15_T8_iSup_subtype_ne i]
    exact hdp.2.2.2 (i : Subgroup _) i.2
  have hcommS : ∀ U ∈ conjSet Kb N, ∀ W ∈ conjSet Kb N, U ≠ W →
      ∀ x ∈ U, ∀ y ∈ W, Commute x y := by
    intro U hU W hW hUW x hx y hy
    have hbot := hdp.2.2.1 U hU W hW hUW
    have hmem : ⁅x, y⁆ ∈ ⁅U, W⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [hbot, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_commute.mp hmem
  have hKb3 : ∀ i : conjSet Kb N, Nat.card ↥(i : Subgroup (MulAut (Vtil ⊥ V hV))) = 3 := by
    intro i
    obtain ⟨n, -, hi⟩ := i.2
    rw [hi, s15_T8_card_map_conj Kb n]
    exact hKcyc.2
  have hLbcard : Nat.card ↥(barSub ⊥ V hV L) = 3 ^ (conjSet Kb N).ncard := by
    have hSsup : barSub ⊥ V hV L = sSup (conjSet Kb N) := by
      rw [sSup_eq_iSup]
      exact hdp.2.1.symm
    rw [hSsup, s15_T8_card_sSup_eq_prod hind hcommS]
    calc (∏ i : conjSet Kb N, Nat.card ↥(i : Subgroup (MulAut (Vtil ⊥ V hV))))
        = ∏ _i : conjSet Kb N, 3 := Finset.prod_congr rfl (fun i _ => hKb3 i)
      _ = 3 ^ Fintype.card (conjSet Kb N) := by rw [Finset.prod_const, Finset.card_univ]
      _ = 3 ^ (conjSet Kb N).ncard := by rw [Set.fintypeCard_eq_ncard]
  have hrpos : 0 < (conjSet Kb N).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨Kb, s15_T7_mem_conjSet_self Kb N⟩
  have hr : (conjSet Kb N).ncard ≠ 1 := by
    intro h1
    have hLK : barSub ⊥ V hV L = Kb := s15_T7_eq_of_ncard_one hdp h1
    have hgamma : gamma15 D.M ⊥ V hV L = rk ↥(commSub ⊤ Kb) := by
      have h1 : gamma15 D.M ⊥ V hV L = rk ↥(wTil ⊥ V hV L) := by
        have hA : mSub (wSub ⊥ V hV L) =
            gamma15 D.M ⊥ V hV L + delta15 D.M ⊥ V hV L :=
          mSub_wSub D h.hyp151.hyp125 hV
        have hdelta : delta15 D.M ⊥ V hV L = 0 := by
          unfold delta15
          rw [hV1, bot_inf_eq]
          exact rk_bot
        have hB : mSub (wSub ⊥ V hV L) =
            rk ↥(imgTil ⊥ V hV (wSub ⊥ V hV L)) + mSub (wSub ⊥ V hV L ⊓ ⊥) :=
          s15_Infra_mSub_eq_rk_imgTil_add ⊥ V (wSub ⊥ V hV L) hV (preTil_le ⊥ V hV _)
        have himg : imgTil ⊥ V hV (wSub ⊥ V hV L) = wTil ⊥ V hV L := by
          rw [wSub, imgTil_preTil]
        have hbotm : mSub (wSub ⊥ V hV L ⊓ ⊥) = 0 := by
          rw [inf_bot_eq]
          exact rk_bot
        rw [himg, hbotm, add_zero] at hB
        rw [hdelta, add_zero] at hA
        omega
      rw [h1, wTil, hLK]
    have h2 : rk ↥(commSub ⊤ Kb) = 2 := by
      obtain ⟨π, hπ⟩ := hnat
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hcard := CFSG.Quasithin.G64.RealizesVia.card_eq hπ
      have hmod : Nat.card (FFModel.altDn 3).Mod = 4 := by
        have h := CFSG.Quasithin.Explicit.card_dn_sec (n := 3) (by norm_num)
          CFSG.Quasithin.Explicit.AltSym.alternating
        rw [if_neg (by decide : ¬ Even 3)] at h
        exact h
      have hcardU : Nat.card ↥(commSub ⊤ Kb) = 4 := by
        rw [hcard, hmod]
        simp
      unfold rk
      rw [hcardU, show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]
    have := hγ
    omega
  have htwo : 2 ≤ (conjSet Kb N).ncard := by omega
  obtain ⟨B, m, jidx, hB0, hBinj, hBm, hBidx⟩ := s15_T8_exists_enum D h.hyp151 hs4
  let Y : Fin 4 → Subgroup (Vtil ⊥ V hV) := fun j => commSub ⊤ (B j)
  have hconj_eq : ∀ j, B j = (barSub ⊥ V hV L).map
      (MulAut.conj (actTil ⊥ V hV ⟨((m j : D.M) : G), hMs (m j).2⟩)⁻¹).toMonoidHom := by
    intro j
    rw [hBm j]
    exact s15_Infra_barSub_conjSubgroup ⊥ V hV (hMs (m j).2) L
  have htriv : ∀ i j, i ≠ j → ∀ c ∈ B i, ∀ y ∈ Y j, c y = y := by
    intro i j hij c hc y hy
    have hne : ((m i : D.M) : G) * (((m j : D.M) : G))⁻¹ ∉ nBar D.M ⊥ V hV L := by
      intro hmem
      have hthis := (s15_Infra_mul_inv_mem_nBar_iff h125 hV (m j).2 (m i).2).1 hmem
      have hBij : B i = B j := by rw [hBm i, hBm j]; exact hthis
      exact hij (hBinj hBij)
    have hbot := (s15_Kbar_commute_conj h.hyp151 (m j).2 (m i).2 hne).2
    have hle : commSub ⊤ (barSub ⊥ V hV (conjSubgroup L ((m j : D.M) : G))) ≤
        fixV (barSub ⊥ V hV (conjSubgroup L ((m i : D.M) : G))) :=
      commSub_eq_bot_iff.mp hbot
    have hy' : y ∈ commSub ⊤ (barSub ⊥ V hV (conjSubgroup L ((m j : D.M) : G))) := by
      rw [← hBm j]; exact hy
    have hc' : c ∈ barSub ⊥ V hV (conjSubgroup L ((m i : D.M) : G)) := by
      rw [← hBm i]; exact hc
    exact (mem_fixV.mp (hle hy')) c hc'
  have hfaith : ∀ j, ∀ c ∈ B j, (∀ y ∈ Y j, c y = y) → c = 1 := by
    intro j c hc hcy
    refine MulEquiv.ext fun y => ?_
    have hy : y ∈ (⨆ μ : D.M, commSub ⊤ (barSub ⊥ V hV (conjSubgroup L (μ : G)))) := by
      rw [s15_Two_iSup_commSub_eq_top D h1217 h.hyp151 hL]
      trivial
    have hle : (⨆ μ : D.M, commSub ⊤ (barSub ⊥ V hV (conjSubgroup L (μ : G)))) ≤
        fixV (Subgroup.zpowers c) := by
      refine iSup_le fun μ => ?_
      intro z hz
      rw [mem_fixV_zpowers_iff_apply]
      by_cases hμ : jidx μ = j
      · have hzj : z ∈ Y j := by
          have hmem : z ∈ commSub ⊤ (B (jidx μ)) := by rw [hBidx μ]; exact hz
          rwa [hμ] at hmem
        exact hcy z hzj
      · have hzj : z ∈ Y (jidx μ) := by
          change z ∈ commSub ⊤ (B (jidx μ))
          rw [hBidx μ]
          exact hz
        exact htriv j (jidx μ) (Ne.symm hμ) c hc z hzj
    exact mem_fixV_zpowers_iff_apply.1 (hle hy)
  have hEN : (⨆ j : Fin 4, B j) =
      (⨆ μ : D.M, barSub ⊥ V hV (conjSubgroup L (μ : G))) := by
    apply le_antisymm
    · refine iSup_le fun j => ?_
      rw [hBm j]
      exact le_iSup (fun μ : D.M => barSub ⊥ V hV (conjSubgroup L (μ : G))) (m j)
    · refine iSup_le fun μ => ?_
      rw [← hBidx μ]
      exact le_iSup (fun j : Fin 4 => B j) (jidx μ)
  classical
  let J : Finset (Fin 4) :=
    Finset.univ.filter (fun j => ¬ ∀ y ∈ Y j, actTil ⊥ V hV ⟨u, hus⟩ y = y)
  refine ⟨(conjSet Kb N).ncard, B, Y, J, ?_, ?_⟩
  · refine ⟨?_, htwo, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro w
      simpa [pow_two] using s15_Infra_vtil_sq_eq_one ⊥ V hV w
    · intro j
      rw [hBm j]
      exact (le_iSup (fun μ : D.M => barSub ⊥ V hV (conjSubgroup L (μ : G))) (m j)).trans
        (s15_Infra_iSup_barSub_le h.hyp151)
    · intro j
      rw [hconj_eq j]
      exact (hL3.map _).1
    · intro j
      rw [hconj_eq j]
      exact (hL3.map _).2
    · intro j
      rw [hconj_eq j, s15_T8_card_map_conj]
      exact hLbcard
    · intro i j hij c hc c' hc'
      have hne : ((m j : D.M) : G) * (((m i : D.M) : G))⁻¹ ∉ nBar D.M ⊥ V hV L := by
        intro hmem
        have hthis := (s15_Infra_mul_inv_mem_nBar_iff h125 hV (m i).2 (m j).2).1 hmem
        have hBij : B i = B j := by rw [hBm i, hBm j]; exact hthis.symm
        exact hij (hBinj hBij)
      have hbot : ⁅B i, B j⁆ = ⊥ := by
        rw [hBm i, hBm j]
        exact (s15_Kbar_commute_conj h.hyp151 (m i).2 (m j).2 hne).1
      have hmem : ⁅c, c'⁆ ∈ ⁅B i, B j⁆ := Subgroup.commutator_mem_commutator hc hc'
      rw [hbot, Subgroup.mem_bot] at hmem
      exact commutatorElement_eq_one_iff_mul_comm.mp hmem
    · intro j
      rw [eq_bot_iff]
      intro c hc
      rw [Subgroup.mem_bot]
      refine hfaith j c hc.1 ?_
      have hle : (⨆ i ∈ {i : Fin 4 | i ≠ j}, B i) ≤ s15_T8_fixPts (Y j) := by
        refine iSup₂_le fun i hi => ?_
        exact htriv i j hi
      exact s15_T8_mem_fixPts.mp (hle hc.2)
    · intro j
      refine ⟨(actTil ⊥ V hV ⟨((m j : D.M) : G), hMs (m j).2⟩)⁻¹, ?_, ?_⟩
      · exact Subgroup.inv_mem _ (actTil_mem_barSub ⊥ V hV (m j).2 (hMs (m j).2))
      · rw [hB0]
        exact hconj_eq j
    · intro q hq x hx
      rw [hEN] at hx ⊢
      exact (Subgroup.normal_subgroupOf_iff (s15_Infra_iSup_barSub_le h.hyp151)).1
        (s15_Infra_iSup_barSub_normal h.hyp151) x q hx hq
    · exact htriv
    · intro j c hc y hy
      exact s15_T7_commSub_stable (X := B j)
        (fun θ hθ => (B j).mul_mem ((B j).mul_mem hc hθ) ((B j).inv_mem hc)) hy
    · exact hfaith
  ·
    have hu_til : actTil ⊥ V hV ⟨u, hus⟩ * actTil ⊥ V hV ⟨u, hus⟩ = 1 := by
      rw [← map_mul]
      have h1 : (⟨u, hus⟩ * ⟨u, hus⟩ : stabTil ⊥ V) = 1 := Subtype.ext hu2
      rw [h1, map_one]
    have hEfix : ∀ j, conjSubgroup (conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G)) u =
        conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G) := by
      intro j
      by_cases hEs : conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G) ∈
          suppAct (wConj D.M ⊥ V hV L) u
      · exact (hfix _ hEs).1
      · have hmem : conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G) ∈ wConj D.M ⊥ V hV L :=
          ⟨((m j : D.M) : G), (m j).2, rfl⟩
        have hle : conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G) ≤
            centralizer ({u} : Set G) := by
          by_contra h
          exact hEs ⟨hmem, h⟩
        refine conjSubgroup_eq_iff_mem_normalizer.mpr
          (Subgroup.centralizer_le_normalizer _ ?_)
        refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
        exact (Subgroup.mem_centralizer_iff.mp (hle hy) u (Set.mem_singleton u)).symm
    have hEfix_inv : ∀ j, conjSubgroup (conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G)) u⁻¹ =
        conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G) := by
      intro j
      have h1 : conjSubgroup (conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G)) u⁻¹ =
          conjSubgroup (conjSubgroup (conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G)) u)
            u⁻¹ := by rw [hEfix j]
      rw [h1, conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
    have hUle : ∀ j, conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G) ≤ V := by
      intro j
      rw [← s15_Infra_wSub_conjSubgroup ⊥ V L hV (hMs (m j).2)]
      exact preTil_le ⊥ V hV _
    have hWimg : imgTil ⊥ V hV (wSub ⊥ V hV L) = wTil ⊥ V hV L := by
      rw [wSub, imgTil_preTil]
    have hEimg : ∀ j, imgTil ⊥ V hV (conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G)) = Y j := by
      intro j
      rw [s15_Infra_imgTil_conjSubgroup ⊥ V (wSub ⊥ V hV L) hV (hMs (m j).2), hWimg,
        ← s15_Infra_wTil_conjSubgroup ⊥ V L hV (hMs (m j).2)]
      show wTil ⊥ V hV (conjSubgroup L ((m j : D.M) : G)) = commSub ⊤ (B j)
      rw [wTil, ← hBm j]
    have hYinv : ∀ j, (Y j).map (actTil ⊥ V hV ⟨u, hus⟩)⁻¹.toMonoidHom = Y j := by
      intro j
      have h1 := s15_Infra_imgTil_conjSubgroup ⊥ V
        (conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G)) hV hus
      rw [hEfix j, hEimg j] at h1
      exact h1.symm
    have hYstab_eq : ∀ j, (Y j).map (actTil ⊥ V hV ⟨u, hus⟩).toMonoidHom = Y j := by
      intro j
      have h1 := s15_Infra_imgTil_conjSubgroup ⊥ V
        (conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G)) hV ((stabTil ⊥ V).inv_mem hus)
      rw [hEfix_inv j] at h1
      rw [show actTil ⊥ V hV ⟨u⁻¹, (stabTil ⊥ V).inv_mem hus⟩ =
          (actTil ⊥ V hV ⟨u, hus⟩)⁻¹ from by
            rw [show (⟨u⁻¹, _⟩ : stabTil ⊥ V) = (⟨u, hus⟩ : stabTil ⊥ V)⁻¹ from rfl, map_inv],
        inv_inv] at h1
      rw [hEimg j] at h1
      exact h1.symm
    have hYstab_mem : ∀ j, ∀ y ∈ Y j, actTil ⊥ V hV ⟨u, hus⟩ y ∈ Y j := by
      intro j y hy
      have h := Subgroup.mem_map_of_mem (actTil ⊥ V hV ⟨u, hus⟩).toMonoidHom hy
      rwa [hYstab_eq j] at h
    have hstab : ∀ j, actTil ⊥ V hV ⟨u, hus⟩ ∈ stabSub (Y j) := by
      intro j
      rw [mem_stabSub]
      intro y
      refine ⟨fun hy => ?_, fun hy => hYstab_mem j y hy⟩
      have h := Subgroup.mem_map_of_mem (actTil ⊥ V hV ⟨u, hus⟩)⁻¹.toMonoidHom hy
      rw [hYinv j] at h
      simpa using h
    have hinv : ∀ j, ∀ x ∈ Subgroup.zpowers (actTil ⊥ V hV ⟨u, hus⟩), ∀ y ∈ Y j, x y ∈ Y j := by
      intro j x hx y hy
      exact ((mem_stabSub.mp (Subgroup.zpowers_le.mpr (hstab j) hx)) y).mpr hy
    have htop_inv : ∀ x ∈ Subgroup.zpowers (actTil ⊥ V hV ⟨u, hus⟩),
        ∀ y ∈ ⨆ j : Fin 4, Y j, x y ∈ ⨆ j : Fin 4, Y j := by
      intro x hx y hy
      have hle : (⨆ j : Fin 4, Y j) ≤ (⨆ j : Fin 4, Y j).comap x.toMonoidHom := by
        refine iSup_le fun j => ?_
        intro z hz
        exact le_iSup (fun j : Fin 4 => Y j) j (hinv j x hx z hz)
      exact hle hy
    have hYtop : (⨆ j : Fin 4, Y j) = ⊤ := by
      have h1 : (⨆ j : Fin 4, Y j) = commSub ⊤ (⨆ j : Fin 4, B j) := by
        rw [s15_Lin_commSub_top_iSup]
      rw [h1, hEN, s15_Lin_commSub_top_iSup]
      exact s15_Two_iSup_commSub_eq_top D h1217 h.hyp151 hL
    have hJbot : ∀ j, j ∉ J →
        commSub (Y j) (Subgroup.zpowers (actTil ⊥ V hV ⟨u, hus⟩)) = ⊥ := by
      intro j hj
      rw [commSub_eq_bot_iff]
      intro y hy
      rw [mem_fixV_zpowers_iff_apply]
      have h : ¬ ¬ (∀ y ∈ Y j, actTil ⊥ V hV ⟨u, hus⟩ y = y) := by
        intro hc
        exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hc⟩)
      exact (not_not.mp h) y hy
    have hcomm_iSup : commSub (⊤ : Subgroup (Vtil ⊥ V hV))
        (Subgroup.zpowers (actTil ⊥ V hV ⟨u, hus⟩)) =
        ⨆ j : Fin 4, commSub (Y j) (Subgroup.zpowers (actTil ⊥ V hV ⟨u, hus⟩)) := by
      rw [← hYtop]
      rw [commSub_zpowers_eq_map (g := actTil ⊥ V hV ⟨u, hus⟩)
        (W := ⨆ j : Fin 4, Y j) htop_inv, Subgroup.map_iSup]
      refine iSup_congr fun j => ?_
      exact (commSub_zpowers_eq_map (hinv j)).symm
    have hJjoin : (⨆ j : Fin 4, commSub (Y j) (Subgroup.zpowers (actTil ⊥ V hV ⟨u, hus⟩))) =
        ⨆ j ∈ J, commSub (Y j) (Subgroup.zpowers (actTil ⊥ V hV ⟨u, hus⟩)) := by
      apply le_antisymm
      · refine iSup_le fun j => ?_
        by_cases hj : j ∈ J
        · exact (le_iSup (fun _ : j ∈ J =>
              commSub (Y j) (Subgroup.zpowers (actTil ⊥ V hV ⟨u, hus⟩))) hj).trans
            (le_iSup (fun j : Fin 4 => ⨆ (_ : j ∈ J),
              commSub (Y j) (Subgroup.zpowers (actTil ⊥ V hV ⟨u, hus⟩))) j)
        · rw [hJbot j hj]
          exact bot_le
      · refine iSup₂_le fun j hj => le_iSup (fun j : Fin 4 =>
            commSub (Y j) (Subgroup.zpowers (actTil ⊥ V hV ⟨u, hus⟩))) j
    have hmapB : ∀ j, (B j).map (MulAut.conj (actTil ⊥ V hV ⟨u, hus⟩)).toMonoidHom = B j := by
      intro j
      let μ : D.M := ⟨((m j : D.M) : G) * u⁻¹,
        D.M.mul_mem (m j).2 (D.M.inv_mem hu)⟩
      have hconj : (B j).map (MulAut.conj (actTil ⊥ V hV ⟨u, hus⟩)).toMonoidHom =
          barSub ⊥ V hV (conjSubgroup L (μ : G)) := by
        rw [hBm j]
        have h1 := s15_Infra_barSub_conjSubgroup ⊥ V hV ((stabTil ⊥ V).inv_mem hus)
          (conjSubgroup L ((m j : D.M) : G))
        have h2 : actTil ⊥ V hV ⟨u⁻¹, (stabTil ⊥ V).inv_mem hus⟩ =
            (actTil ⊥ V hV ⟨u, hus⟩)⁻¹ := by
          rw [show (⟨u⁻¹, _⟩ : stabTil ⊥ V) = (⟨u, hus⟩ : stabTil ⊥ V)⁻¹ from rfl, map_inv]
        rw [h2, inv_inv, conjSubgroup_conjSubgroup] at h1
        exact h1.symm
      have hYeq : Y (jidx μ) = Y j := by
        change commSub ⊤ (B (jidx μ)) = commSub ⊤ (B j)
        rw [hBidx μ, ← hconj]
        have htop : (⊤ : Subgroup (Vtil ⊥ V hV)).map (actTil ⊥ V hV ⟨u, hus⟩).toMonoidHom = ⊤ := by
          rw [Subgroup.map_top, MonoidHom.range_eq_top]
          exact (actTil ⊥ V hV ⟨u, hus⟩).surjective
        have hcomm := s15_Kbar_commSub_map_conj (⊤ : Subgroup (Vtil ⊥ V hV)) (B j)
          (actTil ⊥ V hV ⟨u, hus⟩)
        rw [htop] at hcomm
        rw [hcomm, hYstab_eq j]
      have hBμ : B (jidx μ) = B j := by
        have hw : wTil ⊥ V hV (conjSubgroup L ((m (jidx μ) : D.M) : G)) =
            wTil ⊥ V hV (conjSubgroup L ((m j : D.M) : G)) := by
          rw [wTil, ← hBm (jidx μ), wTil, ← hBm j]
          exact hYeq
        rw [hBm (jidx μ), hBm j]
        exact (s15_Core_wTil_conj_eq_iff h.hyp151 hL (m (jidx μ)).2 (m j).2).1 hw
      rw [hconj, ← hBidx μ]
      exact hBμ
    have hEinj : Function.Injective
        (fun j : Fin 4 => conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G)) := by
      intro i j hij
      have hw : wTil ⊥ V hV (conjSubgroup L ((m i : D.M) : G)) =
          wTil ⊥ V hV (conjSubgroup L ((m j : D.M) : G)) := by
        have h1 : Y i = Y j := by
          calc Y i = imgTil ⊥ V hV (conjSubgroup (wSub ⊥ V hV L) ((m i : D.M) : G)) :=
                (hEimg i).symm
            _ = imgTil ⊥ V hV (conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G)) :=
                  congrArg (imgTil ⊥ V hV) hij
            _ = Y j := hEimg j
        rw [wTil, ← hBm i, wTil, ← hBm j]
        exact h1
      have hBij : B i = B j := by
        rw [hBm i, hBm j]
        exact (s15_Core_wTil_conj_eq_iff h.hyp151 hL (m i).2 (m j).2).1 hw
      exact hBinj hBij
    have hEsupp : ∀ j, j ∈ J → conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G) ∈
        suppAct (wConj D.M ⊥ V hV L) u := by
      intro j hj
      refine ⟨⟨((m j : D.M) : G), (m j).2, rfl⟩, ?_⟩
      intro hle
      have hfixy : ∀ y ∈ Y j, actTil ⊥ V hV ⟨u, hus⟩ y = y := by
        intro y hy
        obtain ⟨x, rfl⟩ := mkTil_surjective ⊥ V hV y
        have hy' : mkTil ⊥ V hV x ∈ imgTil ⊥ V hV
            (conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G)) := by rwa [hEimg j]
        obtain ⟨x₀, hx₀, hx₀eq⟩ := (mem_imgTil ⊥ V hV _ _).1 hy'
        have hxval : x.val ∈ conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G) := by
          have hdiff : x.val * x₀.val⁻¹ ∈ (⊥ : Subgroup G) :=
            (mkTil_eq_iff ⊥ V hV x x₀).1 hx₀eq.symm
          rw [Subgroup.mem_bot] at hdiff
          rw [show x.val = x.val * x₀.val⁻¹ * x₀.val by group, hdiff, one_mul]
          exact hx₀
        rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot]
        have hcomm : u * x.val = x.val * u :=
          Subgroup.mem_centralizer_iff.mp (hle hxval) u (Set.mem_singleton u)
        rw [show u * x.val * u⁻¹ * x.val⁻¹ = 1 by
          rw [hcomm]; group]
      exact (Finset.mem_filter.mp hj).2 hfixy
    have hsupp_fin : (suppAct (wConj D.M ⊥ V hV L) u).Finite := Set.toFinite _
    have hJcard : J.card ≤ (suppAct (wConj D.M ⊥ V hV L) u).ncard := by
      rw [Set.ncard_eq_toFinset_card _ hsupp_fin,
        ← Finset.card_image_of_injective J hEinj]
      refine Finset.card_le_card ?_
      intro x hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hx
      exact hsupp_fin.mem_toFinset.mpr (hEsupp j hj)
    have hYfix : ∀ j, Y j ⊓ fixV (Subgroup.zpowers (actTil ⊥ V hV ⟨u, hus⟩)) =
        imgTil ⊥ V hV (conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G) ⊓
          centralizer ({u} : Set G)) := by
      intro j
      apply le_antisymm
      · intro q hq
        obtain ⟨hqY, hqfix⟩ := Subgroup.mem_inf.mp hq
        rw [mem_fixV_zpowers_iff_apply] at hqfix
        have hqY' : q ∈ imgTil ⊥ V hV
            (conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G)) := by rwa [hEimg j]
        obtain ⟨x, hx, rfl⟩ := (mem_imgTil ⊥ V hV _ _).1 hqY'
        rw [mem_imgTil]
        refine ⟨x, ⟨hx, ?_⟩, rfl⟩
        have hxfix : u * x.val * u⁻¹ = x.val := by
          have h1 : mkTil ⊥ V hV (actStab ⊥ V hV ⟨u, hus⟩ x) = mkTil ⊥ V hV x := by
            rw [← actTil_mk]
            exact hqfix
          have h2 := (mkTil_eq_iff ⊥ V hV (actStab ⊥ V hV ⟨u, hus⟩ x) x).1 h1
          rw [actStab_apply_val, Subgroup.mem_bot] at h2
          simpa using (mul_inv_eq_iff_eq_mul).1 h2
        refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact (mul_inv_eq_iff_eq_mul).1 hxfix
      · intro q hq
        obtain ⟨x, ⟨hxE, hxC⟩, rfl⟩ := (mem_imgTil ⊥ V hV _ _).1 hq
        rw [Subgroup.mem_inf, mem_fixV_zpowers_iff_apply]
        refine ⟨?_, ?_⟩
        · rw [← hEimg j, mem_imgTil]
          exact ⟨x, hxE, rfl⟩
        · rw [actTil_mk, mkTil_eq_iff, actStab_apply_val, Subgroup.mem_bot]
          have hxu : u * x.val = x.val * u :=
            Subgroup.mem_centralizer_iff.mp hxC u (Set.mem_singleton u)
          rw [show u * x.val * u⁻¹ * x.val⁻¹ = 1 by
            rw [show u * x.val * u⁻¹ = x.val by rw [hxu]; group, mul_inv_cancel]]
    have hrkY : ∀ j, rk ↥(Y j) = rk ↥(conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G)) := by
      intro j
      rw [← hEimg j]
      have h := s15_Infra_mSub_eq_rk_imgTil_add ⊥ V
        (conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G)) hV (hUle j)
      rw [inf_bot_eq] at h
      rw [show mSub (⊥ : Subgroup G) = 0 from rk_bot, add_zero] at h
      exact h.symm
    have hrkfix : ∀ j, rk ↥(Y j ⊓ fixV (Subgroup.zpowers (actTil ⊥ V hV ⟨u, hus⟩))) =
        rk ↥(conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G) ⊓
          centralizer ({u} : Set G)) := by
      intro j
      rw [hYfix j]
      have hUle' : conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G) ⊓
          centralizer ({u} : Set G) ≤ V := inf_le_left.trans (hUle j)
      have h := s15_Infra_mSub_eq_rk_imgTil_add ⊥ V
        (conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G) ⊓
          centralizer ({u} : Set G)) hV hUle'
      rw [inf_bot_eq] at h
      rw [show mSub (⊥ : Subgroup G) = 0 from rk_bot, add_zero] at h
      exact h.symm
    have hrkE : ∀ j, j ∈ J → rk ↥(conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G)) =
        rk ↥(conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G) ⊓
          centralizer ({u} : Set G)) + 1 := by
      intro j hj
      have h2 := rk_add_rkIdx ((conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G) ⊓
        centralizer ({u} : Set G)).subgroupOf
          (conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G)))
      have h3 : rk ↥((conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G) ⊓
          centralizer ({u} : Set G)).subgroupOf
            (conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G))) =
          rk ↥(conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G) ⊓
            centralizer ({u} : Set G)) := by
        unfold rk
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
      have hmq : rkIdx ((conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G) ⊓
          centralizer ({u} : Set G)).subgroupOf
            (conjSubgroup (wSub ⊥ V hV L) ((m j : D.M) : G))) = 1 :=
        (hfix _ (hEsupp j hj)).2
      rw [h3, hmq] at h2
      exact h2.symm
    have hz2 : (a * u * a⁻¹ * u⁻¹) * (a * u * a⁻¹ * u⁻¹) = 1 := by
      have h := hV.2 _ hz
      simpa [pow_two] using h
    have hzu : u * a * u⁻¹ * a⁻¹ = a * u * a⁻¹ * u⁻¹ := by
      have h1 : (a * u * a⁻¹ * u⁻¹)⁻¹ = a * u * a⁻¹ * u⁻¹ := inv_eq_of_mul_eq_one_right hz2
      have h2 : (a * u * a⁻¹ * u⁻¹)⁻¹ = u * a * u⁻¹ * a⁻¹ := by group
      rw [← h2, h1]
    let w : IntMod V hV := IntMod.mk hV ⟨a, ha⟩
    let z0 : IntMod V hV := IntMod.mk hV ⟨a * u * a⁻¹ * u⁻¹, hz⟩
    have hzw : actStab ⊥ V hV ⟨u, hus⟩ w * w⁻¹ = z0 := by
      apply IntMod.val_injective
      rw [IntMod.val_mul, IntMod.val_inv, actStab_apply_val]
      show (u * a * u⁻¹) * a⁻¹ = a * u * a⁻¹ * u⁻¹
      exact hzu
    have hz_mem : mkTil ⊥ V hV z0 ∈
        commSub (⊤ : Subgroup (Vtil ⊥ V hV)) (Subgroup.zpowers (actTil ⊥ V hV ⟨u, hus⟩)) := by
      have h := commSub_zpowers_eq_map (g := actTil ⊥ V hV ⟨u, hus⟩) (W := ⊤)
        (fun _ _ _ _ => Subgroup.mem_top _)
      rw [h]
      refine ⟨mkTil ⊥ V hV w, Subgroup.mem_top _, ?_⟩
      rw [commHom_apply, actTil_mk, ← map_inv, ← map_mul, hzw]
    refine ⟨hu_til, le_trans hJcard hsupp, ?_, hYstab_mem, ?_, ?_, ?_⟩
    · intro j c hc
      have hmem : (MulAut.conj (actTil ⊥ V hV ⟨u, hus⟩)) c ∈
          (B j).map (MulAut.conj (actTil ⊥ V hV ⟨u, hus⟩)).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hc
      rw [hmapB j] at hmem
      simpa only [MulAut.conj_apply] using hmem
    · intro j hj
      exact (not_not.mp (by
        intro hc
        exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hc⟩)))
    · intro j hj
      have hsum := rk_commSub_add_rk_inf_fixV (g := actTil ⊥ V hV ⟨u, hus⟩) (W := Y j) (hinv j)
      rw [hrkfix j, hrkY j, hrkE j hj] at hsum
      omega
    · rw [hcomm_iSup, hJjoin] at hz_mem
      exact hz_mem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
