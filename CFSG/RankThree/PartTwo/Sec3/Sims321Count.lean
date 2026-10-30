module

public import CFSG.RankThree.PartTwo.Sec3.Sims321CountDef
import CFSG.RankThree.PartTwo.Sec3.Sims321Series
public import CFSG.RankThree.PartTwo.Sec3.Sims321

public section

namespace CFSG.RankThree.PartTwo.Sec3.Sims321

open CFSG CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)

section Count

open CFSG.RankThree.FFModules CFSG.LocalAnalysis.ComponentInitial.LinearFlag

private def commKer {G : Type*} [Group G] (L U W : Subgroup G)
    (hU : L ≤ Subgroup.normalizer (U : Set G)) (hW : L ≤ Subgroup.normalizer (W : Set G)) :
    Subgroup L where
  carrier := {l | ∀ v ∈ W, (l : G) * v * (l : G)⁻¹ * v⁻¹ ∈ U}
  one_mem' := fun v _ => by simpa using U.one_mem
  mul_mem' := by
    intro a b ha hb v hv
    have h1 : ((a * b : L) : G) * v * ((a * b : L) : G)⁻¹ * v⁻¹ =
        ((a : G) * ((b : G) * v * (b : G)⁻¹ * v⁻¹) * (a : G)⁻¹) *
          ((a : G) * v * (a : G)⁻¹ * v⁻¹) := by
      simp only [Subgroup.coe_mul]; group
    rw [h1]
    exact U.mul_mem ((Subgroup.mem_normalizer_iff.mp (hU a.2) _).mp (hb v hv)) (ha v hv)
  inv_mem' := by
    intro a ha v hv
    have hv' : (a : G)⁻¹ * v * (a : G) ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp (hW (a⁻¹).2) v).mp hv
      simpa using this
    have h1 : ((a⁻¹ : L) : G) * v * ((a⁻¹ : L) : G)⁻¹ * v⁻¹ =
        ((a : G) * ((a : G)⁻¹ * v * (a : G)) * (a : G)⁻¹ *
          ((a : G)⁻¹ * v * (a : G))⁻¹)⁻¹ := by
      simp only [Subgroup.coe_inv]; group
    rw [h1]
    exact U.inv_mem (ha _ hv')

private theorem commKer_normal {G : Type*} [Group G] {L U W : Subgroup G}
    (hU : L ≤ Subgroup.normalizer (U : Set G)) (hW : L ≤ Subgroup.normalizer (W : Set G)) :
    (commKer L U W hU hW).Normal := by
  refine ⟨fun k hk g v hv => ?_⟩
  have hv' : (g : G)⁻¹ * v * (g : G) ∈ W := by
    have := (Subgroup.mem_normalizer_iff.mp (hW (g⁻¹).2) v).mp hv
    simpa using this
  have h1 : ((g * k * g⁻¹ : L) : G) * v * ((g * k * g⁻¹ : L) : G)⁻¹ * v⁻¹ =
      (g : G) * ((k : G) * ((g : G)⁻¹ * v * (g : G)) * (k : G)⁻¹ *
        ((g : G)⁻¹ * v * (g : G))⁻¹) * (g : G)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group
  rw [h1]
  exact (Subgroup.mem_normalizer_iff.mp (hU g.2) _).mp (hk _ hv')

private theorem exists_comm_not_mem {G : Type*} [Group G] [Finite G] {L U W : Subgroup G}
    (hperf : Group.IsPerfect L) (hS : IsSimpleGroup (L ⧸ CFSG.pCore 2 L))
    (hU : L ≤ Subgroup.normalizer (U : Set G)) (hW : L ≤ Subgroup.normalizer (W : Set G))
    (hUW : ¬ ⁅W, L⁆ ≤ U) {y : L} (hy : (y : L ⧸ CFSG.pCore 2 L) ≠ 1) :
    ∃ v ∈ W, (y : G) * v * (y : G)⁻¹ * v⁻¹ ∉ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hcon
  push Not at hcon
  set K := commKer L U W hU hW
  haveI hKn : K.Normal := commKer_normal hU hW
  have hyK : y ∈ K := hcon
  have hKP : K.map (QuotientGroup.mk' (CFSG.pCore 2 L)) = ⊤ := by
    haveI hN : (K.map (QuotientGroup.mk' (CFSG.pCore 2 L))).Normal :=
      hKn.map _ (QuotientGroup.mk'_surjective _)
    rcases hS.eq_bot_or_eq_top_of_normal (K.map (QuotientGroup.mk' (CFSG.pCore 2 L))) with h | h
    · exfalso
      apply hy
      have hmem : QuotientGroup.mk' (CFSG.pCore 2 L) y ∈
          K.map (QuotientGroup.mk' (CFSG.pCore 2 L)) := ⟨y, hyK, rfl⟩
      rw [h, Subgroup.mem_bot] at hmem
      exact hmem
    · exact h
  have h2 : IsPGroup 2 (L ⧸ K) := by
    intro g
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
    have hl : QuotientGroup.mk' (CFSG.pCore 2 L) l ∈
        K.map (QuotientGroup.mk' (CFSG.pCore 2 L)) := by
      rw [hKP]; trivial
    obtain ⟨k, hk, hkl⟩ := hl
    have hp : k⁻¹ * l ∈ CFSG.pCore 2 L := QuotientGroup.eq.mp hkl
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := L)) ⟨_, hp⟩
    refine ⟨a, ?_⟩
    have ha' : (k⁻¹ * l) ^ 2 ^ a = 1 := by
      have := congrArg Subtype.val ha
      simpa using this
    have hkl' : (QuotientGroup.mk (k⁻¹ * l) : L ⧸ K) = QuotientGroup.mk l := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff k).mpr hk,
        inv_one, one_mul]
    rw [← hkl', ← QuotientGroup.mk_pow, ha', QuotientGroup.mk_one]
  haveI := hperf
  haveI : Group.IsNilpotent (L ⧸ K) := h2.isNilpotent
  have hsub : Subsingleton (L ⧸ K) := by
    rw [← not_nontrivial_iff_subsingleton]
    intro hnt
    exact Group.IsPerfect.not_isNilpotent (L ⧸ K) ‹_›
  have hKtop : K = ⊤ := by
    rw [eq_top_iff]
    intro l _
    rw [← QuotientGroup.eq_one_iff]
    exact Subsingleton.elim _ _
  apply hUW
  rw [Subgroup.commutator_le]
  intro v hv l hl
  have hlK : (⟨l, hl⟩ : L) ∈ K := hKtop ▸ Subgroup.mem_top _
  have h3 := U.inv_mem (hlK v hv)
  convert h3 using 1
  rw [commutatorElement_def]
  group

private theorem count_contra {G : Type} [Group G] [Finite G] {X L T : Subgroup G} {n : ℕ}
    (hLN : X ≤ Subgroup.normalizer (L : Set G))
    (φ : L ⧸ CFSG.pCore 2 L ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 2 n))
    (hL : L ∈ oTwoComponentsIn X) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T X) (hLT : L ⊔ T = X)
    (hn : Odd n) (hX : L ⊔ CFSG.Open.pCoreOf 2 X = X) {A : Subgroup G} (hA : A ∈ famG T 0)
    (hAQ : ¬ A ≤ CFSG.Open.pCoreOf 2 X) {r : ℕ} {Vs : Fin (r + 1) → Subgroup G}
    (hVs : IsChiefSeriesUnder L (omegaZOf (CFSG.Open.pCoreOf 2 X)) r Vs) {i j k : Fin r}
    (hij : i < j) (hjk : j < k) (hi : ¬ ⁅Vs i.succ, L⁆ ≤ Vs i.castSucc)
    (hj : ¬ ⁅Vs j.succ, L⁆ ≤ Vs j.castSucc) (hk : ¬ ⁅Vs k.succ, L⁆ ≤ Vs k.castSucc) :
    False := by
  classical
  letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hn0 : n ≠ 0 := by obtain ⟨k, rfl⟩ := hn; omega
  obtain ⟨hAT, hA2, -⟩ := mem_famG.mp hA
  have hTX : T ≤ X := le_of_isSylowOf' hT
  have hAX : A ≤ X := hAT.trans hTX
  have hALQ : A ≤ L ⊔ CFSG.Open.pCoreOf 2 X := hAX.trans hX.ge
  obtain ⟨hVc, hV2, hVQ, hQV⟩ := omegaZOf_facts (CFSG.Open.pCoreOf 2 X)
  have hXV := le_normalizer_omegaZOf X
  have hVT := hVQ.trans (pCoreOf_le_of_sylow hT)
  set V := omegaZOf (CFSG.Open.pCoreOf 2 X)
  have hoff := relIndex_le_of_famG hVT hVc hV2 (hTX.trans hXV) hA
  have hoff' : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ≤
      (A ⊓ CFSG.Open.pCoreOf 2 X).relIndex A :=
    Subgroup.relIndex_le_of_le_left (inf_le_inf_left _ fun q hq =>
      Subgroup.mem_centralizer_iff.mpr fun v hv => (hQV v hv q hq).symm)
      (relIndex_ne_zero_of_finite _ _)
  have hcardE : Nat.card (imgSL hLN φ A) = (A ⊓ CFSG.Open.pCoreOf 2 X).relIndex A :=
    card_imgSL hLN φ hL hT hLT hn hAX hALQ
  obtain ⟨hE2, hEc⟩ := imgSL_elem hLN φ hn hA2
  have hEle := card_le_sq_of_elementary hE2 hEc
  have hNE : (V ⊓ Subgroup.centralizer (A : Set G)).relIndex V ≤ Nat.card (imgSL hLN φ A) := by
    rw [hcardE]; exact hoff.trans hoff'
  obtain ⟨τ, hτE, hτ1⟩ : ∃ τ ∈ imgSL hLN φ A, τ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : imgSL hLN φ A = ⊥ := eq_bot_iff.mpr fun g hg => (Subgroup.mem_bot).mpr (hcon g hg)
    rw [hbot, Subgroup.card_bot, eq_comm, Subgroup.relIndex_eq_one] at hcardE
    exact hAQ (hcardE.trans inf_le_right)
  have hτ2 : τ * τ = 1 := hE2 τ hτE
  obtain ⟨p, hp, hp2, hp3, hpk, hk3⟩ := exists_ppd hn
  obtain ⟨y₀, τ₁, τ₂, τ₃, hy₀r, -, hy₀, h1a, h1b, h2a, h2b, h3a, h3b⟩ :=
    exists_symm_orderOf_prod_three (card_galoisField hn0) (Nat.pos_of_ne_zero hn0) hp hp3 hpk
  obtain ⟨k₁, hk₁⟩ := exists_conj_eq_of_involution τ τ₁ hτ2 hτ1 h1a h1b
  obtain ⟨k₂, hk₂⟩ := exists_conj_eq_of_involution τ τ₂ hτ2 hτ1 h2a h2b
  obtain ⟨k₃, hk₃⟩ := exists_conj_eq_of_involution τ τ₃ hτ2 hτ1 h3a h3b
  have hpr : (proj 3 (GaloisField 2 n) y₀) ^ p = 1 := by
    rw [← map_pow, ← hy₀r, pow_orderOf_eq_one, map_one]
  obtain ⟨y, hyg, hyr⟩ := exists_lift φ hp hp2 _ hpr
  have hy₀1 : y₀ ≠ 1 := by
    intro h; rw [h, orderOf_one] at hy₀r; exact hp.one_lt.ne hy₀r
  have hyg' : psi φ y = proj 3 _ ((k₁ * τ * k₁⁻¹) * (k₂ * τ * k₂⁻¹) * (k₃ * τ * k₃⁻¹)) := by
    rw [hyg, hy₀, hk₁, hk₂, hk₃]
  have hcube := relIndex_le_cube hLN φ hL hT hLT hτE k₁ k₂ k₃ hyg'
  have hup : (V ⊓ Subgroup.centralizer ({(y : G)} : Set G)).relIndex V ≤ 2 ^ (n * 6) := by
    have h1 := hcube.trans (Nat.pow_le_pow_left (hNE.trans hEle) 3)
    rw [card_galoisField hn0, ← pow_mul, ← pow_mul] at h1
    exact h1
  have hy' : (y : L ⧸ CFSG.pCore 2 L) ≠ 1 := by
    intro h
    have h1 : psi φ y = 1 := by
      change (φ.trans (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 _))
        (QuotientGroup.mk y) = 1
      rw [h, map_one]
    rw [hyg] at h1
    exact hy₀1 (proj_injective_of_odd hn (by rw [h1, map_one]))
  have hnt : ∀ l : Fin r, ¬ ⁅Vs l.succ, L⁆ ≤ Vs l.castSucc →
      ∃ v ∈ Vs l.succ, (y : G) * v * (y : G)⁻¹ * v⁻¹ ∉ Vs l.castSucc := fun l hl =>
    exists_comm_not_mem (isPerfect_of_mem_oTwoComponentsIn hL) (isSimpleGroup_quot φ)
      (hVs.normalized _) (hVs.normalized _) hl hy'
  have hcard : ({i, j, k} : Finset (Fin r)).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨i, j, k, hij.ne, (hij.trans hjk).ne, hjk.ne, rfl⟩
  have hyr' : (y : G) ^ p = 1 := by rw [← Subgroup.coe_pow, hyr, Subgroup.coe_one]
  have hlow := two_pow_mul_le_relIndex_of_series hVc hV2 hp hp2 hk3 hyr' Vs hVs.zero hVs.last
    (fun l => (hVs.lt l).le) (fun l => hVs.normalized l y.2) {i, j, k} (by
      intro l hl
      simp only [Finset.mem_insert, Finset.mem_singleton] at hl
      rcases hl with rfl | rfl | rfl
      exacts [hnt _ hi, hnt _ hj, hnt _ hk])
  rw [hcard] at hlow
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (hlow.trans hup)
  omega

end Count

theorem item321Count_holds : Item321Count := by
  intro G _ _ X L T n hF hL hLN hT hLT hn ⟨φ⟩
  by_cases hJ : X ≤ Subgroup.normalizer (thompsonOf T : Set G)
  · exact Or.inl (Or.inl hJ)
  by_cases hV : ⁅omegaZOf (CFSG.Open.pCoreOf 2 X), L⁆ = ⊥
  · exact Or.inl (Or.inr hV)
  right
  have hX : L ⊔ CFSG.Open.pCoreOf 2 X = X := by
    rcases item321Split_holds G X L T n hF hL hLN hT hLT hn ⟨φ⟩ with (h | h) | h
    · exact absurd h hJ
    · exact absurd h hV
    · exact h
  refine ⟨hX, fun r Vs hVs i j k hij hjk hi hj hk => ?_⟩
  have hJT : thompsonOf T = jG T 0 := map_higherElemThompson T 0
  rw [hJT] at hJ
  obtain ⟨A, hA, hAQ⟩ : ∃ A ∈ famG T 0, ¬ A ≤ CFSG.Open.pCoreOf 2 X := by
    by_contra hcon
    push Not at hcon
    exact hJ (le_normalizer_jG_of_le hT (sSup_le fun A hA => hcon A hA))
  exact count_contra hLN φ hL hT hLT hn hX hA hAQ hVs hij hjk hi hj hk

end CFSG.RankThree.PartTwo.Sec3.Sims321
