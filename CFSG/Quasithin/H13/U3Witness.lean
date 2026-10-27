module

public import CFSG.Quasithin.H13.U3Hyp1223
public import CFSG.Quasithin.Background.E1Param
public import CFSG.Quasithin.Background.E3Lower
public import CFSG.Quasithin.Background.E3Bar
public import CFSG.Quasithin.Vol2.Ch12Sec2StatementsPrime

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

theorem twoResidualOf_le_twoResidual [Finite G] (K : Subgroup G) :
    SteinbergBQ.twoResidualOf K ≤ CFSG.Quasithin.twoResidual K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_iInf₂ fun N hN => ?_
  obtain ⟨hNK, hKN, hpow⟩ := hN
  have hn : (N.subgroupOf K).Normal := (normal_subgroupOf_iff_le_normalizer hNK).2 hKN
  have h2 : IsPGroup 2 (K ⧸ N.subgroupOf K) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨k, hk⟩ := hpow x x.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, mem_subgroupOf]
      exact hk
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 h2
  exact iInf_le_of_le N (iInf_le_of_le hNK (iInf_le_of_le hn (iInf_le_of_le ⟨m, hm⟩ le_rfl)))

theorem conjClosure_eq_closure_conjSub (A K : Subgroup G) :
    CFSG.Quasithin.conjClosure A K =
      closure (⋃ k ∈ K, (SteinbergBQ.conjSub k A : Set G)) := by
  unfold CFSG.Quasithin.conjClosure
  congr 1
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_iUnion, SetLike.mem_coe, SteinbergBQ.mem_conjSub,
    exists_prop]
  constructor
  · rintro ⟨k, hk, a, ha, rfl⟩
    exact ⟨k, hk, by simpa [mul_assoc] using ha⟩
  · rintro ⟨k, hk, hx⟩
    exact ⟨k, hk, _, hx, by group⟩

theorem conjSub_conjSubgroup_eq (h g : G) (V : Subgroup G) :
    A1b.conjSub h (conjSubgroup V g) = conjSubgroup V (g * h⁻¹) := by
  ext x
  rw [A1b.mem_conjSub_iff, mem_conjSubgroup_iff, mem_conjSubgroup_iff]
  constructor
  · intro hx
    convert hx using 1
    group
  · intro hx
    convert hx using 1
    group

theorem u3_escaping_local_generation_witness
    (h1332 : Stmt13_3_2) (h12211 : Stmt12_2_11')
    (hesc : U3LocalUniquenessEscapeProducer) (hcod : U3CodimThreeCentralizerControl) :
    U3EscapingLocalGenerationWitness := by
  intro G _ _ T L V z hH hU3 hF hcodim
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hVT, hVe, hV64, hVO, -, -, hTV, -, -, hTC, hVz, hz2⟩ := id hF
  set M := normalizer (L : Set G) with hM
  obtain ⟨-, hVM, -, hzM⟩ := hesc G T L V z hH hU3 hF
  have hHyp := u3_hyp1223 h1332 hH hU3 hF
  have hT2 : IsPGroup 2 T := hH.sylow.1
  have hV2 : IsPGroup 2 V := hT2.to_le hVT
  have hVea : CFSG.Open.IsElemAbelian 2 V := ⟨hVe.toIsMulCommutative, fun x hx =>
    elemPow_eq_one_of_isElementaryAbelian (A := V) x hx⟩
  have hzVT : z ∈ V ⊓ centralizer (T : Set G) := by
    rw [hVz]
    exact mem_zpowers z
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hTz : T ≤ centralizer ({z} : Set G) := fun t ht =>
    mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 hzVT.2) t ht)
  have hcn : centralizer ({z} : Set G) ≤ normalizer ((zpowers z : Subgroup G) : Set G) := by
    have h := Subgroup.centralizer_le_normalizer ((zpowers z : Subgroup G) : Set G)
    rwa [zpowers_eq_closure, centralizer_closure, ← zpowers_eq_closure] at h
  have hO2z : pCoreOf 2 (centralizer ({z} : Set G)) ≠ ⊥ := by
    have hz2' : IsPGroup 2 (zpowers z) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz2]; norm_num)
    have hle : zpowers z ≤ pCoreOf 2 (centralizer ({z} : Set G)) :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        (zpowers_le.2 (mem_centralizer_singleton_iff.2 rfl)) hcn hz2'
    intro h
    rw [h, le_bot_iff, zpowers_eq_bot] at hle
    exact hz1 hle
  obtain ⟨H, ⟨hHH, hHM, hHz⟩, hmin⟩ :=
    (Set.toFinite {Y : Subgroup G | InH T Y ∧ ¬ Y ≤ M ∧
      Y ≤ centralizer ({z} : Set G)}).exists_minimal ⟨_, ⟨hTz, hO2z⟩, hzM, le_rfl⟩
  have hHstar : IsHStar T M H := ⟨hHH, hHM, fun Y hY hYH hYM =>
    le_antisymm hYH (hmin ⟨hY, hYM, hYH.trans hHz⟩ hYH)⟩
  have hTH : T ≤ H := hHH.1
  have hUne : zpowers z ≠ ⊥ := by
    intro h
    apply hz1
    rw [← mem_bot, ← h]
    exact mem_zpowers z
  have hV₃ : ∀ V₃ : Subgroup G, V₃ ≤ V → Nat.card V₃ = 2 ^ 3 →
      T ⊓ L ≤ normalizer (V₃ : Set G) → centralizer (V₃ : Set G) ≤ M := by
    intro V₃ hV₃V hV₃8 _
    have hidx : V₃.relIndex V = 8 := by
      have h1 := card_mul_relIndex hV₃V
      rw [hV₃8, hV64] at h1
      omega
    exact (hcod G T L V z hH hU3 hF V₃ hV₃V hidx.le).trans hVM
  have hn := (h12211 G T L V H (zpowers z) hHyp hHstar hUne (zpowers_le.2 hzVT.1)
    (hHz.trans hcn) (Or.inr (Or.inr ⟨hU3, hV64, hV₃⟩))).1
  have hE : E1.InE 2 H := (E1.nParam_le_iff (n := 2) (by norm_num)).1 (by exact_mod_cast hn)
  have hTsyl : IsSylowIn 2 T H :=
    ⟨hTH, hT2, fun h2 => hH.sylow.2 (h2.trans (relIndex_dvd_index_of_le hTH))⟩
  set Ω : Set (Subgroup G) := {A | A ≤ H ∧ ∃ g : G, A = conjSubgroup V g} with hΩ
  have hΩinv : E1.IsInvColl H Ω := by
    refine ⟨fun A hA => hA.1, fun A hA => ?_, fun A hA h hh => ?_⟩
    · obtain ⟨-, g, rfl⟩ := hA
      exact E3.isElemAbelian_conjSubgroup hVea g
    · obtain ⟨hAH, g, rfl⟩ := hA
      refine ⟨?_, g * h⁻¹, conjSub_conjSubgroup_eq h g V⟩
      intro x hx
      rw [A1b.mem_conjSub_iff] at hx
      have h1 := H.mul_mem (H.mul_mem hh (hAH hx)) (H.inv_mem hh)
      rwa [show h * (h⁻¹ * x * h) * h⁻¹ = x by group] at h1
  have hgen := hE T hTsyl Ω hΩinv
  have hW : E1.weakClosure T Ω = E3.wClos V 0 T := by
    unfold E1.weakClosure E3.wClos
    apply le_antisymm
    · refine iSup₂_le fun A hA => iSup_le fun hAT => ?_
      obtain ⟨-, g, rfl⟩ := hA
      exact le_iSup₂_of_le (f := fun A (_ : A ∈ E3.gammaSet V 0 T) => A) (conjSubgroup V g)
        ⟨hAT, g, le_rfl, E3.mQuot_self _⟩ le_rfl
    · refine iSup₂_le fun A hA => ?_
      obtain ⟨hAT, g, hAg, h0⟩ := hA
      have hAeq : A = conjSubgroup V g :=
        (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup hV2 g) hAg).1 h0
      exact le_iSup₂_of_le (f := fun A (_ : A ∈ Ω) => ⨆ (_ : A ≤ T), A) A
        ⟨hAT.trans hTH, g, hAeq⟩ (le_iSup_of_le (f := fun (_ : A ≤ T) => A) hAT le_rfl)
  have hw : ((0 : ℕ) : ℕ∞) < E3.wParam T V := by
    have h1 : ((1 : ℕ) : ℕ∞) ≤ E3.wParam T V := E3.le_wParam_of_wClos_le fun j hj => by
      obtain rfl : j = 0 := by omega
      refine iSup₂_le fun A hA => ?_
      obtain ⟨hAT, g, hAg, h0⟩ := hA
      have hAeq : A = CFSG.conjugate V g :=
        (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup hV2 g) hAg).1 h0
      subst hAeq
      have hc := hcodim g _ (le_inf hAT le_rfl) (by rw [relIndex_self]; norm_num)
      exact le_inf hAT (commutator_eq_bot_iff_le_centralizer.1 hc)
    exact lt_of_lt_of_le (by norm_num) h1
  have hrk : 0 < rk ↥V := by
    unfold rk
    rw [hV64, show (64 : ℕ) = 2 ^ 6 by norm_num, padicValNat.prime_pow]
    norm_num
  have hQ : IsUniqueM (normalizer ((T ⊓ centralizer (V : Set G) : Subgroup G) : Set G)) M := by
    obtain ⟨-, -, -, -, h3⟩ := u3_original_local_maximality_and_unique_normalizer_of_1332 h1332 hH
    have hV1 : V ≠ ⊥ := by
      intro h
      rw [h, card_bot] at hV64
      norm_num at hV64
    have hQne : T ⊓ centralizer (V : Set G) ≠ ⊥ := by
      rw [hTC]
      intro h
      exact hV1 (le_bot_iff.1 (h ▸ hVO))
    have hLTQ : L ⊔ T ≤ normalizer ((T ⊓ centralizer (V : Set G) : Subgroup G) : Set G) := by
      rw [hTC]
      exact LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
    obtain ⟨-, hM1, hM2, hM3⟩ := h3 _ hQne (hT2.to_le inf_le_left)
      (inf_le_left.trans le_sup_right) hLTQ
    exact ⟨⟨hM1, hM2⟩, fun M' hM' => hM3 M' hM'.1 hM'.2⟩
  have hNW : normalizer (E1.weakClosure T Ω : Set G) ≤ M := by
    rw [hW]
    have hT322 : E3.HypE322 T V :=
      ⟨⟨le_top, hT2, by rw [relIndex_top_right]; exact hH.sylow.2⟩, hVT, hTV⟩
    exact (E3.e3_34_two hVea hT322 hQ hrk hw).1
  set S : Set (Subgroup G × Subgroup G) :=
    {AK | AK.1 ∈ Ω ∧ AK.1 ≤ T ∧ E1.IsE 2 H T AK.1 AK.2} with hS
  set P : Finset (Subgroup G × Subgroup G) := (Set.toFinite S).toFinset with hP
  have hmemP : ∀ AK, AK ∈ P ↔ AK ∈ S := fun AK => Set.Finite.mem_toFinset _
  have hEgen : E1.eGen 2 H T Ω = ⨆ AK ∈ P, AK.2 := by
    unfold E1.eGen
    apply le_antisymm
    · refine iSup₂_le fun A hA => iSup_le fun hAT => iSup₂_le fun K hK => ?_
      exact le_iSup₂_of_le (f := fun AK (_ : AK ∈ P) => AK.2) (A, K)
        ((hmemP _).2 ⟨hA, hAT, hK⟩) le_rfl
    · refine iSup₂_le fun AK hAK => ?_
      obtain ⟨hA, hAT, hK⟩ := (hmemP AK).1 hAK
      exact le_iSup₂_of_le AK.1 hA (le_iSup_of_le hAT (le_iSup₂_of_le
        (f := fun K (_ : K ∈ {K : Subgroup G | E1.IsE 2 H T AK.1 K}) => K) AK.2 hK le_rfl))
  refine ⟨H, H ⊓ normalizer (E1.weakClosure T Ω : Set G), P, hTH, hHz, hHM,
    inf_le_inf_left _ hNW, fun AK hAK => ?_, ?_, fun AK hAK => ?_⟩
  · obtain ⟨⟨hAH, -⟩, -, hK⟩ := (hmemP AK).1 hAK
    exact ⟨hAH, hK.1⟩
  · rw [← hEgen, sup_comm]
    exact hgen.symm
  · obtain ⟨⟨-, g, hAg⟩, hAT, hK⟩ := (hmemP AK).1 hAK
    have hAea : CFSG.Open.IsElemAbelian 2 AK.1 := by
      rw [hAg]
      exact E3.isElemAbelian_conjSubgroup hVea g
    obtain ⟨hAK2, hcard⟩ := E3.card_le_of_isE hTsyl hAT hAea hK
    refine ⟨⟨g, hAg⟩, hAK2, hK.2.2.1, ?_, ?_⟩
    · have h1 := card_mul_relIndex (inf_le_left : AK.1 ⊓ pCoreOf 2 AK.2 ≤ AK.1)
      have hpos : 0 < Nat.card ↥(AK.1 ⊓ pCoreOf 2 AK.2) := Nat.card_pos
      have h2 : Nat.card ↥(AK.1 ⊓ pCoreOf 2 AK.2) * (AK.1 ⊓ pCoreOf 2 AK.2).relIndex AK.1 ≤
          Nat.card ↥(AK.1 ⊓ pCoreOf 2 AK.2) * 4 := by
        rw [h1, mul_comm]
        exact hcard
      exact Nat.le_of_mul_le_mul_left h2 hpos
    · calc SteinbergBQ.twoResidualOf AK.2 ≤ CFSG.Quasithin.twoResidual AK.2 :=
            twoResidualOf_le_twoResidual _
        _ ≤ CFSG.Quasithin.conjClosure AK.1 AK.2 := E1.twoResidual_le_conjClosure hK.isEAny
        _ = closure (⋃ k ∈ AK.2, (SteinbergBQ.conjSub k AK.1 : Set G)) :=
            conjClosure_eq_closure_conjSub _ _

end CFSG.Quasithin.H13.U3
