module

public import CFSG.Quasithin.EmptyFaithful.S14112
public import CFSG.Quasithin.EmptyFaithful.S141Statements
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks
public import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type*} [Group G]

@[expose] def IsChiBlock (X L : Subgroup G) : Prop :=
  IsBlock2 X L ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type L n) ∨ ∃ m : ℕ, Odd m ∧ 3 ≤ m ∧ IsAltType L m)

@[expose] def GNCampbellC128 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T : Subgroup G), IsSimpleGroup G → quasithinIsQTKECat G →
    quasithinIsSylowTwo T → T ≠ ⊥ →
    ∃ C₁ C₂ : Subgroup G, C₁ ≠ ⊥ ∧ C₁ ≤ quasithinOmegaOneCenter T ∧
      (C₁.subgroupOf T).Characteristic ∧ C₂ ≠ ⊥ ∧ C₂ ≤ baum T ∧
      (C₂.subgroupOf (baum T)).Characteristic ∧
      ∀ M : Subgroup G, InM T M →
        M = (M ⊓ Subgroup.centralizer (C₁ : Set G)) ⊔ (M ⊓ Subgroup.normalizer (C₂ : Set G)) ∨
        ∃ (s : ℕ) (L : Fin s → Subgroup G), 1 ≤ s ∧ s ≤ 2 ∧
          (∀ i, IsChiBlock M (L i) ∧ ⁅L i, thompsonJ T⁆ = L i) ∧
          M = ((M ⊓ Subgroup.centralizer (C₁ : Set G)) ⊔
            (M ⊓ Subgroup.normalizer (C₂ : Set G))) ⊔ ⨆ i, L i

@[expose] def StageLemma14110 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc : Subgroup G), quasithinQTFE14Cat G T Mc →
    ∀ M X R : Subgroup G, InM T M → IsBlock2 M X → IsAltType X 3 → pCoreOf 2 M ≤ R → R ≤ T →
      ⁅X, thompsonJ R⁆ = X → M = Mc ∧ 2 < Nat.card (quasithinOmegaOneCenter T)

@[expose] def StageLemma1417Stab : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc : Subgroup G), quasithinQTFE14Cat G T Mc →
    ∀ M V : Subgroup G, InM T M → IsTwoReducedIn M V →
      ¬ thompsonJ T ≤ M ⊓ Subgroup.centralizer (V : Set G) →
      (M ≠ Mc ∨ Nat.card (quasithinOmegaOneCenter T) = 2) →
      M ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤
        (M ⊓ Subgroup.centralizer (V : Set G)) ⊔ T

section Reduction

variable [Finite G]

omit [Finite G] in
private theorem s14111_le_normalizer_inf_centralizer {M V : Subgroup G}
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) :
    M ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g ∈ M, ∀ c ∈ M ⊓ Subgroup.centralizer (V : Set G),
      g * c * g⁻¹ ∈ M ⊓ Subgroup.centralizer (V : Set G) := by
    intro g hg c hc
    refine ⟨M.mul_mem (M.mul_mem hg hc.1) (M.inv_mem hg), ?_⟩
    have hcen : c ∈ Subgroup.centralizer (V : Set G) := hc.2
    show g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G)
    rw [Subgroup.mem_centralizer_iff] at hcen ⊢
    intro v hv
    have hv' : g⁻¹ * v * g⁻¹⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hMV (M.inv_mem hg)) v).mp hv
    rw [inv_inv] at hv'
    have h1 := hcen _ hv'
    calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * v := by group
  intro c
  constructor
  · exact key m hm c
  · intro hc
    have := key m⁻¹ (M.inv_mem hm) _ hc
    simpa [mul_assoc] using this

omit [Finite G] in
private theorem s14111_relIndex_sup_eq {D T : Subgroup G}
    (hT : T ≤ Subgroup.normalizer (D : Set G)) : D.relIndex (T ⊔ D) = D.relIndex T := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer hT
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer hT
  exact Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient T D hT).toEquiv.symm

private theorem s14111_odd_relIndex {S D : Subgroup G} (hS : ¬ 2 ∣ S.index)
    (hSN : S ≤ Subgroup.normalizer (D : Set G)) : ¬ 2 ∣ (S ⊓ D).relIndex D := by
  have h1 : (S ⊓ D).relIndex S * S.relIndex (S ⊔ D) = (S ⊓ D).relIndex (S ⊔ D) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left le_sup_left
  have h2 : (S ⊓ D).relIndex D * D.relIndex (S ⊔ D) = (S ⊓ D).relIndex (S ⊔ D) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_right le_sup_right
  have h3 : D.relIndex (S ⊔ D) = (S ⊓ D).relIndex S :=
    (s14111_relIndex_sup_eq hSN).trans (Subgroup.inf_relIndex_left S D).symm
  have h4 : 0 < (S ⊓ D).relIndex S :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := ((S ⊓ D).subgroupOf S)))
  have h5 : (S ⊓ D).relIndex D = S.relIndex (S ⊔ D) := by
    refine Nat.eq_of_mul_eq_mul_left h4 ?_
    rw [h3] at h2
    rw [mul_comm ((S ⊓ D).relIndex S) ((S ⊓ D).relIndex D), h2, ← h1]
  rw [h5]
  exact fun h => hS (h.trans (Subgroup.relIndex_dvd_index_of_le le_sup_left))

omit [Finite G] in
private theorem s14111_le_perfectCore {M L : Subgroup G} (hLM : L ≤ M) (hL : ⁅L, L⁆ = L) :
    L ≤ perfectCore M := by
  unfold perfectCore
  refine le_iInf fun n => ?_
  induction n with
  | zero => exact hLM
  | succ n ih =>
    rw [← hL]
    exact Subgroup.commutator_mono ih ih

omit [Finite G] in
private theorem s14111_perfect_of_short {L : Subgroup G} (hL : IsShort2 L) {Q : Type*} [Group Q]
    [hQ : Group.IsPerfect Q] (α : L →* Q) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 L) : ⁅L, L⁆ = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← Subgroup.isPerfect_iff, Group.isPerfect_def]
  have hmap : (commutator L).map α = ⊤ := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hα]
    exact hQ.commutator_eq_top
  have hp : IsPGroup 2 (L ⧸ commutator L) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      have hx : α x ∈ (commutator L).map α := by rw [hmap]; trivial
      obtain ⟨d, hd, hdx⟩ := hx
      have hk : d⁻¹ * x ∈ CFSG.pCore 2 L := by
        rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, hdx, inv_mul_cancel]
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := L)) ⟨_, hk⟩
      refine ⟨n, ?_⟩
      have hn' : (d⁻¹ * x) ^ 2 ^ n = 1 := congrArg Subtype.val hn
      have hdq : (QuotientGroup.mk d : L ⧸ commutator L) = 1 :=
        (QuotientGroup.eq_one_iff d).mpr hd
      have hxq : (QuotientGroup.mk x : L ⧸ commutator L) = QuotientGroup.mk (d⁻¹ * x) := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hdq, inv_one, one_mul]
      rw [hxq, ← QuotientGroup.mk_pow, hn', QuotientGroup.mk_one]
  exact hL.1 (commutator L) hp

theorem stageLemma14111_of_parts (hGN : GNCampbellC128) (h16 : StageLemma1416)
    (h17 : StageLemma1417) (h17s : StageLemma1417Stab) (h110 : StageLemma14110) :
    StageLemma14111 := by
  intro G _ _ T Mc h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨C₁, C₂, hC₁ne, hC₁Z, -, hC₂ne, hC₂S, hC₂char, hC128⟩ :=
    hGN G T h.simple h.qtke h.sylow h.ne_bot
  obtain ⟨S, hS⟩ := h.exists_sylow
  have hEven := h.qtke.2.1
  refine ⟨C₂, hC₂ne, hC₂S, hC₂char, fun M hM => ?_⟩
  set V : Subgroup G := VZ T M with hVdef
  have hTM : T ≤ M := hM.2
  have hSM : (S : Subgroup G) ≤ M := hS ▸ hTM
  have hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    hEven M hM.1.1 ⟨S, hSM⟩
  have hVred : IsTwoReducedIn M V := by
    have := isTwoReducedIn_conjClosure M S hSM hF le_rfl
    rwa [hS] at this
  have hMV : M ≤ Subgroup.normalizer (V : Set G) := hVred.2.1
  have hTC₂ : T ≤ Subgroup.normalizer (C₂ : Set G) :=
    (Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)).trans
      (normalizer_le_normalizer_of_characteristic_subgroupOf hC₂S hC₂char)
  set C : Subgroup G := M ⊓ Subgroup.centralizer (V : Set G) with hCdef
  have hMC : M ≤ Subgroup.normalizer (C : Set G) := s14111_le_normalizer_inf_centralizer hMV
  have hfac_of_le : M ≤ C ⊔ (M ⊓ Subgroup.normalizer (C₂ : Set G)) →
      ∀ m ∈ M, ∃ c ∈ C, ∃ n ∈ M ⊓ Subgroup.normalizer (C₂ : Set G), m = c * n := by
    intro hle m hm
    have hm' : m ∈ ((C ⊔ (M ⊓ Subgroup.normalizer (C₂ : Set G)) : Subgroup G) : Set G) := hle hm
    rw [Subgroup.coe_mul_of_right_le_normalizer_left C _ (inf_le_left.trans hMC)] at hm'
    obtain ⟨c, hc, n, hn, rfl⟩ := hm'
    exact ⟨c, hc, n, hn, rfl⟩
  by_cases hJ : thompsonJ T ≤ M ⊓ Subgroup.centralizer (V : Set G)
  ·
    left
    set R : Subgroup G := T ⊓ Subgroup.centralizer (V : Set G) with hRdef
    have hRC : R ≤ C := inf_le_inf_right _ hTM
    have hRp : IsPGroup 2 R := h.sylow.1.to_le inf_le_left
    have hRodd : ¬ 2 ∣ R.relIndex C := by
      have h1 := s14111_odd_relIndex (S := (S : Subgroup G)) (D := C) S.not_dvd_index
        (hSM.trans hMC)
      have h2 : (S : Subgroup G) ⊓ C = R := by
        rw [hS, hCdef, hRdef, ← inf_assoc, inf_eq_left.mpr hTM]
      rwa [h2] at h1
    have hfrat := exists_mul_of_sylow inf_le_left hMC hRC hRp hRodd
    have hbaum : baum T = baum R := by
      have := (lemma_14_1_2_one S hSM hVred (by rwa [hS])).2
      rwa [hS] at this
    have hNR : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C₂ : Set G) :=
      (normalizer_le_normalizer_baum R).trans (hbaum ▸
        normalizer_le_normalizer_of_characteristic_subgroupOf hC₂S hC₂char)
    intro m hm
    obtain ⟨n, hn, c, hc, rfl⟩ := hfrat m hm
    refine ⟨n * c * n⁻¹, ?_, n, ⟨hn.1, hNR hn.2⟩, by group⟩
    exact (Subgroup.mem_normalizer_iff.mp (hMC hn.1) c).mp hc
  · by_cases h2 : M = Mc ∧ 2 < Nat.card (quasithinOmegaOneCenter T)
    · exact Or.inr h2
    left
    by_contra h1
    have hZne : quasithinOmegaOneCenter T ≠ ⊥ := h.omegaOneCenter_ne_bot
    have hZp : IsPGroup 2 (quasithinOmegaOneCenter T) := h.sylow.1.to_le (by
      unfold quasithinOmegaOneCenter
      rw [Subgroup.closure_le]
      exact fun z hz => hz.1.1)
    have hZcard : 2 ≤ Nat.card (quasithinOmegaOneCenter T) := by
      obtain ⟨k, hk⟩ := hZp.exists_card_eq
      rcases k with _ | k
      · exact absurd (Subgroup.card_eq_one.mp (by simpa using hk)) hZne
      · rw [hk]; exact Nat.le_self_pow (Nat.succ_ne_zero k) 2 |>.trans' le_rfl
    have hcase : M ≠ Mc ∨ Nat.card (quasithinOmegaOneCenter T) = 2 := by
      by_cases hMMc : M = Mc
      · right
        have : ¬ 2 < Nat.card (quasithinOmegaOneCenter T) := fun hlt => h2 ⟨hMMc, hlt⟩
        omega
      · left; exact hMMc
    have hZ2 : Nat.card (quasithinOmegaOneCenter T) = 2 := by
      rcases h17 G T Mc h M V hM hVred hJ hcase with h7 | h7
      · exact h7.2.2.2
      · exact h7.2.choose_spec.choose_spec.choose_spec.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    have hC₁eq : C₁ = quasithinOmegaOneCenter T := by
      refine Subgroup.eq_of_le_of_card_ge hC₁Z ?_
      rw [hZ2]
      have hdvd : Nat.card C₁ ∣ 2 := hZ2 ▸ Subgroup.card_dvd_of_le hC₁Z
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1' | h1'
      · exact absurd (Subgroup.card_eq_one.mp h1') hC₁ne
      · exact h1'.ge
    have hstab := h17s G T Mc h M V hM hVred hJ hcase
    have hM0 : (M ⊓ Subgroup.centralizer (C₁ : Set G)) ⊔
        (M ⊓ Subgroup.normalizer (C₂ : Set G)) ≤ C ⊔ (M ⊓ Subgroup.normalizer (C₂ : Set G)) := by
      refine sup_le ?_ le_sup_right
      rw [hC₁eq]
      exact hstab.trans (sup_le le_sup_left ((le_inf hTM hTC₂).trans le_sup_right))
    rcases hC128 M hM with hM0eq | ⟨s, L, -, -, hL, hMeq⟩
    · exact h1 (hfac_of_le (hM0eq.le.trans hM0))
    obtain ⟨i, hi⟩ : ∃ i, ¬ L i ≤ C := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      exact h1 (hfac_of_le (hMeq.le.trans (sup_le hM0 (iSup_le fun i => (hall i).trans le_sup_left))))
    obtain ⟨⟨hblock, htype⟩, hLJ⟩ := hL i
    have hinf : perfectCore M ≤ Subgroup.centralizer (V : Set G) :=
      (h16 G T Mc h).1 M V hM hVred
    have hLM : L i ≤ M := hblock.2.1
    have hnotperf : ¬ ⁅L i, L i⁆ = L i := fun hp =>
      hi ((le_inf hLM ((s14111_le_perfectCore hLM hp).trans hinf)))
    have hA3 : IsAltType (L i) 3 := by
      rcases htype with ⟨n, hn, F, hF, hFt, hcard, α, hα, hker, -⟩ | ⟨m, hm, hm3, hAlt⟩
      · exfalso
        apply hnotperf
        have h4 : ∃ s : Finset F, s.card = 4 := by
          have : 4 ≤ (Finset.univ : Finset F).card := by
            rw [Finset.card_univ, hcard]
            calc 4 = 2 ^ 2 := by norm_num
              _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
          obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq this
          exact ⟨t, ht⟩
        have := CFSG.LinearGroups.special_linear_dimension_two_perfect h4
        exact s14111_perfect_of_short hblock.1 α hα hker
      · by_cases hm3' : m = 3
        · rwa [hm3'] at hAlt
        · exfalso
          apply hnotperf
          obtain ⟨α, hα, hker, -⟩ := hAlt
          have h5 : 5 ≤ Nat.card (Fin m) := by
            rw [Nat.card_eq_fintype_card, Fintype.card_fin]
            obtain ⟨k, rfl⟩ := hm
            omega
          have : Group.IsPerfect (alternatingGroup (Fin m)) :=
            ⟨commutator_alternatingGroup_eq_top h5⟩
          exact s14111_perfect_of_short hblock.1 α hα hker
    obtain ⟨hMc, hZ⟩ := h110 G T Mc h M (L i) T hM hblock hA3
      (by rw [← hS]; exact pCoreOf_two_le_sylow M S hSM) le_rfl hLJ
    exact h2 ⟨hMc, hZ⟩

end Reduction

end CFSG.Quasithin
