module

public import CFSG.Milestones.ASVolI.F48.D43.Rels
public import Certificates.Certificate7804
public import Certificates.Certificate7805
public import CFSG.Milestones.ASVolI.A3Aut.Core

public section

namespace CFSG.ASVolI

open CFSG.Blueprint.Chevalley CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
  CFSG.CosetTable

attribute [local irreducible] burnsideF48d_KeysHex burnsideF48d_TabsHex burnsideF48d_GensHex
  burnsideF48d_PhiHex burnsideF48d_limbs burnsideF48d_colTab

theorem burnsideF48d_ev_map_letters {G : Type*} [Group G] {m m' : ℕ} (h : Fin m → G)
    (f : Fin m' → Fin m) (w : List (Fin m' × Bool)) :
    burnsideF48s_ev h (w.map fun l => (f l.1, l.2)) = burnsideF48s_ev (fun i => h (f i)) w := by
  simp only [burnsideF48s_ev, List.map_map, Function.comp_def]

theorem burnsideF48d_ev_restrict {G : Type*} [Group G] {m : ℕ} (S : List (Fin m))
    {ws : List (List (Fin m × Bool))} (h : Fin m → G) (hrel : ∀ w ∈ ws, burnsideF48s_ev h w = 1) :
    ∀ w ∈ restrictWords S ws, burnsideF48s_ev (fun i => h (S.get i)) w = 1 := by
  intro w hw
  simp only [restrictWords, List.mem_filterMap] at hw
  obtain ⟨w0, hw0, hren⟩ := hw
  rw [← burnsideF48d_ev_map_letters, map_renumber S w0 w hren]
  exact hrel w0 hw0

theorem burnsideF48d_card_closure_le {G : Type*} [Group G] {m : ℕ}
    {ws : List (List (Fin m × Bool))} [Finite (PG m ws)] (h : Fin m → G)
    (hrel : ∀ w ∈ ws, burnsideF48s_ev h w = 1) :
    Nat.card (Subgroup.closure (Set.range h)) ≤ Nat.card (PG m ws) := by
  have hr : (burnsideF48s_presHom ws h hrel).range = Subgroup.closure (Set.range h) := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      ← Set.range_comp]
    congr 2
    funext i
    exact burnsideF48s_presHom_of hrel i
  rw [← hr]
  exact Nat.card_le_card_of_surjective _ (burnsideF48s_presHom ws h hrel).rangeRestrict_surjective

abbrev burnsideF48d_S1L : List (Fin 17) := subsetOf 17 burnsideF48d_tS1

abbrev burnsideF48d_SBL : List (Fin burnsideF48d_S1L.length) :=
  subsetOf burnsideF48d_S1L.length burnsideF48d_tSB

abbrev burnsideF48d_SUL : List (Fin burnsideF48d_SBL.length) :=
  subsetOf burnsideF48d_SBL.length burnsideF48d_tSU

@[expose] def burnsideF48d_back3 (i : Fin burnsideF48d_SUL.length) : Fin 17 :=
  burnsideF48d_S1L.get (burnsideF48d_SBL.get (burnsideF48d_SUL.get i))

theorem burnsideF48d_back3_ge : ∀ i, 5 ≤ (burnsideF48d_back3 i).val := by decide

theorem burnsideF48d_back3_surj : ∀ j : Fin 17, 5 ≤ j.val → ∃ i, burnsideF48d_back3 i = j := by
  decide

theorem burnsideF48d_range_back3 :
    Set.range (fun i => burnsideF48d_L (burnsideF48d_back3 i)) =
      burnsideF48d_L '' {j | 5 ≤ j.val} := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, burnsideF48d_back3_ge i, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨i, hi⟩ := burnsideF48d_back3_surj j hj
    exact ⟨i, by simp only [hi]⟩

section Model


theorem burnsideF48d_rels_Ws : ∀ w ∈ burnsideF48d_Ws, burnsideF48s_ev burnsideF48d_L w = 1 := by
  intro w hw
  simp only [burnsideF48d_Ws, burnsideF48s_eWs, List.mem_append, List.mem_singleton] at hw
  rcases hw with (h | h) | rfl
  · exact burnsideF48d_rels w (List.mem_append_left _ (List.mem_append_left _ h))
  · exact burnsideF48d_rels w (List.mem_append_left _ (List.mem_append_right _ h))
  · have e : burnsideF48s_eCandRel 6 [((0 : Fin 17), true)] [((1 : Fin 17), true)] [] =
        (List.replicate 6 burnsideF48d_xyW).flatten := by
      simp [burnsideF48s_eCandRel, burnsideF48s_eInvW]
    rw [e]
    exact burnsideF48d_rels _ (List.mem_append_right _ (by simp))

theorem burnsideF48d_rels_Ws3 : ∀ w ∈ burnsideF48d_Ws3,
    burnsideF48s_ev (fun i => burnsideF48d_L (burnsideF48d_back3 i)) w = 1 :=
  burnsideF48d_ev_restrict burnsideF48d_SUL _
    (burnsideF48d_ev_restrict burnsideF48d_SBL _
      (burnsideF48d_ev_restrict burnsideF48d_S1L _ burnsideF48d_rels_Ws))

theorem burnsideF48d_tc2_parts :
    (Finite (PG _ burnsideF48d_Ws3) ∧ Nat.card (PG _ burnsideF48d_Ws3) ≤ 729 * 729) ∧
    (Finite (PG _ burnsideF48d_Ws1) ∧
      Nat.card (PG _ burnsideF48d_Ws1) ≤ 28 * (52 * (729 * 729))) :=
  Certificates.certificate7805

theorem burnsideF48d_card_U_le :
    Nat.card ↥burnsideF48d_U ≤ 531441 := by
  obtain ⟨⟨f3, d3⟩, -⟩ := burnsideF48d_tc2_parts
  have hle := burnsideF48d_card_closure_le (ws := burnsideF48d_Ws3)
    (fun i => burnsideF48d_L (burnsideF48d_back3 i)) burnsideF48d_rels_Ws3
  have hU : Subgroup.closure (burnsideF48d_L '' {j | 5 ≤ j.val}) = burnsideF48d_U := rfl
  rw [burnsideF48d_range_back3, hU] at hle
  have := hle.trans d3
  omega

theorem burnsideF48d_sup_UT : burnsideF48d_U ⊔ burnsideF48d_T = burnsideF48d_P1 ⊓ burnsideF48d_P2 := by
  apply le_antisymm (sup_le burnsideF48d_U_le burnsideF48d_T_le)
  rw [burnsideF48d_B_eq_closure, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  by_cases h5 : 5 ≤ j.val
  · exact Subgroup.mem_sup_left (Subgroup.subset_closure ⟨j, h5, rfl⟩)
  · have hj' : 2 ≤ j.val := hj
    exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨j, ⟨hj', by omega⟩, rfl⟩)

theorem burnsideF48d_T_le_normalizer :
    burnsideF48d_T ≤ Subgroup.normalizer (burnsideF48d_U : Set ↥burnsideF48d_X) :=
  le_trans burnsideF48d_T_le burnsideF48d_B_le_normalizer

theorem burnsideF48d_card_U_ge : 531441 ≤ Nat.card ↥burnsideF48d_U := by
  let f : ↥burnsideF48d_U × ↥burnsideF48d_T → ↥(burnsideF48d_P1 ⊓ burnsideF48d_P2) := fun p =>
    ⟨p.1 * p.2, by rw [← burnsideF48d_sup_UT]; exact Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Surjective f := by
    rintro ⟨b, hb⟩
    rw [← burnsideF48d_sup_UT] at hb
    obtain ⟨u, hu, t, ht, rfl⟩ := (burnsideAut_mem_sup_iff burnsideF48d_T_le_normalizer).1 hb
    exact ⟨(⟨u, hu⟩, ⟨t, ht⟩), rfl⟩
  have := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_prod, burnsideF48d_card_B, burnsideF48d_card_T] at this
  omega

theorem burnsideF48d_card_U : Nat.card ↥burnsideF48d_U = 531441 :=
  le_antisymm burnsideF48d_card_U_le burnsideF48d_card_U_ge

theorem burnsideF48d_sylow : ChF.IsSylowOf 3 burnsideF48d_U ⊤ := by
  have hc : Nat.card ↥burnsideF48d_U = 3 ^ 12 := by rw [burnsideF48d_card_U]; norm_num
  refine ⟨le_top, IsPGroup.of_card hc, ?_⟩
  rw [Subgroup.relIndex_top_right]
  have h := Subgroup.card_mul_index burnsideF48d_U
  rw [burnsideF48d_card_U, burnsideF48d_card_X] at h
  have h2 : burnsideF48d_U.index = 38688832 := by omega
  rw [h2]
  decide

theorem burnsideF48d_hconj : ∀ K'' : Subgroup ↥burnsideF48d_X,
    K'' ≤ burnsideF48d_P1 ⊓ burnsideF48d_P2 → Nat.card ↥K'' = 52 →
      ∃ t ∈ burnsideF48d_P1 ⊓ burnsideF48d_P2, ∀ z, z ∈ K'' ↔ t * z * t⁻¹ ∈ burnsideF48d_T := by
  intro K'' hle hcard
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hU3 : IsPGroup 3 burnsideF48d_U :=
    IsPGroup.of_card (n := 12) (by rw [burnsideF48d_card_U]; norm_num)
  have hKn : K'' ≤ Subgroup.normalizer (burnsideF48d_U : Set ↥burnsideF48d_X) :=
    le_trans hle burnsideF48d_B_le_normalizer
  have hT3 : ¬ 3 ∣ Nat.card ↥burnsideF48d_T := by rw [burnsideF48d_card_T]; decide
  have hdisj : ∀ H : Subgroup ↥burnsideF48d_X, Nat.card ↥H = 52 → Disjoint burnsideF48d_U H :=
    fun H hH => Subgroup.disjoint_of_coprime_natCard (by rw [burnsideF48d_card_U, hH]; decide)
  have hsupB : ∀ H : Subgroup ↥burnsideF48d_X, H ≤ burnsideF48d_P1 ⊓ burnsideF48d_P2 →
      Nat.card ↥H = 52 → burnsideF48d_U ⊔ H = burnsideF48d_P1 ⊓ burnsideF48d_P2 := by
    intro H hH hc
    apply Subgroup.eq_of_le_of_card_ge (sup_le burnsideF48d_U_le hH)
    have h1 : Nat.card ↥burnsideF48d_U ∣ Nat.card ↥(burnsideF48d_U ⊔ H) :=
      Subgroup.card_dvd_of_le le_sup_left
    have h2 : Nat.card ↥H ∣ Nat.card ↥(burnsideF48d_U ⊔ H) := Subgroup.card_dvd_of_le le_sup_right
    have hcop : Nat.Coprime (Nat.card ↥burnsideF48d_U) (Nat.card ↥H) := by
      rw [burnsideF48d_card_U, hc]; decide
    have h3 := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h1 h2
    rw [burnsideF48d_card_U, hc] at h3
    rw [burnsideF48d_card_B]
    exact Nat.le_of_dvd Nat.card_pos h3
  obtain ⟨e, he, hmap⟩ := burnsideAut_conj_of_complements (p := 3) burnsideF48d_T_le_normalizer hKn
    hU3 hT3 (hdisj _ burnsideF48d_card_T) (hdisj _ hcard)
    (by rw [hsupB K'' hle hcard, hsupB _ burnsideF48d_T_le burnsideF48d_card_T])
  refine ⟨e, burnsideF48d_U_le he, fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · rw [← hmap]
    exact ⟨z, hz, rfl⟩
  · rw [← hmap] at hz
    obtain ⟨z', hz', he'⟩ := hz
    have h : e * z' * e⁻¹ = e * z * e⁻¹ := he'
    simp only [mul_left_inj, mul_right_inj] at h
    rw [← h]
    exact hz'

theorem burnsideF48d_card_PG :
    Finite (PG 17 burnsideF48d_Ws) ∧ Nat.card (PG 17 burnsideF48d_Ws) ≤ 20560831566912 := by
  obtain ⟨f0, d0⟩ := CFSG.KC.MiscCoset.card_le_of_index_restrict burnsideF48d_Ws
    (subsetOf 17 burnsideF48d_tS1) Certificates.certificate7804 burnsideF48d_tc2_parts.2
  exact ⟨f0, d0.trans (by norm_num)⟩

end Model

end CFSG.ASVolI
