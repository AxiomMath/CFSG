module

public import CFSG.Milestones.ASVolI.F48.Rest.U52Stab
public import CFSG.Milestones.ASVolI.F48.Rest.G23Lie
public import Certificates.Certificate7771

public section

namespace CFSG.ASVolI

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore CFSG.Monster.B.Co2.Native
  CFSG.Certificates.Native CFSG.Certificates CFSG.CosetTable CFSG.Quasithin

attribute [local irreducible] burnsideF48t_u52LArr burnsideF48t_u52GensArr

@[expose] noncomputable def burnsideF48t_u52S0 : Subgroup ↥burnsideF48t_u52X :=
  burnsideF48t_u52S0'.subgroupOf burnsideF48t_u52X

@[expose] noncomputable def burnsideF48t_u52K : Subgroup ↥burnsideF48t_u52X :=
  burnsideF48t_u52K'.subgroupOf burnsideF48t_u52X

section Letters


@[expose] noncomputable def burnsideF48t_u52L (i : Fin 4) : ↥burnsideF48t_u52X :=
  ⟨burnsideF48t_u52σ i, burnsideF48t_u52_σ_mem i.2⟩

theorem burnsideF48t_u52_coe_L (i : Fin 4) :
    ((burnsideF48t_u52L i : ↥burnsideF48t_u52X) : Equiv.Perm (Fin 462)) = burnsideF48t_u52σ i :=
  rfl

theorem burnsideF48t_u52_coe_L' (i : Fin 4) (n : ℕ) (h : (i : ℕ) = n) :
    ((burnsideF48t_u52L i : ↥burnsideF48t_u52X) : Equiv.Perm (Fin 462)) = burnsideF48t_u52σ n := by
  subst h
  rfl

theorem burnsideF48t_u52_coe_ev (w : List (Fin 4 × Bool)) :
    ((burnsideF48s_ev burnsideF48t_u52L w : ↥burnsideF48t_u52X) : Equiv.Perm (Fin 462)) =
      burnsideF48s_ev (fun i : Fin 4 => burnsideF48t_u52σ i) w :=
  (burnsideF48s_ev_map burnsideF48t_u52X.subtype burnsideF48t_u52L w).symm

@[expose] noncomputable def burnsideF48t_u52P1 : Subgroup ↥burnsideF48t_u52X :=
  Subgroup.closure (burnsideF48t_u52L '' burnsideF48t_g23S1)

@[expose] noncomputable def burnsideF48t_u52P2 : Subgroup ↥burnsideF48t_u52X :=
  Subgroup.closure (burnsideF48t_u52L '' burnsideF48t_g23S2)

end Letters

section Sub


theorem burnsideF48t_u52_σ_mem_P1' {i : ℕ} (hi : i < 3) :
    burnsideF48t_u52σ i ∈ burnsideF48t_u52P1' := by
  rw [burnsideF48t_u52_P1'_eq_closure]
  exact Subgroup.subset_closure ⟨⟨i, by rw [burnsideF48t_u52_P1Arr.1]; exact hi⟩, rfl⟩

theorem burnsideF48t_u52_σ_mem_P2' {i : ℕ} (hi : i = 0 ∨ i = 1 ∨ i = 3) :
    burnsideF48t_u52σ i ∈ burnsideF48t_u52P2' := by
  rw [burnsideF48t_u52_P2'_eq_closure]
  rcases hi with rfl | rfl | rfl
  · exact Subgroup.subset_closure ⟨⟨0, by rw [burnsideF48t_u52_P2Arr.1]; norm_num⟩,
      by simp [burnsideF48t_u52P2Idx]⟩
  · exact Subgroup.subset_closure ⟨⟨1, by rw [burnsideF48t_u52_P2Arr.1]; norm_num⟩,
      by simp [burnsideF48t_u52P2Idx]⟩
  · exact Subgroup.subset_closure ⟨⟨2, by rw [burnsideF48t_u52_P2Arr.1]; norm_num⟩,
      by simp [burnsideF48t_u52P2Idx]⟩

theorem burnsideF48t_u52_map_P1 :
    burnsideF48t_u52P1.map burnsideF48t_u52X.subtype = burnsideF48t_u52P1' := by
  rw [burnsideF48t_u52P1, MonoidHom.map_closure, Set.image_image]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi3 : (i : ℕ) < 3 := by
      have h1 := i.2
      have h2 : (i : ℕ) ≠ 3 := fun h => hi (Fin.ext h)
      omega
    simp only [SetLike.mem_coe, burnsideF48t_u52_coe_L]
    exact burnsideF48t_u52_σ_mem_P1' hi3
  · rw [burnsideF48t_u52_P1'_eq_closure, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    have hk : (k : ℕ) < 3 := burnsideF48t_u52_P1Arr.1 ▸ k.2
    refine Subgroup.subset_closure ⟨⟨k, by omega⟩, fun h => ?_, ?_⟩
    · have := congrArg Fin.val h
      simp only at this
      omega
    · simp only [burnsideF48t_u52_coe_L]
      rfl

theorem burnsideF48t_u52_map_P2 :
    burnsideF48t_u52P2.map burnsideF48t_u52X.subtype = burnsideF48t_u52P2' := by
  rw [burnsideF48t_u52P2, MonoidHom.map_closure, Set.image_image]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    have hi3 : (i : ℕ) = 0 ∨ (i : ℕ) = 1 ∨ (i : ℕ) = 3 := by
      have h1 := i.2
      have h2 : (i : ℕ) ≠ 2 := fun h => hi (Fin.ext h)
      omega
    simp only [SetLike.mem_coe, burnsideF48t_u52_coe_L]
    exact burnsideF48t_u52_σ_mem_P2' hi3
  · rw [burnsideF48t_u52_P2'_eq_closure, Subgroup.closure_le]
    rintro _ ⟨k, rfl⟩
    rcases burnsideF48t_u52_P2Idx_cases k with h | h | h
    · refine Subgroup.subset_closure ⟨0, by decide, ?_⟩
      simp only [Subgroup.coe_subtype, burnsideF48t_u52_coe_L' 0 0 rfl, h]
    · refine Subgroup.subset_closure ⟨1, by decide, ?_⟩
      simp only [Subgroup.coe_subtype, burnsideF48t_u52_coe_L' 1 1 rfl, h]
    · refine Subgroup.subset_closure ⟨3, by decide, ?_⟩
      simp only [Subgroup.coe_subtype, burnsideF48t_u52_coe_L' 3 3 rfl, h]

theorem burnsideF48t_u52_mem_P1 (z : ↥burnsideF48t_u52X) :
    z ∈ burnsideF48t_u52P1 ↔ (z : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52P1' := by
  rw [← burnsideF48t_u52_map_P1]
  exact (Subgroup.mem_map_iff_mem burnsideF48t_u52X.subtype_injective).symm

theorem burnsideF48t_u52_mem_P2 (z : ↥burnsideF48t_u52X) :
    z ∈ burnsideF48t_u52P2 ↔ (z : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52P2' := by
  rw [← burnsideF48t_u52_map_P2]
  exact (Subgroup.mem_map_iff_mem burnsideF48t_u52X.subtype_injective).symm

theorem burnsideF48t_u52_mem_P1_iff (z : ↥burnsideF48t_u52X) :
    z ∈ burnsideF48t_u52P1 ↔ (z : Equiv.Perm (Fin 462)) burnsideF48t_u52pA = burnsideF48t_u52pA := by
  rw [burnsideF48t_u52_mem_P1, burnsideF48t_u52_P1'_eq]
  exact ⟨fun h => MulAction.mem_stabilizer_iff.1 h.2,
    fun h => ⟨z.2, MulAction.mem_stabilizer_iff.2 h⟩⟩

theorem burnsideF48t_u52_mem_P2_iff (z : ↥burnsideF48t_u52X) :
    z ∈ burnsideF48t_u52P2 ↔ (z : Equiv.Perm (Fin 462)) burnsideF48t_u52pB = burnsideF48t_u52pB := by
  rw [burnsideF48t_u52_mem_P2, burnsideF48t_u52_P2'_eq]
  exact ⟨fun h => MulAction.mem_stabilizer_iff.1 h.2,
    fun h => ⟨z.2, MulAction.mem_stabilizer_iff.2 h⟩⟩

theorem burnsideF48t_u52_map_B :
    (burnsideF48t_u52P1 ⊓ burnsideF48t_u52P2).map burnsideF48t_u52X.subtype = burnsideF48t_u52B' := by
  rw [Subgroup.map_inf_eq _ _ _ burnsideF48t_u52X.subtype_injective, burnsideF48t_u52_map_P1,
    burnsideF48t_u52_map_P2, burnsideF48t_u52_B'_eq]

theorem burnsideF48t_u52_card_B :
    Nat.card ↥(burnsideF48t_u52P1 ⊓ burnsideF48t_u52P2) = 9216 := by
  rw [← Subgroup.card_map_of_injective burnsideF48t_u52X.subtype_injective, burnsideF48t_u52_map_B,
    burnsideF48t_u52_card_B']

theorem burnsideF48t_u52_card_S0 : Nat.card ↥burnsideF48t_u52S0 = 1024 := by
  rw [burnsideF48t_u52S0, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    burnsideF48t_u52_S0'_le_X).toEquiv, burnsideF48t_u52_card_S0']

theorem burnsideF48t_u52_K'_le_X :
    burnsideF48t_u52K' ≤ burnsideF48t_u52X := by
  refine burnsideF48t_u52_K'_le_B'.trans ?_
  rw [burnsideF48t_u52_B'_eq]
  exact inf_le_left.trans burnsideF48t_u52_P1'_le_X

theorem burnsideF48t_u52_card_K :
    Nat.card ↥burnsideF48t_u52K = 9 := by
  rw [burnsideF48t_u52K, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    burnsideF48t_u52_K'_le_X).toEquiv, burnsideF48t_u52_card_K']

theorem burnsideF48t_u52_sylow : ChF.IsSylowOf 2 burnsideF48t_u52S0 ⊤ := by
  have hc : Nat.card ↥burnsideF48t_u52S0 = 2 ^ 10 := by rw [burnsideF48t_u52_card_S0]; norm_num
  refine ⟨le_top, IsPGroup.of_card hc, ?_⟩
  rw [Subgroup.relIndex_top_right]
  have h := Subgroup.card_mul_index burnsideF48t_u52S0
  rw [hc, burnsideF48t_u52_card_X] at h
  have h2 : burnsideF48t_u52S0.index = 13365 := by omega
  rw [h2]
  decide

theorem burnsideF48t_u52_B_eq : burnsideF48t_u52P1 ⊓ burnsideF48t_u52P2 =
    ⊤ ⊓ Subgroup.normalizer (burnsideF48t_u52S0 : Set ↥burnsideF48t_u52X) := by
  rw [top_inf_eq]
  ext z
  constructor
  · intro hz
    have hzB : (z : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52B' := by
      rw [burnsideF48t_u52_B'_eq]
      exact ⟨(burnsideF48t_u52_mem_P1 z).1 hz.1, (burnsideF48t_u52_mem_P2 z).1 hz.2⟩
    have hn := burnsideF48t_u52_B'_le_normalizer hzB
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro w
    rw [burnsideF48t_u52S0, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv]
    exact hn w
  · intro hz
    have hn : ∀ s ∈ burnsideF48t_u52S0',
        (z : Equiv.Perm (Fin 462))⁻¹ * s * z ∈ burnsideF48t_u52S0' := by
      intro s hs
      have hsX : s ∈ burnsideF48t_u52X := burnsideF48t_u52_S0'_le_X hs
      have hz' := Subgroup.inv_mem _ hz
      have h1 := (Subgroup.mem_normalizer_iff.1 hz' ⟨s, hsX⟩).1
        (show (⟨s, hsX⟩ : ↥burnsideF48t_u52X) ∈ burnsideF48t_u52S0 from hs)
      rw [inv_inv, burnsideF48t_u52S0, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
        Subgroup.coe_mul, Subgroup.coe_inv] at h1
      exact h1
    obtain ⟨h0, h165⟩ := burnsideF48t_u52_fix_of_norm z.2 hn
    exact ⟨(burnsideF48t_u52_mem_P1_iff z).2 h0, (burnsideF48t_u52_mem_P2_iff z).2 h165⟩

theorem burnsideF48t_u52_L2_not_mem : burnsideF48t_u52L 2 ∉ burnsideF48t_u52P2 := by
  rw [burnsideF48t_u52_mem_P2_iff, burnsideF48t_u52_coe_L' 2 2 rfl]
  exact burnsideF48t_u52_σ_fix.2.2.2.2.2.2.2

theorem burnsideF48t_u52_L3_not_mem : burnsideF48t_u52L 3 ∉ burnsideF48t_u52P1 := by
  rw [burnsideF48t_u52_mem_P1_iff, burnsideF48t_u52_coe_L' 3 3 rfl]
  exact burnsideF48t_u52_σ_fix.2.2.2.2.2.2.1

theorem burnsideF48t_u52_P1_ne_P2 : burnsideF48t_u52P1 ≠ burnsideF48t_u52P2 := by
  intro h
  have h1 : burnsideF48t_u52L 2 ∈ burnsideF48t_u52P1 :=
    Subgroup.subset_closure ⟨2, show (2 : Fin 4) ≠ 3 by decide, rfl⟩
  rw [h] at h1
  exact burnsideF48t_u52_L2_not_mem h1

theorem burnsideF48t_u52_P1_max : burnsideF48t_u52P1 ⊓ burnsideF48t_u52P2 ≤ burnsideF48t_u52P1 ∧
    burnsideF48t_u52P1 ≤ ⊤ ∧ burnsideF48t_u52P1 ≠ ⊤ ∧
    ∀ R : Subgroup ↥burnsideF48t_u52X, burnsideF48t_u52P1 < R → R ≤ ⊤ → R = ⊤ := by
  refine ⟨inf_le_left, le_top, fun h => burnsideF48t_u52_L3_not_mem (h ▸ Subgroup.mem_top _),
    fun R hR _ => ?_⟩
  have hlt : burnsideF48t_u52P1' < R.map burnsideF48t_u52X.subtype := by
    rw [← burnsideF48t_u52_map_P1]
    exact (Subgroup.map_lt_map_iff_of_injective burnsideF48t_u52X.subtype_injective).2 hR
  have hRX := burnsideF48t_u52_P1'_max hlt (Subgroup.map_subtype_le R)
  rw [eq_top_iff]
  intro z _
  have hz : (z : Equiv.Perm (Fin 462)) ∈ R.map burnsideF48t_u52X.subtype := by
    rw [hRX]
    exact z.2
  exact (Subgroup.mem_map_iff_mem burnsideF48t_u52X.subtype_injective).1 hz

theorem burnsideF48t_u52_P2_max : burnsideF48t_u52P1 ⊓ burnsideF48t_u52P2 ≤ burnsideF48t_u52P2 ∧
    burnsideF48t_u52P2 ≤ ⊤ ∧ burnsideF48t_u52P2 ≠ ⊤ ∧
    ∀ R : Subgroup ↥burnsideF48t_u52X, burnsideF48t_u52P2 < R → R ≤ ⊤ → R = ⊤ := by
  refine ⟨inf_le_right, le_top, fun h => burnsideF48t_u52_L2_not_mem (h ▸ Subgroup.mem_top _),
    fun R hR _ => ?_⟩
  have hlt : burnsideF48t_u52P2' < R.map burnsideF48t_u52X.subtype := by
    rw [← burnsideF48t_u52_map_P2]
    exact (Subgroup.map_lt_map_iff_of_injective burnsideF48t_u52X.subtype_injective).2 hR
  have hRX := burnsideF48t_u52_P2'_max hlt (Subgroup.map_subtype_le R)
  rw [eq_top_iff]
  intro z _
  have hz : (z : Equiv.Perm (Fin 462)) ∈ R.map burnsideF48t_u52X.subtype := by
    rw [hRX]
    exact z.2
  exact (Subgroup.mem_map_iff_mem burnsideF48t_u52X.subtype_injective).1 hz

end Sub

section Engine

theorem burnsideF48t_renumber_none {m : ℕ} {S : List (Fin m)} :
    ∀ {w : List (Fin m × Bool)} {l : Fin m × Bool}, l ∈ w → l.1 ∉ S → renumber S w = none := by
  intro w
  induction w with
  | nil => intro l hl; cases hl
  | cons l' w ih =>
    intro l hl hS
    simp only [renumber]
    rcases List.mem_cons.1 hl with rfl | hl'
    · have : S.finIdxOf? l.1 = none := by
        rw [List.finIdxOf?_eq_none_iff]
        exact hS
      rw [this]
    · rw [ih hl' hS]
      split <;> simp_all

theorem burnsideF48t_u52_restrict {i j k : ℕ} (hj : j < 2) :
    restrictWords (subsetOf 4 [0, 1, 2]) (burnsideF48t_u52Ws i j k) = burnsideF48t_u52WsB := by
  have hy : ∀ v ∈ burnsideF48t_u52YW, ∃ b, ((3 : Fin 4), b) ∈ v := by decide
  have hv : burnsideF48t_u52YW.getD j [] ∈ burnsideF48t_u52YW := by
    rw [List.getD_eq_getElem _ _ (by simpa [burnsideF48t_u52YW] using hj)]
    exact List.getElem_mem _
  obtain ⟨b, hb⟩ := hy _ hv
  have hmem : ((3 : Fin 4), b) ∈ burnsideF48s_eCandRel 4 (burnsideF48t_u52XW.getD i [])
      (burnsideF48t_u52YW.getD j []) (burnsideF48t_u52KW.getD k []) := by
    simp only [burnsideF48s_eCandRel, List.mem_append, List.mem_flatten, List.mem_replicate]
    exact Or.inl ⟨_, ⟨by norm_num, rfl⟩, List.mem_append_right _ hb⟩
  have hn := burnsideF48t_renumber_none (S := subsetOf 4 [0, 1, 2]) hmem
    (show (3 : Fin 4) ∉ subsetOf 4 [0, 1, 2] by decide)
  simp only [burnsideF48t_u52Ws, burnsideF48s_eWs, restrictWords, List.filterMap_append,
    List.filterMap_cons, hn, List.filterMap_nil, List.append_nil]


theorem burnsideF48t_u52_rels : ∀ r ∈ burnsideF48t_u52R1 ++ burnsideF48t_u52R2,
    burnsideF48s_ev (fun i : Fin 4 => burnsideF48t_u52σ i) r = 1 := by
  have h := burnsideF48t_u52_mem.2.2.1
  simp only [burnsideF48t_u52RelOK] at h
  intro r hr
  exact burnsideF48t_ev_eq_one_of burnsideF48t_u52_recL (List.all_eq_true.1 h r hr)

theorem burnsideF48t_u52_ev_single (i : Fin 4) :
    burnsideF48s_ev burnsideF48t_u52L [(i, true)] = burnsideF48t_u52L i := by
  simp [burnsideF48s_ev]

theorem burnsideF48t_u52_tc {t : ℕ × ℕ × ℕ × ℕ} (ht : t ∈ burnsideF48t_u52Cands) :
    Finite (PG 4 (burnsideF48t_u52Ws t.1 t.2.1 t.2.2.1)) ∧
      Nat.card (PG 4 (burnsideF48t_u52Ws t.1 t.2.1 t.2.2.1)) ≤ t.2.2.2 * 82944 :=
  Certificates.certificate7771 t ht

theorem burnsideF48t_u52_cand {i j k : ℕ} (hi : i < 4) (hj : j < 2) (hk : k < 9) :
    (∃ t ∈ burnsideF48t_u52Cands, t.1 = i ∧ t.2.1 = j ∧ t.2.2.1 = k ∧
      (t.2.2.2 = 165 → burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_u52σ l)
        (burnsideF48s_eCandRel 4 (burnsideF48t_u52XW.getD i []) (burnsideF48t_u52YW.getD j [])
          (burnsideF48t_u52KW.getD k [])) = 1)) ∨
    ¬ (burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_u52σ l) (burnsideF48t_u52XW.getD i []) *
        burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_u52σ l) (burnsideF48t_u52YW.getD j []) *
        burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_u52σ l) (burnsideF48t_u52KW.getD k []) =
      burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_u52σ l) (burnsideF48t_u52KW.getD k []) *
        (burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_u52σ l) (burnsideF48t_u52XW.getD i []) *
          burnsideF48s_ev (fun l : Fin 4 => burnsideF48t_u52σ l) (burnsideF48t_u52YW.getD j []))) := by
  have h := burnsideF48t_u52_mem.2.2.2.1
  simp only [burnsideF48t_u52CandOK] at h
  have h1 := allBelowN_spec (allBelowN_spec (allBelowN_spec h hi) hj) hk
  have hrec := burnsideF48t_u52_recL
  split at h1
  · rename_i t ht
    left
    refine ⟨t, List.mem_of_find?_eq_some ht, ?_⟩
    have hp := List.find?_some ht
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨h1', h2'⟩, h3'⟩ := hp
    refine ⟨h1', h2', h3', fun h165 => ?_⟩
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, h165, not_true_eq_false, false_or] at h1
    exact burnsideF48t_ev_eq_one_of hrec h1
  · right
    intro he
    simp only [Bool.not_eq_true'] at h1
    have hu := burnsideF48t_prep_evA hrec (burnsideF48t_u52XW.getD i [])
    have hv := burnsideF48t_prep_evA hrec (burnsideF48t_u52YW.getD j [])
    have hc := burnsideF48t_prep_evA hrec (burnsideF48t_u52KW.getD k [])
    have := (peq_iff (prep_pcomp (prep_pcomp hu hv) hc) (prep_pcomp hc (prep_pcomp hu hv))).2 he
    rw [this] at h1
    exact absurd h1 (by decide)

theorem burnsideF48t_u52_facts : burnsideF48t_Facts burnsideF48t_u52L burnsideF48t_u52P1
    burnsideF48t_u52P2 burnsideF48t_g23S1 burnsideF48t_g23S2 burnsideF48t_u52K burnsideF48t_u52R1
    burnsideF48t_u52R2 burnsideF48t_u52XW burnsideF48t_u52YW burnsideF48t_u52KW 4 where
  hP1 := rfl
  hP2 := rfl
  rel1 := fun r hr => ⟨by
      have h : ∀ r ∈ burnsideF48t_u52R1, ∀ l ∈ r, l.1 ≠ 3 := by decide
      exact h r hr,
    Subtype.ext ((burnsideF48t_u52_coe_ev r).trans (burnsideF48t_u52_rels r
      (List.mem_append_left _ hr)))⟩
  rel2 := fun r hr => ⟨by
      have h : ∀ r ∈ burnsideF48t_u52R2, ∀ l ∈ r, l.1 ≠ 2 := by decide
      exact h r hr,
    Subtype.ext ((burnsideF48t_u52_coe_ev r).trans (burnsideF48t_u52_rels r
      (List.mem_append_right _ hr)))⟩
  sup := by
    obtain ⟨-, -, -, hmax⟩ := burnsideF48t_u52_P1_max
    refine hmax _ (lt_of_le_of_ne le_sup_left fun h => burnsideF48t_u52_L3_not_mem ?_) le_top
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨3, show (3 : Fin 4) ≠ 2 by decide, rfl⟩)
  K_le := fun z hz => by
    have h1 : (z : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52K' := hz
    have h2 := burnsideF48t_u52_K'_le_B' h1
    rw [burnsideF48t_u52_B'_eq] at h2
    exact ⟨(burnsideF48t_u52_mem_P1 z).2 h2.1, (burnsideF48t_u52_mem_P2 z).2 h2.2⟩
  KW_let := by
    have h : ∀ w ∈ burnsideF48t_u52KW, ∀ l ∈ w, l.1 ≠ 3 := by decide
    exact h
  KW_cov := fun c hc => by
    obtain ⟨m, hm, he⟩ := burnsideF48t_u52_K'_cases
      (show (c : Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52K' from hc)
    refine ⟨burnsideF48t_u52KW.getD m [], ?_, Subtype.ext ?_⟩
    · rw [List.getD_eq_getElem _ _ (by rw [burnsideF48t_u52_KW_length]; exact hm)]
      exact List.getElem_mem _
    · rw [burnsideF48t_u52_coe_ev, he]
      rfl
  XW_let := by
    have h : ∀ w ∈ burnsideF48t_u52XW, ∀ l ∈ w, l.1 ≠ 3 := by decide
    exact h
  YW_let := by
    have h : ∀ w ∈ burnsideF48t_u52YW, ∀ l ∈ w, l.1 ≠ 2 := by decide
    exact h
  xred := fun x hx hx2 hxK hxx => by
    have hK : ∀ k ∈ burnsideF48t_u52K',
        (x : Equiv.Perm (Fin 462)) * k * (x : Equiv.Perm (Fin 462))⁻¹ ∈ burnsideF48t_u52K' := by
      intro k hk
      have := hxK ⟨k, burnsideF48t_u52_K'_le_X hk⟩ hk
      rw [burnsideF48t_u52K, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv] at this
      exact this
    have hxx' : (x : Equiv.Perm (Fin 462)) * x ∈ burnsideF48t_u52K' := by
      have := hxx
      rw [burnsideF48t_u52K, Subgroup.mem_subgroupOf, Subgroup.coe_mul] at this
      exact this
    obtain ⟨w, hw, hk⟩ := burnsideF48t_u52_xred ((burnsideF48t_u52_mem_P1 x).1 hx)
      (fun h => hx2 ((burnsideF48t_u52_mem_P2 x).2 h)) hK hxx'
    refine ⟨w, hw, ?_⟩
    show (((burnsideF48s_ev burnsideF48t_u52L w)⁻¹ * x : ↥burnsideF48t_u52X) :
      Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52K'
    rw [Subgroup.coe_mul, Subgroup.coe_inv, burnsideF48t_u52_coe_ev]
    exact hk
  yred := fun y hy hy1 hyK hyy => by
    have hK : ∀ k ∈ burnsideF48t_u52K',
        (y : Equiv.Perm (Fin 462)) * k * (y : Equiv.Perm (Fin 462))⁻¹ ∈ burnsideF48t_u52K' := by
      intro k hk
      have := hyK ⟨k, burnsideF48t_u52_K'_le_X hk⟩ hk
      rw [burnsideF48t_u52K, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv] at this
      exact this
    have hyy' : (y : Equiv.Perm (Fin 462)) * y ∈ burnsideF48t_u52K' := by
      have := hyy
      rw [burnsideF48t_u52K, Subgroup.mem_subgroupOf, Subgroup.coe_mul] at this
      exact this
    obtain ⟨w, hw, hk⟩ := burnsideF48t_u52_yred ((burnsideF48t_u52_mem_P2 y).1 hy)
      (fun h => hy1 ((burnsideF48t_u52_mem_P1 y).2 h)) hK hyy'
    refine ⟨w, hw, ?_⟩
    show (((burnsideF48s_ev burnsideF48t_u52L w)⁻¹ * y : ↥burnsideF48t_u52X) :
      Equiv.Perm (Fin 462)) ∈ burnsideF48t_u52K'
    rw [Subgroup.coe_mul, Subgroup.coe_inv, burnsideF48t_u52_coe_ev]
    exact hk
  cand := fun u hu v hv c hc hcomm => by
    obtain ⟨i, hi, hiu⟩ := List.mem_iff_getElem.1 hu
    obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.1 hv
    obtain ⟨k, hk, hkc⟩ := List.mem_iff_getElem.1 hc
    have hi4 : i < 4 := by simpa [burnsideF48t_u52XW] using hi
    have hj2 : j < 2 := by simpa [burnsideF48t_u52YW] using hj
    have hk9 : k < 9 := by simpa [burnsideF48t_u52_KW_length] using hk
    have eu : u = burnsideF48t_u52XW.getD i [] := by rw [List.getD_eq_getElem _ _ hi, hiu]
    have ev : v = burnsideF48t_u52YW.getD j [] := by rw [List.getD_eq_getElem _ _ hj, hjv]
    have ec : c = burnsideF48t_u52KW.getD k [] := by rw [List.getD_eq_getElem _ _ hk, hkc]
    subst eu ev ec
    have hcomm' := congrArg Subtype.val hcomm
    simp only [Subgroup.coe_mul, burnsideF48t_u52_coe_ev] at hcomm'
    rcases burnsideF48t_u52_cand hi4 hj2 hk9 with ⟨t, ht, rfl, rfl, rfl, hrel⟩ | hne
    · obtain ⟨hfin, hcard⟩ := burnsideF48t_u52_tc ht
      have hn : t.2.2.2 = 1 ∨ t.2.2.2 = 165 := by
        have : ∀ s ∈ burnsideF48t_u52Cands, s.2.2.2 = 1 ∨ s.2.2.2 = 165 := by decide
        exact this t ht
      refine ⟨hfin, ?_⟩
      rcases hn with h1 | h165
      · left
        rw [h1, one_mul] at hcard
        rw [burnsideF48t_u52_card_X]
        exact lt_of_le_of_lt hcard (by norm_num)
      · right
        refine ⟨by rw [burnsideF48t_u52_card_X]; rw [h165] at hcard; exact hcard, ?_⟩
        apply Subtype.ext
        rw [burnsideF48t_u52_coe_ev]
        exact hrel h165
    · exact absurd hcomm' hne

theorem burnsideF48t_u52_hconj : ∀ K'' : Subgroup ↥burnsideF48t_u52X,
    K'' ≤ burnsideF48t_u52P1 ⊓ burnsideF48t_u52P2 → Nat.card ↥K'' = Nat.card ↥burnsideF48t_u52K →
    ∃ t ∈ burnsideF48t_u52P1 ⊓ burnsideF48t_u52P2, ∀ z, z ∈ K'' ↔ t * z * t⁻¹ ∈ burnsideF48t_u52K := by
  intro K'' hle hcard
  have hKc : Nat.card ↥burnsideF48t_u52K = 9 := burnsideF48t_u52_card_K
  have hsyl : ∀ H : Subgroup ↥burnsideF48t_u52X, H ≤ burnsideF48t_u52P1 ⊓ burnsideF48t_u52P2 →
      Nat.card ↥H = 9 → ChF.IsSylowOf 3 H (burnsideF48t_u52P1 ⊓ burnsideF48t_u52P2) := by
    intro H hH hc
    refine ⟨hH, IsPGroup.of_card (n := 2) (by rw [hc]; norm_num), ?_⟩
    have h := Subgroup.relIndex_mul_card (H := H) (K := burnsideF48t_u52P1 ⊓ burnsideF48t_u52P2)
    rw [inf_eq_left.2 hH, hc, burnsideF48t_u52_card_B] at h
    have h2 : H.relIndex (burnsideF48t_u52P1 ⊓ burnsideF48t_u52P2) = 1024 := by omega
    rw [h2]
    decide
  obtain ⟨g, hg⟩ := burnsideF48_sylow_conj (hsyl _ burnsideF48t_u52_facts.K_le hKc)
    (hsyl K'' hle (hcard.trans hKc))
  refine ⟨g, g.2, fun z => ⟨fun hz => ?_, fun hz => ?_⟩⟩
  · rw [hg]
    exact ⟨z, hz, by simp [MulAut.conj_apply]⟩
  · rw [hg] at hz
    obtain ⟨z', hz', he⟩ := hz
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj, mul_right_inj] at he
    rw [← he]
    exact hz'

end Engine

end CFSG.ASVolI
