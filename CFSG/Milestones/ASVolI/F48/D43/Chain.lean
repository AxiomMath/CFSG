module

public import CFSG.Perm.ChainByOrder
public import CFSG.Certificates.Kernel.RouteP.TabComplete
public import Certificates.Certificate7802

public section

namespace CFSG.ASVolI

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.TwistedD4 CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm
  CFSG.Perm.Native

attribute [local irreducible] burnsideF48d_KeysHex burnsideF48d_TabsHex burnsideF48d_GensHex
  burnsideF48d_PhiHex burnsideF48d_limbs burnsideF48d_colTab

instance burnsideF48d_finite_X : Finite ↥burnsideF48d_X := Subgroup.instFiniteSubtypeMem _

section Chains

abbrev burnsideF48d_lv0 : Fin 26572 × Finset (Fin 17) × ℕ := (0, ∅, 0)

@[expose] noncomputable def burnsideF48d_lvH (C : List (Fin 26572 × Finset (Fin 17) × ℕ))
    (i : ℕ) : Subgroup ↥burnsideF48d_X :=
  Subgroup.closure (burnsideF48d_L '' ↑(C.getD i burnsideF48d_lv0).2.1)

variable {C : List (Fin 26572 × Finset (Fin 17) × ℕ)}

theorem burnsideF48d_getD_lv {i : ℕ} (hi : i < C.length) : C.getD i burnsideF48d_lv0 = C[i] := by
  simp [hi]

theorem burnsideF48d_lvH_length : burnsideF48d_lvH C C.length = ⊥ := by
  simp [burnsideF48d_lvH, List.getD_eq_default]

@[expose] def burnsideF48d_ChainNested (C : List (Fin 26572 × Finset (Fin 17) × ℕ)) : Prop :=
  ∀ i < C.length - 1, (C.getD (i + 1) burnsideF48d_lv0).2.1 ⊆ (C.getD i burnsideF48d_lv0).2.1

theorem burnsideF48d_lvH_le (hC : burnsideF48d_ChainBound C) (hsub : burnsideF48d_ChainNested C)
    {i : ℕ} (hi : i < C.length) :
    burnsideF48d_lvH C (i + 1) ≤
      burnsideF48d_lvH C i ⊓ MulAction.stabilizer ↥burnsideF48d_X C[i].1 := by
  by_cases h : i + 1 < C.length
  · rw [burnsideF48d_lvH, Subgroup.closure_le]
    rintro _ ⟨j, hj, rfl⟩
    refine ⟨Subgroup.subset_closure ⟨j, hsub i (by omega) hj, rfl⟩, ?_⟩
    change burnsideF48d_L j ∈ MulAction.stabilizer ↥burnsideF48d_X C[i].1
    rw [MulAction.mem_stabilizer_iff]
    have hj' : j ∈ C[i + 1].2.1 := by
      have := hj
      rwa [Finset.mem_coe, burnsideF48d_getD_lv h] at this
    exact (hC (i + 1) h).1 j hj' i (Nat.lt_succ_self i)
  · rw [show i + 1 = C.length by omega, burnsideF48d_lvH_length]
    exact bot_le

theorem burnsideF48d_lvH_card (hC : burnsideF48d_ChainBound C) (hsub : burnsideF48d_ChainNested C)
    {i : ℕ} (hi : i < C.length) :
    C[i].2.2 * Nat.card (burnsideF48d_lvH C (i + 1)) ≤ Nat.card (burnsideF48d_lvH C i) := by
  rw [card_eq_orbit_mul_inf (burnsideF48d_lvH C i) C[i].1, Nat.card_coe_set_eq]
  refine Nat.mul_le_mul ?_ (Subgroup.card_le_of_le (burnsideF48d_lvH_le hC hsub hi))
  have e : burnsideF48d_lvH C i = Subgroup.closure (burnsideF48d_L '' ↑C[i].2.1) := by
    rw [burnsideF48d_lvH, burnsideF48d_getD_lv hi]
  rw [e]
  exact (hC i hi).2

theorem burnsideF48d_lvH_prod_le (hC : burnsideF48d_ChainBound C)
    (hsub : burnsideF48d_ChainNested C) : ∀ j ≤ C.length,
    ∏ l ∈ Finset.Ico j C.length, (C.getD l burnsideF48d_lv0).2.2 ≤
      Nat.card (burnsideF48d_lvH C j) := by
  suffices h : ∀ d j, j + d = C.length → ∏ l ∈ Finset.Ico j C.length,
      (C.getD l burnsideF48d_lv0).2.2 ≤ Nat.card (burnsideF48d_lvH C j) from
    fun j hj => h (C.length - j) j (by omega)
  intro d
  induction d with
  | zero =>
    intro j hj
    rw [show j = C.length by omega, Finset.Ico_self, Finset.prod_empty]
    exact Nat.card_pos
  | succ d ih =>
    intro j hj
    have hjm : j < C.length := by omega
    rw [Finset.prod_eq_prod_Ico_succ_bot hjm, burnsideF48d_getD_lv hjm]
    exact (Nat.mul_le_mul_left _ (ih (j + 1) (by omega))).trans
      (burnsideF48d_lvH_card hC hsub hjm)

theorem burnsideF48d_lvH_tight (hC : burnsideF48d_ChainBound C) (hsub : burnsideF48d_ChainNested C)
    (hN : Nat.card ↥burnsideF48d_X ≤
      ∏ l ∈ Finset.range C.length, (C.getD l burnsideF48d_lv0).2.2) :
    (∀ j ≤ C.length, Nat.card (burnsideF48d_lvH C j) =
      ∏ l ∈ Finset.Ico j C.length, (C.getD l burnsideF48d_lv0).2.2) ∧
    ∀ i (hi : i < C.length), burnsideF48d_lvH C (i + 1) =
      burnsideF48d_lvH C i ⊓ MulAction.stabilizer ↥burnsideF48d_X C[i].1 := by
  set s : ℕ → ℕ := fun l => (C.getD l burnsideF48d_lv0).2.2 with hs
  set a : ℕ → ℕ := fun j => Nat.card (burnsideF48d_lvH C j) with ha
  have hstep : ∀ i < C.length, s i * a (i + 1) ≤ a i := fun i hi => by
    have := burnsideF48d_lvH_card hC hsub hi
    rwa [← burnsideF48d_getD_lv hi] at this
  have hN0 : ∏ l ∈ Finset.range C.length, s l ≠ 0 :=
    Nat.pos_iff_ne_zero.1 (lt_of_lt_of_le Nat.card_pos hN)
  have hspos : ∀ l < C.length, 0 < s l := fun l hl =>
    Nat.pos_iff_ne_zero.2 (Finset.prod_ne_zero_iff.1 hN0 l (Finset.mem_range.2 hl))
  have hup : ∀ j ≤ C.length, a j * ∏ l ∈ Finset.range j, s l ≤ a 0 := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      rw [Finset.prod_range_succ]
      calc a (j + 1) * ((∏ l ∈ Finset.range j, s l) * s j)
          = (s j * a (j + 1)) * ∏ l ∈ Finset.range j, s l := by ring
        _ ≤ a j * ∏ l ∈ Finset.range j, s l := Nat.mul_le_mul_right _ (hstep j (by omega))
        _ ≤ a 0 := ih (by omega)
  have ha0 : a 0 ≤ ∏ l ∈ Finset.range C.length, s l :=
    (Subgroup.card_le_card_group _).trans hN
  have heq : ∀ j ≤ C.length, a j = ∏ l ∈ Finset.Ico j C.length, s l := by
    intro j hj
    refine le_antisymm ?_ (burnsideF48d_lvH_prod_le hC hsub j hj)
    have hP : 0 < ∏ l ∈ Finset.range j, s l :=
      Finset.prod_pos fun l hl => hspos l (by simp at hl; omega)
    rw [← Finset.prod_range_mul_prod_Ico s hj] at ha0
    have := (hup j hj).trans ha0
    rw [mul_comm (a j)] at this
    exact Nat.le_of_mul_le_mul_left this hP
  refine ⟨heq, fun i hi => ?_⟩
  have hle := burnsideF48d_lvH_le hC hsub hi
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hc := card_eq_orbit_mul_inf (burnsideF48d_lvH C i) C[i].1
  rw [Nat.card_coe_set_eq] at hc
  have ho : s i ≤ (MulAction.orbit ↥(burnsideF48d_lvH C i) C[i].1).ncard := by
    have h0 := (hC i hi).2
    have e : burnsideF48d_lvH C i = Subgroup.closure (burnsideF48d_L '' ↑C[i].2.1) := by
      rw [burnsideF48d_lvH, burnsideF48d_getD_lv hi]
    rw [e]
    change (C.getD i burnsideF48d_lv0).2.2 ≤ _
    rw [burnsideF48d_getD_lv hi]
    exact h0
  have hai : a i = s i * a (i + 1) := by
    rw [heq i hi.le, heq (i + 1) hi, Finset.prod_eq_prod_Ico_succ_bot hi]
  have h1 : s i * Nat.card ↥(burnsideF48d_lvH C i ⊓
      MulAction.stabilizer ↥burnsideF48d_X C[i].1) ≤ s i * a (i + 1) := by
    rw [← hai]
    exact (Nat.mul_le_mul_right _ ho).trans hc.ge
  exact Nat.le_of_mul_le_mul_left h1 (hspos i hi)

end Chains

theorem burnsideF48d_genTabs_even {k : ℕ} (hk : k < 8) :
    (burnsideF48d_genTabs ())[2 * k]! = burnsideF48d_toT (burnsideF48d_gen k) := by
  simp only [burnsideF48d_genTabs]
  rw [getElem!_pos _ (2 * k) (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn]
  simp only [show 2 * k % 2 = 0 by omega, if_true, show 2 * k / 2 = k by omega]
  rw [getElem!_pos _ k (by rw [Array.size_map, Array.size_range]; exact hk), Array.getElem_map,
    Array.getElem_range]

theorem burnsideF48d_genTabs_odd {k : ℕ} (hk : k < 8) :
    (burnsideF48d_genTabs ())[2 * k + 1]! = invT 26572 (burnsideF48d_toT (burnsideF48d_gen k)) := by
  simp only [burnsideF48d_genTabs]
  rw [getElem!_pos _ (2 * k + 1) (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn]
  simp only [show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega]
  rw [if_neg (by omega), getElem!_pos _ k (by rw [Array.size_map, Array.size_range]; exact hk),
    Array.getElem_map, Array.getElem_range]

theorem burnsideF48d_letters_even {j : ℕ} (hj : j < 17) :
    (burnsideF48d_letters ())[2 * j]! = wordT 26572 (burnsideF48d_letterT (burnsideF48d_genTabs ()))
      (burnsideF48d_intWord (burnsideF48d_LW.getD j [])) := by
  have hs : j < burnsideF48d_LW.length := lt_of_lt_of_eq hj rfl
  simp only [burnsideF48d_letters]
  rw [getElem!_pos _ (2 * j) (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn]
  simp only [show 2 * j % 2 = 0 by omega, if_true, show 2 * j / 2 = j by omega]
  rw [getElem!_pos _ j (by rw [Array.size_map, List.size_toArray]; exact hs), Array.getElem_map,
    List.getElem_toArray, List.getD_eq_getElem]

theorem burnsideF48d_letters_odd {j : ℕ} (hj : j < 17) :
    (burnsideF48d_letters ())[2 * j + 1]! = invT 26572 (burnsideF48d_letters ())[2 * j]! := by
  have hs : j < burnsideF48d_LW.length := lt_of_lt_of_eq hj rfl
  rw [burnsideF48d_letters_even hj]
  simp only [burnsideF48d_letters]
  rw [getElem!_pos _ (2 * j + 1) (by rw [Array.size_ofFn]; omega), Array.getElem_ofFn]
  simp only [show (2 * j + 1) % 2 = 1 by omega, show (2 * j + 1) / 2 = j by omega]
  rw [if_neg (by omega), getElem!_pos _ j (by rw [Array.size_map, List.size_toArray]; exact hs),
    Array.getElem_map, List.getElem_toArray, List.getD_eq_getElem]

section Reps

@[expose] noncomputable def burnsideF48d_γX (k : Fin 8) : ↥burnsideF48d_X :=
  ⟨burnsideF48d_γ k, burnsideF48d_γ_mem k⟩

theorem burnsideF48d_rep_X_iff {T : Table} {z : ↥burnsideF48d_X} :
    CFSG.Sporadic.Th.Rep 26572 T z ↔ CFSG.Sporadic.Th.Rep 26572 T (z : Equiv.Perm (Fin 26572)) := by
  unfold CFSG.Sporadic.Th.Rep
  refine forall₂_congr fun i hi => ?_
  rw [idx_of_lt _ hi, idx_of_lt _ hi]
  rfl

abbrev burnsideF48d_F : Type := GaloisField 3 3

instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

theorem burnsideF48d_card_F : Nat.card burnsideF48d_F = 27 := by
  rw [GaloisField.card 3 3 (by norm_num)]
  norm_num

noncomputable abbrev burnsideF48d_σF : burnsideF48d_F →+* burnsideF48d_F := frobenius burnsideF48d_F 3

theorem burnsideF48d_σF_apply (c : burnsideF48d_F) : burnsideF48d_σF c = c ^ 3 := frobenius_def 3 c

noncomputable def burnsideF48d_ωF : burnsideF48d_F := by
  haveI : Fintype burnsideF48d_F := Fintype.ofFinite _
  exact Classical.choose (burnsideF48d_exists_omega (K := burnsideF48d_F)
    (by rw [← Nat.card_eq_fintype_card, burnsideF48d_card_F]))

theorem burnsideF48d_ωF_spec : burnsideF48d_ωF ^ 3 = burnsideF48d_ωF + 1 := by
  haveI : Fintype burnsideF48d_F := Fintype.ofFinite _
  exact Classical.choose_spec (burnsideF48d_exists_omega (K := burnsideF48d_F)
    (by rw [← Nat.card_eq_fintype_card, burnsideF48d_card_F]))

theorem burnsideF48d_gen_rep {k : ℕ} (hk : k < 8) :
    CFSG.Sporadic.Th.Rep 26572 (burnsideF48d_toT (burnsideF48d_gen k)) (burnsideF48d_γ k) := by
  have h := burnsideF48d_rep_ρ_g burnsideF48d_σF burnsideF48d_ωF burnsideF48d_card_F
    burnsideF48d_σF_apply burnsideF48d_ωF_spec ⟨k, hk⟩
  rw [burnsideF48d_ρ_g] at h
  exact h

theorem burnsideF48d_card_X_le' : Nat.card ↥burnsideF48d_X ≤ 20560831566912 :=
  burnsideF48d_card_X_le burnsideF48d_σF burnsideF48d_ωF burnsideF48d_card_F burnsideF48d_σF_apply
    burnsideF48d_ωF_spec

theorem burnsideF48d_gen_rep_inv {k : ℕ} (hk : k < 8) :
    CFSG.Sporadic.Th.Rep 26572 (burnsideF48d_genTabs ())[2 * k + 1]! (burnsideF48d_γ k)⁻¹ := by
  rw [burnsideF48d_genTabs_odd hk]
  exact CFSG.KS.RouteP.rep_invT (by norm_num) (burnsideF48d_gen_rep hk)

@[expose] noncomputable def burnsideF48d_gensG (l : ℤ) : ↥burnsideF48d_X :=
  if 0 < l then (if h : l.toNat - 1 < 8 then burnsideF48d_γX ⟨l.toNat - 1, h⟩ else 1)
  else (if h : (-l).toNat - 1 < 8 then (burnsideF48d_γX ⟨(-l).toNat - 1, h⟩)⁻¹ else 1)

theorem burnsideF48d_gensG_pos (k : Fin 8) :
    burnsideF48d_gensG ((k.val + 1 : ℕ) : ℤ) = burnsideF48d_γX k := by
  unfold burnsideF48d_gensG
  have h1 : (0 : ℤ) < ((k.val + 1 : ℕ) : ℤ) := by omega
  have h2 : (((k.val + 1 : ℕ) : ℤ)).toNat - 1 = k.val := by omega
  rw [if_pos h1, dif_pos (h2 ▸ k.2)]
  exact congrArg _ (Fin.ext h2)

theorem burnsideF48d_gensG_neg (k : Fin 8) :
    burnsideF48d_gensG (-((k.val + 1 : ℕ) : ℤ)) = (burnsideF48d_γX k)⁻¹ := by
  unfold burnsideF48d_gensG
  have h1 : ¬ (0 : ℤ) < -((k.val + 1 : ℕ) : ℤ) := by omega
  have h2 : (-(-((k.val + 1 : ℕ) : ℤ))).toNat - 1 = k.val := by omega
  rw [if_neg h1, dif_pos (h2 ▸ k.2)]
  exact congrArg (fun z => z⁻¹) (congrArg _ (Fin.ext h2))

theorem burnsideF48d_letterT_pos (GT : Array Table) (k : Fin 8) :
    burnsideF48d_letterT GT ((k.val + 1 : ℕ) : ℤ) = GT[2 * k.val]! := by
  unfold burnsideF48d_letterT
  have h1 : (0 : ℤ) < ((k.val + 1 : ℕ) : ℤ) := by omega
  have h2 : (((k.val + 1 : ℕ) : ℤ)).toNat - 1 = k.val := by omega
  rw [if_pos h1, h2]

theorem burnsideF48d_letterT_neg (GT : Array Table) (k : Fin 8) :
    burnsideF48d_letterT GT (-((k.val + 1 : ℕ) : ℤ)) = GT[2 * k.val + 1]! := by
  unfold burnsideF48d_letterT
  have h1 : ¬ (0 : ℤ) < -((k.val + 1 : ℕ) : ℤ) := by omega
  have h2 : (-(-((k.val + 1 : ℕ) : ℤ))).toNat - 1 = k.val := by omega
  rw [if_neg h1, h2]

theorem burnsideF48d_rep_letterT (w : List (Fin 8 × Bool)) :
    ∀ l ∈ burnsideF48d_intWord w, CFSG.Sporadic.Th.Rep 26572
      (burnsideF48d_letterT (burnsideF48d_genTabs ()) l) (burnsideF48d_gensG l) := by
  intro l hl
  unfold burnsideF48d_intWord at hl
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hl
  obtain ⟨k, b⟩ := a
  rw [burnsideF48d_rep_X_iff]
  cases b
  · simp only [Bool.false_eq_true, if_false]
    rw [burnsideF48d_letterT_neg, burnsideF48d_gensG_neg, Subgroup.coe_inv]
    exact burnsideF48d_gen_rep_inv k.2
  · simp only [if_true]
    rw [burnsideF48d_letterT_pos, burnsideF48d_gensG_pos, burnsideF48d_genTabs_even k.2]
    exact burnsideF48d_gen_rep k.2

theorem burnsideF48d_wordG_intWord (w : List (Fin 8 × Bool)) :
    wordG burnsideF48d_gensG (burnsideF48d_intWord w) =
      burnsideF48s_ev (fun k : Fin 8 => burnsideF48d_γX k) w := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    obtain ⟨k, b⟩ := a
    rw [burnsideF48s_ev_cons]
    unfold wordG at ih ⊢
    rw [burnsideF48d_intWord, List.map_cons, List.map_cons, List.prod_cons]
    rw [burnsideF48d_intWord] at ih
    rw [ih]
    congr 1
    cases b
    · simp only [Bool.false_eq_true, if_false, cond_false]
      exact burnsideF48d_gensG_neg k
    · simp only [if_true, cond_true]
      exact burnsideF48d_gensG_pos k

theorem burnsideF48d_ev_γX (j : Fin 17) :
    burnsideF48s_ev (fun k : Fin 8 => burnsideF48d_γX k) (burnsideF48d_LW.getD j []) =
      burnsideF48d_L j := by
  apply Subtype.ext
  show burnsideF48d_X.subtype _ = _
  rw [← burnsideF48s_ev_map]
  rfl

theorem burnsideF48d_letter_rep {j : ℕ} (hj : j < 17) :
    CFSG.Sporadic.Th.Rep 26572 (burnsideF48d_letters ())[2 * j]! (burnsideF48d_L ⟨j, hj⟩) ∧
      CFSG.Sporadic.Th.Rep 26572 (burnsideF48d_letters ())[2 * j + 1]! (burnsideF48d_L ⟨j, hj⟩)⁻¹ := by
  have h1 : CFSG.Sporadic.Th.Rep 26572 (burnsideF48d_letters ())[2 * j]! (burnsideF48d_L ⟨j, hj⟩) := by
    rw [burnsideF48d_letters_even hj, ← burnsideF48d_ev_γX ⟨j, hj⟩, ← burnsideF48d_wordG_intWord]
    exact CFSG.Sporadic.Th.Rep.wordT (by norm_num) _ (burnsideF48d_rep_letterT _)
  refine ⟨h1, ?_⟩
  rw [burnsideF48d_letters_odd hj]
  exact CFSG.KS.RouteP.rep_invT (by norm_num) h1

end Reps

section ChainX

theorem burnsideF48d_chain_cert :
    burnsideF48d_ChainBound burnsideF48d_chainXL ∧ burnsideF48d_ChainBound burnsideF48d_chainBL :=
  Certificates.certificate7802

theorem burnsideF48d_nestedX : burnsideF48d_ChainNested burnsideF48d_chainXL := by
  unfold burnsideF48d_ChainNested
  decide +kernel

theorem burnsideF48d_nestedB : burnsideF48d_ChainNested burnsideF48d_chainBL := by
  unfold burnsideF48d_ChainNested
  decide +kernel

theorem burnsideF48d_tightX :
    (∀ j ≤ 8, Nat.card (burnsideF48d_lvH burnsideF48d_chainXL j) =
      ∏ l ∈ Finset.Ico j 8, (burnsideF48d_chainXL.getD l burnsideF48d_lv0).2.2) ∧
    ∀ i (hi : i < burnsideF48d_chainXL.length), burnsideF48d_lvH burnsideF48d_chainXL (i + 1) =
      burnsideF48d_lvH burnsideF48d_chainXL i ⊓
        MulAction.stabilizer ↥burnsideF48d_X burnsideF48d_chainXL[i].1 :=
  burnsideF48d_lvH_tight burnsideF48d_chain_cert.1 burnsideF48d_nestedX
    (burnsideF48d_card_X_le'.trans (by decide +kernel))

theorem burnsideF48d_card_X : Nat.card ↥burnsideF48d_X = 20560831566912 := by
  refine le_antisymm burnsideF48d_card_X_le' ?_
  have h := burnsideF48d_lvH_prod_le burnsideF48d_chain_cert.1 burnsideF48d_nestedX 0
    (Nat.zero_le _)
  have e : ∏ l ∈ Finset.Ico 0 burnsideF48d_chainXL.length,
      (burnsideF48d_chainXL.getD l burnsideF48d_lv0).2.2 = 20560831566912 := by
    decide +kernel
  rw [e] at h
  exact h.trans (Subgroup.card_le_card_group _)

theorem burnsideF48d_lvX_zero : burnsideF48d_lvH burnsideF48d_chainXL 0 = ⊤ := by
  refine Subgroup.eq_top_of_card_eq _ ?_
  rw [burnsideF48d_tightX.1 0 (by norm_num), burnsideF48d_card_X]
  decide +kernel

theorem burnsideF48d_mem_lvX : ∀ i ≤ 8, ∀ g : ↥burnsideF48d_X,
    g ∈ burnsideF48d_lvH burnsideF48d_chainXL i ↔
      ∀ t < i, (g : Equiv.Perm (Fin 26572)) (burnsideF48d_chainXL.getD t burnsideF48d_lv0).1 =
        (burnsideF48d_chainXL.getD t burnsideF48d_lv0).1 := by
  intro i
  induction i with
  | zero =>
    intro _ g
    rw [burnsideF48d_lvX_zero]
    simp
  | succ i ih =>
    intro hi g
    have hi8 : i < burnsideF48d_chainXL.length := by
      change i < 8
      omega
    rw [burnsideF48d_tightX.2 i hi8, Subgroup.mem_inf, ih (by omega), MulAction.mem_stabilizer_iff,
      ← burnsideF48d_getD_lv hi8]
    constructor
    · rintro ⟨h, hg⟩ t ht
      rcases Nat.lt_succ_iff_lt_or_eq.1 ht with ht | rfl
      · exact h t ht
      · exact hg
    · intro h
      exact ⟨fun t ht => h t (by omega), h i (by omega)⟩

theorem burnsideF48d_mem_P1 (z : ↥burnsideF48d_X) :
    z ∈ burnsideF48d_P1 ↔ (z : Equiv.Perm (Fin 26572)) 0 = 0 := by
  have hS : ∀ j : Fin 17, j ∈ (burnsideF48d_chainXL.getD 1 burnsideF48d_lv0).2.1 ↔ j ≠ 1 := by
    decide +kernel
  have e : burnsideF48d_lvH burnsideF48d_chainXL 1 = burnsideF48d_P1 := by
    unfold burnsideF48d_lvH burnsideF48d_P1
    congr 2
    ext j
    exact hS j
  rw [← e, burnsideF48d_mem_lvX 1 (by norm_num)]
  constructor
  · intro h
    exact h 0 (by norm_num)
  · intro h t ht
    obtain rfl : t = 0 := by omega
    exact h

theorem burnsideF48d_lvX_six : burnsideF48d_lvH burnsideF48d_chainXL 6 = burnsideF48d_T := by
  have hS : ∀ j : Fin 17, j ∈ (burnsideF48d_chainXL.getD 6 burnsideF48d_lv0).2.1 ↔
      2 ≤ j.val ∧ j.val ≤ 4 := by
    decide +kernel
  unfold burnsideF48d_lvH burnsideF48d_T
  congr 2
  ext j
  exact hS j

theorem burnsideF48d_card_lvT : Nat.card ↥burnsideF48d_T = 52 := by
  rw [← burnsideF48d_lvX_six, burnsideF48d_tightX.1 6 (by norm_num)]
  decide +kernel

theorem burnsideF48d_mem_T (z : ↥burnsideF48d_X) :
    z ∈ burnsideF48d_T ↔ ∀ p ∈ burnsideF48d_aptF, (z : Equiv.Perm (Fin 26572)) p = p := by
  rw [← burnsideF48d_lvX_six, burnsideF48d_mem_lvX 6 (by norm_num)]
  have h1 : ∀ t < 6, (burnsideF48d_chainXL.getD t burnsideF48d_lv0).1 ∈ burnsideF48d_aptF := by
    decide +kernel
  constructor
  · intro h p hp
    simp only [burnsideF48d_aptF, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h 0 (by norm_num), h 2 (by norm_num), h 3 (by norm_num), h 1 (by norm_num),
      h 4 (by norm_num), h 5 (by norm_num)]
  · intro h t ht
    exact h _ (h1 t ht)

theorem burnsideF48d_base (z : ↥burnsideF48d_X)
    (h : ∀ p ∈ burnsideF48d_baseF, (z : Equiv.Perm (Fin 26572)) p = p) : z = 1 := by
  have h1 : ∀ t < 8, (burnsideF48d_chainXL.getD t burnsideF48d_lv0).1 ∈ burnsideF48d_baseF := by
    decide +kernel
  have hmem := (burnsideF48d_mem_lvX 8 le_rfl z).2 fun t ht => h _ (h1 t ht)
  rw [show (8 : ℕ) = burnsideF48d_chainXL.length from rfl, burnsideF48d_lvH_length] at hmem
  exact hmem

theorem burnsideF48d_closure_L : Subgroup.closure (Set.range burnsideF48d_L) = ⊤ := by
  rw [← burnsideF48d_lvX_zero, burnsideF48d_lvH]
  simp

theorem burnsideF48d_trans (p : Fin 26572) :
    ∃ z : ↥burnsideF48d_X, (z : Equiv.Perm (Fin 26572)) 0 = p := by
  have h := (burnsideF48d_chain_cert.1 0 (by decide)).2
  have huniv : MulAction.orbit ↥(Subgroup.closure (burnsideF48d_L '' ↑burnsideF48d_chainXL[0].2.1))
      burnsideF48d_chainXL[0].1 = Set.univ := by
    apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
    rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
    exact h
  have hp : p ∈ MulAction.orbit ↥(Subgroup.closure (burnsideF48d_L '' ↑burnsideF48d_chainXL[0].2.1))
      burnsideF48d_chainXL[0].1 := by
    rw [huniv]
    exact Set.mem_univ p
  obtain ⟨g, hg⟩ := hp
  exact ⟨(g : ↥burnsideF48d_X), hg⟩

end ChainX

section Equiv

theorem burnsideF48d_C0_equiv_X {K : Type} [Field K] [CharP K 3] (σ : K →+* K) (ω : K)
    (hK : Nat.card K = 27) (hσ : ∀ c, σ c = c ^ 3) (hω : ω ^ 3 = ω + 1) :
    Nonempty (↥(graphFixedRootGroup TwistTag.D4 K σ) ≃* ↥burnsideF48d_X) := by
  haveI : Finite ↥(graphFixedRootGroup TwistTag.D4 K σ) :=
    Nat.finite_of_card_ne_zero (by rw [burnsideF48d_card_C0 σ hK hσ]; norm_num)
  set ρ := burnsideF48d_ρ σ ω hK hσ hω with hρ
  have hsurj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
  have hle : Nat.card ↥(graphFixedRootGroup TwistTag.D4 K σ) ≤ Nat.card ↥ρ.range := by
    rw [burnsideF48d_range_ρ, burnsideF48d_card_X, burnsideF48d_card_C0 σ hK hσ]
  have hbij : Function.Bijective ρ.rangeRestrict := by
    haveI : Finite ↥ρ.range := Subgroup.instFiniteSubtypeMem _
    exact ⟨(Function.Surjective.bijective_of_nat_card_le hsurj hle).1, hsurj⟩
  exact ⟨(MulEquiv.ofBijective _ hbij).trans
    (MulEquiv.subgroupCongr (burnsideF48d_range_ρ σ ω hK hσ hω))⟩

theorem burnsideF48d_equiv_X : ∀ (H : Type) [Group H], ChF.IsGenLie H .D4tw 3 1 →
    Nonempty (↥burnsideF48d_X ≃* H) := by
  intro H _ hH
  obtain ⟨-, -, K, _, _, hcardK, σ, hσ, ⟨e⟩⟩ := hH
  have hK : Nat.card K = 27 := by rw [hcardK]; rfl
  haveI : CharP K 3 := burnsideF48d_charP hK
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨ω, hω⟩ := burnsideF48d_exists_omega (K := K) (by rw [← Nat.card_eq_fintype_card, hK])
  have hσ3 : ∀ c, σ c = c ^ 3 := fun c => by rw [hσ]; norm_num
  let σE : K ≃+* K := RingEquiv.ofBijective σ ⟨σ.injective, Finite.surjective_of_injective σ.injective⟩
  have hσE : σE.toRingHom = σ := RingHom.ext fun _ => rfl
  have hnf := (CFSG.LieType.Chevalley.odd_triality_exact_automorphism_normal_form Nat.prime_three
    (by norm_num) le_rfl K (by rw [hK]; norm_num) σE (fun c => by
      show σ c = c ^ (3 ^ 1)
      rw [hσ3]; norm_num)).2.2.2.2.2.2.2
  rw [hσE] at hnf
  obtain ⟨f⟩ := hnf
  obtain ⟨g⟩ := burnsideF48d_C0_equiv_X σ ω hK hσ3 hω
  exact ⟨g.symm.trans (f.symm.trans e.symm)⟩

end Equiv

end CFSG.ASVolI
