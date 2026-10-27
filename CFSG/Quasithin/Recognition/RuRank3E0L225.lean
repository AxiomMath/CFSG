module

public import CFSG.Quasithin.Recognition.RuRank3RuAut
public import CFSG.Quasithin.Recognition.RuRank3E0Data

public section

namespace CFSG.Quasithin.RuRank3

open CFSG.Sporadic.Schreier.Tits CFSG.Sporadic.RuSchreier
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
open scoped MatrixGroups

attribute [local instance] fact_prime_five' fact_two_not_square_five

@[expose] def titsK0O : Set (Fin 1755) := {x | titsK0Lab[(x : ℕ)]! = 1}

theorem titsK0Gen_mem {i : ℕ} (hi : i < 3) : titsK0Gen i ∈ titsK0 := by
  rw [titsK0_eq_closure]
  exact Subgroup.subset_closure ⟨i, hi, rfl⟩

theorem mem_titsK0_of_closure {g : Equiv.Perm (Fin 1755)}
    (hg : g ∈ Subgroup.closure {g | ∃ i < 3, permOfArr 1755 titsK0Strong[i]! = g}) :
    g ∈ titsK0 := by
  rw [titsK0_eq_closure]
  exact hg

theorem titsK0O_apply
    {k : Equiv.Perm (Fin 1755)} (hk : k ∈ titsK0) {x : Fin 1755}
    (hx : x ∈ titsK0O) : k x ∈ titsK0O := by
  have h : k x ∈ MulAction.orbit titsK0 x := ⟨⟨k, hk⟩, rfl⟩
  rw [orbit_titsK0] at h
  have h' : titsK0Lab[((k x : Fin 1755) : ℕ)]! = titsK0Lab[(x : ℕ)]! := h
  show titsK0Lab[((k x : Fin 1755) : ℕ)]! = 1
  rw [h']
  exact hx

theorem titsK0Bl_facts
    {i : ℕ} (hi : i < 3) {x : Fin 1755} (hx : x ∈ titsK0O) :
    titsK0Bl[(x : ℕ)]! < 26 ∧
      titsK0Bl[(titsK0Gens[i]!)[(x : ℕ)]!]! = (titsK0Tau[i]!)[titsK0Bl[(x : ℕ)]!]! := by
  have h := allLt_spec (allLt_spec titsK0Block_check.1 hi) x.2
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  rcases h with h | h
  · exact absurd hx h
  · exact h

@[expose] def titsK0BlF (x : Fin 1755) : Fin 26 :=
  ⟨titsK0Bl[(x : ℕ)]! % 26, Nat.mod_lt _ (by norm_num)⟩

theorem titsK0BlF_val {x : Fin 1755} (hx : x ∈ titsK0O) :
    ((titsK0BlF x : Fin 26) : ℕ) = titsK0Bl[(x : ℕ)]! :=
  Nat.mod_eq_of_lt (titsK0Bl_facts (by norm_num : 0 < 3) hx).1

theorem titsK0Tau_facts {i : ℕ} (hi : i < 3) :
    isInvA 26 titsK0Tau[i]! (invCand 26 titsK0Tau[i]!) = true ∧
    lettersOK 3 (titsK0TauWords.getD i []) = true ∧
    eqA 26 (wordA 26 psl26GensA psl26GensInvA (titsK0TauWords.getD i [])) titsK0Tau[i]! =
      true := by
  have h := allLt_spec titsK0Block_check.2.2.1 hi
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

@[expose] noncomputable def titsK0TauP (i : ℕ) : Equiv.Perm (Fin 26) :=
  permOfArr 26 titsK0Tau[i]!

theorem rep_titsK0TauP
    {i : ℕ} (hi : i < 3) : Rep 26 titsK0Tau[i]! (titsK0TauP i) :=
  (rep_permOfArr (titsK0Tau_facts hi).1).1

theorem titsK0BlF_gen
    {i : ℕ} (hi : i < 3) {x : Fin 1755} (hx : x ∈ titsK0O) :
    titsK0BlF (titsK0Gen i x) = titsK0TauP i (titsK0BlF x) := by
  have hgx := titsK0O_apply (titsK0Gen_mem hi) hx
  have hrep := titsK0Gens_rep i (by rw [titsK0Gens_size]; exact hi)
  apply Fin.ext
  rw [titsK0BlF_val hgx, ← hrep x, ← rep_titsK0TauP hi (titsK0BlF x), titsK0BlF_val hx]
  exact (titsK0Bl_facts hi hx).2

theorem exists_titsK0_block
    {k : Equiv.Perm (Fin 1755)}
    (hk : k ∈ Subgroup.closure {g | ∃ i < 3, permOfArr 1755 titsK0Strong[i]! = g}) :
    ∃ τ : Equiv.Perm (Fin 26), ∀ x ∈ titsK0O, titsK0BlF (k x) = τ (titsK0BlF x) := by
  induction hk using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨i, hi, rfl⟩ := hg
    exact ⟨titsK0TauP i, fun x hx => titsK0BlF_gen hi hx⟩
  | one => exact ⟨1, fun x _ => rfl⟩
  | mul g h hg hh ihg ihh =>
    obtain ⟨τ, hτ⟩ := ihg
    obtain ⟨σ, hσ⟩ := ihh
    refine ⟨τ * σ, fun x hx => ?_⟩
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      hτ _ (titsK0O_apply (mem_titsK0_of_closure hh) hx), hσ x hx]
  | inv g hg ihg =>
    obtain ⟨τ, hτ⟩ := ihg
    refine ⟨τ⁻¹, fun x hx => ?_⟩
    have hy := titsK0O_apply (inv_mem (mem_titsK0_of_closure hg)) hx
    have e := hτ _ hy
    rw [perm_apply_inv] at e
    rw [e, perm_inv_apply]

theorem titsK0BlF_surj
    (c : Fin 26) : ∃ x ∈ titsK0O, titsK0BlF x = c := by
  have h := allLt_spec titsK0Block_check.2.1 c.2
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hlt, hlab⟩, hbl⟩ := h
  have hO : (⟨titsK0BlReps[(c : ℕ)]!, hlt⟩ : Fin 1755) ∈ titsK0O := hlab
  refine ⟨⟨titsK0BlReps[(c : ℕ)]!, hlt⟩, hO, Fin.ext ?_⟩
  rw [titsK0BlF_val hO]
  exact hbl

theorem titsK0_block_unique
    {k : Equiv.Perm (Fin 1755)} {τ σ : Equiv.Perm (Fin 26)}
    (hτ : ∀ x ∈ titsK0O, titsK0BlF (k x) = τ (titsK0BlF x))
    (hσ : ∀ x ∈ titsK0O, titsK0BlF (k x) = σ (titsK0BlF x)) : τ = σ := by
  ext c
  obtain ⟨x, hx, rfl⟩ := titsK0BlF_surj c
  rw [← hτ x hx, ← hσ x hx]

theorem exists_titsK0_block'
    (k : titsK0) : ∃ τ : Equiv.Perm (Fin 26),
    ∀ x ∈ titsK0O, titsK0BlF ((k : Equiv.Perm (Fin 1755)) x) = τ (titsK0BlF x) :=
  exists_titsK0_block (by rw [← titsK0_eq_closure]; exact k.2)

@[expose] noncomputable def titsK0BlockHom
    : titsK0 →* Equiv.Perm (Fin 26) where
  toFun k := Classical.choose (exists_titsK0_block' k)
  map_one' := titsK0_block_unique (Classical.choose_spec (exists_titsK0_block' 1))
    (fun _ _ => rfl)
  map_mul' k k' := titsK0_block_unique (Classical.choose_spec (exists_titsK0_block' (k * k')))
    (fun x hx => by
      show titsK0BlF ((k : Equiv.Perm (Fin 1755)) ((k' : Equiv.Perm (Fin 1755)) x)) = _
      rw [Classical.choose_spec (exists_titsK0_block' k) _ (titsK0O_apply k'.2 hx),
        Classical.choose_spec (exists_titsK0_block' k') x hx]
      rfl)

theorem titsK0BlockHom_spec
    (k : titsK0) (x : Fin 1755) (hx : x ∈ titsK0O) :
    titsK0BlF ((k : Equiv.Perm (Fin 1755)) x) = titsK0BlockHom k (titsK0BlF x) :=
  Classical.choose_spec (exists_titsK0_block' k) x hx

theorem titsK0BlockHom_gen
    {i : ℕ} (hi : i < 3) :
    titsK0BlockHom ⟨titsK0Gen i, titsK0Gen_mem hi⟩ = titsK0TauP i :=
  titsK0_block_unique (titsK0BlockHom_spec _) (fun _ hx => titsK0BlF_gen hi hx)

@[expose] noncomputable def titsK0TauGroup : Subgroup (Equiv.Perm (Fin 26)) :=
  Subgroup.closure (Set.range fun i : Fin 3 => titsK0TauP i)

theorem titsK0TauP_mem {i : ℕ} (hi : i < 3) : titsK0TauP i ∈ titsK0TauGroup :=
  Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩

theorem range_titsK0BlockHom_le
    : titsK0BlockHom.range ≤ titsK0TauGroup := by
  have key : ∀ g (hg : g ∈ Subgroup.closure {g | ∃ i < 3, permOfArr 1755 titsK0Strong[i]! = g})
      (h : g ∈ titsK0), titsK0BlockHom ⟨g, h⟩ ∈ titsK0TauGroup := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨i, hi, rfl⟩ := hg
      intro h
      rw [show (⟨permOfArr 1755 titsK0Strong[i]!, h⟩ : titsK0) =
        ⟨titsK0Gen i, titsK0Gen_mem hi⟩ from rfl, titsK0BlockHom_gen hi]
      exact titsK0TauP_mem hi
    | one =>
      intro h
      rw [show (⟨1, h⟩ : titsK0) = 1 from rfl, map_one]
      exact one_mem _
    | mul g g' hg hg' ihg ihg' =>
      intro h
      rw [show (⟨g * g', h⟩ : titsK0) = ⟨g, mem_titsK0_of_closure hg⟩ *
        ⟨g', mem_titsK0_of_closure hg'⟩ from rfl, map_mul]
      exact mul_mem (ihg _) (ihg' _)
    | inv g hg ihg =>
      intro h
      rw [show (⟨g⁻¹, h⟩ : titsK0) = (⟨g, mem_titsK0_of_closure hg⟩)⁻¹ from rfl, map_inv]
      exact inv_mem (ihg _)
  rintro _ ⟨⟨g, hg⟩, rfl⟩
  exact key g (by rw [← titsK0_eq_closure]; exact hg) hg

theorem titsK0TauGroup_le_range
    : titsK0TauGroup ≤ titsK0BlockHom.range := by
  rw [titsK0TauGroup, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨titsK0Gen i, titsK0Gen_mem i.2⟩, titsK0BlockHom_gen i.2⟩

theorem getElem!_map_of_lt {α β : Type*} [Inhabited α] [Inhabited β] (f : α → β) (a : Array α)
    {i : ℕ} (hi : i < a.size) : (a.map f)[i]! = f a[i]! := by
  rw [getElem!_pos (a.map f) i (by simpa using hi), getElem!_pos a i hi, Array.getElem_map]

theorem psl26Gens_facts {i : ℕ} (hi : i < 3) :
    isInvA 26 psl26GensA[i]! (invCand 26 psl26GensA[i]!) = true :=
  allLt_spec titsK0Block_check.2.2.2.2 hi

theorem rep_psl26Gens :
    ∀ h < 3, Rep 26 psl26GensA[h]! ([sigma26 pslX, sigma26 pslS, sigma26 pslT].getD h 1) := by
  intro h hh
  interval_cases h
  · exact rep_sigma26X
  · exact rep_sigma26S
  · exact rep_sigma26T

theorem rep_psl26GensInv :
    ∀ h < 3, Rep 26 psl26GensInvA[h]!
      ([sigma26 pslX, sigma26 pslS, sigma26 pslT].getD h 1)⁻¹ := by
  intro h hh
  rw [psl26GensInvA, getElem!_map_of_lt _ _ (by simpa [psl26GensA] using hh)]
  exact rep_inv_of_isInvA (rep_psl26Gens h hh) (psl26Gens_facts hh)

theorem rep_titsK0Taus :
    ∀ h < 3, Rep 26 titsK0Tau[h]! ([titsK0TauP 0, titsK0TauP 1, titsK0TauP 2].getD h 1) := by
  intro h hh
  interval_cases h
  · exact rep_titsK0TauP (by norm_num)
  · exact rep_titsK0TauP (by norm_num)
  · exact rep_titsK0TauP (by norm_num)

theorem rep_titsK0TausInv :
    ∀ h < 3, Rep 26 titsK0TauInv[h]!
      ([titsK0TauP 0, titsK0TauP 1, titsK0TauP 2].getD h 1)⁻¹ := by
  intro h hh
  rw [titsK0TauInv, getElem!_map_of_lt _ _ (by simpa [titsK0Tau] using hh)]
  exact rep_inv_of_isInvA (rep_titsK0Taus h hh) (titsK0Tau_facts hh).1

theorem titsK0TauGroup_le_range_sigma26
    : titsK0TauGroup ≤ sigma26.range := by
  rw [titsK0TauGroup, Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  have hi := i.2
  have e := eq_of_eqA (rep_wordA_evalSigned rep_psl26Gens rep_psl26GensInv _
    (titsK0Tau_facts hi).2.1) (rep_titsK0TauP hi) (titsK0Tau_facts hi).2.2
  show titsK0TauP i ∈ (sigma26.range : Set (Equiv.Perm (Fin 26)))
  rw [← e, range_sigma26]
  apply evalSigned_mem
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

theorem range_sigma26_le_titsK0TauGroup
    : sigma26.range ≤ titsK0TauGroup := by
  rw [range_sigma26, Subgroup.closure_le]
  have hw : ∀ i < 3, [sigma26 pslX, sigma26 pslS, sigma26 pslT].getD i 1 ∈ titsK0TauGroup := by
    intro i hi
    have h := allLt_spec titsK0Block_check.2.2.2.1 hi
    rw [Bool.and_eq_true] at h
    have e := eq_of_eqA (rep_wordA_evalSigned rep_titsK0Taus rep_titsK0TausInv _ h.1)
      (rep_psl26Gens i hi) h.2
    rw [← e]
    apply evalSigned_mem
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl
    · exact titsK0TauP_mem (by norm_num)
    · exact titsK0TauP_mem (by norm_num)
    · exact titsK0TauP_mem (by norm_num)
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · exact hw 0 (by norm_num)
  · exact hw 1 (by norm_num)
  · exact hw 2 (by norm_num)

theorem range_titsK0BlockHom
    : titsK0BlockHom.range = sigma26.range :=
  le_antisymm (range_titsK0BlockHom_le.trans titsK0TauGroup_le_range_sigma26)
    (range_sigma26_le_titsK0TauGroup.trans titsK0TauGroup_le_range)

theorem titsK0BlockHom_injective
    : Function.Injective titsK0BlockHom := by
  apply injective_of_card_range
  rw [range_titsK0BlockHom, card_titsK0, range_sigma26, card_closure26]

@[expose] noncomputable def titsK0EquivPSL
    : titsK0 ≃* PSL(2, GaloisField 5 2) :=
  ((MonoidHom.ofInjective titsK0BlockHom_injective).trans
    (MulEquiv.subgroupCongr range_titsK0BlockHom)).trans
    ((MonoidHom.ofInjective sigma26_injective).symm.trans pslF25EquivGalois)

theorem titsK0_le_ruE0
    : titsK0.subgroupOf titsA ≤ ruE0 := by
  intro k hk
  rw [Subgroup.mem_subgroupOf] at hk
  apply mem_ruE0_of_normalizes
  intro j
  constructor
  · intro hj
    exact mul_mem (mul_mem hk hj) (inv_mem hk)
  · intro hj
    have := mul_mem (mul_mem (inv_mem hk) hj) hk
    rwa [show ((k : Equiv.Perm (Fin 1755)))⁻¹ * ((k : Equiv.Perm (Fin 1755)) * j *
      ((k : Equiv.Perm (Fin 1755)))⁻¹) * (k : Equiv.Perm (Fin 1755)) = j by group] at this

@[expose] noncomputable def ruK0E
    : Subgroup ruE0 := (titsK0.subgroupOf titsA).subgroupOf ruE0

theorem mem_ruK0E
    {c : ruE0} : c ∈ ruK0E ↔ ((c : titsA) : Equiv.Perm (Fin 1755)) ∈ titsK0 := by
  rw [ruK0E, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]

@[expose] noncomputable def ruK0EEquiv
    : ruK0E ≃* titsK0 :=
  (Subgroup.subgroupOfEquivOfLe titsK0_le_ruE0).trans (Subgroup.subgroupOfEquivOfLe titsK0_le)

theorem card_ruK0E
    : Nat.card ruK0E = 7800 := by
  rw [Nat.card_congr ruK0EEquiv.toEquiv, card_titsK0]

theorem index_ruK0E
    : ruK0E.index = 2 := by
  have h := Subgroup.card_mul_index ruK0E
  rw [card_ruK0E, card_ruE0] at h
  omega

theorem centralizer_ruK0E
    : Subgroup.centralizer (ruK0E : Set ruE0) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  have hxE : titsX13A ∈ ruE0 := titsK0_le_ruE0 (by
    rw [Subgroup.mem_subgroupOf]
    exact titsX13_mem_K0)
  have htA : titsTInv ∈ titsA := titsK0_le titsTInv_mem_K0
  have htE : (⟨titsTInv, htA⟩ : titsA) ∈ ruE0 := titsK0_le_ruE0 (by
    rw [Subgroup.mem_subgroupOf]
    exact titsTInv_mem_K0)
  have hx : (⟨titsX13A, hxE⟩ : ruE0) ∈ ruK0E := mem_ruK0E.2 titsX13_mem_K0
  have ht : (⟨⟨titsTInv, htA⟩, htE⟩ : ruE0) ∈ ruK0E := mem_ruK0E.2 titsTInv_mem_K0
  have h1 := Subgroup.mem_centralizer_iff.1 hc _ hx
  have h2 := Subgroup.mem_centralizer_iff.1 hc _ ht
  have hcx : (c : titsA) * titsX13A = titsX13A * (c : titsA) :=
    (congrArg Subtype.val h1).symm
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_commute_titsX13 hcx)
  have hC : ((c : titsA) : Equiv.Perm (Fin 1755)) = titsX13 ^ n := by
    rw [← hn]
    rfl
  have hct : titsTInv * ((c : titsA) : Equiv.Perm (Fin 1755)) =
      ((c : titsA) : Equiv.Perm (Fin 1755)) * titsTInv :=
    congrArg (fun y : ruE0 => ((y : titsA) : Equiv.Perm (Fin 1755))) h2
  have hconj : titsTInv * titsX13 ^ n * titsTInv⁻¹ = titsX13 ^ n := by
    rw [← hC, hct, mul_inv_cancel_right]
  have hTX : titsTInv * titsX13 ^ n * titsTInv⁻¹ = (titsX13 ^ n)⁻¹ := by
    rw [← conj_zpow, titsT_inverts_X13, inv_zpow]
  have hsq : titsX13 ^ (n + n) = 1 := by
    rw [zpow_add]
    have e : (titsX13 ^ n)⁻¹ = titsX13 ^ n := hTX.symm.trans hconj
    calc titsX13 ^ n * titsX13 ^ n = (titsX13 ^ n)⁻¹ * titsX13 ^ n := by rw [e]
      _ = 1 := inv_mul_cancel _
  have h13 : ((13 : ℕ) : ℤ) ∣ n + n := by
    rw [← orderOf_titsX13]
    exact orderOf_dvd_iff_zpow_eq_one.2 hsq
  have h13' : ((orderOf titsX13 : ℕ) : ℤ) ∣ n := by
    rw [orderOf_titsX13]
    push_cast at h13 ⊢
    omega
  have hn1 : titsX13 ^ n = 1 := orderOf_dvd_iff_zpow_eq_one.1 h13'
  apply Subtype.ext
  apply Subtype.ext
  rw [hC, hn1]
  rfl

@[expose] noncomputable def ruSdAP : Equiv.Perm (Fin 1755) := permOfArr 1755 ruSdA

@[expose] noncomputable def ruSdBP : Equiv.Perm (Fin 1755) := permOfArr 1755 ruSdB

theorem rep_ruSdAP
    : Rep 1755 ruSdA ruSdAP := (rep_permOfArr ruSd_check.1).1

theorem rep_ruSdAP_inv
    : Rep 1755 (invCand 1755 ruSdA) ruSdAP⁻¹ := (rep_permOfArr ruSd_check.1).2

theorem rep_ruSdBP
    : Rep 1755 ruSdB ruSdBP := (rep_permOfArr ruSd_check.2.1).1

theorem rep_ruSdBP_inv : Rep 1755 (invCand 1755 ruSdB) ruSdBP⁻¹ :=
  (rep_permOfArr ruSd_check.2.1).2

theorem rep_conjArr {c t : Array ℕ} {C T : Equiv.Perm (Fin 1755)} (hc : Rep 1755 c C)
    (hcinv : Rep 1755 (invCand 1755 c) C⁻¹) (ht : Rep 1755 t T) :
    Rep 1755 (conjArr c t) (C * T * C⁻¹) :=
  rep_compA (rep_compA hc ht) hcinv

theorem normalizes_titsK0_of_gens {a : Equiv.Perm (Fin 1755)}
    (h : ∀ i < 3, a * titsK0Gen i * a⁻¹ ∈ titsK0) :
    ∀ k, k ∈ titsK0 ↔ a * k * a⁻¹ ∈ titsK0 := by
  have hfwd : ∀ k ∈ titsK0, a * k * a⁻¹ ∈ titsK0 := by
    intro k hk
    rw [titsK0_eq_closure] at hk
    induction hk using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨i, hi, rfl⟩ := hg
      exact h i hi
    | one =>
      rw [mul_one, mul_inv_cancel]
      exact one_mem _
    | mul g g' _ _ ihg ihg' =>
      have := mul_mem ihg ihg'
      rwa [show a * g * a⁻¹ * (a * g' * a⁻¹) = a * (g * g') * a⁻¹ by group] at this
    | inv g _ ihg =>
      have := inv_mem ihg
      rwa [show (a * g * a⁻¹)⁻¹ = a * g⁻¹ * a⁻¹ by group] at this
  intro k
  refine ⟨hfwd k, fun hk => ?_⟩
  have hle : titsK0.map (MulAut.conj a).toMonoidHom ≤ titsK0 := by
    rintro _ ⟨k', hk', rfl⟩
    exact hfwd k' hk'
  have heq : titsK0.map (MulAut.conj a).toMonoidHom = titsK0 :=
    Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj a).injective).ge
  rw [← heq] at hk
  obtain ⟨k', hk', e⟩ := hk
  rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at e
  rw [← mul_left_cancel (mul_right_cancel e)]
  exact hk'

theorem ruSd_normalizes
    {c : Array ℕ} {C : Equiv.Perm (Fin 1755)} (hc : Rep 1755 c C)
    (hcinv : Rep 1755 (invCand 1755 c) C⁻¹)
    (h : ∀ i < 3, inTitsK0 (conjArr c titsK0Gens[i]!) = true) :
    ∀ k, k ∈ titsK0 ↔ C * k * C⁻¹ ∈ titsK0 :=
  normalizes_titsK0_of_gens fun i hi => mem_titsK0_of_sift
    (rep_conjArr hc hcinv (titsK0Gens_rep i (by rw [titsK0Gens_size]; exact hi))) (h i hi)

theorem ruSdAP_normalizes
    : ∀ k, k ∈ titsK0 ↔ ruSdAP * k * ruSdAP⁻¹ ∈ titsK0 :=
  ruSd_normalizes rep_ruSdAP rep_ruSdAP_inv fun i hi => by
    have := allLt_spec ruSd_check.2.2.2.2.1 hi
    rw [Bool.and_eq_true] at this
    exact this.1

theorem ruSdBP_normalizes
    : ∀ k, k ∈ titsK0 ↔ ruSdBP * k * ruSdBP⁻¹ ∈ titsK0 :=
  ruSd_normalizes rep_ruSdBP rep_ruSdBP_inv fun i hi => by
    have := allLt_spec ruSd_check.2.2.2.2.1 hi
    rw [Bool.and_eq_true] at this
    exact this.2

@[expose] noncomputable def ruSdAE
    : ruE0 :=
  ⟨⟨ruSdAP, mem_titsA_of_inTitsA rep_ruSdAP ruSd_check.2.2.1⟩,
    mem_ruE0_of_normalizes ruSdAP_normalizes⟩

@[expose] noncomputable def ruSdBE
    : ruE0 :=
  ⟨⟨ruSdBP, mem_titsA_of_inTitsA rep_ruSdBP ruSd_check.2.2.2.1⟩,
    mem_ruE0_of_normalizes ruSdBP_normalizes⟩

theorem ruE0_ext
    {x y : ruE0}
    (h : ((x : titsA) : Equiv.Perm (Fin 1755)) = ((y : titsA) : Equiv.Perm (Fin 1755))) :
    x = y :=
  Subtype.ext (Subtype.ext h)

theorem coe_ruE0_pow
    (x : ruE0) (n : ℕ) :
    (((x ^ n : ruE0) : titsA) : Equiv.Perm (Fin 1755)) =
      ((x : titsA) : Equiv.Perm (Fin 1755)) ^ n := rfl

theorem ruSdAP_pow8 : ruSdAP ^ 8 = 1 :=
  eq_of_eqA (rep_powArr rep_ruSdAP 8) rep_idA ruSd_check.2.2.2.2.2.1

theorem ruSdAP_pow4 : ruSdAP ^ 4 ≠ 1 := fun h => by
  have := (eqA_iff (rep_powArr rep_ruSdAP 4) rep_idA).2 h
  rw [ruSd_check.2.2.2.2.2.2.1] at this
  exact Bool.false_ne_true this

theorem ruSdBP_sq : ruSdBP * ruSdBP = 1 :=
  eq_of_eqA (rep_compA rep_ruSdBP rep_ruSdBP) rep_idA ruSd_check.2.2.2.2.2.2.2.1

theorem ruSdBP_conj : ruSdBP * ruSdAP * ruSdBP⁻¹ = ruSdAP ^ 3 :=
  eq_of_eqA (rep_conjArr rep_ruSdBP rep_ruSdBP_inv rep_ruSdAP) (rep_powArr rep_ruSdAP 3)
    ruSd_check.2.2.2.2.2.2.2.2.1

theorem ruSdBP_ne_pow
    {i : ℕ} (hi : i < 8) : ruSdBP ≠ ruSdAP ^ i := fun h => by
  have h1 := allLt_spec ruSd_check.2.2.2.2.2.2.2.2.2 hi
  rw [(eqA_iff rep_ruSdBP (rep_powArr rep_ruSdAP i)).2 h] at h1
  exact Bool.false_ne_true h1

theorem exists_sylow_semidihedral_ruE0
    :
    ∃ P : Sylow 2 ruE0, Nonempty (CFSG.Open.SemidihedralGroup 4 ≃* (P : Subgroup ruE0)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA8 : ruSdAE ^ 8 = 1 := ruE0_ext (by rw [coe_ruE0_pow]; exact ruSdAP_pow8)
  have hA4 : ruSdAE ^ 4 ≠ 1 := fun h => ruSdAP_pow4 (by
    have := congrArg (fun y : ruE0 => ((y : titsA) : Equiv.Perm (Fin 1755))) h
    rw [coe_ruE0_pow] at this
    exact this)
  have hB2 : ruSdBE ^ 2 = 1 := ruE0_ext (by rw [coe_ruE0_pow, sq]; exact ruSdBP_sq)
  have hab : ruSdBE * ruSdAE * ruSdBE⁻¹ = ruSdAE ^ (2 ^ (4 - 2) - 1) := by
    rw [show (2 ^ (4 - 2) - 1 : ℕ) = 3 by norm_num]
    exact ruE0_ext (by rw [coe_ruE0_pow]; exact ruSdBP_conj)
  have hrels : ∀ r ∈ CFSG.Open.semidihedralRels 4, FreeGroup.lift ![ruSdAE, ruSdBE] r = 1 := by
    rintro r (rfl | rfl | rfl)
    · simpa using hA8
    · simpa using hB2
    · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_fin_one]
      rw [hab, mul_inv_cancel]
  let φ : CFSG.Open.SemidihedralGroup 4 →* ruE0 := PresentedGroup.toGroup hrels
  have hφ0 : φ (PresentedGroup.of 0) = ruSdAE := (PresentedGroup.toGroup.of hrels).trans (by simp)
  have hφ1 : φ (PresentedGroup.of 1) = ruSdBE := (PresentedGroup.toGroup.of hrels).trans (by simp)
  have hfin : Finite (CFSG.Open.SemidihedralGroup 4) :=
    CFSG.Semidihedral.presentation_finite 4 (by norm_num)
  have hcardSD : Nat.card (CFSG.Open.SemidihedralGroup 4) = 16 := by
    rw [CFSG.Semidihedral.card 4 (by norm_num)]
    norm_num
  have haP : ruSdAE ∈ φ.range := ⟨_, hφ0⟩
  have hbP : ruSdBE ∈ φ.range := ⟨_, hφ1⟩
  have hle16 : Nat.card φ.range ≤ 16 := by
    rw [← hcardSD]
    exact Nat.card_le_card_of_surjective _ φ.rangeRestrict_surjective
  have hordA : orderOf ruSdAE = 8 := by
    have := orderOf_eq_prime_pow (p := 2) (n := 2) (by norm_num; exact hA4) (by norm_num; exact hA8)
    simpa using this
  have hzA : Subgroup.zpowers ruSdAE ≤ φ.range := (Subgroup.zpowers_le).2 haP
  have h8 : 8 ∣ Nat.card φ.range := by
    have := Subgroup.card_dvd_of_le hzA
    rwa [Nat.card_zpowers, hordA] at this
  have hbnot : ruSdBE ∉ Subgroup.zpowers ruSdAE := by
    intro hb
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hb
    have hk' : ruSdAE ^ (k % 8) = ruSdBE := by
      have e := zpow_mod_orderOf ruSdAE k
      rw [hordA, Nat.cast_ofNat] at e
      rw [← hk, e]
    have hnn : 0 ≤ k % 8 := Int.emod_nonneg k (by norm_num)
    have hlt : (k % 8).toNat < 8 := by omega
    have hk'' : ruSdAE ^ (k % 8).toNat = ruSdBE := by
      rw [← hk', ← zpow_natCast, Int.toNat_of_nonneg hnn]
    apply ruSdBP_ne_pow hlt
    have := congrArg (fun y : ruE0 => ((y : titsA) : Equiv.Perm (Fin 1755))) hk''
    rw [coe_ruE0_pow] at this
    exact this.symm
  have h16 : Nat.card φ.range = 16 := by
    have hne : Nat.card φ.range ≠ 8 := by
      intro h8'
      apply hbnot
      have heq : Subgroup.zpowers ruSdAE = φ.range :=
        Subgroup.eq_of_le_of_card_ge hzA (by rw [h8', Nat.card_zpowers, hordA])
      rw [heq]
      exact hbP
    have hpos : 0 < Nat.card φ.range := Nat.card_pos
    omega
  have hbij : Function.Bijective φ.rangeRestrict :=
    φ.rangeRestrict_surjective.bijective_of_nat_card_le (by rw [h16, hcardSD])
  have hp : IsPGroup 2 φ.range := IsPGroup.of_card (n := 4) (by rw [h16]; norm_num)
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp Q.isPGroup'
  have hdvd : 2 ^ k ∣ 15600 := by
    rw [← hk, ← card_ruE0]
    exact Subgroup.card_subgroup_dvd_card _
  have hk4 : k ≤ 4 := by
    by_contra hk5
    have := (pow_dvd_pow 2 (by omega : 5 ≤ k)).trans hdvd
    norm_num at this
  have hQeq : φ.range = (Q : Subgroup ruE0) := by
    apply Subgroup.eq_of_le_of_card_ge hQ
    rw [hk, h16]
    calc 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk4
      _ = 16 := by norm_num
  exact ⟨Q, ⟨(MulEquiv.ofBijective _ hbij).trans (MulEquiv.subgroupCongr hQeq)⟩⟩

theorem isL225Plus_ruE0
    : IsL225Plus ruE0 := by
  refine ⟨ruK0E, Subgroup.normal_of_index_eq_two index_ruK0E, index_ruK0E,
    ⟨ruK0EEquiv.trans titsK0EquivPSL⟩, centralizer_ruK0E, fun S => ?_⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, ⟨e⟩⟩ := exists_sylow_semidihedral_ruE0
  exact ⟨e.trans (Sylow.equiv P S)⟩

end CFSG.Quasithin.RuRank3
