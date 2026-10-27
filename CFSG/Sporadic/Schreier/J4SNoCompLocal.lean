module

public import CFSG.Sporadic.Schreier.J4SNoCompCover
public import CFSG.Sporadic.Schreier.J4SNoCompGen

public noncomputable section

namespace CFSG.Sporadic.J4Schreier.NoComp

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.GLQ CFSG.Sporadic.SmallF2
open CFSG.Sporadic.SmallF2.Native CFSG.SectionRank.Native MulAction

theorem N_le_centralizer_of_mem {n : J} (hn : n ∈ N) :
    N ≤ Subgroup.centralizer ({n} : Set J) := fun m hm =>
  Subgroup.mem_centralizer_singleton_iff.2 (N_comm n hn m hm).symm

theorem centralizer_N_inf_H :
    Subgroup.centralizer (N : Set J) ⊓ H = N :=
  QT_unique_J4_local_normal_module_irreducible.2.2.2.2.2.2.2.2.2

theorem not_isComponent_centralizer_η14
    (B : Subgroup (Subgroup.centralizer ({η 14} : Set J))) :
    ¬ CFSG.IsComponent B := by
  have hNX := N_le_centralizer_of_mem (η_mem_N 14)
  refine CFSG.LocalCores.not_isComponent_of_self_centralizing
    (R := N.subgroupOf (Subgroup.centralizer ({η 14} : Set J))) ⟨fun r hr x => ?_⟩ ?_ ?_ B
  · rw [Subgroup.mem_subgroupOf] at hr ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_mem_N_of_mem_H _ (centralizer_η14_le_H x.2) _ hr
  · refine Group.isSolvable_of_comm fun p q => Subtype.ext (Subtype.ext ?_)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    exact N_comm _ (Subgroup.mem_subgroupOf.1 p.2) _ (Subgroup.mem_subgroupOf.1 q.2)
  · intro x hx
    rw [Subgroup.mem_subgroupOf, ← centralizer_N_inf_H]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun n hn => ?_,
      centralizer_η14_le_H x.2⟩
    have h1 := Subgroup.mem_centralizer_iff.1 hx ⟨n, hNX hn⟩ (Subgroup.mem_subgroupOf.2 hn)
    have h2 := congrArg Subtype.val h1
    rw [Subgroup.coe_mul, Subgroup.coe_mul] at h2
    exact h2

@[expose] def Tset : Set J := {m | m ∈ conjOrbit K (η 14) ∧ m * η 1 ∈ conjOrbit K (η 14)}

@[expose] def DSub : Subgroup J := Subgroup.closure Tset

theorem zero_mem_dList : 0 ∈ dList := by
  unfold dList
  exact List.mem_cons_self

theorem Tset_subset
    {m : J} (hm : m ∈ Tset) : ∃ a ∈ dList, m = η a := by
  obtain ⟨h1, h2⟩ := hm
  rw [conjOrbit_fourteen] at h1 h2
  obtain ⟨i, hi, rfl⟩ := h1
  obtain ⟨i', hi', e⟩ := h2
  rw [← η_xor] at e
  have hlt : orb14.1[i]! ^^^ 1 < 2 ^ 11 :=
    Nat.xor_lt_two_pow (bfsOK_lt orb14_ok hi) (by norm_num)
  exact ⟨_, td_check.2.2.1 i hi i' hi' (η_injOn hlt (bfsOK_lt orb14_ok hi') e), rfl⟩

theorem DSub_subset
    {m : J} (hm : m ∈ DSub) : ∃ a ∈ dList, m = η a := by
  induction hm using Subgroup.closure_induction with
  | mem m hm => exact Tset_subset hm
  | one => exact ⟨0, zero_mem_dList, η_zero.symm⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a ^^^ b, td_check.2.1 a ha b hb, (η_xor a b).symm⟩
  | inv x _ hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact ⟨a, ha, η_inv a⟩

theorem DSub_le_N :
    DSub ≤ N := fun m hm => by
  obtain ⟨a, -, rfl⟩ := DSub_subset hm
  exact η_mem_N a

theorem conj_mem_conjOrbit
    {c m : J} (hc : c ∈ H) (hm : m ∈ conjOrbit K (η 14)) :
    c * m * c⁻¹ ∈ conjOrbit K (η 14) := by
  obtain ⟨k, hk, rfl⟩ := hm
  have h := conj_η14_mem (H.mul_mem hc (K_le_H hk))
  rw [show c * (k * η 14 * k⁻¹) * c⁻¹ = c * k * η 14 * (c * k)⁻¹ by group]
  exact h

theorem Tset_conj
    {c : J} (hc : c ∈ H) (hcz : c * η 1 = η 1 * c) {m : J} (hm : m ∈ Tset) :
    c * m * c⁻¹ ∈ Tset := by
  refine ⟨conj_mem_conjOrbit hc hm.1, ?_⟩
  have e : c * m * c⁻¹ * η 1 = c * (m * η 1) * c⁻¹ := by
    calc c * m * c⁻¹ * η 1 = c * m * c⁻¹ * (η 1 * c) * c⁻¹ := by group
      _ = c * m * c⁻¹ * (c * η 1) * c⁻¹ := by rw [hcz]
      _ = c * (m * η 1) * c⁻¹ := by group
  rw [e]
  exact conj_mem_conjOrbit hc hm.2

theorem DSub_conj
    {c : J} (hc : c ∈ H) (hcz : c * η 1 = η 1 * c) {m : J} (hm : m ∈ DSub) :
    c * m * c⁻¹ ∈ DSub := by
  induction hm using Subgroup.closure_induction with
  | mem m hm => exact Subgroup.subset_closure (Tset_conj hc hcz hm)
  | one => rw [mul_one, mul_inv_cancel]; exact DSub.one_mem
  | mul x y _ _ hx hy =>
    rw [show c * (x * y) * c⁻¹ = c * x * c⁻¹ * (c * y * c⁻¹) by group]
    exact DSub.mul_mem hx hy
  | inv x _ hx =>
    rw [show c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ by group]
    exact DSub.inv_mem hx

theorem kd_word {l e : ℕ} (hl : l = 5 ∨ l = 6) (he : e ∈ dSets[l]!) :
    ∃ w : List ℤ, app11W w 1 = e ∧
      ∀ a ∈ dList, etaV unMats repVecs[l]! (app11W w a) = repVecs[l]! := by
  have hl' : l ∈ [5, 6] := by rcases hl with rfl | rfl <;> simp
  obtain ⟨p, hp, hpe⟩ := List.any_eq_true.1 (kd_check.2 l hl' e he)
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at hpe
  have h2 := kd_check.1 p hp
  refine ⟨p.2.2, hpe.1 ▸ h2.1, fun a ha => ?_⟩
  rw [← hpe.2]
  exact h2.2 a ha

theorem mem_H_iff_smul_v
    {g : J} : g ∈ H ↔ g • v = v := by
  rw [H_eq_Hj, ← stabilizer_v_eq_Hj, mem_stabilizer_iff]

theorem dSets_small {l a : ℕ} (hl : l < 7) (ha : a ∈ dSets[l]!) : l = 5 ∨ l = 6 := by
  interval_cases l <;> simp_all [dSets]

theorem conj_DSub_mem_H
    {c : J} (hc : c ∈ Subgroup.centralizer ({η 1} : Set J)) {m : J}
    (hm : m ∈ DSub) : c * m * c⁻¹ ∈ H := by
  have hc' : c⁻¹ * η 1 * c = η 1 := by
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hc
    rw [mul_assoc, ← h1, inv_mul_cancel_left]
  obtain ⟨l, hl, h, hh, h', hh', e⟩ := exists_decomp c⁻¹
  have ec : c = h'⁻¹ * mRep l * h⁻¹ := by
    rw [← inv_inv c, e]
    group
  have hrs : (mRep l)⁻¹ * (h' * η 1 * h'⁻¹) * mRep l = h⁻¹ * η 1 * h := by
    calc (mRep l)⁻¹ * (h' * η 1 * h'⁻¹) * mRep l = h⁻¹ * (c⁻¹ * η 1 * c) * h := by
          rw [e, ec]; group
      _ = h⁻¹ * η 1 * h := by rw [hc']
  have hr : h' * η 1 * h'⁻¹ ∈ N := conj_mem_N_of_mem_H h' hh' _ (η_mem_N 1)
  have hs : h⁻¹ * η 1 * h ∈ N := by
    have := conj_mem_N_of_mem_H h⁻¹ (H.inv_mem hh) _ (η_mem_N 1)
    rwa [inv_inv] at this
  have hmN : m ∈ N := DSub_le_N hm
  obtain ⟨a, -, hsa, hcase⟩ := conj_rep_mem hl hr hs hrs
  rcases hcase with ha0 | hl0 | hD
  · exfalso
    rw [ha0, η_zero] at hsa
    apply η_one_ne_one
    calc η 1 = h * (h⁻¹ * η 1 * h) * h⁻¹ := by group
      _ = 1 := by rw [hsa]; group
  · have hcH : c⁻¹ ∈ H := by
      rw [e, hl0, mRep_zero, inv_one, mul_one]
      exact H.mul_mem hh hh'
    have hcH' : c ∈ H := by simpa using H.inv_mem hcH
    exact H.mul_mem (H.mul_mem hcH' (N_le_H hmN)) (H.inv_mem hcH')
  · obtain ⟨w, hw1, hwD⟩ := kd_word (dSets_small hl hD) hD
    have hk : signedWord x y w * η 1 * (signedWord x y w)⁻¹ = η a := by
      rw [word_conj_η, hw1]
    have hkH : signedWord x y w ∈ H := K_le_H (signedWord_mem_K w)
    have hcH : h * signedWord x y w ∈ H := H.mul_mem hh hkH
    have hcz : (h * signedWord x y w)⁻¹ * η 1 = η 1 * (h * signedWord x y w)⁻¹ := by
      have e1 : h * signedWord x y w * η 1 * (h * signedWord x y w)⁻¹ = η 1 := by
        calc h * signedWord x y w * η 1 * (h * signedWord x y w)⁻¹ =
              h * (signedWord x y w * η 1 * (signedWord x y w)⁻¹) * h⁻¹ := by group
          _ = h * (h⁻¹ * η 1 * h) * h⁻¹ := by rw [hk, hsa]
          _ = η 1 := by group
      calc (h * signedWord x y w)⁻¹ * η 1 =
            (h * signedWord x y w)⁻¹ * (h * signedWord x y w * η 1 * (h * signedWord x y w)⁻¹) :=
            by rw [e1]
        _ = η 1 * (h * signedWord x y w)⁻¹ := by group
    have hm' := DSub_conj (H.inv_mem hcH) hcz hm
    rw [inv_inv] at hm'
    obtain ⟨a', ha', he'⟩ := DSub_subset hm'
    have key : h⁻¹ * m * h = η (app11W w a') := by
      calc h⁻¹ * m * h = signedWord x y w *
            ((h * signedWord x y w)⁻¹ * m * (h * signedWord x y w)) * (signedWord x y w)⁻¹ := by
            group
        _ = η (app11W w a') := by rw [he', word_conj_η]
    have hfix : η (app11W w a') • ((mRep l)⁻¹ • v) = (mRep l)⁻¹ • v := by
      rw [mRep_inv_smul_v hl, η_smul_toRow, hwD a' ha']
    have hH : mRep l * (h⁻¹ * m * h) * (mRep l)⁻¹ ∈ H := by
      rw [mem_H_iff_smul_v, key, mul_smul, mul_smul, hfix, smul_inv_smul]
    rw [ec, show h'⁻¹ * mRep l * h⁻¹ * m * (h'⁻¹ * mRep l * h⁻¹)⁻¹ =
      h'⁻¹ * (mRep l * (h⁻¹ * m * h) * (mRep l)⁻¹) * h' by group]
    exact H.mul_mem (H.mul_mem (H.inv_mem hh') hH) hh'

section ChainBound

variable {G : Type*} [Group G]

@[expose] def chainSub (L : Subgroup G) (b : ℕ → G) : ℕ → Subgroup G
  | 0 => L
  | j + 1 => chainSub L b j ⊓ Subgroup.centralizer {b j}

theorem mem_chainSub {L : Subgroup G} {b : ℕ → G} {x : G} {m : ℕ} :
    x ∈ chainSub L b m ↔ x ∈ L ∧ ∀ i < m, b i * x = x * b i := by
  induction m with
  | zero => simp [chainSub]
  | succ m ih =>
    simp only [chainSub, Subgroup.mem_inf, ih, Subgroup.mem_centralizer_iff,
      Set.mem_singleton_iff, forall_eq]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, fun i hi => by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact h2 i hi
        · exact h3⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, fun i hi => h2 i (by omega)⟩, h2 m (by omega)⟩

theorem card_mul_card_inf_le [Finite G] (L : Subgroup G) (b : G) (n : ℕ) (t : ℕ → G)
    (ht : ∀ k < n, t k ∈ L)
    (hd : ∀ k < n, ∀ k' < n, t k * b * (t k)⁻¹ = t k' * b * (t k')⁻¹ → k = k') :
    n * Nat.card ↥(L ⊓ Subgroup.centralizer {b}) ≤ Nat.card ↥L := by
  classical
  have hs : ∀ s : ↥(L ⊓ Subgroup.centralizer {b}), (s : G) * b * (s : G)⁻¹ = b := by
    intro s
    have := Subgroup.mem_centralizer_iff.1 s.2.2 b (Set.mem_singleton b)
    rw [mul_inv_eq_iff_eq_mul]
    exact this.symm
  let f : Fin n × ↥(L ⊓ Subgroup.centralizer {b}) → ↥L := fun p =>
    ⟨t p.1 * p.2, L.mul_mem (ht _ p.1.2) p.2.2.1⟩
  have hf : Function.Injective f := by
    rintro ⟨k, s⟩ ⟨k', s'⟩ h
    have h1 : t k * (s : G) = t k' * (s' : G) := congrArg Subtype.val h
    have h2 : t k * b * (t k)⁻¹ = t k' * b * (t k')⁻¹ := by
      calc t k * b * (t k)⁻¹ = t k * ((s : G) * b * (s : G)⁻¹) * (t k)⁻¹ := by rw [hs]
        _ = (t k * (s : G)) * b * (t k * (s : G))⁻¹ := by group
        _ = (t k' * (s' : G)) * b * (t k' * (s' : G))⁻¹ := by rw [h1]
        _ = t k' * ((s' : G) * b * (s' : G)⁻¹) * (t k')⁻¹ := by group
        _ = t k' * b * (t k')⁻¹ := by rw [hs]
    have hk : k = k' := Fin.ext (hd k k.2 k' k'.2 h2)
    subst hk
    have : (s : G) = s' := mul_left_cancel h1
    rw [Subtype.ext this]
  have := Nat.card_le_card_of_injective f hf
  simpa [Nat.card_prod] using this

theorem prod_mul_card_chainSub_le [Finite G] (L : Subgroup G) (b : ℕ → G) (cnt : ℕ → ℕ)
    (t : ℕ → ℕ → G) (m : ℕ) (ht : ∀ j < m, ∀ k < cnt j, t j k ∈ chainSub L b j)
    (hd : ∀ j < m, ∀ k < cnt j, ∀ k' < cnt j,
      t j k * b j * (t j k)⁻¹ = t j k' * b j * (t j k')⁻¹ → k = k') :
    (∏ j ∈ Finset.range m, cnt j) * Nat.card ↥(chainSub L b m) ≤ Nat.card ↥L := by
  induction m with
  | zero => simp [chainSub]
  | succ m ih =>
    have ih' := ih (fun j hj => ht j (by omega)) (fun j hj => hd j (by omega))
    have h1 := card_mul_card_inf_le (chainSub L b m) (b m) (cnt m) (t m) (ht m (by omega))
      (hd m (by omega))
    rw [Finset.prod_range_succ]
    calc (∏ j ∈ Finset.range m, cnt j) * cnt m * Nat.card ↥(chainSub L b (m + 1))
        = (∏ j ∈ Finset.range m, cnt j) * (cnt m * Nat.card ↥(chainSub L b m ⊓
          Subgroup.centralizer {b m})) := by rw [mul_assoc]; rfl
      _ ≤ (∏ j ∈ Finset.range m, cnt j) * Nat.card ↥(chainSub L b m) := Nat.mul_le_mul_left _ h1
      _ ≤ Nat.card ↥L := ih'

end ChainBound

@[expose] def sw (w : List ℕ) : J := (w.map fun i => sgen idx1[i]!).prod

theorem sTab_get {i : ℕ} (hi : i < 8) : sTab[i]! = sCols idx1[i]! := by
  unfold sTab
  rw [getElem!_pos _ i (by simpa using hi), Array.getElem_ofFn]

theorem sw_mem_K (w : List ℕ) : sw w ∈ K := by
  refine K.list_prod_mem fun g hg => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  exact sgen_mem_K _

theorem sw_conj : ∀ (w : List ℕ), w.all (· < 8) = true → ∀ a,
    sw w * η a * (sw w)⁻¹ = η (swApp sTab w a)
  | [], _, a => by
    rw [sw, List.map_nil, List.prod_nil, swApp, List.foldr_nil]
    group
  | i :: w, h, a => by
    rw [List.all_cons, Bool.and_eq_true] at h
    have hi : i < 8 := of_decide_eq_true h.1
    have ih := sw_conj w h.2 a
    have e1 : sw (i :: w) = sgen idx1[i]! * sw w := by
      rw [sw, List.map_cons, List.prod_cons, sw]
    have e2 : swApp sTab (i :: w) a = app11 (sCols idx1[i]!) (swApp sTab w a) := by
      rw [swApp, List.foldr_cons, ← swApp, sTab_get hi]
    rw [e1, e2, ← sgen_conj, ← ih]
    group

@[expose] def baseElt (i : ℕ) : J := η chainBase[i]!

@[expose] def trElt (j k : ℕ) : J :=
  if j = 0 then (if h : k < 1771 then Classical.choose (reach1 k h) else 1)
  else sw (chainWords[j - 1]!)[k]!

theorem chain_cnt_prod : (∏ j ∈ Finset.range 7, chainCnt[j]!) = 244823040 := by
  simp [Finset.prod_range_succ, chainCnt]

theorem chain_ht :

    ∀ j < 7, ∀ k < chainCnt[j]!, trElt j k ∈ chainSub K baseElt j := by
  intro j hj k hk
  rw [mem_chainSub]
  by_cases hj0 : j = 0
  · subst hj0
    have hk' : k < 1771 := hk
    refine ⟨?_, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
    rw [trElt, ite_eq_left rfl, dite_eq_left hk']
    exact (Classical.choose_spec (reach1 k hk')).1
  · have hjl : j ∈ [1, 2, 3, 4, 5, 6] := by
      simp only [List.mem_cons, List.not_mem_nil]
      omega
    obtain ⟨-, hc⟩ := chain_check j hjl
    obtain ⟨h8, hfix, -, -⟩ := hc k hk
    rw [trElt, ite_eq_right hj0]
    refine ⟨sw_mem_K _, fun i hi => ?_⟩
    have e := sw_conj _ h8 chainBase[i]!
    rw [hfix i hi] at e
    rw [baseElt]
    calc η chainBase[i]! * sw (chainWords[j - 1]!)[k]! =
          sw (chainWords[j - 1]!)[k]! * η chainBase[i]! * (sw (chainWords[j - 1]!)[k]!)⁻¹ *
            sw (chainWords[j - 1]!)[k]! := by rw [e]
      _ = sw (chainWords[j - 1]!)[k]! * η chainBase[i]! := by group

theorem chain_hd :
    ∀ j < 7, ∀ k < chainCnt[j]!, ∀ k' < chainCnt[j]!,
    trElt j k * baseElt j * (trElt j k)⁻¹ = trElt j k' * baseElt j * (trElt j k')⁻¹ →
      k = k' := by
  intro j hj k hk k' hk' e
  by_cases hj0 : j = 0
  · subst hj0
    have hk1 : k < 1771 := hk
    have hk1' : k' < 1771 := hk'
    rw [trElt, trElt, ite_eq_left rfl, ite_eq_left rfl, dite_eq_left hk1, dite_eq_left hk1',
      baseElt,
      show chainBase[0]! = 1 from rfl, (Classical.choose_spec (reach1 k hk1)).2,
      (Classical.choose_spec (reach1 k' hk1')).2] at e
    by_contra hne
    exact bfsOK_ne orb1_ok hk1 hk1' hne
      (η_injOn (bfsOK_lt orb1_ok hk1) (bfsOK_lt orb1_ok hk1') e)
  · have hjl : j ∈ [1, 2, 3, 4, 5, 6] := by
      simp only [List.mem_cons, List.not_mem_nil]
      omega
    obtain ⟨-, hc⟩ := chain_check j hjl
    obtain ⟨h8, -, hlt, hinj⟩ := hc k hk
    obtain ⟨h8', -, hlt', -⟩ := hc k' hk'
    rw [trElt, trElt, ite_eq_right hj0, ite_eq_right hj0, baseElt, sw_conj _ h8,
      sw_conj _ h8'] at e
    exact hinj k' hk' (η_injOn hlt hlt' e)

theorem eq_one_of_mem_K_of_comm
    {k : J} (hk : k ∈ K) (hc : ∀ i < 7, baseElt i * k = k * baseElt i) :
    k = 1 := by
  have hb := prod_mul_card_chainSub_le K baseElt (fun j => chainCnt[j]!) trElt 7 chain_ht chain_hd
  rw [chain_cnt_prod, card_K] at hb
  have h1 : Nat.card (chainSub K baseElt 7) ≤ 1 := by omega
  have hmem : k ∈ chainSub K baseElt 7 := mem_chainSub.2 ⟨hk, hc⟩
  have hbot := Subgroup.eq_bot_of_card_le (chainSub K baseElt 7) h1
  rw [hbot] at hmem
  exact hmem

theorem base_mem_Tset
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i < 7) : baseElt i ∈ Tset := by
  obtain ⟨h1, h2⟩ := td_check.2.2.2.1 i hi hi1
  obtain ⟨i₁, hi₁, e₁⟩ := List.any_eq_true.1 h1
  obtain ⟨i₂, hi₂, e₂⟩ := List.any_eq_true.1 h2
  rw [beq_iff_eq] at e₁ e₂
  refine ⟨?_, ?_⟩
  · rw [conjOrbit_fourteen]
    exact ⟨i₁, List.mem_range.1 hi₁, by rw [baseElt, e₁]⟩
  · rw [conjOrbit_fourteen, baseElt, ← η_xor]
    exact ⟨i₂, List.mem_range.1 hi₂, by rw [e₂]⟩

theorem not_isComponent_centralizer_η1
    (B : Subgroup (Subgroup.centralizer ({η 1} : Set J))) :
    ¬ CFSG.IsComponent B := by
  intro hB
  have hNX := N_le_centralizer_of_mem (η_mem_N 1)
  set L : Subgroup (Subgroup.centralizer ({η 1} : Set J)) :=
    H.subgroupOf (Subgroup.centralizer ({η 1} : Set J)) with hL
  rcases CFSG.LocalCores.component_normal_subgroup hB (Subgroup.normalCore_normal L) with h | h
  · refine CFSG.LocalCores.not_isComponent_le_of_self_centralizing (L := L)
      (R := N.subgroupOf (Subgroup.centralizer ({η 1} : Set J))) (fun r hr => ?_)
      (fun l hl r hr => ?_) ?_ (fun l hl hc => ?_) hB (h.trans (Subgroup.normalCore_le L))
    · rw [Subgroup.mem_subgroupOf] at hr
      rw [hL, Subgroup.mem_subgroupOf]
      exact N_le_H hr
    · rw [hL, Subgroup.mem_subgroupOf] at hl
      rw [Subgroup.mem_subgroupOf] at hr ⊢
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact conj_mem_N_of_mem_H _ hl _ hr
    · refine Group.isSolvable_of_comm fun p q => Subtype.ext (Subtype.ext ?_)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul]
      exact N_comm _ (Subgroup.mem_subgroupOf.1 p.2) _ (Subgroup.mem_subgroupOf.1 q.2)
    · rw [hL, Subgroup.mem_subgroupOf] at hl
      rw [Subgroup.mem_subgroupOf, ← centralizer_N_inf_H]
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_iff.2 fun n hn => ?_, hl⟩
      have h1 := hc ⟨n, hNX hn⟩ (Subgroup.mem_subgroupOf.2 hn)
      have h2 := congrArg Subtype.val h1
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at h2
      exact h2.symm
  · have hBC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hM : ∀ i < 7, (⟨baseElt i, hNX (η_mem_N _)⟩ : Subgroup.centralizer ({η 1} : Set J)) ∈
        L.normalCore := by
      intro i hi c
      rw [hL, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      show (c : J) * baseElt i * (c : J)⁻¹ ∈ H
      by_cases hi0 : i = 0
      · subst hi0
        have hc := Subgroup.mem_centralizer_singleton_iff.1 c.2
        have e : baseElt 0 = η 1 := rfl
        rw [e, hc, mul_inv_cancel_right]
        exact N_le_H (η_mem_N 1)
      · exact conj_DSub_mem_H c.2 (Subgroup.subset_closure (base_mem_Tset (by omega) hi))
    have hBN : ∀ p ∈ B, ((p : Subgroup.centralizer ({η 1} : Set J)) : J) ∈ N := by
      intro p hp
      have hcomm : ∀ i < 7, baseElt i * (p : J) = (p : J) * baseElt i := by
        intro i hi
        have h1 := Subgroup.mem_centralizer_iff.1 (hBC hp) _ (hM i hi)
        have h2 := congrArg Subtype.val h1
        rw [Subgroup.coe_mul, Subgroup.coe_mul] at h2
        exact h2
      have h14 : (p : J) ∈ Subgroup.centralizer ({η 14} : Set J) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        have := hcomm 1 (by norm_num)
        rw [baseElt, show chainBase[1]! = 14 from rfl] at this
        exact this.symm
      obtain ⟨n, hn, k, hk, hnk⟩ := exists_mul_of_mem_H (centralizer_η14_le_H h14)
      have hk1 : k = 1 := by
        refine eq_one_of_mem_K_of_comm hk fun i hi => ?_
        have h1 := hcomm i hi
        have h2 : baseElt i * n = n * baseElt i := N_comm _ (η_mem_N _) _ hn
        rw [hnk] at h1
        refine mul_left_cancel (a := n) ?_
        calc n * (baseElt i * k) = baseElt i * n * k := by rw [h2, mul_assoc]
          _ = n * k * baseElt i := by rw [mul_assoc, h1]
          _ = n * (k * baseElt i) := by rw [mul_assoc]
      rw [hnk, hk1, mul_one]
      exact hn
    refine CFSG.LocalCores.not_isSolvable_of_isComponent hB
      (Group.isSolvable_of_comm fun p q => Subtype.ext (Subtype.ext ?_))
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    exact N_comm _ (hBN p p.2) _ (hBN q q.2)

end CFSG.Sporadic.J4Schreier.NoComp
