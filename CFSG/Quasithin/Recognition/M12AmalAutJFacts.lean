module

public import CFSG.Quasithin.Recognition.M12AmalAutInst
public import CFSG.Quasithin.Recognition.M12AmalAutJCheck
public import CFSG.Quasithin.Recognition.M12AmalAutIso

public section

namespace CFSG.Quasithin.M12AmalAut

open CFSG.Sporadic.Bridge Equiv CFSG.Open CFSG.Quasithin.AmalTransport

theorem autEq_of_compL {i j k : ℕ} (hi : i < 128) (hj : j < 128) (hk : k < 128)
    (h : compL (tl i) (tl j) = tl k) : telG i * telG j = telG k :=
  eq_of_reprG (reprG_mul (reprG_tel i hi) (reprG_tel j hj))
    (show ReprG (compL (tl i) (tl j)) (telG k) by rw [h]; exact reprG_tel k hk)

theorem telG_mul {i j : ℕ} (hi : i < 128) (hj : j < 128) :
    telG i * telG j = telG (telMul i j) := by
  obtain ⟨hk, he⟩ := telMul_chk i hi j hj
  exact autEq_of_compL hi hj hk he

theorem telG_inv {i : ℕ} (hi : i < 128) : (telG i)⁻¹ = telG (telInv i) := by
  obtain ⟨hk, he⟩ := telInv_chk i hi
  have : telG i * telG (telInv i) = 1 :=
    eq_of_reprG (reprG_mul (reprG_tel i hi) (reprG_tel _ hk))
      (show ReprG (compL (tl i) (tl (telInv i))) 1 by rw [he]; exact reprG_one)
  exact inv_eq_of_mul_eq_one_right this

theorem telG_inj_idx {i j : ℕ} (hi : i < 128) (hj : j < 128) (h : telG i = telG j) : i = j :=
  tl_inj_chk i hi j hj (repL_unique (reprG_tel i hi) (h ▸ reprG_tel j hj))

theorem telG_zero_idx : telG 0 = 1 := tel_zero

theorem telG_mem_T {i : ℕ} (hi : i < 128) : telG i ∈ autData.T :=
  autData.Tel_mem_T (⟨i, hi⟩ : Fin 128)

theorem exists_idx_of_mem_T {g : AutG} (hg : g ∈ autData.T) : ∃ i : ℕ, i < 128 ∧ g = telG i := by
  obtain ⟨i, hi⟩ := (autData.mem_T_iff g).1 hg
  exact ⟨i, i.2, hi.symm⟩

@[expose] def idxSubgroup (L : List ℕ) (h0 : 0 ∈ L) (hlt : ∀ i ∈ L, i < 128)
    (hmul : ∀ i ∈ L, ∀ j ∈ L, telMul i j ∈ L) (hinv : ∀ i ∈ L, telInv i ∈ L) : Subgroup AutG where
  carrier := {g | ∃ i ∈ L, g = telG i}
  one_mem' := ⟨0, h0, telG_zero_idx.symm⟩
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    exact ⟨telMul i j, hmul i hi j hj, telG_mul (hlt i hi) (hlt j hj)⟩
  inv_mem' := by
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨telInv i, hinv i hi, telG_inv (hlt i hi)⟩

@[expose] noncomputable def Esub : Subgroup AutG :=
  idxSubgroup eIdx eIdx_chk.2.2.2.1 eIdx_chk.2.2.1
    (fun i hi j hj => ((eIdx_chk.2.2.2.2 i hi j hj).1)) eIdx_inv_chk

@[expose] noncomputable def Rsub : Subgroup AutG :=
  idxSubgroup rIdx rIdx_chk.2.2.2.1 rIdx_chk.2.2.1 rIdx_chk.2.2.2.2 rIdx_inv_chk

@[expose] noncomputable def ERsub : Subgroup AutG :=
  idxSubgroup erIdx ((erIdx_chk 0 (by norm_num)).2 ⟨eIdx_chk.2.2.2.1, rIdx_chk.2.2.2.1⟩)
    erIdx_lt_chk
    (fun i hi j hj => by
      have hi' := (erIdx_chk i (erIdx_lt_chk i hi)).1 hi
      have hj' := (erIdx_chk j (erIdx_lt_chk j hj)).1 hj
      exact (erIdx_chk _ (telMul_chk i (erIdx_lt_chk i hi) j (erIdx_lt_chk j hj)).1).2
        ⟨(eIdx_chk.2.2.2.2 i hi'.1 j hj'.1).1, rIdx_chk.2.2.2.2 i hi'.2 j hj'.2⟩)
    (fun i hi => by
      have hi' := (erIdx_chk i (erIdx_lt_chk i hi)).1 hi
      exact (erIdx_chk _ (telInv_chk i (erIdx_lt_chk i hi)).1).2
        ⟨eIdx_inv_chk i hi'.1, rIdx_inv_chk i hi'.2⟩)

theorem ERsub_eq : ERsub = Esub ⊓ Rsub := by
  ext g
  constructor
  · rintro ⟨i, hi, rfl⟩
    obtain ⟨he, hr⟩ := (erIdx_chk i (erIdx_lt_chk i hi)).1 hi
    exact ⟨⟨i, he, rfl⟩, ⟨i, hr, rfl⟩⟩
  · rintro ⟨⟨i, hi, rfl⟩, ⟨j, hj, hij⟩⟩
    have hi128 := eIdx_chk.2.2.1 i hi
    have hj128 := rIdx_chk.2.2.1 j hj
    have : i = j := telG_inj_idx hi128 hj128 hij
    subst this
    exact ⟨i, (erIdx_chk i hi128).2 ⟨hi, hj⟩, rfl⟩

theorem Esub_le_T : Esub ≤ autData.T := by
  rintro _ ⟨i, hi, rfl⟩
  exact telG_mem_T (eIdx_chk.2.2.1 i hi)

theorem Rsub_le_T : Rsub ≤ autData.T := by
  rintro _ ⟨i, hi, rfl⟩
  exact telG_mem_T (rIdx_chk.2.2.1 i hi)

theorem card_mem_list (X : List ℕ) (hX : X.Nodup) : Nat.card {i // i ∈ X} = X.length := by
  have e : Fin X.attach.length ≃ {i // i ∈ X} :=
    List.Nodup.getEquivOfForallMemList X.attach (hX.attach) (fun x => List.mem_attach X x)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin, List.length_attach]

theorem card_of_idx {B : Subgroup AutG} {X : List ℕ} (hX : X.Nodup) (hlt : ∀ i ∈ X, i < 128)
    (hB : ∀ g, g ∈ B ↔ ∃ i ∈ X, g = telG i) : Nat.card B = X.length := by
  have hinj : Function.Injective (fun i : {i // i ∈ X} => telG i.1) := fun i j h =>
    Subtype.ext (telG_inj_idx (hlt _ i.2) (hlt _ j.2) h)
  have hrange : Set.range (fun i : {i // i ∈ X} => telG i.1) = (B : Set AutG) := by
    ext g
    simp only [Set.mem_range, SetLike.mem_coe, hB]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i.1, i.2, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨⟨i, hi⟩, rfl⟩
  have h1 : Nat.card B = Nat.card (Set.range (fun i : {i // i ∈ X} => telG i.1)) := by
    rw [hrange]
    rfl
  rw [h1, Nat.card_range_of_injective hinj, card_mem_list X hX]

theorem card_Esub : Nat.card Esub = 16 := by
  rw [card_of_idx eIdx_chk.2.1 eIdx_chk.2.2.1 (fun g => Iff.rfl)]
  exact eIdx_chk.1

theorem card_Rsub : Nat.card Rsub = 64 := by
  rw [card_of_idx rIdx_chk.2.1 rIdx_chk.2.2.1 (fun g => Iff.rfl)]
  exact rIdx_chk.1

theorem Esub_elem : IsElemAbelian 2 Esub := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨x, i, hi, rfl⟩ := x
    obtain ⟨y, j, hj, rfl⟩ := y
    apply Subtype.ext
    show telG i * telG j = telG j * telG i
    have hi' := eIdx_chk.2.2.1 i hi
    have hj' := eIdx_chk.2.2.1 j hj
    rw [telG_mul hi' hj', telG_mul hj' hi', (eIdx_chk.2.2.2.2 i hi j hj).2.1]
  · rintro _ ⟨i, hi, rfl⟩
    have hi' := eIdx_chk.2.2.1 i hi
    rw [pow_two, telG_mul hi' hi', (eIdx_chk.2.2.2.2 i hi i hi).2.2]
    exact telG_zero_idx

theorem sorted_ext_mem (X : List ℕ) (u i : ℕ) :
    i ∈ extList X u ↔ i ∈ X ∨ ∃ j ∈ X, telMul j u = i := by
  unfold extList
  rw [mem_sortList, List.mem_append, List.mem_map]

theorem elemAbelian_mem_fam : ∀ (n : ℕ) (B : Subgroup AutG), B ≤ autData.T → IsElemAbelian 2 B →
    Nat.card B = n → ∃ X ∈ famTab, ∀ g, g ∈ B ↔ ∃ i ∈ X, g = telG i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro B hBT hel hn
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases h1 : n = 1
  ·
    have hB : B = ⊥ := Subgroup.eq_bot_of_card_eq B (hn.trans h1)
    refine ⟨[0], famTab_zero_chk, fun g => ?_⟩
    rw [hB, Subgroup.mem_bot]
    constructor
    · rintro rfl
      exact ⟨0, by simp, telG_zero_idx.symm⟩
    · rintro ⟨i, hi, rfl⟩
      simp only [List.mem_singleton] at hi
      subst hi
      exact telG_zero_idx
  ·
    have hp : IsPGroup 2 ↥B := fun x => ⟨1, Subtype.ext (by simpa using hel.2 x x.2)⟩
    obtain ⟨m, hm⟩ := hp.exists_card_eq
    have hn0 : n ≠ 0 := by
      intro h0
      rw [h0] at hn
      exact Nat.card_pos.ne' hn
    have hm0 : m ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hm
      exact h1 (hn.symm.trans hm)
    obtain ⟨B'', hB''card, -, hB''le⟩ :=
      Sylow.exists_subgroup_card_pow_prime_le_le (p := 2) Nat.prime_two (n := m - 1)
        (H := ⊥) (L := B) (by simp) (by
          rw [hm]
          exact pow_dvd_pow 2 (Nat.sub_le m 1)) bot_le
    have hBcard : Nat.card B = 2 * Nat.card B'' := by
      rw [hm, hB''card, ← pow_succ']
      congr 1
      omega
    have hB''lt : Nat.card B'' < n := by
      have := Nat.card_pos (α := ↥B'')
      omega
    obtain ⟨X', hX'fam, hX'⟩ := ih _ hB''lt B'' (hB''le.trans hBT) (isElemAbelian_mono hB''le hel) rfl
    obtain ⟨b, hbB, hbB''⟩ : ∃ b ∈ B, b ∉ B'' := by
      by_contra hcon
      push Not at hcon
      have := Subgroup.card_le_of_le (show B ≤ B'' from hcon)
      have := Nat.card_pos (α := ↥B'')
      omega
    obtain ⟨u, hu128, rfl⟩ := exists_idx_of_mem_T (hBT hbB)
    have hX'lt : ∀ i ∈ X', i < 128 := by
      have := famTab_bound_chk X' hX'fam
      exact this.2.2.2.1
    have hb1 : u ≠ 0 := fun h => hbB'' (by rw [h, telG_zero_idx]; exact B''.one_mem)
    have hb2 : telMul u u = 0 := by
      have hsq : telG u * telG u = 1 := by
        rw [← pow_two]
        exact hel.2 _ hbB
      rw [telG_mul hu128 hu128, ← telG_zero_idx] at hsq
      exact telG_inj_idx (telMul_chk u hu128 u hu128).1 (by norm_num) hsq
    have huinv : u ∈ invIdx := (invIdx_chk u hu128).1 ⟨hb1, hb2⟩
    have hunot : u ∉ X' := fun hu => hbB'' ((hX' _).2 ⟨u, hu, rfl⟩)
    have hcomm : ∀ j ∈ X', telMul u j = telMul j u := by
      intro j hj
      have hjB : telG j ∈ B := hB''le ((hX' _).2 ⟨j, hj, rfl⟩)
      have hc := hel.1.is_comm.comm (⟨telG u, hbB⟩ : B) ⟨telG j, hjB⟩
      have hc' : telG u * telG j = telG j * telG u := congrArg Subtype.val hc
      rw [telG_mul hu128 (hX'lt j hj), telG_mul (hX'lt j hj) hu128] at hc'
      exact telG_inj_idx (telMul_chk u hu128 j (hX'lt j hj)).1 (telMul_chk j (hX'lt j hj) u hu128).1 hc'
    refine ⟨extList X' u, famTab_ext_chk X' hX'fam u huinv hunot hcomm, fun g => ?_⟩
    simp only [sorted_ext_mem]
    have hidx : (B''.subgroupOf B).index = 2 := by
      have h := Subgroup.card_mul_index (B''.subgroupOf B)
      have e : Nat.card (B''.subgroupOf B) = Nat.card B'' :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB''le).toEquiv
      rw [e] at h
      have hpos : 0 < Nat.card B'' := Nat.card_pos
      exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h, hBcard]; ring)
    constructor
    · intro hg
      by_cases hgB'' : g ∈ B''
      · obtain ⟨i, hi, rfl⟩ := (hX' g).1 hgB''
        exact ⟨i, Or.inl hi, rfl⟩
      · have hmem : g * (telG u)⁻¹ ∈ B'' := by
          have ha : (⟨g, hg⟩ : B) ∉ B''.subgroupOf B := hgB''
          have hb : (⟨telG u, hbB⟩ : B)⁻¹ ∉ B''.subgroupOf B := by
            rw [Subgroup.inv_mem_iff]
            exact hbB''
          have h := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨g, hg⟩ : B))
            (b := (⟨telG u, hbB⟩ : B)⁻¹)).2 ⟨fun h => absurd h ha, fun h => absurd h hb⟩
          exact Subgroup.mem_subgroupOf.1 h
        obtain ⟨j, hj, hjeq⟩ := (hX' _).1 hmem
        refine ⟨telMul j u, Or.inr ⟨j, hj, rfl⟩, ?_⟩
        rw [← telG_mul (hX'lt j hj) hu128, ← hjeq]
        group
    · rintro ⟨i, hi | ⟨j, hj, rfl⟩, rfl⟩
      · exact hB''le ((hX' _).2 ⟨i, hi, rfl⟩)
      · rw [← telG_mul (hX'lt j hj) hu128]
        exact B.mul_mem (hB''le ((hX' _).2 ⟨j, hj, rfl⟩)) hbB

theorem thompsonJ_T : thompsonJ autData.T = Esub := by
  have hEmax : IsMaxElemAbelian autData.T Esub := by
    refine ⟨Esub_le_T, Esub_elem, fun B hBT hB => ?_⟩
    obtain ⟨X, hXfam, hX⟩ := elemAbelian_mem_fam _ B hBT hB rfl
    obtain ⟨hlen, -, hnd, hlt, -⟩ := famTab_bound_chk X hXfam
    rw [card_of_idx hnd hlt hX, card_Esub]
    exact hlen
  apply le_antisymm
  · refine iSup_le fun A => iSup_le fun hA => ?_
    obtain ⟨hAT, hAel, hAmax⟩ := hA
    have h16 : 16 ≤ Nat.card A := by
      have := hAmax Esub Esub_le_T Esub_elem
      rwa [card_Esub] at this
    obtain ⟨X, hXfam, hX⟩ := elemAbelian_mem_fam _ A hAT hAel rfl
    obtain ⟨hlen, hX16, hnd, hlt, -⟩ := famTab_bound_chk X hXfam
    have hcard := card_of_idx hnd hlt hX
    have hXe : X = eIdx := hX16 (by omega)
    intro g hg
    obtain ⟨i, hi, rfl⟩ := (hX g).1 hg
    exact ⟨i, hXe ▸ hi, rfl⟩
  · exact le_iSup₂_of_le Esub hEmax le_rfl

theorem closure_le_normalizer_of_conj' {G : Type*} [Group G] (S : Set G) (K : Subgroup G)
    (h : ∀ s ∈ S, ∀ k ∈ K, s * k * s⁻¹ ∈ K ∧ s⁻¹ * k * s ∈ K) :
    Subgroup.closure S ≤ Subgroup.normalizer (K : Set G) := by
  refine (Subgroup.closure_le _).2 fun s hs => ?_
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro k
  refine ⟨fun hk => (h s hs k hk).1, fun hk => ?_⟩
  have := (h s hs _ hk).2
  have e : s⁻¹ * (s * k * s⁻¹) * s = k := by group
  rwa [e] at this

theorem B_le_normalizer_idx {L : List ℕ} {h0 : 0 ∈ L} {hlt : ∀ i ∈ L, i < 128}
    {hmul : ∀ i ∈ L, ∀ j ∈ L, telMul i j ∈ L} {hinv : ∀ i ∈ L, telInv i ∈ L} (hN : NormOK L) :
    autData.B ≤ Subgroup.normalizer
      (idxSubgroup L h0 hlt hmul hinv : Set AutG) := by
  show Subgroup.closure ({genG 0, genG 1, genG 2, genG 4} : Set AutG) ≤ _
  refine closure_le_normalizer_of_conj' _ _ ?_
  intro s hs k hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hj128 := hlt j hj
  have key : ∀ g : ℕ, g ∈ [0, 1, 2, 4] → s = genG g →
      s * telG j * s⁻¹ ∈ idxSubgroup L h0 hlt hmul hinv ∧
        s⁻¹ * telG j * s ∈ idxSubgroup L h0 hlt hmul hinv := by
    intro g hg hsg
    subst hsg
    obtain ⟨⟨k₁, hk₁, hl₁⟩, ⟨k₂, hk₂, hl₂⟩⟩ := hN g hg j hj
    have hg5 : g < 5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      omega
    have r1 : ReprG (compL (compL (gl g) (tl j)) (gil g)) (genG g * telG j * (genG g)⁻¹) :=
      reprG_mul (reprG_mul (reprG_gen g hg5) (reprG_tel j hj128)) (reprG_inv_gen g hg5)
    have r2 : ReprG (compL (compL (gil g) (tl j)) (gl g)) ((genG g)⁻¹ * telG j * genG g) :=
      reprG_mul (reprG_mul (reprG_inv_gen g hg5) (reprG_tel j hj128)) (reprG_gen g hg5)
    exact ⟨⟨k₁, hk₁, eq_of_reprG r1 (by rw [hl₁]; exact reprG_tel k₁ (hlt k₁ hk₁))⟩,
      ⟨k₂, hk₂, eq_of_reprG r2 (by rw [hl₂]; exact reprG_tel k₂ (hlt k₂ hk₂))⟩⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with h | h | h | h
  · exact key 0 (by simp) h
  · exact key 1 (by simp) h
  · exact key 2 (by simp) h
  · exact key 4 (by simp) h

theorem dG_mem_A (j : ℕ) (hj : j = 0 ∨ j = 1) : dG j ∈ autData.A := by
  rcases hj with rfl | rfl
  · rw [d_zero]
    exact autData.A.one_mem
  · rw [dG_one]
    exact autData.x_mem_A

theorem dG_mem_B (j : ℕ) (hj : j = 0 ∨ j = 2) : dG j ∈ autData.B := by
  rcases hj with rfl | rfl
  · rw [d_zero]
    exact autData.B.one_mem
  · rw [dG_two]
    exact autData.y_mem_B

theorem fusion_of_path : ∀ (p : List (ℕ × ℕ × ℕ × ℕ × ℕ)) (s : ℕ), pathEndB s p = true →
    ∃ t ∈ erIdx, AmalFusion autData.A autData.B (telG s) (telG t) := by
  intro p
  induction p with
  | nil =>
    intro s h
    exact ⟨s, pathEndB_nil h, Relation.ReflTransGen.refl⟩
  | cons st rest ih =>
    intro s h
    obtain ⟨hstep, hrest⟩ := pathEndB_cons h
    obtain ⟨t, ht, hf⟩ := ih st.1 hrest
    refine ⟨t, ht, Relation.ReflTransGen.head ?_ hf⟩
    obtain ⟨hs, hdst, hi1, hi2, hj, hgrp, he⟩ := hstep
    obtain ⟨dst, grp, i1, j, i2⟩ := st
    simp only at hs hdst hi1 hi2 hj hgrp he ⊢
    have hAB : autData.A ⊓ autData.B = autData.T := autData.inf_AB
    have hsT : telG s ∈ autData.A ⊓ autData.B := by rw [hAB]; exact telG_mem_T hs
    have hdT : telG dst ∈ autData.A ⊓ autData.B := by rw [hAB]; exact telG_mem_T hdst
    refine ⟨hsT, hdT, ?_⟩
    have hconj : telG i1 * dG j * telG i2 * telG s * (telG i1 * dG j * telG i2)⁻¹ = telG dst := by
      have hinv : (telG i1 * dG j * telG i2)⁻¹ = (telG i2)⁻¹ * (dG j)⁻¹ * (telG i1)⁻¹ := by
        group
      have e1 : ReprG (tl (telInv i2)) (telG i2)⁻¹ := by
        rw [telG_inv hi2]; exact reprG_tel _ (telInv_chk i2 hi2).1
      have e2 : ReprG (tl (telInv i1)) (telG i1)⁻¹ := by
        rw [telG_inv hi1]; exact reprG_tel _ (telInv_chk i1 hi1).1
      have e4 := reprG_mul (reprG_mul (reprG_tel i1 hi1) (reprG_d j hj)) (reprG_tel i2 hi2)
      have r : ReprG (compL (compL (compL (compL (tl i1) (dTab.getD j [])) (tl i2)) (tl s))
          (compL (compL (tl (telInv i2)) (dInvTab.getD j [])) (tl (telInv i1))))
          (telG i1 * dG j * telG i2 * telG s * (telG i1 * dG j * telG i2)⁻¹) := by
        rw [hinv]
        exact reprG_mul (reprG_mul e4 (reprG_tel s hs))
          (reprG_mul (reprG_mul e1 (reprG_dInv j hj)) e2)
      rw [he] at r
      exact eq_of_reprG r (reprG_tel dst hdst)
    rcases hgrp with ⟨rfl, hj'⟩ | ⟨rfl, hj'⟩
    · left
      refine ⟨telG i1 * dG j * telG i2, ?_, hconj⟩
      exact autData.A.mul_mem (autData.A.mul_mem (autData.T_le_A (telG_mem_T hi1)) (dG_mem_A j hj'))
        (autData.T_le_A (telG_mem_T hi2))
    · right
      refine ⟨telG i1 * dG j * telG i2, ?_, hconj⟩
      exact autData.B.mul_mem (autData.B.mul_mem (autData.T_le_B (telG_mem_T hi1)) (dG_mem_B j hj'))
        (autData.T_le_B (telG_mem_T hi2))

theorem autConcl_model : AutConcl autData.A autData.B := by
  have hAB : autData.A ⊓ autData.B = autData.T := autData.inf_AB
  unfold AutConcl
  rw [hAB, thompsonJ_T]
  have hER : ∀ j, j ∈ Esub ⊓ Rsub ↔ j ∈ ERsub := fun j => by rw [ERsub_eq]
  refine ⟨Rsub, Rsub_le_T, ?_, Esub_elem, ?_, ?_, ?_, ?_⟩
  ·
    have h := Subgroup.card_mul_index (Rsub.subgroupOf autData.T)
    have e : Nat.card (Rsub.subgroupOf autData.T) = Nat.card Rsub :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe Rsub_le_T).toEquiv
    rw [e, card_Rsub, aut_card_T] at h
    show (Rsub.subgroupOf autData.T).index = 2
    omega
  · exact B_le_normalizer_idx E_norm_chk
  · obtain ⟨i, hiE, hiR⟩ := eNotR_chk
    refine ⟨telG i, ⟨i, hiE, rfl⟩, ?_⟩
    rintro ⟨i', hi', hii'⟩
    exact hiR (by
      have := telG_inj_idx (eIdx_chk.2.2.1 i hiE) (rIdx_chk.2.2.1 i' hi') hii'
      rwa [this])
  ·
    intro j hjE hjR y hy
    have hN : autData.B ≤ Subgroup.normalizer (ERsub : Set AutG) :=
      B_le_normalizer_idx ER_norm_chk
    have hNE : autData.B ≤ Subgroup.normalizer (Esub : Set AutG) :=
      B_le_normalizer_idx E_norm_chk
    intro hyR
    have hyE : y * j * y⁻¹ ∈ Esub := (Subgroup.mem_normalizer_iff.1 (hNE hy) j).1 hjE
    have hyER : y * j * y⁻¹ ∈ ERsub := by rw [ERsub_eq]; exact ⟨hyE, hyR⟩
    have hjER : j ∈ ERsub := (Subgroup.mem_normalizer_iff.1 (hN hy) j).2 hyER
    rw [ERsub_eq] at hjER
    exact hjR hjER.2
  ·
    intro r hr hr2
    obtain ⟨i, hi, rfl⟩ := hr
    have hi128 := rIdx_chk.2.2.1 i hi
    have hsq : telMul i i = 0 := by
      have : telG i * telG i = 1 := by rw [← pow_two]; exact hr2
      rw [telG_mul hi128 hi128, ← telG_zero_idx] at this
      exact telG_inj_idx (telMul_chk i hi128 i hi128).1 (by norm_num) this
    rcases rInv_chk i hi hsq with rfl | hinv
    · refine ⟨telG 0, ?_, Relation.ReflTransGen.refl⟩
      rw [hER]
      exact ⟨0, (erIdx_chk 0 (by norm_num)).2 ⟨eIdx_chk.2.2.2.1, rIdx_chk.2.2.2.1⟩, rfl⟩
    · obtain ⟨k, hk, hkeq⟩ := List.mem_iff_getElem.1 hinv
      have hk27 : k < 27 := by have := invRIdx_len.1; omega
      have hpath := fuse_chk k hk27
      rw [List.getD_eq_getElem _ _ hk, hkeq] at hpath
      obtain ⟨t, ht, hf⟩ := fusion_of_path _ _ hpath
      refine ⟨telG t, ?_, hf⟩
      rw [hER]
      exact ⟨t, ht, rfl⟩

end CFSG.Quasithin.M12AmalAut
