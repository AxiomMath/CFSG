module

public import CFSG.Quasithin.Recognition.M12AmalFacts
public import CFSG.Quasithin.Recognition.M12AmalE8Check
public import CFSG.Quasithin.Recognition.M12AmalE8Iso

public section

namespace CFSG.Quasithin.M12AmalE8

open CFSG.Sporadic.Bridge Equiv CFSG.Open CFSG.Quasithin.AmalTransport CFSG.QuasithinUnique
  CFSG.Quasithin.M12Amal

theorem telG_mul {i j : ℕ} (hi : i < 64) (hj : j < 64) : telG i * telG j = telG (tmul i j) := by
  obtain ⟨hk, he⟩ := tmul_chk i hi j hj
  exact eq_of_compL_eq hi hj hk he

theorem telG_inv {i : ℕ} (hi : i < 64) : (telG i)⁻¹ = telG (tinv i) := by
  obtain ⟨hk, he⟩ := tinv_chk i hi
  have : telG i * telG (tinv i) = 1 :=
    eq_of_reprG (reprG_mul (reprG_tel i hi) (reprG_tel _ hk))
      (show ReprG (compL (tl i) (tl (tinv i))) 1 by rw [he]; exact reprG_one)
  exact inv_eq_of_mul_eq_one_right this

theorem telG_inj_idx {i j : ℕ} (hi : i < 64) (hj : j < 64) (h : telG i = telG j) : i = j :=
  tl_inj_chk i hi j hj (repL_unique (reprG_tel i hi) (h ▸ reprG_tel j hj))

theorem telG_zero_idx : telG 0 = 1 := tel_zero

theorem telG_mem_T {i : ℕ} (hi : i < 64) : telG i ∈ m12Data.T :=
  m12Data.Tel_mem_T (⟨i, hi⟩ : Fin 64)

theorem telG_sq_eq_one_iff {i : ℕ} (hi : i < 64) : telG i ^ 2 = 1 ↔ tmul i i = 0 := by
  rw [pow_two, telG_mul hi hi, ← telG_zero_idx]
  exact ⟨fun h => telG_inj_idx (tmul_chk i hi i hi).1 (by norm_num) h, fun h => by rw [h]⟩

@[expose] def idxSubgroup (L : List ℕ) (h0 : 0 ∈ L) (hlt : ∀ i ∈ L, i < 64)
    (hmul : ∀ i ∈ L, ∀ j ∈ L, tmul i j ∈ L) (hinv : ∀ i ∈ L, tinv i ∈ L) : Subgroup M12G where
  carrier := {g | ∃ i ∈ L, g = telG i}
  one_mem' := ⟨0, h0, telG_zero_idx.symm⟩
  mul_mem' := by
    rintro _ _ ⟨i, hi, rfl⟩ ⟨j, hj, rfl⟩
    exact ⟨tmul i j, hmul i hi j hj, telG_mul (hlt i hi) (hlt j hj)⟩
  inv_mem' := by
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨tinv i, hinv i hi, telG_inv (hlt i hi)⟩

theorem card_mem_list (X : List ℕ) (hX : X.Nodup) : Nat.card {i // i ∈ X} = X.length := by
  have e : Fin X.attach.length ≃ {i // i ∈ X} :=
    List.Nodup.getEquivOfForallMemList X.attach (hX.attach) (fun x => List.mem_attach X x)
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin, List.length_attach]

theorem card_of_idx {B : Subgroup M12G} {X : List ℕ} (hX : X.Nodup) (hlt : ∀ i ∈ X, i < 64)
    (hB : ∀ g, g ∈ B ↔ ∃ i ∈ X, g = telG i) : Nat.card B = X.length := by
  have hinj : Function.Injective (fun i : {i // i ∈ X} => telG i.1) := fun i j h =>
    Subtype.ext (telG_inj_idx (hlt _ i.2) (hlt _ j.2) h)
  have hrange : Set.range (fun i : {i // i ∈ X} => telG i.1) = (B : Set M12G) := by
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

theorem genG_mem_B {k : ℕ} (hk : k ∈ [0, 1, 2, 4]) : genG k ∈ m12Data.B := by
  show genG k ∈ Subgroup.closure ({genG 0, genG 1, genG 2, genG 4} : Set M12G)
  apply Subgroup.subset_closure
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> simp

theorem conj_gen_idx {k : ℕ} (hk : k < 5) {j i : ℕ} (hj : j < 64) (hi : i < 64)
    (h : genG k * telG j * (genG k)⁻¹ = telG i) :
    compL (compL (gl k) (tl j)) (gil k) = tl i := by
  have r1 : ReprG (compL (compL (gl k) (tl j)) (gil k)) (genG k * telG j * (genG k)⁻¹) :=
    reprG_mul (reprG_mul (reprG_gen k hk) (reprG_tel j hj)) (reprG_inv_gen k hk)
  rw [h] at r1
  exact repL_unique r1 (reprG_tel i hi)

theorem normFwd_of_le_normalizer {H Q : Subgroup M12G} {L : List ℕ} (hlt : ∀ i ∈ L, i < 64)
    (hQL : ∀ g, g ∈ Q ↔ ∃ i ∈ L, g = telG i) {gs : List ℕ}
    (hgs : ∀ k ∈ gs, k < 5 ∧ genG k ∈ H) (hN : H ≤ Subgroup.normalizer (Q : Set M12G)) :
    NormFwd gs L := by
  intro k hk j hj
  obtain ⟨hk5, hkH⟩ := hgs k hk
  have hjQ : telG j ∈ Q := (hQL _).2 ⟨j, hj, rfl⟩
  have h1 : genG k * telG j * (genG k)⁻¹ ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.1 (hN hkH) (telG j)).1 hjQ
    exact this
  obtain ⟨i', hi', hi'e⟩ := (hQL _).1 h1
  exact ⟨i', hi', conj_gen_idx hk5 (hlt j hj) (hlt i' hi') hi'e⟩

theorem A_le_normalizer_idx {L : List ℕ} {h0 : 0 ∈ L} {hlt : ∀ i ∈ L, i < 64}
    {hmul : ∀ i ∈ L, ∀ j ∈ L, tmul i j ∈ L} {hinv : ∀ i ∈ L, tinv i ∈ L}
    (hN : NormBoth [0, 1, 2, 3] L) :
    m12Data.A ≤ Subgroup.normalizer (idxSubgroup L h0 hlt hmul hinv : Set M12G) := by
  show Subgroup.closure ({genG 0, genG 1, genG 2, genG 3} : Set M12G) ≤ _
  refine closure_le_normalizer_of_conj _ _ ?_
  intro s hs k hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hj64 := hlt j hj
  have key : ∀ g : ℕ, g ∈ [0, 1, 2, 3] → s = genG g →
      s * telG j * s⁻¹ ∈ idxSubgroup L h0 hlt hmul hinv ∧
        s⁻¹ * telG j * s ∈ idxSubgroup L h0 hlt hmul hinv := by
    intro g hg hsg
    subst hsg
    obtain ⟨⟨k₁, hk₁, hl₁⟩, ⟨k₂, hk₂, hl₂⟩⟩ := hN g hg j hj
    have hg5 : g < 5 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      omega
    have r1 : ReprG (compL (compL (gl g) (tl j)) (gil g)) (genG g * telG j * (genG g)⁻¹) :=
      reprG_mul (reprG_mul (reprG_gen g hg5) (reprG_tel j hj64)) (reprG_inv_gen g hg5)
    have r2 : ReprG (compL (compL (gil g) (tl j)) (gl g)) ((genG g)⁻¹ * telG j * genG g) :=
      reprG_mul (reprG_mul (reprG_inv_gen g hg5) (reprG_tel j hj64)) (reprG_gen g hg5)
    exact ⟨⟨k₁, hk₁, eq_of_reprG r1 (by rw [hl₁]; exact reprG_tel k₁ (hlt k₁ hk₁))⟩,
      ⟨k₂, hk₂, eq_of_reprG r2 (by rw [hl₂]; exact reprG_tel k₂ (hlt k₂ hk₂))⟩⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with h | h | h | h
  · exact key 0 (by simp) h
  · exact key 1 (by simp) h
  · exact key 2 (by simp) h
  · exact key 3 (by simp) h

theorem B_le_normalizer_idx {L : List ℕ} {h0 : 0 ∈ L} {hlt : ∀ i ∈ L, i < 64}
    {hmul : ∀ i ∈ L, ∀ j ∈ L, tmul i j ∈ L} {hinv : ∀ i ∈ L, tinv i ∈ L}
    (hN : NormBoth [0, 1, 2, 4] L) :
    m12Data.B ≤ Subgroup.normalizer (idxSubgroup L h0 hlt hmul hinv : Set M12G) := by
  show Subgroup.closure ({genG 0, genG 1, genG 2, genG 4} : Set M12G) ≤ _
  refine closure_le_normalizer_of_conj _ _ ?_
  intro s hs k hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hj64 := hlt j hj
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
      reprG_mul (reprG_mul (reprG_gen g hg5) (reprG_tel j hj64)) (reprG_inv_gen g hg5)
    have r2 : ReprG (compL (compL (gil g) (tl j)) (gl g)) ((genG g)⁻¹ * telG j * genG g) :=
      reprG_mul (reprG_mul (reprG_inv_gen g hg5) (reprG_tel j hj64)) (reprG_gen g hg5)
    exact ⟨⟨k₁, hk₁, eq_of_reprG r1 (by rw [hl₁]; exact reprG_tel k₁ (hlt k₁ hk₁))⟩,
      ⟨k₂, hk₂, eq_of_reprG r2 (by rw [hl₂]; exact reprG_tel k₂ (hlt k₂ hk₂))⟩⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with h | h | h | h
  · exact key 0 (by simp) h
  · exact key 1 (by simp) h
  · exact key 2 (by simp) h
  · exact key 4 (by simp) h

@[expose] noncomputable def LAsub : Subgroup M12G :=
  idxSubgroup laIdx laIdx_chk.2.2.2.1 laIdx_chk.2.2.1 laIdx_chk.2.2.2.2 laIdx_inv_chk

theorem LAsub_le_T : LAsub ≤ m12Data.T := by
  rintro _ ⟨i, hi, rfl⟩
  exact telG_mem_T (laIdx_chk.2.2.1 i hi)

theorem pCoreOf_A_eq : CFSG.Open.pCoreOf 2 m12Data.A = LAsub := by
  apply le_antisymm
  · intro g hg
    obtain ⟨i, rfl⟩ := core_tel m12Data.T_le_A hg
    exact ⟨i, (laIdx_iff_chk i i.2).1 (LAp_of_mem_core hg), rfl⟩
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (LAsub_le_T.trans m12Data.T_le_A) (A_le_normalizer_idx laIdx_norm_chk)
      (isPGroup_T.to_le LAsub_le_T)

theorem pCoreOf_A_le_inf : CFSG.Open.pCoreOf 2 m12Data.A ≤ m12Data.A ⊓ m12Data.B := by
  rw [m12Data.inf_AB, pCoreOf_A_eq]
  exact LAsub_le_T

@[expose] noncomputable def ERsub : Subgroup M12G :=
  idxSubgroup erIdx erIdx_chk.2.2.2.1 (fun i hi => laIdx_chk.2.2.1 i (erIdx_chk.2.2.1 i hi))
    (fun i hi j hj => (erIdx_chk.2.2.2.2 i hi j hj).1) erIdx_inv_chk

theorem ERsub_le_LAsub : ERsub ≤ LAsub := by
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨i, erIdx_chk.2.2.1 i hi, rfl⟩

theorem ERsub_elem : IsElemAbelian 2 ERsub := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · obtain ⟨x, i, hi, rfl⟩ := x
    obtain ⟨y, j, hj, rfl⟩ := y
    apply Subtype.ext
    show telG i * telG j = telG j * telG i
    have hi' := laIdx_chk.2.2.1 i (erIdx_chk.2.2.1 i hi)
    have hj' := laIdx_chk.2.2.1 j (erIdx_chk.2.2.1 j hj)
    rw [telG_mul hi' hj', telG_mul hj' hi', (erIdx_chk.2.2.2.2 i hi j hj).2.1]
  · rintro _ ⟨i, hi, rfl⟩
    have hi' := laIdx_chk.2.2.1 i (erIdx_chk.2.2.1 i hi)
    rw [pow_two, telG_mul hi' hi', (erIdx_chk.2.2.2.2 i hi i hi).2.2]
    exact telG_zero_idx

theorem card_ERsub : Nat.card ERsub = 8 := by
  rw [card_of_idx erIdx_chk.2.1 (fun i hi => laIdx_chk.2.2.1 i (erIdx_chk.2.2.1 i hi))
    (fun g => Iff.rfl)]
  exact erIdx_chk.1

theorem B_le_normalizer_ERsub : m12Data.B ≤ Subgroup.normalizer (ERsub : Set M12G) :=
  B_le_normalizer_idx erIdx_norm_chk

theorem V4_le_ERsub (V : Subgroup M12G) (hVP : V ≤ LAsub) (hV4 : Nat.card V = 4)
    (hN : m12Data.B ≤ Subgroup.normalizer (V : Set M12G)) : V ≤ ERsub := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ : ∃ a : ↥V, orderOf a = 2 :=
    exists_prime_orderOf_dvd_card' 2 (by rw [hV4]; norm_num)
  have ha2 : a ^ 2 = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; omega
  obtain ⟨b, hb1, hba⟩ : ∃ b : ↥V, b ≠ 1 ∧ b ≠ a := by
    by_contra hcon
    push Not at hcon
    have hsurj : Function.Surjective (fun t : Bool => if t then (1 : ↥V) else a) := by
      intro v
      by_cases hv : v = 1
      · exact ⟨true, by simp [hv]⟩
      · exact ⟨false, by simp [hcon v hv]⟩
    have := Nat.card_le_card_of_surjective _ hsurj
    rw [hV4, Nat.card_eq_fintype_card, Fintype.card_bool] at this
    omega
  have haa : a * a = 1 := by rw [← pow_two]; exact ha2
  have hab1 : a * b ≠ 1 := by
    intro h
    apply hba
    have h1 : a⁻¹ = b := mul_eq_one_iff_inv_eq.1 h
    have h2 : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
    exact h1.symm.trans h2
  have hab2 : a * b ≠ a := fun h => hb1 (by simpa using h)
  have hab3 : a * b ≠ b := fun h => ha1 (by simpa using h)
  have hall : ∀ v : ↥V, v = 1 ∨ v = a ∨ v = b ∨ v = a * b := by
    have : Fintype ↥V := Fintype.ofFinite _
    have hcard : Fintype.card ↥V = 4 := by rw [← Nat.card_eq_fintype_card]; exact hV4
    have n1 : (1 : ↥V) ∉ ({a, b, a * b} : Finset ↥V) := by
      simp [ha1.symm, hb1.symm, hab1.symm]
    have n2 : a ∉ ({b, a * b} : Finset ↥V) := by
      simp [hba.symm, hab2.symm]
    have hs : ({1, a, b, a * b} : Finset ↥V).card = 4 := by
      rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2,
        Finset.card_pair (Ne.symm hab3)]
    have := Finset.eq_univ_of_card ({1, a, b, a * b} : Finset ↥V) (by rw [hs, hcard])
    intro v
    have hv : v ∈ ({1, a, b, a * b} : Finset ↥V) := by rw [this]; exact Finset.mem_univ v
    simpa using hv
  obtain ⟨ia, hia, hae⟩ := hVP a.2
  obtain ⟨ib, hib, hbe⟩ := hVP b.2
  have hia64 := laIdx_chk.2.2.1 ia hia
  have hib64 := laIdx_chk.2.2.1 ib hib
  have hiab64 := (tmul_chk ia hia64 ib hib64).1
  have hX : ∀ g, g ∈ V ↔ ∃ k ∈ [0, ia, ib, tmul ia ib], g = telG k := by
    intro g
    constructor
    · intro hg
      rcases hall ⟨g, hg⟩ with h | h | h | h
      · refine ⟨0, by simp, ?_⟩
        rw [telG_zero_idx]
        exact congrArg Subtype.val h
      · exact ⟨ia, by simp, (congrArg Subtype.val h).trans hae⟩
      · exact ⟨ib, by simp, (congrArg Subtype.val h).trans hbe⟩
      · refine ⟨tmul ia ib, by simp, ?_⟩
        rw [← telG_mul hia64 hib64, ← hae, ← hbe]
        exact congrArg Subtype.val h
    · rintro ⟨k, hk, rfl⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · rw [telG_zero_idx]
        exact V.one_mem
      · rw [← hae]
        exact a.2
      · rw [← hbe]
        exact b.2
      · rw [← telG_mul hia64 hib64, ← hae, ← hbe]
        exact V.mul_mem a.2 b.2
  have hXlt : ∀ k ∈ [0, ia, ib, tmul ia ib], k < 64 := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · norm_num
    · exact hia64
    · exact hib64
    · exact hiab64
  have hclosure : ∀ i ∈ [0, ia, ib, tmul ia ib], ∀ j ∈ [0, ia, ib, tmul ia ib],
      tmul i j ∈ [0, ia, ib, tmul ia ib] := by
    intro i hi j hj
    have hi' := hXlt i hi
    have hj' := hXlt j hj
    have hmem : telG (tmul i j) ∈ V := by
      rw [← telG_mul hi' hj']
      exact V.mul_mem ((hX _).2 ⟨i, hi, rfl⟩) ((hX _).2 ⟨j, hj, rfl⟩)
    obtain ⟨k, hk, hke⟩ := (hX _).1 hmem
    rw [telG_inj_idx (tmul_chk i hi' j hj').1 (hXlt k hk) hke]
    exact hk
  have hnorm : NormFwd [0, 1, 2, 4] [0, ia, ib, tmul ia ib] :=
    normFwd_of_le_normalizer (H := m12Data.B) hXlt hX
      (fun k hk => ⟨by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega,
        genG_mem_B hk⟩) hN
  have hia0 : ia ≠ 0 := by
    intro h
    apply ha1
    apply Subtype.ext
    show (a : M12G) = 1
    rw [hae, h]
    exact telG_zero_idx
  have hib0 : ib ≠ 0 := by
    intro h
    apply hb1
    apply Subtype.ext
    show (b : M12G) = 1
    rw [hbe, h]
    exact telG_zero_idx
  have hibia : ib ≠ ia := by
    intro h
    apply hba
    apply Subtype.ext
    show (b : M12G) = a
    rw [hae, hbe, h]
  have hiasq : tmul ia ia = 0 := by
    apply (telG_sq_eq_one_iff hia64).1
    have : (a : M12G) ^ 2 = 1 := by
      have := congrArg Subtype.val ha2
      simpa using this
    rwa [hae] at this
  obtain ⟨h1, h2, h3⟩ := V4_chk ia (invPIdx_chk.2 ia hia hia0 hiasq) ib hib hib0 hibia hclosure hnorm
  intro g hg
  obtain ⟨k, hk, rfl⟩ := (hX g).1 hg
  refine ⟨k, ?_, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact erIdx_chk.2.2.2.1
  · exact h1
  · exact h2
  · exact h3

theorem m12E8Concl_model : E8Concl m12Data.A m12Data.B := by
  unfold E8Concl
  rw [pCoreOf_A_eq]
  exact ⟨ERsub, ERsub_le_LAsub, ERsub_elem, card_ERsub, B_le_normalizer_ERsub,
    fun V hVP hV4 hN => V4_le_ERsub V hVP hV4 hN⟩

end CFSG.Quasithin.M12AmalE8
