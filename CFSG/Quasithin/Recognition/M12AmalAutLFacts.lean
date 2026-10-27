module

public import CFSG.Quasithin.Recognition.M12AmalAutJFacts
public import CFSG.Quasithin.Recognition.M12AmalAutLCheck
public import CFSG.Quasithin.Recognition.M12AmalAutLIso

public section

namespace CFSG.Quasithin.M12AmalAut

open CFSG.Sporadic.Bridge Equiv CFSG.Open CFSG.Quasithin.AmalTransport CFSG.QuasithinUnique

theorem genG_mem_A {k : ℕ} (hk : k ∈ [0, 1, 2, 3]) : genG k ∈ autData.A := by
  show genG k ∈ Subgroup.closure ({genG 0, genG 1, genG 2, genG 3} : Set AutG)
  apply Subgroup.subset_closure
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> simp

theorem genG_mem_B {k : ℕ} (hk : k ∈ [0, 1, 2, 4]) : genG k ∈ autData.B := by
  show genG k ∈ Subgroup.closure ({genG 0, genG 1, genG 2, genG 4} : Set AutG)
  apply Subgroup.subset_closure
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl <;> simp

theorem conj_gen_idx {k : ℕ} (hk : k < 5) {j i : ℕ} (hj : j < 128) (hi : i < 128)
    (h : genG k * telG j * (genG k)⁻¹ = telG i) :
    compL (compL (gl k) (tl j)) (gil k) = tl i := by
  have r1 : ReprG (compL (compL (gl k) (tl j)) (gil k)) (genG k * telG j * (genG k)⁻¹) :=
    reprG_mul (reprG_mul (reprG_gen k hk) (reprG_tel j hj)) (reprG_inv_gen k hk)
  rw [h] at r1
  exact repL_unique r1 (reprG_tel i hi)

theorem normFwd_of_le_normalizer {H Q : Subgroup AutG} {L : List ℕ} (hlt : ∀ i ∈ L, i < 128)
    (hQL : ∀ g, g ∈ Q ↔ ∃ i ∈ L, g = telG i) {gs : List ℕ}
    (hgs : ∀ k ∈ gs, k < 5 ∧ genG k ∈ H) (hN : H ≤ Subgroup.normalizer (Q : Set AutG)) :
    NormFwd gs L := by
  intro k hk j hj
  obtain ⟨hk5, hkH⟩ := hgs k hk
  have hjQ : telG j ∈ Q := (hQL _).2 ⟨j, hj, rfl⟩
  have h1 : genG k * telG j * (genG k)⁻¹ ∈ Q := conj_mem_of_mem_normalizer (hN hkH) hjQ
  obtain ⟨i', hi', hi'e⟩ := (hQL _).1 h1
  exact ⟨i', hi', conj_gen_idx hk5 (hlt j hj) (hlt i' hi') hi'e⟩

theorem telG_sq_eq_one_iff {i : ℕ} (hi : i < 128) : telG i ^ 2 = 1 ↔ telMul i i = 0 := by
  rw [pow_two, telG_mul hi hi, ← telG_zero_idx]
  exact ⟨fun h => telG_inj_idx (telMul_chk i hi i hi).1 (by norm_num) h, fun h => by rw [h]⟩

theorem telG_comm {i j : ℕ} (hi : i < 128) (hj : j < 128) :
    commI i j < 128 ∧ telG i * telG j * (telG i)⁻¹ * (telG j)⁻¹ = telG (commI i j) := by
  have h1 := (telMul_chk i hi j hj).1
  have h2 := (telInv_chk i hi).1
  have h3 := (telMul_chk _ h1 _ h2).1
  have h4 := (telInv_chk j hj).1
  refine ⟨(telMul_chk _ h3 _ h4).1, ?_⟩
  unfold commI
  rw [telG_inv hi, telG_inv hj, telG_mul hi hj, telG_mul h1 h2, telG_mul h3 h4]

theorem pCoreOf_le_T_of_le {H : Subgroup AutG} (hH : autData.T ≤ H) :
    CFSG.Open.pCoreOf 2 H ≤ autData.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Sylow 2 AutG := aut_syl.1.toSylow aut_syl.2
  have hP : IsPGroup 2 (CFSG.Open.pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hnorm : autData.T ≤ Subgroup.normalizer (CFSG.Open.pCoreOf 2 H : Set AutG) :=
    hH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hsup : IsPGroup 2 (CFSG.Open.pCoreOf 2 H ⊔ autData.T : Subgroup AutG) :=
    hP.to_sup_of_normal_left' aut_syl.1 hnorm
  have h1 : CFSG.Open.pCoreOf 2 H ⊔ autData.T = (S : Subgroup AutG) :=
    S.is_maximal' hsup le_sup_right
  have h2 : (S : Subgroup AutG) = autData.T := rfl
  rw [h2] at h1
  exact le_sup_left.trans h1.le

theorem conj_mem_pCoreOf_aut {H : Subgroup AutG} {g : AutG} (hg : g ∈ H) {p : AutG}
    (hp : p ∈ CFSG.Open.pCoreOf 2 H) :
    g * p * g⁻¹ ∈ CFSG.Open.pCoreOf 2 H ∧ g⁻¹ * p * g ∈ CFSG.Open.pCoreOf 2 H := by
  refine ⟨(Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hg) p).1 hp, ?_⟩
  have h2 := (Subgroup.mem_normalizer_iff.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (H.inv_mem hg)) p).1 hp
  simpa using h2

theorem core_tel_of_le {H : Subgroup AutG} (hH : autData.T ≤ H) {q : AutG}
    (hq : q ∈ CFSG.Open.pCoreOf 2 H) : ∃ i : Fin 128, telG i = q :=
  (autData.mem_T_iff q).1 (pCoreOf_le_T_of_le hH hq)

theorem LAq_of_mem_core {i : Fin 128} (hq : telG i ∈ CFSG.Open.pCoreOf 2 autData.A) : LAq i := by
  obtain ⟨h1, h2⟩ := conj_mem_pCoreOf_aut autData.x_mem_A hq
  obtain ⟨j₁, hj₁⟩ := core_tel_of_le autData.T_le_A h1
  obtain ⟨j₂, hj₂⟩ := core_tel_of_le autData.T_le_A h2
  have hj₁' : telG j₁ = genG 3 * telG i * (genG 3)⁻¹ := hj₁
  have hj₂' : telG j₂ = (genG 3)⁻¹ * telG i * genG 3 := hj₂
  have r1 : ReprG (compL (compL (gl 3) (tl i)) (gil 3)) (genG 3 * telG i * (genG 3)⁻¹) :=
    reprG_mul (reprG_mul (reprG_gen 3 (by norm_num)) (reprG_tel i i.2))
      (reprG_inv_gen 3 (by norm_num))
  have r2 : ReprG (compL (compL (gil 3) (tl i)) (gl 3)) ((genG 3)⁻¹ * telG i * genG 3) :=
    reprG_mul (reprG_mul (reprG_inv_gen 3 (by norm_num)) (reprG_tel i i.2))
      (reprG_gen 3 (by norm_num))
  rw [← hj₁'] at r1
  rw [← hj₂'] at r2
  refine ⟨?_, ?_⟩
  · rw [repL_unique r1 (reprG_tel j₁ j₁.2)]
    exact tl_mem_chk j₁ j₁.2
  · rw [repL_unique r2 (reprG_tel j₂ j₂.2)]
    exact tl_mem_chk j₂ j₂.2

@[expose] noncomputable def LAsub : Subgroup AutG :=
  idxSubgroup laIdx laIdx_chk.2.2.2.1 laIdx_chk.2.2.1 laIdx_chk.2.2.2.2 laIdx_inv_chk

theorem LAsub_le_T : LAsub ≤ autData.T := by
  rintro _ ⟨i, hi, rfl⟩
  exact telG_mem_T (laIdx_chk.2.2.1 i hi)

theorem A_le_normalizer_idx {L : List ℕ} {h0 : 0 ∈ L} {hlt : ∀ i ∈ L, i < 128}
    {hmul : ∀ i ∈ L, ∀ j ∈ L, telMul i j ∈ L} {hinv : ∀ i ∈ L, telInv i ∈ L}
    (hN : NormBoth [0, 1, 2, 3] L) :
    autData.A ≤ Subgroup.normalizer (idxSubgroup L h0 hlt hmul hinv : Set AutG) := by
  show Subgroup.closure ({genG 0, genG 1, genG 2, genG 3} : Set AutG) ≤ _
  refine closure_le_normalizer_of_conj' _ _ ?_
  intro s hs k hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hj128 := hlt j hj
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
  · exact key 3 (by simp) h

theorem pCoreOf_A_eq : CFSG.Open.pCoreOf 2 autData.A = LAsub := by
  apply le_antisymm
  · intro g hg
    obtain ⟨i, rfl⟩ := core_tel_of_le autData.T_le_A hg
    exact ⟨i, (laIdx_iff_chk i i.2).1 (LAq_of_mem_core hg), rfl⟩
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (LAsub_le_T.trans autData.T_le_A)
      (A_le_normalizer_idx laIdx_norm_chk) (isPGroup_T.to_le LAsub_le_T)

theorem pCoreOf_A_le_inf : CFSG.Open.pCoreOf 2 autData.A ≤ autData.A ⊓ autData.B := by
  rw [autData.inf_AB, pCoreOf_A_eq]
  exact LAsub_le_T

theorem mem_centerOf_LA (g : AutG) : g ∈ centerOf LAsub ↔ ∃ i ∈ zIdx, g = telG i := by
  obtain ⟨hz1, -, hziff⟩ := zIdx_chk
  constructor
  · rintro ⟨⟨i, hi, rfl⟩, hc⟩
    refine ⟨i, (hziff i hi).1 (fun j hj => ?_), rfl⟩
    have hc' := Subgroup.mem_centralizer_iff.1 hc (telG j) ⟨j, hj, rfl⟩
    have hi' := laIdx_chk.2.2.1 i hi
    have hj' := laIdx_chk.2.2.1 j hj
    rw [telG_mul hj' hi', telG_mul hi' hj'] at hc'
    exact (telG_inj_idx (telMul_chk j hj' i hi').1 (telMul_chk i hi' j hj').1 hc').symm
  · rintro ⟨i, hi, rfl⟩
    have hiL := hz1 i hi
    refine ⟨⟨i, hiL, rfl⟩, Subgroup.mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨j, hj, rfl⟩
    have hi' := laIdx_chk.2.2.1 i hiL
    have hj' := laIdx_chk.2.2.1 j hj
    have hcomm := (hziff i hiL).2 hi j hj
    show telG j * telG i = telG i * telG j
    rw [telG_mul hj' hi', telG_mul hi' hj', hcomm]

theorem mem_secondCenter_LA (g : AutG) :
    g ∈ secondCenterOf LAsub ↔ ∃ i ∈ fIdx, g = telG i := by
  obtain ⟨-, -, hfsub, -, hfiff⟩ := fIdx_chk
  constructor
  · intro hg
    obtain ⟨⟨i, hi, rfl⟩, hc⟩ := mem_secondCenterOf.1 hg
    refine ⟨i, (hfiff i hi).1 (fun j hj => ?_), rfl⟩
    have hi' := laIdx_chk.2.2.1 i hi
    have hj' := laIdx_chk.2.2.1 j hj
    have hc' := hc (telG j) ⟨j, hj, rfl⟩
    obtain ⟨k, hk, hke⟩ := (mem_centerOf_LA _).1 hc'
    rw [(telG_comm hi' hj').2] at hke
    have hkz := laIdx_chk.2.2.1 k (zIdx_chk.1 k hk)
    rw [telG_inj_idx (telG_comm hi' hj').1 hkz hke]
    exact hk
  · rintro ⟨i, hi, rfl⟩
    have hiL := hfsub i hi
    have hi' := laIdx_chk.2.2.1 i hiL
    refine mem_secondCenterOf.2 ⟨⟨i, hiL, rfl⟩, fun y hy => ?_⟩
    obtain ⟨j, hj, rfl⟩ := hy
    have hj' := laIdx_chk.2.2.1 j hj
    rw [(telG_comm hi' hj').2]
    exact (mem_centerOf_LA _).2 ⟨commI i j, (hfiff i hiL).2 hi j hj, rfl⟩

theorem fIdx_lt : ∀ i ∈ fIdx, i < 128 := fun i hi =>
  laIdx_chk.2.2.1 i (fIdx_chk.2.2.1 i hi)

theorem card_secondCenterOf_A : Nat.card (secondCenterOf (CFSG.Open.pCoreOf 2 autData.A)) = 8 := by
  rw [card_of_idx (B := secondCenterOf (CFSG.Open.pCoreOf 2 autData.A)) fIdx_chk.2.1 fIdx_lt
    (fun g => by rw [pCoreOf_A_eq]; exact mem_secondCenter_LA g)]
  exact fIdx_chk.1

theorem sq_of_mem_secondCenterOf_A {x : AutG}
    (hx : x ∈ secondCenterOf (CFSG.Open.pCoreOf 2 autData.A)) : x * x = 1 := by
  rw [pCoreOf_A_eq] at hx
  obtain ⟨i, hi, rfl⟩ := (mem_secondCenter_LA x).1 hx
  have hi' := fIdx_lt i hi
  rw [telG_mul hi' hi', fIdx_chk.2.2.2.1 i hi]
  exact telG_zero_idx

@[expose] noncomputable def Wsub : Subgroup AutG :=
  idxSubgroup wIdx wIdx_chk.2.2.2.1 (fun i hi => laIdx_chk.2.2.1 i (wIdx_chk.2.2.1 i hi))
    wIdx_chk.2.2.2.2 wIdx_inv_chk

theorem wIdx_lt : ∀ i ∈ wIdx, i < 128 := fun i hi => laIdx_chk.2.2.1 i (wIdx_chk.2.2.1 i hi)

theorem foldl_mem {S : Subgroup AutG} : ∀ (w : List ℕ) (a : ℕ), a < 128 →
    (∀ l ∈ w, l < 128 ∧ telG l ∈ S) → telG a ∈ S → telG (w.foldl telMul a) ∈ S := by
  intro w
  induction w with
  | nil =>
    intro a _ _ h
    exact h
  | cons l w ih =>
    intro a ha hw h
    obtain ⟨hl, hlS⟩ := hw l List.mem_cons_self
    simp only [List.foldl_cons]
    refine ih (telMul a l) (telMul_chk a ha l hl).1
      (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')) ?_
    rw [← telG_mul ha hl]
    exact S.mul_mem h hlS

theorem omegaOneOf_LA : omegaOneOf LAsub = Wsub := by
  apply le_antisymm
  · refine (Subgroup.closure_le Wsub).2 ?_
    rintro x ⟨⟨i, hi, rfl⟩, hx2⟩
    have hi' := laIdx_chk.2.2.1 i hi
    exact ⟨i, wIdx_invol_chk i hi ((telG_sq_eq_one_iff hi').1 hx2), rfl⟩
  · rintro g ⟨i, hi, rfl⟩
    obtain ⟨w, hw, hwinv, hwprod⟩ := wWords_chk i hi
    rw [← hwprod]
    refine foldl_mem w 0 (by norm_num) (fun l hl => ?_) ?_
    · obtain ⟨hlL, hl0, hl2⟩ := invPIdx_chk.1 l (hwinv l hl)
      have hl128 := laIdx_chk.2.2.1 l hlL
      exact ⟨hl128, Subgroup.subset_closure ⟨⟨l, hlL, rfl⟩, (telG_sq_eq_one_iff hl128).2 hl2⟩⟩
    · rw [telG_zero_idx]
      exact Subgroup.one_mem _

theorem card_Wsub : Nat.card Wsub = 32 := by
  rw [card_of_idx wIdx_chk.2.1 wIdx_lt (fun g => Iff.rfl)]
  exact wIdx_chk.1

@[expose] noncomputable def q8Hom (A X : List ℕ) (h : Q8Tab A X) : QuaternionGroup 2 →* AutG where
  toFun g := telG (q8Idx' A X g)
  map_one' := by
    show telG (q8Idx' A X 1) = 1
    rw [h.2.2]
    exact telG_zero_idx
  map_mul' g g' := by
    obtain ⟨hg, hg', he⟩ := h.1 g g'
    have hgg := (h.1 (g * g') 1).1
    exact (autEq_of_compL hg hg' hgg he).symm

theorem q8Hom_apply (A X : List ℕ) (h : Q8Tab A X) (g : QuaternionGroup 2) :
    q8Hom A X h g = telG (q8Idx' A X g) := rfl

theorem q8Hom_injective (A X : List ℕ) (h : Q8Tab A X) : Function.Injective (q8Hom A X h) := by
  intro g g' he
  exact h.2.1 g g' (telG_inj_idx ((h.1 g 1).1) ((h.1 g' 1).1) he)

theorem isQ8Sq_of_homs {W : Subgroup AutG} (f₁ f₂ : QuaternionGroup 2 →* AutG)
    (hf₁ : Function.Injective f₁) (hf₂ : Function.Injective f₂)
    (h₁W : ∀ g, f₁ g ∈ W) (h₂W : ∀ g, f₂ g ∈ W)
    (hcomm : ∀ g h, f₁ g * f₂ h = f₂ h * f₁ g)
    (hgen : ∀ w ∈ W, ∃ g h, w = f₁ g * f₂ h) (hcard : Nat.card W = 32) : IsQ8Sq ↥W := by
  have hle₁ : f₁.range ≤ W := by
    rintro _ ⟨g, rfl⟩
    exact h₁W g
  have hle₂ : f₂.range ≤ W := by
    rintro _ ⟨g, rfl⟩
    exact h₂W g
  refine ⟨hcard, f₁.range.subgroupOf W, f₂.range.subgroupOf W, ⟨?_, ?_⟩,
    ⟨(Subgroup.subgroupOfEquivOfLe hle₁).trans (MonoidHom.ofInjective hf₁).symm⟩,
    ⟨(Subgroup.subgroupOfEquivOfLe hle₂).trans (MonoidHom.ofInjective hf₂).symm⟩⟩
  · intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    obtain ⟨g, hg⟩ : ∃ g, f₁ g = a.1 := ha
    obtain ⟨h, hh⟩ : ∃ h, f₂ h = b.1 := hb
    apply Subtype.ext
    show b.1 * a.1 = a.1 * b.1
    rw [← hg, ← hh]
    exact (hcomm g h).symm
  · rw [eq_top_iff]
    intro w _
    obtain ⟨g, h, hw⟩ := hgen w.1 w.2
    have e : w = ⟨f₁ g, h₁W g⟩ * ⟨f₂ h, h₂W h⟩ := Subtype.ext hw
    rw [e]
    exact Subgroup.mul_mem_sup (show (⟨f₁ g, h₁W g⟩ : ↥W) ∈ f₁.range.subgroupOf W from ⟨g, rfl⟩)
      (show (⟨f₂ h, h₂W h⟩ : ↥W) ∈ f₂.range.subgroupOf W from ⟨h, rfl⟩)

theorem isQ8Sq_Wsub : IsQ8Sq ↥Wsub := by
  obtain ⟨hlt_a, hlt_b⟩ := q8_lt_chk
  obtain ⟨hinc_a, hinc_b⟩ := q8_incl_chk
  obtain ⟨hsa, hsb, hra, hrb⟩ := q8_surj_chk
  have hlt : ∀ (A X : List ℕ) (h : Q8Tab A X) (g : QuaternionGroup 2), q8Idx' A X g < 128 :=
    fun A X h g => (h.1 g 1).1
  refine isQ8Sq_of_homs (q8Hom q8aA q8aX q8a_chk) (q8Hom q8bA q8bX q8b_chk)
    (q8Hom_injective _ _ _) (q8Hom_injective _ _ _) (fun g => ?_) (fun g => ?_) (fun g h => ?_)
    (fun w hw => ?_) card_Wsub
  · exact ⟨q8Idx' q8aA q8aX g, hinc_a _ (hra g), rfl⟩
  · exact ⟨q8Idx' q8bA q8bX g, hinc_b _ (hrb g), rfl⟩
  · rw [q8Hom_apply, q8Hom_apply, telG_mul (hlt _ _ q8a_chk g) (hlt _ _ q8b_chk h),
      telG_mul (hlt _ _ q8b_chk h) (hlt _ _ q8a_chk g)]
    exact congrArg telG (q8_comm_chk _ (hra g) _ (hrb h))
  · obtain ⟨i, hi, rfl⟩ := hw
    obtain ⟨a, ha, b, hb, hab⟩ := q8_gen_chk i hi
    obtain ⟨g, rfl⟩ := hsa a ha
    obtain ⟨h, rfl⟩ := hsb b hb
    refine ⟨g, h, ?_⟩
    rw [q8Hom_apply, q8Hom_apply, telG_mul (hlt _ _ q8a_chk g) (hlt _ _ q8b_chk h), hab]

theorem exists_mask (Q : Subgroup AutG) (hFQ : secondCenterOf LAsub ≤ Q) (hQP : Q ≤ LAsub) :
    ∃ p : ℕ → Bool, (maskOf p).getD 0 false = true ∧
      ∀ g, g ∈ Q ↔ ∃ i ∈ maskSet (maskOf p), g = telG i := by
  classical
  obtain ⟨-, -, c3, c4, c5, c6, c8⟩ := cosetTab_chk
  have hlt : ∀ i ∈ laIdx, i < 128 := laIdx_chk.2.2.1
  have hF : ∀ f ∈ fIdx, telG f ∈ Q := fun f hf =>
    hFQ ((mem_secondCenter_LA _).2 ⟨f, hf, rfl⟩)
  have hcos : ∀ k < 8, ∀ i ∈ cosetOf k, (telG i ∈ Q ↔ telG ((cosetOf k).headD 0) ∈ Q) := by
    intro k hk i hi
    have hi128 : i < 128 := hlt i (c3 k hk i hi)
    obtain ⟨f₀, hf₀, hfe₀⟩ := c6 k hk i hi
    have hhead : (cosetOf k).headD 0 < 128 := by
      rw [← hfe₀]
      exact (telMul_chk i hi128 f₀ (fIdx_lt f₀ hf₀)).1
    constructor
    · intro hiQ
      have e : telG (telMul i f₀) = telG i * telG f₀ := (telG_mul hi128 (fIdx_lt f₀ hf₀)).symm
      rw [hfe₀] at e
      rw [e]
      exact Q.mul_mem hiQ (hF f₀ hf₀)
    · intro hhQ
      obtain ⟨f, hf, hfe⟩ := c5 k hk i hi
      have e : telG (telMul ((cosetOf k).headD 0) f) = telG ((cosetOf k).headD 0) * telG f :=
        (telG_mul hhead (fIdx_lt f hf)).symm
      rw [hfe] at e
      rw [e]
      exact Q.mul_mem hhQ (hF f hf)
  refine ⟨fun k => decide (telG ((cosetOf k).headD 0) ∈ Q), ?_, fun g => ?_⟩
  · rw [maskOf_getD _ 0 (by norm_num)]
    simp only [c8, telG_zero_idx]
    simp
  · constructor
    · intro hg
      obtain ⟨i, hi, rfl⟩ := hQP hg
      obtain ⟨k, hk, hik⟩ := c4 i hi
      refine ⟨i, mem_maskSet.2 ⟨k, hk, ?_, hik⟩, rfl⟩
      rw [maskOf_getD _ k hk]
      simpa using (hcos k hk i hik).1 hg
    · rintro ⟨i, hi, rfl⟩
      obtain ⟨k, hk, hb, hik⟩ := mem_maskSet.1 hi
      rw [maskOf_getD _ k hk] at hb
      exact (hcos k hk i hik).2 (by simpa using hb)

theorem maskSet_lt {bs : List Bool} : ∀ i ∈ maskSet bs, i < 128 := by
  intro i hi
  obtain ⟨k, hk, -, hik⟩ := mem_maskSet.1 hi
  exact laIdx_chk.2.2.1 i (cosetTab_chk.2.2.1 k hk i hik)

theorem trichotomy_model (Q : Subgroup AutG) (hFQ : secondCenterOf LAsub ≤ Q) (hQP : Q ≤ LAsub)
    (hN : autData.A ≤ Subgroup.normalizer (Q : Set AutG)) :
    Q = secondCenterOf LAsub ∨
      (Nat.card Q = 16 ∧ ∀ x ∈ Q, x * x = 1 → x ∈ secondCenterOf LAsub) ∨
      omegaOneOf LAsub ≤ Q := by
  obtain ⟨p, hbs0, hQ⟩ := exists_mask Q hFQ hQP
  obtain ⟨hnd, hmain⟩ := mask_chk p
  generalize maskOf p = bs at hbs0 hQ hnd hmain
  have hclosure : ∀ i ∈ maskSet bs, ∀ j ∈ maskSet bs, telMul i j ∈ maskSet bs := by
    intro i hi j hj
    have hi' := maskSet_lt i hi
    have hj' := maskSet_lt j hj
    have hmem : telG (telMul i j) ∈ Q := by
      rw [← telG_mul hi' hj']
      exact Q.mul_mem ((hQ _).2 ⟨i, hi, rfl⟩) ((hQ _).2 ⟨j, hj, rfl⟩)
    obtain ⟨k, hk, hke⟩ := (hQ _).1 hmem
    rw [telG_inj_idx (telMul_chk i hi' j hj').1 (maskSet_lt k hk) hke]
    exact hk
  have hnorm : NormFwd [0, 1, 2, 3] (maskSet bs) :=
    normFwd_of_le_normalizer (H := autData.A) maskSet_lt hQ
      (fun k hk => ⟨by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega,
        genG_mem_A hk⟩) hN
  rcases hmain hbs0 hclosure hnorm with h1 | ⟨h2, h3⟩ | h4
  · left
    ext g
    rw [hQ, mem_secondCenter_LA]
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, (h1 i (maskSet_lt i hi)).1 hi, rfl⟩
    · rintro ⟨i, hi, rfl⟩
      exact ⟨i, (h1 i (fIdx_lt i hi)).2 hi, rfl⟩
  · right
    left
    refine ⟨(card_of_idx hnd maskSet_lt hQ).trans h2, fun x hx hx2 => ?_⟩
    obtain ⟨i, hi, rfl⟩ := (hQ _).1 hx
    have hi' := maskSet_lt i hi
    have hsq : telMul i i = 0 := by
      rw [← telG_sq_eq_one_iff hi', pow_two]
      exact hx2
    exact (mem_secondCenter_LA _).2 ⟨i, h3 i hi hsq, rfl⟩
  · right
    right
    rw [omegaOneOf_LA]
    rintro g ⟨i, hi, rfl⟩
    exact (hQ _).2 ⟨i, h4 i hi, rfl⟩

theorem ERsub_le_Wsub : ERsub ≤ Wsub := by
  rintro _ ⟨i, hi, rfl⟩
  exact ⟨i, erIdx_chk8.2.2 i hi, rfl⟩

theorem ERsub_elem : IsElemAbelian 2 ERsub := by
  refine isElemAbelian_mono ?_ Esub_elem
  rw [ERsub_eq]
  exact inf_le_left

theorem card_ERsub : Nat.card ERsub = 8 := by
  rw [card_of_idx erIdx_chk8.2.1 erIdx_lt_chk (fun g => Iff.rfl)]
  exact erIdx_chk8.1

theorem B_le_normalizer_ERsub : autData.B ≤ Subgroup.normalizer (ERsub : Set AutG) :=
  B_le_normalizer_idx ER_norm_chk

theorem V4_le_ERsub (V : Subgroup AutG) (hVP : V ≤ LAsub) (hV4 : Nat.card V = 4)
    (hN : autData.B ≤ Subgroup.normalizer (V : Set AutG)) : V ≤ ERsub := by
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
  have hia128 := laIdx_chk.2.2.1 ia hia
  have hib128 := laIdx_chk.2.2.1 ib hib
  have hiab128 := (telMul_chk ia hia128 ib hib128).1
  have hX : ∀ g, g ∈ V ↔ ∃ k ∈ [0, ia, ib, telMul ia ib], g = telG k := by
    intro g
    constructor
    · intro hg
      rcases hall ⟨g, hg⟩ with h | h | h | h
      · refine ⟨0, by simp, ?_⟩
        rw [telG_zero_idx]
        exact congrArg Subtype.val h
      · exact ⟨ia, by simp, (congrArg Subtype.val h).trans hae⟩
      · exact ⟨ib, by simp, (congrArg Subtype.val h).trans hbe⟩
      · refine ⟨telMul ia ib, by simp, ?_⟩
        rw [← telG_mul hia128 hib128, ← hae, ← hbe]
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
      · rw [← telG_mul hia128 hib128, ← hae, ← hbe]
        exact V.mul_mem a.2 b.2
  have hXlt : ∀ k ∈ [0, ia, ib, telMul ia ib], k < 128 := by
    intro k hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · norm_num
    · exact hia128
    · exact hib128
    · exact hiab128
  have hclosure : ∀ i ∈ [0, ia, ib, telMul ia ib], ∀ j ∈ [0, ia, ib, telMul ia ib],
      telMul i j ∈ [0, ia, ib, telMul ia ib] := by
    intro i hi j hj
    have hi' := hXlt i hi
    have hj' := hXlt j hj
    have hmem : telG (telMul i j) ∈ V := by
      rw [← telG_mul hi' hj']
      exact V.mul_mem ((hX _).2 ⟨i, hi, rfl⟩) ((hX _).2 ⟨j, hj, rfl⟩)
    obtain ⟨k, hk, hke⟩ := (hX _).1 hmem
    rw [telG_inj_idx (telMul_chk i hi' j hj').1 (hXlt k hk) hke]
    exact hk
  have hnorm : NormFwd [0, 1, 2, 4] [0, ia, ib, telMul ia ib] :=
    normFwd_of_le_normalizer (H := autData.B) hXlt hX
      (fun k hk => ⟨by simp only [List.mem_cons, List.not_mem_nil, or_false] at hk; omega,
        genG_mem_B hk⟩) hN
  have hia0 : ia ≠ 0 := by
    intro h
    apply ha1
    apply Subtype.ext
    show (a : AutG) = 1
    rw [hae, h]
    exact telG_zero_idx
  have hib0 : ib ≠ 0 := by
    intro h
    apply hb1
    apply Subtype.ext
    show (b : AutG) = 1
    rw [hbe, h]
    exact telG_zero_idx
  have hibia : ib ≠ ia := by
    intro h
    apply hba
    apply Subtype.ext
    show (b : AutG) = a
    rw [hae, hbe, h]
  have hiasq : telMul ia ia = 0 := by
    apply (telG_sq_eq_one_iff hia128).1
    have : (a : AutG) ^ 2 = 1 := by
      have := congrArg Subtype.val ha2
      simpa using this
    rwa [hae] at this
  obtain ⟨h1, h2, h3⟩ := V4_chk ia (invPIdx_chk.2 ia hia hia0 hiasq) ib hib hib0 hibia hclosure hnorm
  intro g hg
  obtain ⟨k, hk, rfl⟩ := (hX g).1 hg
  refine ⟨k, ?_, rfl⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact (erIdx_chk 0 (by norm_num)).2 ⟨eIdx_chk.2.2.2.1, rIdx_chk.2.2.2.1⟩
  · exact h1
  · exact h2
  · exact h3

theorem autLocalConcl_model : AutLocalConcl autData.A autData.B := by
  unfold AutLocalConcl
  rw [pCoreOf_A_eq]
  refine ⟨?_, ?_, ?_, ?_, ERsub, ?_, ERsub_elem, card_ERsub, B_le_normalizer_ERsub, ?_⟩
  · have := card_secondCenterOf_A
    rwa [pCoreOf_A_eq] at this
  · intro x hx
    exact sq_of_mem_secondCenterOf_A (by rwa [pCoreOf_A_eq])
  · exact fun Q hFQ hQP hN => trichotomy_model Q hFQ hQP hN
  · rw [omegaOneOf_LA]
    exact isQ8Sq_Wsub
  · rw [omegaOneOf_LA]
    exact ERsub_le_Wsub
  · exact fun V hVP hV4 hN => V4_le_ERsub V hVP hV4 hN

end CFSG.Quasithin.M12AmalAut
