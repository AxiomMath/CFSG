module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Core
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsMaxModel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_16FactsA6Model
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.NineDefs
public import CFSG.Quasithin.Background.E1Sec3
public import CFSG.Quasithin.Background.F7Basic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NFA6

open CFSG.Quasithin CFSG.Open Subgroup CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
  CFSG.QuasithinUnique.A6Facts.Core CFSG.LocalAnalysis.WeakClosure81.NFA6.Core

structure Desc (H : Subgroup P10) (L : List (List ℕ)) : Prop where
  mem : ∀ x, x ∈ H ↔ code x ∈ L
  surj : ∀ c ∈ L, ∃ x ∈ H, code x = c

theorem Desc.card {H : Subgroup P10} {L : List (List ℕ)} (h : Desc H L) (hnd : L.Nodup) :
    Nat.card H = L.length :=
  card_eq_of_code_mem hnd h.mem h.surj

theorem Desc.inf {H K : Subgroup P10} {L M : List (List ℕ)} (hH : Desc H L) (hK : Desc K M) :
    Desc (H ⊓ K) (L.filter M.contains) := by
  refine ⟨fun x => ?_, fun c hc => ?_⟩
  · rw [mem_inf, hH.mem, hK.mem, List.mem_filter, List.contains_iff_mem]
  · rw [List.mem_filter, List.contains_iff_mem] at hc
    obtain ⟨x, hx, rfl⟩ := hH.surj c hc.1
    exact ⟨x, ⟨hx, (hK.mem x).mpr hc.2⟩, rfl⟩

theorem nodup_of_nodupB : ∀ {l : List (List ℕ)}, nodupB l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    exact List.nodup_cons.mpr ⟨fun ha => by
      have := List.contains_iff_mem.mpr ha
      rw [h.1] at this
      exact Bool.false_ne_true this, nodup_of_nodupB h.2⟩

theorem exists_list_of_codes {S : Set P10} :
    ∀ {L : List (List ℕ)}, (∀ c ∈ L, ∃ x ∈ S, code x = c) →
      ∃ l : List P10, l.map code = L ∧ ∀ x ∈ l, x ∈ S
  | [], _ => ⟨[], rfl, by simp⟩
  | c :: L, h => by
    obtain ⟨x, hx, rfl⟩ := h c List.mem_cons_self
    obtain ⟨l, hl, hlS⟩ := exists_list_of_codes (L := L) fun d hd => h d (List.mem_cons_of_mem _ hd)
    exact ⟨x :: l, by simp [hl], by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact hlS y hy⟩

theorem SubData.spec {D : SubData} (hD : D.ok = true) {gens : List P10}
    (hg : gens.map code = D.gc) :
    Desc (closure {g | g ∈ gens}) D.lit ∧ D.lit.Nodup := by
  simp only [SubData.ok, Bool.and_eq_true, beq_iff_eq] at hD
  obtain ⟨⟨hlit, htbl⟩, hnd⟩ := hD
  have htbl' : Core.tblCheckC Core.cid D.gc (Core.buildCodes Core.cid D.gc D.tree) D.tbl = true := by
    rw [← hlit]; exact htbl
  obtain ⟨hmem, hsurj⟩ := mem_closure_iff_of_tbl hg htbl'
  rw [← hlit] at hmem hsurj
  exact ⟨⟨hmem, hsurj⟩, nodup_of_nodupB hnd⟩

theorem SubData.exists_desc {D : SubData} (hD : D.ok = true) {S : Set P10}
    (hgens : ∀ c ∈ D.gc, ∃ x ∈ S, code x = c) :
    ∃ H : Subgroup P10, H ≤ closure S ∧ Desc H D.lit ∧ D.lit.Nodup := by
  obtain ⟨l, hl, hlS⟩ := exists_list_of_codes hgens
  obtain ⟨hd, hnd⟩ := SubData.spec hD hl
  exact ⟨_, closure_mono fun x hx => hlS x hx, hd, hnd⟩

theorem code_mul_eq_iff {x y z w : P10} :
    cmul (code x) (code y) = cmul (code z) (code w) ↔ x * y = z * w := by
  rw [← code_mul, ← code_mul]
  exact ⟨fun h => code_injective h, fun h => by rw [h]⟩

theorem cid_eq : Core.cid = code 1 := code_one.symm

theorem code_eq_cid_iff {x : P10} : code x = Core.cid ↔ x = 1 := by
  rw [cid_eq]
  exact ⟨fun h => code_injective h, fun h => by rw [h]⟩

theorem ccomm_iff {x y : P10} : ccomm (code x) (code y) = true ↔ x * y = y * x := by
  rw [ccomm, beq_iff_eq, code_mul_eq_iff]

theorem cinvol_iff {x : P10} : cinvol (code x) = true ↔ x * x = 1 := by
  rw [cinvol, beq_iff_eq, ← code_mul, code_eq_cid_iff]

theorem cpow_eq_code {x : P10} (n : ℕ) : Core.cpow (code x) n = code (x ^ n) :=
  (code_pow x n).symm

theorem normB_spec {K N : Subgroup P10} {KL NL : List (List ℕ)} (hK : Desc K KL) (hN : Desc N NL)
    (h : normB KL NL = true) {k n : P10} (hk : k ∈ K) (hn : n ∈ N) : k * n * k⁻¹ ∈ N := by
  simp only [normB, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨c, hc, he⟩ := h _ ((hK.mem k).mp hk) _ ((hN.mem n).mp hn)
  obtain ⟨n', hn', rfl⟩ := hN.surj c hc
  rw [code_mul_eq_iff] at he
  rw [he]
  simpa using hn'

theorem relIndex_of_card {H K : Subgroup P10} (hHK : H ≤ K) {a b : ℕ} (hH : Nat.card H = a)
    (hK : Nat.card K = b) (ha : a ≠ 0) : H.relIndex K = b / a := by
  have h1 := relIndex_mul_card H K
  rw [inf_eq_left.mpr hHK, hH, hK] at h1
  rw [← h1, Nat.mul_div_cancel _ (Nat.pos_of_ne_zero ha)]

theorem KData.spec {G T₀ : Subgroup P10} {TL : List (List ℕ)} (hT : Desc T₀ TL)
    (hT2 : IsPGroup 2 T₀) {D : KData} (hD : D.check TL = true)
    (hgens : ∀ c ∈ D.K.gc, ∃ x ∈ (G : Set P10), code x = c) :
    ∃ K : Subgroup P10, K ≤ G ∧ Desc K D.K.lit ∧ D.K.lit.Nodup ∧
      (∃ Z : Subgroup P10, TwoPTwo K (K ⊓ T₀) Z D.p ∧ Nat.card Z = D.p) ∧
      ∃ N : Subgroup P10, Desc N D.N2.lit ∧ N ≤ pCoreOf 2 K := by
  simp only [KData.check, sylB, Bool.and_eq_true, and_assoc, bne_iff_ne, ne_eq, beq_iff_eq,
    Bool.or_eq_true] at hD
  obtain ⟨hKok, hN2ok, hNpok, hN2K, hNpK, hN2g, hNpg, hnorm2, hnormp, hexp2, hpow, hq, hy, hyp,
    hy1, hp35, hS0, -, hSodd, -, hpodd⟩ := hD
  obtain ⟨K, hKG, hK, hKnd⟩ := SubData.exists_desc hKok hgens
  rw [closure_eq] at hKG
  have hgK : ∀ {L : List (List ℕ)}, L.all D.K.lit.contains = true →
      ∀ c ∈ L, ∃ x ∈ (K : Set P10), code x = c := by
    intro L hL c hc
    rw [List.all_eq_true] at hL
    exact hK.surj c (List.contains_iff_mem.mp (hL c hc))
  obtain ⟨N2, hN2le, hN2, -⟩ := SubData.exists_desc hN2ok (hgK hN2g)
  obtain ⟨Np, hNple, hNp, -⟩ := SubData.exists_desc hNpok (hgK hNpg)
  rw [closure_eq] at hN2le hNple
  have hpr : D.p.Prime := by rcases hp35 with h | h <;> rw [h] <;> norm_num
  have : Fact D.p.Prime := ⟨hpr⟩
  have hn2 : (N2.subgroupOf K).Normal :=
    ⟨fun n hn k => by
      rw [mem_subgroupOf] at hn ⊢
      exact normB_spec hK hN2 hnorm2 k.2 hn⟩
  have hnp : (Np.subgroupOf K).Normal :=
    ⟨fun n hn k => by
      rw [mem_subgroupOf] at hn ⊢
      exact normB_spec hK hNp hnormp k.2 hn⟩
  have hN2p : IsPGroup 2 (N2.subgroupOf K) := by
    intro g
    refine ⟨3, ?_⟩
    have hx : ((g : K) : P10) ∈ N2 := g.2
    rw [List.all_eq_true] at hexp2
    have h8 := hexp2 _ ((hN2.mem _).mp hx)
    rw [beq_iff_eq, cpow_eq_code, code_eq_cid_iff] at h8
    apply Subtype.ext
    apply Subtype.ext
    simpa using h8
  have hO : CFSG.Quasithin.E1.oTwoPTwo ↥K D.p = ⊤ := by
    have := hn2
    have := hnp
    refine CFSG.Quasithin.E1.oTwoPTwo_eq_top_of_series (N₂ := N2.subgroupOf K)
      (N₂p := Np.subgroupOf K) hN2p (fun x hx => ⟨1, ?_⟩) (fun q => ⟨2, ?_⟩)
    · rw [mem_subgroupOf] at hx ⊢
      rw [List.all_eq_true] at hpow
      have h1 := List.contains_iff_mem.mp (hpow _ ((hNp.mem _).mp hx))
      rw [cpow_eq_code] at h1
      rw [pow_one, Subgroup.coe_pow]
      exact (hN2.mem _).mpr h1
    · rw [mem_subgroupOf]
      rw [List.all_eq_true] at hq
      have h1 := List.contains_iff_mem.mp (hq _ ((hK.mem _).mp q.2))
      rw [cpow_eq_code] at h1
      rw [Subgroup.coe_pow]
      exact (hNp.mem _).mpr (by simpa using h1)
  have hS : Desc (K ⊓ T₀) (D.K.lit.filter TL.contains) := hK.inf hT
  have hSc : Nat.card (K ⊓ T₀ : Subgroup P10) = (D.K.lit.filter TL.contains).length :=
    hS.card (hKnd.filter _)
  have hKc : Nat.card K = D.K.lit.length := hK.card hKnd
  obtain ⟨y, hyK, hyc⟩ := hK.surj _ (List.contains_iff_mem.mp hy)
  rw [← hyc, cpow_eq_code, code_eq_cid_iff] at hyp
  have hy1' : y ≠ 1 := fun h => hy1 (by rw [← hyc, h, code_one])
  have hoy : orderOf y = D.p := orderOf_eq_prime hyp hy1'
  have hZc : Nat.card (zpowers y) = D.p := by rw [Nat.card_zpowers, hoy]
  refine ⟨K, hKG, hK, hKnd, ⟨zpowers y, ⟨hpr, ?_, hO, ⟨inf_le_left, hT2.to_le inf_le_right, ?_⟩,
    ⟨zpowers_le.mpr hyK, IsPGroup.of_card (n := 1) (by rw [hZc, pow_one]), ?_⟩⟩, hZc⟩,
    N2, hN2, ?_⟩
  · rcases hp35 with h | h <;> rw [h] <;> norm_num
  · rw [relIndex_of_card inf_le_left hSc hKc hS0]
    omega
  · rw [relIndex_of_card (zpowers_le.mpr hyK) hZc hKc hpr.ne_zero]
    exact hpodd ∘ Nat.mod_eq_zero_of_dvd
  · intro x hx
    have h1 : (⟨x, hN2le hx⟩ : ↥K) ∈ CFSG.pCore 2 ↥K :=
      CFSG.LieType.BorelTits.le_pCore 2 hn2 hN2p (show _ ∈ N2.subgroupOf K from hx)
    exact ⟨_, h1, rfl⟩

theorem mem_e4_iff {a b x : P10} : code x ∈ e4 (code a) (code b) ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
  simp only [e4, List.mem_cons, List.not_mem_nil, or_false, cid_eq, ← code_mul,
    code_injective.eq_iff]

theorem mem_e8_iff {a b c x : P10} : code x ∈ e8 (code a) (code b) (code c) ↔
    x = 1 ∨ x = a ∨ x = b ∨ x = c ∨ x = a * b ∨ x = a * c ∨ x = b * c ∨ x = a * b * c := by
  simp only [e8, List.mem_cons, List.not_mem_nil, or_false, cid_eq, ← code_mul,
    code_injective.eq_iff]

theorem setEq_mem {E F : List (List ℕ)} (h : setEq E F = true) (c : List ℕ) : c ∈ E ↔ c ∈ F := by
  simp only [setEq, Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem] at h
  exact ⟨h.1 c, h.2 c⟩

theorem exists_two_ne {A : Subgroup P10} (h : 3 ≤ Nat.card A) :
    ∃ a ∈ A, a ≠ 1 ∧ ∃ b ∈ A, b ≠ 1 ∧ b ≠ a := by
  by_cases h1 : ∃ a ∈ A, a ≠ 1
  · obtain ⟨a, ha, ha1⟩ := h1
    by_contra hcon
    have hsub : (A : Set P10) ⊆ {1, a} := by
      intro b hb
      by_cases hb1 : b = 1
      · simp [hb1]
      · have : b = a := by
          by_contra hba
          exact hcon ⟨a, ha, ha1, b, hb, hb1, hba⟩
        simp [this]
    have h2 : Nat.card A ≤ 2 := by
      change Nat.card (A : Set P10) ≤ 2
      rw [Nat.card_coe_set_eq]
      calc (A : Set P10).ncard ≤ ({1, a} : Set P10).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ ≤ 2 := by
          refine (Set.ncard_insert_le _ _).trans ?_
          rw [Set.ncard_singleton]
    omega
  · push Not at h1
    have : A = ⊥ := eq_bot_iff.mpr fun x hx => (mem_bot).mpr (h1 x hx)
    rw [this, card_bot] at h
    omega

theorem seed_spec {T₀ : Subgroup P10} {TL : List (List ℕ)} (hT : Desc T₀ TL)
    {Es : List (List (List ℕ))} (hseed : seedCheck TL Es = true) {A : Subgroup P10}
    (hAT : A ≤ T₀) (hAe : IsElemAbelian 2 A) (hA4 : 4 ≤ Nat.card A) :
    ∃ E ∈ Es, ∀ x, x ∈ A ↔ code x ∈ E := by
  obtain ⟨a, ha, ha1, b, hb, hb1, hba⟩ := exists_two_ne (by omega : 3 ≤ Nat.card A)
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    intro x hx y hy
    have := hAe.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← pow_two]; exact hAe.2 x hx
  have hinvs : ∀ x ∈ A, x ≠ 1 → code x ∈ invs TL := by
    intro x hx hx1
    rw [invs, List.mem_filter]
    refine ⟨(hT.mem x).mp (hAT hx), ?_⟩
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
    exact ⟨fun h => hx1 (code_eq_cid_iff.mp h), cinvol_iff.mpr (hsq x hx)⟩
  have hW : ∀ x ∈ A, x ≠ 1 →
      code x ∈ ((invs TL).filter (ccomm (code a))).filter (ccomm (code b)) := by
    intro x hx hx1
    rw [List.mem_filter, List.mem_filter]
    exact ⟨⟨hinvs x hx hx1, ccomm_iff.mpr (hcomm a ha x hx)⟩, ccomm_iff.mpr (hcomm b hb x hx)⟩
  unfold seedCheck seedCheckI at hseed
  rw [List.all_eq_true] at hseed
  have h1 := hseed _ (hinvs a ha ha1)
  rw [List.all_eq_true] at h1
  have h2 := h1 (code b) (List.mem_filter.mpr ⟨hinvs b hb hb1, ccomm_iff.mpr (hcomm a ha b hb)⟩)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, List.any_eq_true,
    List.all_eq_true] at h2
  rcases h2 with h2 | ⟨⟨E, hE, hEeq⟩, hX⟩
  · exact absurd (code_injective h2).symm hba
  by_cases hall : ∀ x ∈ A, code x ∈ e4 (code a) (code b)
  · refine ⟨E, hE, fun x => ?_⟩
    rw [← setEq_mem hEeq]
    refine ⟨hall x, fun hx => ?_⟩
    rcases mem_e4_iff.mp hx with rfl | rfl | rfl | rfl
    · exact one_mem A
    · exact ha
    · exact hb
    · exact mul_mem ha hb
  · push Not at hall
    obtain ⟨c, hc, hc4⟩ := hall
    have hc1 : c ≠ 1 := by
      rintro rfl
      exact hc4 (mem_e4_iff.mpr (Or.inl rfl))
    rcases hX (code c) (hW c hc hc1) with h3 | ⟨⟨E', hE', hE'eq⟩, hY⟩
    · exact absurd (List.contains_iff_mem.mp h3) hc4
    refine ⟨E', hE', fun x => ?_⟩
    rw [← setEq_mem hE'eq]
    constructor
    · intro hx
      by_cases hx1 : x = 1
      · rw [hx1]
        exact mem_e8_iff.mpr (Or.inl rfl)
      · rcases hY (code x) (hW x hx hx1) with h4 | h4
        · exact absurd (ccomm_iff.mpr (hcomm c hc x hx)) (by simpa using h4)
        · exact List.contains_iff_mem.mp h4
    · intro hx
      rcases mem_e8_iff.mp hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact one_mem A
      · exact ha
      · exact hb
      · exact hc
      · exact mul_mem ha hb
      · exact mul_mem ha hc
      · exact mul_mem hb hc
      · exact mul_mem (mul_mem ha hb) hc

theorem normT_spec {S : Subgroup P10} {SL : List (List ℕ)} (hS : Desc S SL) {t : List ℕ}
    (h : Core.normT SL t = true) {τ : P10} (hτ : code τ = t) : τ ∈ normalizer (S : Set P10) := by
  simp only [Core.normT, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  rw [mem_normalizer_iff]
  intro s
  constructor
  · intro hs
    obtain ⟨c, hc, he⟩ := h1 _ ((hS.mem s).mp hs)
    obtain ⟨σ, hσ, rfl⟩ := hS.surj c hc
    rw [← hτ, code_mul_eq_iff] at he
    have e : τ * s * τ⁻¹ = σ := by rw [he]; group
    rw [e]
    exact hσ
  · intro hs
    obtain ⟨c, hc, he⟩ := h2 _ ((hS.mem _).mp hs)
    obtain ⟨σ, hσ, rfl⟩ := hS.surj c hc
    rw [← hτ, code_mul_eq_iff] at he
    have e : s = σ :=
      calc s = τ⁻¹ * (τ * s * τ⁻¹ * τ) := by group
        _ = τ⁻¹ * (τ * σ) := by rw [he]
        _ = σ := by group
    rw [e]
    exact hσ

theorem invCheck_spec {T₀ : Subgroup P10} {TL TLinv : List (List ℕ)} (hT : Desc T₀ TL)
    (hinv : Core.invCheck TL TLinv = true) {h hi : List ℕ} (hmem : (h, hi) ∈ TL.zip TLinv) :
    ∃ y ∈ T₀, code y = h ∧ code y⁻¹ = hi := by
  simp only [Core.invCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hinv
  obtain ⟨⟨-, hprod⟩, hin⟩ := hinv
  obtain ⟨hh, hhi⟩ := List.of_mem_zip hmem
  obtain ⟨y, hy, rfl⟩ := hT.surj h hh
  obtain ⟨z, -, rfl⟩ := hT.surj hi (List.contains_iff_mem.mp (hin _ hhi))
  have h1 := hprod _ hmem
  simp only at h1
  rw [← code_mul, code_eq_cid_iff] at h1
  exact ⟨y, hy, rfl, by rw [eq_inv_of_mul_eq_one_right h1]⟩

theorem entry_spec {T₀ : Subgroup P10} {TL TLinv : List (List ℕ)} (hT : Desc T₀ TL)
    (hinv : Core.invCheck TL TLinv = true) {D : KData} {K : Subgroup P10} (hK : Desc K D.K.lit)
    {en : Entry} (hen : Core.entryCheck TL TLinv D en = true) {A : Subgroup P10}
    (hA : ∀ x, x ∈ A ↔ code x ∈ en.E) :
    A ≤ K ∧ CFSG.Quasithin.coreIn (T₀ ⊓ centralizer (A : Set P10)) T₀ ≤ K ⊓ T₀ ∧
      ∀ R : Subgroup P10, A ≤ R → R ≤ K ⊓ T₀ →
        ¬ K ⊔ (T₀ ⊓ normalizer ((K ⊓ T₀ : Subgroup P10) : Set P10)) ≤
          normalizer (R : Set P10) := by
  simp only [Core.entryCheck, Bool.and_eq_true, and_assoc] at hen
  obtain ⟨hET, hEK, hcore, hk1, hk2, ht, hnT, he, hv⟩ := hen
  have hS := hK.inf hT
  have hEsurj : ∀ c ∈ en.E, ∃ x ∈ A, code x = c := by
    intro c hc
    obtain ⟨x, -, rfl⟩ := hT.surj c (List.contains_iff_mem.mp ((List.all_eq_true.mp hET) c hc))
    exact ⟨x, (hA x).mpr hc, rfl⟩
  refine ⟨fun x hx => ?_, fun x hx => ?_, fun R hAR hRK hle => ?_⟩
  · exact (hK.mem x).mpr (List.contains_iff_mem.mp ((List.all_eq_true.mp hEK) _ ((hA x).mp hx)))
  · obtain ⟨hxT, hxc⟩ := hx
    refine ⟨?_, hxT⟩
    have h1 := (List.all_eq_true.mp hcore) (code x) ((hT.mem x).mp hxT)
    simp only [Bool.or_eq_true, List.any_eq_true, Bool.not_eq_true'] at h1
    rcases h1 with h1 | ⟨⟨h, hinv'⟩, hmem, e, heE, hne⟩
    · exact (hK.mem x).mpr (List.contains_iff_mem.mp h1)
    · exfalso
      obtain ⟨y, hyT, rfl, rfl⟩ := invCheck_spec hT hinv hmem
      obtain ⟨ε, hεA, rfl⟩ := hEsurj e heE
      have hc : y⁻¹ * x * y ∈ centralizer (A : Set P10) := (hxc y hyT).2
      rw [mem_centralizer_iff] at hc
      have h2 : ccomm (Core.cmul (Core.cmul (code y⁻¹) (code x)) (code y)) (code ε) = true := by
        rw [← code_mul, ← code_mul, ccomm_iff]
        exact (hc ε hεA).symm
      simp only at hne
      rw [h2] at hne
      exact Bool.noConfusion hne
  · obtain ⟨κ1, hκ1, h1⟩ := hK.surj _ (List.contains_iff_mem.mp hk1)
    obtain ⟨κ2, hκ2, h2⟩ := hK.surj _ (List.contains_iff_mem.mp hk2)
    obtain ⟨τ, hτ, h3⟩ := hT.surj _ (List.contains_iff_mem.mp ht)
    obtain ⟨ε, hεA, h4⟩ := hEsurj _ (List.contains_iff_mem.mp he)
    have hτN := normT_spec hS hnT h3
    have hj : κ1 * τ * κ2 ∈ normalizer (R : Set P10) :=
      hle (mul_mem (mul_mem (mem_sup_left hκ1) (mem_sup_right ⟨hτ, hτN⟩)) (mem_sup_left hκ2))
    have hjR : κ1 * τ * κ2 * ε * (κ1 * τ * κ2)⁻¹ ∈ R := (mem_normalizer_iff.mp hj ε).mp (hAR hεA)
    have h5 := (List.all_eq_true.mp hv) _ ((hS.mem _).mp (hRK hjR))
    rw [← h1, ← h2, ← h3, ← h4, ← code_mul, ← code_mul, ← code_mul, ← code_mul,
      Bool.not_eq_true', beq_eq_false_iff_ne] at h5
    exact h5 (by congr 1; group)

theorem pair_spec {G T₀ : Subgroup P10} {TL GLc : List (List ℕ)} (hT : Desc T₀ TL)
    (hGL : ∀ c ∈ GLc, ∃ x ∈ G, code x = c) {ws : List PairW}
    (h : Core.pairCheck TL GLc ws = true) :
    ∀ x ∈ T₀, orderOf x = 2 → ∃ m ∈ G, ∃ n ∈ G, m * x * m⁻¹ ∈ T₀ ∧ n * x * n⁻¹ ∈ T₀ ∧
      (m * x * m⁻¹) * (n * x * n⁻¹) ≠ (n * x * n⁻¹) * (m * x * m⁻¹) := by
  intro x hx hx2
  have hx1 : x ≠ 1 := by
    rintro rfl
    simp at hx2
  have hxx : x * x = 1 := by rw [← pow_two, ← hx2, pow_orderOf_eq_one]
  unfold Core.pairCheck at h
  have h1 := (List.all_eq_true.mp h) (code x) ((hT.mem x).mp hx)
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true', List.any_eq_true,
    Bool.and_eq_true] at h1
  rcases h1 with (h1 | h1) | ⟨w, -, ⟨⟨⟨⟨⟨⟨hwx, hm⟩, hn⟩, hy⟩, hz⟩, hmy⟩, hnz⟩, hyz⟩
  · exact absurd (code_eq_cid_iff.mp h1) hx1
  · rw [cinvol_iff.mpr hxx] at h1
    exact Bool.noConfusion h1
  · obtain ⟨m, hmG, hmc⟩ := hGL _ (List.contains_iff_mem.mp hm)
    obtain ⟨n, hnG, hnc⟩ := hGL _ (List.contains_iff_mem.mp hn)
    obtain ⟨y, hyT, hyc⟩ := hT.surj _ (List.contains_iff_mem.mp hy)
    obtain ⟨z, hzT, hzc⟩ := hT.surj _ (List.contains_iff_mem.mp hz)
    rw [← hmc, ← hyc, code_mul_eq_iff] at hmy
    rw [← hnc, ← hzc, code_mul_eq_iff] at hnz
    have e1 : m * x * m⁻¹ = y := by rw [hmy]; group
    have e2 : n * x * n⁻¹ = z := by rw [hnz]; group
    refine ⟨m, hmG, n, hnG, e1 ▸ hyT, e2 ▸ hzT, ?_⟩
    rw [e1, e2]
    intro hc
    have h3 := ccomm_iff.mpr hc
    rw [hyc, hzc, hyz] at h3
    exact Bool.noConfusion h3

theorem nonNormal_spec {T₀ : Subgroup P10} {TL TLinv : List (List ℕ)} (hT : Desc T₀ TL)
    (hinv : Core.invCheck TL TLinv = true) {E : List (List ℕ)} (hET : E.all TL.contains = true)
    (h : Core.nonNormal TL TLinv E = true) {A : Subgroup P10} (hA : ∀ x, x ∈ A ↔ code x ∈ E) :
    ¬ T₀ ≤ normalizer (A : Set P10) := by
  intro hTN
  simp only [Core.nonNormal, List.any_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨hc, hic⟩, hmem, e, heE, hne⟩ := h
  obtain ⟨y, hyT, rfl, rfl⟩ := invCheck_spec hT hinv hmem
  obtain ⟨ε, -, rfl⟩ := hT.surj e (List.contains_iff_mem.mp ((List.all_eq_true.mp hET) e heE))
  have h1 : y * ε * y⁻¹ ∈ A := (mem_normalizer_iff.mp (hTN hyT) ε).mp ((hA ε).mpr heE)
  rw [hA, code_mul, code_mul] at h1
  simp only at hne
  rw [List.contains_iff_mem.mpr h1] at hne
  exact Bool.noConfusion hne

theorem close_spec {T₀ : Subgroup P10} {TL : List (List ℕ)} (hT : Desc T₀ TL) {D : KData}
    {K N : Subgroup P10} (hK : Desc K D.K.lit) (hN : Desc N D.N2.lit) (hNK : N ≤ pCoreOf 2 K)
    {Est : List (List ℕ)} (hET : Est.all TL.contains = true)
    (h : Core.closeCheck TL D Est = true) {E : Subgroup P10} (hE : ∀ x, x ∈ E ↔ code x ∈ Est) :
    D.p = 3 ∧ E ≤ pCoreOf 2 K ∧ T₀ ⊓ centralizer (E : Set P10) ≤ K ∧ ¬ K ≤ T₀ := by
  simp only [Core.closeCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.any_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨hp, hEN⟩, hcen⟩, ⟨k, hk, hkT⟩⟩ := h
  refine ⟨hp, fun x hx => hNK ((hN.mem x).mpr (List.contains_iff_mem.mp
    (hEN _ ((hE x).mp hx)))), fun x hx => ?_, fun hKT => ?_⟩
  · obtain ⟨hxT, hxc⟩ := hx
    rcases hcen _ ((hT.mem x).mp hxT) with h1 | ⟨e, heE, hne⟩
    · exact (hK.mem x).mpr (List.contains_iff_mem.mp h1)
    · exfalso
      obtain ⟨ε, -, rfl⟩ := hT.surj e (List.contains_iff_mem.mp (List.all_eq_true.mp hET e heE))
      have hxc' : x ∈ centralizer (E : Set P10) := hxc
      rw [mem_centralizer_iff] at hxc'
      rw [ccomm_iff.mpr (hxc' ε ((hE ε).mpr heE)).symm] at hne
      exact Bool.noConfusion hne
  · obtain ⟨κ, hκ, rfl⟩ := hK.surj k hk
    rw [List.contains_iff_mem.mpr ((hT.mem κ).mp (hKT hκ))] at hkT
    exact Bool.noConfusion hkT

theorem ov_spec {T₀ : Subgroup P10} {TL : List (List ℕ)} (hT : Desc T₀ TL)
    {reps repsInv : List (List ℕ)} {cert : List (List ℕ × ℕ × List ℕ × List ℕ)}
    {words : List (List (List (List ℕ)))} (h : Core.ovCheck TL reps repsInv cert words = true)
    {H : Subgroup P10} (hTH : T₀ ≤ H) {k : P10} (hk : k ∈ A6Models.psl29) (hkT : k ∉ T₀)
    (hkH : k ∈ H) : A6Models.psl29 ≤ H := by
  simp only [Core.ovCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hlen, hrps⟩, hrinvps⟩, hri⟩, hkeys⟩, hcert⟩, hwords⟩ := h
  have hkL : code k ∈ Core.pslLit := (mem_psl29_iff k).1 hk
  have hkn : TL.contains (code k) = false := by
    rw [Bool.eq_false_iff]
    intro h1
    exact hkT ((hT.mem k).mpr (List.contains_iff_mem.mp h1))
  have hkey : code k ∈ cert.map (fun e => e.1) := by
    rw [hkeys, List.mem_filter]
    exact ⟨hkL, by rw [hkn]; rfl⟩
  obtain ⟨⟨ek, i, p, q⟩, he, hek⟩ := List.mem_map.mp hkey
  simp only at hek
  subst hek
  obtain ⟨⟨⟨hi, hp⟩, hq⟩, heq⟩ := hcert _ he
  simp only [decide_eq_true_eq] at hi
  have hp := List.contains_iff_mem.mp hp
  have hq := List.contains_iff_mem.mp hq
  obtain ⟨σp, hσp, rfl⟩ := hT.surj p hp
  obtain ⟨σq, hσq, rfl⟩ := hT.surj q hq
  have hgetD : ∀ (l : List (List ℕ)) (j : ℕ), j < l.length → l.getD j [] ∈ l := by
    intro l j hj
    rw [List.getD_eq_getElem _ _ hj]
    exact List.getElem_mem hj
  obtain ⟨ρ, -, hρc⟩ := exists_psl29_of_code
    (List.contains_iff_mem.mp (hrps _ (hgetD reps i hi)))
  obtain ⟨ρ', -, hρ'c⟩ := exists_psl29_of_code
    (List.contains_iff_mem.mp (hrinvps _ (hgetD repsInv i (hlen ▸ hi))))
  rw [← hρc, ← code_mul, ← code_mul] at heq
  have hkeq := code_injective heq
  have hρH : ρ ∈ H := by
    have e : ρ = σp⁻¹ * (σp * ρ * σq) * σq⁻¹ := by group
    rw [e, hkeq]
    exact mul_mem (mul_mem (inv_mem (hTH hσp)) hkH) (inv_mem (hTH hσq))
  have hρρ' : ρ' = ρ⁻¹ := by
    have h1 := hri i (List.mem_range.mpr hi)
    rw [← hρc, ← hρ'c, ← code_mul, code_eq_cid_iff] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hgens : ∀ j : ℕ, j < 3 → pslGens.getD j 1 ∈ H := by
    intro j hj
    have h2 := hwords i (List.mem_range.mpr hi) j (List.mem_range.mpr hj)
    simp only [Core.ovWordOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true,
      List.contains_iff_mem] at h2
    obtain ⟨hletters, hprod⟩ := h2
    have hmem : ∀ a ∈ (words.getD i []).getD j [], ∃ σ ∈ H, code σ = a := by
      intro a ha
      rcases hletters a ha with (h3 | h3) | h3
      · obtain ⟨σ, hσ, rfl⟩ := hT.surj a h3
        exact ⟨σ, hTH hσ, rfl⟩
      · exact ⟨ρ, hρH, by rw [hρc, h3]⟩
      · exact ⟨ρ', hρρ' ▸ inv_mem hρH, by rw [hρ'c, h3]⟩
    obtain ⟨σ, hσH, hσc⟩ := eval_word_mem ((words.getD i []).getD j []) 1 H.one_mem hmem
    rw [code_one] at hσc
    have hgc : code (pslGens.getD j 1) = Core.pslGenC.getD j [] := by
      rw [← pslGens_code]
      have : j < pslGens.length := by simpa [pslGens] using hj
      exact (getD_map_code pslGens j this).symm
    have e : σ = pslGens.getD j 1 := code_injective (by rw [hσc, hprod, hgc])
    rw [← e]
    exact hσH
  rw [psl29_eq, closure_le]
  intro g hg
  simp only [pslGens, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hg
  rcases hg with rfl | rfl | rfl
  · exact hgens 0 (by norm_num)
  · exact hgens 1 (by norm_num)
  · exact hgens 2 (by norm_num)

theorem max_of_overgroup {Y : Type} [Group Y] [Finite Y] {G L T : Subgroup Y}
    (hsyl : IsSylowIn 2 T G) (hsq : ∀ x ∈ G, x * x ∈ L) (hsup : L ⊔ T = G)
    (hov : ∀ H : Subgroup Y, T ≤ H → ∀ k ∈ L, k ∉ T → k ∈ H → L ≤ H) :
    ∀ H : Subgroup Y, T ≤ H → H ≤ G → H = T ∨ H = G := by
  intro H hTH hHG
  by_cases hHT : H ≤ T
  · exact Or.inl (le_antisymm hHT hTH)
  right
  have h1 := relIndex_mul_relIndex T H G hTH hHG
  have hodd : ¬ 2 ∣ T.relIndex H := fun h => hsyl.not_dvd_relIndex (h1 ▸ dvd_mul_of_dvd_left h _)
  have hne1 : T.relIndex H ≠ 1 := fun h => hHT (relIndex_eq_one.mp h)
  obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hne1
  have hq2 : q ≠ 2 := fun h => hodd (h ▸ hqd)
  have hqH : q ∣ Nat.card H := hqd.trans ⟨_, (relIndex_mul_card T H).symm⟩
  have : Fact q.Prime := ⟨hq⟩
  have : Fintype H := Fintype.ofFinite H
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card (G := H) q (by rwa [← Nat.card_eq_fintype_card])
  have hk : orderOf (x : Y) = q := by rw [orderOf_coe, hx]
  have hkG : (x : Y) ∈ G := hHG x.2
  have hkL : (x : Y) ∈ L := by
    obtain ⟨r, hr⟩ := hq.odd_of_ne_two hq2
    have e : (x : Y) = ((x : Y) * (x : Y)) ^ (r + 1) := by
      rw [← pow_two, ← pow_mul, show 2 * (r + 1) = q + 1 by omega, pow_succ, ← hk,
        pow_orderOf_eq_one, one_mul]
    rw [e]
    exact pow_mem (hsq _ hkG) _
  have hkT : (x : Y) ∉ T := by
    intro hkT
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hsyl.isPGroup) ⟨_, hkT⟩
    rw [Subgroup.orderOf_mk, hk] at hn
    rcases n with _ | n
    · exact hq.one_lt.ne' (by simpa using hn)
    · exact hq2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).mp
        (hn ▸ dvd_pow_self 2 (Nat.succ_ne_zero n))).symm
  exact le_antisymm hHG (hsup ▸ sup_le (hov H hTH _ hkL hkT x.2) hTH)

theorem le_of_normal_psl {G : Subgroup P10} (hGA : G ≤ A6Models.autA6)
    (hLG : A6Models.psl29 ≤ G) (K : Subgroup P10) (hKG : K ≤ G)
    (hKn : ∀ g ∈ G, ∀ x ∈ K, g * x * g⁻¹ ∈ K) (hK1 : K ≠ ⊥) : A6Models.psl29 ≤ K := by
  obtain ⟨-, ψ, -, -⟩ := CFSG.QuasithinUnique.Unc25K1.A6Model.exists_pslEquiv
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup ↥A6Models.psl29 := ψ.isSimpleGroup
  have hN : (K.subgroupOf A6Models.psl29).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    simpa using hKn g (hLG g.2) n hn⟩
  have := hs
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf A6Models.psl29) with h | h
  · exfalso
    apply hK1
    rw [eq_bot_iff]
    intro k hk
    rw [mem_bot]
    refine centralizer_psl29 (hGA (hKG hk)) fun l hl => ?_
    have hc1 : k * l * k⁻¹ * l⁻¹ ∈ K := by
      have h2 : l * k⁻¹ * l⁻¹ ∈ K := hKn l (hLG hl) _ (inv_mem hk)
      simpa [mul_assoc] using mul_mem hk h2
    have hc2 : k * l * k⁻¹ * l⁻¹ ∈ A6Models.psl29 :=
      mul_mem (psl29_normal k (hGA (hKG hk)) l hl) (inv_mem hl)
    have h3 : (⟨_, hc2⟩ : ↥A6Models.psl29) ∈ K.subgroupOf A6Models.psl29 := by
      rw [mem_subgroupOf]
      exact hc1
    rw [h, mem_bot] at h3
    have h4 : k * l * k⁻¹ * l⁻¹ = 1 := congrArg Subtype.val h3
    calc k * l = (k * l * k⁻¹ * l⁻¹) * l * k := by group
      _ = l * k := by rw [h4, one_mul]
  · intro l hl
    have h2 : (⟨l, hl⟩ : ↥A6Models.psl29) ∈ K.subgroupOf A6Models.psl29 := h ▸ mem_top _
    exact h2

theorem sq_mem_of_reps {G : Subgroup P10} {reps : List P10}
    (hreps : ∀ r ∈ reps, r ∈ A6Models.autA6 ∧ r * r ∈ A6Models.psl29)
    (hmem : ∀ x ∈ G, ∃ r ∈ reps, x * r⁻¹ ∈ A6Models.psl29) :
    ∀ x ∈ G, x * x ∈ A6Models.psl29 := by
  intro x hx
  obtain ⟨r, hr, hxr⟩ := hmem x hx
  obtain ⟨hrA, hrr⟩ := hreps r hr
  have e : x * x = (x * r⁻¹) * (r * (x * r⁻¹) * r⁻¹) * (r * r) := by group
  rw [e]
  exact mul_mem (mul_mem hxr (psl29_normal r hrA _ hxr)) hrr

theorem getD_mem_of_lt {α : Type*} {l : List α} {i : ℕ} (d : α) (hi : i < l.length) :
    l.getD i d ∈ l := by
  rw [List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

theorem entry_data {TL TLinv : List (List ℕ)} {Ks : List KData} {Es : List Entry}
    (hE : Core.entriesCheck TL TLinv Ks Es = true) {en : Entry} (hen : en ∈ Es) :
    Ks.getD en.k KData.dflt ∈ Ks ∧ Core.entryCheck TL TLinv (Ks.getD en.k KData.dflt) en = true := by
  have h1 := (List.all_eq_true.mp hE) en hen
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  exact ⟨getD_mem_of_lt _ h1.1, h1.2⟩

theorem entry_E_sub {TL TLinv : List (List ℕ)} {D : KData} {en : Entry}
    (h : Core.entryCheck TL TLinv D en = true) : en.E.all TL.contains = true := by
  simp only [Core.entryCheck, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1.1.1

theorem table_spec {G T₀ : Subgroup P10} {TL TLinv : List (List ℕ)} {Ks : List KData}
    {Es : List Entry} (hT : Desc T₀ TL) (hT2 : IsPGroup 2 T₀)
    (hinv : Core.invCheck TL TLinv = true) (hKs : ∀ D ∈ Ks, D.check TL = true)
    (hgens : ∀ D ∈ Ks, ∀ c ∈ D.K.gc, ∃ x ∈ (G : Set P10), code x = c)
    (hE : Core.entriesCheck TL TLinv Ks Es = true)
    (hseed : Core.seedCheck TL (Es.map Entry.E) = true)
    (hmax : ∀ D ∈ Ks, D.p = 3 ∨ ∀ H : Subgroup P10, T₀ ≤ H → H ≤ G → H = T₀ ∨ H = G) :
    ∀ A : Subgroup P10, A ≤ T₀ → IsElemAbelian 2 A → 4 ≤ Nat.card A →
    ∃ (K Z : Subgroup P10) (p : ℕ), K ≤ G ∧ A ≤ K ∧ TwoPTwo K (K ⊓ T₀) Z p ∧ Nat.card Z = p ∧
      CFSG.Quasithin.coreIn (T₀ ⊓ centralizer (A : Set P10)) T₀ ≤ K ⊓ T₀ ∧
      (∀ R : Subgroup P10, A ≤ R → R ≤ K ⊓ T₀ →
        ¬ K ⊔ (T₀ ⊓ normalizer ((K ⊓ T₀ : Subgroup P10) : Set P10)) ≤
          normalizer (R : Set P10)) ∧
      (p = 3 ∨ ∀ H : Subgroup P10, T₀ ≤ H → H ≤ G → H = T₀ ∨ H = G) := by
  intro A hAT hAe hA4
  obtain ⟨E, hE', hA⟩ := seed_spec hT hseed hAT hAe hA4
  obtain ⟨en, hen, rfl⟩ := List.mem_map.mp hE'
  obtain ⟨hD, hchk⟩ := entry_data hE hen
  obtain ⟨K, hKG, hK, -, ⟨Z, h2, hZ⟩, -⟩ := KData.spec hT hT2 (hKs _ hD) (hgens _ hD)
  obtain ⟨hAK, hcore, hR⟩ := entry_spec hT hinv hK hchk hA
  exact ⟨K, Z, _, hKG, hAK, h2, hZ, hcore, hR, hmax _ hD⟩

theorem close_vacuous {T₀ : Subgroup P10} {TL TLinv : List (List ℕ)} {Ks : List KData}
    {Es : List Entry} (hT : Desc T₀ TL) (hinv : Core.invCheck TL TLinv = true)
    (hE : Core.entriesCheck TL TLinv Ks Es = true)
    (hseed : Core.seedCheck TL (Es.map Entry.E) = true)
    (hnn : Es.all (fun en => Core.nonNormal TL TLinv en.E) = true) {E : Subgroup P10}
    (hET : E ≤ T₀) (hTE : T₀ ≤ normalizer (E : Set P10)) (hEe : IsElemAbelian 2 E)
    (hE4 : 4 ≤ Nat.card E) : False := by
  obtain ⟨F, hF', hA⟩ := seed_spec hT hseed hET hEe hE4
  obtain ⟨en, hen, rfl⟩ := List.mem_map.mp hF'
  exact nonNormal_spec hT hinv (entry_E_sub (entry_data hE hen).2)
    ((List.all_eq_true.mp hnn) en hen) hA hTE

theorem close_star {G T₀ : Subgroup P10} {TL TLinv : List (List ℕ)} {Ks : List KData}
    {Es : List Entry} {iStar : ℕ} (hT : Desc T₀ TL) (hT2 : IsPGroup 2 T₀) (hTG : T₀ ≤ G)
    (hinv : Core.invCheck TL TLinv = true) (hKs : ∀ D ∈ Ks, D.check TL = true)
    (hgens : ∀ D ∈ Ks, ∀ c ∈ D.K.gc, ∃ x ∈ (G : Set P10), code x = c)
    (hE : Core.entriesCheck TL TLinv Ks Es = true)
    (hseed : Core.seedCheck TL (Es.map Entry.E) = true)
    (hnn : (List.range Es.length).all (fun i => i == iStar ||
      Core.nonNormal TL TLinv (Es.getD i ⟨[], 0, [], [], [], []⟩).E) = true)
    (hclose : Core.closeCheck TL (Ks.getD (Es.getD iStar ⟨[], 0, [], [], [], []⟩).k KData.dflt)
      (Es.getD iStar ⟨[], 0, [], [], [], []⟩).E = true)
    (hmax : ∀ H : Subgroup P10, T₀ ≤ H → H ≤ G → H = T₀ ∨ H = G) {E : Subgroup P10}
    (hET : E ≤ T₀) (hTE : T₀ ≤ normalizer (E : Set P10)) (hEe : IsElemAbelian 2 E)
    (hE4 : 4 ≤ Nat.card E) :
    ∃ K Z : Subgroup P10, K ≤ G ∧ TwoPTwo K (K ⊓ T₀) Z 3 ∧ Nat.card Z = 3 ∧
      E ≤ pCoreOf 2 K ∧ T₀ ⊓ centralizer (E : Set P10) ≤ K ∧ K ⊔ T₀ = G := by
  obtain ⟨F, hF', hA⟩ := seed_spec hT hseed hET hEe hE4
  obtain ⟨en, hen, rfl⟩ := List.mem_map.mp hF'
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hen
  have hgi : Es.getD i ⟨[], 0, [], [], [], []⟩ = Es[i] := List.getD_eq_getElem _ _ hi
  have hiS : i = iStar := by
    have h1 := (List.all_eq_true.mp hnn) i (List.mem_range.mpr hi)
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with h1 | h1
    · exact h1
    · rw [hgi] at h1
      exact absurd hTE (nonNormal_spec hT hinv (entry_E_sub (entry_data hE hen).2) h1 hA)
  subst hiS
  rw [hgi] at hclose
  obtain ⟨hD, -⟩ := entry_data hE hen
  obtain ⟨K, hKG, hK, -, ⟨Z, h2, hZ⟩, N, hN, hNK⟩ := KData.spec hT hT2 (hKs _ hD) (hgens _ hD)
  obtain ⟨hp, hEK, hcen, hKT⟩ := close_spec hT hK hN hNK (entry_E_sub (entry_data hE hen).2)
    hclose hA
  rw [hp] at h2 hZ
  refine ⟨K, Z, hKG, h2, hZ, hEK, hcen, ?_⟩
  rcases hmax (K ⊔ T₀) le_sup_right (sup_le hKG hTG) with h | h
  · exact absurd (le_sup_left.trans h.le) hKT
  · exact h

theorem sup_eq_of_card {Y : Type} [Group Y] [Finite Y] {G L T : Subgroup Y} (hLG : L ≤ G)
    (hTG : T ≤ G) {a b c : ℕ} (hL : Nat.card L = a) (hT : Nat.card T = b) (hG : Nat.card G = c)
    (hc : c ∣ Nat.lcm a b) : L ⊔ T = G := by
  refine eq_of_le_of_card_ge (sup_le hLG hTG) ?_
  rw [hG]
  have h1 : a ∣ Nat.card (L ⊔ T : Subgroup Y) := hL ▸ card_dvd_of_le le_sup_left
  have h2 : b ∣ Nat.card (L ⊔ T : Subgroup Y) := hT ▸ card_dvd_of_le le_sup_right
  exact Nat.le_of_dvd Nat.card_pos (hc.trans (Nat.lcm_dvd h1 h2))

end CFSG.LocalAnalysis.WeakClosure81.NFA6
