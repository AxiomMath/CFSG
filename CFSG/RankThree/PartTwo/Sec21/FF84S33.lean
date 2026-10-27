module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs
public import CFSG.RankThree.PartTwo.Sec4.Steps434
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Coprime
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaithRank
public import CFSG.Quasithin.EmptyFaithful.SBc17L45Syl

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.RankThree.LocalRank (aschbacherSolvableCore)

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B : Subgroup G}

theorem commute_of_mem_elemAb {x y : G} (hB : IsElementaryAbelian 3 B)
    (hx : x ∈ B) (hy : y ∈ B) : Commute x y := by
  have h := (IsMulCommutative.is_comm (M := B)).comm ⟨x, hx⟩ ⟨y, hy⟩
  exact congrArg Subtype.val h

theorem not_le_closure_pair {x y : G} (hB27 : Nat.card B = 3 ^ 3)
    (hxy : x * y = y * x) (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hle : B ≤ Subgroup.closure ({x, y} : Set G)) : False := by
  have h1 := Subgroup.card_le_of_le hle
  have h2 := CFSG.RankThree.PartTwo.Sec19.Item19Res5Proof.card_closure_pair_le_nine hxy hx hy
  rw [hB27] at h1
  omega

theorem mem_B_b (hs : FF84Sec3 b L B b₁ b₂) : b ∈ B := by
  rw [hs.mono.2.1]; exact Subgroup.subset_closure (by simp)

theorem mem_B_b₁ (hs : FF84Sec3 b L B b₁ b₂) : b₁ ∈ B := by
  rw [hs.mono.2.1]; exact Subgroup.subset_closure (by simp)

theorem mem_B_b₂ (hs : FF84Sec3 b L B b₁ b₂) : b₂ ∈ B := by
  rw [hs.mono.2.1]; exact Subgroup.subset_closure (by simp)

theorem pow3_of_mem_B (hs : FF84Sec3 b L B b₁ b₂) {x : G} (hx : x ∈ B) : x ^ 3 = 1 := by
  haveI := hs.mono.1.1
  exact elemPow_eq_one_of_isElementaryAbelian x hx

theorem comm_of_mem_B (hs : FF84Sec3 b L B b₁ b₂) {x y : G} (hx : x ∈ B) (hy : y ∈ B) :
    Commute x y :=
  commute_of_mem_elemAb hs.mono.1.1 hx hy

theorem B_le_of_mem (hs : FF84Sec3 b L B b₁ b₂) {K : Subgroup G} (hb : b ∈ K) (h1 : b₁ ∈ K)
    (h2 : b₂ ∈ K) : B ≤ K := by
  rw [hs.mono.2.1]
  refine (Subgroup.closure_le _).2 ?_
  intro z hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl <;> assumption

theorem b₁_notin_K (hs : FF84Sec3 b L B b₁ b₂) :
    b₁ ∉ Subgroup.closure ({b, b₁ * b₂} : Set G) := by
  intro h
  have hK : b₁ * b₂ ∈ Subgroup.closure ({b, b₁ * b₂} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hb₂ : b₂ ∈ Subgroup.closure ({b, b₁ * b₂} : Set G) := by
    have := mul_mem (inv_mem h) hK
    simpa using this
  have hbK : b ∈ Subgroup.closure ({b, b₁ * b₂} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hc : b₁ * b₂ ∈ B := mul_mem (mem_B_b₁ hs) (mem_B_b₂ hs)
  have hcomm : b * (b₁ * b₂) = (b₁ * b₂) * b :=
    ((comm_of_mem_B hs (mem_B_b hs) (mem_B_b₁ hs)).mul_right
      (comm_of_mem_B hs (mem_B_b hs) (mem_B_b₂ hs)))
  exact not_le_closure_pair hs.mono.1.2 hcomm
    (pow3_of_mem_B hs (mem_B_b hs)) (pow3_of_mem_B hs hc)
    (B_le_of_mem hs hbK h hb₂)

theorem b₁_inv_notin_K (hs : FF84Sec3 b L B b₁ b₂) :
    b₁⁻¹ ∉ Subgroup.closure ({b, b₁ * b₂} : Set G) := fun h =>
  b₁_notin_K hs (by simpa using inv_mem h)

theorem b₂_notin_K (hs : FF84Sec3 b L B b₁ b₂) :
    b₂ ∉ Subgroup.closure ({b, b₁ * b₂} : Set G) := by
  intro h
  apply b₁_notin_K hs
  have := mul_mem (Subgroup.subset_closure (by simp : b₁ * b₂ ∈ ({b, b₁ * b₂} : Set G))) (inv_mem h)
  simpa using this

theorem b₂_inv_notin_K (hs : FF84Sec3 b L B b₁ b₂) :
    b₂⁻¹ ∉ Subgroup.closure ({b, b₁ * b₂} : Set G) := fun h =>
  b₂_notin_K hs (by simpa using inv_mem h)

theorem b₁b₂_ne_one (hs : FF84Sec3 b L B b₁ b₂) : b₁ * b₂ ≠ 1 := by
  intro h
  have hb₂ : b₂ = b₁⁻¹ := eq_inv_of_mul_eq_one_right h
  have hbB := mem_B_b hs
  have hb1 := mem_B_b₁ hs
  refine not_le_closure_pair hs.mono.1.2 (comm_of_mem_B hs hbB hb1)
    (pow3_of_mem_B hs hbB) (pow3_of_mem_B hs hb1) (B_le_of_mem hs ?_ ?_ ?_)
  · exact Subgroup.subset_closure (by simp)
  · exact Subgroup.subset_closure (by simp)
  · rw [hb₂]; exact inv_mem (Subgroup.subset_closure (by simp))

theorem fusion_mem (hs : FF84Sec3 b L B b₁ b₂) {g : G} (hg : g * b * g⁻¹ ∈ B) :
    g * b * g⁻¹ ∈ ({b, b⁻¹, b₁, b₁⁻¹, b₂, b₂⁻¹} : Set G) := by
  obtain ⟨n, hn, hnb⟩ := hs.fus b (mem_B_b hs) (g * b * g⁻¹) hg g rfl
  rw [← hnb]
  exact hs.mono.2.2.1 n hn b (by simp)

theorem fusion_eq_b_or (hs : FF84Sec3 b L B b₁ b₂) {g : G} (hg : g * b * g⁻¹ ∈ B)
    (hK : g * b * g⁻¹ ∈ Subgroup.closure ({b, b₁ * b₂} : Set G)) :
    g * b * g⁻¹ = b ∨ g * b * g⁻¹ = b⁻¹ := by
  have hmem := fusion_mem hs hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h | h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · rw [h] at hK; exact absurd hK (b₁_notin_K hs)
  · rw [h] at hK; exact absurd hK (b₁_inv_notin_K hs)
  · rw [h] at hK; exact absurd hK (b₂_notin_K hs)
  · rw [h] at hK; exact absurd hK (b₂_inv_notin_K hs)

theorem isPGroup_of_map_subtype {p : ℕ} {K : Subgroup G} {N : Subgroup K}
    (h : IsPGroup p (N.map K.subtype)) : IsPGroup p N := by
  intro g
  obtain ⟨k, hk⟩ := h ⟨(g : G), Subgroup.mem_map.2 ⟨g, g.2, rfl⟩⟩
  refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
  have h1 := congrArg Subtype.val hk
  simpa using h1

theorem conj_mem_opp3 {a x h : G} (hx : x ∈ Subgroup.centralizer ({a} : Set G))
    (hh : h ∈ Opp 3 (Subgroup.centralizer ({a} : Set G))) :
    x * h * x⁻¹ ∈ Opp 3 (Subgroup.centralizer ({a} : Set G)) := by
  obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hh
  have hN := (CFSG.pPrimeCore_normal (p := 3)
    (G := ↥(Subgroup.centralizer ({a} : Set G)))).conj_mem n hn ⟨x, hx⟩
  refine Subgroup.mem_map.2 ⟨_, hN, ?_⟩
  simp

theorem exists_sylow_map_eq {B : Subgroup G} (hB : IsSylowOf 3 B (Subgroup.centralizer ({b} : Set G))) :
    ∃ P : Sylow 3 ↥(Subgroup.centralizer ({b} : Set G)),
      (P : Subgroup ↥(Subgroup.centralizer ({b} : Set G))).map
        (Subgroup.centralizer ({b} : Set G)).subtype = B := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hH : IsPGroup 3 ↥(B.subgroupOf (Subgroup.centralizer ({b} : Set G))) :=
    isPGroup_of_map_subtype (by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hB.1]; exact hB.2.1)
  have hi : ¬ 3 ∣ (B.subgroupOf (Subgroup.centralizer ({b} : Set G))).index :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 hB.2.2
  refine ⟨CFSG.Quasithin.SBc17.sylowOfIndex _ hH hi, ?_⟩
  change (B.subgroupOf (Subgroup.centralizer ({b} : Set G))).map
    (Subgroup.centralizer ({b} : Set G)).subtype = B
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hB.1]

theorem opp_three_eq_bot (hs : FF84Sec3 b L B b₁ b₂)
    (h2 : IsPGroup 2 (Opp 3 (Subgroup.centralizer ({b₁ * b₂} : Set G))))
    (hSb : Opp 3 (Subgroup.centralizer ({b₁ * b₂} : Set G)) ⊓ Subgroup.centralizer ({b} : Set G) = ⊥) :
    Opp 3 (Subgroup.centralizer ({b₁ * b₂} : Set G)) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : b₁ * b₂ ∈ B := mul_mem (mem_B_b₁ hs) (mem_B_b₂ hs)
  have hBa : ∀ x ∈ B, x ∈ Subgroup.centralizer ({b₁ * b₂} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.2 (comm_of_mem_B hs hx hc).eq
  set S := Opp 3 (Subgroup.centralizer ({b₁ * b₂} : Set G)) with hSdef
  have hBnor : B ≤ Subgroup.normalizer (S : Set G) := fun x hx =>
    Subgroup.mem_normalizer_iff.2 fun h =>
      ⟨fun hh => conj_mem_opp3 (hBa x hx) hh, fun hh => by
        have := conj_mem_opp3 (inv_mem (hBa x hx)) hh
        have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
        rw [e] at this
        exact this⟩
  have hBp : IsPGroup 3 ↥B := hs.sylB.2.1
  have hcop : Nat.Coprime 3 (Nat.card ↥S) := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h2
    rw [hn]
    exact Nat.Coprime.pow_right n (by norm_num)
  have hfac := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_factorization
    3 Nat.prime_three B S hBp hBnor hcop
  have hSC : S ⊓ Subgroup.centralizer (B : Set G) = ⊥ := by
    rw [eq_bot_iff]
    rintro s ⟨hsS, hsC⟩
    have hsb : s ∈ Subgroup.centralizer ({b} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2
        ((Subgroup.mem_centralizer_iff.1 hsC) b (mem_B_b hs)).symm
    have hmem : s ∈ S ⊓ Subgroup.centralizer ({b} : Set G) := ⟨hsS, hsb⟩
    rw [hSb] at hmem
    exact hmem
  have hsub1 : S ≤ ⁅S, B⁆ := by
    calc S = ⁅S, B⁆ ⊔ S ⊓ Subgroup.centralizer (B : Set G) := hfac.symm
      _ = ⁅S, B⁆ ⊔ ⊥ := by rw [hSC]
      _ ≤ ⁅S, B⁆ := by simp
  have hSΘ : S ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b₁ * b₂} : Set G)) := by
    have hN := CFSG.pPrimeCore_normal (p := 3)
      (G := ↥(Subgroup.centralizer ({b₁ * b₂} : Set G)))
    have hNp : IsPGroup 2 ↥(CFSG.pPrimeCore 3 ↥(Subgroup.centralizer ({b₁ * b₂} : Set G))) :=
      isPGroup_of_map_subtype h2
    have hle := CFSG.RankThree.PartTwo.Sec4.le_aschbacherSolvableCore_of_isPGroup
      (p := 2) Nat.prime_two (by norm_num) hN hNp
    exact Subgroup.map_mono hle
  have hodd := hs.hyp.ii₁ B (exists_sylow_map_eq hs.sylB) (b₁ * b₂) hc (b₁b₂_ne_one hs)
  have hdvd : Nat.card ↥S ∣
      Nat.card ↥(⁅inSubgroup (aschbacherSolvableCore 3)
        (Subgroup.centralizer ({b₁ * b₂} : Set G)), B⁆ : Subgroup G) :=
    Subgroup.card_dvd_of_le (hsub1.trans (Subgroup.commutator_mono hSΘ le_rfl))
  have hoddS : Odd (Nat.card ↥S) := Odd.of_dvd_nat hodd hdvd
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 h2
  have hn0 : n = 0 := by
    by_contra hne
    have heven : Even (Nat.card ↥S) := by
      rw [hn]; exact (Nat.even_pow).2 ⟨even_two, hne⟩
    exact (Nat.not_even_iff_odd.2 hoddS) heven
  exact Subgroup.eq_bot_of_card_eq S (by rw [hn, hn0, pow_zero])

theorem mem_nor_zpowers_of_conj {b n : G} (hn : n * b * n⁻¹ = b ∨ n * b * n⁻¹ = b⁻¹) :
    n ∈ Nor (Subgroup.zpowers b) := by
  have hz : n⁻¹ * b * n⁻¹⁻¹ ∈ Subgroup.zpowers b := by
    rw [inv_inv]
    rcases hn with h1 | h1
    · have hc : n * b = b * n := mul_inv_eq_iff_eq_mul.1 h1
      have e : n⁻¹ * b * n = b := by
        calc n⁻¹ * b * n = n⁻¹ * (b * n) := by group
          _ = n⁻¹ * (n * b) := by rw [hc]
          _ = b := by group
      rw [e]; exact Subgroup.mem_zpowers b
    · have h3 : n⁻¹ * b⁻¹ * n = b := by rw [← h1]; group
      have e2 : n⁻¹ * b * n = b⁻¹ := by
        calc n⁻¹ * b * n = (n⁻¹ * b⁻¹ * n)⁻¹ := by group
          _ = b⁻¹ := by rw [h3]
      rw [e2]; exact Subgroup.inv_mem _ (Subgroup.mem_zpowers b)
  simp only [Subgroup.mem_normalizer_iff, SetLike.mem_coe]
  intro h
  constructor
  · intro hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
    rw [← hk, ← conj_zpow]
    rcases hn with h1 | h1
    · rw [h1]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k
    · rw [h1]; exact Subgroup.zpow_mem _ (Subgroup.inv_mem _ (Subgroup.mem_zpowers b)) k
  · intro hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hh' : h = (n⁻¹ * b * n⁻¹⁻¹) ^ k := by
      rw [conj_zpow, hk]; group
    rw [hh']; exact Subgroup.zpow_mem _ hz k

theorem nor_zpowers_transfer {m n c c' : G} (hm : m * c * m⁻¹ = c')
    (hn : n ∈ Nor (Subgroup.zpowers c')) : m⁻¹ * n * m ∈ Nor (Subgroup.zpowers c) := by
  have key : ∀ x : G, x ∈ Subgroup.zpowers c ↔ m * x * m⁻¹ ∈ Subgroup.zpowers c' := by
    intro x
    constructor
    · intro hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      rw [← hm, conj_zpow]
    · intro hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
      refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
      rw [← hm, conj_zpow] at hk
      exact mul_left_cancel (mul_right_cancel hk)
  simp only [Subgroup.mem_normalizer_iff, SetLike.mem_coe] at hn ⊢
  intro h
  rw [key h, hn (m * h * m⁻¹), key ((m⁻¹ * n * m) * h * (m⁻¹ * n * m)⁻¹)]
  rw [show m * ((m⁻¹ * n * m) * h * (m⁻¹ * n * m)⁻¹) * m⁻¹ = n * (m * h * m⁻¹) * n⁻¹ by group]

theorem nor_zpowers_le_nor_b (hs : FF84Sec3 b L B b₁ b₂)
    (hS : Opp 3 (Subgroup.centralizer ({b₁ * b₂} : Set G)) = ⊥)
    (hfac : setMul (Opp 3 (Subgroup.centralizer ({b₁ * b₂} : Set G)))
        (Nor (Subgroup.closure ({b, b₁ * b₂} : Set G))) =
      ↑(Nor (Subgroup.zpowers (b₁ * b₂)))) :
    Nor (Subgroup.zpowers (b₁ * b₂)) ≤ Nor (Subgroup.zpowers b) := by
  intro n hn
  have hn' : n ∈ setMul (Opp 3 (Subgroup.centralizer ({b₁ * b₂} : Set G)))
      (Nor (Subgroup.closure ({b, b₁ * b₂} : Set G))) := by
    rw [hfac]; exact hn
  obtain ⟨h, hh, k, hk, hnk⟩ := hn'
  rw [hS, Subgroup.mem_bot] at hh
  subst hh
  have hc : b₁ * b₂ ∈ B := mul_mem (mem_B_b₁ hs) (mem_B_b₂ hs)
  have hKB : Subgroup.closure ({b, b₁ * b₂} : Set G) ≤ B :=
    (Subgroup.closure_le _).2 (by
      rintro z (rfl | rfl)
      · exact mem_B_b hs
      · exact hc)
  have hbK : b ∈ Subgroup.closure ({b, b₁ * b₂} : Set G) :=
    Subgroup.subset_closure (by simp)
  have hnb : k * b * k⁻¹ ∈ Subgroup.closure ({b, b₁ * b₂} : Set G) :=
    (Subgroup.mem_normalizer_iff.1 hk b).1 hbK
  have hfus := fusion_eq_b_or hs (hKB hnb) hnb
  have hkN := mem_nor_zpowers_of_conj hfus
  rw [one_mul] at hnk
  rw [hnk]
  exact hkN

theorem nor_zpowers_mul_inv_le (hs : FF84Sec3 b L B b₁ b₂)
    (hL2 : Nor (Subgroup.zpowers (b₁ * b₂)) ≤ Nor (Subgroup.zpowers b)) :
    Nor (Subgroup.zpowers (b₁ * b₂⁻¹)) ≤ Nor (Subgroup.zpowers b) := by
  obtain ⟨n₁, hn₁, h1b, h1b₁, h1b₂⟩ := hs.mono.2.2.2.1
  obtain ⟨n₃, hn₃, h3b, h3b₁, h3b₂⟩ := hs.mono.2.2.2.2.2
  have inv_conj : ∀ c x y : G, c * x * c⁻¹ = y → c⁻¹ * y * c = x := by
    intro c x y h; rw [← h]; group
  have conj_id : ∀ c d x : G, (c⁻¹ * d * c) * x * (c⁻¹ * d * c)⁻¹ =
      c⁻¹ * (d * (c * x * c⁻¹) * d⁻¹) * c := by
    intro c d x; group
  set m := n₃⁻¹ * n₁ * n₃ with hm
  have hmN : m ∈ Nor B := mul_mem (mul_mem (inv_mem hn₃) hn₁) hn₃
  have hmb : m * b * m⁻¹ = b := by
    rw [hm, conj_id, h3b, h1b₁]; exact inv_conj n₃ b b₁ h3b
  have hmb₁ : m * b₁ * m⁻¹ = b₁ := by
    rw [hm, conj_id, h3b₁, h1b₂]; exact inv_conj n₃ b₁ b₂ h3b₁
  have hmb₂ : m * b₂ * m⁻¹ = b₂⁻¹ := by
    rw [hm, conj_id, h3b₂, h1b]
    have := inv_conj n₃ b₂ b h3b₂
    rw [show n₃⁻¹ * b⁻¹ * n₃ = (n₃⁻¹ * b * n₃)⁻¹ by group, this]
  have hmc : m * (b₁ * b₂) * m⁻¹ = b₁ * b₂⁻¹ := by
    rw [show m * (b₁ * b₂) * m⁻¹ = (m * b₁ * m⁻¹) * (m * b₂ * m⁻¹) by group, hmb₁, hmb₂]
  have hmNb : m ∈ Nor (Subgroup.zpowers b) := mem_nor_zpowers_of_conj (Or.inl hmb)
  intro n hn
  have hn0 := nor_zpowers_transfer hmc hn
  have hn1 := hL2 hn0
  have key := mul_mem (mul_mem hmNb hn1) (inv_mem hmNb)
  have e : m * (m⁻¹ * n * m) * m⁻¹ = n := by group
  rw [e] at key
  exact key

theorem zpow_mod3 {x : G} (hx3 : x ^ 3 = 1) (hxne : x ≠ 1) (k : ℤ) : x ^ (k % 3) = x ^ k := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf x = 3 := orderOf_eq_prime hx3 hxne
  have := zpow_mod_orderOf x k
  rw [hord] at this
  simpa using this

theorem cen_b_of_nor (hs : FF84Sec3 b L B b₁ b₂) {U : Subgroup G} (hU2 : IsPGroup 2 U)
    (hBU : B ≤ Nor U) {x : G} (hxU : x ∈ U) (hxN : x ∈ Nor (Subgroup.zpowers b)) :
    x ∈ Cen b := by
  have hb3 := pow3_of_mem_B hs (mem_B_b hs)
  have hbord : orderOf b = 3 := hs.hyp.ord
  have hbne : b ≠ 1 := by
    intro h
    have := hbord
    rw [h, orderOf_one] at this
    norm_num at this
  have hxb : x * b * x⁻¹ ∈ Subgroup.zpowers b :=
    (Subgroup.mem_normalizer_iff.1 hxN b).1 (Subgroup.mem_zpowers b)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxb
  have hk3 := zpow_mod3 hb3 hbne k
  have hr0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  have hr1 : k % 3 < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hcase : x * b * x⁻¹ = 1 ∨ x * b * x⁻¹ = b ∨ x * b * x⁻¹ = b⁻¹ := by
    rw [← hk, ← hk3]
    generalize k % 3 = r at hr0 hr1 ⊢
    interval_cases r
    · left; simp
    · right; left; simp
    · right; right
      have h3' : b ^ (3 : ℤ) = 1 := by simpa using hb3
      exact eq_inv_of_mul_eq_one_left (by rw [show b ^ (2 : ℤ) * b = b ^ (3 : ℤ) by group]; exact h3')
  rcases hcase with h | h | h
  · exfalso
    exact hbne (by
      calc b = x⁻¹ * (x * b * x⁻¹) * x := by group
        _ = 1 := by rw [h]; group)
  · exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 h)
  · exfalso
    have hmem1 : b * x⁻¹ * b⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.1 (hBU (mem_B_b hs)) x⁻¹).1 (inv_mem hxU)
    have hprod : x * (b * x⁻¹ * b⁻¹) ∈ U := mul_mem hxU hmem1
    have e : x * (b * x⁻¹ * b⁻¹) = b⁻¹ * b⁻¹ := by
      calc x * (b * x⁻¹ * b⁻¹) = (x * b * x⁻¹) * b⁻¹ := by group
        _ = b⁻¹ * b⁻¹ := by rw [h]
    rw [e] at hprod
    have e3 : b⁻¹ * b⁻¹ = b := by
      have := (show b⁻¹ * b⁻¹ * b ^ 3 = b by group)
      rwa [hb3, mul_one] at this
    rw [e3] at hprod
    obtain ⟨k', hk'⟩ := hU2 ⟨b, hprod⟩
    have hb' : b ^ (2 ^ k') = 1 := by
      have := congrArg Subtype.val hk'
      simpa using this
    have hd : orderOf b ∣ 2 ^ k' := orderOf_dvd_of_pow_eq_one hb'
    rw [hbord] at hd
    have h3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    norm_num at h3

theorem cen_le_of_mem_zpowers {a w : G} (hw : w ∈ Subgroup.zpowers a) :
    Subgroup.centralizer ({a} : Set G) ≤ Subgroup.centralizer ({w} : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  exact ((Commute.zpow_right (show Commute x a from hx) k)).eq

theorem mem_zpowers_of_mem_zpowers_ne_one {a w : G} (ha : a ∈ Subgroup.zpowers w)
    (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1) (ha1 : a ≠ 1) : w ∈ Subgroup.zpowers a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hw : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  have hdvd : orderOf a ∣ 3 := hw ▸ orderOf_dvd_of_mem_zpowers ha
  have ha3 : orderOf a = 3 :=
    (Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three _ hdvd).resolve_left
      (fun h => ha1 (orderOf_eq_one_iff.1 h))
  have hle : Subgroup.zpowers a ≤ Subgroup.zpowers w := Subgroup.zpowers_le.2 ha
  have heq : Subgroup.zpowers a = Subgroup.zpowers w :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, ha3, hw])
  rw [heq]
  exact Subgroup.mem_zpowers w

theorem exists_zpow_mul_of_mem_sup {x y : G} (hc : Commute x y) {a : G}
    (ha : a ∈ Subgroup.zpowers x ⊔ Subgroup.zpowers y) :
    ∃ i j : ℤ, a = x ^ i * y ^ j := by
  let T : Subgroup G :=
    { carrier := {z | ∃ i j : ℤ, z = x ^ i * y ^ j}
      mul_mem' := by
        rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
        refine ⟨i + k, j + l, ?_⟩
        have ce : Commute (y ^ j) (x ^ k) := ((hc.symm.zpow_left j).zpow_right k)
        rw [show x ^ i * y ^ j * (x ^ k * y ^ l) = x ^ i * (y ^ j * x ^ k) * y ^ l by group,
          ce.eq, zpow_add, zpow_add]
        group
      one_mem' := ⟨0, 0, by simp⟩
      inv_mem' := by
        rintro _ ⟨i, j, rfl⟩
        refine ⟨-i, -j, ?_⟩
        have ce : Commute (x ^ (-i)) (y ^ (-j)) := ((hc.zpow_left (-i)).zpow_right (-j))
        rw [mul_inv_rev, ← zpow_neg, ← zpow_neg]
        exact ce.eq.symm }
  have hT : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ T :=
    sup_le (Subgroup.zpowers_le.2 ⟨1, 0, by simp⟩) (Subgroup.zpowers_le.2 ⟨0, 1, by simp⟩)
  obtain ⟨i, j, hij⟩ := hT ha
  exact ⟨i, j, hij⟩

theorem b_ne_one' (hs : FF84Sec3 b L B b₁ b₂) : b ≠ 1 := by
  intro h
  have := hs.hyp.ord
  rw [h, orderOf_one] at this
  norm_num at this

theorem b₁_ne_one (hs : FF84Sec3 b L B b₁ b₂) : b₁ ≠ 1 := fun h =>
  not_le_closure_pair hs.mono.1.2 (comm_of_mem_B hs (mem_B_b hs) (mem_B_b₂ hs))
    (pow3_of_mem_B hs (mem_B_b hs)) (pow3_of_mem_B hs (mem_B_b₂ hs))
    (B_le_of_mem hs (Subgroup.subset_closure (by simp))
      (by rw [h]; exact Subgroup.one_mem _) (Subgroup.subset_closure (by simp)))

theorem b₂_ne_one (hs : FF84Sec3 b L B b₁ b₂) : b₂ ≠ 1 := fun h =>
  not_le_closure_pair hs.mono.1.2 (comm_of_mem_B hs (mem_B_b hs) (mem_B_b₁ hs))
    (pow3_of_mem_B hs (mem_B_b hs)) (pow3_of_mem_B hs (mem_B_b₁ hs))
    (B_le_of_mem hs (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)) (by rw [h]; exact Subgroup.one_mem _))

theorem b₂_notin_zpowers_b₁ (hs : FF84Sec3 b L B b₁ b₂) : b₂ ∉ Subgroup.zpowers b₁ := by
  intro h
  have hle : Subgroup.zpowers b₁ ≤ Subgroup.closure ({b, b₁} : Set G) :=
    Subgroup.zpowers_le.2 (Subgroup.subset_closure (by simp))
  exact not_le_closure_pair hs.mono.1.2 (comm_of_mem_B hs (mem_B_b hs) (mem_B_b₁ hs))
    (pow3_of_mem_B hs (mem_B_b hs)) (pow3_of_mem_B hs (mem_B_b₁ hs))
    (B_le_of_mem hs (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp)) (hle h))

theorem b₁b₂inv_ne_one (hs : FF84Sec3 b L B b₁ b₂) : b₁ * b₂⁻¹ ≠ 1 := by
  intro h
  have he : b₂ = b₁ := (mul_inv_eq_one.1 h).symm
  exact not_le_closure_pair hs.mono.1.2 (comm_of_mem_B hs (mem_B_b hs) (mem_B_b₁ hs))
    (pow3_of_mem_B hs (mem_B_b hs)) (pow3_of_mem_B hs (mem_B_b₁ hs))
    (B_le_of_mem hs (Subgroup.subset_closure (by simp))
      (Subgroup.subset_closure (by simp))
      (by rw [he]; exact Subgroup.subset_closure (by simp)))

theorem elemAb_sup (hs : FF84Sec3 b L B b₁ b₂) :
    IsElementaryAbelian 3 ↥(Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂ : Subgroup G) := by
  haveI : IsElementaryAbelian 3 ↥(Subgroup.zpowers b₁) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (pow3_of_mem_B hs (mem_B_b₁ hs))
  haveI : IsElementaryAbelian 3 ↥(Subgroup.zpowers b₂) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one (pow3_of_mem_B hs (mem_B_b₂ hs))
  have hcomm12 : Commute b₁ b₂ := comm_of_mem_B hs (mem_B_b₁ hs) (mem_B_b₂ hs)
  have hCE : Subgroup.zpowers b₂ ≤ Subgroup.centralizer ((Subgroup.zpowers b₁ : Subgroup G) : Set G) := by
    intro x hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((hcomm12.zpow_left j).zpow_right k).eq
  exact IsElementaryAbelian.sup_of_le_centralizer hCE

theorem nine_le_card_sup (hs : FF84Sec3 b L B b₁ b₂) :
    9 ≤ Nat.card ↥(Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂ : Subgroup G) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI := elemAb_sup hs
  have hb1_3 := pow3_of_mem_B hs (mem_B_b₁ hs)
  have hb1ne := b₁_ne_one hs
  have hpg : IsPGroup 3 ↥(Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂ : Subgroup G) :=
    IsElementaryAbelian.isPGroup 3 _
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hpg
  have hle : Nat.card ↥(Subgroup.zpowers b₁) ≤
      Nat.card ↥(Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂ : Subgroup G) :=
    Subgroup.card_le_of_le le_sup_left
  rw [Nat.card_zpowers, orderOf_eq_prime hb1_3 hb1ne] at hle
  have hne : Nat.card ↥(Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂ : Subgroup G) ≠ 3 := by
    intro hc
    have heq : Subgroup.zpowers b₁ = Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂ :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by
        rw [hc, Nat.card_zpowers, orderOf_eq_prime hb1_3 hb1ne])
    apply b₂_notin_zpowers_b₁ hs
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers b₂)
  rcases Nat.lt_or_ge n 2 with hlt | hge
  · interval_cases n
    · rw [pow_zero] at hn; omega
    · rw [pow_one] at hn; exact absurd hn hne
  · rw [hn]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) hge

theorem nor_zpowers_of_cen {c x : G} (hx : x ∈ Subgroup.centralizer ({c} : Set G)) :
    x ∈ Nor (Subgroup.zpowers c) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx
  simp only [Subgroup.mem_normalizer_iff, SetLike.mem_coe]
  intro h
  constructor
  · intro hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hcx := (Commute.zpow_right (show Commute x c from hx) k).eq
    rw [hcx, mul_inv_cancel_right]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k
  · intro hh
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hcx := (Commute.zpow_right (show Commute x c from hx) k).eq
    have hxc : x⁻¹ * c ^ k * x = c ^ k := by
      calc x⁻¹ * c ^ k * x = x⁻¹ * (c ^ k * x) := by group
        _ = x⁻¹ * (x * c ^ k) := by rw [hcx]
        _ = c ^ k := by group
    have hh' : h = x⁻¹ * c ^ k * x := by
      calc h = x⁻¹ * (x * h * x⁻¹) * x := by group
        _ = x⁻¹ * c ^ k * x := by rw [hk]
    rw [hh', hxc]
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k

theorem key_cen (hs : FF84Sec3 b L B b₁ b₂)
    (hL2 : Nor (Subgroup.zpowers (b₁ * b₂)) ≤ Nor (Subgroup.zpowers b))
    {U : Subgroup G} (hU2 : IsPGroup 2 U) (hBU : B ≤ Nor U)
    {a x : G} (ha : a ∈ Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂) (ha1 : a ≠ 1)
    (hxU : x ∈ U) (hxa : x ∈ Subgroup.centralizer ({a} : Set G)) :
    x ∈ (U ⊓ Cen b₁) ⊔ (U ⊓ Cen b₂) ⊔ (U ⊓ Cen b) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm12 : Commute b₁ b₂ := comm_of_mem_B hs (mem_B_b₁ hs) (mem_B_b₂ hs)
  have hb1_3 := pow3_of_mem_B hs (mem_B_b₁ hs)
  have hb2_3 := pow3_of_mem_B hs (mem_B_b₂ hs)
  have hb1ne := b₁_ne_one hs
  have hb2ne := b₂_ne_one hs
  have hc3 : (b₁ * b₂) ^ 3 = 1 := pow3_of_mem_B hs (mul_mem (mem_B_b₁ hs) (mem_B_b₂ hs))
  have hcne := b₁b₂_ne_one hs
  have hd3 : (b₁ * b₂⁻¹) ^ 3 = 1 :=
    pow3_of_mem_B hs (mul_mem (mem_B_b₁ hs) (inv_mem (mem_B_b₂ hs)))
  have hdne := b₁b₂inv_ne_one hs
  have R1 : U ⊓ Cen b₁ ≤ (U ⊓ Cen b₁) ⊔ (U ⊓ Cen b₂) ⊔ (U ⊓ Cen b) := le_sup_left.trans le_sup_left
  have R2 : U ⊓ Cen b₂ ≤ (U ⊓ Cen b₁) ⊔ (U ⊓ Cen b₂) ⊔ (U ⊓ Cen b) :=
    le_sup_right.trans le_sup_left
  have R3 : U ⊓ Cen b ≤ (U ⊓ Cen b₁) ⊔ (U ⊓ Cen b₂) ⊔ (U ⊓ Cen b) := le_sup_right
  have hb2sq : b₂ ^ (2 : ℤ) = b₂⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [show b₂ ^ (2 : ℤ) * b₂ = b₂ ^ (3 : ℤ) by group]
    simpa using hb2_3
  have hb2inv2 : (b₂⁻¹) ^ (2 : ℤ) = b₂ := by
    rw [inv_zpow, hb2sq, inv_inv]
  have hcomm1inv : Commute b₁ b₂⁻¹ := hcomm12.inv_right
  obtain ⟨i, j, hij⟩ := exists_zpow_mul_of_mem_sup hcomm12 ha
  have hform : ∃ r s : ℤ, 0 ≤ r ∧ r < 3 ∧ 0 ≤ s ∧ s < 3 ∧ a = b₁ ^ r * b₂ ^ s :=
    ⟨i % 3, j % 3, Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num),
      Int.emod_nonneg _ (by norm_num), Int.emod_lt_of_pos _ (by norm_num), by
        rw [hij, zpow_mod3 hb1_3 hb1ne i, zpow_mod3 hb2_3 hb2ne j]⟩
  obtain ⟨r, s, hr0, hr1, hs0, hs1, hae⟩ := hform
  rw [hae] at ha1 hxa
  interval_cases r <;> interval_cases s
  · exact (ha1 (by simp)).elim
  · exact R2 ⟨hxU, cen_le_of_mem_zpowers
      (mem_zpowers_of_mem_zpowers_ne_one (w := b₂) (by simp) hb2_3 hb2ne ha1) hxa⟩
  · exact R2 ⟨hxU, cen_le_of_mem_zpowers
      (mem_zpowers_of_mem_zpowers_ne_one (w := b₂)
        (by rw [zpow_zero, one_mul]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b₂) 2)
        hb2_3 hb2ne ha1) hxa⟩
  · exact R1 ⟨hxU, cen_le_of_mem_zpowers
      (mem_zpowers_of_mem_zpowers_ne_one (w := b₁) (by simp) hb1_3 hb1ne ha1) hxa⟩
  ·
    have hm : b₁ ^ (1 : ℤ) * b₂ ^ (1 : ℤ) ∈ Subgroup.zpowers (b₁ * b₂) := by
      rw [zpow_one, zpow_one]; exact Subgroup.mem_zpowers _
    have hxw := cen_le_of_mem_zpowers
      (mem_zpowers_of_mem_zpowers_ne_one hm hc3 hcne ha1) hxa
    exact R3 ⟨hxU, cen_b_of_nor hs hU2 hBU hxU (hL2 (nor_zpowers_of_cen hxw))⟩
  ·
    have hm : b₁ ^ (1 : ℤ) * b₂ ^ (2 : ℤ) ∈ Subgroup.zpowers (b₁ * b₂⁻¹) := by
      rw [zpow_one, hb2sq]; exact Subgroup.mem_zpowers _
    have hxw := cen_le_of_mem_zpowers
      (mem_zpowers_of_mem_zpowers_ne_one hm hd3 hdne ha1) hxa
    exact R3 ⟨hxU, cen_b_of_nor hs hU2 hBU hxU (nor_zpowers_mul_inv_le hs hL2 (nor_zpowers_of_cen hxw))⟩
  · exact R1 ⟨hxU, cen_le_of_mem_zpowers
      (mem_zpowers_of_mem_zpowers_ne_one (w := b₁) (by simp) hb1_3 hb1ne ha1) hxa⟩
  ·
    have e : (b₁ * b₂⁻¹) ^ (2 : ℤ) = b₁ ^ (2 : ℤ) * b₂ := by
      rw [hcomm1inv.mul_zpow, hb2inv2]
    have hm : b₁ ^ (2 : ℤ) * b₂ ^ (1 : ℤ) ∈ Subgroup.zpowers (b₁ * b₂⁻¹) := by
      rw [zpow_one, ← e]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) 2
    have hxw := cen_le_of_mem_zpowers
      (mem_zpowers_of_mem_zpowers_ne_one hm hd3 hdne ha1) hxa
    exact R3 ⟨hxU, cen_b_of_nor hs hU2 hBU hxU (nor_zpowers_mul_inv_le hs hL2 (nor_zpowers_of_cen hxw))⟩
  ·
    have hm : b₁ ^ (2 : ℤ) * b₂ ^ (2 : ℤ) ∈ Subgroup.zpowers (b₁ * b₂) := by
      rw [← hcomm12.mul_zpow]; exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) 2
    have hxw := cen_le_of_mem_zpowers
      (mem_zpowers_of_mem_zpowers_ne_one hm hc3 hcne ha1) hxa
    exact R3 ⟨hxU, cen_b_of_nor hs hU2 hBU hxU (hL2 (nor_zpowers_of_cen hxw))⟩

theorem gen_nor (hs : FF84Sec3 b L B b₁ b₂)
    (hL2 : Nor (Subgroup.zpowers (b₁ * b₂)) ≤ Nor (Subgroup.zpowers b))
    {U : Subgroup G} (hU2 : IsPGroup 2 U) (hBU : B ≤ Nor U) :
    (U ⊓ Cen b₁) ⊔ (U ⊓ Cen b₂) ⊔ (U ⊓ Cen b) = U := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := elemAb_sup hs
  have hAB : Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂ ≤ B :=
    sup_le (Subgroup.zpowers_le.2 (mem_B_b₁ hs)) (Subgroup.zpowers_le.2 (mem_B_b₂ hs))
  have hAU : Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂ ≤ Nor U := hAB.trans hBU
  have hUcard : ¬ 3 ∣ Nat.card U := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hU2
    rw [hn]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    norm_num at this
  have h9 : 3 ^ 2 ≤ Nat.card ↥(Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂ : Subgroup G) := by
    norm_num; exact nine_le_card_sup hs
  have hgen := CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.le_iSup_centralizer_of_coprime
    (p := 3) (A := Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂) (U := U) h9 hUcard hAU
  apply le_antisymm
  · exact sup_le (sup_le inf_le_left inf_le_left) inf_le_left
  · refine hgen.trans (iSup_le fun a => iSup_le fun ha => iSup_le fun hne => ?_)
    rintro x ⟨hxU, hxa⟩
    exact key_cen hs hL2 hU2 hBU ha hne hxU hxa

theorem ff84_3_3_of (h32 : FF84_3_2) : FF84_3_3 := by
  intro G _ _ b L B b₁ b₂ hs
  obtain ⟨h2, -, hSb, hfac⟩ := h32 G b L B b₁ b₂ hs
  have hS := opp_three_eq_bot hs h2 hSb
  have hL2 := nor_zpowers_le_nor_b hs hS hfac
  exact ⟨hS, hL2, fun U hU2 hBU => gen_nor hs hL2 hU2 hBU⟩

end CFSG.RankThree.PartTwo.Sec21.FF84
