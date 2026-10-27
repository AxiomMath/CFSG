module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenGlue3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThirteenA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s15_Eleven_wClos_le (V : Subgroup G) (i : ℕ) (X : Subgroup G) : E3.wClos V i X ≤ X :=
  iSup₂_le fun _ hA => hA.1

theorem s15_Eleven_v1_eq_bot (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) {i : ℕ}
    (hC : ¬ centralizer (E3.cClos V i D.T : Set G) ≤ D.M) : v1Sub D.M V₀ V hV L = ⊥ := by
  by_contra hne
  have hP := D.sylowM.isPGroup
  have hTM := D.sylowM.le
  have hW : E3.wClos V i D.T ≤ D.T := s15_Eleven_wClos_le V i D.T
  have hV1V : v1Sub D.M V₀ V hV L ≤ V := s15_Infra_v1Sub_le h.hyp151.hyp125 hV
  have hVT : V ≤ D.T := s15_13A_le_T h.hyp151.hyp125
  have hV12 : IsPGroup 2 (v1Sub D.M V₀ V hV L) := hV.isPGroup.to_le hV1V
  obtain ⟨u, hu, hu1, hcomm⟩ := s15_Glue3_exists_fixed (P := E3.wClos V i D.T)
    (U := v1Sub D.M V₀ V hV L) (hP.to_le hW) hV12 hne
    (fun x hx => s15_Infra_le_normalizer_v1Sub h.hyp151.hyp125 hV (hTM (hW hx)))
  apply hC
  have huc : u ∈ E3.cClos V i D.T := ⟨hVT (hV1V hu), mem_centralizer_iff.2 hcomm⟩
  refine le_trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 huc)) ?_
  have hgood : UniqueMax D.M (D.M ⊓ centralizer ({u} : Set G)) := by
    refine s15_Tools_good_of_mem_conj D h hV (m := 1) D.M.one_mem ?_ hu1
    rw [conjSubgroup_one]
    exact (le_sup_right : v1Sub D.M V₀ V hV L ≤ wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) hu
  exact (centralizer_le_of_uniqueMax D.maxLocal hu1 ⟨1, by simpa using hV.2 u (hV1V hu)⟩ hgood).1

theorem s15_Eleven_not_le_normalizer (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) (hV1 : v1Sub D.M V₀ V hV L = ⊥) {i : ℕ}
    (hC : ¬ centralizer (E3.cClos V i D.T : Set G) ≤ D.M) {X : Subgroup G}
    (hX : X ∈ wConj D.M V₀ V hV L) : ¬ E3.wClos V i D.T ≤ normalizer (X : Set G) := by
  intro hN
  have hXV : X ≤ V := by
    obtain ⟨m, hm, rfl⟩ := hX
    exact s15_Tools_conj_wSub_le D h.hyp151.hyp125 hV hm
  have hX0 : X ≠ ⊥ := by
    intro hb
    have h1 := s15_Glue3_rk_wConj D h.hyp151 hV hV1 hX
    have h2 := two_le_gamma15 D h.hyp151 hV hL
    rw [hb, rk_bot] at h1
    omega
  have hX2 : IsPGroup 2 X := hV.isPGroup.to_le hXV
  obtain ⟨u, hu, hu1, hcomm⟩ := s15_Glue3_exists_fixed (P := E3.wClos V i D.T) (U := X)
    (D.sylowM.isPGroup.to_le (s15_Eleven_wClos_le V i D.T)) hX2 hX0 hN
  apply hC
  have huc : u ∈ E3.cClos V i D.T :=
    ⟨s15_13A_le_T h.hyp151.hyp125 (hXV hu), mem_centralizer_iff.2 hcomm⟩
  refine le_trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 huc)) ?_
  have hgood := s15_Glue3_good_of_mem_wConj D h hV hX hu hu1
  exact (centralizer_le_of_uniqueMax D.maxLocal hu1 ⟨1, by simpa using hV.2 u (hXV hu)⟩ hgood).1

theorem s15_Eleven_even (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) (hV1 : v1Sub D.M V₀ V hV L = ⊥) {i : ℕ}
    (hC : ¬ centralizer (E3.cClos V i D.T : Set G) ≤ D.M) : Even (s15 D.M V₀ V hV L) := by
  refine s15_Glue3_even_of_no_fixed D h.hyp151 hV D.sylowM.isPGroup D.sylowM.le ?_
  intro X hX hTN
  exact s15_Eleven_not_le_normalizer D h hV hL hV1 hC hX
    (le_trans (s15_Eleven_wClos_le V i D.T) hTN)

theorem s15_Eleven_pos_s (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) : 0 < s15 D.M V₀ V hV L := by
  rw [← ncard_wConj D h hV]
  exact (Set.ncard_pos (Set.toFinite _)).2
    ⟨wSub V₀ V hV L, 1, D.M.one_mem, by simp [conjSubgroup_one]⟩

theorem s15_Eleven_four_le_max {s γ : ℕ} (hs : Even s) (hspos : 0 < s) (hγ : 2 ≤ γ)
    (h2 : ¬ (s = 2 ∧ γ ≤ 3)) : 4 ≤ max γ ((s - 2) * γ) := by
  obtain ⟨k, hk⟩ := hs
  by_cases hs2 : s = 2
  · have h4 : 4 ≤ γ := by
      by_contra hlt
      exact h2 ⟨hs2, by omega⟩
    exact le_trans h4 (le_max_left _ _)
  · have hs4 : 4 ≤ s := by omega
    have h4 : 4 ≤ (s - 2) * γ :=
      calc 4 = 2 * 2 := by norm_num
        _ ≤ (s - 2) * γ := Nat.mul_le_mul (by omega) hγ
    exact le_trans h4 (le_max_right _ _)

theorem s15_Eleven_h4 (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) (hev : Even (s15 D.M V₀ V hV L))
    (hn2 : ¬ (s15 D.M V₀ V hV L = 2 ∧ gamma15 D.M V₀ V hV L ≤ 3)) :
    ∀ U : Subgroup G, U ≤ V → ¬ centralizer (U : Set G) ≤ D.M → 4 ≤ E3.mQuot V U := by
  intro U hUV hU
  have h1 := s15_Tools_le_mQuot D h hV hL hUV hU
  have h2 := s15_Eleven_four_le_max hev (s15_Eleven_pos_s D h.hyp151 hV)
    (two_le_gamma15 D h.hyp151 hV hL) hn2
  exact le_trans h2 (le_trans (Nat.le_add_right _ _) h1)

structure Cfg11 (V M : Subgroup G) (i : ℕ) (g : G) (A B : Subgroup G) (v : G) : Prop where
  A_le : A ≤ conjSubgroup V g
  A_le_M : A ≤ M
  mQuot_A : E3.mQuot (conjSubgroup V g) A = i
  B_le : B ≤ A
  mQuot_B : E3.mQuot A B = 1
  v_mem : v ∈ V
  comm_B : ∀ b ∈ B, b * v * b⁻¹ * v⁻¹ = 1
  comm_A : ∃ a ∈ A, a * v * a⁻¹ * v⁻¹ ≠ 1

theorem s15_Eleven_exists_A (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) (hV1 : v1Sub D.M V₀ V hV L = ⊥) {i : ℕ}
    (hC : ¬ centralizer (E3.cClos V i D.T : Set G) ≤ D.M) :
    ∃ (g : G) (A : Subgroup G), A ≤ conjSubgroup V g ∧ A ≤ D.M ∧
      E3.mQuot (conjSubgroup V g) A = i ∧ ¬ A ≤ normalizer (wSub V₀ V hV L : Set G) := by
  have hW : wSub V₀ V hV L ∈ wConj D.M V₀ V hV L :=
    ⟨1, D.M.one_mem, by simp [conjSubgroup_one]⟩
  have h2 := s15_Eleven_not_le_normalizer D h hV hL hV1 hC hW
  by_contra hcon
  push Not at hcon
  apply h2
  refine iSup₂_le fun A hA => ?_
  obtain ⟨hAT, g, hAg, hmA⟩ := hA
  exact hcon g A hAg (le_trans hAT D.sylowM.le) hmA

theorem s15_Eleven_exists_Bv (D : Data G) {V₀ V L : Subgroup G} (h : Hyp154 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) (hV1 : v1Sub D.M V₀ V hV L = ⊥) {g : G}
    {A : Subgroup G} {i : ℕ} (hAg : A ≤ conjSubgroup V g) (hAM : A ≤ D.M)
    (hmA : E3.mQuot (conjSubgroup V g) A = i)
    (hAN : ¬ A ≤ normalizer (wSub V₀ V hV L : Set G)) :
    ∃ (B : Subgroup G) (v : G), Cfg11 V D.M i g A B v := by
  have hA2 : IsPGroup 2 A := (E3.isElemAbelian_conjSubgroup hV g).isPGroup.to_le hAg
  have hlt : A ⊓ normalizer (wSub V₀ V hV L : Set G) < A :=
    lt_of_le_of_ne inf_le_left fun heq => hAN (inf_eq_left.1 heq)
  obtain ⟨E, hCE, hEA, hmE⟩ := s15_Glue_exists_hyperplane hA2 hlt
  have hne : E ≠ A := by
    intro heq
    rw [heq, E3.mQuot_self] at hmE
    omega
  obtain ⟨v, hv, hcomm, ⟨a, haA, hanot⟩, -⟩ :=
    fifteen_seven_G D h.hyp151 hV hL hAM hA2 hEA hCE hne
  refine ⟨E, v, ⟨hAg, hAM, hmA, hEA, hmE, hv, ?_, ⟨a, haA, ?_⟩⟩⟩
  · intro b hb
    have := hcomm b hb
    rw [hV1] at this
    exact Subgroup.mem_bot.1 this
  · intro h1
    apply hanot
    rw [hV1, h1]
    exact Subgroup.one_mem _

theorem s15_Eleven_not_le_of_wClos (M V : Subgroup G)
    (hW : E3.wClos V 0 M ≤ centralizer (V : Set G))
    {i : ℕ} {g : G} {A B : Subgroup G} {v : G}
    (hcfg : Cfg11 V M i g A B v) :
    ¬ conjSubgroup V g ≤ M ∧ ¬ V ≤ conjSubgroup M g := by
  obtain ⟨a, haA, ha⟩ := hcfg.comm_A
  have hC := hW
  have hav : a * v = v * a → a * v * a⁻¹ * v⁻¹ = 1 := fun hh => by
    rw [hh]
    group
  constructor
  · intro hVgM
    have hmem : conjSubgroup V g ≤ E3.wClos V 0 M :=
      le_iSup₂_of_le (conjSubgroup V g) ⟨hVgM, g, le_rfl, E3.mQuot_self _⟩ le_rfl
    exact ha (hav (Subgroup.mem_centralizer_iff.1 (hC (hmem (hcfg.A_le haA))) v hcfg.v_mem).symm)
  · intro hVM
    have hmem' : conjSubgroup V g⁻¹ ≤ M := by
      have := E3.conjSubgroup_mono_left g⁻¹ hVM
      rwa [E3.conjSubgroup_conj_inv] at this
    have hmem : conjSubgroup V g⁻¹ ≤ E3.wClos V 0 M :=
      le_iSup₂_of_le (conjSubgroup V g⁻¹) ⟨hmem', g⁻¹, le_rfl, E3.mQuot_self _⟩ le_rfl
    have hx : g * v * g⁻¹ ∈ conjSubgroup V g⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have e : g⁻¹ * (g * v * g⁻¹) * g⁻¹⁻¹ = v := by group
      rw [e]
      exact hcfg.v_mem
    have hy : g * a * g⁻¹ ∈ V := mem_conjSubgroup_iff.1 (hcfg.A_le haA)
    have hcomm := Subgroup.mem_centralizer_iff.1 (hC (hmem hx)) _ hy
    apply ha
    apply hav
    have h1 : g * a * g⁻¹ * (g * v * g⁻¹) = g * v * g⁻¹ * (g * a * g⁻¹) := hcomm
    have h2 : g * (a * v) * g⁻¹ = g * (v * a) * g⁻¹ := by
      calc g * (a * v) * g⁻¹ = g * a * g⁻¹ * (g * v * g⁻¹) := by group
        _ = g * v * g⁻¹ * (g * a * g⁻¹) := h1
        _ = g * (v * a) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)

theorem s15_Eleven_not_le (D : Data G) (h159 : R15_9 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {i : ℕ} {g : G}
    {A B : Subgroup G} {v : G} (hcfg : Cfg11 V D.M i g A B v) :
    ¬ conjSubgroup V g ≤ D.M ∧ ¬ V ≤ conjSubgroup D.M g :=
  s15_Eleven_not_le_of_wClos D.M V (h159 V₀ V L h hL) hcfg

theorem s15_Eleven_not_centralizer_le_of_wClos (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hW : E3.wClos V 0 D.M ≤ centralizer (V : Set G))
    {i : ℕ} {g : G} {A B : Subgroup G} {v : G}
    (hcfg : Cfg11 V D.M i g A B v) {a : G} (haA : a ∈ A) :
    ¬ centralizer ({a * v * a⁻¹ * v⁻¹} : Set G) ≤ conjSubgroup D.M g := by
  intro hle
  apply (s15_Eleven_not_le_of_wClos D.M V hW hcfg).2
  have hz : a * v * a⁻¹ * v⁻¹ ∈ V := by
    have h1 : a * v * a⁻¹ ∈ V := by
      have := h.hyp151.hyp125.pairFacts.le_normalizer (hcfg.A_le_M haA)
      exact (Subgroup.mem_normalizer_iff.1 this v).1 hcfg.v_mem
    exact V.mul_mem h1 (V.inv_mem hcfg.v_mem)
  intro y hy
  apply hle
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  rw [hw]
  exact congrArg Subtype.val (hV.1.is_comm.comm ⟨_, hz⟩ ⟨y, hy⟩)

theorem s15_Eleven_not_centralizer_le (D : Data G) (h159 : R15_9 D) {V₀ V L : Subgroup G}
    (h : Hyp154 D V₀ V L) (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥) {i : ℕ} {g : G}
    {A B : Subgroup G} {v : G} (hcfg : Cfg11 V D.M i g A B v) {a : G} (haA : a ∈ A) :
    ¬ centralizer ({a * v * a⁻¹ * v⁻¹} : Set G) ≤ conjSubgroup D.M g :=
  s15_Eleven_not_centralizer_le_of_wClos D h hV (h159 V₀ V L h hL) hcfg haA

theorem s15_Eleven_v_mem_conj (D : Data G) {V : Subgroup G} {i : ℕ} (hi : i ≤ 2) {g : G}
    {A B : Subgroup G} {v : G} (hcfg : Cfg11 V D.M i g A B v)
    (h4 : ∀ U : Subgroup G, U ≤ V → ¬ centralizer (U : Set G) ≤ D.M → 4 ≤ E3.mQuot V U) :
    v ∈ conjSubgroup D.M g := by
  by_contra hv
  have hvB : v ∈ centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have := hcfg.comm_B b hb
    have h2 : b * v = v * b := by
      calc b * v = b * v * b⁻¹ * v⁻¹ * (v * b) := by group
        _ = v * b := by rw [this, one_mul]
    exact h2
  have hcB : ¬ centralizer (B : Set G) ≤ conjSubgroup D.M g := fun hle => hv (hle hvB)
  have hBV : conjSubgroup B g⁻¹ ≤ V := by
    have := E3.conjSubgroup_mono_left g⁻¹ (hcfg.B_le.trans hcfg.A_le)
    rwa [E3.conjSubgroup_conj_inv] at this
  have hcU : ¬ centralizer (conjSubgroup B g⁻¹ : Set G) ≤ D.M := by
    intro hle
    apply hcB
    rw [← E3.conjSubgroup_centralizer] at hle
    have := E3.conjSubgroup_mono_left g hle
    rwa [E3.conjSubgroup_inv_conj] at this
  have h5 := h4 _ hBV hcU
  have h6 : E3.mQuot V (conjSubgroup B g⁻¹) = E3.mQuot (conjSubgroup V g) B := by
    rw [← E3.mQuot_conjSubgroup V (conjSubgroup B g⁻¹) g, E3.conjSubgroup_inv_conj]
  have h7 := E3.mQuot_add hcfg.B_le hcfg.A_le
  have h8 := hcfg.mQuot_A
  have h9 := hcfg.mQuot_B
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
