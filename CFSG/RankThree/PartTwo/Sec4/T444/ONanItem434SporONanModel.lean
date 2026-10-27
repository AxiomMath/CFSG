module

public import CFSG.RankThree.Native.ONTripleAut

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporONan9

attribute [local irreducible] dotProduct

open CFSG.RankThree.Native.ONTriple Subgroup

section Extraspecial

variable {G : Type*} [Group G] {x : G} {v : Fin 4 → G} {ω : Fin 4 → Fin 4 → ZMod 3}

theorem index_centralizer_le (h : ThreeQRel x v ω) (g : threeQ x v) :
    (centralizer ({g} : Set (threeQ x v))).index ≤ 3 := by
  have hfin := h.finite
  by_cases hg : (g : G) ∈ zpowers x
  · have hc : centralizer ({g} : Set (threeQ x v)) = ⊤ := by
      rw [Subgroup.centralizer_eq_top_iff_subset]
      rintro _ rfl
      exact h.mem_center_of_val hg
    rw [hc, index_top]
    norm_num
  · have h81 := h.card_centralizer g hg
    have h1 := Subgroup.card_mul_index (centralizer ({g} : Set (threeQ x v)))
    rw [h81, h.card_threeQ_type] at h1
    omega

theorem exists_centralizing (h : ThreeQRel x v ω) {l₁ l₂ : G} (h₁ : l₁ ∈ threeQ x v)
    (h₂ : l₂ ∈ threeQ x v) :
    ∃ Hc : Subgroup G, 27 ≤ Nat.card Hc ∧ (∀ y ∈ Hc, y ^ 3 = 1) ∧
      ∀ y ∈ Hc, y * l₁ = l₁ * y ∧ y * l₂ = l₂ * y := by
  have hfin := h.finite
  set C : Subgroup (threeQ x v) :=
    centralizer ({(⟨l₁, h₁⟩ : threeQ x v)} : Set (threeQ x v)) ⊓
      centralizer ({(⟨l₂, h₂⟩ : threeQ x v)} : Set (threeQ x v)) with hC
  have hidx : C.index ≤ 9 := by
    have e1 := index_centralizer_le h ⟨l₁, h₁⟩
    have e2 := index_centralizer_le h ⟨l₂, h₂⟩
    calc C.index ≤ _ * _ := Subgroup.index_inf_le
      _ ≤ 3 * 3 := Nat.mul_le_mul e1 e2
  have hcard : 27 ≤ Nat.card C := by
    have h1 := Subgroup.card_mul_index C
    rw [h.card_threeQ_type] at h1
    by_contra hlt
    have : Nat.card C * C.index ≤ 26 * 9 := Nat.mul_le_mul (by omega) hidx
    omega
  refine ⟨C.map (threeQ x v).subtype, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (threeQ x v).subtype_injective]
    exact hcard
  · rintro _ ⟨y, -, rfl⟩
    exact h.pow_three_of_mem y.2
  · rintro _ ⟨y, ⟨hy1, hy2⟩, rfl⟩
    exact ⟨congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy1),
      congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy2)⟩

end Extraspecial

theorem exists_cent_cube
    {l₁ l₂ : GM} (hT : IsPGroup 3 (Subgroup.closure {l₁, l₂})) :
    ∃ Hc : Subgroup GM, 27 ≤ Nat.card Hc ∧ (∀ y ∈ Hc, y ^ 3 = 1) ∧
      ∀ y ∈ Hc, y * l₁ = l₁ * y ∧ y * l₂ = l₂ * y := by
  obtain ⟨P, hP⟩ := hT.exists_le_sylow
  obtain ⟨g, hg⟩ := sylow_eq_threeQ P
  have hr := relG_conj g
  have h1 : l₁ ∈ threeQ (MulAut.conj g zG) (fun i => MulAut.conj g (xG i)) := by
    rw [← hg]
    exact hP (subset_closure (by simp))
  have h2 : l₂ ∈ threeQ (MulAut.conj g zG) (fun i => MulAut.conj g (xG i)) := by
    rw [← hg]
    exact hP (subset_closure (by simp))
  exact exists_centralizing hr h1 h2

theorem mem_P0_of_muN_eq_one
    (n : NP0) (hn : muN n = 1) : (n : GM) ∈ P0G := by
  set ψ : GM ≃* GM := MulAut.conj (n : GM)⁻¹ with hψ
  have hψ_apply : ∀ g, ψ g = (n : GM)⁻¹ * g * n := fun g => by
    rw [hψ, MulAut.conj_apply, inv_inv]
  have hz : ψ zG = zG := by
    rw [hψ_apply, mul_assoc, zG_central, ← mul_assoc, inv_mul_cancel, one_mul]
  have hP : ∀ g ∈ P0G, ψ g ∈ P0G := fun g hg => by
    rw [hψ_apply]
    exact conj_mem_P0_of n.2 hg
  have hc : ∀ g ∈ P0G, coordG (ψ g) = coordG g := by
    intro g hg
    have h1 := coord_conjN n ⟨g, hg⟩
    rw [hn, Matrix.vecMul_one] at h1
    have e : (conjN n ⟨g, hg⟩ : P0G) = ⟨ψ g, hP g hg⟩ := Subtype.ext (hψ_apply g).symm
    rw [e] at h1
    rw [coordG_of (hP g hg), coordG_of hg]
    exact h1
  obtain ⟨p, hp, hpf⟩ := exists_P0_fix ψ hz hP hc
  have hcent : ∀ g ∈ P0G, ((n : GM) * p⁻¹) * g = g * ((n : GM) * p⁻¹) := by
    intro g hg
    have e := hpf g hg
    rw [hψ_apply] at e
    calc (n : GM) * p⁻¹ * g = (n : GM) * p⁻¹ * (p * ((n : GM)⁻¹ * g * n) * p⁻¹) := by rw [e]
      _ = g * ((n : GM) * p⁻¹) := by
        have e2 := hpf g hg
        rw [hψ_apply] at e2
        group
  have hz' := mem_zpowers_of_centralizes_P0 hcent
  have hzP : ((n : GM) * p⁻¹) ∈ P0G := by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hz'
    rw [← hk]
    exact zpow_mem ThreeQRel.x_mem k
  have := mul_mem hzP hp
  rwa [inv_mul_cancel_right] at this

@[expose] def mat16 (l : List ℕ) : M4 :=
  Matrix.of fun i j => ((l.getD (4 * i.val + j.val) 0 : ℕ) : ZMod 3)

@[expose] def wMat (w : List ℕ) : M4 := (w.map fun k => matNM k).prod

@[expose] def winvData : List (List (List ℕ)) :=
  [[[0, 2, 0, 0, 2, 0, 0, 0, 2, 0, 2, 1, 2, 2, 0, 1],
      [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
      [2, 2, 0, 0, 2, 1, 0, 0, 0, 1, 0, 2, 2, 1, 1, 0],
      [2, 2, 0, 0, 1, 2, 0, 0, 0, 2, 0, 1, 2, 2, 1, 2]],
    [[0, 1, 1, 0, 1, 0, 2, 1, 0, 0, 1, 2, 0, 0, 0, 2],
      [1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1],
      [2, 2, 2, 0, 2, 1, 1, 1, 0, 0, 0, 2, 0, 0, 1, 0],
      [1, 2, 2, 0, 2, 2, 0, 1, 0, 0, 2, 2, 0, 0, 2, 1]]]

@[expose] def wInv (j l : ℕ) : M4 := mat16 ((winvData.getD j []).getD l [])

@[expose] def T4 : M4 := wMat [0, 1, 1] ^ 3

@[expose] def yMat (j l : ℕ) : M4 := wInv j l * T4 * wMat (lw j l)

@[expose] def genWord (j k : ℕ) : List ℕ :=
  ([[[0, 0, 1], [1, 2, 0]], [[0, 0, 1], [0, 2, 1, 2, 0]]].getD j []).getD k []

theorem winv_check : ∀ j < 2, ∀ l < 4,
    wMat (lw j l) * wInv j l = 1 ∧ wInv j l * wMat (lw j l) = 1 := by
  decide +kernel

theorem gen_matrix : ∀ j < 2, ∀ k < 2, matNM k = ((genWord j k).map (yMat j)).prod := by
  decide +kernel

theorem genWord_lt : ∀ j < 2, ∀ k < 2, ∀ l ∈ genWord j k, l < 4 := by
  decide

theorem uL_ne_zero : ∀ j < 2, ∀ l < 4, uL j l ≠ 0 := by
  decide +kernel

@[expose] noncomputable def tL (j l : ℕ) : GM :=
  (nL j l)⁻¹ * t4G * nL j l

theorem nL_mem_NP0
    {j : ℕ} (hj : j < 2) {l : ℕ} (hl : l < 4) : nL j l ∈ NP0 :=
  wordN_mem_NP0 _ (lw_lt hj hl)

theorem tL_mem_NP0
    {j : ℕ} (hj : j < 2) {l : ℕ} (hl : l < 4) : tL j l ∈ NP0 :=
  mul_mem (mul_mem (inv_mem (nL_mem_NP0 hj hl)) t4G_mem_NP0) (nL_mem_NP0 hj hl)

theorem muN_t4G :
    muN ⟨t4G, t4G_mem_NP0⟩ = T4 := by
  have h := muN_wordN [0, 1, 1] (by decide)
  have e : (⟨t4G, t4G_mem_NP0⟩ : NP0) =
      (⟨wordN [0, 1, 1], wordN_mem_NP0 _ (by decide)⟩ : NP0) ^ 3 :=
    Subtype.ext (by rw [Subgroup.coe_pow]; rfl)
  rw [e]
  show muHom _ = _
  rw [map_pow]
  show (muN _) ^ 3 = _
  rw [h]
  rfl

theorem muN_tL
    {j : ℕ} (hj : j < 2) {l : ℕ} (hl : l < 4) :
    muN ⟨tL j l, tL_mem_NP0 hj hl⟩ = yMat j l := by
  set n : NP0 := ⟨nL j l, nL_mem_NP0 hj hl⟩ with hn
  have e : (⟨tL j l, tL_mem_NP0 hj hl⟩ : NP0) = n⁻¹ * ⟨t4G, t4G_mem_NP0⟩ * n :=
    Subtype.ext rfl
  have hW : muN n = wMat (lw j l) := muN_wordN _ (lw_lt hj hl)
  have h1 : muN n⁻¹ * muN n = 1 := by rw [← muN_mul, inv_mul_cancel, muN_one]
  have hinv : muN n⁻¹ = wInv j l := by
    have hc := winv_check j hj l hl
    calc muN n⁻¹ = muN n⁻¹ * (wMat (lw j l) * wInv j l) := by rw [hc.1, mul_one]
      _ = (muN n⁻¹ * muN n) * wInv j l := by rw [hW, mul_assoc]
      _ = wInv j l := by rw [h1, one_mul]
  rw [e, muN_mul, muN_mul, muN_t4G, hW, hinv, yMat]

theorem tL_mem_centralizer
    (j l : ℕ) :
    tL j l ∈ centralizer ({mL j l} : Set GM) := by
  rw [mem_centralizer_singleton_iff]
  have h := t4_facts.1
  unfold tL mL
  calc (nL j l)⁻¹ * t4G * nL j l * ((nL j l)⁻¹ * xG 0 * nL j l)
      = (nL j l)⁻¹ * (t4G * xG 0) * nL j l := by group
    _ = (nL j l)⁻¹ * (xG 0 * t4G) * nL j l := by rw [h]
    _ = (nL j l)⁻¹ * xG 0 * nL j l * ((nL j l)⁻¹ * t4G * nL j l) := by group

theorem mL_not_mem_zpowers
    {j : ℕ} (hj : j < 2) {l : ℕ} (hl : l < 4) :
    mL j l ∉ zpowers zG := by
  intro hmem
  have h0 : relG.coord ⟨mL j l, mL_mem_P0 hj hl⟩ = 0 := (relG.coord_eq_zero_iff _).2 hmem
  rw [coord_mL hj hl] at h0
  exact uL_ne_zero j hj l hl h0

theorem exists_word_y
    {j : ℕ} (hj : j < 2) {H : Subgroup GM}
    (hH : ∀ l < 4, tL j l ∈ H) :
    ∀ u : List ℕ, (∀ l ∈ u, l < 4) →
      ∃ y : NP0, (y : GM) ∈ H ∧ muN y = (u.map (yMat j)).prod := by
  intro u
  induction u with
  | nil => exact fun _ => ⟨1, one_mem H, by rw [muN_one]; rfl⟩
  | cons l u ih =>
    intro hu
    obtain ⟨y, hyH, hy⟩ := ih fun k hk => hu k (List.mem_cons_of_mem _ hk)
    have hl : l < 4 := hu l List.mem_cons_self
    refine ⟨⟨tL j l, tL_mem_NP0 hj hl⟩ * y, mul_mem (hH l hl) hyH, ?_⟩
    rw [muN_mul, muN_tL hj hl, hy, List.map_cons, List.prod_cons]

theorem nG_mem
    {j : ℕ} (hj : j < 2) {H : Subgroup GM} (hP0 : P0G ≤ H)
    (hH : ∀ l < 4, tL j l ∈ H) {k : ℕ} (hk : k < 2) : nG k ∈ H := by
  obtain ⟨y, hyH, hy⟩ := exists_word_y hj hH (genWord j k) (genWord_lt j hj k hk)
  set n : NP0 := ⟨nG k, nG_mem_NP0 hk⟩ with hn
  have hmu : muN y = muN n := by
    rw [hy, hn, muN_nG hk]
    exact (gen_matrix j hj k hk).symm
  have hu : muN (y⁻¹ * n) = 1 := by
    rw [muN_mul, ← hmu, ← muN_mul, inv_mul_cancel, muN_one]
  have hP : ((y⁻¹ * n : NP0) : GM) ∈ P0G := mem_P0_of_muN_eq_one _ hu
  have e : nG k = (y : GM) * ((y⁻¹ * n : NP0) : GM) := by
    simp [hn]
  rw [e]
  exact mul_mem hyH (hP0 hP)

theorem xG_comm_zero
    {i : Fin 4} (hω : (omegaZ 0 i).val = 0) :
    xG 0 * xG i = xG i * xG 0 := by
  have hc := relG.comm 0 i
  rw [hω, pow_zero, commutatorElement_eq_one_iff_mul_comm] at hc
  exact hc

theorem threePair_x3 : ∀ j < 2,
    ThreeQRel.threePair omegaZ (Pi.single 3 1) (Pi.single 0 1 + yv j) = 0 := by
  decide +kernel

theorem e0_add_yv_ne : ∀ j < 2, (Pi.single 0 1 + yv j : Fin 4 → ZMod 3) ≠ 0 := by
  decide +kernel

theorem xG3_comm_m
    {j : ℕ} (hj : j < 2) :
    xG 3 * (xG 0 * yG j) = (xG 0 * yG j) * xG 3 := by
  have hm : xG 0 * yG j ∈ P0G := mul_mem (ThreeQRel.v_mem 0) (yG_mem_P0 hj)
  have hc := (relG.commute_iff ⟨xG 3, ThreeQRel.v_mem 3⟩ ⟨xG 0 * yG j, hm⟩).2 (by
    rw [coord_xG, coord_mul' (ThreeQRel.v_mem 0) (yG_mem_P0 hj), coord_xG0, coord_yG hj]
    exact threePair_x3 j hj)
  exact congrArg Subtype.val hc

theorem x0y_not_mem
    {j : ℕ} (hj : j < 2) :
    xG 0 * yG j ∉ zpowers zG := by
  intro hmem
  have hm : xG 0 * yG j ∈ P0G := mul_mem (ThreeQRel.v_mem 0) (yG_mem_P0 hj)
  have h0 := (relG.coord_eq_zero_iff ⟨_, hm⟩).2 hmem
  rw [coord_mul' (ThreeQRel.v_mem 0) (yG_mem_P0 hj), coord_xG0, coord_yG hj] at h0
  exact e0_add_yv_ne j hj h0

theorem xG0_not_mem :
    xG 0 ∉ zpowers zG := by
  intro hmem
  have h0 := (relG.coord_eq_zero_iff ⟨xG 0, ThreeQRel.v_mem 0⟩).2 hmem
  rw [coord_xG0] at h0
  have := congrFun h0 0
  simp at this

theorem eq_top_of_cent_AG
    {j : ℕ} (hj : j < 2)
    (H : Subgroup GM)
    (hH : ∀ a ∈ AG j, a ∉ zpowers zG → centralizer ({a} : Set GM) ≤ H) : H = ⊤ := by
  have hx0 : centralizer ({xG 0} : Set GM) ≤ H := hH _ (xG0_mem_AG j) xG0_not_mem
  have hxc : ∀ y, y * xG 0 = xG 0 * y → y ∈ H := fun y hy =>
    hx0 (mem_centralizer_singleton_iff.2 hy)
  have hz : zG ∈ H := hxc _ (zG_central _)
  have hx0H : xG 0 ∈ H := hxc _ rfl
  have hx1 : xG 1 ∈ H := hxc _ (xG_comm_zero (by decide)).symm
  have hx2 : xG 2 ∈ H := hxc _ (xG_comm_zero (by decide)).symm
  have hm : xG 0 * yG j ∈ AG j := mul_mem (xG0_mem_AG j) (yG_mem_AG hj)
  have hx3 : xG 3 ∈ H :=
    hH _ hm (x0y_not_mem hj) (mem_centralizer_singleton_iff.2 (xG3_comm_m hj))
  have hP0 : P0G ≤ H := by
    show Subgroup.closure (insert zG (Set.range xG)) ≤ H
    rw [closure_le]
    rintro _ (rfl | ⟨i, rfl⟩)
    · exact hz
    · fin_cases i
      exacts [hx0H, hx1, hx2, hx3]
  have hK0 : K0G ≤ H := K0G_le_centralizer.trans hx0
  have hk1 : k1G ∈ H := hK0 (subset_closure (by simp))
  have hk2 : k2G ∈ H := hK0 (subset_closure (by simp))
  have htL : ∀ l < 4, tL j l ∈ H := fun l hl =>
    hH _ (mL_mem_AG hj hl) (mL_not_mem_zpowers hj hl) (tL_mem_centralizer j l)
  have hn0 : nG 0 ∈ H := nG_mem hj hP0 htL (by norm_num)
  have hn1 : nG 1 ∈ H := nG_mem hj hP0 htL (by norm_num)
  rw [eq_top_iff, ← closure_Y, closure_le]
  rintro _ ⟨i, rfl⟩
  fin_cases i
  · exact hx0H
  · exact hx1
  · exact hx2
  · exact hx3
  · have e : (⟨eM 7, eM_mem 7⟩ : GM) = zG := Subtype.ext zM_eq
    show (⟨eM 7, eM_mem 7⟩ : GM) ∈ H
    rw [e]
    exact hz
  · exact hn0
  · exact hn1
  · exact hk1
  · exact hk2

theorem eq_top_of_cent_E27
    {A : Subgroup GM}
    (hA : CFSG.RankThree.PartTwo.Late.IsE27 A) (H : Subgroup GM)
    (hH : ∀ a ∈ A, a ∉ zpowers zG → centralizer ({a} : Set GM) ≤ H) : H = ⊤ := by
  obtain ⟨g, j, hj, hAg⟩ := exists_conj_AG hA
  set φ : GM →* GM := (MulAut.conj g).toMonoidHom with hφ
  have hφa : ∀ a, φ a = g * a * g⁻¹ := fun a => rfl
  have hzg : φ zG = zG := by
    rw [hφa, ← zG_central, mul_assoc, mul_inv_cancel, mul_one]
  have key := eq_top_of_cent_AG hj (H.map φ) (by
    intro a' ha' hna'
    rw [← hAg] at ha'
    obtain ⟨a, haA, rfl⟩ := ha'
    have hna : a ∉ zpowers zG := by
      intro hmem
      apply hna'
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hmem
      exact ⟨k, by rw [← hk, map_zpow, hzg]⟩
    intro y hy
    rw [mem_centralizer_singleton_iff, hφa] at hy
    have hy' : g⁻¹ * y * g ∈ centralizer ({a} : Set GM) := by
      rw [mem_centralizer_singleton_iff]
      calc g⁻¹ * y * g * a = g⁻¹ * (y * (g * a * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * a * g⁻¹) * y) * g := by rw [hy]
        _ = a * (g⁻¹ * y * g) := by group
    exact ⟨g⁻¹ * y * g, hH a haA hna hy', by rw [hφa]; group⟩)
  rw [eq_top_iff]
  intro x _
  have hx : φ x ∈ H.map φ := by rw [key]; trivial
  obtain ⟨y, hyH, hy⟩ := hx
  have : y = x := (MulAut.conj g).injective hy
  rw [← this]
  exact hyH

end CFSG.RankThree.PartTwo.Sec4.Item434SporONan9
