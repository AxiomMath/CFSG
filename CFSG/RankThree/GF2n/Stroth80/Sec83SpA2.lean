module

public import CFSG.ClassicalGroups.Symplectic.StatedSpTransport

public section

namespace CFSG.ClassicalGroups.Symplectic

open CFSG.ClassicalGroups.F2Fixed CFSG.ClassicalGroups.Alternating CFSG.Open
open Matrix

@[expose] def FixedNonA2Fact : Prop :=
  ∀ {m : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    {X : Type} [Group X] {M : Type} [AddCommGroup M] [Finite M]
    (φ : X →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K) (hm : 1 ≤ m)
    (h2 : ∀ a : M, a + a = 0) [DistribMulAction X M]
    (hker : ∀ x ∈ φ.ker, ∀ a : M, x • a = a) {u u' : Fin m ⊕ Fin m → K}
    (huu' : spForm m K u u' ≠ 0) {L₁ L₂ : Subgroup X}
    (hL₁ : L₁.map φ = LspGL m K u) (hL₂ : L₂.map φ = LspGL m K u')
    (hdec : IsCompl (fixedSub M (L₁ : Set X)) (fixedSub M (L₂ : Set X)))
    {x : X} (hx : φ x ∈ LspGL m K u)
    (hn : ∃ y : Fin m ⊕ Fin m → K,
      spForm m K y ((φ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) ≠ 0),
    (comm M x).range = fixedSub M (L₁ : Set X) ∧
      Nat.card M = Nat.card (fixedSub M (L₁ : Set X)) ^ 2

section Lemmas

theorem a2_Ssp_mul {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {B : LinearMap.BilinForm K V} (hB : B.IsAlt) {v w w' : V} (hw : B v w = 0)
    (hw' : B v w' = 0) (c c' : K) :
    Ssp hB v w c * Ssp hB v w' c' = Ssp hB v (w + w') (c + c' + B w' w) :=
  Subtype.ext (siegel_mul hB hw hw' c c')

theorem a2_Ssp_conj {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {B : LinearMap.BilinForm K V} (hB : B.IsAlt) (T : Gsp B) (v w : V) (c : K) :
    T * Ssp hB v w c * T⁻¹ = Ssp hB (T.app v) (T.app w) c :=
  Subtype.ext (siegel_conj hB T.2 v w c)

theorem a2_Tsp_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {B : LinearMap.BilinForm K V} (hB : B.IsAlt) (v : V) : Tsp hB v 0 = 1 :=
  Subtype.ext (symplecticTransvection_zero hB v)

theorem a2_form_Ssp_app {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {B : LinearMap.BilinForm K V} (h2 : (2 : K) = 0) (hB : B.IsAlt) {u w : V}
    (huw : B u w = 0) (c : K) (y : V) :
    B y ((Ssp hB u w c).app y) = c * B y u ^ 2 :=
  siegel_form_apply_self h2 hB huw c y

theorem a2_exists_form_ne_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {B : LinearMap.BilinForm K V} (hB : B.IsAlt) (hBn : B.Nondegenerate) {u : V}
    (hu : u ≠ 0) : ∃ y : V, B y u ≠ 0 := by
  obtain ⟨n, hn⟩ : ∃ n : V, B u n ≠ 0 := by
    by_contra h
    push Not at h
    exact hu (hBn.1 u h)
  exact ⟨n, by rw [← hB.neg_eq u n]; exact neg_ne_zero.mpr hn⟩

theorem a2_exists_form_apply_ne_zero {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {B : LinearMap.BilinForm K V} (hB : B.IsAlt) (hBn : B.Nondegenerate) {u w : V}
    (hu : u ≠ 0) (hw : ∀ s : K, w ≠ s • u) : ∃ v : V, B u v = 0 ∧ B w v ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨n₀, hn₀⟩ : ∃ n : V, B u n ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hu (hBn.1 u h')
  obtain ⟨e, he⟩ : ∃ e : V, B u e = 1 :=
    ⟨(B u n₀)⁻¹ • n₀, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hn₀]⟩
  have key : ∀ n : V, B w n = B u n * B w e := by
    intro n
    have h1 : B u (n + B n u • e) = 0 := by
      rw [map_add, map_smul, he, smul_eq_mul, mul_one, ← hB.neg_eq u n, add_neg_cancel]
    have h2 := h _ h1
    rw [map_add, map_smul, smul_eq_mul, ← hB.neg_eq u n] at h2
    linear_combination h2
  have hzero : w - B w e • u = 0 := by
    refine hBn.1 _ fun n => ?_
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
      key n]
    ring
  exact hw (B w e) (sub_eq_zero.mp hzero)

theorem a2_comm_mul_apply {X M : Type*} [Group X] [AddCommGroup M] [DistribMulAction X M]
    (x y : X) (m : M) : comm M (x * y) m = comm M x (y • m) + comm M y m := by
  simp only [comm_apply, mul_smul]
  abel

theorem a2_card_sup_le {M : Type*} [AddCommGroup M] [Finite M] (A B : AddSubgroup M) :
    Nat.card (A ⊔ B : AddSubgroup M) ≤ Nat.card A * Nat.card B := by
  rw [← Nat.card_prod]
  refine Nat.card_le_card_of_surjective
    (fun p : A × B => (⟨p.1.1 + p.2.1, AddSubgroup.add_mem_sup p.1.2 p.2.2⟩ :
      (A ⊔ B : AddSubgroup M))) ?_
  rintro ⟨z, hz⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.mp hz
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

theorem a2_card_range_comm_mul_le {X M : Type*} [Group X] [AddCommGroup M] [Finite M]
    [DistribMulAction X M] (x y : X) :
    Nat.card (comm M (x * y)).range ≤ Nat.card (comm M x).range * Nat.card (comm M y).range := by
  have hle : (comm M (x * y)).range ≤ (comm M x).range ⊔ (comm M y).range := by
    rintro _ ⟨m, rfl⟩
    rw [a2_comm_mul_apply]
    exact AddSubgroup.add_mem_sup (AddMonoidHom.mem_range.mpr ⟨y • m, rfl⟩)
      (AddMonoidHom.mem_range.mpr ⟨m, rfl⟩)
  exact (AddSubgroup.card_le_of_le hle).trans (a2_card_sup_le _ _)

theorem a2_card_range_comm_conj {X M : Type*} [Group X] [AddCommGroup M] [Finite M]
    [DistribMulAction X M] (t x : X) :
    Nat.card (comm M (t * x * t⁻¹)).range = Nat.card (comm M x).range := by
  have h1 := card_eq_card_fixedSub_mul_card_range (M := M) x
  have h2 := card_eq_card_fixedSub_mul_card_range (M := M) (t * x * t⁻¹)
  have h3 : Nat.card (fixedSub M ({t * x * t⁻¹} : Set X)) =
      Nat.card (fixedSub M ({x} : Set X)) := by
    have := card_fixedSub_conj (M := M) ({x} : Set X) t
    simpa only [Set.image_singleton] using this
  rw [h3] at h2
  have hpos : 0 < Nat.card (fixedSub M ({x} : Set X)) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_left hpos (h2.symm.trans h1)

theorem a2_spEquiv_mk_eq {m : ℕ} {K : Type} [Field K] {X : Type} [Group X]
    (φ : X →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K) (y : X)
    (hy : φ y ∈ StatedSp m K) :
    spEquiv (m := m) (K := K) ⟨φ y, hy⟩ = toGsp φ hφ y :=
  Gsp.ext' fun v => (spEquiv_app ⟨φ y, hy⟩ v).trans (toGsp_app φ hφ y v).symm

end Lemmas

theorem stroth_2_1_a2_of_fixed (H : FixedNonA2Fact) {m : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {X : Type} [Group X] {M : Type} [AddCommGroup M] [Finite M]
    (φ : X →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K) (hm : 1 ≤ m)
    (h2 : ∀ a : M, a + a = 0) [DistribMulAction X M]
    (hker : ∀ x ∈ φ.ker, ∀ a : M, x • a = a) {u u' : Fin m ⊕ Fin m → K}
    (huu' : spForm m K u u' ≠ 0) {L₁ L₂ : Subgroup X}
    (hL₁ : L₁.map φ = LspGL m K u) (hL₂ : L₂.map φ = LspGL m K u')
    (hdec : IsCompl (fixedSub M (L₁ : Set X)) (fixedSub M (L₂ : Set X)))
    {x : X} (hx : φ x ∈ LspGL m K u) (hx1 : φ x ≠ 1)
    (hn : ¬ ∃ y : Fin m ⊕ Fin m → K,
      spForm m K y ((φ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) ≠ 0) :
    Nat.card M ≤ Nat.card (comm M x).range ^ 4 := by
  have hB : (spForm m K).IsAlt := spForm_isAlt
  have hu : u ≠ 0 := fun h => huu' (by rw [h]; simp)
  obtain ⟨hA, hLA⟩ := mem_LspGL_iff.mp hx
  have hLψ : toGsp φ hφ x ∈ Lsp (spForm m K) hB u := by
    rw [← a2_spEquiv_mk_eq φ hφ x hA]
    exact hLA
  obtain ⟨w, c, hw, hgw⟩ := mem_pointRadical.mp (mem_Lsp.mp hLψ)
  have hgeq : Ssp hB u w c = toGsp φ hφ x := Subtype.ext hgw
  have hform : ∀ y : Fin m ⊕ Fin m → K,
      spForm m K y ((φ x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) =
        c * spForm m K y u ^ 2 := by
    intro y
    rw [← toGsp_app φ hφ x y, ← hgeq]
    exact a2_form_Ssp_app CharTwo.two_eq_zero hB hw c y
  have hc : c = 0 := by
    obtain ⟨y₀, hy₀⟩ := a2_exists_form_ne_zero hB spForm_nondegenerate hu
    by_contra hc
    apply hn
    exact ⟨y₀, by rw [hform y₀]; exact mul_ne_zero hc (pow_ne_zero 2 hy₀)⟩
  subst hc
  have hw_ne : ∀ s : K, w ≠ s • u := by
    intro s hs
    have h1 : toGsp φ hφ x = 1 := by
      rw [← hgeq, hs, Ssp_smul_self, a2_Tsp_zero]
    apply hx1
    have h4 : (⟨φ x, hA⟩ : StatedSp m K) = 1 := by
      apply (spEquiv (m := m) (K := K)).injective
      rw [map_one, a2_spEquiv_mk_eq φ hφ x hA, h1]
    exact congrArg Subtype.val h4
  obtain ⟨v, hBuv, hBwv⟩ := a2_exists_form_apply_ne_zero hB spForm_nondegenerate hu hw_ne
  obtain ⟨T, hT⟩ : ∃ T : Gsp (spForm m K), T = Tsp hB v 1 := ⟨_, rfl⟩
  obtain ⟨t, ht⟩ := toGsp_surjective φ hφ T
  have hTu : T.app u = u := by
    rw [hT, Tsp_app, one_mul, hBuv, zero_smul, add_zero]
  have hBuw' : spForm m K u (T.app w) = 0 := by
    rw [hT, Tsp_app, one_mul]
    simp [hw, hBuv]
  have hBw'w : spForm m K (T.app w) w = -(spForm m K w v * spForm m K w v) := by
    have hvw : spForm m K v w = -spForm m K w v := (hB.neg_eq w v).symm
    rw [hT, Tsp_app, one_mul]
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
      hB.self_eq_zero, hvw]
    ring
  obtain ⟨x', hx'⟩ : ∃ x' : X, x' = x * (t * x * t⁻¹) := ⟨_, rfl⟩
  have hψx' : toGsp φ hφ x' = Ssp hB u (w + T.app w) (spForm m K (T.app w) w) := by
    rw [hx']
    simp only [map_mul, map_inv]
    rw [ht, ← hgeq, a2_Ssp_conj, hTu, a2_Ssp_mul hB hw hBuw' 0 0]
    simp only [zero_add]
  have hwu'' : spForm m K u (w + T.app w) = 0 := by
    rw [map_add, hw, hBuw', add_zero]
  have hcne : spForm m K (T.app w) w ≠ 0 := by
    rw [hBw'w]
    exact neg_ne_zero.mpr (mul_ne_zero hBwv hBwv)
  have hn' : ∃ y : Fin m ⊕ Fin m → K,
      spForm m K y ((φ x' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ y) ≠ 0 := by
    obtain ⟨y₀, hy₀⟩ := a2_exists_form_ne_zero hB spForm_nondegenerate hu
    refine ⟨y₀, ?_⟩
    rw [← toGsp_app φ hφ x' y₀, hψx', a2_form_Ssp_app CharTwo.two_eq_zero hB hwu'' _ y₀]
    exact mul_ne_zero hcne (pow_ne_zero 2 hy₀)
  have hA' : φ x' ∈ StatedSp m K := by
    rw [← hφ]
    exact MonoidHom.mem_range.mpr ⟨x', rfl⟩
  have hx'mem : φ x' ∈ LspGL m K u := by
    refine mem_LspGL_iff.mpr ⟨hA', ?_⟩
    rw [a2_spEquiv_mk_eq φ hφ x' hA', hψx']
    exact Ssp_mem_Lsp hB hwu'' _
  obtain ⟨hcomm, hcardH⟩ := H φ hφ hm h2 hker huu' hL₁ hL₂ hdec hx'mem hn'
  have hcardM : Nat.card M = Nat.card (comm M x').range ^ 2 := by
    rw [hcomm]
    exact hcardH
  have hle : Nat.card (comm M x').range ≤
      Nat.card (comm M x).range * Nat.card (comm M (t * x * t⁻¹)).range := by
    rw [hx']
    exact a2_card_range_comm_mul_le x (t * x * t⁻¹)
  rw [a2_card_range_comm_conj t x] at hle
  rw [hcardM]
  calc Nat.card (comm M x').range ^ 2
      ≤ (Nat.card (comm M x).range * Nat.card (comm M x).range) ^ 2 :=
        Nat.pow_le_pow_left hle 2
    _ = Nat.card (comm M x).range ^ 4 := by ring

end CFSG.ClassicalGroups.Symplectic
