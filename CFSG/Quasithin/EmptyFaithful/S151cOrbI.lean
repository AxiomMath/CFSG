module

public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S151cTwoBl

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

section OrbI151c

variable {V : Type} [CommGroup V] [Finite V] {X Tb Xc : Subgroup (MulAut V)}

open Classical in
private theorem blocks_eq_pair_OrbI151c {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L₁ L₂ : Subgroup (MulAut V)} (h1 : L₁ ∈ I) (h2 : L₂ ∈ I)
    (hJ : Jhat X = L₁ ⊔ L₂) : ∀ L' ∈ I, L' = L₁ ∨ L' = L₂ := by
  intro L' hL'
  by_contra hcon
  push Not at hcon
  obtain ⟨hn1, hn2⟩ := hcon
  have hle : L' ≤ L₁ ⊔ L₂ := hJ ▸ block_le_J hI hL'
  have hsup : L₁ ⊔ L₂ ≤ ⨆ L'' ∈ I.erase L', L'' :=
    sup_le (le_iSup₂ (f := fun L'' (_ : L'' ∈ I.erase L') => L'') L₁
        (Finset.mem_erase.mpr ⟨Ne.symm hn1, h1⟩))
      (le_iSup₂ (f := fun L'' (_ : L'' ∈ I.erase L') => L'') L₂
        (Finset.mem_erase.mpr ⟨Ne.symm hn2, h2⟩))
  have h3 : L' ⊓ ⨆ L'' ∈ I.erase L', L'' = L' := inf_eq_left.mpr (hle.trans hsup)
  rw [hI.indep L' hL'] at h3
  exact hI.ne_bot L' hL' h3.symm

open Classical in
private theorem commV_pair_OrbI151c (h : Setting151c X Tb Xc) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L₁ L₂ : Subgroup (MulAut V)} (h1 : L₁ ∈ I) (h2 : L₂ ∈ I)
    (hne : L₂ ≠ L₁) (hJ : Jhat X = L₁ ⊔ L₂) (hfix : fixV (Jhat X) = ⊥) :
    commV L₁ ⊓ commV L₂ = ⊥ ∧ commV L₁ ⊔ commV L₂ = ⊤ := by
  refine ⟨?_, ?_⟩
  · refine le_bot_iff.mp ?_
    rw [← hI.indepV L₁ h1]
    exact inf_le_inf_left _ (le_iSup₂ (f := fun L' (_ : L' ∈ I.erase L₁) => commV L') L₂
      (Finset.mem_erase.mpr ⟨hne, h2⟩))
  · have hcop := commV_fitting_sup_fixV h.sq h.o2
    have hFJ : fittingOf (Jhat X) ≤ Jhat X := fittingOf_le _
    have hfix_eq : fixV (Jhat X) = fixV (fittingOf (Jhat X)) :=
      le_antisymm (fun c hc f hf => hc f (hFJ hf)) (fun c hc j hj => h.central c hc j hj)
    have hC0 : fixV (fittingOf (Jhat X)) = ⊥ := by rw [← hfix_eq]; exact hfix
    have hcomm : commV (fittingOf (Jhat X)) = ⊤ := by
      have := hcop.1
      rwa [hC0, sup_bot_eq] at this
    have hle : commV (Jhat X) ≤ commV L₁ ⊔ commV L₂ := by
      rw [hJ]
      exact commV_sup_le151c L₁ L₂
    rw [eq_top_iff, ← hcomm]
    exact (commV_mono216 hFJ).trans hle

omit [Finite V] in
private theorem nonempty_equiv_conjBy_OrbI151c {L L' : Subgroup (MulAut V)} {x : MulAut V}
    (e : conjBy x L = L') : Nonempty (↥L ≃* ↥L') := by
  subst e
  exact ⟨Subgroup.equivMapOfInjective L (MulAut.conj x).toMonoidHom (MulAut.conj x).injective⟩


private theorem card_le_three_OrbI151c {G : Type*} [Group G] [Finite G] [IsCyclic G]
    (hexp : ∀ g : G, g ^ 3 = 1) : Nat.card G ≤ 3 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := G)
  have h3 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (hexp g)
  rw [hg] at h3
  exact Nat.le_of_dvd (by norm_num) h3

omit [CommGroup V] [Finite V] in
private theorem not_isCyclic_of_four_cubes_OrbI151c {C : Type*} [Group C] [Finite C] {α β : C}
    (hα : α ^ 3 = 1) (hβ : β ^ 3 = 1) (h1 : α ≠ 1) (h2 : β ≠ 1) (h3 : β ≠ α) (h4 : β ≠ α⁻¹) :
    ¬ IsCyclic C := by
  classical
  intro hcyc
  have : Fintype C := Fintype.ofFinite C
  have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 3) (by norm_num)
  have hα3 : α⁻¹ ^ 3 = 1 := by rw [inv_pow, hα, inv_one]
  have hαinv : α⁻¹ ≠ α := by
    intro h
    apply h1
    have h5 : α * α = 1 := by
      nth_rewrite 1 [← h]
      exact inv_mul_cancel α
    have h6 : α ^ 3 = α := by rw [pow_succ, pow_two, h5, one_mul]
    rw [← h6]
    exact hα
  have e1 : (1 : C) ≠ α := h1.symm
  have e2 : (1 : C) ≠ α⁻¹ := fun h => h1 (inv_eq_one.mp h.symm)
  have e3 : (1 : C) ≠ β := h2.symm
  have e4 : α ≠ α⁻¹ := hαinv.symm
  have e5 : α ≠ β := h3.symm
  have e6 : α⁻¹ ≠ β := h4.symm
  have hsub : ({1, α, α⁻¹, β} : Finset C) ⊆ Finset.univ.filter (fun a : C => a ^ 3 = 1) := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with h | h | h | h <;> rw [h]
    · exact one_pow 3
    · exact hα
    · exact hα3
    · exact hβ
  have hcard : ({1, α, α⁻¹, β} : Finset C).card = 4 := by
    simp [Finset.card_insert_of_notMem, e1, e2, e3, e4, e5, e6]
  have := Finset.card_le_card hsub
  omega

private theorem d3_cube_mul_OrbI151c : ∀ a b : DihedralGroup 3, a * a * a = 1 → b * b * b = 1 →
    (a * b) * (a * b) * (a * b) = 1 := by
  decide

private theorem d33_cube_mul_OrbI151c (a b : DihedralGroup 3 × DihedralGroup 3)
    (ha : a * a * a = 1) (hb : b * b * b = 1) : (a * b) * (a * b) * (a * b) = 1 :=
  Prod.ext (d3_cube_mul_OrbI151c _ _ (congrArg Prod.fst ha) (congrArg Prod.fst hb))
    (d3_cube_mul_OrbI151c _ _ (congrArg Prod.snd ha) (congrArg Prod.snd hb))

private theorem not_isCyclic_fittingOf_D33_OrbI151c {W : Type*} [CommGroup W] [Finite W]
    {Y : Subgroup (MulAut W)} (e : ↥Y ≃* DihedralGroup 3 × DihedralGroup 3) :
    ¬ IsCyclic ↥(fittingOf Y) := by
  have hcube : ∀ y : ↥Y, y ^ 3 = 1 ↔ e y * e y * e y = 1 := by
    intro y
    rw [← pow_three', ← map_pow]
    exact e.map_eq_one_iff.symm
  let N : Subgroup (MulAut W) :=
    { carrier := {y | ∃ hy : y ∈ Y, (⟨y, hy⟩ : ↥Y) ^ 3 = 1}
      one_mem' := ⟨Y.one_mem, one_pow 3⟩
      mul_mem' := by
        rintro a b ⟨ha, ha3⟩ ⟨hb, hb3⟩
        refine ⟨Y.mul_mem ha hb, ?_⟩
        have e1 : (⟨a * b, Y.mul_mem ha hb⟩ : ↥Y) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
        rw [e1, hcube, map_mul]
        exact d33_cube_mul_OrbI151c _ _ ((hcube _).mp ha3) ((hcube _).mp hb3)
      inv_mem' := by
        rintro a ⟨ha, ha3⟩
        refine ⟨Y.inv_mem ha, ?_⟩
        have e1 : (⟨a⁻¹, Y.inv_mem ha⟩ : ↥Y) = (⟨a, ha⟩ : ↥Y)⁻¹ := rfl
        rw [e1, inv_pow, ha3, inv_one] }
  have hmemN : ∀ y : ↥Y, y ^ 3 = 1 → (y : MulAut W) ∈ N := fun y hy => ⟨y.2, hy⟩
  have hNY : N ≤ Y := fun y hy => hy.1
  have hnorm : ∀ x ∈ Y, ∀ n ∈ N, x * n * x⁻¹ ∈ N := by
    rintro x hx n ⟨hn, hn3⟩
    refine ⟨Y.mul_mem (Y.mul_mem hx hn) (Y.inv_mem hx), ?_⟩
    have e1 : (⟨x * n * x⁻¹, Y.mul_mem (Y.mul_mem hx hn) (Y.inv_mem hx)⟩ : ↥Y) =
        ⟨x, hx⟩ * ⟨n, hn⟩ * (⟨x, hx⟩ : ↥Y)⁻¹ := rfl
    rw [e1, conj_pow, hn3, mul_one, mul_inv_cancel]
  have hnil : Group.IsNilpotent ↥N := by
    have : IsPGroup 3 ↥N := fun g => by
      obtain ⟨hg, hg3⟩ := g.2
      refine ⟨1, Subtype.ext ?_⟩
      simpa using congrArg Subtype.val hg3
    exact this.isNilpotent
  have hNF : N ≤ fittingOf Y := le_fittingOf_of_normal_nilpotent hNY hnorm hnil
  intro hcyc
  set α₀ : ↥Y := e.symm (DihedralGroup.r 1, 1) with hα₀
  set β₀ : ↥Y := e.symm (1, DihedralGroup.r 1) with hβ₀
  have hα3 : α₀ ^ 3 = 1 := by
    rw [hcube, hα₀, MulEquiv.apply_symm_apply]
    decide
  have hβ3 : β₀ ^ 3 = 1 := by
    rw [hcube, hβ₀, MulEquiv.apply_symm_apply]
    decide
  have hαF : (α₀ : MulAut W) ∈ fittingOf Y := hNF (hmemN α₀ hα3)
  have hβF : (β₀ : MulAut W) ∈ fittingOf Y := hNF (hmemN β₀ hβ3)
  refine not_isCyclic_of_four_cubes_OrbI151c (C := ↥(fittingOf Y))
    (α := ⟨(α₀ : MulAut W), hαF⟩) (β := ⟨(β₀ : MulAut W), hβF⟩) ?_ ?_ ?_ ?_ ?_ ?_ hcyc
  · exact Subtype.ext (by simpa using congrArg Subtype.val hα3)
  · exact Subtype.ext (by simpa using congrArg Subtype.val hβ3)
  · intro h
    have h1 : α₀ = 1 := Subtype.ext (congrArg (fun z : ↥(fittingOf Y) => (z : MulAut W)) h)
    have h2 := congrArg e h1
    rw [hα₀, MulEquiv.apply_symm_apply, map_one] at h2
    exact absurd h2 (by decide)
  · intro h
    have h1 : β₀ = 1 := Subtype.ext (congrArg (fun z : ↥(fittingOf Y) => (z : MulAut W)) h)
    have h2 := congrArg e h1
    rw [hβ₀, MulEquiv.apply_symm_apply, map_one] at h2
    exact absurd h2 (by decide)
  · intro h
    have h1 : β₀ = α₀ := Subtype.ext (congrArg (fun z : ↥(fittingOf Y) => (z : MulAut W)) h)
    have h2 := congrArg e h1
    rw [hβ₀, hα₀, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h2
    exact absurd h2 (by decide)
  · intro h
    have h1 : β₀ = α₀⁻¹ := Subtype.ext (congrArg (fun z : ↥(fittingOf Y) => (z : MulAut W)) h)
    have h2 := congrArg e h1
    rw [hβ₀, hα₀, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h2
    exact absurd h2 (by decide)

private theorem dihedral_shapes_OrbI151c {W : Type*} [CommGroup W] [Finite W]
    {Y : Subgroup (MulAut W)} {r : ℚ} (hD : D217Concl Y r) (hcyc : IsCyclic ↥(fittingOf Y)) :
    (Nonempty (↥Y ≃* DihedralGroup 3) ∧ (rk W : ℚ) = 2 * r ∧ (r = 1 ∨ r = 2)) ∨
      (Nonempty (↥Y ≃* DihedralGroup 5) ∧ rk W = 4 ∧ r = 2) := by
  have := hcyc
  rcases hD with h1 | h2 | ⟨hE, hF, -⟩ | ⟨hF, hexp, -⟩ | ⟨-, -, ⟨e⟩, -⟩ | ⟨hE, hF, -⟩
  · exact Or.inl h1
  · exact Or.inr h2
  · exfalso
    have := card_le_three_OrbI151c (G := ↥(fittingOf Y))
      (fun g => Subtype.ext (hE.2 (g : MulAut W) g.2))
    omega
  · exfalso
    have := card_le_three_OrbI151c (G := ↥(fittingOf Y))
      (fun g => Subtype.ext (hexp (g : MulAut W) g.2))
    omega
  · exact absurd hcyc (not_isCyclic_fittingOf_D33_OrbI151c e)
  · exfalso
    have := card_le_three_OrbI151c (G := ↥(fittingOf Y))
      (fun g => Subtype.ext (hE.2 (g : MulAut W) g.2))
    omega

private theorem d3_rot_OrbI151c : ∀ w : DihedralGroup 3, w * w * w = 1 →
    ∃ i : ZMod 3, w = DihedralGroup.r i := by
  decide

private theorem d5_rot_OrbI151c : ∀ w : DihedralGroup 5, w * w * w * w * w = 1 →
    ∃ i : ZMod 5, w = DihedralGroup.r i := by
  decide

private theorem exists_pow_of_pow_eq_one_OrbI151c {G : Type*} [Group G] {p : ℕ}
    (hp : p = 3 ∨ p = 5) {L : Subgroup G} (e : ↥L ≃* DihedralGroup p) {y : G} (hyL : y ∈ L)
    (hy : y ^ p = 1) : ∃ m : ℕ, y = ((e.symm (DihedralGroup.r 1) : ↥L) : G) ^ m := by
  have : NeZero p := ⟨by rcases hp with rfl | rfl <;> norm_num⟩
  have hyL' : (⟨y, hyL⟩ : ↥L) ^ p = 1 := Subtype.ext (by simpa using hy)
  have hw : e ⟨y, hyL⟩ ^ p = 1 := by rw [← map_pow, hyL', map_one]
  have hex : ∃ i : ZMod p, e ⟨y, hyL⟩ = DihedralGroup.r i := by
    rcases hp with rfl | rfl
    · exact d3_rot_OrbI151c _ (by rwa [pow_three'] at hw)
    · refine d5_rot_OrbI151c _ ?_
      have e5 : ∀ w : DihedralGroup 5, w ^ 5 = w * w * w * w * w := fun w => by
        simp [pow_succ]
      rwa [e5] at hw
  obtain ⟨i, hi⟩ := hex
  refine ⟨i.val, ?_⟩
  have h1 : (⟨y, hyL⟩ : ↥L) = (e.symm (DihedralGroup.r 1)) ^ i.val := by
    apply e.injective
    rw [map_pow, MulEquiv.apply_symm_apply, DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
    exact hi
  simpa using congrArg Subtype.val h1

private theorem pow_four_comm_OrbI151c {G : Type*} [Group G] {p : ℕ} (hp : p = 3 ∨ p = 5)
    {a x : G} (ha : a ^ p = 1) (ha1 : a ≠ 1) {m : ℕ} (hm : x * a * x⁻¹ = a ^ m) :
    x ^ 4 * a = a * x ^ 4 := by
  have hpow : ∀ j : ℕ, x ^ j * a * (x ^ j)⁻¹ = a ^ (m ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have e1 : x ^ (j + 1) * a * (x ^ (j + 1))⁻¹ = x * (x ^ j * a * (x ^ j)⁻¹) * x⁻¹ := by
        group
      rw [e1, ih, ← conj_pow, hm, ← pow_mul, pow_succ']
  have hmp : m % p ≠ 0 := by
    intro h0
    obtain ⟨k, hk⟩ := Nat.dvd_of_mod_eq_zero h0
    apply ha1
    have h1 : x * a * x⁻¹ = 1 := by rw [hm, hk, pow_mul, ha, one_pow]
    have h2 : x * a = x * 1 := by rw [mul_one]; exact mul_inv_eq_one.mp h1
    exact mul_left_cancel h2
  have hmod : m ^ 4 % p = 1 := by
    rw [Nat.pow_mod]
    have hlt : m % p < p := Nat.mod_lt _ (by rcases hp with rfl | rfl <;> norm_num)
    have key : ∀ k : ℕ, k < p → k ≠ 0 → k ^ 4 % p = 1 := by
      rcases hp with rfl | rfl <;> decide
    exact key _ hlt hmp
  have h4 : x ^ 4 * a * (x ^ 4)⁻¹ = a := by
    rw [hpow 4, pow_eq_pow_mod _ ha, hmod, pow_one]
  calc x ^ 4 * a = (x ^ 4 * a * (x ^ 4)⁻¹) * x ^ 4 := by group
    _ = a * x ^ 4 := by rw [h4]

private theorem rot_gen_props_OrbI151c {G : Type*} [Group G] {p : ℕ} (hp : p = 3 ∨ p = 5)
    {L : Subgroup G} (e : ↥L ≃* DihedralGroup p) :
    ((e.symm (DihedralGroup.r 1) : ↥L) : G) ∈ L ∧
      ((e.symm (DihedralGroup.r 1) : ↥L) : G) ^ p = 1 ∧
      ((e.symm (DihedralGroup.r 1) : ↥L) : G) ≠ 1 := by
  have : NeZero p := ⟨by rcases hp with rfl | rfl <;> norm_num⟩
  refine ⟨(e.symm (DihedralGroup.r 1)).2, ?_, ?_⟩
  · have h1 : (e.symm (DihedralGroup.r 1)) ^ p = 1 := by
      rw [← map_pow, DihedralGroup.r_one_pow, ZMod.natCast_self, ← DihedralGroup.one_def,
        map_one]
    simpa using congrArg Subtype.val h1
  · intro h
    have h1 : e.symm (DihedralGroup.r 1) = 1 := Subtype.ext h
    have h2 := congrArg e h1
    rw [MulEquiv.apply_symm_apply, map_one] at h2
    rcases hp with rfl | rfl <;> exact absurd h2 (by decide)

private theorem pow_four_comm_of_normalizes_OrbI151c {G : Type*} [Group G] {p : ℕ}
    (hp : p = 3 ∨ p = 5) {L : Subgroup G} (e : ↥L ≃* DihedralGroup p) {x : G}
    (hx : ∀ y ∈ L, x * y * x⁻¹ ∈ L) : ∀ y ∈ L, y ^ p = 1 → x ^ 4 * y = y * x ^ 4 := by
  obtain ⟨haL, hap, ha1⟩ := rot_gen_props_OrbI151c hp e
  obtain ⟨m, hm⟩ := exists_pow_of_pow_eq_one_OrbI151c hp e (hx _ haL)
    (by rw [conj_pow, hap, mul_one, mul_inv_cancel])
  have hcomm := pow_four_comm_OrbI151c hp hap ha1 hm
  intro y hy hyp
  obtain ⟨k, rfl⟩ := exists_pow_of_pow_eq_one_OrbI151c hp e hy hyp
  exact (Commute.pow_right (show Commute (x ^ 4) _ from hcomm) k).eq

omit [Finite V] in
private theorem conjAut_eq_conjBy_OrbI151c (g : MulAut V) (A : Subgroup (MulAut V)) :
    B1.conjAut g A = conjBy g A := by
  ext x
  rw [B1.mem_conjAut, mem_conjBy_iff]

omit [Finite V] in
private theorem perm_pair_OrbI151c {L₁ L₂ : Subgroup (MulAut V)} (hne : L₂ ≠ L₁) {x₂ : MulAut V}
    (hx₂ : x₂ ∈ X) (e₂ : conjBy x₂ L₁ = L₂)
    (horb : ∀ x ∈ X, conjBy x L₁ = L₁ ∨ conjBy x L₁ = L₂) :
    ∀ x ∈ X, (conjBy x L₁ = L₁ ∧ conjBy x L₂ = L₂) ∨ (conjBy x L₁ = L₂ ∧ conjBy x L₂ = L₁) := by
  intro g hg
  have horb₂ : conjBy g L₂ = L₂ ∨ conjBy g L₂ = L₁ := by
    have e : conjBy g L₂ = conjBy (g * x₂) L₁ := by rw [← e₂, conjBy_conjBy]
    rcases horb (g * x₂) (X.mul_mem hg hx₂) with h3 | h3
    · right; rw [e, h3]
    · left; rw [e, h3]
  rcases horb g hg with h3 | h3
  · left
    refine ⟨h3, ?_⟩
    rcases horb₂ with h4 | h4
    · exact h4
    · exact absurd (conjBy_injective g (h4.trans h3.symm)) hne
  · right
    refine ⟨h3, ?_⟩
    rcases horb₂ with h4 | h4
    · exact absurd (conjBy_injective g (h4.trans h3.symm)) hne
    · exact h4

omit [Finite V] in
private theorem sq_normalizes_OrbI151c {L₁ L₂ : Subgroup (MulAut V)} (hne : L₂ ≠ L₁)
    {x₂ : MulAut V} (hx₂ : x₂ ∈ X) (e₂ : conjBy x₂ L₁ = L₂)
    (horb : ∀ x ∈ X, conjBy x L₁ = L₁ ∨ conjBy x L₁ = L₂) :
    ∀ x ∈ X, conjBy (x * x) L₁ = L₁ ∧ conjBy (x * x) L₂ = L₂ := by
  intro x hx
  rcases perm_pair_OrbI151c hne hx₂ e₂ horb x hx with ⟨a1, a2⟩ | ⟨a1, a2⟩
  · exact ⟨by rw [← conjBy_conjBy, a1, a1], by rw [← conjBy_conjBy, a2, a2]⟩
  · exact ⟨by rw [← conjBy_conjBy, a1, a2], by rw [← conjBy_conjBy, a2, a1]⟩

private theorem twoNilp_of_noInvol_OrbI151c {L₁ L₂ : Subgroup (MulAut V)} (hne : L₂ ≠ L₁)
    {x₂ : MulAut V} (hx₂ : x₂ ∈ X) (e₂ : conjBy x₂ L₁ = L₂)
    (horb : ∀ x ∈ X, conjBy x L₁ = L₁ ∨ conjBy x L₁ = L₂) {p : ℕ} (hp : p = 3 ∨ p = 5)
    (e₁ : ↥L₁ ≃* DihedralGroup p) (e₂' : ↥L₂ ≃* DihedralGroup p)
    (hnoinv : ∀ z ∈ X, (∀ y ∈ L₁, y ^ p = 1 → y * z = z * y) →
      (∀ y ∈ L₂, y ^ p = 1 → y * z = z * y) → z * z = 1 → z = 1) :
    TwoNilpAut X := by
  set R : Set (MulAut V) := {y | (y ∈ L₁ ∨ y ∈ L₂) ∧ y ^ p = 1} with hR
  have hperm := perm_pair_OrbI151c hne hx₂ e₂ horb
  have hRconj : ∀ g ∈ X, ∀ y ∈ R, g * y * g⁻¹ ∈ R := by
    rintro g hg y ⟨hy, hyp⟩
    refine ⟨?_, by rw [conj_pow, hyp, mul_one, mul_inv_cancel]⟩
    rcases hy with hy | hy
    · have := mem_conjBy_of_mem (g := g) hy
      rcases hperm g hg with ⟨a1, -⟩ | ⟨a1, -⟩
      · rw [a1] at this; exact Or.inl this
      · rw [a1] at this; exact Or.inr this
    · have := mem_conjBy_of_mem (g := g) hy
      rcases hperm g hg with ⟨-, a2⟩ | ⟨-, a2⟩
      · rw [a2] at this; exact Or.inr this
      · rw [a2] at this; exact Or.inl this
  refine ⟨X ⊓ Subgroup.centralizer R, inf_le_left, ?_, ?_, ?_⟩
  · rintro g hg n ⟨hnX, hnc⟩
    refine ⟨X.mul_mem (X.mul_mem hg hnX) (X.inv_mem hg),
      Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ R := by
      have := hRconj g⁻¹ (X.inv_mem hg) y hy
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hnc _ hy'
    calc y * (g * n * g⁻¹) = g * ((g⁻¹ * y * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = (g * n * g⁻¹) * y := by group
  · by_contra hodd
    have heven : 2 ∣ Nat.card ↥(X ⊓ Subgroup.centralizer R) :=
      even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥(X ⊓ Subgroup.centralizer R)) 2 heven
    have hz2 : (z : MulAut V) * z = 1 := by
      have := pow_orderOf_eq_one z
      rw [hz, pow_two] at this
      exact congrArg Subtype.val this
    have hz1 : z = 1 := by
      refine Subtype.ext (hnoinv (z : MulAut V) z.2.1 (fun y hy hyp => ?_) (fun y hy hyp => ?_) hz2)
      · exact Subgroup.mem_centralizer_iff.mp z.2.2 y ⟨Or.inl hy, hyp⟩
      · exact Subgroup.mem_centralizer_iff.mp z.2.2 y ⟨Or.inr hy, hyp⟩
    rw [hz1, orderOf_one] at hz
    omega
  · intro x hx
    refine ⟨3, X.pow_mem hx _, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨s1, s2⟩ := sq_normalizes_OrbI151c hne hx₂ e₂ horb x hx
    have hx8 : x ^ 2 ^ 3 = (x * x) ^ 4 := by
      rw [← pow_two, ← pow_mul]
      norm_num
    rw [hx8]
    obtain ⟨hy, hyp⟩ := hy
    rcases hy with hy | hy
    · exact (pow_four_comm_of_normalizes_OrbI151c hp e₁
        (fun y hy => by have := mem_conjBy_of_mem (g := x * x) hy; rwa [s1] at this) y hy hyp).symm
    · exact (pow_four_comm_of_normalizes_OrbI151c hp e₂'
        (fun y hy => by have := mem_conjBy_of_mem (g := x * x) hy; rwa [s2] at this) y hy hyp).symm

open Classical in
private theorem actsAsNaturalL2_block_OrbI151c (h : Setting151c X Tb Xc)
    {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I) {L : Subgroup (MulAut V)}
    (hL : L ∈ I) (e : Nonempty (↥L ≃* DihedralGroup 3)) (hrk : rk (commV L) = 2) :
    ActsAsNaturalL2 L (commV L) := by
  have hs := suppData_block h hI hL
  have hUsq : ∀ v : ↥(commV L), v ^ 2 = 1 := fun v => Subtype.ext (h.sq v)
  have hcard : Nat.card ↥(commV L) = 4 := by
    rw [card_eq_two_pow h.sq, hrk]
    norm_num
  refine actsAsNaturalL2_of_full h.sq hcard (le_stabSub_commV L) hs.inf_centSub ?_
  obtain ⟨e⟩ := e
  have h6 : Nat.card (autSub L (commV L)) = 6 := by
    rw [← Nat.card_congr hs.restrictEquiv.toEquiv, Nat.card_congr e.toEquiv,
      DihedralGroup.nat_card]
  have h6' : Nat.card (MulAut ↥(commV L)) = 6 := card_mulAut_of_rk_two hUsq hrk
  exact (Subgroup.card_eq_iff_eq_top _).mp (by rw [h6, h6'])

open Classical in
private theorem false_of_rk_two_OrbI151c (h : Setting151c X Tb Xc)
    {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L₁ L₂ : Subgroup (MulAut V)} (h1 : L₁ ∈ I) (h2 : L₂ ∈ I) (hne : L₂ ≠ L₁) {x₂ : MulAut V}
    (hx₂ : x₂ ∈ X) (e₂ : conjBy x₂ L₁ = L₂)
    (horb : ∀ x ∈ X, conjBy x L₁ = L₁ ∨ conjBy x L₁ = L₂) (hJ : Jhat X = L₁ ⊔ L₂)
    (hfix : fixV (Jhat X) = ⊥) (hCE : ¬ IsOFourPlusAct X)
    (hS₁ : Nonempty (↥L₁ ≃* DihedralGroup 3)) (hrk : rk (commV L₁) = 2) : False := by
  obtain ⟨hUinf, hUsup⟩ := commV_pair_OrbI151c h hI h1 h2 hne hJ hfix
  have hLinf := block_inf_eq_bot hI h1 h2 hne.symm
  have hcomm := hI.comm L₁ h1 L₂ h2 hne.symm
  have hrk₂ : rk (commV L₂) = 2 := by rw [← e₂, rk_commV_conjBy]; exact hrk
  obtain ⟨iso⟩ := nonempty_equiv_conjBy_OrbI151c e₂
  have hN₁ := actsAsNaturalL2_block_OrbI151c h hI h1 hS₁ hrk
  have hN₂ := actsAsNaturalL2_block_OrbI151c h hI h2 ⟨iso.symm.trans hS₁.some⟩ hrk₂
  have hL₁X : L₁ ≤ X := (block_le_J hI h1).trans (Jhat_le X)
  have hL₂X : L₂ ≤ X := (block_le_J hI h2).trans (Jhat_le X)
  have hperm : ∀ g ∈ X, (B1.conjAut g L₁ = L₁ ∧ B1.conjAut g L₂ = L₂) ∨
      (B1.conjAut g L₁ = L₂ ∧ B1.conjAut g L₂ = L₁) := fun g hg => by
    simp only [conjAut_eq_conjBy_OrbI151c]
    exact perm_pair_OrbI151c hne hx₂ e₂ horb g hg
  have hcv : ∀ L : Subgroup (MulAut V), ∀ g ∈ X,
      (commV L).map g.toMonoidHom = commV (B1.conjAut g L) := fun L g _ => by
    rw [conjAut_eq_conjBy_OrbI151c]
    exact (commV_conjBy g L).symm
  rcases S1417.eq_sup_or_exists_swap hN₁ hN₂ hcomm hLinf hUinf hUsup hL₁X hL₂X hperm (hcv L₁)
      (hcv L₂) with hXeq | ⟨t', -, -, -, hc1, hc2, hXeq⟩
  · obtain ⟨τ, hτ, hτe⟩ := exists_swap_of_orbit_two h hne hx₂ e₂ horb
    have hτX : τ ∈ L₁ ⊔ L₂ := hXeq ▸ h.syl.1 hτ
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_sup_of_commute216 hcomm hτX
    have hb1 : conjBy b L₁ = L₁ := conjBy_eq_self_of_commute fun l hl => (hcomm l hl b hb).symm
    have hab : conjBy (a * b) L₁ = L₁ := by
      rw [← conjBy_conjBy, hb1]
      exact conjBy_eq_self_of_mem ha
    exact hne (hτe.symm.trans hab)
  · have hc1' : conjBy t' L₁ = L₂ := (conjAut_eq_conjBy_OrbI151c t' L₁).symm.trans hc1
    have hc2' : conjBy t' L₂ = L₁ := (conjAut_eq_conjBy_OrbI151c t' L₂).symm.trans hc2
    have ht₁ : ∀ u ∈ commV L₁, t' u ∈ commV L₂ := by
      intro u hu
      have : t' u ∈ commV (conjBy t' L₁) := by
        rw [commV_conjBy]
        exact ⟨u, hu, rfl⟩
      rwa [hc1'] at this
    have ht₂ : ∀ u ∈ commV L₂, t' u ∈ commV L₁ := by
      intro u hu
      have : t' u ∈ commV (conjBy t' L₂) := by
        rw [commV_conjBy]
        exact ⟨u, hu, rfl⟩
      rwa [hc2'] at this
    obtain ⟨hcard16, q, hq, hnd, hpl, hXq⟩ :=
      S1417.exists_quad_orthogonal hN₁ hN₂ hcomm hUinf hUsup ht₁ ht₂
    exact hCE ⟨hcard16, q, hq, hnd, hpl, hXeq.trans hXq⟩

omit [Finite V] in
private theorem normalizes_of_commute_OrbI151c {L₁ L₂ : Subgroup (MulAut V)}
    (hLinf : L₁ ⊓ L₂ = ⊥) (hne : L₂ ≠ L₁) {x₂ : MulAut V} (hx₂ : x₂ ∈ X)
    (e₂ : conjBy x₂ L₁ = L₂) (horb : ∀ x ∈ X, conjBy x L₁ = L₁ ∨ conjBy x L₁ = L₂)
    {z a : MulAut V} (hz : z ∈ X) (ha : a ∈ L₁) (ha1 : a ≠ 1) (hza : z * a = a * z) :
    conjBy z L₁ = L₁ ∧ conjBy z L₂ = L₂ := by
  rcases perm_pair_OrbI151c hne hx₂ e₂ horb z hz with h | ⟨h1, -⟩
  · exact h
  · exfalso
    have hmem : z * a * z⁻¹ ∈ conjBy z L₁ := mem_conjBy_of_mem ha
    rw [h1, hza, mul_inv_cancel_right] at hmem
    have : a ∈ L₁ ⊓ L₂ := ⟨ha, hmem⟩
    rw [hLinf, Subgroup.mem_bot] at this
    exact ha1 this

private theorem d3_comm_cube_OrbI151c : ∀ w : DihedralGroup 3,
    w * DihedralGroup.r 1 = DihedralGroup.r 1 * w → w * w * w = 1 := by
  decide

private theorem cube_eq_one_of_commute_OrbI151c {G : Type*} [Group G] {L : Subgroup G}
    (e : ↥L ≃* DihedralGroup 3) {l : G} (hl : l ∈ L)
    (hc : l * ((e.symm (DihedralGroup.r 1) : ↥L) : G) =
      ((e.symm (DihedralGroup.r 1) : ↥L) : G) * l) : l ^ 3 = 1 := by
  have h1 : (⟨l, hl⟩ : ↥L) * e.symm (DihedralGroup.r 1) =
      e.symm (DihedralGroup.r 1) * ⟨l, hl⟩ := Subtype.ext hc
  have h2 := congrArg e h1
  rw [map_mul, map_mul, MulEquiv.apply_symm_apply] at h2
  have h3 := d3_comm_cube_OrbI151c _ h2
  have h4 : (⟨l, hl⟩ : ↥L) ^ 3 = 1 := by
    apply e.injective
    rw [map_pow, map_one, pow_three']
    exact h3
  simpa using congrArg Subtype.val h4

open Classical in
private theorem stab_le_J_OrbI151c (h : Setting151c X Tb Xc) {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L₁ L₂ : Subgroup (MulAut V)} (h1 : L₁ ∈ I) (h2 : L₂ ∈ I)
    (hne : L₂ ≠ L₁) {x₂ : MulAut V} (hx₂ : x₂ ∈ X) (e₂ : conjBy x₂ L₁ = L₂)
    (horb : ∀ x ∈ X, conjBy x L₁ = L₁ ∨ conjBy x L₁ = L₂) (hJ : Jhat X = L₁ ⊔ L₂)
    (hfix : fixV (Jhat X) = ⊥) (hS₁ : S3Block L₁) :
    ∀ x ∈ X, conjBy x L₁ = L₁ → x ∈ L₁ ⊔ L₂ := by
  have hS₂ : S3Block L₂ := S3Block_of_conj e₂ hS₁
  have hI2 := blocks_eq_pair_OrbI151c hI h1 h2 hJ
  have hS : ∀ L ∈ I, S3Block L := fun L hL =>
    (hI2 L hL).elim (fun e => e ▸ hS₁) (fun e => e ▸ hS₂)
  obtain ⟨-, hUsup⟩ := commV_pair_OrbI151c h hI h1 h2 hne hJ hfix
  have hLX : ∀ L ∈ I, L ≤ X := fun L hL => (block_le_J hI hL).trans (Jhat_le X)
  have hperm := perm_pair_OrbI151c hne hx₂ e₂ horb
  obtain ⟨e₁'⟩ := hS₁.1
  obtain ⟨e₂'⟩ := hS₂.1
  set N : Subgroup (MulAut V) := stabConj X L₁ with hN
  have hNn : ∀ x ∈ N, conjBy x L₂ = L₂ := fun x hx =>
    ((hperm x hx.1).resolve_right (fun hh => hne (hh.1.symm.trans hx.2))).2
  have hL₁N : L₁ ≤ N := fun l hl => ⟨hLX L₁ h1 hl, conjBy_eq_self_of_mem hl⟩
  have step1 : ∀ x ∈ N, ∃ l ∈ L₁, ∃ d ∈ N, (∀ m ∈ L₁, d * m = m * d) ∧ x = l * d :=
    fun x hx => exists_mul_eq_of_normalizes_D3 e₁' hL₁N
      (fun y hy => mem_normalizer_of_conjBy_eq hy.2) hx
  set N' : Subgroup (MulAut V) := N ⊓ Subgroup.centralizer (L₁ : Set (MulAut V)) with hN'
  have hL₂N' : L₂ ≤ N' := by
    intro l hl
    have hcomm' : ∀ m ∈ L₁, l * m = m * l := fun m hm => hI.comm L₂ h2 L₁ h1 hne l hl m hm
    exact ⟨⟨hLX L₂ h2 hl, conjBy_eq_self_of_commute hcomm'⟩,
      Subgroup.mem_centralizer_iff.mpr fun m hm => (hcomm' m hm).symm⟩
  have step2 : ∀ x ∈ N', ∃ l ∈ L₂, ∃ d ∈ N', (∀ m ∈ L₂, d * m = m * d) ∧ x = l * d :=
    fun x hx => exists_mul_eq_of_normalizes_D3 e₂' hL₂N'
      (fun y hy => mem_normalizer_of_conjBy_eq (hNn y hy.1)) hx
  set D₂ : Subgroup (MulAut V) :=
    X ⊓ Subgroup.centralizer (L₁ : Set (MulAut V)) ⊓ Subgroup.centralizer (L₂ : Set (MulAut V))
    with hD₂
  have hdc : ∀ d ∈ D₂, ∀ m, (m ∈ L₁ ∨ m ∈ L₂) → d * m = m * d := by
    intro d hd m hm
    rcases hm with hm | hm
    · exact (Subgroup.mem_centralizer_iff.mp hd.1.2 m hm).symm
    · exact (Subgroup.mem_centralizer_iff.mp hd.2 m hm).symm
  have hconjmem : ∀ x ∈ X, ∀ l, (l ∈ L₁ ∨ l ∈ L₂) →
      (x * l * x⁻¹ ∈ L₁ ∨ x * l * x⁻¹ ∈ L₂) := by
    intro x hx l hl
    rcases hl with hl | hl
    · have hm := mem_conjBy_of_mem (g := x) hl
      rcases hperm x hx with ⟨a1, -⟩ | ⟨a1, -⟩
      · rw [a1] at hm; exact Or.inl hm
      · rw [a1] at hm; exact Or.inr hm
    · have hm := mem_conjBy_of_mem (g := x) hl
      rcases hperm x hx with ⟨-, a2⟩ | ⟨-, a2⟩
      · rw [a2] at hm; exact Or.inr hm
      · rw [a2] at hm; exact Or.inl hm
  have hD₂n : NormalIn X D₂ := by
    intro x hx d hd
    have key : ∀ l, (x⁻¹ * l * x ∈ L₁ ∨ x⁻¹ * l * x ∈ L₂) →
        x * d * x⁻¹ * l = l * (x * d * x⁻¹) := by
      intro l hl
      have hc := hdc d hd _ hl
      calc x * d * x⁻¹ * l = x * (d * (x⁻¹ * l * x)) * x⁻¹ := by group
        _ = x * ((x⁻¹ * l * x) * d) * x⁻¹ := by rw [hc]
        _ = l * (x * d * x⁻¹) := by group
    have hinv : ∀ l, (l ∈ L₁ ∨ l ∈ L₂) → (x⁻¹ * l * x ∈ L₁ ∨ x⁻¹ * l * x ∈ L₂) := by
      intro l hl
      simpa using hconjmem x⁻¹ (X.inv_mem hx) l hl
    refine ⟨⟨X.mul_mem (X.mul_mem hx hd.1.1) (X.inv_mem hx), ?_⟩, ?_⟩
    · exact Subgroup.mem_centralizer_iff.mpr fun l hl => (key l (hinv l (Or.inl hl))).symm
    · exact Subgroup.mem_centralizer_iff.mpr fun l hl => (key l (hinv l (Or.inr hl))).symm
  have hodd1 : ∀ d ∈ D₂, Odd (orderOf d) → d = 1 := by
    intro d hd hodd
    have hd1 : ∀ l ∈ L₁, d * l = l * d := fun l hl => hdc d hd l (Or.inl hl)
    have hd2 : ∀ l ∈ L₂, d * l = l * d := fun l hl => hdc d hd l (Or.inr hl)
    have hno3 := not_three_dvd_orderOf h hr hr2 hI hS h1 h2 hne.symm hd.1.1 hd1 hd2
    have hcop : Nat.Coprime (orderOf d) 6 := by
      have h6 : (6 : ℕ) = 2 * 3 := by norm_num
      rw [h6]
      exact Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hodd)
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hno3).symm
    have hf1 := fix_commV_of_coprime h hr hr2 hI h1 hS₁ hd1 hcop
    have hf2 := fix_commV_of_coprime h hr hr2 hI h2 hS₂ hd2 hcop
    refine MulEquiv.ext fun v => ?_
    have hv : v ∈ commV L₁ ⊔ commV L₂ := by rw [hUsup]; exact Subgroup.mem_top v
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.mp hv
    show d (u₁ * u₂) = (1 : MulAut V) (u₁ * u₂)
    rw [map_mul, hf1 u₁ hu₁, hf2 u₂ hu₂]
    rfl
  have hD₂p : IsPGroup 2 D₂ := by
    intro d
    obtain ⟨k, m, hm, hdm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (d : MulAut V)).ne'
    have hdk : (d : MulAut V) ^ 2 ^ k ∈ D₂ := D₂.pow_mem d.2 _
    have hk0 : 0 < 2 ^ k := by positivity
    have hord : orderOf ((d : MulAut V) ^ 2 ^ k) = m := by
      rw [orderOf_pow_of_dvd hk0.ne' ⟨m, hdm⟩, hdm, Nat.mul_div_cancel_left m hk0]
    have h1' := hodd1 _ hdk (hord ▸ hm)
    rw [h1', orderOf_one] at hord
    refine ⟨k, Subtype.ext ?_⟩
    have : orderOf (d : MulAut V) = 2 ^ k := by rw [hdm, ← hord, mul_one]
    show (d : MulAut V) ^ 2 ^ k = 1
    rw [← this]
    exact pow_orderOf_eq_one _
  have hD₂bot : D₂ = ⊥ := by
    have hle : D₂ ≤ pCoreOf 2 X :=
      le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans inf_le_left) hD₂n.le_normalizer hD₂p
    rw [h.o2, le_bot_iff] at hle
    exact hle
  intro x hx hxL
  have hxN : x ∈ N := ⟨hx, hxL⟩
  obtain ⟨l₁, hl₁, d₁, hd₁N, hd₁c, rfl⟩ := step1 x hxN
  have hd₁N' : d₁ ∈ N' :=
    ⟨hd₁N, Subgroup.mem_centralizer_iff.mpr fun m hm => (hd₁c m hm).symm⟩
  obtain ⟨l₂, hl₂, d₂, hd₂N', hd₂c, rfl⟩ := step2 d₁ hd₁N'
  have hd₂D : d₂ ∈ D₂ :=
    ⟨⟨hd₂N'.1.1, hd₂N'.2⟩, Subgroup.mem_centralizer_iff.mpr fun m hm => (hd₂c m hm).symm⟩
  rw [hD₂bot, Subgroup.mem_bot] at hd₂D
  rw [hd₂D, mul_one]
  exact Subgroup.mul_mem_sup hl₁ hl₂

open Classical in
private theorem genTop_p3_OrbI151c (h : Setting151c X Tb Xc) {L₁ L₂ : Subgroup (MulAut V)}
    (hne : L₂ ≠ L₁) {x₂ : MulAut V} (hx₂ : x₂ ∈ X) (e₂ : conjBy x₂ L₁ = L₂)
    (horb : ∀ x ∈ X, conjBy x L₁ = L₁ ∨ conjBy x L₁ = L₂) (hJ : Jhat X = L₁ ⊔ L₂)
    (hstab : ∀ x ∈ X, conjBy x L₁ = L₁ → x ∈ L₁ ⊔ L₂) :
    (∀ x ∈ X, ∃ j ∈ Jhat X, ∃ t ∈ Tb, x = j * t) ∧ GenTop (Jhat X) Tb := by
  have hXJT : ∀ x ∈ X, ∃ j ∈ Jhat X, ∃ t ∈ Tb, x = j * t := by
    intro x hx
    rcases perm_pair_OrbI151c hne hx₂ e₂ horb x hx with ⟨a1, -⟩ | ⟨a1, a2⟩
    · exact ⟨x, by rw [hJ]; exact hstab x hx a1, 1, Tb.one_mem, by simp⟩
    · obtain ⟨τ, hτ, hτe⟩ := exists_swap_of_orbit_two h hne hx₂ e₂ horb
      have hτX : τ ∈ X := h.syl.1 hτ
      have hτ2 : conjBy τ L₂ = L₁ := by
        rcases perm_pair_OrbI151c hne hx₂ e₂ horb τ hτX with ⟨b1, -⟩ | ⟨-, b2⟩
        · exact absurd (hτe.symm.trans b1) hne
        · exact b2
      have hτ' : conjBy τ⁻¹ L₁ = L₂ := conjBy_inv_eq_of_eq hτ2
      refine ⟨x * τ⁻¹, ?_, τ, hτ, by group⟩
      rw [hJ]
      refine hstab _ (X.mul_mem hx (X.inv_mem hτX)) ?_
      rw [← conjBy_conjBy, hτ', a2]
  refine ⟨hXJT, ?_⟩
  unfold GenTop
  refine h.gen _ ?_
  intro g hg z hz
  obtain ⟨j, hj, t, ht, rfl⟩ := hXJT g hg
  have hz' : t z = z := hz t ht
  have : (j * t) z = j z := by rw [MulAut.mul_apply, hz']
  rw [this]
  exact Subgroup.subset_closure ⟨j, hj, z, hz, rfl⟩

omit [Finite V] in
private theorem noInvol_p3_OrbI151c {L₁ L₂ : Subgroup (MulAut V)} (hLinf : L₁ ⊓ L₂ = ⊥)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hne : L₂ ≠ L₁) {x₂ : MulAut V}
    (hx₂ : x₂ ∈ X) (e₂ : conjBy x₂ L₁ = L₂)
    (horb : ∀ x ∈ X, conjBy x L₁ = L₁ ∨ conjBy x L₁ = L₂)
    (hstab : ∀ x ∈ X, conjBy x L₁ = L₁ → x ∈ L₁ ⊔ L₂) (e₁ : ↥L₁ ≃* DihedralGroup 3)
    (e₂' : ↥L₂ ≃* DihedralGroup 3) :
    ∀ z ∈ X, (∀ y ∈ L₁, y ^ 3 = 1 → y * z = z * y) → (∀ y ∈ L₂, y ^ 3 = 1 → y * z = z * y) →
      z * z = 1 → z = 1 := by
  intro z hz hz1 hz2 hzz
  obtain ⟨ha₁L, ha₁p, ha₁1⟩ := rot_gen_props_OrbI151c (Or.inl rfl) e₁
  obtain ⟨ha₂L, ha₂p, -⟩ := rot_gen_props_OrbI151c (Or.inl rfl) e₂'
  set a₁ : MulAut V := ((e₁.symm (DihedralGroup.r 1) : ↥L₁) : MulAut V) with ha₁def
  set a₂ : MulAut V := ((e₂'.symm (DihedralGroup.r 1) : ↥L₂) : MulAut V) with ha₂def
  have hza₁ : z * a₁ = a₁ * z := (hz1 _ ha₁L ha₁p).symm
  have hza₂ : z * a₂ = a₂ * z := (hz2 _ ha₂L ha₂p).symm
  obtain ⟨hn1, -⟩ := normalizes_of_commute_OrbI151c hLinf hne hx₂ e₂ horb hz ha₁L ha₁1 hza₁
  obtain ⟨l₁, hl₁, l₂, hl₂, hzl⟩ := mem_sup_of_commute216 hcomm (hstab z hz hn1)
  have hl₁a : l₁ * a₁ = a₁ * l₁ := by
    have h1 : l₁ * l₂ * a₁ = a₁ * (l₁ * l₂) := by rw [← hzl]; exact hza₁
    have h2 : a₁ * l₂ = l₂ * a₁ := hcomm _ ha₁L l₂ hl₂
    have h3 : (l₁ * a₁) * l₂ = (a₁ * l₁) * l₂ := by
      calc (l₁ * a₁) * l₂ = l₁ * (a₁ * l₂) := by group
        _ = l₁ * (l₂ * a₁) := by rw [h2]
        _ = (l₁ * l₂) * a₁ := by group
        _ = a₁ * (l₁ * l₂) := h1
        _ = (a₁ * l₁) * l₂ := by group
    exact mul_right_cancel h3
  have hl₂a : l₂ * a₂ = a₂ * l₂ := by
    have h1 : l₁ * l₂ * a₂ = a₂ * (l₁ * l₂) := by rw [← hzl]; exact hza₂
    have h2 : l₁ * a₂ = a₂ * l₁ := hcomm l₁ hl₁ _ ha₂L
    have h3 : l₁ * (l₂ * a₂) = l₁ * (a₂ * l₂) := by
      calc l₁ * (l₂ * a₂) = (l₁ * l₂) * a₂ := by group
        _ = a₂ * (l₁ * l₂) := h1
        _ = (a₂ * l₁) * l₂ := by group
        _ = (l₁ * a₂) * l₂ := by rw [h2]
        _ = l₁ * (a₂ * l₂) := by group
    exact mul_left_cancel h3
  have hc1 := cube_eq_one_of_commute_OrbI151c e₁ hl₁ hl₁a
  have hc2 := cube_eq_one_of_commute_OrbI151c e₂' hl₂ hl₂a
  have hz3 : z ^ 3 = 1 := by
    rw [hzl, Commute.mul_pow (hcomm l₁ hl₁ l₂ hl₂), hc1, hc2, one_mul]
  calc z = z ^ 3 * (z * z)⁻¹ := by group
    _ = 1 := by rw [hz3, hzz]; simp

open Classical in
private theorem fix_of_commute_D5_OrbI151c (h : Setting151c X Tb Xc) {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L : Subgroup (MulAut V)} (hL : L ∈ I)
    (e : ↥L ≃* DihedralGroup 5) (hrk : rk (commV L) = 4) {z : MulAut V}
    (hzs : z ∈ stabSub (commV L)) (hz2 : z * z = 1)
    (hza : z * ((e.symm (DihedralGroup.r 1) : ↥L) : MulAut V) =
      ((e.symm (DihedralGroup.r 1) : ↥L) : MulAut V) * z) :
    ∀ u ∈ commV L, z u = u := by
  have hs := suppData_block h hI hL
  have hH := block_d217hyp h hr hr2 hI hL
  have hUsq : ∀ v : ↥(commV L), v ^ 2 = 1 := fun v => Subtype.ext (h.sq v)
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨haL, hap, -⟩ := rot_gen_props_OrbI151c (Or.inr rfl) e
  set eY : ↥(autSub L (commV L)) ≃* DihedralGroup 5 := hs.restrictEquiv.symm.trans e with heY
  set a : MulAut V := ((e.symm (DihedralGroup.r 1) : ↥L) : MulAut V) with ha
  set a' : MulAut ↥(commV L) := resHom (commV L) ⟨a, hs.stab haL⟩ with ha'
  have hay : ((eY.symm (DihedralGroup.r 1) : ↥(autSub L (commV L))) : MulAut ↥(commV L)) = a' :=
    hs.restrictEquiv_coe _
  have hFP : fittingOf (autSub L (commV L)) ≤ Subgroup.zpowers a' := by
    intro f hf
    have hfY : f ∈ autSub L (commV L) := fittingOf_le _ hf
    have hcardY : Nat.card ↥(autSub L (commV L)) = 10 := by
      rw [Nat.card_congr eY.toEquiv, DihedralGroup.nat_card]
    have hodd := odd_card_fittingOf hH.o2
    have hd1 : orderOf f ∣ Nat.card (fittingOf (autSub L (commV L))) := by
      have := orderOf_dvd_natCard (⟨f, hf⟩ : ↥(fittingOf (autSub L (commV L))))
      rwa [Subgroup.orderOf_mk] at this
    have hd2 : orderOf f ∣ 10 := by
      have := orderOf_dvd_natCard (⟨f, hfY⟩ : ↥(autSub L (commV L)))
      rwa [Subgroup.orderOf_mk, hcardY] at this
    have hoddo : Odd (orderOf f) := hodd.of_dvd_nat hd1
    have hd5 : orderOf f ∣ 5 := by
      have : orderOf f ∣ 5 * 2 := hd2
      exact (Nat.coprime_two_right.mpr hoddo).dvd_of_dvd_mul_right this
    have hf5 : f ^ 5 = 1 := orderOf_dvd_iff_pow_eq_one.mp hd5
    obtain ⟨m, hm⟩ := exists_pow_of_pow_eq_one_OrbI151c (Or.inr rfl) eY hfY hf5
    rw [hay] at hm
    exact Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), by rw [zpow_natCast]; exact hm.symm⟩
  have hfixF := fixV_fittingOf_eq_bot hUsq hH.o2 hH.comm_fitting
  have hfixP : fixV (Subgroup.zpowers a') = ⊥ :=
    le_bot_iff.mp ((fixV_anti hFP).trans (le_of_eq hfixF))
  have hP5 : IsPGroup 5 (Subgroup.zpowers a') := by
    have ha'5 : a' ^ 5 = 1 := by
      have : (⟨a, hs.stab haL⟩ : ↥(stabSub (commV L))) ^ 5 = 1 := Subtype.ext (by simpa using hap)
      rw [ha', ← map_pow, this, map_one]
    have hord : orderOf a' ∣ 5 := orderOf_dvd_of_pow_eq_one ha'5
    rcases (Nat.dvd_prime Nat.prime_five).mp hord with h1 | h5
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h5]; rfl)
  set ρ : MulAut ↥(commV L) := resHom (commV L) ⟨z, hzs⟩ with hρ
  have hρρ : ρ * ρ = 1 := by
    have : (⟨z, hzs⟩ : ↥(stabSub (commV L))) * ⟨z, hzs⟩ = 1 := Subtype.ext hz2
    rw [hρ, ← map_mul, this, map_one]
  have hρa : ρ * a' = a' * ρ := by
    have : (⟨z, hzs⟩ : ↥(stabSub (commV L))) * ⟨a, hs.stab haL⟩ =
        ⟨a, hs.stab haL⟩ * ⟨z, hzs⟩ := Subtype.ext hza
    rw [hρ, ha', ← map_mul, ← map_mul, this]
  set K : Subgroup ↥(commV L) := fixV (Subgroup.zpowers ρ) with hK
  have hKinv : ∀ g ∈ Subgroup.zpowers a', ∀ b ∈ K, g b ∈ K := by
    intro g hg b hb
    have hρb : ρ b = b := mem_fixV_zpowers_iff.mp hb
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hcg : ρ * a' ^ n = a' ^ n * ρ := (Commute.zpow_right (show Commute ρ a' from hρa) n).eq
    refine mem_fixV_zpowers_iff.mpr ?_
    calc ρ ((a' ^ n) b) = (ρ * a' ^ n) b := rfl
      _ = (a' ^ n * ρ) b := by rw [hcg]
      _ = (a' ^ n) (ρ b) := rfl
      _ = (a' ^ n) b := by rw [hρb]
  have hmod := card_invariant_modEq hP5 hfixP hKinv
  have hKne : K ≠ ⊥ := by
    have hρ2 : IsPGroup 2 (Subgroup.zpowers ρ) :=
      (isElemAbelian2_zpowers151c (s := ρ) (by rw [pow_two]; exact hρρ)).isPGroup
    have hrkpos : 0 < rk ↥(commV L) := by rw [hrk]; norm_num
    have h0 : 0 < rk K := rk_fixV_pos_of_isPGroup_two hUsq hρ2 hrkpos
    intro hbot
    rw [hbot, rk_bot] at h0
    exact lt_irrefl _ h0
  have hKdvd : Nat.card K ∣ 16 := by
    have := Subgroup.card_subgroup_dvd_card K
    rwa [card_eq_two_pow_rk hUsq, hrk] at this
  have hK16 : Nat.card K = 16 := by
    have hpos := Nat.card_pos (α := K)
    have hle := Nat.le_of_dvd (by norm_num) hKdvd
    have h1 : Nat.card K ≠ 1 := fun h1 => hKne (Subgroup.card_eq_one.mp h1)
    unfold Nat.ModEq at hmod
    generalize Nat.card K = n at *
    interval_cases n <;> omega
  have hKtop : K = ⊤ := by
    refine (Subgroup.card_eq_iff_eq_top K).mp ?_
    rw [hK16, card_eq_two_pow_rk hUsq, hrk]
    norm_num
  intro u hu
  have hmem : (⟨u, hu⟩ : ↥(commV L)) ∈ K := by rw [hKtop]; exact Subgroup.mem_top _
  have h3 : ρ ⟨u, hu⟩ = ⟨u, hu⟩ := mem_fixV_zpowers_iff.mp hmem
  exact congrArg Subtype.val h3

open Classical in
private theorem noInvol_p5_OrbI151c (h : Setting151c X Tb Xc) {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L₁ L₂ : Subgroup (MulAut V)} (h1 : L₁ ∈ I) (h2 : L₂ ∈ I)
    (hne : L₂ ≠ L₁) {x₂ : MulAut V} (hx₂ : x₂ ∈ X) (e₂ : conjBy x₂ L₁ = L₂)
    (horb : ∀ x ∈ X, conjBy x L₁ = L₁ ∨ conjBy x L₁ = L₂) (hJ : Jhat X = L₁ ⊔ L₂)
    (hfix : fixV (Jhat X) = ⊥) (e₁ : ↥L₁ ≃* DihedralGroup 5) (e₂' : ↥L₂ ≃* DihedralGroup 5)
    (hrk₁ : rk (commV L₁) = 4) (hrk₂ : rk (commV L₂) = 4) :
    ∀ z ∈ X, (∀ y ∈ L₁, y ^ 5 = 1 → y * z = z * y) → (∀ y ∈ L₂, y ^ 5 = 1 → y * z = z * y) →
      z * z = 1 → z = 1 := by
  intro z hz hz1 hz2 hzz
  obtain ⟨-, hUsup⟩ := commV_pair_OrbI151c h hI h1 h2 hne hJ hfix
  have hLinf := block_inf_eq_bot hI h1 h2 hne.symm
  obtain ⟨ha₁L, ha₁p, ha₁1⟩ := rot_gen_props_OrbI151c (Or.inr rfl) e₁
  obtain ⟨ha₂L, ha₂p, -⟩ := rot_gen_props_OrbI151c (Or.inr rfl) e₂'
  have hza₁ := (hz1 _ ha₁L ha₁p).symm
  have hza₂ := (hz2 _ ha₂L ha₂p).symm
  obtain ⟨hn1, hn2⟩ := normalizes_of_commute_OrbI151c hLinf hne hx₂ e₂ horb hz ha₁L ha₁1 hza₁
  have hf1 := fix_of_commute_D5_OrbI151c h hr hr2 hI h1 e₁ hrk₁
    (mem_stabSub_commV_of_conjBy hn1) hzz hza₁
  have hf2 := fix_of_commute_D5_OrbI151c h hr hr2 hI h2 e₂' hrk₂
    (mem_stabSub_commV_of_conjBy hn2) hzz hza₂
  refine MulEquiv.ext fun v => ?_
  have hv : v ∈ commV L₁ ⊔ commV L₂ := by rw [hUsup]; exact Subgroup.mem_top v
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.mp hv
  show z (u₁ * u₂) = (1 : MulAut V) (u₁ * u₂)
  rw [map_mul, hf1 u₁ hu₁, hf2 u₂ hu₂]
  rfl

omit [Finite V] in
private theorem not_S3Block_of_D5_OrbI151c {L : Subgroup (MulAut V)}
    (e : ↥L ≃* DihedralGroup 5) : ¬ S3Block L := by
  rintro ⟨⟨e'⟩, -⟩
  have h1 : Nat.card ↥L = 6 := by rw [Nat.card_congr e'.toEquiv, DihedralGroup.nat_card]
  have h2 : Nat.card ↥L = 10 := by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  omega

open Classical in
private theorem genTop_p5_OrbI151c (h : Setting151c X Tb Xc) {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L₁ L₂ : Subgroup (MulAut V)} (h1 : L₁ ∈ I) (h2 : L₂ ∈ I)
    (hne : L₂ ≠ L₁) {x₂ : MulAut V} (hx₂ : x₂ ∈ X) (e₂ : conjBy x₂ L₁ = L₂)
    (horb : ∀ x ∈ X, conjBy x L₁ = L₁ ∨ conjBy x L₁ = L₂) (hJ : Jhat X = L₁ ⊔ L₂)
    (hfix : fixV (Jhat X) = ⊥) (hnS₁ : ¬ S3Block L₁) (hnS₂ : ¬ S3Block L₂) :
    GenTop (Jhat X) Tb := by
  obtain ⟨τ, hτ, hτe⟩ := exists_swap_of_orbit_two h hne hx₂ e₂ horb
  have hperm := perm_pair_OrbI151c hne hx₂ e₂ horb
  have hτ2 : conjBy τ L₂ = L₁ := by
    rcases hperm τ (h.syl.1 hτ) with ⟨b1, -⟩ | ⟨-, b2⟩
    · exact absurd (hτe.symm.trans b1) hne
    · exact b2
  have hτ' : conjBy τ⁻¹ L₂ = L₁ := conjBy_inv_eq_of_eq hτe
  have horb₂ : ∀ x ∈ X, conjBy x L₂ = L₂ ∨ conjBy x L₂ = L₁ := fun x hx =>
    (hperm x hx).elim (fun h' => Or.inl h'.2) (fun h' => Or.inr h'.2)
  have hq1 := pair_le_closure h hr hr2 hI h1 h2 hne hτ hτe horb hnS₁
  have hq2 := pair_le_closure h hr hr2 hI h2 h1 hne.symm (Tb.inv_mem hτ) hτ' horb₂ hnS₂
  rw [sup_comm L₂ L₁] at hq2
  obtain ⟨-, hUsup⟩ := commV_pair_OrbI151c h hI h1 h2 hne hJ hfix
  have hsub : {x | ∃ g ∈ L₁ ⊔ L₂, ∃ z ∈ fixV Tb ⊓ commV (L₁ ⊔ L₂), g z = x} ⊆
      {x | ∃ ψ ∈ Jhat X, ∃ z ∈ fixV Tb, ψ z = x} := by
    rintro x ⟨g, hg, z, hz, rfl⟩
    exact ⟨g, by rw [hJ]; exact hg, z, hz.1, rfl⟩
  unfold GenTop
  rw [eq_top_iff, ← hUsup]
  exact sup_le (hq1.trans (Subgroup.closure_mono hsub)) (hq2.trans (Subgroup.closure_mono hsub))

open Classical in
private theorem exists_order_two_OrbI151c (h : Setting151c X Tb Xc) {r : ℚ}
    (hr : qhatOf X = (r : WithTop ℚ)) (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))}
    (hI : IsBlocks216 (Jhat X) I) {L : Subgroup (MulAut V)} (hL : L ∈ I) {p : ℕ}
    (hp : p = 3 ∨ p = 5) (e : ↥L ≃* DihedralGroup p) : ∃ A ∈ QhatStar X, Nat.card A = 2 := by
  obtain ⟨A, hA⟩ := block_qstar_nonempty hI hL
  have hsyl := block_qstar_eq_sylow h hr hr2 hI hL
  have hAX : A ∈ QhatStar X := by
    have h1 := (block_qhat hr hr2 hI hL).1
    rw [h1] at hA
    exact hA.1
  refine ⟨A, hAX, ?_⟩
  have hAs : A ∈ sylow2Of L := hsyl ▸ hA
  have hodd : Odd p := by rcases hp with rfl | rfl <;> decide
  have hcard : Nat.card L = 2 ^ 1 * p := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    ring
  have hrkA : rk A = 1 := rk_eq_of_mem_sylow2Of hAs hodd hcard
  have := card_eq_two_pow_of_isPGroup hAs.2.1
  rw [hrkA] at this
  simpa using this

open Classical in
theorem twoOrbit_cases (h : Setting151c X Tb Xc) {r : ℚ} (hr : qhatOf X = (r : WithTop ℚ))
    (hr2 : r ≤ 2) {I : Finset (Subgroup (MulAut V))} (hI : IsBlocks216 (Jhat X) I)
    {L₁ L₂ : Subgroup (MulAut V)} (h1 : L₁ ∈ I) (h2 : L₂ ∈ I) (hne : L₂ ≠ L₁)
    {x₂ : MulAut V} (hx₂ : x₂ ∈ X) (e₂ : conjBy x₂ L₁ = L₂)
    (horb : ∀ x ∈ X, conjBy x L₁ = L₁ ∨ conjBy x L₁ = L₂)
    (hJ : Jhat X = L₁ ⊔ L₂) (hfix : fixV (Jhat X) = ⊥) (hCE : ¬ IsOFourPlusAct X) :
    r = 2 ∧ (∃ p : ℕ, (p = 3 ∨ p = 5) ∧ ACase6 Tb (Jhat X) p) ∧ TwoNilpAut X ∧
      GenTop (Jhat X) Tb ∧ ∃ A ∈ QhatStar X, Nat.card A = 2 := by
  have hs₁ := suppData_block h hI h1
  have hLinf := block_inf_eq_bot hI h1 h2 hne.symm
  have hcomm := hI.comm L₁ h1 L₂ h2 hne.symm
  obtain ⟨hUinf, hUsup⟩ := commV_pair_OrbI151c h hI h1 h2 hne hJ hfix
  obtain ⟨t, htT, het⟩ := exists_swap_of_orbit_two h hne hx₂ e₂ horb
  have hcycF : IsCyclic ↥(fittingOf L₁) :=
    orbit_two_fitting_cyclic h hr hr2 hI h1 h2 hne.symm e₂.symm
  have hcycY : IsCyclic ↥(fittingOf (autSub L₁ (commV L₁))) := by
    by_contra hnc
    exact not_isCyclic_fittingOf_block h hI h1 hnc hcycF
  obtain ⟨iso⟩ := nonempty_equiv_conjBy_OrbI151c e₂
  have hrk₂ : rk (commV L₂) = rk (commV L₁) := by rw [← e₂, rk_commV_conjBy]
  have key : ∀ p : ℕ, (p = 3 ∨ p = 5) →
      Nonempty (↥(autSub L₁ (commV L₁)) ≃* DihedralGroup p) → rk (commV L₁) = 4 →
      ACase6 Tb (Jhat X) p := by
    intro p _ ⟨eY⟩ hrk
    have eL₁ : ↥L₁ ≃* DihedralGroup p := hs₁.restrictEquiv.trans eY
    refine ⟨?_, L₁, L₂, ⟨hJ, hLinf, hcomm⟩, ⟨eL₁⟩, ⟨iso.symm.trans eL₁⟩, ⟨t, htT, het⟩, hUinf,
      hUsup⟩
    have hc := card_sup_mul_card_inf (commV L₁) (commV L₂)
    rw [hUsup, hUinf, Subgroup.card_top, Subgroup.card_bot, mul_one, card_eq_two_pow h.sq,
      card_eq_two_pow h.sq, hrk, hrk₂, hrk] at hc
    rw [hc]
    norm_num
  obtain ⟨-, hD⟩ := block_d217 h hr hr2 hI h1
  rcases dihedral_shapes_OrbI151c hD hcycY with ⟨hY, hrk, hr12⟩ | ⟨hY, hrk, hr_eq⟩
  · have hr_eq : r = 2 := by
      rcases hr12 with hr1 | hr2'
      · exfalso
        have hrk2 : rk (commV L₁) = 2 := by
          have : (rk (commV L₁) : ℚ) = 2 := by rw [hrk, hr1]; norm_num
          exact_mod_cast this
        exact false_of_rk_two_OrbI151c h hI h1 h2 hne hx₂ e₂ horb hJ hfix hCE
          ⟨hs₁.restrictEquiv.trans hY.some⟩ hrk2
      · exact hr2'
    have hrk4 : rk (commV L₁) = 4 := by
      have : (rk (commV L₁) : ℚ) = 4 := by rw [hrk, hr_eq]; norm_num
      exact_mod_cast this
    obtain ⟨eY⟩ := hY
    have eL₁ : ↥L₁ ≃* DihedralGroup 3 := hs₁.restrictEquiv.trans eY
    have eL₂ : ↥L₂ ≃* DihedralGroup 3 := iso.symm.trans eL₁
    have hstab := stab_le_J_OrbI151c h hr hr2 hI h1 h2 hne hx₂ e₂ horb hJ hfix ⟨⟨eL₁⟩, hrk4⟩
    obtain ⟨-, hgen⟩ := genTop_p3_OrbI151c h hne hx₂ e₂ horb hJ hstab
    exact ⟨hr_eq, ⟨3, Or.inl rfl, key 3 (Or.inl rfl) ⟨eY⟩ hrk4⟩,
      twoNilp_of_noInvol_OrbI151c hne hx₂ e₂ horb (Or.inl rfl) eL₁ eL₂
        (noInvol_p3_OrbI151c hLinf hcomm hne hx₂ e₂ horb hstab eL₁ eL₂),
      hgen, exists_order_two_OrbI151c h hr hr2 hI h1 (Or.inl rfl) eL₁⟩
  · obtain ⟨eY⟩ := hY
    have eL₁ : ↥L₁ ≃* DihedralGroup 5 := hs₁.restrictEquiv.trans eY
    have eL₂ : ↥L₂ ≃* DihedralGroup 5 := iso.symm.trans eL₁
    have hrk₂' : rk (commV L₂) = 4 := by rw [hrk₂]; exact hrk
    exact ⟨hr_eq, ⟨5, Or.inr rfl, key 5 (Or.inr rfl) ⟨eY⟩ hrk⟩,
      twoNilp_of_noInvol_OrbI151c hne hx₂ e₂ horb (Or.inr rfl) eL₁ eL₂
        (noInvol_p5_OrbI151c h hr hr2 hI h1 h2 hne hx₂ e₂ horb hJ hfix eL₁ eL₂ hrk hrk₂'),
      genTop_p5_OrbI151c h hr hr2 hI h1 h2 hne hx₂ e₂ horb hJ hfix (not_S3Block_of_D5_OrbI151c eL₁)
        (not_S3Block_of_D5_OrbI151c eL₂),
      exists_order_two_OrbI151c h hr hr2 hI h1 (Or.inr rfl) eL₁⟩

end OrbI151c

end CFSG.Quasithin
