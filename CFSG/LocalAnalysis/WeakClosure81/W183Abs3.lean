module

public import CFSG.LocalAnalysis.WeakClosure81.W183Abs2
import CFSG.SignalizerFunctorTheorem.Quadratic.Invariance

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem w183_commSpace_le_of_simple {L X : Subgroup (LGL 2 V)} [IsSimpleGroup ↥L]
    (hXL : X ≤ L) (hX : X ≠ ⊥) {P : Submodule (ZMod 2) V}
    (hP : ∀ l ∈ L, ∀ p ∈ P, l p ∈ P) (hcomm : commSpace X ⊤ ≤ P) : commSpace L ⊤ ≤ P := by
  let N : Subgroup ↥L :=
    { carrier := {x | ∀ v : V, (x : LGL 2 V) v - v ∈ P}
      one_mem' := fun v => by
        change (1 : LGL 2 V) v - v ∈ P
        simp
      mul_mem' := fun {a b} ha hb v => by
        change ((a : LGL 2 V) * (b : LGL 2 V)) v - v ∈ P
        rw [LinearEquiv.mul_apply]
        have h1 : (a : LGL 2 V) ((b : LGL 2 V) v) - (a : LGL 2 V) v ∈ P := by
          rw [← map_sub]
          exact hP (a : LGL 2 V) a.2 ((b : LGL 2 V) v - v) (hb v)
        have h2 : (a : LGL 2 V) v - v ∈ P := ha v
        have he : (a : LGL 2 V) ((b : LGL 2 V) v) - v
            = ((a : LGL 2 V) ((b : LGL 2 V) v) - (a : LGL 2 V) v)
              + ((a : LGL 2 V) v - v) := by
          abel
        rw [he]
        exact P.add_mem h1 h2
      inv_mem' := fun {a} ha v => by
        change (a : LGL 2 V)⁻¹ v - v ∈ P
        have h : v - (a : LGL 2 V)⁻¹ v ∈ P := by
          simpa using ha ((a : LGL 2 V)⁻¹ v)
        simpa using P.neg_mem h }
  have hNnormal : N.Normal := ⟨fun n hn g => by
    intro v
    change ((g : LGL 2 V) * (n : LGL 2 V) * (g : LGL 2 V)⁻¹) v - v ∈ P
    have hgw : (g : LGL 2 V) ((g : LGL 2 V)⁻¹ v) = v :=
      LinearEquiv.apply_symm_apply (g : LGL 2 V) v
    have hn' : (n : LGL 2 V) ((g : LGL 2 V)⁻¹ v) - (g : LGL 2 V)⁻¹ v ∈ P :=
      hn ((g : LGL 2 V)⁻¹ v)
    have he : ((g : LGL 2 V) * (n : LGL 2 V) * (g : LGL 2 V)⁻¹) v - v
        = (g : LGL 2 V) ((n : LGL 2 V) ((g : LGL 2 V)⁻¹ v) - (g : LGL 2 V)⁻¹ v) := by
      rw [map_sub]
      simp only [LinearEquiv.mul_apply]
      rw [hgw]
    rw [he]
    exact hP (g : LGL 2 V) g.2 _ hn'⟩
  haveI := hNnormal
  have hXN : X.subgroupOf L ≤ N := fun x hx => by
    rw [Subgroup.mem_subgroupOf] at hx
    intro v
    exact hcomm (sub_mem_commSpace hx (Submodule.mem_top))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · exfalso
    apply hX
    have hsub : X.subgroupOf L = ⊥ := le_bot_iff.mp (hbot ▸ hXN)
    rw [eq_bot_iff]
    intro x hx
    have hxL : x ∈ L := hXL hx
    have hmem : (⟨x, hxL⟩ : ↥L) ∈ X.subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]; exact hx
    rw [hsub, Subgroup.mem_bot] at hmem
    exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hmem)
  · rw [commSpace_le_iff]
    intro l hl v _
    have hlN : (⟨l, hl⟩ : ↥L) ∈ N := by rw [htop]; trivial
    exact hlN v

theorem w183_inf_eq_bot_of_commute {L₁ L₂ : Subgroup (LGL 2 V)} [IsSimpleGroup ↥L₁]
    (hnab : ∃ a ∈ L₁, ∃ b ∈ L₁, a * b ≠ b * a) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) :
    L₁ ⊓ L₂ = ⊥ := by
  let N : Subgroup ↥L₁ := (L₁ ⊓ L₂).subgroupOf L₁
  have hNnormal : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
    refine ⟨?_, ?_⟩
    · exact L₁.mul_mem (L₁.mul_mem g.2 hn.1) (L₁.inv_mem g.2)
    · have hgn : (g : LGL 2 V) * (n : LGL 2 V) = (n : LGL 2 V) * (g : LGL 2 V) :=
        hcomm g g.2 n hn.2
      have he : ((g * n * g⁻¹ : ↥L₁) : LGL 2 V) = (n : LGL 2 V) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hgn]; group
      rw [he]; exact hn.2⟩
  haveI := hNnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxN : (⟨x, hx.1⟩ : ↥L₁) ∈ N := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]; exact hx
    rw [hbot, Subgroup.mem_bot] at hxN
    exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hxN)
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    have haN : (⟨a, ha⟩ : ↥L₁) ∈ N := by rw [htop]; trivial
    have hbN : (⟨b, hb⟩ : ↥L₁) ∈ N := by rw [htop]; trivial
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at haN hbN
    exact hab (hcomm a ha b hbN.2)

private theorem w183_self_mul_eq_one_comm {Q : Type*} [Group Q] {X : Subgroup Q}
    (hel : ∀ x ∈ X, x * x = 1) : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := by
  intro x hx y hy
  have hxy : (x * y) * (x * y) = 1 := hel (x * y) (X.mul_mem hx hy)
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hel x hx)
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hel y hy)
  calc x * y = (x * y)⁻¹ := (inv_eq_of_mul_eq_one_right hxy).symm
    _ = y⁻¹ * x⁻¹ := mul_inv_rev x y
    _ = y * x := by rw [hxinv, hyinv]

theorem w183_exists_klein_basis {Q : Type*} [Group Q] {X : Subgroup Q} (hX : Nat.card ↥X = 4)
    (hel : ∀ x ∈ X, x * x = 1) {n : Q} (hn : ∀ x ∈ X, n * x * n⁻¹ ∈ X)
    (hfpf : ∀ x ∈ X, x ≠ 1 → n * x * n⁻¹ ≠ x) :
    ∃ a b : Q, a ∈ X ∧ b ∈ X ∧ a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b ∧
      (∀ x, x ∈ X ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b) ∧ n * a * n⁻¹ = b ∧
      n * b * n⁻¹ = a * b := by
  classical
  have hcommX : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := w183_self_mul_eq_one_comm hel
  have hXne : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hX
    norm_num at hX
  obtain ⟨⟨a, ha⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hXne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  set b : Q := n * a * n⁻¹ with hbdef
  have hb : b ∈ X := by rw [hbdef]; exact hn a ha
  have hb1 : b ≠ 1 := by
    intro h
    apply ha1'
    have h' : n * a * n⁻¹ = 1 := by rw [← hbdef]; exact h
    calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
      _ = 1 := by rw [h']; group
  have hba : b ≠ a := by
    intro h
    apply hfpf a ha ha1'
    rw [← hbdef]
    exact h
  have hab : a ≠ b := hba.symm
  have hab1_1 : a * b ≠ 1 := by
    intro h
    have hb_eq : b = a := by
      have h1 := eq_inv_of_mul_eq_one_right h
      rwa [inv_eq_of_mul_eq_one_right (hel a ha)] at h1
    exact hab hb_eq.symm
  have hab_a : a ≠ a * b := by
    intro h
    have h1 : a * 1 = a * b := by rw [mul_one]; exact h
    exact hb1 (mul_left_cancel h1).symm
  have hab_b : b ≠ a * b := by
    intro h
    have h1 : 1 * b = a * b := by rw [one_mul]; exact h
    exact ha1' (mul_right_cancel h1).symm
  have h1a : (1 : Q) ≠ a := fun h => ha1' h.symm
  have h1b : (1 : Q) ≠ b := fun h => hb1 h.symm
  have h1ab : (1 : Q) ≠ a * b := fun h => hab1_1 h.symm
  let T : Finset Q := {1, a, b, a * b}
  have hTcard : T.card = 4 := by
    show ({1, a, b, a * b} : Finset Q).card = 4
    rw [Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨h1a, h1b, h1ab⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨hab, hab_a⟩),
        Finset.card_insert_of_notMem (by
          simp only [Finset.mem_singleton]
          exact hab_b),
        Finset.card_singleton]
  have hTsub : (T : Set Q) ⊆ (X : Set Q) := by
    intro x hx
    rw [Finset.mem_coe] at hx
    change x ∈ ({1, a, b, a * b} : Finset Q) at hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact X.one_mem
    · exact ha
    · exact hb
    · exact X.mul_mem ha hb
  haveI hfinX : Finite ↥X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have hXcard : (X : Set Q).ncard = 4 := hX
  have hTX : (T : Set Q) = (X : Set Q) :=
    Set.eq_of_subset_of_ncard_le hTsub (by rw [hXcard, Set.ncard_coe_finset, hTcard])
      (Set.finite_coe_iff.mpr hfinX)
  have hXchar : ∀ x, x ∈ X ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b := by
    intro x
    change x ∈ (X : Set Q) ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b
    rw [← hTX, Finset.mem_coe]
    change x ∈ ({1, a, b, a * b} : Finset Q) ↔ x = 1 ∨ x = a ∨ x = b ∨ x = a * b
    simp only [Finset.mem_insert, Finset.mem_singleton]
  have hnb : n * b * n⁻¹ = a * b := by
    have hmem : n * b * n⁻¹ ∈ X := hn b hb
    have hne1 : n * b * n⁻¹ ≠ 1 := by
      intro h
      apply hb1
      calc b = n⁻¹ * (n * b * n⁻¹) * n := by group
        _ = 1 := by rw [h]; group
    have hneb : n * b * n⁻¹ ≠ b := hfpf b hb hb1
    have hnea : n * b * n⁻¹ ≠ a := by
      intro h
      have hfix : n * (a * b) * n⁻¹ = a * b := by
        have h1 : n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) := by group
        rw [h1, ← hbdef, h, hcommX a ha b hb]
      exact hfpf (a * b) (X.mul_mem ha hb) hab1_1 hfix
    rcases (hXchar (n * b * n⁻¹)).mp hmem with h1 | h2 | h3 | h4
    · exact absurd h1 hne1
    · exact absurd h2 hnea
    · exact absurd h3 hneb
    · exact h4
  exact ⟨a, b, ha, hb, ha1', hb1, hab, hXchar, hbdef.symm, hnb⟩

namespace Assumption131

variable {G : Subgroup (LGL 2 V)} {Γ : Set (Subgroup (LGL 2 V))}
  {VA : Subgroup (LGL 2 V) → Submodule (ZMod 2) V} {i : ℕ}

theorem exists_three_members (h : Assumption131 G Γ VA i)
    {L₁ L₂ X₁ X₂ D₀ : Subgroup (LGL 2 V)} [IsSimpleGroup ↥L₁]
    (hnab₁ : ∃ a ∈ L₁, ∃ b ∈ L₁, a * b ≠ b * a) (hL₁G : L₁ ≤ G)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hX₁ : X₁ ≤ L₁) (hX₂ : X₂ ≤ L₂)
    (hX₁c : Nat.card ↥X₁ = 4) (hX₁sq : ∀ x ∈ X₁, x * x = 1) (φ : ↥X₁ ≃* ↥X₂)
    (hD₀ : D₀ ∈ Γ) (hD₀r : mRank D₀ ≤ i)
    (hD₀eq : ∀ d, d ∈ D₀ ↔ ∃ x : ↥X₁, d = (x : LGL 2 V) * (φ x : LGL 2 V))
    {n : LGL 2 V} (hn : n ∈ L₁) (hnX : ∀ x ∈ X₁, n * x * n⁻¹ ∈ X₁)
    (hfpf : ∀ x ∈ X₁, x ≠ 1 → n * x * n⁻¹ ≠ x) :
    ∃ D : Fin 3 → Subgroup (LGL 2 V), (∀ k, D k ∈ Γ) ∧ (∀ k, mRank (D k) ≤ i) ∧
      (∀ j k, j ≠ k → D j ≠ D k) ∧ (∀ j k, ∀ a ∈ D j, ∀ b ∈ D k, a * b = b * a) ∧
      X₁ ⊔ X₂ ≤ D 0 ⊔ D 1 ⊔ D 2 ∧
      (∀ s ∈ X₁, s ≠ 1 → ∀ u ∈ X₂, u ≠ 1 → ∃ k, s * u ∈ D k) ∧
      (∀ u ∈ X₂, u ≠ 1 → ∀ k, ∃ s ∈ X₁, s ≠ 1 ∧ s * u ∈ D k) := by
  classical
  obtain ⟨a, b, ha, hb, ha1, hb1, hab, hXchar, hna, hnb⟩ :=
    w183_exists_klein_basis hX₁c hX₁sq hnX hfpf
  have hcommX₁ : ∀ x ∈ X₁, ∀ y ∈ X₁, x * y = y * x := w183_self_mul_eq_one_comm hX₁sq
  have hX₁0 : X₁ ≠ ⊥ := by
    intro hb0
    rw [hb0, Subgroup.card_bot] at hX₁c
    norm_num at hX₁c
  have hab_a : a ≠ a * b := by
    intro hh
    have h1 : a * 1 = a * b := by rw [mul_one]; exact hh
    exact hb1 (mul_left_cancel h1).symm
  have hab_b : b ≠ a * b := by
    intro hh
    have h1 : 1 * b = a * b := by rw [one_mul]; exact hh
    exact ha1 (mul_right_cancel h1).symm
  let w : ℕ → LGL 2 V → LGL 2 V := fun k x => n ^ k * x * (n ^ k)⁻¹
  have hw_succ : ∀ k x, w (k + 1) x = n * w k x * n⁻¹ := by
    intro k x; simp only [w, pow_succ]; group
  have hw_mem : ∀ k x, x ∈ X₁ → w k x ∈ X₁ := by
    intro k
    induction k with
    | zero => intro x hx; simpa [w] using hx
    | succ k ih => intro x hx; rw [hw_succ]; exact hnX _ (ih x hx)
  have hnpow_mem : ∀ k : ℕ, n ^ k ∈ L₁ := fun k => L₁.pow_mem hn k
  have hconj_phi : ∀ (k : ℕ) (x : ↥X₁),
      n ^ k * (φ x : LGL 2 V) * (n ^ k)⁻¹ = (φ x : LGL 2 V) := by
    intro k x
    have hh := hcomm (n ^ k) (hnpow_mem k) (φ x : LGL 2 V) (hX₂ (φ x).2)
    rw [hh]; group
  have hconj_phi' : ∀ (k : ℕ) (x : ↥X₁),
      (n ^ k)⁻¹ * (φ x : LGL 2 V) * n ^ k = (φ x : LGL 2 V) := by
    intro k x
    have hh := hconj_phi k x
    calc (n ^ k)⁻¹ * (φ x : LGL 2 V) * n ^ k
        = (n ^ k)⁻¹ * (n ^ k * (φ x : LGL 2 V) * (n ^ k)⁻¹) * n ^ k := by rw [hh]
      _ = (φ x : LGL 2 V) := by group
  have hphi_sq : ∀ x : ↥X₁, (φ x : LGL 2 V) * (φ x : LGL 2 V) = 1 := by
    intro x
    have h : x * x = 1 := Subtype.ext (hX₁sq (x : LGL 2 V) x.2)
    calc (φ x : LGL 2 V) * (φ x : LGL 2 V) = (φ (x * x) : LGL 2 V) := by rw [map_mul]; rfl
      _ = 1 := by rw [h, map_one]; rfl
  have hphi_comm : ∀ x y : ↥X₁,
      (φ x : LGL 2 V) * (φ y : LGL 2 V) = (φ y : LGL 2 V) * (φ x : LGL 2 V) := by
    intro x y
    have hxy : x * y = y * x :=
      Subtype.ext (hcommX₁ (x : LGL 2 V) x.2 (y : LGL 2 V) y.2)
    have h1 : (φ (x * y) : LGL 2 V) = (φ x : LGL 2 V) * (φ y : LGL 2 V) := by
      rw [map_mul]; rfl
    have h2 : (φ (y * x) : LGL 2 V) = (φ y : LGL 2 V) * (φ x : LGL 2 V) := by
      rw [map_mul]; rfl
    rw [← h1, ← h2, hxy]
  have hbb : b * b = 1 := hX₁sq b hb
  have haa : a * a = 1 := hX₁sq a ha
  have habc : a * b = b * a := hcommX₁ a ha b hb
  have hba : b * (a * b) = a := by rw [habc, ← mul_assoc, hbb, one_mul]
  have haba : (a * b) * a = b := by rw [mul_assoc, ← habc, ← mul_assoc, haa, one_mul]
  have hr1ab : n * (a * b) * n⁻¹ = a := by
    rw [show n * (a * b) * n⁻¹ = (n * a * n⁻¹) * (n * b * n⁻¹) by group, hna, hnb, hba]
  have hr2a : n ^ 2 * a * (n ^ 2)⁻¹ = a * b := by
    have e : n ^ 2 * a * (n ^ 2)⁻¹ = n * (n * a * n⁻¹) * n⁻¹ := by
      simp only [pow_two]
      group
    rw [e, hna, hnb]
  have hr2b : n ^ 2 * b * (n ^ 2)⁻¹ = a := by
    have e : n ^ 2 * b * (n ^ 2)⁻¹ = n * (n * b * n⁻¹) * n⁻¹ := by
      simp only [pow_two]
      group
    rw [e, hnb, hr1ab]
  have hr2ab : n ^ 2 * (a * b) * (n ^ 2)⁻¹ = b := by
    have e : n ^ 2 * (a * b) * (n ^ 2)⁻¹ = n * (n * (a * b) * n⁻¹) * n⁻¹ := by
      simp only [pow_two]
      group
    rw [e, hr1ab, hna]
  have hw0 : ∀ x : LGL 2 V, w 0 x = x := by intro x; simp [w]
  have hw1a : w 1 a = b := by
    change n ^ 1 * a * (n ^ 1)⁻¹ = b
    rw [pow_one]; exact hna
  have hw1b : w 1 b = a * b := by
    change n ^ 1 * b * (n ^ 1)⁻¹ = a * b
    rw [pow_one]; exact hnb
  have hw1ab : w 1 (a * b) = a := by
    change n ^ 1 * (a * b) * (n ^ 1)⁻¹ = a
    rw [pow_one]; exact hr1ab
  have hw2a : w 2 a = a * b := by
    change n ^ 2 * a * (n ^ 2)⁻¹ = a * b
    exact hr2a
  have hw2b : w 2 b = a := by
    change n ^ 2 * b * (n ^ 2)⁻¹ = a
    exact hr2b
  have hw2ab : w 2 (a * b) = b := by
    change n ^ 2 * (a * b) * (n ^ 2)⁻¹ = b
    exact hr2ab
  have hne_ba : b ≠ a := hab.symm
  have hne_aba : a * b ≠ a := hab_a.symm
  have hne_abb : a * b ≠ b := hab_b.symm
  have hw_inj : ∀ x ∈ X₁, x ≠ 1 → ∀ j k : Fin 3, j ≠ k → w (j : ℕ) x ≠ w (k : ℕ) x := by
    intro x hx hx1 j k hjk
    rcases (hXchar x).mp hx with hx' | hx' | hx' | hx'
    · exact absurd hx' hx1
    · rw [hx']
      fin_cases j <;> fin_cases k <;>
        simp only [hw0, hw1a, hw2a] <;>
        first
          | exact absurd rfl hjk
          | exact hab
          | exact hab.symm
          | exact hab_a
          | exact hab_a.symm
          | exact hab_b
          | exact hab_b.symm
    · rw [hx']
      fin_cases j <;> fin_cases k <;>
        simp only [hw0, hw1b, hw2b] <;>
        first
          | exact absurd rfl hjk
          | exact hab
          | exact hab.symm
          | exact hab_a
          | exact hab_a.symm
          | exact hab_b
          | exact hab_b.symm
    · rw [hx']
      fin_cases j <;> fin_cases k <;>
        simp only [hw0, hw1ab, hw2ab] <;>
        first
          | exact absurd rfl hjk
          | exact hab
          | exact hab.symm
          | exact hab_a
          | exact hab_a.symm
          | exact hab_b
          | exact hab_b.symm
  have hw_surj : ∀ x ∈ X₁, x ≠ 1 → ∀ s ∈ X₁, s ≠ 1 → ∃ k : Fin 3, w (k : ℕ) x = s := by
    intro x hx hx1 s hs hs1
    rcases (hXchar x).mp hx with hx' | hx' | hx' | hx'
    · exact absurd hx' hx1
    · rw [hx']
      rcases (hXchar s).mp hs with hs' | hs' | hs' | hs'
      · exact absurd hs' hs1
      · exact ⟨0, by rw [hs']; exact hw0 a⟩
      · exact ⟨1, by rw [hs']; exact hw1a⟩
      · exact ⟨2, by rw [hs']; exact hw2a⟩
    · rw [hx']
      rcases (hXchar s).mp hs with hs' | hs' | hs' | hs'
      · exact absurd hs' hs1
      · exact ⟨2, by rw [hs']; exact hw2b⟩
      · exact ⟨0, by rw [hs']; exact hw0 b⟩
      · exact ⟨1, by rw [hs']; exact hw1b⟩
    · rw [hx']
      rcases (hXchar s).mp hs with hs' | hs' | hs' | hs'
      · exact absurd hs' hs1
      · exact ⟨1, by rw [hs']; exact hw1ab⟩
      · exact ⟨2, by rw [hs']; exact hw2ab⟩
      · exact ⟨0, by rw [hs']; exact hw0 (a * b)⟩
  let D : Fin 3 → Subgroup (LGL 2 V) := fun k => cj (n ^ (k : ℕ)) D₀
  have mem_D : ∀ (k : Fin 3) (d : LGL 2 V),
      d ∈ D k ↔ ∃ x : ↥X₁, d = w (k : ℕ) (x : LGL 2 V) * (φ x : LGL 2 V) := by
    intro k d
    constructor
    · intro hd
      have hd0 : (n ^ (k : ℕ))⁻¹ * d * n ^ (k : ℕ) ∈ D₀ :=
        mem_cj.mp (show d ∈ cj (n ^ (k : ℕ)) D₀ from hd)
      obtain ⟨x, hx⟩ := (hD₀eq _).mp hd0
      refine ⟨x, ?_⟩
      have hd' : d = n ^ (k : ℕ) * ((x : LGL 2 V) * (φ x : LGL 2 V)) * (n ^ (k : ℕ))⁻¹ := by
        rw [← hx]; group
      rw [hd']
      change n ^ (k : ℕ) * ((x : LGL 2 V) * (φ x : LGL 2 V)) * (n ^ (k : ℕ))⁻¹
        = n ^ (k : ℕ) * (x : LGL 2 V) * (n ^ (k : ℕ))⁻¹ * (φ x : LGL 2 V)
      rw [show n ^ (k : ℕ) * ((x : LGL 2 V) * (φ x : LGL 2 V)) * (n ^ (k : ℕ))⁻¹
          = (n ^ (k : ℕ) * (x : LGL 2 V) * (n ^ (k : ℕ))⁻¹)
            * (n ^ (k : ℕ) * (φ x : LGL 2 V) * (n ^ (k : ℕ))⁻¹) by group,
        hconj_phi k x]
    · rintro ⟨x, rfl⟩
      show w (k : ℕ) (x : LGL 2 V) * (φ x : LGL 2 V) ∈ cj (n ^ (k : ℕ)) D₀
      rw [mem_cj, hD₀eq]
      refine ⟨x, ?_⟩
      change (n ^ (k : ℕ))⁻¹ * (n ^ (k : ℕ) * (x : LGL 2 V) * (n ^ (k : ℕ))⁻¹
          * (φ x : LGL 2 V)) * n ^ (k : ℕ) = (x : LGL 2 V) * (φ x : LGL 2 V)
      rw [show (n ^ (k : ℕ))⁻¹ * (n ^ (k : ℕ) * (x : LGL 2 V) * (n ^ (k : ℕ))⁻¹
            * (φ x : LGL 2 V)) * n ^ (k : ℕ)
          = (x : LGL 2 V) * ((n ^ (k : ℕ))⁻¹ * (φ x : LGL 2 V) * n ^ (k : ℕ)) by group,
        hconj_phi' k x]
  have hDΓ : ∀ k, D k ∈ Γ := by
    intro k
    exact h.invariant D₀ hD₀ (n ^ (k : ℕ)) (hL₁G (hnpow_mem _))
  have hDr : ∀ k, mRank (D k) ≤ i := by
    intro k
    show mRank (cj (n ^ (k : ℕ)) D₀) ≤ i
    unfold mRank
    rw [card_cj]
    exact hD₀r
  have hDne : ∀ j k, j ≠ k → D j ≠ D k := by
    intro j k hjk hEq
    obtain ⟨⟨x₀, hx₀⟩, hx₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hX₁0
    let x₀' : ↥X₁ := ⟨x₀, hx₀⟩
    have hx₀1' : (x₀' : LGL 2 V) ≠ 1 := fun hh => hx₀1 (Subtype.ext hh)
    have hdj : w (j : ℕ) (x₀' : LGL 2 V) * (φ x₀' : LGL 2 V) ∈ D j :=
      (mem_D j _).mpr ⟨x₀', rfl⟩
    have hdk : w (j : ℕ) (x₀' : LGL 2 V) * (φ x₀' : LGL 2 V) ∈ D k := hEq ▸ hdj
    obtain ⟨y, hy⟩ := (mem_D k _).mp hdk
    have hL₁ : w (j : ℕ) (x₀' : LGL 2 V) ∈ L₁ := hX₁ (hw_mem (j : ℕ) _ x₀'.2)
    have hL₂ : (φ x₀' : LGL 2 V) ∈ L₂ := hX₂ (φ x₀').2
    have hyL₁ : w (k : ℕ) (y : LGL 2 V) ∈ L₁ := hX₁ (hw_mem (k : ℕ) _ y.2)
    have hyL₂ : (φ y : LGL 2 V) ∈ L₂ := hX₂ (φ y).2
    have huy : w (k : ℕ) (y : LGL 2 V)
        = w (j : ℕ) (x₀' : LGL 2 V) * (φ x₀' : LGL 2 V) * (φ y : LGL 2 V)⁻¹ := by
      rw [hy]; group
    have h2 : (w (k : ℕ) (y : LGL 2 V))⁻¹ * w (j : ℕ) (x₀' : LGL 2 V)
        = (φ y : LGL 2 V) * (φ x₀' : LGL 2 V)⁻¹ := by
      rw [huy]; group
    have hmem_bot : (w (k : ℕ) (y : LGL 2 V))⁻¹ * w (j : ℕ) (x₀' : LGL 2 V) ∈ L₁ ⊓ L₂ := by
      rw [Subgroup.mem_inf]
      exact ⟨L₁.mul_mem (L₁.inv_mem hyL₁) hL₁, by rw [h2]; exact L₂.mul_mem hyL₂ (L₂.inv_mem hL₂)⟩
    rw [w183_inf_eq_bot_of_commute hnab₁ hcomm, Subgroup.mem_bot, inv_mul_eq_one] at hmem_bot
    have heq : w (j : ℕ) (x₀' : LGL 2 V) = w (k : ℕ) (y : LGL 2 V) := hmem_bot.symm
    have hphi_eq : (φ x₀' : LGL 2 V) = (φ y : LGL 2 V) := by
      rw [heq] at hy
      exact mul_left_cancel hy
    have hxy : x₀' = y := φ.injective (Subtype.ext hphi_eq)
    have heq' : w (j : ℕ) (x₀' : LGL 2 V) = w (k : ℕ) (x₀' : LGL 2 V) := by
      have h1 : w (k : ℕ) (x₀' : LGL 2 V) = w (k : ℕ) (y : LGL 2 V) := by rw [hxy]
      rw [h1]; exact heq
    exact hw_inj (x₀' : LGL 2 V) x₀'.2 hx₀1' j k hjk heq'
  have hDcomm : ∀ j k, ∀ a ∈ D j, ∀ b ∈ D k, a * b = b * a := by
    intro j k a ha b hb
    obtain ⟨x, rfl⟩ := (mem_D j a).mp ha
    obtain ⟨y, rfl⟩ := (mem_D k b).mp hb
    have hux : w (j : ℕ) (x : LGL 2 V) ∈ X₁ := hw_mem (j : ℕ) _ x.2
    have huy : w (k : ℕ) (y : LGL 2 V) ∈ X₁ := hw_mem (k : ℕ) _ y.2
    have hAC : Commute (w (j : ℕ) (x : LGL 2 V)) (w (k : ℕ) (y : LGL 2 V)) :=
      hcommX₁ _ hux _ huy
    have hAD : Commute (w (j : ℕ) (x : LGL 2 V)) (φ y : LGL 2 V) :=
      hcomm _ (hX₁ hux) _ (hX₂ (φ y).2)
    have hCB : Commute (w (k : ℕ) (y : LGL 2 V)) (φ x : LGL 2 V) :=
      hcomm _ (hX₁ huy) _ (hX₂ (φ x).2)
    have hBD : Commute (φ x : LGL 2 V) (φ y : LGL 2 V) := hphi_comm x y
    exact Commute.mul_left (Commute.mul_right hAC hAD) (Commute.mul_right hCB.symm hBD)
  have hmemD0 : ∀ y : ↥X₁, (y : LGL 2 V) * (φ y : LGL 2 V) ∈ D 0 := by
    intro y
    refine (mem_D 0 _).mpr ⟨y, ?_⟩
    show (y : LGL 2 V) * (φ y : LGL 2 V) = w 0 (y : LGL 2 V) * (φ y : LGL 2 V)
    rw [hw0]
  have hmemD1 : ∀ y : ↥X₁, w 1 (y : LGL 2 V) * (φ y : LGL 2 V) ∈ D 1 :=
    fun y => (mem_D 1 _).mpr ⟨y, rfl⟩
  have hkey : ∀ y : ↥X₁,
      ((y : LGL 2 V) * (φ y : LGL 2 V)) * (w 1 (y : LGL 2 V) * (φ y : LGL 2 V))
        = (y : LGL 2 V) * w 1 (y : LGL 2 V) := by
    intro y
    have hc : w 1 (y : LGL 2 V) * (φ y : LGL 2 V) = (φ y : LGL 2 V) * w 1 (y : LGL 2 V) :=
      hcomm _ (hX₁ (hw_mem 1 _ y.2)) _ (hX₂ (φ y).2)
    have hpsq := hphi_sq y
    calc ((y : LGL 2 V) * (φ y : LGL 2 V)) * (w 1 (y : LGL 2 V) * (φ y : LGL 2 V))
        = (y : LGL 2 V) * ((φ y : LGL 2 V) * w 1 (y : LGL 2 V)) * (φ y : LGL 2 V) := by
          group
      _ = (y : LGL 2 V) * (w 1 (y : LGL 2 V) * (φ y : LGL 2 V)) * (φ y : LGL 2 V) := by
          rw [← hc]
      _ = (y : LGL 2 V) * w 1 (y : LGL 2 V) * ((φ y : LGL 2 V) * (φ y : LGL 2 V)) := by
          group
      _ = (y : LGL 2 V) * w 1 (y : LGL 2 V) := by rw [hpsq, mul_one]
  have hmem_a : a ∈ D 0 ⊔ D 1 ⊔ D 2 := by
    have hprod : ((⟨b, hb⟩ : ↥X₁) : LGL 2 V) * (φ ⟨b, hb⟩ : LGL 2 V)
        * (w 1 (b : LGL 2 V) * (φ ⟨b, hb⟩ : LGL 2 V)) ∈ D 0 ⊔ D 1 :=
      (D 0 ⊔ D 1).mul_mem (Subgroup.mem_sup_left (hmemD0 ⟨b, hb⟩))
        (Subgroup.mem_sup_right (hmemD1 ⟨b, hb⟩))
    have heq : ((⟨b, hb⟩ : ↥X₁) : LGL 2 V) * (φ ⟨b, hb⟩ : LGL 2 V)
        * (w 1 (b : LGL 2 V) * (φ ⟨b, hb⟩ : LGL 2 V)) = a := by
      rw [hkey ⟨b, hb⟩]
      show b * w 1 b = a
      rw [hw1b, hba]
    rw [← heq]
    exact Subgroup.mem_sup_left hprod
  have hmem_b : b ∈ D 0 ⊔ D 1 ⊔ D 2 := by
    have hprod : ((⟨a * b, X₁.mul_mem ha hb⟩ : ↥X₁) : LGL 2 V)
          * (φ ⟨a * b, X₁.mul_mem ha hb⟩ : LGL 2 V)
        * (w 1 (a * b) * (φ ⟨a * b, X₁.mul_mem ha hb⟩ : LGL 2 V)) ∈ D 0 ⊔ D 1 :=
      (D 0 ⊔ D 1).mul_mem (Subgroup.mem_sup_left (hmemD0 ⟨a * b, X₁.mul_mem ha hb⟩))
        (Subgroup.mem_sup_right (hmemD1 ⟨a * b, X₁.mul_mem ha hb⟩))
    have heq : ((⟨a * b, X₁.mul_mem ha hb⟩ : ↥X₁) : LGL 2 V)
          * (φ ⟨a * b, X₁.mul_mem ha hb⟩ : LGL 2 V)
        * (w 1 (a * b) * (φ ⟨a * b, X₁.mul_mem ha hb⟩ : LGL 2 V)) = b := by
      rw [hkey ⟨a * b, X₁.mul_mem ha hb⟩]
      show (a * b) * w 1 (a * b) = b
      rw [hw1ab, haba]
    rw [← heq]
    exact Subgroup.mem_sup_left hprod
  have hmem_ab : a * b ∈ D 0 ⊔ D 1 ⊔ D 2 := by
    have hprod : ((⟨a, ha⟩ : ↥X₁) : LGL 2 V) * (φ ⟨a, ha⟩ : LGL 2 V)
        * (w 1 (a : LGL 2 V) * (φ ⟨a, ha⟩ : LGL 2 V)) ∈ D 0 ⊔ D 1 :=
      (D 0 ⊔ D 1).mul_mem (Subgroup.mem_sup_left (hmemD0 ⟨a, ha⟩))
        (Subgroup.mem_sup_right (hmemD1 ⟨a, ha⟩))
    have heq : ((⟨a, ha⟩ : ↥X₁) : LGL 2 V) * (φ ⟨a, ha⟩ : LGL 2 V)
        * (w 1 (a : LGL 2 V) * (φ ⟨a, ha⟩ : LGL 2 V)) = a * b := by
      rw [hkey ⟨a, ha⟩]
      show a * w 1 a = a * b
      rw [hw1a]
    rw [← heq]
    exact Subgroup.mem_sup_left hprod
  have hX₁_le : X₁ ≤ D 0 ⊔ D 1 ⊔ D 2 := by
    intro y hy
    rcases (hXchar y).mp hy with h1 | h1 | h1 | h1
    · rw [h1]; exact Subgroup.one_mem _
    · rw [h1]; exact hmem_a
    · rw [h1]; exact hmem_b
    · rw [h1]; exact hmem_ab
  have hX₂_le : X₂ ≤ D 0 ⊔ D 1 ⊔ D 2 := by
    intro z hz
    obtain ⟨x, hx⟩ := φ.surjective ⟨z, hz⟩
    have hzx : z = (φ x : LGL 2 V) := congrArg Subtype.val hx.symm
    rw [hzx]
    have hxD : (x : LGL 2 V) ∈ D 0 ⊔ D 1 ⊔ D 2 := hX₁_le x.2
    have hxD0 : (x : LGL 2 V) * (φ x : LGL 2 V) ∈ D 0 ⊔ D 1 ⊔ D 2 :=
      Subgroup.mem_sup_left (Subgroup.mem_sup_left (hmemD0 x))
    have hxinv : (x : LGL 2 V)⁻¹ * ((x : LGL 2 V) * (φ x : LGL 2 V)) = (φ x : LGL 2 V) := by
      group
    rw [← hxinv]
    exact (D 0 ⊔ D 1 ⊔ D 2).mul_mem ((D 0 ⊔ D 1 ⊔ D 2).inv_mem hxD) hxD0
  have hgen : X₁ ⊔ X₂ ≤ D 0 ⊔ D 1 ⊔ D 2 := sup_le hX₁_le hX₂_le
  have hcover : ∀ s ∈ X₁, s ≠ 1 → ∀ u ∈ X₂, u ≠ 1 → ∃ k, s * u ∈ D k := by
    intro s hs hs1 u hu hu1
    obtain ⟨x, hx⟩ := φ.surjective ⟨u, hu⟩
    have hux : u = (φ x : LGL 2 V) := congrArg Subtype.val hx.symm
    rw [hux] at hu1 ⊢
    have hx1 : (x : LGL 2 V) ≠ 1 := by
      intro h1
      apply hu1
      have hx1' : x = 1 := Subtype.ext h1
      rw [hx1', map_one]; rfl
    obtain ⟨k, hk⟩ := hw_surj (x : LGL 2 V) x.2 hx1 s hs hs1
    exact ⟨k, (mem_D k _).mpr ⟨x, by rw [← hk]⟩⟩
  have hcover' : ∀ u ∈ X₂, u ≠ 1 → ∀ k, ∃ s ∈ X₁, s ≠ 1 ∧ s * u ∈ D k := by
    intro u hu hu1 k
    obtain ⟨x, hx⟩ := φ.surjective ⟨u, hu⟩
    have hux : u = (φ x : LGL 2 V) := congrArg Subtype.val hx.symm
    rw [hux] at hu1 ⊢
    have hx1 : (x : LGL 2 V) ≠ 1 := by
      intro h1
      apply hu1
      have hx1' : x = 1 := Subtype.ext h1
      rw [hx1', map_one]; rfl
    have hwne : w (k : ℕ) (x : LGL 2 V) ≠ 1 := by
      intro h1
      apply hx1
      have h2 : (x : LGL 2 V)
          = (n ^ (k : ℕ))⁻¹ * w (k : ℕ) (x : LGL 2 V) * n ^ (k : ℕ) := by
        show (x : LGL 2 V)
          = (n ^ (k : ℕ))⁻¹ * (n ^ (k : ℕ) * (x : LGL 2 V) * (n ^ (k : ℕ))⁻¹) * n ^ (k : ℕ)
        group
      rw [h2, h1]; group
    exact ⟨w (k : ℕ) (x : LGL 2 V), hw_mem (k : ℕ) _ x.2, hwne,
      (mem_D k _).mpr ⟨x, rfl⟩⟩
  exact ⟨D, hDΓ, hDr, hDne, hDcomm, hgen, hcover, hcover'⟩

theorem false_of_three_members (h : Assumption131 G Γ VA i)
    (hVfix : ∀ A ∈ Γ, VA A ≤ fixSub A)
    {L₁ L₂ X₁ X₂ : Subgroup (LGL 2 V)} [IsSimpleGroup ↥L₁] [IsSimpleGroup ↥L₂]
    (hnab₂ : ∃ a ∈ L₂, ∃ b ∈ L₂, a * b ≠ b * a)
    (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hX₁ : X₁ ≤ L₁) (hX₂ : X₂ ≤ L₂)
    (hX₁0 : X₁ ≠ ⊥) (hX₂0 : X₂ ≠ ⊥) (hX₁sq : ∀ x ∈ X₁, x * x = 1)
    (D : Fin 3 → Subgroup (LGL 2 V)) (hDΓ : ∀ k, D k ∈ Γ) (hDr : ∀ k, mRank (D k) ≤ i)
    (hDne : ∀ j k, j ≠ k → D j ≠ D k)
    (hDcomm : ∀ j k, ∀ a ∈ D j, ∀ b ∈ D k, a * b = b * a)
    (hgen : X₁ ⊔ X₂ ≤ D 0 ⊔ D 1 ⊔ D 2)
    (hcover : ∀ s ∈ X₁, s ≠ 1 → ∀ u ∈ X₂, u ≠ 1 → ∃ k, s * u ∈ D k)
    (hcover' : ∀ u ∈ X₂, u ≠ 1 → ∀ k, ∃ s ∈ X₁, s ≠ 1 ∧ s * u ∈ D k) : False := by
  classical
  have hVfix_le : ∀ k, VA (D k) ≤ fixSub (X₁ ⊔ X₂) := by
    intro k v hv
    rw [mem_fixSub]
    intro x hx
    let stab : Subgroup (LGL 2 V) :=
      { carrier := {g | g v = v}
        one_mem' := rfl
        mul_mem' := fun {a b} ha hb => by
          change (a * b) v = v
          rw [LinearEquiv.mul_apply, hb, ha]
        inv_mem' := fun {a} ha => by
          change a⁻¹ v = v
          calc a⁻¹ v = a⁻¹ (a v) := by rw [ha]
            _ = v := a.symm_apply_apply v }
    have hDj : ∀ j, D j ≤ stab := by
      intro j d hd
      by_cases hjk : j = k
      · rw [hjk] at hd
        exact hVfix (D k) (hDΓ k) hv d hd
      · have hbot := h.commSpace_VA_eq_bot_of_commute (hDΓ k) (hDΓ j) (hDr j)
            (hDne k j (Ne.symm hjk)) (hDcomm k j)
        exact (commSpace_eq_bot_iff.mp hbot) d hd v hv
    exact (hgen.trans (sup_le (sup_le (hDj 0) (hDj 1)) (hDj 2))) hx
  have hstep2 : ∀ s ∈ X₁, s ≠ 1 → ∀ u ∈ X₂, u ≠ 1 → ∀ v : V, s (u v - v) = u v - v := by
    intro s hs hs1 u hu hu1 v
    obtain ⟨k, hk⟩ := hcover s hs hs1 u hu hu1
    have hz : (s * u) v - v ∈ VA (D k) :=
      commSub_le_VA_of_mRank_le h (hDΓ k) (hDr k) (sub_mem_commSub (D k) hk v)
    have hzfix : s ((s * u) v - v) = (s * u) v - v :=
      (hVfix_le k hz) s (Subgroup.mem_sup_left hs)
    have h1 : s ((s * u) v - v) = u v - s v := by
      rw [map_sub]
      have hsuv : s ((s * u) v) = u v := by
        rw [LinearEquiv.mul_apply, ← LinearEquiv.mul_apply, hX₁sq s hs]
        rfl
      rw [hsuv]
    have h2 : (s * u) v - v = s (u v) - v := by rw [LinearEquiv.mul_apply]
    have heq : u v - s v = s (u v) - v := by
      rw [← h1, ← h2]
      exact hzfix
    have hsuv2 : s (u v) = u v - s v + v := by
      have hh := congrArg (fun x : V => x + v) heq
      simpa using hh.symm
    rw [map_sub, hsuv2]
    have hL : (u v - s v + v) - s v = u v + v := by
      simp only [sub_eq_add_neg, ZModModule.neg_eq_self]
      rw [show u v + s v + v + s v = u v + v + (s v + s v) by abel,
          ZModModule.add_self (s v), add_zero]
    rw [hL, sub_eq_add_neg, ZModModule.neg_eq_self]
  have hcommX₂_le : commSpace X₂ ⊤ ≤ fixSub X₁ := by
    rw [commSpace_le_iff]
    intro u hu v _
    rw [mem_fixSub]
    intro s hs
    by_cases hu1 : u = 1
    · subst hu1; simp
    by_cases hs1 : s = 1
    · subst hs1; simp
    · exact hstep2 s hs hs1 u hu hu1 v
  have hinv : Invariant L₁ (commSpace X₂ ⊤) := by
    refine invariant_commSpace (K := X₂) (K' := L₁) ?_ (fun _ _ _ _ => trivial)
    intro l hl u hu
    have h := hcomm l hl u (hX₂ hu)
    have e : l * u * l⁻¹ = u := by rw [h]; group
    rw [e]
    exact hu
  have hE₀ : commSpace X₂ ⊤ ≤ fixSub L₁ :=
    w183_fixSub_le_of_simple hX₁ hX₁0 hinv hcommX₂_le
  have hE₀_le_X₂ : fixSub L₁ ≤ fixSub X₂ := by
    intro e he
    rw [mem_fixSub]
    intro u hu
    by_cases hu1 : u = 1
    · subst hu1; simp
    · obtain ⟨s₀, hs₀, _, hs₀u⟩ := hcover' u hu hu1 0
      obtain ⟨s₁, hs₁, _, hs₁u⟩ := hcover' u hu hu1 1
      have hue : u e ∈ fixSub L₁ := by
        rw [mem_fixSub]
        intro l hl
        have h := hcomm l hl u (hX₂ hu)
        calc l (u e) = (l * u) e := (LinearEquiv.mul_apply l u e).symm
          _ = (u * l) e := by rw [h]
          _ = u (l e) := LinearEquiv.mul_apply u l e
          _ = u e := by rw [he l hl]
      have h₀ : u e - e ∈ VA (D 0) := by
        have hmem : (s₀ * u) e - e ∈ VA (D 0) :=
          commSub_le_VA_of_mRank_le h (hDΓ 0) (hDr 0) (sub_mem_commSub (D 0) hs₀u e)
        have he' : (s₀ * u) e - e = u e - e := by
          rw [LinearEquiv.mul_apply, hue s₀ (hX₁ hs₀)]
        rwa [he'] at hmem
      have h₁ : u e - e ∈ VA (D 1) := by
        have hmem : (s₁ * u) e - e ∈ VA (D 1) :=
          commSub_le_VA_of_mRank_le h (hDΓ 1) (hDr 1) (sub_mem_commSub (D 1) hs₁u e)
        have he' : (s₁ * u) e - e = u e - e := by
          rw [LinearEquiv.mul_apply, hue s₁ (hX₁ hs₁)]
        rwa [he'] at hmem
      have hbot : VA (D 0) ⊓ VA (D 1) = ⊥ :=
        h.disjoint (D 0) (hDΓ 0) (D 1) (hDΓ 1) (hDne 0 1 (by decide))
      have hmem : u e - e ∈ VA (D 0) ⊓ VA (D 1) := ⟨h₀, h₁⟩
      rw [hbot, Submodule.mem_bot] at hmem
      exact sub_eq_zero.mp hmem
  have hL₂inv : ∀ l ∈ L₂, ∀ e ∈ fixSub L₁, l e ∈ fixSub L₁ := by
    intro l hl e he
    rw [mem_fixSub] at he ⊢
    intro l₁ hl₁
    have h := hcomm l₁ hl₁ l hl
    calc l₁ (l e) = (l₁ * l) e := (LinearEquiv.mul_apply l₁ l e).symm
      _ = (l * l₁) e := by rw [h]
      _ = l (l₁ e) := LinearEquiv.mul_apply l l₁ e
      _ = l e := by rw [he l₁ hl₁]
  have hE₀_le_L₂ : fixSub L₁ ≤ fixSub L₂ :=
    w183_fixSub_le_of_simple hX₂ hX₂0 hL₂inv hE₀_le_X₂
  have hL₂comm_le : commSpace L₂ ⊤ ≤ fixSub L₁ :=
    w183_commSpace_le_of_simple hX₂ hX₂0 hL₂inv hE₀
  have hmul : ∀ a ∈ L₂, ∀ b ∈ L₂, ∀ v : V, a (b v - v) = b v - v := by
    intro a ha b hb v
    have hmem : b v - v ∈ commSpace L₂ ⊤ := by
      rw [commSpace_top_eq_commSub]
      exact sub_mem_commSub L₂ hb v
    exact (hE₀_le_L₂ (hL₂comm_le hmem)) a ha
  obtain ⟨a, ha, b, hb, hab⟩ := hnab₂
  exact hab (w183_mul_comm_of_comp_eq (N := L₂) hmul a ha b hb)

theorem false_of_diagonal_member (h : Assumption131 G Γ VA i)
    (hVfix : ∀ A ∈ Γ, VA A ≤ fixSub A)
    {L₁ L₂ X₁ X₂ D₀ : Subgroup (LGL 2 V)} [IsSimpleGroup ↥L₁] [IsSimpleGroup ↥L₂]
    (hnab₁ : ∃ a ∈ L₁, ∃ b ∈ L₁, a * b ≠ b * a) (hnab₂ : ∃ a ∈ L₂, ∃ b ∈ L₂, a * b ≠ b * a)
    (hL₁G : L₁ ≤ G) (hcomm : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) (hX₁ : X₁ ≤ L₁)
    (hX₂ : X₂ ≤ L₂) (hX₁c : Nat.card ↥X₁ = 4) (hX₁sq : ∀ x ∈ X₁, x * x = 1) (φ : ↥X₁ ≃* ↥X₂)
    (hD₀ : D₀ ∈ Γ) (hD₀r : mRank D₀ ≤ i)
    (hD₀eq : ∀ d, d ∈ D₀ ↔ ∃ x : ↥X₁, d = (x : LGL 2 V) * (φ x : LGL 2 V))
    {n : LGL 2 V} (hn : n ∈ L₁) (hnX : ∀ x ∈ X₁, n * x * n⁻¹ ∈ X₁)
    (hfpf : ∀ x ∈ X₁, x ≠ 1 → n * x * n⁻¹ ≠ x) : False := by
  obtain ⟨D, hDΓ, hDr, hDne, hDcomm, hgen, hcover, hcover'⟩ :=
    h.exists_three_members hnab₁ hL₁G hcomm hX₁ hX₂ hX₁c hX₁sq φ hD₀ hD₀r hD₀eq hn hnX hfpf
  have hX₁0 : X₁ ≠ ⊥ := by
    rintro rfl
    simp at hX₁c
  have hX₂0 : X₂ ≠ ⊥ := by
    rintro rfl
    have : Nat.card ↥X₁ = Nat.card ↥(⊥ : Subgroup (LGL 2 V)) := Nat.card_congr φ.toEquiv
    rw [hX₁c] at this
    simp at this
  exact h.false_of_three_members hVfix hnab₂ hcomm hX₁ hX₂ hX₁0 hX₂0 hX₁sq D hDΓ hDr hDne
    hDcomm hgen hcover hcover'

end Assumption131

end CFSG.LocalAnalysis.WeakClosure81

end
