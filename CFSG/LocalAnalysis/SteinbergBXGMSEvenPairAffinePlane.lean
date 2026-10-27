module

public import CFSG.LocalAnalysis.SteinbergBXGMSNormalRootDichotomy

public section

namespace CFSG.LocalAnalysis.SteinbergBX

universe u

open Subgroup CFSG CFSG.LocalAnalysis CFSG.LocalAnalysis.SteinbergBV

@[expose] def permTranslates {Ω : Type*} (N : Subgroup (Equiv.Perm Ω)) (F : Set Ω) :
    Set (Set Ω) :=
  {ℓ | ∃ g ∈ N, ℓ = ⇑g '' F}

namespace GMSAffine

section Counting

theorem ncard_mul_eq_ncard_mul {A B : Type*} [Finite A] [Finite B] (S : Set A) (T : Set B)
    (r : A → B → Prop) {m k : ℕ} (hm : ∀ a ∈ S, {b | b ∈ T ∧ r a b}.ncard = m)
    (hk : ∀ b ∈ T, {a | a ∈ S ∧ r a b}.ncard = k) : S.ncard * m = T.ncard * k := by
  classical
  have := Fintype.ofFinite A
  have := Fintype.ofFinite B
  rw [Set.ncard_eq_toFinset_card' S, Set.ncard_eq_toFinset_card' T]
  refine Finset.card_mul_eq_card_mul r (fun a ha => ?_) (fun b hb => ?_)
  · rw [← hm a (Set.mem_toFinset.1 ha), Set.ncard_eq_toFinset_card']
    congr 1
    ext b
    simp [Finset.mem_bipartiteAbove]
  · rw [← hk b (Set.mem_toFinset.1 hb), Set.ncard_eq_toFinset_card']
    congr 1
    ext a
    simp [Finset.mem_bipartiteBelow]

theorem sq_sub_one_eq (s : ℕ) : s ^ 2 - 1 = (s + 1) * (s - 1) := by
  rcases s with _ | s
  · rfl
  · have h : (s + 1) ^ 2 = (s + 1 + 1) * s + 1 := by ring
    rw [h, Nat.add_sub_cancel, Nat.add_sub_cancel]

theorem sq_sub_self_eq (s : ℕ) : s ^ 2 - s = (s - 1) * s := by
  rcases s with _ | s
  · rfl
  · have h : (s + 1) ^ 2 = s * (s + 1) + (s + 1) := by ring
    rw [h, Nat.add_sub_cancel, Nat.add_sub_cancel]

theorem perm_apply_inv {Ω : Type*} (f : Equiv.Perm Ω) (x : Ω) : f (f⁻¹ x) = x :=
  f.apply_symm_apply x

theorem perm_inv_apply {Ω : Type*} (f : Equiv.Perm Ω) (x : Ω) : f⁻¹ (f x) = x :=
  f.symm_apply_apply x

theorem orderOf_conj_eq {G : Type*} [Group G] (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  simpa [MulAut.conj_apply] using
    orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x

end Counting

section Geometry

variable {Ω : Type*} {N : Subgroup (Equiv.Perm Ω)} {τ : Equiv.Perm Ω} {α β : Ω} {s : ℕ}

theorem fixedPoints_conj (g τ : Equiv.Perm Ω) :
    Function.fixedPoints ⇑(g * τ * g⁻¹) = ⇑g '' Function.fixedPoints ⇑τ := by
  ext x
  constructor
  · intro hx
    refine ⟨g⁻¹ x, ?_, perm_apply_inv g x⟩
    have h1 : g (τ (g⁻¹ x)) = x := hx
    have h2 := congrArg (⇑g⁻¹) h1
    rwa [perm_inv_apply] at h2
  · rintro ⟨y, hy, rfl⟩
    have hy' : τ y = y := hy
    show g (τ (g⁻¹ (g y))) = g y
    rw [perm_inv_apply, hy']

theorem image_mem_permTranslates {F : Set Ω} {g : Equiv.Perm Ω} (hg : g ∈ N) {ℓ : Set Ω}
    (hℓ : ℓ ∈ permTranslates N F) : ⇑g '' ℓ ∈ permTranslates N F := by
  obtain ⟨g', hg', rfl⟩ := hℓ
  exact ⟨g * g', mul_mem hg hg', by rw [Set.image_image]; rfl⟩

@[expose] def nonregInvolutions (N : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω) :=
  {v | v ∈ N ∧ orderOf v = 2 ∧ ∃ x, v x = x}

@[expose] def regInvolutions (N : Subgroup (Equiv.Perm Ω)) : Set (Equiv.Perm Ω) :=
  {v | v ∈ N ∧ orderOf v = 2 ∧ ∀ x, v x ≠ x}

theorem apply_apply_of_orderOf_eq_two {v : Equiv.Perm Ω} (hv2 : orderOf v = 2) (x : Ω) :
    v (v x) = x := by
  rw [← Equiv.Perm.mul_apply, ← pow_two, ← hv2, pow_orderOf_eq_one, Equiv.Perm.one_apply]

theorem mul_self_of_orderOf_eq_two {G : Type*} [Group G] {v : G} (hv2 : orderOf v = 2) :
    v * v = 1 := by
  rw [← pow_two, ← hv2, pow_orderOf_eq_one]

theorem conj_mem_nonregInvolutions {v h : Equiv.Perm Ω} (hv : v ∈ nonregInvolutions N)
    (hh : h ∈ N) : h * v * h⁻¹ ∈ nonregInvolutions N := by
  obtain ⟨hvN, hv2, x, hx⟩ := hv
  refine ⟨mul_mem (mul_mem hh hvN) (inv_mem hh), by rw [orderOf_conj_eq, hv2], h x, ?_⟩
  show h (v (h⁻¹ (h x))) = h x
  rw [perm_inv_apply, hx]

theorem conj_mem_regInvolutions {v h : Equiv.Perm Ω} (hv : v ∈ regInvolutions N) (hh : h ∈ N) :
    h * v * h⁻¹ ∈ regInvolutions N := by
  obtain ⟨hvN, hv2, hfree⟩ := hv
  refine ⟨mul_mem (mul_mem hh hvN) (inv_mem hh), by rw [orderOf_conj_eq, hv2], fun x hx => ?_⟩
  apply hfree (h⁻¹ x)
  have h1 : h (v (h⁻¹ x)) = x := hx
  have h2 := congrArg (⇑h⁻¹) h1
  rwa [perm_inv_apply] at h2

theorem inv_apply_eq_of_apply_eq {h : Equiv.Perm Ω} {x : Ω} (hx : h x = x) : h⁻¹ x = x := by
  rw [Equiv.Perm.inv_eq_iff_eq, hx]

theorem mul_succ_sub_succ (s : ℕ) : s * (s + 1) - (s + 1) = s ^ 2 - 1 := by
  rcases s with _ | s
  · rfl
  · have h1 : (s + 1) * (s + 1 + 1) = s * (s + 1 + 1) + (s + 1 + 1) := by ring
    have h2 : (s + 1) ^ 2 = s * (s + 1 + 1) + 1 := by ring
    rw [h1, h2, Nat.add_sub_cancel, Nat.add_sub_cancel]

theorem mem_permTranslates_self (N : Subgroup (Equiv.Perm Ω)) (F : Set Ω) :
    F ∈ permTranslates N F :=
  ⟨1, one_mem N, by rw [Equiv.Perm.coe_one, Set.image_id]⟩

theorem exists_mul_of_singer (hne : α ≠ β)
    {T : Subgroup (Equiv.Perm Ω)} (hTN : T ≤ N) (hTα : ∀ t ∈ T, t α = α)
    (hTtrans : ∀ x y, x ≠ α → y ≠ α → ∃ t ∈ T, t x = y) {h : Equiv.Perm Ω} (hh : h ∈ N)
    (hhα : h α = α) : ∃ t ∈ T, ∃ b, (b ∈ N ∧ b α = α ∧ b β = β) ∧ h = t * b := by
  have hβα : β ≠ α := Ne.symm hne
  have hhβ : h β ≠ α := fun h1 => hβα (h.injective (h1.trans hhα.symm))
  obtain ⟨t, ht, htβ⟩ := hTtrans β (h β) hβα hhβ
  refine ⟨t, ht, t⁻¹ * h, ⟨mul_mem (inv_mem (hTN ht)) hh, ?_, ?_⟩, by group⟩
  · show t⁻¹ (h α) = α
    rw [hhα, inv_apply_eq_of_apply_eq (hTα t ht)]
  · show t⁻¹ (h β) = β
    rw [← htβ, perm_inv_apply]

structure InvolutionGeometry (N : Subgroup (Equiv.Perm Ω)) (τ : Equiv.Perm Ω) (α β : Ω)
    (s : ℕ) : Prop where
  two_trans : ∀ x y x' y' : Ω, x ≠ y → x' ≠ y' → ∃ g ∈ N, g x = x' ∧ g y = y'
  ne : α ≠ β
  mem : τ ∈ N
  fix_left : τ α = α
  fix_right : τ β = β
  orderOf_eq : orderOf τ = 2
  unique : ∀ b ∈ N, b α = α → b β = β → orderOf b = 2 → b = τ
  card_fix : (Function.fixedPoints ⇑τ).ncard = s
  card : Nat.card Ω = s ^ 2
  two_le : 2 ≤ s
  even : Even s

namespace InvolutionGeometry

theorem conj_mem (hG : InvolutionGeometry N τ α β s) {g : Equiv.Perm Ω} (hg : g ∈ N) :
    g * τ * g⁻¹ ∈ N :=
  mul_mem (mul_mem hg hG.mem) (inv_mem hg)

theorem orderOf_conj (hG : InvolutionGeometry N τ α β s) (g : Equiv.Perm Ω) :
    orderOf (g * τ * g⁻¹) = 2 := by
  rw [orderOf_conj_eq, hG.orderOf_eq]

theorem tau_sq (hG : InvolutionGeometry N τ α β s) : τ * τ = 1 := by
  rw [← pow_two, ← hG.orderOf_eq, pow_orderOf_eq_one]

theorem tau_apply_apply (hG : InvolutionGeometry N τ α β s) (x : Ω) : τ (τ x) = x := by
  rw [← Equiv.Perm.mul_apply, hG.tau_sq, Equiv.Perm.one_apply]

theorem tau_ne_one (hG : InvolutionGeometry N τ α β s) : τ ≠ 1 := by
  intro h
  have := hG.orderOf_eq
  rw [h, orderOf_one] at this
  omega

theorem s_pos (hG : InvolutionGeometry N τ α β s) : 0 < s := by
  have := hG.two_le
  omega

theorem eq_conj_of_fix (hG : InvolutionGeometry N τ α β s) {v g : Equiv.Perm Ω} (hv : v ∈ N)
    (hv2 : orderOf v = 2) (hg : g ∈ N) {x y : Ω} (hgx : g α = x) (hgy : g β = y)
    (hvx : v x = x) (hvy : v y = y) : v = g * τ * g⁻¹ := by
  have h1 : g⁻¹ * v * g = τ := by
    apply hG.unique _ (mul_mem (mul_mem (inv_mem hg) hv) hg)
    · show g⁻¹ (v (g α)) = α
      rw [hgx, hvx, ← hgx, perm_inv_apply]
    · show g⁻¹ (v (g β)) = β
      rw [hgy, hvy, ← hgy, perm_inv_apply]
    · have := orderOf_conj_eq g⁻¹ v
      rwa [inv_inv, hv2] at this
  rw [← h1]
  group

theorem exists_conj_of_fix (hG : InvolutionGeometry N τ α β s) {v : Equiv.Perm Ω} (hv : v ∈ N)
    (hv2 : orderOf v = 2) {x y : Ω} (hxy : x ≠ y) (hvx : v x = x) (hvy : v y = y) :
    ∃ g ∈ N, g α = x ∧ g β = y ∧ v = g * τ * g⁻¹ := by
  obtain ⟨g, hg, hgx, hgy⟩ := hG.two_trans α β x y hG.ne hxy
  exact ⟨g, hg, hgx, hgy, hG.eq_conj_of_fix hv hv2 hg hgx hgy hvx hvy⟩

theorem eq_of_fix (hG : InvolutionGeometry N τ α β s) {v w : Equiv.Perm Ω} (hv : v ∈ N)
    (hw : w ∈ N) (hv2 : orderOf v = 2) (hw2 : orderOf w = 2) {x y : Ω} (hxy : x ≠ y)
    (hvx : v x = x) (hvy : v y = y) (hwx : w x = x) (hwy : w y = y) : v = w := by
  obtain ⟨g, hg, hgx, hgy, rfl⟩ := hG.exists_conj_of_fix hv hv2 hxy hvx hvy
  exact (hG.eq_conj_of_fix hw hw2 hg hgx hgy hwx hwy).symm

theorem line_eq (hG : InvolutionGeometry N τ α β s) {g g' : Equiv.Perm Ω} (hg : g ∈ N)
    (hg' : g' ∈ N) {x y : Ω} (hxy : x ≠ y) (hx : x ∈ ⇑g '' Function.fixedPoints ⇑τ)
    (hy : y ∈ ⇑g '' Function.fixedPoints ⇑τ) (hx' : x ∈ ⇑g' '' Function.fixedPoints ⇑τ)
    (hy' : y ∈ ⇑g' '' Function.fixedPoints ⇑τ) :
    ⇑g '' Function.fixedPoints ⇑τ = ⇑g' '' Function.fixedPoints ⇑τ := by
  rw [← fixedPoints_conj] at hx hy hx' hy'
  rw [← fixedPoints_conj, ← fixedPoints_conj, hG.eq_of_fix (hG.conj_mem hg) (hG.conj_mem hg')
    (hG.orderOf_conj g) (hG.orderOf_conj g') hxy hx hy hx' hy']

theorem exists_line (hG : InvolutionGeometry N τ α β s) {x y : Ω} (hxy : x ≠ y) :
    ∃ g ∈ N, x ∈ ⇑g '' Function.fixedPoints ⇑τ ∧ y ∈ ⇑g '' Function.fixedPoints ⇑τ := by
  obtain ⟨g, hg, hgx, hgy⟩ := hG.two_trans α β x y hG.ne hxy
  exact ⟨g, hg, ⟨α, hG.fix_left, hgx⟩, ⟨β, hG.fix_right, hgy⟩⟩

theorem existsUnique_line (hG : InvolutionGeometry N τ α β s) {x y : Ω} (hxy : x ≠ y) :
    ∃! ℓ, ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ) ∧ x ∈ ℓ ∧ y ∈ ℓ := by
  obtain ⟨g, hg, hx, hy⟩ := hG.exists_line hxy
  refine ⟨⇑g '' Function.fixedPoints ⇑τ, ⟨⟨g, hg, rfl⟩, hx, hy⟩, ?_⟩
  rintro _ ⟨⟨g', hg', rfl⟩, hx', hy'⟩
  exact hG.line_eq hg' hg hxy hx' hy' hx hy

theorem ncard_line (hG : InvolutionGeometry N τ α β s) {ℓ : Set Ω}
    (hℓ : ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ)) : ℓ.ncard = s := by
  obtain ⟨g, -, rfl⟩ := hℓ
  rw [Set.ncard_image_of_injective _ g.injective, hG.card_fix]

theorem ncard_lines_through [Finite Ω] (hG : InvolutionGeometry N τ α β s) (x : Ω) :
    {ℓ | ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ) ∧ x ∈ ℓ}.ncard = s + 1 := by
  have h := ncard_mul_eq_ncard_mul {y | y ≠ x}
    {ℓ | ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ) ∧ x ∈ ℓ} (fun y ℓ => y ∈ ℓ)
    (m := 1) (k := s - 1) ?_ ?_
  · have hS : {y : Ω | y ≠ x}.ncard = s ^ 2 - 1 := by
      rw [show {y : Ω | y ≠ x} = Set.univ \ {x} by ext; simp,
        Set.ncard_sdiff_singleton_of_mem (Set.mem_univ x), Set.ncard_univ, hG.card]
    rw [hS, mul_one, sq_sub_one_eq] at h
    have := hG.two_le
    exact (Nat.eq_of_mul_eq_mul_right (by omega) h).symm
  · intro y hy
    obtain ⟨ℓ, hℓ, huniq⟩ := hG.existsUnique_line (Ne.symm hy)
    rw [Set.ncard_eq_one]
    refine ⟨ℓ, ?_⟩
    ext m
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hm, hxm⟩, hym⟩
      exact huniq m ⟨hm, hxm, hym⟩
    · rintro rfl
      exact ⟨⟨hℓ.1, hℓ.2.1⟩, hℓ.2.2⟩
  · rintro ℓ ⟨hℓ, hxℓ⟩
    rw [show {y | y ∈ {y : Ω | y ≠ x} ∧ y ∈ ℓ} = ℓ \ {x} by ext; simp [and_comm],
      Set.ncard_sdiff_singleton_of_mem hxℓ, hG.ncard_line hℓ]

theorem ncard_lines [Finite Ω] (hG : InvolutionGeometry N τ α β s) :
    (permTranslates N (Function.fixedPoints ⇑τ)).ncard = s * (s + 1) := by
  have h := ncard_mul_eq_ncard_mul Set.univ (permTranslates N (Function.fixedPoints ⇑τ))
    (fun x ℓ => x ∈ ℓ) (m := s + 1) (k := s) (fun x _ => hG.ncard_lines_through x) ?_
  · rw [Set.ncard_univ, hG.card] at h
    apply Nat.eq_of_mul_eq_mul_right hG.s_pos
    rw [← h]
    ring
  · intro ℓ hℓ
    simp only [Set.mem_univ, true_and, Set.ofPred_mem_eq]
    exact hG.ncard_line hℓ

theorem existsUnique_parallel [Finite Ω] (hG : InvolutionGeometry N τ α β s) {ℓ : Set Ω}
    (hℓ : ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ)) {x : Ω} (hx : x ∉ ℓ) :
    ∃! m, m ∈ permTranslates N (Function.fixedPoints ⇑τ) ∧ x ∈ m ∧ Disjoint m ℓ := by
  set Tx := {m | m ∈ permTranslates N (Function.fixedPoints ⇑τ) ∧ x ∈ m} with hTx
  set Meet := {m | m ∈ Tx ∧ ¬ Disjoint m ℓ} with hMeet
  set Par := {m | m ∈ Tx ∧ Disjoint m ℓ} with hPar
  have hMeetcard : Meet.ncard = s := by
    have h := ncard_mul_eq_ncard_mul ℓ Meet (fun y m => y ∈ m) (m := 1) (k := 1) ?_ ?_
    · rw [mul_one, mul_one, hG.ncard_line hℓ] at h
      exact h.symm
    · intro y hy
      have hxy : x ≠ y := fun h => hx (h ▸ hy)
      obtain ⟨m, hm, huniq⟩ := hG.existsUnique_line hxy
      rw [Set.ncard_eq_one]
      refine ⟨m, ?_⟩
      ext m'
      simp only [hMeet, hTx, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨⟨⟨hm', hxm'⟩, -⟩, hym'⟩
        exact huniq m' ⟨hm', hxm', hym'⟩
      · rintro rfl
        exact ⟨⟨⟨hm.1, hm.2.1⟩, Set.not_disjoint_iff.2 ⟨y, hm.2.2, hy⟩⟩, hm.2.2⟩
    · rintro m ⟨⟨hm, hxm⟩, hmeet⟩
      obtain ⟨y, hym, hyℓ⟩ := Set.not_disjoint_iff.1 hmeet
      rw [Set.ncard_eq_one]
      refine ⟨y, ?_⟩
      ext y'
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hy'ℓ, hy'm⟩
        by_contra hne
        have h1 := (hG.existsUnique_line hne).unique ⟨hm, hy'm, hym⟩ ⟨hℓ, hy'ℓ, hyℓ⟩
        exact hx (h1 ▸ hxm)
      · rintro rfl
        exact ⟨hyℓ, hym⟩
  have hsplit : Tx = Meet ∪ Par := by
    ext m
    simp only [hMeet, hPar, Set.mem_union, Set.mem_ofPred_eq]
    tauto
  have hdisj : Disjoint Meet Par := by
    rw [Set.disjoint_left]
    rintro m ⟨-, h1⟩ ⟨-, h2⟩
    exact h1 h2
  have hParcard : Par.ncard = 1 := by
    have h1 := hG.ncard_lines_through x
    rw [← hTx, hsplit, Set.ncard_union_eq hdisj, hMeetcard] at h1
    omega
  obtain ⟨m, hm⟩ := Set.ncard_eq_one.1 hParcard
  have hmPar : m ∈ Par := by
    rw [hm]
    exact Set.mem_singleton m
  refine ⟨m, ⟨hmPar.1.1, hmPar.1.2, hmPar.2⟩, ?_⟩
  rintro m' ⟨hm', hxm', hd⟩
  have : m' ∈ Par := ⟨⟨hm', hxm'⟩, hd⟩
  rw [hm] at this
  exact this

theorem image_fix_eq_iff (hG : InvolutionGeometry N τ α β s) {g : Equiv.Perm Ω} (hg : g ∈ N) :
    ⇑g '' Function.fixedPoints ⇑τ = Function.fixedPoints ⇑τ ↔ g * τ = τ * g := by
  constructor
  · intro h
    have h1 : g * τ * g⁻¹ = τ := by
      have hF : Function.fixedPoints ⇑(g * τ * g⁻¹) = Function.fixedPoints ⇑τ := by
        rw [fixedPoints_conj, h]
      apply hG.unique _ (hG.conj_mem hg)
      · have : α ∈ Function.fixedPoints ⇑(g * τ * g⁻¹) := by
          rw [hF]
          exact hG.fix_left
        exact this
      · have : β ∈ Function.fixedPoints ⇑(g * τ * g⁻¹) := by
          rw [hF]
          exact hG.fix_right
        exact this
      · exact hG.orderOf_conj g
    calc g * τ = g * τ * g⁻¹ * g := by group
      _ = τ * g := by rw [h1]
  · intro h
    rw [← fixedPoints_conj, show g * τ * g⁻¹ = τ by rw [h]; group]

theorem conj_eq_conj_iff (hG : InvolutionGeometry N τ α β s) {g g' : Equiv.Perm Ω} (hg : g ∈ N)
    (hg' : g' ∈ N) : g * τ * g⁻¹ = g' * τ * g'⁻¹ ↔
      ⇑g '' Function.fixedPoints ⇑τ = ⇑g' '' Function.fixedPoints ⇑τ := by
  constructor
  · intro h
    rw [← fixedPoints_conj, ← fixedPoints_conj, h]
  · intro h
    have h1 : ⇑(g'⁻¹ * g) '' Function.fixedPoints ⇑τ = Function.fixedPoints ⇑τ := by
      rw [Equiv.Perm.coe_mul, Set.image_comp, h, ← Set.image_comp, ← Equiv.Perm.coe_mul,
        inv_mul_cancel, Equiv.Perm.coe_one, Set.image_id]
    have h2 := (hG.image_fix_eq_iff (mul_mem (inv_mem hg') hg)).1 h1
    calc g * τ * g⁻¹ = g' * ((g'⁻¹ * g) * τ) * g⁻¹ := by group
      _ = g' * (τ * (g'⁻¹ * g)) * g⁻¹ := by rw [h2]
      _ = g' * τ * g'⁻¹ := by group

theorem exists_ne_fixed [Finite Ω] (hG : InvolutionGeometry N τ α β s) {v : Equiv.Perm Ω}
    (hv2 : orderOf v = 2) {x : Ω} (hx : v x = x) : ∃ y, y ≠ x ∧ v y = y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv2, pow_one])
  have hmod := hp.card_modEq_card_fixedPoints Ω
  have hfix : MulAction.fixedPoints (zpowers v) Ω = Function.fixedPoints ⇑v := by
    ext y
    constructor
    · intro hy
      exact hy ⟨v, mem_zpowers v⟩
    · intro hy
      rintro ⟨_, k, rfl⟩
      exact Function.IsFixedPt.perm_zpow hy k
  rw [hfix, hG.card] at hmod
  have heven : 2 ∣ Nat.card (Function.fixedPoints ⇑v) := by
    have h1 : 2 ∣ s ^ 2 := dvd_pow (even_iff_two_dvd.1 hG.even) two_ne_zero
    exact (Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 h1)))
  rw [Nat.card_coe_set_eq] at heven
  have hpos : 0 < (Function.fixedPoints ⇑v).ncard :=
    (Set.ncard_pos (Set.toFinite _)).2 ⟨x, hx⟩
  obtain ⟨y, hy, hyx⟩ := Set.exists_ne_of_one_lt_ncard (s := Function.fixedPoints ⇑v)
    (by obtain ⟨k, hk⟩ := heven; omega) x
  exact ⟨y, hyx, hy⟩

theorem nonreg_iff [Finite Ω] (hG : InvolutionGeometry N τ α β s) {v : Equiv.Perm Ω} :
    (v ∈ N ∧ orderOf v = 2 ∧ ∃ x, v x = x) ↔ ∃ g ∈ N, v = g * τ * g⁻¹ := by
  constructor
  · rintro ⟨hv, hv2, x, hx⟩
    obtain ⟨y, hyx, hy⟩ := hG.exists_ne_fixed hv2 hx
    obtain ⟨g, hg, -, -, rfl⟩ := hG.exists_conj_of_fix hv hv2 (Ne.symm hyx) hx hy
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    refine ⟨hG.conj_mem hg, hG.orderOf_conj g, g α, ?_⟩
    show g (τ (g⁻¹ (g α))) = g α
    rw [perm_inv_apply, hG.fix_left]

theorem bijOn_fixedPoints [Finite Ω] (hG : InvolutionGeometry N τ α β s) :
    Set.BijOn (fun v : Equiv.Perm Ω => Function.fixedPoints ⇑v)
      {v | v ∈ N ∧ orderOf v = 2 ∧ ∃ x, v x = x} (permTranslates N (Function.fixedPoints ⇑τ)) := by
  refine ⟨fun v hv => ?_, fun v hv w hw hvw => ?_, fun ℓ hℓ => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := hG.nonreg_iff.1 hv
    exact ⟨g, hg, fixedPoints_conj g τ⟩
  · obtain ⟨g, hg, rfl⟩ := hG.nonreg_iff.1 hv
    obtain ⟨g', hg', rfl⟩ := hG.nonreg_iff.1 hw
    have hvw' : Function.fixedPoints ⇑(g * τ * g⁻¹) = Function.fixedPoints ⇑(g' * τ * g'⁻¹) :=
      hvw
    rw [fixedPoints_conj, fixedPoints_conj] at hvw'
    exact (hG.conj_eq_conj_iff hg hg').2 hvw'
  · obtain ⟨g, hg, rfl⟩ := hℓ
    exact ⟨g * τ * g⁻¹, hG.nonreg_iff.2 ⟨g, hg, rfl⟩, fixedPoints_conj g τ⟩

theorem ncard_nonreg [Finite Ω] (hG : InvolutionGeometry N τ α β s) :
    {v | v ∈ N ∧ orderOf v = 2 ∧ ∃ x, v x = x}.ncard = s * (s + 1) := by
  rw [← hG.ncard_lines, ← hG.bijOn_fixedPoints.image_eq, hG.bijOn_fixedPoints.injOn.ncard_image]

theorem nonregInvolutions_eq (hG : InvolutionGeometry N τ α β s) [Finite Ω] :
    nonregInvolutions N = {v | ∃ g ∈ N, v = g * τ * g⁻¹} := by
  ext v
  exact hG.nonreg_iff

theorem ncard_fixedPoints_of_mem (hG : InvolutionGeometry N τ α β s) [Finite Ω]
    {v : Equiv.Perm Ω} (hv : v ∈ nonregInvolutions N) : (Function.fixedPoints ⇑v).ncard = s :=
  hG.ncard_line (hG.bijOn_fixedPoints.mapsTo hv)

theorem ncard_nonreg_apply_eq [Finite Ω] (hG : InvolutionGeometry N τ α β s) {y : Ω}
    (hy : y ≠ α) : {v | v ∈ nonregInvolutions N ∧ v α = y}.ncard = 1 := by
  have hconst : ∀ y', y' ≠ α → {v | v ∈ nonregInvolutions N ∧ v α = y'}.ncard =
      {v | v ∈ nonregInvolutions N ∧ v α = β}.ncard := by
    intro y' hy'
    obtain ⟨h, hh, hhα, hhy⟩ := hG.two_trans α y' α β (Ne.symm hy') hG.ne
    refine Set.ncard_congr (fun v _ => h * v * h⁻¹) ?_ ?_ ?_
    · rintro v ⟨hv, hvα⟩
      refine ⟨conj_mem_nonregInvolutions hv hh, ?_⟩
      show h (v (h⁻¹ α)) = β
      rw [inv_apply_eq_of_apply_eq hhα, hvα, hhy]
    · intro v w _ _ hvw
      exact mul_left_cancel (mul_right_cancel hvw)
    · rintro w ⟨hw, hwα⟩
      refine ⟨h⁻¹ * w * h, ⟨?_, ?_⟩, by group⟩
      · have := conj_mem_nonregInvolutions hw (inv_mem hh)
        rwa [inv_inv] at this
      · show h⁻¹ (w (h α)) = y'
        rw [hhα, hwα, ← hhy, perm_inv_apply]
  set M := {v | v ∈ nonregInvolutions N ∧ v α ≠ α} with hMdef
  have hM : M.ncard = s ^ 2 - 1 := by
    have h1 : (fun v : Equiv.Perm Ω => Function.fixedPoints ⇑v) '' M =
        {ℓ | ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ) ∧ α ∉ ℓ} := by
      ext ℓ
      constructor
      · rintro ⟨v, ⟨hv, hvα⟩, rfl⟩
        exact ⟨hG.bijOn_fixedPoints.mapsTo hv, hvα⟩
      · rintro ⟨hℓ, hαℓ⟩
        obtain ⟨v, hv, rfl⟩ := hG.bijOn_fixedPoints.surjOn hℓ
        exact ⟨v, ⟨hv, hαℓ⟩, rfl⟩
    have h2 : M.ncard =
        {ℓ | ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ) ∧ α ∉ ℓ}.ncard := by
      rw [← h1, (hG.bijOn_fixedPoints.injOn.mono (fun v hv => hv.1)).ncard_image]
    have h3 : {ℓ | ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ) ∧ α ∉ ℓ} =
        permTranslates N (Function.fixedPoints ⇑τ) \
          {ℓ | ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ) ∧ α ∈ ℓ} := by
      ext ℓ
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
      tauto
    rw [h2, h3, Set.ncard_sdiff (fun ℓ hℓ => hℓ.1), hG.ncard_lines, hG.ncard_lines_through,
      mul_succ_sub_succ]
  have hS : {y : Ω | y ≠ α}.ncard = s ^ 2 - 1 := by
    rw [show {y : Ω | y ≠ α} = Set.univ \ {α} by ext; simp,
      Set.ncard_sdiff_singleton_of_mem (Set.mem_univ α), Set.ncard_univ, hG.card]
  have h := ncard_mul_eq_ncard_mul M {y | y ≠ α} (fun v y => v α = y) (m := 1)
    (k := {v | v ∈ nonregInvolutions N ∧ v α = β}.ncard) ?_ ?_
  · rw [hM, hS, mul_one] at h
    rw [hconst y hy]
    have hpos : 0 < s ^ 2 - 1 := by
      have h2 := hG.two_le
      have : 4 ≤ s ^ 2 := by nlinarith
      omega
    exact (Nat.eq_of_mul_eq_mul_left hpos (h.symm.trans (mul_one _).symm))
  · intro v hv
    rw [Set.ncard_eq_one]
    refine ⟨v α, ?_⟩
    ext y'
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun h => h.2.symm, fun h => ⟨h ▸ hv.2, h.symm⟩⟩
  · intro y' hy'
    rw [← hconst y' hy']
    congr 1
    ext v
    simp only [hMdef, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hv, -⟩, hvy⟩
      exact ⟨hv, hvy⟩
    · rintro ⟨hv, hvy⟩
      exact ⟨⟨hv, hvy ▸ hy'⟩, hvy⟩

theorem switching_base [Finite Ω] (hG : InvolutionGeometry N τ α β s) :
    ∃ u, u ∈ nonregInvolutions N ∧ u α = β ∧
      (∀ v ∈ N, orderOf v = 2 → v α = β → v = u ∨ v = u * τ) ∧
      u * τ ∈ regInvolutions N ∧ u * τ ≠ u ∧ (u * τ) α = β := by
  obtain ⟨u, hu⟩ := Set.ncard_eq_one.1 (hG.ncard_nonreg_apply_eq (Ne.symm hG.ne))
  have huI : u ∈ {v | v ∈ nonregInvolutions N ∧ v α = β} := by
    rw [hu]
    exact Set.mem_singleton u
  have hunr : u ∈ nonregInvolutions N := huI.1
  obtain ⟨⟨huN, hu2, -⟩, huα⟩ := huI
  have hu2' := mul_self_of_orderOf_eq_two hu2
  have huβ : u β = α := by
    rw [← huα]
    exact apply_apply_of_orderOf_eq_two hu2 α
  have huniq : ∀ v, v ∈ nonregInvolutions N → v α = β → v = u := fun v hv hvα => by
    have : v ∈ {v | v ∈ nonregInvolutions N ∧ v α = β} := ⟨hv, hvα⟩
    rw [hu] at this
    exact this
  have hcomm : ∀ b ∈ N, b α = α → b β = β → b * u = u * b := by
    intro b hb hbα hbβ
    have h1 : b * u * b⁻¹ = u := huniq _ (conj_mem_nonregInvolutions hunr hb) (by
      show b (u (b⁻¹ α)) = β
      rw [inv_apply_eq_of_apply_eq hbα, huα, hbβ])
    calc b * u = b * u * b⁻¹ * b := by group
      _ = u * b := by rw [h1]
  have hτu := hcomm τ hG.mem hG.fix_left hG.fix_right
  have huτα : (u * τ) α = β := by
    show u (τ α) = β
    rw [hG.fix_left, huα]
  have hne : u * τ ≠ u := by
    intro h1
    apply hG.tau_ne_one
    calc τ = u⁻¹ * (u * τ) := by group
      _ = 1 := by rw [h1, inv_mul_cancel]
  refine ⟨u, hunr, huα, fun v hv hv2 hvα => ?_, ?_, hne, huτα⟩
  · set b := u⁻¹ * v with hb
    have hbN : b ∈ N := mul_mem (inv_mem huN) hv
    have hbα : b α = α := by
      show u⁻¹ (v α) = α
      rw [hvα, Equiv.Perm.inv_eq_iff_eq, huα]
    have hvβ : v β = α := by
      rw [← hvα]
      exact apply_apply_of_orderOf_eq_two hv2 α
    have hbβ : b β = β := by
      show u⁻¹ (v β) = β
      rw [hvβ, Equiv.Perm.inv_eq_iff_eq, huβ]
    have hvub : v = u * b := by
      rw [hb]
      group
    have hb2 : b * b = 1 := by
      have hv2' := mul_self_of_orderOf_eq_two hv2
      have hbu := hcomm b hbN hbα hbβ
      calc b * b = u * u * (b * b) := by rw [hu2', one_mul]
        _ = u * (u * b) * b := by group
        _ = u * (b * u) * b := by rw [hbu]
        _ = (u * b) * (u * b) := by group
        _ = 1 := by rw [← hvub, hv2']
    by_cases hb1 : b = 1
    · left
      rw [hvub, hb1, mul_one]
    · right
      have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hb2) hb1
      rw [hvub, hG.unique b hbN hbα hbβ hbo]
  · have huτ2 : orderOf (u * τ) = 2 := by
      apply orderOf_eq_prime
      · rw [pow_two]
        calc u * τ * (u * τ) = u * (τ * u) * τ := by group
          _ = u * (u * τ) * τ := by rw [hτu]
          _ = (u * u) * (τ * τ) := by group
          _ = 1 := by rw [hu2', hG.tau_sq, mul_one]
      · intro h1
        have h2 := congrArg (fun f : Equiv.Perm Ω => f α) h1
        simp only [Equiv.Perm.one_apply] at h2
        rw [huτα] at h2
        exact hG.ne h2.symm
    refine ⟨mul_mem huN hG.mem, huτ2, fun x hx => ?_⟩
    exact hne (huniq (u * τ) ⟨mul_mem huN hG.mem, huτ2, x, hx⟩ huτα)

theorem switching [Finite Ω] (hG : InvolutionGeometry N τ α β s) {x y : Ω} (hxy : x ≠ y) :
    ∃ v₁ ∈ N, ∃ v₂ ∈ N, orderOf v₁ = 2 ∧ orderOf v₂ = 2 ∧ v₁ x = y ∧ v₁ y = x ∧ v₂ x = y ∧
      v₂ y = x ∧ v₁ ≠ v₂ ∧ v₁ ∈ nonregInvolutions N ∧ (Function.fixedPoints ⇑v₁).ncard = s ∧
      v₂ ∈ regInvolutions N ∧
      ∀ v ∈ N, orderOf v = 2 → v x = y → v y = x → v = v₁ ∨ v = v₂ := by
  obtain ⟨u, hu, huα, huniq, hureg, hne, huτα⟩ := hG.switching_base
  obtain ⟨g, hg, hgx, hgy⟩ := hG.two_trans α β x y hG.ne hxy
  have hgx' : g⁻¹ x = α := by rw [Equiv.Perm.inv_eq_iff_eq, hgx]
  have hgy' : g⁻¹ y = β := by rw [Equiv.Perm.inv_eq_iff_eq, hgy]
  have hu1 := conj_mem_nonregInvolutions hu hg
  have hu2 := conj_mem_regInvolutions hureg hg
  have hswap : ∀ w : Equiv.Perm Ω, orderOf w = 2 → w α = β →
      (g * w * g⁻¹) x = y ∧ (g * w * g⁻¹) y = x := by
    intro w hw2 hwα
    have hwβ : w β = α := by
      rw [← hwα]
      exact apply_apply_of_orderOf_eq_two hw2 α
    constructor
    · show g (w (g⁻¹ x)) = y
      rw [hgx', hwα, hgy]
    · show g (w (g⁻¹ y)) = x
      rw [hgy', hwβ, hgx]
  obtain ⟨h1x, h1y⟩ := hswap u hu.2.1 huα
  obtain ⟨h2x, h2y⟩ := hswap (u * τ) hureg.2.1 huτα
  refine ⟨g * u * g⁻¹, hu1.1, g * (u * τ) * g⁻¹, hu2.1, hu1.2.1, hu2.2.1, h1x, h1y, h2x, h2y,
    fun h => hne (mul_left_cancel (mul_right_cancel h)).symm, hu1,
    hG.ncard_fixedPoints_of_mem hu1, hu2, fun v hv hv2 hvx hvy => ?_⟩
  have hv' : g⁻¹ * v * g ∈ N := mul_mem (mul_mem (inv_mem hg) hv) hg
  have hv2' : orderOf (g⁻¹ * v * g) = 2 := by
    have := orderOf_conj_eq g⁻¹ v
    rwa [inv_inv, hv2] at this
  have hvα : (g⁻¹ * v * g) α = β := by
    show g⁻¹ (v (g α)) = β
    rw [hgx, hvx, hgy']
  rcases huniq _ hv' hv2' hvα with h | h
  · left
    rw [← h]
    group
  · right
    rw [← h]
    group

theorem existsUnique_reg [Finite Ω] (hG : InvolutionGeometry N τ α β s) {y : Ω} (hy : y ≠ α) :
    ∃! w, w ∈ regInvolutions N ∧ w α = y := by
  obtain ⟨v₁, hv₁, v₂, hv₂, -, -, -, -, h2x, -, -, hnr, -, hreg, huniq⟩ :=
    hG.switching (Ne.symm hy)
  refine ⟨v₂, ⟨hreg, h2x⟩, ?_⟩
  rintro w ⟨⟨hwN, hw2, hfree⟩, hwα⟩
  have hwy : w y = α := by
    rw [← hwα]
    exact apply_apply_of_orderOf_eq_two hw2 α
  rcases huniq w hwN hw2 hwα hwy with rfl | rfl
  · obtain ⟨-, -, x, hx⟩ := hnr
    exact absurd hx (hfree x)
  · rfl

theorem ncard_reg [Finite Ω] (hG : InvolutionGeometry N τ α β s) :
    (regInvolutions N).ncard = s ^ 2 - 1 := by
  have hS : {y : Ω | y ≠ α}.ncard = s ^ 2 - 1 := by
    rw [show {y : Ω | y ≠ α} = Set.univ \ {α} by ext; simp,
      Set.ncard_sdiff_singleton_of_mem (Set.mem_univ α), Set.ncard_univ, hG.card]
  rw [← hS]
  refine Set.ncard_congr (fun w _ => w α) (fun w hw => hw.2.2 α) ?_ ?_
  · intro w w' hw hw' hww'
    obtain ⟨w₀, -, huniq⟩ := hG.existsUnique_reg (hw.2.2 α)
    exact (huniq w ⟨hw, rfl⟩).trans (huniq w' ⟨hw', hww'.symm⟩).symm
  · intro y hy
    obtain ⟨w, ⟨hw, hwy⟩, -⟩ := hG.existsUnique_reg hy
    exact ⟨w, hw, hwy⟩

theorem regInvolutions_eq [Finite Ω] (hG : InvolutionGeometry N τ α β s) {w : Equiv.Perm Ω}
    (hw : w ∈ regInvolutions N) : regInvolutions N = {v | ∃ g ∈ N, v = g * w * g⁻¹} := by
  ext v
  constructor
  · intro hv
    obtain ⟨h, hh, hhα, hhy⟩ := hG.two_trans α (w α) α (v α) (Ne.symm (hw.2.2 α))
      (Ne.symm (hv.2.2 α))
    refine ⟨h, hh, ?_⟩
    obtain ⟨v₀, -, huniq⟩ := hG.existsUnique_reg (hv.2.2 α)
    refine (huniq v ⟨hv, rfl⟩).trans (huniq _ ⟨conj_mem_regInvolutions hw hh, ?_⟩).symm
    show h (w (h⁻¹ α)) = v α
    rw [inv_apply_eq_of_apply_eq hhα, hhy]
  · rintro ⟨g, hg, rfl⟩
    exact conj_mem_regInvolutions hw hg

theorem ncard_switching [Finite Ω] (hG : InvolutionGeometry N τ α β s) :
    {v | v ∈ N ∧ orderOf v = 2 ∧ v α = β ∧ v β = α}.ncard = 2 ∧
      {v | v ∈ N ∧ orderOf v = 2 ∧ v α = β ∧ v β = α ∧ ∀ x, v x ≠ x}.ncard = 1 := by
  obtain ⟨v₁, hv₁, v₂, hv₂, h1, h2, h1x, h1y, h2x, h2y, hne, hnr, -, hreg, huniq⟩ :=
    hG.switching hG.ne
  have hset : {v | v ∈ N ∧ orderOf v = 2 ∧ v α = β ∧ v β = α} = {v₁, v₂} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hv, hv2, hvα, hvβ⟩
      exact huniq v hv hv2 hvα hvβ
    · rintro (rfl | rfl)
      · exact ⟨hv₁, h1, h1x, h1y⟩
      · exact ⟨hv₂, h2, h2x, h2y⟩
  have hset0 : {v | v ∈ N ∧ orderOf v = 2 ∧ v α = β ∧ v β = α ∧ ∀ x, v x ≠ x} = {v₂} := by
    ext v
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hv, hv2, hvα, hvβ, hfree⟩
      rcases huniq v hv hv2 hvα hvβ with rfl | rfl
      · obtain ⟨-, -, x, hx⟩ := hnr
        exact absurd hx (hfree x)
      · rfl
    · rintro rfl
      exact ⟨hv₂, h2, h2x, h2y, hreg.2.2⟩
  rw [hset, hset0, Set.ncard_pair hne, Set.ncard_singleton]
  exact ⟨rfl, rfl⟩

theorem exists_comm_of_fix (hG : InvolutionGeometry N τ α β s) {x y : Ω} (hx : τ x = x)
    (hy : τ y = y) (hxy : x ≠ y) : ∃ g ∈ N, g * τ = τ * g ∧ g α = x ∧ g β = y := by
  obtain ⟨g, hg, hgx, hgy⟩ := hG.two_trans α β x y hG.ne hxy
  refine ⟨g, hg, ?_, hgx, hgy⟩
  have h1 : τ = g * τ * g⁻¹ := hG.eq_conj_of_fix hG.mem hG.orderOf_eq hg hgx hgy hx hy
  calc g * τ = g * τ * g⁻¹ * g := by group
    _ = τ * g := by rw [← h1]

theorem two_trans_fix (hG : InvolutionGeometry N τ α β s) {x y x' y' : Ω} (hx : τ x = x)
    (hy : τ y = y) (hx' : τ x' = x') (hy' : τ y' = y') (hxy : x ≠ y) (hxy' : x' ≠ y') :
    ∃ g ∈ N, g * τ = τ * g ∧ g x = x' ∧ g y = y' := by
  obtain ⟨g₁, hg₁, hc₁, h₁x, h₁y⟩ := hG.exists_comm_of_fix hx hy hxy
  obtain ⟨g₂, hg₂, hc₂, h₂x, h₂y⟩ := hG.exists_comm_of_fix hx' hy' hxy'
  refine ⟨g₂ * g₁⁻¹, mul_mem hg₂ (inv_mem hg₁), ?_, ?_, ?_⟩
  · have hc₁' : g₁⁻¹ * τ = τ * g₁⁻¹ := by
      calc g₁⁻¹ * τ = g₁⁻¹ * (τ * g₁) * g₁⁻¹ := by group
        _ = g₁⁻¹ * (g₁ * τ) * g₁⁻¹ := by rw [hc₁]
        _ = τ * g₁⁻¹ := by group
    calc g₂ * g₁⁻¹ * τ = g₂ * (g₁⁻¹ * τ) := by group
      _ = g₂ * (τ * g₁⁻¹) := by rw [hc₁']
      _ = (g₂ * τ) * g₁⁻¹ := by group
      _ = (τ * g₂) * g₁⁻¹ := by rw [hc₂]
      _ = τ * (g₂ * g₁⁻¹) := by group
  · show g₂ (g₁⁻¹ x) = x'
    rw [← h₁x, perm_inv_apply, h₂x]
  · show g₂ (g₁⁻¹ y) = y'
    rw [← h₁y, perm_inv_apply, h₂y]

theorem exists_comm_apply_left (hG : InvolutionGeometry N τ α β s) {x : Ω} (hx : τ x = x) :
    ∃ g ∈ N, g * τ = τ * g ∧ g α = x := by
  by_cases hxα : x = α
  · exact ⟨1, one_mem N, by group, by rw [hxα]; rfl⟩
  · obtain ⟨g, hg, hgc, hgα, -⟩ := hG.exists_comm_of_fix hx hG.fix_left hxα
    exact ⟨g, hg, hgc, hgα⟩

theorem eq_tau_of_comm (hG : InvolutionGeometry N τ α β s)
    (hCH : ∀ w ∈ N, w α = α → w * τ = τ * w → orderOf w = 2 → w = τ) {x : Ω} (hx : τ x = x)
    {w : Equiv.Perm Ω} (hw : w ∈ N) (hwx : w x = x) (hwc : w * τ = τ * w)
    (hw2 : orderOf w = 2) : w = τ := by
  obtain ⟨e, he, hec, heα⟩ := hG.exists_comm_apply_left hx
  have hec' : Commute e τ := hec
  have hwc' : Commute w τ := hwc
  have h1 : e⁻¹ * w * e = τ := by
    apply hCH _ (mul_mem (mul_mem (inv_mem he) hw) he)
    · show e⁻¹ (w (e α)) = α
      rw [heα, hwx, ← heα, perm_inv_apply]
    · exact ((hec'.inv_left.mul_left hwc').mul_left hec').eq
    · have := orderOf_conj_eq e⁻¹ w
      rwa [inv_inv, hw2] at this
  calc w = e * (e⁻¹ * w * e) * e⁻¹ := by group
    _ = e * τ * e⁻¹ := by rw [h1]
    _ = τ * e * e⁻¹ := by rw [hec]
    _ = τ := by group

theorem centralizer_involutions [Finite Ω] (hG : InvolutionGeometry N τ α β s)
    (hCH : ∀ w ∈ N, w α = α → w * τ = τ * w → orderOf w = 2 → w = τ) :
    {v | v ∈ nonregInvolutions N ∧ v * τ = τ * v ∧ v ≠ τ}.ncard = s - 1 ∧
      (∀ v ∈ {v | v ∈ nonregInvolutions N ∧ v * τ = τ * v ∧ v ≠ τ}, ∀ x, τ x = x → v x ≠ x) ∧
      (fun v : Equiv.Perm Ω => Function.fixedPoints ⇑v) ''
          {v | v ∈ nonregInvolutions N ∧ v * τ = τ * v ∧ v ≠ τ} =
        {ℓ | ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ) ∧
          Disjoint ℓ (Function.fixedPoints ⇑τ)} := by
  set S := {v | v ∈ nonregInvolutions N ∧ v * τ = τ * v ∧ v ≠ τ} with hSdef
  have hfree : ∀ v ∈ S, ∀ x, τ x = x → v x ≠ x := by
    rintro v ⟨⟨hvN, hv2, -⟩, hvc, hvτ⟩ x hx hvx
    exact hvτ (hG.eq_tau_of_comm hCH hx hvN hvx hvc hv2)
  have hsub : ∀ v ∈ S, Function.fixedPoints ⇑v ∈ permTranslates N (Function.fixedPoints ⇑τ) ∧
      Disjoint (Function.fixedPoints ⇑v) (Function.fixedPoints ⇑τ) := fun v hv =>
    ⟨hG.bijOn_fixedPoints.mapsTo hv.1,
      Set.disjoint_left.2 fun x hxv hxτ => hfree v hv x hxτ hxv⟩
  have himage : (fun v : Equiv.Perm Ω => Function.fixedPoints ⇑v) '' S =
      {ℓ | ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ) ∧
        Disjoint ℓ (Function.fixedPoints ⇑τ)} := by
    ext ℓ
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hsub v hv
    · rintro ⟨hℓ, hdisj⟩
      have hne : ℓ.Nonempty := by
        rw [← Set.ncard_pos (Set.toFinite ℓ), hG.ncard_line hℓ]
        exact hG.s_pos
      obtain ⟨y, hy⟩ := hne
      have hyF : y ∉ Function.fixedPoints ⇑τ := fun h => Set.disjoint_left.1 hdisj hy h
      have hτy : τ y ≠ y := hyF
      obtain ⟨m, ⟨hm, hym, hτym⟩, huniq⟩ := hG.existsUnique_line (Ne.symm hτy)
      obtain ⟨v, hv, rfl⟩ := hG.bijOn_fixedPoints.surjOn hm
      have hτm : ⇑τ '' Function.fixedPoints ⇑v = Function.fixedPoints ⇑v :=
        huniq _ ⟨image_mem_permTranslates hG.mem hm, ⟨τ y, hτym, hG.tau_apply_apply y⟩,
          ⟨y, hym, rfl⟩⟩
      have hvc : v * τ = τ * v := by
        have h1 : τ * v * τ⁻¹ = v := by
          apply hG.bijOn_fixedPoints.injOn (conj_mem_nonregInvolutions hv hG.mem) hv
          show Function.fixedPoints ⇑(τ * v * τ⁻¹) = Function.fixedPoints ⇑v
          rw [fixedPoints_conj, hτm]
        calc v * τ = τ * v * τ⁻¹ * τ := by rw [h1]
          _ = τ * v := by group
      have hvτ : v ≠ τ := by
        rintro rfl
        exact hyF hym
      have hvS : v ∈ S := ⟨hv, hvc, hvτ⟩
      refine ⟨v, hvS, ?_⟩
      exact (hG.existsUnique_parallel (mem_permTranslates_self N _) hyF).unique
        ⟨(hsub v hvS).1, hym, (hsub v hvS).2⟩ ⟨hℓ, hy, hdisj⟩
  refine ⟨?_, hfree, himage⟩
  rw [← (hG.bijOn_fixedPoints.injOn.mono (fun v hv => hv.1)).ncard_image, himage]
  have hcompl : (Function.fixedPoints ⇑τ)ᶜ.ncard = s ^ 2 - s := by
    rw [Set.ncard_compl, hG.card, hG.card_fix]
  have h := ncard_mul_eq_ncard_mul (Function.fixedPoints ⇑τ)ᶜ
    {ℓ | ℓ ∈ permTranslates N (Function.fixedPoints ⇑τ) ∧ Disjoint ℓ (Function.fixedPoints ⇑τ)}
    (fun y ℓ => y ∈ ℓ) (m := 1) (k := s) ?_ ?_
  · rw [hcompl, mul_one, sq_sub_self_eq] at h
    exact (Nat.eq_of_mul_eq_mul_right hG.s_pos h).symm
  · intro y hy
    obtain ⟨m, hm, huniq⟩ := hG.existsUnique_parallel (mem_permTranslates_self N _) hy
    rw [Set.ncard_eq_one]
    refine ⟨m, ?_⟩
    ext m'
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨hm', hd⟩, hym'⟩
      exact huniq m' ⟨hm', hym', hd⟩
    · rintro rfl
      exact ⟨⟨hm.1, hm.2.2⟩, hm.2.1⟩
  · rintro ℓ ⟨hℓ, hd⟩
    rw [← hG.ncard_line hℓ]
    congr 1
    ext y
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
    exact ⟨fun h => h.2, fun h => ⟨fun h' => Set.disjoint_left.1 hd h h', h⟩⟩

theorem eq_tau_of_singer (hG : InvolutionGeometry N τ α β s) {T : Subgroup (Equiv.Perm Ω)}
    (hTN : T ≤ N) (hTα : ∀ t ∈ T, t α = α)
    (hTn : ∀ t ∈ T, ∀ h ∈ N, h α = α → h * t * h⁻¹ ∈ T)
    (hTtrans : ∀ x y, x ≠ α → y ≠ α → ∃ t ∈ T, t x = y)
    (hTfree : ∀ t ∈ T, ∀ x, x ≠ α → t x = x → t = 1) (hTodd : Odd (Nat.card T)) :
    ∀ w ∈ N, w α = α → w * τ = τ * w → orderOf w = 2 → w = τ := by
  intro w hw hwα hwc hw2
  have hβα : β ≠ α := Ne.symm hG.ne
  obtain ⟨t, ht, b, ⟨hbN, hbα, hbβ⟩, hwtb⟩ := exists_mul_of_singer hG.ne hTN hTα hTtrans hw hwα
  have hw2' := mul_self_of_orderOf_eq_two hw2
  have ht' : b * t * b⁻¹ ∈ T := hTn t ht b hbN hbα
  have hYX : t * (b * t * b⁻¹) * (b * b) = 1 := by
    calc t * (b * t * b⁻¹) * (b * b) = t * b * (t * b) := by group
      _ = 1 := by rw [← hwtb, hw2']
  have hb2T : b * b ∈ T := by
    rw [eq_inv_of_mul_eq_one_right hYX]
    exact inv_mem (mul_mem ht ht')
  have hb2 : b * b = 1 := hTfree _ hb2T β hβα (by
    show b (b β) = β
    rw [hbβ, hbβ])
  have hodd : ∀ g ∈ T, g * g = 1 → g = 1 := by
    intro g hg hg2
    have h1 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hg2)
    have h2 := Subgroup.orderOf_dvd_natCard T hg
    have h3 : orderOf g ∣ Nat.gcd 2 (Nat.card T) := Nat.dvd_gcd h1 h2
    rw [Nat.coprime_two_left.2 hTodd] at h3
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  by_cases hb1 : b = 1
  · exfalso
    rw [hb1, mul_one] at hwtb
    have hw1 : w = 1 := hodd w (hwtb ▸ ht) hw2'
    rw [hw1, orderOf_one] at hw2
    omega
  · have hbo : orderOf b = 2 := orderOf_eq_prime (by rw [pow_two]; exact hb2) hb1
    rw [hG.unique b hbN hbα hbβ hbo] at hwtb
    have ht_eq : t = w * τ := by
      calc t = t * (τ * τ) := by rw [hG.tau_sq, mul_one]
        _ = t * τ * τ := by group
        _ = w * τ := by rw [← hwtb]
    have htc : t * τ = τ * t := by
      rw [ht_eq]
      calc w * τ * τ = w * (τ * τ) := by group
        _ = (τ * τ) * w := by rw [hG.tau_sq, one_mul, mul_one]
        _ = τ * (τ * w) := by group
        _ = τ * (w * τ) := by rw [hwc]
    have ht2 : t * t = 1 := by
      calc t * t = t * t * (τ * τ) := by rw [hG.tau_sq, mul_one]
        _ = t * (t * τ) * τ := by group
        _ = t * (τ * t) * τ := by rw [htc]
        _ = (t * τ) * (t * τ) := by group
        _ = 1 := by rw [← hwtb, hw2']
    rw [hwtb, hodd t ht ht2, one_mul]

end InvolutionGeometry

end Geometry

section Restriction

variable {Ω : Type*} {N : Subgroup (Equiv.Perm Ω)} {τ : Equiv.Perm Ω} {α β : Ω} {s : ℕ}

theorem mem_fixedPoints_apply_iff {e : Equiv.Perm Ω} (he : e * τ = τ * e) (x : Ω) :
    e x ∈ Function.fixedPoints ⇑τ ↔ x ∈ Function.fixedPoints ⇑τ := by
  show τ (e x) = e x ↔ τ x = x
  rw [← Equiv.Perm.mul_apply, ← he, Equiv.Perm.mul_apply]
  exact e.injective.eq_iff

theorem comm_of_mem_centralizer {e : Equiv.Perm Ω} (he : e ∈ N ⊓ centralizer {τ}) :
    e * τ = τ * e :=
  mem_centralizer_singleton_iff.1 (mem_inf.1 he).2

@[expose] def fixRestrict (N : Subgroup (Equiv.Perm Ω)) (τ : Equiv.Perm Ω) :
    ↥(N ⊓ centralizer {τ}) →* Equiv.Perm ↥(Function.fixedPoints ⇑τ) where
  toFun e := (e : Equiv.Perm Ω).subtypePerm fun x =>
    mem_fixedPoints_apply_iff (comm_of_mem_centralizer e.2) x
  map_one' := Equiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := Equiv.ext fun _ => Subtype.ext rfl

namespace InvolutionGeometry

theorem tau_mem_centralizer (hG : InvolutionGeometry N τ α β s) : τ ∈ N ⊓ centralizer {τ} :=
  mem_inf.2 ⟨hG.mem, mem_centralizer_singleton_iff.2 rfl⟩

theorem mem_zpowers_iff (hG : InvolutionGeometry N τ α β s) {g : Equiv.Perm Ω} :
    g ∈ zpowers τ ↔ g = 1 ∨ g = τ := by
  constructor
  · rintro ⟨k, rfl⟩
    show τ ^ k = 1 ∨ τ ^ k = τ
    rw [← zpow_mod_orderOf, hG.orderOf_eq, Nat.cast_ofNat]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [h, zpow_zero]
    · right
      rw [h, zpow_one]
  · rintro (h | h)
    · rw [h]
      exact one_mem _
    · rw [h]
      exact mem_zpowers τ

theorem fixes_fix_iff (hG : InvolutionGeometry N τ α β s)
    (hpt : ∀ g ∈ N, (∀ x, τ x = x → g x = x) → g = 1 ∨ g = τ) {g : Equiv.Perm Ω} (hg : g ∈ N) :
    (∀ x ∈ Function.fixedPoints ⇑τ, g x = x) ↔ g ∈ zpowers τ := by
  rw [hG.mem_zpowers_iff]
  constructor
  · intro h
    exact hpt g hg h
  · rintro (rfl | rfl) x hx
    · rfl
    · exact hx

theorem ker_fixRestrict (hG : InvolutionGeometry N τ α β s)
    (hpt : ∀ g ∈ N, (∀ x, τ x = x → g x = x) → g = 1 ∨ g = τ) :
    (fixRestrict N τ).ker = (zpowers τ).subgroupOf (N ⊓ centralizer {τ}) := by
  ext e
  rw [MonoidHom.mem_ker, mem_subgroupOf, ← hG.fixes_fix_iff hpt (mem_inf.1 e.2).1]
  constructor
  · intro he x hx
    exact congrArg Subtype.val (Equiv.ext_iff.1 he ⟨x, hx⟩)
  · intro he
    exact Equiv.ext fun x => Subtype.ext (he x x.2)

theorem ker_fixRestrict_eq_normalCore (hG : InvolutionGeometry N τ α β s) :
    (fixRestrict N τ).ker = ((N ⊓ MulAction.stabilizer (Equiv.Perm Ω) α).subgroupOf
      (N ⊓ centralizer {τ})).normalCore := by
  ext e
  rw [MonoidHom.mem_ker]
  constructor
  · intro he b
    rw [mem_subgroupOf, mem_inf]
    refine ⟨(b * e * b⁻¹ : ↥(N ⊓ centralizer {τ})).2.1, ?_⟩
    rw [MulAction.mem_stabilizer_iff]
    show (b : Equiv.Perm Ω) ((e : Equiv.Perm Ω) ((b : Equiv.Perm Ω)⁻¹ α)) = α
    have hb : (b : Equiv.Perm Ω)⁻¹ α ∈ Function.fixedPoints ⇑τ :=
      (mem_fixedPoints_apply_iff (comm_of_mem_centralizer (b⁻¹).2) α).2 hG.fix_left
    have h1 := congrArg Subtype.val (Equiv.ext_iff.1 he ⟨_, hb⟩)
    change (e : Equiv.Perm Ω) ((b : Equiv.Perm Ω)⁻¹ α) = (b : Equiv.Perm Ω)⁻¹ α at h1
    rw [h1, perm_apply_inv]
  · intro he
    refine Equiv.ext fun x => Subtype.ext ?_
    obtain ⟨g, hg, hgc, hgα⟩ := hG.exists_comm_apply_left x.2
    have hgE : g ∈ N ⊓ centralizer {τ} := mem_inf.2 ⟨hg, mem_centralizer_singleton_iff.2 hgc⟩
    have h1 := he ⟨g, hgE⟩⁻¹
    rw [mem_subgroupOf, mem_inf, MulAction.mem_stabilizer_iff] at h1
    have h2 : g⁻¹ ((e : Equiv.Perm Ω) (g α)) = α := h1.2
    show (e : Equiv.Perm Ω) x = x
    rw [← hgα]
    calc (e : Equiv.Perm Ω) (g α) = g (g⁻¹ ((e : Equiv.Perm Ω) (g α))) :=
          (perm_apply_inv g _).symm
      _ = g α := by rw [h2]

theorem card_centralizer [Finite Ω] (hG : InvolutionGeometry N τ α β s)
    (hBc : ∀ b ∈ N, b α = α → b β = β → b * τ = τ * b) :
    Nat.card ↥(N ⊓ centralizer {τ}) = s * (s - 1) *
      Nat.card ↥(N ⊓ MulAction.stabilizer (Equiv.Perm Ω) α ⊓
        MulAction.stabilizer (Equiv.Perm Ω) β) := by
  classical
  set E := N ⊓ centralizer {τ} with hE
  set B := N ⊓ MulAction.stabilizer (Equiv.Perm Ω) α ⊓ MulAction.stabilizer (Equiv.Perm Ω) β
    with hB
  have hBE : B ≤ E := fun b hb =>
    mem_inf.2 ⟨hb.1.1, mem_centralizer_singleton_iff.2 (hBc b hb.1.1 hb.1.2 hb.2)⟩
  have horb : MulAction.orbit E (α, β) = (Function.fixedPoints ⇑τ).offDiag := by
    ext ⟨x, y⟩
    rw [Set.mem_offDiag]
    constructor
    · rintro ⟨e, he⟩
      have hx : (e : Equiv.Perm Ω) α = x := congrArg Prod.fst he
      have hy : (e : Equiv.Perm Ω) β = y := congrArg Prod.snd he
      have hc := comm_of_mem_centralizer e.2
      refine ⟨hx ▸ (mem_fixedPoints_apply_iff hc α).2 hG.fix_left,
        hy ▸ (mem_fixedPoints_apply_iff hc β).2 hG.fix_right, fun hxy => hG.ne ?_⟩
      apply (e : Equiv.Perm Ω).injective
      rw [hx, hy]
      exact hxy
    · rintro ⟨hx, hy, hxy⟩
      obtain ⟨g, hg, hgc, hgx, hgy⟩ :=
        hG.two_trans_fix hG.fix_left hG.fix_right hx hy hG.ne hxy
      exact ⟨⟨g, mem_inf.2 ⟨hg, mem_centralizer_singleton_iff.2 hgc⟩⟩, Prod.ext hgx hgy⟩
  have hstab : MulAction.stabilizer E (α, β) = B.subgroupOf E := by
    ext e
    rw [MulAction.mem_stabilizer_iff, mem_subgroupOf]
    constructor
    · intro he
      exact ⟨⟨(mem_inf.1 e.2).1, congrArg Prod.fst he⟩, congrArg Prod.snd he⟩
    · intro he
      exact Prod.ext he.1.2 he.2
  have hoff : Nat.card ↥(Function.fixedPoints ⇑τ).offDiag = s * (s - 1) := by
    have := Fintype.ofFinite Ω
    rw [Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card', Set.toFinset_offDiag,
      Finset.offDiag_card, ← Set.ncard_eq_toFinset_card', hG.card_fix, Nat.mul_sub_one]
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup E (α, β))
  rw [Nat.card_prod, horb, hstab, hoff] at h
  rw [← h, Nat.card_congr (subgroupOfEquivOfLe hBE).toEquiv]

theorem card_ker_fixRestrict (hG : InvolutionGeometry N τ α β s)
    (hpt : ∀ g ∈ N, (∀ x, τ x = x → g x = x) → g = 1 ∨ g = τ) :
    Nat.card (fixRestrict N τ).ker = 2 := by
  rw [hG.ker_fixRestrict hpt,
    Nat.card_congr (subgroupOfEquivOfLe (zpowers_le.2 hG.tau_mem_centralizer)).toEquiv,
    Nat.card_zpowers, hG.orderOf_eq]

theorem card_quotient_fixRestrict [Finite Ω] (hG : InvolutionGeometry N τ α β s)
    (hpt : ∀ g ∈ N, (∀ x, τ x = x → g x = x) → g = 1 ∨ g = τ)
    (hBc : ∀ b ∈ N, b α = α → b β = β → b * τ = τ * b) :
    Nat.card (↥(N ⊓ centralizer {τ}) ⧸ (fixRestrict N τ).ker) * 2 = s * (s - 1) *
      Nat.card ↥(N ⊓ MulAction.stabilizer (Equiv.Perm Ω) α ⊓
        MulAction.stabilizer (Equiv.Perm Ω) β) := by
  rw [← hG.card_ker_fixRestrict hpt, ← Subgroup.card_eq_card_quotient_mul_card_subgroup,
    hG.card_centralizer hBc]

end InvolutionGeometry

theorem comap_kerLift_eq (Q : Subgroup (Equiv.Perm ↥(Function.fixedPoints ⇑τ)))
    (S : Subgroup (Equiv.Perm Ω))
    (hS : ∀ e : ↥(N ⊓ centralizer {τ}), (e : Equiv.Perm Ω) ∈ S ↔ fixRestrict N τ e ∈ Q) :
    Q.comap (QuotientGroup.kerLift (fixRestrict N τ)) =
      (S.subgroupOf (N ⊓ centralizer {τ})).map (QuotientGroup.mk' (fixRestrict N τ).ker) := by
  ext u
  induction u using QuotientGroup.induction_on with
  | H e =>
    rw [mem_comap, QuotientGroup.kerLift_mk, ← hS]
    constructor
    · intro he
      exact ⟨e, mem_subgroupOf.2 he, rfl⟩
    · rintro ⟨e', he', hee'⟩
      rw [SetLike.mem_coe, mem_subgroupOf] at he'
      have h1 : fixRestrict N τ e' = fixRestrict N τ e := by
        have := congrArg (QuotientGroup.kerLift (fixRestrict N τ)) hee'
        rwa [QuotientGroup.mk'_apply, QuotientGroup.kerLift_mk, QuotientGroup.kerLift_mk] at this
      rw [hS] at he' ⊢
      rwa [← h1]

theorem isCyclic_map_mk (S : Subgroup (Equiv.Perm Ω)) (hSE : S ≤ N ⊓ centralizer {τ})
    [IsCyclic S] :
    IsCyclic ↥((S.subgroupOf (N ⊓ centralizer {τ})).map
      (QuotientGroup.mk' (fixRestrict N τ).ker)) := by
  have : IsCyclic ↥(S.subgroupOf (N ⊓ centralizer {τ})) :=
    isCyclic_of_surjective (subgroupOfEquivOfLe hSE).symm.toMonoidHom
      (subgroupOfEquivOfLe hSE).symm.surjective
  exact isCyclic_of_surjective _ (MonoidHom.subgroupMap_surjective _ _)

namespace InvolutionGeometry

theorem card_map_mk_mul_two (hG : InvolutionGeometry N τ α β s)
    (hpt : ∀ g ∈ N, (∀ x, τ x = x → g x = x) → g = 1 ∨ g = τ) (S : Subgroup (Equiv.Perm Ω))
    (hSE : S ≤ N ⊓ centralizer {τ}) (hτS : τ ∈ S) :
    Nat.card ↥((S.subgroupOf (N ⊓ centralizer {τ})).map
      (QuotientGroup.mk' (fixRestrict N τ).ker)) * 2 = Nat.card S := by
  set E := N ⊓ centralizer {τ} with hE
  set K := (fixRestrict N τ).ker with hK
  set S' := S.subgroupOf E with hS'
  let f : S' →* E ⧸ K := (QuotientGroup.mk' K).comp S'.subtype
  have hker : f.ker = K.subgroupOf S' := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    exact QuotientGroup.eq_one_iff _
  have hrange : f.range = S'.map (QuotientGroup.mk' K) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hKS : K ≤ S' := by
    rw [hK, hG.ker_fixRestrict hpt]
    intro k hk
    rw [mem_subgroupOf] at hk ⊢
    exact zpowers_le.2 hτS hk
  have hKcard : Nat.card (K.subgroupOf S') = 2 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hKS).toEquiv, hK, hG.card_ker_fixRestrict hpt]
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (K.subgroupOf S')
  rw [hKcard, ← hker, Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv,
    hrange] at h1
  rw [← h1, Nat.card_congr (subgroupOfEquivOfLe hSE).toEquiv]

theorem existsUnique_centralizer_singer [Finite Ω] (hG : InvolutionGeometry N τ α β s)
    {T : Subgroup (Equiv.Perm Ω)} (hTα : ∀ t ∈ T, t α = α)
    (hTfree : ∀ t ∈ T, ∀ x, x ≠ α → t x = x → t = 1)
    (hCT : Nat.card ↥(T ⊓ centralizer {τ}) = s - 1) {x y : Ω} (hx : τ x = x) (hy : τ y = y)
    (hxα : x ≠ α) (hyα : y ≠ α) : ∃! c, c ∈ T ⊓ centralizer {τ} ∧ c x = y := by
  classical
  set C := T ⊓ centralizer {τ} with hC
  have hmem : ∀ c : ↥C, τ ((c : Equiv.Perm Ω) x) = (c : Equiv.Perm Ω) x ∧
      (c : Equiv.Perm Ω) x ≠ α := by
    intro c
    have hc : (c : Equiv.Perm Ω) * τ = τ * c :=
      mem_centralizer_singleton_iff.1 (mem_inf.1 c.2).2
    refine ⟨(mem_fixedPoints_apply_iff hc x).2 hx, fun h => hxα ?_⟩
    apply (c : Equiv.Perm Ω).injective
    rw [h, hTα _ (mem_inf.1 c.2).1]
  let φ : ↥C → ↥{z : Ω | τ z = z ∧ z ≠ α} := fun c => ⟨(c : Equiv.Perm Ω) x, hmem c⟩
  have hinj : Function.Injective φ := by
    intro c c' hcc'
    have h1 : (c : Equiv.Perm Ω) x = (c' : Equiv.Perm Ω) x := congrArg Subtype.val hcc'
    have h2 : (c' : Equiv.Perm Ω)⁻¹ * c = 1 := by
      apply hTfree _ (mul_mem (inv_mem (mem_inf.1 c'.2).1) (mem_inf.1 c.2).1) x hxα
      show (c' : Equiv.Perm Ω)⁻¹ ((c : Equiv.Perm Ω) x) = x
      rw [h1, perm_inv_apply]
    apply Subtype.ext
    rw [← mul_inv_cancel_left (c' : Equiv.Perm Ω) c, h2, mul_one]
  have hcard : Nat.card ↥{z : Ω | τ z = z ∧ z ≠ α} ≤ Nat.card ↥C := by
    rw [hCT, Nat.card_coe_set_eq,
      show {z : Ω | τ z = z ∧ z ≠ α} = Function.fixedPoints ⇑τ \ {α} by
        ext z
        simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
        exact Iff.rfl,
      Set.ncard_sdiff_singleton_of_mem (s := Function.fixedPoints ⇑τ) hG.fix_left, hG.card_fix]
  obtain ⟨c, hc⟩ := (hinj.bijective_of_nat_card_le hcard).2 ⟨y, hy, hyα⟩
  refine ⟨c, ⟨c.2, congrArg Subtype.val hc⟩, ?_⟩
  rintro c' ⟨hc', hc'x⟩
  have h1 := @hinj ⟨c', hc'⟩ c (Subtype.ext (hc'x.trans (congrArg Subtype.val hc).symm))
  exact congrArg Subtype.val h1

theorem centralizer_singer_image [Finite Ω] (hG : InvolutionGeometry N τ α β s)
    (hpt : ∀ g ∈ N, (∀ x, τ x = x → g x = x) → g = 1 ∨ g = τ) {T : Subgroup (Equiv.Perm Ω)}
    (hTN : T ≤ N) (hTα : ∀ t ∈ T, t α = α)
    (hTn : ∀ t ∈ T, ∀ h ∈ N, h α = α → h * t * h⁻¹ ∈ T)
    (hTfree : ∀ t ∈ T, ∀ x, x ≠ α → t x = x → t = 1) [IsCyclic T]
    (hCT : Nat.card ↥(T ⊓ centralizer {τ}) = s - 1) :
    ((T ⊓ centralizer {τ}).subgroupOf (N ⊓ centralizer {τ})).map
        (QuotientGroup.mk' (fixRestrict N τ).ker) ≤
      ((N ⊓ MulAction.stabilizer (Equiv.Perm Ω) α).subgroupOf (N ⊓ centralizer {τ})).map
        (QuotientGroup.mk' (fixRestrict N τ).ker) ∧
    ((((T ⊓ centralizer {τ}).subgroupOf (N ⊓ centralizer {τ})).map
        (QuotientGroup.mk' (fixRestrict N τ).ker)).subgroupOf
      (((N ⊓ MulAction.stabilizer (Equiv.Perm Ω) α).subgroupOf (N ⊓ centralizer {τ})).map
        (QuotientGroup.mk' (fixRestrict N τ).ker))).Normal ∧
    IsCyclic ↥(((T ⊓ centralizer {τ}).subgroupOf (N ⊓ centralizer {τ})).map
        (QuotientGroup.mk' (fixRestrict N τ).ker)) ∧
    Nat.card ↥(((T ⊓ centralizer {τ}).subgroupOf (N ⊓ centralizer {τ})).map
        (QuotientGroup.mk' (fixRestrict N τ).ker)) = s - 1 ∧
    ∀ x y : ↥(Function.fixedPoints ⇑τ), (x : Ω) ≠ α → (y : Ω) ≠ α →
      ∃! c : ↥(((T ⊓ centralizer {τ}).subgroupOf (N ⊓ centralizer {τ})).map
          (QuotientGroup.mk' (fixRestrict N τ).ker)),
        QuotientGroup.kerLift (fixRestrict N τ) c x = y := by
  set E := N ⊓ centralizer {τ} with hE
  set K := (fixRestrict N τ).ker with hK
  set C' := (T ⊓ centralizer {τ}).subgroupOf E with hC'
  have hCE : T ⊓ centralizer {τ} ≤ E := fun c hc => mem_inf.2 ⟨hTN (mem_inf.1 hc).1,
    (mem_inf.1 hc).2⟩
  have hτT : τ ∉ T := fun h => hG.tau_ne_one (hTfree τ h β (Ne.symm hG.ne) hG.fix_right)
  let f : C' →* E ⧸ K := (QuotientGroup.mk' K).comp C'.subtype
  have hfinj : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have hcK : (c : E) ∈ K := (QuotientGroup.eq_one_iff _).1 hc
    rw [hK, hG.ker_fixRestrict hpt, mem_subgroupOf, hG.mem_zpowers_iff] at hcK
    rcases hcK with h1 | h1
    · exact Subtype.ext (Subtype.ext h1)
    · exact absurd (h1 ▸ (mem_inf.1 (mem_subgroupOf.1 c.2)).1) hτT
  have hrange : f.range = C'.map (QuotientGroup.mk' K) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let e₁ : C' ≃* ↥(C'.map (QuotientGroup.mk' K)) :=
    (MonoidHom.ofInjective hfinj).trans (MulEquiv.subgroupCongr hrange)
  have he₁ : ∀ c : C', ((e₁ c : ↥(C'.map (QuotientGroup.mk' K))) : E ⧸ K) =
      QuotientGroup.mk' K (c : E) := fun c => rfl
  have : IsCyclic ↥(T ⊓ centralizer {τ}) := Subgroup.isCyclic_of_le inf_le_left
  refine ⟨Subgroup.map_mono fun c hc => ?_, ⟨fun n hn g => ?_⟩, isCyclic_map_mk _ hCE, ?_,
    fun x y hx hy => ?_⟩
  · rw [mem_subgroupOf] at hc ⊢
    exact mem_inf.2 ⟨hTN (mem_inf.1 hc).1, hTα _ (mem_inf.1 hc).1⟩
  · rw [mem_subgroupOf] at hn ⊢
    obtain ⟨c, hc, hcn⟩ := hn
    obtain ⟨e, he, heg⟩ := g.2
    rw [SetLike.mem_coe, mem_subgroupOf] at hc he
    refine ⟨e * c * e⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_subgroupOf]
      refine mem_inf.2 ⟨?_, (mem_inf.1 (e * c * e⁻¹ : E).2).2⟩
      exact hTn _ (mem_inf.1 hc).1 _ (mem_inf.1 he).1 (mem_inf.1 he).2
    · rw [map_mul, map_mul, map_inv, heg, hcn]
      rfl
  · rw [← Nat.card_congr e₁.toEquiv, Nat.card_congr (subgroupOfEquivOfLe hCE).toEquiv, hCT]
  · obtain ⟨c₀, ⟨hc₀, hc₀x⟩, huniq⟩ := hG.existsUnique_centralizer_singer hTα hTfree hCT x.2
      y.2 hx hy
    refine ⟨e₁ ⟨⟨c₀, hCE hc₀⟩, mem_subgroupOf.2 hc₀⟩, ?_, ?_⟩
    · apply Subtype.ext
      rw [he₁]
      exact hc₀x
    · rintro ⟨c', hc'⟩ hc'x
      obtain ⟨c₁, hc₁, rfl⟩ := hc'
      rw [SetLike.mem_coe, mem_subgroupOf] at hc₁
      have h1 : (c₁ : Equiv.Perm Ω) x = y := congrArg Subtype.val hc'x
      have h2 : (c₁ : Equiv.Perm Ω) = c₀ := huniq _ ⟨hc₁, h1⟩
      have h3 : c₁ = ⟨c₀, hCE hc₀⟩ := Subtype.ext h2
      subst h3
      rfl

end InvolutionGeometry

end Restriction

section FieldFacts

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {ψ σ : G} (hψ : orderOf ψ = 2)
    (hσ : σ ∈ zpowers ψ) : σ = 1 ∨ σ = ψ := by
  obtain ⟨k, rfl⟩ := hσ
  show ψ ^ k = 1 ∨ ψ ^ k = ψ
  rw [← zpow_mod_orderOf, hψ, Nat.cast_ofNat]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [h, zpow_zero]
  · right
    rw [h, zpow_one]

theorem eq_of_orderOf_eq_two_of_isCyclic {G : Type*} [Group G] [Finite G] [IsCyclic G] {a b : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  have h : zpowers a = zpowers b := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, ha, hb]
  have hab : a ∈ zpowers b := h ▸ mem_zpowers a
  rcases eq_one_or_eq_of_mem_zpowers hb hab with h1 | h1
  · rw [h1, orderOf_one] at ha
    omega
  · exact h1

variable {K : Type*} [Field K] [Fintype K] [Algebra (ZMod 2) K] {n : ℕ}

theorem finrank_eq_of_card (hK : Fintype.card K = 2 ^ n) : Module.finrank (ZMod 2) K = n := by
  have h := Module.card_eq_pow_finrank (K := ZMod 2) (V := K)
  rw [ZMod.card, hK] at h
  exact (Nat.pow_right_injective le_rfl h).symm

theorem card_gal (hK : Fintype.card K = 2 ^ n) : Nat.card (K ≃ₐ[ZMod 2] K) = n := by
  rw [IsGalois.card_aut_eq_finrank, finrank_eq_of_card hK]

theorem frob_pow_apply (j : ℕ) (k : K) :
    (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K ^ j) k = k ^ (2 ^ j) := by
  rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate, ZMod.card]

theorem orderOf_frob_half (hK : Fintype.card K = 2 ^ n) (hn : Even n) (hn0 : n ≠ 0) :
    orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K ^ (n / 2)) = 2 := by
  have h1 : orderOf (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K) = n := by
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic, finrank_eq_of_card hK]
  obtain ⟨m, rfl⟩ := hn
  have hm : m ≠ 0 := by omega
  have hmm : (m + m) / 2 = m := by omega
  rw [hmm, orderOf_pow_of_dvd hm (by rw [h1]; exact ⟨2, by ring⟩), h1]
  exact Nat.div_eq_of_eq_mul_left (Nat.pos_of_ne_zero hm) (by ring)

theorem eq_frob_half (hK : Fintype.card K = 2 ^ n) (hn : Even n) (hn0 : n ≠ 0)
    {σ : K ≃ₐ[ZMod 2] K} (hσ : orderOf σ = 2) :
    σ = FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K ^ (n / 2) :=
  eq_of_orderOf_eq_two_of_isCyclic hσ (orderOf_frob_half hK hn hn0)

theorem card_fixed_frob_half (hK : Fintype.card K = 2 ^ n) (hn : Even n) (hn0 : n ≠ 0) :
    Nat.card {k : K // k ^ 2 ^ (n / 2) = k} = 2 ^ (n / 2) := by
  classical
  have : FiniteDimensional (ZMod 2) K := Module.Finite.of_finite
  set σ := FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K ^ (n / 2) with hσ
  have hσ2 := orderOf_frob_half hK hn hn0
  set E := IntermediateField.fixedField (zpowers σ) with hE
  have hrank : Module.finrank E K = 2 := by
    rw [hE, IntermediateField.finrank_fixedField_eq_card, Nat.card_zpowers, hσ2]
  have hcard : Nat.card {k : K // k ^ 2 ^ (n / 2) = k} = Nat.card E := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun k => ?_)
    rw [hE, IntermediateField.mem_fixedField_iff]
    have hσk : σ k = k ^ 2 ^ (n / 2) := frob_pow_apply (n / 2) k
    constructor
    · intro hk f hf
      rcases eq_one_or_eq_of_mem_zpowers hσ2 hf with rfl | rfl
      · rfl
      · rw [hσk, hk]
    · intro hk
      rw [← hσk]
      exact hk σ (mem_zpowers σ)
  have : Fintype E := Fintype.ofFinite E
  have h1 : Fintype.card K = Fintype.card E ^ Module.finrank E K := Module.card_eq_pow_finrank
  rw [hrank, hK] at h1
  rw [hcard, Nat.card_eq_fintype_card]
  obtain ⟨m, rfl⟩ := hn
  have h2 : 2 ^ (m + m) = (2 ^ m) ^ 2 := by ring
  rw [h2] at h1
  rw [show (m + m) / 2 = m by omega]
  exact (Nat.pow_left_injective two_ne_zero h1).symm

end FieldFacts

section Coordinate

variable {Δ K : Type*} [Field K] {T : Subgroup (Equiv.Perm Δ)} {R₀ β : Δ}

theorem exists_coordinate (hβ : β ≠ R₀) (hTR : ∀ t ∈ T, t R₀ = R₀)
    (hTreg : ∀ x y, x ≠ R₀ → y ≠ R₀ → ∃! t : T, (t : Equiv.Perm Δ) x = y) (θ : T ≃* Kˣ) :
    ∃ z : Δ ≃ K, z R₀ = 0 ∧ z β = 1 ∧ ∀ t : T, ∀ x, z ((t : Equiv.Perm Δ) x) = θ t * z x := by
  classical
  let w : K → Δ := fun k =>
    if hk : k = 0 then R₀ else ((θ.symm (Units.mk0 k hk) : T) : Equiv.Perm Δ) β
  have hw0 : w 0 = R₀ := dite_eq_left rfl
  have hwk : ∀ k (hk : k ≠ 0), w k = ((θ.symm (Units.mk0 k hk) : T) : Equiv.Perm Δ) β :=
    fun k hk => dite_eq_right hk
  have hne : ∀ t : T, (t : Equiv.Perm Δ) β ≠ R₀ := by
    intro t h1
    apply hβ
    have h2 : (t : Equiv.Perm Δ) R₀ = R₀ := hTR t t.2
    exact (t : Equiv.Perm Δ).injective (h1.trans h2.symm)
  have hinj : Function.Injective w := by
    intro k k' hkk'
    by_cases hk : k = 0 <;> by_cases hk' : k' = 0
    · rw [hk, hk']
    · rw [hk, hw0, hwk k' hk'] at hkk'
      exact absurd hkk'.symm (hne _)
    · rw [hk', hw0, hwk k hk] at hkk'
      exact absurd hkk' (hne _)
    · rw [hwk k hk, hwk k' hk'] at hkk'
      obtain ⟨t, -, huniq⟩ :=
        hTreg β (((θ.symm (Units.mk0 k hk) : T) : Equiv.Perm Δ) β) hβ (hne _)
      have h1 := (huniq _ rfl).trans (huniq _ hkk'.symm).symm
      have h2 := congrArg Units.val (θ.symm.injective h1)
      simpa using h2
  have hsurj : Function.Surjective w := by
    intro x
    by_cases hx : x = R₀
    · exact ⟨0, by rw [hw0, hx]⟩
    · obtain ⟨t, ht, -⟩ := hTreg β x hβ hx
      refine ⟨(θ t : K), ?_⟩
      rw [hwk _ (θ t).ne_zero, Units.mk0_val, MulEquiv.symm_apply_apply, ht]
  have hzw : ∀ k, (Equiv.ofBijective w ⟨hinj, hsurj⟩).symm (w k) = k := fun k =>
    Equiv.ofBijective_symm_apply_apply w ⟨hinj, hsurj⟩ k
  refine ⟨(Equiv.ofBijective w ⟨hinj, hsurj⟩).symm, by rw [← hw0, hzw], ?_, fun t x => ?_⟩
  · have h1 : w 1 = β := by
      rw [hwk 1 one_ne_zero]
      have : Units.mk0 (1 : K) one_ne_zero = 1 := Units.ext rfl
      rw [this, map_one]
      rfl
    rw [← h1, hzw]
  · obtain ⟨k, rfl⟩ := hsurj x
    rw [hzw]
    by_cases hk : k = 0
    · rw [hk, hw0, hTR t t.2, mul_zero, ← hw0, hzw]
    · have hck : (θ t : K) * k ≠ 0 := mul_ne_zero (θ t).ne_zero hk
      have h1 : w ((θ t : K) * k) = (t : Equiv.Perm Δ) (w k) := by
        rw [hwk _ hck, hwk k hk]
        have : Units.mk0 ((θ t : K) * k) hck = θ t * Units.mk0 k hk := Units.ext rfl
        rw [this, map_mul, MulEquiv.symm_apply_apply]
        rfl
      rw [← h1, hzw]

theorem coordinate_pow {z : Δ ≃ K} (hz0 : z R₀ = 0) (hz1 : z β = 1) (θ : T ≃* Kˣ)
    (hzT : ∀ t : T, ∀ x, z ((t : Equiv.Perm Δ) x) = θ t * z x) {b : Equiv.Perm Δ}
    (hbR : b R₀ = R₀) (hbβ : b β = β) {m : ℕ} (hm : m ≠ 0)
    (hb : ∀ t ∈ T, b * t * b⁻¹ = t ^ m) (x : Δ) : z (b x) = z x ^ m := by
  by_cases hx : z x = 0
  · have hxR : x = R₀ := z.injective (hx.trans hz0.symm)
    rw [hxR, hbR, hz0, zero_pow hm]
  · set t := θ.symm (Units.mk0 (z x) hx) with ht
    have htβ : (t : Equiv.Perm Δ) β = x := by
      apply z.injective
      rw [hzT, hz1, mul_one, ht, MulEquiv.apply_symm_apply, Units.val_mk0]
    have h1 : b x = ((t ^ m : T) : Equiv.Perm Δ) β := by
      rw [SubgroupClass.coe_pow, ← hb t t.2, ← htβ]
      show b ((t : Equiv.Perm Δ) β) = b ((t : Equiv.Perm Δ) (b⁻¹ β))
      rw [inv_apply_eq_of_apply_eq hbβ]
    rw [h1, hzT, hz1, mul_one, map_pow, ht, MulEquiv.apply_symm_apply,
      Units.val_pow_eq_pow_val, Units.val_mk0]

end Coordinate

end GMSAffine

@[expose] def gmsPairStabilizer {D : Type*} [Group D] (U R : Subgroup D)
    (β : gmsRootConjugates (U ⊔ R) R) : Subgroup (Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) :=
  gmsPermStabilizer U R ⊓ MulAction.stabilizer _ β

namespace GMSAffine

section GMS

variable {D : Type u} [Group D] {J R X U P : Subgroup D} {n : ℕ}

theorem gms_singer_regular [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) (x y : gmsRootConjugates (U ⊔ R) R)
    (hx : x ≠ ⟨R, gms_R_mem⟩) (hy : y ≠ ⟨R, gms_R_mem⟩) :
    ∃! t : gmsSingerPermImage X U R, (t : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) x = y := by
  have hx' : (x : Subgroup D) ≠ R := fun h1 => hx (Subtype.ext h1)
  have hy' : (y : Subgroup D) ≠ R := fun h1 => hy (Subtype.ext h1)
  obtain ⟨t, ht, htQ⟩ := GMSDichotomy.exists_mem_gmsSingerPermImage_apply_eq h h3 hx' hy'
  refine ⟨⟨t, ht⟩, htQ, fun s hs => Subtype.ext ?_⟩
  have h1 : ((t⁻¹ * s : Equiv.Perm (gmsRootConjugates (U ⊔ R) R))) x = x := by
    rw [Equiv.Perm.mul_apply, hs, ← htQ, ← Equiv.Perm.mul_apply, inv_mul_cancel,
      Equiv.Perm.one_apply]
  have h2 := GMSDichotomy.eq_one_of_mem_gmsSingerPermImage h h3 (mul_mem (inv_mem ht) s.2) hx' h1
  exact (inv_mul_eq_one.1 h2).symm

theorem gms_coordinate [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) (β : gmsRootConjugates (U ⊔ R) R)
    (hβ : (β : Subgroup D) ≠ R) :
    ∃ (K : Type u) (_ : Field K) (_ : Fintype K) (_ : Algebra (ZMod 2) K),
      Fintype.card K = 2 ^ n ∧ ∃ z : gmsRootConjugates (U ⊔ R) R ≃ K,
        z ⟨R, gms_R_mem⟩ = 0 ∧ z β = 1 ∧
        ∃ θ : gmsSingerPermImage X U R ≃* Kˣ,
          (∀ t : gmsSingerPermImage X U R, ∀ x,
            z ((t : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) x) = θ t * z x) ∧
          ∀ b ∈ gmsPermStabilizer U R, b β = β → ∃ j : ℕ, ∀ x, z (b x) = z x ^ 2 ^ j := by
  classical
  obtain ⟨K, _, _, _, hK, -⟩ := SteinbergBT.gms_singer_field h
  obtain ⟨hTcyc, hTcard⟩ := GMSDichotomy.isCyclic_gmsSingerPermImage h h3
  have hKcard : Nat.card (gmsSingerPermImage X U R) = Nat.card Kˣ := by
    rw [hTcard, Nat.card_eq_fintype_card, Fintype.card_units, hK]
  let θ : gmsSingerPermImage X U R ≃* Kˣ := mulEquivOfCyclicCardEq hKcard
  have hTR : ∀ t ∈ gmsSingerPermImage X U R, t ⟨R, gms_R_mem⟩ = ⟨R, gms_R_mem⟩ := fun t ht =>
    (GMSDichotomy.mem_gmsPermStabilizer.1 (GMSDichotomy.gmsSingerPermImage_le h ht)).2
  have hβ' : β ≠ ⟨R, gms_R_mem⟩ := fun h1 => hβ (congrArg Subtype.val h1)
  obtain ⟨z, hz0, hz1, hzT⟩ :=
    exists_coordinate hβ' hTR (fun x y hx hy => gms_singer_regular h h3 x y hx hy) θ
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK, z, hz0, hz1, θ, hzT,
    fun b hb hbβ => ?_⟩
  obtain ⟨j, hj⟩ := GMSDichotomy.exists_conj_eq_pow_perm h h3 hb
  exact ⟨j, coordinate_pow hz0 hz1 θ hzT (GMSDichotomy.mem_gmsPermStabilizer.1 hb).2 hbβ
    (pow_ne_zero _ two_ne_zero) hj⟩

theorem gms_galois [Finite D] (h : GMSNormalRootData J R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard) (β : gmsRootConjugates (U ⊔ R) R)
    (hβ : (β : Subgroup D) ≠ R) (hd : Even (Nat.card (gmsPairStabilizer U R β))) :
    ∃ (K : Type u) (_ : Field K) (_ : Fintype K) (_ : Algebra (ZMod 2) K),
      Fintype.card K = 2 ^ n ∧ ∃ z : gmsRootConjugates (U ⊔ R) R ≃ K,
        z ⟨R, gms_R_mem⟩ = 0 ∧ z β = 1 ∧
        (∃ θ : gmsSingerPermImage X U R ≃* Kˣ,
          ∀ t : gmsSingerPermImage X U R, ∀ x,
            z ((t : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) x) = θ t * z x) ∧
        ∃ γ : gmsPairStabilizer U R β →* (K ≃ₐ[ZMod 2] K), Function.Injective γ ∧
          (∀ b : gmsPairStabilizer U R β, ∀ x,
            z ((b : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) x) = γ b (z x)) ∧
          4 ≤ n ∧ Even n ∧ Nat.card (gmsPairStabilizer U R β) ∣ n ∧
          IsCyclic (gmsPairStabilizer U R β) ∧
          (∀ S : Subgroup (K ≃ₐ[ZMod 2] K),
            Nat.card S = Nat.card (gmsPairStabilizer U R β) ↔ S = γ.range) ∧
          Nat.card {k : K // k ^ 2 ^ (n / 2) = k} = 2 ^ (n / 2) ∧
          ∀ τ ∈ gmsPairStabilizer U R β, orderOf τ = 2 →
            (∀ x, z (τ x) = z x ^ 2 ^ (n / 2)) ∧ (∀ x, τ x = x ↔ z x ^ 2 ^ (n / 2) = z x) ∧
            (Function.fixedPoints ⇑τ).ncard = 2 ^ (n / 2) ∧
            (∀ g ∈ (gmsRootConjugateAction (U ⊔ R) R).range,
              (∀ x, τ x = x → g x = x) → g = 1 ∨ g = τ) ∧
            Nat.card ↥(gmsSingerPermImage X U R ⊓ centralizer {τ}) = 2 ^ (n / 2) - 1 := by
  classical
  obtain ⟨K, _, _, _, hK, z, hz0, hz1, θ, hzT, hzB⟩ := gms_coordinate h h3 β hβ
  have hBH : ∀ b ∈ gmsPairStabilizer U R β, b ∈ gmsPermStabilizer U R :=
    fun b hb => (mem_inf.1 hb).1
  have hBβ : ∀ b ∈ gmsPairStabilizer U R β, b β = β :=
    fun b hb => MulAction.mem_stabilizer_iff.1 (mem_inf.1 hb).2
  have hzB' : ∀ b : gmsPairStabilizer U R β, ∃ j : ℕ,
      ∀ x, z ((b : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) x) = z x ^ 2 ^ j :=
    fun b => hzB b (hBH b b.2) (hBβ b b.2)
  choose j hj using hzB'
  have hγapply : ∀ (b : gmsPairStabilizer U R β) x,
      z ((b : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) x) =
        (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K ^ j b) (z x) := fun b x => by
    rw [frob_pow_apply, hj]
  let γ : gmsPairStabilizer U R β →* (K ≃ₐ[ZMod 2] K) :=
    { toFun := fun b => FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K ^ j b
      map_one' := by
        apply AlgEquiv.ext
        intro k
        obtain ⟨x, rfl⟩ := z.surjective k
        rw [← hγapply 1 x]
        rfl
      map_mul' := fun b b' => by
        apply AlgEquiv.ext
        intro k
        obtain ⟨x, rfl⟩ := z.surjective k
        rw [← hγapply (b * b') x, AlgEquiv.mul_apply, ← hγapply b' x, ← hγapply b]
        rfl }
  have hγ : ∀ (b : gmsPairStabilizer U R β) x,
      z ((b : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) x) = γ b (z x) := hγapply
  have hγinj : Function.Injective γ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    apply Subtype.ext
    apply Equiv.ext
    intro x
    apply z.injective
    rw [hγ, hb]
    rfl
  have hBcyc : IsCyclic (gmsPairStabilizer U R β) := isCyclic_of_injective γ hγinj
  have hGal := card_gal hK
  have hBcard : Nat.card (gmsPairStabilizer U R β) = Nat.card γ.range :=
    Nat.card_congr (MonoidHom.ofInjective hγinj).toEquiv
  have hdn : Nat.card (gmsPairStabilizer U R β) ∣ n := by
    rw [hBcard, ← hGal]
    exact Subgroup.card_subgroup_dvd_card γ.range
  have hn3 : 3 ≤ n := h.1
  have hneven : Even n := even_iff_two_dvd.2 ((even_iff_two_dvd.1 hd).trans hdn)
  have hn4 : 4 ≤ n := by
    obtain ⟨m, hm⟩ := hneven
    omega
  have hn0 : n ≠ 0 := by omega
  have hrange : ∀ S : Subgroup (K ≃ₐ[ZMod 2] K),
      Nat.card S = Nat.card (gmsPairStabilizer U R β) ↔ S = γ.range := by
    intro S
    rw [hBcard, IsCyclic.subgroup_eq_iff_card_eq]
  have hFk := card_fixed_frob_half hK hneven hn0
  refine ⟨K, inferInstance, inferInstance, inferInstance, hK, z, hz0, hz1, ⟨θ, hzT⟩, γ, hγinj, hγ,
    hn4, hneven, hdn, hBcyc, hrange, hFk, fun τ hτ hτ2 => ?_⟩
  have hγτ : γ ⟨τ, hτ⟩ = FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K ^ (n / 2) :=
    eq_frob_half hK hneven hn0 (by rw [orderOf_injective γ hγinj, Subgroup.orderOf_mk, hτ2])
  have hzτ : ∀ x, z (τ x) = z x ^ 2 ^ (n / 2) := fun x => by
    rw [show τ x = ((⟨τ, hτ⟩ : gmsPairStabilizer U R β) :
      Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) x from rfl, hγ, hγτ, frob_pow_apply]
  have hfixτ : ∀ x, τ x = x ↔ z x ^ 2 ^ (n / 2) = z x := fun x => by
    rw [← hzτ]
    exact z.injective.eq_iff.symm
  have hFcard : (Function.fixedPoints ⇑τ).ncard = 2 ^ (n / 2) := by
    rw [← Nat.card_coe_set_eq, ← hFk]
    exact Nat.card_congr (z.subtypeEquiv fun x => hfixτ x)
  have hτR : τ ⟨R, gms_R_mem⟩ = ⟨R, gms_R_mem⟩ :=
    (GMSDichotomy.mem_gmsPermStabilizer.1 (hBH τ hτ)).2
  have hτβ := hBβ τ hτ
  have hpt : ∀ g ∈ (gmsRootConjugateAction (U ⊔ R) R).range,
      (∀ x, τ x = x → g x = x) → g = 1 ∨ g = τ := by
    intro g hg hgF
    have hgB : g ∈ gmsPairStabilizer U R β :=
      mem_inf.2 ⟨GMSDichotomy.mem_gmsPermStabilizer.2 ⟨hg, hgF _ hτR⟩,
        MulAction.mem_stabilizer_iff.2 (hgF _ hτβ)⟩
    have : FiniteDimensional (ZMod 2) K := Module.Finite.of_finite
    have hmem : γ ⟨g, hgB⟩ ∈
        zpowers (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K ^ (n / 2)) := by
      rw [← IntermediateField.fixingSubgroup_fixedField
        (zpowers (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K ^ (n / 2))),
        IntermediateField.mem_fixingSubgroup_iff]
      intro k hk
      rw [IntermediateField.mem_fixedField_iff] at hk
      have hk' : k ^ 2 ^ (n / 2) = k := by
        rw [← frob_pow_apply]
        exact hk _ (mem_zpowers _)
      obtain ⟨x, rfl⟩ := z.surjective k
      rw [← hγ]
      exact congrArg z (hgF x ((hfixτ x).2 hk'))
    rcases eq_one_or_eq_of_mem_zpowers (orderOf_frob_half hK hneven hn0) hmem with h1 | h1
    · left
      exact congrArg Subtype.val (hγinj (h1.trans (map_one γ).symm))
    · right
      exact congrArg Subtype.val (hγinj (h1.trans hγτ.symm))
  have hTn : ∀ t ∈ gmsSingerPermImage X U R, τ * t * τ⁻¹ ∈ gmsSingerPermImage X U R := by
    intro t ht
    have h1 := (GMSDichotomy.gmsSingerPermImage_normal h (X := X)).conj_mem
      ⟨t, GMSDichotomy.gmsSingerPermImage_le h ht⟩ (mem_subgroupOf.2 ht) ⟨τ, hBH τ hτ⟩
    rw [mem_subgroupOf] at h1
    exact h1
  have hθτ : ∀ t : gmsSingerPermImage X U R,
      ((θ ⟨τ * t * τ⁻¹, hTn t t.2⟩ : Kˣ) : K) = (θ t : K) ^ 2 ^ (n / 2) := by
    intro t
    have h1 := hzT ⟨τ * t * τ⁻¹, hTn t t.2⟩ β
    rw [hz1, mul_one] at h1
    rw [← h1]
    show z (τ ((t : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) (τ⁻¹ β))) = _
    rw [inv_apply_eq_of_apply_eq hτβ, hzτ, hzT, hz1, mul_one]
  have hcomm : ∀ t : gmsSingerPermImage X U R,
      (t : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) ∈ centralizer {τ} ↔
        (θ t : K) ^ 2 ^ (n / 2) = θ t := by
    intro t
    rw [mem_centralizer_singleton_iff, ← hθτ]
    constructor
    · intro htc
      have h2 : (⟨τ * t * τ⁻¹, hTn t t.2⟩ : gmsSingerPermImage X U R) = t := by
        apply Subtype.ext
        show τ * (t : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) * τ⁻¹ = t
        rw [← htc]
        group
      rw [h2]
    · intro h1
      have h2 : (⟨τ * t * τ⁻¹, hTn t t.2⟩ : gmsSingerPermImage X U R) = t :=
        θ.injective (Units.ext h1)
      have h3 : τ * (t : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) * τ⁻¹ = t :=
        congrArg Subtype.val h2
      calc (t : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) * τ =
          τ * t * τ⁻¹ * τ := by rw [h3]
        _ = τ * t := by group
  have hCT : Nat.card ↥(gmsSingerPermImage X U R ⊓ centralizer {τ}) = 2 ^ (n / 2) - 1 := by
    let e1 : ↥(gmsSingerPermImage X U R ⊓ centralizer {τ}) ≃
        {c : Kˣ // (c : K) ^ 2 ^ (n / 2) = c} :=
      { toFun := fun c => ⟨θ ⟨c, (mem_inf.1 c.2).1⟩, (hcomm ⟨c, _⟩).1 (mem_inf.1 c.2).2⟩
        invFun := fun c => ⟨θ.symm c, mem_inf.2 ⟨(θ.symm c).2, (hcomm _).2 (by
          rw [MulEquiv.apply_symm_apply]
          exact c.2)⟩⟩
        left_inv := fun c => Subtype.ext (by simp)
        right_inv := fun c => Subtype.ext (by simp) }
    let e2 : {c : Kˣ // (c : K) ^ 2 ^ (n / 2) = c} ≃
        ↥({k : K | k ^ 2 ^ (n / 2) = k} \ {0}) :=
      { toFun := fun c => ⟨c.1, c.2, c.1.ne_zero⟩
        invFun := fun k => ⟨Units.mk0 k.1 k.2.2, k.2.1⟩
        left_inv := fun c => Subtype.ext (Units.ext rfl)
        right_inv := fun k => Subtype.ext rfl }
    have h0 : (0 : K) ∈ {k : K | k ^ 2 ^ (n / 2) = k} := by
      show (0 : K) ^ 2 ^ (n / 2) = 0
      exact zero_pow (pow_ne_zero _ two_ne_zero)
    rw [Nat.card_congr (e1.trans e2), Nat.card_coe_set_eq, Set.ncard_sdiff_singleton_of_mem h0,
      ← Nat.card_coe_set_eq, Set.coe_ofPred, hFk]
  exact ⟨hzτ, hfixτ, hFcard, hpt, hCT⟩

end GMS

end GMSAffine

open GMSAffine

variable {D : Type u} [Group D] {J R X U P : Subgroup D} {n : ℕ}

theorem gms_normal_root_even_pair_involution_affine_plane [Finite D]
    (h : GMSNormalRootData J R X U P n) (h3 : 3 ≤ (gmsRootConjugates (U ⊔ R) R).ncard)
    (β : gmsRootConjugates (U ⊔ R) R) (hβ : (β : Subgroup D) ≠ R)
    (hd : Even (Nat.card (gmsPairStabilizer U R β))) :
    IsCyclic (gmsPairStabilizer U R β) ∧
    (∀ x ∈ gmsPermStabilizer U R, ∃ t ∈ gmsSingerPermImage X U R,
      ∃ b ∈ gmsPairStabilizer U R β, x = t * b) ∧
    gmsSingerPermImage X U R ⊔ gmsPairStabilizer U R β = gmsPermStabilizer U R ∧
    gmsSingerPermImage X U R ⊓ gmsPairStabilizer U R β = ⊥ ∧
    Nat.card (gmsPairStabilizer U R β) ∣ n ∧ 4 ≤ n ∧ Even n ∧ 2 ^ n = (2 ^ (n / 2)) ^ 2 ∧
    4 ≤ 2 ^ (n / 2) ∧
    (∃ (K : Type u) (_ : Field K) (_ : Fintype K) (_ : Algebra (ZMod 2) K),
      Fintype.card K = 2 ^ n ∧ ∃ z : gmsRootConjugates (U ⊔ R) R ≃ K,
        z ⟨R, gms_R_mem⟩ = 0 ∧ z β = 1 ∧
        (∀ t ∈ gmsSingerPermImage X U R, ∃ c : Kˣ, ∀ x, z (t x) = c * z x) ∧
        (∀ c : Kˣ, ∃ t ∈ gmsSingerPermImage X U R, ∀ x, z (t x) = c * z x) ∧
        ∃ γ : gmsPairStabilizer U R β →* (K ≃ₐ[ZMod 2] K), Function.Injective γ ∧
          (∀ b : gmsPairStabilizer U R β, ∀ x,
            z ((b : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) x) = γ b (z x)) ∧
          (∀ S : Subgroup (K ≃ₐ[ZMod 2] K),
            Nat.card S = Nat.card (gmsPairStabilizer U R β) ↔ S = γ.range) ∧
          Nat.card {k : K // k ^ 2 ^ (n / 2) = k} = 2 ^ (n / 2) ∧
          ∀ τ ∈ gmsPairStabilizer U R β, orderOf τ = 2 →
            (∀ x, z (τ x) = z x ^ 2 ^ (n / 2)) ∧ ∀ x, τ x = x ↔ z x ^ 2 ^ (n / 2) = z x) ∧
    (∃! τ, τ ∈ gmsPairStabilizer U R β ∧ orderOf τ = 2) ∧
    (U ⊔ R).normalizerMonoidHom.ker = (centralizer ((U ⊔ R : Subgroup D) : Set D)).subgroupOf
      (normalizer ((U ⊔ R : Subgroup D) : Set D)) ∧
    (gmsRootConjugateAction (U ⊔ R) R).ker = gmsRootKernel (U ⊔ R) R ∧
    (centralizer ((U ⊔ R : Subgroup D) : Set D)).subgroupOf
      (normalizer ((U ⊔ R : Subgroup D) : Set D)) ≤ gmsRootKernel (U ⊔ R) R ∧
    (gmsConjAct X U).ker =
      (X ⊓ centralizer (U : Set D)).subgroupOf (X ⊓ normalizer (U : Set D)) ∧
    (∀ g (hg : g ∈ X ⊓ normalizer (U : Set D)),
      gmsRootConjugateAction (U ⊔ R) R ⟨g, gms_NXU_le_L h hg⟩ = 1 ↔
        g ∈ X ⊓ centralizer (U : Set D)) ∧
    (commutator (normalizer ((U ⊔ R : Subgroup D) : Set D))).map
        (gmsRootConjugateAction (U ⊔ R) R) =
      ⁅(gmsRootConjugateAction (U ⊔ R) R).range, (gmsRootConjugateAction (U ⊔ R) R).range⁆ ∧
    ((gmsRootConjugateAction (U ⊔ R) R).comp
        (commutator (normalizer ((U ⊔ R : Subgroup D) : Set D))).subtype).ker =
      (gmsRootKernel (U ⊔ R) R).subgroupOf
        (commutator (normalizer ((U ⊔ R : Subgroup D) : Set D))) ∧
    ∀ τ ∈ gmsPairStabilizer U R β, orderOf τ = 2 →
      (Function.fixedPoints ⇑τ).ncard = 2 ^ (n / 2) ∧
      (∀ x y, x ≠ y → ∃! ℓ, ℓ ∈ permTranslates (gmsRootConjugateAction (U ⊔ R) R).range
        (Function.fixedPoints ⇑τ) ∧ x ∈ ℓ ∧ y ∈ ℓ) ∧
      (∀ ℓ ∈ permTranslates (gmsRootConjugateAction (U ⊔ R) R).range (Function.fixedPoints ⇑τ),
        ℓ.ncard = 2 ^ (n / 2)) ∧
      (∀ x, {ℓ | ℓ ∈ permTranslates (gmsRootConjugateAction (U ⊔ R) R).range
        (Function.fixedPoints ⇑τ) ∧ x ∈ ℓ}.ncard = 2 ^ (n / 2) + 1) ∧
      (permTranslates (gmsRootConjugateAction (U ⊔ R) R).range
        (Function.fixedPoints ⇑τ)).ncard = 2 ^ (n / 2) * (2 ^ (n / 2) + 1) ∧
      (∀ ℓ ∈ permTranslates (gmsRootConjugateAction (U ⊔ R) R).range (Function.fixedPoints ⇑τ),
        ∀ x, x ∉ ℓ → ∃! m, m ∈ permTranslates (gmsRootConjugateAction (U ⊔ R) R).range
          (Function.fixedPoints ⇑τ) ∧ x ∈ m ∧ Disjoint m ℓ) ∧
      (∀ g ∈ (gmsRootConjugateAction (U ⊔ R) R).range,
        ∀ ℓ ∈ permTranslates (gmsRootConjugateAction (U ⊔ R) R).range (Function.fixedPoints ⇑τ),
          ⇑g '' ℓ ∈ permTranslates (gmsRootConjugateAction (U ⊔ R) R).range
            (Function.fixedPoints ⇑τ)) ∧
      (∀ g ∈ (gmsRootConjugateAction (U ⊔ R) R).range, (∀ x, g x = x) → g = 1) ∧
      (∀ x y x' y', x ≠ y → x' ≠ y' →
        ∃ g ∈ (gmsRootConjugateAction (U ⊔ R) R).range, g x = x' ∧ g y = y') ∧
      (∀ g ∈ (gmsRootConjugateAction (U ⊔ R) R).range,
        g ∈ (gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ} ↔
          ⇑g '' Function.fixedPoints ⇑τ = Function.fixedPoints ⇑τ) ∧
      (∃ κ : ↥((gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ}) →*
          Equiv.Perm ↥(Function.fixedPoints ⇑τ),
        (∀ e x, ((κ e x : ↥(Function.fixedPoints ⇑τ)) : gmsRootConjugates (U ⊔ R) R) =
          (e : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) x) ∧
        (∀ x y x' y' : ↥(Function.fixedPoints ⇑τ), x ≠ y → x' ≠ y' →
          ∃ e, κ e x = x' ∧ κ e y = y') ∧
        κ.ker = (zpowers τ).subgroupOf ((gmsRootConjugateAction (U ⊔ R) R).range ⊓
          centralizer {τ}) ∧
        κ.ker = ((gmsPermStabilizer U R).subgroupOf
          ((gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ})).normalCore ∧
        (∀ g ∈ (gmsRootConjugateAction (U ⊔ R) R).range,
          (∀ x ∈ Function.fixedPoints ⇑τ, g x = x) ↔ g ∈ zpowers τ) ∧
        Function.Injective (QuotientGroup.kerLift κ) ∧
        (∀ x y x' y' : ↥(Function.fixedPoints ⇑τ), x ≠ y → x' ≠ y' →
          ∃ u, QuotientGroup.kerLift κ u x = x' ∧ QuotientGroup.kerLift κ u y = y') ∧
        Nat.card (↥((gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ}) ⧸ κ.ker) * 2 =
          2 ^ (n / 2) * (2 ^ (n / 2) - 1) * Nat.card (gmsPairStabilizer U R β) ∧
        gmsPairStabilizer U R β ≤ (gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ} ∧
        (∀ x y : ↥(Function.fixedPoints ⇑τ), (x : gmsRootConjugates (U ⊔ R) R) = ⟨R, gms_R_mem⟩ →
          (y : gmsRootConjugates (U ⊔ R) R) = β →
          (MulAction.stabilizer (Equiv.Perm ↥(Function.fixedPoints ⇑τ)) x ⊓
              MulAction.stabilizer (Equiv.Perm ↥(Function.fixedPoints ⇑τ)) y).comap
            (QuotientGroup.kerLift κ) =
            ((gmsPairStabilizer U R β).subgroupOf
              ((gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ})).map
              (QuotientGroup.mk' κ.ker)) ∧
        IsCyclic ↥(((gmsPairStabilizer U R β).subgroupOf
          ((gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ})).map
            (QuotientGroup.mk' κ.ker)) ∧
        Nat.card ↥(((gmsPairStabilizer U R β).subgroupOf
          ((gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ})).map
            (QuotientGroup.mk' κ.ker)) * 2 = Nat.card (gmsPairStabilizer U R β) ∧
        Nat.card (gmsPairStabilizer U R β) / 2 ∣ n / 2 ∧
        (∀ x : ↥(Function.fixedPoints ⇑τ), (x : gmsRootConjugates (U ⊔ R) R) = ⟨R, gms_R_mem⟩ →
          (MulAction.stabilizer (Equiv.Perm ↥(Function.fixedPoints ⇑τ)) x).comap
            (QuotientGroup.kerLift κ) =
            ((gmsPermStabilizer U R).subgroupOf
              ((gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ})).map
              (QuotientGroup.mk' κ.ker)) ∧
        IsCyclic ↥(gmsSingerPermImage X U R ⊓ centralizer {τ}) ∧
        Nat.card ↥(gmsSingerPermImage X U R ⊓ centralizer {τ}) = 2 ^ (n / 2) - 1 ∧
        ((gmsSingerPermImage X U R ⊓ centralizer {τ}).subgroupOf
            ((gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ})).map
            (QuotientGroup.mk' κ.ker) ≤
          ((gmsPermStabilizer U R).subgroupOf
            ((gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ})).map
            (QuotientGroup.mk' κ.ker) ∧
        ((((gmsSingerPermImage X U R ⊓ centralizer {τ}).subgroupOf
            ((gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ})).map
            (QuotientGroup.mk' κ.ker)).subgroupOf
          (((gmsPermStabilizer U R).subgroupOf
            ((gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ})).map
            (QuotientGroup.mk' κ.ker))).Normal ∧
        IsCyclic ↥(((gmsSingerPermImage X U R ⊓ centralizer {τ}).subgroupOf
            ((gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ})).map
            (QuotientGroup.mk' κ.ker)) ∧
        Nat.card ↥(((gmsSingerPermImage X U R ⊓ centralizer {τ}).subgroupOf
            ((gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ})).map
            (QuotientGroup.mk' κ.ker)) = 2 ^ (n / 2) - 1 ∧
        ∀ x y : ↥(Function.fixedPoints ⇑τ), (x : gmsRootConjugates (U ⊔ R) R) ≠ ⟨R, gms_R_mem⟩ →
          (y : gmsRootConjugates (U ⊔ R) R) ≠ ⟨R, gms_R_mem⟩ →
          ∃! c : ↥(((gmsSingerPermImage X U R ⊓ centralizer {τ}).subgroupOf
              ((gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ})).map
              (QuotientGroup.mk' κ.ker)),
            QuotientGroup.kerLift κ c x = y) ∧
      Nat.card ↥((gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ}) =
        2 ^ (n / 2) * (2 ^ (n / 2) - 1) * Nat.card (gmsPairStabilizer U R β) ∧
      (∀ x y, x ≠ y → ∃ v₁ ∈ (gmsRootConjugateAction (U ⊔ R) R).range,
        ∃ v₂ ∈ (gmsRootConjugateAction (U ⊔ R) R).range, orderOf v₁ = 2 ∧ orderOf v₂ = 2 ∧
          v₁ x = y ∧ v₁ y = x ∧ v₂ x = y ∧ v₂ y = x ∧ v₁ ≠ v₂ ∧
          (Function.fixedPoints ⇑v₁).ncard = 2 ^ (n / 2) ∧ (∀ w, v₂ w ≠ w) ∧
          ∀ v ∈ (gmsRootConjugateAction (U ⊔ R) R).range, orderOf v = 2 → v x = y → v y = x →
            v = v₁ ∨ v = v₂) ∧
      nonregInvolutions (gmsRootConjugateAction (U ⊔ R) R).range =
        {v | ∃ g ∈ (gmsRootConjugateAction (U ⊔ R) R).range, v = g * τ * g⁻¹} ∧
      (nonregInvolutions (gmsRootConjugateAction (U ⊔ R) R).range).ncard =
        2 ^ (n / 2) * (2 ^ (n / 2) + 1) ∧
      Set.BijOn (fun v : Equiv.Perm (gmsRootConjugates (U ⊔ R) R) => Function.fixedPoints ⇑v)
        (nonregInvolutions (gmsRootConjugateAction (U ⊔ R) R).range)
        (permTranslates (gmsRootConjugateAction (U ⊔ R) R).range (Function.fixedPoints ⇑τ)) ∧
      (regInvolutions (gmsRootConjugateAction (U ⊔ R) R).range).ncard = 2 ^ n - 1 ∧
      (∀ w ∈ regInvolutions (gmsRootConjugateAction (U ⊔ R) R).range,
        regInvolutions (gmsRootConjugateAction (U ⊔ R) R).range =
          {v | ∃ g ∈ (gmsRootConjugateAction (U ⊔ R) R).range, v = g * w * g⁻¹}) ∧
      (∀ y, y ≠ ⟨R, gms_R_mem⟩ → ∃! w,
        w ∈ regInvolutions (gmsRootConjugateAction (U ⊔ R) R).range ∧ w ⟨R, gms_R_mem⟩ = y) ∧
      {v | v ∈ nonregInvolutions (gmsRootConjugateAction (U ⊔ R) R).range ∧
        v ∈ (gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ} ∧ v ≠ τ}.ncard =
          2 ^ (n / 2) - 1 ∧
      (∀ v ∈ {v | v ∈ nonregInvolutions (gmsRootConjugateAction (U ⊔ R) R).range ∧
        v ∈ (gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ} ∧ v ≠ τ},
          ∀ x ∈ Function.fixedPoints ⇑τ, v x ≠ x) ∧
      (fun v : Equiv.Perm (gmsRootConjugates (U ⊔ R) R) => Function.fixedPoints ⇑v) ''
          {v | v ∈ nonregInvolutions (gmsRootConjugateAction (U ⊔ R) R).range ∧
            v ∈ (gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ} ∧ v ≠ τ} =
        {ℓ | ℓ ∈ permTranslates (gmsRootConjugateAction (U ⊔ R) R).range
          (Function.fixedPoints ⇑τ) ∧ Disjoint ℓ (Function.fixedPoints ⇑τ)} ∧
      {v | v ∈ (gmsRootConjugateAction (U ⊔ R) R).range ∧ orderOf v = 2 ∧
        v ⟨R, gms_R_mem⟩ = β ∧ v β = ⟨R, gms_R_mem⟩}.ncard = 2 ∧
      {v | v ∈ (gmsRootConjugateAction (U ⊔ R) R).range ∧ orderOf v = 2 ∧
        v ⟨R, gms_R_mem⟩ = β ∧ v β = ⟨R, gms_R_mem⟩ ∧ ∀ x, v x ≠ x}.ncard = 1 ∧
      2 ^ n = 2 ^ (n / 2) * (({v | v ∈ (gmsRootConjugateAction (U ⊔ R) R).range ∧
          orderOf v = 2 ∧ v ⟨R, gms_R_mem⟩ = β ∧ v β = ⟨R, gms_R_mem⟩}.ncard -
        {v | v ∈ (gmsRootConjugateAction (U ⊔ R) R).range ∧ orderOf v = 2 ∧
          v ⟨R, gms_R_mem⟩ = β ∧ v β = ⟨R, gms_R_mem⟩ ∧ ∀ x, v x ≠ x}.ncard) *
            (2 ^ (n / 2) - 1) + 1) ∧
      (∃ κπ : ↥(((gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ}).comap
          (gmsRootConjugateAction (U ⊔ R) R)) →* Equiv.Perm ↥(Function.fixedPoints ⇑τ),
        (∀ l x, ((κπ l x : ↥(Function.fixedPoints ⇑τ)) : gmsRootConjugates (U ⊔ R) R) =
          gmsRootConjugateAction (U ⊔ R) R l x) ∧
        κπ.ker = ((zpowers τ).comap (gmsRootConjugateAction (U ⊔ R) R)).subgroupOf
          (((gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ}).comap
            (gmsRootConjugateAction (U ⊔ R) R))) ∧
      gmsRootKernel (U ⊔ R) R ≤ (zpowers τ).comap (gmsRootConjugateAction (U ⊔ R) R) ∧
      ∃ e : ↥((zpowers τ).comap (gmsRootConjugateAction (U ⊔ R) R)) ⧸
          (gmsRootKernel (U ⊔ R) R).subgroupOf
            ((zpowers τ).comap (gmsRootConjugateAction (U ⊔ R) R)) ≃* zpowers τ,
        ∀ l : ↥((zpowers τ).comap (gmsRootConjugateAction (U ⊔ R) R)),
          ((e (QuotientGroup.mk l) : zpowers τ) : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) =
            gmsRootConjugateAction (U ⊔ R) R l := by
  classical
  obtain ⟨-, hΔcard, -, -, h2tr, -, -, -, -, hρker, hπker, -, -, -, hCK, hπY, -⟩ :=
    gms_normal_root_partition_and_two_transitivity h h3
  have hkerU :=
    (SteinbergBT.gms_normal_root_singer_action_and_weak_closure h).2.2.2.2.2.2.2.2.1
  obtain ⟨K, _, _, _, hK, z, hz0, hz1, ⟨θ, hzT⟩, γ, hγinj, hγ, hn4, hneven, hdn, hBcyc, hrange,
    hFk, hτfacts⟩ := gms_galois h h3 β hβ hd
  have hβR : β ≠ ⟨R, gms_R_mem⟩ := fun h1 => hβ (congrArg Subtype.val h1)
  have hTH := GMSDichotomy.gmsSingerPermImage_le h (X := X)
  have hTN : gmsSingerPermImage X U R ≤ (gmsRootConjugateAction (U ⊔ R) R).range :=
    fun t ht => (GMSDichotomy.mem_gmsPermStabilizer.1 (hTH ht)).1
  have hTR : ∀ t ∈ gmsSingerPermImage X U R, t ⟨R, gms_R_mem⟩ = ⟨R, gms_R_mem⟩ :=
    fun t ht => (GMSDichotomy.mem_gmsPermStabilizer.1 (hTH ht)).2
  have hTtrans : ∀ x y, x ≠ ⟨R, gms_R_mem⟩ → y ≠ ⟨R, gms_R_mem⟩ →
      ∃ t ∈ gmsSingerPermImage X U R, t x = y := fun x y hx hy => by
    obtain ⟨t, ht, -⟩ := gms_singer_regular h h3 x y hx hy
    exact ⟨t, t.2, ht⟩
  have hTfree : ∀ t ∈ gmsSingerPermImage X U R, ∀ x, x ≠ ⟨R, gms_R_mem⟩ → t x = x → t = 1 := by
    intro t ht x hx htx
    obtain ⟨t₀, -, huniq⟩ := gms_singer_regular h h3 x x hx hx
    exact congrArg Subtype.val ((huniq ⟨t, ht⟩ htx).trans (huniq 1 rfl).symm)
  have hTn : ∀ t ∈ gmsSingerPermImage X U R, ∀ g ∈ (gmsRootConjugateAction (U ⊔ R) R).range,
      g ⟨R, gms_R_mem⟩ = ⟨R, gms_R_mem⟩ → g * t * g⁻¹ ∈ gmsSingerPermImage X U R := by
    intro t ht g hg hgR
    have h1 := (GMSDichotomy.gmsSingerPermImage_normal h (X := X)).conj_mem ⟨t, hTH ht⟩
      (mem_subgroupOf.2 ht) ⟨g, GMSDichotomy.mem_gmsPermStabilizer.2 ⟨hg, hgR⟩⟩
    rw [mem_subgroupOf] at h1
    exact h1
  obtain ⟨hTcyc, hTcard⟩ := GMSDichotomy.isCyclic_gmsSingerPermImage h h3
  have hTodd : Odd (Nat.card (gmsSingerPermImage X U R)) := by
    rw [hTcard]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (Nat.even_pow.2 ⟨even_two, by omega⟩) odd_one
  obtain ⟨m, hm⟩ := hneven
  have hn2 : n / 2 = m := by omega
  have hsq : 2 ^ n = (2 ^ (n / 2)) ^ 2 := by
    rw [hn2, hm, ← pow_mul]
    ring_nf
  have hs4 : 4 ≤ 2 ^ (n / 2) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (n / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hτex : ∃! τ, τ ∈ gmsPairStabilizer U R β ∧ orderOf τ = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := gmsPairStabilizer U R β) 2
      (even_iff_two_dvd.1 hd)
    refine ⟨b, ⟨b.2, by rw [Subgroup.orderOf_coe, hb]⟩, ?_⟩
    rintro τ ⟨hτ, hτ2⟩
    exact congrArg Subtype.val (eq_of_orderOf_eq_two_of_isCyclic (a := ⟨τ, hτ⟩) (b := b)
      (by rw [Subgroup.orderOf_mk, hτ2]) hb)
  have hdecomp : ∀ x ∈ gmsPermStabilizer U R, ∃ t ∈ gmsSingerPermImage X U R,
      ∃ b ∈ gmsPairStabilizer U R β, x = t * b := by
    intro x hx
    obtain ⟨hxN, hxR⟩ := GMSDichotomy.mem_gmsPermStabilizer.1 hx
    obtain ⟨t, ht, b, ⟨hbN, hbR, hbβ⟩, hxtb⟩ :=
      exists_mul_of_singer hβR.symm hTN hTR hTtrans hxN hxR
    exact ⟨t, ht, b, mem_inf.2 ⟨GMSDichotomy.mem_gmsPermStabilizer.2 ⟨hbN, hbR⟩,
      MulAction.mem_stabilizer_iff.2 hbβ⟩, hxtb⟩
  have hsup : gmsSingerPermImage X U R ⊔ gmsPairStabilizer U R β = gmsPermStabilizer U R := by
    refine le_antisymm (sup_le hTH inf_le_left) fun x hx => ?_
    obtain ⟨t, ht, b, hb, rfl⟩ := hdecomp x hx
    exact mul_mem (mem_sup_left ht) (mem_sup_right hb)
  have hinf : gmsSingerPermImage X U R ⊓ gmsPairStabilizer U R β = ⊥ := by
    rw [eq_bot_iff]
    intro t ht
    exact hTfree t (mem_inf.1 ht).1 β hβR
      (MulAction.mem_stabilizer_iff.1 (mem_inf.1 (mem_inf.1 ht).2).2)
  refine ⟨hBcyc, hdecomp, hsup, hinf, hdn, hn4, ⟨m, hm⟩, hsq, hs4,
    ⟨K, inferInstance, inferInstance, inferInstance, hK, z, hz0, hz1,
      fun t ht => ⟨θ ⟨t, ht⟩, hzT ⟨t, ht⟩⟩,
      fun c => ⟨θ.symm c, (θ.symm c).2, fun x => by rw [hzT, MulEquiv.apply_symm_apply]⟩,
      γ, hγinj, hγ, hrange, hFk, fun τ hτ hτ2 => ⟨(hτfacts τ hτ hτ2).1, (hτfacts τ hτ hτ2).2.1⟩⟩,
    hτex, hρker, hπker, hCK, hkerU, hπY,
    GMSDichotomy.map_commutator_gmsRootConjugateAction (U ⊔ R) R,
    GMSDichotomy.ker_comp_commutator_subtype (U ⊔ R) R, fun τ hτ hτ2 => ?_⟩
  obtain ⟨-, -, hFcard, hpt, hCT⟩ := hτfacts τ hτ hτ2
  have hτH : τ ∈ gmsPermStabilizer U R := (mem_inf.1 hτ).1
  obtain ⟨hτN, hτR⟩ := GMSDichotomy.mem_gmsPermStabilizer.1 hτH
  have hτβ : τ β = β := MulAction.mem_stabilizer_iff.1 (mem_inf.1 hτ).2
  have hmemB : ∀ b, b ∈ (gmsRootConjugateAction (U ⊔ R) R).range → b ⟨R, gms_R_mem⟩ =
      ⟨R, gms_R_mem⟩ → b β = β → b ∈ gmsPairStabilizer U R β := fun b hb hbR hbβ =>
    mem_inf.2 ⟨GMSDichotomy.mem_gmsPermStabilizer.2 ⟨hb, hbR⟩, MulAction.mem_stabilizer_iff.2 hbβ⟩
  have hBuniq : ∀ b ∈ (gmsRootConjugateAction (U ⊔ R) R).range, b ⟨R, gms_R_mem⟩ =
      ⟨R, gms_R_mem⟩ → b β = β → orderOf b = 2 → b = τ := by
    intro b hb hbR hbβ hb2
    exact congrArg Subtype.val (eq_of_orderOf_eq_two_of_isCyclic
      (a := (⟨b, hmemB b hb hbR hbβ⟩ : gmsPairStabilizer U R β)) (b := ⟨τ, hτ⟩)
      (by rw [Subgroup.orderOf_mk, hb2]) (by rw [Subgroup.orderOf_mk, hτ2]))
  have hG : InvolutionGeometry (gmsRootConjugateAction (U ⊔ R) R).range τ ⟨R, gms_R_mem⟩ β
      (2 ^ (n / 2)) :=
    { two_trans := fun x y x' y' hxy hxy' => h2tr x y x' y' hxy hxy'
      ne := hβR.symm
      mem := hτN
      fix_left := hτR
      fix_right := hτβ
      orderOf_eq := hτ2
      unique := hBuniq
      card_fix := hFcard
      card := by rw [Nat.card_coe_set_eq, hΔcard, hsq]
      two_le := by omega
      even := Nat.even_pow.2 ⟨even_two, by omega⟩ }
  have hBc : ∀ b ∈ (gmsRootConjugateAction (U ⊔ R) R).range, b ⟨R, gms_R_mem⟩ =
      ⟨R, gms_R_mem⟩ → b β = β → b * τ = τ * b := by
    intro b hb hbR hbβ
    let _ : CommGroup (gmsPairStabilizer U R β) := IsCyclic.commGroup
    exact congrArg Subtype.val
      (mul_comm (⟨b, hmemB b hb hbR hbβ⟩ : gmsPairStabilizer U R β) ⟨τ, hτ⟩)
  have hCH := hG.eq_tau_of_singer hTN hTR hTn hTtrans hTfree hTodd
  have hBE : gmsPairStabilizer U R β ≤
      (gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ} := fun b hb => by
    obtain ⟨⟨hbN, hbR⟩, hbβ⟩ := hb
    exact mem_inf.2 ⟨hbN, mem_centralizer_singleton_iff.2 (hBc b hbN hbR hbβ)⟩
  have hstabκ : ∀ (e : ↥((gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ}))
      (x : ↥(Function.fixedPoints ⇑τ)),
      fixRestrict _ τ e ∈ MulAction.stabilizer (Equiv.Perm ↥(Function.fixedPoints ⇑τ)) x ↔
        (e : Equiv.Perm (gmsRootConjugates (U ⊔ R) R)) x = x := fun e x => by
    rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def, Subtype.ext_iff]
    rfl
  obtain ⟨hc, hc0⟩ := hG.ncard_switching
  have hcount := hG.centralizer_involutions hCH
  have hset : {v | v ∈ nonregInvolutions (gmsRootConjugateAction (U ⊔ R) R).range ∧
      v ∈ (gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ} ∧ v ≠ τ} =
      {v | v ∈ nonregInvolutions (gmsRootConjugateAction (U ⊔ R) R).range ∧ v * τ = τ * v ∧
        v ≠ τ} := by
    ext v
    simp only [Set.mem_ofPred_eq, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hv, ⟨-, hvc⟩, hne⟩
      exact ⟨hv, hvc, hne⟩
    · rintro ⟨hv, hvc, hne⟩
      exact ⟨hv, ⟨hv.1, hvc⟩, hne⟩
  rw [hset]
  let πE : ↥(((gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ}).comap
      (gmsRootConjugateAction (U ⊔ R) R)) →*
      ↥((gmsRootConjugateAction (U ⊔ R) R).range ⊓ centralizer {τ}) :=
    ((gmsRootConjugateAction (U ⊔ R) R).comp (Subgroup.subtype _)).codRestrict _ fun l => l.2
  let f : ↥((zpowers τ).comap (gmsRootConjugateAction (U ⊔ R) R)) →* ↥(zpowers τ) :=
    ((gmsRootConjugateAction (U ⊔ R) R).comp (Subgroup.subtype _)).codRestrict _ fun l => l.2
  have hfsurj : Function.Surjective f := by
    rintro ⟨w, hw⟩
    obtain ⟨l, hl⟩ := (zpowers_le.2 hτN) hw
    exact ⟨⟨l, show gmsRootConjugateAction (U ⊔ R) R l ∈ zpowers τ by rw [hl]; exact hw⟩,
      Subtype.ext hl⟩
  have hfker : f.ker = (gmsRootKernel (U ⊔ R) R).subgroupOf
      ((zpowers τ).comap (gmsRootConjugateAction (U ⊔ R) R)) := by
    ext l
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← hπker, MonoidHom.mem_ker, Subtype.ext_iff]
    rfl
  refine ⟨hFcard, fun x y hxy => hG.existsUnique_line hxy, fun ℓ hℓ => hG.ncard_line hℓ,
    hG.ncard_lines_through, hG.ncard_lines, fun ℓ hℓ x hx => hG.existsUnique_parallel hℓ hx,
    fun g hg ℓ hℓ => image_mem_permTranslates hg hℓ, fun g _ hg => Equiv.ext hg,
    fun x y x' y' hxy hxy' => h2tr x y x' y' hxy hxy', fun g hg => ?_,
    ⟨fixRestrict _ τ, fun e x => rfl, fun x y x' y' hxy hxy' => ?_, hG.ker_fixRestrict hpt,
      hG.ker_fixRestrict_eq_normalCore, fun g hg => hG.fixes_fix_iff hpt hg,
      QuotientGroup.kerLift_injective _, fun x y x' y' hxy hxy' => ?_,
      hG.card_quotient_fixRestrict hpt hBc, hBE, fun x y hx hy => ?_,
      isCyclic_map_mk _ hBE, hG.card_map_mk_mul_two hpt _ hBE hτ, ?_, fun x hx => ?_,
      Subgroup.isCyclic_of_le inf_le_left, hCT,
      hG.centralizer_singer_image hpt hTN hTR hTn hTfree hCT⟩,
    hG.card_centralizer hBc, fun x y hxy => ?_, hG.nonregInvolutions_eq, hG.ncard_nonreg,
    hG.bijOn_fixedPoints, by rw [hG.ncard_reg, ← hsq], fun w hw => hG.regInvolutions_eq hw,
    fun y hy => hG.existsUnique_reg hy, hcount.1, hcount.2.1, hcount.2.2, hc, hc0, ?_,
    ⟨(fixRestrict _ τ).comp πE, fun l x => rfl, ?_⟩, fun l hl => ?_,
    ⟨(QuotientGroup.quotientMulEquivOfEq hfker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hfsurj), fun l => rfl⟩⟩
  ·
    rw [mem_inf, mem_centralizer_singleton_iff, hG.image_fix_eq_iff hg]
    exact ⟨fun h1 => h1.2, fun h1 => ⟨hg, h1⟩⟩
  ·
    obtain ⟨g, hg, hgc, hgx, hgy⟩ := hG.two_trans_fix x.2 y.2 x'.2 y'.2
      (fun h1 => hxy (Subtype.ext h1)) (fun h1 => hxy' (Subtype.ext h1))
    exact ⟨⟨g, mem_inf.2 ⟨hg, mem_centralizer_singleton_iff.2 hgc⟩⟩, Subtype.ext hgx,
      Subtype.ext hgy⟩
  ·
    obtain ⟨g, hg, hgc, hgx, hgy⟩ := hG.two_trans_fix x.2 y.2 x'.2 y'.2
      (fun h1 => hxy (Subtype.ext h1)) (fun h1 => hxy' (Subtype.ext h1))
    exact ⟨QuotientGroup.mk ⟨g, mem_inf.2 ⟨hg, mem_centralizer_singleton_iff.2 hgc⟩⟩,
      Subtype.ext hgx, Subtype.ext hgy⟩
  ·
    refine comap_kerLift_eq _ _ fun e => ?_
    rw [mem_inf, hstabκ, hstabκ, hx, hy]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨(mem_inf.1 e.2).1, h1⟩, h2⟩
  ·
    obtain ⟨a, ha⟩ := hd
    rw [ha, hn2, show (a + a) / 2 = a by omega]
    rw [ha, hm] at hdn
    exact Nat.dvd_of_mul_dvd_mul_left two_pos (by rw [two_mul, two_mul]; exact hdn)
  ·
    refine comap_kerLift_eq _ _ fun e => ?_
    rw [hstabκ, hx]
    exact ⟨fun h1 => h1.2, fun h1 => ⟨(mem_inf.1 e.2).1, h1⟩⟩
  ·
    obtain ⟨v₁, hv₁, v₂, hv₂, h1, h2, h1x, h1y, h2x, h2y, hne, -, hfix, hreg, huniq⟩ :=
      hG.switching hxy
    exact ⟨v₁, hv₁, v₂, hv₂, h1, h2, h1x, h1y, h2x, h2y, hne, hfix, hreg.2.2, huniq⟩
  ·
    rw [hc, hc0, hsq]
    have : 1 ≤ 2 ^ (n / 2) := Nat.one_le_two_pow
    rw [show (2 - 1) * (2 ^ (n / 2) - 1) + 1 = 2 ^ (n / 2) by omega, sq]
  ·
    ext l
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hG.ker_fixRestrict hpt,
      mem_subgroupOf, mem_subgroupOf, mem_comap]
    rfl
  ·
    rw [← hπker, MonoidHom.mem_ker] at hl
    rw [mem_comap, hl]
    exact one_mem _

end CFSG.LocalAnalysis.SteinbergBX
