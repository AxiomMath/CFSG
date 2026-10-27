module

public import CFSG.Sporadic.Co2Rank3.Orbital
public import Mathlib.Algebra.BigOperators.Fin

public section

namespace CFSG.Sporadic.Co2Rank3

open MulAction
open scoped Pointwise

variable {G X : Type*} [Group G] [MulAction G X]

section Suborbits

variable [Finite G] [Finite X] {H : Subgroup G} {a b c : X}

omit [Finite G] [Finite X] in
theorem suborbit_facts (hb : (orbit (H ⊓ stabilizer G a : Subgroup G) b).ncard = 891)
    (hc : (orbit (H ⊓ stabilizer G a : Subgroup G) c).ncard = 1408) :
    a ∉ orbit (H ⊓ stabilizer G a : Subgroup G) b ∧
      a ∉ orbit (H ⊓ stabilizer G a : Subgroup G) c ∧
      Disjoint (orbit (H ⊓ stabilizer G a : Subgroup G) b)
        (orbit (H ⊓ stabilizer G a : Subgroup G) c) ∧ a ≠ b := by
  have ha : orbit (H ⊓ stabilizer G a : Subgroup G) a = {a} :=
    orbit_subgroup_eq_singleton fun k hk => mem_stabilizer_iff.1 hk.2
  have hab : a ∉ orbit (H ⊓ stabilizer G a : Subgroup G) b := fun h => by
    have := orbit_eq_of_mem h
    rw [ha] at this
    rw [← this, Set.ncard_singleton] at hb
    norm_num at hb
  refine ⟨hab, fun h => ?_, disjoint_orbit_of_ncard_ne (by rw [hb, hc]; norm_num), ?_⟩
  · have := orbit_eq_of_mem h
    rw [ha] at this
    rw [← this, Set.ncard_singleton] at hc
    norm_num at hc
  · rintro rfl
    exact hab (mem_orbit_self _)

omit [Finite X] in
theorem orbitalRel_swap_of_suborbits (htr : ∀ x, ∃ g ∈ H, g • a = x)
    (hcov : ∀ x, x = a ∨ x ∈ orbit (H ⊓ stabilizer G a : Subgroup G) b ∨
      x ∈ orbit (H ⊓ stabilizer G a : Subgroup G) c)
    (hb : (orbit (H ⊓ stabilizer G a : Subgroup G) b).ncard = 891)
    (hc : (orbit (H ⊓ stabilizer G a : Subgroup G) c).ncard = 1408) :
    orbitalRel H a b b a := by
  obtain ⟨-, -, -, hab⟩ := suborbit_facts hb hc
  obtain ⟨g, hg, hga⟩ := htr b
  have hsb : g⁻¹ • b = a := by rw [← hga, inv_smul_smul]
  have hlen := ncard_orbit_swap (H.inv_mem hg) hsb
  have hw : g⁻¹ • a ∈ orbit (H ⊓ stabilizer G a : Subgroup G) b := by
    rcases hcov (g⁻¹ • a) with h | h | h
    · exact absurd (MulAction.injective g⁻¹ (h.trans hsb.symm)) hab
    · exact h
    · rw [orbit_eq_of_mem h, hc, hb] at hlen
      norm_num at hlen
  obtain ⟨k, hk, hkb⟩ := mem_orbit_subgroup_iff.1 hw
  refine ⟨g * k, H.mul_mem hg hk.1, ?_, ?_⟩
  · rw [mul_smul, mem_stabilizer_iff.1 hk.2, hga]
  · rw [mul_smul, hkb, smul_inv_smul]

omit [Finite G] in
theorem false_of_orbitalNbr_subset (htr : ∀ x, ∃ g ∈ H, g • a = x)
    (hcov : ∀ x, x = a ∨ x ∈ orbit (H ⊓ stabilizer G a : Subgroup G) b ∨
      x ∈ orbit (H ⊓ stabilizer G a : Subgroup G) c)
    (hb : (orbit (H ⊓ stabilizer G a : Subgroup G) b).ncard = 891)
    (hc : (orbit (H ⊓ stabilizer G a : Subgroup G) c).ncard = 1408)
    (hsub : orbitalNbr H a b b ⊆ insert a (orbit (H ⊓ stabilizer G a : Subgroup G) b)) :
    False := by
  obtain ⟨haΔ, haΓ, hΔΓ, hab⟩ := suborbit_facts hb hc
  let B : X → Set X := fun x => insert x (orbitalNbr H a b x)
  have hBcard : ∀ x, (B x).ncard = 892 := fun x => by
    show (insert x (orbitalNbr H a b x)).ncard = 892
    rw [Set.ncard_insert_of_notMem (show x ∉ orbitalNbr H a b x from not_orbitalRel_self hab x)
      (Set.toFinite _),
      ncard_orbitalNbr htr, hb]
  have hBsmul : ∀ g ∈ H, ∀ x, B (g • x) = g • B x := fun g hg x => by
    simp only [B, Set.smul_set_insert, orbitalNbr_smul hg]
  have hBa : B a = insert a (orbit (H ⊓ stabilizer G a : Subgroup G) b) := by
    simp only [B, orbitalNbr_self]
  have hclosed_a : ∀ y ∈ B a, orbitalNbr H a b y ⊆ B a := by
    intro y hy
    rw [hBa] at hy ⊢
    rcases hy with rfl | hy
    · intro z hz
      exact Or.inr (mem_orbitalNbr_self.1 hz)
    · obtain ⟨k, hk, rfl⟩ := mem_orbit_subgroup_iff.1 hy
      rw [orbitalNbr_smul hk.1]
      rintro _ ⟨z, hz, rfl⟩
      rcases hsub hz with rfl | hz
      · exact Or.inl (mem_stabilizer_iff.1 hk.2)
      · exact Or.inr (smul_mem_orbit_subgroup hk hz)
  have hclosed : ∀ x, ∀ y ∈ B x, orbitalNbr H a b y ⊆ B x := by
    intro x y hy
    obtain ⟨g, hg, rfl⟩ := htr x
    rw [hBsmul g hg] at hy ⊢
    obtain ⟨y', hy', rfl⟩ := hy
    rw [orbitalNbr_smul hg]
    exact Set.smul_set_mono (hclosed_a y' hy')
  have hBeq : ∀ x, ∀ z ∈ B x, B z = B x := fun x z hz =>
    Set.eq_of_subset_of_ncard_le (Set.insert_subset hz (hclosed x z hz))
      (by rw [hBcard, hBcard]) (Set.toFinite _)
  have hdisj : ∀ x y, x ∉ B y → Disjoint (B x) (B y) := fun x y hx =>
    Set.disjoint_left.2 fun z hzx hzy => hx (by
      rw [← hBeq y z hzy, hBeq x z hzx]
      exact Set.mem_insert _ _)
  have hsubΓ : ∀ x, x ∉ B a → B x ⊆ orbit (H ⊓ stabilizer G a : Subgroup G) c := by
    intro x hx y hy
    have hya : y ∉ B a := Set.disjoint_left.1 (hdisj x a hx) hy
    rw [hBa] at hya
    rcases hcov y with rfl | h | h
    · exact absurd (Set.mem_insert _ _) hya
    · exact absurd (Set.mem_insert_of_mem _ h) hya
    · exact h
  have hnotBa : ∀ x ∈ orbit (H ⊓ stabilizer G a : Subgroup G) c, x ∉ B a := by
    intro x hx hxa
    rw [hBa] at hxa
    rcases hxa with rfl | hxa
    · exact haΓ hx
    · exact Set.disjoint_left.1 hΔΓ hxa hx
  have hcΓ : c ∈ orbit (H ⊓ stabilizer G a : Subgroup G) c := mem_orbit_self c
  obtain ⟨z, hzΓ, hzc⟩ : ∃ z ∈ orbit (H ⊓ stabilizer G a : Subgroup G) c, z ∉ B c := by
    by_contra h
    have h' : orbit (H ⊓ stabilizer G a : Subgroup G) c ⊆ B c := fun z hz => by
      by_contra hz'
      exact h ⟨z, hz, hz'⟩
    have := Set.ncard_le_ncard h' (Set.toFinite _)
    rw [hc, hBcard] at this
    norm_num at this
  have hle := Set.ncard_le_ncard (Set.union_subset (hsubΓ z (hnotBa z hzΓ))
    (hsubΓ c (hnotBa c hcΓ))) (Set.toFinite _)
  rw [Set.ncard_union_eq (hdisj z c hzc) (Set.toFinite _) (Set.toFinite _), hBcard, hBcard,
    hc] at hle
  norm_num at hle

omit [Finite G] in
theorem false_of_orbitalNbr_eq (htr : ∀ x, ∃ g ∈ H, g • a = x)
    (hb : (orbit (H ⊓ stabilizer G a : Subgroup G) b).ncard = 891)
    (hc : (orbit (H ⊓ stabilizer G a : Subgroup G) c).ncard = 1408)
    (hswap : orbitalRel H a b b a)
    (heq : orbitalNbr H a b c = orbit (H ⊓ stabilizer G a : Subgroup G) b) : False := by
  obtain ⟨-, haΓ, -, -⟩ := suborbit_facts hb hc
  have hall : ∀ x ∈ orbit (H ⊓ stabilizer G a : Subgroup G) c, orbitalRel H a b b x := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := mem_orbit_subgroup_iff.1 hx
    have hb' : b ∈ orbitalNbr H a b (k • c) := by
      rw [orbitalNbr_smul hk.1, heq, Set.mem_smul_set_iff_inv_smul_mem]
      exact smul_mem_orbit_subgroup (Subgroup.inv_mem _ hk) (mem_orbit_self b)
    exact orbitalRel_symm hswap hb'
  have hsub : insert a (orbit (H ⊓ stabilizer G a : Subgroup G) c) ⊆ orbitalNbr H a b b := by
    rintro x (rfl | hx)
    · exact hswap
    · exact hall x hx
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [Set.ncard_insert_of_notMem haΓ (Set.toFinite _), hc, ncard_orbitalNbr htr, hb] at hle
  norm_num at hle

omit [Finite G] in
theorem ncard_eq_sum_ncard_orbits {N : Subgroup G} {k : ℕ} {r : Fin k → X}
    (hne : ∀ i j, i ≠ j → orbit N (r i) ≠ orbit N (r j)) (hcov : ∀ x, ∃ i, x ∈ orbit N (r i))
    (S : Set X) : S.ncard = ∑ i, (S ∩ orbit N (r i)).ncard :=
  ncard_eq_sum_ncard_inter _ (fun i j hij => (orbit.eq_or_disjoint _ _).resolve_left
    (hne i j hij)) hcov S

theorem orbitalRel_b_iff (htr : ∀ x, ∃ g ∈ H, g • a = x)
    (hcov : ∀ x, x = a ∨ x ∈ orbit (H ⊓ stabilizer G a : Subgroup G) b ∨
      x ∈ orbit (H ⊓ stabilizer G a : Subgroup G) c)
    (hb : (orbit (H ⊓ stabilizer G a : Subgroup G) b).ncard = 891)
    (hc : (orbit (H ⊓ stabilizer G a : Subgroup G) c).ncard = 1408)
    {N : Subgroup G} (hN : N ≤ H ⊓ stabilizer G a ⊓ stabilizer G b) {d₁ d₂ d₃ d₄ d₅ : X}
    (hNcov : ∀ x, x = a ∨ x = b ∨ x ∈ orbit N d₁ ∨ x ∈ orbit N d₂ ∨ x ∈ orbit N d₃ ∨
      x ∈ orbit N d₄ ∨ x ∈ orbit N d₅)
    (h₁ : (orbit N d₁).ncard = 42) (h₂ : (orbit N d₂).ncard = 336)
    (h₃ : (orbit N d₃).ncard = 512) (h₄ : (orbit N d₄).ncard = 512)
    (h₅ : (orbit N d₅).ncard = 896)
    (hd₁ : d₁ ∈ orbit (H ⊓ stabilizer G a : Subgroup G) b)
    (hd₂ : d₂ ∈ orbit (H ⊓ stabilizer G a : Subgroup G) b)
    (hd₃ : d₃ ∈ orbit (H ⊓ stabilizer G a : Subgroup G) b)
    (hd₄ : d₄ ∈ orbit (H ⊓ stabilizer G a : Subgroup G) c) (y : X) :
    orbitalRel H a b b y ↔ y = a ∨ y ∈ orbit N d₁ ∨ y ∈ orbit N d₂ ∨ y ∈ orbit N d₄ := by
  obtain ⟨-, -, hΔΓ, hab⟩ := suborbit_facts hb hc
  have hswap := orbitalRel_swap_of_suborbits htr hcov hb hc
  have hNa : orbit N a = {a} :=
    orbit_subgroup_eq_singleton fun n hn => mem_stabilizer_iff.1 (hN hn).1.2
  have hNb : orbit N b = {b} :=
    orbit_subgroup_eq_singleton fun n hn => mem_stabilizer_iff.1 (hN hn).2
  have hloc : ∀ {d e : X}, d ∈ orbit (H ⊓ stabilizer G a : Subgroup G) e →
      orbit N d ⊆ orbit (H ⊓ stabilizer G a : Subgroup G) e := fun hd =>
    (orbit_subgroup_mono (le_trans hN inf_le_left) _).trans (orbit_eq_of_mem hd).subset
  have hinv : ∀ n ∈ N, ∀ y : X, n • y ∈ orbitalNbr H a b b ↔ y ∈ orbitalNbr H a b b := by
    intro n hn y
    have hnb : n • b = b := mem_stabilizer_iff.1 (hN hn).2
    rw [mem_orbitalNbr, mem_orbitalNbr]
    have h := orbitalRel_smul_iff (H := H) (a := a) (b := b) (hN hn).1.1 (x := b) (y := y)
    rwa [hnb] at h
  have haS : a ∈ orbitalNbr H a b b := hswap
  have hbS : b ∉ orbitalNbr H a b b := not_orbitalRel_self hab b
  let r : Fin 7 → X := ![a, b, d₁, d₂, d₃, d₄, d₅]
  have hsz : ∀ i, (orbit N (r i)).ncard = ![1, 1, 42, 336, 512, 512, 896] i := by
    intro i
    fin_cases i <;> simp [r, hNa, hNb, h₁, h₂, h₃, h₄, h₅]
  have hne : ∀ i j, i ≠ j → orbit N (r i) ≠ orbit N (r j) := by
    intro i j hij he
    have hs := congrArg Set.ncard he
    rw [hsz, hsz] at hs
    fin_cases i <;> fin_cases j <;> simp at hs hij <;> simp only [r] at he <;>
      simp at he
    · rw [hNa, hNb, Set.singleton_eq_singleton_iff] at he
      exact hab he
    · rw [hNa, hNb, Set.singleton_eq_singleton_iff] at he
      exact hab he.symm
    · exact Set.disjoint_left.1 hΔΓ (hloc hd₃ (he ▸ mem_orbit_self d₄)) hd₄
    · exact Set.disjoint_left.1 hΔΓ (hloc hd₃ (by rw [← he]; exact mem_orbit_self d₄)) hd₄
  have hcovr : ∀ x, ∃ i, x ∈ orbit N (r i) := by
    intro x
    rcases hNcov x with rfl | rfl | h | h | h | h | h
    · exact ⟨0, mem_orbit_self _⟩
    · exact ⟨1, mem_orbit_self _⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
    · exact ⟨5, h⟩
    · exact ⟨6, h⟩
  have hcount := ncard_eq_sum_ncard_orbits hne hcovr (orbitalNbr H a b b)
  rw [Fin.sum_univ_seven] at hcount
  simp only [r, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hNa, hNb,
    Set.inter_singleton_of_mem haS, Set.inter_singleton_eq_empty.2 hbS, Set.ncard_singleton,
    Set.ncard_empty, ncard_orbitalNbr htr, hb] at hcount
  have c₁ := ncard_inter_orbit hinv d₁
  have c₂ := ncard_inter_orbit hinv d₂
  have c₃ := ncard_inter_orbit hinv d₃
  have c₄ := ncard_inter_orbit hinv d₄
  have c₅ := ncard_inter_orbit hinv d₅
  rw [h₁] at c₁
  rw [h₂] at c₂
  rw [h₃] at c₃
  rw [h₄] at c₄
  rw [h₅] at c₅
  have key : (orbitalNbr H a b b ∩ orbit N d₁).ncard = 42 ∧
      (orbitalNbr H a b b ∩ orbit N d₂).ncard = 336 ∧
      (orbitalNbr H a b b ∩ orbit N d₅).ncard = 0 ∧
      (((orbitalNbr H a b b ∩ orbit N d₃).ncard = 512 ∧
        (orbitalNbr H a b b ∩ orbit N d₄).ncard = 0) ∨
       ((orbitalNbr H a b b ∩ orbit N d₃).ncard = 0 ∧
        (orbitalNbr H a b b ∩ orbit N d₄).ncard = 512)) := by
    rcases c₁ with ⟨-, c₁⟩ | ⟨-, c₁⟩ <;> rcases c₂ with ⟨-, c₂⟩ | ⟨-, c₂⟩ <;>
      rcases c₃ with ⟨-, c₃⟩ | ⟨-, c₃⟩ <;> rcases c₄ with ⟨-, c₄⟩ | ⟨-, c₄⟩ <;>
      rcases c₅ with ⟨-, c₅⟩ | ⟨-, c₅⟩ <;> omega
  obtain ⟨k₁, k₂, k₅, k₃₄⟩ := key
  have sub₁ : orbit N d₁ ⊆ orbitalNbr H a b b := by
    rcases c₁ with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · omega
  have sub₂ : orbit N d₂ ⊆ orbitalNbr H a b b := by
    rcases c₂ with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · omega
  have dis₅ : Disjoint (orbit N d₅) (orbitalNbr H a b b) := by
    rcases c₅ with ⟨-, h⟩ | ⟨h, -⟩
    · omega
    · exact h
  rcases k₃₄ with ⟨k₃, k₄⟩ | ⟨k₃, k₄⟩
  · exfalso
    have dis₄ : Disjoint (orbit N d₄) (orbitalNbr H a b b) := by
      rcases c₄ with ⟨-, h⟩ | ⟨h, -⟩
      · omega
      · exact h
    refine false_of_orbitalNbr_subset htr hcov hb hc fun z hz => ?_
    rcases hNcov z with rfl | rfl | h | h | h | h | h
    · exact Set.mem_insert _ _
    · exact absurd hz hbS
    · exact Set.mem_insert_of_mem _ (hloc hd₁ h)
    · exact Set.mem_insert_of_mem _ (hloc hd₂ h)
    · exact Set.mem_insert_of_mem _ (hloc hd₃ h)
    · exact absurd hz (Set.disjoint_left.1 dis₄ h)
    · exact absurd hz (Set.disjoint_left.1 dis₅ h)
  · have dis₃ : Disjoint (orbit N d₃) (orbitalNbr H a b b) := by
      rcases c₃ with ⟨-, h⟩ | ⟨h, -⟩
      · omega
      · exact h
    have sub₄ : orbit N d₄ ⊆ orbitalNbr H a b b := by
      rcases c₄ with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · omega
    constructor
    · intro hy
      have hy' : y ∈ orbitalNbr H a b b := hy
      rcases hNcov y with rfl | rfl | h | h | h | h | h
      · exact Or.inl rfl
      · exact absurd hy' hbS
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact absurd hy' (Set.disjoint_left.1 dis₃ h)
      · exact Or.inr (Or.inr (Or.inr h))
      · exact absurd hy' (Set.disjoint_left.1 dis₅ h)
    · rintro (rfl | h | h | h)
      · exact haS
      · exact sub₁ h
      · exact sub₂ h
      · exact sub₄ h

theorem orbitalRel_c_iff (htr : ∀ x, ∃ g ∈ H, g • a = x)
    (hcov : ∀ x, x = a ∨ x ∈ orbit (H ⊓ stabilizer G a : Subgroup G) b ∨
      x ∈ orbit (H ⊓ stabilizer G a : Subgroup G) c)
    (hb : (orbit (H ⊓ stabilizer G a : Subgroup G) b).ncard = 891)
    (hc : (orbit (H ⊓ stabilizer G a : Subgroup G) c).ncard = 1408)
    {M : Subgroup G} (hM : M ≤ H ⊓ stabilizer G a ⊓ stabilizer G c) {e₁ e₂ e₃ e₄ : X}
    (hMcov : ∀ x, x = a ∨ x = c ∨ x ∈ orbit M e₁ ∨ x ∈ orbit M e₂ ∨ x ∈ orbit M e₃ ∨
      x ∈ orbit M e₄)
    (h₁ : (orbit M e₁).ncard = 324) (h₂ : (orbit M e₂).ncard = 567)
    (h₃ : (orbit M e₃).ncard = 567) (h₄ : (orbit M e₄).ncard = 840)
    (he₁ : e₁ ∈ orbit (H ⊓ stabilizer G a : Subgroup G) b)
    (he₂ : e₂ ∈ orbit (H ⊓ stabilizer G a : Subgroup G) b)
    (he₃ : e₃ ∈ orbit (H ⊓ stabilizer G a : Subgroup G) c) (y : X) :
    orbitalRel H a b c y ↔ y ∈ orbit M e₁ ∨ y ∈ orbit M e₃ := by
  obtain ⟨-, haΓ, hΔΓ, -⟩ := suborbit_facts hb hc
  have hswap := orbitalRel_swap_of_suborbits htr hcov hb hc
  have hcΓ : c ∈ orbit (H ⊓ stabilizer G a : Subgroup G) c := mem_orbit_self c
  have hac : a ≠ c := fun h => haΓ (h ▸ hcΓ)
  have hMa : orbit M a = {a} :=
    orbit_subgroup_eq_singleton fun n hn => mem_stabilizer_iff.1 (hM hn).1.2
  have hMc : orbit M c = {c} :=
    orbit_subgroup_eq_singleton fun n hn => mem_stabilizer_iff.1 (hM hn).2
  have hloc : ∀ {d e : X}, d ∈ orbit (H ⊓ stabilizer G a : Subgroup G) e →
      orbit M d ⊆ orbit (H ⊓ stabilizer G a : Subgroup G) e := fun hd =>
    (orbit_subgroup_mono (le_trans hM inf_le_left) _).trans (orbit_eq_of_mem hd).subset
  have hinv : ∀ n ∈ M, ∀ y : X, n • y ∈ orbitalNbr H a b c ↔ y ∈ orbitalNbr H a b c := by
    intro n hn y
    have hnc : n • c = c := mem_stabilizer_iff.1 (hM hn).2
    rw [mem_orbitalNbr, mem_orbitalNbr]
    have h := orbitalRel_smul_iff (H := H) (a := a) (b := b) (hM hn).1.1 (x := c) (y := y)
    rwa [hnc] at h
  have haS : a ∉ orbitalNbr H a b c := fun h =>
    Set.disjoint_left.1 hΔΓ (mem_orbitalNbr_self.1 (orbitalRel_symm hswap h)) hcΓ
  have hcS : c ∉ orbitalNbr H a b c := not_orbitalRel_self (suborbit_facts hb hc).2.2.2 c
  let r : Fin 6 → X := ![a, c, e₁, e₂, e₃, e₄]
  have hsz : ∀ i, (orbit M (r i)).ncard = ![1, 1, 324, 567, 567, 840] i := by
    intro i
    fin_cases i <;> simp [r, hMa, hMc, h₁, h₂, h₃, h₄]
  have hne : ∀ i j, i ≠ j → orbit M (r i) ≠ orbit M (r j) := by
    intro i j hij he
    have hs := congrArg Set.ncard he
    rw [hsz, hsz] at hs
    fin_cases i <;> fin_cases j <;> simp at hs hij <;> simp only [r] at he <;>
      simp at he
    · rw [hMa, hMc, Set.singleton_eq_singleton_iff] at he
      exact hac he
    · rw [hMa, hMc, Set.singleton_eq_singleton_iff] at he
      exact hac he.symm
    · exact Set.disjoint_left.1 hΔΓ (hloc he₂ (he ▸ mem_orbit_self e₃)) he₃
    · exact Set.disjoint_left.1 hΔΓ (hloc he₂ (by rw [← he]; exact mem_orbit_self e₃)) he₃
  have hcovr : ∀ x, ∃ i, x ∈ orbit M (r i) := by
    intro x
    rcases hMcov x with rfl | rfl | h | h | h | h
    · exact ⟨0, mem_orbit_self _⟩
    · exact ⟨1, mem_orbit_self _⟩
    · exact ⟨2, h⟩
    · exact ⟨3, h⟩
    · exact ⟨4, h⟩
    · exact ⟨5, h⟩
  have hcount := ncard_eq_sum_ncard_orbits hne hcovr (orbitalNbr H a b c)
  rw [Fin.sum_univ_six] at hcount
  simp only [r, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hMa, hMc,
    Set.inter_singleton_eq_empty.2 haS, Set.inter_singleton_eq_empty.2 hcS,
    Set.ncard_empty, ncard_orbitalNbr htr, hb] at hcount
  have c₁ := ncard_inter_orbit hinv e₁
  have c₂ := ncard_inter_orbit hinv e₂
  have c₃ := ncard_inter_orbit hinv e₃
  have c₄ := ncard_inter_orbit hinv e₄
  rw [h₁] at c₁
  rw [h₂] at c₂
  rw [h₃] at c₃
  rw [h₄] at c₄
  have key : (orbitalNbr H a b c ∩ orbit M e₁).ncard = 324 ∧
      (orbitalNbr H a b c ∩ orbit M e₄).ncard = 0 ∧
      (((orbitalNbr H a b c ∩ orbit M e₂).ncard = 567 ∧
        (orbitalNbr H a b c ∩ orbit M e₃).ncard = 0) ∨
       ((orbitalNbr H a b c ∩ orbit M e₂).ncard = 0 ∧
        (orbitalNbr H a b c ∩ orbit M e₃).ncard = 567)) := by
    rcases c₁ with ⟨-, c₁⟩ | ⟨-, c₁⟩ <;> rcases c₂ with ⟨-, c₂⟩ | ⟨-, c₂⟩ <;>
      rcases c₃ with ⟨-, c₃⟩ | ⟨-, c₃⟩ <;> rcases c₄ with ⟨-, c₄⟩ | ⟨-, c₄⟩ <;> omega
  obtain ⟨k₁, k₄, k₂₃⟩ := key
  have sub₁ : orbit M e₁ ⊆ orbitalNbr H a b c := by
    rcases c₁ with ⟨h, -⟩ | ⟨-, h⟩
    · exact h
    · omega
  have dis₄ : Disjoint (orbit M e₄) (orbitalNbr H a b c) := by
    rcases c₄ with ⟨-, h⟩ | ⟨h, -⟩
    · omega
    · exact h
  rcases k₂₃ with ⟨k₂, k₃⟩ | ⟨k₂, k₃⟩
  · exfalso
    have dis₃ : Disjoint (orbit M e₃) (orbitalNbr H a b c) := by
      rcases c₃ with ⟨-, h⟩ | ⟨h, -⟩
      · omega
      · exact h
    have hsub : orbitalNbr H a b c ⊆ orbit (H ⊓ stabilizer G a : Subgroup G) b := by
      intro z hz
      rcases hMcov z with rfl | rfl | h | h | h | h
      · exact absurd hz haS
      · exact absurd hz hcS
      · exact hloc he₁ h
      · exact hloc he₂ h
      · exact absurd hz (Set.disjoint_left.1 dis₃ h)
      · exact absurd hz (Set.disjoint_left.1 dis₄ h)
    refine false_of_orbitalNbr_eq htr hb hc hswap
      (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _))
    rw [hb, ncard_orbitalNbr htr, hb]
  · have dis₂ : Disjoint (orbit M e₂) (orbitalNbr H a b c) := by
      rcases c₂ with ⟨-, h⟩ | ⟨h, -⟩
      · omega
      · exact h
    have sub₃ : orbit M e₃ ⊆ orbitalNbr H a b c := by
      rcases c₃ with ⟨h, -⟩ | ⟨-, h⟩
      · exact h
      · omega
    constructor
    · intro hy
      have hy' : y ∈ orbitalNbr H a b c := hy
      rcases hMcov y with rfl | rfl | h | h | h | h
      · exact absurd hy' haS
      · exact absurd hy' hcS
      · exact Or.inl h
      · exact absurd hy' (Set.disjoint_left.1 dis₂ h)
      · exact Or.inr h
      · exact absurd hy' (Set.disjoint_left.1 dis₄ h)
    · rintro (h | h)
      · exact sub₁ h
      · exact sub₃ h

theorem orbitalRel_co2_suborbits (htr : ∀ x, ∃ g ∈ H, g • a = x)
    (hcov : ∀ x, x = a ∨ x ∈ orbit (H ⊓ stabilizer G a : Subgroup G) b ∨
      x ∈ orbit (H ⊓ stabilizer G a : Subgroup G) c)
    (hb : (orbit (H ⊓ stabilizer G a : Subgroup G) b).ncard = 891)
    (hc : (orbit (H ⊓ stabilizer G a : Subgroup G) c).ncard = 1408)
    {N : Subgroup G} (hN : N ≤ H ⊓ stabilizer G a ⊓ stabilizer G b) {d₁ d₂ d₃ d₄ d₅ : X}
    (hNcov : ∀ x, x = a ∨ x = b ∨ x ∈ orbit N d₁ ∨ x ∈ orbit N d₂ ∨ x ∈ orbit N d₃ ∨
      x ∈ orbit N d₄ ∨ x ∈ orbit N d₅)
    (hN₁ : (orbit N d₁).ncard = 42) (hN₂ : (orbit N d₂).ncard = 336)
    (hN₃ : (orbit N d₃).ncard = 512) (hN₄ : (orbit N d₄).ncard = 512)
    (hN₅ : (orbit N d₅).ncard = 896)
    (hd₁ : d₁ ∈ orbit (H ⊓ stabilizer G a : Subgroup G) b)
    (hd₂ : d₂ ∈ orbit (H ⊓ stabilizer G a : Subgroup G) b)
    (hd₃ : d₃ ∈ orbit (H ⊓ stabilizer G a : Subgroup G) b)
    (hd₄ : d₄ ∈ orbit (H ⊓ stabilizer G a : Subgroup G) c)
    {M : Subgroup G} (hM : M ≤ H ⊓ stabilizer G a ⊓ stabilizer G c) {e₁ e₂ e₃ e₄ : X}
    (hMcov : ∀ x, x = a ∨ x = c ∨ x ∈ orbit M e₁ ∨ x ∈ orbit M e₂ ∨ x ∈ orbit M e₃ ∨
      x ∈ orbit M e₄)
    (hM₁ : (orbit M e₁).ncard = 324) (hM₂ : (orbit M e₂).ncard = 567)
    (hM₃ : (orbit M e₃).ncard = 567) (hM₄ : (orbit M e₄).ncard = 840)
    (he₁ : e₁ ∈ orbit (H ⊓ stabilizer G a : Subgroup G) b)
    (he₂ : e₂ ∈ orbit (H ⊓ stabilizer G a : Subgroup G) b)
    (he₃ : e₃ ∈ orbit (H ⊓ stabilizer G a : Subgroup G) c) :
    (∀ x y, orbitalRel H a b x y → orbitalRel H a b y x) ∧
      (∀ y, orbitalRel H a b a y ↔ y ∈ orbit (H ⊓ stabilizer G a : Subgroup G) b) ∧
      (∀ y, orbitalRel H a b b y ↔ y = a ∨ y ∈ orbit N d₁ ∨ y ∈ orbit N d₂ ∨
        y ∈ orbit N d₄) ∧
      (∀ y, orbitalRel H a b c y ↔ y ∈ orbit M e₁ ∨ y ∈ orbit M e₃) :=
  ⟨fun _ _ => orbitalRel_symm (orbitalRel_swap_of_suborbits htr hcov hb hc),
    fun _ => mem_orbitalNbr_self,
    orbitalRel_b_iff htr hcov hb hc hN hNcov hN₁ hN₂ hN₃ hN₄ hN₅ hd₁ hd₂ hd₃ hd₄,
    orbitalRel_c_iff htr hcov hb hc hM hMcov hM₁ hM₂ hM₃ hM₄ he₁ he₂ he₃⟩

end Suborbits

end CFSG.Sporadic.Co2Rank3
