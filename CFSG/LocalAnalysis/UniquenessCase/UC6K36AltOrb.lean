module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36AltGen
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Alt36

open Equiv Equiv.Perm

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

@[expose] noncomputable def fixE (E : Subgroup (Perm Ω)) : Finset Ω := by
  classical exact Finset.univ.filter fun x => ∀ e ∈ E, e x = x

@[expose] def stb (E : Subgroup (Perm Ω)) (x : Ω) : Subgroup (Perm Ω) :=
  E ⊓ MulAction.stabilizer (Perm Ω) x

@[expose] noncomputable def kfix (E : Subgroup (Perm Ω)) (x : Ω) : Finset Ω := by
  classical exact Finset.univ.filter fun y => ∀ e ∈ E, e x = x → e y = y

@[expose] noncomputable def orb (E : Subgroup (Perm Ω)) (x : Ω) : Finset Ω := by
  classical exact Finset.univ.filter fun y => ∃ e ∈ E, e x = y

@[expose] def centClosure (E : Subgroup (Perm Ω)) : Subgroup (Perm Ω) :=
  Subgroup.closure {g | g ∈ alternatingGroup Ω ∧ ∃ e ∈ E, e ≠ 1 ∧ g * e = e * g}

theorem mem_fixE {E : Subgroup (Perm Ω)} {x : Ω} : x ∈ fixE E ↔ ∀ e ∈ E, e x = x := by
  classical
  unfold fixE
  rw [Finset.mem_filter]
  simp

theorem mem_stb {E : Subgroup (Perm Ω)} {x : Ω} {e : Perm Ω} : e ∈ stb E x ↔ e ∈ E ∧ e x = x := by
  simp [stb, MulAction.mem_stabilizer_iff]

theorem mem_kfix {E : Subgroup (Perm Ω)} {x y : Ω} : y ∈ kfix E x ↔ ∀ e ∈ E, e x = x → e y = y := by
  classical
  unfold kfix
  rw [Finset.mem_filter]
  simp

theorem mem_orb {E : Subgroup (Perm Ω)} {x y : Ω} : y ∈ orb E x ↔ ∃ e ∈ E, e x = y := by
  classical
  unfold orb
  rw [Finset.mem_filter]
  simp

section Plane

variable {p : ℕ} {E : Subgroup (Perm Ω)}

theorem comm_of_elem (hE : CFSG.Open.IsElemAbelian p E) {a b : Perm Ω} (ha : a ∈ E) (hb : b ∈ E) :
    a * b = b * a := by
  haveI := hE.1
  exact congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : ↥E) ⟨b, hb⟩)

theorem stb_apply (hE : CFSG.Open.IsElemAbelian p E) {g : Perm Ω} (hg : g ∈ E) (x : Ω) :
    stb E (g x) = stb E x := by
  ext k
  rw [mem_stb, mem_stb]
  refine and_congr_right fun hk => ?_
  have hkg : k * g = g * k := comm_of_elem hE hk hg
  constructor
  · intro h
    have h1 : g (k x) = g x := by
      have := congrArg (fun f : Perm Ω => f x) hkg
      simp only [Perm.coe_mul, Function.comp_apply] at this
      rw [← this, h]
    exact g.injective h1
  · intro h
    have := congrArg (fun f : Perm Ω => f x) hkg
    simp only [Perm.coe_mul, Function.comp_apply] at this
    rw [this, h]

theorem card_stb (hp : p.Prime) (hEc : Nat.card E = p ^ 2) (x : Ω) :
    Nat.card (stb E x) = 1 ∨ Nat.card (stb E x) = p ∨ Nat.card (stb E x) = p ^ 2 := by
  have hd : Nat.card (stb E x) ∣ p ^ 2 := hEc ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk, hkx⟩ := (Nat.dvd_prime_pow hp).1 hd
  interval_cases k <;> simp_all

theorem mem_fixE_iff_card (hEc : Nat.card E = p ^ 2) {x : Ω} :
    x ∈ fixE E ↔ Nat.card (stb E x) = p ^ 2 := by
  constructor
  · intro hx
    have : stb E x = E := le_antisymm inf_le_left fun e he => mem_stb.2 ⟨he, mem_fixE.1 hx e he⟩
    rw [this, hEc]
  · intro hc
    have hle : stb E x ≤ E := inf_le_left
    have : stb E x = E := Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hEc])
    refine mem_fixE.2 fun e he => ?_
    have he' : e ∈ stb E x := by rw [this]; exact he
    exact (mem_stb.1 he').2

theorem fixE_subset_kfix (x : Ω) : fixE E ⊆ kfix E x := fun y hy =>
  mem_kfix.2 fun e he _ => mem_fixE.1 hy e he

theorem orb_subset_kfix (hE : CFSG.Open.IsElemAbelian p E) (x : Ω) : orb E x ⊆ kfix E x := by
  intro y hy
  obtain ⟨g, hg, rfl⟩ := mem_orb.1 hy
  refine mem_kfix.2 fun e he hex => ?_
  have h := (stb_apply hE hg x).symm ▸ (mem_stb.2 ⟨he, hex⟩ : e ∈ stb E x)
  exact (mem_stb.1 h).2

theorem mem_orb_self (x : Ω) : x ∈ orb E x := mem_orb.2 ⟨1, E.one_mem, rfl⟩

theorem disjoint_orb_kfix (hE : CFSG.Open.IsElemAbelian p E) {x x' : Ω} (hx : Nat.card (stb E x) = p)
    (hx' : Nat.card (stb E x') = p) (hne : kfix E x' ≠ kfix E x) : Disjoint (orb E x) (kfix E x') := by
  rw [Finset.disjoint_left]
  intro y hy hy'
  obtain ⟨g, hg, rfl⟩ := mem_orb.1 hy
  have hle : stb E x' ≤ stb E x := by
    intro e he
    rw [← stb_apply hE hg x]
    exact mem_stb.2 ⟨(mem_stb.1 he).1, mem_kfix.1 hy' e (mem_stb.1 he).1 (mem_stb.1 he).2⟩
  have heq : stb E x' = stb E x := Subgroup.eq_of_le_of_card_ge hle (by rw [hx, hx'])
  apply hne
  ext y
  rw [mem_kfix, mem_kfix]
  refine forall₂_congr fun e he => ?_
  have h1 : e x' = x' ↔ e x = x := by
    constructor
    · intro h
      have h' : e ∈ stb E x' := mem_stb.2 ⟨he, h⟩
      rw [heq] at h'
      exact (mem_stb.1 h').2
    · intro h
      have h' : e ∈ stb E x := mem_stb.2 ⟨he, h⟩
      rw [← heq] at h'
      exact (mem_stb.1 h').2
  rw [h1]

theorem card_orb_mul_card_stb (x : Ω) : (orb E x).card * Nat.card (stb E x) = Nat.card E := by
  have h1 := MulAction.index_stabilizer (↥E) x
  have h2 := Subgroup.index_mul_card (MulAction.stabilizer (↥E) x)
  have h3 : MulAction.orbit (↥E) x = ((orb E x : Finset Ω) : Set Ω) := by
    ext y
    rw [MulAction.mem_orbit_iff, Finset.mem_coe, mem_orb]
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, g.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have h4 : (MulAction.stabilizer (↥E) x).map E.subtype = stb E x := by
    ext g
    rw [Subgroup.mem_map, mem_stb]
    constructor
    · rintro ⟨g', hg', rfl⟩
      exact ⟨g'.2, MulAction.mem_stabilizer_iff.1 hg'⟩
    · rintro ⟨hg, hgx⟩
      exact ⟨⟨g, hg⟩, MulAction.mem_stabilizer_iff.2 hgx, rfl⟩
  have h5 : Nat.card (stb E x) = Nat.card (MulAction.stabilizer (↥E) x) := by
    rw [← h4, Subgroup.card_map_of_injective E.subtype_injective]
  rw [h5, ← h2, h1, h3, Set.ncard_coe_finset]

theorem le_card_orb (hp : p.Prime) (hEc : Nat.card E = p ^ 2) {x : Ω} (hx : x ∉ fixE E) :
    p ≤ (orb E x).card := by
  have h := card_orb_mul_card_stb (E := E) x
  rw [hEc] at h
  have hne : Nat.card (stb E x) ≠ p ^ 2 := fun h' => hx ((mem_fixE_iff_card hEc).2 h')
  rcases card_stb hp hEc x with h1 | h1 | h1
  · rw [h1, mul_one] at h
    rw [h]
    exact Nat.le_self_pow two_ne_zero p
  · rw [h1, pow_two] at h
    rw [Nat.eq_of_mul_eq_mul_right hp.pos h]
  · exact absurd h1 hne

theorem card_orb_of_card_stb_one (hEc : Nat.card E = p ^ 2) {x : Ω} (hx : Nat.card (stb E x) = 1) :
    (orb E x).card = p ^ 2 := by
  have h := card_orb_mul_card_stb (E := E) x
  rwa [hx, mul_one, hEc] at h

theorem three_le_of_odd_prime (hp : p.Prime) (hp2 : p ≠ 2) : 3 ≤ p := by
  have := hp.two_le
  omega

theorem exists_not_mem_fixE (hp : p.Prime) (hEc : Nat.card E = p ^ 2) : ∃ x, x ∉ fixE E := by
  by_contra h
  push Not at h
  have hbot : E = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro e he
    ext y
    simp [mem_fixE.1 (h y) e he]
  rw [hbot, Subgroup.card_bot] at hEc
  have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
  omega

theorem exists_mem_fixE (hp : p.Prime) (hp2 : p ≠ 2) (hE : CFSG.Open.IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) {σ₀ : Perm Ω} (hσ₀ : σ₀ ∈ E) (hσ₀1 : σ₀ ≠ 1)
    (hfix : σ₀.supportᶜ.card = 2 ∨ σ₀.supportᶜ.card = 4) : ∃ c ∈ σ₀.supportᶜ, c ∈ fixE E := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf σ₀ = p := orderOf_eq_prime (hE.2 σ₀ hσ₀) hσ₀1
  have hZ : Nat.card (Subgroup.zpowers σ₀) = p := by rw [Nat.card_zpowers, hord]
  obtain ⟨τ, hτE, hτZ⟩ : ∃ τ ∈ E, τ ∉ Subgroup.zpowers σ₀ := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers σ₀ from h)
    rw [hEc, hZ] at hle
    have : p < p ^ 2 := by
      rw [pow_two]
      exact lt_mul_self hp.one_lt
    omega
  have hcomm : τ * σ₀ = σ₀ * τ := comm_of_elem hE hτE hσ₀
  have hcomm' : ∀ y, τ (σ₀ y) = σ₀ (τ y) := fun y => by
    have := congrArg (fun f : Perm Ω => f y) hcomm
    simpa only [Perm.coe_mul, Function.comp_apply] using this
  have hpres : ∀ y, τ y ∈ σ₀.supportᶜ ↔ y ∈ σ₀.supportᶜ := by
    intro y
    simp only [Finset.mem_compl, mem_support, not_not]
    constructor
    · intro h
      have h1 : τ (σ₀ y) = τ y := by rw [hcomm' y, h]
      exact τ.injective h1
    · intro h
      rw [← hcomm' y, h]
  set τ' : Perm {y // y ∈ σ₀.supportᶜ} := τ.subtypePerm hpres with hτ'
  have hτ'p : τ' ^ p ^ 1 = 1 := by
    rw [pow_one, hτ', subtypePerm_pow]
    ext y
    simp [hE.2 τ hτE]
  have hmod := Equiv.Perm.card_compl_support_modEq hτ'p
  rw [Fintype.card_coe] at hmod
  have hne : τ'.supportᶜ.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h0
    rw [h0, Finset.card_empty] at hmod
    have hd : p ∣ σ₀.supportᶜ.card := Nat.modEq_zero_iff_dvd.1 hmod.symm
    have h4 : p ∣ 2 ^ 2 := by
      rcases hfix with h | h
      · rw [h] at hd
        exact dvd_trans hd (by norm_num)
      · rw [h] at hd
        exact hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
  obtain ⟨⟨c, hc⟩, hc'⟩ := hne
  have hτc : τ c = c := by
    rw [Finset.mem_compl, mem_support, not_not] at hc'
    exact congrArg Subtype.val hc'
  have hσc : σ₀ c = c := by
    rw [Finset.mem_compl, mem_support, not_not] at hc
    exact hc
  refine ⟨c, hc, mem_fixE.2 fun e he => ?_⟩
  have hZle : Subgroup.zpowers σ₀ ≤ stb E c := (Subgroup.zpowers_le).2 (mem_stb.2 ⟨hσ₀, hσc⟩)
  have hτst : τ ∈ stb E c := mem_stb.2 ⟨hτE, hτc⟩
  rcases card_stb hp hEc c with h1 | h1 | h1
  · have := Subgroup.card_le_of_le hZle
    rw [h1, hZ] at this
    exact absurd hp.two_le (by omega)
  · have heq : Subgroup.zpowers σ₀ = stb E c := Subgroup.eq_of_le_of_card_ge hZle (by rw [h1, hZ])
    exact absurd (heq ▸ hτst) hτZ
  · have heq : stb E c = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hEc])
    have he' : e ∈ stb E c := by rw [heq]; exact he
    exact (mem_stb.1 he').2

theorem alternatingGroup_le_of_no_regular (hp : p.Prime) (hp2 : p ≠ 2) (hE : CFSG.Open.IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) (hreg : ∀ x, Nat.card (stb E x) ≠ 1) {c : Ω} (hc : c ∈ fixE E) :
    alternatingGroup Ω ≤ centClosure E := by
  classical
  have hst : ∀ x, x ∉ fixE E → Nat.card (stb E x) = p := by
    intro x hx
    rcases card_stb hp hEc x with h | h | h
    · exact absurd h (hreg x)
    · exact h
    · exact absurd ((mem_fixE_iff_card hEc).2 h) hx
  obtain ⟨x₀, hx₀⟩ := exists_not_mem_fixE hp hEc
  set 𝒳 : Finset (Finset Ω) := (Finset.univ.filter fun x => x ∉ fixE E).image (kfix E) with h𝒳
  have hmem𝒳 : ∀ A ∈ 𝒳, ∃ x, x ∉ fixE E ∧ kfix E x = A := by
    intro A hA
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hA
    exact ⟨x, (Finset.mem_filter.1 hx).2, rfl⟩
  have hin𝒳 : ∀ x, x ∉ fixE E → kfix E x ∈ 𝒳 := fun x hx =>
    Finset.mem_image_of_mem _ (Finset.mem_filter.2 ⟨Finset.mem_univ x, hx⟩)
  refine alternatingGroup_le_of_family 𝒳 (r := c) ?_ ?_ ?_ ?_
  · intro A hA
    obtain ⟨x, -, rfl⟩ := hmem𝒳 A hA
    exact fixE_subset_kfix x hc
  · intro y
    by_cases hy : y ∈ fixE E
    · exact ⟨kfix E x₀, hin𝒳 x₀ hx₀, fixE_subset_kfix x₀ hy⟩
    · exact ⟨kfix E y, hin𝒳 y hy, orb_subset_kfix hE y (mem_orb_self y)⟩
  · intro A hA
    obtain ⟨x, hx, rfl⟩ := hmem𝒳 A hA
    have hsub : orb E x ⊆ kfix E x \ (𝒳.erase (kfix E x)).biUnion id := by
      intro y hy
      rw [Finset.mem_sdiff]
      refine ⟨orb_subset_kfix hE x hy, fun hy' => ?_⟩
      obtain ⟨B, hB, hyB⟩ := Finset.mem_biUnion.1 hy'
      obtain ⟨hBne, hB𝒳⟩ := Finset.mem_erase.1 hB
      obtain ⟨x', hx', rfl⟩ := hmem𝒳 B hB𝒳
      exact Finset.disjoint_left.1 (disjoint_orb_kfix hE (hst x hx) (hst x' hx') hBne) hy hyB
    exact (three_le_of_odd_prime hp hp2).trans ((le_card_orb hp hEc hx).trans (Finset.card_le_card hsub))
  · intro A hA a b d hab hbd had ha hb hd
    obtain ⟨x, hx, rfl⟩ := hmem𝒳 A hA
    obtain ⟨k, hk, hk1⟩ : ∃ k ∈ stb E x, k ≠ 1 := by
      by_contra h
      push Not at h
      have hbot : stb E x = ⊥ := (Subgroup.eq_bot_iff_forall _).2 h
      have h1 := hst x hx
      rw [hbot, Subgroup.card_bot] at h1
      exact hp.one_lt.ne h1
    have hfixk : ∀ y ∈ kfix E x, k y = y := fun y hy =>
      mem_kfix.1 hy k (mem_stb.1 hk).1 (mem_stb.1 hk).2
    have hnd : [a, b, d].Nodup := by simp [hab, hbd, had]
    have hsupp := Equiv.Perm.support_swap_mul_swap hnd
    unfold C3
    apply Subgroup.subset_closure
    refine ⟨?_, k, (mem_stb.1 hk).1, hk1, ?_⟩
    · have h3 : (swap a b * swap b d).IsThreeCycle := by
        rw [← card_support_eq_three_iff, hsupp]
        simp [hab, hbd, had]
      exact h3.mem_alternatingGroup
    · have hdj : Perm.Disjoint (swap a b * swap b d) k := by
        rw [disjoint_iff_disjoint_support, hsupp, Finset.disjoint_left]
        intro v hv hvk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl | rfl
        · exact (mem_support.1 hvk) (hfixk _ ha)
        · exact (mem_support.1 hvk) (hfixk _ hb)
        · exact (mem_support.1 hvk) (hfixk _ hd)
      exact hdj.commute.eq

theorem regular_case (hp : p.Prime) (hp2 : p ≠ 2) (hE : CFSG.Open.IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) (hΩ : Fintype.card Ω ≤ 12) {x₀ : Ω} (hx₀ : Nat.card (stb E x₀) = 1)
    {c : Ω} (hc : c ∈ fixE E) :
    p = 3 ∧ (fixE E).card + 9 = Fintype.card Ω ∧ ∀ e ∈ E, e ≠ 1 → e.supportᶜ = fixE E := by
  classical
  have hO : (orb E x₀).card = p ^ 2 := card_orb_of_card_stb_one hEc hx₀
  have hbot : stb E x₀ = ⊥ := (Subgroup.card_eq_one).1 hx₀
  have hstO : ∀ y ∈ orb E x₀, stb E y = ⊥ := by
    intro y hy
    obtain ⟨g, hg, rfl⟩ := mem_orb.1 hy
    rw [stb_apply hE hg, hbot]
  have hOF : Disjoint (orb E x₀) (fixE E) := by
    rw [Finset.disjoint_left]
    intro y hy hyF
    have h1 := (mem_fixE_iff_card hEc).1 hyF
    rw [hstO y hy, Subgroup.card_bot] at h1
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  have hcardOF : (orb E x₀ ∪ fixE E).card = p ^ 2 + (fixE E).card := by
    rw [Finset.card_union_of_disjoint hOF, hO]
  have hle1 : p ^ 2 + (fixE E).card ≤ Fintype.card Ω := hcardOF ▸ Finset.card_le_univ _
  have hF1 : 1 ≤ (fixE E).card := Finset.card_pos.2 ⟨c, hc⟩
  have hp3 : p = 3 := by
    have h3 := three_le_of_odd_prime hp hp2
    by_contra hne
    have h5 : 5 ≤ p := by
      rcases Nat.lt_or_ge p 5 with h | h
      · interval_cases p
        · exact absurd rfl hne
        · exact absurd (by norm_num : ¬ Nat.Prime 4) (not_not.2 hp)
      · exact h
    have : 25 ≤ p ^ 2 := by nlinarith
    omega
  subst hp3
  have hall : ∀ y, y ∈ orb E x₀ ∪ fixE E := by
    intro y
    by_contra hy
    rw [Finset.mem_union, not_or] at hy
    have hOy : Disjoint (orb E y) (orb E x₀ ∪ fixE E) := by
      rw [Finset.disjoint_left]
      intro z hz hz'
      obtain ⟨g, hg, rfl⟩ := mem_orb.1 hz
      rcases Finset.mem_union.1 hz' with h | h
      · obtain ⟨h', hh', hgy⟩ := mem_orb.1 h
        apply hy.1
        refine mem_orb.2 ⟨g⁻¹ * h', E.mul_mem (E.inv_mem hg) hh', ?_⟩
        rw [Perm.mul_apply, hgy]
        simp
      · apply hy.2
        have h1 : g⁻¹ (g y) = g y := (mem_fixE.1 h) g⁻¹ (E.inv_mem hg)
        have h2 : g⁻¹ (g y) = y := by simp
        rw [← h2, h1]
        exact h
    have h3 : 3 ≤ (orb E y).card := le_card_orb (by norm_num) hEc hy.2
    have hU := Finset.card_union_of_disjoint hOy
    have hle := Finset.card_le_univ (orb E y ∪ (orb E x₀ ∪ fixE E))
    rw [hU, hcardOF] at hle
    omega
  have huniv : orb E x₀ ∪ fixE E = Finset.univ := Finset.eq_univ_of_forall hall
  refine ⟨rfl, ?_, ?_⟩
  · have := congrArg Finset.card huniv
    rw [hcardOF, Finset.card_univ] at this
    omega
  · intro e he he1
    ext y
    rw [Finset.mem_compl, mem_support, not_not]
    constructor
    · intro hey
      rcases Finset.mem_union.1 (hall y) with h | h
      · have : e ∈ stb E y := mem_stb.2 ⟨he, hey⟩
        rw [hstO y h, Subgroup.mem_bot] at this
        exact absurd this he1
      · exact h
    · intro hy
      exact mem_fixE.1 hy e he

theorem plane_dichotomy (hp : p.Prime) (hp2 : p ≠ 2) (hE : CFSG.Open.IsElemAbelian p E)
    (hEc : Nat.card E = p ^ 2) (hΩ : Fintype.card Ω ≤ 12) {σ₀ : Perm Ω} (hσ₀ : σ₀ ∈ E) (hσ₀1 : σ₀ ≠ 1)
    (hfix : σ₀.supportᶜ.card = 2 ∨ σ₀.supportᶜ.card = 4) :
    alternatingGroup Ω ≤ centClosure E ∨
      (p = 3 ∧ Fintype.card Ω = 11 ∧ (fixE E).card = 2 ∧ ∀ e ∈ E, e ≠ 1 → e.supportᶜ = fixE E) := by
  obtain ⟨c, -, hc⟩ := exists_mem_fixE hp hp2 hE hEc hσ₀ hσ₀1 hfix
  by_cases hreg : ∃ x₀, Nat.card (stb E x₀) = 1
  · obtain ⟨x₀, hx₀⟩ := hreg
    obtain ⟨hp3, hcard, hfixe⟩ := regular_case hp hp2 hE hEc hΩ hx₀ hc
    right
    have hσ := hfixe σ₀ hσ₀ hσ₀1
    rw [hσ] at hfix
    refine ⟨hp3, ?_, ?_, hfixe⟩
    · rcases hfix with h | h <;> omega
    · rcases hfix with h | h
      · exact h
      · omega
  · push Not at hreg
    exact Or.inl (alternatingGroup_le_of_no_regular hp hp2 hE hEc hreg hc)

end Plane

end CFSG.LocalAnalysis.UniquenessCase.UCK.Alt36
