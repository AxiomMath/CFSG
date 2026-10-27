module

public import CFSG.Quasithin.H13.VolIAltCoverSevenData

public section

namespace CFSG.Quasithin.ModA7

open Equiv CFSG.Quasithin CFSG.Quasithin.G6

abbrev A7 : Type := ↥(alternatingGroup (Fin 7))

private theorem card_A7 : Nat.card A7 = 2520 := by
  rw [nat_card_alternatingGroup]
  simp [Nat.factorial]

private instance : IsSimpleGroup A7 := alternatingGroup.isSimpleGroup (by simp)

private theorem card_modEq_fixed_prime {p : ℕ} [hp : Fact p.Prime] {α : Type*} [Finite α] (f : α → α)
    (hf : f^[p] = id) : Nat.card α ≡ Nat.card {a // f a = a} [MOD p] := by
  classical
  have : Fintype α := Fintype.ofFinite α
  let g : Function.End α := f
  have h5 : g ^ p ^ 1 = (1 : Function.End α) := by
    rw [pow_one]
    funext a
    exact congrFun hf a
  have h := Equiv.Perm.card_fixedPoints_modEq (α := α) (f := g) (p := p) (n := 1) h5
  have e : Nat.card {a // f a = a} = Nat.card ↑(Function.fixedPoints g) :=
    Nat.card_congr (Equiv.refl _)
  rw [e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact h

section Orbit

variable {X : Type*} [MulAction A7 X]

private theorem card_orbit_dvd (x₀ : X) : Nat.card (MulAction.orbit A7 x₀) ∣ 2520 := by
  rw [← card_A7, Nat.card_congr (MulAction.orbitEquivQuotientStabilizer A7 x₀)]
  exact Subgroup.index_dvd_card _

private theorem seven_le_card_of_nontrivial {Y : Type*} [MulAction A7 Y] [Finite Y]
    (h : ∃ (y : Y) (σ : A7), σ • y ≠ y) : 7 ≤ Nat.card Y := by
  by_contra hlt
  push Not at hlt
  have hn : (MulAction.toPermHom A7 Y).ker.Normal := MonoidHom.normal_ker _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MulAction.toPermHom A7 Y).ker with hb | ht
  · have hinj := (MonoidHom.ker_eq_bot_iff _).mp hb
    have h1 := Nat.card_le_card_of_injective _ hinj
    rw [card_A7, Nat.card_perm] at h1
    have h2 : (Nat.card Y).factorial ≤ (6 : ℕ).factorial := Nat.factorial_le (by omega)
    have h3 : (6 : ℕ).factorial = 720 := by decide
    omega
  · obtain ⟨y, σ, hy⟩ := h
    apply hy
    have hσ : σ ∈ (MulAction.toPermHom A7 Y).ker := by rw [ht]; trivial
    rw [MonoidHom.mem_ker] at hσ
    have := congrArg (fun f : Perm Y => f y) hσ
    simpa using this

private theorem orbit_card_eq_one_or_seven_le (x₀ : X) [Finite X] :
    Nat.card (MulAction.orbit A7 x₀) = 1 ∨ 7 ≤ Nat.card (MulAction.orbit A7 x₀) := by
  by_cases h : ∃ (y : MulAction.orbit A7 x₀) (σ : A7), σ • y ≠ y
  · exact Or.inr (seven_le_card_of_nontrivial h)
  · left
    push Not at h
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => ?_⟩, ⟨⟨x₀, MulAction.mem_orbit_self x₀⟩⟩⟩
    obtain ⟨a, g, rfl⟩ := a
    obtain ⟨b, k, rfl⟩ := b
    have e1 := congrArg Subtype.val (h ⟨x₀, MulAction.mem_orbit_self x₀⟩ g)
    have e2 := congrArg Subtype.val (h ⟨x₀, MulAction.mem_orbit_self x₀⟩ k)
    exact Subtype.ext (e1.trans e2.symm)

end Orbit

section Counting

variable {Ω : Type*} [MulAction A7 Ω]

private theorem card_modEq_set [Finite Ω] {p : ℕ} [Fact p.Prime] (S : Set Ω) {g : A7} (hg : g ^ p = 1)
    (hS : ∀ s ∈ S, g • s ∈ S) :
    S.ncard ≡ (S ∩ MulAction.fixedBy Ω g).ncard [MOD p] := by
  let f : S → S := fun a => ⟨g • a.1, hS a.1 a.2⟩
  have key : ∀ (n : ℕ) (a : S), (f^[n] a).1 = g ^ n • a.1 := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [Function.iterate_succ_apply, ih, pow_succ, mul_smul]
  have hf : f^[p] = id := by
    funext a
    apply Subtype.ext
    rw [key, hg, one_smul]
    rfl
  have h := card_modEq_fixed_prime f hf
  have e : Nat.card {a : S // f a = a} = (S ∩ MulAction.fixedBy Ω g).ncard := by
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_congr
      { toFun := fun a => ⟨a.1.1, a.1.2, by
          have := congrArg Subtype.val a.2
          simpa [f] using this⟩
        invFun := fun a => ⟨⟨a.1, a.2.1⟩, Subtype.ext (by simpa [f] using a.2.2)⟩
        left_inv := fun a => rfl
        right_inv := fun a => rfl }
  rw [e, Nat.card_coe_set_eq] at h
  exact h

private theorem fixing_top_of_fix (S : Set Ω) (hS : ∀ σ : A7, ∀ s ∈ S, σ • s ∈ S) {g : A7} (hg : g ≠ 1)
    (h : ∀ s ∈ S, g • s = s) : ∀ σ : A7, ∀ s ∈ S, σ • s = s := by
  have hN : (fixingSubgroup A7 S).Normal :=
    ⟨fun n hn k => by
      rw [mem_fixingSubgroup_iff] at hn ⊢
      intro s hs
      have hk : k⁻¹ • s ∈ S := hS k⁻¹ s hs
      rw [mul_smul, mul_smul, hn (k⁻¹ • s) hk, smul_inv_smul]⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (fixingSubgroup A7 S) with hb | ht
  · exfalso
    apply hg
    have : g ∈ fixingSubgroup A7 S := by
      rw [mem_fixingSubgroup_iff]
      exact h
    rw [hb] at this
    simpa using this
  · intro σ s hs
    have : σ ∈ fixingSubgroup A7 S := by rw [ht]; trivial
    rw [mem_fixingSubgroup_iff] at this
    exact this s hs

private theorem fixed_of_card_orbit_eq_one {x₀ : Ω} (h : Nat.card (MulAction.orbit A7 x₀) = 1) (σ : A7) :
    σ • x₀ = x₀ := by
  rw [Nat.card_eq_one_iff_unique] at h
  obtain ⟨hsub, -⟩ := h
  have := hsub.elim ⟨σ • x₀, MulAction.mem_orbit x₀ σ⟩ ⟨x₀, MulAction.mem_orbit_self x₀⟩
  exact congrArg Subtype.val this

private theorem pow_two_modEq_five (d j : ℕ) (hjd : j ≤ d) (hd : d ≤ 4) (h : 2 ^ d ≡ 2 ^ j [MOD 5]) :
    j = d ∨ (d = 4 ∧ j = 0) := by
  interval_cases d <;> interval_cases j <;> simp_all [Nat.ModEq]

private theorem arith_one (m : ℕ) (h1 : m ≤ 16) (h2 : m ∣ 2520) (h3 : m ≡ 1 [MOD 5])
    (h4 : m = 1 ∨ 7 ≤ m) : m = 1 := by
  interval_cases m <;> simp_all [Nat.ModEq]

private theorem exists_fixed_of_five [Finite Ω] (S : Set Ω) (hS : ∀ σ : A7, ∀ s ∈ S, σ • s ∈ S) {d : ℕ}
    (hd : d ≤ 4) (hcard : S.ncard = 2 ^ d) {y : A7} (hy5 : y ^ 5 = 1) (hy1 : y ≠ 1)
    (hpow : (S ∩ MulAction.fixedBy Ω y).ncard = 0 ∨
      ∃ j, (S ∩ MulAction.fixedBy Ω y).ncard = 2 ^ j) :
    ∃ s ∈ S, ∀ σ : A7, σ • s = s := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hmod : S.ncard ≡ (S ∩ MulAction.fixedBy Ω y).ncard [MOD 5] :=
    card_modEq_set S hy5 (fun s hs => hS y s hs)
  have hFS : S ∩ MulAction.fixedBy Ω y ⊆ S := Set.inter_subset_left
  have hle : (S ∩ MulAction.fixedBy Ω y).ncard ≤ S.ncard :=
    Set.ncard_le_ncard hFS (Set.toFinite S)
  have hne : S.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hcard]; positivity)
  rcases hpow with h0 | ⟨j, hj⟩
  · exfalso
    rw [h0, hcard] at hmod
    interval_cases d <;> simp [Nat.ModEq] at hmod
  · have hjd : j ≤ d := by
      rw [hj, hcard] at hle
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hle
    have hmod' := hmod
    rw [hj, hcard] at hmod'
    rcases pow_two_modEq_five d j hjd hd hmod' with h | ⟨hd4, hj0⟩
    · subst h
      have hFeq : S ∩ MulAction.fixedBy Ω y = S :=
        Set.eq_of_subset_of_ncard_le hFS (by rw [hj, hcard]) (Set.toFinite S)
      have hall := fixing_top_of_fix S hS hy1 (fun s hs => by
        have : s ∈ S ∩ MulAction.fixedBy Ω y := by rw [hFeq]; exact hs
        exact this.2)
      exact ⟨hne.some, hne.some_mem, fun σ => hall σ _ hne.some_mem⟩
    · rw [hj0, pow_zero] at hj
      obtain ⟨s₀, hs₀⟩ := Set.ncard_eq_one.mp hj
      have hs₀mem : s₀ ∈ S ∩ MulAction.fixedBy Ω y := by rw [hs₀]; exact Set.mem_singleton s₀
      have hs₀S : s₀ ∈ S := hs₀mem.1
      refine ⟨s₀, hs₀S, ?_⟩
      have hOS : MulAction.orbit A7 s₀ ⊆ S := by
        rintro _ ⟨σ, rfl⟩
        exact hS σ s₀ hs₀S
      have hm1 : Nat.card (MulAction.orbit A7 s₀) ≤ 16 := by
        rw [Nat.card_coe_set_eq]
        have := Set.ncard_le_ncard hOS (Set.toFinite S)
        rw [hcard, hd4] at this
        simpa using this
      have hm2 := card_orbit_dvd s₀
      have hOfix : MulAction.orbit A7 s₀ ∩ MulAction.fixedBy Ω y = {s₀} := by
        apply Set.Subset.antisymm
        · rintro z ⟨hzO, hzF⟩
          have : z ∈ S ∩ MulAction.fixedBy Ω y := ⟨hOS hzO, hzF⟩
          rw [hs₀] at this
          exact this
        · rintro z rfl
          exact ⟨MulAction.mem_orbit_self _, hs₀mem.2⟩
      have hm3 : Nat.card (MulAction.orbit A7 s₀) ≡ 1 [MOD 5] := by
        have := card_modEq_set (MulAction.orbit A7 s₀) hy5 (fun s hs => by
          obtain ⟨σ, rfl⟩ := hs
          exact ⟨y * σ, mul_smul y σ s₀⟩)
        rw [hOfix, Set.ncard_singleton, ← Nat.card_coe_set_eq] at this
        exact this
      have hm4 := orbit_card_eq_one_or_seven_le s₀
      have hm := arith_one _ hm1 hm2 hm3 hm4
      exact fixed_of_card_orbit_eq_one hm

private theorem pow_two_modEq_seven (j : ℕ) (hj : j ≤ 5) (h : 2 ^ j ≡ 32 [MOD 7]) : j = 2 ∨ j = 5 := by
  interval_cases j <;> simp_all [Nat.ModEq]

private theorem pow_two_modEq_five' (j : ℕ) (hj : j ≤ 5) (h : 2 ^ j ≡ 32 [MOD 5]) : j = 1 ∨ j = 5 := by
  interval_cases j <;> simp_all [Nat.ModEq]

private theorem arith_orbit (m cy cx : ℕ) (h32 : m ≤ 32) (hdvd : m ∣ 2520) (h7 : 7 ≤ m)
    (hy1 : 1 ≤ cy) (hy2 : cy ≤ 2) (hmy : m ≡ cy [MOD 5]) (hx : cx ≤ 4) (hmx : m ≡ cx [MOD 7]) :
    m = 7 ∨ m = 21 := by
  interval_cases m <;> interval_cases cy <;> interval_cases cx <;> simp_all [Nat.ModEq]

private theorem fixed_card_of_prime [Finite Ω] (S : Set Ω) (hS : ∀ σ : A7, ∀ s ∈ S, σ • s ∈ S)
    (hcard : S.ncard = 32) {p : ℕ} [Fact p.Prime] {g : A7} (hgp : g ^ p = 1) (hg1 : g ≠ 1)
    (hp32 : ¬ p ∣ 32)
    (hpow : (S ∩ MulAction.fixedBy Ω g).ncard = 0 ∨
      ∃ j, (S ∩ MulAction.fixedBy Ω g).ncard = 2 ^ j)
    (hnofix : ∀ s ∈ S, ∃ σ : A7, σ • s ≠ s) :
    ∃ j, j ≤ 5 ∧ (S ∩ MulAction.fixedBy Ω g).ncard = 2 ^ j ∧ 2 ^ j ≡ 32 [MOD p] ∧ j ≠ 5 := by
  have hmod : S.ncard ≡ (S ∩ MulAction.fixedBy Ω g).ncard [MOD p] :=
    card_modEq_set S hgp (fun s hs => hS g s hs)
  have hFS : S ∩ MulAction.fixedBy Ω g ⊆ S := Set.inter_subset_left
  have hle : (S ∩ MulAction.fixedBy Ω g).ncard ≤ 32 := by
    rw [← hcard]; exact Set.ncard_le_ncard hFS (Set.toFinite S)
  have hne : S.Nonempty := Set.nonempty_of_ncard_ne_zero (by rw [hcard]; norm_num)
  rcases hpow with h0 | ⟨j, hj⟩
  · exfalso
    rw [h0, hcard] at hmod
    exact hp32 (Nat.modEq_zero_iff_dvd.mp hmod)
  · refine ⟨j, ?_, hj, ?_, ?_⟩
    · rw [hj] at hle
      by_contra hcon
      push Not at hcon
      have : 2 ^ 6 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hcon
      omega
    · rw [hj, hcard] at hmod
      exact hmod.symm
    · intro hj5
      subst hj5
      have hFeq : S ∩ MulAction.fixedBy Ω g = S :=
        Set.eq_of_subset_of_ncard_le hFS (by rw [hj, hcard]; norm_num) (Set.toFinite S)
      have hall := fixing_top_of_fix S hS hg1 (fun s hs => by
        have : s ∈ S ∩ MulAction.fixedBy Ω g := by rw [hFeq]; exact hs
        exact this.2)
      obtain ⟨σ, hσ⟩ := hnofix _ hne.some_mem
      exact hσ (hall σ _ hne.some_mem)

private theorem exists_orbit_seven [Finite Ω] (S : Set Ω) (hS : ∀ σ : A7, ∀ s ∈ S, σ • s ∈ S)
    (hcard : S.ncard = 32) {x y : A7} (hx7 : x ^ 7 = 1) (hx1 : x ≠ 1) (hy5 : y ^ 5 = 1)
    (hy1 : y ≠ 1)
    (hpx : (S ∩ MulAction.fixedBy Ω x).ncard = 0 ∨
      ∃ j, (S ∩ MulAction.fixedBy Ω x).ncard = 2 ^ j)
    (hpy : (S ∩ MulAction.fixedBy Ω y).ncard = 0 ∨
      ∃ j, (S ∩ MulAction.fixedBy Ω y).ncard = 2 ^ j)
    (hnofix : ∀ s ∈ S, ∃ σ : A7, σ • s ≠ s) :
    ∃ s ∈ S, Nat.card (MulAction.orbit A7 s) = 7 := by
  have h7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have h5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨jx, hjx5, hFx, hjxmod, hjxne⟩ :=
    fixed_card_of_prime S hS hcard hx7 hx1 (by decide) hpx hnofix
  obtain ⟨jy, hjy5, hFy, hjymod, hjyne⟩ :=
    fixed_card_of_prime S hS hcard hy5 hy1 (by decide) hpy hnofix
  have hjx : jx = 2 := (pow_two_modEq_seven jx hjx5 hjxmod).resolve_right hjxne
  have hjy : jy = 1 := (pow_two_modEq_five' jy hjy5 hjymod).resolve_right hjyne
  subst hjx hjy
  have hFx4 : (S ∩ MulAction.fixedBy Ω x).ncard = 4 := by rw [hFx]; norm_num
  have hFy2 : (S ∩ MulAction.fixedBy Ω y).ncard = 2 := by rw [hFy]; norm_num
  obtain ⟨y₁, y₂, hy12, hFy'⟩ := Set.ncard_eq_two.mp hFy2
  have hy₁ : y₁ ∈ S ∩ MulAction.fixedBy Ω y := by rw [hFy']; simp
  have hy₂ : y₂ ∈ S ∩ MulAction.fixedBy Ω y := by rw [hFy']; simp
  have key : ∀ s₀ ∈ S ∩ MulAction.fixedBy Ω y,
      (MulAction.orbit A7 s₀).ncard = 7 ∨
      ((MulAction.orbit A7 s₀).ncard = 21 ∧
        (MulAction.orbit A7 s₀ ∩ MulAction.fixedBy Ω y).ncard = 1) := by
    intro s₀ hs₀
    have hOS : MulAction.orbit A7 s₀ ⊆ S := by
      rintro _ ⟨σ, rfl⟩
      exact hS σ s₀ hs₀.1
    have hm1 : (MulAction.orbit A7 s₀).ncard ≤ 32 := by
      rw [← hcard]; exact Set.ncard_le_ncard hOS (Set.toFinite S)
    have hm2 : (MulAction.orbit A7 s₀).ncard ∣ 2520 := by
      rw [← Nat.card_coe_set_eq]; exact card_orbit_dvd s₀
    have hm7 : 7 ≤ (MulAction.orbit A7 s₀).ncard := by
      rcases orbit_card_eq_one_or_seven_le s₀ with h1 | h7'
      · exfalso
        obtain ⟨σ, hσ⟩ := hnofix s₀ hs₀.1
        exact hσ (fixed_of_card_orbit_eq_one h1 σ)
      · rwa [← Nat.card_coe_set_eq]
    have hcy := card_modEq_set (MulAction.orbit A7 s₀) hy5 (fun s hs => by
      obtain ⟨σ, rfl⟩ := hs
      exact ⟨y * σ, mul_smul y σ s₀⟩)
    have hcx := card_modEq_set (MulAction.orbit A7 s₀) hx7 (fun s hs => by
      obtain ⟨σ, rfl⟩ := hs
      exact ⟨x * σ, mul_smul x σ s₀⟩)
    have hcy1 : 1 ≤ (MulAction.orbit A7 s₀ ∩ MulAction.fixedBy Ω y).ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr ⟨s₀, MulAction.mem_orbit_self s₀, hs₀.2⟩
    have hcy2 : (MulAction.orbit A7 s₀ ∩ MulAction.fixedBy Ω y).ncard ≤ 2 := by
      rw [← hFy2]
      exact Set.ncard_le_ncard (Set.inter_subset_inter_left _ hOS) (Set.toFinite _)
    have hcx4 : (MulAction.orbit A7 s₀ ∩ MulAction.fixedBy Ω x).ncard ≤ 4 := by
      rw [← hFx4]
      exact Set.ncard_le_ncard (Set.inter_subset_inter_left _ hOS) (Set.toFinite _)
    have hm := arith_orbit _ _ _ hm1 hm2 hm7 hcy1 hcy2 hcy hcx4 hcx
    rcases hm with h | h
    · exact Or.inl h
    · right
      refine ⟨h, ?_⟩
      have := hcy
      rw [h] at this
      unfold Nat.ModEq at this
      omega
  by_contra hno
  push Not at hno
  have hno' : ∀ s ∈ S, (MulAction.orbit A7 s).ncard ≠ 7 := fun s hs h => hno s hs (by
    rw [Nat.card_coe_set_eq]; exact h)
  have h1 := (key y₁ hy₁).resolve_left (hno' y₁ hy₁.1)
  have h2 := (key y₂ hy₂).resolve_left (hno' y₂ hy₂.1)
  have hy₂O : y₂ ∉ MulAction.orbit A7 y₁ := by
    intro hmem
    have hsub : ({y₁, y₂} : Set Ω) ⊆ MulAction.orbit A7 y₁ ∩ MulAction.fixedBy Ω y := by
      intro z hz
      rcases hz with rfl | rfl
      · exact ⟨MulAction.mem_orbit_self _, hy₁.2⟩
      · exact ⟨hmem, hy₂.2⟩
    have := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_pair hy12, h1.2] at this
    omega
  have hdisj : Disjoint (MulAction.orbit A7 y₁) (MulAction.orbit A7 y₂) := by
    rw [Set.disjoint_left]
    intro z hz1 hz2
    obtain ⟨g, rfl⟩ := hz1
    obtain ⟨h, hh⟩ := hz2
    have hh' : h • y₂ = g • y₁ := hh
    apply hy₂O
    refine ⟨h⁻¹ * g, ?_⟩
    show (h⁻¹ * g) • y₁ = y₂
    rw [mul_smul, ← hh', inv_smul_smul]
  have hunion : MulAction.orbit A7 y₁ ∪ MulAction.orbit A7 y₂ ⊆ S := by
    intro z hz
    rcases hz with ⟨σ, rfl⟩ | ⟨σ, rfl⟩
    · exact hS σ y₁ hy₁.1
    · exact hS σ y₂ hy₂.1
  have := Set.ncard_le_ncard hunion (Set.toFinite S)
  rw [Set.ncard_union_eq hdisj (Set.toFinite _) (Set.toFinite _), h1.1, h2.1, hcard] at this
  omega

end Counting

section Chars

variable {W : Type} [CommGroup W]

private def charSmul (ρ : A7 →* MulAut W) (σ : A7) (χ : W →* ℂˣ) : W →* ℂˣ :=
  χ.comp (ρ σ)⁻¹.toMonoidHom

private theorem charSmul_apply (ρ : A7 →* MulAut W) (σ : A7) (χ : W →* ℂˣ) (w : W) :
    charSmul ρ σ χ w = χ ((ρ σ)⁻¹ w) := rfl

@[instance_reducible] private def charAct (ρ : A7 →* MulAut W) : MulDistribMulAction A7 (W →* ℂˣ) where
  smul := charSmul ρ
  one_smul χ := by
    refine MonoidHom.ext fun w => ?_
    show χ ((ρ 1)⁻¹ w) = χ w
    simp
  mul_smul σ τ χ := by
    refine MonoidHom.ext fun w => ?_
    show χ ((ρ (σ * τ))⁻¹ w) = χ ((ρ τ)⁻¹ ((ρ σ)⁻¹ w))
    simp [mul_inv_rev]
  smul_mul σ χ₁ χ₂ := by
    refine MonoidHom.ext fun w => ?_
    show (χ₁ * χ₂) ((ρ σ)⁻¹ w) = χ₁ ((ρ σ)⁻¹ w) * χ₂ ((ρ σ)⁻¹ w)
    simp
  smul_one σ := by
    refine MonoidHom.ext fun w => ?_
    show (1 : W →* ℂˣ) ((ρ σ)⁻¹ w) = 1
    simp

end Chars

private def pv (a b : Fin 7) : PermMod 7 := Multiplicative.ofAdd (Pi.single a 1 + Pi.single b 1)

private theorem zmod_two_add_self (x : ZMod 2) : x + x = 0 := by revert x; decide

private theorem three_cycle_inv_apply {i j k : Fin 7} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (p : Fin 7) :
    ((swap i j * swap j k)⁻¹ : Perm (Fin 7)) p =
      if p = i then k else if p = j then i else if p = k then j else p := by
  rw [mul_inv_rev, Equiv.swap_inv, Equiv.swap_inv]
  simp only [Perm.mul_apply, Equiv.swap_apply_def]
  split_ifs <;> simp_all

private theorem exists_third : ∀ i j : Fin 7, ∃ k : Fin 7, k ≠ i ∧ k ≠ j := by decide

private theorem key7_core {i j k : Fin 7} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (v : PermMod 7)
    (hi : Multiplicative.toAdd v i = 1) (hj : Multiplicative.toAdd v j = 0) :
    ∃ a b : Fin 7, a ≠ b ∧ permAct 7 (swap i j * swap j k) v * v = pv a b := by
  have hk : Multiplicative.toAdd v k = 0 ∨ Multiplicative.toAdd v k = 1 := by
    generalize Multiplicative.toAdd v k = t
    revert t; decide
  rcases hk with hk | hk
  · refine ⟨i, j, hij, ?_⟩
    apply Multiplicative.toAdd.injective
    funext p
    simp only [toAdd_mul, Pi.add_apply, permAct_apply, three_cycle_inv_apply hij hjk hik, pv,
      toAdd_ofAdd, Pi.single_apply]
    by_cases hpi : p = i
    · subst hpi; simp [hij, hk, hi]
    · by_cases hpj : p = j
      · subst hpj; simp [hij.symm, hi, hj]
      · by_cases hpk : p = k
        · subst hpk; simp [hpi, hpj, hj, hk]
        · simp [hpi, hpj, hpk, zmod_two_add_self]
  · refine ⟨j, k, hjk, ?_⟩
    apply Multiplicative.toAdd.injective
    funext p
    simp only [toAdd_mul, Pi.add_apply, permAct_apply, three_cycle_inv_apply hij hjk hik, pv,
      toAdd_ofAdd, Pi.single_apply]
    by_cases hpi : p = i
    · subst hpi; simp [hij, hik, hk, hi, zmod_two_add_self]
    · by_cases hpj : p = j
      · subst hpj; simp [hij.symm, hi, hj, hjk]
      · by_cases hpk : p = k
        · subst hpk; simp [hpi, hpj, hj, hk]
        · simp [hpi, hpj, hpk, zmod_two_add_self]

private theorem lattice7 (R : Subgroup (PermMod 7))
    (hR : ∀ σ ∈ alternatingGroup (Fin 7), ∀ v ∈ R, permAct 7 σ v ∈ R) :
    (∀ v ∈ R, v = 1 ∨ v = allOnes 7) ∨ ∃ a b : Fin 7, a ≠ b ∧ pv a b ∈ R := by
  by_cases h : ∀ v ∈ R, v = 1 ∨ v = allOnes 7
  · exact Or.inl h
  · right
    push Not at h
    obtain ⟨v, hvR, hv1, hvo⟩ := h
    have hzc : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
    obtain ⟨i, hi⟩ : ∃ i, Multiplicative.toAdd v i = 1 := by
      by_contra hcon
      push Not at hcon
      apply hv1
      apply Multiplicative.toAdd.injective
      funext i
      exact (hzc _).resolve_right (hcon i)
    obtain ⟨j, hj⟩ : ∃ j, Multiplicative.toAdd v j = 0 := by
      by_contra hcon
      push Not at hcon
      apply hvo
      apply Multiplicative.toAdd.injective
      funext i
      exact (hzc _).resolve_left (hcon i)
    have hij : i ≠ j := by
      rintro rfl
      rw [hi] at hj
      exact one_ne_zero hj
    obtain ⟨k, hki, hkj⟩ := exists_third i j
    have hσ : (swap i j * swap j k : Perm (Fin 7)) ∈ alternatingGroup (Fin 7) := by
      rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_swap hij, Perm.sign_swap hkj.symm]
      decide
    obtain ⟨a, b, hab, hv⟩ := key7_core hij hkj.symm hki.symm v hi hj
    exact ⟨a, b, hab, hv ▸ R.mul_mem (hR _ hσ v hvR) hvR⟩

section ProdHom

variable {M : Type*} [CommGroup M]

private theorem zmod_two_val_one : ZMod.val (1 : ZMod 2) = 1 := rfl

private theorem pow_val_add (c : M) (hc : c * c = 1) (a b : ZMod 2) :
    c ^ (a + b).val = c ^ a.val * c ^ b.val := by
  have ha := ZMod.val_lt a
  have hb := ZMod.val_lt b
  rw [ZMod.val_add]
  interval_cases h1 : a.val <;> interval_cases h2 : b.val <;> simp [hc]

private def prodHom (hM : ∀ m : M, m * m = 1) (c : Fin 7 → M) : PermMod 7 →* M where
  toFun v := ∏ i, c i ^ (Multiplicative.toAdd v i).val
  map_one' := by simp
  map_mul' a b := by
    simp only [toAdd_mul, Pi.add_apply]
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => pow_val_add (c i) (hM _) _ _

private theorem prodHom_apply (hM : ∀ m : M, m * m = 1) (c : Fin 7 → M) (v : PermMod 7) :
    prodHom hM c v = ∏ i, c i ^ (Multiplicative.toAdd v i).val := rfl

private theorem prodHom_equivariant (hM : ∀ m : M, m * m = 1) (c : Fin 7 → M) (φ : M →* M)
    (σ : Perm (Fin 7)) (hφ : ∀ i, φ (c i) = c (σ i)) (v : PermMod 7) :
    φ (prodHom hM c v) = prodHom hM c (permAct 7 σ v) := by
  rw [prodHom_apply, prodHom_apply, map_prod]
  simp only [map_pow, hφ, permAct_apply]
  rw [← Equiv.prod_comp σ (fun j => c j ^ (Multiplicative.toAdd v (σ⁻¹ j)).val)]
  simp

private theorem prodHom_pv (hM : ∀ m : M, m * m = 1) (c : Fin 7 → M) {a b : Fin 7} (hab : a ≠ b) :
    prodHom hM c (pv a b) = c a * c b := by
  rw [prodHom_apply, Finset.prod_eq_mul a b hab]
  · simp [pv, hab, hab.symm, zmod_two_val_one]
  · intro i _ hi
    simp [pv, hi.1, hi.2]
  · intro h
    exact absurd (Finset.mem_univ a) h
  · intro h
    exact absurd (Finset.mem_univ b) h

end ProdHom

section Theta

variable {M : Type*} [CommGroup M] [Finite M] [MulDistribMulAction A7 M]

private theorem card_ker_ge_of_orbit_seven (hM : ∀ m : M, m * m = 1) {Q : Type*} [CommGroup Q]
    (hQ : ∀ q : Q, q * q = 1) (π : M →* Q) (m₀ : M) (hπ : ∀ σ : A7, π (σ • m₀) = π m₀)
    (h7 : Nat.card (MulAction.orbit A7 m₀) = 7) : 64 ≤ Nat.card π.ker := by
  classical
  let b : Fin 7 ≃ MulAction.orbit A7 m₀ := ((Finite.equivFin _).trans (finCongr h7)).symm
  let c : Fin 7 → M := fun i => (b i : M)
  let τ : A7 →* Perm (Fin 7) :=
    { toFun := fun g => (b.trans (MulAction.toPerm g : Perm (MulAction.orbit A7 m₀))).trans b.symm
      map_one' := by ext i; simp
      map_mul' := fun g h => by ext i; simp [mul_smul] }
  have hτ : ∀ g i, g • c i = c (τ g i) := by
    intro g i
    simp [c, τ]
  have hinj : Function.Injective τ := by
    rw [← MonoidHom.ker_eq_bot_iff]
    have hn : τ.ker.Normal := MonoidHom.normal_ker _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal τ.ker with hb | ht
    · exact hb
    · exfalso
      have hall : ∀ g : A7, ∀ i, g • c i = c i := by
        intro g i
        have hg : g ∈ τ.ker := by rw [ht]; trivial
        rw [MonoidHom.mem_ker] at hg
        rw [hτ, hg]
        rfl
      have hm₀ : ∀ g : A7, g • m₀ = m₀ := by
        intro g
        obtain ⟨i, hi⟩ := b.surjective ⟨m₀, MulAction.mem_orbit_self m₀⟩
        have := hall g i
        have hci : c i = m₀ := congrArg Subtype.val hi
        rw [hci] at this
        exact this
      have h1 : Nat.card (MulAction.orbit A7 m₀) = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        refine ⟨⟨fun x y => ?_⟩, ⟨⟨m₀, MulAction.mem_orbit_self m₀⟩⟩⟩
        obtain ⟨x, g, rfl⟩ := x
        obtain ⟨y, k, rfl⟩ := y
        exact Subtype.ext ((hm₀ g).trans (hm₀ k).symm)
      omega
  have hsign : ∀ g, Perm.sign (τ g) = 1 := by
    have hn : (Perm.sign.comp τ).ker.Normal := MonoidHom.normal_ker _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Perm.sign.comp τ).ker with hb | ht
    · exfalso
      have hinj' := (MonoidHom.ker_eq_bot_iff _).mp hb
      have := Nat.card_le_card_of_injective _ hinj'
      rw [card_A7, Nat.card_eq_fintype_card, Fintype.card_units_int] at this
      omega
    · intro g
      have hg : g ∈ (Perm.sign.comp τ).ker := by rw [ht]; trivial
      simpa using hg
  have hrange : τ.range = alternatingGroup (Fin 7) := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨g, rfl⟩
      exact Perm.mem_alternatingGroup.mpr (hsign g)
    · have h1 : Nat.card τ.range = 2520 := by
        rw [← card_A7]
        exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      have h2 : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
        rw [nat_card_alternatingGroup]
        simp [Nat.factorial]
      rw [h1, h2]
  have hsurj : ∀ σ ∈ alternatingGroup (Fin 7), ∃ g, τ g = σ := by
    intro σ hσ
    rw [← hrange] at hσ
    exact hσ
  set Θ := prodHom hM c with hΘ
  have hR : ∀ σ ∈ alternatingGroup (Fin 7), ∀ v ∈ Θ.ker, permAct 7 σ v ∈ Θ.ker := by
    intro σ hσ v hv
    obtain ⟨g, rfl⟩ := hsurj σ hσ
    rw [MonoidHom.mem_ker] at hv ⊢
    rw [← prodHom_equivariant hM c (MulDistribMulAction.toMonoidHom M g) (τ g)
      (fun i => hτ g i) v]
    show g • Θ v = 1
    rw [hv, smul_one]
  rcases lattice7 Θ.ker hR with hA | ⟨a, a', hne, hmem⟩
  ·
    have hpc : ∀ i, π (c i) = π m₀ := by
      intro i
      obtain ⟨g, hg⟩ := (b i).2
      have : (b i : M) = g • m₀ := hg.symm
      show π (b i : M) = π m₀
      rw [this]
      exact hπ g
    have hmem : ∀ v ∈ coreMod 7, Θ v ∈ π.ker := by
      intro v hv
      rw [MonoidHom.mem_ker, hΘ, prodHom_apply, map_prod]
      simp only [map_pow, hpc]
      rw [Finset.prod_pow_eq_pow_sum]
      have hcast : ((∑ i, (Multiplicative.toAdd v i).val : ℕ) : ZMod 2) = 0 := by
        rw [Nat.cast_sum]
        simp only [ZMod.natCast_zmod_val]
        exact mem_coreMod.mp hv
      have hdvd : 2 ∣ ∑ i, (Multiplicative.toAdd v i).val :=
        (ZMod.natCast_eq_zero_iff _ 2).mp hcast
      obtain ⟨k, hk⟩ := hdvd
      rw [hk, two_mul, pow_add, ← mul_pow, hQ, one_pow]
    let f : coreMod 7 → π.ker := fun v => ⟨Θ v, hmem v v.2⟩
    have hfinj : Function.Injective f := by
      intro v w hvw
      have hvw' : Θ v = Θ w := congrArg Subtype.val hvw
      have hker : (v : PermMod 7) * (w : PermMod 7)⁻¹ ∈ Θ.ker := by
        rw [MonoidHom.mem_ker]
        exact (map_mul_inv Θ (v : PermMod 7) (w : PermMod 7)).trans
          (by rw [hvw', mul_inv_cancel])
      rcases hA _ hker with h | h
      · exact Subtype.ext (mul_inv_eq_one.mp h)
      · exfalso
        apply CFSG.Quasithin.H13.VolI.allOnes_seven_not_mem
        rw [← h]
        exact (coreMod 7).mul_mem v.2 ((coreMod 7).inv_mem w.2)
    have := Nat.card_le_card_of_injective f hfinj
    rwa [CFSG.Quasithin.H13.VolI.card_coreMod_seven] at this
  · exfalso
    rw [MonoidHom.mem_ker, hΘ, prodHom_pv hM c hne] at hmem
    have h1 : c a = (c a')⁻¹ := eq_inv_of_mul_eq_one_left hmem
    have h2 : c a = c a' := by
      rw [h1]
      exact inv_eq_of_mul_eq_one_right (hM _)
    exact hne (b.injective (Subtype.ext h2))

end Theta

section Main

variable {W : Type} [CommGroup W]

private def Kgrp (Z : Subgroup W) : Subgroup (W →* ℂˣ) := (MonoidHom.domRestrictHom Z ℂˣ).ker

private theorem mem_Kgrp {Z : Subgroup W} {μ : W →* ℂˣ} : μ ∈ Kgrp Z ↔ ∀ z ∈ Z, μ z = 1 := by
  simp only [Kgrp, MonoidHom.mem_ker]
  constructor
  · intro h z hz
    have := DFunLike.congr_fun h ⟨z, hz⟩
    simpa using this
  · intro h
    refine MonoidHom.ext fun z => ?_
    simpa using h z z.2

private theorem card_Kgrp [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1) [Nontrivial W] (Z : Subgroup W) :
    Nat.card (Kgrp Z) = Z.index := by
  have hexp : Monoid.exponent W = 2 :=
    (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg => orderOf_eq_prime (hW2 g) hg
  have : HasEnoughRootsOfUnity ℂ (Monoid.exponent W) := by rw [hexp]; infer_instance
  have h := CommGroup.card_domRestrictHom_ker (G := W) (M := ℂ) Z
  rw [Subgroup.index_eq_card]
  exact h

private def cosetSet (Z : Subgroup W) (χ₀ : W →* ℂˣ) : Set (W →* ℂˣ) := {χ | ∀ z ∈ Z, χ z = χ₀ z}

private theorem cosetSet_eq_image (Z : Subgroup W) (χ₀ : W →* ℂˣ) :
    cosetSet Z χ₀ = (fun μ => μ * χ₀) '' (Kgrp Z : Set (W →* ℂˣ)) := by
  ext χ
  constructor
  · intro h
    refine ⟨χ * χ₀⁻¹, ?_, inv_mul_cancel_right χ χ₀⟩
    rw [SetLike.mem_coe, mem_Kgrp]
    intro z hz
    simp [h z hz]
  · rintro ⟨μ, hμ, rfl⟩ z hz
    rw [SetLike.mem_coe, mem_Kgrp] at hμ
    simp [hμ z hz]

private theorem ncard_cosetSet (Z : Subgroup W) (χ₀ : W →* ℂˣ) :
    (cosetSet Z χ₀).ncard = Nat.card (Kgrp Z) := by
  rw [cosetSet_eq_image, Set.ncard_image_of_injective _ (mul_left_injective χ₀),
    ← Nat.card_coe_set_eq]
  rfl

private def fixSub (ρ : A7 →* MulAut W) (g : A7) : Subgroup (W →* ℂˣ) where
  carrier := {μ | charSmul ρ g μ = μ}
  one_mem' := by
    refine MonoidHom.ext fun w => ?_
    simp [charSmul_apply]
  mul_mem' := fun {a b} ha hb => by
    refine MonoidHom.ext fun w => ?_
    have h1 := DFunLike.congr_fun ha w
    have h2 := DFunLike.congr_fun hb w
    simp only [charSmul_apply] at h1 h2
    show (a * b) ((ρ g)⁻¹ w) = (a * b) w
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, h1, h2]
  inv_mem' := fun {a} ha => by
    refine MonoidHom.ext fun w => ?_
    have h1 := DFunLike.congr_fun ha w
    simp only [charSmul_apply] at h1
    show (a⁻¹) ((ρ g)⁻¹ w) = (a⁻¹) w
    rw [MonoidHom.inv_apply, MonoidHom.inv_apply, h1]

private theorem inv_apply_of_apply_eq {e : MulAut W} {z : W} (h : e z = z) : e⁻¹ z = z := by
  have : (e⁻¹ : MulAut W) z = e.symm z := rfl
  rw [this, MulEquiv.symm_apply_eq]
  exact h.symm

private theorem charSmul_apply_of_mem {ρ : A7 →* MulAut W} {Z : Subgroup W}
    (hZ : ∀ σ : A7, ∀ z ∈ Z, ρ σ z = z) (σ : A7) (χ : W →* ℂˣ) {z : W} (hz : z ∈ Z) :
    charSmul ρ σ χ z = χ z := by
  rw [charSmul_apply, inv_apply_of_apply_eq (hZ σ z hz)]

private theorem charSmul_mem_cosetSet {ρ : A7 →* MulAut W} {Z : Subgroup W}
    (hZ : ∀ σ : A7, ∀ z ∈ Z, ρ σ z = z) {χ₀ : W →* ℂˣ} (σ : A7) {χ : W →* ℂˣ}
    (hχ : χ ∈ cosetSet Z χ₀) : charSmul ρ σ χ ∈ cosetSet Z χ₀ := fun z hz => by
  rw [charSmul_apply_of_mem hZ σ χ hz]
  exact hχ z hz

private theorem char_eq_one_of_fixed {ρ : A7 →* MulAut W} (hcomm : commV ρ.range = ⊤) {χ : W →* ℂˣ}
    (hfix : ∀ σ : A7, charSmul ρ σ χ = χ) (w : W) : χ w = 1 := by
  have hker : commV ρ.range ≤ χ.ker := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨x, ⟨σ, rfl⟩, v, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv]
    have h := DFunLike.congr_fun (hfix σ⁻¹) v
    have e : ((ρ σ⁻¹)⁻¹ : MulAut W) = ρ σ := by rw [map_inv, inv_inv]
    rw [charSmul_apply, e] at h
    rw [h, mul_inv_cancel]
  have := hker (by rw [hcomm]; trivial : w ∈ commV ρ.range)
  exact this

private theorem charSmul_fixed_apply {ρ : A7 →* MulAut W} {g : A7} {χ : W →* ℂˣ}
    (h : charSmul ρ g χ = χ) (w : W) : χ ((ρ g)⁻¹ w) = χ w := by
  have := DFunLike.congr_fun h w
  rwa [charSmul_apply] at this

private theorem charSmul_fixed_of_apply {ρ : A7 →* MulAut W} {g : A7} {χ : W →* ℂˣ}
    (h : ∀ w, χ ((ρ g)⁻¹ w) = χ w) : charSmul ρ g χ = χ :=
  MonoidHom.ext fun w => by rw [charSmul_apply]; exact h w

private theorem fix_pow {ρ : A7 →* MulAut W} [inst : MulDistribMulAction A7 (W →* ℂˣ)]
    (hsmul : ∀ σ χ, σ • χ = charSmul ρ σ χ) (Z : Subgroup W) (χ₀ : W →* ℂˣ) (g : A7)
    {n : ℕ} (hn : Nat.card (W →* ℂˣ) = 2 ^ n) :
    (cosetSet Z χ₀ ∩ MulAction.fixedBy (W →* ℂˣ) g).ncard = 0 ∨
      ∃ j, (cosetSet Z χ₀ ∩ MulAction.fixedBy (W →* ℂˣ) g).ncard = 2 ^ j := by
  by_cases hne : (cosetSet Z χ₀ ∩ MulAction.fixedBy (W →* ℂˣ) g).Nonempty
  · right
    obtain ⟨χ₁, hχ₁S, hχ₁F⟩ := hne
    have hχ₁F' : charSmul ρ g χ₁ = χ₁ := by rw [← hsmul]; exact hχ₁F
    have hset : cosetSet Z χ₀ ∩ MulAction.fixedBy (W →* ℂˣ) g =
        (fun μ => μ * χ₁) '' ((Kgrp Z ⊓ fixSub ρ g : Subgroup (W →* ℂˣ)) : Set (W →* ℂˣ)) := by
      ext χ
      constructor
      · rintro ⟨hχS, hχF⟩
        have hχF' : charSmul ρ g χ = χ := by rw [← hsmul]; exact hχF
        refine ⟨χ * χ₁⁻¹, ⟨?_, ?_⟩, inv_mul_cancel_right χ χ₁⟩
        · show χ * χ₁⁻¹ ∈ Kgrp Z
          rw [mem_Kgrp]
          intro z hz
          rw [MonoidHom.mul_apply, MonoidHom.inv_apply, hχS z hz, hχ₁S z hz, mul_inv_cancel]
        · show charSmul ρ g (χ * χ₁⁻¹) = χ * χ₁⁻¹
          apply charSmul_fixed_of_apply
          intro w
          rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.mul_apply, MonoidHom.inv_apply,
            charSmul_fixed_apply hχF', charSmul_fixed_apply hχ₁F']
      · rintro ⟨μ, ⟨hμK, hμF⟩, rfl⟩
        have hμK' : μ ∈ Kgrp Z := hμK
        rw [mem_Kgrp] at hμK'
        have hμF' : charSmul ρ g μ = μ := hμF
        refine ⟨?_, ?_⟩
        · intro z hz
          rw [MonoidHom.mul_apply, hμK' z hz, one_mul]
          exact hχ₁S z hz
        · rw [MulAction.mem_fixedBy, hsmul]
          apply charSmul_fixed_of_apply
          intro w
          rw [MonoidHom.mul_apply, MonoidHom.mul_apply, charSmul_fixed_apply hμF',
            charSmul_fixed_apply hχ₁F']
    rw [hset, Set.ncard_image_of_injective _ (mul_left_injective χ₁), ← Nat.card_coe_set_eq]
    have hdvd : Nat.card ↥(Kgrp Z ⊓ fixSub ρ g) ∣ 2 ^ n := by
      rw [← hn]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact ⟨j, hj⟩
  · left
    rw [Set.not_nonempty_iff_eq_empty] at hne
    rw [hne, Set.ncard_empty]

private theorem char_mul_self {G : Type*} [CommGroup G] (hG2 : ∀ g : G, g ^ 2 = 1) (μ : G →* ℂˣ) :
    μ * μ = 1 :=
  MonoidHom.ext fun w => by
    rw [MonoidHom.mul_apply, ← map_mul, ← sq, hG2, map_one]
    rfl

private def y5 : A7 :=
  ⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4, by rw [Perm.mem_alternatingGroup]; decide⟩

private def x7 : A7 :=
  ⟨swap 0 1 * swap 1 2 * swap 2 3 * swap 3 4 * swap 4 5 * swap 5 6, by
    rw [Perm.mem_alternatingGroup]; decide +kernel⟩

private theorem y5_pow : y5 ^ 5 = 1 := by decide +kernel

private theorem y5_ne : y5 ≠ 1 := by decide +kernel

private theorem x7_pow : x7 ^ 7 = 1 := by decide +kernel

private theorem x7_ne : x7 ≠ 1 := by decide +kernel

end Main

theorem fixV_eq_bot_of_a7 {W : Type} [CommGroup W] [Finite W] (hW2 : ∀ w : W, w ^ 2 = 1)
    (h64 : Nat.card W = 64) (ρ : A7 →* MulAut W) (hcomm : commV ρ.range = ⊤) :
    fixV ρ.range = ⊥ := by
  by_contra hZ
  have hnt : Nontrivial W := Finite.one_lt_card_iff_nontrivial.mp (by rw [h64]; norm_num)
  obtain ⟨⟨z₀, hz₀Z⟩, hz₀⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZ
  have hz₀' : z₀ ≠ 1 := fun h => hz₀ (Subtype.ext h)
  have hexp : Monoid.exponent W = 2 :=
    (Monoid.exponent_eq_prime_iff Nat.prime_two).mpr fun g hg => orderOf_eq_prime (hW2 g) hg
  have hroots : HasEnoughRootsOfUnity ℂ (Monoid.exponent W) := by rw [hexp]; infer_instance
  obtain ⟨χ₀, hχ₀⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity W ℂ hz₀'
  have hcardW : Nat.card (W →* ℂˣ) = 2 ^ 6 := by
    rw [CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity W ℂ, h64]
    norm_num
  have : Finite (W →* ℂˣ) := Nat.finite_of_card_ne_zero (by rw [hcardW]; norm_num)
  let _inst : MulDistribMulAction A7 (W →* ℂˣ) := charAct ρ
  have hsmul : ∀ (σ : A7) (χ : W →* ℂˣ), σ • χ = charSmul ρ σ χ := fun _ _ => rfl
  set Z := fixV ρ.range with hZdef
  have hZfix : ∀ σ : A7, ∀ z ∈ Z, ρ σ z = z := fun σ z hz => hz (ρ σ) ⟨σ, rfl⟩
  set S := cosetSet Z χ₀ with hS
  have hSinv : ∀ σ : A7, ∀ s ∈ S, σ • s ∈ S := fun σ s hs => charSmul_mem_cosetSet hZfix σ hs
  have hcardK : Nat.card (Kgrp Z) = Z.index := card_Kgrp hW2 Z
  have hSK : S.ncard = Z.index := by rw [ncard_cosetSet, hcardK]
  have hZcard : 2 ≤ Nat.card Z := Z.one_lt_card_iff_ne_bot.mpr hZ
  have hindex : Z.index ≤ 32 := by
    have h := Subgroup.card_mul_index Z
    rw [h64] at h
    by_contra hcon
    push Not at hcon
    nlinarith
  obtain ⟨d, hd6, hdK⟩ : ∃ d, d ≤ 6 ∧ Z.index = 2 ^ d := by
    have : Z.index ∣ 2 ^ 6 := by
      have := Subgroup.index_dvd_card Z
      rwa [h64] at this
    exact (Nat.dvd_prime_pow Nat.prime_two).mp this
  have hd5 : d ≤ 5 := by
    by_contra hcon
    push Not at hcon
    have : 2 ^ 6 ≤ 2 ^ d := Nat.pow_le_pow_right (by norm_num) hcon
    omega
  have hnofix : ∀ s ∈ S, ∃ σ : A7, σ • s ≠ s := by
    intro s hs
    by_contra hcon
    push Not at hcon
    have h1 := char_eq_one_of_fixed hcomm (fun σ => (hsmul σ s) ▸ hcon σ) z₀
    exact hχ₀ ((hs z₀ hz₀Z).symm.trans h1)
  have hpowy := fix_pow hsmul Z χ₀ y5 hcardW
  have hpowx := fix_pow hsmul Z χ₀ x7 hcardW
  rcases Nat.lt_or_ge d 5 with hd | hd
  · obtain ⟨s, hsS, hsfix⟩ := exists_fixed_of_five S hSinv (d := d) (by omega) (by rw [hSK, hdK])
      y5_pow y5_ne hpowy
    obtain ⟨σ, hσ⟩ := hnofix s hsS
    exact hσ (hsfix σ)
  · have hd5' : d = 5 := le_antisymm hd5 hd
    obtain ⟨s, hsS, hs7⟩ := exists_orbit_seven S hSinv (by rw [hSK, hdK, hd5']; norm_num)
      x7_pow x7_ne y5_pow y5_ne hpowx hpowy hnofix
    have hZ2 : ∀ z : Z, z ^ 2 = 1 := fun z => Subtype.ext (hW2 z)
    have hπ : ∀ σ : A7, MonoidHom.domRestrictHom Z ℂˣ (σ • s) = MonoidHom.domRestrictHom Z ℂˣ s := by
      intro σ
      refine MonoidHom.ext fun z => ?_
      show charSmul ρ σ s z = s z
      exact charSmul_apply_of_mem hZfix σ s z.2
    have := card_ker_ge_of_orbit_seven (M := W →* ℂˣ) (char_mul_self hW2) (Q := Z →* ℂˣ)
      (char_mul_self hZ2) (MonoidHom.domRestrictHom Z ℂˣ) s hπ hs7
    have h2 : Nat.card (MonoidHom.domRestrictHom Z ℂˣ).ker = Z.index := hcardK
    rw [h2, hdK, hd5'] at this
    omega

end CFSG.Quasithin.ModA7
