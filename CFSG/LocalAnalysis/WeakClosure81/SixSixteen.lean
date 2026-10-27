module

public import CFSG.LocalAnalysis.WeakClosure81.SixFifteen

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem card_le_of_isCyclic_of_pow_eq_one {p : ℕ} (hp : p.Prime) {X Y : Subgroup G}
    (hYX : Y ≤ X) (hexp : ∀ x ∈ X, x ^ p = 1) (hYc : IsCyclic Y) : Nat.card Y ≤ p := by
  have hexpY : Monoid.exponent Y ∣ p := by
    rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro y
    exact Subtype.ext (by simpa using hexp (y : G) (hYX y.2))
  have hcard : Monoid.exponent Y = Nat.card Y := IsCyclic.exponent_eq_card
  exact Nat.le_of_dvd hp.pos (hcard ▸ hexpY)

theorem inf_eq_bot_of_cyclic_of_prod {p : ℕ} (hp : p.Prime) {X A B : Subgroup G}
    (hAX : A ≤ X) (hBX : B ≤ X) (hexp : ∀ x ∈ X, x ^ p = 1)
    (hAc : IsCyclic A) (hBc : IsCyclic B)
    (hprod : ∀ x ∈ X, ∃ a ∈ A, ∃ b ∈ B, x = a * b)
    (hXnc : ¬ IsCyclic X) : A ⊓ B = ⊥ := by
  by_contra hne
  haveI : Nontrivial ↥(A ⊓ B) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  obtain ⟨z, hz⟩ := exists_ne (1 : ↥(A ⊓ B))
  have hzA : (z : G) ∈ A := z.2.1
  have hzB : (z : G) ∈ B := z.2.2
  have hz1 : (z : G) ≠ 1 := fun h => hz (Subtype.ext h)
  have hzp : (z : G) ^ p = 1 := hexp _ (hAX hzA)
  have hord : orderOf (z : G) = p := by
    have hdvd : orderOf (z : G) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hzp
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  have hAeq : A = Subgroup.zpowers (z : G) :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzA)
      (by rw [Nat.card_zpowers, hord]
          exact card_le_of_isCyclic_of_pow_eq_one hp hAX hexp hAc)).symm
  have hBeq : B = Subgroup.zpowers (z : G) :=
    (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzB)
      (by rw [Nat.card_zpowers, hord]
          exact card_le_of_isCyclic_of_pow_eq_one hp hBX hexp hBc)).symm
  have hXA : X ≤ A := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hprod x hx
    rw [hBeq, ← hAeq] at hb
    exact A.mul_mem ha hb
  exact hXnc ((le_antisymm hXA hAX) ▸ hAc)

theorem card_le_mul_card_of_prod {X A B : Subgroup G} (hAX : A ≤ X) (hBX : B ≤ X)
    (hprod : ∀ x ∈ X, ∃ a ∈ A, ∃ b ∈ B, x = a * b) :
    Nat.card X ≤ Nat.card A * Nat.card B := by
  have hsurj : Function.Surjective
      (fun p : ↥A × ↥B =>
        (⟨(p.1 : G) * (p.2 : G), X.mul_mem (hAX p.1.2) (hBX p.2.2)⟩ : ↥X)) := by
    intro x
    obtain ⟨a, ha, b, hb, hx⟩ := hprod x x.2
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hx.symm⟩
  have h := Nat.card_le_card_of_surjective _ hsurj
  rwa [Nat.card_prod] at h

theorem wClos_ne_bot_of_zero {V S : Subgroup G} (hV : IsElemAbelian 2 V)
    (hW0 : E3.wClos V 0 S ≠ ⊥) {j : ℕ} (hj : j < rk ↥V) : E3.wClos V j S ≠ ⊥ := by
  intro hb
  apply hW0
  exact le_bot_iff.1 ((SteinbergBS.wClos_le_wClos hV
    (card_eq_two_pow_of_isPGroup (B2F.isPGroup_of_isElemAbelian hV))
    (Nat.zero_le j) hj S) |>.trans (le_of_eq hb))

theorem six_sixteen_of_nc {V M H S X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : rankThreeIsMaxTwoLocal M) (hS : IsSylowIn 2 S H) {k : ℕ} (hk : 1 ≤ k)
    (hH : E1.InE k H) (hW0 : E3.wClos V 0 S ≠ ⊥) (hgt : k + 1 < E3.sParam hV)
    (hXM : X ≤ M) (hUY : ∀ Y : Subgroup G, Y ≤ X → ¬ IsCyclic Y → InCalU M Y)
    (hnc : ∀ i : ℕ, i ≤ k →
      ¬ IsCyclic ↥(X ⊓ Subgroup.normalizer (E3.wClos V i S : Set G)) ∨
        ¬ IsCyclic ↥(X ⊓ Subgroup.centralizer (E3.cClos V (i + 1) S : Set G))) :
    H ≤ M := by
  refine six_fifteen_four hV hM hS hk hH hW0 hgt ?_
  intro i hi
  rcases hnc i hi with h | h
  · exact Or.inl (InCalU.mono hM
      (hUY _ (show X ⊓ Subgroup.normalizer (E3.wClos V i S : Set G) ≤ X from inf_le_left) h)
      (inf_le_inf hXM le_rfl) inf_le_left)
  · exact Or.inr (InCalU.mono hM
      (hUY _ (show X ⊓ Subgroup.centralizer (E3.cClos V (i + 1) S : Set G) ≤ X from inf_le_left) h)
      (inf_le_inf hXM le_rfl) inf_le_left)

theorem six_sixteen_one_i {V M H S X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : rankThreeIsMaxTwoLocal M) (hS : IsSylowIn 2 S H) {k : ℕ} (hk : 1 ≤ k)
    (hH : E1.InE k H) (hW0 : E3.wClos V 0 S ≠ ⊥) (hgt : k + 1 < E3.sParam hV)
    {p : ℕ} (hp : p.Prime) (hXM : X ≤ M)
    (hexp : ∀ x ∈ X, x ^ p = 1) (hbig : p ^ 2 < Nat.card X)
    (hUY : ∀ Y : Subgroup G, Y ≤ X → ¬ IsCyclic Y → InCalU M Y)
    (hstar : ∀ i : ℕ, i < k + 1 → ∀ x ∈ X,
      ∃ a ∈ X ⊓ Subgroup.normalizer (E3.wClos V i S : Set G),
      ∃ b ∈ X ⊓ Subgroup.centralizer (E3.cClos V (i + 1) S : Set G), x = a * b) :
    H ≤ M := by
  refine six_sixteen_of_nc hV hM hS hk hH hW0 hgt hXM hUY ?_
  intro i hi
  by_contra h
  push Not at h
  have hprod := hstar i (by omega)
  have hcard := card_le_mul_card_of_prod (X := X)
    (A := X ⊓ Subgroup.normalizer (E3.wClos V i S : Set G))
    (B := X ⊓ Subgroup.centralizer (E3.cClos V (i + 1) S : Set G))
    (show X ⊓ Subgroup.normalizer (E3.wClos V i S : Set G) ≤ X from inf_le_left)
    (show X ⊓ Subgroup.centralizer (E3.cClos V (i + 1) S : Set G) ≤ X from inf_le_left) hprod
  have h1 := card_le_of_isCyclic_of_pow_eq_one hp
    (show X ⊓ Subgroup.normalizer (E3.wClos V i S : Set G) ≤ X from inf_le_left) hexp h.1
  have h2 := card_le_of_isCyclic_of_pow_eq_one hp
    (show X ⊓ Subgroup.centralizer (E3.cClos V (i + 1) S : Set G) ≤ X from inf_le_left) hexp h.2
  have : Nat.card X ≤ p ^ 2 := by nlinarith [hcard, h1, h2]
  omega

theorem six_sixteen_one_iii {V M H S X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : rankThreeIsMaxTwoLocal M) (hS : IsSylowIn 2 S H) {k : ℕ} (hk : 1 ≤ k)
    (hH : E1.InE k H) (hW0 : E3.wClos V 0 S ≠ ⊥) (hgt : k + 1 < E3.sParam hV)
    (hXM : X ≤ M) (hXnc : ¬ IsCyclic X)
    (hIrr : UC22.IrrOn (Subgroup.normalizer (X : Set G) ⊓
        Subgroup.normalizer (S : Set G)) X)
    (hUY : ∀ Y : Subgroup G, Y ≤ X → ¬ IsCyclic Y → InCalU M Y)
    (hstar : ∀ i : ℕ, i < k + 1 → ∀ x ∈ X,
      ∃ a ∈ X ⊓ Subgroup.normalizer (E3.wClos V i S : Set G),
      ∃ b ∈ X ⊓ Subgroup.centralizer (E3.cClos V (i + 1) S : Set G), x = a * b) :
    H ≤ M := by
  refine six_sixteen_of_nc hV hM hS hk hH hW0 hgt hXM hUY ?_
  intro i hi
  let R : Subgroup G := Subgroup.normalizer (X : Set G) ⊓ Subgroup.normalizer (S : Set G)
  have hWN : R ≤ Subgroup.normalizer
      (X ⊓ Subgroup.normalizer (E3.wClos V i S : Set G) : Set G) := by
    refine A1a.le_normalizer_inf (show R ≤ Subgroup.normalizer (X : Set G) from inf_le_left) ?_
    exact ((show R ≤ Subgroup.normalizer (S : Set G) from inf_le_right).trans
      (E3.normalizer_le_normalizer_wClos (V := V) (i := i) S)).trans Subgroup.le_normalizer
  have hRC : R ≤ Subgroup.normalizer
      (Subgroup.centralizer (E3.cClos V (i + 1) S : Set G) : Set G) := by
    intro r hr
    rw [← conjSubgroup_eq_iff_mem_normalizer] at ⊢
    rw [E3.conjSubgroup_centralizer]
    have hrc : conjSubgroup (E3.cClos V (i + 1) S) r = E3.cClos V (i + 1) S :=
      conjSubgroup_eq_iff_mem_normalizer.2
        (((show R ≤ Subgroup.normalizer (S : Set G) from inf_le_right).trans
          (E3.normalizer_le_normalizer_cClos (V := V) (i := i + 1) S)) hr)
    rw [hrc]
  have hWC : R ≤ Subgroup.normalizer
      (X ⊓ Subgroup.centralizer (E3.cClos V (i + 1) S : Set G) : Set G) :=
    A1a.le_normalizer_inf (show R ≤ Subgroup.normalizer (X : Set G) from inf_le_left) hRC
  rcases hIrr _ inf_le_left hWN with hN | hN
  · rcases hIrr _ inf_le_left hWC with hC | hC
    · exfalso
      apply hXnc
      have hXbot : X ≤ ⊥ := by
        intro x hx
        obtain ⟨a, ha, b, hb, rfl⟩ := hstar i (by omega) x hx
        rw [hN] at ha
        rw [hC] at hb
        simp only [Subgroup.mem_bot] at ha hb
        simp [ha, hb]
      exact (le_bot_iff.1 hXbot).symm ▸ (inferInstance : IsCyclic (⊥ : Subgroup G))
    · exact Or.inr fun hc => hXnc (hC ▸ hc)
  · exact Or.inl fun hc => hXnc (hN ▸ hc)

theorem six_sixteen_B {V M S X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : rankThreeIsMaxTwoLocal M) (hXM : X ≤ M)
    {k : ℕ} {i : ℕ} (hik : i ≤ k) (hWk : k + 2 < rk ↥V)
    {p : ℕ} (hp : p.Prime) (hXnc : ¬ IsCyclic X) (hexp : ∀ x ∈ X, x ^ p = 1)
    (hUY : ∀ Y : Subgroup G, Y ≤ X → ¬ IsCyclic Y → InCalU M Y)
    (hstar : ∀ j : ℕ, j < k + 2 → ∀ x ∈ X,
      ∃ a ∈ X ⊓ Subgroup.normalizer (E3.wClos V j S : Set G),
      ∃ b ∈ X ⊓ Subgroup.centralizer (E3.cClos V (j + 1) S : Set G), x = a * b) :
    InCalU M (M ⊓ Subgroup.normalizer (E3.wClos V i S : Set G)) ∨
      InCalU M (M ⊓ Subgroup.normalizer (centerOf (E3.wClos V (i + 1) S) : Set G)) ∨
      InCalU M (M ⊓ Subgroup.centralizer (E3.cClos V (i + 2) S : Set G)) := by
  by_cases hcyc : IsCyclic
        ↥(X ⊓ Subgroup.normalizer (centerOf (E3.wClos V (i + 1) S) : Set G)) ∧
      IsCyclic ↥(X ⊓ Subgroup.centralizer (E3.cClos V (i + 2) S : Set G))
  ·
    have hP1 : X ⊓ Subgroup.normalizer (centerOf (E3.wClos V (i + 1) S) : Set G) ≤ X :=
      (show X ⊓ Subgroup.normalizer (centerOf (E3.wClos V (i + 1) S) : Set G) ≤ X from inf_le_left)
    have hP2 : X ⊓ Subgroup.centralizer (E3.cClos V (i + 2) S : Set G) ≤ X :=
      (show X ⊓ Subgroup.centralizer (E3.cClos V (i + 2) S : Set G) ≤ X from inf_le_left)
    have hprod : ∀ x ∈ X,
        ∃ a ∈ X ⊓ Subgroup.normalizer (centerOf (E3.wClos V (i + 1) S) : Set G),
        ∃ b ∈ X ⊓ Subgroup.centralizer (E3.cClos V (i + 2) S : Set G), x = a * b := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hstar (i + 1) (by omega) x hx
      exact ⟨a, ⟨ha.1, (E3.normalizer_le_normalizer_centerOf (E3.wClos V (i + 1) S)) ha.2⟩,
        b, hb, rfl⟩
    have hdisj := inf_eq_bot_of_cyclic_of_prod hp hP1 hP2 hexp hcyc.1 hcyc.2 hprod hXnc
    have hC1le : X ⊓ Subgroup.centralizer (E3.cClos V (i + 1) S : Set G) ≤
        X ⊓ Subgroup.normalizer (centerOf (E3.wClos V (i + 1) S) : Set G) :=
      inf_le_inf le_rfl ((Subgroup.centralizer_le (centerOf_wClos_le_cClos_self (i + 1) S)).trans
        (Subgroup.centralizer_le_normalizer _))
    have hC2le : X ⊓ Subgroup.centralizer (E3.cClos V (i + 1) S : Set G) ≤
        X ⊓ Subgroup.centralizer (E3.cClos V (i + 2) S : Set G) :=
      inf_le_inf le_rfl (Subgroup.centralizer_le (cClos_anti (V := V) hV (i := i + 1)
        (j := i + 2) (by omega) (by omega) S))
    have hCbot : X ⊓ Subgroup.centralizer (E3.cClos V (i + 1) S : Set G) = ⊥ :=
      le_bot_iff.1 (le_inf hC1le hC2le |>.trans (le_of_eq hdisj))
    have hXNW : X ≤ X ⊓ Subgroup.normalizer (E3.wClos V i S : Set G) := by
      intro x hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hstar i (by omega) x hx
      have hb' : b = 1 := by
        have : b ∈ (⊥ : Subgroup G) := hCbot ▸ hb
        simpa using this
      refine ⟨?_, ?_⟩
      · exact X.mul_mem ha.1 (by rw [hb']; exact X.one_mem)
      · rw [hb', mul_one]
        exact ha.2
    have hNc : ¬ IsCyclic ↥(X ⊓ Subgroup.normalizer (E3.wClos V i S : Set G)) := fun hc =>
      hXnc (le_antisymm inf_le_left hXNW ▸ hc)
    exact Or.inl (InCalU.mono hM
      (hUY _ (show X ⊓ Subgroup.normalizer (E3.wClos V i S : Set G) ≤ X from inf_le_left) hNc)
      (inf_le_inf hXM le_rfl) inf_le_left)
  · have hcyc' : ¬ IsCyclic ↥(X ⊓ Subgroup.normalizer (centerOf (E3.wClos V (i + 1) S) : Set G)) ∨
        ¬ IsCyclic ↥(X ⊓ Subgroup.centralizer (E3.cClos V (i + 2) S : Set G)) :=
      not_and_or.mp hcyc
    rcases hcyc' with hcyc | hcyc
    · exact Or.inr (Or.inl (InCalU.mono hM
        (hUY _ (show X ⊓ Subgroup.normalizer (centerOf (E3.wClos V (i + 1) S) : Set G) ≤ X from
          inf_le_left) hcyc)
        (inf_le_inf hXM le_rfl) inf_le_left))
    · exact Or.inr (Or.inr (InCalU.mono hM
        (hUY _ (show X ⊓ Subgroup.centralizer (E3.cClos V (i + 2) S : Set G) ≤ X from inf_le_left)
          hcyc)
        (inf_le_inf hXM le_rfl) inf_le_left))

theorem six_sixteen_two {V M H S X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : rankThreeIsMaxTwoLocal M) (hS : IsSylowIn 2 S H) {k : ℕ} (hk : 1 ≤ k)
    (hH : E1.InE k H) (hW0 : E3.wClos V 0 S ≠ ⊥) (hgt : k + 2 < E3.sParam hV)
    {p : ℕ} (hp : p.Prime) (hXM : X ≤ M) (hXnc : ¬ IsCyclic X)
    (hexp : ∀ x ∈ X, x ^ p = 1)
    (hUY : ∀ Y : Subgroup G, Y ≤ X → ¬ IsCyclic Y → InCalU M Y)
    (hstar : ∀ i : ℕ, i < k + 2 → ∀ x ∈ X,
      ∃ a ∈ X ⊓ Subgroup.normalizer (E3.wClos V i S : Set G),
      ∃ b ∈ X ⊓ Subgroup.centralizer (E3.cClos V (i + 1) S : Set G), x = a * b) :
    H ≤ M := by
  by_contra hHM
  have hsV : E3.sParam hV ≤ rk ↥V := E3.sParam_le_rk hV
  have hS2 : IsPGroup 2 S := hS.isPGroup
  have hVk : k + 2 < rk ↥V := lt_of_lt_of_le hgt hsV
  have hfac0 := e3_19_of_inE hV hS (i := 0) (j := k) hH (by omega)
  have hfac1 := e3_19_of_inE hV hS (i := 1) (j := k) hH (by omega)
  have hfac2 := e3_19_of_inE hV hS (i := 2) (j := k) hH (by omega)
  have hstep1 : ¬ InCalU M (M ⊓ Subgroup.centralizer (E3.cClos V 2 S : Set G)) := by
    intro hU1
    have h2 := six_fifteen_two' hV hM hS2 hW0 (i := 2) (by omega) hU1
    have hC : Subgroup.centralizer (E3.cClos V (2 + k) S : Set G) ≤ M := h2.1 (2 + k) (by omega)
    have hN : Subgroup.normalizer (E3.wClos V 2 S : Set G) ≤ M := h2.2.1 2 le_rfl (by omega)
    apply hHM
    rw [← hfac2]
    exact sup_le (by simpa using inf_le_right.trans hC) (by simpa using inf_le_right.trans hN)
  have hB0 := six_sixteen_B hV hM hXM (k := k) (i := 0) (Nat.zero_le k) hVk hp hXnc hexp hUY hstar
  have hN1 : Subgroup.normalizer (E3.wClos V 1 S : Set G) ≤ M := by
    rcases hB0 with h | h | h
    · have h3 := six_fifteen_three hV hM hS2 hW0 (i := 0) (by omega) h
      exact h3.1 1 (by omega)
    · have hZ1ne : centerOf (E3.wClos V 1 S) ≠ ⊥ :=
        E3.centerOf_ne_bot_of_isPGroup (hS2.to_le (E3.wClos_le 1 S))
          (wClos_ne_bot_of_zero hV hW0 (by omega))
      have hNZ : Subgroup.normalizer (centerOf (E3.wClos V 1 S) : Set G) ≤ M :=
        normalizer_le_of_inCalU h inf_le_right hZ1ne
          ((hS2.to_le (E3.wClos_le 1 S)).to_le inf_le_left)
      exact (E3.normalizer_le_normalizer_centerOf _).trans hNZ
    · exact absurd h hstep1
  have hN2 : Subgroup.normalizer (E3.wClos V 2 S : Set G) ≤ M :=
    (normalizer_wClos_anti (V := V) (S := S) hV (i := 1) (j := 2) (by omega) (by omega)).trans hN1
  have hNk : InCalU M (M ⊓ Subgroup.normalizer (E3.wClos V k S : Set G)) := by
    have hBk := six_sixteen_B hV hM hXM (k := k) (i := k) le_rfl hVk hp hXnc hexp hUY hstar
    rcases hBk with h | h | h
    · exact h
    · exfalso
      apply hHM
      have hZne : centerOf (E3.wClos V (k + 1) S) ≠ ⊥ :=
        E3.centerOf_ne_bot_of_isPGroup (hS2.to_le (E3.wClos_le (k + 1) S))
          (wClos_ne_bot_of_zero hV hW0 (by omega))
      have hNZ : Subgroup.normalizer (centerOf (E3.wClos V (k + 1) S) : Set G) ≤ M :=
        normalizer_le_of_inCalU h inf_le_right hZne
          ((hS2.to_le (E3.wClos_le (k + 1) S)).to_le inf_le_left)
      have hCk1 : Subgroup.centralizer (E3.cClos V (1 + k) S : Set G) ≤ M := by
        have h := (Subgroup.centralizer_le (centerOf_wClos_le_cClos_self (k + 1) S)).trans
          ((Subgroup.centralizer_le_normalizer _).trans hNZ)
        simpa [Nat.add_comm] using h
      rw [← hfac1]
      exact sup_le (by simpa using inf_le_right.trans hCk1)
        (by simpa using inf_le_right.trans hN1)
    · exfalso
      apply hHM
      have h2 := six_fifteen_two' hV hM hS2 hW0 (i := k + 2) (by omega) h
      have hC : Subgroup.centralizer (E3.cClos V (2 + k) S : Set G) ≤ M := by
        have h := h2.1 (k + 2) (by omega)
        simpa [Nat.add_comm] using h
      rw [← hfac2]
      exact sup_le (by simpa using inf_le_right.trans hC)
        (by simpa using inf_le_right.trans hN2)
  have h3 := six_fifteen_three hV hM hS2 hW0 (i := k) (by omega) hNk
  apply hHM
  rw [← hfac0]
  exact sup_le (by simpa using inf_le_right.trans (h3.2 0 (Nat.zero_le k)))
    (by simpa using inf_le_right.trans (h3.1 0 (by omega)))

end CFSG.LocalAnalysis.WeakClosure81
