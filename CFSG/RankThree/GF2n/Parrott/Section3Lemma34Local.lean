module

public import CFSG.Assembly.Defs
public import CFSG.SignalizerFunctorTheorem.Inheritance.Diagonal

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open

section Abstract

variable {M : Type} [Group M] [Finite M] (π : M →* Equiv.Perm (Fin 5))

private theorem card_eq_of_surjective_permFive (hs : Function.Surjective π)
    (hk : Nat.card π.ker = 16) : Nat.card M = 1920 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup π.ker
  have h2 : Nat.card (M ⧸ π.ker) = 120 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective π hs).toEquiv,
      Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    rfl
  rw [h1, h2, hk]

private theorem index_centralizer_eq_fifteen (hk : Nat.card π.ker = 16)
    (htr : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a ≠ 1 → b ≠ 1 → ∃ g : M, g * a * g⁻¹ = b)
    {a : M} (ha : a ∈ π.ker) (ha1 : a ≠ 1) :
    (Subgroup.centralizer ({a} : Set M)).index = 15 := by
  rw [Subgroup.index_centralizer_eq_ncard]
  have hset : conjugatesOf a = (π.ker : Set M) \ {1} := by
    ext b
    constructor
    · intro hb
      obtain ⟨c, hc⟩ := isConj_iff.1 hb
      refine ⟨?_, ?_⟩
      · rw [← hc]
        exact (π.normal_ker).conj_mem a ha c
      · rintro (h : b = 1)
        apply ha1
        rw [h] at hc
        simpa using hc
    · rintro ⟨hb, hb1⟩
      obtain ⟨g, hg⟩ := htr a ha b hb ha1 hb1
      exact isConj_iff.2 ⟨g, hg⟩
  rw [hset, Set.ncard_diff_singleton_of_mem (by exact one_mem π.ker), ← Nat.card_coe_set_eq]
  change Nat.card π.ker - 1 = 15
  omega

private theorem card_centralizer_eq_of_permFive (hs : Function.Surjective π)
    (hk : Nat.card π.ker = 16)
    (htr : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a ≠ 1 → b ≠ 1 → ∃ g : M, g * a * g⁻¹ = b)
    {a : M} (ha : a ∈ π.ker) (ha1 : a ≠ 1) :
    Nat.card (Subgroup.centralizer ({a} : Set M)) = 128 := by
  have h := Subgroup.card_mul_index (Subgroup.centralizer ({a} : Set M))
  rw [index_centralizer_eq_fifteen π hk htr ha ha1, card_eq_of_surjective_permFive π hs hk] at h
  omega

private theorem centralizer_ker_le_ker_of_permFive (hs : Function.Surjective π)
    (hk : Nat.card π.ker = 16)
    (htr : ∀ a ∈ π.ker, ∀ b ∈ π.ker, a ≠ 1 → b ≠ 1 → ∃ g : M, g * a * g⁻¹ = b) :
    Subgroup.centralizer (π.ker : Set M) ≤ π.ker := by
  have hker : π.ker ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hk
    omega
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hker
  have ha1' : (a : M) ≠ 1 := fun h => ha1 (Subtype.ext h)
  set C := Subgroup.centralizer (π.ker : Set M) with hC
  have hCa : C ≤ Subgroup.centralizer ({(a : M)} : Set M) :=
    Subgroup.centralizer_le (by simpa using a.2)
  have hcard : Nat.card C ∣ 128 := by
    rw [← card_centralizer_eq_of_permFive π hs hk htr a.2 ha1']
    exact Subgroup.card_dvd_of_le hCa
  have hnorm : (C.map π).Normal := Subgroup.Normal.map inferInstance π hs
  by_contra hnot
  have hne : C.map π ≠ ⊥ := by
    intro h
    exact hnot ((Subgroup.map_eq_bot_iff C).1 h)
  haveI : Nontrivial (C.map π) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  have hA := Equiv.Perm.alternatingGroup_le_of_normal (α := Fin 5) (by simp) (N := C.map π) this
  have hA60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    have h120 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    have := two_mul_nat_card_alternatingGroup (α := Fin 5)
    rw [h120] at this
    omega
  have h60 : 60 ∣ 128 :=
    hA60 ▸ (Subgroup.card_dvd_of_le hA).trans ((Subgroup.card_map_dvd C π).trans hcard)
  omega

private theorem eq_comap_alternatingGroup_of_index_two (hs : Function.Surjective π)
    {L : Subgroup M} (hker : π.ker ≤ L) (hL : L.index = 2) :
    L = (alternatingGroup (Fin 5)).comap π := by
  have h1 : L = (L.map π).comap π := (Subgroup.comap_map_eq_self hker).symm
  have h2 : ((L.map π).comap π).index = (L.map π).index :=
    Subgroup.index_comap_of_surjective (L.map π) hs
  rw [← h1] at h2
  have h3 : (L.map π).index = 2 := h2 ▸ hL
  rw [h1, Equiv.Perm.eq_alternatingGroup_of_index_eq_two h3]

end Abstract

section InsideY

variable {Y : Type} [Group Y] [Finite Y] {M D : Subgroup Y}

theorem exists_mem_ne_one_ne_of_two_lt_card (hD : 2 < Nat.card D) (d : Y) :
    ∃ e ∈ D, e ≠ 1 ∧ e ≠ d := by
  by_contra hcon
  push Not at hcon
  have hsub : (D : Set Y) ⊆ {1, d} := by
    intro e he
    by_cases h1 : e = 1
    · simp [h1]
    · simp [hcon e he h1]
  have h2 : (D : Set Y).ncard ≤ ({1, d} : Set Y).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h3 : ({1, d} : Set Y).ncard ≤ 2 := by
    refine (Set.ncard_insert_le _ _).trans ?_
    rw [Set.ncard_singleton]
  rw [← Nat.card_coe_set_eq] at h2
  have h4 : Nat.card (D : Set Y) = Nat.card D := rfl
  omega

theorem card_ker_eq_card_of_eq_subgroupOf (hDM : D ≤ M) {π : ↥M →* Equiv.Perm (Fin 5)}
    (hk : π.ker = D.subgroupOf M) : Nat.card π.ker = Nat.card D := by
  rw [hk]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDM).toEquiv

theorem ker_transitive_of_eq_subgroupOf {π : ↥M →* Equiv.Perm (Fin 5)}
    (hk : π.ker = D.subgroupOf M)
    (hTrans : ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ M, g * a * g⁻¹ = b) :
    ∀ a ∈ π.ker, ∀ b ∈ π.ker, a ≠ 1 → b ≠ 1 → ∃ g : ↥M, g * a * g⁻¹ = b := by
  intro a ha b hb ha1 hb1
  rw [hk, Subgroup.mem_subgroupOf] at ha hb
  obtain ⟨g, hg, hgab⟩ := hTrans a ha b hb (fun h => ha1 (Subtype.ext h))
    (fun h => hb1 (Subtype.ext h))
  exact ⟨⟨g, hg⟩, Subtype.ext hgab⟩

theorem local_data_of_permFive (hDM : D ≤ M) (hD16 : Nat.card D = 16)
    (hπ : ∃ π : ↥M →* Equiv.Perm (Fin 5), Function.Surjective π ∧ π.ker = D.subgroupOf M)
    (hTrans : ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ M, g * a * g⁻¹ = b)
    (hCent : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer ({d} : Set Y) ≤ M) :
    Nat.card M = 1920 ∧ (∀ g ∈ M, ∀ d ∈ D, g * d * g⁻¹ ∈ D) ∧
      (∀ g ∈ M, (∀ d ∈ D, g * d = d * g) → g ∈ D) ∧
      ∀ d ∈ D, d ≠ 1 → Nat.card (Subgroup.centralizer ({d} : Set Y)) = 128 := by
  obtain ⟨π, hs, hk⟩ := hπ
  have hkcard : Nat.card π.ker = 16 := (card_ker_eq_card_of_eq_subgroupOf hDM hk).trans hD16
  have htr := ker_transitive_of_eq_subgroupOf hk hTrans
  refine ⟨card_eq_of_surjective_permFive π hs hkcard, ?_, ?_, ?_⟩
  · intro g hg d hd
    have hd' : (⟨d, hDM hd⟩ : ↥M) ∈ π.ker := by rw [hk]; exact hd
    have := (π.normal_ker).conj_mem _ hd' ⟨g, hg⟩
    rw [hk] at this
    exact this
  · intro g hg hcomm
    have hmem : (⟨g, hg⟩ : ↥M) ∈ Subgroup.centralizer (π.ker : Set ↥M) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk'
      have hk'' : (k : Y) ∈ D := by
        have : k ∈ D.subgroupOf M := by rw [← hk]; exact hk'
        exact this
      exact Subtype.ext (hcomm k hk'').symm
    have := centralizer_ker_le_ker_of_permFive π hs hkcard htr hmem
    rw [hk, Subgroup.mem_subgroupOf] at this
    exact this
  · intro d hd hd1
    have hdker : (⟨d, hDM hd⟩ : ↥M) ∈ π.ker := by rw [hk]; exact hd
    have h128 := card_centralizer_eq_of_permFive π hs hkcard htr hdker
      (fun h => hd1 (congrArg Subtype.val h))
    have heq : Subgroup.centralizer ({(⟨d, hDM hd⟩ : ↥M)} : Set ↥M) =
        (Subgroup.centralizer ({d} : Set Y)).subgroupOf M := by
      ext x
      rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf,
        Subgroup.mem_centralizer_singleton_iff]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [heq] at h128
    rw [← h128]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hCent d hd hd1)).toEquiv).symm

theorem isPGroup_and_not_two_dvd_index_of_card_eq (hM : Nat.card M = 1920)
    (hodd : Odd M.index) {C : Subgroup Y} (hC : Nat.card C = 128) :
    IsPGroup 2 C ∧ ¬ 2 ∣ C.index := by
  refine ⟨IsPGroup.of_card (n := 7) (by rw [hC]; norm_num), ?_⟩
  have h1 := Subgroup.card_mul_index M
  have h2 := Subgroup.card_mul_index C
  rw [hM] at h1
  rw [hC] at h2
  have := Nat.odd_iff.1 hodd
  omega

theorem not_le_of_odd_index_of_index_two (hodd : Odd M.index) {K : Subgroup Y}
    (hK2 : K.index = 2) : ¬ M ≤ K := by
  intro hMK
  have h := Subgroup.relIndex_mul_index hMK
  rw [hK2] at h
  have := Nat.odd_iff.1 hodd
  omega

theorem le_of_index_two_of_transitive (hD16 : Nat.card D = 16)
    (hTrans : ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ M, g * a * g⁻¹ = b)
    {K : Subgroup Y} [K.Normal] (hK2 : K.index = 2) : D ≤ K := by
  intro d hd
  by_contra hdK
  have hd1 : d ≠ 1 := fun h => hdK (h ▸ K.one_mem)
  have hout : ∀ e ∈ D, e ≠ 1 → e ∉ K := by
    intro e he he1 heK
    obtain ⟨g, -, hg⟩ := hTrans e he d hd he1 hd1
    apply hdK
    rw [← hg]
    exact (inferInstance : K.Normal).conj_mem e heK g
  obtain ⟨e, he, he1, hed⟩ := exists_mem_ne_one_ne_of_two_lt_card (D := D) (by omega) d⁻¹
  have hde : d * e ∈ D := D.mul_mem hd he
  have hde1 : d * e ≠ 1 := by
    intro h
    exact hed (eq_inv_of_mul_eq_one_right h)
  have h3 := (Subgroup.mul_mem_iff_of_index_two hK2).2 (iff_of_false hdK (hout e he he1))
  exact hout (d * e) hde hde1 h3

theorem relIndex_eq_two_of_index_two {K : Subgroup Y} [K.Normal] (hMK : ¬ M ≤ K)
    (hK2 : K.index = 2) : K.relIndex M = 2 := by
  have h1 : K.relIndex M ∣ K.index := Subgroup.relIndex_dvd_index_of_normal K M
  rw [hK2] at h1
  have h2 : K.relIndex M ≠ 1 := fun h => hMK (Subgroup.relIndex_eq_one.1 h)
  rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
  · exact absurd h h2
  · exact h

theorem card_inf_eq_of_relIndex_two (hM : Nat.card M = 1920) {K : Subgroup Y}
    (hK : K.relIndex M = 2) : Nat.card (K ⊓ M : Subgroup Y) = 960 := by
  have h := Subgroup.relIndex_mul_card (H := K) (K := M)
  rw [hK, hM] at h
  omega

private theorem subgroupOf_eq_comap_of_relIndex_two {π : ↥M →* Equiv.Perm (Fin 5)}
    (hs : Function.Surjective π) (hk : π.ker = D.subgroupOf M) {L : Subgroup Y} (hDL : D ≤ L)
    (hL2 : L.relIndex M = 2) : L.subgroupOf M = (alternatingGroup (Fin 5)).comap π := by
  apply eq_comap_alternatingGroup_of_index_two π hs
  · rw [hk]
    intro x hx
    exact Subgroup.mem_subgroupOf.2 (hDL (Subgroup.mem_subgroupOf.1 hx))
  · exact hL2

theorem eq_inf_of_relIndex_two {π : ↥M →* Equiv.Perm (Fin 5)}
    (hs : Function.Surjective π) (hk : π.ker = D.subgroupOf M) {K : Subgroup Y} (hDK : D ≤ K)
    (hK : K.relIndex M = 2) :
    ∀ L : Subgroup Y, D ≤ L → L ≤ M → L.relIndex M = 2 → L = K ⊓ M := by
  intro L hDL hLM hL2
  have h1 := subgroupOf_eq_comap_of_relIndex_two hs hk hDL hL2
  have h2 := subgroupOf_eq_comap_of_relIndex_two hs hk hDK hK
  rw [← h2, Subgroup.subgroupOf_inj, inf_of_le_left hLM] at h1
  rw [h1]

theorem exists_mem_inf_conj_eq_of_index_two
    (hCent : ∀ d ∈ D, d ≠ 1 → Subgroup.centralizer ({d} : Set Y) ≤ M)
    (hC128 : ∀ d ∈ D, d ≠ 1 → Nat.card (Subgroup.centralizer ({d} : Set Y)) = 128)
    (hTrans : ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ M, g * a * g⁻¹ = b)
    {K : Subgroup Y} [K.Normal] (hK2 : K.index = 2)
    (hcard : Nat.card (K ⊓ M : Subgroup Y) = 960) :
    ∀ a ∈ D, ∀ b ∈ D, a ≠ 1 → b ≠ 1 → ∃ g ∈ K ⊓ M, g * a * g⁻¹ = b := by
  intro a ha b hb ha1 hb1
  obtain ⟨g, hgM, hg⟩ := hTrans a ha b hb ha1 hb1
  by_cases hgK : g ∈ K
  · exact ⟨g, Subgroup.mem_inf.2 ⟨hgK, hgM⟩, hg⟩
  · have hcK : ∃ c ∈ Subgroup.centralizer ({a} : Set Y), c ∉ K := by
      by_contra hcon
      push Not at hcon
      have hle : Subgroup.centralizer ({a} : Set Y) ≤ K ⊓ M := fun c hc =>
        Subgroup.mem_inf.2 ⟨hcon c hc, hCent a ha ha1 hc⟩
      have h := Subgroup.card_dvd_of_le hle
      rw [hC128 a ha ha1, hcard] at h
      omega
    obtain ⟨c, hc, hcK⟩ := hcK
    refine ⟨g * c, ?_, ?_⟩
    · refine Subgroup.mem_inf.2 ⟨?_, M.mul_mem hgM (hCent a ha ha1 hc)⟩
      exact (Subgroup.mul_mem_iff_of_index_two hK2).2 (iff_of_false hgK hcK)
    · have hca : c * a = a * c := Subgroup.mem_centralizer_singleton_iff.1 hc
      calc g * c * a * (g * c)⁻¹ = g * (c * a * c⁻¹) * g⁻¹ := by group
        _ = g * a * g⁻¹ := by rw [hca]; group
        _ = b := hg

theorem exists_hom_alternatingGroup_of_relIndex_two (hDM : D ≤ M)
    (hπ : ∃ π : ↥M →* Equiv.Perm (Fin 5), Function.Surjective π ∧ π.ker = D.subgroupOf M)
    {K : Subgroup Y} (hDK : D ≤ K) (hK : K.relIndex M = 2) :
    ∃ φ : ↥(K ⊓ M) →* alternatingGroup (Fin 5), Function.Surjective φ ∧
      φ.ker = D.subgroupOf (K ⊓ M) := by
  obtain ⟨π, hs, hk⟩ := hπ
  have hKM := subgroupOf_eq_comap_of_relIndex_two hs hk hDK hK
  let ι : ↥(K ⊓ M) →* ↥M := Subgroup.inclusion inf_le_right
  have hmem : ∀ x : ↥(K ⊓ M), π (ι x) ∈ alternatingGroup (Fin 5) := by
    intro x
    have h1 : ι x ∈ K.subgroupOf M := Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.1 x.2).1
    rw [hKM] at h1
    exact h1
  refine ⟨(π.comp ι).codRestrict (alternatingGroup (Fin 5)) hmem, ?_, ?_⟩
  · intro σ
    obtain ⟨m, hm⟩ := hs (σ : Equiv.Perm (Fin 5))
    have h1 : m ∈ K.subgroupOf M := by
      rw [hKM]
      change π m ∈ alternatingGroup (Fin 5)
      rw [hm]
      exact σ.2
    exact ⟨⟨(m : Y), Subgroup.mem_inf.2 ⟨Subgroup.mem_subgroupOf.1 h1, m.2⟩⟩,
      Subtype.ext hm⟩
  · ext x
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : π (ι x) = 1 := congrArg Subtype.val h
      have h2 : ι x ∈ π.ker := h1
      rw [hk] at h2
      exact Subgroup.mem_subgroupOf.1 h2
    · intro h
      apply Subtype.ext
      have h2 : ι x ∈ D.subgroupOf M := Subgroup.mem_subgroupOf.2 h
      rw [← hk] at h2
      exact h2

end InsideY

end CFSG.RankThree.GF2n.Parrott
