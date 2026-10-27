module

public import CFSG.RankThree.PartTwo.Sec21.Item222KLeProof

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item222Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem perm_three_cases : ∀ g : Equiv.Perm (Fin 3),
    g = 1 ∨ g = Equiv.swap 0 1 ∨ g = Equiv.swap 1 2 ∨ g = Equiv.swap 0 1 * Equiv.swap 1 2 ∨
      g = Equiv.swap 1 2 * Equiv.swap 0 1 ∨
      g = Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 0 1 := by
  decide

theorem dihedral_four_cases : ∀ g : DihedralGroup 4,
    g = 1 ∨ g = DihedralGroup.sr 0 ∨ g = DihedralGroup.sr 1 ∨
      g = DihedralGroup.sr 0 * DihedralGroup.sr 1 ∨ g = DihedralGroup.sr 1 * DihedralGroup.sr 0 ∨
      g = DihedralGroup.sr 0 * DihedralGroup.sr 1 * DihedralGroup.sr 0 ∨
      g = DihedralGroup.sr 1 * DihedralGroup.sr 0 * DihedralGroup.sr 1 ∨
      g = DihedralGroup.sr 0 * DihedralGroup.sr 1 * DihedralGroup.sr 0 * DihedralGroup.sr 1 := by
  decide

theorem perm_three_facts :
    Equiv.swap (0 : Fin 3) 1 * Equiv.swap 0 1 = 1 ∧ Equiv.swap (1 : Fin 3) 2 * Equiv.swap 1 2 = 1 ∧
      Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 ≠ Equiv.swap 1 2 * Equiv.swap 0 1 ∧
      Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 * (Equiv.swap 0 1 * Equiv.swap 1 2) *
        (Equiv.swap 0 1 * Equiv.swap 1 2) = 1 ∧
      Equiv.swap (0 : Fin 3) 1 * Equiv.swap 1 2 ≠ 1 := by
  decide

theorem dihedral_four_facts :
    DihedralGroup.sr (0 : ZMod 4) * DihedralGroup.sr 0 = 1 ∧
      DihedralGroup.sr (1 : ZMod 4) * DihedralGroup.sr 1 = 1 ∧
      DihedralGroup.sr (0 : ZMod 4) * DihedralGroup.sr 1 ≠
        DihedralGroup.sr 1 * DihedralGroup.sr 0 ∧
      DihedralGroup.sr (0 : ZMod 4) * DihedralGroup.sr 1 * (DihedralGroup.sr 0 * DihedralGroup.sr 1)
        ≠ 1 ∧
      DihedralGroup.sr (0 : ZMod 4) * DihedralGroup.sr 1 * (DihedralGroup.sr 0 * DihedralGroup.sr 1)
        * (DihedralGroup.sr 0 * DihedralGroup.sr 1) * (DihedralGroup.sr 0 * DihedralGroup.sr 1)
        = 1 := by
  decide

theorem perm_four_facts :
    let v₁ : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3
    let v₂ : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3
    v₁ * v₁ = 1 ∧ v₂ * v₂ = 1 ∧ v₁ ≠ 1 ∧ v₂ ≠ 1 ∧ v₁ * v₂ = v₂ * v₁ ∧ v₁ ≠ v₂ ∧
      Equiv.swap 1 2 * v₁ * (Equiv.swap 1 2)⁻¹ = v₂ ∧
      Equiv.swap 1 3 * v₁ * (Equiv.swap 1 3)⁻¹ = v₁ * v₂ := by
  decide

variable {M : Type*} [Group M]

theorem exists_generators_perm_three {S : Subgroup M} (e : S ≃* Equiv.Perm (Fin 3)) :
    ∃ σ₁ ∈ S, ∃ σ₂ ∈ S, σ₁ * σ₁ = 1 ∧ σ₂ * σ₂ = 1 ∧ σ₁ * σ₂ ≠ σ₂ * σ₁ ∧
      σ₁ * σ₂ * (σ₁ * σ₂) * (σ₁ * σ₂) = 1 ∧ σ₁ * σ₂ ≠ 1 ∧ S = Subgroup.closure {σ₁, σ₂} := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := perm_three_facts
  set ι : Equiv.Perm (Fin 3) →* M := S.subtype.comp e.symm.toMonoidHom with hι
  have hinj : Function.Injective ι := S.subtype_injective.comp e.symm.injective
  have hmem : ∀ a, ι a ∈ S := fun a => (e.symm a).2
  set y₁ := ι (Equiv.swap 0 1) with hy₁
  set y₂ := ι (Equiv.swap 1 2) with hy₂
  have h1 : y₁ ∈ Subgroup.closure ({y₁, y₂} : Set M) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have h2 : y₂ ∈ Subgroup.closure ({y₁, y₂} : Set M) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  refine ⟨y₁, hmem _, y₂, hmem _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hy₁, ← map_mul, f1, map_one]
  · rw [hy₂, ← map_mul, f2, map_one]
  · intro h
    rw [hy₁, hy₂, ← map_mul, ← map_mul] at h
    exact f3 (hinj h)
  · rw [hy₁, hy₂, ← map_mul, ← map_mul, ← map_mul, f4, map_one]
  · intro h
    rw [hy₁, hy₂, ← map_mul, ← map_one ι] at h
    exact f5 (hinj h)
  · apply le_antisymm
    · intro g hg
      have hcl : ∀ a : Equiv.Perm (Fin 3), ι a ∈ Subgroup.closure ({y₁, y₂} : Set M) := by
        intro a
        rcases perm_three_cases a with rfl | rfl | rfl | rfl | rfl | rfl
        · rw [map_one]
          exact Subgroup.one_mem _
        · exact h1
        · exact h2
        · rw [map_mul]
          exact Subgroup.mul_mem _ h1 h2
        · rw [map_mul]
          exact Subgroup.mul_mem _ h2 h1
        · rw [map_mul, map_mul]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h1
      have := hcl (e ⟨g, hg⟩)
      simpa [hι] using this
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hmem _
      · exact hmem _

theorem exists_generators_dihedral {S : Subgroup M} (e : S ≃* DihedralGroup 4) :
    ∃ σ₁ ∈ S, ∃ σ₂ ∈ S, σ₁ * σ₁ = 1 ∧ σ₂ * σ₂ = 1 ∧ σ₁ * σ₂ ≠ σ₂ * σ₁ ∧
      σ₁ * σ₂ * (σ₁ * σ₂) ≠ 1 ∧
      σ₁ * σ₂ * (σ₁ * σ₂) * (σ₁ * σ₂) * (σ₁ * σ₂) = 1 ∧ S = Subgroup.closure {σ₁, σ₂} := by
  obtain ⟨f1, f2, f3, f4, f5⟩ := dihedral_four_facts
  set ι : DihedralGroup 4 →* M := S.subtype.comp e.symm.toMonoidHom with hι
  have hinj : Function.Injective ι := S.subtype_injective.comp e.symm.injective
  have hmem : ∀ a, ι a ∈ S := fun a => (e.symm a).2
  set y₁ := ι (DihedralGroup.sr 0) with hy₁
  set y₂ := ι (DihedralGroup.sr 1) with hy₂
  have h1 : y₁ ∈ Subgroup.closure ({y₁, y₂} : Set M) :=
    Subgroup.subset_closure (Set.mem_insert _ _)
  have h2 : y₂ ∈ Subgroup.closure ({y₁, y₂} : Set M) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  refine ⟨y₁, hmem _, y₂, hmem _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hy₁, ← map_mul, f1, map_one]
  · rw [hy₂, ← map_mul, f2, map_one]
  · intro h
    rw [hy₁, hy₂, ← map_mul, ← map_mul] at h
    exact f3 (hinj h)
  · intro h
    rw [hy₁, hy₂, ← map_mul, ← map_mul, ← map_one ι] at h
    exact f4 (hinj h)
  · rw [hy₁, hy₂, ← map_mul, ← map_mul, ← map_mul, ← map_mul, f5, map_one]
  · apply le_antisymm
    · intro g hg
      have hcl : ∀ a : DihedralGroup 4, ι a ∈ Subgroup.closure ({y₁, y₂} : Set M) := by
        intro a
        rcases dihedral_four_cases a with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · rw [map_one]
          exact Subgroup.one_mem _
        · exact h1
        · exact h2
        · rw [map_mul]
          exact Subgroup.mul_mem _ h1 h2
        · rw [map_mul]
          exact Subgroup.mul_mem _ h2 h1
        · rw [map_mul, map_mul]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h1
        · rw [map_mul, map_mul]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ h2 h1) h2
        · rw [map_mul, map_mul, map_mul]
          exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ h1 h2) h1) h2
      have := hcl (e ⟨g, hg⟩)
      simpa [hι] using this
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact hmem _
      · exact hmem _

theorem exists_klein_perm_four {S : Subgroup M} (e : S ≃* Equiv.Perm (Fin 4)) :
    ∃ v₁ ∈ S, ∃ v₂ ∈ S, v₁ * v₁ = 1 ∧ v₂ * v₂ = 1 ∧ v₁ ≠ 1 ∧ v₂ ≠ 1 ∧ v₁ * v₂ = v₂ * v₁ ∧
      v₁ ≠ v₂ ∧ (∃ g ∈ S, g * v₁ * g⁻¹ = v₂) ∧ ∃ g ∈ S, g * v₁ * g⁻¹ = v₁ * v₂ := by
  obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8⟩ := perm_four_facts
  have hmul : ∀ a b : Equiv.Perm (Fin 4), (e.symm (a * b) : M) = e.symm a * e.symm b := by
    intro a b
    rw [map_mul, Subgroup.coe_mul]
  have hinv : ∀ a : Equiv.Perm (Fin 4), (e.symm a⁻¹ : M) = (e.symm a : M)⁻¹ := by
    intro a
    rw [map_inv, Subgroup.coe_inv]
  have hinj : ∀ {a b : Equiv.Perm (Fin 4)}, (e.symm a : M) = e.symm b → a = b := fun h =>
    e.symm.injective (Subtype.ext h)
  have hone : ((e.symm 1 : S) : M) = 1 := by rw [map_one, Subgroup.coe_one]
  refine ⟨e.symm (Equiv.swap 0 1 * Equiv.swap 2 3), (e.symm _).2,
    e.symm (Equiv.swap 0 2 * Equiv.swap 1 3), (e.symm _).2, ?_, ?_, ?_, ?_, ?_, ?_,
    ⟨e.symm (Equiv.swap 1 2), (e.symm _).2, ?_⟩, ⟨e.symm (Equiv.swap 1 3), (e.symm _).2, ?_⟩⟩
  · rw [← hmul, f1, hone]
  · rw [← hmul, f2, hone]
  · intro h
    rw [← hone] at h
    exact f3 (hinj h)
  · intro h
    rw [← hone] at h
    exact f4 (hinj h)
  · rw [← hmul, ← hmul, f5]
  · intro h
    exact f6 (hinj h)
  · rw [← hinv, ← hmul, ← hmul, f7]
  · rw [← hinv, ← hmul, ← hmul, f8, hmul]

theorem eq_closure_inter {S : Subgroup M} {D : Set M} {σ₁ σ₂ : M} (h₁ : σ₁ ∈ S) (h₂ : σ₂ ∈ S)
    (hD₁ : σ₁ ∈ D) (hD₂ : σ₂ ∈ D) (hS : S = Subgroup.closure {σ₁, σ₂}) :
    S = Subgroup.closure ((S : Set M) ∩ D) := by
  apply le_antisymm
  · calc S = Subgroup.closure {σ₁, σ₂} := hS
      _ ≤ Subgroup.closure ((S : Set M) ∩ D) := by
        rw [Subgroup.closure_le]
        rintro _ (rfl | rfl)
        · exact Subgroup.subset_closure ⟨h₁, hD₁⟩
        · exact Subgroup.subset_closure ⟨h₂, hD₂⟩
  · rw [Subgroup.closure_le]
    exact Set.inter_subset_left

variable {G : Type} [Group G]

theorem commOf_le_comap_of_mem_starOf [Finite G] {A L : Subgroup G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) {c : G} (hcA : c ∈ A)
    (hLc : L ∈ thetaComponentsAt 3 c) {φ : MulAut A} (hφL : φ ∈ starOf A L)
    (hφ2 : φ * φ = 1) : commOf φ ≤ L.comap A.subtype := by
  have hAc : ∀ a b : A, a * b = b * a := hAe.1.is_comm.comm
  obtain ⟨t, htL, htφ⟩ := hφL
  have htL' : (t : G) ∈ L := Subgroup.mem_subgroupOf.mp htL
  have hφt : ∀ a : A, ((φ a : A) : G) = (t : G) * a * (t : G)⁻¹ := fun a => by
    rw [← htφ]
    rfl
  have hφφ : ∀ a : A, φ (φ a) = a := fun a => by
    change (φ * φ) a = a
    rw [hφ2]
    rfl
  rw [commOf, Subgroup.closure_le]
  rintro _ ⟨a, rfl⟩
  change ((a⁻¹ * φ a : A) : G) ∈ L
  have hφw : φ (a⁻¹ * φ a) = (a⁻¹ * φ a)⁻¹ := by
    rw [map_mul, map_inv, hφφ]
    group
  refine mem_of_conj_eq_inv_of_mem_thetaComponentsAt hLc htL'
    (congrArg Subtype.val (hAc (a⁻¹ * φ a) ⟨c, hcA⟩)) (hAe.2 _ (a⁻¹ * φ a).2) ?_
  rw [← hφt (a⁻¹ * φ a), hφw]
  rfl

variable {P : Type*} [Group P]

theorem exists_ne_one_mem_inf [Finite P] (h27 : Nat.card P = 27)
    {B C : Subgroup P} (hB : Nat.card B = 9) (hC : Nat.card C = 9) :
    ∃ d ∈ B ⊓ C, d ≠ 1 := by
  by_contra h
  push Not at h
  have hinj : Function.Injective fun p : B × C => (p.1 : P) * p.2 := by
    rintro ⟨b, c⟩ ⟨b', c'⟩ hbc
    simp only at hbc
    have hx : (b' : P)⁻¹ * b = c' * (c : P)⁻¹ := by
      calc (b' : P)⁻¹ * b = (b' : P)⁻¹ * (b * c) * (c : P)⁻¹ := by group
        _ = (b' : P)⁻¹ * (b' * c') * (c : P)⁻¹ := by rw [hbc]
        _ = c' * (c : P)⁻¹ := by group
    have h1 : (b' : P)⁻¹ * b = 1 := h _ ⟨B.mul_mem (B.inv_mem b'.2) b.2,
      hx ▸ C.mul_mem c'.2 (C.inv_mem c.2)⟩
    have hb : b = b' := Subtype.ext (by rw [inv_mul_eq_one] at h1; exact h1.symm)
    have hc : c = c' := by
      subst hb
      have : (b : P) * c' = b * c := hbc.symm
      exact (Subtype.ext (mul_left_cancel this)).symm
    rw [hb, hc]
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, hB, hC, h27] at this
  omega

theorem eq_sup_zpowers [Finite P] (hP3 : ∀ a : P, a ^ 3 = 1) {B : Subgroup P}
    (hB : Nat.card B = 9) {c d : P} (hcB : c ∈ B) (hdB : d ∈ B) (hc1 : c ≠ 1)
    (hdc : d ∉ Subgroup.zpowers c) : B = Subgroup.zpowers c ⊔ Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set J := Subgroup.zpowers c ⊔ Subgroup.zpowers d with hJ
  have hJB : J ≤ B := sup_le (Subgroup.zpowers_le.mpr hcB) (Subgroup.zpowers_le.mpr hdB)
  have hc3 : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hP3 c) hc1]
  have hlt : Subgroup.zpowers c < J := by
    refine lt_of_le_of_ne le_sup_left fun h => hdc ?_
    rw [h]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers d)
  have hdvd : Nat.card J ∣ 9 := hB ▸ Subgroup.card_dvd_of_le hJB
  have hgt : 3 < Nat.card J := by
    rw [← hc3]
    exact Subgroup.card_lt_of_lt hlt
  have hJ9 : Nat.card J = 9 := by
    have := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card J <;> simp_all
  exact (Subgroup.eq_of_le_of_card_ge hJB (by rw [hB, hJ9])).symm

theorem centralizer_zpowers_eq (g : G) :
    Subgroup.centralizer ((Subgroup.zpowers g : Subgroup G) : Set G) =
      Subgroup.centralizer ({g} : Set G) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

theorem inf_centralizer_eq {A L : Subgroup G} {B : Subgroup A} {c d : A}
    (hB : B = Subgroup.zpowers c ⊔ Subgroup.zpowers d)
    (hLC : L ≤ Subgroup.centralizer ({(c : G)} : Set G)) :
    L ⊓ Subgroup.centralizer ((B.map A.subtype : Subgroup G) : Set G) =
      L ⊓ Subgroup.centralizer ({(d : G)} : Set G) := by
  apply le_antisymm
  · refine le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le ?_))
    rw [Set.singleton_subset_iff]
    exact ⟨d, hB ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers d), rfl⟩
  · intro x hx
    obtain ⟨hxL, hxd⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨hxL, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    set Cx : Subgroup A := (Subgroup.centralizer ({x} : Set G)).comap A.subtype with hCx
    have hcCx : c ∈ Cx := by
      change (c : G) ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hLC hxL)).symm
    have hdCx : d ∈ Cx := by
      change (d : G) ∈ Subgroup.centralizer ({x} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hxd).symm
    have hBC : B ≤ Cx := hB ▸ sup_le (Subgroup.zpowers_le.mpr hcCx) (Subgroup.zpowers_le.mpr hdCx)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hBC hb)

end CFSG.RankThree.PartTwo.Sec21.Item222Proof
