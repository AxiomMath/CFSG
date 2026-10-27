module

public import CFSG.RankThree.GF2n.Stroth80.Sec101Extend
public import CFSG.RankThree.GF2n.Stroth80.Sec101Swap
public import CFSG.RankThree.GF2n.Stroth80.Sec101Roots

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem not_le_sup_Z_of_mem_QB (hc : Ctx M Q Z B) {C E : Subgroup G}
    (hC : IsRootB M B C) (hE : IsRootB M B E) {β : G} (hβQ : β ∈ Q) (hβC : β ∈ QB C)
    (hβE : β ∉ QB E) : ¬ C ≤ E ⊔ Z := by
  intro hCZ
  have hCZE : C ≤ Z ⊔ E := by rwa [sup_comm] at hCZ
  obtain ⟨p, hpQ, hpC⟩ := (hE.ctx hc).exists_conj_of_le_ZB (hC.ctx hc) hCZE
  have hInf : Q ⊓ QB C = Q ⊓ QB E := by
    rw [← hpC]
    exact (hE.ctx hc).conj_inf_QB_of_mem_Q hpQ
  apply hβE
  have hβ : β ∈ Q ⊓ QB C := ⟨hβQ, hβC⟩
  have hβ' : β ∈ Q ⊓ QB E := by rwa [hInf] at hβ
  exact hβ'.2

private theorem mem_centralizer_conj_of_forall_comm {E Z : Subgroup G} {ν β : G}
    (hνE : conjSubgroup ν E = Z) (hcomm : ∀ e ∈ E, β * e = e * β) :
    ν * β * ν⁻¹ ∈ Subgroup.centralizer (Z : Set G) := by
  refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
  have hzE : ν⁻¹ * z * ν ∈ E := by
    have h : z ∈ conjSubgroup ν E := by rwa [hνE]
    exact mem_conjSubgroup.mp h
  have hc := hcomm (ν⁻¹ * z * ν) hzE
  have h1 : z * (ν * β * ν⁻¹) = ν * ((ν⁻¹ * z * ν) * β) * ν⁻¹ := by group
  have h2 : ν * ((ν⁻¹ * z * ν) * β) * ν⁻¹ =
      ν * (β * (ν⁻¹ * z * ν)) * ν⁻¹ := by
    rw [show (ν⁻¹ * z * ν) * β = β * (ν⁻¹ * z * ν) from hc.symm]
  have h3 : ν * (β * (ν⁻¹ * z * ν)) * ν⁻¹ = (ν * β * ν⁻¹) * z := by group
  exact h1.trans (h2.trans h3)

private theorem exists_conj_Z_of_mem_root (hc : Ctx M Q Z B) {D : Subgroup G}
    (hD : IsRootB M B D) {β : G} (hβ : β ∈ D) (hβ1 : β ≠ 1) :
    ∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = β := by
  obtain ⟨m, -, hDB⟩ := hD
  obtain ⟨g, hg⟩ := hc.conj
  have hβmB : m⁻¹ * β * m ∈ B := by
    have h := hβ
    rw [hDB] at h
    exact mem_conjSubgroup.mp h
  have hzZ : g⁻¹ * (m⁻¹ * β * m) * g ∈ Z := by
    have h := hβmB
    rw [hg] at h
    exact mem_conjSubgroup.mp h
  have hz1 : g⁻¹ * (m⁻¹ * β * m) * g ≠ 1 := by
    intro h
    apply hβ1
    have h1 : m⁻¹ * β * m = 1 := by
      have := congrArg (fun x => g * x * g⁻¹) h
      simpa [mul_assoc] using this
    have := congrArg (fun x => m * x * m⁻¹) h1
    simpa [mul_assoc] using this
  refine ⟨m * g, g⁻¹ * (m⁻¹ * β * m) * g, hzZ, hz1, ?_⟩
  group

private theorem exists_good101_of_swap (hc : Ctx M Q Z B) {n : ℕ} (H : Sec10Hyp hc n)
    {C E D : Subgroup G} (hC : IsRootB M B C) (hE : IsRootB M B E) (hD : IsRootB M B D)
    {β : G} (hβ : β ∈ D) (hβQ : β ∈ Q)
    (hβC : β ∈ QB C) (hβE : β ∉ QB E)
    (hβcomm : ∀ e ∈ E, β * e = e * β) (hCZ : ¬ C ≤ E ⊔ Z)
    (hCQ : C ≤ Q) (hCQB : C ≤ QB E) :
    ∃ t : G, ∃ D' : Subgroup G, IsRootB M B D' ∧ D' ≤ Q ⊓ QB E ∧ ¬ D' ≤ E ⊔ Z ∧
      Good101 M Q Z D' t := by
  obtain ⟨ν, hν, hνQ, hνQB, hνZ, hνE⟩ := (hE.ctx hc).exists_swap_mem
  set t : G := ν * β * ν⁻¹ with htdef
  set D' : Subgroup G := conjSubgroup ν C with hD'def
  have htM : t ∈ M := by
    have hcZ : t ∈ Subgroup.centralizer (Z : Set G) := by
      rw [htdef]
      exact mem_centralizer_conj_of_forall_comm hνE hβcomm
    have hnorm := Subgroup.centralizer_le_normalizer (Z : Set G) hcZ
    rwa [hc.hyp.normalizer_Z.1] at hnorm
  have htQ : t ∉ Q := by
    intro ht
    have hmem : β ∈ QB E := by
      have h' : t ∈ conjSubgroup ν (QB E) := by rwa [hνQB]
      have h := mem_conjSubgroup.mp h'
      rwa [htdef, show ν⁻¹ * (ν * β * ν⁻¹) * ν = β by group] at h
    exact hβE hmem
  have htQB : t ∈ QB E := by
    rw [htdef, ← hνQ]
    exact mem_conjSubgroup.mpr (by rwa [show ν⁻¹ * (ν * β * ν⁻¹) * ν = β by group])
  have htQBD' : t ∈ QB D' := by
    rw [htdef, hD'def, QB_conj]
    exact mem_conjSubgroup.mpr (by rwa [show ν⁻¹ * (ν * β * ν⁻¹) * ν = β by group])
  have htconj : ∃ g : G, ∃ z ∈ Z, z ≠ 1 ∧ g * z * g⁻¹ = t := by
    have hβ1 : β ≠ 1 := fun h => hβE (h ▸ (QB E).one_mem)
    obtain ⟨g, z, hzZ, hz1, hgz⟩ := exists_conj_Z_of_mem_root hc hD hβ hβ1
    refine ⟨ν * g, z, hzZ, hz1, ?_⟩
    have h1 : (ν * g) * z * (ν * g)⁻¹ = ν * (g * z * g⁻¹) * ν⁻¹ := by group
    have h2 : ν * (g * z * g⁻¹) * ν⁻¹ = ν * β * ν⁻¹ := by rw [hgz]
    exact h1.trans (h2.trans htdef.symm)
  obtain ⟨hD'root, hD'le, hD'Z⟩ :=
    hc.root_conj_of_mem_sup hE hC (fun x hx => ⟨hCQ hx, hCQB hx⟩) hCZ hν
  have hne : D' ⊔ Z ≠ E ⊔ Z := fun h => hD'Z (h ▸ le_sup_left)
  have htE : t ∈ LB M Q E := Subgroup.mem_sup_right ⟨htQB, htM⟩
  have hRt : Rt M (LB M Q D') t ≠ LB M Q D' := IsRootB.Rt_ne H hD'root hE htE hne
  exact ⟨t, D', hD'root, hD'le, hD'Z, ⟨htconj, htM, htQ, htQBD', hRt⟩⟩

theorem Ctx.exists_good101_of_not_mem_QB (hc : Ctx M Q Z B) {n : ℕ} (H : Sec10Hyp hc n)
    {X : Subgroup G} (hX : IsClique101 M Q Z B X) {C E D : Subgroup G}
    (hC : IsRootB M B C) (hCX : C ≤ X) (hE : IsRootB M B E) (hEX : E ≤ X)
    (hD : IsRootB M B D) (hDC : D ≤ Q ⊓ QB C) {β : G} (hβ : β ∈ D) (hβE : β ∉ QB E) :
    ∃ t : G, Good101 M Q Z B t := by
  have hβQ : β ∈ Q := (Subgroup.mem_inf.mp (hDC hβ)).1
  have hβC : β ∈ QB C := (Subgroup.mem_inf.mp (hDC hβ)).2
  have hβcomm : ∀ e ∈ E, β * e = e * β := by
    intro e he
    exact commutatorElement_eq_one_iff_mul_comm.mp
      (n12l3_comm_inf_QB (hC.ctx hc) β (hDC hβ)
        e ⟨(hE.ctx hc).le he, hX.le_QB C hC hCX (hEX he)⟩)
  have hCZ : ¬ C ≤ E ⊔ Z := not_le_sup_Z_of_mem_QB hc hC hE hβQ hβC hβE
  have hCQ : C ≤ Q := (hC.ctx hc).le
  have hCQB : C ≤ QB E := hCX.trans (hX.le_QB E hE hEX)
  obtain ⟨t, D', hD'root, -, -, hgood⟩ :=
    exists_good101_of_swap hc H hC hE hD hβ hβQ hβC hβE hβcomm hCZ hCQ hCQB
  exact hD'root.exists_good101 hc hgood

theorem IsMaxClique101.isSaturated (hc : Ctx M Q Z B) {n : ℕ} (H : Sec10Hyp hc n)
    (hno : ∀ t : G, ¬ Good101 M Q Z B t) {X : Subgroup G} (hX : IsMaxClique101 M Q Z B X) :
    IsSaturated101 M Q Z B X := by
  intro C hC hCX D hD hDC
  by_contra hDX
  by_cases hDQ : ∀ E, IsRootB M B E → E ≤ X → D ≤ QB E
  · have hsup := IsClique101.sup_root hc hX.1 hD hDQ hDX
    exact absurd hsup.2 (not_lt_of_ge (hX.2 (X ⊔ D) hsup.1))
  · push Not at hDQ
    obtain ⟨E, hE, hEX, hnot⟩ := hDQ
    obtain ⟨β, hβD, hβE⟩ := Set.not_subset.mp hnot
    obtain ⟨t, ht⟩ := hc.exists_good101_of_not_mem_QB H hX.1 hC hCX hE hEX hD hDC hβD hβE
    exact hno t ht

end CFSG.RankThree.GF2n.Stroth80
