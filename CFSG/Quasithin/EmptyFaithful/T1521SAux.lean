module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setting
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem conjJoin_le_of_le {S K P : Subgroup G} (hK : K ≤ P) (hS : S ≤ P) : conjJoin S K ≤ P := by
  refine iSup_le fun s => ?_
  rintro _ ⟨x, hx, rfl⟩
  simpa using P.mul_mem (P.mul_mem (hS s.2) (hK hx)) (P.inv_mem (hS s.2))

theorem le_conjJoin {S K : Subgroup G} : K ≤ conjJoin S K := by
  intro x hx
  refine Subgroup.mem_iSup_of_mem (⟨1, S.one_mem⟩ : S) ?_
  exact ⟨x, hx, by simp⟩

theorem mem_normalizer_conjJoin_of_orbits {X S L : Subgroup G} (hSX : S ≤ X)
    (horb : conjSubgroupsBy X L = conjSubgroupsBy S L) {y : G} (hy : y ∈ X) :
    y ∈ Subgroup.normalizer (conjJoin S L : Set G) := by
  have key : ∀ y ∈ X, ∀ z ∈ conjJoin S L, y * z * y⁻¹ ∈ conjJoin S L := by
    intro y hy z hz
    refine Subgroup.iSup_induction (fun s : S => L.map (MulAut.conj (s : G)).toMonoidHom)
      (C := fun z => y * z * y⁻¹ ∈ conjJoin S L) hz ?_ ?_ ?_
    · rintro s _ ⟨l, hl, rfl⟩
      have hys : y * (s : G) ∈ X := X.mul_mem hy (hSX s.2)
      have hmem : L.map (MulAut.conj (y * (s : G))).toMonoidHom ∈ conjSubgroupsBy X L :=
        ⟨y * (s : G), hys, rfl⟩
      rw [horb] at hmem
      obtain ⟨t, ht, hteq⟩ := hmem
      have hl' : y * ((s : G) * l * (s : G)⁻¹) * y⁻¹ ∈
          L.map (MulAut.conj (y * (s : G))).toMonoidHom :=
        ⟨l, hl, by simp [mul_assoc]⟩
      rw [hteq] at hl'
      exact Subgroup.mem_iSup_of_mem (⟨t, ht⟩ : S) hl'
    · simp
    · intro a b ha hb
      have : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [this]
      exact Subgroup.mul_mem _ ha hb
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => key y hy h hh, fun hh => ?_⟩
  have := key y⁻¹ (X.inv_mem hy) _ hh
  simpa [mul_assoc] using this

theorem oTwoUpper_oTwoUpper1521 (X : Subgroup G) : oTwoUpper (oTwoUpper X) = oTwoUpper X := by
  refine le_antisymm (oTwoUpper_le _) ?_
  refine (Subgroup.closure_le _).mpr fun x hx => ?_
  exact mem_oTwoUpper_of_odd (Subgroup.subset_closure hx) hx.2

variable [Finite G]

theorem borelOver_le_of_parabolic {L P Q S' : Subgroup G} (hQ : IsSylowTwoOf Q L)
    (hS' : IsSylowTwoOf S' L) (hPL : P ≤ L)
    (hle : L ⊓ Subgroup.normalizer (S' : Set G) ≤ P) (hQP : Q ≤ P) :
    L ⊓ Subgroup.normalizer (Q : Set G) ≤ P := by
  have hS'P : S' ≤ P := (le_inf hS'.1 Subgroup.le_normalizer).trans hle
  have hQ' : IsSylowTwoOf Q P := A4.isSylowTwoOf_mono hQ hQP hPL
  have hS'' : IsSylowTwoOf S' P := A4.isSylowTwoOf_mono hS' hS'P hPL
  obtain ⟨p, hp, hconj⟩ := A4.exists_conj_of_isSylowTwoOf hQ' hS''
  intro g hg
  have hpL : p ∈ L := hPL hp
  have hg' : p * g * p⁻¹ ∈ L ⊓ Subgroup.normalizer (S' : Set G) := by
    refine ⟨L.mul_mem (L.mul_mem hpL hg.1) (L.inv_mem hpL), ?_⟩
    show _ ∈ Subgroup.normalizer (S' : Set G)
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hconj x, hconj (p * g * p⁻¹ * x * (p * g * p⁻¹)⁻¹)]
    have e : p⁻¹ * (p * g * p⁻¹ * x * (p * g * p⁻¹)⁻¹) * p = g * (p⁻¹ * x * p) * g⁻¹ := by group
    rw [e]
    exact Subgroup.mem_normalizer_iff.mp hg.2 (p⁻¹ * x * p)
  have h1 := P.mul_mem (P.mul_mem (P.inv_mem hp) (hle hg')) hp
  simpa [mul_assoc] using h1

end CFSG.Quasithin
