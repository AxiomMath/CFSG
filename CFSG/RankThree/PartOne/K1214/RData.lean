module

public import CFSG.RankThree.PartOne.K1214.Frame
public import CFSG.RankThree.PartOne.K1214.SylowSL2
public import CFSG.RankThree.PartOne.K1214.SylowSU3
public import CFSG.RankThree.PartOne.K1214.SylowSp4
public import CFSG.RankThree.PartOne.K1214.Arith
public import CFSG.RankThree.PartOne.S12K.RigidDef

public section

namespace CFSG.RankThree.PartOne.K1214

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.GroupTheory CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedLieTag)
open CFSG.RankThree.PartOne.S12K (LieRigidity3)

variable {G : Type} [Group G]

theorem statedClassicalModel_of_lieModel_of_tag' {X : Type} [Group X] {t : StatedLieTag}
    {n p f : ℕ} (ht : t = .PSU ∨ t = .PSp ∨ t = .PSL) (h : LieModel X t n p f) :
    StatedClassicalModel X t n p f :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by rcases ht with rfl | rfl | rfl <;> decide)

variable [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {b : G}
  {K I X P Q : Subgroup G}

theorem rData (hRig : LieRigidity3) (ctx : Fus12Ctx G p A c L E)
    (hL : Layer1212 p A c L E b K I) (hF : Field1213 p A c L b K I)
    (hKR : K = inSubgroup perfectResidual (I ⊓ Subgroup.centralizer ({c} : Set G))) :
    ∃ r e : ℕ, (r = 1 ∨ r = 2) ∧ 2 ≤ e ∧ Nat.card E = p ^ (r + 2) ∧
      SylowShape p r e (↥I ⧸ Subgroup.center ↥I) ∧
      SylowShape p r (e - 1) (↥K ⧸ Subgroup.center ↥K) := by
  obtain ⟨hp, hp5⟩ := prime_five_le ctx
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  obtain ⟨r0, hr1, hr12, hrow, -, hEA, hE4⟩ := ctx.facts.three.2
  obtain ⟨-, -, -, t, n, f, -, hmodI, hmodR⟩ := hF.field
  have hmodK := hL.K_model
  subst hKR
  by_cases h8 : r0 ≤ 8
  ·
    obtain ⟨g, hg1, hdvd, hK⟩ := hmodK.2.2 ⟨r0, hr1, h8, hrow⟩
    rw [one_mul] at hK
    obtain ⟨rfl, rfl, rfl⟩ := (hRig _ t n f hmodR).2.2 g hK
    have hI : StatedClassicalModel (↥I ⧸ Subgroup.center ↥I) .PSL 2 2 (p * f) :=
      statedClassicalModel_of_lieModel_of_tag' (Or.inr (Or.inr rfl)) hmodI
    obtain ⟨e, m, m', he2, hm'1, hm'2, hm1, hm2⟩ := lte_minus hp hp2 hg1 hdvd
    have hEcard : Nat.card E = p ^ 3 := by
      rw [hEA h8]
      exact ctx.hyp.A_card
    exact ⟨1, e, Or.inl rfl, he2, by simpa using hEcard,
      sylowShape_of_psl2Model hp hp2 (by omega) hm1 hm2 hI,
      sylowShape_of_psl2Model hp hp2 (by omega) hm'1 hm'2 hK⟩
  · have h9 : 9 ≤ r0 := by omega
    have hE4' : Nat.card E = p ^ (2 + 2) := by simpa using hE4 h9
    have hU : ∀ f0 : ℕ, 1 ≤ f0 → p ∣ 2 ^ f0 + 1 →
        (StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 4 2 f0 ∨
          StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSU 5 2 f0) →
        ∃ r e : ℕ, (r = 1 ∨ r = 2) ∧ 2 ≤ e ∧ Nat.card E = p ^ (r + 2) ∧
          SylowShape p r e (↥I ⧸ Subgroup.center ↥I) ∧
          SylowShape p r (e - 1)
            (↥(inSubgroup perfectResidual (I ⊓ Subgroup.centralizer ({c} : Set G))) ⧸
              Subgroup.center ↥(inSubgroup perfectResidual
                (I ⊓ Subgroup.centralizer ({c} : Set G)))) := by
      intro f0 hf0 hdvd hm
      have hK := hmodK.1 f0 hf0 hdvd hm
      rw [one_mul] at hK
      obtain ⟨rfl, rfl, rfl⟩ := (hRig _ t n f hmodR).1 f0 hK
      have hI : StatedClassicalModel (↥I ⧸ Subgroup.center ↥I) .PSU 3 2 (p * f) :=
        statedClassicalModel_of_lieModel_of_tag' (Or.inl rfl) hmodI
      obtain ⟨e, m, m', he2, hm'1, hm'2, hm1, hm2⟩ := lte_plus hp hp2 hdvd
      exact ⟨2, e, Or.inr rfl, he2, hE4',
        sylowShape_of_psu3Model hp hp2 hp3 (by omega) hm1 hm2 hI,
        sylowShape_of_psu3Model hp hp2 hp3 (by omega) hm'1 hm'2 hK⟩
    interval_cases r0
    · obtain ⟨f0, hf0, hdvd, hm⟩ := hrow
      exact hU f0 hf0 hdvd (Or.inl hm)
    · obtain ⟨f0, hf0, hdvd, hm⟩ := hrow
      have hK := hmodK.2.1 f0 hf0 hdvd hm
      rw [one_mul] at hK
      obtain ⟨rfl, rfl, rfl⟩ := (hRig _ t n f hmodR).2.1 f0 hK
      have hI : StatedClassicalModel (↥I ⧸ Subgroup.center ↥I) .PSp 2 2 (p * f) :=
        statedClassicalModel_of_lieModel_of_tag' (Or.inr (Or.inl rfl)) hmodI
      obtain ⟨e, m, m', he2, hm'1, hm'2, hm1, hm2⟩ := lte_plus hp hp2 hdvd
      exact ⟨2, e, Or.inr rfl, he2, hE4',
        sylowShape_of_psp4Model hp hp2 (by omega) hm1 hm2 hI,
        sylowShape_of_psp4Model hp hp2 (by omega) hm'1 hm'2 hK⟩
    · obtain ⟨rfl, -, f0, hf0, hdvd, hm⟩ := hrow
      exact hU f0 hf0 hdvd (Or.inr hm)
    · obtain ⟨rfl, -, f0, hf0, hdvd, -, hm⟩ := hrow
      exact hU f0 hf0 hdvd (Or.inr hm)

end CFSG.RankThree.PartOne.K1214
