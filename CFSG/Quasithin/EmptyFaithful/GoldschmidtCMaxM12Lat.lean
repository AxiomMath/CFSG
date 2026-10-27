module

public import CFSG.Quasithin.Background.HSporLatMathieu
import all CFSG.Quasithin.Background.HSporLatMathieu
public import CFSG.Quasithin.EmptyFaithful.S151S9E
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A1cA132Action
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B216Quotient
public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.C1GNSolvConnect
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.E3Gen
public import CFSG.Quasithin.Background.FLcAutMat
public import CFSG.Quasithin.EmptyFaithful.FLcMLEGrp
public import CFSG.Quasithin.EmptyFaithful.S14117
public import CFSG.Quasithin.EmptyFaithful.S14117Coprime
public import CFSG.Quasithin.EmptyFaithful.S14117Rank
public import CFSG.Quasithin.EmptyFaithful.S1417Glue
public import CFSG.Quasithin.EmptyFaithful.S1421Defs
public import CFSG.Quasithin.EmptyFaithful.S151S6B
public import CFSG.Quasithin.EmptyFaithful.S151cA2
public import CFSG.Quasithin.EmptyFaithful.S151cCases
public import CFSG.Quasithin.EmptyFaithful.S152UGen
public import CFSG.Quasithin.EmptyFaithful.T1515Top9
public import CFSG.Quasithin.H13.J4Core
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311

public section

namespace CFSG.Quasithin.GoldCMax

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1.SporLat CFSG.Quasithin.H.MathieuLat

theorem overgroup_bound_of_lattice {Γ : Type} [Group Γ] [Finite Γ] {S : Subgroup Γ}
    (hS2 : IsPGroup 2 ↥S) (hSi : ¬ 2 ∣ S.index) {J : ℕ} {Y : ℕ → Subgroup Γ} {B : ℕ}
    (hall : ∀ Z : Subgroup Γ, S ≤ Z → ∃ j ≤ J, Z = memberOrTop J Y j)
    (hY : ∀ j < J, Nat.card (Y j) ≤ B) {T Z : Subgroup Γ} (hT2 : IsPGroup 2 ↥T)
    (hTi : ¬ 2 ∣ T.index) (hTZ : T ≤ Z) : Z = ⊤ ∨ Nat.card Z ≤ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq Γ (hT2.toSylow hTi) (hS2.toSylow hSi)
  have hST : S = T.map (MulAut.conj g).toMonoidHom :=
    (congrArg (fun T : Sylow 2 Γ => (T : Subgroup Γ)) hg).symm
  have hSZ : S ≤ Z.map (MulAut.conj g).toMonoidHom := by
    rw [hST]
    exact Subgroup.map_mono hTZ
  obtain ⟨j, -, hZ⟩ := hall _ hSZ
  have hcard : Nat.card (Z.map (MulAut.conj g).toMonoidHom) = Nat.card Z :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  by_cases hjJ : j < J
  · right
    have hm : memberOrTop J Y j = Y j := by simp [memberOrTop, hjJ]
    rw [← hcard, hZ, hm]
    exact hY j hjJ
  · left
    have hm : memberOrTop J Y j = ⊤ := by simp [memberOrTop, hjJ]
    rw [hm] at hZ
    have h := congrArg (Subgroup.comap (MulAut.conj g).toMonoidHom) hZ
    rwa [Subgroup.comap_map_eq_self_of_injective (MulAut.conj g).injective,
      Subgroup.comap_top] at h

theorem m12_overgroup_bound
    {T Z : Subgroup ↥CFSG.Blueprint.NativeSporadic.M12}
    (hT2 : IsPGroup 2 ↥T) (hTi : ¬ 2 ∣ T.index) (hTZ : T ≤ Z) : Z = ⊤ ∨ Nat.card Z ≤ 192 := by
  have hO : m12Ctx.D.O.lbl.size = 1485 := m12_lat_cert.2.1
  have hSyl := latSylow m12Ctx (by rw [hO]; decide)
  refine overgroup_bound_of_lattice (S := m12Ctx.S) (J := m12Ctx.J) (Y := m12Ctx.Y) hSyl.isPGroup
    (by
      have := hSyl.not_dvd_relIndex
      rwa [Subgroup.relIndex_top_right] at this) m12Ctx.complete (fun j hj => ?_) hT2 hTi hTZ
  rw [m12Ctx.Y_card hj]
  rw [m12_J] at hj
  rw [om_size_eq m12_lat_cert.2.2 (by simpa using hj)]
  show #[1, 3, 3][j]! * 2 ^ 6 ≤ 192
  interval_cases j <;> decide

end CFSG.Quasithin.GoldCMax
