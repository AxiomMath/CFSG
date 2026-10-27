module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TLocDefs
public import CFSG.RankThree.PartTwo.Sec14.Item142L3ResProofListBar
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
import CFSG.RankThree.PartTwo.Sec14.Ronan148TLocPoint
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec15.Item1423ProofTools
import CFSG.RankThree.PartTwo.Sec14.Ronan148HPointK
import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofOne

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.LocalRank
open CFSG.RankThree.PartTwo.Sec4 (ModThree PiField slPi glPi Type123)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.Assembly.LowTwoRank (StatedScalars)
open Matrix (ProjGenLinGroup)

@[expose] def PGLModel (X : Type) [Group X] (P : Subgroup (MulAut X)) : Prop :=
  ∃ (π : Bool) (p f : ℕ) (K : Type) (_ : Field K) (_ : PiField π p f K) (_ : ModThree π (p ^ f))
    (e : X ≃* projImage (slPi π 3 (p ^ f) K)) (y s : GL (Fin 3) K),
    y ∈ glPi π 3 (p ^ f) K ∧ Type123 π (p ^ f) K y 3 ∧ s ∈ slPi π 3 (p ^ f) K ∧
      s ∉ StatedScalars (Fin 3) K ∧ s ^ 3 ∈ StatedScalars (Fin 3) K ∧
      y * s * y⁻¹ * s⁻¹ ∈ StatedScalars (Fin 3) K ∧
      ∀ σ ∈ P, ∃ i j : ℤ, ∀ z : X,
        ((e (σ z) : projImage (slPi π 3 (p ^ f) K)) : ProjGenLinGroup (Fin 3) K) =
          (ProjGenLinGroup.mk s ^ i * ProjGenLinGroup.mk y ^ j) *
            (e z : ProjGenLinGroup (Fin 3) K) *
              (ProjGenLinGroup.mk s ^ i * ProjGenLinGroup.mk y ^ j)⁻¹

@[expose] def L3PointFacts {Γ : Type} [Group Γ] [Finite Γ] (A L : Subgroup Γ) (b : Γ) : Prop :=
  Ronan148T.LocA A L ∧ IsPGroup 3 (L3PGL.fixA A L) ∧
    ((b ∉ L ∧ Nat.card (A ⊓ L : Subgroup Γ) = 9 ∧
        (Nonempty (Sec4.autIn L A ≃* QuaternionGroup 2) ∨
          Nonempty (Sec4.autIn L A ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)))) ∨
      (b ∉ L ∧ PGLModel (↥L ⧸ aschbacherSolvableCore 3 ↥L) (Sec4.autThetaQuot A L))) ∧
    (∀ K₀ : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), Group.IsPerfect ↥K₀ →
      IsQuasisimple (↥K₀ ⧸ aschbacherSolvableCore 3 ↥K₀) →
      Sec4.IsList46 (↥K₀ ⧸ aschbacherSolvableCore 3 ↥K₀)) ∧
    ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
      Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e → p = 2 ∨ e ≤ 2

variable {G : Type} [Group G] [Finite G]

theorem pglModel_of_std {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (hPGLA : Sec8.IsZ3PGLThreePi (lBarA c L A)) (hx : ∃ x ∈ A, Sec4.InducesTypeOn L x 3) :
    PGLModel (↥L ⧸ aschbacherSolvableCore 3 ↥L) (Sec4.autThetaQuot A L) := by
  obtain ⟨x, hxA, hxN, π, p, f, K, _, hK, hq, e, y, hyH, hy3, hact⟩ := hx
  obtain ⟨s, hs, hsZ, hs3, hysZ, hcorr, -⟩ :=
    L3PGL.plane_model h hPGLA hxA hxN hK hq e hyH hy3 hact
  refine ⟨π, p, f, K, inferInstance, hK, hq, e, y, s, hyH, hy3, hs, hsZ, hs3, hysZ,
    fun σ hσ => ?_⟩
  obtain ⟨a, haN, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hσ
  exact hcorr a haA haN

theorem isList46_of_le_thetaQuot (h46 : Sec4.Item4_6) (hG : TheoremFourHyp G) {b : G}
    (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) {L : Subgroup G} (hLb : L ≤ Subgroup.centralizer ({b} : Set G))
    (K₀ : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)) (hK₀p : Group.IsPerfect ↥K₀)
    (hK₀q : IsQuasisimple (↥K₀ ⧸ aschbacherSolvableCore 3 ↥K₀)) :
    Sec4.IsList46 (↥K₀ ⧸ aschbacherSolvableCore 3 ↥K₀) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θL := aschbacherSolvableCore 3 ↥L with hθL
  set π := QuotientGroup.mk' θL with hπ
  set K₁ : Subgroup ↥L := K₀.comap π with hK₁
  set π₁ : ↥K₁ →* ↥K₀ := (π.comp K₁.subtype).codRestrict K₀ (fun k => k.2) with hπ₁
  have hπ₁s : Function.Surjective π₁ := by
    rintro ⟨z, hz⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
    exact ⟨⟨l, hz⟩, rfl⟩
  set R₁ := CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥K₁ with hR₁
  have hR₁p : Group.IsPerfect ↥R₁ :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect
  haveI := hK₀p
  have hR₁map : R₁.map π₁ = ⊤ :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_surjects_to_perfect_image π₁ hπ₁s
  set ψ : ↥R₁ →* ↥K₀ := π₁.comp R₁.subtype with hψ
  have hψs : Function.Surjective ψ := by
    intro z
    have hz : z ∈ R₁.map π₁ := by rw [hR₁map]; exact Subgroup.mem_top z
    obtain ⟨r, hr, rfl⟩ := hz
    exact ⟨⟨r, hr⟩, rfl⟩
  set ι : ↥R₁ →* ↥L := K₁.subtype.comp R₁.subtype with hι
  have hιinj : Function.Injective ι :=
    K₁.subtype_injective.comp R₁.subtype_injective
  have hkerθ : ψ.ker.map ι ≤ θL := by
    rintro _ ⟨r, hr, rfl⟩
    have h1 : π (ι r) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hr)
      exact this
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hθs := (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1
  have hθ3 := (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
  have hkers : Group.IsSolvable ψ.ker := by
    have e := ψ.ker.equivMapOfInjective ι hιinj
    haveI : Group.IsSolvable (ψ.ker.map ι) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hkerθ)
    exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
  have hker3 : ¬ 3 ∣ Nat.card ψ.ker := by
    rw [← Subgroup.card_map_of_injective hιinj]
    exact fun h => hθ3 (h.trans (Subgroup.card_dvd_of_le hkerθ))
  obtain ⟨e₁⟩ := Sec14.ONLoc.nonempty_thetaQuot_equiv ψ hψs hkers hker3
  set J : Subgroup G := (R₁.map K₁.subtype).map L.subtype with hJ
  have hJinj : Function.Injective (L.subtype.comp K₁.subtype) :=
    L.subtype_injective.comp K₁.subtype_injective
  have hJeq : J = R₁.map (L.subtype.comp K₁.subtype) := by rw [hJ, Subgroup.map_map]
  let eJ : ↥R₁ ≃* ↥J :=
    (R₁.equivMapOfInjective _ hJinj).trans (MulEquiv.subgroupCongr hJeq.symm)
  have hθJ := CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eJ
  set e₂ : ↥R₁ ⧸ aschbacherSolvableCore 3 ↥R₁ ≃* ↥J ⧸ aschbacherSolvableCore 3 ↥J :=
    QuotientGroup.congr _ _ eJ hθJ
  have hJb : J ≤ Subgroup.centralizer ({b} : Set G) :=
    (Subgroup.map_subtype_le _).trans hLb
  have hJp : Group.IsPerfect ↥J := Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
  have hJq : IsQuasisimple (↥J ⧸ aschbacherSolvableCore 3 ↥J) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (e₁.trans e₂) hK₀q
  have h := Ronan148H.isList46_of_perfect_le_centralizer h46 hG hb3 hb1 hJb hJp hJq
  exact Sec21.Item223PrintProof.isList46_of_mulEquiv (e₁.trans e₂).symm h

theorem l3PointFacts_of_std
    (h131 : Item131) (h46 : Sec4.Item4_6)
    (h41 : Sec4.Item4_1LargePrime) {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (hL3 : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
    L3PointFacts A L c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hloc, hfix⟩ := Ronan148T.locA_fixA_of_std h131 h hL3
  refine ⟨hloc, hfix, ?_, fun K₀ hK₀p hK₀q => isList46_of_le_thetaQuot h46 h.toTheoremFourHyp
    (h.isE27'.1.2 c h.toSec13Data.mem_A) (h.toSec13Data.ne_one) h.toSec13Data.le_centralizer K₀ hK₀p
    hK₀q, Ronan148T.two_or_le_two_of_sec13 h41 h.toSec13Data⟩
  have hD := h.toSec13Data
  have hspor := Sec13.sporadicModels131
  have hLq : CFSG.IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    Sec15.Proof1423.isQuasisimple_of_mem_thetaComponentsIn1423
      (M := Subgroup.centralizer ({c} : Set G)) hD.mem_thetaComponentsAt
  have hLp : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) := hLq.1
  have : Nontrivial (↥L ⧸ aschbacherSolvableCore 3 ↥L) := LocalCores.isQuasisimple_nontrivial hLq
  have hZ := center_eq_bot_of_isLThreePi hL3 hLp
  have hcL' : c ∉ L := not_mem_of_center_eq_bot hD hZ
  rcases cases131 h131 hspor slTwoCenter hD with
      ⟨hcL, h9AL, -, hcase⟩ | ⟨-, -, hcase, -⟩ | ⟨-, hPGLA, -, hx⟩ | ⟨hcL, -⟩
  · rcases hcase with ⟨-, hQ⟩ | ⟨⟨φ⟩, -⟩ | ⟨⟨φ⟩, -⟩
    · exact Or.inl ⟨hcL, h9AL, hQ⟩
    · exact absurd hL3 (not_isLThreePi_of_mulEquiv φ not_isoLThreePi_alternating_seven)
    · exact absurd hL3 (not_isLThreePi_of_mulEquiv φ KFacts.KS14.not_isoLThreePi_M22)
  · obtain ⟨⟨hM22p, hM22z⟩, ⟨hM12p, hM12z⟩, ⟨hJ2p, hJ2z⟩⟩ := hspor
    rcases hcase with hφ | hφ
    · obtain ⟨φ⟩ := hφ
      obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hM12p hM12z φ
      exact absurd hL3 (not_isLThreePi_of_mulEquiv ψ KFacts.KS14.not_isoLThreePi_M12)
    · obtain ⟨φ⟩ := hφ
      obtain ⟨-, -, -, ⟨ψ⟩⟩ := facts_of_prod hD hJ2p hJ2z φ
      exact absurd hL3 (not_isLThreePi_of_mulEquiv ψ KFacts.KS14.ks17J2NotList.1)
  · exact Or.inr ⟨hcL', pglModel_of_std h hPGLA hx⟩
  · exact absurd hcL hcL'

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
