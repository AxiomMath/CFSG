module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.OddSz
public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProofCross
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.OddLinear
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.OddG2Lin
import CFSG.LinearAlgebra.LinearGroups.QuadraticActions
import CFSG.RankThree.PartTwo.Sec6.Item611Res3ProofG2
import CFSG.Quasithin.EmptyFaithful.Gold14610LiftCenter
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LThreeFourAutFive
import CFSG.LieType.Chevalley.ExceptionalG2F4ModelSchreier
import CFSG.RankThree.PartOne.SEITZ11.G2SevenRep
import CFSG.RankThree.PartTwo.Sec21.Item223RankResProofSeven
import CFSG.Foundations
import CFSG.GroupTheory.BaerSuzuki
import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeFamilies
import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81AutSectionDefs
import CFSG.Quasithin.Recognition.GoldschmidtTriple
import CFSG.RankThree.Asc83Table.Automizer
import CFSG.RankThree.PartTwo.NotationBlocks
import CFSG.RankThree.PartTwo.Sec21.Item21Statements
import CFSG.RankThree.PartTwo.Sec6.Item611ResProof
import CFSG.RankThree.PartTwo.Sec7.ThreeTranspositions

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open CFSG.RankThree.PartTwo.Sec21.Item223RankResProof CFSG.RankThree.PartOne.SEITZ11 Matrix
open Subgroup
open CFSG.RankThree.PartOne.SEITZ11.G2Seven
open CFSG.RankThree.PartTwo.Sec6.Res611G2Cent
open CFSG.Quasithin.Gold14610

section LinearSplit

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]


private theorem commute_on_invariant_submodule
    (hF : ringChar F ≠ 2)
    {e : (Module.End F V)ˣ} (he : e * e = 1)
    {R : Subgroup (Module.End F V)ˣ} (hR : IsPGroup 2 R)
    (hRe : ∀ r ∈ R, r * e = e * r)
    {y : (Module.End F V)ˣ} (hye : y * e = e * y)
    (hyR : y ∈ normalizer (R : Set (Module.End F V)ˣ))
    {r : ℕ} (hr : r.Prime) (hr7 : r = 7 ∨ 17 ≤ r) (hyr : y ^ r = 1)
    (W : Submodule F V) (hWdim : Module.finrank F W ≤ 4)
    (hWinv : ∀ g ∈ Subgroup.centralizer ({e} : Set (Module.End F V)ˣ), ∀ w ∈ W,
      (g : V →ₗ[F] V) w ∈ W) :
    ∀ x ∈ R, ∀ w ∈ W, (y : V →ₗ[F] V) ((x : V →ₗ[F] V) w) =
      (x : V →ₗ[F] V) ((y : V →ₗ[F] V) w) := by
  intro x hx w hw
  let S : Subgroup (Module.End F V)ˣ := Subgroup.centralizer ({e} : Set (Module.End F V)ˣ)
  have hRS : R ≤ S := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact (hRe z hz).symm
  have hyS : y ∈ S := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact hye.symm
  let R' : Subgroup S := R.comap S.subtype
  let ψR : R' →* ↥R :=
    { toFun := fun t => (⟨t.1.1, t.2⟩ : ↥R)
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  have hψR : Function.Injective ψR := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun t : ↥R => (t.1 : (Module.End F V)ˣ)) hab
  have hR'2 : IsPGroup 2 R' := hR.of_injective ψR hψR
  have hnorm : (⟨y, hyS⟩ : S) ∈ normalizer (R' : Set S) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [Subgroup.mem_comap, Subgroup.mem_comap]
    simpa [Subgroup.coe_mul, Subgroup.coe_inv] using (Subgroup.mem_normalizer_iff.mp hyR z.1)
  let φ : S →* LinearMap.GeneralLinearGroup F W :=
    CFSG.LinearGroups.invariantRestrict S W hWinv
  have hRφ2 : IsPGroup 2 (R'.map φ) := hR'2.map φ
  have hnormφ : φ ⟨y, hyS⟩ ∈ normalizer ((R'.map φ : Subgroup (LinearMap.GeneralLinearGroup F W)) :
      Set (LinearMap.GeneralLinearGroup F W)) :=
    Subgroup.le_normalizer_map φ (Subgroup.mem_map.mpr ⟨⟨y, hyS⟩, hnorm, rfl⟩)
  have hpowφ : (φ ⟨y, hyS⟩) ^ r = 1 := by
    have hyr' : (⟨y, hyS⟩ : S) ^ r = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow]
      exact hyr
    rw [← map_pow, hyr', map_one]
  have hcomm := commute_of_normalizes_two_of_finrank_le_four (W := ↥W) hF hWdim hRφ2 hr hr7 hpowφ
    hnormφ
  have hxR' : (⟨x, hRS hx⟩ : S) ∈ R' := by
    rw [Subgroup.mem_comap]
    exact hx
  have hxφ : φ ⟨x, hRS hx⟩ ∈ R'.map φ := Subgroup.mem_map.mpr ⟨⟨x, hRS hx⟩, hxR', rfl⟩
  have hc := hcomm _ hxφ
  have hcw := congrArg (fun (g : LinearMap.GeneralLinearGroup F W) =>
    (((g : Module.End F W) ⟨w, hw⟩) : V)) hc
  simpa only [φ, Units.val_mul, Module.End.mul_apply,
    CFSG.LinearGroups.coe_invariantRestrict_apply] using hcw

private theorem commute_of_eigenspaces_finrank_le_four
    (hF : ringChar F ≠ 2)
    {e : (Module.End F V)ˣ} (he : e * e = 1)
    {R : Subgroup (Module.End F V)ˣ} (hR : IsPGroup 2 R)
    (hRe : ∀ r ∈ R, r * e = e * r)
    {y : (Module.End F V)ˣ} (hye : y * e = e * y)
    (hyR : y ∈ normalizer (R : Set (Module.End F V)ˣ))
    {r : ℕ} (hr : r.Prime) (hr7 : r = 7 ∨ 17 ≤ r) (hyr : y ^ r = 1)
    (hP : Module.finrank F (LinearMap.ker ((e : Module.End F V) - 1)) ≤ 4)
    (hM : Module.finrank F (LinearMap.ker ((e : Module.End F V) + 1)) ≤ 4) :
    ∀ x ∈ R, y * x = x * y := by
  have hF2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  have hee : ∀ v : V, (e : V →ₗ[F] V) ((e : V →ₗ[F] V) v) = v := by
    intro v
    have h1 : (e : Module.End F V) * (e : Module.End F V) = 1 := congrArg Units.val he
    have h2 : (((e : Module.End F V) * (e : Module.End F V) : Module.End F V) : V → V) =
        ((1 : Module.End F V) : V → V) := congrArg (fun u : Module.End F V => (u : V → V)) h1
    simpa [Module.End.mul_apply, Module.End.one_apply] using congrFun h2 v
  let P : Submodule F V := LinearMap.ker ((e : Module.End F V) - 1)
  let M : Submodule F V := LinearMap.ker ((e : Module.End F V) + 1)
  have hPinv : ∀ g ∈ Subgroup.centralizer ({e} : Set (Module.End F V)ˣ), ∀ w ∈ P,
      (g : V →ₗ[F] V) w ∈ P := by
    intro g hg w hw
    have hge : (e : V →ₗ[F] V) ((g : V →ₗ[F] V) w) = (g : V →ₗ[F] V) ((e : V →ₗ[F] V) w) := by
      have h := Subgroup.mem_centralizer_iff.mp hg e (Set.mem_singleton e)
      have h' : (((e : Module.End F V) * (g : Module.End F V) : Module.End F V) : V → V) =
          (((g : Module.End F V) * (e : Module.End F V) : Module.End F V) : V → V) :=
        congrArg (fun u : Module.End F V => (u : V → V)) (congrArg Units.val h)
      simpa [Module.End.mul_apply] using congrFun h' w
    have hw' : (e : V →ₗ[F] V) w = w := by
      have h := LinearMap.mem_ker.mp hw
      rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at h
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, hge, hw', sub_self]
  have hMinv : ∀ g ∈ Subgroup.centralizer ({e} : Set (Module.End F V)ˣ), ∀ w ∈ M,
      (g : V →ₗ[F] V) w ∈ M := by
    intro g hg w hw
    have hge : (e : V →ₗ[F] V) ((g : V →ₗ[F] V) w) = (g : V →ₗ[F] V) ((e : V →ₗ[F] V) w) := by
      have h := Subgroup.mem_centralizer_iff.mp hg e (Set.mem_singleton e)
      have h' : (((e : Module.End F V) * (g : Module.End F V) : Module.End F V) : V → V) =
          (((g : Module.End F V) * (e : Module.End F V) : Module.End F V) : V → V) :=
        congrArg (fun u : Module.End F V => (u : V → V)) (congrArg Units.val h)
      simpa [Module.End.mul_apply] using congrFun h' w
    have hw' : (e : V →ₗ[F] V) w = -w := by
      have h := LinearMap.mem_ker.mp hw
      rw [LinearMap.add_apply, Module.End.one_apply, add_eq_zero_iff_eq_neg] at h
      exact h
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, hge, hw', map_neg,
      neg_add_cancel]
  have hPcomm := commute_on_invariant_submodule hF he hR hRe hye hyR hr hr7 hyr P hP hPinv
  have hMcomm := commute_on_invariant_submodule hF he hR hRe hye hyR hr hr7 hyr M hM hMinv
  intro x hx
  apply Units.ext
  apply LinearMap.ext
  intro v
  set p : V := (2 : F)⁻¹ • (v + (e : V →ₗ[F] V) v) with hpdef
  set m : V := (2 : F)⁻¹ • (v - (e : V →ₗ[F] V) v) with hmdef
  have hp : p ∈ P := by
    rw [hpdef, LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, map_smul, map_add,
      hee, add_comm, sub_self]
  have hm : m ∈ M := by
    rw [hmdef, LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, map_smul, map_sub,
      hee, ← smul_add,
      show ((e : V →ₗ[F] V) v - v) + (v - (e : V →ₗ[F] V) v) = 0 from by abel, smul_zero]
  have hv : v = p + m := by
    rw [hpdef, hmdef, ← smul_add, add_add_sub_cancel, ← two_smul F v, smul_smul,
      inv_mul_cancel₀ hF2, one_smul]
  have h1 := hPcomm x hx p hp
  have h2 := hMcomm x hx m hm
  calc ((y * x : (Module.End F V)ˣ) : Module.End F V) v
      = (y : V →ₗ[F] V) ((x : V →ₗ[F] V) v) := by
        rw [Units.val_mul, Module.End.mul_apply]
    _ = (y : V →ₗ[F] V) ((x : V →ₗ[F] V) (p + m)) := by rw [hv]
    _ = (y : V →ₗ[F] V) ((x : V →ₗ[F] V) p + (x : V →ₗ[F] V) m) := by rw [map_add]
    _ = (y : V →ₗ[F] V) ((x : V →ₗ[F] V) p) + (y : V →ₗ[F] V) ((x : V →ₗ[F] V) m) := by
        rw [map_add]
    _ = (x : V →ₗ[F] V) ((y : V →ₗ[F] V) p) + (x : V →ₗ[F] V) ((y : V →ₗ[F] V) m) := by
        rw [h1, h2]
    _ = (x : V →ₗ[F] V) ((y : V →ₗ[F] V) p + (y : V →ₗ[F] V) m) := by rw [map_add]
    _ = (x : V →ₗ[F] V) ((y : V →ₗ[F] V) (p + m)) := by conv_rhs => rw [map_add]
    _ = (x : V →ₗ[F] V) ((y : V →ₗ[F] V) v) := by rw [hv]
    _ = ((x * y : (Module.End F V)ˣ) : Module.End F V) v := by
        rw [Units.val_mul, Module.End.mul_apply]

end LinearSplit

private theorem finrank_eigP_of_involution {K : Type} [Field K]
    {M : Matrix (Fin 7) (Fin 7) K} (h2 : (2 : K) ≠ 0) (hM : M * M = 1)
    (hMB : M.transpose * G2Seven.gram K * M = G2Seven.gram K)
    (hMX : ∀ u v, M *ᵥ cross7 u v = cross7 (M *ᵥ u) (M *ᵥ v)) (hM1 : M ≠ 1) :
    Module.finrank K (eigP M) = 3 := by
  have hsum : Module.finrank K (eigP M) + Module.finrank K (eigM M) = 7 := by
    have h := finrank_split h2 hM ⊤ (fun _ _ => Submodule.mem_top)
    rw [finrank_top, Module.finrank_fin_fun, top_inf_eq, top_inf_eq] at h
    omega
  have := finrank_eigM_eq_four h2 hM hMB hMX hM1
  omega

private theorem commute_of_pow_commute_seven {G : Type} [Group G] {y z : G} (h7 : y ^ 7 = 1)
    {k : ℕ} (hk : k = 2 ∨ k = 3) (h : y ^ k * z = z * y ^ k) : y * z = z * y := by
  rcases hk with rfl | rfl
  · have hy : (y ^ 2) ^ 4 = y := by
      rw [← pow_mul, show 2 * 4 = 7 + 1 by norm_num, pow_add, h7, one_mul, pow_one]
    have hc : Commute (y ^ 2) z := h
    have := (hc.pow_left 4).eq
    rwa [hy] at this
  · have hy : (y ^ 3) ^ 5 = y := by
      rw [← pow_mul, show 3 * 5 = 7 * 2 + 1 by norm_num, pow_add, pow_mul, h7, one_pow,
        one_mul, pow_one]
    have hc : Commute (y ^ 3) z := h
    have := (hc.pow_left 5).eq
    rwa [hy] at this

theorem noSzOverTwo_of_g2Seven {X F : Type} [Group X] [Field F]
    [Finite F] (hF : ringChar F ≠ 2) (ρ : X →* GL (Fin 7) F) (hρ : Function.Injective ρ)
    (hform : ∀ g : X, ((ρ g : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F).transpose *
      G2Seven.gram F * ((ρ g : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) = G2Seven.gram F)
    (hcross : ∀ (g : X) (u v : Fin 7 → F),
      ((ρ g : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) *ᵥ cross7 u v =
        cross7 (((ρ g : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) *ᵥ u)
          (((ρ g : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) *ᵥ v)) :
    NoSzOverTwo X := by
  intro H N hNnormal hN p f hSz
  obtain ⟨P, y, hP2, ⟨u, huP, v, hvP, huv⟩, hyNorm, hyPrime, hy7, x₀, hx₀P, hx₀⟩ :=
    exists_twoSubgroup_of_suzukiModel_quotient N hN hSz
  have hXfin : Finite X := Finite.of_injective ρ hρ
  have hHfin : Finite H := inferInstance
  have hPfin : Finite ↥P := inferInstance
  have hEndfin : Finite (Module.End F (Fin 7 → F)) :=
    Finite.of_injective (fun g : Module.End F (Fin 7 → F) => (g : (Fin 7 → F) → (Fin 7 → F)))
      (fun a b h => LinearMap.ext (congrFun h))
  have hUnitfin : Finite (Module.End F (Fin 7 → F))ˣ :=
    Finite.of_injective (fun g : (Module.End F (Fin 7 → F))ˣ => (g : Module.End F (Fin 7 → F)))
      (fun a b h => Units.ext h)
  have hFact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ρH : H →* GL (Fin 7) F := ρ.comp H.subtype
  have hρH : Function.Injective ρH := hρ.comp (Subgroup.subtype_injective H)
  let ψ : H →* (Module.End F (Fin 7 → F))ˣ :=
    (Matrix.GeneralLinearGroup.toLin (n := Fin 7) (R := F)).toMonoidHom.comp ρH
  have hψ : Function.Injective ψ :=
    (Matrix.GeneralLinearGroup.toLin (n := Fin 7) (R := F)).injective.comp hρH
  let m : H →* Matrix (Fin 7) (Fin 7) F :=
    (Units.coeHom (Matrix (Fin 7) (Fin 7) F)).comp ρH
  have hm : Function.Injective m := by
    intro a b hab
    apply hρH
    exact Units.ext hab
  let E : Subgroup H := centerInvolutions P
  have hEmem : ∀ x : H, x ∈ E ↔
      ∃ b : ↥P, b ∈ Subgroup.center ↥P ∧ b ^ 2 = 1 ∧ (b : H) = x := fun _ => Iff.rfl
  have hPnt : Nontrivial ↥P := by
    refine ⟨⟨⟨u, huP⟩, ⟨1, P.one_mem⟩, ?_⟩⟩
    intro h
    exact huv (by rw [show u = 1 from congrArg Subtype.val h, one_mul, mul_one])
  have hEsq : ∀ a ∈ E, a * a = 1 := by
    intro a ha
    obtain ⟨b, -, hb2, rfl⟩ := (hEmem a).mp ha
    have h := congrArg (fun t : ↥P => (t : H)) hb2
    simpa [pow_two] using h
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    intro a ha b hb
    obtain ⟨ba, hbac, -, rfl⟩ := (hEmem a).mp ha
    obtain ⟨bb, hbbc, -, rfl⟩ := (hEmem b).mp hb
    have h := Subgroup.mem_center_iff.mp hbac bb
    have h' := congrArg (fun t : ↥P => (t : H)) h
    simpa using h'.symm
  have hEcenter : ∀ a ∈ E, ∀ p ∈ P, a * p = p * a := by
    intro a ha p hp
    obtain ⟨ba, hbac, -, rfl⟩ := (hEmem a).mp ha
    have h := Subgroup.mem_center_iff.mp hbac ⟨p, hp⟩
    have h' := congrArg (fun t : ↥P => (t : H)) h
    simpa using h'.symm
  have hEconj : ∀ g ∈ E, ∀ y' ∈ normalizer (P : Set H), y' * g * y'⁻¹ ∈ E := by
    intro g hg y' hy'
    obtain ⟨b, hbc, hb2, hbval⟩ := (hEmem g).mp hg
    have hmem : y' * (b : H) * y'⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp hy' (b : H)).mp b.2
    refine (hEmem _).mpr ⟨⟨y' * (b : H) * y'⁻¹, hmem⟩, ?_, ?_, ?_⟩
    · rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      have hyinv : y'⁻¹ ∈ normalizer (P : Set H) := Subgroup.inv_mem _ hy'
      have hd : y'⁻¹ * (c : H) * y' ∈ P := by
        simpa using (Subgroup.mem_normalizer_iff.mp hyinv (c : H)).mp c.2
      have hcent := Subgroup.mem_center_iff.mp hbc ⟨y'⁻¹ * (c : H) * y', hd⟩
      have hcent' : (y'⁻¹ * (c : H) * y') * (b : H) =
          (b : H) * (y'⁻¹ * (c : H) * y') :=
        congrArg (fun t : ↥P => (t : H)) hcent
      calc (c : H) * (y' * (b : H) * y'⁻¹)
          = y' * ((y'⁻¹ * (c : H) * y') * b) * y'⁻¹ := by group
        _ = y' * (b * (y'⁻¹ * (c : H) * y')) * y'⁻¹ := by rw [hcent']
        _ = (y' * (b : H) * y'⁻¹) * (c : H) := by group
    · apply Subtype.ext
      show (y' * (b : H) * y'⁻¹) ^ 2 = 1
      have hb2' : (b : H) * (b : H) = 1 := by
        have h := congrArg (fun t : ↥P => (t : H)) hb2
        simpa [pow_two] using h
      calc (y' * (b : H) * y'⁻¹) ^ 2 = y' * ((b : H) * (b : H)) * y'⁻¹ := by
            rw [pow_two]; group
        _ = 1 := by rw [hb2']; group
    · show y' * (b : H) * y'⁻¹ = y' * g * y'⁻¹
      rw [hbval]
  have hEnorm : y ∈ normalizer (E : Set H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · exact fun hg => hEconj g hg y hyNorm
    · intro hg
      have h := hEconj (y * g * y⁻¹) hg y⁻¹ (Subgroup.inv_mem _ hyNorm)
      have h' : y⁻¹ * (y * g * y⁻¹) * (y⁻¹)⁻¹ = g := by group
      rwa [h'] at h
  obtain ⟨b, hbord⟩ : ∃ b : ↥(Subgroup.center ↥P), orderOf b = 2 := by
    have hc2 : IsPGroup 2 ↥(Subgroup.center ↥P) := hP2.to_subgroup _
    have hnt : Nontrivial ↥(Subgroup.center ↥P) := hP2.center_nontrivial
    obtain ⟨n, hn0, hn⟩ := hc2.nontrivial_iff_card.mp hnt
    have hdvd : 2 ∣ Nat.card ↥(Subgroup.center ↥P) := by
      rw [hn]
      exact dvd_pow_self 2 (by omega : n ≠ 0)
    exact exists_prime_orderOf_dvd_card' 2 hdvd
  let bP : ↥P := b.1
  have hbc : bP ∈ Subgroup.center ↥P := b.2
  have hb2 : bP ^ 2 = 1 := by
    have h : b ^ 2 = 1 := by rw [← hbord]; exact pow_orderOf_eq_one b
    exact congrArg Subtype.val h
  let z₀ : H := (bP : H)
  have hz₀E : z₀ ∈ E := (hEmem z₀).mpr ⟨bP, hbc, hb2, rfl⟩
  have hz₀1 : z₀ ≠ 1 := by
    intro h
    have hbP1 : bP = 1 := Subtype.ext (by simpa [z₀] using h)
    have hb1 : b = 1 := Subtype.ext (by simpa [bP] using hbP1)
    rw [hb1, orderOf_one] at hbord
    omega
  by_cases hA : ∃ z ∈ E, z ≠ 1 ∧ z * y = y * z
  · obtain ⟨z, hzE, hz1, hzy⟩ := hA
    let e : (Module.End F (Fin 7 → F))ˣ :=
      Matrix.GeneralLinearGroup.toLin (n := Fin 7) (R := F) (ρH z)
    let Mz : Matrix (Fin 7) (Fin 7) F := m z
    have he : e * e = 1 := by
      have h : ψ z * ψ z = 1 := by rw [← map_mul, hEsq z hzE, map_one]
      show e * e = 1
      rw [show e = ψ z from rfl, h]
    have hMzsq : Mz * Mz = 1 := by
      have h : ρH z * ρH z = 1 := by rw [← map_mul, hEsq z hzE, map_one]
      have h' := congrArg Units.val h
      simpa [Mz, m, Units.coeHom, Units.val_mul] using h'
    have hMzB : Mz.transpose * G2Seven.gram F * Mz = G2Seven.gram F := hform (z : X)
    have hMzX : ∀ a b, Mz *ᵥ cross7 a b = cross7 (Mz *ᵥ a) (Mz *ᵥ b) := hcross (z : X)
    have hMz1 : Mz ≠ 1 := by
      intro h
      apply hz1
      apply hm
      rw [show m z = 1 from h, map_one]
    have hMeig : Module.finrank F (eigM Mz) = 4 :=
      finrank_eigM_eq_four (Ring.two_ne_zero hF) hMzsq hMzB hMzX hMz1
    have hPeig : Module.finrank F (eigP Mz) = 3 :=
      finrank_eigP_of_involution (Ring.two_ne_zero hF) hMzsq hMzB hMzX hMz1
    have heigP : LinearMap.ker ((e : Module.End F (Fin 7 → F)) - 1) = eigP Mz := by
      ext a
      rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero, mem_eigP,
        Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply]
      rfl
    have heigM : LinearMap.ker ((e : Module.End F (Fin 7 → F)) + 1) = eigM Mz := by
      ext a
      rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
        add_eq_zero_iff_eq_neg, mem_eigM, Matrix.GeneralLinearGroup.toLin_apply,
        Matrix.mulVecLin_apply]
      rfl
    have hPdim : Module.finrank F (LinearMap.ker ((e : Module.End F (Fin 7 → F)) - 1)) ≤ 4 := by
      rw [heigP, hPeig]
      omega
    have hMdim : Module.finrank F (LinearMap.ker ((e : Module.End F (Fin 7 → F)) + 1)) ≤ 4 := by
      rw [heigM, hMeig]
    let R : Subgroup (Module.End F (Fin 7 → F))ˣ := P.map ψ
    have hR2 : IsPGroup 2 R := hP2.map ψ
    have hRe : ∀ r ∈ R, r * e = e * r := by
      intro r hr
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hr
      have h' := congrArg ψ (hEcenter z hzE q hq)
      show ψ q * ψ z = ψ z * ψ q
      simpa only [map_mul] using h'.symm
    have hye : ψ y * e = e * ψ y := by
      have h' := congrArg ψ hzy
      show ψ y * ψ z = ψ z * ψ y
      simpa only [map_mul] using h'.symm
    have hyR : ψ y ∈ normalizer (R : Set (Module.End F (Fin 7 → F))ˣ) :=
      Subgroup.le_normalizer_map ψ (Subgroup.mem_map.mpr ⟨y, hyNorm, rfl⟩)
    have hyr : ψ y ^ orderOf y = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hcomm := commute_of_eigenspaces_finrank_le_four (V := Fin 7 → F) hF he hR2 hRe hye hyR
      hyPrime hy7 hyr hPdim hMdim
    have hx₀R : ψ x₀ ∈ R := Subgroup.mem_map.mpr ⟨x₀, hx₀P, rfl⟩
    have hψcomm := hcomm (ψ x₀) hx₀R
    have hyx₀ : y * x₀ = x₀ * y := by
      apply hψ
      simpa only [map_mul] using hψcomm
    exact hx₀ hyx₀
  · have hB : ∀ z ∈ E, z ≠ 1 → z * y ≠ y * z := by
      intro z hz hz1 hzy
      exact hA ⟨z, hz, hz1, hzy⟩
    rcases hy7 with h7 | h17
    ·
      have hy7 : y ^ 7 = 1 := by rw [← h7]; exact pow_orderOf_eq_one y
      let z₁ : H := z₀
      let z₂ : H := y * z₀ * y⁻¹
      let z₃ : H := y ^ 2 * z₀ * (y ^ 2)⁻¹
      let z₄ : H := y ^ 3 * z₀ * (y ^ 3)⁻¹
      have hz₁E : z₁ ∈ E := hz₀E
      have hz₂E : z₂ ∈ E := by
        have h := hEconj z₀ hz₀E y hyNorm
        simpa [z₂] using h
      have hz₃E : z₃ ∈ E := by
        have hy2 : y ^ 2 ∈ normalizer (P : Set H) := Subgroup.pow_mem _ hyNorm 2
        have h := hEconj z₀ hz₀E (y ^ 2) hy2
        simpa [z₃] using h
      have hz₄E : z₄ ∈ E := by
        have hy3 : y ^ 3 ∈ normalizer (P : Set H) := Subgroup.pow_mem _ hyNorm 3
        have h := hEconj z₀ hz₀E (y ^ 3) hy3
        simpa [z₄] using h
      have hsq₁ : z₁ * z₁ = 1 := hEsq z₁ hz₁E
      have hsq₂ : z₂ * z₂ = 1 := hEsq z₂ hz₂E
      have hsq₃ : z₃ * z₃ = 1 := hEsq z₃ hz₃E
      have hsq₂₃ : (z₂ * z₃) * (z₂ * z₃) = 1 := hEsq (z₂ * z₃) (E.mul_mem hz₂E hz₃E)
      have h12 : z₁ * z₂ = z₂ * z₁ := hEcomm z₁ hz₁E z₂ hz₂E
      have h13 : z₁ * z₃ = z₃ * z₁ := hEcomm z₁ hz₁E z₃ hz₃E
      have h23 : z₂ * z₃ = z₃ * z₂ := hEcomm z₂ hz₂E z₃ hz₃E
      have hz₁1 : z₁ ≠ 1 := hz₀1
      have hz₂1 : z₂ ≠ 1 := by
        intro h
        apply hz₀1
        have h' : y * z₀ * y⁻¹ = 1 := h
        calc z₀ = y⁻¹ * (y * z₀ * y⁻¹) * y := by group
          _ = 1 := by rw [h']; group
      have hz₃1 : z₃ ≠ 1 := by
        intro h
        apply hz₀1
        have h' : y ^ 2 * z₀ * (y ^ 2)⁻¹ = 1 := h
        calc z₀ = (y ^ 2)⁻¹ * (y ^ 2 * z₀ * (y ^ 2)⁻¹) * y ^ 2 := by group
          _ = 1 := by rw [h']; group
      have hz₁₂ : z₁ * z₂ ≠ 1 := by
        intro h
        apply hB z₀ hz₀E hz₀1
        have h' : y * z₀ * y⁻¹ = z₀ := by
          calc y * z₀ * y⁻¹ = (z₁ * z₁) * (y * z₀ * y⁻¹) := by rw [hsq₁, one_mul]
            _ = z₁ * (z₁ * (y * z₀ * y⁻¹)) := by group
            _ = z₁ * 1 := by rw [show z₁ * (y * z₀ * y⁻¹) = 1 from h]
            _ = z₁ := mul_one _
        calc z₀ * y = (y * z₀ * y⁻¹) * y := by rw [h']
          _ = y * z₀ := by group
      have hz₁₃ : z₁ * z₃ ≠ 1 := by
        intro h
        apply hB z₀ hz₀E hz₀1
        have h' : y ^ 2 * z₀ * (y ^ 2)⁻¹ = z₀ := by
          calc y ^ 2 * z₀ * (y ^ 2)⁻¹ = (z₁ * z₁) * (y ^ 2 * z₀ * (y ^ 2)⁻¹) := by
                rw [hsq₁, one_mul]
            _ = z₁ * (z₁ * (y ^ 2 * z₀ * (y ^ 2)⁻¹)) := by group
            _ = z₁ * 1 := by rw [show z₁ * (y ^ 2 * z₀ * (y ^ 2)⁻¹) = 1 from h]
            _ = z₁ := mul_one _
        have h2 : y ^ 2 * z₀ = z₀ * y ^ 2 := by
          calc y ^ 2 * z₀ = (y ^ 2 * z₀ * (y ^ 2)⁻¹) * y ^ 2 := by group
            _ = z₀ * y ^ 2 := by rw [h']
        exact (commute_of_pow_commute_seven hy7 (k := 2) (Or.inl rfl) h2).symm
      have hz₂₃ : z₂ * z₃ ≠ 1 := by
        intro h
        have hyinv : y⁻¹ ∈ normalizer (P : Set H) := Subgroup.inv_mem _ hyNorm
        have hconj : y⁻¹ * (z₂ * z₃) * (y⁻¹)⁻¹ ∈ E :=
          hEconj (z₂ * z₃) (E.mul_mem hz₂E hz₃E) y⁻¹ hyinv
        have h' : y⁻¹ * (z₂ * z₃) * (y⁻¹)⁻¹ = z₁ * z₂ := by
          show y⁻¹ * ((y * z₀ * y⁻¹) * (y ^ 2 * z₀ * (y ^ 2)⁻¹)) * (y⁻¹)⁻¹ =
            z₀ * (y * z₀ * y⁻¹)
          group
        have hzero : y⁻¹ * (z₂ * z₃) * (y⁻¹)⁻¹ = 1 := by rw [h]; group
        rw [h'] at hzero
        exact hz₁₂ hzero
      have hz₁₂₃ : z₁ * z₂ * z₃ ≠ 1 := by
        intro h
        have hconj : y * (z₁ * z₂ * z₃) * y⁻¹ = 1 := by rw [h]; group
        have h234 : z₂ * z₃ * z₄ = 1 := by
          have h' : y * (z₁ * z₂ * z₃) * y⁻¹ = z₂ * z₃ * z₄ := by
            show y * (z₀ * (y * z₀ * y⁻¹) * (y ^ 2 * z₀ * (y ^ 2)⁻¹)) * y⁻¹ =
              (y * z₀ * y⁻¹) * (y ^ 2 * z₀ * (y ^ 2)⁻¹) * (y ^ 3 * z₀ * (y ^ 3)⁻¹)
            group
          rwa [h'] at hconj
        have h4 : z₄ = z₂ * z₃ := by
          calc z₄ = ((z₂ * z₃) * (z₂ * z₃)) * z₄ := by rw [hsq₂₃, one_mul]
            _ = (z₂ * z₃) * (z₂ * z₃ * z₄) := by group
            _ = (z₂ * z₃) * 1 := by rw [h234]
            _ = z₂ * z₃ := mul_one _
        have h1 : z₁ = z₂ * z₃ := by
          calc z₁ = z₁ * ((z₂ * z₃) * (z₂ * z₃)) := by rw [hsq₂₃, mul_one]
            _ = (z₁ * z₂ * z₃) * (z₂ * z₃) := by group
            _ = 1 * (z₂ * z₃) := by rw [h]
            _ = z₂ * z₃ := one_mul _
        have hz₄ : z₄ = z₁ := h4.trans h1.symm
        have hcomm3 : y ^ 3 * z₀ = z₀ * y ^ 3 := by
          have hz₄' : y ^ 3 * z₀ * (y ^ 3)⁻¹ = z₀ := hz₄
          calc y ^ 3 * z₀ = (y ^ 3 * z₀ * (y ^ 3)⁻¹) * y ^ 3 := by group
            _ = z₀ * y ^ 3 := by rw [hz₄']
        exact hB z₀ hz₀E hz₀1 (commute_of_pow_commute_seven hy7 (k := 3) (Or.inr rfl) hcomm3).symm
      let M₁ : Matrix (Fin 7) (Fin 7) F := m z₁
      let M₂ : Matrix (Fin 7) (Fin 7) F := m z₂
      let M₃ : Matrix (Fin 7) (Fin 7) F := m z₃
      have hM₁sq : M₁ * M₁ = 1 := by
        change m z₁ * m z₁ = 1
        rw [← map_mul, hsq₁, map_one]
      have hM₂sq : M₂ * M₂ = 1 := by
        change m z₂ * m z₂ = 1
        rw [← map_mul, hsq₂, map_one]
      have hM₃sq : M₃ * M₃ = 1 := by
        change m z₃ * m z₃ = 1
        rw [← map_mul, hsq₃, map_one]
      have hM₁₂ : M₁ * M₂ = M₂ * M₁ := by
        change m z₁ * m z₂ = m z₂ * m z₁
        rw [← map_mul, ← map_mul, h12]
      have hM₁₃ : M₁ * M₃ = M₃ * M₁ := by
        change m z₁ * m z₃ = m z₃ * m z₁
        rw [← map_mul, ← map_mul, h13]
      have hM₂₃ : M₂ * M₃ = M₃ * M₂ := by
        change m z₂ * m z₃ = m z₃ * m z₂
        rw [← map_mul, ← map_mul, h23]
      have hM₁B : M₁.transpose * G2Seven.gram F * M₁ = G2Seven.gram F := hform (z₁ : X)
      have hM₂B : M₂.transpose * G2Seven.gram F * M₂ = G2Seven.gram F := hform (z₂ : X)
      have hM₃B : M₃.transpose * G2Seven.gram F * M₃ = G2Seven.gram F := hform (z₃ : X)
      have hM₁X : ∀ a b, M₁ *ᵥ cross7 a b = cross7 (M₁ *ᵥ a) (M₁ *ᵥ b) := hcross (z₁ : X)
      have hM₂X : ∀ a b, M₂ *ᵥ cross7 a b = cross7 (M₂ *ᵥ a) (M₂ *ᵥ b) := hcross (z₂ : X)
      have hM₃X : ∀ a b, M₃ *ᵥ cross7 a b = cross7 (M₃ *ᵥ a) (M₃ *ᵥ b) := hcross (z₃ : X)
      have hM₁ne : M₁ ≠ 1 := by
        intro h
        apply hz₁1
        apply hm
        rw [show m z₁ = 1 from h, map_one]
      have hM₂ne : M₂ ≠ 1 := by
        intro h
        apply hz₂1
        apply hm
        rw [show m z₂ = 1 from h, map_one]
      have hM₃ne : M₃ ≠ 1 := by
        intro h
        apply hz₃1
        apply hm
        rw [show m z₃ = 1 from h, map_one]
      have hM₁₂ne : M₁ * M₂ ≠ 1 := by
        intro h
        apply hz₁₂
        apply hm
        rw [map_mul, map_one]
        exact h
      have hM₁₃ne : M₁ * M₃ ≠ 1 := by
        intro h
        apply hz₁₃
        apply hm
        rw [map_mul, map_one]
        exact h
      have hM₂₃ne : M₂ * M₃ ≠ 1 := by
        intro h
        apply hz₂₃
        apply hm
        rw [map_mul, map_one]
        exact h
      have hM₁₂₃ne : M₁ * M₂ * M₃ ≠ 1 := by
        intro h
        apply hz₁₂₃
        apply hm
        rw [map_mul, map_mul, map_one]
        exact h
      have hNu₁ : m u * M₁ = M₁ * m u := by
        change m u * m z₁ = m z₁ * m u
        rw [← map_mul, ← map_mul]
        exact congrArg m (hEcenter z₁ hz₁E u huP).symm
      have hNu₂ : m u * M₂ = M₂ * m u := by
        change m u * m z₂ = m z₂ * m u
        rw [← map_mul, ← map_mul]
        exact congrArg m (hEcenter z₂ hz₂E u huP).symm
      have hNu₃ : m u * M₃ = M₃ * m u := by
        change m u * m z₃ = m z₃ * m u
        rw [← map_mul, ← map_mul]
        exact congrArg m (hEcenter z₃ hz₃E u huP).symm
      have hNv₁ : m v * M₁ = M₁ * m v := by
        change m v * m z₁ = m z₁ * m v
        rw [← map_mul, ← map_mul]
        exact congrArg m (hEcenter z₁ hz₁E v hvP).symm
      have hNv₂ : m v * M₂ = M₂ * m v := by
        change m v * m z₂ = m z₂ * m v
        rw [← map_mul, ← map_mul]
        exact congrArg m (hEcenter z₂ hz₂E v hvP).symm
      have hNv₃ : m v * M₃ = M₃ * m v := by
        change m v * m z₃ = m z₃ * m v
        rw [← map_mul, ← map_mul]
        exact congrArg m (hEcenter z₃ hz₃E v hvP).symm
      have hNN' := commute_of_commute_three_involutions (K := F) (Ring.two_ne_zero hF)
        hM₁sq hM₂sq hM₃sq hM₁₂ hM₁₃ hM₂₃
        hM₁B hM₂B hM₃B hM₁X hM₂X hM₃X
        hM₁ne hM₂ne hM₃ne hM₁₂ne hM₁₃ne hM₂₃ne hM₁₂₃ne
        hNu₁ hNu₂ hNu₃ hNv₁ hNv₂ hNv₃
      have huv' : u * v = v * u := by
        apply hm
        rw [map_mul, map_mul]
        exact hNN'
      exact huv huv'
    ·
      have hW17 : Module.finrank F (Fin 7 → F) < orderOf y := by
        rw [Module.finrank_fin_fun]
        omega
      have hE2 : ∀ e ∈ E.map ψ, e * e = 1 := by
        intro e he
        obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp he
        rw [← map_mul, hEsq q hq, map_one]
      have hEc : ∀ e ∈ E.map ψ, ∀ f ∈ E.map ψ, e * f = f * e := by
        intro e he f hf
        obtain ⟨q₁, hq₁, rfl⟩ := Subgroup.mem_map.mp he
        obtain ⟨q₂, hq₂, rfl⟩ := Subgroup.mem_map.mp hf
        rw [← map_mul, ← map_mul, hEcomm q₁ hq₁ q₂ hq₂]
      have hyEnorm : ψ y ∈ normalizer ((E.map ψ : Subgroup _) : Set _) :=
        Subgroup.le_normalizer_map ψ (Subgroup.mem_map.mpr ⟨y, hEnorm, rfl⟩)
      have hb : ψ y ^ (orderOf y ^ 1) = 1 := by
        rw [pow_one, ← map_pow, pow_orderOf_eq_one, map_one]
      have hcomm :=
        CFSG.LocalAnalysis.RankThreeTheoremC.AutSection.commute_of_sq_eq_one_of_normalizes
          hyPrime hF hW17 hE2 hEc (k := 1) hb hyEnorm
      have hzz := hcomm (ψ z₀) (Subgroup.mem_map.mpr ⟨z₀, hz₀E, rfl⟩)
      exact hB z₀ hz₀E hz₀1 (by
        apply hψ
        simpa only [map_mul] using hzz.symm)

theorem noSzOverTwo_of_chevalleyExceptionalModel_G2
    {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2)
    (h : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 p f) : NoSzOverTwo X := by
  obtain ⟨hp, hf, -⟩ := h.1
  have hFact : Fact (Nat.Prime p) := ⟨hp⟩
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup .G2 h.2
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K p :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  let ρ : X →* GL (Fin 7) K := (rep7 K).comp e.toMonoidHom
  have hρ : Function.Injective ρ := (rep7_injective K hK2).comp e.injective
  have hform : ∀ g : X, ((ρ g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K).transpose *
      G2Seven.gram K * ((ρ g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) = G2Seven.gram K :=
    fun g => rep7_form K (e g)
  have hcross : ∀ g : X, ∀ u v,
      ((ρ g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *ᵥ cross7 u v =
      cross7 (((ρ g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *ᵥ u)
        (((ρ g : GL (Fin 7) K) : Matrix (Fin 7) (Fin 7) K) *ᵥ v) := by
    intro g u v
    have hh := rep7_map_mem_crossSubgroup K (RingHom.id K) (e g)
    rw [Matrix.GeneralLinearGroup.map_id, MonoidHom.id_apply] at hh
    exact hh u v
  exact noSzOverTwo_of_g2Seven hK2 ρ hρ hform hcross

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
