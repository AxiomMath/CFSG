module

public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitCount
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.QuasithinUnique.Setting
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CharacteristicPrimeLocal
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Monster.Code.Weights
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.H13.StatementsL2
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43

public section

namespace CFSG.Quasithin.H13.Orbit

open CFSG.Open
open scoped commutatorElement

section Ring

variable {R : Type*} [CommRing R]

@[expose] def zornEquivOf (f g : quasithinZorn R → quasithinZorn R)
    (hadd : ∀ x y, f (x + y) = f x + f y) (hsmul : ∀ (c : R) x, f (c • x) = c • f x)
    (hgf : ∀ x, g (f x) = x) (hfg : ∀ x, f (g x) = x) :
    quasithinZorn R ≃ₗ[R] quasithinZorn R where
  toFun := f
  invFun := g
  map_add' := hadd
  map_smul' := hsmul
  left_inv := hgf
  right_inv := hfg

@[expose] def fT01 (x : quasithinZorn R) : quasithinZorn R :=
  (x.1, ![x.2.1 0 + x.2.1 1, x.2.1 1, x.2.1 2], ![x.2.2.1 0, x.2.2.1 1 - x.2.2.1 0, x.2.2.1 2],
    x.2.2.2)

@[expose] def gT01 (x : quasithinZorn R) : quasithinZorn R :=
  (x.1, ![x.2.1 0 - x.2.1 1, x.2.1 1, x.2.1 2], ![x.2.2.1 0, x.2.2.1 1 + x.2.2.1 0, x.2.2.1 2],
    x.2.2.2)

@[expose] def fT10 (x : quasithinZorn R) : quasithinZorn R :=
  (x.1, ![x.2.1 0, x.2.1 1 + x.2.1 0, x.2.1 2], ![x.2.2.1 0 - x.2.2.1 1, x.2.2.1 1, x.2.2.1 2],
    x.2.2.2)

@[expose] def gT10 (x : quasithinZorn R) : quasithinZorn R :=
  (x.1, ![x.2.1 0, x.2.1 1 - x.2.1 0, x.2.1 2], ![x.2.2.1 0 + x.2.2.1 1, x.2.2.1 1, x.2.2.1 2],
    x.2.2.2)

@[expose] def fTau (x : quasithinZorn R) : quasithinZorn R :=
  (x.2.2.2, -x.2.2.1, -x.2.1, x.1)

@[expose] def fX (x : quasithinZorn R) : quasithinZorn R :=
  (x.1 - x.2.1 0, ![x.2.1 0, x.2.1 1 - x.2.2.1 2, x.2.1 2 + x.2.2.1 1],
    ![x.2.2.1 0 + x.1 - x.2.2.2 - x.2.1 0, x.2.2.1 1, x.2.2.1 2], x.2.2.2 + x.2.1 0)

@[expose] def gX (x : quasithinZorn R) : quasithinZorn R :=
  (x.1 + x.2.1 0, ![x.2.1 0, x.2.1 1 + x.2.2.1 2, x.2.1 2 - x.2.2.1 1],
    ![x.2.2.1 0 - x.1 + x.2.2.2 - x.2.1 0, x.2.2.1 1, x.2.2.1 2], x.2.2.2 - x.2.1 0)

omit [CommRing R] in
theorem zorn_ext {x y : quasithinZorn R} (h1 : x.1 = y.1) (h2 : ∀ i, x.2.1 i = y.2.1 i)
    (h3 : ∀ i, x.2.2.1 i = y.2.2.1 i) (h4 : x.2.2.2 = y.2.2.2) : x = y :=
  Prod.ext h1 (Prod.ext (funext h2) (Prod.ext (funext h3) h4))

macro "zorn_tac" : tactic => `(tactic| (
  apply zorn_ext <;> (try intro i) <;> (try fin_cases i) <;>
    (try simp [fT01, gT01, fT10, gT10, fTau, fX, gX, quasithinZornMul, quasithinCross,
      Fin.sum_univ_three]) <;> (try ring)))

@[expose] def zT01 : quasithinZorn R ≃ₗ[R] quasithinZorn R :=
  zornEquivOf fT01 gT01 (fun _ _ => by zorn_tac) (fun _ _ => by zorn_tac)
    (fun _ => by zorn_tac) (fun _ => by zorn_tac)

@[expose] def zT10 : quasithinZorn R ≃ₗ[R] quasithinZorn R :=
  zornEquivOf fT10 gT10 (fun _ _ => by zorn_tac) (fun _ _ => by zorn_tac)
    (fun _ => by zorn_tac) (fun _ => by zorn_tac)

@[expose] def zTau : quasithinZorn R ≃ₗ[R] quasithinZorn R :=
  zornEquivOf fTau fTau (fun _ _ => by zorn_tac) (fun _ _ => by zorn_tac)
    (fun _ => by zorn_tac) (fun _ => by zorn_tac)

@[expose] def zX : quasithinZorn R ≃ₗ[R] quasithinZorn R :=
  zornEquivOf fX gX (fun _ _ => by zorn_tac) (fun _ _ => by zorn_tac)
    (fun _ => by zorn_tac) (fun _ => by zorn_tac)

theorem zT01_mul (x y : quasithinZorn R) :
    zT01 (quasithinZornMul x y) = quasithinZornMul (zT01 x) (zT01 y) := by
  change fT01 _ = quasithinZornMul (fT01 x) (fT01 y)
  zorn_tac

theorem zT10_mul (x y : quasithinZorn R) :
    zT10 (quasithinZornMul x y) = quasithinZornMul (zT10 x) (zT10 y) := by
  change fT10 _ = quasithinZornMul (fT10 x) (fT10 y)
  zorn_tac

theorem zTau_mul (x y : quasithinZorn R) :
    zTau (quasithinZornMul x y) = quasithinZornMul (zTau x) (zTau y) := by
  change fTau _ = quasithinZornMul (fTau x) (fTau y)
  zorn_tac

theorem zX_mul (x y : quasithinZorn R) :
    zX (quasithinZornMul x y) = quasithinZornMul (zX x) (zX y) := by
  change fX _ = quasithinZornMul (fX x) (fX y)
  zorn_tac

theorem mem_quasithinG2 {g : quasithinZorn R ≃ₗ[R] quasithinZorn R}
    (hg : ∀ x y, g (quasithinZornMul x y) = quasithinZornMul (g x) (g y)) :
    g ∈ quasithinG2 R :=
  Subgroup.subset_closure hg

@[expose] def zC1 : quasithinZorn R ≃ₗ[R] quasithinZorn R := ⁅zT01 (R := R), zT10 (R := R)⁆

@[expose] def zC2 : quasithinZorn R ≃ₗ[R] quasithinZorn R := ⁅zTau (R := R), zX (R := R)⁆

theorem zC1_mem : zC1 ∈ ⁅quasithinG2 R, quasithinG2 R⁆ :=
  Subgroup.commutator_mem_commutator (mem_quasithinG2 (R := R) zT01_mul)
    (mem_quasithinG2 (R := R) zT10_mul)

theorem zC2_mem : zC2 ∈ ⁅quasithinG2 R, quasithinG2 R⁆ :=
  Subgroup.commutator_mem_commutator (mem_quasithinG2 (R := R) zTau_mul)
    (mem_quasithinG2 (R := R) zX_mul)

theorem zC1_apply (x : quasithinZorn R) : zC1 x = fT01 (fT10 (gT01 (gT10 x))) := rfl

theorem zC2_apply (x : quasithinZorn R) : zC2 x = fTau (fX (fTau (gX x))) := rfl

end Ring

section Map

variable {R S : Type*} [CommRing R] [CommRing S] (ψ : R →+* S)

@[expose] def zornMap (x : quasithinZorn R) : quasithinZorn S :=
  (ψ x.1, fun i => ψ (x.2.1 i), fun i => ψ (x.2.2.1 i), ψ x.2.2.2)

theorem zornMap_zC1 (x : quasithinZorn R) : zC1 (zornMap ψ x) = zornMap ψ (zC1 x) := by
  rw [zC1_apply, zC1_apply]
  apply zorn_ext <;> (try intro i) <;> (try fin_cases i) <;>
    simp [zornMap, fT01, gT01, fT10, gT10]

theorem zornMap_zC2 (x : quasithinZorn R) : zC2 (zornMap ψ x) = zornMap ψ (zC2 x) := by
  rw [zC2_apply, zC2_apply]
  apply zorn_ext <;> (try intro i) <;> (try fin_cases i) <;>
    simp [zornMap, fTau, fX, gX]

end Map

section Field

variable {K : Type*} [Field K]

@[expose] def zornOne : quasithinZorn K := (1, 0, 0, 1)

@[expose] def zornTr (x : quasithinZorn K) : K := x.1 + x.2.2.2

@[expose] def zornNorm (x : quasithinZorn K) : K := x.1 * x.2.2.2 - ∑ i, x.2.1 i * x.2.2.1 i

theorem zornOne_mul (x : quasithinZorn K) : quasithinZornMul zornOne x = x := by
  apply zorn_ext <;> (try intro i) <;> (try fin_cases i) <;>
    simp [zornOne, quasithinZornMul, quasithinCross]

theorem mul_zornOne (x : quasithinZorn K) : quasithinZornMul x zornOne = x := by
  apply zorn_ext <;> (try intro i) <;> (try fin_cases i) <;>
    simp [zornOne, quasithinZornMul, quasithinCross]

theorem zorn_quadratic (x : quasithinZorn K) :
    quasithinZornMul x x = zornTr x • x - zornNorm x • zornOne := by
  apply zorn_ext <;> (try intro i) <;> (try fin_cases i) <;>
    simp [zornOne, zornTr, zornNorm, quasithinZornMul, quasithinCross, Fin.sum_univ_three] <;>
    ring

@[expose] def zornAuts : Set (quasithinZorn K ≃ₗ[K] quasithinZorn K) :=
  {g | ∀ x y, g (quasithinZornMul x y) = quasithinZornMul (g x) (g y)}

theorem mem_zornAuts_of_mem {g : quasithinZorn K ≃ₗ[K] quasithinZorn K}
    (hg : g ∈ quasithinG2 K) : g ∈ zornAuts := by
  induction hg using Subgroup.closure_induction with
  | mem g hg => exact hg
  | one => intro x y; rfl
  | mul g h _ _ hg hh =>
    intro x y
    rw [LinearEquiv.mul_apply, hh, hg]
    rfl
  | inv g _ hg =>
    intro x y
    rw [LinearEquiv.coe_inv]
    apply g.injective
    rw [hg, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.apply_symm_apply]

theorem quasithinG2_one {g : quasithinZorn K ≃ₗ[K] quasithinZorn K} (hg : g ∈ quasithinG2 K) :
    g zornOne = zornOne := by
  have h : ∀ x y, g (quasithinZornMul x y) = quasithinZornMul (g x) (g y) :=
    mem_zornAuts_of_mem hg
  obtain ⟨y, hy⟩ := g.surjective zornOne
  have key : quasithinZornMul (g zornOne) (g y) = g y := by rw [← h, zornOne_mul]
  rw [hy, mul_zornOne] at key
  exact key

theorem quasithinG2_norm {g : quasithinZorn K ≃ₗ[K] quasithinZorn K} (hg : g ∈ quasithinG2 K)
    (x : quasithinZorn K) : zornNorm (g x) = zornNorm x := by
  have h : ∀ x y, g (quasithinZornMul x y) = quasithinZornMul (g x) (g y) :=
    mem_zornAuts_of_mem hg
  have h1 := zorn_quadratic (g x)
  have h2 := congrArg g (zorn_quadratic x)
  rw [h, map_sub, map_smul, map_smul, quasithinG2_one hg] at h2
  have h3 : (zornTr (g x) - zornTr x) • g x = (zornNorm (g x) - zornNorm x) • zornOne := by
    rw [sub_smul, sub_smul, sub_eq_sub_iff_sub_eq_sub, ← h1, h2]
  by_cases ht : zornTr (g x) - zornTr x = 0
  · rw [ht, zero_smul] at h3
    have h4 := congrArg Prod.fst h3
    simp only [Prod.smul_fst, zornOne, smul_eq_mul, mul_one, Prod.fst_zero] at h4
    exact (sub_eq_zero.1 h4.symm)
  ·
    have h5 : g x = ((zornTr (g x) - zornTr x)⁻¹ * (zornNorm (g x) - zornNorm x)) • zornOne := by
      rw [mul_smul, ← h3, smul_smul, inv_mul_cancel₀ ht, one_smul]
    set c := (zornTr (g x) - zornTr x)⁻¹ * (zornNorm (g x) - zornNorm x)
    have h6 : x = c • zornOne := by
      apply g.injective
      rw [h5, map_smul, quasithinG2_one hg]
    rw [h5, h6]

end Field

end CFSG.Quasithin.H13.Orbit
