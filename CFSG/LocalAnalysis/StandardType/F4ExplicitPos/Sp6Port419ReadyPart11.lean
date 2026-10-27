module

public import CFSG.HardMathSupport.Solomon.Proving.AutSixBalance
public import CFSG.LieType.AlgebraicGroups.ConvolutionPoints
public import CFSG.LocalAnalysis.StandardType.GGSixTCKSpace
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart10

@[expose] public section

public section
open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
  CFSG.LocalAnalysis.ComponentInitial

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.AlgebraicGroups
open scoped CFSG.ConvolutionPoints

public noncomputable section
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.AlgebraicGroups WithConv
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped CFSG.ConvolutionPoints

public section

public section

public section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition

public section

public section
open Matrix Matrix.SpecialLinearGroup
open scoped MatrixGroups

public section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.TableCRes
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

public section
open CFSG.Open
open scoped MatrixGroups

public section
open CFSG.Open CFSG.StandardType CFSG.StandardType.ClassicalPosition
open CFSG.LieType.Chevalley

public section

public section

public section
open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition

public noncomputable section
open CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley
  CFSG.LieType.TitsSimplicity CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

public section

public section

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.PartOne.KF4

public section
open CFSG.LieType.Universal CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

public noncomputable section
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LieType.Universal CFSG.StandardType

namespace CFSG.StandardType.F4ExplicitPos.RootScalar

private theorem xPar_simple_local
    {K : Type} [Field K] (F : RootOperatorFamily .F4)
    (i : Fin Tag.F4.rank) (c : K) :
    xPar F (Pi.single i 1) c = F.eltElement (simpleRoot .F4 i) c :=
  dif_pos (isRoot_single .F4 i)

theorem f4_xPar_simple_scalar_of_mem_ggTorus
    (K : Type) [Field K] [CharP K 2] (i : Fin Tag.F4.rank)
    (h : adjointGroup .F4 K) (hh : h ∈ ggTorus (f4Datum K)) :
    ∃ χ : Kˣ, ∀ c : K,
      h * xPar (rootOperatorFamily .F4) (Pi.single i 1) c * h⁻¹ =
        xPar (rootOperatorFamily .F4) (Pi.single i 1) ((χ : K) * c) := by
  let F := rootOperatorFamily .F4
  let D := f4Datum K
  have hnormal : ∀ γ ∈ D.roots,
      h ∈ Subgroup.normalizer (D.rootGroup γ : Set (adjointGroup .F4 K)) := by
    intro γ hγ
    exact (Subgroup.mem_iInf.mp (Subgroup.mem_iInf.mp hh γ) hγ)
  have hroot_pos : D.rootGroup (Pi.single i 1) = F.rootSubgroup K (simpleRoot .F4 i) := by
    classical
    change rootGroup F K (Pi.single i 1) = F.rootSubgroup K (simpleRoot .F4 i)
    rw [show rootGroup F K (Pi.single i 1) =
        (if h : IsRoot .F4 (Pi.single i 1) then F.rootSubgroup K ⟨Pi.single i 1, h⟩ else ⊥)
        from rfl,
      dif_pos (isRoot_single .F4 i)]
    congr 1
  have hroot_neg : D.rootGroup (-Pi.single i 1) = F.rootSubgroup K (-simpleRoot .F4 i) := by
    classical
    change rootGroup F K (-Pi.single i 1) = F.rootSubgroup K (-simpleRoot .F4 i)
    rw [show rootGroup F K (-Pi.single i 1) =
        (if h : IsRoot .F4 (-Pi.single i 1) then
          F.rootSubgroup K ⟨-Pi.single i 1, h⟩ else ⊥) from rfl,
      dif_pos (isRoot_neg_single .F4 i)]
    congr 1
  have hpos : ∀ c : K, ∃ c' : K,
      (h : ModGL .F4 K) * xUnit .F4 K i c * (h : ModGL .F4 K)⁻¹ = xUnit .F4 K i c' := by
    intro c
    have hN := hnormal (Pi.single i 1) (CFSG.StandardType.single_mem_roots (D := D) i)
    have hx : F.eltElement (simpleRoot .F4 i) c ∈ D.rootGroup (Pi.single i 1) := by
      rw [hroot_pos]
      exact F.eltElement_mem_rootSubgroup (simpleRoot .F4 i) c
    have hconj : h * F.eltElement (simpleRoot .F4 i) c * h⁻¹ ∈ D.rootGroup (Pi.single i 1) :=
      (Subgroup.mem_normalizer_iff.mp hN _).1 hx
    rw [hroot_pos] at hconj
    obtain ⟨c', hc'⟩ := F.mem_rootSubgroup.mp hconj
    refine ⟨c', ?_⟩
    have hc'' := congrArg (fun g : adjointGroup .F4 K => (g : ModGL .F4 K)) hc'
    simpa [F.eltUnit_simple, Subgroup.coe_mul, Subgroup.coe_inv] using hc''.symm
  have hneg : ∃ a : K,
      (h : ModGL .F4 K) * yUnit .F4 K i 1 * (h : ModGL .F4 K)⁻¹ = yUnit .F4 K i a := by
    have hN := hnormal (-Pi.single i 1) (CFSG.StandardType.neg_single_mem_roots (D := D) i)
    have hx : F.eltElement (-simpleRoot .F4 i) 1 ∈ D.rootGroup (-Pi.single i 1) := by
      rw [hroot_neg]
      exact F.eltElement_mem_rootSubgroup (-simpleRoot .F4 i) 1
    have hconj : h * F.eltElement (-simpleRoot .F4 i) 1 * h⁻¹ ∈
        D.rootGroup (-Pi.single i 1) :=
      (Subgroup.mem_normalizer_iff.mp hN _).1 hx
    rw [hroot_neg] at hconj
    obtain ⟨a, ha⟩ := F.mem_rootSubgroup.mp hconj
    refine ⟨a, ?_⟩
    have ha' := congrArg (fun g : adjointGroup .F4 K => (g : ModGL .F4 K)) ha
    simpa [F.eltUnit_neg_simple, Subgroup.coe_mul, Subgroup.coe_inv] using ha'.symm
  obtain ⟨χ, hχ⟩ := f4_simple_root_scalar_of_conj_mem K i (h : ModGL .F4 K) hpos hneg
  refine ⟨χ, fun c => ?_⟩
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [show (↑(xPar F (Pi.single i 1) c) : ModGL .F4 K) = xUnit .F4 K i c from by
        rw [xPar_simple_local F i c, F.coe_eltElement, F.eltUnit_simple],
      show (↑(xPar F (Pi.single i 1) ((χ : K) * c)) : ModGL .F4 K) =
          xUnit .F4 K i ((χ : K) * c) from by
        rw [xPar_simple_local F i ((χ : K) * c), F.coe_eltElement, F.eltUnit_simple]]
  exact hχ c

end CFSG.StandardType.F4ExplicitPos.RootScalar

public section

open CFSG.LieType.Universal CFSG.StandardType

public section

namespace CFSG.StandardType.F4ExplicitPos.CubicAction

open CFSG.Open

variable {X : Type} [Group X] [Finite X] {p : ℕ}

def conjAction {K B : Subgroup X}
    (hBN : B ≤ Subgroup.normalizer (K : Set X)) : B →* MulAut ↥K :=
  K.normalizerMonoidHom.comp (Subgroup.inclusion hBN)

theorem conjAction_apply {K B : Subgroup X} (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (b : B) (y : ↥K) :
    ((conjAction hBN b y : ↥K) : X) = (b : X) * (y : X) * (b : X)⁻¹ :=
  rfl

theorem conjAction_isElemAbelian {K B : Subgroup X} (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hBel : IsElemAbelian p B) : IsElemAbelian p (conjAction hBN).range := by
  have h := (hBel.subgroupOf B).map (conjAction hBN)
  rwa [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map] at h

theorem conjAction_ker {K B : Subgroup X} (hBN : B ≤ Subgroup.normalizer (K : Set X)) :
    (conjAction hBN).ker = (B ⊓ Subgroup.centralizer (K : Set X)).subgroupOf B := by
  ext b
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    refine ⟨b.2, fun y hy => ?_⟩
    have h1 := congrArg (fun a : ↥K => (a : X)) (DFunLike.congr_fun h ⟨y, hy⟩)
    simp only [conjAction_apply hBN, MulAut.one_apply] at h1
    calc y * (b : X) = ((b : X) * y * (b : X)⁻¹) * (b : X) := by rw [h1]
      _ = (b : X) * y := by group
  · rintro ⟨-, h⟩
    ext y
    rw [conjAction_apply hBN, MulAut.one_apply, mul_inv_eq_iff_eq_mul, ← h y y.2]

theorem conjAction_ker_card_le_p {B D J K : Subgroup X}
    (hp : p.Prime) (hBel : IsElemAbelian p B) (hDcard : Nat.card D = p ^ 2)
    (hD : D = B ⊓ Subgroup.centralizer (J : Set X)) (hJK : J ≤ K)
    (hDnc : ¬ D ≤ Subgroup.centralizer (K : Set X)) :
    Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) ≤ p := by
  have hCK : Subgroup.centralizer (K : Set X) ≤ Subgroup.centralizer (J : Set X) :=
    Subgroup.centralizer_le (SetLike.coe_mono hJK)
  have hle : B ⊓ Subgroup.centralizer (K : Set X) ≤ D := by
    rw [hD]
    exact le_inf inf_le_left (le_trans inf_le_right hCK)
  have hne : B ⊓ Subgroup.centralizer (K : Set X) ≠ D := by
    intro hEq
    apply hDnc
    rw [← hEq]
    exact inf_le_right
  have hHel : IsElemAbelian p (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) :=
    hBel.mono inf_le_left
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hHel.isPGroup.exists_card_eq
  have hk_le : k ≤ 2 := by
    have hcard_le : Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) ≤ p ^ 2 := by
      calc Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) ≤ Nat.card D :=
            Subgroup.card_le_of_le hle
        _ = p ^ 2 := hDcard
    rw [hk] at hcard_le
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hcard_le
  have hk_ne : k ≠ 2 := by
    intro hk2
    apply hne
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [hDcard, hk, hk2]
  have hk1 : k ≤ 1 := by omega
  rw [hk]
  calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
    _ = p := pow_one p

theorem cubic_action_image {B D J K : Subgroup X}
    (hp : p.Prime) (_hp2 : p ≠ 2) (hBel : IsElemAbelian p B) (hB4 : p ^ 4 ≤ Nat.card B)
    (hDcard : Nat.card D = p ^ 2) (hD : D = B ⊓ Subgroup.centralizer (J : Set X))
    (hJK : J ≤ K) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hDnc : ¬ D ≤ Subgroup.centralizer (K : Set X)) :
    IsElemAbelian p (conjAction hBN).range ∧ p ^ 3 ≤ Nat.card (conjAction hBN).range ∧
      (∀ (b : B) (y : ↥K),
        ((conjAction hBN b y : ↥K) : X) = (b : X) * (y : X) * (b : X)⁻¹) := by
  have hker_le := conjAction_ker_card_le_p (B := B) (D := D) (J := J) (K := K)
    hp hBel hDcard hD hJK hDnc
  have hcard := Subgroup.card_ker_mul_card_range (conjAction hBN)
  rw [conjAction_ker hBN,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv] at hcard
  refine ⟨conjAction_isElemAbelian hBN hBel, ?_, conjAction_apply hBN⟩
  have hmul : p * p ^ 3 ≤ p * Nat.card (conjAction hBN).range := by
    calc p * p ^ 3 = p ^ 4 := (pow_succ' p 3).symm
      _ ≤ Nat.card B := hB4
      _ = Nat.card (B ⊓ Subgroup.centralizer (K : Set X) : Subgroup X) *
            Nat.card (conjAction hBN).range := hcard.symm
      _ ≤ p * Nat.card (conjAction hBN).range := Nat.mul_le_mul_right _ hker_le
  exact Nat.le_of_mul_le_mul_left hmul hp.pos

theorem cubic_dvd_card_mulAut {B D J K : Subgroup X}
    (hp : p.Prime) (hp2 : p ≠ 2) (hBel : IsElemAbelian p B) (hB4 : p ^ 4 ≤ Nat.card B)
    (hDcard : Nat.card D = p ^ 2) (hD : D = B ⊓ Subgroup.centralizer (J : Set X))
    (hJK : J ≤ K) (hBN : B ≤ Subgroup.normalizer (K : Set X))
    (hDnc : ¬ D ≤ Subgroup.centralizer (K : Set X)) :
    p ^ 3 ∣ Nat.card (MulAut ↥K) := by
  obtain ⟨hIm, hbound, -⟩ := cubic_action_image (p := p) (B := B) (D := D) (J := J) (K := K)
    hp hp2 hBel hB4 hDcard hD hJK hBN hDnc
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, hr⟩ := hIm.isPGroup.exists_card_eq
  have hr3 : 3 ≤ r := by
    rw [hr] at hbound
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hbound
  have hIm3 : p ^ 3 ∣ Nat.card (conjAction hBN).range := by
    rw [hr]
    exact pow_dvd_pow p hr3
  have hrange_dvd : Nat.card (conjAction hBN).range ∣ Nat.card (MulAut ↥K) := by
    have h := Subgroup.card_dvd_of_le (le_top : (conjAction hBN).range ≤ ⊤)
    rwa [Nat.card_congr (Subgroup.topEquiv).toEquiv] at h
  exact dvd_trans hIm3 hrange_dvd

end CFSG.StandardType.F4ExplicitPos.CubicAction

public section

namespace CFSG.StandardType.F4ExplicitPos.GeometricRank

open Matrix CFSG.Open

variable {K L : Type} [Field K] [Field L]

def spMapHom {n : ℕ} (φ : K →+* L) : StatedSp n K →* StatedSp n L where
  toFun g := ⟨GeneralLinearGroup.map φ (g : GL (Fin n ⊕ Fin n) K),
    CFSG.Open.StatedAPI.map_mem_statedSp φ g.2⟩
  map_one' := Subtype.ext (map_one (GeneralLinearGroup.map φ))
  map_mul' g h := Subtype.ext (map_mul (GeneralLinearGroup.map φ)
    (g : GL (Fin n ⊕ Fin n) K) (h : GL (Fin n ⊕ Fin n) K))

end CFSG.StandardType.F4ExplicitPos.GeometricRank
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end
end

end
