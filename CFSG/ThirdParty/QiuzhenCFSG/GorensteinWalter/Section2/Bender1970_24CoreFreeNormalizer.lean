module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PCoreFreeFixedPointsCentralize
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.OddQuotientFixedPointFree
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.SelfCommutatorFixedPointFreeQuotient
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.InvolutionCentralizesNormalizedTwoSubgroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorSupLeOfCommutatorLeAndNormalize
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Nilpotent
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection9.theorem_9_1

namespace CFSG
end CFSG
open CFSG

/-!
# Bender §2.4: the Fitting normalizer in the core-free branch

For `D = C_{F(X)}(U)` and `R = N_{F(X)}(D)`, split the nilpotent group `R`
into its `2`-core and odd core.  Abelian Sylow `2`-subgroups put the first
part in `D`; coprime fixed-point lifting and the self-commutator action
control the second part modulo `D`.
-/

open scoped Pointwise commutatorElement

namespace CFSG.GorensteinWalter

universe u

/-- In the `O_p(X)=1` branch of solvable Bender §2.4, the normalizer in
`F(X)` of `C_{F(X)}(U)` centralizes `U` modulo that centralizer. -/
public theorem bender1970_2_4_coreFree_fittingNormalizer_commutator_le
    {X : Type u} [Group X] [Finite X]
    (U : Subgroup X) (p : ℕ) {t : X}
    (hsolv : Group.IsSolvable X) (hp : p.Prime)
    (hSylowTwo : ∀ S : Sylow 2 X,
      IsMulCommutative (S : Subgroup X))
    (ht : IsInvolution t) (hUp : IsPGroup p U)
    (hpcore : pCore p X = ⊥)
    (hUinv : Subgroup.centralizer ({t} : Set X) ≤
      Subgroup.normalizer (U : Set X))
    (hUcomm : ⁅U, Subgroup.zpowers t⁆ = U) :
    let F : Subgroup X := fittingSubgroup X
    let D : Subgroup X := F ⊓ Subgroup.centralizer (U : Set X)
    let R : Subgroup X := F ⊓ Subgroup.normalizer (D : Set X)
    ⁅R, U⁆ ≤ D := by
  classical
  let F : Subgroup X := fittingSubgroup X
  let D : Subgroup X := F ⊓ Subgroup.centralizer (U : Set X)
  let R : Subgroup X := F ⊓ Subgroup.normalizer (D : Set X)
  dsimp only
  have hFnormal : F.Normal := by
    dsimp [F]
    infer_instance
  have hFnil : Group.IsNilpotent F := by
    dsimp [F]
    infer_instance
  have hRleF : R ≤ F := inf_le_left
  have hRnormD : R ≤ Subgroup.normalizer (D : Set X) := inf_le_right
  have hDleF : D ≤ F := inf_le_left
  have hDleR : D ≤ R := by
    intro d hd
    exact ⟨hDleF hd, D.le_normalizer hd⟩
  have hUnormF : U ≤ Subgroup.normalizer (F : Set X) :=
    Subgroup.le_normalizer_of_normal
  have hUnormCU : U ≤
      Subgroup.normalizer (Subgroup.centralizer (U : Set X) : Set X) :=
    U.le_normalizer.trans (normalizer_le_normalizer_centralizer_subgroup U)
  have hUnormD : U ≤ Subgroup.normalizer (D : Set X) := by
    simpa [D] using
      ((le_inf hUnormF hUnormCU).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  have htCent : t ∈ Subgroup.centralizer ({t} : Set X) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have htnormU : t ∈ Subgroup.normalizer (U : Set X) := hUinv htCent
  have htnormF : t ∈ Subgroup.normalizer (F : Set X) :=
    (Subgroup.le_normalizer_of_normal
      (H := F) (K := (⊤ : Subgroup X))) (by simp)
  have htnormCU : t ∈
      Subgroup.normalizer (Subgroup.centralizer (U : Set X) : Set X) :=
    (normalizer_le_normalizer_centralizer_subgroup U) htnormU
  have htnormD : t ∈ Subgroup.normalizer (D : Set X) := by
    simpa [D] using
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨htnormF, htnormCU⟩)
  have hUnormR : U ≤ Subgroup.normalizer (R : Set X) := by
    have hUnormND : U ≤
        Subgroup.normalizer (Subgroup.normalizer (D : Set X) : Set X) :=
      hUnormD.trans (Subgroup.normalizer (D : Set X)).le_normalizer
    simpa [R] using
      ((le_inf hUnormF hUnormND).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  have htnormR : t ∈ Subgroup.normalizer (R : Set X) := by
    have htnormND : t ∈
        Subgroup.normalizer (Subgroup.normalizer (D : Set X) : Set X) :=
      (Subgroup.normalizer (D : Set X)).le_normalizer htnormD
    simpa [R] using
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨htnormF, htnormND⟩)
  have hRnil : Group.IsNilpotent R := by
    have hsub : Group.IsNilpotent (R.subgroupOf F) := by infer_instance
    exact Group.nilpotent_of_mulEquiv
      (G := R.subgroupOf F) (G' := R) (_h := hsub)
      (Subgroup.subgroupOfEquivOfLe hRleF)
  have hfixedF :
      F ⊓ Subgroup.centralizer ({t} : Set X) ≤ D := by
    simpa [D] using
      (normal_nilpotent_fixedPoints_le_centralizer_of_pCore_eq_bot
        U F p hp hUp hFnormal hFnil hpcore hUinv)
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let P : Subgroup R := pCore 2 R
  let K : Subgroup R := pPrimeCore 2 R
  let PX : Subgroup X := P.map R.subtype
  let KX : Subgroup X := K.map R.subtype
  let : Group.IsSolvable X := hsolv
  have : P.Characteristic := by
    dsimp [P]
    infer_instance
  have : K.Characteristic := by
    dsimp [K]
    infer_instance
  have htop : (⊤ : Subgroup R) ≤ P ⊔ K := by
    simpa [P, K] using
      (nilpotent_top_le_pCore_sup_pPrimeCore (Q := R) (p := 2) hRnil)
  have hRle : R ≤ PX ⊔ KX := by
    intro x hxR
    have hxint : (⟨x, hxR⟩ : R) ∈ P ⊔ K := htop trivial
    have hxmap : x ∈ (P ⊔ K).map R.subtype :=
      Subgroup.mem_map.mpr ⟨⟨x, hxR⟩, hxint, rfl⟩
    simpa [PX, KX, Subgroup.map_sup] using hxmap
  have hPXleR : PX ≤ R := by
    simpa [PX, P] using (Subgroup.map_subtype_le (H := R) (pCore 2 R))
  have hKXleR : KX ≤ R := by
    simpa [KX, K] using (Subgroup.map_subtype_le (H := R) (pPrimeCore 2 R))
  have hUnormPX : U ≤ Subgroup.normalizer (PX : Set X) :=
    hUnormR.trans
      (section9_normalizer_le_normalizer_map_subtype_of_characteristic
        (G := X) R P)
  have hUnormKX : U ≤ Subgroup.normalizer (KX : Set X) :=
    hUnormR.trans
      (section9_normalizer_le_normalizer_map_subtype_of_characteristic
        (G := X) R K)
  have htnormPX : t ∈ Subgroup.normalizer (PX : Set X) :=
    (section9_normalizer_le_normalizer_map_subtype_of_characteristic
      (G := X) R P) htnormR
  have htnormKX : t ∈ Subgroup.normalizer (KX : Set X) :=
    (section9_normalizer_le_normalizer_map_subtype_of_characteristic
      (G := X) R K) htnormR
  have hPXtwo : IsPGroup 2 PX := by
    simpa [PX, P] using
      (IsPGroup.map (pCore_isPGroup (G := R) (p := 2)) R.subtype)
  have hPXcent : PX ≤ Subgroup.centralizer ({t} : Set X) :=
    twoSubgroup_le_centralizer_involution_of_hasAbelianSylow
      PX hSylowTwo hPXtwo ht htnormPX
  have hPXleD : PX ≤ D := by
    intro x hx
    exact hfixedF ⟨hRleF (hPXleR hx), hPXcent hx⟩
  have hPXU : ⁅PX, U⁆ ≤ D :=
    (Subgroup.commutator_mono hPXleD le_rfl).trans
      ((Subgroup.le_normalizer_iff_commutator_le_left).mp hUnormD)
  have hKcardOdd : Odd (Nat.card K) :=
    Nat.coprime_two_left.mp (by
      simpa [K] using (pPrimeCore_coprime_card (G := R) (p := 2)))
  have hKXcard : Nat.card KX = Nat.card K := by
    simpa [KX] using
      (Subgroup.card_map_of_injective (K := K) (f := R.subtype)
        R.subtype_injective)
  have hKXodd : Odd (Nat.card KX) := by
    rw [hKXcard]
    exact hKcardOdd
  have hKXsolv : Group.IsSolvable KX := by infer_instance
  let DK : Subgroup X := KX ⊓ D
  have hDKleKX : DK ≤ KX := inf_le_left
  have hKXnormD : KX ≤ Subgroup.normalizer (D : Set X) :=
    hKXleR.trans hRnormD
  have hKXnormDK : KX ≤ Subgroup.normalizer (DK : Set X) := by
    simpa [DK] using
      ((le_inf KX.le_normalizer hKXnormD).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  have hDKnormalKX : (DK.subgroupOf KX).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hDKleKX]
    exact hKXnormDK
  have htnormDK : t ∈ Subgroup.normalizer (DK : Set X) := by
    simpa [DK] using
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨htnormKX, htnormD⟩)
  have hUnormDK : U ≤ Subgroup.normalizer (DK : Set X) := by
    simpa [DK] using
      ((le_inf hUnormKX hUnormD).trans
        Subgroup.inf_normalizer_le_normalizer_inf)
  have hfixedDK :
      KX ⊓ Subgroup.centralizer ({t} : Set X) ≤ DK := by
    intro x hx
    exact ⟨hx.1, hfixedF ⟨hRleF (hKXleR hx.1), hx.2⟩⟩
  have hquotFixed : ∀ k : KX,
      t * (k : X) * t⁻¹ * (k : X)⁻¹ ∈ DK → (k : X) ∈ DK :=
    fixedPointFree_quotient_of_odd_solvable_and_fixedPoints_le
      KX DK hDKleKX hDKnormalKX htnormKX htnormDK ht hKXsolv hKXodd hfixedDK
  have hKXU_DK : ⁅KX, U⁆ ≤ DK :=
    commutator_le_of_selfCommutator_fixedPointFree_involution_quotient
      KX DK U hDKleKX hDKnormalKX hUnormKX htnormKX
      hUnormDK htnormDK ht hUcomm hquotFixed
  have hKXU : ⁅KX, U⁆ ≤ D := hKXU_DK.trans inf_le_right
  have hsupComm : ⁅PX ⊔ KX, U⁆ ≤ D :=
    commutator_sup_le_of_commutator_le_and_normalize
      PX KX U D hPXU hKXU
      (hPXleR.trans hRnormD) (hKXleR.trans hRnormD)
  exact (Subgroup.commutator_mono hRle le_rfl).trans hsupComm

end CFSG.GorensteinWalter
