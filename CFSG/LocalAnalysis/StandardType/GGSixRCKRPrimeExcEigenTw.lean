module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcDefs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.Defs
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.FrobeniusOnRoots
public import CFSG.RankThree.E6.RootLatticeTools
public import CFSG.LieType.SeitzGeneration.ExcTorusCount
public import CFSG.LocalAnalysis.StandardType.GGLieCoreAutomizer

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.StandardType CFSG.StandardType.GGFinModel
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.SeitzGeneration CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag IsElemAbelian)
open scoped Matrix

theorem rckExc_torus_eigen_of_rho
    {τ : Tag} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Dl : LangDatum τ GGL) (ρ : Equiv.Perm (Fin τ.rank → ℤ)) (hρ : FrobRootMap Dl ρ)
    (N : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (hρN : ∀ i, ρ (Pi.single i 1) = N *ᵥ (Pi.single i 1 : Fin τ.rank → ℤ))
    (A' : Subgroup (ModGL τ GGL)) (hA'el : IsElemAbelian p A')
    (hA' : ∀ x ∈ A', Dl.g0⁻¹ * x * Dl.g0 ∈ Dl.torus) :
    Nat.card A' ≤ Nat.card {z : Fin τ.rank → ZMod p //
      (modMat p N)ᵀ *ᵥ z = (Dl.q : ZMod p) • z} := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_units (L := GGL) (ℓ := 2) (by norm_num) hp hp2
  have hζL : IsPrimitiveRoot (ζ : GGL) p := IsPrimitiveRoot.coe_units_iff.mpr hζ
  have hex : ∀ x : A', ∃ q : (Fin τ.rank → GGLˣ) × (Fin τ.rank → ZMod p),
      rootDiagUnit τ q.1 = Dl.g0⁻¹ * (x : ModGL τ GGL) * Dl.g0 ∧
      (∀ j, q.1 j = ζ ^ (q.2 j).val) ∧
      (modMat p N)ᵀ *ᵥ q.2 = (Dl.q : ZMod p) • q.2 := by
    intro x
    have hx : (x : ModGL τ GGL) ∈ A' := x.2
    set y : ModGL τ GGL := Dl.g0⁻¹ * (x : ModGL τ GGL) * Dl.g0 with hydef
    have hy : y ∈ Dl.torus := hA' _ hx
    have hyT : y ∈ torusGroup τ GGL :=
      (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.1
        (show y ∈ CFSG.RankThree.PartOne.KE.twistedTorusOf Dl.n Dl.Φ from hy)).1
    obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (τ := τ) (K := GGL) hyT
    have hxp : (x : ModGL τ GGL) ^ p = 1 := hA'el.2 x x.2
    have hyp : y ^ p = 1 := by
      rw [hydef]
      have hconj : Dl.g0⁻¹ * (x : ModGL τ GGL) * Dl.g0 =
          (MulAut.conj Dl.g0⁻¹) (x : ModGL τ GGL) := by
        simp [MulAut.conj_apply]
      rw [hconj, ← map_pow, hxp, map_one]
    have hrootp : (rootDiagUnit τ a) ^ p = 1 := by rw [← ha]; exact hyp
    have hap : a ^ p = 1 := by
      apply rootDiagUnit_injective (τ := τ) (K := GGL)
      show (rootDiagUnitHom τ GGL) (a ^ p) = (rootDiagUnitHom τ GGL) 1
      rw [map_pow]
      change (rootDiagUnit τ a) ^ p = (rootDiagUnitHom τ GGL) 1
      rw [hrootp, map_one]
    have haj : ∀ j, (a j : GGL) ^ p = 1 := fun j => by
      have := congrFun hap j
      have h2 : (a ^ p) j = a j ^ p := Pi.pow_apply a p j
      rw [h2, Pi.one_apply] at this
      simpa using congrArg (fun t : GGLˣ => (t : GGL)) this
    choose k hk hka using fun j => hζL.eq_pow_of_pow_eq_one (haj j)
    let z : Fin τ.rank → ZMod p := fun j => (k j : ZMod p)
    have hzval : ∀ j, (z j).val = k j := fun j => ZMod.val_natCast_of_lt (hk j)
    have haz : ∀ j, a j = ζ ^ (z j).val := fun j => by
      apply Units.ext
      rw [hzval j, Units.val_pow_eq_pow_val]
      exact (hka j).symm
    have heig : (modMat p N)ᵀ *ᵥ z = (Dl.q : ZMod p) • z := by
      ext i
      set u : Fin τ.rank → ℤ := N *ᵥ (Pi.single i 1) with hu
      have hya : rootDiagUnit τ a ∈ Dl.torus := ha ▸ hy
      have hchar := hρ.rootChar_eq a hya (Pi.single i 1) (isRoot_single τ i)
      have hρsingle : ρ (Pi.single i 1) = u := by rw [hu]; exact hρN i
      rw [hρsingle] at hchar
      have hsing : rootChar a (Pi.single i 1) = a i := by
        have := rootChar_nsmul_single a i 1
        simpa only [one_nsmul, pow_one] using this
      rw [hsing] at hchar
      have hL : rootChar a u = ζ ^ (∑ j, ((z j).val : ℤ) * u j) := by
        rw [show a = expTuple ζ z from funext fun j => haz j]
        exact rootChar_expTuple z u
      have hR : a i ^ Dl.q = ζ ^ (((z i).val : ℤ) * (Dl.q : ℤ)) := by
        rw [haz i, ← pow_mul, ← zpow_natCast]
        congr 1
      have hζeq : ζ ^ (∑ j, ((z j).val : ℤ) * u j) =
          ζ ^ (((z i).val : ℤ) * (Dl.q : ℤ)) := by
        rw [← hL, hchar, hR]
      have hdvd : (p : ℤ) ∣ (∑ j, ((z j).val : ℤ) * u j) - ((z i).val : ℤ) * (Dl.q : ℤ) := by
        apply (hζ.zpow_eq_one_iff_dvd _).1
        rw [zpow_sub, hζeq, mul_inv_cancel]
      have hzero : (((∑ j, ((z j).val : ℤ) * u j) - ((z i).val : ℤ) * (Dl.q : ℤ) : ℤ) :
          ZMod p) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact hdvd
      have hsum2 : (∑ j, (z j).val * (Pi.single i 1 : Fin τ.rank → ℤ) j) = (z i).val := by
        rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj])
          (fun h => absurd (Finset.mem_univ i) h)]
        simp [Pi.single_apply]
      have hsum1 : (∑ j, (((Pi.single i 1 : Fin τ.rank → ℤ) j : ℤ) : ZMod p) *
          (((modMat p N)ᵀ *ᵥ z - (Dl.q : ZMod p) • z) j)) =
          ((modMat p N)ᵀ *ᵥ z - (Dl.q : ZMod p) • z) i := by
        rw [Finset.sum_eq_single i (fun j _ hj => by simp [Pi.single_apply, hj])
          (fun h => absurd (Finset.mem_univ i) h)]
        simp [Pi.single_apply]
      have hcast := cast_rootChar_exponent (p := p) N z (Pi.single i 1) Dl.q
      have hcast' : (((∑ j, ((z j).val : ℤ) * u j) - ((z i).val : ℤ) * (Dl.q : ℤ) : ℤ) :
          ZMod p) = ((modMat p N)ᵀ *ᵥ z - (Dl.q : ZMod p) • z) i := by
        rw [hu]
        have hc := hcast
        rw [hsum2] at hc
        rw [hsum1] at hc
        exact hc
      have hcoord : ((modMat p N)ᵀ *ᵥ z - (Dl.q : ZMod p) • z) i = 0 := by
        rw [← hcast']
        exact hzero
      exact sub_eq_zero.mp hcoord
    exact ⟨(a, z), ha.symm, haz, heig⟩
  let F : A' → (Fin τ.rank → GGLˣ) × (Fin τ.rank → ZMod p) := fun x => Classical.choose (hex x)
  let f : A' → {z : Fin τ.rank → ZMod p //
      (modMat p N)ᵀ *ᵥ z = (Dl.q : ZMod p) • z} :=
    fun x => ⟨(F x).2, (Classical.choose_spec (hex x)).2.2⟩
  refine Nat.card_le_card_of_injective f ?_
  intro x y hxy
  have hzxy : (F x).2 = (F y).2 := congrArg Subtype.val hxy
  have hspecx := (Classical.choose_spec (hex x)).2
  have hspecy := (Classical.choose_spec (hex y)).2
  have haxy : (F x).1 = (F y).1 := funext fun j => by
    rw [hspecx.1 j, hspecy.1 j, hzxy]
  have hconj : Dl.g0⁻¹ * (x : ModGL τ GGL) * Dl.g0 =
      Dl.g0⁻¹ * (y : ModGL τ GGL) * Dl.g0 := by
    rw [← (Classical.choose_spec (hex x)).1, ← (Classical.choose_spec (hex y)).1, haxy]
  have hxy_modgl : (x : ModGL τ GGL) = (y : ModGL τ GGL) := by
    calc (x : ModGL τ GGL)
        = Dl.g0 * (Dl.g0⁻¹ * (x : ModGL τ GGL) * Dl.g0) * Dl.g0⁻¹ := by group
      _ = Dl.g0 * (Dl.g0⁻¹ * (y : ModGL τ GGL) * Dl.g0) * Dl.g0⁻¹ := by rw [hconj]
      _ = (y : ModGL τ GGL) := by group
  exact Subtype.ext hxy_modgl

private theorem rckEigTw_step_pinnedX
    {f : ℕ} (Dl : LangDatum Tag.E6 GGL) (w : WeylGroup Tag.E6)
    (hn : Dl.n = canonicalRep (coxeterSystem Tag.E6) GGL w)
    (hΦ : Dl.Φ = twistHom TwistTag.E6 GGL (ggFrobT f))
    {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) :
    ∃ ε : GGL, ε * ε = 1 ∧ ∀ c : GGL,
      Dl.step (pinnedX Tag.E6 GGL γ c) =
        pinnedX Tag.E6 GGL (w • permLattice e6Rho γ) (ε * c ^ 2 ^ f) := by
  set P : ModGL Tag.E6 GGL := diagramMap TwistTag.E6 GGL with hP
  obtain ⟨ε1, hε1, h1⟩ := diagramMap_conj_pinnedX (K := GGL) TwistTag.E6 hγ
  have hβ : IsRoot Tag.E6 (permLattice e6Rho γ) := by
    rw [← latticePerm_apply]
    exact (isRoot_latticePerm_iff (τ := Tag.E6) (π := e6Rho) TwistTag.E6.cartan_perm γ).2 hγ
  obtain ⟨ε2, hε2, h2⟩ := exists_canonicalRep_mul_pinnedX_mul_inv GGL w hβ
  have h1P : ∀ c : GGL, P * pinnedX Tag.E6 GGL γ c * P⁻¹ =
      pinnedX Tag.E6 GGL (permLattice e6Rho γ) (ε1 * c) := by
    intro c
    change diagramMap TwistTag.E6 GGL * pinnedX TwistTag.E6.tag GGL γ c *
        (diagramMap TwistTag.E6 GGL)⁻¹ =
      pinnedX TwistTag.E6.tag GGL (permLattice TwistTag.E6.perm γ) (ε1 * c)
    exact h1 c
  refine ⟨ε2 * ε1, by linear_combination (ε2 * ε2) * hε1 + hε2, fun c => ?_⟩
  have hΦc : Dl.Φ (pinnedX Tag.E6 GGL γ c) = P * pinnedX Tag.E6 GGL γ (ggFrobT f c) * P⁻¹ := by
    rw [hΦ]
    show (MulAut.conj P) (Units.map (entrywiseHom (ggFrobT f)) (pinnedX Tag.E6 GGL γ c)) =
      P * pinnedX Tag.E6 GGL γ (ggFrobT f c) * P⁻¹
    rw [MulAut.conj_apply, CFSG.RankThree.PartOne.KE.units_map_entrywiseHom_pinnedX]
  rw [show Dl.step (pinnedX Tag.E6 GGL γ c) =
      Dl.n * Dl.Φ (pinnedX Tag.E6 GGL γ c) * Dl.n⁻¹ by
    simp [LangDatum.step, MulAut.conj_apply]]
  rw [hΦc, hn]
  rw [h1P ((ggFrobT f) c)]
  rw [h2, ggFrobT_apply]
  congr 1
  ring

theorem rckExc_rho_twisted
    {f : ℕ} (Dl : LangDatum Tag.E6 GGL) (ρ : Equiv.Perm (Fin Tag.E6.rank → ℤ))
    (hΦ : Dl.Φ = ggPhi .twistedE6 f) (hρ : FrobRootMap Dl ρ) :
    ∃ w : WeylGroup Tag.E6,
      ∀ γ, IsRoot Tag.E6 γ → ρ γ = (weylMatrix w * rhoMatrix) *ᵥ γ := by
  obtain ⟨w, hw⟩ := Dl.n_weyl
  have hΦ' : Dl.Φ = twistHom TwistTag.E6 GGL (ggFrobT f) := hΦ
  refine ⟨w, fun γ hγ => ?_⟩
  obtain ⟨ε, hε, hstep⟩ := rckEigTw_step_pinnedX (f := f) Dl w hw hΦ' hγ
  have hε0 : ε ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hε
    exact zero_ne_one hε
  have hsurj : Function.Surjective (fun c : GGL => ε * c ^ 2 ^ f) := by
    intro y
    obtain ⟨x, hx⟩ :=
      IsAlgClosed.exists_pow_nat_eq (y / ε) (pow_pos (by norm_num : (0 : ℕ) < 2) f)
    exact ⟨x, by show ε * x ^ 2 ^ f = y; rw [hx]; field_simp⟩
  have hmap : (rootSubgroup Tag.E6 GGL γ).map Dl.step =
      rootSubgroup Tag.E6 GGL (w • permLattice e6Rho γ) :=
    map_rootSubgroup_eq_of_forall (f := Dl.step) (g := fun c : GGL => ε * c ^ 2 ^ f) hsurj hstep
  have hmapρ : (rootSubgroup Tag.E6 GGL γ).map Dl.step = rootSubgroup Tag.E6 GGL (ρ γ) :=
    hρ.map_rootSubgroup γ hγ
  have hsub : rootSubgroup Tag.E6 GGL (ρ γ) =
      rootSubgroup Tag.E6 GGL (w • permLattice e6Rho γ) := by
    rw [← hmapρ, hmap]
  have hργ : IsRoot Tag.E6 (ρ γ) := (hρ.isRoot_iff γ).2 hγ
  have hβ : IsRoot Tag.E6 (permLattice e6Rho γ) := by
    rw [← latticePerm_apply]
    exact (isRoot_latticePerm_iff (τ := Tag.E6) (π := e6Rho) TwistTag.E6.cartan_perm γ).2 hγ
  have hρ0γ : IsRoot Tag.E6 (w • permLattice e6Rho γ) := IsRoot.smul hβ w
  have heq : ρ γ = w • permLattice e6Rho γ :=
    CFSG.StandardType.LieCore.rootSubgroup_injective_of_isRoot hργ hρ0γ hsub
  rw [heq, permLattice_eq_mulVec, ← weylMatrix_mulVec, ← Matrix.mulVec_mulVec]

end CFSG.StandardType.RCKRP
