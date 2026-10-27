module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdCent
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryDvdAct
public import CFSG.LocalAnalysis.StandardType.GGTBJSuDefs
public import CFSG.LocalAnalysis.StandardType.GGTBRowPermFrameAux
public import CFSG.LinearAlgebra.LinearGroups.UnitaryScalarKernel

public section

namespace CFSG.StandardType

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover UCoord UModel

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
  {L' : Type} [Group L'] [Finite L'] {φ : ↥(unitarySU 2 n K 6) →* L'}

theorem false_of_diagonal_frame_card_twentyseven
    (hM : UnitTB.Model φ) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hpq : 3 ∣ 2 ^ n + 1)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hsc : GGTorusSelfCent 3 A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin 6 → K, LineU.ActsDiagU φ a t)
    (hcardA : Nat.card A = 27) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : NeZero 3 := ⟨by norm_num⟩
  have hn : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num at hpq
    · exact hn
  have hd : 4 ≤ 6 := by norm_num
  obtain ⟨u, hord, huq⟩ :=
    CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one (ℓ := 2) (f := n) hM.field
      (p := 3) Nat.prime_three hpq
  have hu : u ^ 3 = 1 := hord ▸ pow_orderOf_eq_one u
  let D : ↥(sumZero 6 3) →* ↥(unitarySU 2 n K 6) :=
    ggTBJSuD hM.field hu huq hord
  have hDdiag : ∀ f : ↥(sumZero 6 3),
      (((D f : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
        diagonal (fun i => ((uvec hu f i : Kˣ) : K)) := by
    intro f
    rw [show D f = ggTBJSuD hM.field hu huq hord f from rfl, ggTBJSuD_coe]
    ext i j
    rw [coe_diagHom]
  have hDval : ∀ f : ↥(sumZero 6 3),
      (D f : GL (Fin 6) K) = diagHom 6 (uvec hu f) := fun f => rfl
  have hsum3 : ∀ f : ↥(sumZero 6 3), f ^ 3 = 1 := by
    intro f
    apply UCoord.ext_crd
    intro i
    rw [UCoord.crd_pow, UCoord.crd_one]
    change (3 : ZMod 3) * UCoord.crd f i = 0
    have h3 : (3 : ZMod 3) = 0 := ZMod.natCast_self 3
    rw [h3, zero_mul]
  have hDpow : ∀ f : ↥(sumZero 6 3), (D f) ^ 3 = 1 := by
    intro f
    calc (D f) ^ 3 = D (f ^ 3) := by rw [map_pow]
      _ = D 1 := by rw [hsum3 f]
      _ = 1 := map_one D
  let τ : ↥(sumZero 6 3) →* A :=
    { toFun := fun f =>
        ⟨MulAut.conj (φ (D f)),
          LineU.conj_mem_of_selfCent_U (p := 3) (φ := φ) hsc hdiag
            (D := D f) (u := fun i => ((uvec hu f i : Kˣ) : K)) (hDdiag f)
            (fun i => by
              simpa using congrArg (fun x : Kˣ => (x : K)) (uvec_pow_eq_one hu f i))⟩
      map_one' := by
        apply Subtype.ext
        show MulAut.conj (φ (D 1)) = 1
        simp
      map_mul' := by
        intro f g
        apply Subtype.ext
        show MulAut.conj (φ (D (f * g))) = MulAut.conj (φ (D f)) * MulAut.conj (φ (D g))
        simp [map_mul] }
  have hscalar : ∀ x : τ.ker, ∃ c : K,
      (((D x.1 : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) :
        Matrix (Fin 6) (Fin 6) K) = diagonal (fun _ => c) := by
    intro x
    exact UnitTB.scalar_of_map_conj_eq (φ := φ) hM hK hd (g := D x.1) (fun y => by
      have hx : τ x.1 = 1 := x.2
      have hconj : MulAut.conj (φ (D x.1)) = 1 := congrArg Subtype.val hx
      have h1 : MulAut.conj (φ (D x.1)) (φ y) = φ y := by rw [hconj]; rfl
      simpa [MulAut.conj_apply] using h1)
  choose sc hsc using hscalar
  have hsc_ne : ∀ x : τ.ker, sc x ≠ 0 := by
    intro x h0
    have hDunit : IsUnit ((diagonal (fun _ : Fin 6 => sc x) :
        Matrix (Fin 6) (Fin 6) K)) := by
      rw [← hsc x]
      exact ⟨(D x.1 : GL (Fin 6) K), rfl⟩
    rw [h0] at hDunit
    simpa using hDunit
  have hsc_pow : ∀ x : τ.ker, (sc x) ^ 3 = 1 := by
    intro x
    have hmatpow := congrArg (fun z : ↥(unitarySU 2 n K 6) =>
      (((z : GL (Fin 6) K)) : Matrix (Fin 6) (Fin 6) K)) (hDpow x.1)
    rw [Subgroup.coe_pow] at hmatpow
    rw [Units.val_pow_eq_pow_val] at hmatpow
    rw [hsc x] at hmatpow
    have h00 := congrFun (congrFun hmatpow 0) 0
    simpa [Matrix.diagonal_pow] using h00
  let toRoots : τ.ker → rootsOfUnity 3 K := fun x =>
    ⟨Units.mk0 (sc x) (hsc_ne x), by
      rw [mem_rootsOfUnity]
      exact Units.ext (hsc_pow x)⟩
  have htoRoots_inj : Function.Injective toRoots := by
    intro x y hxy
    apply Subtype.ext
    have hc_eq : sc x = sc y := by
      have := congrArg (fun z : rootsOfUnity 3 K => ((z : Kˣ) : K)) hxy
      simpa [toRoots] using this
    have hD_eq : D x.1 = D y.1 := by
      apply Subtype.ext
      apply Units.ext
      rw [hsc x, hsc y, hc_eq]
    have huv : uvec hu x.1 = uvec hu y.1 := by
      have hDgl : (D x.1 : GL (Fin 6) K) = (D y.1 : GL (Fin 6) K) :=
        congrArg Subtype.val hD_eq
      have hdiag : diagHom 6 (uvec hu x.1) = diagHom 6 (uvec hu y.1) := by
        simpa [hDval x.1, hDval y.1] using hDgl
      exact diagHom_injective 6 hdiag
    exact uvec_injective hu hord huv
  have hker_le : Nat.card τ.ker ≤ 3 := by
    calc Nat.card τ.ker ≤ Nat.card (rootsOfUnity 3 K) :=
          Nat.card_le_card_of_injective toRoots htoRoots_inj
      _ = 3 := by
          rw [CFSG.Timmesfeld.ClassicalOrders.card_rootsOfUnity_eq_gcd]
          have h3 : 3 ∣ Nat.card K - 1 := by
            rw [hK]
            have h : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
              simpa using (Nat.sq_sub_sq (a := 2 ^ n) (b := 1))
            rw [h]
            exact Dvd.dvd.mul_right hpq _
          rw [Nat.gcd_eq_right_iff_dvd]
          exact h3
  have hrange_le : Nat.card τ.range ≤ 27 := by
    rw [← hcardA]
    exact Nat.card_le_card_of_injective (fun x : τ.range => (x : A)) (by
      intro x y hxy
      exact Subtype.ext (Subtype.ext (congrArg (fun z : A => (z : MulAut L')) hxy)))
  have hcarddom : Nat.card ↥(sumZero 6 3) = 3 ^ 5 := by
    rw [ggTBRowPerm_card_sumZero' 6 3]
  have hmul := Subgroup.card_ker_mul_card_range τ
  rw [hcarddom] at hmul
  have hle : Nat.card τ.ker * Nat.card τ.range ≤ 3 * 27 :=
    Nat.mul_le_mul hker_le hrange_le
  rw [hmul] at hle
  norm_num at hle

end CFSG.StandardType

end
