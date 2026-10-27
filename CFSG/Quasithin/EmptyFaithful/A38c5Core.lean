module

public import CFSG.Quasithin.EmptyFaithful.A38c5Omega
public import CFSG.Quasithin.EmptyFaithful.A38c5Aut
public import CFSG.Quasithin.EmptyFaithful.S153GCount

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

namespace CFSG.Quasithin.A38c5

section Core

variable {G : Type} [Group G] [Finite G]

theorem core_abstract (hFM : FiniteFactS8)
    {U S I L K X P A : Subgroup G} (hV : IsElemAbelian 2 U)
    (hSN : S ≤ Subgroup.normalizer (U : Set G)) (hIN : I ≤ Subgroup.normalizer (U : Set G))
    (hsyl : IsSylowTwoOf S I) (hCS : I ⊓ Subgroup.centralizer (U : Set G) ≤ S)
    (hC2 : IsPGroup 2 ↥(I ⊓ Subgroup.centralizer (U : Set G))) (hUS : U ≤ S)
    (q : IntMod U hV → ZMod 2) (hq : IsQuadraticFormOn q) (hnd : IsNondegQuadratic q)
    (E : Subgroup (IntMod U hV)) (hE : Nat.card E = 2 ^ 3) (hEq : ∀ e ∈ E, q e = 0)
    (hcard : Nat.card (IntMod U hV) = 2 ^ 6) (hort : autI hV I = orthogonalGroupOf q)
    (hLI : L ≤ I) (hIL : I ≤ Subgroup.normalizer (L : Set G))
    (hLp : ⁅autI hV L, autI hV L⁆ = autI hV L) (hL1 : autI hV L ≠ ⊥)
    (hKL : K ≤ L) (hKmax : IsMaxParabolic2 (autI hV L) (autI hV K))
    (hSK : S ≤ Subgroup.normalizer (K : Set G)) (hX : X = oPrimeResidualOf 3 K)
    (hP : P = pCoreOf 2 (X ⊔ S)) (hPS : P ≤ S)
    (hSCP : S ⊓ Subgroup.centralizer (U : Set G) ≤ P)
    (hA : IsMaxElemAbelian S A)
    (hstrong : cm3 U A < rk ↥A - rk ↥(A ⊓ Subgroup.centralizer (U : Set G))) :
    cm1 P U A + 1 = cm3 U A := by
  have hW : ∀ w : IntMod U hV, w ^ 2 = 1 := IntMod.sq_eq_one
  have hAS : A ≤ S := hA.1
  have hAN : A ≤ Subgroup.normalizer (U : Set G) := hAS.trans hSN
  have hSI : S ≤ I := hsyl.1
  have hKI : K ≤ I := hKL.trans hLI
  have hKN : K ≤ Subgroup.normalizer (U : Set G) := hKI.trans hIN
  have hXK : X ≤ K := by
    rw [hX]
    exact (Subgroup.closure_le _).2 fun x hx => hx.1
  have hXN : X ≤ Subgroup.normalizer (U : Set G) := hXK.trans hKN
  have hXSI : X ⊔ S ≤ I := sup_le (hXK.trans hKI) hSI
  have hXSN : X ⊔ S ≤ Subgroup.normalizer (U : Set G) := hXSI.trans hIN
  have hAnot : ¬ A ≤ Subgroup.centralizer (U : Set G) := by
    intro h
    rw [inf_eq_left.2 h, Nat.sub_self] at hstrong
    exact Nat.not_lt_zero _ hstrong
  have hFF : IsFFStarOffender (autI hV S) (autI hV A) :=
    offenderImages_isFFStarOffender hV hUS hSN (show autI hV A ∈ offenderImages hV S from
      ⟨A, ⟨hA, hAnot⟩, rfl⟩)
  have hlt : rAV (autI hV A) < 1 := rAV_autI_lt_one hV hFF.isA2 hAN hstrong
  have hS₀ : IsSylowTwoOf (autI hV S) (orthogonalGroupOf q) :=
    hort ▸ isSylowTwoOf_autI hV hsyl hIN hCS
  have hLΩ : autI hV L ≤ orthogonalGroupOf q := hort ▸ autI_mono hV hLI
  have hLn : ((autI hV L).subgroupOf (orthogonalGroupOf q)).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    obtain ⟨l, hl, hlx⟩ := (mem_autI hV).1 hx
    have hg : (g : MulAut (IntMod U hV)) ∈ autI hV I := by
      rw [hort]
      exact g.2
    obtain ⟨i, hi, hig⟩ := (mem_autI hV).1 hg
    have hil : (i : G) * l * (i : G)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hIL hi) l).1 hl
    have key : convI hV (i * l * i⁻¹) =
        (g : MulAut (IntMod U hV)) * x * (g : MulAut (IntMod U hV))⁻¹ := by
      rw [map_mul, map_mul, map_inv, hig, hlx]
    show (g : MulAut (IntMod U hV)) * x * (g : MulAut (IntMod U hV))⁻¹ ∈ autI hV L
    rw [← key]
    exact convI_mem_autI hV hil (i * l * i⁻¹).2
  have hC2' : IsPGroup 2 ↥((X ⊔ S) ⊓ Subgroup.centralizer (U : Set G)) :=
    hC2.to_le (inf_le_inf_right _ hXSI)
  have hautP : autI hV P = pCoreOf 2 (oPrimeResidualOf 3 (autI hV K) ⊔ autI hV S) := by
    rw [hP, autI_pCoreOf hV hXSN hC2', autI_sup hV hXN hSN, hX, autI_oPrimeResidualOf hV hKN]
  have e3 : cm3 U A = rkIdx (fixV (autI hV A)) := (rkIdx_fixV_autI hV hAN).symm
  have e1 : cm1 P U A =
      rk ↥(autI hV A ⊓ pCoreOf 2 (oPrimeResidualOf 3 (autI hV K) ⊔ autI hV S)) := by
    have h1 := rk_autI_add hV (le_trans inf_le_left hAN : A ⊓ P ≤ Subgroup.normalizer (U : Set G))
    rw [autI_inf_eq hV hAS hPS hSCP, hautP] at h1
    unfold cm1
    omega
  obtain ⟨h3, h2⟩ := strong_offender_data hFM hW q hq hnd E hE hEq hcard hS₀ hLΩ hLn hLp hL1 hKmax
    (autI_le_normalizer hV hSK) ⟨hFF, hlt⟩
  rw [e1, e3, h3, h2]

end Core

end CFSG.Quasithin.A38c5
