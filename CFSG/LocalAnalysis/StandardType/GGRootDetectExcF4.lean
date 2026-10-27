module

public import CFSG.LocalAnalysis.StandardType.GGRootDetectExcCore
public import CFSG.LieType.Ree.LargeReeExceptionalFullCentralizer
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Universal CFSG.Assembly.LowTwoRank CFSG.LieType.Ree

namespace RootDetectExc

theorem frobeniusEquiv_pow_apply {K : Type} [Field K] [Finite K] [CharP K 2] (n : ℕ) (c : K) :
    (frobeniusEquiv K 2 ^ n) c = c ^ 2 ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, pow_one]; rfl
  | succ n ih =>
    rw [pow_succ', RingAut.mul_apply, ih, frobeniusEquiv_def, ← pow_mul, ← pow_succ]

theorem frobeniusEquiv_pow_card {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (hK : Nat.card K = 2 ^ f) : frobeniusEquiv K 2 ^ f = 1 := by
  have : Fintype K := Fintype.ofFinite K
  refine RingEquiv.ext fun c => ?_
  rw [frobeniusEquiv_pow_apply, ← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  rfl

theorem adjFieldForm_F4
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    {p : ℕ} (hp : Odd p) : AdjFieldForm .F4 K p := by
  have : CharP K ReeTag.F4.prime := ‹CharP K 2›
  obtain ⟨-, hex, ⟨Θ, hΘ, -, -⟩, -⟩ := even_F4_exact_automorphism_normal_form hf K hK
  show AdjFieldForm ReeTag.F4.tag K p
  intro β hβ
  obtain ⟨⟨g, k⟩, hgk, -⟩ := hex β
  simp only at hgk
  have h1 : Θ β = Multiplicative.ofAdd (((k : ℕ) : ZMod (2 * f))) := hΘ β g k hgk
  have h2 : ((p * (k : ℕ) : ℕ) : ZMod (2 * f)) = 0 := by
    have h := congrArg Θ hβ
    rw [map_pow, h1, map_one, ← ofAdd_nsmul, ofAdd_eq_one, nsmul_eq_mul] at h
    exact_mod_cast h
  have h3 : 2 * f ∣ p * (k : ℕ) := (ZMod.natCast_eq_zero_iff _ _).mp h2
  have h2p : ¬ 2 ∣ p := by
    rintro ⟨m, rfl⟩
    exact (Nat.not_even_iff_odd.mpr hp) ⟨m, by ring⟩
  obtain ⟨j, hj⟩ : 2 ∣ (k : ℕ) :=
    ((Nat.Prime.dvd_mul Nat.prime_two).mp ((dvd_mul_right 2 f).trans h3)).resolve_left h2p
  have hfj : f ∣ p * j := by
    rw [hj, show p * (2 * j) = 2 * (p * j) by ring] at h3
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h3
  refine ⟨g, frobeniusEquiv K 2 ^ j, ?_, fun h => ?_⟩
  · obtain ⟨m, hm⟩ := hfj
    rw [← pow_mul, mul_comm, hm, pow_mul, frobeniusEquiv_pow_card hK, one_pow]
  · have e := DFunLike.congr_fun hgk h
    rw [MulAut.mul_apply, MulAut.conj_apply, hj, finiteExceptionalAut_pow_two_mul ReeTag.F4 j] at e
    rw [e, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      ReeTag.coe_finiteFrobeniusAut_pow (fun c => frobeniusEquiv_def K 2 c) j h]

end RootDetectExc

section Family

theorem ggRootDetect_F4 : GGRootDetect .F4 := by
  intro G _ _ n f ψ hadm _ hker p hp hp2 _ c hc hcp γ hγ u hT
  obtain ⟨-, hf, -⟩ := hadm
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  change γ ∈ (f4Datum (GaloisField 2 f)).roots at hγ
  have hγ' : IsRoot .F4 γ := mem_adjDatum_roots.mp hγ
  exact RootDetectExc.ggPsiInnerDiag_of_isogeny (rootOperatorFamily .F4)
    (f4Datum (GaloisField 2 f)) (isPerfect_f4 (GaloisField 2 f)).commutator_eq_top
    center_adjointGroup_eq_bot (π := MonoidHom.id _) (fun x => ⟨x, rfl⟩)
    (by rw [MonoidHom.ker_id]; exact bot_le) (hp.odd_of_ne_two hp2)
    (RootDetectExc.adjFieldForm_F4 hf _ hK (hp.odd_of_ne_two hp2)) hker hc hcp
    (α := ⟨γ, hγ'⟩)
    (fun t => ⟨xPar (rootOperatorFamily .F4) γ t, xPar_mem hγ' t, xPar_of_isRoot hγ' t⟩) hT

end Family

end CFSG.StandardType
