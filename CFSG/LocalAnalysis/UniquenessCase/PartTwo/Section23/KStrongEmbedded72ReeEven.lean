module

public import CFSG.Quasithin.Recognition.St84.L2Group
public import CFSG.Quasithin.EmptyFaithful.SzN28PRank
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7S25FW2
public import CFSG.Walter.Cited.CentralSplit
public import CFSG.Quasithin.Background.F6ResL28
public import CFSG.GroupTheory.QuasiDihedralFusion.Transport

public section

open scoped MatrixGroups

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

theorem reeEven_case {X : Type} [Group X] [Finite X] {L K : Subgroup X}
    (hKL : K ≤ L) (hKn : K.Normal) [hKs : IsSimpleGroup ↥K]
    (hKnab : ∃ a b : ↥K, a * b ≠ b * a)
    (hKC : Subgroup.centralizer (K : Set X) = ⊥)
    (hLab : ∀ S : Sylow 2 ↥L, IsMulCommutative (S : Subgroup ↥L))
    (hL8 : ∀ S : Sylow 2 ↥L, Nat.card (S : Subgroup ↥L) = 8)
    {f : ℕ} (hf : 2 ≤ f) (e : ↥K ≃* PSL(2, GaloisField 2 f)) :
    Nonempty (↥K ≃* CFSG.Quasithin.F6.L28Res.G8) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : K.Normal := hKn
  have hfpos : 1 ≤ f := by omega
  let SK : Sylow 2 ↥K := Sylow.nonempty.some
  have hSKcard : Nat.card (SK : Subgroup ↥K) = 2 ^ f := by
    have h := CFSG.Quasithin.St84.psl2_sylow_two_card (f := f) hfpos
      (SK.mapSurjective (f := e.toMonoidHom) e.surjective)
    have hcoe := Sylow.coe_mapSurjective (p := 2) (P := SK) (f := e.toMonoidHom)
      (hf := e.surjective)
    rw [hcoe, Subgroup.card_map_of_injective (K := (SK : Subgroup ↥K)) e.injective] at h
    exact h
  let SKL : Subgroup ↥L := (SK : Subgroup ↥K).map (Subgroup.inclusion hKL)
  have hSKLcard : Nat.card SKL = 2 ^ f := by
    rw [Subgroup.card_map_of_injective (K := (SK : Subgroup ↥K))
      (Subgroup.inclusion_injective hKL), hSKcard]
  have hSKLpg : IsPGroup 2 SKL := SK.isPGroup'.map (Subgroup.inclusion hKL)
  obtain ⟨SL, hSKLle⟩ := hSKLpg.exists_le_sylow
  have hSL8 : Nat.card (SL : Subgroup ↥L) = 8 := hL8 SL
  have hpow8 : 2 ^ f ≤ 8 := by
    calc 2 ^ f = Nat.card SKL := hSKLcard.symm
      _ ≤ Nat.card (SL : Subgroup ↥L) := Subgroup.card_le_of_le hSKLle
      _ = 8 := hSL8
  have hf3 : f ≤ 3 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp (by simpa using hpow8)
  rcases (by omega : f = 2 ∨ f = 3) with hf2 | hf3'
  ·
    subst hf2
    have hKcard : Nat.card ↥K = 60 := by
      rw [Nat.card_congr e.toEquiv]
      exact CFSG.Walter.Suzuki.card_psl24
    obtain ⟨eA⟩ :=
      CFSG.ClassicalInvolution.Hat2A7.nonempty_mulEquiv_alternatingGroup_five_of_simple hKcard
    let cK : ↥L →* MulAut ↥K :=
      (MulAut.conjNormal (H := K) : X →* MulAut ↥K).comp L.subtype
    have hcK : Function.Injective cK := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hfix : ∀ k : ↥K, (x : X) * (k : X) * (x : X)⁻¹ = (k : X) := by
        intro k
        have h := congrArg (fun g : MulAut ↥K => g k) hx
        change MulAut.conjNormal (H := K) (x : X) k = (1 : MulAut ↥K) k at h
        have h' := congrArg (fun y : ↥K => (y : X)) h
        simpa using h'
      have hmem : (x : X) ∈ Subgroup.centralizer (K : Set X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have h1 : (x : X) * k * (x : X)⁻¹ = k := hfix ⟨k, hk⟩
        calc k * (x : X) = ((x : X) * k * (x : X)⁻¹) * (x : X) := by rw [h1]
          _ = (x : X) * k := by group
      rw [hKC, Subgroup.mem_bot] at hmem
      exact Subtype.ext hmem
    let eAutK : MulAut ↥K ≃* MulAut ↥(alternatingGroup (Fin 5)) := MulAut.congr eA
    let eAutA : MulAut ↥(alternatingGroup (Fin 5)) ≃* Equiv.Perm (Fin 5) :=
      (MulEquiv.ofBijective (MulAut.conjNormal (H := alternatingGroup (Fin 5)))
        (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 5
          (by norm_num) (by norm_num))).symm
    let φ : ↥L →* Equiv.Perm (Fin 5) := eAutA.toMonoidHom.comp (eAutK.toMonoidHom.comp cK)
    have hφ : Function.Injective φ := by
      intro x y hxy
      exact hcK (eAutK.injective (eAutA.injective hxy))
    let E : Subgroup (Equiv.Perm (Fin 5)) := (SL : Subgroup ↥L).map φ
    have hEcard : Nat.card E = 8 := by
      change Nat.card ((SL : Subgroup ↥L).map φ) = 8
      rw [Subgroup.card_map_of_injective (K := (SL : Subgroup ↥L)) hφ, hL8 SL]
    have hEpg : IsPGroup 2 E := IsPGroup.of_card (n := 3) (by rw [hEcard]; norm_num)
    have hEcomm : IsMulCommutative ↥E :=
      CFSG.QuasiDihedralFusion.isMulCommutative_of_mulEquiv
        (Subgroup.equivMapOfInjective (SL : Subgroup ↥L) φ hφ) (hLab SL)
    have hfac : (Nat.card (Equiv.Perm (Fin 5))).factorization 2 = 3 := by
      have h120 : Nat.card (Equiv.Perm (Fin 5)) = 2 ^ 3 * 15 := by
        rw [Nat.card_perm, Nat.card_fin]
        rfl
      rw [h120, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    have hlt := CFSG.Quasithin.SzN28P.card_lt_pow_of_abelian_of_nonabelian
      (p := 2) (P := CFSG.Quasithin.SzN28P.d8Sub5) (X := E)
      CFSG.Quasithin.SzN28P.d8Sub5_isPGroup
      CFSG.Quasithin.SzN28P.d8Sub5_nonabelian hEpg hEcomm
    rw [hfac, hEcard] at hlt
    norm_num at hlt
  ·
    subst hf3'
    obtain ⟨eG⟩ := CFSG.Quasithin.F6.L28Res.nonempty_equiv (GaloisField 2 3) (by
      rw [GaloisField.card 2 3 (by norm_num)]
      norm_num)
    exact ⟨e.trans ((CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2
      (GaloisField 2 3)).trans eG)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
