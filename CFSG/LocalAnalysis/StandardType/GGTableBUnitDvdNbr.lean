module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitDvdCent
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUCoverTwo
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNineSCr
public import CFSG.RankThree.PartOne.KF.UnitaryDiag

public section

namespace CFSG.StandardType.UnitTB

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU CFSG.Assembly TableB

variable {K : Type} [Field K] {n d p : ℕ} {L' : Type} [Group L']
  {φ : ↥(unitarySU 2 n K d) →* L'}

theorem nbr_of_model [Finite K] [Finite L'] (hM : Model φ) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ n + 1) (hd : 5 ≤ d)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (hA1 : Nat.card A ≠ 1)
    (hsc : GGTorusSelfCent p A) (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t) :
    ∃ W : Set L',
      (∀ w ∈ W, ∀ a ∈ A, (w * (a w)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (w * (a w)⁻¹) = w * (a w)⁻¹) ∧
      ∀ Y : Subgroup (MulAut L'),
        (∀ w ∈ W, ∀ a ∈ A, MulAut.conj w * a * (MulAut.conj w)⁻¹ ∈ A) →
        (∀ w ∈ W, ∀ f ∈ Y, MulAut.conj w * f * (MulAut.conj w)⁻¹ ∈ Y) →
        (∀ f ∈ Y, ∀ a ∈ A, f * a * f⁻¹ ∈ A) →
        (∀ f ∈ Y, ∃ k : ℕ, ∀ a ∈ A, f ^ p ^ k * a = a * f ^ p ^ k) →
        ∀ f ∈ Y, ∀ a ∈ A, f * a = a * f := by
  classical
  have := Fact.mk hp
  obtain ⟨ζ, hζ⟩ := CFSG.RankThree.PartOne.KFU.exists_isPrimitiveRoot hM.field hp hpq
  have hζinv : ζ ≠ ζ⁻¹ := TypeA.ne_inv_of_isPrimitiveRoot hζ hp hp2
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hd3 : 3 ≤ d := by omega
  have hAp : ∀ a ∈ A, a ^ p = 1 := hA.2
  have hpv : ∀ k l m : Fin d, TypeA.ggPairVec k l ζ m ^ p = 1 := fun k l m =>
    TypeA.pow_ggPairVec hζ.pow_eq_one m
  have hDex : ∀ k l : Fin d, k ≠ l → ∃ D : ↥(unitarySU 2 n K d),
      ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal (TypeA.ggPairVec k l ζ) :=
    fun k l _ => exists_diagSU hM.field hpq (fun m => hpv k l m) (TypeA.prod_ggPairVec ζ hζ0)
  refine ⟨{x | ∃ σ : Equiv.Perm (Fin d), x = φ (permSU hM.field σ)},
    weyl_W_prop hM.field hd3 hM.ker hAp hdiag, ?_⟩
  intro Y hWA hWY hYA hYp
  set A' : Subgroup (MulAut L') := A ⊓ Subgroup.centralizer (Y : Set (MulAut L')) with hA'
  have hA'inv : ∀ σ : Equiv.Perm (Fin d), ∀ a ∈ A',
      MulAut.conj (φ (permSU hM.field σ)) * a * (MulAut.conj (φ (permSU hM.field σ)))⁻¹ ∈ A' := by
    intro σ a ha
    have hw : φ (permSU hM.field σ) ∈ {x | ∃ σ : Equiv.Perm (Fin d), x = φ (permSU hM.field σ)} :=
      ⟨σ, rfl⟩
    refine ⟨hWA _ hw a ha.1, Subgroup.mem_centralizer_iff.mpr fun f hf => ?_⟩
    have hχ := inv_conj_mem_of_conj_mem (hWY _ hw) hf
    have hcf := Subgroup.mem_centralizer_iff.mp ha.2 _ hχ
    set c := MulAut.conj (φ (permSU hM.field σ))
    calc f * (c * a * c⁻¹) = c * ((c⁻¹ * f * c) * a) * c⁻¹ := by group
      _ = c * (a * (c⁻¹ * f * c)) * c⁻¹ := by rw [hcf]
      _ = c * a * c⁻¹ * f := by group
  obtain ⟨a₀, ha₀, ha₀1, ha₀c⟩ :=
    exists_ne_one_forall_comm_of_pGroup (isPGroup_of_isElemAbelian hA) hA1 hYA hYp
  have ha₀A' : a₀ ∈ A' := ⟨ha₀, Subgroup.mem_centralizer_iff.mpr fun f hf => ha₀c f hf⟩
  have hV : ∀ (D : ↥(unitarySU 2 n K d)) (u : Fin d → K),
      ((D : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = diagonal u → (∀ i, u i ^ p = 1) →
      MulAut.conj (φ D) ∈ A' := fun D u hD hu =>
    conj_mem_of_invariant hM hp hpq hd inf_le_left hsc hdiag hAp hA'inv ha₀A' ha₀1 hD hu
  have hinner : ∀ s : ↥(unitarySU 2 n K d), MulAut.conj (φ s) ∈ Y →
      ∀ a ∈ A, MulAut.conj (φ s) * a = a * MulAut.conj (φ s) := by
    intro s hs a ha
    have hsd : ((s : GL (Fin d) K) : Matrix (Fin d) (Fin d) K).IsDiag := by
      refine isDiag_of_conj_comm hM hK (by omega) hζinv hDex fun k l _ D hD => ?_
      exact Subgroup.mem_centralizer_iff.mp (hV D _ hD (fun i => hpv k l i)).2 _ hs
    obtain ⟨t, hat⟩ := hdiag a ha
    exact (actsDiagU_mul_conj_comm hat ((isDiag_iff_diagonal_diag _).mp hsd).symm).symm
  have hstep : ∀ f ∈ Y, ∀ σ : Equiv.Perm (Fin d), ∀ a ∈ A,
      f * (MulAut.conj (φ (permSU hM.field σ)) * a * (MulAut.conj (φ (permSU hM.field σ)))⁻¹) *
          f⁻¹ =
        MulAut.conj (φ (permSU hM.field σ)) * (f * a * f⁻¹) *
          (MulAut.conj (φ (permSU hM.field σ)))⁻¹ := by
    intro f hf σ a ha
    set w := φ (permSU hM.field σ) with hw
    have hwmem : w ∈ {x | ∃ σ : Equiv.Perm (Fin d), x = φ (permSU hM.field σ)} := ⟨σ, rfl⟩
    have hzY : MulAut.conj w * f * (MulAut.conj w)⁻¹ * f⁻¹ ∈ Y :=
      Y.mul_mem (hWY w hwmem f hf) (Y.inv_mem hf)
    have hz : MulAut.conj w * f * (MulAut.conj w)⁻¹ * f⁻¹ = MulAut.conj (w * (f w)⁻¹) := by
      have hfw : MulAut.conj (f w) = f * MulAut.conj w * f⁻¹ := by
        rw [TypeANbrDvd.mul_conj_eq_conj_apply_mul, mul_inv_cancel_right]
      rw [map_mul, map_inv, hfw]
      group
    obtain ⟨s, hs⟩ := hM.surj (w * (f w)⁻¹)
    have hzc : ∀ b ∈ A, (MulAut.conj w * f * (MulAut.conj w)⁻¹ * f⁻¹) * b =
        b * (MulAut.conj w * f * (MulAut.conj w)⁻¹ * f⁻¹) := by
      rw [hz, ← hs]
      exact hinner s (by rw [hs, ← hz]; exact hzY)
    have hx : f * (MulAut.conj w * a * (MulAut.conj w)⁻¹) * f⁻¹ ∈ A :=
      hYA f hf _ (hWA w hwmem a ha)
    calc f * (MulAut.conj w * a * (MulAut.conj w)⁻¹) * f⁻¹
        = (MulAut.conj w * f * (MulAut.conj w)⁻¹ * f⁻¹) *
            (f * (MulAut.conj w * a * (MulAut.conj w)⁻¹) * f⁻¹) *
            (MulAut.conj w * f * (MulAut.conj w)⁻¹ * f⁻¹)⁻¹ := by
          rw [hzc _ hx, mul_inv_cancel_right]
      _ = MulAut.conj w * (f * a * f⁻¹) * (MulAut.conj w)⁻¹ := by group
  intro f hf a ha
  have hbA : f * a * f⁻¹ * a⁻¹ ∈ A := A.mul_mem (hYA f hf a ha) (A.inv_mem ha)
  obtain ⟨tb, hbt⟩ := hdiag _ hbA
  obtain ⟨t, hat⟩ := hdiag a ha
  have hfix : ∀ σ : Equiv.Perm (Fin d),
      MulAut.conj (φ (permSU hM.field σ)) * (f * a * f⁻¹ * a⁻¹) *
        (MulAut.conj (φ (permSU hM.field σ)))⁻¹ = f * a * f⁻¹ * a⁻¹ := by
    intro σ
    set w := φ (permSU hM.field σ) with hw
    have het : ActsDiagU φ (MulAut.conj w * a * (MulAut.conj w)⁻¹ * a⁻¹)
        (fun k => t (σ⁻¹ k) * (t k)⁻¹) :=
      actsDiagU_mul (hat.conj_perm hM.field σ) (actsDiagU_inv hat)
    have hprod : ∏ k, (t (σ⁻¹ k) * (t k)⁻¹) = 1 := by
      rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Equiv.prod_comp σ⁻¹ t]
      exact mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr fun k _ => hat.ne_zero k)
    have hpow : ∀ k, (t (σ⁻¹ k) * (t k)⁻¹) ^ p = 1 := fun k =>
      hat.ratio_pow hM.field hd3 hM.ker (hAp a ha) (σ⁻¹ k) k
    obtain ⟨De, hDe⟩ := exists_diagSU hM.field hpq hpow hprod
    have heq : MulAut.conj w * a * (MulAut.conj w)⁻¹ * a⁻¹ = MulAut.conj (φ De) :=
      actsDiagU_unique hM.surj het (actsDiagU_conj hDe)
    have heA' : MulAut.conj w * a * (MulAut.conj w)⁻¹ * a⁻¹ ∈ A' := by
      rw [heq]
      exact hV De _ hDe hpow
    have hφe : f * (MulAut.conj w * a * (MulAut.conj w)⁻¹ * a⁻¹) * f⁻¹ =
        MulAut.conj w * a * (MulAut.conj w)⁻¹ * a⁻¹ := by
      rw [Subgroup.mem_centralizer_iff.mp heA'.2 f hf, mul_inv_cancel_right]
    have h7 := hstep f hf σ a ha
    have hcomm := IsElemAbelian.comm hA heA'.1 hbA
    calc MulAut.conj w * (f * a * f⁻¹ * a⁻¹) * (MulAut.conj w)⁻¹
        = (MulAut.conj w * (f * a * f⁻¹) * (MulAut.conj w)⁻¹) *
            (MulAut.conj w * a * (MulAut.conj w)⁻¹)⁻¹ := by group
      _ = (f * (MulAut.conj w * a * (MulAut.conj w)⁻¹) * f⁻¹) *
            (MulAut.conj w * a * (MulAut.conj w)⁻¹)⁻¹ := by rw [h7]
      _ = (f * (MulAut.conj w * a * (MulAut.conj w)⁻¹ * a⁻¹) * f⁻¹) * (f * a * f⁻¹ * a⁻¹) *
            (MulAut.conj w * a * (MulAut.conj w)⁻¹ * a⁻¹)⁻¹ := by group
      _ = (MulAut.conj w * a * (MulAut.conj w)⁻¹ * a⁻¹) * (f * a * f⁻¹ * a⁻¹) *
            (MulAut.conj w * a * (MulAut.conj w)⁻¹ * a⁻¹)⁻¹ := by rw [hφe]
      _ = f * a * f⁻¹ * a⁻¹ := by rw [hcomm, mul_inv_cancel_right]
  have hb1 := eq_one_of_conj_perm hM hd3 hbt hfix
  calc f * a = f * a * f⁻¹ * a⁻¹ * a * f := by group
    _ = a * f := by rw [hb1, one_mul]

theorem ggTorusNbrSCr_unitary
    [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n)
    (hd : 5 ≤ d) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hpd : p ∣ d) (hnd : ¬ (d = 6 ∧ p = 3)) :
    GGTorusNbrSCr p (ggUnitaryTorusRank p d) (LargeEvenProj (LargeEvenSUGroup (Fin d) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin d) K (2 ^ n)))
        (LargeEvenGUSet (Fin d) K (2 ^ n))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  have hrank : ggUnitaryTorusRank p d = d - 3 := by simp [ggUnitaryTorusRank, hpd]
  rw [hrank] at hr
  have hcard : p ^ (d / p + 2) ≤ Nat.card A := card_ge_of_dvd hp hp2 hd hpd hnd hr h3
  have hdnd : (d, n) ≠ (6, 1) := by
    rintro ⟨rfl, rfl⟩
    have h3' : p ∣ 3 := by simpa using hpq
    exact hnd ⟨rfl, (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3'⟩
  obtain ⟨φ, hφs, hφker, hdiag⟩ := exists_diagModel hK hn hd hp hpq hpd
    (unitaryUniversalCover_holds n d K hK hd hdnd) hψ hker hperf hA hAI hcard
  haveI : Finite (MulAut L') := Finite.of_injective (fun f : MulAut L' => (f : L' → L'))
    DFunLike.coe_injective
  have hM : Model φ := ⟨TableBU.unitaryFieldData_of_card hK hn, hφs, hφker⟩
  have hA1 : Nat.card A ≠ 1 := by
    intro h1
    rw [h1] at h3
    have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  exact nbr_of_model hM hK hp hp2 hpq hd hA hA1 hsc hdiag

end CFSG.StandardType.UnitTB

end
