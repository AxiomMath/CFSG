module

public import CFSG.RankThree.SubgroupLists.LinearThreeFamily
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Sporadic.McL.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec15

namespace KL3Sub3Proof

open Matrix CFSG.ComponentClassification
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

theorem card_mulAut_dvd (T : Type*) [Group T] :
    Nat.card (MulAut T) ∣ Nat.card T * Nat.card (Outer T) := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (inner T), mul_comm]
  exact Nat.mul_dvd_mul_right (Subgroup.card_range_dvd (MulAut.conj : T →* MulAut T)) _

section Conj

variable {Γ : Type*} [Group Γ]

@[expose] def conjOn (G H : Subgroup Γ) (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) :
    G →* MulAut H where
  toFun g :=
    { toFun := fun x => ⟨(g : Γ) * x * (g : Γ)⁻¹, hnorm g g.2 x x.2⟩
      invFun := fun x => ⟨(g : Γ)⁻¹ * x * (g : Γ), by
        simpa using hnorm (g : Γ)⁻¹ (G.inv_mem g.2) x x.2⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun x y => Subtype.ext (by simp [mul_assoc]) }
  map_one' := MulEquiv.ext fun x => Subtype.ext (by simp)
  map_mul' := fun a b => MulEquiv.ext fun x => Subtype.ext (by simp [mul_assoc])

theorem conjOn_apply (G H : Subgroup Γ) (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) (g : G)
    (x : H) : ((conjOn G H hnorm g x : H) : Γ) = (g : Γ) * x * (g : Γ)⁻¹ :=
  rfl

end Conj

variable {K : Type} [Field K] [Finite K]

theorem dvd_card_mulAut (G H : Subgroup (GL (Fin 3) K))
    (hnorm : ∀ g ∈ G, ∀ x ∈ H, g * x * g⁻¹ ∈ H) (hperf : Group.IsPerfect H)
    (hscal : ∀ M : Matrix (Fin 3) (Fin 3) K,
      (∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K) * M = M * x) →
        ∃ c : K, M = Matrix.scalar (Fin 3) c)
    (hGdet : ∀ g ∈ G, (g : Matrix (Fin 3) (Fin 3) K).det = 1) (hcard : 20160 ∣ Nat.card G) :
    6720 ∣ Nat.card (MulAut (H ⧸ Subgroup.center H)) := by
  classical
  set φ : G →* MulAut (H ⧸ Subgroup.center H) :=
    (PerfectAutomorphisms.centerQuotientHom H).comp (conjOn G H hnorm) with hφ
  set W : Subgroup (GL (Fin 3) K) :=
    (Subgroup.center (SpecialLinearGroup (Fin 3) K)).map SpecialLinearGroup.toGL with hW
  have hker : φ.ker.map G.subtype ≤ W := by
    rintro _ ⟨k, hk, rfl⟩
    have h1 : conjOn G H hnorm k = 1 := by
      apply PerfectAutomorphisms.centerQuotientHom_injective H
      rw [map_one]
      exact hk
    have hcomm : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K) * ((k : GL (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ((k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * x := by
      intro x hx
      have h2 := congrArg (fun a : MulAut H => ((a ⟨x, hx⟩ : H) : GL (Fin 3) K)) h1
      simp only [conjOn_apply, MulAut.one_apply] at h2
      rw [← Units.val_mul, ← Units.val_mul]
      congr 1
      calc x * (k : GL (Fin 3) K) = (k : GL (Fin 3) K) * x * (k : GL (Fin 3) K)⁻¹ * k := by
            rw [h2]
        _ = k * x := by group
    obtain ⟨c, hc⟩ := hscal _ hcomm
    have hdet := hGdet k k.2
    obtain ⟨A, hA⟩ : ∃ A : Matrix.SpecialLinearGroup (Fin 3) K,
        (A : Matrix (Fin 3) (Fin 3) K) = ((k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) :=
      ⟨⟨_, hdet⟩, rfl⟩
    have hmem : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
      rw [Matrix.SpecialLinearGroup.mem_center_iff, Fintype.card_fin]
      refine ⟨c, ?_, by rw [hA, hc]⟩
      rw [hc, scalar_apply, det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] at hdet
      exact hdet
    exact ⟨A, hmem, Units.ext hA⟩
  have hkdvd : Nat.card φ.ker ∣ 3 := by
    have h1 : Nat.card (φ.ker.map G.subtype) = Nat.card φ.ker :=
      Subgroup.card_map_of_injective G.subtype_injective
    have h2 : Nat.card W = Nat.card (Subgroup.center (SpecialLinearGroup (Fin 3) K)) :=
      Subgroup.card_map_of_injective SpecialLinearGroup.toGL_injective
    rw [← h1]
    refine (Subgroup.card_dvd_of_le hker).trans ?_
    rw [h2, CFSG.RankThree.SubgroupLists.card_center_sl3]
    exact Nat.gcd_dvd_right _ _
  have hGk : Nat.card G = Nat.card φ.ker * Nat.card φ.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hrange : 6720 ∣ Nat.card φ.range := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hkdvd with h | h
    · rw [hGk, h, one_mul] at hcard
      exact (by norm_num : 6720 ∣ 20160).trans hcard
    · rw [hGk, h, show (20160 : ℕ) = 3 * 6720 by norm_num] at hcard
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hcard
  exact hrange.trans (Subgroup.card_subgroup_dvd_card _)

omit [Finite K] in
theorem card_quotient_center_dvd {H : Subgroup (GL (Fin 3) K)}
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) K).det = 1) :
    Nat.card (H ⧸ Subgroup.center H) ∣ Nat.card (SpecialLinearGroup (Fin 3) K) := by
  have hle : H ≤ (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin 3) K →* GL (Fin 3) K).range :=
    fun x hx => (CFSG.RankThree.SubgroupLists.mem_range_toGL_iff x).mpr (hdet x hx)
  have hT : Nat.card (SpecialLinearGroup.toGL :
      SpecialLinearGroup (Fin 3) K →* GL (Fin 3) K).range =
        Nat.card (SpecialLinearGroup (Fin 3) K) :=
    (Nat.card_congr (MonoidHom.ofInjective SpecialLinearGroup.toGL_injective).toEquiv).symm
  exact (Subgroup.card_quotient_dvd_card _).trans (hT ▸ Subgroup.card_dvd_of_le hle)

theorem card_galois : Nat.card (GaloisField 5 2) = 25 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  rw [GaloisField.card 5 2 (by norm_num)]
  norm_num

theorem card_SL_galois :
    Nat.card (SpecialLinearGroup (Fin 3) (GaloisField 5 2)) = 152334000000 := by
  rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), card_galois]
  decide

end KL3Sub3Proof

end CFSG.RankThree.PartTwo.Sec15
