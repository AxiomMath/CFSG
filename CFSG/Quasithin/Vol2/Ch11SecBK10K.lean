module

public import CFSG.Quasithin.Vol2.Ch11SecBK10A
public import CFSG.RankThree.PartOne.S11d.OutLinear

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

namespace BK10.L3

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartOne.OutStructure (linear_D2 mem_of_pow_mem_of_index_le_two)

variable {K : Type} [Field K]

@[expose] noncomputable def torus3 (ζ : Kˣ) : SpecialLinearGroup (Fin 3) K :=
  ⟨Matrix.diagonal ![(ζ : K), ((ζ⁻¹ : Kˣ) : K), 1], by
    simp [Matrix.det_diagonal, Fin.prod_univ_three]⟩

theorem coe_torus3 (ζ : Kˣ) :
    ((torus3 ζ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      Matrix.diagonal ![(ζ : K), ((ζ⁻¹ : Kˣ) : K), 1] := rfl

@[expose] noncomputable def torus3SL : Kˣ →* SpecialLinearGroup (Fin 3) K where
  toFun := torus3
  map_one' := by
    apply Subtype.ext
    change Matrix.diagonal ![((1 : Kˣ) : K), (((1 : Kˣ)⁻¹ : Kˣ) : K), 1] = 1
    rw [← Matrix.diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  map_mul' ζ η := by
    apply Subtype.ext
    change Matrix.diagonal ![((ζ * η : Kˣ) : K), (((ζ * η)⁻¹ : Kˣ) : K), 1] =
      Matrix.diagonal ![(ζ : K), ((ζ⁻¹ : Kˣ) : K), 1] *
        Matrix.diagonal ![(η : K), ((η⁻¹ : Kˣ) : K), 1]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    fin_cases i <;> simp [mul_comm]

@[expose] noncomputable def torus3Hom : Kˣ →* projectiveSL 3 K :=
  (proj 3 K).comp torus3SL

theorem torus3Hom_injective : Function.Injective (torus3Hom (K := K)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro ζ hζ
  rw [MonoidHom.mem_ker] at hζ
  change QuotientGroup.mk' (scalars 3 K) (torus3SL ζ) = 1 at hζ
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hζ
  obtain ⟨c, -, hc⟩ := hζ
  change ((torus3 ζ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _ at hc
  rw [coe_torus3] at hc
  have h2 := congrFun (congrFun hc 2) 2
  have h0 := congrFun (congrFun hc 0) 0
  simp at h2 h0
  rw [Subgroup.mem_bot]
  apply Units.ext
  rw [h0, ← h2, Units.val_one]

theorem orderOf_proj_torus3 (ζ : Kˣ) : orderOf (torus3Hom ζ) = orderOf ζ :=
  orderOf_injective _ torus3Hom_injective ζ

variable [Finite K]

theorem sub_one_dvd_card : Nat.card K - 1 ∣ Nat.card (projectiveSL 3 K) := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := Kˣ)
  have h1 : orderOf ζ = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hζ
  rw [← Nat.card_units, ← h1, ← orderOf_proj_torus3]
  exact orderOf_dvd_natCard _

theorem eq_one_of_isCoprimePrimeAut_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK : Nat.card K = p) {β : MulAut (projectiveSL 3 K)} (hβ : IsCoprimePrimeAut β) : β = 1 := by
  obtain ⟨r, hr, hβr, hβ1, hrX⟩ := hβ
  have hq1 := sub_one_dvd_card (K := K)
  have hr2 : r ≠ 2 := by
    rintro rfl
    apply hrX
    refine dvd_trans ?_ hq1
    rw [hK]
    obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
    rw [hm]
    exact ⟨m, by omega⟩
  obtain ⟨hgenTop, -⟩ := automorphism_generation (K := K) (le_refl 3)
  obtain ⟨-, -, -, -, -, -, -, hidx, -, -⟩ := standard_outer_quotients (n := 3) (K := K)
  have hidx' : (semilinearAutGroup 3 K).index ≤ 2 := by
    have h2 : (semilinearAutGroup 3 K).relIndex (standardAutGroup 3 K) ≤ 2 := hidx
    rwa [hgenTop, Subgroup.relIndex_top_right] at h2
  have : Finite (MulAut (projectiveSL 3 K)) := inferInstance
  have hE : β ∈ semilinearAutGroup 3 K :=
    mem_of_pow_mem_of_index_le_two _ hidx' (hr.odd_of_ne_two hr2) (by rw [hβr]; exact one_mem _)
  obtain ⟨B, τ, hBτ⟩ := mem_semilinearAutGroup_iff.mp hE
  have hτ : τ = 1 := by
    obtain ⟨hcard, -⟩ := card_ringAut_and_isCyclic hp K (n := 1) (by rw [hK, pow_one])
    have : Subsingleton (RingAut K) := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact Subsingleton.elim _ _
  rw [hτ, map_one, mul_one] at hBτ
  have hD : β ∈ linearAutGroup 3 K := hBτ ▸ conjAut_mem_linearAutGroup B
  have hdiag : ¬ r ∣ Nat.gcd 3 (Nat.card K - 1) := fun h =>
    hrX ((h.trans (Nat.gcd_dvd_right _ _)).trans hq1)
  have hin := linear_D2 hr (le_refl 3) hdiag β hD 1 (by rw [pow_one, hβr]; exact one_mem _)
  exact eq_one_of_mem_inner ⟨r, hr, hβr, hβ1, hrX⟩ hin

theorem torusRigid_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hK : Nat.card K = p) :
    TorusRigid (projectiveSL 3 K) :=
  torusRigid_of_forall_eq_one fun _ hβ => eq_one_of_isCoprimePrimeAut_prime hp hp2 hK hβ

end BK10.L3

end CFSG.Quasithin.Vol2.Ch11.SecD
