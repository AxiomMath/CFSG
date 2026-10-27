module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.S126P31

section PerfectCentral

variable {K : Type} [Group K]

@[expose] noncomputable def descendCentral : MulAut K →* MulAut (K ⧸ Subgroup.center K) where
  toFun α := QuotientGroup.congr (Subgroup.center K) (Subgroup.center K) α
    (Subgroup.map_center_eq α)
  map_one' := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rfl
  map_mul' α β := by
    ext x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    rfl

theorem descendCentral_mk (α : MulAut K) (x : K) :
    descendCentral α (QuotientGroup.mk x) = QuotientGroup.mk (α x) := rfl

theorem descendCentral_injective (hperf : commutator K = ⊤) :
    Function.Injective (descendCentral (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro α hα
  have hcen : ∀ x : K, x⁻¹ * α x ∈ Subgroup.center K := by
    intro x
    have h1 : descendCentral α (QuotientGroup.mk x) = QuotientGroup.mk x := by rw [hα]; rfl
    rw [descendCentral_mk] at h1
    exact QuotientGroup.eq.1 h1.symm
  let φ : K →* K :=
    { toFun := fun x => x⁻¹ * α x
      map_one' := by simp
      map_mul' := fun x y => by
        have hx : y⁻¹ * (x⁻¹ * α x) = (x⁻¹ * α x) * y⁻¹ :=
          Subgroup.mem_center_iff.1 (hcen x) y⁻¹
        rw [map_mul, mul_inv_rev]
        calc y⁻¹ * x⁻¹ * (α x * α y) = (y⁻¹ * (x⁻¹ * α x)) * α y := by group
          _ = ((x⁻¹ * α x) * y⁻¹) * α y := by rw [hx]
          _ = (x⁻¹ * α x) * (y⁻¹ * α y) := by group }
  have hker : commutator K ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.1 (hcen a) (φ b)).symm
  rw [hperf, top_le_iff] at hker
  refine MulEquiv.ext fun x => ?_
  have hx : x ∈ φ.ker := by rw [hker]; exact Subgroup.mem_top x
  rw [MonoidHom.mem_ker] at hx
  have h1 : x⁻¹ * α x = 1 := hx
  rw [MulAut.one_apply]
  exact (inv_mul_eq_one.1 h1).symm

theorem descendCentral_conj (y : K) :
    descendCentral (MulAut.conj y) =
      MulAut.conj (QuotientGroup.mk y : K ⧸ Subgroup.center K) := by
  ext z
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
  simp [descendCentral_mk, MulAut.conj_apply]

theorem card_mulAut_dvd_of_perfect_central (hperf : commutator K = ⊤) :
    Nat.card (MulAut K) ∣ Nat.card (MulAut (K ⧸ Subgroup.center K)) := by
  have hinj := descendCentral_injective hperf
  rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

theorem out_exp_of_perfect_central (hperf : commutator K = ⊤)
    (h : ∀ β : MulAut (K ⧸ Subgroup.center K),
      β ^ 4 ∈ (MulAut.conj : (K ⧸ Subgroup.center K) →* MulAut (K ⧸ Subgroup.center K)).range →
      β ^ 2 ∈ (MulAut.conj : (K ⧸ Subgroup.center K) →* MulAut (K ⧸ Subgroup.center K)).range) :
    ∀ α : MulAut K, α ^ 4 ∈ (MulAut.conj : K →* MulAut K).range →
      α ^ 2 ∈ (MulAut.conj : K →* MulAut K).range := by
  intro α hα
  obtain ⟨x, hx⟩ := hα
  have h4 : descendCentral α ^ 4 ∈
      (MulAut.conj : (K ⧸ Subgroup.center K) →* MulAut (K ⧸ Subgroup.center K)).range :=
    ⟨QuotientGroup.mk x, by rw [← map_pow, ← hx, descendCentral_conj]⟩
  obtain ⟨z, hz⟩ := h _ h4
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
  refine ⟨y, ?_⟩
  apply descendCentral_injective hperf
  rw [descendCentral_conj, map_pow]
  exact hz

end PerfectCentral

end CFSG.Quasithin.H13.S126P31
