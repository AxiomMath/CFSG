module

public import CFSG.RankThree.GF2n.Stroth80.Sec712OddCommute
public import CFSG.RankThree.GF2n.Stroth80.Sec12Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem mem_Q_of_comm_LB_of_odd (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) {x : G} (hxH : x ∈ H0 M Z) {m : ℕ} (hm : Odd m) (hxm : x ^ m ∈ Q)
    (hcomm : ∀ l ∈ LB M Q B, ⁅x, l⁆ ∈ Q) : x ∈ Q := by
  classical
  obtain ⟨K, fK, finK, chK, γ, M₀, h⟩ := stroth_globalModelData hc.hyp
  obtain ⟨φ, hφπ, hφker, hφQ⟩ := exists_actionHom_H0 hc.hyp h
  haveI : Finite M₀.E := Module.finite_of_finite K
  let Λ : Subgroup (M₀.E ≃ₗ[K] M₀.E) := (φ.comp (Subgroup.inclusion hc.LB_le_H0')).range
  have hΛp : IsPGroup 2 Λ := hc.isPGroup_range_LB φ hφker
  have h35 := (stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen).2.1
  obtain ⟨b, hb0, -, hB, -, -⟩ := hc.dictB h
  obtain ⟨u₀, hu₀B, hu₀Q, hbu₀⟩ := (M₀.mem_img).1 ((hB b).mpr ⟨1, (one_smul _ _).symm⟩)
  have hu₀C : u₀ ∈ CQt Q Z (LB M Q B) := by
    rw [h35]
    exact Subgroup.mem_sup_left hu₀B
  have hbfix : ∀ g ∈ Λ, g b = b := by
    rintro _ ⟨l, rfl⟩
    have hlM : (l : G) ∈ M := hc.LB_le_M l.2
    have hlQ : (l : G) * u₀ * (l : G)⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hlM) u₀).mp hu₀Q
    have h1 := (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hu₀Q hlQ).mp (hu₀C.2 l l.2)
    show φ (Subgroup.inclusion hc.LB_le_H0' l) b = b
    rw [← hbu₀, ← hφπ _ u₀ hu₀Q]
    exact h1
  have hle' : B ⊔ Z ≤ M₀.lift (M₀.img B) := sup_le
    (fun u hu => ⟨hc.le hu, M₀.pi_mem_img hu (hc.le hu)⟩)
    (fun z hz => ⟨hc.Z_le_Q hz, by
      rw [(M₀.π_ker z (hc.Z_le_Q hz)).mpr hz]
      exact AddSubgroup.zero_mem _⟩)
  have hfixed : ∀ e : M₀.E, (∀ g ∈ Λ, g e = e) → ∃ c : K, e = c • b := by
    intro e he
    obtain ⟨a, haQ, rfl⟩ := M₀.π_surj e
    have haC : a ∈ CQt Q Z (LB M Q B) := by
      refine ⟨haQ, fun l hl => ?_⟩
      have hmem : φ (Subgroup.inclusion hc.LB_le_H0' ⟨l, hl⟩) ∈ Λ := ⟨⟨l, hl⟩, rfl⟩
      have h1 := he _ hmem
      rw [← hφπ _ a haQ] at h1
      exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) haQ
        ((Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.LB_le_M hl)) a).mp haQ)).mpr h1
    rw [h35] at haC
    obtain ⟨s, hs⟩ := (hB _).mp (hle' haC).2
    exact ⟨s, hs⟩
  have hcommΛ : ∀ g ∈ Λ, g * φ ⟨x, hxH⟩ = φ ⟨x, hxH⟩ * g := by
    rintro _ ⟨l, rfl⟩
    have h1 : ⁅φ (Subgroup.inclusion hc.LB_le_H0' l), φ ⟨x, hxH⟩⁆ = 1 := by
      rw [← map_commutatorElement]
      refine (hφker _).mpr ?_
      show ⁅(l : G), x⁆ ∈ Q
      rw [← commutatorElement_inv]
      exact Q.inv_mem (hcomm l l.2)
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hTm : φ ⟨x, hxH⟩ ^ m = 1 := by
    rw [← map_pow]
    exact (hφker _).mpr (by simpa using hxm)
  have hQ0 : ∃ e, M₀.Qf e ≠ 0 := by
    by_contra hall
    push Not at hall
    apply hb0
    refine M₀.nondeg b fun f => ?_
    have h1 := M₀.Qf_add b f
    rw [hall, hall, hall] at h1
    simpa using h1.symm
  have hT1 := eqOneOfCommutesOdd_holds K M₀.E Λ hΛp b hb0 hbfix hfixed M₀.Qf M₀.Qf_smul hQ0
    (φ ⟨x, hxH⟩) hcommΛ (hφQ ⟨x, hxH⟩) m hm hTm
  exact (hφker ⟨x, hxH⟩).mp hT1
end CFSG.RankThree.GF2n.Stroth80
