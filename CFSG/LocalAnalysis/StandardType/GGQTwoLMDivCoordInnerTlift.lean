module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerLift
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerTor
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary Matrix

variable {G : Type} [Group G] [Finite G]

private lemma qTwoLMDivCoordInner_tlift_eq_one_of_mem_ker_of_pow {L L0 : Type} [Group L] [Group L0]
    {c : L →* L0} (hc2 : IsPGroup 2 c.ker) {z : L} (hz : z ∈ c.ker) (hz3 : z ^ 3 = 1) :
    z = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hc2.exists_orderOf_eq_pow ⟨z, hz⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : 2 ^ k ∣ 3 := by
    rw [← hk]
    exact orderOf_dvd_iff_pow_eq_one.mpr hz3
  have hk0 : 2 ^ k = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h | h
    · exact h
    · exfalso
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · rw [hk0, pow_zero] at h
        norm_num at h
      · have h2 : 2 ∣ 2 ^ k := dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp hkpos)
        rw [h] at h2
        norm_num at h2
  have h1 : orderOf z = 1 := by rw [hk, hk0]
  exact orderOf_eq_one_iff.mp h1

theorem qTwoLMDivCoordInner_tlift {B Bs L : Subgroup G} (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m : ℕ} {F0 : Type} [Field F0] [Finite F0]
    [CharP F0 2] {L0 : Type} [Group L0] {c : ↥L →* L0} {π : Su F0 2 1 m →* L0}
    {ρ : ↥Bs →* MulAut L0} (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ) {h3 : 3 ∣ m}
    {δ : ↥(sumZero m 3) →* Su F0 2 1 m} (hδ : QTwoDivTorus h3 δ) :
    ∃ τ : ↥(sumZero m 3) →* ↥L, QTwoDivLift Bs L c π δ τ := by
  letI : CommGroup ↥(sumZero m 3) := Subgroup.toCommGroup _
  obtain ⟨s, hs, hs3⟩ := qTwoLMDivCoordInner_section c hU.c_surj hU.c_ker hU.c_two
    (fun v : ↥(sumZero m 3) => pow_p_eq_one v) (π.comp δ)
  have hs_pt : ∀ f, c (s f) = π (δ f) :=
    fun f => congrArg (fun τ : ↥(sumZero m 3) →* L0 => τ f) hs
  have hmem : ∀ f, ((s f : ↥L) : G) ∈ Bs := by
    intro f
    refine hBs.2.2.2 ((s f : ↥L) : G) ?_ ?_
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      set l : ↥L := s f with hl
      let b' : ↥Bs := ⟨b, hb⟩
      let l' : ↥L := ⟨(b' : G) * (l : G) * (b' : G)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hN b'.2) l).mp l.2⟩
      have hl_comm : c l = π (δ f) := by
        rw [hl]
        exact hs_pt f
      have hl_ind : c l' = ρ b' (c l) := hU.induced b' l
      obtain ⟨g, hgdiag, hgu⟩ := hU.diag b'
      obtain ⟨u', hu'mat, hρ⟩ := hgu (δ f)
      obtain ⟨dg, hdg⟩ := hgdiag
      obtain ⟨du, hdu⟩ := hδ.diag f
      have hgu_comm : g * (δ f : GL (Fin m) F0) = (δ f : GL (Fin m) F0) * g := by
        apply Units.ext
        simp only [Units.val_mul]
        rw [hdg, hdu, Matrix.diagonal_mul_diagonal dg du,
          Matrix.diagonal_mul_diagonal du dg]
        rw [Matrix.diagonal_eq_diagonal_iff]
        intro i
        exact mul_comm _ _
      have hgu_eq : g * (δ f : GL (Fin m) F0) * g⁻¹ = (δ f : GL (Fin m) F0) := by
        rw [hgu_comm]
        group
      have hu'u : u' = δ f := Subtype.ext (hu'mat.trans hgu_eq)
      have hcl_eq : c l' = c l := by
        rw [hl_ind, hl_comm, hρ, hu'u]
      set z : ↥L := l⁻¹ * l' with hz
      have hzk : z ∈ c.ker := by
        rw [MonoidHom.mem_ker, hz, map_mul, map_inv, hcl_eq, inv_mul_cancel]
      have hzcenter : z ∈ Subgroup.center ↥L := hU.c_ker hzk
      have hl'_eq : l' = l * z := by rw [hz, mul_inv_cancel_left]
      have hl3 : l ^ 3 = 1 := by rw [hl]; exact hs3 f
      have hl3G : (l : G) ^ 3 = 1 := by
        rw [← Subgroup.coe_pow, hl3, Subgroup.coe_one]
      have hl'3 : l' ^ 3 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        change ((b' : G) * (l : G) * (b' : G)⁻¹) ^ 3 = 1
        rw [conj_pow, hl3G]
        group
      have hz3 : z ^ 3 = 1 := by
        have hcomm_lz : Commute l z := Subgroup.mem_center_iff.mp hzcenter l
        have h1 : (l * z) ^ 3 = 1 := by rw [← hl'_eq]; exact hl'3
        rw [hcomm_lz.mul_pow, hl3, one_mul] at h1
        exact h1
      have hl'eq : l' = l := by
        have hz1 : z = 1 :=
          qTwoLMDivCoordInner_tlift_eq_one_of_mem_ker_of_pow hU.c_two hzk hz3
        rw [hl'_eq, hz1, mul_one]
      have hconjG : (b' : G) * (l : G) * (b' : G)⁻¹ = (l : G) :=
        congrArg (fun x : ↥L => (x : G)) hl'eq
      change (b' : G) * (l : G) = (l : G) * (b' : G)
      calc (b' : G) * (l : G) = (b' : G) * (l : G) * (b' : G)⁻¹ * (b' : G) := by group
        _ = (l : G) * (b' : G) := by rw [hconjG]
    · rw [← Subgroup.coe_pow, hs3 f, Subgroup.coe_one]
  exact ⟨s, ⟨hs_pt, hmem, hs3⟩⟩

end CFSG.StandardType.QTwo

end
