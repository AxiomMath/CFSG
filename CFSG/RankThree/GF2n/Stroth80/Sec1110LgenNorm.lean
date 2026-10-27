module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110LgenCoord
import CFSG.RankThree.GF2n.Stroth80.Sec12NatDualField

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.SpecialLinear
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal] {n : ℕ}

private theorem act_mem_img {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {φH0 : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)}
    (hφπ : ∀ (m : H0 M Z) (x : G), x ∈ Q → M₀.π ((m : G) * x * (m : G)⁻¹) = φH0 m (M₀.π x))
    {V : Subgroup G} (hVQ : V ≤ Q) {u : H0 M Z} (hu : conjSubgroup (u : G) V = V) {e : M₀.E}
    (he : e ∈ M₀.img V) : φH0 u e ∈ M₀.img V := by
  obtain ⟨v, hvV, hvQ, rfl⟩ := he
  rw [← hφπ u v hvQ]
  have h : (u : G) * v * (u : G)⁻¹ ∈ conjSubgroup (u : G) V :=
    mem_conjSubgroup.mpr (by simpa [mul_assoc] using hvV)
  rw [hu] at h
  exact M₀.pi_mem_img h (hVQ h)

private theorem act_act_eq {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
    {φH0 : ↥(H0 M Z) →* (M₀.E ≃ₗ[K] M₀.E)} (hc : Ctx M Q Z B)
    (hφker : ∀ m : H0 M Z, φH0 m = 1 ↔ (m : G) ∈ Q) {u : G} (hu : u ∈ LB M Q B) (e : M₀.E) :
    φH0 ⟨u, hc.LB_le_H0 hu⟩ (φH0 ⟨u, hc.LB_le_H0 hu⟩ e) = e := by
  have h1 : φH0 (⟨u, hc.LB_le_H0 hu⟩ * ⟨u, hc.LB_le_H0 hu⟩) = 1 :=
    (hφker _).mpr (by simpa [pow_two] using hc.sq_mem_Q_of_mem_LB hu)
  rw [map_mul] at h1
  calc φH0 ⟨u, hc.LB_le_H0 hu⟩ (φH0 ⟨u, hc.LB_le_H0 hu⟩ e) =
      (φH0 ⟨u, hc.LB_le_H0 hu⟩ * φH0 ⟨u, hc.LB_le_H0 hu⟩) e := rfl
    _ = e := by rw [h1]; rfl

theorem XbarCore.mem_XbarPre_of_conj_eq (hc : Ctx M Q Z B) (hn : 3 ≤ n)
    (S : XbarCore M Q Z B n) {y : G} (hy : y ∈ LB M Q B)
    (h₁ : conjSubgroup y S.V₁ = S.V₁) (h₂ : conjSubgroup y S.V₂ = S.V₂) :
    y ∈ XbarPre M Q Z B := by
  obtain ⟨K, _, _, _, γ, M₀, hD, φH0, hφπ, hφker, hφQf, C, hW₁, hW₂⟩ := S.exists_coord hc hn
  have hP : C.Preserves (φH0 ⟨y, hc.LB_le_H0 hy⟩) := by
    refine ⟨fun x => (hW₁ _).mp ?_, fun x => (hW₂ _).mp ?_⟩
    · exact act_mem_img hφπ S.le_Q₁ h₁ ((hW₁ _).mpr (C.inl_mem_W₁ x))
    · exact act_mem_img hφπ S.le_Q₂ h₂ ((hW₂ _).mpr (C.inr_mem_W₂ x))
  obtain ⟨r, k, hZpow, -⟩ := hc.hyp.cp
  letI : Fintype S.F := Fintype.ofFinite S.F
  haveI : CharP S.F 2 := by
    apply charP_of_card_eq_prime_pow (p := 2) (f := r)
    rw [Fintype.card_eq_nat_card, S.card, hZpow]
  have hK : ∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1 :=
    exists_ne_zero_sq_ne_one_of_two_lt_card K (by rw [hD.card]; have := hc.hyp.q4; omega)
  let QD : QuadDatum K M₀.E := ⟨M₀.Qf, M₀.B, M₀.Qf_smul, M₀.Qf_add, M₀.alt, M₀.nondeg⟩
  obtain ⟨g, hg⟩ := C.exists_eq_of_preserves QD hn S.range_eq (fun g e => hφQf _ e) hK
    (φH0 ⟨y, hc.LB_le_H0 hy⟩) (fun e => act_act_eq hc hφker hy e)
    (fun e => hφQf _ e) hP
  have hg' : φH0 ⟨(g : G), XbarPre_le_H0 hc g.2⟩ = φH0 ⟨y, hc.LB_le_H0 hy⟩ := hg
  have hgy : (g : G)⁻¹ * y ∈ Q := by
    have h3 : φH0 (⟨(g : G), XbarPre_le_H0 hc g.2⟩⁻¹ * ⟨y, hc.LB_le_H0 hy⟩) = 1 := by
      rw [map_mul, map_inv, hg', inv_mul_cancel]
    exact (hφker _).mp h3
  have h4 := (XbarPre M Q Z B).mul_mem g.2 (Q_le_XbarPre hc hgy)
  rwa [mul_inv_cancel_left] at h4

end CFSG.RankThree.GF2n.Stroth80
