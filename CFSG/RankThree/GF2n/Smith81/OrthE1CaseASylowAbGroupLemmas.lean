module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

open scoped Pointwise

theorem exists_conj_mem_of_index_odd {H : Type} [Group H] [Finite H] (P : Subgroup H)
    (hP : IsPGroup 2 P) (hodd : ¬ 2 ∣ P.index) (r : H) (hr : r ^ 2 = 1) :
    ∃ g : H, g⁻¹ * r * g ∈ P := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : IsPGroup 2 (Subgroup.zpowers r) := by
    refine IsPGroup.of_card_dvd_pow (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hr
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hZ
  haveI : Finite (Sylow 2 H) :=
    Finite.of_injective (fun T : Sylow 2 H => (T : Set H)) SetLike.coe_injective
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H Q (hP.toSylow hodd)
  have hrQ : r ∈ (Q : Subgroup H) := hQ (Subgroup.mem_zpowers r)
  have hgQ : (MulAut.conj g) r ∈ MulAut.conj g • (Q : Subgroup H) :=
    Subgroup.smul_mem_pointwise_smul r (MulAut.conj g) (Q : Subgroup H) hrQ
  have hsub : MulAut.conj g • (Q : Subgroup H) = P := by
    rw [← Sylow.coe_subgroup_smul, hg, IsPGroup.toSylow_coe]
  refine ⟨g⁻¹, ?_⟩
  rw [inv_inv, ← hsub]
  rw [MulAut.conj_apply] at hgQ
  exact hgQ

theorem relIndex_le_two_of_hom {G H : Type} [Group G] [Group H] (S R : Subgroup G)
    (ρ : ↥S →* H) (O Ω : Subgroup H) (hΩO : Ω ≤ O)
    (hρO : ∀ s : ↥S, ρ s ∈ O) (hker : ∀ s : ↥S, ρ s ∈ Ω ↔ (s : G) ∈ R)
    (hcard : Nat.card O = 2 * Nat.card Ω) [Finite O] :
    R.relIndex S ≤ 2 := by
  obtain ⟨ρ', hρ'⟩ : ∃ ρ' : ↥S →* ↥O, ∀ s : ↥S, (ρ' s : H) = ρ s :=
    ⟨ρ.codRestrict O hρO, fun _ => rfl⟩
  have hcomap : R.subgroupOf S = (Ω.subgroupOf O).comap ρ' := by
    ext s
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap, hρ']
    exact (hker s).symm
  have hpos : 0 < Nat.card O := Nat.card_pos
  have hΩpos : 0 < Nat.card Ω := by
    rw [hcard] at hpos
    omega
  have hidx : (Ω.subgroupOf O).index = 2 := by
    have h1 : Nat.card (Ω.subgroupOf O) = Nat.card Ω :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hΩO).toEquiv
    have h2 := (Ω.subgroupOf O).card_mul_index
    rw [h1, hcard] at h2
    exact Nat.eq_of_mul_eq_mul_left hΩpos (by rw [h2, mul_comm])
  have htop : (Ω.subgroupOf O).relIndex ⊤ = 2 := by
    rw [Subgroup.relIndex_top_right, hidx]
  unfold Subgroup.relIndex
  rw [hcomap, Subgroup.index_comap]
  calc (Ω.subgroupOf O).relIndex ρ'.range
      ≤ (Ω.subgroupOf O).relIndex ⊤ :=
        Subgroup.relIndex_le_of_le_right le_top (by rw [htop]; norm_num)
    _ = 2 := htop

theorem card_eq_two_pow_of_isPGroup {H : Type} [Group H] [Finite H] (P : Subgroup H)
    (hP : IsPGroup 2 P) : ∃ a : ℕ, Nat.card P = 2 ^ a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.iff_card.mp hP

theorem two_pow_eq_of_odd_mul {a e m c : ℕ} (hm : Odd m) (hc : Odd c)
    (h : 2 ^ a * c = 2 * 2 ^ e * m) : 2 ^ a = 2 ^ (e + 1) := by
  have h' : 2 ^ a * c = 2 ^ (e + 1) * m := by
    rw [h]
    ring
  have hm2 : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  have hc2 : Nat.Coprime (2 ^ (e + 1)) c :=
    Nat.Coprime.pow_left (e + 1) (Nat.coprime_two_left.mpr hc)
  have h1 : 2 ^ a ∣ 2 ^ (e + 1) :=
    Nat.Coprime.dvd_of_dvd_mul_right hm2 ⟨c, h'.symm⟩
  have h2 : 2 ^ (e + 1) ∣ 2 ^ a :=
    Nat.Coprime.dvd_of_dvd_mul_right hc2 ⟨m, h'⟩
  exact Nat.dvd_antisymm h1 h2

end CFSG.RankThree.GF2n.Smith81.Smith23E1.CaseASylowAb

end
