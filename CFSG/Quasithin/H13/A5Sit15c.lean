module

public import CFSG.Quasithin.H13.A5Sit15b
public import CFSG.Quasithin.H13.A5S1515c

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.A5.Orth
open CFSG.Quasithin.H13.A5 (inSA_swap sq_comm_of_normalizes le_sup_of_sq_mem
  le_normalizer_of_conj_mem)

namespace A5SitPf15

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  {S : A5Sit G T V V₁ V₃ L₁ H} {SY : A5SitY S L₁} (P : A5SitPf15 S SY)
include P

theorem inSA_mem {x : MulAut (Multiplicative V4)} (hx : InSA P.t1 P.t2 x) :
    ∃ y : ↥H, (y : G) ∈ V ⊔ conjSub P.g⁻¹ V ∧ P.Φ y = x := by
  have ha : P.v ∈ V ⊔ conjSub P.g⁻¹ V := le_sup_left (a := V) P.v_mem
  have hb : P.g⁻¹ * P.v * P.g ∈ V ⊔ conjSub P.g⁻¹ V :=
    le_sup_right (b := conjSub P.g⁻¹ V) P.v'_mem
  set a : ↥H := ⟨P.v, P.v_mem_H⟩ with hadef
  set b : ↥H := ⟨P.g⁻¹ * P.v * P.g, P.v'_mem_H⟩ with hbdef
  have hta : P.t1 = P.Φ a := rfl
  have htb : P.t2 = P.Φ b := rfl
  unfold InSA at hx
  rw [hta, htb] at hx
  rcases hx with h | h | h | h | h | h
  · exact ⟨1, Subgroup.one_mem _, by rw [h, map_one]⟩
  · exact ⟨a, ha, h.symm⟩
  · exact ⟨b, hb, h.symm⟩
  · exact ⟨a * b, Subgroup.mul_mem _ ha hb, by rw [h, map_mul]⟩
  · exact ⟨b * a, Subgroup.mul_mem _ hb ha, by rw [h, map_mul]⟩
  · exact ⟨a * (b * a), Subgroup.mul_mem _ ha (Subgroup.mul_mem _ hb ha),
      by rw [h, map_mul, map_mul]⟩

theorem centralizer_le_Φ {b : MulAut (Multiplicative V4)} (hb : b ∈ Oq)
    (hbc : b * P.ch = P.ch * b) :
    ∃ x : ↥H, (x : G) ∈ L₁ ⊔ (V ⊔ conjSub P.g⁻¹ V) ∧ P.Φ x = b := by
  have hc := P.ch_props
  have hcube : P.ch * P.ch * P.ch = 1 := by rw [← pow_three']; exact hc.2.2
  have hcL : SY.c ∈ L₁ ⊔ (V ⊔ conjSub P.g⁻¹ V) := le_sup_left (a := L₁) SY.c_mem
  have hIY : V ⊔ conjSub P.g⁻¹ V ≤ L₁ ⊔ (V ⊔ conjSub P.g⁻¹ V) := le_sup_right
  rcases centralizer_S3_aut hc.1 P.t1_props.1 P.t2_props.1 hb hc.2 P.t1_props.2
    P.t2_props.2 P.t12_props hbc with h | h | h
  · obtain ⟨y, hyI, hy⟩ := P.inSA_mem h
    exact ⟨y, hIY hyI, hy⟩
  ·
    obtain ⟨y, hyI, hy⟩ := P.inSA_mem h
    refine ⟨⟨SY.c, SY.c_mem_H⟩ * y, Subgroup.mul_mem _ hcL (hIY hyI), ?_⟩
    rw [map_mul, hy]
    show P.ch * (P.ch * P.ch * b) = b
    calc P.ch * (P.ch * P.ch * b) = P.ch * P.ch * P.ch * b := by group
      _ = b := by rw [hcube, one_mul]
  ·
    obtain ⟨y, hyI, hy⟩ := P.inSA_mem h
    refine ⟨⟨SY.c, SY.c_mem_H⟩ * ⟨SY.c, SY.c_mem_H⟩ * y,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hcL hcL) (hIY hyI), ?_⟩
    rw [map_mul, map_mul, hy]
    show P.ch * P.ch * (P.ch * b) = b
    calc P.ch * P.ch * (P.ch * b) = P.ch * P.ch * P.ch * b := by group
      _ = b := by rw [hcube, one_mul]

theorem dvd_card_range : 18 ∣ Nat.card P.Φ.range := by
  rw [← card_centralizer_aut P.ch_props.1 P.ch_props.2]
  refine Subgroup.card_dvd_of_le fun b hb => ?_
  obtain ⟨x, -, hx⟩ := P.centralizer_le_Φ hb.1 (Subgroup.mem_centralizer_singleton_iff.mp hb.2)
  exact ⟨x, hx⟩

end A5SitPf15

namespace A5Sit

variable {G : Type} [Group G] [Finite G] {T V V₁ V₃ L₁ H : Subgroup G}
  (S : A5Sit G T V V₁ V₃ L₁ H)
include S

theorem exists_V1_eq : ∃ z : G, z ≠ 1 ∧ ∀ x, x ∈ V₁ ↔ x = 1 ∨ x = z := by
  have hz : ∃ z ∈ V₁, z ≠ 1 := by
    by_contra h
    push Not at h
    have hb : V₁ = ⊥ := (Subgroup.eq_bot_iff_forall V₁).2 h
    have := S.card_V1
    rw [hb, Subgroup.card_bot] at this
    omega
  obtain ⟨z, hzV, hz1⟩ := hz
  have hord : orderOf z = 2 := by
    have h1 : orderOf z ∣ 2 := by
      rw [← S.card_V1]
      exact Subgroup.orderOf_dvd_natCard V₁ hzV
    rcases (Nat.dvd_prime Nat.prime_two).1 h1 with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hz1
    · exact h
  have hZ : Subgroup.zpowers z = V₁ := Subgroup.eq_of_le_of_card_ge
    (Subgroup.zpowers_le.2 hzV) (by rw [S.card_V1, Nat.card_zpowers, hord])
  refine ⟨z, hz1, fun x => ?_⟩
  rw [← hZ]
  constructor
  · intro hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← zpow_mod_orderOf, hord]
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · left
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_zero]
    · right
      rw [show ((2 : ℕ) : ℤ) = 2 from rfl, h, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem nonempty_pf15 (hF956 : A5.StmtF956i) (SY : A5SitY S L₁)
    (hn : H ≤ Subgroup.normalizer (L₁ : Set G)) (U_eq : conjClosure V₃ H = pCoreOf 2 L₁)
    (hUQ8 : IsQ8Sq ↥(conjClosure V₃ H)) : Nonempty (A5SitPf15 S SY) := by
  obtain ⟨g, hg, hQ8, hS3, hUI⟩ := S.F956_data hF956
  obtain ⟨C⟩ := nonempty_q8Coords hUQ8
  obtain ⟨v, hv, hvQ⟩ := IsConcreteLE.not_le_iff_exists.1 S.not_V_le
  obtain ⟨z, hz1, hzV⟩ := S.exists_V1_eq
  have hzV1 : z ∈ V₁ := (hzV z).2 (Or.inr rfl)
  have hzU : z ∈ conjClosure V₃ H := le_conjClosure _ _ (S.V1_le_V3 hzV1)
  have hUH : conjClosure V₃ H ≤ H := S.U_le_Q.trans (pCoreOf_le 2 H)
  have hCz : C.z = z := by
    have := C.center ⟨z, hzU⟩ fun u => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (S.hF.H_le_centralizer (hUH u.2)) z hzV1)
    rcases this with h | h
    · exact absurd h hz1
    · exact h.symm
  exact ⟨⟨hn, U_eq, hUQ8, g, hg, hQ8, hS3, hUI, C, fun x => hCz ▸ hzV x, v, hv, hvQ⟩⟩

end A5Sit

end CFSG.Quasithin.H13
