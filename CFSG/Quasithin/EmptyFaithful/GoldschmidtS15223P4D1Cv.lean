module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4D1Par
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4Ctx
public import CFSG.Quasithin.EmptyFaithful.SBd8Abs

public section

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open

namespace CFSG.Quasithin.S15223P4.D1

section Hom

variable {Γ Δ : Type} [Group Γ] [Finite Γ] [Group Δ]

theorem card_eq_card_map_mul_card_ker' (ρ : Γ →* Δ) {Q : Subgroup Γ} (hkQ : ρ.ker ≤ Q) :
    Nat.card Q = Nat.card (Q.map ρ) * Nat.card ρ.ker := by
  have hker : ρ.rangeRestrict.ker = ρ.ker := MonoidHom.ker_rangeRestrict ρ
  have h := card_eq_card_map_mul_card_ker ρ.rangeRestrict ρ.rangeRestrict_surjective
    (Q := Q) (by rw [hker]; exact hkQ)
  rw [hker] at h
  rw [h]
  congr 1
  have hmap : (Q.map ρ.rangeRestrict).map ρ.range.subtype = Q.map ρ := by
    rw [Subgroup.map_map]; rfl
  rw [← hmap, Subgroup.card_map_of_injective ρ.range.subtype_injective]

end Hom

section Order

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem card_autOn_M (c : P4Ctx T Mc M H B₀ I X) :
    Nat.card ↥(autOn M (V154 T Mc M)) = 36 := by
  obtain ⟨hV, hom⟩ := c.concl.2.2.1
  let _ : CommGroup ↥(V154 T Mc M) := commGroupOfElemAbelian hV
  exact (S152O4.om4_facts (V := ↥(V154 T Mc M)) hom).card_eq

theorem card_autOn_inf (c : P4Ctx T Mc M H B₀ I X) :
    Nat.card ↥(autOn (M ⊓ I) (V154 T Mc M)) = 6 := by
  have hMV := le_normalizer_V154 T Mc M
  set ρ := A4.actionOn (V154 T Mc M) M hMV with hρ
  have hker : ρ.ker ≤ (M ⊓ I).subgroupOf M := by
    intro x hx
    have h1 : (x : G) ∈ Subgroup.centralizer (V154 T Mc M : Set G) :=
      (A4.actionOn_eq_one_iff hMV x).mp hx
    exact ⟨x.2, (cv_le_inf152 c.setting c.inputs ⟨x.2, h1⟩).2⟩
  have e1 := card_eq_card_map_mul_card_ker' ρ (Q := (M ⊓ I).subgroupOf M) hker
  have e2 := card_eq_card_map_mul_card_ker' ρ (Q := (⊤ : Subgroup ↥M)) le_top
  have h1 : ((M ⊓ I).subgroupOf M).map ρ = autOn (M ⊓ I) (V154 T Mc M) :=
    (SBd8.autOn_eq_map_actionOn hMV inf_le_left).symm
  have h2 : (⊤ : Subgroup ↥M).map ρ = autOn M (V154 T Mc M) := by
    rw [SBd8.autOn_eq_map_actionOn hMV le_rfl, Subgroup.subgroupOf_self]
  rw [h1] at e1
  rw [h2, Subgroup.card_top, card_autOn_M c] at e2
  have e3 := Subgroup.card_mul_index ((M ⊓ I).subgroupOf M)
  have hidx : ((M ⊓ I).subgroupOf M).index = 6 := by
    obtain ⟨-, -, -, Z₁, -, -, -, h6⟩ := c.concl
    exact h6
  rw [hidx, e1] at e3
  have hpos : 0 < Nat.card ↥ρ.ker := Nat.card_pos
  have e4 : Nat.card ↥(autOn (M ⊓ I) (V154 T Mc M)) * 6 * Nat.card ↥ρ.ker =
      36 * Nat.card ↥ρ.ker := by
    calc Nat.card ↥(autOn (M ⊓ I) (V154 T Mc M)) * 6 * Nat.card ↥ρ.ker
        = Nat.card ↥(autOn (M ⊓ I) (V154 T Mc M)) * Nat.card ↥ρ.ker * 6 := by ring
      _ = Nat.card ↥M := e3
      _ = 36 * Nat.card ↥ρ.ker := e2
  have := Nat.eq_of_mul_eq_mul_right hpos e4
  omega

end Order

section Six

theorem mem_zpowers_of_card_six {Q : Type*} [Group Q] [Finite Q] (hQ : Nat.card Q = 6) {a b : Q}
    (ha : a ^ 3 = 1) (ha1 : a ≠ 1) (hb : b ^ 3 = 1) : b ∈ Subgroup.zpowers a := by
  have hord : orderOf a = 3 := orderOf_eq_prime ha ha1
  have hcard : Nat.card (Subgroup.zpowers a) = 3 := by rw [Nat.card_zpowers, hord]
  have hidx : (Subgroup.zpowers a).index = 2 := by
    have := Subgroup.card_mul_index (Subgroup.zpowers a)
    rw [hcard, hQ] at this
    omega
  have : (Subgroup.zpowers a).Normal := Subgroup.normal_of_index_eq_two hidx
  have hqc : Nat.card (Q ⧸ Subgroup.zpowers a) = 2 := hidx
  have hb' : (QuotientGroup.mk b : Q ⧸ Subgroup.zpowers a) ^ 3 = 1 := by
    rw [← QuotientGroup.mk_pow, hb, QuotientGroup.mk_one]
  have hdvd2 : orderOf (QuotientGroup.mk b : Q ⧸ Subgroup.zpowers a) ∣ 2 := by
    rw [← hqc]; exact orderOf_dvd_natCard _
  have hdvd3 : orderOf (QuotientGroup.mk b : Q ⧸ Subgroup.zpowers a) ∣ 3 :=
    orderOf_dvd_of_pow_eq_one hb'
  have h1 : orderOf (QuotientGroup.mk b : Q ⧸ Subgroup.zpowers a) = 1 := by
    have := Nat.dvd_gcd hdvd2 hdvd3
    simpa using this
  exact (QuotientGroup.eq_one_iff b).mp (orderOf_eq_one_iff.mp h1)

end Six

section Cube

variable {G : Type} [Group G] [Finite G]
  {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

theorem exists_zpow_of_cube (c : P4Ctx T Mc M H B₀ I X) {a b : G} (ha : a ∈ M ⊓ I)
    (hb : b ∈ M ⊓ I) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1)
    (hρa : A4.actionOn (V154 T Mc M) M (le_normalizer_V154 T Mc M) ⟨a, ha.1⟩ ≠ 1) :
    ∃ k : ℤ, A4.actionOn (V154 T Mc M) M (le_normalizer_V154 T Mc M) ⟨b, hb.1⟩ =
      A4.actionOn (V154 T Mc M) M (le_normalizer_V154 T Mc M) ⟨a, ha.1⟩ ^ k := by
  have hMV := le_normalizer_V154 T Mc M
  set ρ := A4.actionOn (V154 T Mc M) M hMV with hρ
  have hQ := card_autOn_inf c
  have hmemA : ρ ⟨a, ha.1⟩ ∈ autOn (M ⊓ I) (V154 T Mc M) := by
    rw [SBd8.autOn_eq_map_actionOn hMV inf_le_left]
    exact Subgroup.mem_map_of_mem ρ (show (⟨a, ha.1⟩ : ↥M) ∈ (M ⊓ I).subgroupOf M from ha)
  have hmemB : ρ ⟨b, hb.1⟩ ∈ autOn (M ⊓ I) (V154 T Mc M) := by
    rw [SBd8.autOn_eq_map_actionOn hMV inf_le_left]
    exact Subgroup.mem_map_of_mem ρ (show (⟨b, hb.1⟩ : ↥M) ∈ (M ⊓ I).subgroupOf M from hb)
  let a' : ↥(autOn (M ⊓ I) (V154 T Mc M)) := ⟨ρ ⟨a, ha.1⟩, hmemA⟩
  let b' : ↥(autOn (M ⊓ I) (V154 T Mc M)) := ⟨ρ ⟨b, hb.1⟩, hmemB⟩
  have ha' : a' ^ 3 = 1 := Subtype.ext (by
    show ρ ⟨a, ha.1⟩ ^ 3 = 1
    rw [← map_pow]
    exact (by simpa using congrArg (fun z : ↥M => ρ z) (show (⟨a, ha.1⟩ : ↥M) ^ 3 = 1 from
      Subtype.ext ha3)))
  have hb'3 : b' ^ 3 = 1 := Subtype.ext (by
    show ρ ⟨b, hb.1⟩ ^ 3 = 1
    rw [← map_pow]
    exact (by simpa using congrArg (fun z : ↥M => ρ z) (show (⟨b, hb.1⟩ : ↥M) ^ 3 = 1 from
      Subtype.ext hb3)))
  have ha1' : a' ≠ 1 := fun h => hρa (congrArg Subtype.val h)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (mem_zpowers_of_card_six hQ ha' ha1' hb'3)
  exact ⟨k, by simpa using (congrArg Subtype.val hk).symm⟩

end Cube

end CFSG.Quasithin.S15223P4.D1
