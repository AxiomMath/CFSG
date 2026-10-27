module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7S3F

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

theorem surjective_of_ker_card {N P : Type*} [Group N] [Group P] [Finite N] [Finite P]
    (φ : N →* P) {K : Subgroup N} (hker : φ.ker = K)
    (hcard : Nat.card N = Nat.card K * Nat.card P) : Function.Surjective φ := by
  subst hker
  have hinj := QuotientGroup.kerLift_injective φ
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
  have hq : Nat.card (N ⧸ φ.ker) = Nat.card P := by
    have hpos : 0 < Nat.card ↥φ.ker := Nat.card_pos
    rw [h1] at hcard
    exact Nat.eq_of_mul_eq_mul_right hpos (hcard.trans (mul_comm _ _))
  have hbij := hinj.bijective_of_nat_card_le hq.ge
  intro p
  obtain ⟨q, hq'⟩ := hbij.2 p
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨n, hq'⟩

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Act

variable (c : AutCtx G M₁ M₂ z) (hZ : ZStmt c) (hT₀G : IsSylowTwoOf (c.iso.imgG That) ⊤)

include hZ hT₀G

theorem normalizer_A2_act {a a' b b' : G}
    (ha : a ∈ c.iso.imgG B1h) (ha1 : a ≠ 1) (ha' : a' ∈ c.iso.imgG B1h) (ha1' : a' ≠ 1)
    (hb : b ∈ c.iso.imgG B2h) (hb1 : b ≠ 1) (hb' : b' ∈ c.iso.imgG B2h) (hb1' : b' ≠ 1) :
    ∃ n ∈ Subgroup.normalizer (c.iso.imgG A2h : Set G),
      n * a * n⁻¹ = a' ∧ n * b * n⁻¹ = b' := by
  classical
  set A := c.iso.imgG A2h with hA
  set N := Subgroup.normalizer (A : Set G) with hN
  have hab := imgG_E16 c.iso (K := A2h) (fun a ha b hb => A2h_comm ha hb) fun a ha => A2h_sq ha
  have hcent : Subgroup.centralizer (A : Set G) = A := by
    have := centralizer_aOf_M2 c
    rwa [aOf_M2] at this
  set X : Set G := {u | u ∈ c.iso.imgG B1h ∧ u ≠ 1} with hX
  set Y : Set G := {u | u ∈ c.iso.imgG B2h ∧ u ≠ 1} with hY
  have hcardB : ∀ {S : Subgroup Ah} (hS : S ≤ That) (hc : Nat.card ↥S = 4),
      Nat.card ↥{u : G | u ∈ c.iso.imgG S ∧ u ≠ 1} = 3 := by
    intro S hS hc
    have e : {u : G | u ∈ c.iso.imgG S ∧ u ≠ 1} = (c.iso.imgG S : Set G) \ {1} := by
      ext u
      simp
    have h4 : Nat.card ↥(c.iso.imgG S) = 4 := by
      rw [c.iso.card_imgG (hS.trans That_le_Bh), hc]
    rw [Nat.card_coe_set_eq, e, Set.ncard_sdiff_singleton_of_mem (c.iso.imgG S).one_mem]
    have : (c.iso.imgG S : Set G).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact h4
    omega
  have hXm : Nat.card ↥X = 3 := hcardB (B1h_le_A2h.trans A2h_le_That) card_B1h
  have hYm : Nat.card ↥Y = 3 := hcardB (B2h_le_A2h.trans A2h_le_That) card_B2h
  have hXinv : ∀ n ∈ N, ∀ u ∈ X, n * u * n⁻¹ ∈ X := by
    rintro n hn u ⟨hu, hu1⟩
    refine ⟨(Subgroup.mem_normalizer_iff.1 (N2_le_normalizer_B1 c hZ hT₀G hn) u).1 hu, ?_⟩
    intro h
    apply hu1
    have : u = n⁻¹ * (n * u * n⁻¹) * n := by group
    rw [this, h]
    group
  have hYinv : ∀ n ∈ N, ∀ u ∈ Y, n * u * n⁻¹ ∈ Y := by
    rintro n hn u ⟨hu, hu1⟩
    refine ⟨(Subgroup.mem_normalizer_iff.1 (N2_le_normalizer_B2 c hZ hT₀G hn) u).1 hu, ?_⟩
    intro h
    apply hu1
    have : u = n⁻¹ * (n * u * n⁻¹) * n := by group
    rw [this, h]
    group
  have hAc : ∀ a ∈ A, ∀ u ∈ X ∪ Y, a * u = u * a := by
    intro a ha u hu
    rcases hu with ⟨hu, -⟩ | ⟨hu, -⟩
    · exact hab.1 a ha u (imgG_mono' c.iso B1h_le_A2h hu)
    · exact hab.1 a ha u (imgG_mono' c.iso B2h_le_A2h hu)
  have hker : ∀ n ∈ N, (∀ u ∈ X ∪ Y, n * u = u * n) → n ∈ A := by
    intro n hn hnc
    have hcomm := comm_of_span c (h1 := A2_check.1) (hmul := A2_check.2.1) (Sl := Th2)
      span_check.2.2 (n := n) (fun r hr => by
        have hr' := Th2_props hr
        refine ⟨A2_check.2.2.2.1 r hr'.1, hnc _ ?_⟩
        have hrT : r ∈ Thl := A2_check.2.2.2.1 r hr'.1
        have hrep : RepL r (eltB r : P45) := by
          rw [coe_eltB hrT]
          exact repL_eltOfL hrT
        have hne1 := (toG_eltB_Th2 c hZ hr).2.1
        rcases Bl_th.2.2.1 r hr with h | h
        · exact Or.inl ⟨c.iso.mem_imgG.2 ⟨eltB r, ⟨r, h, hrep⟩, rfl⟩, hne1⟩
        · exact Or.inr ⟨c.iso.mem_imgG.2 ⟨eltB r, ⟨r, h, hrep⟩, rfl⟩, hne1⟩)
    rw [← hcent, Subgroup.mem_centralizer_iff]
    intro a ha
    exact (hcomm a ha).symm
  have hAN : A ≤ N := Subgroup.le_normalizer
  have hk : ((conjPermOf N X hXinv).prod (conjPermOf N Y hYinv)).ker = A.subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : n ∈ (conjPermOf N X hXinv).ker := congrArg Prod.fst h
      have h2 : n ∈ (conjPermOf N Y hYinv).ker := congrArg Prod.snd h
      rw [mem_ker_conjPermOf] at h1 h2
      refine hker n n.2 fun u hu => ?_
      rcases hu with hu | hu
      · exact h1 u hu
      · exact h2 u hu
    · intro h
      refine Prod.ext ?_ ?_
      · have : n ∈ (conjPermOf N X hXinv).ker :=
          mem_ker_conjPermOf.2 fun u hu => hAc _ h u (Or.inl hu)
        exact this
      · have : n ∈ (conjPermOf N Y hYinv).ker :=
          mem_ker_conjPermOf.2 fun u hu => hAc _ h u (Or.inr hu)
        exact this
  have hc : Nat.card ↥N = Nat.card ↥(A.subgroupOf N) *
      Nat.card (Equiv.Perm ↥X × Equiv.Perm ↥Y) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv, Nat.card_prod]
    have h1 : Nat.card (Equiv.Perm ↥X) = (3 : ℕ).factorial := by
      classical
      have := Fintype.ofFinite ↥X
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hXm]
    have h2 : Nat.card (Equiv.Perm ↥Y) = (3 : ℕ).factorial := by
      classical
      have := Fintype.ofFinite ↥Y
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, ← Nat.card_eq_fintype_card, hYm]
    rw [h1, h2, card_normalizer_A2 c hZ hT₀G, hA,
      c.iso.card_imgG (A2h_le_That.trans That_le_Bh), card_A2h]
    norm_num [Nat.factorial]
  have hsurj := surjective_of_ker_card _ hk hc
  obtain ⟨n, hn⟩ := hsurj (Equiv.swap (⟨a, ha, ha1⟩ : X) ⟨a', ha', ha1'⟩,
    Equiv.swap (⟨b, hb, hb1⟩ : Y) ⟨b', hb', hb1'⟩)
  refine ⟨n, n.2, ?_, ?_⟩
  · have h1 := congrArg (fun p : Equiv.Perm ↥X × Equiv.Perm ↥Y => (p.1 ⟨a, ha, ha1⟩ : G)) hn
    simpa [conjPermOf] using h1
  · have h1 := congrArg (fun p : Equiv.Perm ↥X × Equiv.Perm ↥Y => (p.2 ⟨b, hb, hb1⟩ : G)) hn
    simpa [conjPermOf] using h1

end Act

end CFSG.Quasithin.H13.F431.U42Aut
