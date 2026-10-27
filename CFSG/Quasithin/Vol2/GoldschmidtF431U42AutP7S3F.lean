module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7S3
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7S5

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Final

variable (c : AutCtx G M₁ M₂ z) (hZ : ZStmt c) (hT₀G : IsSylowTwoOf (c.iso.imgG That) ⊤)

theorem M1_inf_N2_le {n : G}
    (hn : n ∈ Subgroup.normalizer (c.iso.imgG A2h : Set G) ⊓ M₁) :
    n ∈ Subgroup.normalizer (c.iso.imgG B1h : Set G) ∧
      n ∈ Subgroup.normalizer (c.iso.imgG B2h : Set G) := by
  have hmap := c.iso.map_toG1_normalizer (K := A2h) (A2h_le_That.trans That_le_Bh)
  rw [← hmap] at hn
  obtain ⟨p, hp, rfl⟩ := hn
  have hpN : (p : Ah) ∈ P1h ⊓ Subgroup.normalizer (A2h : Set Ah) := ⟨p.2, hp⟩
  rw [N_P1h_A2h] at hpN
  have hpT : (p : Ah) ∈ That := Tt_le_That hpN
  set b : Bh := ⟨p, That_le_Bh hpT⟩ with hb
  have hpb : p = Subgroup.inclusion Bh_le_P1h b := Subtype.ext rfl
  have h1 : c.iso.toG1 p = c.iso.toG b := by rw [hpb, c.iso.toG1_inclusion]
  rw [h1]
  have hmem : c.iso.toG b ∈ c.iso.imgG Tt := c.iso.mem_imgG.2 ⟨b, hpN, rfl⟩
  exact ⟨imgG_le_normalizer c.iso (fun g hg => (Tt_normalizer hg).1) hmem,
    imgG_le_normalizer c.iso (fun g hg => (Tt_normalizer hg).2) hmem⟩

include hZ hT₀G

theorem N2_le_normalizer_B1 : Subgroup.normalizer (c.iso.imgG A2h : Set G) ≤
    Subgroup.normalizer (c.iso.imgG B1h : Set G) := by
  refine le_normalizer_of_pair (C₁ := c.iso.imgG B1h) (C₂ := c.iso.imgG B2h)
    (S := Subgroup.normalizer (c.iso.imgG A2h : Set G) ⊓ M₁) (card_normalizer_A2 c hZ hT₀G) ?_
    inf_le_left (fun n hn => (M1_inf_N2_le c hn).1) ?_
  · rw [c.iso.card_normalizer_M1 (A2h_le_That.trans That_le_Bh), card_N1_A2]
  · intro n hn
    exact conjSub_B_cases c hZ Bl_pairs.1.1 Bl_pairs.1.2.1 Bl_pairs.1.2.2.1 Bl_pairs.1.2.2.2
      (S := B1h) (fun a ha => ha) (B1h_le_A2h.trans A2h_le_That |>.trans That_le_Bh) card_B1h hn

theorem N2_le_normalizer_B2 : Subgroup.normalizer (c.iso.imgG A2h : Set G) ≤
    Subgroup.normalizer (c.iso.imgG B2h : Set G) := by
  refine le_normalizer_of_pair (C₁ := c.iso.imgG B1h) (C₂ := c.iso.imgG B2h)
    (S := Subgroup.normalizer (c.iso.imgG A2h : Set G) ⊓ M₁) (card_normalizer_A2 c hZ hT₀G) ?_
    inf_le_left (fun n hn => (M1_inf_N2_le c hn).2) ?_
  · rw [c.iso.card_normalizer_M1 (A2h_le_That.trans That_le_Bh), card_N1_A2]
  · intro n hn
    exact conjSub_B_cases c hZ Bl_pairs.2.1 Bl_pairs.2.2.1 Bl_pairs.2.2.2.1 Bl_pairs.2.2.2.2
      (S := B2h) (fun a ha => ha) (B2h_le_A2h.trans A2h_le_That |>.trans That_le_Bh) card_B2h hn

theorem normalizer_A2_equiv : Nonempty
    (↥(Subgroup.normalizer (c.iso.imgG A2h : Set G)) ⧸
      (c.iso.imgG A2h).subgroupOf (Subgroup.normalizer (c.iso.imgG A2h : Set G)) ≃*
        Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
  set A := c.iso.imgG A2h with hA
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
  refine quot_equiv_perm_prod (A := A) (m := 3) (m' := 3) (Subgroup.le_normalizer) X Y ?_ ?_ ?_ ?_
    (hcardB (B1h_le_A2h.trans A2h_le_That) card_B1h)
    (hcardB (B2h_le_A2h.trans A2h_le_That) card_B2h) ?_
  · rintro n hn u ⟨hu, hu1⟩
    refine ⟨(Subgroup.mem_normalizer_iff.1 (N2_le_normalizer_B1 c hZ hT₀G hn) u).1 hu, ?_⟩
    intro h
    apply hu1
    have : u = n⁻¹ * (n * u * n⁻¹) * n := by group
    rw [this, h]
    group
  · rintro n hn u ⟨hu, hu1⟩
    refine ⟨(Subgroup.mem_normalizer_iff.1 (N2_le_normalizer_B2 c hZ hT₀G hn) u).1 hu, ?_⟩
    intro h
    apply hu1
    have : u = n⁻¹ * (n * u * n⁻¹) * n := by group
    rw [this, h]
    group
  · intro a ha u hu
    rcases hu with ⟨hu, -⟩ | ⟨hu, -⟩
    · exact hab.1 a ha u (imgG_mono' c.iso B1h_le_A2h hu)
    · exact hab.1 a ha u (imgG_mono' c.iso B2h_le_A2h hu)
  · intro n hn hnc
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
  · rw [card_normalizer_A2 c hZ hT₀G, hA, c.iso.card_imgG (A2h_le_That.trans That_le_Bh), card_A2h]
    norm_num [Nat.factorial]

end Final

end CFSG.Quasithin.H13.F431.U42Aut
