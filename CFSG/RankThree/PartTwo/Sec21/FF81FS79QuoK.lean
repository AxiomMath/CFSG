module

public import CFSG.RankThree.PartTwo.Sec21.FF81FS79KStmt
public import CFSG.RankThree.PartTwo.Sec21.FF81FS79Quo

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 Equiv
open CFSG.Assembly (InCatalog)

variable {H : Type} [Group H] [Finite H]

theorem QData.conclusionP (P : ∀ (G : Type) [Group G] [Finite G], Prop)
    (hR1 : ∀ (G : Type) [Group G] [Finite G], P G → Prop2OneAt G) {Γ Z : Subgroup H}
    {b t c : H} {J' : Subgroup H} (D : QData Γ Z b t c J')
    (hP : haveI : (Z.subgroupOf Γ).Normal := ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf] at hn ⊢
        simpa using D.Z_norm (g : H) g.2 (n : H) hn⟩
      P (↥Γ ⧸ Z.subgroupOf Γ)) :
    ∃ O : Subgroup H, Z ≤ O ∧ O ≤ Γ ∧ (∀ g ∈ Γ, ∀ o ∈ O, g * o * g⁻¹ ∈ O) ∧
      (∀ o ∈ O, ∃ m : ℕ, Nat.Coprime 6 m ∧ o ^ m ∈ Z) ∧
      ∀ g ∈ Γ, ∃ o ∈ O, ∃ n ∈ Γ ⊓ Nor (Subgroup.zpowers b ⊔ Z), g = o * n := by
  classical
  haveI hN : (Z.subgroupOf Γ).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using D.Z_norm (g : H) g.2 (n : H) hn⟩
  let Q : Quo Γ Z (↥Γ ⧸ Z.subgroupOf Γ) :=
    ⟨QuotientGroup.mk' _, QuotientGroup.mk'_surjective _, QuotientGroup.ker_mk' _⟩
  have hbc : Q.φ ⟨b, D.b_mem⟩ * Q.φ ⟨c, D.c_mem⟩ = Q.φ ⟨c, D.c_mem⟩ * Q.φ ⟨b, D.b_mem⟩ := by
    have := Q.Jq_cen_b D (Q.φ_mem_Jq D D.c_mem_J)
    exact (Subgroup.mem_centralizer_singleton_iff.mp this).symm
  have hb3 : (Q.φ ⟨b, D.b_mem⟩) ^ 3 = 1 := by
    rw [← Q.orderOf_b D]
    exact pow_orderOf_eq_one _
  have hc3 : (Q.φ ⟨c, D.c_mem⟩) ^ 3 = 1 := by
    rw [← Q.orderOf_c D]
    exact pow_orderOf_eq_one _
  have hA := isPGroup_closure_pair hbc hb3 hc3
  have hodd : Odd (Nat.card (Opp 3 (⊤ : Subgroup (↥Γ ⧸ Z.subgroupOf Γ)))) :=
    odd_Opp_of_no_two hA (fun R hR hBR => Q.no_two_quot D R hR hBR)
  have hres := hR1 (↥Γ ⧸ Z.subgroupOf Γ) hP (Q.φ ⟨b, D.b_mem⟩) (Q.φ ⟨t, D.t_mem⟩)
    (Q.φ ⟨c, D.c_mem⟩) (Q.Jq (J' := J')) (Q.orderOf_b D) (Q.orderOf_t D) (Q.tb_eq D)
    (Q.Jq_iso D) (Q.Jq_cen_b D) (Q.Jq_cen_t D) (Q.Nor_b_le_Nor_Jq D) (Q.setMul_b D)
    (Q.φ_mem_Jq D D.c_mem_J) (Q.orderOf_c D) (Q.setMul_c D)
    (fun R hR hBR => Q.no_two_quot D R hR hBR) (fun h hh => Q.weak_quot D h hh)
  refine ⟨Q.pre (Opp 3 (⊤ : Subgroup (↥Γ ⧸ Z.subgroupOf Γ))), Q.Z_le_pre _ D.Z_le,
    Q.pre_le _, ?_, ?_, ?_⟩
  · intro g hg o ho
    obtain ⟨hoΓ, hoO⟩ := (Q.mem_pre_iff _).mp ho
    refine (Q.mem_pre_iff _).mpr ⟨Γ.mul_mem (Γ.mul_mem hg hoΓ) (Γ.inv_mem hg), ?_⟩
    have e : (⟨g * o * g⁻¹, Γ.mul_mem (Γ.mul_mem hg hoΓ) (Γ.inv_mem hg)⟩ : ↥Γ) =
        ⟨g, hg⟩ * ⟨o, hoΓ⟩ * ⟨g, hg⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact L14.Opp_conj_mem (Subgroup.mem_top _) hoO
  · intro o ho
    obtain ⟨hoΓ, hoO⟩ := (Q.mem_pre_iff _).mp ho
    have h2 : Nat.Coprime 2 (Nat.card (Opp 3 (⊤ : Subgroup (↥Γ ⧸ Z.subgroupOf Γ)))) :=
      Nat.coprime_two_left.mpr hodd
    have h3 : Nat.Coprime 3 (Nat.card (Opp 3 (⊤ : Subgroup (↥Γ ⧸ Z.subgroupOf Γ)))) := by
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      exact L14.Opp_coprime 3 _
    refine ⟨Nat.card (Opp 3 (⊤ : Subgroup (↥Γ ⧸ Z.subgroupOf Γ))), Nat.Coprime.mul_left h2 h3, ?_⟩
    have h1 : (⟨Q.φ ⟨o, hoΓ⟩, hoO⟩ : ↥(Opp 3 (⊤ : Subgroup (↥Γ ⧸ Z.subgroupOf Γ)))) ^
        Nat.card (Opp 3 (⊤ : Subgroup (↥Γ ⧸ Z.subgroupOf Γ))) = 1 := pow_card_eq_one'
    have h4 : (Q.φ ⟨o, hoΓ⟩) ^ Nat.card (Opp 3 (⊤ : Subgroup (↥Γ ⧸ Z.subgroupOf Γ))) = 1 := by
      have := congrArg Subtype.val h1
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have h5 : Q.φ ⟨o ^ Nat.card (Opp 3 (⊤ : Subgroup (↥Γ ⧸ Z.subgroupOf Γ))), Γ.pow_mem hoΓ _⟩ =
        1 := by
      have : (⟨o ^ Nat.card (Opp 3 (⊤ : Subgroup (↥Γ ⧸ Z.subgroupOf Γ))), Γ.pow_mem hoΓ _⟩ :
          ↥Γ) = (⟨o, hoΓ⟩ : ↥Γ) ^ Nat.card (Opp 3 (⊤ : Subgroup (↥Γ ⧸ Z.subgroupOf Γ))) := rfl
      rw [this, map_pow]
      exact h4
    exact (Q.eq_one_iff (Γ.pow_mem hoΓ _)).mp h5
  · intro g hg
    have hmem : Q.φ ⟨g, hg⟩ ∈ setMul (Opp 3 (⊤ : Subgroup (↥Γ ⧸ Z.subgroupOf Γ)))
        (Nor (Subgroup.zpowers (Q.φ ⟨b, D.b_mem⟩))) := by
      rw [hres]
      trivial
    obtain ⟨oq, hoq, nq, hnq, hgq⟩ := hmem
    obtain ⟨nh, rfl, hnN⟩ := (Q.mem_Nor_x_iff D.Z_le D.b_mem nq).mp hnq
    obtain ⟨oh, rfl⟩ := Q.surj oq
    have hge : Q.φ (oh * nh) = Q.φ ⟨g, hg⟩ := by rw [map_mul]; exact hgq.symm
    have hzmem : ((oh : H) * (nh : H))⁻¹ * g ∈ Z := (Q.eq_iff (Γ.mul_mem oh.2 nh.2) hg).mp hge
    refine ⟨(oh : H), (Q.mem_pre_iff _).mpr ⟨oh.2, hoq⟩, (nh : H) * (((oh : H) * (nh : H))⁻¹ * g),
      ⟨Γ.mul_mem nh.2 (Γ.mul_mem (Γ.inv_mem (Γ.mul_mem oh.2 nh.2)) hg), ?_⟩, ?_⟩
    · exact (Nor _).mul_mem hnN (Subgroup.le_normalizer (Subgroup.mem_sup_right hzmem))
    · group

theorem kGroupNonab_quotient (hK : KCore.KGroupNonab InCatalog H) (Γ : Subgroup H)
    (N : Subgroup ↥Γ) [N.Normal] : KCore.KGroupNonab InCatalog (↥Γ ⧸ N) :=
  (hK.subgroup CFSG.Assembly.inCatalog_isoInvariant Γ).quotient
    CFSG.Assembly.inCatalog_isoInvariant N

end CFSG.RankThree.PartTwo.Sec21.FF81
