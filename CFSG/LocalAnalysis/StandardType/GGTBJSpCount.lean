module

public import CFSG.LocalAnalysis.StandardType.GGTBJCount
public import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem card_ggFixingJ_mul_card_centralizer
    {G : Type} [Group G] [Finite G] {Bs X J : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (X : Set G)) (hJX : J ≤ X) :
    Nat.card ↥(ggFixingJ X J (ggGamma X hN).range) *
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) =
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := by
  let D : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G)
  have hDN : D ≤ Subgroup.normalizer (X : Set G) := inf_le_left.trans hN
  have hRange : (ggGamma X hDN).range = ggFixingJ X J (ggGamma X hN).range := by
    ext a
    constructor
    · rintro ⟨d, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · refine MonoidHom.mem_range.mpr ⟨⟨(d : G), d.2.1⟩, ?_⟩
        ext l
        rw [ggGamma_coe, ggGamma_coe]
      · rw [Subgroup.mem_iInf]
        intro l
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        apply Subtype.ext
        rw [ggGamma_coe]
        have hcomm := (Subgroup.mem_centralizer_iff.mp d.2.2 (l.1 : G) l.2).symm
        rw [hcomm]
        group
    · intro ha
      obtain ⟨haA, hafix⟩ := Subgroup.mem_inf.mp ha
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp haA
      have hbJ : (b : G) ∈ Subgroup.centralizer (J : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro j hj
        have hfix := Subgroup.mem_iInf.mp hafix ⟨⟨j, hJX hj⟩, hj⟩
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, ← hb] at hfix
        have hcoe := congrArg (fun z : X => (z : G)) hfix
        rw [ggGamma_coe] at hcoe
        rw [eq_comm]
        calc (b : G) * j = ((b : G) * j * (b : G)⁻¹) * (b : G) := by group
          _ = j * (b : G) := by rw [hcoe]
      refine MonoidHom.mem_range.mpr ⟨⟨(b : G), b.2, hbJ⟩, ?_⟩
      rw [← hb]
      ext l
      rw [ggGamma_coe, ggGamma_coe]
  have hInf : D ⊓ Subgroup.centralizer (X : Set G) =
      Bs ⊓ Subgroup.centralizer (X : Set G) := by
    ext z
    constructor
    · rintro ⟨⟨hb, _hj⟩, hx⟩
      exact ⟨hb, hx⟩
    · rintro ⟨hb, hx⟩
      exact ⟨⟨hb, Subgroup.centralizer_le hJX hx⟩, hx⟩
  have h := NbrU63.card_range_ggGamma_mul_card_inf hDN
  rw [hRange, hInf] at h
  exact h

theorem ggTBJ_card_fixingJ_eq_of_bstar_eq
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hBsB : Bs = B) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Nat.card ↥(ggFixingJ L J (ggGamma L hN).range) = p := by
  have hJ_comp : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.2.1
  have hJL : J ≤ L := hJ_comp.1.trans inf_le_left
  have hCL : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = p :=
    hcfg.card_bstar_inf_centralizer_L
  have hCJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 2 := by
    rw [hBsB, ← hcfg.2.2.1.2.2.2.2.2.2]
    exact hcfg.2.2.1.2.2.1
  have h := card_ggFixingJ_mul_card_centralizer hN hJL
  rw [hCL, hCJ, pow_two] at h
  exact Nat.eq_of_mul_eq_mul_right hcfg.tableB_facts.1.pos h

theorem ggTBJ_card_fixingJ_eq_nbr_of_bstar_eq
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hJK : J ≤ K) (hBsB : Bs = B)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    Nat.card ↥(ggFixingJ K J (ggGamma K hN).range) = p := by
  obtain ⟨hp, hBs, _hx, _hLx, _hBs4⟩ := hcfg.tableB_facts
  haveI : Fact p.Prime := ⟨hp⟩
  have hyOrder : orderOf y = p :=
    orderOf_eq_prime (hBs.2 y (hcfg.2.1.1 hnb.1.2.1)) hnb.1.2.2.1
  have hCK : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) = p := by
    rw [hBsB, inf_centralizer_eq_zpowers_of_sHat hnb.1, Nat.card_zpowers, hyOrder]
  have hCJ : Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 2 := by
    rw [hBsB, ← hcfg.2.2.1.2.2.2.2.2.2]
    exact hcfg.2.2.1.2.2.1
  have h := card_ggFixingJ_mul_card_centralizer hN hJK
  rw [hCK, hCJ, pow_two] at h
  exact Nat.eq_of_mul_eq_mul_right hp.pos h

theorem ggTBJ_card_fixingJ_mul_le_nbr_of_bstar_eq
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hJK : J ≤ K) (hBsB : Bs = B)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) :
    p ^ 2 * Nat.card ↥(ggFixingJ K J (ggGamma K hN).range) ≤
      Nat.card ↥(ggGamma K hN).range := by
  obtain ⟨hp, hBs, _hx, _hLx, hBs4⟩ := hcfg.tableB_facts
  haveI : Fact p.Prime := ⟨hp⟩
  have hyOrder : orderOf y = p :=
    orderOf_eq_prime (hBs.2 y (hcfg.2.1.1 hnb.1.2.1)) hnb.1.2.2.1
  have hCK : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) = p := by
    rw [hBsB, inf_centralizer_eq_zpowers_of_sHat hnb.1, Nat.card_zpowers, hyOrder]
  have hFix := ggTBJ_card_fixingJ_eq_nbr_of_bstar_eq hcfg hnb hJK hBsB hN
  have hCard := NbrU63.card_range_ggGamma_mul_card_inf hN
  rw [hCK] at hCard
  have hA3 : p ^ 3 ≤ Nat.card ↥(ggGamma K hN).range := by
    have hcube : p ^ 3 * p = p ^ 4 := by ring
    rw [← hCard, ← hcube] at hBs4
    exact Nat.le_of_mul_le_mul_right hBs4 hp.pos
  rw [hFix, ← pow_succ]
  exact hA3

end CFSG.StandardType
