module

public import CFSG.LocalAnalysis.StandardType.GGTBJRowGeneric

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.HardMathSupport.Solomon.Coordinator

theorem ggTBJ_config_unpack {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ y : MulAut ↥L, y ∈ (ggGamma L hN).range ∧ y ≠ 1 ∧
      CFSG.Open.IsComponentOf (J.subgroupOf L) (fixSubgroup y) ∧
      p ^ 2 * Nat.card ↥((ggGamma L hN).range ⊓
        ⨅ j : ↥(J.subgroupOf L), MulAction.stabilizer (MulAut ↥L) (j : ↥L)) ≤
        Nat.card ↥(ggGamma L hN).range := by
  classical
  obtain ⟨hp, -, -, hLx, -⟩ := GGConfig.tableB_facts hcfg
  haveI : Fact p.Prime := ⟨hp⟩
  have hJ_comp : CFSG.Assembly.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.2.1
  have hJ_layer : J = LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.1
  have hJ_le_L : J ≤ L := hJ_comp.1.trans inf_le_left
  have hxD : x ∈ D := hcfg.2.2.1.2.2.2.1
  have hB_le_Bs : B ≤ Bs := hcfg.2.1.1
  have hD_le_B : D ≤ B := hcfg.2.2.1.1
  have hD_ea : CFSG.Open.IsElemAbelian p D := hcfg.2.2.1.2.1
  have hcardD : Nat.card D = p ^ 2 := hcfg.2.2.1.2.2.1
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hS.2.2.1
  have hcyc : ∀ S : Subgroup G, S ≤ Subgroup.centralizer (L : Set G) → IsPGroup p S →
      IsCyclic S := hS.2.2.2.2
  have hND : D ≤ Subgroup.normalizer (L : Set G) := hD_le_B.trans (hB_le_Bs.trans hN)
  have hcardDg : Nat.card (ggGamma L hND).range * p = Nat.card D :=
    card_range_ggGamma_mul_of hp hD_ea hxD hx1 hLx hcyc hND
  have hcardΓ : Nat.card ↥(ggGamma L hND).range = p := by
    have h1 : Nat.card ↥(ggGamma L hND).range * p = p * p := by
      rw [hcardDg, hcardD, pow_two]
    exact Nat.eq_of_mul_eq_mul_right hp.pos h1
  have hΓA : (ggGamma L hND).range ≤ (ggGamma L hN).range := by
    intro u hu
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hu
    refine MonoidHom.mem_range.mpr ⟨⟨(b : G), hB_le_Bs (hD_le_B b.2)⟩, ?_⟩
    apply MulEquiv.ext
    intro l
    apply Subtype.ext
    rw [ggGamma_coe, ggGamma_coe]
  haveI : Nontrivial ↥(ggGamma L hND).range := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcardΓ]
    exact hp.one_lt
  obtain ⟨⟨y, hyΓ⟩, hy1⟩ := exists_ne (1 : ↥(ggGamma L hND).range)
  have hy1' : y ≠ 1 := fun h' => hy1 (Subtype.ext h')
  have hzΓ : Subgroup.zpowers (⟨y, hyΓ⟩ : ↥(ggGamma L hND).range) = ⊤ :=
    zpowers_eq_top_of_prime_card hcardΓ hy1
  have hΓz : ∀ a ∈ (ggGamma L hND).range, ∃ k : ℤ, y ^ k = a := by
    intro a ha
    have hmem : (⟨a, ha⟩ : ↥(ggGamma L hND).range) ∈
        Subgroup.zpowers (⟨y, hyΓ⟩ : ↥(ggGamma L hND).range) := by
      rw [hzΓ]
      exact Subgroup.mem_top _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hfix : fixSubgroup y = (L ⊓ Subgroup.centralizer (D : Set G)).subgroupOf L := by
    ext l
    rw [mem_fixSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_iff]
    constructor
    · intro hl
      refine ⟨l.2, fun e he => ?_⟩
      obtain ⟨k, hk⟩ := hΓz (ggGamma L hND ⟨e, he⟩) (MonoidHom.mem_range.mpr ⟨⟨e, he⟩, rfl⟩)
      have hst : y ∈ MulAction.stabilizer (MulAut ↥L) l := by
        rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
        exact hl
      have hstk : y ^ k ∈ MulAction.stabilizer (MulAut ↥L) l := Subgroup.zpow_mem _ hst k
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, hk] at hstk
      have hcoe := congrArg (fun z : ↥L => (z : G)) hstk
      simp only [ggGamma_coe] at hcoe
      calc e * (l : G) = e * (l : G) * e⁻¹ * e := by group
        _ = (l : G) * e := by rw [hcoe]
    · rintro ⟨-, hc⟩
      obtain ⟨e₀, he₀⟩ := MonoidHom.mem_range.mp hyΓ
      apply Subtype.ext
      rw [← he₀, ggGamma_coe]
      have := hc (e₀ : G) e₀.2
      rw [this]
      group
  have hJopen : CFSG.Open.IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    CFSG.Assembly.isComponentOf_iff_open.mp hJ_comp
  have hJ'comp : CFSG.Open.IsComponentOf (J.subgroupOf L) (fixSubgroup y) := by
    rw [hfix]
    exact ⟨Subgroup.comap_mono hJopen.1, hJopen.2.1.comap L.subtype,
      CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ_le_L) hJopen.2.2⟩
  have hJ'layer : ∀ Q : Subgroup ↥L, CFSG.Open.IsComponentOf Q (fixSubgroup y) →
      Q ≤ J.subgroupOf L := by
    intro Q hQ
    have hmap : (fixSubgroup y).map L.subtype = L ⊓ Subgroup.centralizer (D : Set G) := by
      rw [hfix]
      exact Subgroup.map_subgroupOf_eq_of_le inf_le_left
    have hQG : CFSG.Open.IsComponentOf (Q.map L.subtype) (L ⊓ Subgroup.centralizer (D : Set G)) := by
      rw [← hmap]
      exact ⟨Subgroup.map_mono hQ.1, CFSG.Open.IsSubnormal.map L.subtype hQ.2.1,
        CFSG.Open.IsQuasisimple.of_mulEquiv
          (Q.equivMapOfInjective L.subtype L.subtype_injective).symm hQ.2.2⟩
    have hle : Q.map L.subtype ≤ J := by
      rw [hJ_layer]
      exact le_sSup (CFSG.Assembly.isComponentOf_iff_open.mpr hQG)
    intro q hq
    exact Subgroup.mem_subgroupOf.2 (hle ⟨q, hq, rfl⟩)
  have hcount : p ^ 2 * Nat.card ↥((ggGamma L hN).range ⊓
      ⨅ j : ↥(J.subgroupOf L), MulAction.stabilizer (MulAut ↥L) (j : ↥L)) ≤
      Nat.card ↥(ggGamma L hN).range := by
    have hfixJ : (ggGamma L hN).range ⊓
        ⨅ j : ↥(J.subgroupOf L), MulAction.stabilizer (MulAut ↥L) (j : ↥L) =
        ggFixingJ L J (ggGamma L hN).range := by
      ext g
      simp only [ggFixingJ, Subgroup.mem_inf, Subgroup.mem_iInf]
      constructor
      · rintro ⟨hgA, hg⟩
        exact ⟨hgA, fun l => hg ⟨l.1, Subgroup.mem_subgroupOf.2 l.2⟩⟩
      · rintro ⟨hgA, hg⟩
        exact ⟨hgA, fun j => hg ⟨j.1, Subgroup.mem_subgroupOf.1 j.2⟩⟩
    rw [hfixJ]
    exact ggTBJ_card_fixingJ_mul_le hcfg hN
  exact ⟨y, hΓA hyΓ, hy1', hJ'comp, hcount⟩

theorem ggTBJ_noPElt_center_of_not_dvd {L' : Type} [Group L'] [Finite L'] {p : ℕ} [Fact p.Prime]
    (h : ¬ p ∣ Nat.card (Subgroup.center L')) :
    ∀ z ∈ Subgroup.center L', z ^ p = 1 → z = 1 := by
  intro z hz hzp
  by_contra hz1
  have hd : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
  have h1 : orderOf z ≠ 1 := fun h' => hz1 (orderOf_eq_one_iff.mp h')
  have hpz : orderOf z = p := ((Nat.dvd_prime (Fact.out : p.Prime)).mp hd).resolve_left h1
  exact h (hpz ▸ Subgroup.orderOf_dvd_natCard _ hz)

end CFSG.StandardType

end
