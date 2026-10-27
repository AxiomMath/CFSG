module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Mc
public import CFSG.GroupTheory.ABGLocalTools.ZJFactorization
public import CFSG.RankThree.PartOne.KE8F.HyperGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 TheoremCAt SigmaOne4)

variable {G : Type} [Group G] [Finite G]

theorem exists_frattini_of_isPConstrained {X : Type} [Group X] [Finite X] {r : ℕ} [Fact r.Prime]
    (hX : IsPConstrained r X) {S E : Subgroup X} (hS : IsSylowOf r S ⊤) (hES : E ≤ S)
    (hEc : ∀ e ∈ E, ∀ s ∈ S, e * s = s * e) :
    ∃ P : Subgroup X, E ≤ P ∧ IsPGroup r P ∧
      CFSG.pPrimeCore r X ⊔ normalizer (P : Set X) = ⊤ := by
  classical
  haveI hNn : (CFSG.Op_p'p r X).Normal := CFSG.Op_p'p_normal r X
  have hSyl : IsSylowOf r (S ⊓ CFSG.Op_p'p r X) (CFSG.Op_p'p r X) :=
    hS.inf_of_le_normalizer le_top (by rw [normalizer_eq_top_iff.mpr hNn])
  have hEP : E ≤ S ⊓ CFSG.Op_p'p r X := by
    refine le_inf hES fun e he => ?_
    refine hX (S ⊓ CFSG.Op_p'p r X) hSyl ?_
    rw [mem_centralizer_iff]
    intro h hh
    exact (hEc e he h hh.1).symm
  refine ⟨S ⊓ CFSG.Op_p'p r X, hEP, hSyl.isPGroup, ?_⟩
  obtain ⟨Q, hQ⟩ := id hSyl
  have hfrat := Sylow.normalizer_sup_eq_top Q
  rw [hQ] at hfrat
  have hsup : CFSG.pPrimeCore r X ⊔ (S ⊓ CFSG.Op_p'p r X) = CFSG.Op_p'p r X :=
    (sup_eq_Op_p'p_iff_isSylowOf hSyl.isPGroup).2 hSyl
  have hN : CFSG.Op_p'p r X ≤
      CFSG.pPrimeCore r X ⊔ normalizer ((S ⊓ CFSG.Op_p'p r X : Subgroup X) : Set X) := by
    calc CFSG.Op_p'p r X = CFSG.pPrimeCore r X ⊔ (S ⊓ CFSG.Op_p'p r X) := hsup.symm
      _ ≤ _ := sup_le_sup_left le_normalizer _
  refine top_le_iff.1 ?_
  rw [← hfrat]
  exact sup_le le_sup_right hN

omit [Finite G] in
theorem coe_mem_normalizer_map_subtype {X : Subgroup G} {K : Subgroup X} {n : X}
    (hn : n ∈ normalizer (K : Set X)) :
    (n : G) ∈ normalizer ((K.map X.subtype : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hn ⊢
  intro g
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨n * k * n⁻¹, (hn k).1 hk, by simp⟩
  · rintro ⟨k, hk, hkg⟩
    refine ⟨n⁻¹ * k * n, (hn (n⁻¹ * k * n)).2 ?_, ?_⟩
    · rwa [show n * (n⁻¹ * k * n) * n⁻¹ = k by group]
    · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hkg ⊢
      rw [hkg]
      group

namespace Mc614

variable {c : Mc614 G}

theorem E_ne_bot (c : Mc614 G) : c.E ≠ ⊥ := by
  intro h
  have : c.r ^ 2 = 1 := by rw [← c.d.E_card, h]; exact Subgroup.card_bot
  rcases pow_eq_one_iff.1 this with h1 | h1
  · exact c.d.prime.ne_one h1
  · exact two_ne_zero h1

theorem le_M_of_isPConstrained {Z : Subgroup G} (hZ : c.IsZ Z)
    (h69 : R6_9 (dataOfSetup4 c.hS c.hU c.S)) {X : Subgroup G} (hEX : c.E ≤ X)
    (hX : IsPConstrained c.r X) : X ≤ c.M := by
  classical
  haveI : Fact c.r.Prime := ⟨c.d.prime⟩
  have hE1 := c.E_ne_bot
  have hEp : IsPGroup c.r c.E := IsElemAbelian.isPGroup c.d.E_el
  obtain ⟨S, hS, hES⟩ := exists_isSylowOf_ge hEX hEp
  have hSp : IsPGroup c.r S := hS.isPGroup
  have hSN : normalizer (S : Set G) ≤ c.M :=
    c.d.normalizer_le_of_le_pGroup c.hC le_rfl hE1 hES hSp
  have hSM : S ≤ c.M := fun s hs => hSN (Subgroup.le_normalizer hs)
  have hEc : ∀ e ∈ c.E, ∀ s ∈ S, e * s = s * e := by
    obtain ⟨k, -, hk⟩ := exists_conj_le_of_isSylowOf c.d.sylow hSM hSp
    intro e he s hs
    have h16 := hZ.sixteen h69
    have hek : k⁻¹ * e * k ∈ c.R := hk e (hES he)
    have heo : (k⁻¹ * e * k) ^ c.r = 1 := by
      have h1 : e ^ c.r = 1 := c.d.E_el.2 e he
      have h3 := conj_pow (a := k⁻¹) (b := e) (i := c.r)
      rw [inv_inv] at h3
      rw [h3, h1]
      group
    have heA := h16.2 _ hek heo
    have hsk : k⁻¹ * s * k ∈ c.R := hk s hs
    have h2 := h16.1 _ heA _ hsk
    calc e * s = k * ((k⁻¹ * e * k) * (k⁻¹ * s * k)) * k⁻¹ := by group
      _ = k * ((k⁻¹ * s * k) * (k⁻¹ * e * k)) * k⁻¹ := by rw [h2]
      _ = s * e := by group
  have hSX : IsSylowOf c.r (S.subgroupOf X) (⊤ : Subgroup X) := by
    refine (isSylowOf_map_subtype_iff (p := c.r) X).1 ?_
    rw [map_subgroupOf_eq_of_le hS.le, ← MonoidHom.range_eq_map, range_subtype]
    exact hS
  have hESX : c.E.subgroupOf X ≤ S.subgroupOf X := fun x hx => hES hx
  have hEcX : ∀ e ∈ c.E.subgroupOf X, ∀ s ∈ S.subgroupOf X, e * s = s * e := fun e he s hs =>
    Subtype.ext (hEc e he s hs)
  obtain ⟨PX, hEPX, hPXp, hfrat⟩ := exists_frattini_of_isPConstrained hX hSX hESX hEcX
  have hPp : IsPGroup c.r (PX.map X.subtype) := hPXp.map X.subtype
  have hEP : c.E ≤ PX.map X.subtype := fun e he => ⟨⟨e, hEX he⟩, hEPX he, rfl⟩
  have hNP : normalizer ((PX.map X.subtype : Subgroup G) : Set G) ≤ c.M :=
    c.d.normalizer_le_of_le_pGroup c.hC le_rfl hE1 hEP hPp
  have hNXM : ∀ n ∈ normalizer (PX : Set X), (n : G) ∈ c.M := fun n hn =>
    hNP (coe_mem_normalizer_map_subtype hn)
  have hYM : ∀ y ∈ CFSG.pPrimeCore c.r X, (y : G) ∈ c.M := by
    set Y : Subgroup G := (CFSG.pPrimeCore c.r X).map X.subtype with hY
    have hcop : ¬ c.r ∣ Nat.card Y := by
      rw [hY, Subgroup.card_map_of_injective X.subtype_injective]
      exact (Nat.Prime.coprime_iff_not_dvd c.d.prime).1 CFSG.pPrimeCore_coprime_card
    have hEnorm : c.E ≤ normalizer (Y : Set G) := fun e he => by
      have hn : (⟨e, hEX he⟩ : X) ∈ normalizer ((CFSG.pPrimeCore c.r X : Subgroup X) : Set X) := by
        rw [normalizer_eq_top_iff.mpr (CFSG.pPrimeCore_normal (p := c.r) (G := X))]
        exact mem_top _
      exact coe_mem_normalizer_map_subtype hn
    haveI : CFSG.IsElementaryAbelian c.r c.E := c.d.E_el.isElementaryAbelian
    haveI : Nontrivial c.E := (Subgroup.nontrivial_iff_ne_bot c.E).2 hE1
    have hgen := CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers (p := c.r)
      (A := c.E) (V := Y) hEnorm hcop
    have hYle : Y ≤ c.M := by
      refine hgen.trans (iSup₂_le fun B hB => ?_)
      have hBcard : Nat.card B = c.r := by
        have h1 := Subgroup.card_mul_index B
        rw [hB, c.d.E_card] at h1
        have hr0 : 0 < c.r := c.d.prime.pos
        have : Nat.card B * c.r = c.r * c.r := by rw [h1]; ring
        exact Nat.eq_of_mul_eq_mul_right hr0 this
      set B' : Subgroup G := B.map c.E.subtype with hB'
      have hB'E : B' ≤ c.E := map_subtype_le B
      have hB'card : Nat.card B' = c.r := by
        rw [hB', Subgroup.card_map_of_injective c.E.subtype_injective, hBcard]
      have hB'1 : B' ≠ ⊥ := by
        intro h
        have : c.r = 1 := by rw [← hB'card, h]; exact Subgroup.card_bot
        exact c.d.prime.ne_one this
      have hB'p : IsPGroup c.r B' := hEp.to_le hB'E
      have hN : normalizer (B' : Set G) ≤ c.M :=
        (CFSG.RankThreeCoreUniqueness.Helpers.gamma_normalizer_le 1 c.r c.E B' hB'E
          (one_le_pRank_of_ne_bot c.d.prime hB'p hB'1)).trans c.d.E_gamma
      exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer (B' : Set G)).trans hN)
    exact fun y hy => hYle ⟨y, hy, rfl⟩
  intro x hx
  have htop : (⟨x, hx⟩ : X) ∈ (⊤ : Subgroup X) := mem_top _
  rw [← hfrat] at htop
  obtain ⟨y, hy, n, hn, hxyn⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := CFSG.pPrimeCore c.r X) (t := normalizer (PX : Set X))).1
      htop
  have hx' : x = (y : G) * (n : G) := congrArg Subtype.val hxyn.symm
  rw [hx']
  exact c.M.mul_mem (hYM y hy) (hNXM n hn)

end Mc614

end CFSG.LocalAnalysis.UniquenessCase.UC6
