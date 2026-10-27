module

public import CFSG.LocalAnalysis.UniquenessCase.UC6G.Mc
public import CFSG.LocalAnalysis.UniquenessCase.UC6S18

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6G

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.LocalAnalysis.UniquenessCase.UC6
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.Yardstones.Mf4cdcdf2e013 (TheoremCAt)

variable {G : Type} [Group G] [Finite G] {Dat : Data G}

namespace Mc614

variable {c : Mc614 Dat}

theorem E_ne_bot (c : Mc614 Dat) : c.E ≠ ⊥ := by
  intro h
  have : c.r ^ 2 = 1 := by rw [← c.d.E_card, h]; exact Subgroup.card_bot
  rcases pow_eq_one_iff.1 this with h1 | h1
  · exact c.d.prime.ne_one h1
  · exact two_ne_zero h1

theorem le_M_of_isPConstrained {Z : Subgroup G} (hZ : c.IsZ Z)
    (h69 : R6_9 Dat) {X : Subgroup G} (hEX : c.E ≤ X)
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

end CFSG.LocalAnalysis.UniquenessCase.UC6G
