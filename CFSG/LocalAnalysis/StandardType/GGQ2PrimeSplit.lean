module

public import CFSG.LocalAnalysis.StandardType.GGQ2PrimeTransport
public import CFSG.LocalAnalysis.StandardType.GGSecFiveIdentDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieRowY1OutUniRank
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGSpJoinNbrModel
public import CFSG.LocalAnalysis.ComponentClassification.BurgoyneProjSlice
public import CFSG.LocalAnalysis.ComponentClassification.InnAutDerivedUnitary

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open CFSG.Models CFSG.Assembly CFSG.StandardType

@[expose] def O2Z {G : Type} [Group G] (L : Subgroup G) : Subgroup G where
  carrier := {g | g ∈ L ∧ (∀ y ∈ L, g * y = y * g) ∧ g ^ (2 ^ Nat.card G) = 1}
  one_mem' := ⟨one_mem _, fun y _ => by simp, one_pow _⟩
  mul_mem' := by
    rintro a b ⟨haL, hac, ha2⟩ ⟨hbL, hbc, hb2⟩
    refine ⟨mul_mem haL hbL, fun y hy => ?_, ?_⟩
    · rw [mul_assoc, hbc y hy, ← mul_assoc, hac y hy, mul_assoc]
    · rw [(Commute.mul_pow (hac b hbL) _), ha2, hb2, one_mul]
  inv_mem' := by
    rintro a ⟨haL, hac, ha2⟩
    refine ⟨inv_mem haL, fun y hy => ?_, by rw [inv_pow, ha2, inv_one]⟩
    have := hac y hy
    calc a⁻¹ * y = a⁻¹ * (y * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * y) * a⁻¹ := by rw [this]
      _ = y * a⁻¹ := by group

theorem O2Z_two {G : Type} [Group G] [Finite G] (L : Subgroup G) : IsPGroup 2 (O2Z L) := fun g =>
  ⟨Nat.card G, Subtype.ext (by simpa using g.2.2.2)⟩

theorem L_le_cent_O2Z {G : Type} [Group G]
    (L : Subgroup G) : L ≤ centralizer (O2Z L : Set G) := fun y hy => by
  rw [mem_centralizer_iff]
  intro g hg
  exact (hg.2.1 y hy)

theorem norm_le_norm_O2Z {G : Type} [Group G] (L : Subgroup G) :
    normalizer (L : Set G) ≤ normalizer (O2Z L : Set G) := by
  intro n hn
  have hL : ∀ y, y ∈ L ↔ n * y * n⁻¹ ∈ L := mem_normalizer_iff.1 hn
  have key : ∀ g ∈ O2Z L, n * g * n⁻¹ ∈ O2Z L := by
    rintro g ⟨hgL, hgc, hg2⟩
    refine ⟨(hL g).1 hgL, fun y hy => ?_, ?_⟩
    · have hy' : n⁻¹ * y * n ∈ L := by
        have := (hL (n⁻¹ * y * n)).2
        apply this
        simpa [mul_assoc] using hy
      have e := hgc _ hy'
      calc n * g * n⁻¹ * y = n * (g * (n⁻¹ * y * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * y * n) * g) * n⁻¹ := by rw [e]
        _ = y * (n * g * n⁻¹) := by group
    · rw [conj_pow, hg2, mul_one, mul_inv_cancel]
  have key' : ∀ g ∈ O2Z L, n⁻¹ * g * n ∈ O2Z L := by
    rintro g ⟨hgL, hgc, hg2⟩
    have hL' : n⁻¹ ∈ normalizer (L : Set G) := inv_mem hn
    have hL2 : ∀ y, y ∈ L ↔ n⁻¹ * y * n⁻¹⁻¹ ∈ L := mem_normalizer_iff.1 hL'
    refine ⟨by simpa using (hL2 g).1 hgL, fun y hy => ?_, ?_⟩
    · have hy' : n * y * n⁻¹ ∈ L := (hL y).1 hy
      have e := hgc _ hy'
      calc n⁻¹ * g * n * y = n⁻¹ * (g * (n * y * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * y * n⁻¹) * g) * n := by rw [e]
        _ = y * (n⁻¹ * g * n) := by group
    · have : n⁻¹ * g * n = n⁻¹ * g * n⁻¹⁻¹ := by rw [inv_inv]
      rw [this, conj_pow, hg2, mul_one]; group
  rw [mem_normalizer_iff]
  intro g
  refine ⟨key g, fun h => ?_⟩
  have := key' _ h
  simpa [mul_assoc] using this

theorem O2Z_ne_bot {G : Type} [Group G] [Finite G]
    {L : Subgroup G} (hev : ¬ Odd (Nat.card (center L))) : O2Z L ≠ ⊥ := by
  have h2 : 2 ∣ Nat.card (center L) := by
    rcases Nat.even_or_odd (Nat.card (center L)) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hev
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc⟩ : ∃ c : center L, orderOf c = 2 := exists_prime_orderOf_dvd_card' 2 h2
  have hc2 : c ^ 2 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hcL : ∀ y : L, (c : L) * y = y * (c : L) := fun y => ((mem_center_iff.1 c.2) y).symm
  have hg2 : ((c : L) : G) ^ 2 = 1 := by
    have := congrArg (fun t : center L => ((t : L) : G)) hc2
    simpa using this
  have hgmem : ((c : L) : G) ∈ O2Z L := by
    refine ⟨(c : L).2, fun y hy => congrArg Subtype.val (hcL ⟨y, hy⟩), ?_⟩
    have hN : 2 ∣ 2 ^ Nat.card G := dvd_pow_self 2 (Nat.card_pos.ne')
    obtain ⟨k, hk⟩ := hN
    rw [hk, pow_mul, hg2, one_pow]
  intro hbot
  rw [hbot, mem_bot] at hgmem
  have : c = 1 := Subtype.ext (Subtype.ext hgmem)
  rw [this, orderOf_one] at hc
  exact absurd hc (by norm_num)

theorem noncyclic_three_of_U62 {G : Type} [Group G] [Finite G] {L : Subgroup G}
    (hm : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) :
    ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : StatedClassicalModel (L ⧸ center L) .PSU 6 2 1 := by
    rcases hm with ⟨-, h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;>
      first | exact h | exact absurd h (by norm_num)
  obtain ⟨K, hF, hfin, hK, ⟨e⟩⟩ := hc.2
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, le_refl 1, by rw [hK]; norm_num⟩
  obtain ⟨E, hEab, hEc⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.KD264Lie.exists_elemAbelian_card_81_unitary hU
      (by norm_num) (m := 6) (by norm_num)
  set F : Subgroup (L ⧸ center L) := E.map e.symm.toMonoidHom with hFdef
  have hFE : F ≃* E := (E.equivMapOfInjective _ e.symm.injective).symm
  have hFp : IsPGroup 3 F := fun g => ⟨1, by
    rw [pow_one]
    apply hFE.injective
    rw [map_pow, map_one]
    exact Subtype.ext (by simpa using hEab.2 _ (hFE g).2)⟩
  have hFnc : ¬ IsCyclic F := by
    intro hcyc
    have hEcyc : IsCyclic E := isCyclic_of_surjective hFE.toMonoidHom hFE.surjective
    have hexp : Monoid.exponent E ∣ 3 :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (by simpa using hEab.2 _ g.2)
    rw [IsCyclic.exponent_eq_card, hEc] at hexp
    norm_num at hexp
  exact exists_noncyclic_of_noncyclic_quot (QuotientGroup.mk' (center L))
    (QuotientGroup.mk'_surjective _) hFp hFnc

theorem L_norm_of_U62 {G : Type} [Group G] [Finite G]
    {B L : Subgroup G} {x : G} (hG : GGThmIHyp 3 B x L)
    (hm : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) :
    centralizer ({x} : Set G) ≤ normalizer (L : Set G) := by
  obtain ⟨-, -, -, hLc, hcyc, -⟩ := ggThmIHyp_unpack hG
  obtain ⟨S, hSL, hSp, hSnc⟩ := noncyclic_three_of_U62 hm
  exact component_normal hLc hcyc hSL hSp hSnc

structure Q2pSetting {G : Type} [Group G] [Finite G]
    (B Bs : Subgroup G) (x : G) (L : Subgroup G) : Prop where
  hyp : GGThmIHyp 3 B x L
  bstar : GGBstar 3 B Bs
  Bs_card : Nat.card Bs = 3 ^ 6
  Bs_norm : Bs ≤ normalizer (L : Set G)
  model : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1

theorem cor_9_5 {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L : Subgroup G} (h : Q2pSetting B Bs x L)
    (hev : ¬ Odd (Nat.card (center L))) : Bs = B ∧ twoLocalPrimeRank 3 G = 6 := by
  obtain ⟨-, -, -, -, -, -, hSS, -⟩ := h.hyp
  obtain ⟨hBmax, -⟩ := hSS
  obtain ⟨hEq, h6⟩ := bstar_eq_of_normalizes hBmax h.bstar (O2Z_ne_bot hev) (O2Z_two L)
    (h.Bs_norm.trans (norm_le_norm_O2Z L))
  exact ⟨hEq, h6 h.Bs_card⟩

structure O1pRest {G : Type} [Group G] (B : Subgroup G) (x : G) (L : Subgroup G) (g : Fin 3 → G)
    (χ0 : B →* Multiplicative (ZMod 3)) (X Xk : Subgroup G) : Prop where
  T_card : Nat.card (O2Z L) = 4
  lemma81 : ∀ b (hb : b ∈ B), b ∈ centralizer (O2Z L : Set G) ↔ χ0 ⟨b, hb⟩ = 1
  g0 : g 0 = 1
  g_norm : ∀ i, g i ∈ normalizer (B : Set G)
  coord : ∀ i j (hb : (g j)⁻¹ * zT g x i * g j ∈ B), χ0 ⟨_, hb⟩ = if i = j then 1 else ω3
  X_model : LieModel X .PSU 5 2 1
  X_le : X ≤ L ⊓ centralizer ({zT g x 1} : Set G)
  X_split : ∀ h ∈ L ⊓ centralizer ({zT g x 1} : Set G),
    ∃ c ∈ L ⊓ centralizer (L : Set G), ∃ y ∈ X, h = c * y
  X_le_L1 : X ≤ LT g L 1
  B_cent_X : B ⊓ centralizer (X : Set G) = closure {x, x * (zT g x 1)⁻¹}
  Xk_model : LieModel Xk .PSU 4 2 1
  Xk_le : Xk ≤ X ⊓ centralizer ({zT g x 2} : Set G)
  Xk_le_L2 : Xk ≤ LT g L 2
  F14 : ∀ α : MulAut X, (∀ y : X, (y : G) ∈ Xk → α y = y) → α ^ 3 = 1

theorem o1pAt_of_setting {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L : Subgroup G} {g : Fin 3 → G}
    {χ0 : B →* Multiplicative (ZMod 3)} {X Xk : Subgroup G} (h : Q2pSetting B Bs x L)
    (hr : O1pRest B x L g χ0 X Xk) : O1pAt B Bs x L (O2Z L) g χ0 X Xk where
  hyp := h.hyp
  bstar := h.bstar
  Bs_card := h.Bs_card
  Bs_norm := h.Bs_norm.trans (norm_le_norm_O2Z L)
  g0 := hr.g0
  g_norm := hr.g_norm
  coord := hr.coord
  L_norm := L_norm_of_U62 h.hyp h.model
  T_card := hr.T_card
  T_cent := L_le_cent_O2Z L
  T_char := norm_le_norm_O2Z L
  lemma81 := hr.lemma81
  X_model := hr.X_model
  X_le := hr.X_le
  X_split := hr.X_split
  X_le_L1 := hr.X_le_L1
  B_cent_X := hr.B_cent_X
  Xk_model := hr.Xk_model
  Xk_le := hr.Xk_le
  Xk_le_L2 := hr.Xk_le_L2
  F14 := hr.F14

theorem q2p_of_rest {G : Type} [Group G] [Finite G] (hL : GGLBalanceInput) (hI : PumpUpLieInputs)
    {B Bs : Subgroup G} {x : G} {L : Subgroup G} (h : Q2pSetting B Bs x L)
    (hrest : ¬ Odd (Nat.card (center L)) →
      ∃ (g : Fin 3 → G) (χ0 : B →* Multiplicative (ZMod 3)) (X Xk : Subgroup G),
        O1pRest B x L g χ0 X Xk) :
    Odd (Nat.card (center L)) := by
  by_contra hev
  obtain ⟨g, χ0, X, Xk, hr⟩ := hrest hev
  exact o1p_at_false hL hI (o1pAt_of_setting h hr)

theorem q2pSetting_of_routeCfg {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hcard : Nat.card Bs = 3 ^ 6) (hm : CFSG.Blueprint.LieModel (L ⧸ center L) .PSU 6 2 1) :
    Q2pSetting B Bs x L := by
  obtain ⟨⟨⟨hyp, hbs, -⟩, -, ⟨hid, -⟩, -⟩, -⟩ := hcfg
  exact ⟨hyp, hbs, hcard, hid.le_normalizer, hm⟩

end CFSG.GGQ2Prime
