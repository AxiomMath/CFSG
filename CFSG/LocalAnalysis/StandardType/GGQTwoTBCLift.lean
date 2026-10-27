module

public import CFSG.LocalAnalysis.StandardType.GGQTwoTBCCoreDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXGraphLin
public import CFSG.GroupTheory.SupCommute
public import CFSG.LocalAnalysis.StandardType.GGTPNDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

private lemma ggQ2tbc_coroot_mem_E [Fact (Nat.Prime 3)]
    (hS : GGQTwoSetting 3 B Bs x L D J) (M : GGQ2LDatum 3 Bs L x) (i : M.Λ) :
    M.coroot i ∈ ggQ2gl_E M L := by
  obtain ⟨hcfg, -, -, -, -⟩ := hS.1
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hBsEA : CFSG.Open.IsElemAbelian 3 Bs := hBstar.2.1
  have hNL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    ggInnerDiagOn_le_normalizer hS.1.2.2.1.1
  have hsimp : M.simple i ∈ ggAutomizer L Bs := by
    rw [M.automizer_L]
    exact Subgroup.subset_closure ⟨i, rfl⟩
  obtain ⟨g, hgL, hgN, hgapp⟩ := mem_ggAutomizer_iff.mp hsimp
  let c : ↥Bs := Additive.toMul (M.model.symm (M.coroot i))
  have hcval : M.model (Additive.ofMul c) = M.coroot i := by
    simp [c]
  let b : ↥Bs := Additive.toMul (M.model.symm ((2 : ZMod 3) • M.coroot i))
  have hbval : M.model (Additive.ofMul b) = (2 : ZMod 3) • M.coroot i := by
    simp [b]
  have hroot : M.root i ((2 : ZMod 3) • M.coroot i) = 1 := by
    rw [map_smul, M.pairing i i, M.isCartan.1]
    rfl
  have hsimple : M.simple i b = c := by
    apply Additive.ofMul.injective
    apply M.model.injective
    rw [← ggLin_apply_ofMul (p := 3) M.model (M.simple i) b]
    calc ggLin (p := 3) M.model (M.simple i) (M.model (Additive.ofMul b))
        = (2 : ZMod 3) • M.coroot i - M.root i ((2 : ZMod 3) • M.coroot i) •
            M.coroot i := by rw [hbval, M.simple_apply i]
      _ = (2 : ZMod 3) • M.coroot i - M.coroot i := by rw [hroot, one_smul]
      _ = M.coroot i := by rw [two_smul (ZMod 3), add_sub_cancel_right]
      _ = M.model (Additive.ofMul c) := hcval.symm
  have hb_eq : b = c ^ 2 := by
    apply Additive.ofMul.injective
    apply M.model.injective
    have h2 : (2 : ZMod 3) • M.coroot i = (2 : ℕ) • M.coroot i :=
      Nat.cast_smul_eq_nsmul (ZMod 3) 2 _
    rw [hbval, ofMul_pow, map_nsmul, hcval]
    exact h2
  have hcG : (c : G) = g * (b : G) * g⁻¹ := by
    have h := hgapp b
    rwa [hsimple] at h
  have hb_eqG : (b : G) = (c : G) ^ 2 := by
    rw [hb_eq, Subgroup.coe_pow]
  have hbinv : (b : G)⁻¹ * g⁻¹ * (b : G) ∈ L := by
    have hbN : (b : G) ∈ Subgroup.normalizer (L : Set G) := hNL b.2
    have hbNinv : (b : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hbN
    have h := (Subgroup.mem_normalizer_iff.mp hbNinv) (g⁻¹)
    have hbin : (b : G)⁻¹ * g⁻¹ * (b : G)⁻¹⁻¹ ∈ L := h.mp (L.inv_mem hgL)
    simpa using hbin
  have hformula : (c : G) = g * (b : G)⁻¹ * g⁻¹ * (b : G) := by
    have hcinv : g * (b : G)⁻¹ * g⁻¹ = (c : G)⁻¹ := by
      rw [hcG]
      group
    calc (c : G) = (c : G)⁻¹ * (c : G) ^ 2 := by group
      _ = (g * (b : G)⁻¹ * g⁻¹) * (b : G) := by rw [hcinv, hb_eqG]
      _ = g * (b : G)⁻¹ * g⁻¹ * (b : G) := by group
  have hcL : (c : G) ∈ L := by
    rw [hformula]
    have hassoc : g * (b : G)⁻¹ * g⁻¹ * (b : G) =
        g * ((b : G)⁻¹ * g⁻¹ * (b : G)) := by group
    rw [hassoc]
    exact L.mul_mem hgL hbinv
  exact (ggQ2gl_mem_E M L).mpr ⟨c, hcL, hcval⟩

private lemma ggQ2tbc_coSpan_le_E [Fact (Nat.Prime 3)]
    (hS : GGQTwoSetting 3 B Bs x L D J) (M : GGQ2LDatum 3 Bs L x) :
    M.coSpan ≤ ggQ2gl_E M L := by
  rw [GGQ2LDatum.coSpan]
  exact Submodule.span_le.mpr
    (Set.range_subset_iff.mpr fun i => ggQ2tbc_coroot_mem_E hS M i)

private lemma ggQ2tbc_E_eq_coSpan [Fact (Nat.Prime 3)]
    (hS : GGQTwoSetting 3 B Bs x L D J) (M : GGQ2LDatum 3 Bs L x) (hM : M.ShapeFull) :
    ggQ2gl_E M L = M.coSpan := by
  have hxE : M.xV ∉ ggQ2gl_E M L := by
    intro hmem
    obtain ⟨b, hbL, hbval⟩ := (ggQ2gl_mem_E M L).mp hmem
    have hb : b = ⟨x, M.hx⟩ := by
      apply Additive.ofMul.injective
      apply M.model.injective
      rw [hbval]
      rfl
    exact hM.1 (by simpa [hb] using hbL)
  refine le_antisymm ?_ (ggQ2tbc_coSpan_le_E hS M)
  intro v hv
  have hvsup : v ∈ M.coSpan ⊔ Submodule.span (ZMod 3) ({M.xV} : Set M.V) := by
    rw [hM.2.2.2]
    exact Submodule.mem_top
  rw [Submodule.mem_sup'] at hvsup
  obtain ⟨y, z, hyz⟩ := hvsup
  have hzmem : (z : M.V) ∈ Submodule.span (ZMod 3) ({M.xV} : Set M.V) := z.2
  rw [Submodule.mem_span_singleton] at hzmem
  obtain ⟨t, ht⟩ := hzmem
  have hzE : (z : M.V) ∈ ggQ2gl_E M L := by
    have hzv : (z : M.V) = v - (y : M.V) := by
      rw [← hyz]
      abel
    rw [hzv]
    exact Submodule.sub_mem _ hv (ggQ2tbc_coSpan_le_E hS M y.2)
  have ht0 : t = 0 := by
    by_contra ht0
    apply hxE
    have hx : M.xV = t⁻¹ • (z : M.V) := by
      rw [← ht]
      exact (inv_smul_smul₀ ht0 M.xV).symm
    rw [hx]
    exact Submodule.smul_mem _ _ hzE
  have hz0 : (z : M.V) = 0 := by
    rw [← ht, ht0, zero_smul]
  have hvy : v = (y : M.V) := by
    rw [← hyz, hz0, add_zero]
  rw [hvy]
  exact y.2

private lemma ggQ2tbc_card_H [Fact (Nat.Prime 3)]
    (hS : GGQTwoSetting 3 B Bs x L D J) (M : GGQ2LDatum 3 Bs L x) (hM : M.ShapeFull) :
    Nat.card ↥(Bs ⊓ L) = 3 ^ Fintype.card M.Λ := by
  have hfinV : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have hfinE : Finite ↥(M.coSpan) :=
    Finite.of_injective (fun v : ↥(M.coSpan) => (v : M.V))
      (fun _ _ h => Subtype.ext h)
  have hEH : ggQ2gl_E M L = ggQ2gl_E M (Bs ⊓ L) := by
    ext v
    rw [ggQ2gl_mem_E M L, ggQ2gl_mem_E M (Bs ⊓ L)]
    constructor
    · rintro ⟨b, hbL, hbv⟩
      exact ⟨b, ⟨b.2, hbL⟩, hbv⟩
    · rintro ⟨b, hb, hbv⟩
      exact ⟨b, hb.2, hbv⟩
  have hcardEH : Nat.card ↥(ggQ2gl_E M L) = Nat.card ↥(Bs ⊓ L) := by
    rw [hEH]
    exact Nat.card_congr (ggQ2gl_E_equiv (D := Bs ⊓ L) M inf_le_left)
  have hfr : Module.finrank (ZMod 3) ↥(M.coSpan) = Fintype.card M.Λ := by
    rw [GGQ2LDatum.coSpan]
    exact finrank_span_eq_card hM.2.1
  rw [← hcardEH, ggQ2tbc_E_eq_coSpan hS M hM, ← hfr]
  exact (@FiniteField.pow_finrank_eq_natCard 3 _ ↥(M.coSpan) _ hfinE _).symm

private lemma ggQ2tbc_decomp [Fact (Nat.Prime 3)]
    (hS : GGQTwoSetting 3 B Bs x L D J) (M : GGQ2LDatum 3 Bs L x) (hM : M.ShapeFull) :
    ∀ b : ↥Bs, ∃ (k : ℕ) (h : ↥Bs), (h : G) ∈ L ∧ b = ⟨x, M.hx⟩ ^ k * h := by
  intro b
  have hE : ggQ2gl_E M L = M.coSpan := ggQ2tbc_E_eq_coSpan hS M hM
  have hvsup : M.model (Additive.ofMul b) ∈
      M.coSpan ⊔ Submodule.span (ZMod 3) ({M.xV} : Set M.V) := by
    rw [hM.2.2.2]
    exact Submodule.mem_top
  rw [Submodule.mem_sup'] at hvsup
  obtain ⟨y, z, hyz⟩ := hvsup
  have hzmem : (z : M.V) ∈ Submodule.span (ZMod 3) ({M.xV} : Set M.V) := z.2
  rw [Submodule.mem_span_singleton] at hzmem
  obtain ⟨t, ht⟩ := hzmem
  have hyE : (y : M.V) ∈ ggQ2gl_E M L := by
    rw [hE]
    exact y.2
  obtain ⟨h, hhL, hhval⟩ := (ggQ2gl_mem_E M L).mp hyE
  refine ⟨t.val, h, hhL, ?_⟩
  have ha_model : M.model (Additive.ofMul (⟨x, M.hx⟩ ^ t.val)) = t.val • M.xV := by
    rw [ofMul_pow, map_nsmul]
    rfl
  have hk : t • M.xV = t.val • M.xV := by
    conv_lhs => rw [← ZMod.natCast_zmod_val t]
    rw [Nat.cast_smul_eq_nsmul]
  have hbval : M.model (Additive.ofMul b) = (y : M.V) + t • M.xV := by
    rw [← hyz, ht]
  apply Additive.ofMul.injective
  apply M.model.injective
  rw [ofMul_mul, map_add, ha_model, hhval, hbval, hk, add_comm]

private lemma ggQ2tbc_P_card [Fact (Nat.Prime 3)]
    (hS : GGQTwoSetting 3 B Bs x L D J) (M : GGQ2LDatum 3 Bs L x) :
    Nat.card ↥(Subgroup.zpowers x) = 3 := by
  obtain ⟨hcfg, -, -, -, -⟩ := hS.1
  obtain ⟨hI, hBstar, -⟩ := hcfg
  have hSstar : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hSstar.2.2.1
  have hx3 : x ^ 3 = 1 := hBstar.2.1.2 x M.hx
  rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]

private lemma ggQ2tbc_P_inf [Fact (Nat.Prime 3)]
    (hS : GGQTwoSetting 3 B Bs x L D J) (M : GGQ2LDatum 3 Bs L x) (hM : M.ShapeFull) :
    Subgroup.zpowers x ⊓ (Bs ⊓ L) = ⊥ := by
  have hPcard : Nat.card ↥(Subgroup.zpowers x) = 3 := ggQ2tbc_P_card hS M
  have hle : Subgroup.zpowers x ⊓ (Bs ⊓ L) ≤ Subgroup.zpowers x := inf_le_left
  have hdvd : Nat.card ↥(Subgroup.zpowers x ⊓ (Bs ⊓ L)) ∣ 3 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [hPcard] at this
  have hne : Nat.card ↥(Subgroup.zpowers x ⊓ (Bs ⊓ L)) ≠ 3 := by
    intro hc
    have heq : Subgroup.zpowers x ⊓ (Bs ⊓ L) = Subgroup.zpowers x :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hPcard])
    have hxH : x ∈ (Bs ⊓ L : Subgroup G) := by
      have hx : x ∈ Subgroup.zpowers x ⊓ (Bs ⊓ L) := by
        rw [heq]
        exact Subgroup.mem_zpowers x
      exact hx.2
    exact hM.1 hxH.2
  have hone : Nat.card ↥(Subgroup.zpowers x ⊓ (Bs ⊓ L)) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact h
    · exact absurd h hne
  exact Subgroup.card_eq_one.mp hone

private lemma ggQ2tbc_P_sup [Fact (Nat.Prime 3)]
    (hS : GGQTwoSetting 3 B Bs x L D J) (M : GGQ2LDatum 3 Bs L x) (hM : M.ShapeFull) :
    Subgroup.zpowers x ⊔ (Bs ⊓ L) = Bs := by
  refine le_antisymm ?_ ?_
  · exact sup_le (Subgroup.zpowers_le.mpr M.hx) inf_le_left
  · intro b hb
    obtain ⟨k, h, hhL, hbk⟩ := ggQ2tbc_decomp hS M hM ⟨b, hb⟩
    have hbG : b = x ^ k * (h : G) := by
      have := congrArg Subtype.val hbk
      simpa [Subgroup.coe_mul] using this
    rw [hbG]
    exact Subgroup.mul_mem_sup
      (Subgroup.pow_mem (Subgroup.zpowers x) (Subgroup.mem_zpowers x) k) ⟨h.2, hhL⟩

private lemma ggQ2tbc_card_Bs [Fact (Nat.Prime 3)]
    (hS : GGQTwoSetting 3 B Bs x L D J) (M : GGQ2LDatum 3 Bs L x) (hM : M.ShapeFull) :
    Nat.card ↥Bs = 3 * Nat.card ↥(Bs ⊓ L) := by
  obtain ⟨hcfg, -, -, -, -⟩ := hS.1
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hBsEA : CFSG.Open.IsElemAbelian 3 Bs := hBstar.2.1
  have hPcard : Nat.card ↥(Subgroup.zpowers x) = 3 := ggQ2tbc_P_card hS M
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ (Bs ⊓ L : Subgroup G), Commute a b := by
    intro a ha b hb
    exact commute_of_mem_of_isMulCommutative (A := Bs) hBsEA.1
      (Subgroup.zpowers_le.mpr M.hx ha) hb.1
  have hcard := CFSG.card_sup_eq_mul_of_commute (Subgroup.zpowers x) (Bs ⊓ L)
    hcomm (ggQ2tbc_P_inf hS M hM)
  rw [ggQ2tbc_P_sup hS M hM, hPcard] at hcard
  exact hcard

private lemma ggQ2tbc_exists_d [Fact (Nat.Prime 3)]
    (hS : GGQTwoSetting 3 B Bs x L D J) (M : GGQ2LDatum 3 Bs L x) (hM : M.ShapeFull) :
    ∃ d : G, d ∈ D ∧ d ∈ Bs ∧ d ∈ L ∧ d ≠ 1 ∧ d ∉ Subgroup.zpowers x ∧
      D = Subgroup.closure ({x, d} : Set G) := by
  obtain ⟨hcfg, -, -, -, -⟩ := hS.1
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hPcard : Nat.card ↥(Subgroup.zpowers x) = 3 := ggQ2tbc_P_card hS M
  have hxD : x ∈ D := hStdSub.1.2.2.2.1
  have hDcard : Nat.card ↥D = 9 := by simpa using hStdSub.1.2.2.1
  have hDIsElem : CFSG.Open.IsElemAbelian 3 D := hStdSub.1.2.1
  have hDP : ¬ D ≤ Subgroup.zpowers x := by
    intro h
    have hle := Subgroup.card_le_of_le h
    rw [hDcard, hPcard] at hle
    omega
  have hDBs : D ≤ Bs := hStdSub.1.1.trans hBstar.1
  have hDP' : ¬ (D : Set G) ⊆ (Subgroup.zpowers x : Set G) := hDP
  obtain ⟨b, hbD, hbP⟩ := Set.not_subset.mp hDP'
  obtain ⟨k, h, hhL, hbk⟩ := ggQ2tbc_decomp hS M hM ⟨b, hDBs hbD⟩
  have hbG : (b : G) = x ^ k * (h : G) := by
    have := congrArg Subtype.val hbk
    simpa [Subgroup.coe_mul] using this
  have hdD : (h : G) ∈ D := by
    have hh : (h : G) = (x ^ k)⁻¹ * (b : G) := by
      rw [hbG]
      group
    rw [hh]
    exact D.mul_mem (D.inv_mem (D.pow_mem hxD k)) hbD
  have hdP : (h : G) ∉ Subgroup.zpowers x := by
    intro hdP
    apply hbP
    rw [hbG]
    exact Subgroup.mul_mem _
      (Subgroup.pow_mem (Subgroup.zpowers x) (Subgroup.mem_zpowers x) k) hdP
  have hd1 : (h : G) ≠ 1 := by
    intro h1
    apply hdP
    rw [h1]
    exact Subgroup.one_mem _
  have hd3 : (h : G) ^ 3 = 1 := hDIsElem.2 (h : G) hdD
  have hdord : orderOf (h : G) = 3 := orderOf_eq_prime hd3 hd1
  have hQcard : Nat.card ↥(Subgroup.zpowers (h : G)) = 3 := by
    rw [Nat.card_zpowers, hdord]
  have hxQ : x ∉ Subgroup.zpowers (h : G) := by
    intro hxQ
    have hle : Subgroup.zpowers x ≤ Subgroup.zpowers (h : G) := Subgroup.zpowers_le.mpr hxQ
    have heq : Subgroup.zpowers x = Subgroup.zpowers (h : G) :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hQcard, hPcard])
    apply hdP
    rw [heq]
    exact Subgroup.mem_zpowers (h : G)
  have hPQinf : Subgroup.zpowers x ⊓ Subgroup.zpowers (h : G) = ⊥ := by
    have hle : Subgroup.zpowers x ⊓ Subgroup.zpowers (h : G) ≤ Subgroup.zpowers x :=
      inf_le_left
    have hdvd : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers (h : G)) ∣ 3 := by
      have := Subgroup.card_dvd_of_le hle
      rwa [hPcard] at this
    have hne : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers (h : G)) ≠ 3 := by
      intro hc
      have heq : Subgroup.zpowers x ⊓ Subgroup.zpowers (h : G) = Subgroup.zpowers x :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hPcard])
      have hx : x ∈ Subgroup.zpowers x ⊓ Subgroup.zpowers (h : G) := by
        rw [heq]
        exact Subgroup.mem_zpowers x
      exact hxQ hx.2
    have hone : Nat.card ↥(Subgroup.zpowers x ⊓ Subgroup.zpowers (h : G)) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact h
      · exact absurd h hne
    exact Subgroup.card_eq_one.mp hone
  have hcomm : ∀ a ∈ Subgroup.zpowers x, ∀ b ∈ Subgroup.zpowers (h : G), Commute a b := by
    intro a ha b hb
    have hxd : Commute x (h : G) :=
      commute_of_mem_of_isMulCommutative hDIsElem.1 hxD hdD
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    exact hxd.zpow_zpow m n
  have hcardPQ : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers (h : G)) = 9 := by
    rw [CFSG.card_sup_eq_mul_of_commute _ _ hcomm hPQinf, hPcard, hQcard]
  have hle : Subgroup.zpowers x ⊔ Subgroup.zpowers (h : G) ≤ D :=
    sup_le (Subgroup.zpowers_le.mpr hxD) (Subgroup.zpowers_le.mpr hdD)
  have hcard : Nat.card ↥D ≤ Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers (h : G)) := by
    rw [hDcard, hcardPQ]
  have hDsup : D = Subgroup.zpowers x ⊔ Subgroup.zpowers (h : G) :=
    (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  refine ⟨(h : G), hdD, h.2, hhL, hd1, hdP, ?_⟩
  rw [hDsup, closure_pair_eq_sup]

omit [Finite G] in
private lemma ggQ2tbc_centralizer_eq {d : G} (hdD : d ∈ D)
    (hDcl : D = Subgroup.closure ({x, d} : Set G))
    (hLcent : L ≤ Subgroup.centralizer ({x} : Set G)) :
    L ⊓ Subgroup.centralizer (D : Set G) = L ⊓ Subgroup.centralizer ({d} : Set G) := by
  ext g
  constructor
  · rintro ⟨hgL, hgD⟩
    refine ⟨hgL, ?_⟩
    change g ∈ Subgroup.centralizer (D : Set G) at hgD
    change g ∈ Subgroup.centralizer ({d} : Set G)
    rw [Subgroup.mem_centralizer_iff] at hgD ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    exact (Subgroup.mem_centralizer_iff.mp hgD) d hdD
  · rintro ⟨hgL, hgd⟩
    refine ⟨hgL, ?_⟩
    change g ∈ Subgroup.centralizer (D : Set G)
    rw [hDcl, Subgroup.centralizer_closure]
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hzx | hzd
    · rw [hzx]
      exact (Subgroup.mem_centralizer_iff.mp (hLcent hgL)) x (by simp)
    · rw [hzd]
      exact (Subgroup.mem_centralizer_iff.mp hgd) d (by simp)

private lemma ggQ2tbc_reflection_restrict [Fact (Nat.Prime 3)]
    (hS : GGQTwoSetting 3 B Bs x L D J) (M : GGQ2LDatum 3 Bs L x) (hM : M.ShapeFull)
    {φ : MulAut ↥Bs} (hr : GGIsReflection 3 φ)
    (hfixx : φ ⟨x, M.hx⟩ = ⟨x, M.hx⟩)
    {φ' : MulAut ↥(Bs ⊓ L)}
    (hφ' : ∀ y : ↥(Bs ⊓ L),
      ((φ ⟨(y : G), y.2.1⟩ : ↥Bs) : G) = (φ' y : G)) :
    GGIsReflection 3 φ' := by
  have hHleBs : (Bs ⊓ L : Subgroup G) ≤ Bs := inf_le_left
  have hPcard : Nat.card ↥(Subgroup.zpowers x) = 3 := ggQ2tbc_P_card hS M
  have hPleBs : Subgroup.zpowers x ≤ Bs := Subgroup.zpowers_le.mpr M.hx
  have hPinf : Subgroup.zpowers x ⊓ (Bs ⊓ L) = ⊥ := ggQ2tbc_P_inf hS M hM
  have hBs_card : Nat.card ↥Bs = 3 * Nat.card ↥(Bs ⊓ L) := ggQ2tbc_card_Bs hS M hM
  have hPfix : ∀ a : ↥Bs, (a : G) ∈ Subgroup.zpowers x → φ a = a := by
    intro a ha
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp ha
    have haeq : a = ⟨x, M.hx⟩ ^ k := by
      apply Subtype.ext
      rw [Subgroup.coe_zpow Bs ⟨x, M.hx⟩ k]
      exact hk.symm
    rw [haeq, map_zpow, hfixx]
  have hφH : ∀ y : ↥(Bs ⊓ L),
      φ ⟨(y : G), y.2.1⟩ = ⟨(φ' y : G), (φ' y).2.1⟩ := by
    intro y
    apply Subtype.ext
    exact hφ' y
  have hsq : φ' ^ 2 = 1 := by
    refine MulEquiv.ext fun y => Subtype.ext ?_
    simp only [pow_two, MulAut.mul_apply]
    show ((φ' (φ' y) : ↥(Bs ⊓ L)) : G) = (y : G)
    have h1 : (φ ⟨(φ' y : G), (φ' y).2.1⟩ : ↥Bs) = φ (φ ⟨(y : G), y.2.1⟩) := by
      rw [hφH y]
    have h2 : φ (φ ⟨(y : G), y.2.1⟩) = ⟨(y : G), y.2.1⟩ := by
      have := congrArg (fun τ : MulAut ↥Bs => τ ⟨(y : G), y.2.1⟩) hr.1
      simpa [pow_two, MulAut.mul_apply] using this
    calc ((φ' (φ' y) : ↥(Bs ⊓ L)) : G) =
        ((φ ⟨(φ' y : G), (φ' y).2.1⟩ : ↥Bs) : G) := (hφ' (φ' y)).symm
      _ = ((φ (φ ⟨(y : G), y.2.1⟩) : ↥Bs) : G) := by rw [h1]
      _ = (y : G) := by rw [h2]
  let f : ↥(Subgroup.zpowers x) × {y : ↥(Bs ⊓ L) // φ' y = y} →
      {b : ↥Bs // φ b = b} := fun q =>
    ⟨⟨(q.1 : G) * (q.2.1 : G), Bs.mul_mem (hPleBs q.1.2) (hHleBs q.2.1.2)⟩, by
      show φ ⟨(q.1 : G) * (q.2.1 : G),
          Bs.mul_mem (hPleBs q.1.2) (hHleBs q.2.1.2)⟩ =
        ⟨(q.1 : G) * (q.2.1 : G), Bs.mul_mem (hPleBs q.1.2) (hHleBs q.2.1.2)⟩
      rw [show (⟨(q.1 : G) * (q.2.1 : G),
          Bs.mul_mem (hPleBs q.1.2) (hHleBs q.2.1.2)⟩ : ↥Bs) =
          ⟨(q.1 : G), hPleBs q.1.2⟩ * ⟨(q.2.1 : G), hHleBs q.2.1.2⟩ from
        Subtype.ext rfl,
        map_mul]
      have hq : φ ⟨(q.2.1 : G), hHleBs q.2.1.2⟩ =
          ⟨(q.2.1 : G), hHleBs q.2.1.2⟩ := by
        have h := hφH q.2.1
        rw [q.2.2] at h
        simpa using h
      rw [hPfix _ q.1.2, hq]⟩
  have hinj : Function.Injective f := by
    intro q r h
    have hval : (q.1 : G) * (q.2.1 : G) = (r.1 : G) * (r.2.1 : G) := by
      have h' := congrArg (fun b : ↥Bs => (b : G)) (congrArg Subtype.val h)
      change (q.1 : G) * (q.2.1 : G) = (r.1 : G) * (r.2.1 : G)
      simpa [f] using h'
    have hmem : (r.1 : G)⁻¹ * (q.1 : G) ∈ Subgroup.zpowers x ⊓ (Bs ⊓ L) := by
      constructor
      · exact Subgroup.mul_mem _ (Subgroup.inv_mem _ r.1.2) q.1.2
      · have heq : (r.1 : G)⁻¹ * (q.1 : G) = (r.2.1 : G) * (q.2.1 : G)⁻¹ := by
          have := congrArg (fun z => (r.1 : G)⁻¹ * z * (q.2.1 : G)⁻¹) hval
          simpa [mul_assoc] using this
        rw [heq]
        exact Subgroup.mul_mem _ r.2.1.2 (Subgroup.inv_mem _ q.2.1.2)
    have hone : (r.1 : G)⁻¹ * (q.1 : G) = 1 := by
      have := hmem
      rw [hPinf] at this
      simpa using this
    have ha : q.1 = r.1 := by
      apply Subtype.ext
      calc (q.1 : G) = (r.1 : G) * ((r.1 : G)⁻¹ * (q.1 : G)) := by group
        _ = (r.1 : G) := by rw [hone, mul_one]
    have hy : q.2 = r.2 := by
      apply Subtype.ext
      apply Subtype.ext
      have hval' : (q.1 : G) * (q.2.1 : G) = (q.1 : G) * (r.2.1 : G) := by
        rw [hval, ← ha]
      exact mul_left_cancel hval'
    exact Prod.ext ha hy
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨k, h, hhL, hbk⟩ := ggQ2tbc_decomp hS M hM b.1
    let a : ↥(Subgroup.zpowers x) :=
      ⟨x ^ k, Subgroup.pow_mem (Subgroup.zpowers x) (Subgroup.mem_zpowers x) k⟩
    let hh : ↥(Bs ⊓ L) := ⟨(h : G), ⟨h.2, hhL⟩⟩
    have hbG : ((b.1 : ↥Bs) : G) = x ^ k * (h : G) := by
      have := congrArg Subtype.val hbk
      simpa [Subgroup.coe_pow, Subgroup.coe_mul] using this
    have hfix_h : φ' hh = hh := by
      apply Subtype.ext
      have hb_fix : φ b.1 = b.1 := b.2
      have h2 : φ b.1 =
          (⟨x, M.hx⟩ ^ k) * ⟨(φ' hh : G), (φ' hh).2.1⟩ := by
        rw [hbk, map_mul,
          hPfix _ (Subgroup.pow_mem (Subgroup.zpowers x) (Subgroup.mem_zpowers x) k)]
        congr 1
        exact hφH hh
      have h3 : ((⟨x, M.hx⟩ ^ k) * ⟨(φ' hh : G), (φ' hh).2.1⟩ : ↥Bs) =
          ((⟨x, M.hx⟩ ^ k) * ⟨(h : G), h.2⟩ : ↥Bs) := by
        calc _ = φ b.1 := h2.symm
          _ = b.1 := hb_fix
          _ = (⟨x, M.hx⟩ ^ k) * ⟨(h : G), h.2⟩ := hbk
      have h4 : (φ' hh : G) = (h : G) := by
        have := congrArg (fun z : ↥Bs => (z : G)) (mul_left_cancel h3)
        simpa using this
      exact h4
    refine ⟨(a, ⟨hh, hfix_h⟩), ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show (a : G) * (hh : G) = ((b.1 : ↥Bs) : G)
    rw [show (a : G) = x ^ k from rfl, show (hh : G) = (h : G) from rfl]
    exact hbG.symm
  have hcard_fix : Nat.card {b : ↥Bs // φ b = b} =
      3 * Nat.card {y : ↥(Bs ⊓ L) // φ' y = y} := by
    have h := (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm
    calc Nat.card {b : ↥Bs // φ b = b}
        = Nat.card (↥(Subgroup.zpowers x) × {y : ↥(Bs ⊓ L) // φ' y = y}) := h
      _ = Nat.card ↥(Subgroup.zpowers x) *
          Nat.card {y : ↥(Bs ⊓ L) // φ' y = y} := Nat.card_prod _ _
      _ = 3 * Nat.card {y : ↥(Bs ⊓ L) // φ' y = y} := by rw [hPcard]
  refine ⟨hsq, ?_⟩
  have hr2 := hr.2
  rw [hcard_fix, hBs_card] at hr2
  have h3 : 3 * (Nat.card {y : ↥(Bs ⊓ L) // φ' y = y} * 3) =
      3 * Nat.card ↥(Bs ⊓ L) := by
    calc 3 * (Nat.card {y : ↥(Bs ⊓ L) // φ' y = y} * 3) =
        (3 * Nat.card {y : ↥(Bs ⊓ L) // φ' y = y}) * 3 := by ring
      _ = 3 * Nat.card ↥(Bs ⊓ L) := hr2
  exact Nat.mul_left_cancel (by norm_num) h3

omit [Finite G] in
private lemma ggQ2tbc_mem_normalizer_inf {u : G} (huL : u ∈ L)
    (huBs : u ∈ Subgroup.normalizer (Bs : Set G)) :
    u ∈ Subgroup.normalizer ((Bs ⊓ L : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact ⟨(Subgroup.mem_normalizer_iff.mp huBs y).mp hy.1,
      L.mul_mem (L.mul_mem huL hy.2) (L.inv_mem huL)⟩
  · intro hy
    refine ⟨(Subgroup.mem_normalizer_iff.mp huBs y).mpr hy.1, ?_⟩
    have h := L.mul_mem (L.mul_mem (L.inv_mem huL) hy.2) huL
    simpa [mul_assoc] using h

private lemma ggQ2tbc_conj_mem_Bs [Fact (Nat.Prime 3)]
    (hS : GGQTwoSetting 3 B Bs x L D J) (M : GGQ2LDatum 3 Bs L x) (hM : M.ShapeFull)
    {u : G} (hux : Commute u x)
    (huH : ∀ z ∈ (Bs ⊓ L : Subgroup G), u * z * u⁻¹ ∈ (Bs ⊓ L : Subgroup G))
    {y : G} (hy : y ∈ Bs) : u * y * u⁻¹ ∈ Bs := by
  obtain ⟨k, h, hhL, hbk⟩ := ggQ2tbc_decomp hS M hM ⟨y, hy⟩
  have hyG : y = x ^ k * (h : G) := by
    have := congrArg Subtype.val hbk
    simpa [Subgroup.coe_pow, Subgroup.coe_mul] using this
  have huh : u * (h : G) * u⁻¹ ∈ (Bs ⊓ L : Subgroup G) := huH (h : G) ⟨h.2, hhL⟩
  have huxk : u * x ^ k = x ^ k * u := (hux.pow_right k).eq
  rw [hyG]
  have heq : u * (x ^ k * (h : G)) * u⁻¹ = x ^ k * (u * (h : G) * u⁻¹) := by
    calc u * (x ^ k * (h : G)) * u⁻¹ = (u * x ^ k) * (h : G) * u⁻¹ := by group
      _ = (x ^ k * u) * (h : G) * u⁻¹ := by rw [huxk]
      _ = x ^ k * (u * (h : G) * u⁻¹) := by group
  rw [heq]
  exact Bs.mul_mem (Bs.pow_mem M.hx k) huh.1

private lemma ggQ2tbc_mem_normalizer_Bs [Fact (Nat.Prime 3)]
    (hS : GGQTwoSetting 3 B Bs x L D J) (M : GGQ2LDatum 3 Bs L x) (hM : M.ShapeFull)
    {u : G} (hux : Commute u x)
    (huH : u ∈ Subgroup.normalizer ((Bs ⊓ L : Subgroup G) : Set G)) :
    u ∈ Subgroup.normalizer (Bs : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    exact ggQ2tbc_conj_mem_Bs hS M hM hux
      (fun z hz => (Subgroup.mem_normalizer_iff.mp huH z).mp hz) hy
  · intro hy
    have h1 : u⁻¹ * (u * y * u⁻¹) * u ∈ Bs := by
      simpa [inv_inv] using ggQ2tbc_conj_mem_Bs hS M hM (Commute.inv_left hux)
        (fun z hz => (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ huH) z).mp hz) hy
    simpa [mul_assoc] using h1

omit [Finite G] in
private lemma ggQ2tbc_conj_action [Fact (Nat.Prime 3)]
    (M : GGQ2LDatum 3 Bs L x) {u : G}
    (huBs : u ∈ Subgroup.normalizer (Bs : Set G)) (hux : Commute u x)
    {u' : MulAut ↥(Bs ⊓ L)}
    (hu' : ∀ y : ↥(Bs ⊓ L),
      ((ggConjAut Bs huBs ⟨(y : G), y.2.1⟩ : ↥Bs) : G) = (u' y : G))
    {m : ℕ} {h : ↥Bs} (hhL : (h : G) ∈ L) :
    ((ggConjAut Bs huBs (⟨x, M.hx⟩ ^ m * h) : ↥Bs) : G) =
      x ^ m * (u' ⟨(h : G), ⟨h.2, hhL⟩⟩ : G) := by
  have huxm : u * x ^ m = x ^ m * u := (hux.pow_right m).eq
  have hxconj : u * x ^ m * u⁻¹ = x ^ m := by
    rw [huxm]
    group
  have hx' : ((ggConjAut Bs huBs (⟨x, M.hx⟩ ^ m) : ↥Bs) : G) = x ^ m := by
    rw [ggConjAut_apply, Subgroup.coe_pow]
    exact hxconj
  have hhconj : u * (h : G) * u⁻¹ = (u' ⟨(h : G), ⟨h.2, hhL⟩⟩ : G) := by
    have h := hu' ⟨(h : G), ⟨h.2, hhL⟩⟩
    rwa [ggConjAut_apply] at h
  have hh' : ((ggConjAut Bs huBs h : ↥Bs) : G) = (u' ⟨(h : G), ⟨h.2, hhL⟩⟩ : G) := by
    rw [ggConjAut_apply]
    exact hhconj
  calc ((ggConjAut Bs huBs (⟨x, M.hx⟩ ^ m * h) : ↥Bs) : G)
      = ((ggConjAut Bs huBs (⟨x, M.hx⟩ ^ m) : ↥Bs) : G) *
        ((ggConjAut Bs huBs h : ↥Bs) : G) := by
        rw [map_mul, Subgroup.coe_mul]
    _ = x ^ m * (u' ⟨(h : G), ⟨h.2, hhL⟩⟩ : G) := by rw [hx', hh']

theorem ggQ2_tbc_of_coreIn {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) [Fact (Nat.Prime 3)]
    (M : GGQ2LDatum 3 Bs L x) (hM : M.ShapeFull)
    (hcore : GGTBCReflCoreIn (Fintype.card M.Λ) L)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer L Bs) (hr : GGIsReflection 3 φ)
    (hfix : ∀ b : ↥Bs, (b : G) ∈ D → φ b = b) :
    φ ∈ ggAutomizer J Bs ∨ ∀ ψ ∈ ggAutomizer J Bs, φ * ψ = ψ * φ := by
  classical
  obtain ⟨hcfg, -, -, -, -⟩ := hS.1
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hSstar : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hLcent : L ≤ Subgroup.centralizer ({x} : Set G) := hSstar.2.2.2.1.1
  have hx_D : x ∈ D := hStdSub.1.2.2.2.1
  have hJcompD : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hStdSub.1.2.2.2.2.2.1
  obtain ⟨d, hdD, hdBs, hdL, hd1, hdP, hDcl⟩ := ggQ2tbc_exists_d hS M hM
  have hJcomp : IsComponentOf J (L ⊓ Subgroup.centralizer ({d} : Set G)) := by
    rw [← ggQ2tbc_centralizer_eq hdD hDcl hLcent]
    exact hJcompD
  have hHIsElem : CFSG.Open.IsElemAbelian 3 (Bs ⊓ L) := by
    refine ⟨?_, ?_⟩
    · rw [isMulCommutative_iff_of_setLike]
      intro a ha b hb
      exact isMulCommutative_iff_of_setLike.mp hBstar.2.1.1 a ha.1 b hb.1
    · intro a ha
      exact hBstar.2.1.2 a ha.1
  obtain ⟨g, hgL, hgN, hgapp⟩ := mem_ggAutomizer_iff.mp hφ
  have hfixx : φ ⟨x, M.hx⟩ = ⟨x, M.hx⟩ := hfix ⟨x, M.hx⟩ hx_D
  have hgx : Commute g x := by
    have h1 : (x : G) = g * x * g⁻¹ := by
      have := hgapp ⟨x, M.hx⟩
      rw [hfixx] at this
      exact this
    have h2 : x * g = g * x := by
      have := congrArg (fun z : G => z * g) h1
      simpa [mul_assoc] using this
    exact h2.symm
  have hgd : g ∈ Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst y
    have h1 : d = g * d * g⁻¹ := by
      have := hgapp ⟨d, hdBs⟩
      rw [hfix ⟨d, hdBs⟩ hdD] at this
      exact this
    have h2 := congrArg (fun z : G => z * g) h1
    simpa [mul_assoc] using h2
  have hgHnorm : g ∈ Subgroup.normalizer ((Bs ⊓ L : Subgroup G) : Set G) :=
    ggQ2tbc_mem_normalizer_inf hgL hgN
  let φ' : MulAut ↥(Bs ⊓ L) := ggConjAut (Bs ⊓ L) hgHnorm
  have hφ'auto : φ' ∈ ggAutomizer (L ⊓ Subgroup.centralizer ({d} : Set G))
      (Bs ⊓ L) :=
    ggConjAut_mem_ggAutomizer (H := L ⊓ Subgroup.centralizer ({d} : Set G)) ⟨hgL, hgd⟩ hgHnorm
  have hφ'_apply : ∀ y : ↥(Bs ⊓ L),
      ((φ ⟨(y : G), y.2.1⟩ : ↥Bs) : G) = (φ' y : G) := by
    intro y
    rw [hgapp ⟨(y : G), y.2.1⟩]
    exact (ggConjAut_apply (Bs ⊓ L) hgHnorm y).symm
  have hr' : GGIsReflection 3 φ' :=
    ggQ2tbc_reflection_restrict hS M hM hr hfixx hφ'_apply
  have hcoreapp := hcore (Bs ⊓ L) inf_le_right hHIsElem (ggQ2tbc_card_H hS M hM) d
    ⟨hdBs, hdL⟩ hd1 J hJcomp φ' hφ'auto hr'
  have hφ_eq : φ = ggConjAut Bs hgN := by
    refine MulEquiv.ext fun b => Subtype.ext ?_
    rw [ggConjAut_apply]
    exact hgapp b
  rcases hcoreapp with hJ | hcomm
  · left
    obtain ⟨j, hjJ, hjHnorm, hjapp⟩ := mem_ggAutomizer_iff.mp hJ
    have hjL : j ∈ L := (hJcomp.1 hjJ).1
    have hjx : Commute j x := by
      have h := hLcent hjL
      rw [Subgroup.mem_centralizer_iff] at h
      exact (show Commute x j from h x (by simp)).symm
    have hjBs : j ∈ Subgroup.normalizer (Bs : Set G) :=
      ggQ2tbc_mem_normalizer_Bs hS M hM hjx hjHnorm
    refine mem_ggAutomizer_iff.mpr ⟨j, hjJ, hjBs, fun b => ?_⟩
    obtain ⟨m, h, hhL, hbk⟩ := ggQ2tbc_decomp hS M hM b
    let hh : ↥(Bs ⊓ L) := ⟨(h : G), ⟨h.2, hhL⟩⟩
    have h1 : ((φ b : ↥Bs) : G) = x ^ m * (φ' hh : G) := by
      rw [hbk, hφ_eq]
      exact ggQ2tbc_conj_action M hgN hgx
        (fun y => by rw [← hφ_eq]; exact hφ'_apply y) hhL
    have h2 : ((ggConjAut Bs hjBs b : ↥Bs) : G) = x ^ m * (φ' hh : G) := by
      rw [hbk]
      exact ggQ2tbc_conj_action M hjBs hjx (fun y => by
        rw [ggConjAut_apply]
        exact (hjapp y).symm) hhL
    rw [h1, ← h2, ggConjAut_apply]
  · right
    intro ψ hψ
    obtain ⟨k, hkJ, hkBs, hkapp⟩ := mem_ggAutomizer_iff.mp hψ
    have hkL : k ∈ L := (hJcomp.1 hkJ).1
    have hkx : Commute k x := by
      have h := hLcent hkL
      rw [Subgroup.mem_centralizer_iff] at h
      exact (show Commute x k from h x (by simp)).symm
    have hkH : k ∈ Subgroup.normalizer ((Bs ⊓ L : Subgroup G) : Set G) :=
      ggQ2tbc_mem_normalizer_inf hkL hkBs
    let ψ' : MulAut ↥(Bs ⊓ L) := ggConjAut (Bs ⊓ L) hkH
    have hψ'auto : ψ' ∈ ggAutomizer J (Bs ⊓ L) :=
      ggConjAut_mem_ggAutomizer hkJ hkH
    have hcomm' : φ' * ψ' = ψ' * φ' := hcomm ψ' hψ'auto
    have hψ_eq : ψ = ggConjAut Bs hkBs := by
      refine MulEquiv.ext fun b => Subtype.ext ?_
      rw [ggConjAut_apply]
      exact hkapp b
    refine MulEquiv.ext fun b => Subtype.ext ?_
    obtain ⟨m, h, hhL, hbk⟩ := ggQ2tbc_decomp hS M hM b
    let hh : ↥(Bs ⊓ L) := ⟨(h : G), ⟨h.2, hhL⟩⟩
    have hψb : ((ψ b : ↥Bs) : G) = x ^ m * (ψ' hh : G) := by
      rw [hbk, hψ_eq]
      exact ggQ2tbc_conj_action M hkBs hkx (fun y => by
        rw [ggConjAut_apply]
        exact (ggConjAut_apply (Bs ⊓ L) hkH y).symm) hhL
    have hφψ : ((φ (ψ b) : ↥Bs) : G) = x ^ m * (φ' (ψ' hh) : G) := by
      have hb' : ψ b = ⟨x, M.hx⟩ ^ m * ⟨(ψ' hh : G), (ψ' hh).2.1⟩ := by
        apply Subtype.ext
        exact hψb
      rw [hb', hφ_eq]
      exact ggQ2tbc_conj_action M hgN hgx
        (fun y => by rw [← hφ_eq]; exact hφ'_apply y) (ψ' hh).2.2
    have hφb : ((φ b : ↥Bs) : G) = x ^ m * (φ' hh : G) := by
      rw [hbk, hφ_eq]
      exact ggQ2tbc_conj_action M hgN hgx
        (fun y => by rw [← hφ_eq]; exact hφ'_apply y) hhL
    have hψφb : ((ψ (φ b) : ↥Bs) : G) = x ^ m * (ψ' (φ' hh) : G) := by
      have hb'' : φ b = ⟨x, M.hx⟩ ^ m * ⟨(φ' hh : G), (φ' hh).2.1⟩ := by
        apply Subtype.ext
        exact hφb
      rw [hb'', hψ_eq]
      exact ggQ2tbc_conj_action M hkBs hkx (fun y => by
        rw [ggConjAut_apply]
        exact (ggConjAut_apply (Bs ⊓ L) hkH y).symm) (φ' hh).2.2
    simp only [MulAut.mul_apply]
    rw [hφψ, hψφb]
    have hhcomm := congrArg (fun τ : MulAut ↥(Bs ⊓ L) => (τ hh : G)) hcomm'
    simpa [MulAut.mul_apply] using hhcomm

end CFSG.StandardType

end
