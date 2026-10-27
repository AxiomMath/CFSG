module

public import CFSG.LocalAnalysis.StandardType.GGQTwoReflCut

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem ggQ2tbd_cent_eq {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (M : GGQ2LDatum p Bs L x) :
    (Subgroup.centralizer (L : Set G)).subgroupOf Bs = Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) := by
  classical
  obtain ⟨hcfg, -, -⟩ := hS
  obtain ⟨hconfig, -, -⟩ := hcfg
  obtain ⟨hI, hBstar, -⟩ := hconfig
  have hSst : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hLle : L ≤ Subgroup.centralizer ({x} : Set G) := hSst.2.2.2.1.1
  have hxcen : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLle hl)
  apply le_antisymm
  · intro b hb
    rw [Subgroup.mem_subgroupOf] at hb
    have hbc : ∀ l ∈ L, l * (b : G) = (b : G) * l := Subgroup.mem_centralizer_iff.mp hb
    have hfix : M.model (Additive.ofMul b) ∈
        ggFixedSubmodule (p := p) M.model (ggAutomizer L Bs) := by
      rw [mem_ggFixedSubmodule_iff]
      intro φ hφ
      refine Subgroup.closure_induction (k := ggInduced L Bs)
        (p := fun φ _ => ggLin (p := p) M.model φ (M.model (Additive.ofMul b)) =
          M.model (Additive.ofMul b)) ?_ ?_ ?_ ?_ hφ
      · rintro φ ⟨g, hgL, hgnorm, hφg⟩
        apply (ggLin_fix_iff (p := p) M.model φ b).mp
        apply Subtype.ext
        rw [hφg b]
        have hcomm : g * (b : G) = (b : G) * g := hbc g hgL
        rw [hcomm]
        group
      · simp
      · intro a c ha hc iha ihc
        rw [map_mul, LinearEquiv.mul_apply, ihc, iha]
      · intro a ha iha
        rw [map_inv]
        change (ggLin (p := p) M.model a).symm (M.model (Additive.ofMul b)) =
          M.model (Additive.ofMul b)
        apply LinearEquiv.injective (ggLin (p := p) M.model a)
        rw [LinearEquiv.apply_symm_apply, iha]
    rw [M.fixed_x] at hfix
    rw [Submodule.mem_span_singleton] at hfix
    obtain ⟨c, hc⟩ := hfix
    have hβ : Additive.ofMul b = c.val • Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) := by
      apply M.model.injective
      calc M.model (Additive.ofMul b)
          = c • M.model (Additive.ofMul (⟨x, M.hx⟩ : ↥Bs)) := hc.symm
        _ = (c.val : ZMod p) • M.model (Additive.ofMul (⟨x, M.hx⟩ : ↥Bs)) := by
              rw [ZMod.natCast_zmod_val]
        _ = c.val • M.model (Additive.ofMul (⟨x, M.hx⟩ : ↥Bs)) :=
              Nat.cast_smul_eq_nsmul (ZMod p) c.val _
        _ = M.model (c.val • Additive.ofMul (⟨x, M.hx⟩ : ↥Bs)) :=
              (map_nsmul M.model.toAddMonoidHom c.val _).symm
    rw [← ofMul_pow] at hβ
    have hb_eq : b = (⟨x, M.hx⟩ : ↥Bs) ^ c.val := Additive.ofMul.injective hβ
    refine Subgroup.mem_zpowers_iff.mpr ⟨(c.val : ℤ), ?_⟩
    rw [zpow_natCast]
    exact hb_eq.symm
  · rw [Subgroup.zpowers_le, Subgroup.mem_subgroupOf]
    exact hxcen

private theorem ggQ2tbd_card_x {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J)
    (M : GGQ2LDatum p Bs L x) : Nat.card (Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs)) = p := by
  obtain ⟨hcfg, -, -⟩ := hS
  obtain ⟨hconfig, -, -⟩ := hcfg
  obtain ⟨hI, hBstar, -⟩ := hconfig
  have hSst : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hxne : x ≠ 1 := hSst.2.2.1
  have hBs : IsElemAbelian p Bs := hBstar.2.1
  have hpow : (⟨x, M.hx⟩ : ↥Bs) ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hBs.2 x M.hx, Subgroup.coe_one]
  have hne : (⟨x, M.hx⟩ : ↥Bs) ≠ 1 := by
    intro h
    exact hxne (by simpa using congrArg Subtype.val h)
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime hpow hne

private theorem ggQ2tbd_card_Bs {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum p Bs L x) :
    Nat.card ↥Bs = p ^ Module.finrank (ZMod p) M.V := by
  haveI hE : Finite (Additive ↥Bs) :=
    Finite.of_injective (Additive.ofMul.symm : Additive ↥Bs → ↥Bs)
      Additive.ofMul.symm.injective
  haveI : Finite M.V :=
    Finite.of_injective (M.model.toEquiv.symm : M.V → Additive ↥Bs)
      M.model.toEquiv.symm.injective
  haveI : Fintype M.V := Fintype.ofFinite M.V
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hcard : Nat.card ↥Bs = Nat.card M.V :=
    Nat.card_congr (Additive.ofMul.trans M.model.toEquiv)
  rw [hcard, Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod p), ZMod.card]

theorem GGQ2LDatum.index_centralizer_of_setting {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (M : GGQ2LDatum p Bs L x) :
    ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index =
      p ^ (Module.finrank (ZMod p) M.V - 1) := by
  classical
  have hCcard : Nat.card ↥((Subgroup.centralizer (L : Set G)).subgroupOf Bs) = p := by
    rw [ggQ2tbd_cent_eq hS M]
    exact ggQ2tbd_card_x hS M
  have hcard := Subgroup.card_mul_index ((Subgroup.centralizer (L : Set G)).subgroupOf Bs)
  rw [hCcard, ggQ2tbd_card_Bs M] at hcard
  have hD : 0 < Module.finrank (ZMod p) M.V := by
    by_contra hD
    rw [Nat.eq_zero_of_not_pos hD, pow_zero] at hcard
    exact (Fact.out : p.Prime).not_dvd_one ⟨_, hcard.symm⟩
  have hD' : Module.finrank (ZMod p) M.V = (Module.finrank (ZMod p) M.V - 1) + 1 :=
    (Nat.succ_pred_eq_of_pos hD).symm
  rw [hD', pow_succ, Nat.mul_comm (p ^ (Module.finrank (ZMod p) M.V - 1)) p] at hcard
  exact Nat.mul_left_cancel (Fact.out : p.Prime).pos hcard

end CFSG.StandardType

end
