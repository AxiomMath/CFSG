module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223P4CExcl
public import CFSG.Quasithin.EmptyFaithful.FLcFlagLocal
public import CFSG.Quasithin.EmptyFaithful.FLcP0

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

namespace S15223P4

namespace C

variable {G : Type} [Group G] [Finite G]

theorem natural_positive' {T Mc Z₁ Z₂ L : Subgroup G} (hF : Facts15128 T Mc Z₁ Z₂ L) {n : ℕ}
    (hn : n = 4 ∨ n = 5)
    (h : @DirectSumOfCopies ↥(uOf1527 Z₂ L) (commGroupOfElemAbelian hF.hU) (autOn L (uOf1527 Z₂ L))
      ((uLOf1527 Z₂ L).subgroupOf (uOf1527 Z₂ L)) ⊥ (FFModel.nat (StatedSL n (ZMod 2))) 1) :
    IsNaturalUL L (uLOf1527 Z₂ L) ∧ Nat.card (zUOf1528 Z₂ L) = 2 := by
  let _ : CommGroup ↥(uOf1527 Z₂ L) := commGroupOfElemAbelian hF.hU
  have hn3 : 3 ≤ n := by omega
  obtain ⟨I, π, -, -, hsup, hreal⟩ := h
  have hI0 : I ⟨0, Nat.one_pos⟩ = (uLOf1527 Z₂ L).subgroupOf (uOf1527 Z₂ L) := by
    rw [← hsup, bot_sup_eq]
    exact (iSup_unique (f := I)).symm
  have hreal0 := hreal ⟨0, Nat.one_pos⟩
  rw [hI0] at hreal0
  obtain ⟨D⟩ := FLc.vmodelNat hreal0
    (fun g hg z hz => by rw [Subgroup.mem_bot.1 hz]; exact map_one g)
  obtain ⟨a, ha⟩ := FLc.exists_ne_one_nat (by omega : 1 ≤ n)
  have hne : (uLOf1527 Z₂ L).subgroupOf (uOf1527 Z₂ L) ≠ ⊥ :=
    FLc.ne_bot_of_surj D.β D.surj a ha
  have hne' : uLOf1527 Z₂ L ≠ ⊥ := fun h => hne (by rw [h, Subgroup.bot_subgroupOf])
  have hρ₀inj : Function.Injective (FLc.rhoOf π) :=
    rho_inj_of_ne_bot hF hn3 (FLc.rhoOf π) (FLc.rhoOf_surj hreal0.1) hne'
  obtain ⟨hh, -, -, -, -, hfixS⟩ :=
    normalize_rho hF hn3 (FLc.rhoOf π) (FLc.rhoOf_surj hreal0.1) (FLc.rhoOf_mem π) hne'
  have hπinj : Function.Injective π := FLc.injective_of_rhoOf_injective hρ₀inj
  have hLU := hF.LU
  let θ : ↥L →* MulAut ↥(uOf1527 Z₂ L) :=
    (conjAct (uOf1527 Z₂ L)).comp (Subgroup.inclusion hLU)
  have hθ : ∀ (l : ↥L) (v : ↥(uOf1527 Z₂ L)),
      (uOf1527 Z₂ L).subtype (θ l v) = (l : G) * (uOf1527 Z₂ L).subtype v * (l : G)⁻¹ := fun l v =>
    Subgroup.normalizerMonoidHom_apply_apply_coe (uOf1527 Z₂ L)
      (Subgroup.inclusion le_rfl (Subgroup.inclusion hLU l)) v
  have hθmem : ∀ l : ↥L, θ l ∈ autOn L (uOf1527 Z₂ L) := fun l =>
    Subgroup.mem_map.2 ⟨⟨(l : G), hLU l.2⟩, Subgroup.mem_subgroupOf.2 l.2, rfl⟩
  have hHθ : ∀ k ∈ autOn L (uOf1527 Z₂ L), ∃ l : ↥L, θ l = k := by
    intro k hk
    obtain ⟨x, hx, hxk⟩ := Subgroup.mem_map.1 hk
    exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.1 hx⟩, hxk⟩
  have key := FLc.isNaturalSection_of_realizes (uOf1527 Z₂ L).subtype Subtype.val_injective θ hθ
    hθmem hHθ hπinj hreal0
  have hmap : ((uLOf1527 Z₂ L).subgroupOf (uOf1527 Z₂ L)).map (uOf1527 Z₂ L).subtype =
      uLOf1527 Z₂ L := Subgroup.map_subgroupOf_eq_of_le hF.ULU
  rw [hmap] at key
  have hzUU : zUOf1528 Z₂ L ≤ uOf1527 Z₂ L := hF.ZUle.trans hF.ULU
  have hcardle : Nat.card (zUOf1528 Z₂ L) ≤ 2 := by
    let W : Subgroup ↥(uOf1527 Z₂ L) := (zUOf1528 Z₂ L).subgroupOf (uOf1527 Z₂ L)
    have hWU : W ≤ (uLOf1527 Z₂ L).subgroupOf (uOf1527 Z₂ L) := fun w hw =>
      Subgroup.mem_subgroupOf.2 (hF.ZUle (Subgroup.mem_subgroupOf.1 hw))
    have h2 := FLc.card_le_two_of_ut_fixed (by omega : 1 ≤ n) (D.rtwist hh) hWU
      (fun w hw s hs => hfixS s hs w (Subgroup.mem_subgroupOf.1 hw))
    have e : Nat.card ↥W = Nat.card ↥(zUOf1528 Z₂ L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hzUU).toEquiv
    omega
  have hzne : zUOf1528 Z₂ L ≠ ⊥ := by
    intro hz
    apply hF.MLne
    refine le_antisymm inf_le_right fun l hl => hF.CM l hl fun z hz' => ?_
    rw [hz, Subgroup.mem_bot] at hz'
    rw [hz']
    group
  have hcard1 : Nat.card (zUOf1528 Z₂ L) ≠ 1 := fun h1 => hzne (Subgroup.card_eq_one.1 h1)
  have hcard0 : 0 < Nat.card (zUOf1528 Z₂ L) := Nat.card_pos
  exact ⟨⟨n, hn, key⟩, by omega⟩

omit [Finite G] in
theorem mem_normalizer_inf_of' {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hA x, hB x]

omit [Finite G] in
theorem mem_normalizer_sup_of' {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
  rw [Subgroup.map_sup, hA, hB]

omit [Finite G] in
theorem card_of_natural {L UL : Subgroup G} {n : ℕ}
    (hsec : IsNaturalSection L UL ⊥ ((L ⊓ Subgroup.centralizer (UL : Set G)).subgroupOf L)
      (StatedSL n (ZMod 2))) : Nat.card ↥UL = 2 ^ n := by
  obtain ⟨α, β, -, hαs, -, hβs, hβk, hrel⟩ := FLc.isNaturalSection_data hsec
  have hβi : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  exact FLc.card_eq_of_bijective hβi hβs

theorem nonempty_p0Setup_of_natural {L S UL : Subgroup G} {n : ℕ} {W : ℕ → Subgroup G}
    (hsec : IsNaturalSection L UL ⊥ ((L ⊓ Subgroup.centralizer (UL : Set G)).subgroupOf L)
      (StatedSL n (ZMod 2)))
    (hn3 : 3 ≤ n) (hflag : IsSFlag S UL n W) (hSylL : IsSylowTwoOf (S ⊓ L) L)
    (hSN : S ≤ Subgroup.normalizer (L : Set G)) (hSUL : S ≤ Subgroup.normalizer (UL : Set G))
    (hS2 : IsPGroup 2 S) (hSyl2 : IsSylowTwoOf S (L ⊔ S))
    (hsimple : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L)) : Nonempty (FLc.P0Setup L S UL n W) := by
  obtain ⟨α₀, β₀, hLU, hαs, hαk, hβs, hβk, hrel⟩ := FLc.isNaturalSection_data hsec
  have hβi : Function.Injective β₀ := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  obtain ⟨α, β, hαs', hαk', hnorm, hrel'⟩ :=
    FLc.exists_normalized (by omega : 1 ≤ n) hSylL α₀ (MulEquiv.ofBijective β₀ ⟨hβi, hβs⟩) hαs
      hrel
  have hkerα : ∀ a : ↥L, α a = 1 ↔ (a : G) ∈ Subgroup.centralizer (UL : Set G) := by
    intro a
    rw [hαk' a, ← MonoidHom.mem_ker, hαk, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨a.2, h⟩⟩
  have hK2 := FLc.kernel_isPGroup (by omega : 2 ≤ n) α hαs' hkerα hsimple
  exact ⟨⟨α, β, hn3, hαs', fun a ha => (hkerα a).1 ha, hnorm, hrel', hLU, hSUL,
    fun s hs l hl => (Subgroup.mem_normalizer_iff.1 (hSN hs) l).1 hl, hS2, hK2, hSyl2,
    fun k h1 h2 => (hflag.2 k h1 h2).1, fun k h1 h2 => (hflag.2 k h1 h2).2.1,
    fun k h1 h2 => (hflag.2 k h1 h2).2.2.1⟩⟩

variable {T Mc M H : Subgroup G} {B₀ : Subgroup (MulAut (V154 T Mc M))} {I X : Subgroup G}

namespace CData

variable (d : CData T Mc M H B₀ I X)

include d

theorem S_le_normalizer_U :
    sOf152 T Mc M B₀ ≤ Subgroup.normalizer (uLOf1527 (zSOf T Mc M B₀) X : Set G) := by
  have hSZ : sOf152 T Mc M B₀ ≤ Subgroup.normalizer (zSOf T Mc M B₀ : Set G) :=
    d.c.S_le_centralizer.trans (Subgroup.centralizer_le_normalizer _)
  exact FLc.le_normalizer_commutator (FLc.le_normalizer_conjClosure hSZ d.S_le_normalizer_X)
    d.S_le_normalizer_X

theorem S_le_normalizer_zU :
    sOf152 T Mc M B₀ ≤ Subgroup.normalizer (zUOf1528 (zSOf T Mc M B₀) X : Set G) := by
  have hSZ : sOf152 T Mc M B₀ ≤ Subgroup.normalizer (zSOf T Mc M B₀ : Set G) :=
    d.c.S_le_centralizer.trans (Subgroup.centralizer_le_normalizer _)
  have hSW := FLc.le_normalizer_conjClosure hSZ d.S_le_normalizer_X
  have hSC : sOf152 T Mc M B₀ ≤ Subgroup.normalizer
      ((Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) :=
    fun g hg => B2F.normalizer_le_normalizer_centralizer X (d.S_le_normalizer_X hg)
  intro g hg
  exact mem_normalizer_inf_of' (mem_normalizer_sup_of' (hSZ hg) (mem_normalizer_inf_of' (hSW hg)
    (hSC hg))) (d.S_le_normalizer_U hg)

theorem exists_natural (hF : ¬ X ≤ Mc) (hN : NatOne T Mc M B₀ X) :
    ∃ (n : ℕ) (W : ℕ → Subgroup G), (n = 4 ∨ n = 5) ∧
      Nonempty (FLc.P0Setup X (sOf152 T Mc M B₀) (uLOf1527 (zSOf T Mc M B₀) X) n W) ∧
      zUOf1528 (zSOf T Mc M B₀) X = W 1 := by
  obtain ⟨hU, n, hn, hnat⟩ := hN
  have hF' := d.facts15128 hF
  obtain ⟨hNat, hcard⟩ := natural_positive' hF' hn hnat
  have hS2 : IsPGroup 2 (sOf152 T Mc M B₀) := d.c.setting.qtfe.sylow.1.to_le S_le_T152
  obtain ⟨nf, W, hnf, hflag, huniq⟩ := input15129FlagLocal_holds G X (sOf152 T Mc M B₀)
    (uLOf1527 (zSOf T Mc M B₀) X) hNat d.S_le_normalizer_X d.S_le_normalizer_U hS2 d.f.sylow
  obtain ⟨n', hn', hsec⟩ := hNat
  have hcardU := card_of_natural hsec
  have hnn : nf = n' := Nat.pow_right_injective (le_refl 2) (hflag.1.symm.trans hcardU)
  subst hnn
  refine ⟨nf, W, hnf, ?_, ?_⟩
  · exact nonempty_p0Setup_of_natural hsec (by omega) hflag d.f.sylow d.S_le_normalizer_X
      d.S_le_normalizer_U hS2 d.sylow_sup d.isSimple_quot
  · exact huniq 1 le_rfl (by omega) _ hF'.ZUle d.S_le_normalizer_zU (by rw [hcard, pow_one])

end CData

end C

end S15223P4

end CFSG.Quasithin
