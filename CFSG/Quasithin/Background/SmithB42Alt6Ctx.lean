module

public import CFSG.Quasithin.Background.SmithB42Alt7Ctx
public import CFSG.Quasithin.Background.B4HypCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3D4Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso

public section

namespace CFSG.Quasithin

namespace B42Alt6

open CFSG.Open CFSG.QuasithinUnique Equiv Equiv.Perm
open scoped commutatorElement

variable {S : Type} [CommGroup S] {G L : Subgroup (MulAut S)}

structure Ctx (G L : Subgroup (MulAut S)) : Prop where
  hF : L = quasithinGenFitting G
  center : Subgroup.center ↥L = ⊥
  perfect : Group.IsPerfect ↥L
  iso : Nonempty (↥L ≃* alternatingGroup (Fin 6))

namespace Ctx

variable (C : Ctx G L)
include C

theorem le_G : L ≤ G :=
  CFSG.QuasithinUnique.Bridge.FStarSimple.le_G C.hF

theorem normal : ∀ g ∈ G, ∀ l ∈ L, g * l * g⁻¹ ∈ L :=
  CFSG.QuasithinUnique.Bridge.FStarSimple.normal C.hF

theorem simple : IsSimpleGroup ↥L := by
  obtain ⟨e⟩ := C.iso
  have : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  exact e.isSimpleGroup

theorem nonab : ∃ a b : ↥L, a * b ≠ b * a := by
  obtain ⟨e⟩ := C.iso
  have h4 : 4 ≤ Nat.card (Fin 6) := by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num
  have hc := alternatingGroup.center_eq_bot h4
  have : Nontrivial (alternatingGroup (Fin 6)) :=
    alternatingGroup.nontrivial_of_three_le_card (by omega)
  by_contra h
  push Not at h
  obtain ⟨x, hx⟩ := exists_ne (1 : alternatingGroup (Fin 6))
  have hxc : x ∈ Subgroup.center (alternatingGroup (Fin 6)) :=
    Subgroup.mem_center_iff.2 fun g => by
      have := h (e.symm g) (e.symm x)
      exact e.symm.injective (by rw [map_mul, map_mul]; exact this)
  rw [hc] at hxc
  exact hx (Subgroup.mem_bot.1 hxc)

theorem cent_trivial [Finite S] : ∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g = 1 :=
  CFSG.QuasithinUnique.Bridge.FStarSimple.cent_trivial C.hF C.center

theorem le_ffJ [Finite S] {A : Subgroup (MulAut S)} (hA : IsFFStarOffender G A) : L ≤ ffJ G :=
  CFSG.QuasithinUnique.Bridge.FStarSimple.le_ffJ C.hF C.simple C.center hA

end Ctx

theorem ctx_of_b4Hyp_core [Finite S] (hB : B4HypCore G L) (hT : B42TypeAlt6 ↥L) : Ctx G L :=
  ⟨hB.1, hT.1, hB.2.1.1, B42Alt7.nonempty_iso_of_center hT.1 hT.2⟩

theorem ctx_of_b4Hyp [Finite S] (hB : B4Hyp G L) (hT : B42TypeAlt6 ↥L) : Ctx G L :=
  ctx_of_b4Hyp_core hB.core hT

theorem card_le_index_pow [Finite S] (C : Ctx G L) (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤)
    {B : Subgroup (MulAut S)} (hBG : B ≤ G) (hB1 : B ≠ ⊥) (hB : IsElemAbelian2 B) :
    ∃ r m : ℕ, Nat.card B = 2 ^ r ∧ 1 ≤ r ∧ r ≤ 3 ∧ m * r ≤ 6 ∧
      Nat.card S ≤ (fixV B).index ^ m := by
  classical
  obtain ⟨ι⟩ := C.iso
  have hLG := C.le_G
  set L' : Subgroup ↥G := L.subgroupOf G with hL'
  have hL'n : L'.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := C.normal g g.2 n hn
    simpa using this⟩
  let eLL : ↥L' ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLG
  have hc' : Subgroup.center ↥L' = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : eLL z ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro k
      obtain ⟨k', rfl⟩ := eLL.surjective k
      rw [← map_mul, ← map_mul, hz k']
    rw [C.center, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    exact eLL.injective (by rw [h1, map_one])
  let eQ : (↥L' ⧸ Subgroup.center ↥L') ≃* alternatingGroup (Fin 6) :=
    ((QuotientGroup.quotientMulEquivOfEq hc').trans QuotientGroup.quotientBot).trans (eLL.trans ι)
  have : Group.IsPerfect ↥L := C.perfect
  have : Group.IsPerfect ↥L' :=
    Group.IsPerfect.ofSurjective (f := eLL.symm.toMonoidHom) eLL.symm.surjective
  have hker : ∀ h : ↥G, Setup.X3.outAct L' eQ h = 1 → h ∈ (Subgroup.center ↥L').map L'.subtype := by
    intro h hh
    have h1 := Setup.X3.mem_centralizer_of_outAct_eq_one L' eQ hh
    have h2 : (h : MulAut S) = 1 := by
      refine C.cent_trivial h h.2 fun l hl => ?_
      have h3 := Subgroup.mem_centralizer_iff.1 h1 ⟨l, hLG hl⟩ (Subgroup.mem_subgroupOf.2 hl)
      exact (congrArg Subtype.val h3).symm
    have : h = 1 := Subtype.ext h2
    rw [this]
    exact one_mem _
  have hinj : Function.Injective (Setup.X3.outAct L' eQ) := by
    rw [injective_iff_map_eq_one]
    intro h hh
    obtain ⟨z, hz, rfl⟩ := hker h hh
    have hz' : z ∈ Subgroup.center ↥L' := hz
    rw [hc', Subgroup.mem_bot] at hz'
    rw [hz', map_one]
  set A' : Subgroup (MulAut (alternatingGroup (Fin 6))) :=
    (B.subgroupOf G).map (Setup.X3.outAct L' eQ) with hA'
  have hBc : Nat.card ↥(B.subgroupOf G) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBG).toEquiv
  have hcardA' : Nat.card A' = Nat.card B := by
    rw [hA', Subgroup.card_map_of_injective hinj, hBc]
  have hA'1 : A' ≠ ⊥ := by
    intro h
    have h1 : Nat.card A' = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hcardA'] at h1
    exact hB1 (Subgroup.card_eq_one.1 h1)
  have hA'el : CFSG.IsElementaryAbelian 2 ↥A' := by
    refine { is_comm := ⟨fun x y => ?_⟩, exponent_dvd_p := ?_ }
    · obtain ⟨_, ⟨a, ha, rfl⟩⟩ := x
      obtain ⟨_, ⟨b, hb, rfl⟩⟩ := y
      apply Subtype.ext
      show Setup.X3.outAct L' eQ a * Setup.X3.outAct L' eQ b =
        Setup.X3.outAct L' eQ b * Setup.X3.outAct L' eQ a
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hB.1 _ (Subgroup.mem_subgroupOf.1 ha) _ (Subgroup.mem_subgroupOf.1 hb))
    · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      obtain ⟨_, ⟨a, ha, rfl⟩⟩ := x
      apply Subtype.ext
      show Setup.X3.outAct L' eQ a ^ 2 = 1
      rw [← map_pow]
      have : a ^ 2 = 1 := Subtype.ext (hB.2 _ (Subgroup.mem_subgroupOf.1 ha))
      rw [this, map_one]
  obtain ⟨r, m, hcard, hr1, hr3, hmr, s, hgen⟩ :=
    Setup.X3Aut.a6ShortGeneration.2.2.2 A' hA'1 hA'el
  obtain ⟨l, hl⟩ := Setup.X3.L_le_closure_of_inner_generation L' eQ hker (B.subgroupOf G) s hgen
  refine ⟨r, m, by rw [← hcardA', hcard], hr1, hr3, hmr, ?_⟩
  let K : Fin m → Subgroup S := fun i =>
    fixV (B.map (MulAut.conj (((l i : ↥G) : MulAut S))).toMonoidHom)
  have hK : ⨅ i, K i = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    have hvK : ∀ i, v ∈ K i := fun i => (Subgroup.mem_iInf.1 hv) i
    let St : Subgroup ↥G := (MulAction.stabilizer (MulAut S) v).comap G.subtype
    have hcl : Subgroup.closure (⋃ i, (((B.subgroupOf G).map
        (MulAut.conj ((l i : ↥G))).toMonoidHom : Subgroup ↥G) : Set ↥G)) ≤ St := by
      rw [Subgroup.closure_le]
      intro x hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.1 hx
      obtain ⟨b, hb, rfl⟩ := hi
      have hmem : ((MulAut.conj ((l i : ↥G))).toMonoidHom b : MulAut S) ∈
          B.map (MulAut.conj (((l i : ↥G) : MulAut S))).toMonoidHom :=
        ⟨(b : MulAut S), Subgroup.mem_subgroupOf.1 hb, by simp⟩
      have := hvK i _ hmem
      show _ • v = v
      exact this
    have hvL : v ∈ fixV L := by
      intro x hx
      have h1 := hcl (hl (Subgroup.mem_subgroupOf.2 hx : (⟨x, hLG hx⟩ : ↥G) ∈ L'))
      exact h1
    rw [B42A57.fixV_eq_bot_of_irr hirr C.nonab] at hvL
    exact hvL
  have h1 := Subgroup.index_iInf_le K
  rw [hK, Subgroup.index_bot] at h1
  have h2 : ∀ i, (K i).index = (fixV B).index := fun i => B42A57.index_fixV_conj B _
  simp only [h2, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h1
  exact h1

theorem card_le_sixtyfour [Finite S] (C : Ctx G L) (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup S) ⊤)
    {A : Subgroup (MulAut S)} (hA : IsFFStarOffender G A) : Nat.card S ≤ 2 ^ 6 := by
  obtain ⟨r, m, hcard, -, -, hmr, hle⟩ := card_le_index_pow C hirr hA.1 hA.2.1 hA.2.2.1
  have hidx := B42A57.index_fixV_le hA
  rw [hcard] at hidx
  calc Nat.card S ≤ (fixV A).index ^ m := hle
    _ ≤ (2 ^ r) ^ m := Nat.pow_le_pow_left hidx m
    _ = 2 ^ (m * r) := by rw [← pow_mul, mul_comm]
    _ ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) hmr

end B42Alt6

end CFSG.Quasithin
