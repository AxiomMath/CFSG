module

public import CFSG.RankThree.GF2n.Tim81.Sec6.Stmts
public import CFSG.RankThree.GF2n.Tim81.Recog.L2Gen
public import CFSG.Timmesfeld.Bridge.OddLocalDefs
public import CFSG.RankThree.GF2n.Tim81.FStarSimple
public import CFSG.Timmesfeld.Bridge.OddTranspBasic
public import CFSG.Timmesfeld.Bridge.Asc72Bender
public import CFSG.Goldschmidt.Steps.StrongEmb
public import CFSG.GroupTheory.OddOrderClosurePResidual
public import CFSG.ThirdParty.BrauerInduction.Background.Group.Basic
import CFSG.RankThree.GF2n.Tim81.Sec6.S65Local
import CFSG.RankThree.GF2n.Tim78S410Core

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {M V : Subgroup G}

private abbrev KGen (V : Subgroup G) : Subgroup G := Subgroup.normalClosure (V : Set G)

private def DGen (V : Subgroup G) : Set ↥(KGen V) := {x | (x : G) ∈ Tim78.classD V}

private theorem V_ne_bot (hS : Sec6Hyp M V) : V ≠ ⊥ := by
  intro h
  have h4 := hS.sec5.toRootHyp.four_le_card
  rw [h, Subgroup.card_bot] at h4
  omega

private theorem simple_KGen (hS : Sec6Hyp M V) (hF : KGen V = generalizedFitting G) :
    IsSimpleGroup ↥(KGen V) ∧ ∃ a b : ↥(KGen V), a * b ≠ b * a := by
  rw [hF]
  exact Hyp.isSimpleGroup_generalizedFitting hS.sec5.toRootHyp.toHyp
    hS.sec5.toRootHyp.four_le_card

private theorem center_KGen_eq_bot (hS : Sec6Hyp M V)
    (hF : KGen V = generalizedFitting G) : Subgroup.center ↥(KGen V) = ⊥ := by
  obtain ⟨hsimple, hnonab⟩ := simple_KGen hS hF
  haveI := hsimple
  refine TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative ?_
  obtain ⟨a, b, hab⟩ := hnonab
  intro hc
  exact hab ((isMulCommutative_iff.mp hc) a b)

private theorem DGen_conj_mem {x : ↥(KGen V)} (hx : x ∈ DGen V) (k : ↥(KGen V)) :
    k * x * k⁻¹ ∈ DGen V :=
  Tim78.mem_classD_conj hx (k : G)

private theorem isConj_of_odd {x y : ↥(KGen V)}
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hodd : Odd (orderOf (x * y))) : IsConj x y := by
  obtain ⟨g, -, hg⟩ := CFSG.Timmesfeld.exists_conj_of_odd_orderOf_mul hx2 hy2 hodd
  exact isConj_iff.mpr ⟨g, hg⟩

private theorem DGen_ne_one {x : ↥(KGen V)} (hx : x ∈ DGen V) : x ≠ 1 := by
  intro h
  exact classD_ne_one hx (by simpa using congrArg Subtype.val h)

private theorem commute_of_class_compl (hodd : Timmesfeld.Bridge.Asc72.IsOddTransp
      (Tim78.classD V)) {d₀ : ↥(KGen V)} {D1 D2 : Set ↥(KGen V)}
    (hD1 : D1 = {z | IsConj d₀ z}) (hD2 : D2 = DGen V \ D1) (hD1sub : D1 ⊆ DGen V) :
    ∀ a ∈ D1, ∀ b ∈ D2, Commute a b := by
  intro a ha b hb
  rw [hD2] at hb
  by_contra hnc
  have haD : a ∈ DGen V := hD1sub ha
  have hbD : b ∈ DGen V := hb.1
  have ha2 : a * a = 1 := Subtype.ext (by simpa using hodd.mul_self_eq_one haD)
  have hb2 : b * b = 1 := Subtype.ext (by simpa using hodd.mul_self_eq_one hbD)
  have hnc' : ¬ Commute (a : G) (b : G) := fun h =>
    hnc ((Subgroup.commute_subtype_iff _ _).mp h)
  have ho : Odd (orderOf (a * b)) := by
    have h := hodd.odd_of_not_commute haD hbD hnc'
    have h' : orderOf ((a : G) * (b : G)) = orderOf (a * b) := by
      rw [← Subgroup.orderOf_coe (a * b), Subgroup.coe_mul]
    rwa [h'] at h
  have hac : IsConj a b := isConj_of_odd ha2 hb2 ho
  have hd0a : IsConj d₀ a := by rw [hD1] at ha; exact ha
  exact hb.2 (by rw [hD1]; exact hd0a.trans hac)

private theorem class_compl_conj_invariant {d₀ : ↥(KGen V)} {D1 D2 : Set ↥(KGen V)}
    (hD1 : D1 = {z | IsConj d₀ z}) (hD2 : D2 = DGen V \ D1) :
    (∀ (k : ↥(KGen V)) {z : ↥(KGen V)}, z ∈ D1 → k * z * k⁻¹ ∈ D1) ∧
      ∀ (k : ↥(KGen V)) {z : ↥(KGen V)}, z ∈ D2 → k * z * k⁻¹ ∈ D2 := by
  have hD1conj : ∀ (k : ↥(KGen V)) {z : ↥(KGen V)}, z ∈ D1 → k * z * k⁻¹ ∈ D1 := by
    intro k z hz
    rw [hD1] at hz ⊢
    obtain ⟨c, rfl⟩ := isConj_iff.mp hz
    exact isConj_iff.mpr ⟨k * c, by group⟩
  refine ⟨hD1conj, ?_⟩
  intro k z hz
  rw [hD2] at hz ⊢
  refine ⟨DGen_conj_mem hz.1 k, ?_⟩
  intro hzD1
  have hz' : k⁻¹ * (k * z * k⁻¹) * (k⁻¹)⁻¹ ∈ D1 := hD1conj k⁻¹ hzD1
  have hzz : k⁻¹ * (k * z * k⁻¹) * (k⁻¹)⁻¹ = z := by group
  rw [hzz] at hz'
  exact hz.2 hz'

private theorem isConj_DGen (hS : Sec6Hyp M V) (hF : KGen V = generalizedFitting G)
    (hodd : Timmesfeld.Bridge.Asc72.IsOddTransp (Tim78.classD V)) :
    ∃ d₀ : ↥(KGen V), d₀ ∈ DGen V ∧ ∀ y ∈ DGen V, IsConj d₀ y := by
  classical
  obtain ⟨⟨v, hvV⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (V_ne_bot hS)
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  set d₀ : ↥(KGen V) := ⟨v, Subgroup.le_normalClosure hvV⟩ with hd0def
  have hd0D : d₀ ∈ DGen V := ⟨1, ⟨v, hvV, hv1', by simp [hd0def]⟩⟩
  have hd0ne : d₀ ≠ 1 := fun h => hv1' (congrArg Subtype.val h)
  refine ⟨d₀, hd0D, ?_⟩
  intro y hy
  by_contra hycon
  set D1 : Set ↥(KGen V) := {z | IsConj d₀ z} with hD1
  set D2 : Set ↥(KGen V) := DGen V \ D1 with hD2
  have hyD2 : y ∈ D2 := by rw [hD2]; exact ⟨hy, hycon⟩
  have hd0D1 : d₀ ∈ D1 := by rw [hD1]; exact IsConj.refl d₀
  have hD1sub : D1 ⊆ DGen V := by
    intro z hz
    rw [hD1] at hz
    obtain ⟨c, rfl⟩ := isConj_iff.mp hz
    exact DGen_conj_mem hd0D c
  have hcomm := commute_of_class_compl hodd hD1 hD2 hD1sub
  obtain ⟨hD1conj, hD2conj⟩ := class_compl_conj_invariant hD1 hD2
  set N1 : Subgroup ↥(KGen V) := Subgroup.closure D1 with hN1
  set N2 : Subgroup ↥(KGen V) := Subgroup.closure D2 with hN2
  have hN1normal : N1.Normal := by
    rw [hN1, ← CFSG.GroupTheory.normalClosure_eq_closure_of_conj_invariant
      (fun g x hx => hD1conj g hx)]
    exact Subgroup.normalClosure_normal
  have hN2normal : N2.Normal := by
    rw [hN2, ← CFSG.GroupTheory.normalClosure_eq_closure_of_conj_invariant
      (fun g x hx => hD2conj g hx)]
    exact Subgroup.normalClosure_normal
  haveI := hN1normal
  haveI := hN2normal
  haveI hsimple : IsSimpleGroup ↥(KGen V) := (simple_KGen hS hF).1
  have hN1top : N1 = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top N1 with h | h
    · exfalso
      have hmem : d₀ ∈ N1 := by rw [hN1]; exact Subgroup.subset_closure hd0D1
      rw [h] at hmem
      exact hd0ne (Subgroup.mem_bot.mp hmem)
    · exact h
  have hN2ne : N2 ≠ ⊥ := by
    intro h
    have hmem : y ∈ N2 := by rw [hN2]; exact Subgroup.subset_closure hyD2
    rw [h] at hmem
    exact DGen_ne_one hy (Subgroup.mem_bot.mp hmem)
  have hle : N1 ≤ Subgroup.centralizer (N2 : Set ↥(KGen V)) := by
    rw [hN1, Subgroup.closure_le]
    intro a ha
    have hcommab : ∀ b ∈ N2, Commute a b := by
      intro b hb
      induction hb using Subgroup.closure_induction with
      | mem b hb => exact hcomm a ha b hb
      | one => exact Commute.one_right a
      | mul b c hb hc ihb ihc => exact ihb.mul_right ihc
      | inv b hb ih => exact ih.inv_right
    exact Subgroup.mem_centralizer_iff.mpr fun b hb => (hcommab b hb).eq.symm
  have hN2le : N2 ≤ Subgroup.center ↥(KGen V) := by
    have h := Subgroup.le_centralizer_iff.mp hle
    intro z hz
    have hz' : z ∈ Subgroup.centralizer (N1 : Set ↥(KGen V)) := h hz
    rw [hN1top] at hz'
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_iff.mp hz' g (Subgroup.mem_top g)
  refine hN2ne (le_bot_iff.mp ?_)
  rw [← center_KGen_eq_bot hS hF]
  exact hN2le

private theorem exists_DGen (hS : Sec6Hyp M V) :
    ∃ d : ↥(KGen V), d ∈ DGen V ∧ d ≠ 1 := by
  obtain ⟨⟨v, hvV⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (V_ne_bot hS)
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  refine ⟨⟨v, Subgroup.le_normalClosure hvV⟩, ⟨1, ⟨v, hvV, hv1', by simp⟩⟩, ?_⟩
  intro h
  exact hv1' (congrArg Subtype.val h)

private theorem setup_DGen (hS : Sec6Hyp M V) (hF : KGen V = generalizedFitting G)
    (hodd : Timmesfeld.Bridge.Asc72.IsOddTransp (Tim78.classD V)) :
    Timmesfeld.Bridge.Asc72.Setup ↥(KGen V) (DGen V) where
  isClass := by
    obtain ⟨d₀, hd0, hconj⟩ := isConj_DGen hS hF hodd
    refine ⟨d₀, ?_⟩
    ext y
    exact ⟨hconj y, fun hy => by
      obtain ⟨c, rfl⟩ := isConj_iff.mp hy
      exact DGen_conj_mem hd0 c⟩
  oddT := hodd.preimage (KGen V)
  gen := by
    haveI hsimple : IsSimpleGroup ↥(KGen V) := (simple_KGen hS hF).1
    have hnormal : (Subgroup.closure (DGen V)).Normal := by
      rw [← CFSG.GroupTheory.normalClosure_eq_closure_of_conj_invariant
        (fun g x hx => DGen_conj_mem hx g)]
      exact Subgroup.normalClosure_normal
    haveI := hnormal
    obtain ⟨d, hd, hd1⟩ := exists_DGen (M := M) hS
    have hne : Subgroup.closure (DGen V) ≠ ⊥ := by
      intro h
      have hmem : d ∈ Subgroup.closure (DGen V) := Subgroup.subset_closure hd
      rw [h, Subgroup.mem_bot] at hmem
      exact hd1 hmem
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.closure (DGen V)) with h | h
    · exact absurd h hne
    · exact h

theorem IsL2Gen.exists_not_commute {A B : Subgroup G} (h : IsL2Gen A B) {e : G}
    (he : e ∈ A) (he1 : e ≠ 1) : ∃ b ∈ B, ¬ Commute e b := by
  by_contra hcon
  push Not at hcon
  have hne : A ≠ B := IsL2Gen.ne h
  have hcard : Nat.card B = Nat.card A := IsL2Gen.card_eq h
  obtain ⟨F, hField, hFin, hCharP, φ, -, hA, hB⟩ := h
  letI := hField
  letI := hFin
  letI := hCharP
  set ψ : ↥(A ⊔ B) →* SL(2, F) := φ.toMonoidHom with hψ
  have hAψ : (A.subgroupOf (A ⊔ B)).map ψ = utri F := hA
  have hBψ : (B.subgroupOf (A ⊔ B)).map ψ = ltri F := hB
  have hψinj : Function.Injective ψ := φ.injective
  have heH : e ∈ A ⊔ B := Subgroup.mem_sup_left he
  let e' : ↥(A ⊔ B) := ⟨e, heH⟩
  have heA : e' ∈ A.subgroupOf (A ⊔ B) := Subgroup.mem_subgroupOf.mpr he
  have he_utri : ψ e' ∈ utri F := by
    rw [← hAψ]
    exact Subgroup.mem_map.mpr ⟨e', heA, rfl⟩
  obtain ⟨s, hs⟩ := mem_utri_iff.mp he_utri
  have hs0 : s ≠ 0 := by
    intro h0
    apply he1
    have h1 : ψ e' = 1 := by rw [hs, h0, utriElt_zero]
    have h2 : e' = 1 := hψinj (by simpa using h1)
    have h2' : (e' : G) = 1 := congrArg Subtype.val h2
    simpa [e'] using h2'
  have hBle : B.subgroupOf (A ⊔ B) ≤ A.subgroupOf (A ⊔ B) := by
    intro b hb
    have hbG : (b : G) ∈ B := Subgroup.mem_subgroupOf.mp hb
    have hcomm : Commute (ψ b) (utriElt s) := by
      have hcommG : Commute (b : ↥(A ⊔ B)) e' := by
        apply Subtype.ext
        exact (hcon (b : G) hbG).symm.eq
      have h2 : Commute (ψ b) (ψ e') := hcommG.map ψ
      rwa [hs] at h2
    have hcent : ψ b ∈ Subgroup.centralizer ({utriElt s} : Set (SL(2, F))) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm.eq
    rw [centralizer_utriElt hs0, ← hAψ] at hcent
    obtain ⟨a, ha, hab⟩ := Subgroup.mem_map.mp hcent
    have hab' : a = b := hψinj hab
    rw [hab'] at ha
    exact ha
  have hBA : B ≤ A := by
    have h := Subgroup.map_mono (f := (A ⊔ B).subtype) hBle
    rwa [Subgroup.map_subgroupOf_eq_of_le le_sup_right,
      Subgroup.map_subgroupOf_eq_of_le le_sup_left] at h
  have hBAeq : B = A := Subgroup.eq_of_le_of_card_ge hBA (by rw [hcard])
  exact hne hBAeq.symm

private theorem mem_omegaSet_iff {A : Subgroup G} :
    A ∈ omegaSet V ↔ ∃ g : G, A = conjSubgroup g V := by
  simp [omegaSet, Tim79a.omegaOf]

private theorem mem_DGen_of_mem {A : Subgroup G} (hA : A ∈ omegaSet V) {e : G}
    (he : e ∈ A) (he1 : e ≠ 1) (heK : e ∈ KGen V) : (⟨e, heK⟩ : ↥(KGen V)) ∈ DGen V := by
  obtain ⟨g, rfl⟩ := (mem_omegaSet_iff).mp hA
  have hb : g⁻¹ * e * g ∈ V := mem_conjSubgroup.mp he
  have hb1 : g⁻¹ * e * g ≠ 1 := by
    intro h
    apply he1
    calc e = g * (g⁻¹ * e * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group
  exact ⟨g, g⁻¹ * e * g, hb, hb1, by group⟩

private theorem conj_inv_le_centralizer {g a : G}
    (hcomm : ∀ x ∈ conjSubgroup a V, ∀ y ∈ conjSubgroup g V, x * y = y * x) :
    conjSubgroup (g⁻¹ * a) V ≤ Subgroup.centralizer (V : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hxA : g * x * g⁻¹ ∈ conjSubgroup a V := by
    rw [← CGT.Timmesfeld75.conjSubgroup_conjSubgroup g⁻¹ a V] at hx
    simpa using mem_conjSubgroup.mp hx
  have hgv : g * v * g⁻¹ ∈ conjSubgroup g V :=
    mem_conjSubgroup.mpr (by rw [show g⁻¹ * (g * v * g⁻¹) * g = v by group]; exact hv)
  have h := hcomm (g * x * g⁻¹) hxA (g * v * g⁻¹) hgv
  calc v * x = g⁻¹ * ((g * v * g⁻¹) * (g * x * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * x * g⁻¹) * (g * v * g⁻¹)) * g := by rw [← h]
    _ = x * v := by group

private theorem conj_inv_mem_sigmaSet (hS : Sec6Hyp M V)
    (h64 : ∀ B ∈ omegaSet V, B ≤ M → B = V ∨ B ∈ sigmaSet M V)
    {C X : Subgroup G} (hX : X ∈ omegaSet V) (hCX : C ≠ X)
    (hcomm : ∀ x ∈ X, ∀ y ∈ C, Commute x y) {c : G} (hCeq : C = conjSubgroup c V) :
    conjSubgroup c⁻¹ X ∈ sigmaSet M V := by
  obtain ⟨a, rfl⟩ := (mem_omegaSet_iff).mp hX
  have hcomm' : ∀ x ∈ conjSubgroup a V, ∀ y ∈ conjSubgroup c V, x * y = y * x := by
    intro x hx y hy
    exact (hcomm x hx y (hCeq.symm ▸ hy)).eq
  have hle : conjSubgroup (c⁻¹ * a) V ≤ Subgroup.centralizer (V : Set G) :=
    conj_inv_le_centralizer (g := c) (a := a) hcomm'
  have hM : conjSubgroup (c⁻¹ * a) V ≤ M := by
    refine hle.trans ?_
    rw [← hS.sec5.toRootHyp.toHyp.normalizer_eq]
    exact Subgroup.centralizer_le_normalizer (V : Set G)
  have homega : conjSubgroup (c⁻¹ * a) V ∈ omegaSet V :=
    (mem_omegaSet_iff).mpr ⟨c⁻¹ * a, rfl⟩
  have hconj : conjSubgroup c⁻¹ (conjSubgroup a V) = conjSubgroup (c⁻¹ * a) V :=
    CGT.Timmesfeld75.conjSubgroup_conjSubgroup c⁻¹ a V
  rw [hconj]
  rcases h64 _ homega hM with hV | hsig
  · exfalso
    apply hCX
    rw [hCeq]
    have h1 : conjSubgroup c (conjSubgroup (c⁻¹ * a) V) = conjSubgroup c V := by rw [hV]
    rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
      show c * (c⁻¹ * a) = a by group] at h1
    exact h1.symm
  · exact hsig

private theorem card_eq_of_mem_omegaSet {A : Subgroup G} (hA : A ∈ omegaSet V) :
    Nat.card A = Nat.card V := by
  obtain ⟨g, rfl⟩ := (mem_omegaSet_iff).mp hA
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

private theorem isPGroup_of_mem_omegaSet (hS : Sec6Hyp M V) {A : Subgroup G}
    (hA : A ∈ omegaSet V) : IsPGroup 2 A := by
  obtain ⟨g, rfl⟩ := (mem_omegaSet_iff).mp hA
  exact hS.sec5.toRootHyp.toHyp.isPGroup_V.map _

private theorem le_KGen_of_mem_omegaSet {A : Subgroup G} (hA : A ∈ omegaSet V) :
    A ≤ KGen V := by
  obtain ⟨g, rfl⟩ := (mem_omegaSet_iff).mp hA
  intro x hx
  rw [mem_conjSubgroup] at hx
  have hx' : x = g * (g⁻¹ * x * g) * g⁻¹ := by group
  rw [hx']
  exact (Subgroup.normalClosure_normal (s := (V : Set G))).conj_mem _
    (Subgroup.subset_normalClosure hx) g

private theorem isPGroup_subgroupOf (hS : Sec6Hyp M V) {A : Subgroup G}
    (hA : A ∈ omegaSet V) : IsPGroup 2 ↥(A.subgroupOf (KGen V)) :=
  (isPGroup_of_mem_omegaSet hS hA).comap_subtype

private theorem exists_triple (hS : Sec6Hyp M V) :
    ∃ u v : ↥V, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v ∧ u * v ≠ 1 := by
  have hV := hS.sec5.toRootHyp.toHyp
  have h4 := hS.sec5.toRootHyp.four_le_card
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (V_ne_bot hS)
  have hu2 : u * u = 1 := by
    have h := hV.elem.2 (u : G) u.2
    rw [pow_two] at h
    exact Subtype.ext h
  have huord : orderOf u = 2 := by
    have h2 : (u : G) * (u : G) = 1 := congrArg Subtype.val hu2
    rw [← Subgroup.orderOf_coe u]
    exact orderOf_eq_prime (by rwa [pow_two]) (fun h => hu1 (Subtype.ext h))
  have hproper : Subgroup.zpowers u < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have hc : Nat.card ↥(Subgroup.zpowers u) = Nat.card ↥(⊤ : Subgroup ↥V) := by rw [htop]
    rw [Nat.card_zpowers, huord, Subgroup.card_top] at hc
    omega
  obtain ⟨v, -, hvnot⟩ := SetLike.exists_of_lt hproper
  have hv1 : v ≠ 1 := fun h => hvnot (h ▸ Subgroup.one_mem _)
  have hvu : u ≠ v := fun h => hvnot (h ▸ Subgroup.mem_zpowers _)
  have huv1 : u * v ≠ 1 := by
    intro h
    apply hvu
    have h' : (v : G) = (u : G)⁻¹ := by
      have h2 := congrArg Subtype.val h
      rw [Subgroup.coe_mul, Subgroup.coe_one] at h2
      exact eq_inv_of_mul_eq_one_right h2
    have hu2' : (u : G) * (u : G) = 1 := congrArg Subtype.val hu2
    rw [inv_eq_of_mul_eq_one_right hu2'] at h'
    exact Subtype.ext h'.symm
  exact ⟨u, v, hu1, hv1, hvu, huv1⟩

private theorem mem_omegaSet_of_mem_sigmaSet {U : Subgroup G} (hU : U ∈ sigmaSet M V) :
    U ∈ omegaSet V := by
  obtain ⟨g, rfl, -⟩ := hU
  exact (mem_omegaSet_iff).mpr ⟨g, rfl⟩

private theorem meetsSq_DGen (hS : Sec6Hyp M V) :
    Timmesfeld.Bridge.OddTransp.MeetsSq (DGen V) := by
  obtain ⟨u, v, hu1, hv1, huv, huv1⟩ := exists_triple (M := M) hS
  have huD : (u : G) ∈ Tim78.classD V := ⟨1, u, u.2, fun h => hu1 (Subtype.ext h), by simp⟩
  have hvD : (v : G) ∈ Tim78.classD V := ⟨1, v, v.2, fun h => hv1 (Subtype.ext h), by simp⟩
  have huvD : ((u * v : ↥V) : G) ∈ Tim78.classD V :=
    ⟨1, (u * v : ↥V), (u * v).2, fun h => huv1 (Subtype.ext h), by simp⟩
  have hcomm : Commute u v := hS.sec5.toRootHyp.toHyp.elem.1.is_comm.comm u v
  refine ⟨⟨u, Subgroup.le_normalClosure u.2⟩, huD, ⟨v, Subgroup.le_normalClosure v.2⟩, hvD,
    ?_, ?_, ?_⟩
  · intro h
    exact huv (Subtype.ext (by simpa using congrArg Subtype.val h))
  · apply Subtype.ext
    simpa using congrArg Subtype.val hcomm.eq
  · exact huvD

private theorem radical_KGen_eq_bot (hKnonab : ∃ a b : ↥(KGen V), a * b ≠ b * a)
    [IsSimpleGroup ↥(KGen V)] :
    ∀ N : Subgroup ↥(KGen V), N.Normal → Group.IsSolvable N → N = ⊥ := by
  intro N hN hsol
  haveI := hN
  rcases Subgroup.Normal.eq_bot_or_eq_top N with h | h
  · exact h
  · exfalso
    have hnc : ¬ IsMulCommutative ↥(KGen V) := fun hc => by
      obtain ⟨a, b, hab⟩ := hKnonab
      exact hab ((isMulCommutative_iff.mp hc) a b)
    haveI : Group.IsPerfect ↥(KGen V) :=
      TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hnc
    haveI : Group.IsSolvable ↥(⊤ : Subgroup ↥(KGen V)) := h ▸ hsol
    refine Group.IsPerfect.not_isSolvable ↥(KGen V) ?_
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup ↥(KGen V)) ≃* ↥(KGen V)).toMonoidHom)
      Subgroup.topEquiv.surjective

private theorem false_of_bender_sylow (hS : Sec6Hyp M V) (h60 : Sec6.Stmt60 M V)
    (hodd : Timmesfeld.Bridge.Asc72.IsOddTransp (Tim78.classD V))
    (hBend : CFSG.BenderSuzuki.IsBenderGroup ↥(KGen V)) : False := by
  have hV2 : IsPGroup 2 ↥(V.subgroupOf (KGen V)) :=
    (hS.sec5.toRootHyp.toHyp.isPGroup_V).comap_subtype
  obtain ⟨Q, hQ⟩ := hV2.exists_le_sylow
  obtain ⟨u, v, hu1, -, -, -⟩ := exists_triple (M := M) hS
  have huD : (u : G) ∈ Tim78.classD V := ⟨1, u, u.2, fun h => hu1 (Subtype.ext h), by simp⟩
  let z : ↥(KGen V) := ⟨u, Subgroup.le_normalClosure u.2⟩
  have hzQ : z ∈ (Q : Subgroup ↥(KGen V)) := hQ (Subgroup.mem_subgroupOf.mpr u.2)
  have hz2 : orderOf z = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hodd.orderOf_eq_two huD
  have hSE := CFSG.Timmesfeld.Bridge.Asc72.IsBenderGroup.isStronglyEmbeddedOrder_normalizer
    hBend Q
  have hCz : Subgroup.centralizer ({z} : Set ↥(KGen V)) ≤
      Subgroup.normalizer ((Q : Subgroup ↥(KGen V)) : Set ↥(KGen V)) :=
    CFSG.Goldschmidt.centralizer_le_of_stronglyEmbedded hSE hz2 (Subgroup.le_normalizer hzQ)
  have hUCgen : ∀ {U : Subgroup G}, U ∈ sigmaSet M V →
      U.subgroupOf (KGen V) ≤ Subgroup.centralizer ({z} : Set ↥(KGen V)) := by
    intro U hU x hx
    have hxU : (x : G) ∈ U := Subgroup.mem_subgroupOf.mp hx
    have hxV : (x : G) ∈ Subgroup.centralizer (V : Set G) :=
      (hS.sec5.le_M_of_mem_sigmaSet hU).2 hxU
    have hcomm := Subgroup.mem_centralizer_iff.mp hxV (u : G) u.2
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    simpa using hcomm.symm
  obtain ⟨U, hU⟩ := hS.ne
  obtain ⟨U', hU', hL2⟩ := h60.1 U hU
  have hUle : U ≤ KGen V := le_KGen_of_mem_omegaSet (mem_omegaSet_of_mem_sigmaSet hU)
  have hU'le : U' ≤ KGen V := le_KGen_of_mem_omegaSet (mem_omegaSet_of_mem_sigmaSet hU')
  have hmax : ∀ H : Subgroup ↥(KGen V), IsPGroup 2 ↥H →
      H ≤ Subgroup.normalizer ((Q : Subgroup ↥(KGen V)) : Set ↥(KGen V)) → H ≤ Q := by
    intro H hH hHN
    have hsup : IsPGroup 2 ↥(H ⊔ (Q : Subgroup ↥(KGen V))) :=
      IsPGroup.to_sup_of_normal_right' hH Q.isPGroup' hHN
    have heq : H ⊔ (Q : Subgroup ↥(KGen V)) = Q := Q.is_maximal' hsup le_sup_right
    rw [← heq]
    exact le_sup_left
  have hUQ : U.subgroupOf (KGen V) ≤ Q :=
    hmax _ (isPGroup_subgroupOf hS (mem_omegaSet_of_mem_sigmaSet hU))
      ((hUCgen hU).trans hCz)
  have hU'Q : U'.subgroupOf (KGen V) ≤ Q :=
    hmax _ (isPGroup_subgroupOf hS (mem_omegaSet_of_mem_sigmaSet hU'))
      ((hUCgen hU').trans hCz)
  have hsupQ : U.subgroupOf (KGen V) ⊔ U'.subgroupOf (KGen V) ≤ Q := sup_le hUQ hU'Q
  have h2 : IsPGroup 2 ↥(U.subgroupOf (KGen V) ⊔ U'.subgroupOf (KGen V)) :=
    Q.isPGroup'.to_le hsupQ
  have hcard4 : 4 ≤ Nat.card ↥(U.subgroupOf (KGen V)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUle).toEquiv,
      card_eq_of_mem_omegaSet (mem_omegaSet_of_mem_sigmaSet hU)]
    exact hS.sec5.toRootHyp.four_le_card
  have hL2K : IsL2Gen (U.subgroupOf (KGen V)) (U'.subgroupOf (KGen V)) :=
    hL2.subgroupOf hUle hU'le
  have hnonabH : ∃ a b : ↥(U.subgroupOf (KGen V) ⊔ U'.subgroupOf (KGen V)), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    refine hL2K.not_commuting ?_
    intro a ha b hb
    have h := hcon ⟨a, Subgroup.mem_sup_left ha⟩ ⟨b, Subgroup.mem_sup_right hb⟩
    exact congrArg Subtype.val h
  haveI : IsSimpleGroup ↥(U.subgroupOf (KGen V) ⊔ U'.subgroupOf (KGen V)) :=
    hL2K.isSimpleGroup hcard4
  have hnc : ¬ IsMulCommutative ↥(U.subgroupOf (KGen V) ⊔ U'.subgroupOf (KGen V)) := by
    obtain ⟨a, b, hab⟩ := hnonabH
    intro hc
    exact hab ((isMulCommutative_iff.mp hc) a b)
  obtain ⟨a, b, hab⟩ := hnonabH
  have ha1 : a ≠ 1 := fun h1 => hab (by rw [h1, one_mul, mul_one])
  haveI : Nontrivial ↥(U.subgroupOf (KGen V) ⊔ U'.subgroupOf (KGen V)) := ⟨a, 1, ha1⟩
  have hZ := TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc
  have hlt := h2.bot_lt_center (p := 2)
  rw [hZ] at hlt
  exact lt_irrefl _ hlt

private theorem false_of_disconnected (hB : Timmesfeld.Bridge.OddTranspBender)
    (hS : Sec6Hyp M V) (h60 : Sec6.Stmt60 M V)
    (hodd : Timmesfeld.Bridge.Asc72.IsOddTransp (Tim78.classD V))
    (hF : KGen V = generalizedFitting G)
    (hdisc : Connectivity.Disconnected (DGen V)) : False := by
  obtain ⟨hKsimple, hKnonab⟩ := simple_KGen hS hF
  haveI := hKsimple
  have hrad := radical_KGen_eq_bot (V := V) hKnonab
  have hsq := meetsSq_DGen (M := M) hS
  exact false_of_bender_sylow hS h60 hodd
    (hB _ _ (setup_DGen hS hF hodd) hrad hsq hdisc)

private theorem exists_common_neighbour (hS : Sec6Hyp M V)
    (h18 : Timmesfeld.Bridge.CommonNeighbourStmt)
    (hodd : Timmesfeld.Bridge.Asc72.IsOddTransp (Tim78.classD V))
    (hF : KGen V = generalizedFitting G) (hdisc : ¬ Connectivity.Disconnected (DGen V))
    {A B : Subgroup G} (hA : A ∈ omegaSet V) (hB : B ∈ omegaSet V)
    (hcomm : ⁅A, B⁆ ≠ ⊥) :
    ∃ C ∈ omegaSet V, C ≠ A ∧ C ≠ B ∧
      (∀ x ∈ A, ∀ y ∈ C, Commute x y) ∧ ∀ x ∈ B, ∀ y ∈ C, Commute x y := by
  classical
  have hAle : ¬ A ≤ Subgroup.centralizer (B : Set G) := fun hle =>
    hcomm ((Subgroup.commutator_eq_bot_iff_le_centralizer).mpr hle)
  obtain ⟨a, haA, haC⟩ := SetLike.not_le_iff_exists.mp hAle
  rw [Subgroup.mem_centralizer_iff] at haC
  push Not at haC
  obtain ⟨b, hbB, hab⟩ := haC
  have hab' : ¬ Commute a b := fun h => hab h.eq.symm
  have ha1 : a ≠ 1 := fun h => hab' (by rw [h]; exact Commute.one_left b)
  have hb1 : b ≠ 1 := fun h => hab' (by rw [h]; exact Commute.one_right a)
  have haK : a ∈ KGen V := le_KGen_of_mem_omegaSet hA haA
  have hbK : b ∈ KGen V := le_KGen_of_mem_omegaSet hB hbB
  let a' : ↥(KGen V) := ⟨a, haK⟩
  let b' : ↥(KGen V) := ⟨b, hbK⟩
  have haD : a' ∈ DGen V := mem_DGen_of_mem hA haA ha1 haK
  have hbD : b' ∈ DGen V := mem_DGen_of_mem hB hbB hb1 hbK
  have hnc : ¬ Commute a' b' := fun h =>
    hab' ((Subgroup.commute_subtype_iff _ _).mpr h)
  obtain ⟨e, heD, hea, heb⟩ :=
    h18 ↥(KGen V) (DGen V) (setup_DGen hS hF hodd)
      (fun x hx y hy => by
        by_contra h
        exact hdisc ⟨x, hx, y, hy, h⟩)
      (meetsSq_DGen (M := M) hS) a' haD b' hbD hnc
  have he1 : (e : G) ≠ 1 := fun h => DGen_ne_one heD (Subtype.ext h)
  have heaG : Commute (e : G) a := (Subgroup.commute_subtype_iff _ _).mpr hea
  have hebG : Commute (e : G) b := (Subgroup.commute_subtype_iff _ _).mpr heb
  obtain ⟨C, hC, heC⟩ := exists_omegaSet_of_mem_classD heD
  have hAC : ∀ x ∈ A, ∀ y ∈ C, Commute x y :=
    hS.sec5.toRootHyp.commute_of_commute_mem hA hC haA heC ha1 he1 heaG.symm
  have hBC : ∀ x ∈ B, ∀ y ∈ C, Commute x y :=
    hS.sec5.toRootHyp.commute_of_commute_mem hB hC hbB heC hb1 he1 hebG.symm
  refine ⟨C, hC, ?_, ?_, hAC, hBC⟩
  · intro hCA
    subst C
    refine hcomm ((Subgroup.commutator_eq_bot_iff_le_centralizer).mpr ?_)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hBC y hy x hx).eq
  · intro hCB
    subst C
    refine hcomm ((Subgroup.commutator_eq_bot_iff_le_centralizer).mpr ?_)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hAC x hx y hy).eq.symm

private theorem omega_pairs_of_connected (hS : Sec6Hyp M V)
    (h18 : Timmesfeld.Bridge.CommonNeighbourStmt)
    (hodd : Timmesfeld.Bridge.Asc72.IsOddTransp (Tim78.classD V))
    (h64 : ∀ B ∈ omegaSet V, B ≤ M → B = V ∨ B ∈ sigmaSet M V)
    (hF : KGen V = generalizedFitting G) (hdisc : ¬ Connectivity.Disconnected (DGen V)) :
    ∀ A ∈ omegaSet V, ∀ B ∈ omegaSet V, A ≠ B → ⁅A, B⁆ = ⊥ ∨ IsL2Gen A B := by
  classical
  intro A hA B hB' _
  by_cases hcomm : ⁅A, B⁆ = ⊥
  · exact Or.inl hcomm
  right
  obtain ⟨C, hC, hCA, hCB, hAC, hBC⟩ :=
    exists_common_neighbour (M := M) hS h18 hodd hF hdisc hA hB' hcomm
  obtain ⟨c, hCeq⟩ := (mem_omegaSet_iff).mp hC
  have hA1sig : conjSubgroup c⁻¹ A ∈ sigmaSet M V :=
    conj_inv_mem_sigmaSet (M := M) hS h64 hA hCA hAC hCeq
  have hB1sig : conjSubgroup c⁻¹ B ∈ sigmaSet M V :=
    conj_inv_mem_sigmaSet (M := M) hS h64 hB' hCB hBC hCeq
  have hAeq : conjSubgroup c (conjSubgroup c⁻¹ A) = A := by
    rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, mul_inv_cancel,
      CGT.Timmesfeld75.conjSubgroup_one]
  have hBeq : conjSubgroup c (conjSubgroup c⁻¹ B) = B := by
    rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, mul_inv_cancel,
      CGT.Timmesfeld75.conjSubgroup_one]
  rcases hS.res.s513 M V hS.sec5 (conjSubgroup c⁻¹ A) hA1sig
      (conjSubgroup c⁻¹ B) hB1sig with ⟨hbot, -⟩ | ⟨hL2, -⟩
  · exfalso
    apply hcomm
    have hmap := Subgroup.map_commutator (f := (MulAut.conj c).toMonoidHom)
      (H₁ := conjSubgroup c⁻¹ A) (H₂ := conjSubgroup c⁻¹ B)
    rw [hbot, Subgroup.map_bot] at hmap
    change ⊥ = ⁅conjSubgroup c (conjSubgroup c⁻¹ A),
      conjSubgroup c (conjSubgroup c⁻¹ B)⁆ at hmap
    rw [hAeq, hBeq] at hmap
    exact hmap.symm
  · have hconj := hL2.conj c
    rwa [hAeq, hBeq] at hconj

theorem Sec6Hyp.omega_pairs
    (hB : Timmesfeld.Bridge.OddTranspBender) (hS : Sec6Hyp M V) (h60 : Sec6.Stmt60 M V)
    (h18 : Timmesfeld.Bridge.CommonNeighbourStmt)
    (hodd : Timmesfeld.Bridge.Asc72.IsOddTransp (Tim78.classD V))
    (h64 : ∀ B ∈ omegaSet V, B ≤ M → B = V ∨ B ∈ sigmaSet M V)
    (hF : Subgroup.normalClosure (V : Set G) = generalizedFitting G) :
    ∀ A ∈ omegaSet V, ∀ B ∈ omegaSet V, A ≠ B → ⁅A, B⁆ = ⊥ ∨ IsL2Gen A B := by
  classical
  intro A hA B hB' hAB
  by_cases hdisc : Connectivity.Disconnected (DGen V)
  · exact (false_of_disconnected hB hS h60 hodd hF hdisc).elim
  · exact omega_pairs_of_connected hS h18 hodd h64 hF hdisc A hA B hB' hAB
