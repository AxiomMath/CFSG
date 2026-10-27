module

public import CFSG.OddTranspositions.PartThree.EightEight.KOneRadical
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs
public import CFSG.Timmesfeld.Bridge.Asc72Defs

import CFSG.OddTranspositions.PartThree.EightEight.StarSigma
import CFSG.OddTranspositions.PartThree.EightEight.WreathNatural
import CFSG.OddTranspositions.PartThree.EightFive.Transitive
import CFSG.OddTranspositions.WidthOne
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
import CFSG.Timmesfeld.Bridge.OddTranspBasic

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem isBenderGroup_closure_conjOrbit_quotient_center (h1 : Asc72.TheoremOne)
    (h86 : Lemma8_6) (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥)
    (hO4 : ¬ O4PairData G D) (hF : FaithfulOnBlocks hC.alpha)
    (hne : derivedSeries (Halpha D hC.alpha) 1 ≠ derivedSeries (Halpha D hC.alpha) 2)
    {x w y : G} (ht : IsTriangle D x w y) {n : ℕ} (hn : Odd n)
    (hord : orderOf (x * y * w) = 2 * n) :
    CFSG.BenderSuzuki.IsBenderGroup
      (Subgroup.closure (conjOrbit (localGroup D ((x * y * w) ^ n)) x) ⧸
        Subgroup.center (Subgroup.closure (conjOrbit (localGroup D ((x * y * w) ^ n)) x))) := by
  classical
  let z : G := (x * y * w) ^ n
  let Δ₁ : Set G := conjOrbit (localGroup D z) x
  let K₁ : Subgroup G := Subgroup.closure Δ₁
  change CFSG.BenderSuzuki.IsBenderGroup (K₁ ⧸ Subgroup.center K₁)
  have hthird := IsTriangle.third_kind hC.setup.oddT hC.setup.normal ht hn hord
  have hzx : Commute z x := by simpa [z] using hthird.2.2.1
  have hxc : x ∈ centSet D z := ⟨ht.1, hzx.symm⟩
  have hΔD : Δ₁ ⊆ D := fun a ha => (conjOrbit_subset_centSet hC.setup.normal hxc ha).1
  have hΔz : ∀ a ∈ Δ₁, Commute a z := fun a ha =>
    (conjOrbit_subset_centSet hC.setup.normal hxc ha).2
  have hxΔ : x ∈ Δ₁ := self_mem_conjOrbit _ x
  have hpowdata := pow_mem_closure_conjOrbit hC.setup ht hn hord
  have hzK₁ : z ∈ K₁ := by simpa [K₁, Δ₁, z] using hpowdata.1
  have hzcenter : (⟨z, hzK₁⟩ : K₁) ∈ Subgroup.center K₁ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hpowdata.2 (g : G) (by simpa [K₁, Δ₁, z] using g.2)).eq
  have horb : conjOrbit K₁ x = Δ₁ := by
    simpa [K₁, Δ₁, z] using conjOrbit_closure_conjOrbit_eq hC.setup ht hn hord
  have hcls : ∃ t : K₁, inClosure Δ₁ = {g | IsConj t g} :=
    isClass_inClosure_of_conjOrbit_closure_eq hxΔ horb
  have hS : Setup K₁ (inClosure Δ₁) := setup_inClosure hC.setup.oddT hΔD hcls
  have h31 : ∀ a ∈ Δ₁, ∃ a' ∈ Δ₁, a' ≠ a ∧ Commute a a' ∧
      {r | r ∈ Δ₁ ∧ Commute r a} = {a, a', a * a' * z} := fun a ha => by
    simpa [Δ₁, z] using
      exists_setOf_commute_mem_conjOrbit_eq h86 h87 hC hrad hO4 hF hne ht hn hord (a := a)
        (by simpa [Δ₁, z] using ha)
  have htrans : ∀ {a b c : G}, a ∈ Δ₁ → b ∈ Δ₁ → c ∈ Δ₁ → Commute a b → Commute b c →
      Commute a c := by
    intro a b c ha hb hc hab hbc
    obtain ⟨b', hb', -, hbb', hset⟩ := h31 b hb
    have c1 : Commute b (b * b' * z) :=
      ((Commute.refl b).mul_right hbb').mul_right (hΔz b hb)
    have c2 : Commute b' (b * b' * z) :=
      (hbb'.symm.mul_right (Commute.refl b')).mul_right (hΔz b' hb')
    have ha' : a ∈ ({b, b', b * b' * z} : Set G) := by
      rw [← hset]
      exact ⟨ha, hab⟩
    have hc' : c ∈ ({b, b', b * b' * z} : Set G) := by
      rw [← hset]
      exact ⟨hc, hbc.symm⟩
    rcases ha' with rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl <;>
      first
      | exact Commute.refl _
      | exact hbb'
      | exact hbb'.symm
      | exact c1
      | exact c1.symm
      | exact c2
      | exact c2.symm
  have hinj := injOn_mk_center_closure_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn hord
  have hcomm : ∀ {a b : K₁}, a ∈ inClosure Δ₁ → b ∈ inClosure Δ₁ →
      (Commute (QuotientGroup.mk' (Subgroup.center K₁) a)
        (QuotientGroup.mk' (Subgroup.center K₁) b) ↔ Commute (a : G) (b : G)) := by
    intro a b ha hb
    rw [commute_mk_center_closure_conjOrbit_iff hC ht hn hord ha hb]
    exact ⟨fun h => h.map K₁.subtype, fun h => Subtype.ext h.eq⟩
  have hne1 : ∀ d ∈ inClosure Δ₁, QuotientGroup.mk' (Subgroup.center K₁) d ≠ 1 := by
    intro d hd hd1
    have hdZ : d ∈ Subgroup.center K₁ := (QuotientGroup.eq_one_iff d).mp hd1
    obtain ⟨c, hc, hdc⟩ := exists_not_commute_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht hn
      hord (a := (d : G)) (by simpa [Δ₁, z] using hd)
    have hcK : c ∈ K₁ := Subgroup.subset_closure (by simpa [Δ₁, z] using hc)
    exact hdc (congrArg Subtype.val (Subgroup.mem_center_iff.mp hdZ ⟨c, hcK⟩)).symm
  set E : Set (K₁ ⧸ Subgroup.center K₁) :=
    QuotientGroup.mk' (Subgroup.center K₁) '' inClosure Δ₁ with hE
  have hSQ : Setup (K₁ ⧸ Subgroup.center K₁) E :=
    hS.map _ (QuotientGroup.mk'_surjective _) hne1
  have hradQ : ∀ N : Subgroup (K₁ ⧸ Subgroup.center K₁), N.Normal → Group.IsSolvable N →
      N = ⊥ := by
    have h36 : CFSG.solvableRadical K₁ = Subgroup.center K₁ := by
      simpa [K₁, Δ₁, z] using
        solvableRadical_closure_conjOrbit_eq_center h86 h87 hC hrad hO4 hF hne ht hn hord
    intro N hN hNs
    let e : K₁ ⧸ Subgroup.center K₁ ≃* K₁ ⧸ CFSG.solvableRadical K₁ :=
      QuotientGroup.quotientMulEquivOfEq h36.symm
    have hmapN : (N.map e.toMonoidHom).Normal := hN.map e.toMonoidHom e.surjective
    have hmapS : Group.IsSolvable (N.map e.toMonoidHom) :=
      solvable_of_surjective (f := (N.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
        (N.equivMapOfInjective e.toMonoidHom e.injective).surjective
    have hle := CFSG.Timmesfeld.Bridge.OddTransp.le_solvableRadical hmapN hmapS
    rw [CFSG.SignalizerFunctorTheorem.Nonsolvable.solvableRadical_quotient, le_bot_iff] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective N e.injective).mp hle
  have htransQ : ∀ {u v t : K₁ ⧸ Subgroup.center K₁}, u ∈ E → v ∈ E → t ∈ E →
      Commute u v → Commute v t → Commute u t := by
    rintro _ _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩ ⟨c, hc, rfl⟩ hab hbc
    exact (hcomm ha hc).mpr (htrans ha hb hc ((hcomm ha hb).mp hab) ((hcomm hb hc).mp hbc))
  obtain ⟨a', ha', ha'x, hxa', hset⟩ := h31 x hxΔ
  let xK : K₁ := ⟨x, Subgroup.subset_closure hxΔ⟩
  let aK : K₁ := ⟨a', Subgroup.subset_closure ha'⟩
  have hxaz : x * a' * z ∈ Δ₁ := by
    have h : x * a' * z ∈ ({x, a', x * a' * z} : Set G) := Or.inr (Or.inr rfl)
    rw [← hset] at h
    exact h.1
  have hxE : QuotientGroup.mk' (Subgroup.center K₁) xK ∈ E := ⟨xK, hxΔ, rfl⟩
  have haE : QuotientGroup.mk' (Subgroup.center K₁) aK ∈ E := ⟨aK, ha', rfl⟩
  have hxa_ne : QuotientGroup.mk' (Subgroup.center K₁) xK ≠
      QuotientGroup.mk' (Subgroup.center K₁) aK := fun h =>
    ha'x (congrArg Subtype.val (hinj (show xK ∈ inClosure Δ₁ from hxΔ)
      (show aK ∈ inClosure Δ₁ from ha') h)).symm
  have hxa_comm : Commute (QuotientGroup.mk' (Subgroup.center K₁) xK)
      (QuotientGroup.mk' (Subgroup.center K₁) aK) :=
    (hcomm (show xK ∈ inClosure Δ₁ from hxΔ) (show aK ∈ inClosure Δ₁ from ha')).mpr hxa'
  have hxa_mem : QuotientGroup.mk' (Subgroup.center K₁) xK *
      QuotientGroup.mk' (Subgroup.center K₁) aK ∈ E := by
    have hz1 : QuotientGroup.mk' (Subgroup.center K₁) ⟨z, hzK₁⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hzcenter
    refine ⟨xK * aK * ⟨z, hzK₁⟩, hxaz, ?_⟩
    rw [map_mul, map_mul, hz1, mul_one]
  have hH : ∃ H : Subgroup (K₁ ⧸ Subgroup.center K₁), H ≠ ⊤ ∧ (∃ u ∈ E, u ∈ H) ∧
      ∀ u ∈ E, u ∈ H → ∀ v ∈ E, Commute u v → v ∈ H := by
    refine ⟨Subgroup.centralizer {QuotientGroup.mk' (Subgroup.center K₁) xK}, ?_,
      ⟨_, hxE, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩, ?_⟩
    · intro htop
      obtain ⟨c, hc, hxc'⟩ := exists_not_commute_of_mem_conjOrbit h86 h87 hC hrad hO4 hF hne ht
        hn hord (a := x) (by simpa [Δ₁, z] using hxΔ)
      have hcΔ : c ∈ Δ₁ := by simpa [Δ₁, z] using hc
      let cK : K₁ := ⟨c, Subgroup.subset_closure hcΔ⟩
      have hmem : QuotientGroup.mk' (Subgroup.center K₁) cK ∈
          Subgroup.centralizer {QuotientGroup.mk' (Subgroup.center K₁) xK} :=
        htop ▸ Subgroup.mem_top _
      have hc1 : Commute (QuotientGroup.mk' (Subgroup.center K₁) cK)
          (QuotientGroup.mk' (Subgroup.center K₁) xK) :=
        Subgroup.mem_centralizer_singleton_iff.mp hmem
      exact hxc' ((hcomm (show cK ∈ inClosure Δ₁ from hcΔ)
        (show xK ∈ inClosure Δ₁ from hxΔ)).mp hc1).symm
    · intro u hu huH v hv huv
      rw [Subgroup.mem_centralizer_singleton_iff] at huH ⊢
      exact (htransQ hxE hu hv huH.symm huv).symm.eq
  rcases h1 (K₁ ⧸ Subgroup.center K₁) E hSQ.isClass hSQ.oddT.1 hSQ.oddT.2 hSQ.gen hradQ hH with
    hB | ⟨f, m, hf, hm, ⟨φ⟩⟩ | hAS
  · exact hB
  ·
    exfalso
    have hEφ := eq_preimage_swapSet_of_mulEquiv hSQ hf hm φ
    have hsign : ∀ s ∈ WreathEndgame.swapSet f m, Equiv.Perm.sign s.right = -1 := by
      rintro s ⟨i, j, hij, hr, -, -⟩
      rw [hr, Equiv.Perm.sign_swap hij]
    have hu : φ (QuotientGroup.mk' (Subgroup.center K₁) xK) ∈ WreathEndgame.swapSet f m := by
      have h := hxE
      rw [hEφ] at h
      exact h
    have hv : φ (QuotientGroup.mk' (Subgroup.center K₁) aK) ∈ WreathEndgame.swapSet f m := by
      have h := haE
      rw [hEφ] at h
      exact h
    have huv : φ (QuotientGroup.mk' (Subgroup.center K₁) xK *
        QuotientGroup.mk' (Subgroup.center K₁) aK) ∈ WreathEndgame.swapSet f m := by
      have h := hxa_mem
      rw [hEφ] at h
      exact h
    have h := hsign _ huv
    rw [map_mul, SemidirectProduct.mul_right, map_mul, hsign _ hu, hsign _ hv] at h
    exact absurd h (by decide)
  ·
    exfalso
    obtain ⟨M, hMnorm, -, -, -, -, hidx, hW, -⟩ := hAS
    haveI : M.Normal := hMnorm
    have hneM : ∀ e ∈ E, QuotientGroup.mk' M e ≠ 1 := by
      intro e he he1
      have heM : e ∈ M := (QuotientGroup.eq_one_iff e).mp he1
      have htop : M = ⊤ := hSQ.eq_top_of_subset M fun e' he' => by
        obtain ⟨g, rfl⟩ := isConj_iff.mp (hSQ.isConj he he')
        exact hMnorm.conj_mem e heM g
      rw [htop, Subgroup.index_top] at hidx
      omega
    have hSM : Setup ((K₁ ⧸ Subgroup.center K₁) ⧸ M) (QuotientGroup.mk' M '' E) :=
      hSQ.map _ (QuotientGroup.mk'_surjective M) hneM
    have heq := eq_of_commute_of_widthOne hSM hW ⟨_, hxE, rfl⟩ ⟨_, haE, rfl⟩
      (hxa_comm.map (QuotientGroup.mk' M))
    apply hneM _ hxa_mem
    rw [map_mul, heq, ← map_mul, hSQ.oddT.mul_self_eq_one haE, map_one]

end CFSG.OddTranspositions.PartThree.EightEight

end
