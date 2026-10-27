module

public import CFSG.OddTranspositions.PartThree.EightEight.ASNZAlmostSimple

import CFSG.LieType.CurtisTits.Recognition
import CFSG.OddTranspositions.BenderMeetsSq
import CFSG.OddTranspositions.PartThree.EightEight.ASNZRadical
import CFSG.OddTranspositions.PartThree.EightEight.WreathNatural
import CFSG.OddTranspositions.PartThree.OddTranspClosure
import CFSG.OddTranspositions.PartThree.Ten.SetupQ
import CFSG.OddTranspositions.PartThree.Ten.TenTwoCover
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.Timmesfeld.Bridge.Asc72Lift
import CFSG.Timmesfeld.Bridge.OddLocalRootCore
import CFSG.Timmesfeld.Bridge.OddTranspBasic

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity

private theorem localBender_map_of_ker_le_center {Y₀ Y : Type} [Group Y₀] [Finite Y₀] [Group Y]
    {Λ₀ : Set Y₀} {Λ : Set Y} (π : Y₀ →* Y) (hker : π.ker ≤ Subgroup.center Y₀) {d : Y₀}
    (himage : π '' commSet Λ₀ d = commSet Λ (π d)) (hL : LocalBender Λ₀ d) :
    LocalBender Λ (π d) := by
  classical
  let K : Subgroup Y₀ := Subgroup.closure (commSet Λ₀ d)
  let K' : Subgroup Y := Subgroup.closure (commSet Λ (π d))
  have hKmap : K.map π = K' := by
    change (Subgroup.closure (commSet Λ₀ d)).map π = Subgroup.closure (commSet Λ (π d))
    rw [MonoidHom.map_closure, himage]
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    rw [← himage] at hx hy
    obtain ⟨x₀, hx₀, rfl⟩ := hx
    obtain ⟨y₀, hy₀, rfl⟩ := hy
    obtain ⟨g, hg, hgxy⟩ := hL.transitive x₀ hx₀ y₀ hy₀
    refine ⟨π g, ?_, ?_⟩
    · show π g ∈ K'
      rw [← hKmap]
      exact Subgroup.mem_map_of_mem π hg
    rw [← map_inv, ← map_mul, ← map_mul, hgxy]
  ·
    let ρ : K →* K' := (π.comp K.subtype).codRestrict K' fun k => by
      rw [← hKmap]
      exact Subgroup.mem_map_of_mem π k.2
    have hρ : Function.Surjective ρ := by
      rintro ⟨y, hy⟩
      rw [← hKmap] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      exact ⟨⟨k, hk⟩, rfl⟩
    have hρker : ρ.ker ≤ Subgroup.center K := by
      intro k hk
      have hk' : (k : Y₀) ∈ π.ker := congrArg Subtype.val (MonoidHom.mem_ker.mp hk)
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_center_iff.mp (hker hk') g)
    let S : Subgroup K' := (Subgroup.center K).map ρ
    have : S.Normal := (inferInstance : (Subgroup.center K).Normal).map ρ hρ
    have hSc : S ≤ Subgroup.center K' := Subgroup.map_center_le_center hρ
    let ψ : K →* K' ⧸ S := (QuotientGroup.mk' S).comp ρ
    have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective S).comp hρ
    have hψker : ψ.ker = Subgroup.center K := by
      rw [show ψ = (QuotientGroup.mk' S).comp ρ from rfl, ← MonoidHom.comap_ker,
        QuotientGroup.ker_mk']
      exact Subgroup.comap_map_eq_self hρker
    let e₁ : K ⧸ Subgroup.center K ≃* K' ⧸ S :=
      (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
    have : IsSimpleGroup (K ⧸ Subgroup.center K) := Asc72.IsBenderGroup.isSimpleGroup hL.bender
    have hsimp : IsSimpleGroup (K' ⧸ S) := e₁.symm.isSimpleGroup
    obtain ⟨u, v, huv⟩ := Asc72.IsBenderGroup.exists_not_commute hL.bender
    have hZ : Subgroup.center K' = S :=
      CFSG.LieType.CurtisTits.center_eq_of_isSimpleGroup_quotient S hSc hsimp
        ⟨e₁ u, e₁ v, fun h => huv (e₁.injective (by rw [map_mul, map_mul]; exact h))⟩
    exact OddLocal.isBenderGroup_of_mulEquiv'
      (e₁.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)) hL.bender

variable {X : Type} [Group X] [Finite X] {E : Set X}

theorem exists_mulEquiv_l2Wreath_three_of_commSet (h1 : TheoremOne) (h91 : Theorem9_1)
    (hS : Setup X E) (hdisc : Disconnected E) {s z : X} (hs : s ∈ E)
    (hzs : z * s ∈ Subgroup.center X)
    (h31 : ∀ a ∈ commSet E s, ∃ a' ∈ commSet E s, a' ≠ a ∧ Commute a a' ∧
      {r | r ∈ commSet E s ∧ Commute r a} = {a, a', a * a' * z})
    (hL : LocalBender E s) :
    ∃ f : ℕ, 2 ≤ f ∧ Nonempty (X ⧸ Subgroup.center X ≃* L2Wreath f 3) := by
  have hfour : ∀ i j : Fin 4, i ≠ j → ∃ k l : Fin 4, k ≠ l ∧ k ≠ i ∧ k ≠ j ∧ l ≠ i ∧ l ≠ j := by
    decide
  classical
  have hs2 : s * s = 1 := hS.oddT.mul_self_eq_one hs
  have hzsc : ∀ g : X, Commute g (z * s) := fun g => Subgroup.mem_center_iff.mp hzs g
  have hΔz : ∀ a ∈ commSet E s, Commute a z := by
    intro a ha
    have h := (hzsc a).mul_right ha.2.1.inv_right
    rwa [mul_inv_cancel_right] at h
  have hnab : ¬ (commSet E s).Pairwise Commute := by
    intro hP
    obtain ⟨u, v, huv⟩ := Asc72.IsBenderGroup.exists_not_commute hL.bender
    obtain ⟨u', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center _) u
    obtain ⟨v', rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center _) v
    have hc : Commute u' v' := (Subgroup.isMulCommutative_closure hP).is_comm.comm u' v'
    exact huv (hc.map _)
  obtain ⟨a₀, ha₀⟩ : (commSet E s).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    exact hnab (h ▸ Set.pairwise_empty _)
  have hz : z ∈ Subgroup.closure (commSet E s) := by
    obtain ⟨a', ha', -, -, hset⟩ := h31 a₀ ha₀
    have hmem : a₀ * a' * z ∈ commSet E s := by
      have h : a₀ * a' * z ∈ ({a₀, a', a₀ * a' * z} : Set X) := Or.inr (Or.inr rfl)
      rw [← hset] at h
      exact h.1
    have h := (Subgroup.closure (commSet E s)).mul_mem
      ((Subgroup.closure (commSet E s)).inv_mem ((Subgroup.closure (commSet E s)).mul_mem
        (Subgroup.subset_closure ha₀) (Subgroup.subset_closure ha')))
      (Subgroup.subset_closure hmem)
    rwa [show (a₀ * a')⁻¹ * (a₀ * a' * z) = z by group] at h
  have hzs' : Commute z s := WreathEndgame.commute_of_mem_closure_commSet hz
  have hD : ∀ a ∈ commSet E s, ∃ b ∈ commSet E s, ¬ Commute a b := by
    intro a ha
    by_contra hcon
    push Not at hcon
    apply hnab
    have hle : Subgroup.closure (commSet E s) ≤ Subgroup.centralizer {a} := by
      rw [Subgroup.closure_le]
      intro c hc
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcon c hc).symm.eq
    have hsingle : ∀ b ∈ commSet E s, b = a := by
      intro b hb
      obtain ⟨g, hg, rfl⟩ := hL.transitive a ha b hb
      have hga : Commute g a := Subgroup.mem_centralizer_singleton_iff.mp (hle hg)
      rw [hga.eq, mul_inv_cancel_right]
    intro x hx y hy hxy
    exact absurd ((hsingle x hx).trans (hsingle y hy).symm) hxy
  have hz2 : z * z = 1 := by
    obtain ⟨a', ha', -, haa', hset⟩ := h31 a₀ ha₀
    have hmem : a₀ * a' * z ∈ commSet E s := by
      have h : a₀ * a' * z ∈ ({a₀, a', a₀ * a' * z} : Set X) := Or.inr (Or.inr rfl)
      rw [← hset] at h
      exact h.1
    have h2 := hS.oddT.mul_self_eq_one hmem.1
    have hc2 : a₀ * a' * (a₀ * a') = 1 := by
      rw [haa'.symm.mul_mul_mul_comm a₀ a', hS.oddT.mul_self_eq_one ha₀.1,
        hS.oddT.mul_self_eq_one ha'.1, one_mul]
    have hcz : Commute z (a₀ * a') := (hΔz a₀ ha₀).symm.mul_right (hΔz a' ha').symm
    rwa [hcz.mul_mul_mul_comm, hc2, one_mul] at h2
  have hcentE : ∀ c ∈ E, c ∉ Subgroup.center X := by
    intro c hc hcz
    have heq : ∀ e ∈ E, e = c := by
      intro e he
      obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj hc he)
      rw [Subgroup.mem_center_iff.mp hcz g, mul_inv_cancel_right]
    exact ha₀.2.2 ((heq a₀ ha₀.1).trans (heq s hs).symm)
  have hszs : s * (z * s) = z := by
    rw [← mul_assoc, hzs'.symm.eq, mul_assoc, hs2, mul_one]
  have hrad : CFSG.solvableRadical X = Subgroup.center X :=
    solvableRadical_eq_center_of_commSet hS hs hzs (by rw [hszs]; exact hz) hD
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hnc : ∀ a ∈ E, ∃ b ∈ E, ¬ Commute a b := by
    intro a ha
    by_contra hcon
    push Not at hcon
    apply hcentE a ha
    have hle : Subgroup.closure E ≤ Subgroup.centralizer {a} := by
      rw [Subgroup.closure_le]
      intro c hc
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcon c hc).symm.eq
    rw [hS.gen] at hle
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g))
  have hinj : Set.InjOn π E := injOn_mk_of_le_center hS.oddT le_rfl hnc
  have hrefl : ∀ {a b : X}, a ∈ E → b ∈ E → Commute (π a) (π b) → Commute a b :=
    fun ha hb h => commute_of_commute_mk_of_le_center' hS.oddT le_rfl ha hb h
  have hne1 : ∀ e ∈ E, π e ≠ 1 := fun e he h => hcentE e he ((QuotientGroup.eq_one_iff e).mp h)
  have hSQ : Setup (X ⧸ Subgroup.center X) (π '' E) := hS.map π hπ hne1
  have hs2Q : π s * π s = 1 := by rw [← map_mul, hs2, map_one]
  have hπz : π z = π s := by
    have h1 : π z * π s = 1 := by rw [← map_mul]; exact (QuotientGroup.eq_one_iff _).mpr hzs
    calc π z = π z * (π s * π s) := by rw [hs2Q, mul_one]
      _ = π s := by rw [← mul_assoc, h1, one_mul]
  have himage : π '' commSet E s = commSet (π '' E) (π s) := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha.1, rfl⟩, ha.2.1.map π, fun h => ha.2.2 (hinj ha.1 hs h)⟩
    · rintro ⟨⟨a, ha, rfl⟩, hc, hne⟩
      exact ⟨a, ⟨ha, hrefl ha hs hc, fun h => hne (by rw [h])⟩, rfl⟩
  have hdiscQ : Disconnected (π '' E) := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hdisc
    refine ⟨π x, ⟨x, hx, rfl⟩, π y, ⟨y, hy, rfl⟩, fun h => hxy ?_⟩
    refine Asc72.reach_of_reach_quotient hS.oddT (fun a ha b hb hab => ?_) hx hy h
    rw [hinj ha hb (QuotientGroup.eq.mpr hab)]
    exact reach_refl b
  have hradQ : ∀ N : Subgroup (X ⧸ Subgroup.center X), N.Normal → Group.IsSolvable N →
      N = ⊥ := by
    intro N hN hNs
    let e : X ⧸ Subgroup.center X ≃* X ⧸ CFSG.solvableRadical X :=
      QuotientGroup.quotientMulEquivOfEq hrad.symm
    have hmapN : (N.map e.toMonoidHom).Normal := hN.map e.toMonoidHom e.surjective
    have hmapS : Group.IsSolvable (N.map e.toMonoidHom) :=
      solvable_of_surjective (f := (N.equivMapOfInjective e.toMonoidHom e.injective).toMonoidHom)
        (N.equivMapOfInjective e.toMonoidHom e.injective).surjective
    have hle := CFSG.Timmesfeld.Bridge.OddTransp.le_solvableRadical hmapN hmapS
    rw [CFSG.SignalizerFunctorTheorem.Nonsolvable.solvableRadical_quotient, le_bot_iff] at hle
    exact (Subgroup.map_eq_bot_iff_of_injective N e.injective).mp hle
  obtain ⟨H, hHtop, ⟨v, hv, hvH⟩, hclosed⟩ := exists_subgroup_of_disconnected hSQ hdiscQ
  rcases h1 (X ⧸ Subgroup.center X) (π '' E) hSQ.isClass hSQ.oddT.1 hSQ.oddT.2 hSQ.gen hradQ
      ⟨H, hHtop, ⟨v, hv, hvH⟩, hclosed⟩ with hB | ⟨f, m, hf, hm, ⟨φ⟩⟩ | hAS
  ·
    exfalso
    obtain ⟨_, ⟨u, hu, rfl⟩, _, ⟨w, hw, rfl⟩, huw, hcuw, ⟨c, hc, hcuw'⟩⟩ :=
      CFSG.OddTranspositions.bender_meetsSq hB hSQ.isClass hSQ.oddT.1
    obtain ⟨g, hg⟩ := isConj_iff.mp (hS.isConj hu hs)
    have huw' : Commute u w := hrefl hu hw hcuw
    have hcu : Commute c u := hrefl hc hu (by rw [hcuw']; exact (Commute.refl _).mul_left hcuw.symm)
    have hcw : Commute c w := hrefl hc hw (by rw [hcuw']; exact hcuw.mul_left (Commute.refl _))
    have hcu1 : c ≠ u := by
      rintro rfl
      apply hne1 w hw
      calc π w = (π c)⁻¹ * (π c * π w) := by group
        _ = 1 := by rw [← hcuw', inv_mul_cancel]
    have hcw1 : c ≠ w := by
      rintro rfl
      apply hne1 u hu
      calc π u = π u * π c * (π c)⁻¹ := by group
        _ = 1 := by rw [← hcuw', mul_inv_cancel]
    set b := g * w * g⁻¹ with hb
    set c' := g * c * g⁻¹ with hc'
    have hconj_ne : ∀ {x y : X}, x ≠ y → g * x * g⁻¹ ≠ g * y * g⁻¹ := fun hxy h =>
      hxy (by simpa using h)
    have hbΔ : b ∈ commSet E s :=
      ⟨hS.normal g w hw, hg ▸ (huw'.symm.conj g), hg ▸ hconj_ne (fun h => huw (congrArg π h).symm)⟩
    have hcΔ : c' ∈ commSet E s :=
      ⟨hS.normal g c hc, hg ▸ hcu.conj g, hg ▸ hconj_ne hcu1⟩
    have hbc : Commute c' b := hcw.conj g
    have hπc : π c' = π s * π b := by
      rw [← hg, hc', hb]
      simp only [map_mul, map_inv, hcuw']
      group
    obtain ⟨b', hb', -, -, hset⟩ := h31 b hbΔ
    have hbcz : b * c' * z ∈ commSet E s := by
      have h : c' ∈ {r | r ∈ commSet E s ∧ Commute r b} := ⟨hcΔ, hbc⟩
      rw [hset] at h
      rcases h with h | h | h
      · exact absurd h (hconj_ne hcw1)
      · rw [h]
        have h' : b * b' * z ∈ ({b, b', b * b' * z} : Set X) := Or.inr (Or.inr rfl)
        rw [← hset] at h'
        exact h'.1
      · rw [h]
        have hbb : b * b = 1 := hS.oddT.mul_self_eq_one hbΔ.1
        have hrw : b * (b * b' * z) * z = b' := by
          calc b * (b * b' * z) * z = (b * b) * b' * (z * z) := by group
            _ = b' := by rw [hbb, hz2, one_mul, mul_one]
        rw [hrw]
        exact hb'
    apply hne1 _ hbcz.1
    have hsb : Commute (π s) (π b) := hbΔ.2.1.symm.map π
    have hb2 : π b * π b = 1 := by rw [← map_mul, hS.oddT.mul_self_eq_one hbΔ.1, map_one]
    rw [map_mul, map_mul, hπc, hπz, hsb.eq]
    calc π b * (π b * π s) * π s = (π b * π b) * (π s * π s) := by group
      _ = 1 := by rw [hb2, hs2Q, one_mul]
  · rcases hm with rfl | rfl
    · exact ⟨f, hf, ⟨φ⟩⟩
    exfalso
    let ψ : X →* L2Wreath f 4 := φ.toMonoidHom.comp π
    have hEφ := eq_preimage_swapSet_of_mulEquiv hSQ hf (Or.inr rfl) φ
    have hψE : ∀ e ∈ E, ψ e ∈ WreathEndgame.swapSet f 4 := by
      intro e he
      have h : π e ∈ π '' E := ⟨e, he, rfl⟩
      rw [hEφ] at h
      exact h
    have hψs := hψE s hs
    obtain ⟨i, j, hij, hsr, -, -⟩ := hψs
    obtain ⟨k, l, hkl, hki, hkj, hli, hlj⟩ := hfour i j hij
    let w : L2Wreath f 4 := SemidirectProduct.inr (Equiv.swap k l)
    have hw : w ∈ WreathEndgame.swapSet f 4 := ⟨k, l, hkl, rfl, fun _ _ _ => rfl, by simp [w]⟩
    have hwD : w ∈ WreathEndgame.disjSwaps f 4 (Equiv.swap i j) :=
      ⟨hw, (WreathEndgame.swapDisjoint_iff hkl hij).mpr ⟨hki, hkj, hli, hlj⟩⟩
    have hwC := WreathEndgame.disjSwaps_subset_commSet hij (hψE s hs) hsr hwD
    obtain ⟨a, ha, hψa⟩ : ∃ a ∈ E, ψ a = w := by
      have h : φ.symm w ∈ π '' E := by
        rw [hEφ]
        simpa using hw
      obtain ⟨a, ha, hπa⟩ := h
      exact ⟨a, ha, by simp [ψ, hπa]⟩
    have haΔ : a ∈ commSet E s := by
      refine ⟨ha, hrefl ha hs ?_, fun has => hwC.2.2 (by rw [← hψa, has])⟩
      have h := (hψa ▸ hwC.2.1 : Commute (ψ a) (ψ s)).map φ.symm.toMonoidHom
      simpa [ψ] using h
    have hwD' : ψ a ∈ WreathEndgame.disjSwaps f 4 (Equiv.swap i j) := by rw [hψa]; exact hwD
    have hfix : ∀ b ∈ commSet E s, (ψ b).right i = i ∧ (ψ b).right j = j := by
      intro b hb
      obtain ⟨g, hg, rfl⟩ := hL.transitive a haΔ b hb
      have hgs : Commute g s := WreathEndgame.commute_of_mem_closure_commSet hg
      have hgr : Commute (ψ g).right (Equiv.swap i j) := by
        have h := (hgs.map ψ).map
          (SemidirectProduct.rightHom : L2Wreath f 4 →* Equiv.Perm (Fin 4))
        have h' : Commute (ψ g).right (ψ s).right := h
        rwa [hsr] at h'
      have hmem := WreathEndgame.conj_mem_disjSwaps hgr hwD'
      rw [← map_inv, ← map_mul, ← map_mul] at hmem
      constructor
      · rcases hmem.2 i with h | h
        · exact h
        · rw [Equiv.swap_apply_left] at h
          exact absurd h.symm hij
      · rcases hmem.2 j with h | h
        · exact h
        · rw [Equiv.swap_apply_right] at h
          exact absurd h hij
    obtain ⟨a', ha', -, -, hset⟩ := h31 a haΔ
    have haz : a * a' * z ∈ commSet E s := by
      have h : a * a' * z ∈ ({a, a', a * a' * z} : Set X) := Or.inr (Or.inr rfl)
      rw [← hset] at h
      exact h.1
    have hψz : ψ z = ψ s := by simp [ψ, hπz]
    have h := (hfix _ haz).2
    rw [map_mul, map_mul, hψz, SemidirectProduct.mul_right, SemidirectProduct.mul_right,
      Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hsr, Equiv.swap_apply_right, (hfix a' ha').1,
      (hfix a haΔ).1] at h
    exact hij h
  ·
    exact absurd hAS (not_almostSimpleCase_of_localBender h1 h91 hSQ ⟨s, hs, rfl⟩
      (localBender_map_of_ker_le_center π (QuotientGroup.ker_mk' _).le himage hL))

theorem exists_perfect_of_mulEquiv_l2Wreath_three (hS : Setup X E) {f : ℕ} (hf : 2 ≤ f)
    (φ : X ⧸ Subgroup.center X ≃* L2Wreath f 3) {s : X} (hs : s ∈ E) :
    ∃ P : Subgroup X, ⁅P, P⁆ = P ∧ Subgroup.center X ≤ P ∧
      ∀ g ∈ P, ∀ e ∈ E, Commute e s → Commute g e := by
  have hthird : ∀ i j : Fin 3, ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by decide
  have h3pts : ∀ a b c d : Fin 3, a ≠ b → c ≠ d → a = c ∨ a = d ∨ b = c ∨ b = d := by decide
  classical
  let q : X →* L2Wreath f 3 := φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hq : Function.Surjective q := φ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : q.ker = Subgroup.center X := by
    ext x
    simp [q]
  have hne : ∀ d ∈ E, q d ≠ 1 := by
    intro d hd hd1
    have himg : ∀ e ∈ E, q e = 1 := by
      intro e he
      obtain ⟨g, rfl⟩ := isConj_iff.mp (hS.isConj hd he)
      rw [map_mul, map_mul, hd1, mul_one, map_inv, mul_inv_cancel]
    have htop : (⊤ : Subgroup (L2Wreath f 3)) ≤ ⊥ := by
      rw [← MonoidHom.range_eq_top.mpr hq, MonoidHom.range_eq_map, ← hS.gen,
        MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨e, he, rfl⟩
      exact himg e he
    have h1 : (SemidirectProduct.inr (Equiv.swap (0 : Fin 3) 1) : L2Wreath f 3) = 1 :=
      Subgroup.mem_bot.mp (htop (Subgroup.mem_top _))
    have h2 := congrArg (fun w : L2Wreath f 3 => w.right (0 : Fin 3)) h1
    simp at h2
  have hswap : q '' E = WreathEndgame.swapSet f 3 :=
    eq_swapSet_of_setup hf (Or.inl rfl) (hS.map q hq hne)
  have hsw : ∀ e ∈ E, q e ∈ WreathEndgame.swapSet f 3 := fun e he => hswap ▸ ⟨e, he, rfl⟩
  obtain ⟨i, j, hij, hsr, -, -⟩ := hsw s hs
  obtain ⟨k, hki, hkj⟩ := hthird i j
  refine ⟨SetupQ.coordComm q k, SetupQ.commutator_coordComm q hq hf hker k,
    TenTwoQ.center_le_coordComm_of_three_le hf le_rfl ⟨hS.isClass, hS.oddT, hS.gen⟩ hq hker k,
    ?_⟩
  intro g hg e he hes
  obtain ⟨a, b, hab, her, hel, -⟩ := hsw e he
  have hsame : Equiv.swap a b = Equiv.swap i j := by
    rcases TenTwoQ.WreathCover.eq_or_disjoint_of_commute (q := q) hes hab hij her hsr with h | h
    · exact h
    · obtain ⟨h1, h2, h3, h4⟩ := (WreathEndgame.swapDisjoint_iff hab hij).mp h
      rcases h3pts a b i j hab hij with h' | h' | h' | h'
      exacts [(h1 h').elim, (h2 h').elim, (h3 h').elim, (h4 h').elim]
  have hfix : Equiv.swap a b k = k := by
    rw [hsame]
    exact Equiv.swap_apply_of_ne_of_ne hki hkj
  have hka : k ≠ a := by
    rintro rfl
    rw [Equiv.swap_apply_left] at hfix
    exact hab hfix.symm
  have hkb : k ≠ b := by
    rintro rfl
    rw [Equiv.swap_apply_right] at hfix
    exact hab hfix
  have hk1 : (q e).left k = 1 := hel k hka hkb
  have hk2 : (q e).right k = k := by rw [her]; exact hfix
  exact TenTwoQ.commute_of_mem_coordComm_of_ker_eq hker k
    (fun c => TenTwoQ.commute_coordHom hk1 hk2 c) g hg

end CFSG.OddTranspositions.PartThree.EightEight

end
