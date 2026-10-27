module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerClassicalModel

public section

namespace CFSG.StandardType

open Multiplicative
open CFSG.Assembly TableB

theorem addSubgroup_eq_bot_or_eq_top_of_monomial {p s : ℕ} [Fact p.Prime]
    {O : Subgroup (ZMod p)ˣ} (hO : O ≠ ⊥) (A : AddSubgroup (Fin s → ZMod p))
    (hA : ∀ (π : Equiv.Perm (Fin s)) (η : Fin s → (ZMod p)ˣ), (∀ i, η i ∈ O) →
      ∀ t ∈ A, (fun i => (η i : ZMod p) * t (π i)) ∈ A) :
    A = ⊥ ∨ A = ⊤ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  by_cases hbot : A = ⊥
  · exact Or.inl hbot
  right
  have hex : ∃ t ∈ A, t ≠ 0 := by
    by_contra h
    push Not at h
    exact hbot ((AddSubgroup.eq_bot_iff_forall A).mpr h)
  obtain ⟨t, htA, ht0⟩ := hex
  obtain ⟨i, hi⟩ : ∃ i, t i ≠ 0 := by
    by_contra h
    push Not at h
    exact ht0 (funext fun j => h j)
  obtain ⟨η₀, hη₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hO
  set η : Fin s → (ZMod p)ˣ := Function.update 1 i (η₀ : (ZMod p)ˣ) with hηdef
  have hηmem : ∀ j, η j ∈ O := by
    intro j
    by_cases hj : j = i
    · subst hj
      rw [hηdef, Function.update_self]
      exact η₀.2
    · rw [hηdef, Function.update_of_ne hj]
      exact O.one_mem
  have hηj : ∀ j, j ≠ i → (η j : ZMod p) = 1 := by
    intro j hj
    rw [hηdef, Function.update_of_ne hj]
    simp
  have hu : (fun j => (η j : ZMod p) * t j) ∈ A := by
    simpa using hA (Equiv.refl (Fin s)) η hηmem t htA
  have hsub : t - (fun j => (η j : ZMod p) * t j) ∈ A := A.sub_mem htA hu
  set c : ZMod p := (1 - ((η₀ : (ZMod p)ˣ) : ZMod p)) * t i with hcdef
  have hw : t - (fun j => (η j : ZMod p) * t j) =
      (Pi.single i c : Fin s → ZMod p) := by
    funext k
    by_cases hk : k = i
    · subst hk
      rw [Pi.sub_apply, Pi.single_eq_same, hcdef]
      simp only [hηdef, Function.update_self]
      ring
    · rw [Pi.sub_apply, Pi.single_eq_of_ne hk]
      simp only [hηdef, Function.update_of_ne hk, Pi.one_apply, Units.val_one]
      ring
  have hc : c ≠ 0 := by
    rw [hcdef]
    refine mul_ne_zero ?_ hi
    have hη0 : ((η₀ : (ZMod p)ˣ) : ZMod p) ≠ 1 := fun h =>
      hη₀ne (Subtype.ext (Units.ext h))
    exact sub_ne_zero.mpr (Ne.symm hη0)
  have hsingle_i : (Pi.single i (1 : ZMod p) : Fin s → ZMod p) ∈ A := by
    have hsub' : (Pi.single i c : Fin s → ZMod p) ∈ A := by rw [← hw]; exact hsub
    have hmem : ((c⁻¹).val) • (Pi.single i c : Fin s → ZMod p) ∈ A :=
      nsmul_mem hsub' (c⁻¹).val
    have heq : ((c⁻¹).val) • (Pi.single i c : Fin s → ZMod p) =
        (Pi.single i (1 : ZMod p) : Fin s → ZMod p) := by
      funext k
      by_cases hk : k = i
      · subst hk
        rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same]
        show ((c⁻¹).val : ℕ) • c = 1
        rw [nsmul_eq_mul, ZMod.natCast_zmod_val, inv_mul_cancel₀ hc]
      · rw [Pi.smul_apply, Pi.single_eq_of_ne hk, Pi.single_eq_of_ne hk]
        simp
    rwa [heq] at hmem
  have hsingle : ∀ j : Fin s, (Pi.single j (1 : ZMod p) : Fin s → ZMod p) ∈ A := by
    intro j
    have hmove := hA (Equiv.swap i j) (fun _ => (1 : (ZMod p)ˣ))
      (fun _ => O.one_mem) (Pi.single i (1 : ZMod p) : Fin s → ZMod p) hsingle_i
    have hfun :
        (fun k => ((1 : (ZMod p)ˣ) : ZMod p) *
            (Pi.single i (1 : ZMod p) : Fin s → ZMod p) (Equiv.swap i j k))
          = (Pi.single j (1 : ZMod p) : Fin s → ZMod p) := by
      funext k
      rw [Pi.single_apply, Pi.single_apply]
      by_cases hk : k = j
      · subst hk
        rw [Equiv.swap_apply_right, if_pos rfl, if_pos rfl]
        simp
      · have hki : Equiv.swap i j k ≠ i := by
          intro h
          rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left] at h
          exact hk h
        rw [if_neg hki, if_neg hk]
        simp
    rwa [hfun] at hmove
  have hsum : ∀ u : Fin s → ZMod p,
      u = ∑ j, (u j).val • (Pi.single j (1 : ZMod p) : Fin s → ZMod p) := by
    intro u
    conv_lhs => rw [pi_eq_sum_univ' u]
    refine Finset.sum_congr rfl fun j _ => ?_
    conv_lhs => rw [← ZMod.natCast_zmod_val (u j)]
    exact Nat.cast_smul_eq_nsmul (ZMod p) (u j).val (Pi.single j (1 : ZMod p) : Fin s → ZMod p)
  refine le_antisymm le_top ?_
  intro u _
  rw [hsum u]
  exact sum_mem fun j _ => nsmul_mem (hsingle j) (u j).val

theorem eq_bot_or_eq_top_of_monomial {p s : ℕ} [Fact p.Prime] {O : Subgroup (ZMod p)ˣ}
    (hO : O ≠ ⊥) (F : Subgroup (Multiplicative (Fin s → ZMod p)))
    (hF : ∀ (π : Equiv.Perm (Fin s)) (η : Fin s → (ZMod p)ˣ), (∀ i, η i ∈ O) →
      ∀ t : Fin s → ZMod p, ofAdd t ∈ F → ofAdd (fun i => (η i : ZMod p) * t (π i)) ∈ F) :
    F = ⊥ ∨ F = ⊤ := by
  let A : AddSubgroup (Fin s → ZMod p) := Subgroup.toAddSubgroup' F
  have hA : ∀ (π : Equiv.Perm (Fin s)) (η : Fin s → (ZMod p)ˣ), (∀ i, η i ∈ O) →
      ∀ t ∈ A, (fun i => (η i : ZMod p) * t (π i)) ∈ A := by
    intro π η hη t ht
    have ht' : ofAdd t ∈ F := ht
    have h1 := hF π η hη t ht'
    change (ofAdd fun i => (η i : ZMod p) * t (π i)) ∈ F
    exact h1
  rcases addSubgroup_eq_bot_or_eq_top_of_monomial hO A hA with h | h
  · left
    rw [← (Subgroup.toAddSubgroup' (A := Fin s → ZMod p)).map_bot] at h
    exact (Subgroup.toAddSubgroup' (A := Fin s → ZMod p)).injective h
  · right
    rw [← (Subgroup.toAddSubgroup' (A := Fin s → ZMod p)).map_top] at h
    exact (Subgroup.toAddSubgroup' (A := Fin s → ZMod p)).injective h

theorem ggWeylIrred_of_monomialModel {R : Type} [Group R] {p s : ℕ} [Fact p.Prime]
    (ι : Multiplicative (Fin s → ZMod p) →* R) (O : Subgroup (ZMod p)ˣ) (hO : O ≠ ⊥)
    (hmove : ∀ (π : Equiv.Perm (Fin s)) (η : Fin s → (ZMod p)ˣ), (∀ i, η i ∈ O) →
      ∃ w ∈ Subgroup.normalizer (ι.range : Set R), ∀ t : Fin s → ZMod p,
        w⁻¹ * ι (ofAdd t) * w = ι (ofAdd fun i => (η i : ZMod p) * t (π i))) :
    GGWeylIrred ι.range := by
  intro E' hE' hN
  let F : Subgroup (Multiplicative (Fin s → ZMod p)) := E'.comap ι
  have hF : ∀ (π : Equiv.Perm (Fin s)) (η : Fin s → (ZMod p)ˣ), (∀ i, η i ∈ O) →
      ∀ t : Fin s → ZMod p, ofAdd t ∈ F →
        ofAdd (fun i => (η i : ZMod p) * t (π i)) ∈ F := by
    intro π η hη t ht
    obtain ⟨w, hw, hwmove⟩ := hmove π η hη
    have h1 : w⁻¹ * ι (ofAdd t) * w ∈ E' := by
      have hN' := hN w⁻¹ (Subgroup.inv_mem _ hw) (ι (ofAdd t)) ht
      rwa [inv_inv] at hN'
    have h2 : ι (ofAdd fun i => (η i : ZMod p) * t (π i)) ∈ E' := by
      rwa [hwmove t] at h1
    change ι (ofAdd fun i => (η i : ZMod p) * t (π i)) ∈ E'
    exact h2
  rcases eq_bot_or_eq_top_of_monomial hO F hF with hbot | htop
  · left
    rw [eq_bot_iff]
    intro e he
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp (hE' he)
    have hyF : y ∈ F := by
      show ι y ∈ E'
      rw [hy]
      exact he
    rw [hbot, Subgroup.mem_bot] at hyF
    rw [Subgroup.mem_bot]
    rw [← hy, hyF, map_one]
  · right
    refine le_antisymm hE' ?_
    intro e he
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp he
    rw [← hy]
    exact (show y ∈ F from by rw [htop]; exact Subgroup.mem_top y)

theorem ggWeylIrred_map {R R' : Type} [Group R] [Group R'] (e : R ≃* R') {E : Subgroup R}
    (h : GGWeylIrred E) : GGWeylIrred (E.map e.toMonoidHom) := by
  intro E' hE' hN
  let F : Subgroup R := E'.comap e.toMonoidHom
  have hFE : F ≤ E := by
    intro x hx
    have hx' : e x ∈ E' := hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp (hE' hx')
    rw [← e.injective hyx]
    exact hy
  have hF : ∀ g ∈ Subgroup.normalizer (E : Set R), ∀ x ∈ F, g * x * g⁻¹ ∈ F := by
    intro g hg x hx
    have hg' : e g ∈ Subgroup.normalizer (E.map e.toMonoidHom : Set R') := by
      rw [← Subgroup.map_equiv_normalizer_eq E e]
      exact Subgroup.mem_map.mpr ⟨g, hg, rfl⟩
    have hx' : e x ∈ E' := hx
    have h1 := hN (e g) hg' (e x) hx'
    show e (g * x * g⁻¹) ∈ E'
    simpa using h1
  rcases h F hFE hF with hbot | htop
  · left
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp (hE' hy)
    have hxF : x ∈ F := by
      show e x ∈ E'
      rw [show e x = y from hxy]
      exact hy
    rw [hbot, Subgroup.mem_bot] at hxF
    rw [Subgroup.mem_bot]
    rw [← hxy, hxF, map_one]
  · right
    refine le_antisymm hE' ?_
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    have hxF : x ∈ F := by rw [htop]; exact hx
    have hx' : e x ∈ E' := hxF
    rw [show e x = y from hxy] at hx'
    exact hx'

theorem ggSCWeylIrred_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : GGSCWeylIrred p r R') : GGSCWeylIrred p r R := by
  intro E hE hr h3 hsc
  have hE' : IsElemAbelian p (E.map e.toMonoidHom) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a', ha', ha'e⟩ := Subgroup.mem_map.mp a.2
      obtain ⟨b', hb', hb'e⟩ := Subgroup.mem_map.mp b.2
      show (↑a : R') * ↑b = ↑b * ↑a
      rw [← ha'e, ← hb'e, ← map_mul, ← map_mul, TableB.IsElemAbelian.comm hE ha' hb']
    · obtain ⟨x', hx', hx'e⟩ := Subgroup.mem_map.mp hx
      rw [← hx'e, ← map_pow, hE.2 x' hx', map_one]
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (K := E) e.injective
  have hsc' : ∀ g : R', (∀ x ∈ E.map e.toMonoidHom, g * x = x * g) → g ^ p = 1 →
      g ∈ E.map e.toMonoidHom := by
    intro g hg hgp
    have hg₀ : e.symm g ∈ E := by
      refine hsc (e.symm g) (fun x hx => ?_) (by rw [← map_pow, hgp, map_one])
      apply e.injective
      rw [map_mul, map_mul, e.apply_symm_apply]
      exact hg (e x) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
    exact Subgroup.mem_map.mpr ⟨e.symm g, hg₀, by simp⟩
  have hirr : GGWeylIrred (E.map e.toMonoidHom) :=
    h (E.map e.toMonoidHom) hE' (by rw [hcard]; exact hr) (by rw [hcard]; exact h3) hsc'
  have hthis := ggWeylIrred_map e.symm hirr
  have hEE : (E.map e.toMonoidHom).map e.symm.toMonoidHom = E := by
    rw [Subgroup.map_map]
    have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id R := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  rwa [hEE] at hthis

theorem ggSCWeylIrred_of_centralQuotient {p r : ℕ} (hp : p.Prime) {G R : Type} [Group G]
    [Finite G] [Group R] (q : G →* R) (hq : Function.Surjective q)
    (hker : q.ker ≤ Subgroup.center G) (hcp : ¬ p ∣ Nat.card (Subgroup.center G))
    (h : GGSCWeylIrred p r G) : GGSCWeylIrred p r R := by
  intro E hE hr h3 hsc
  let Et : Subgroup G :=
    { carrier := {g | g ^ p = 1 ∧ q g ∈ E}
      one_mem' := ⟨one_pow p, by rw [map_one]; exact E.one_mem⟩
      mul_mem' := by
        intro x y hx hy
        have hxy : Commute x y :=
          commute_of_lift_pow_eq_one hp hker hcp
            (TableB.IsElemAbelian.comm hE hx.2 hy.2) hy.1
        exact ⟨by rw [hxy.mul_pow, hx.1, hy.1, one_mul],
          by rw [map_mul]; exact E.mul_mem hx.2 hy.2⟩
      inv_mem' := by
        intro x hx
        exact ⟨by rw [inv_pow, hx.1, inv_one], by rw [map_inv]; exact E.inv_mem hx.2⟩ }
  have hEt_ab : IsElemAbelian p Et := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hx.1⟩
    exact commute_of_lift_pow_eq_one hp hker hcp
      (TableB.IsElemAbelian.comm hE a.2.2 b.2.2) b.2.1
  have hcard : Nat.card Et = Nat.card E := by
    refine Nat.card_congr (Equiv.ofBijective (fun x : Et => (⟨q x, x.2.2⟩ : E)) ⟨?_, ?_⟩)
    · intro x y hxy
      exact Subtype.ext
        (eq_of_lift_pow_eq_one hp hker hcp (Subtype.ext_iff.mp hxy) x.2.1 y.2.1)
    · intro e
      obtain ⟨x, hxq, hxp⟩ := exists_lift_pow_eq_one hp hq hker hcp (hE.2 e e.2)
      exact ⟨⟨x, hxp, hxq ▸ e.2⟩, Subtype.ext hxq⟩
  have hscEt : ∀ g : G, (∀ e ∈ Et, g * e = e * g) → g ^ p = 1 → g ∈ Et := by
    intro g hg hgp
    refine ⟨hgp, ?_⟩
    refine hsc (q g) (fun e he => ?_) (by rw [← map_pow, hgp, map_one])
    obtain ⟨x, hxq, hxp⟩ := exists_lift_pow_eq_one hp hq hker hcp (hE.2 e he)
    have hxEt : x ∈ Et := ⟨hxp, hxq ▸ he⟩
    have h1 : q (g * x) = q (x * g) := congrArg q (hg x hxEt)
    rwa [map_mul, map_mul, hxq] at h1
  have hmap : Et.map q = E := by
    refine le_antisymm ?_ ?_
    · intro e he
      obtain ⟨x, hxEt, rfl⟩ := Subgroup.mem_map.mp he
      exact hxEt.2
    · intro e he
      obtain ⟨x, hxq, hxp⟩ := exists_lift_pow_eq_one hp hq hker hcp (hE.2 e he)
      exact Subgroup.mem_map.mpr ⟨x, ⟨hxp, hxq ▸ he⟩, hxq⟩
  have hirr : GGWeylIrred Et :=
    h Et hEt_ab (by rw [hcard]; exact hr) (by rw [hcard]; exact h3) hscEt
  intro E' hE'E hN
  let Et' : Subgroup G := Et ⊓ E'.comap q
  have hEt'norm : ∀ n ∈ Subgroup.normalizer (Et : Set G), ∀ x ∈ Et', n * x * n⁻¹ ∈ Et' := by
    intro n hn x hx
    have hnE : n * x * n⁻¹ ∈ Et := (Subgroup.mem_normalizer_iff.mp hn x).mp hx.1
    have hqn : q n ∈ Subgroup.normalizer (E : Set R) := by
      rw [Subgroup.mem_normalizer_iff]
      intro e
      constructor
      · intro he
        obtain ⟨y, hy, hyq⟩ := Subgroup.mem_map.mp (by rw [hmap]; exact he : e ∈ Et.map q)
        have h1 : n * y * n⁻¹ ∈ Et := (Subgroup.mem_normalizer_iff.mp hn y).mp hy
        have hqy : q (n * y * n⁻¹) = q n * e * (q n)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hyq]
        rw [← hqy]
        exact h1.2
      · intro he
        obtain ⟨y, hy, hyq⟩ :=
          Subgroup.mem_map.mp (by rw [hmap]; exact he : q n * e * (q n)⁻¹ ∈ Et.map q)
        have h1 : n⁻¹ * y * n ∈ Et := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) y).mp hy
          simpa using this
        have hqy : q (n⁻¹ * y * n) = e := by
          rw [map_mul, map_mul, map_inv, hyq]
          group
        rw [← hqy]
        exact h1.2
    refine ⟨hnE, ?_⟩
    show q (n * x * n⁻¹) ∈ E'
    have hconj : q (n * x * n⁻¹) = q n * q x * (q n)⁻¹ := by rw [map_mul, map_mul, map_inv]
    rw [hconj]
    exact hN (q n) hqn (q x) hx.2
  rcases hirr Et' inf_le_left hEt'norm with hbot | htop
  · left
    rw [eq_bot_iff]
    intro e he
    obtain ⟨x, hxEt, hxq⟩ := Subgroup.mem_map.mp (by rw [hmap]; exact hE'E he : e ∈ Et.map q)
    have hxEt' : x ∈ Et' := ⟨hxEt, by
      show q x ∈ E'
      rw [hxq]
      exact he⟩
    rw [hbot, Subgroup.mem_bot] at hxEt'
    rw [Subgroup.mem_bot]
    rw [← hxq, hxEt', map_one]
  · right
    refine le_antisymm hE'E ?_
    intro e he
    obtain ⟨x, hxEt, hxq⟩ := Subgroup.mem_map.mp (by rw [hmap]; exact he : e ∈ Et.map q)
    have hxEt' : x ∈ Et' := by rw [htop]; exact hxEt
    rw [← hxq]
    exact hxEt'.2

theorem ggCenterPrime_of_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : GGCenterPrime p R') : GGCenterPrime p R := by
  intro L' _ _ ψ hψ hker hperf
  refine h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) ?_ hperf
  intro x hx
  apply hker
  rw [MonoidHom.mem_ker] at hx
  rw [MonoidHom.mem_ker]
  exact e.injective (by rw [map_one]; exact hx)

end CFSG.StandardType

end
