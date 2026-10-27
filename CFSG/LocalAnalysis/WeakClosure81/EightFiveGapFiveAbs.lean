module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFiveX
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFiveSwap

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv Equiv.Perm Subgroup CFSG.Open

theorem gap5_exists_quotAut {X Y : Type} [Group X] [Group Y] (ψ : X →* Y)
    (hψ : Function.Surjective ψ) {U : Type} [Group U] (ρ : U →* MulAut X)
    (hρ : ∀ (u : U) (x : X), ψ x = 1 → ψ (ρ u x) = 1) :
    ∃ α : U →* MulAut Y, ∀ (u : U) (x : X), α u (ψ x) = ψ (ρ u x) := by
  classical
  have hker_le : ∀ u : U, ψ.ker ≤ (ψ.comp (ρ u).toMonoidHom).ker := by
    intro u x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    simpa using hρ u x hx
  let H : U → Y →* Y := fun u =>
    (MonoidHom.liftOfSurjective ψ hψ) ⟨ψ.comp (ρ u).toMonoidHom, hker_le u⟩
  have hHψ : ∀ (u : U) (x : X), H u (ψ x) = ψ (ρ u x) := fun u x =>
    MonoidHom.liftOfRightInverse_comp_apply ψ _ _ ⟨ψ.comp (ρ u).toMonoidHom, hker_le u⟩ x
  have hone : H 1 = MonoidHom.id Y := by
    ext y
    obtain ⟨x, rfl⟩ := hψ y
    rw [hHψ 1 x, map_one, MulAut.one_apply, MonoidHom.id_apply]
  have hcomp : ∀ u v : U, H (u * v) = (H u).comp (H v) := by
    intro u v
    ext y
    obtain ⟨x, rfl⟩ := hψ y
    rw [MonoidHom.comp_apply, hHψ (u * v) x, hHψ v x, hHψ u (ρ v x), map_mul, MulAut.mul_apply]
  have hcomp_inv : ∀ u : U, (H u).comp (H u⁻¹) = MonoidHom.id Y := by
    intro u
    rw [← hcomp u u⁻¹, mul_inv_cancel, hone]
  have hinv_comp : ∀ u : U, (H u⁻¹).comp (H u) = MonoidHom.id Y := by
    intro u
    rw [← hcomp u⁻¹ u, inv_mul_cancel, hone]
  have hbij : ∀ u : U, Function.Bijective (H u) := by
    intro u
    refine ⟨?_, ?_⟩
    · intro a b hab
      have h1 : ((H u⁻¹).comp (H u)) a = ((H u⁻¹).comp (H u)) b :=
        congrArg (fun z => H u⁻¹ z) hab
      rw [hinv_comp u] at h1
      simpa using h1
    · intro y
      exact ⟨H u⁻¹ y, by rw [← MonoidHom.comp_apply, hcomp_inv u, MonoidHom.id_apply]⟩
  let α : U →* MulAut Y :=
  { toFun := fun u => MulEquiv.ofBijective (H u) (hbij u)
    map_one' := by
      apply MulEquiv.ext
      intro y
      rw [MulEquiv.ofBijective_apply, MulAut.one_apply]
      have h := congrFun (congrArg (fun f : Y →* Y => (f : Y → Y)) hone) y
      simpa using h
    map_mul' := by
      intro u v
      apply MulEquiv.ext
      intro y
      rw [MulEquiv.ofBijective_apply, MulAut.mul_apply, MulEquiv.ofBijective_apply,
        MulEquiv.ofBijective_apply]
      have h := congrFun (congrArg (fun f : Y →* Y => (f : Y → Y)) (hcomp u v)) y
      simpa [MonoidHom.comp_apply] using h }
  exact ⟨α, fun u x => by
    change (MulEquiv.ofBijective (H u) (hbij u)) (ψ x) = ψ (ρ u x)
    rw [MulEquiv.ofBijective_apply, hHψ u x]⟩

theorem gap5_fusionOddCore_char {X : Type} [Group X] [Finite X] :
    Odd (Nat.card (fusionOddCore X)) ∧
      ∀ a : MulAut X, ∀ q ∈ fusionOddCore X, a q ∈ fusionOddCore X := by
  refine ⟨CFSG.EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore X, ?_⟩
  intro a q hq
  haveI hmap : ((fusionOddCore X).map a.toMonoidHom).Normal :=
    (fusionOddCore_normal X).map a.toMonoidHom a.surjective
  have hcard : Nat.card ((fusionOddCore X).map a.toMonoidHom) = Nat.card (fusionOddCore X) :=
    Subgroup.card_map_of_injective (f := a.toMonoidHom) a.injective
  have hodd : Odd (Nat.card ((fusionOddCore X).map a.toMonoidHom)) := by
    rw [hcard]
    exact CFSG.EvenSporadicStandard.Fin76b.odd_natCard_fusionOddCore X
  exact CFSG.EvenSporadicStandard.Fin76b.le_fusionOddCore hodd
    (Subgroup.mem_map_of_mem a.toMonoidHom hq)

theorem gap5_closure_involutions {X : Type} [Group X] {S : Subgroup X} (hS : BarSituation X S) :
    Subgroup.closure {x : X | x * x = 1} = ⊤ := by
  rw [eq_top_iff, ← hS.normalClosure_eq_top]
  refine Subgroup.closure_mono ?_
  intro y hy
  obtain ⟨a, haS, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hy
  obtain ⟨c, rfl⟩ := isConj_iff.1 hconj
  have h1 : a * a = 1 := by simpa [pow_two] using hS.elemAbelian.2 a haS
  show c * a * c⁻¹ * (c * a * c⁻¹) = 1
  calc c * a * c⁻¹ * (c * a * c⁻¹) = c * (a * a) * c⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem gap5_mem_zpowers_of_mul_self {Y : Type} [Group Y] {d x : Y} (hd : d * d = 1)
    (hx : x ∈ Subgroup.zpowers d) : x = 1 ∨ x = d := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, zpow_two, hd, one_zpow]
  · right
    rw [zpow_add, zpow_mul, zpow_two, hd, one_zpow, one_mul, zpow_one]

theorem gap5_abstract {X : Type} [Group X] [Finite X] {S Z₁ : Subgroup X} {r : ℕ} {U : Type}
    [Group U] (hS : BarSituation X S) (h2 : Nat.card S = 2) (hc : CentralInSylow X S)
    (hn : ∃ n : ℕ, IsSymGp (X ⧸ fusionOddCore X) n) (ρ : U →* MulAut X)
    (hρinj : Function.Injective ρ) (hAct : ActionFacts X S ρ.range Z₁ r)
    (hU2 : ∀ u : U, u * u = 1) (hU : ∃ u v : U, u ≠ 1 ∧ v ≠ 1 ∧ u ≠ v)
    (hdich : ∀ (x s : X) (u : U), s ∈ S → u ≠ 1 → x * s * x⁻¹ ∉ Z₁ →
      ρ u (x * s * x⁻¹) * (x * s * x⁻¹)⁻¹ ∈ Z₁ →
      ∀ u' : U, ∃ s' ∈ S, ρ u' (x * s * x⁻¹) = x * s' * x⁻¹) :
    ∃ (Y : Type) (_ : Group Y) (ψ : X →* Y), Function.Surjective ψ ∧
      (∀ x, ψ x = 1 ↔ x ∈ Z₁) ∧ IsSymGp Y 6 := by
  obtain ⟨n, hn⟩ := hn
  have hZc : Z₁ ≤ Subgroup.center X := hAct.le_center
  haveI hZnormal : Z₁.Normal := Subgroup.normal_of_le_center hZc
  let ψ : X →* X ⧸ Z₁ := QuotientGroup.mk' Z₁
  have hψs : Function.Surjective ψ := QuotientGroup.mk'_surjective Z₁
  have hψk : ∀ x, ψ x = 1 ↔ x ∈ Z₁ := fun x => QuotientGroup.eq_one_iff x
  have hodd_center : Odd (Nat.card (Subgroup.center X)) :=
    odd_card_center_of_pCore_eq_bot hS.pCore_eq_bot
  have hZodd : Odd (Nat.card Z₁) := Odd.of_dvd_nat hodd_center (Subgroup.card_dvd_of_le hZc)
  have hker : ψ.ker = Z₁ := QuotientGroup.ker_mk' Z₁
  have hcen : ∀ a ∈ ρ.range, ∀ q ∈ Subgroup.center X, a q ∈ Subgroup.center X := by
    intro a _ q hq
    rw [Subgroup.mem_center_iff] at hq ⊢
    intro y
    have h1 := congrArg a (hq (a.symm y))
    simpa [map_mul] using h1
  have hZρ : ∀ (u : U), ∀ z ∈ Z₁, ρ u z ∈ Z₁ := by
    intro u z hz
    have h1 := hAct.oddComm (Subgroup.center X) hodd_center hcen (ρ u) ⟨u, rfl⟩ z (hZc hz)
    simpa using Z₁.mul_mem h1 hz
  have hSρ : ∀ (u : U), ∀ s ∈ S, ρ u s = s := fun u s hs => hAct.fixes (ρ u) ⟨u, rfl⟩ s hs
  obtain ⟨hOodd, hOchar⟩ := gap5_fusionOddCore_char (X := X)
  have hOρ : ∀ (u : U), ∀ o ∈ fusionOddCore X, ρ u o * o⁻¹ ∈ Z₁ := fun u o ho =>
    hAct.oddComm (fusionOddCore X) hOodd (fun a _ q hq => hOchar a q hq) (ρ u) ⟨u, rfl⟩ o ho
  obtain ⟨α, hα⟩ := gap5_exists_quotAut ψ hψs ρ
    (fun u x hx => (hψk _).2 (hZρ u x ((hψk x).1 hx)))
  have hkerc : ψ.ker ≤ Subgroup.center X := by rw [hker]; exact hZc
  have hkodd : Odd (Nat.card ψ.ker) := by rw [hker]; exact hZodd
  have hgen := gap5_closure_involutions hS
  have hαinj : Function.Injective α := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have hρu : ρ u = 1 := gap5Grp_eq_one_of_central_odd_kernel ψ hkerc hkodd hgen
      (fun x => by rw [← hα, hu]; rfl)
    exact hρinj (by rw [hρu, map_one])
  obtain ⟨u₀, v₀, hu₀, hv₀, huv⟩ := hU
  have hb1 : α u₀ ≠ 1 := fun h => hu₀ (hαinj (by rw [h, map_one]))
  have hb2 : α u₀ * α u₀ = 1 := by rw [← map_mul, hU2, map_one]
  have hbS : ∀ s ∈ S, α u₀ (ψ s) = ψ s := fun s hs => by rw [hα, hSρ u₀ s hs]
  have hbO : ∀ o ∈ fusionOddCore X, α u₀ (ψ o) = ψ o := fun o ho => by
    rw [hα]
    have h1 : ψ (ρ u₀ o * o⁻¹) = 1 := (hψk _).2 (hOρ u₀ o ho)
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  obtain ⟨h6, e, d, hSd, hd2, hd1, hswap⟩ :=
    gap5_X hS h2 hc hZc ψ hψs hψk hn hb1 hb2 hbS hbO
  rcases Nat.lt_or_ge n 7 with hn7 | hn7
  · have h6' : n = 6 := by omega
    subst h6'
    exact ⟨X ⧸ Z₁, inferInstance, ψ, hψs, hψk, ⟨e⟩⟩
  · exfalso
    have hdswap : (e d).IsSwap := hswap hn7
    refine gap5_false_of_swap_dichotomy hn7 e α hαinj hU2 ⟨u₀, v₀, hu₀, hv₀, huv⟩ ?_
    intro u hu τ hτ hfix u'
    obtain ⟨c, hcτ⟩ : ∃ c : Perm (Fin n), c * e d * c⁻¹ = e τ := by
      obtain ⟨a, b, hab, hd⟩ := hdswap
      obtain ⟨a', b', hab', ht⟩ := hτ
      rw [hd, ht]
      exact isConj_iff.1 (isConj_swap hab hab')
    obtain ⟨y, hy⟩ : ∃ y : X ⧸ Z₁, e y = c := ⟨e.symm c, e.apply_symm_apply c⟩
    have hτy : τ = y * d * y⁻¹ :=
      e.injective (by rw [map_mul, map_mul, map_inv, hy, ← hcτ])
    obtain ⟨x, hx⟩ := hψs y
    obtain ⟨s₀, hs₀, hs₀d⟩ : ∃ s₀ ∈ S, ψ s₀ = d := by
      have hd' : d ∈ S.map ψ := hSd ▸ Subgroup.mem_zpowers d
      obtain ⟨s, hs, hsd⟩ := Subgroup.mem_map.1 hd'
      exact ⟨s, hs, hsd⟩
    have hψw : ψ (x * s₀ * x⁻¹) = τ := by
      rw [map_mul, map_mul, map_inv, hx, hs₀d, hτy]
    have hτ1 : τ ≠ 1 := by
      intro h1
      obtain ⟨a, b, hab, ht⟩ := hτ
      have h3 : e τ = 1 := by rw [h1, map_one]
      rw [ht] at h3
      have h4 := congrArg (fun f : Perm (Fin n) => f a) h3
      simp at h4
      exact hab h4.symm
    have hxs : x * s₀ * x⁻¹ ∉ Z₁ := fun hz => hτ1 (by rw [← hψw, (hψk _).2 hz])
    have hfixZ : ρ u (x * s₀ * x⁻¹) * (x * s₀ * x⁻¹)⁻¹ ∈ Z₁ := by
      rw [← hψk, map_mul, map_inv, ← hα, hψw, hfix, mul_inv_cancel]
    obtain ⟨s', hs', hρ'⟩ := hdich x s₀ u hs₀ hu hxs hfixZ u'
    have h1 : α u' τ = ψ (x * s' * x⁻¹) := by rw [← hψw, hα, hρ']
    have h2' : ψ (x * s' * x⁻¹) = y * ψ s' * y⁻¹ := by rw [map_mul, map_mul, map_inv, hx]
    have h3 : ψ s' ∈ Subgroup.zpowers d := hSd ▸ Subgroup.mem_map_of_mem ψ hs'
    rcases gap5_mem_zpowers_of_mul_self hd2 h3 with h4 | h4
    · exfalso
      rw [h2', h4, mul_one, mul_inv_cancel] at h1
      exact hτ1 ((MulEquiv.map_eq_one_iff (α u')).1 h1)
    · rw [h1, h2', h4, hτy]

end CFSG.LocalAnalysis.WeakClosure81

end
