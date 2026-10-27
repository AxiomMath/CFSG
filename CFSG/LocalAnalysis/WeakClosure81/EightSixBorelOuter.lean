module

public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelOmega
public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelTI
public import CFSG.LocalAnalysis.WeakClosure81.EightSixBorelBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

variable {G : Type} [Group G] [Finite G] {V H T : Subgroup G} {S : Type} [Group S]
  {ψ : ↥(kGenIn V H) →* S} {ρ : ↥H →* MulAut S} {t₀ : S}

namespace Borel86Data

private theorem borel86_outer_sq_eq_comm {M : Type*} [Group M] {x x' : M} (hx : x * x = 1)
    (hx' : x' * x' = 1) :
    (x⁻¹ * x') * (x⁻¹ * x') = (x⁻¹ * x') * x * (x⁻¹ * x')⁻¹ * x⁻¹ := by
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  have hx'i : x'⁻¹ = x' := inv_eq_of_mul_eq_one_right hx'
  have hc : (x⁻¹ * x')⁻¹ = x' * x := by rw [mul_inv_rev, hxi, hx'i, hxi]
  have key : x * (x⁻¹ * x')⁻¹ * x⁻¹ = x⁻¹ * x' := by
    rw [hc]
    calc x * (x' * x) * x⁻¹ = x * x' * (x * x⁻¹) := by group
      _ = x * x' := by rw [mul_inv_cancel, mul_one]
      _ = x⁻¹ * x' := by rw [hxi]
  calc (x⁻¹ * x') * (x⁻¹ * x') = (x⁻¹ * x') * (x * (x⁻¹ * x')⁻¹ * x⁻¹) := by rw [key]
    _ = (x⁻¹ * x') * x * (x⁻¹ * x')⁻¹ * x⁻¹ := by group

private theorem borel86_outer_exists_two_ne_one {M : Type*} [Group M] [Finite M]
    (h : 2 < Nat.card M) :
    ∃ x y : M, x ≠ 1 ∧ y ≠ 1 ∧ x ≠ y := by
  haveI : Fintype M := Fintype.ofFinite M
  rw [Nat.card_eq_fintype_card] at h
  obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.mp h
  by_cases hx : x = 1
  · exact ⟨y, z, fun hy => hxy (hx.trans hy.symm), fun hz => hxz (hx.trans hz.symm), hyz⟩
  · by_cases hy : y = 1
    · exact ⟨x, z, hx, fun hz => hyz (hy.trans hz.symm), hxz⟩
    · exact ⟨x, y, hx, hy, hxy⟩

private theorem borel86_outer_sq_eq_one {W : Subgroup G} (hW : IsElemAbelian 2 W) {g : G} {x : G}
    (hx : x ∈ conjSubgroup W g) : x * x = 1 := by
  have h : x ^ 2 = 1 := (isElemAbelian_conjSubgroup' hW g).2 x hx
  simpa [pow_two] using h

theorem rho_apply_eq_iff (hD : Borel86Data V H T S ψ ρ t₀) {a : G} (ha : a ∈ H)
    (x : ↥(kGenIn V H)) (hx : (x : G) ∈ conjSubgroup V a) (hxE : (x : G) ∉ eCentSet V H T)
    (y : ↥H) :
    ρ y (ψ x) = ψ x ↔ (y : G) ∈ Subgroup.normalizer (conjSubgroup V a : Set G) := by
  have hHn : H ≤ Subgroup.normalizer (kGenIn V H : Set G) :=
    hD.hyp.le_normalizer_kGenIn_of_eq_sup hD.eq_sup
  have hconst : ∀ z : ↥(kGenIn V H), (z : G) ∈ conjSubgroup V a → (z : G) ∉ eCentSet V H T →
      ψ z = ρ ⟨a⁻¹, H.inv_mem ha⟩ t₀ := by
    intro z hz hzE
    have hza : a * (z : G) * a⁻¹ ∈ V := mem_conjSubgroup_iff.mp hz
    have hzaK : a * (z : G) * a⁻¹ ∈ kGenIn V H := le_kGenIn_self V H hza
    have hzaE : a * (z : G) * a⁻¹ ∉ eCentSet V H T := by
      intro hc
      exact hzE (by
        have h1 := hD.hyp.conj_mem_centralizer_eSub (g := a⁻¹) (H.inv_mem ha) hc
        simpa [eCentSet, mul_assoc] using h1)
    have h1 := hD.act ⟨a⁻¹, H.inv_mem ha⟩ ⟨_, hzaK⟩ z (by
      show (z : G) = a⁻¹ * (a * (z : G) * a⁻¹) * (a⁻¹)⁻¹
      group)
    rw [hD.root ⟨_, hzaK⟩ hza hzaE] at h1
    exact h1.symm
  constructor
  · intro hyfix
    have hx'K : (y : G) * (x : G) * (y : G)⁻¹ ∈ kGenIn V H :=
      (Subgroup.mem_normalizer_iff.mp (hHn y.2) (x : G)).mp x.2
    have hψx' : ψ ⟨_, hx'K⟩ = ψ x := by
      have h1 := hD.act y x ⟨_, hx'K⟩ rfl
      rw [hyfix] at h1
      exact h1.symm
    have hψc : ψ (x⁻¹ * ⟨(y : G) * (x : G) * (y : G)⁻¹, hx'K⟩) = 1 := by
      calc ψ (x⁻¹ * ⟨(y : G) * (x : G) * (y : G)⁻¹, hx'K⟩)
          = ψ x⁻¹ * ψ ⟨(y : G) * (x : G) * (y : G)⁻¹, hx'K⟩ := map_mul ψ _ _
        _ = (ψ x)⁻¹ * ψ ⟨(y : G) * (x : G) * (y : G)⁻¹, hx'K⟩ := by rw [map_inv]
        _ = (ψ x)⁻¹ * ψ x := by rw [hψx']
        _ = 1 := inv_mul_cancel _
    have hc : ((x⁻¹ * ⟨(y : G) * (x : G) * (y : G)⁻¹, hx'K⟩ : ↥(kGenIn V H)) : G) ∈
        centerPre (kGenIn V H) (eCentSet V H T) :=
      (hD.ker (x⁻¹ * ⟨(y : G) * (x : G) * (y : G)⁻¹, hx'K⟩)).mp hψc
    have hc' : (x : G)⁻¹ * ((y : G) * (x : G) * (y : G)⁻¹) ∈
        centerPre (kGenIn V H) (eCentSet V H T) := hc
    have hxx : (x : G) * (x : G) = 1 := borel86_outer_sq_eq_one hD.hyp.elemAbelian hx
    have hx'conj : (y : G) * (x : G) * (y : G)⁻¹ ∈ conjSubgroup V (a * (y : G)⁻¹) := by
      rw [mem_conjSubgroup_iff]
      show (a * (y : G)⁻¹) * ((y : G) * (x : G) * (y : G)⁻¹) * (a * (y : G)⁻¹)⁻¹ ∈ V
      have hxa : a * (x : G) * a⁻¹ ∈ V := mem_conjSubgroup_iff.mp hx
      have heq : (a * (y : G)⁻¹) * ((y : G) * (x : G) * (y : G)⁻¹) * (a * (y : G)⁻¹)⁻¹ =
          a * (x : G) * a⁻¹ := by group
      rw [heq]
      exact hxa
    have hx'sq : ((y : G) * (x : G) * (y : G)⁻¹) * ((y : G) * (x : G) * (y : G)⁻¹) = 1 :=
      borel86_outer_sq_eq_one hD.hyp.elemAbelian hx'conj
    have hcsq : ((x : G)⁻¹ * ((y : G) * (x : G) * (y : G)⁻¹)) *
        ((x : G)⁻¹ * ((y : G) * (x : G) * (y : G)⁻¹)) ∈ eCentSet V H T := by
      have hcomm := hc'.2 (x : G) x.2
      rw [borel86_outer_sq_eq_comm hxx hx'sq]
      exact hcomm
    have hx'cent : (x : G)⁻¹ * ((y : G) * (x : G) * (y : G)⁻¹) ∈ eCentSet V H T :=
      mem_eCentSet_of_mem_centerPre hD.hyp hD.eq_sup hc' hcsq
    have hXeq : conjSubgroup V a = conjSubgroup V (a * (y : G)⁻¹) :=
      conjSubgroup_eq_of_inv_mul_mem_eCentSet hD.hyp hD.eq_sup ha (mul_mem ha (inv_mem y.2))
        hx hxE hx'conj hx'cent
    have hN : (y : G)⁻¹ ∈ Subgroup.normalizer (conjSubgroup V a : Set G) := by
      have h1 : conjSubgroup (conjSubgroup V a) (y : G)⁻¹ = conjSubgroup V a := by
        rw [conjSubgroup_conjSubgroup, ← hXeq]
      exact conjSubgroup_eq_iff_mem_normalizer.mp h1
    simpa using (Subgroup.normalizer (conjSubgroup V a : Set G)).inv_mem hN
  · intro hyN
    have hx' : (y : G) * (x : G) * (y : G)⁻¹ ∈ conjSubgroup V a :=
      (Subgroup.mem_set_normalizer_iff.mp hyN (x : G)).mp hx
    have hx'K : (y : G) * (x : G) * (y : G)⁻¹ ∈ kGenIn V H :=
      (Subgroup.mem_normalizer_iff.mp (hHn y.2) (x : G)).mp x.2
    have hx'E : (y : G) * (x : G) * (y : G)⁻¹ ∉ eCentSet V H T := by
      intro hc
      exact hxE (by
        have h1 := hD.hyp.conj_mem_centralizer_eSub (g := (y : G)⁻¹) (H.inv_mem y.2) hc
        simpa [eCentSet, mul_assoc] using h1)
    have h1 := hD.act y x ⟨_, hx'K⟩ rfl
    have h2 : ψ ⟨_, hx'K⟩ = ρ ⟨a⁻¹, H.inv_mem ha⟩ t₀ := hconst ⟨_, hx'K⟩ hx' hx'E
    rw [h2] at h1
    rw [h1]
    exact (hconst x hx hxE).symm

theorem rho_fix_iff (hD : Borel86Data V H T S ψ ρ t₀) {g : G} (hUH : conjSubgroup V g ≤ H)
    (hUK : ¬ conjSubgroup V g ≤ kGenIn V H) {u u' : ↥H} (hu : (u : G) ∈ conjSubgroup V g)
    (hu1 : (u : G) ≠ 1) (hu' : (u' : G) ∈ conjSubgroup V g) (hu1' : (u' : G) ≠ 1) (s : S) :
    ρ u (s * t₀ * s⁻¹) = s * t₀ * s⁻¹ ↔ ρ u' (s * t₀ * s⁻¹) = s * t₀ * s⁻¹ := by
  obtain ⟨k, rfl⟩ := hD.surj s
  obtain ⟨v, hvV, hvE⟩ := hD.exists_mem_not_mem
  have hvK : v ∈ kGenIn V H := le_kGenIn_self V H hvV
  have hkH : (k : G) ∈ H := hD.kGenIn_le k.2
  have hxK : (k : G) * v * (k : G)⁻¹ ∈ kGenIn V H :=
    mul_mem (mul_mem k.2 hvK) (inv_mem k.2)
  have hxconj : (k : G) * v * (k : G)⁻¹ ∈ conjSubgroup V (k : G)⁻¹ := by
    rw [mem_conjSubgroup_iff]
    show (k : G)⁻¹ * ((k : G) * v * (k : G)⁻¹) * ((k : G)⁻¹)⁻¹ ∈ V
    have heq : (k : G)⁻¹ * ((k : G) * v * (k : G)⁻¹) * ((k : G)⁻¹)⁻¹ = v := by group
    rw [heq]
    exact hvV
  have hxE : (k : G) * v * (k : G)⁻¹ ∉ eCentSet V H T := by
    intro hc
    exact hvE (by
      have h1 := hD.hyp.conj_mem_centralizer_eSub (g := (k : G)⁻¹) (H.inv_mem hkH) hc
      simpa [eCentSet, mul_assoc] using h1)
  have hψx : ψ ⟨_, hxK⟩ = ψ k * t₀ * (ψ k)⁻¹ := by
    have h1 := hD.act ⟨k, hkH⟩ ⟨v, hvK⟩ ⟨_, hxK⟩ rfl
    have h2 : ρ ⟨k, hkH⟩ = MulAut.conj (ψ k) := hD.rho_eq_conj ⟨k, hkH⟩ k rfl
    have h3 : ψ ⟨v, hvK⟩ = t₀ := hD.root ⟨v, hvK⟩ hvV hvE
    rw [h2, h3, MulAut.conj_apply] at h1
    exact h1.symm
  rw [← hψx]
  have hiffu := rho_apply_eq_iff hD (a := (k : G)⁻¹) (H.inv_mem hkH) ⟨_, hxK⟩ hxconj hxE u
  have hiffu' := rho_apply_eq_iff hD (a := (k : G)⁻¹) (H.inv_mem hkH) ⟨_, hxK⟩ hxconj hxE u'
  rw [hiffu, hiffu']
  rcases inf_normalizer_eq_bot_or_commute_or_le_kGenIn hD.hyp hD.eq_sup hUH (H.inv_mem hkH) with
    hbot | hcomm | hle
  · have hnu : (u : G) ∉ Subgroup.normalizer (conjSubgroup V (k : G)⁻¹ : Set G) := by
      intro hn
      have hmem : (u : G) ∈ conjSubgroup V g ⊓
          Subgroup.normalizer (conjSubgroup V (k : G)⁻¹ : Set G) := Subgroup.mem_inf.mpr ⟨hu, hn⟩
      rw [hbot] at hmem
      exact hu1 (Subgroup.mem_bot.mp hmem)
    have hnu' : (u' : G) ∉ Subgroup.normalizer (conjSubgroup V (k : G)⁻¹ : Set G) := by
      intro hn
      have hmem : (u' : G) ∈ conjSubgroup V g ⊓
          Subgroup.normalizer (conjSubgroup V (k : G)⁻¹ : Set G) := Subgroup.mem_inf.mpr ⟨hu', hn⟩
      rw [hbot] at hmem
      exact hu1' (Subgroup.mem_bot.mp hmem)
    exact ⟨fun h => absurd h hnu, fun h => absurd h hnu'⟩
  · have hnorm : ∀ w : G, w ∈ conjSubgroup V g →
        w ∈ Subgroup.normalizer (conjSubgroup V (k : G)⁻¹ : Set G) := by
      intro w hw
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (hcomm w hw z hz).symm
    exact ⟨fun _ => hnorm u' hu', fun _ => hnorm u hu⟩
  · exact absurd hle hUK

theorem rho_mem_range_conj (hD : Borel86Data V H T S ψ ρ t₀) {g : G}
    (hUT : conjSubgroup V g ≤ T) (u : ↥H) (hu : (u : G) ∈ conjSubgroup V g) :
    ρ u ∈ (MulAut.conj : S →* MulAut S).range := by
  have hUH : conjSubgroup V g ≤ H := hUT.trans hD.hyp.T_le_H
  by_cases hUK : conjSubgroup V g ≤ kGenIn V H
  · have huK : (u : G) ∈ kGenIn V H := hUK hu
    have hρu : ρ u = MulAut.conj (ψ ⟨(u : G), huK⟩) := hD.rho_eq_conj u ⟨(u : G), huK⟩ rfl
    exact ⟨_, hρu.symm⟩
  · have hcard : 2 < Nat.card ↥(conjSubgroup V g) := by
      change 2 < Nat.card (Subgroup.map (MulAut.conj g⁻¹).toMonoidHom V)
      rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective]
      exact hD.hyp.two_lt_card
    obtain ⟨w₁, w₂, hw₁1, hw₂1, hw₁₂⟩ := borel86_outer_exists_two_ne_one hcard
    let i : ↥(conjSubgroup V g) → ↥H := fun w => ⟨(w : G), hUH w.2⟩
    have hi : ∀ w : ↥(conjSubgroup V g), (i w : G) = (w : G) := fun _ => rfl
    haveI : IsMulCommutative ↥(conjSubgroup V g) :=
      (isElemAbelian_conjSubgroup' hD.hyp.elemAbelian g).1
    have hfix : ∀ w : ↥(conjSubgroup V g), ρ (i w) t₀ = t₀ := fun w =>
      hD.rho_apply_eq_of_mem_normalizer (i w) (hD.hyp.T_le_normalizer (hUT w.2))
    have hsq : ∀ w : ↥(conjSubgroup V g), ρ (i w) * ρ (i w) = 1 := by
      intro w
      have hw2 : (w : G) * (w : G) = 1 := borel86_outer_sq_eq_one hD.hyp.elemAbelian w.2
      have h1 : i w * i w = 1 := Subtype.ext (by simpa [hi] using hw2)
      rw [← map_mul, h1, map_one]
    have hcomm : ∀ w w' : ↥(conjSubgroup V g), ρ (i w) * ρ (i w') = ρ (i w') * ρ (i w) := by
      intro w w'
      have hww : w * w' = w' * w := mul_comm' w w'
      have h2 : i w * i w' = i w' * i w := Subtype.ext (by
        have h3 := congrArg (fun z : ↥(conjSubgroup V g) => (z : G)) hww
        simpa [hi] using h3)
      rw [← map_mul, ← map_mul, h2]
    have hex : ∃ w : ↥(conjSubgroup V g), w ≠ 1 ∧
        ρ (i w) ∈ (MulAut.conj : S →* MulAut S).range := by
      by_cases h1 : ρ (i w₁) ∈ (MulAut.conj : S →* MulAut S).range
      · exact ⟨w₁, hw₁1, h1⟩
      · by_cases h2 : ρ (i w₂) ∈ (MulAut.conj : S →* MulAut S).range
        · exact ⟨w₂, hw₂1, h2⟩
        · refine ⟨w₁ * w₂, ?_, ?_⟩
          · intro hww
            apply hw₁₂
            have hw₂sq : w₂ * w₂ = 1 :=
              Subtype.ext (by simpa using borel86_outer_sq_eq_one hD.hyp.elemAbelian w₂.2)
            calc w₁ = w₁ * (w₂ * w₂) := by rw [hw₂sq, mul_one]
              _ = (w₁ * w₂) * w₂ := by group
              _ = w₂ := by rw [hww, one_mul]
          · have hout := hD.lie.out (ρ (i w₁)) (ρ (i w₂)) (hfix w₁) (hfix w₂)
              (hsq w₁) (hsq w₂) (hcomm w₁ w₂) h1 h2
            rwa [← map_mul] at hout
    obtain ⟨w, hw1, hwR⟩ := hex
    obtain ⟨g₀, hg₀⟩ := MonoidHom.mem_range.mp hwR
    have hg₀sq : g₀ * g₀ = 1 := by
      have h1 : MulAut.conj (g₀ * g₀) = 1 := by
        rw [map_mul, hg₀, hsq w]
      have h2 : g₀ * g₀ ∈ Subgroup.center S := by
        rw [Subgroup.mem_center_iff]
        intro z
        have hz := congrArg (fun f : MulAut S => f z) h1
        have hz' : (g₀ * g₀) * z * (g₀ * g₀)⁻¹ = z := by
          rw [MulAut.conj_apply, MulAut.one_apply] at hz
          exact hz
        calc z * (g₀ * g₀) = ((g₀ * g₀) * z * (g₀ * g₀)⁻¹) * (g₀ * g₀) := by rw [hz']
          _ = (g₀ * g₀) * z := by group
      rw [hD.lie.center] at h2
      simpa using h2
    by_cases hueq : (u : G) = 1
    · have hu1 : u = 1 := Subtype.ext (by simpa using hueq)
      rw [hu1, map_one]
      exact (MulAut.conj : S →* MulAut S).range.one_mem
    · have hwU : (i w : G) ∈ conjSubgroup V g := by simpa [hi] using w.2
      have hw1' : (i w : G) ≠ 1 := fun h => hw1 (Subtype.ext (by simpa [hi] using h))
      have hfixu : ρ u t₀ = t₀ :=
        hD.rho_apply_eq_of_mem_normalizer u (hD.hyp.T_le_normalizer (hUT hu))
      have hsqu : ρ u * ρ u = 1 := by
        have h2 : (u : G) * (u : G) = 1 := borel86_outer_sq_eq_one hD.hyp.elemAbelian hu
        have h1 : u * u = 1 := Subtype.ext (by simpa using h2)
        rw [← map_mul, h1, map_one]
      refine hD.lie.fix (ρ u) g₀ hsqu hg₀sq hfixu ?_
      intro s
      have hwfix : ρ (i w) (s * t₀ * s⁻¹) = s * t₀ * s⁻¹ ↔
          g₀ * (s * t₀ * s⁻¹) = s * t₀ * s⁻¹ * g₀ := by
        rw [← hg₀]
        simp only [MulAut.conj_apply]
        constructor
        · intro h
          calc g₀ * (s * t₀ * s⁻¹) = (g₀ * (s * t₀ * s⁻¹) * g₀⁻¹) * g₀ := by group
            _ = (s * t₀ * s⁻¹) * g₀ := by rw [h]
        · intro h
          calc g₀ * (s * t₀ * s⁻¹) * g₀⁻¹ = ((s * t₀ * s⁻¹) * g₀) * g₀⁻¹ := by rw [h]
            _ = s * t₀ * s⁻¹ := by group
      exact (rho_fix_iff hD hUH hUK hu hueq hwU hw1' s).trans hwfix

end Borel86Data

end CFSG.LocalAnalysis.WeakClosure81

end
