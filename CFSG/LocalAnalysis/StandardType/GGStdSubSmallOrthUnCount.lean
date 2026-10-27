module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallOrthInRest
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddLayer
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestThreeUnitary
public import CFSG.LieType.SeitzGeneration.OrthSdMixing

public section

namespace CFSG.StandardType

namespace SmallOrthUn

open Module Polynomial CFSG.Assembly CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.Classical2 OrthRestOdd CFSG.RankThree.PartOne.LIT

section Group

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

theorem isoGroup_of_le (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} (hAΩ : A ≤ orthDerived Q) (hA : IsElemAbelian p A) :
    IsoGroup (QuadraticMap.polarBilin Q) p A where
  sep := hQ.1
  alt := fun v => by
    rw [QuadraticMap.polarBilin_apply_apply]
    exact polar_self_eq_zero Q v
  comm := fun g hg h hh => TableB.IsElemAbelian.comm hA hg hh
  pow := fun g hg => hA.2 g hg
  pres := fun g hg u w => by
    rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
    exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
      (orthDerived_le_orthogonalGroup (hAΩ hg)) u w

end Group

section Count

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {p : ℕ} {B : V →ₗ[K] V →ₗ[K] K} {E : Subgroup (V ≃ₗ[K] V)}

theorem card_res_le [Finite E] (hp : p.Prime) (hpK : (p : K) ≠ 0) (hE : IsoGroup B p E)
    {U R : Submodule K V} (hc : IsCompl U R) (hU : ∀ g ∈ E, ∀ s ∈ U, g s ∈ U)
    (horth : ∀ u ∈ U, ∀ r ∈ R, B u r = 0) :
    Nat.card (resHom E U hU).range ≤ p ^ (finrank K U / 2) :=
  (hE.res U hU (sep_res_of_isCompl hE.sep hc horth)).card_le hp hpK

theorem card_res_le_of_inter_ne_bot [Finite E] (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) (hE : IsoGroup B p E) {U R : Submodule K V}
    (hc : IsCompl U R) (hU : ∀ g ∈ E, ∀ s ∈ U, g s ∈ U) (horth : ∀ u ∈ U, ∀ r ∈ R, B u r = 0)
    {Y : Submodule K V} (hY : Y ⊓ U ≠ ⊥) (hYinv : ∀ g ∈ E, ∀ y ∈ Y, g y ∈ Y)
    (hYiso : ∀ y ∈ Y, ∀ y' ∈ Y, B y y' = 0) :
    Nat.card (resHom E U hU).range ≤ p ^ (finrank K U / 2 - 1) := by
  have hEU := hE.res U hU (sep_res_of_isCompl hE.sep hc horth)
  set Y' : Submodule K U := Y.comap U.subtype with hY'
  have hY'0 : Y' ≠ ⊥ := by
    intro h
    obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY
    have hmem : (⟨y, hy.2⟩ : U) ∈ Y' := hy.1
    rw [h, Submodule.mem_bot] at hmem
    exact hy0 (congrArg Subtype.val hmem)
  exact card_le_of_isotropic hp hpK hK1 (finrank K U) U rfl _ _ hEU Y' hY'0
    (by
      rintro _ ⟨h, rfl⟩ z hz
      exact hYinv h h.2 z hz)
    (fun y hy y' hy' => hYiso y hy y' hy')

theorem card_res_comp_le [Finite E] (hp : p.Prime) (hpK : (p : K) ≠ 0)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) (hE : IsoGroup B p E) {U R : Submodule K V}
    (hc : IsCompl U R) (hU : ∀ g ∈ E, ∀ s ∈ U, g s ∈ U) (hR : ∀ g ∈ E, ∀ s ∈ R, g s ∈ R)
    (horth : ∀ u ∈ U, ∀ r ∈ R, B u r = 0) {Y : Submodule K V}
    (hYinv : ∀ g ∈ E, ∀ y ∈ Y, g y ∈ Y) (hYiso : ∀ y ∈ Y, ∀ y' ∈ Y, B y y' = 0)
    (hsplit : Y ⊓ U ≠ ⊥ ∨ Y ⊓ R ≠ ⊥) {n s : ℕ} (hn : finrank K V = 2 * n)
    (hcard : Nat.card E = p ^ (n - 1)) (hker : Nat.card (resHom E U hU).ker ≤ p ^ s) :
    Nat.card (resHom E R hR).range ≤ p ^ s := by
  have horth' : ∀ r ∈ R, ∀ u ∈ U, B r u = 0 := fun r hr u hu => by
    rw [alt_skew hE.alt r u, horth u hu r hr, neg_zero]
  have hEU := hE.res U hU (sep_res_of_isCompl hE.sep hc horth)
  have hER := hE.res R hR (sep_res_of_isCompl hE.sep hc.symm horth')
  obtain ⟨a, ha⟩ := hEU.even_finrank
  obtain ⟨b, hb⟩ := hER.even_finrank
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hab : a + b = n := by omega
  have h1 := Subgroup.card_ker_mul_card_range (resHom E U hU)
  have hp1 : 1 < p := hp.one_lt
  have hUb : Nat.card (resHom E U hU).range ≤ p ^ a := by
    have := card_res_le hp hpK hE hc hU horth
    rwa [show finrank K U / 2 = a by omega] at this
  have hRb : Nat.card (resHom E R hR).range ≤ p ^ b := by
    have := card_res_le hp hpK hE hc.symm hR horth'
    rwa [show finrank K R / 2 = b by omega] at this
  have hkey : p ^ (n - 1) ≤ p ^ s * Nat.card (resHom E U hU).range := by
    rw [← hcard, ← h1]
    exact Nat.mul_le_mul_right _ hker
  rcases hsplit with hY | hY
  · have ha1 : 1 ≤ a := by
      by_contra h0
      have hU0 : finrank K U = 0 := by omega
      apply hY
      rw [Submodule.finrank_eq_zero.mp hU0]
      exact inf_bot_eq _
    have hUb' := card_res_le_of_inter_ne_bot hp hpK hK1 hE hc hU horth hY hYinv hYiso
    rw [show finrank K U / 2 = a by omega] at hUb'
    have h2 : p ^ (n - 1) ≤ p ^ (s + (a - 1)) := by
      calc p ^ (n - 1) ≤ p ^ s * Nat.card (resHom E U hU).range := hkey
        _ ≤ p ^ s * p ^ (a - 1) := Nat.mul_le_mul_left _ hUb'
        _ = p ^ (s + (a - 1)) := (pow_add _ _ _).symm
    have h3 := (Nat.pow_le_pow_iff_right hp1).mp h2
    calc Nat.card (resHom E R hR).range ≤ p ^ b := hRb
      _ ≤ p ^ s := Nat.pow_le_pow_right hp.pos (by omega)
  · have hRb' := card_res_le_of_inter_ne_bot hp hpK hK1 hE hc.symm hR horth' hY hYinv hYiso
    rw [show finrank K R / 2 = b by omega] at hRb'
    have h2 : p ^ (n - 1) ≤ p ^ (s + a) := by
      calc p ^ (n - 1) ≤ p ^ s * Nat.card (resHom E U hU).range := hkey
        _ ≤ p ^ s * p ^ a := Nat.mul_le_mul_left _ hUb
        _ = p ^ (s + a) := (pow_add _ _ _).symm
    have h3 := (Nat.pow_le_pow_iff_right hp1).mp h2
    calc Nat.card (resHom E R hR).range ≤ p ^ (b - 1) := hRb'
      _ ≤ p ^ s := Nat.pow_le_pow_right hp.pos (by omega)

end Count

end SmallOrthUn

end CFSG.StandardType

end
