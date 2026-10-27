module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.AutItems
public import CFSG.SignalizerFunctorTheorem.McBride.Models.Unitary
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryAut.Fixing
public import CFSG.SignalizerFunctorTheorem.McBride.Models.UnitaryAut.Local
import CFSG.SignalizerFunctorTheorem.McBride.Models.Conj

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.McBride

open UnitaryFrame

namespace UnitaryAut

variable {p : ℕ}

theorem eq_one_of_fixes (hp : p.Prime) (h5 : 5 ≤ p) {C P : Subgroup (PSU3 2 p)} (hPC : P ≤ C)
    (hP : Nat.card P = 9)
    (htrans : ∀ x ∈ P, x ≠ 1 → ∀ y ∈ P, y ≠ 1 → ∃ c ∈ C, c * x * c⁻¹ = y)
    (g : MulAut (PSU3 2 p)) (hg : Nat.Coprime p (orderOf g)) (hfix : ∀ x ∈ C, g x = x) :
    g = 1 := by
  obtain ⟨y, hyP, rfl⟩ := exists_conj_of_fixing hp h5 P hP g hg fun x hx => hfix x (hPC hx)
  have hy1 : y = 1 := by
    by_contra hy
    have hyo : orderOf y ∣ 9 := by
      have := Subgroup.orderOf_dvd_natCard P hyP
      rwa [hP] at this
    have hy2 : y * y ≠ 1 := by
      intro h
      have h2 : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
      have : orderOf y ∣ 1 := by
        have := Nat.dvd_gcd h2 hyo
        simpa using this
      exact hy (orderOf_eq_one_iff.mp (Nat.dvd_one.mp this))
    have hall : ∃ y' ∈ P, y' ≠ 1 ∧ y' ≠ y := by
      by_contra hall
      push Not at hall
      have := hall (y * y) (Subgroup.mul_mem _ hyP hyP) hy2
      exact hy (mul_left_cancel (a := y) (by rw [this, mul_one]))
    obtain ⟨y', hy'P, hy'1, hy'y⟩ := hall
    obtain ⟨c, hcC, hc⟩ := htrans y hyP hy y' hy'P hy'1
    have h1 : MulAut.conj y c = c := hfix c hcC
    rw [MulAut.conj_apply] at h1
    have h2 : y * c = c * y := by
      have := congrArg (· * y) h1
      simpa [mul_assoc] using this
    exact hy'y (by rw [← hc, ← h2]; group)
  rw [hy1, map_one]

end UnitaryAut

variable {p : ℕ}

theorem fixedData_fixedFitting_psu3 (hp : p.Prime)
    (hcop : Nat.Coprime p (Nat.card (PSU3 2 p))) (f : MulAut (PSU3 2 p)) (hf : orderOf f = p) :
    FixedData (signalizerFixedSubgroup f) (fixedFitting f) := by
  obtain ⟨P, hF⟩ := exists_fixedData
    (order72_fixedSubgroup hp (five_le_of_coprime hp hcop) hcop f hf)
  have : fixedFitting f = P := hF.fitting
  rw [this]
  exact hF

theorem itemC_psu3 (hp : p.Prime) (hcop : Nat.Coprime p (Nat.card (PSU3 2 p)))
    (f : MulAut (PSU3 2 p)) (hf : orderOf f = p) : ItemC p f := by
  have hF := fixedData_fixedFitting_psu3 hp hcop f hf
  refine isPGroup_of_forall_coprime_orderOf_eq_one hp fun g hgcop => ?_
  have hgfix : ∀ y ∈ signalizerFixedSubgroup f, (g : MulAut (PSU3 2 p)) y = y := fun y hy =>
    (mem_fixingSubgroup_iff _).mp g.2 y hy
  have hgcop' : Nat.Coprime p (orderOf (g : MulAut (PSU3 2 p))) := by
    rwa [Subgroup.orderOf_coe]
  exact Subtype.ext (UnitaryAut.eq_one_of_fixes hp (five_le_of_coprime hp hcop) hF.le hF.card_P
    hF.trans g hgcop' hgfix)

theorem itemG_psu3 (hp : p.Prime) (hcop : Nat.Coprime p (Nat.card (PSU3 2 p)))
    (f : MulAut (PSU3 2 p)) (hf : orderOf f = p) : ItemG p f := by
  have hF := fixedData_fixedFitting_psu3 hp hcop f hf
  have hM := fixedNormalizer_psu3 hp hcop f hf
  have hC := itemC_psu3 hp hcop f hf
  intro g hg hgM hgF
  have hgC : ∀ c ∈ signalizerFixedSubgroup f, g c ∈ signalizerFixedSubgroup f := fun c hc => by
    rw [← hM] at hc ⊢
    exact hgM c hc
  have hgP : ∀ c ∈ signalizerFixedSubgroup f, c⁻¹ * g c ∈ fixedFitting f := fun c hc => by
    have := hgF c (hM ▸ hc)
    rw [hM] at this
    exact this
  obtain ⟨c, hcC, hgc⟩ := UnitaryAut.exists_conj_of_trivial_mod hF g hgC hgP
  refine ⟨c, hM ▸ hcC, ?_⟩
  set g' : MulAut (PSU3 2 p) := MulAut.conj c⁻¹ * g with hg'
  have hg'apply : ∀ y, g' y = c⁻¹ * g y * c := by
    intro y
    simp [hg']
  have hg'fix : ∀ x ∈ signalizerFixedSubgroup f, g' x = x := by
    intro x hx
    rw [hg'apply, hgc x hx]
    group
  have hg'mem : g' ∈ fixingSubgroup (MulAut (PSU3 2 p))
      (signalizerFixedSubgroup f : Set (PSU3 2 p)) :=
    (mem_fixingSubgroup_iff _).mpr fun y hy => hg'fix y hy
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_orderOf.mp hC) ⟨g', hg'mem⟩
  have hn' : orderOf g' = p ^ n := by rwa [Subgroup.orderOf_mk] at hn
  have hgdecomp : g = MulAut.conj c * g' := by
    rw [hg', ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  have hcomm : Commute (MulAut.conj c) g' := by
    show MulAut.conj c * g' = g' * MulAut.conj c
    refine MulEquiv.ext fun y => ?_
    have hcc : g' c = c := hg'fix c hcC
    have h1 : (MulAut.conj c * g') y = c * g' y * c⁻¹ := by
      rw [MulAut.mul_apply, MulAut.conj_apply]
    have h2 : (g' * MulAut.conj c) y = c * g' y * c⁻¹ := by
      rw [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, hcc]
    rw [h1, h2]
  have hdvd : orderOf (MulAut.conj c) ∣ Nat.card (PSU3 2 p) := by
    refine (orderOf_map_dvd (MulAut.conj : PSU3 2 p →* MulAut (PSU3 2 p)) c).trans ?_
    exact orderOf_dvd_natCard c
  have hcop1 : Nat.Coprime (orderOf (MulAut.conj c)) (orderOf g') := by
    rw [hn']
    exact (hcop.symm.coprime_dvd_left hdvd).pow_right n
  have hord : orderOf g = orderOf (MulAut.conj c) * orderOf g' := by
    rw [hgdecomp]
    exact hcomm.orderOf_mul_eq_mul_orderOf_of_coprime hcop1
  have hn0 : n = 0 := by
    by_contra hn0
    have hpd : p ∣ orderOf g := by
      rw [hord, hn']
      exact Dvd.dvd.mul_left (dvd_pow_self p hn0) _
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hg hpd)
  rw [hn0, pow_zero] at hn'
  rw [hgdecomp, orderOf_eq_one_iff.mp hn', mul_one]

end CFSG.SignalizerFunctorTheorem.McBride
