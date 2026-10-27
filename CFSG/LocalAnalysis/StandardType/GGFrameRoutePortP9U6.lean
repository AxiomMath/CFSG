module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9UTorus
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineUAct
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryDvdAct

public section

namespace CFSG.StandardType.FrameRoute

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.StandardType.LineU

variable {L : Type} [Group L] {F : Type} [Field F] {m : ℕ}

private lemma mk_eq_of_actsDiagU (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m)
    {φ : ↥(unitarySU 2 1 F m) →* L}
    (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c))
    {a : MulAut L} {t u : Fin m → Fˣ}
    (ht : ActsDiagU φ a (fun i => (t i : F)))
    (hu : ActsDiagU φ a (fun i => (u i : F))) :
    (QuotientGroup.mk t : UTorus.Proj F m) = QuotientGroup.mk u := by
  have hm0 : 0 < m := by omega
  let i0 : Fin m := ⟨0, hm0⟩
  have hconst : ∀ i, (t⁻¹ * u) i = (t⁻¹ * u) i0 := by
    intro i
    have hratio := ActsDiagU.ratio_eq h hm hφker ht hu i i0
    have hU : t i * (t i0)⁻¹ = u i * (u i0)⁻¹ := by
      apply Units.ext
      simpa only [Units.val_mul, Units.val_inv_eq_inv_val] using hratio
    have h2 : (t i0)⁻¹ * u i0 = (t i)⁻¹ * u i := by
      calc (t i0)⁻¹ * u i0 = (t i)⁻¹ * (t i * (t i0)⁻¹) * u i0 := by group
        _ = (t i)⁻¹ * (u i * (u i0)⁻¹) * u i0 := by rw [hU]
        _ = (t i)⁻¹ * u i := by group
    simpa only [Pi.mul_apply, Pi.inv_apply] using h2.symm
  rw [QuotientGroup.eq, UTorus.mem_scalars]
  exact ⟨(t⁻¹ * u) i0, hconst⟩

theorem P9_U6a_exists_coord (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m)
    {φ : ↥(unitarySU 2 1 F m) →* L} (hφs : Function.Surjective φ)
    (hφker : ∀ g : ↥(unitarySU 2 1 F m), φ g = 1 →
      ∃ c : F, ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = diagonal (fun _ => c))
    {A : Subgroup (MulAut L)} (hdiag : ∀ a ∈ A, ∃ t : Fin m → F, ActsDiagU φ a t) :
    ∃ ι : ↥A →* UTorus.Proj F m, Function.Injective ι ∧
      ∀ (a : ↥A) (t : Fin m → Fˣ), ActsDiagU φ (a : MulAut L) (fun i => (t i : F)) →
        ι a = QuotientGroup.mk t := by
  classical
  have hm0 : 0 < m := by omega
  let t : ↥A → Fin m → F := fun a => (hdiag a a.2).choose
  have ht : ∀ a : ↥A, ActsDiagU φ (a : MulAut L) (t a) := fun a =>
    (hdiag a a.2).choose_spec
  let u : ↥A → Fin m → Fˣ := fun a i => Units.mk0 (t a i) ((ht a).ne_zero i)
  have hu : ∀ a : ↥A, ActsDiagU φ (a : MulAut L) (fun i => (u a i : F)) := by
    intro a
    simpa only [u, Units.val_mk0] using ht a
  have hmul : ∀ a b : ↥A, (QuotientGroup.mk (u (a * b)) : UTorus.Proj F m) =
      QuotientGroup.mk (u a) * QuotientGroup.mk (u b) := by
    intro a b
    have h1 : ActsDiagU φ ((a * b : ↥A) : MulAut L) (fun i => (u (a * b) i : F)) := hu (a * b)
    have h2 : ActsDiagU φ ((a * b : ↥A) : MulAut L) (fun i => ((u a * u b) i : F)) := by
      rw [Subgroup.coe_mul]
      have hh : ActsDiagU φ ((a : MulAut L) * (b : MulAut L)) (fun i => t a i * t b i) :=
        ActsDiagU.mul (ht a) (ht b)
      convert hh using 1
      funext i
      simp only [Pi.mul_apply, u, Units.val_mul, Units.val_mk0]
    rw [mk_eq_of_actsDiagU h hm hφker h1 h2, QuotientGroup.mk_mul]
  let ι : ↥A →* UTorus.Proj F m := MonoidHom.mk' (fun a => QuotientGroup.mk (u a)) hmul
  refine ⟨ι, ?_, ?_⟩
  · rw [injective_iff_map_eq_one]
    intro a ha
    have hmem : u a ∈ UTorus.scalars F m :=
      (QuotientGroup.eq_one_iff (u a)).mp (by simpa only [ι, MonoidHom.mk'_apply] using ha)
    rw [UTorus.mem_scalars] at hmem
    obtain ⟨c, hc⟩ := hmem
    have hconst : ∀ i j, t a i = t a j := by
      intro i j
      have hi : t a i = (c : F) := by
        simpa only [u, Units.val_mk0] using congrArg (fun y : Fˣ => (y : F)) (hc i)
      have hj : t a j = (c : F) := by
        simpa only [u, Units.val_mk0] using congrArg (fun y : Fˣ => (y : F)) (hc j)
      rw [hi, hj]
    have ha1 : (a : MulAut L) = 1 :=
      ActsDiagU.eq_one_of_const hφs (ht a) ⟨0, hm0⟩ hconst
    exact Subtype.ext ha1
  · intro a t' ht'
    exact mk_eq_of_actsDiagU h hm hφker (hu a) ht'

theorem P9_U6a_inner_le_range (h : UnitaryFieldData 2 1 F) {φ : ↥(unitarySU 2 1 F m) →* L}
    {A : Subgroup (MulAut L)} (hdiag : ∀ a ∈ A, ∃ t : Fin m → F, ActsDiagU φ a t)
    (hSC : GGTorusSelfCent 3 A) (ι : ↥A →* UTorus.Proj F m)
    (hι : ∀ (a : ↥A) (t : Fin m → Fˣ), ActsDiagU φ (a : MulAut L) (fun i => (t i : F)) →
      ι a = QuotientGroup.mk t) :
    UTorus.inner F m ≤ ι.range := by
  classical
  haveI : Finite F := h.finite
  have hF : Nat.card F = 4 := by rw [h.card]; norm_num
  have h3 : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have hcube : ∀ c : Fˣ, c ^ 3 = 1 := by
    intro c
    have hc := pow_card_eq_one' (x := c)
    rwa [h3] at hc
  intro x hx
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.mp hx
  have hd1 : ∏ i, d i = 1 := UTorus.mem_detOne.mp hd
  have hu : ∀ i, (d i : F) ^ (2 ^ 1 + 1) = 1 := by
    intro i
    have hc := congrArg (fun y : Fˣ => (y : F)) (hcube (d i))
    simpa using hc
  have hprod : ∏ i, (d i : F) = 1 := by
    rw [← Units.coe_prod, hd1]
    rfl
  obtain ⟨D, hD⟩ := exists_diagSU h hu hprod
  have hmem : MulAut.conj (φ D) ∈ A := conj_mem_of_selfCent_U hSC hdiag hD hu
  refine MonoidHom.mem_range.mpr ⟨⟨MulAut.conj (φ D), hmem⟩, ?_⟩
  have hconj : ActsDiagU φ (MulAut.conj (φ D)) (fun i => (d i : F)) := actsDiagU_conj hD
  simpa [QuotientGroup.mk'_apply] using hι ⟨MulAut.conj (φ D), hmem⟩ d hconj

theorem P9_U6a_dim_eq (h : UnitaryFieldData 2 1 F) (hm : 3 ≤ m) {A : Type} [Group A]
    (ι : A →* UTorus.Proj F m) (hιinj : Function.Injective ι)
    (hinner : UTorus.inner F m ≤ ι.range) {r : ℕ} (hr : Nat.card A = 3 ^ r) :
    m = r + 1 ∨ (3 ∣ m ∧ m = r + 2) := by
  classical
  haveI : Finite F := h.finite
  have hF : Nat.card F = 4 := by rw [h.card]; norm_num
  have hcard : Nat.card ι.range = 3 ^ r := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv, hr]
  rcases UTorus.eq_inner_or_eq_top hF (by omega) hinner with hinner_eq | htop
  · by_cases h3 : 3 ∣ m
    · right
      refine ⟨h3, ?_⟩
      have hcardi : Nat.card ι.range = 3 ^ (m - 2) := by
        rw [hinner_eq, UTorus.card_inner_of_dvd hF (by omega) h3]
      have hpow : 3 ^ r = 3 ^ (m - 2) := by rw [← hcard, hcardi]
      have heq : r = m - 2 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
      omega
    · left
      have hcardi : Nat.card ι.range = 3 ^ (m - 1) := by
        rw [hinner_eq, UTorus.card_inner_of_not_dvd hF (by omega) h3]
      have hpow : 3 ^ r = 3 ^ (m - 1) := by rw [← hcard, hcardi]
      have heq : r = m - 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
      omega
  · left
    have hcardtop : Nat.card ι.range = 3 ^ (m - 1) := by
      rw [htop, Subgroup.card_top, UTorus.card_proj hF (by omega)]
    have hpow : 3 ^ r = 3 ^ (m - 1) := by rw [← hcard, hcardtop]
    have heq : r = m - 1 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) hpow
    omega

end CFSG.StandardType.FrameRoute

end
