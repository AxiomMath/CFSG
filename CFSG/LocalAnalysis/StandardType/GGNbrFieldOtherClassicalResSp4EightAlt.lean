module

public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalCoreLine
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.StandardType

namespace ResSp4Eight

open Equiv Equiv.Perm CFSG.ComponentClassification.PresentationLocal
open scoped Pointwise

@[expose] def tOneSp4Eight : Perm (Fin 6) := swap 0 1 * swap 1 2

@[expose] def tTwoSp4Eight : Perm (Fin 6) := swap 3 4 * swap 4 5

@[expose] def sigmaSp4Eight : Perm (Fin 6) := swap 0 3 * swap 1 4 * swap 4 2 * swap 2 5

@[expose] def eZeroSetSp4Eight : Finset (Perm (Fin 6)) :=
  {1, tOneSp4Eight, tOneSp4Eight * tOneSp4Eight, tTwoSp4Eight, tTwoSp4Eight * tTwoSp4Eight,
    tOneSp4Eight * tTwoSp4Eight, tOneSp4Eight * (tTwoSp4Eight * tTwoSp4Eight),
    tOneSp4Eight * tOneSp4Eight * tTwoSp4Eight,
    tOneSp4Eight * tOneSp4Eight * (tTwoSp4Eight * tTwoSp4Eight)}

theorem one_mem_eZeroSet_Sp4Eight : (1 : Perm (Fin 6)) ∈ eZeroSetSp4Eight := by decide

theorem mul_mem_eZeroSet_Sp4Eight :
    ∀ x ∈ eZeroSetSp4Eight, ∀ y ∈ eZeroSetSp4Eight, x * y ∈ eZeroSetSp4Eight := by
  decide +kernel

theorem inv_mem_eZeroSet_Sp4Eight : ∀ x ∈ eZeroSetSp4Eight, x⁻¹ ∈ eZeroSetSp4Eight := by
  decide +kernel

@[expose] def eZeroSp4Eight : Subgroup (Perm (Fin 6)) where
  carrier := (eZeroSetSp4Eight : Set (Perm (Fin 6)))
  mul_mem' {x y} hx hy := mul_mem_eZeroSet_Sp4Eight x hx y hy
  one_mem' := one_mem_eZeroSet_Sp4Eight
  inv_mem' {x} hx := inv_mem_eZeroSet_Sp4Eight x hx

theorem card_eZero_Sp4Eight : Nat.card eZeroSp4Eight = 9 := by
  have h : (eZeroSp4Eight : Set (Perm (Fin 6))) = ↑eZeroSetSp4Eight := rfl
  rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide

theorem cube_eZeroSet_Sp4Eight : ∀ x ∈ eZeroSetSp4Eight, x * x * x = 1 := by decide +kernel

theorem pow_three_of_mem_eZero_Sp4Eight {x : Perm (Fin 6)} (hx : x ∈ eZeroSp4Eight) :
    x ^ 3 = 1 := by
  rw [pow_three']
  exact cube_eZeroSet_Sp4Eight x hx

theorem sigma_mem_alternatingGroup_Sp4Eight : sigmaSp4Eight ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  decide

theorem sigma_conj_mem_eZeroSet_Sp4Eight :
    ∀ x ∈ eZeroSetSp4Eight, sigmaSp4Eight * x * sigmaSp4Eight⁻¹ ∈ eZeroSetSp4Eight := by
  decide +kernel

theorem sigma_conj_mem_eZero_Sp4Eight {x : Perm (Fin 6)} (hx : x ∈ eZeroSp4Eight) :
    sigmaSp4Eight * x * sigmaSp4Eight⁻¹ ∈ eZeroSp4Eight :=
  sigma_conj_mem_eZeroSet_Sp4Eight x hx

theorem sigma_moves_eZeroSet_Sp4Eight :
    ∀ x ∈ eZeroSetSp4Eight, x ≠ 1 → sigmaSp4Eight * x * sigmaSp4Eight⁻¹ ≠ 1 ∧
      sigmaSp4Eight * x * sigmaSp4Eight⁻¹ ≠ x ∧ sigmaSp4Eight * x * sigmaSp4Eight⁻¹ ≠ x * x := by
  decide +kernel

theorem sigma_conj_not_mem_zpowers_Sp4Eight {x : Perm (Fin 6)} (hx : x ∈ eZeroSp4Eight)
    (hx1 : x ≠ 1) : sigmaSp4Eight * x * sigmaSp4Eight⁻¹ ∉ Subgroup.zpowers x := by
  intro hmem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have h3 : x ^ (3 : ℕ) = 1 := pow_three_of_mem_eZero_Sp4Eight hx
  rw [zpow_eq_zpow_emod' m h3] at hm
  obtain ⟨h1, h2, h3'⟩ := sigma_moves_eZeroSet_Sp4Eight x hx hx1
  have hr : 0 ≤ m % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have hr3 : m % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le hr
  rw [hk, zpow_natCast] at hm
  have hk3 : k < 3 := by omega
  interval_cases k
  · exact h1 (by rw [← hm, pow_zero])
  · exact h2 (by rw [← hm, pow_one])
  · exact h3' (by rw [← hm, pow_two])

theorem card_le_nine_of_isPGroup_Sp4Eight {P : Subgroup (Perm (Fin 6))} (hP : IsPGroup 3 P) :
    Nat.card P ≤ 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hP
  have h720 : Nat.card (Perm (Fin 6)) = 720 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin]
    rfl
  have hdvd : 3 ^ k ∣ 720 := by
    rw [← hk, ← h720]
    exact Subgroup.card_subgroup_dvd_card P
  have hk2 : k ≤ 2 := by
    by_contra hk2
    have h27 : 3 ^ 3 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
    have := h27.trans hdvd
    norm_num at this
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

theorem exists_conj_eZero_Sp4Eight {E : Subgroup (Perm (Fin 6))} (hE : ∀ x ∈ E, x ^ 3 = 1)
    (h9 : 9 ≤ Nat.card E) :
    ∃ g : Perm (Fin 6), ∀ x : Perm (Fin 6), x ∈ E ↔ g⁻¹ * x * g ∈ eZeroSp4Eight := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hEp : IsPGroup 3 E := fun x => ⟨1, by rw [pow_one]; exact Subtype.ext (hE x x.2)⟩
  have h0p : IsPGroup 3 eZeroSp4Eight := fun x =>
    ⟨1, by rw [pow_one]; exact Subtype.ext (pow_three_of_mem_eZero_Sp4Eight x.2)⟩
  obtain ⟨P, hEP⟩ := hEp.exists_le_sylow
  obtain ⟨P₀, h0P⟩ := h0p.exists_le_sylow
  have hEeq : E = P :=
    Subgroup.eq_of_le_of_card_ge hEP ((card_le_nine_of_isPGroup_Sp4Eight P.isPGroup').trans h9)
  have h0eq : eZeroSp4Eight = P₀ :=
    Subgroup.eq_of_le_of_card_ge h0P ((card_le_nine_of_isPGroup_Sp4Eight P₀.isPGroup').trans
      card_eZero_Sp4Eight.ge)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 6)) P₀ P
  have h1 : (P : Subgroup (Perm (Fin 6))) = MulAut.conj g • (P₀ : Subgroup (Perm (Fin 6))) := by
    rw [← hg, Sylow.coe_subgroup_smul]
  refine ⟨g, fun x => ?_⟩
  rw [hEeq, h1, Subgroup.mem_smul_pointwise_iff_exists, ← h0eq]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [MulAut.smul_def, MulAut.conj_apply]
    simpa [mul_assoc] using hy
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    rw [MulAut.smul_def, MulAut.conj_apply]
    group

theorem eq_of_forall_conj_Sp4Eight {σ τ : Perm (Fin 6)}
    (h : ∀ a ∈ alternatingGroup (Fin 6), σ * a * σ⁻¹ = τ * a * τ⁻¹) : σ = τ := by
  have hc : τ⁻¹ * σ ∈ Subgroup.centralizer (alternatingGroup (Fin 6) : Set (Perm (Fin 6))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have e := h a ha
    calc a * (τ⁻¹ * σ) = τ⁻¹ * (τ * a * τ⁻¹) * σ := by group
      _ = τ⁻¹ * (σ * a * σ⁻¹) * σ := by rw [e]
      _ = τ⁻¹ * σ * a := by group
  rw [centralizer_alternatingGroup_eq_bot (by simp), Subgroup.mem_bot] at hc
  calc σ = τ * (τ⁻¹ * σ) := by group
    _ = τ := by rw [hc, mul_one]

theorem conjNormal_injective_Sp4Eight :
    Function.Injective
      (MulAut.conjNormal : Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6))) := by
  intro σ τ hστ
  refine eq_of_forall_conj_Sp4Eight fun a ha => ?_
  have h := congrArg (fun φ : MulAut (alternatingGroup (Fin 6)) =>
    ((φ ⟨a, ha⟩ : alternatingGroup (Fin 6)) : Perm (Fin 6))) hστ
  simpa only [MulAut.conjNormal_apply] using h

theorem mem_alternatingGroup_of_pow_three_Sp4Eight {x : Perm (Fin 6)} (hx : x ^ 3 = 1) :
    x ∈ alternatingGroup (Fin 6) := by
  rw [Equiv.Perm.mem_alternatingGroup]
  have h : sign x ^ 3 = 1 := by rw [← map_pow, hx, map_one]
  rcases Int.units_eq_one_or (sign x) with h1 | h1
  · exact h1
  · rw [h1] at h
    exact absurd h (by decide)

section Ext

variable {L' : Type} [Group L'] {ψ : L' →* alternatingGroup (Fin 6)}

theorem map_eq_of_conj_eq_Sp4Eight (hψ : Function.Surjective ψ) {x y : L'}
    (h : MulAut.conj x = MulAut.conj y) : ψ x = ψ y := by
  apply Subtype.ext
  refine eq_of_forall_conj_Sp4Eight fun a ha => ?_
  obtain ⟨l, hl⟩ := hψ ⟨a, ha⟩
  have e := congrArg (fun φ : MulAut L' => ((ψ (φ l) : alternatingGroup (Fin 6)) :
    Perm (Fin 6))) h
  simp only [MulAut.conj_apply, map_mul, map_inv, hl, Subgroup.coe_mul,
    Subgroup.coe_inv] at e
  exact e

theorem center_eq_ker_Sp4Eight (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') : Subgroup.center L' = ψ.ker := by
  refine le_antisymm (fun z hz => ?_) hker
  rw [MonoidHom.mem_ker]
  have h1 : MulAut.conj z = MulAut.conj (1 : L') := by
    ext l
    rw [MulAut.conj_apply, map_one, MulAut.one_apply, (Subgroup.mem_center_iff.mp hz l).symm,
      mul_inv_cancel_right]
  rw [map_eq_of_conj_eq_Sp4Eight hψ h1, map_one]

end Ext

theorem ggTorusNoLineTwoKX_alt_Sp4Eight :
    GGTorusNoLineTwoKX 3 (fun k => ¬ 3 ∣ k) (alternatingGroup (Fin 6))
      (Set.range (MulAut.conjNormal : Perm (Fin 6) →* MulAut (alternatingGroup (Fin 6)))) ∅ := by
  classical
  intro L' _ _ ψ hψ hker hperf hKp A hA hAI h9 _
  have hp3 : Nat.Prime 3 := Nat.prime_three
  have hcp : ¬ 3 ∣ Nat.card (Subgroup.center L') := by
    rw [center_eq_ker_Sp4Eight hψ hker]
    exact hKp
  obtain ⟨Ind, hInd⟩ := ggInducedHom_exists ψ hψ A (fun a ha => by
    obtain ⟨φ, -, h⟩ := hAI a ha
    exact ⟨φ, h⟩)
  have hIndinj : Function.Injective Ind := by
    rw [injective_iff_map_eq_one]
    intro a ha
    refine Subtype.ext (ggAut_eq_one_of_induced_one ψ hker hperf a fun l => ?_)
    rw [← hInd a l, ha, MulAut.one_apply]
  have hIndI : ∀ a : A, ∃ σ : Perm (Fin 6), Ind a = MulAut.conjNormal σ := by
    intro a
    obtain ⟨φ, ⟨σ, rfl⟩, hφ⟩ := hAI a a.2
    exact ⟨σ, ggInduced_unique hψ (hInd a) hφ⟩
  set E : Subgroup (Perm (Fin 6)) := Ind.range.comap MulAut.conjNormal
  have hmemE : ∀ σ : Perm (Fin 6), σ ∈ E ↔ MulAut.conjNormal σ ∈ Ind.range := fun σ => Iff.rfl
  have hE3 : ∀ σ ∈ E, σ ^ 3 = 1 := by
    intro σ hσ
    obtain ⟨a, ha⟩ := (hmemE σ).mp hσ
    have ha3 : a ^ 3 = 1 := Subtype.ext (hA.2 _ a.2)
    apply conjNormal_injective_Sp4Eight
    rw [map_pow, ← ha, ← map_pow, ha3, map_one, map_one]
  have hEcomm : ∀ σ ∈ E, ∀ τ ∈ E, σ * τ = τ * σ := by
    intro σ hσ τ hτ
    obtain ⟨a, ha⟩ := (hmemE σ).mp hσ
    obtain ⟨b, hb⟩ := (hmemE τ).mp hτ
    have hab : a * b = b * a := Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2)
    apply conjNormal_injective_Sp4Eight
    rw [map_mul, map_mul, ← ha, ← hb, ← map_mul, ← map_mul, hab]
  have hcardE : Nat.card E = Nat.card A := by
    have hbij : Function.Bijective
        (fun σ : E => (⟨MulAut.conjNormal (σ : Perm (Fin 6)), σ.2⟩ : Ind.range)) := by
      refine ⟨fun σ τ h => Subtype.ext (conjNormal_injective_Sp4Eight
        (congrArg Subtype.val h)), fun φ => ?_⟩
      obtain ⟨a, ha⟩ := φ.2
      obtain ⟨σ, hσ⟩ := hIndI a
      refine ⟨⟨σ, (hmemE σ).mpr ⟨a, hσ⟩⟩, Subtype.ext ?_⟩
      change MulAut.conjNormal σ = (φ : MulAut (alternatingGroup (Fin 6)))
      rw [← hσ, ha]
    rw [Nat.card_congr (Equiv.ofBijective _ hbij)]
    exact Nat.card_congr (MonoidHom.ofInjective hIndinj).toEquiv.symm
  have hEA : ∀ σ ∈ E, σ ∈ alternatingGroup (Fin 6) := fun σ hσ =>
    mem_alternatingGroup_of_pow_three_Sp4Eight (hE3 σ hσ)
  obtain ⟨g, hg⟩ := exists_conj_eZero_Sp4Eight hE3 (by rw [hcardE]; exact h9)
  set w : Perm (Fin 6) := g * sigmaSp4Eight * g⁻¹ with hwdef
  have hwA : w ∈ alternatingGroup (Fin 6) :=
    (alternatingGroup.normal (α := Fin 6)).conj_mem _ sigma_mem_alternatingGroup_Sp4Eight g
  have hwE : ∀ x ∈ E, w * x * w⁻¹ ∈ E := by
    intro x hx
    rw [hg] at hx ⊢
    have e : g⁻¹ * (w * x * w⁻¹) * g = sigmaSp4Eight * (g⁻¹ * x * g) * sigmaSp4Eight⁻¹ := by
      rw [hwdef]
      group
    rw [e]
    exact sigma_conj_mem_eZero_Sp4Eight hx
  obtain ⟨n, hn⟩ := hψ ⟨w, hwA⟩
  have hlift : ∀ σ ∈ E, ∃ x : L', (ψ x : Perm (Fin 6)) = σ ∧ x ^ 3 = 1 := by
    intro σ hσ
    have h3 : (⟨σ, hEA σ hσ⟩ : alternatingGroup (Fin 6)) ^ 3 = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact hE3 σ hσ)
    obtain ⟨x, hx, hx3⟩ := exists_lift_pow_eq_one hp3 hψ hker hcp h3
    exact ⟨x, by rw [hx], hx3⟩
  have hrep : ∀ a ∈ A, ∃ x : L', x ^ 3 = 1 ∧ (ψ x : Perm (Fin 6)) ∈ E ∧ a = MulAut.conj x := by
    intro a ha
    obtain ⟨σ, hσ⟩ := hIndI ⟨a, ha⟩
    have hσE : σ ∈ E := (hmemE σ).mpr ⟨⟨a, ha⟩, hσ⟩
    obtain ⟨x, hx, hx3⟩ := hlift σ hσE
    refine ⟨x, hx3, hx ▸ hσE, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [← hInd ⟨a, ha⟩ l, hσ]
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, MulAut.conj_apply, map_mul, map_mul, map_inv, Subgroup.coe_mul,
      Subgroup.coe_mul, Subgroup.coe_inv, hx]
  have hcomm : ∀ x y : L', x ^ 3 = 1 → y ^ 3 = 1 → (ψ x : Perm (Fin 6)) ∈ E →
      (ψ y : Perm (Fin 6)) ∈ E → x * y = y * x := by
    intro x y _ hy3 hxE hyE
    refine commute_of_lift_pow_eq_one hp3 hker hcp ?_ hy3
    exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact hEcomm _ hxE _ hyE)
  have hconjE : ∀ x : L', (ψ x : Perm (Fin 6)) ∈ E →
      (ψ (n * x * n⁻¹) : Perm (Fin 6)) ∈ E := by
    intro x hxE
    have e : (ψ (n * x * n⁻¹) : Perm (Fin 6)) = w * (ψ x : Perm (Fin 6)) * w⁻¹ := by
      rw [map_mul, map_mul, map_inv, hn, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e]
    exact hwE _ hxE
  refine ⟨{n}, ?_, ?_⟩
  ·
    intro n' hn' a ha
    rw [Set.mem_singleton_iff.mp hn']
    obtain ⟨x, hx3, hxE, rfl⟩ := hrep a ha
    have hy3 : (n * x * n⁻¹) ^ 3 = 1 := by rw [conj_pow, hx3, mul_one, mul_inv_cancel]
    have hyE := hconjE x hxE
    have hxy : x * (n * x * n⁻¹) = (n * x * n⁻¹) * x := hcomm _ _ hx3 hy3 hxE hyE
    have hform : n * (MulAut.conj x n)⁻¹ = (n * x * n⁻¹) * x⁻¹ := by
      rw [MulAut.conj_apply]
      group
    rw [hform]
    refine ⟨?_, fun a' ha' => ?_⟩
    · have hc : Commute (n * x * n⁻¹) x⁻¹ :=
        (show Commute x (n * x * n⁻¹) from hxy).symm.inv_right
      rw [hc.mul_pow, hy3, inv_pow, hx3, inv_one, mul_one]
    · obtain ⟨z, hz3, hzE, rfl⟩ := hrep a' ha'
      have hcy : Commute z (n * x * n⁻¹) := hcomm _ _ hz3 hy3 hzE hyE
      have hcx : Commute z x⁻¹ := (show Commute z x from hcomm _ _ hz3 hx3 hzE hxE).inv_right
      rw [MulAut.conj_apply, (hcy.mul_right hcx).eq, mul_inv_cancel_right]
  ·
    intro _ a₀ ha₀ ha₀1
    refine Or.inr ⟨n, rfl, fun hmem => ?_⟩
    obtain ⟨x₀, hx₀3, hx₀E, rfl⟩ := hrep a₀ ha₀
    have he₀ : (ψ x₀ : Perm (Fin 6)) ≠ 1 := by
      intro h
      apply ha₀1
      have hk : x₀ ∈ ψ.ker := by
        rw [MonoidHom.mem_ker]
        exact Subtype.ext h
      ext l
      rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.mp (hker hk) l).symm,
        mul_inv_cancel_right]
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hm' : MulAut.conj (x₀ ^ m) = MulAut.conj (n * x₀ * n⁻¹) := by
      rw [map_zpow, hm, map_mul, map_mul, map_inv]
    have hpm := congrArg (fun y : alternatingGroup (Fin 6) => (y : Perm (Fin 6)))
      (map_eq_of_conj_eq_Sp4Eight hψ hm')
    simp only [map_zpow, map_mul, map_inv, hn, Subgroup.coe_zpow, Subgroup.coe_mul,
      Subgroup.coe_inv] at hpm
    set e₀ : Perm (Fin 6) := (ψ x₀ : Perm (Fin 6))
    have hE₀ : g⁻¹ * e₀ * g ∈ eZeroSp4Eight := (hg e₀).mp hx₀E
    have hne : g⁻¹ * e₀ * g ≠ 1 := by
      intro h1
      apply he₀
      calc e₀ = g * (g⁻¹ * e₀ * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    apply sigma_conj_not_mem_zpowers_Sp4Eight hE₀ hne
    refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
    have e1 : (g⁻¹ * e₀ * g) ^ m = g⁻¹ * e₀ ^ m * g := by
      have := (map_zpow (MulAut.conj g⁻¹) e₀ m).symm
      simpa only [MulAut.conj_apply, inv_inv] using this
    rw [e1, hpm, hwdef]
    group

end ResSp4Eight

end CFSG.StandardType

end
