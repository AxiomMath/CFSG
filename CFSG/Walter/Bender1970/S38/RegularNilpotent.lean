module

public import Mathlib.GroupTheory.Nilpotent
public import CFSG.Walter.Bender1970.S38.NumberTheory

public section

namespace CFSG.Walter

variable {Q : Type*} [Group Q] [Finite Q]

theorem card_ne_one_add_one (Q : Type*) [Group Q] [Finite Q] :
    Nat.card {v : Q // v ≠ 1} + 1 = Nat.card Q := by
  classical
  rw [← Nat.card_congr (Equiv.optionSubtypeNe (1 : Q)), Finite.card_option]

omit [Finite Q] in
theorem card_eq_of_orbit {S : Subgroup (MulAut Q)} {v₀ : Q}
    (hfree : ∀ r ∈ S, r v₀ = v₀ → r = 1) (X : Set Q)
    (hX : ∀ v, v ∈ X ↔ ∃ r ∈ S, r v₀ = v) : Nat.card S = Nat.card X := by
  refine Nat.card_congr (Equiv.ofBijective (fun r : S => (⟨(r : MulAut Q) v₀,
    (hX _).mpr ⟨r, r.2, rfl⟩⟩ : X)) ⟨fun r₁ r₂ h => ?_, fun v => ?_⟩)
  · have h1 : ((r₁ : MulAut Q) v₀) = (r₂ : MulAut Q) v₀ := congrArg Subtype.val h
    have h2 : ((r₁ : MulAut Q)⁻¹ * r₂) v₀ = v₀ := by
      rw [MulAut.mul_apply, ← h1, MulAut.inv_apply_self]
    have h3 := hfree _ (S.mul_mem (S.inv_mem r₁.2) r₂.2) h2
    apply Subtype.ext
    rw [inv_mul_eq_one] at h3
    exact h3
  · obtain ⟨r, hr, hrv⟩ := (hX v).mp v.2
    exact ⟨⟨r, hr⟩, Subtype.ext hrv⟩

theorem eq_of_isNilpotent_of_regular (hQ : IsPGroup 2 Q) {F R : Subgroup (MulAut Q)}
    (hRF : R ≤ F) (hF : Group.IsNilpotent F)
    (hFR : F ≤ Subgroup.normalizer (R : Set (MulAut Q))) (hR : IsCyclic R)
    (hfree : ∀ r ∈ R, ∀ v : Q, r v = v → v ≠ 1 → r = 1)
    (htrans : ∀ u v : Q, u ≠ 1 → v ≠ 1 → ∃ r ∈ R, r u = v) : F = R := by
  classical
  refine le_antisymm (fun x hx => ?_) hRF
  by_cases htriv : ∀ v : Q, v = 1
  · have hx1 : x = 1 := by
      ext v
      rw [htriv (x v), htriv v]
      rfl
    rw [hx1]
    exact R.one_mem
  push Not at htriv
  obtain ⟨v₀, hv₀⟩ := htriv
  have hxv : x v₀ ≠ 1 := fun h => hv₀ ((MulEquiv.map_eq_one_iff _).mp h)
  obtain ⟨r, hrR, hrv⟩ := htrans v₀ (x v₀) hv₀ hxv
  suffices hφ : ∀ φ ∈ F, φ v₀ = v₀ → φ = 1 by
    have h1 := hφ (r⁻¹ * x) (F.mul_mem (F.inv_mem (hRF hrR)) hx)
      (by rw [MulAut.mul_apply, ← hrv, MulAut.inv_apply_self])
    rw [inv_mul_eq_one] at h1
    rw [← h1]
    exact hrR
  intro φ hφF hφv
  by_contra hφ1
  have hord0 : orderOf φ ≠ 0 := (isOfFinOrder_of_finite φ).orderOf_pos.ne'
  have hord1 : orderOf φ ≠ 1 := fun h => hφ1 (orderOf_eq_one_iff.mp h)
  set ℓ := (orderOf φ).minFac with hℓ
  have hℓp : ℓ.Prime := Nat.minFac_prime hord1
  set ψ := φ ^ (orderOf φ / ℓ) with hψ
  have hψord : orderOf ψ = ℓ := orderOf_pow_orderOf_div hord0 (Nat.minFac_dvd _)
  have hψF : ψ ∈ F := F.pow_mem hφF _
  have hψv : ψ v₀ = v₀ := by
    rw [hψ]
    generalize orderOf φ / ℓ = k
    induction k with
    | zero => rfl
    | succ k ih => rw [pow_succ, MulAut.mul_apply, hφv, ih]
  have hψ1 : ψ ≠ 1 := fun h => by
    rw [h, orderOf_one] at hψord
    exact hℓp.one_lt.ne' hψord.symm
  set C : Subgroup Q := MonoidHom.eqLocus ψ.toMonoidHom (MonoidHom.id Q) with hC
  have hmemC : ∀ v, v ∈ C ↔ ψ v = v := fun v => Iff.rfl
  have hcardR : Nat.card R + 1 = Nat.card Q := by
    rw [← card_ne_one_add_one Q]
    congr 1
    rw [card_eq_of_orbit (S := R) (v₀ := v₀) (fun r hr h => hfree r hr v₀ h hv₀)
      {v | v ≠ 1} (fun v => ⟨fun hv => htrans v₀ v hv₀ hv, fun ⟨r, _, hr⟩ => by
        rw [Set.mem_ofPred_eq, ← hr]
        exact fun h => hv₀ ((MulEquiv.map_eq_one_iff _).mp h)⟩)]
    rfl
  set CR : Subgroup (MulAut Q) := R ⊓ Subgroup.centralizer ({ψ} : Set (MulAut Q)) with hCR
  have hcardC : Nat.card CR + 1 = Nat.card C := by
    have h1 : Nat.card {v : C // v ≠ 1} = Nat.card {v : Q | v ∈ C ∧ v ≠ 1} :=
      Nat.card_congr { toFun := fun v => ⟨v.1, v.1.2, fun h => v.2 (Subtype.ext h)⟩
                       invFun := fun v => ⟨⟨v.1, v.2.1⟩, fun h => v.2.2 (congrArg Subtype.val h)⟩
                       left_inv := fun _ => rfl
                       right_inv := fun _ => rfl }
    rw [← card_ne_one_add_one C, h1]
    congr 1
    refine card_eq_of_orbit (S := CR) (v₀ := v₀) (fun r hr h => hfree r hr.1 v₀ h hv₀) _
      (fun v => ⟨fun ⟨hvC, hv1⟩ => ?_, fun ⟨s, hs, hsv⟩ => ?_⟩)
    · obtain ⟨s, hsR, hsv⟩ := htrans v₀ v hv₀ hv1
      refine ⟨s, ⟨hsR, ?_⟩, hsv⟩
      have hconj : ψ * s * ψ⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hFR hψF) s).mp hsR
      have h2 : (ψ * s * ψ⁻¹) v₀ = s v₀ := by
        have hψinv : ψ⁻¹ v₀ = v₀ :=
          calc ψ⁻¹ v₀ = ψ⁻¹ (ψ v₀) := by rw [hψv]
            _ = v₀ := MulAut.inv_apply_self _ ψ v₀
        rw [MulAut.mul_apply, MulAut.mul_apply, hψinv, hsv]
        exact (hmemC v).mp hvC
      have h3 := hfree _ (R.mul_mem (R.inv_mem hsR) hconj) v₀
        (by rw [MulAut.mul_apply, h2, MulAut.inv_apply_self]) hv₀
      rw [inv_mul_eq_one] at h3
      show s ∈ Subgroup.centralizer ({ψ} : Set (MulAut Q))
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc s * ψ = ψ * s * ψ⁻¹ * ψ := by rw [← h3]
        _ = ψ * s := by group
    · refine ⟨?_, ?_⟩
      · rw [hmemC, ← hsv]
        have hc : s * ψ = ψ * s := Subgroup.mem_centralizer_singleton_iff.mp hs.2
        rw [← MulAut.mul_apply, ← hc, MulAut.mul_apply, hψv]
      · rw [← hsv]
        exact fun h => hv₀ ((MulEquiv.map_eq_one_iff _).mp h)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨f, hf⟩ := hQ.exists_card_eq
  obtain ⟨c, hc⟩ := (hQ.to_subgroup C).exists_card_eq
  have hv₀C : v₀ ∈ C := hψv
  have hc1 : 1 ≤ c := by
    by_contra h0
    have hC1 : Nat.card C = 1 := by rw [hc, show c = 0 by omega, pow_zero]
    have := (Subgroup.card_eq_one.mp hC1)
    exact hv₀ (by rw [this] at hv₀C; exact hv₀C)
  have hcf : c < f := by
    have hlt : Nat.card C < Nat.card Q := by
      by_contra hge
      have hCtop : C = ⊤ := Subgroup.eq_top_of_card_eq C (le_antisymm
        (Subgroup.card_le_card_group C) (not_lt.mp hge))
      apply hψ1
      ext v
      have hv : v ∈ C := hCtop ▸ Subgroup.mem_top v
      exact hv
    rw [hc, hf] at hlt
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp hlt
  set n := Nat.card R with hn
  have hnf : n = 2 ^ f - 1 := by omega
  have hn0 : n ≠ 0 := by
    have : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := R)
  have hgord : orderOf g = n := orderOf_eq_card_of_forall_mem_zpowers hg
  set s : MulAut Q := (g : MulAut Q) ^ (ordProj[ℓ] n) with hs
  have hsR : s ∈ R := R.pow_mem g.2 _
  have hsord : orderOf s = ordCompl[ℓ] n := by
    have h1 : s = ((g ^ (ordProj[ℓ] n) : R) : MulAut Q) := by rw [hs, Subgroup.coe_pow]
    rw [h1, Subgroup.orderOf_coe, orderOf_pow_of_dvd (Nat.ordProj_pos n ℓ).ne'
      (hgord ▸ Nat.ordProj_dvd n ℓ), hgord]
  have hsψ : s * ψ = ψ * s := by
    have hcop : (orderOf (⟨s, hRF hsR⟩ : F)).Coprime (orderOf (⟨ψ, hψF⟩ : F)) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hsord, hψord]
      exact (Nat.coprime_ordCompl hℓp hn0).symm
    exact congrArg Subtype.val (Group.IsNilpotent.commute_of_orderOf_coprime hcop).eq
  have hsCR : s ∈ CR := ⟨hsR, Subgroup.mem_centralizer_singleton_iff.mpr hsψ⟩
  have hdvd1 : ordCompl[ℓ] (2 ^ f - 1) ∣ 2 ^ c - 1 := by
    rw [← hnf, ← hsord]
    have h1 : orderOf s ∣ Nat.card CR := Subgroup.orderOf_dvd_natCard CR hsCR
    have h2 : Nat.card CR = 2 ^ c - 1 := by omega
    rwa [h2] at h1
  have hψp : IsPGroup ℓ (Subgroup.zpowers ψ) := by
    have : Fact ℓ.Prime := ⟨hℓp⟩
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hψord, pow_one])
  have : Fact ℓ.Prime := ⟨hℓp⟩
  have hmod := hψp.card_modEq_card_fixedPoints Q
  have hfix : Nat.card (MulAction.fixedPoints (Subgroup.zpowers ψ) Q) = Nat.card C := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    constructor
    · intro hv
      exact hv ⟨ψ, Subgroup.mem_zpowers ψ⟩
    · intro hv
      rintro ⟨g', hg'⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg'
      have hvψ : ψ v = v := hv
      have key : ∀ k : ℤ, (ψ ^ k) v = v := by
        intro k
        induction k using Int.induction_on with
        | zero => rfl
        | succ k ih => rw [zpow_add_one, MulAut.mul_apply, hvψ, ih]
        | pred k ih =>
          rw [zpow_sub_one, MulAut.mul_apply]
          calc (ψ ^ (-(k : ℤ))) (ψ⁻¹ v) = (ψ ^ (-(k : ℤ))) (ψ⁻¹ (ψ v)) := by rw [hvψ]
            _ = v := by rw [MulAut.inv_apply_self, ih]
      exact key k
  rw [hfix, hf, hc] at hmod
  have hle : 2 ^ c ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hcf.le
  have hdvd2 : ℓ ∣ 2 ^ f - 2 ^ c := (Nat.modEq_iff_dvd' hle).mp hmod.symm
  exact false_of_ordCompl_dvd hℓp hc1 hcf hdvd2 hdvd1

end CFSG.Walter
