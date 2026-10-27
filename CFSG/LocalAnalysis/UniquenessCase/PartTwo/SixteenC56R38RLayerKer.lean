module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56R38RTransfer
public import CFSG.Open.RankThreeDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverKer
import TauCeti.GroupTheory.Sylow
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem isCyclic_sylow_of_card {A : Type*} [Group A] [Finite A] {q : ℕ} (hq : q.Prime)
    (h1 : q ∣ Nat.card A) (h2 : ¬ q ^ 2 ∣ Nat.card A) (P : Sylow q A) : IsCyclic ↥P := by
  haveI : Fact q.Prime := ⟨hq⟩
  exact isCyclic_of_prime_card (P.card_eq_of_dvd_of_not_sq_dvd h1 h2)

theorem not_dvd_card_ker_of_layer_prod {Y H : Type} [Group Y] [Finite Y] [Group H]
    (hperf : Group.IsPerfect Y)
    (hlayer : CFSG.Open.rankThreeLayer (⊤ : Subgroup (Y ⧸ CFSG.pCore 2 Y)) = ⊤)
    (f : Y →* H) {T₀ T₁ : Subgroup H} (hcomm : ∀ x ∈ T₀, ∀ y ∈ T₁, x * y = y * x)
    (hdisj : T₀ ⊓ T₁ = ⊥) (hrange : f.range = T₀ ⊔ T₁) (hsolv : Group.IsSolvable ↥f.ker)
    (hR : CFSG.pCore 2 Y ≤ f.ker) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (h₀ : q ∣ Nat.card ↥T₀) (h₀' : ¬ q ^ 2 ∣ Nat.card ↥T₀) (h₁ : q ∣ Nat.card ↥T₁)
    (h₁' : ¬ q ^ 2 ∣ Nat.card ↥T₁) :
    ¬ q ∣ Nat.card ↥f.ker := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : Group.IsPerfect Y := hperf
  haveI : Group.IsSolvable ↥f.ker := hsolv
  let R : Subgroup Y := CFSG.pCore 2 Y
  let π : Y →* Y ⧸ R := QuotientGroup.mk' R
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective R
  have hfR : R ≤ f.ker := hR
  let fhat : Y ⧸ R →* H := QuotientGroup.lift R f hfR
  have hfhatπ : ∀ x : Y, fhat (π x) = f x := fun _ => rfl
  have hQ : Group.IsPerfect (Y ⧸ R) := Group.IsPerfect.ofSurjective hπ
  have hfhat_range : fhat.range = f.range := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := hπ z
      exact ⟨x, (hfhatπ x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨π x, hfhatπ x⟩
  have hfhat_range' : fhat.range = T₀ ⊔ T₁ := hfhat_range.trans hrange
  have hfhat_ker : fhat.ker = f.ker.map π := by
    ext z
    obtain ⟨x, rfl⟩ := hπ z
    rw [MonoidHom.mem_ker, hfhatπ x, Subgroup.mem_map]
    constructor
    · intro hfx
      exact ⟨x, (MonoidHom.mem_ker (f := f)).2 hfx, rfl⟩
    · rintro ⟨x', hx', hx''⟩
      have hx''R : x'⁻¹ * x ∈ R := (QuotientGroup.eq).mp hx''
      have hxker : x ∈ f.ker := by
        have h1 : x' * (x'⁻¹ * x) ∈ f.ker := f.ker.mul_mem hx' (hR hx''R)
        simpa only [mul_inv_cancel_left] using h1
      exact (MonoidHom.mem_ker (f := f)).1 hxker
  have hfhat_ker_solv : Group.IsSolvable ↥fhat.ker := by
    rw [hfhat_ker]
    exact Group.isSolvable_of_surjective (f := π.subgroupMap f.ker)
      (MonoidHom.subgroupMap_surjective π f.ker)
  have hfhat_ker_center : fhat.ker ≤ Subgroup.center (Y ⧸ R) := by
    haveI : fhat.ker.Normal := MonoidHom.normal_ker fhat
    exact close16_le_center_of_isSolvable hlayer hfhat_ker_solv
  have hcomm' : ∀ a : ↥T₀, ∀ b : ↥T₁, Commute (T₀.subtype a) (T₁.subtype b) :=
    fun a b => hcomm a a.2 b b.2
  let ψ : ↥T₀ × ↥T₁ →* H := MonoidHom.noncommCoprod T₀.subtype T₁.subtype hcomm'
  have hψ_range : ψ.range = T₀ ⊔ T₁ := by
    show (MonoidHom.noncommCoprod T₀.subtype T₁.subtype hcomm').range = T₀ ⊔ T₁
    rw [MonoidHom.noncommCoprod_range, Subgroup.range_subtype, Subgroup.range_subtype]
  have hdisj' : Disjoint T₀.subtype.range T₁.subtype.range := by
    rw [Subgroup.range_subtype, Subgroup.range_subtype]
    exact _root_.disjoint_iff.mpr hdisj
  have hψ_inj : Function.Injective ψ := by
    show Function.Injective (MonoidHom.noncommCoprod T₀.subtype T₁.subtype hcomm')
    rw [MonoidHom.noncommCoprod_injective]
    exact ⟨Subgroup.subtype_injective T₀, Subgroup.subtype_injective T₁, hdisj'⟩
  let φ : Y ⧸ R →* ↥T₀ × ↥T₁ :=
    (MonoidHom.ofInjective hψ_inj).symm.toMonoidHom.comp
      (fhat.codRestrict ψ.range fun x => by
        rw [hψ_range, ← hfhat_range']
        exact ⟨x, rfl⟩)
  have hφ_apply : ∀ x : Y ⧸ R, ψ (φ x) = fhat x := by
    intro x
    exact MonoidHom.apply_ofInjective_symm hψ_inj _
  have hφ_surj : Function.Surjective φ := by
    intro p
    have hp : ψ p ∈ fhat.range := by
      rw [hfhat_range', ← hψ_range]
      exact ⟨p, rfl⟩
    obtain ⟨x, hx⟩ := hp
    refine ⟨x, ?_⟩
    apply hψ_inj
    rw [hφ_apply x, hx]
  have hφ_ker : φ.ker = fhat.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hx
      have h := congrArg ψ hx
      simpa [hφ_apply x] using h
    · intro hx
      apply hψ_inj
      simp [hφ_apply x, hx]
  have hφ_ker_center : φ.ker ≤ Subgroup.center (Y ⧸ R) := by
    rw [hφ_ker]
    exact hfhat_ker_center
  haveI : Finite ↥f.range :=
    Finite.of_equiv (Y ⧸ f.ker) (QuotientGroup.quotientKerEquivRange f).toEquiv
  have hT₀_le : T₀ ≤ f.range := by rw [hrange]; exact le_sup_left
  have hT₁_le : T₁ ≤ f.range := by rw [hrange]; exact le_sup_right
  haveI : Finite ↥T₀ := Finite.of_injective (Subgroup.inclusion hT₀_le)
    (Subgroup.inclusion_injective hT₀_le)
  haveI : Finite ↥T₁ := Finite.of_injective (Subgroup.inclusion hT₁_le)
    (Subgroup.inclusion_injective hT₁_le)
  have hA : ∀ P : Sylow q ↥T₀, IsCyclic P := fun P => isCyclic_sylow_of_card hq h₀ h₀' P
  have hB : ∀ P : Sylow q ↥T₁, IsCyclic P := fun P => isCyclic_sylow_of_card hq h₁ h₁' P
  have hq_not_dvd_fhat : ¬ q ∣ Nat.card ↥fhat.ker := by
    rw [← hφ_ker]
    exact not_dvd_card_ker_of_isPerfect_prod hQ φ hφ_surj hφ_ker_center hq hA hB
  intro hqker
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' q hqker
  have hw_mem : π (z : Y) ∈ fhat.ker := by
    rw [MonoidHom.mem_ker, hfhatπ]
    exact (MonoidHom.mem_ker (f := f)).1 z.2
  by_cases hw1 : π (z : Y) = 1
  · have hzR : (z : Y) ∈ R := (QuotientGroup.eq_one_iff (z : Y)).mp hw1
    have hzord : orderOf (z : Y) = q := (Subgroup.orderOf_coe z).trans hz
    have hdvdR : q ∣ Nat.card ↥R := by
      rw [← hzord]
      exact R.orderOf_dvd_natCard hzR
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := Y)).exists_card_eq
    have hq2dvd : q ∣ 2 ^ k := by
      rw [← hk]
      exact hdvdR
    exact hq2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow hq2dvd))
  · have hw_ord_dvd : orderOf (π (z : Y)) ∣ q := by
      rw [← hz, ← Subgroup.orderOf_coe z]
      exact orderOf_map_dvd π (z : Y)
    have hw_ord_ne : orderOf (π (z : Y)) ≠ 1 := fun h => hw1 (orderOf_eq_one_iff.mp h)
    have hw_ord : orderOf (π (z : Y)) = q := by
      rcases (Nat.dvd_prime hq).mp hw_ord_dvd with h | h
      · exact absurd h hw_ord_ne
      · exact h
    have hdvd_fhat : q ∣ Nat.card ↥fhat.ker := by
      rw [← hw_ord]
      exact fhat.ker.orderOf_dvd_natCard hw_mem
    exact hq_not_dvd_fhat hdvd_fhat

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
