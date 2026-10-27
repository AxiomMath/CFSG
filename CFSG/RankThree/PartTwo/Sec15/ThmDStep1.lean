module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.RankThree.PartTwo.Sec15.F153ObsCore

public section

namespace CFSG.RankThree.PartTwo.Sec15.ThmD

open Equiv Equiv.Perm Subgroup
open scoped commutatorElement

theorem exists_inner_of_pow_three {Q : Type*} [Group Q] (K : Subgroup Q) [hK : K.Normal]
    (φ : ↥K ≃* alternatingGroup (Fin 10)) (x : Q) (hx : x ^ 3 = 1) :
    ∃ k ∈ K, ∀ y ∈ K, x * y * x⁻¹ = k * y * k⁻¹ := by
  let β : MulAut (alternatingGroup (Fin 10)) := (MulAut.congr φ) (MulAut.conjNormal x)
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 10
    (by norm_num) (by norm_num)
  obtain ⟨σ, hσ⟩ := hbij.2 β
  have hβ3 : β ^ 3 = 1 := by
    have h1 : (MulAut.conjNormal x : MulAut ↥K) ^ 3 = 1 := by
      rw [← map_pow, hx, map_one]
    simp only [β]
    rw [← map_pow, h1, map_one]
  have hσ3 : σ ^ 3 = 1 := by
    apply hbij.1
    rw [map_pow, hσ, hβ3, map_one]
  have hsign : Perm.sign σ = 1 := by
    have h := congrArg Perm.sign hσ3
    rw [map_pow, map_one] at h
    rcases Int.units_eq_one_or (Perm.sign σ) with h1 | h1
    · exact h1
    · rw [h1] at h
      exact absurd h (by decide)
  let σ' : alternatingGroup (Fin 10) := ⟨σ, Perm.mem_alternatingGroup.mpr hsign⟩
  refine ⟨(φ.symm σ' : Q), (φ.symm σ').2, fun y hy => ?_⟩
  have key : φ ⟨x * y * x⁻¹, hK.conj_mem y hy x⟩ =
      φ (φ.symm σ' * ⟨y, hy⟩ * (φ.symm σ')⁻¹) := by
    have h1 : β (φ ⟨y, hy⟩) = φ ⟨x * y * x⁻¹, hK.conj_mem y hy x⟩ := by
      show φ ((MulAut.conjNormal x) (φ.symm (φ ⟨y, hy⟩))) = _
      rw [MulEquiv.symm_apply_apply]
      exact congrArg φ (Subtype.ext rfl)
    have h2 : β (φ ⟨y, hy⟩) = σ' * φ ⟨y, hy⟩ * σ'⁻¹ := by
      rw [← hσ]
      rfl
    rw [← h1, h2, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have := congrArg Subtype.val (φ.injective key)
  simpa using this

theorem eq_one_of_central_a10 (g : alternatingGroup (Fin 10)) (hg : ∀ h, g * h = h * g) :
    g = 1 := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 10
    (by norm_num) (by norm_num)
  have h1 : (MulAut.conjNormal (g : Perm (Fin 10)) : MulAut (alternatingGroup (Fin 10))) =
      MulAut.conjNormal 1 := by
    refine MulEquiv.ext fun h => Subtype.ext ?_
    have hc : (g : Perm (Fin 10)) * (h : Perm (Fin 10)) = (h : Perm (Fin 10)) * (g : Perm (Fin 10)) :=
      congrArg Subtype.val (hg h)
    show (g : Perm (Fin 10)) * (h : Perm (Fin 10)) * (g : Perm (Fin 10))⁻¹ =
      (1 : Perm (Fin 10)) * (h : Perm (Fin 10)) * (1 : Perm (Fin 10))⁻¹
    rw [hc]
    group
  have := hbij.1 h1
  exact Subtype.ext (by simpa using this)

theorem eq_one_of_central_in {Q : Type*} [Group Q] (K : Subgroup Q)
    (φ : ↥K ≃* alternatingGroup (Fin 10)) (g : Q) (hgK : g ∈ K) (hg : ∀ y ∈ K, g * y = y * g) :
    g = 1 := by
  have h1 : φ ⟨g, hgK⟩ = 1 := by
    apply eq_one_of_central_a10
    intro h
    obtain ⟨y, rfl⟩ := φ.surjective h
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext (hg y y.2))
  have : (⟨g, hgK⟩ : ↥K) = 1 := φ.injective (by rw [h1, map_one])
  exact congrArg Subtype.val this

theorem decompose_of_aut_a10 {Q : Type*} [Group Q] (K Â : Subgroup Q) [hK : K.Normal]
    (φ : ↥K ≃* alternatingGroup (Fin 10))
    (hÂab : ∀ x ∈ Â, ∀ y ∈ Â, x * y = y * x) (hÂ3 : ∀ x ∈ Â, x ^ 3 = 1) :
    ∀ x ∈ Â, ∃ k ∈ K, (∀ y ∈ K, (k⁻¹ * x) * y = y * (k⁻¹ * x)) ∧ (k⁻¹ * x) ^ 3 = 1 ∧
      ∀ x' ∈ Â, (k⁻¹ * x) * x' = x' * (k⁻¹ * x) := by
  intro x hx
  obtain ⟨k, hkK, hk⟩ := exists_inner_of_pow_three K φ x (hÂ3 x hx)
  have hxk : x * k = k * x := by
    have := hk k hkK
    calc x * k = (x * k * x⁻¹) * x := by group
      _ = (k * k * k⁻¹) * x := by rw [this]
      _ = k * x := by group
  have hzK : ∀ y ∈ K, (k⁻¹ * x) * y = y * (k⁻¹ * x) := by
    intro y hy
    have := hk y hy
    calc k⁻¹ * x * y = k⁻¹ * (x * y * x⁻¹) * x := by group
      _ = k⁻¹ * (k * y * k⁻¹) * x := by rw [this]
      _ = y * (k⁻¹ * x) := by group
  have hcomm : Commute k⁻¹ x := Commute.inv_left (show Commute k x from hxk.symm)
  have hz3' : (k⁻¹ * x) ^ 3 = (k⁻¹) ^ 3 := by
    rw [hcomm.mul_pow, hÂ3 x hx, mul_one]
  have hk3 : (k⁻¹) ^ 3 = 1 := by
    refine eq_one_of_central_in K φ _ (K.pow_mem (K.inv_mem hkK) 3) fun y hy => ?_
    rw [← hz3']
    exact ((show Commute (k⁻¹ * x) y from hzK y hy).pow_left 3).eq
  refine ⟨k, hkK, hzK, by rw [hz3', hk3], ?_⟩
  intro x' hx'
  obtain ⟨k', hk'K, hk'⟩ := exists_inner_of_pow_three K φ x' (hÂ3 x' hx')
  have hxx' : x * x' = x' * x := hÂab x hx x' hx'
  have hkk' : k * k' = k' * k := by
    have E : ∀ y ∈ K, (k * k') * y * (k * k')⁻¹ = (k' * k) * y * (k' * k)⁻¹ := by
      intro y hy
      have hu : x' * y * x'⁻¹ ∈ K := hK.conj_mem y hy x'
      have hv : x * y * x⁻¹ ∈ K := hK.conj_mem y hy x
      have e1 : x * (x' * y * x'⁻¹) * x⁻¹ = (k * k') * y * (k * k')⁻¹ := by
        rw [hk _ hu, hk' y hy]
        group
      have e2 : x' * (x * y * x⁻¹) * x'⁻¹ = (k' * k) * y * (k' * k)⁻¹ := by
        rw [hk' _ hv, hk y hy]
        group
      have e3 : x * (x' * y * x'⁻¹) * x⁻¹ = x' * (x * y * x⁻¹) * x'⁻¹ := by
        calc x * (x' * y * x'⁻¹) * x⁻¹ = (x * x') * y * (x * x')⁻¹ := by group
          _ = (x' * x) * y * (x' * x)⁻¹ := by rw [hxx']
          _ = x' * (x * y * x⁻¹) * x'⁻¹ := by group
      rw [← e1, ← e2, e3]
    have hcK : (k * k') * (k' * k)⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem hkK hk'K) (K.inv_mem (K.mul_mem hk'K hkK))
    have hc1 : (k * k') * (k' * k)⁻¹ = 1 := by
      refine eq_one_of_central_in K φ _ hcK fun y hy => ?_
      have hu : (k' * k)⁻¹ * y * (k' * k) ∈ K :=
        K.mul_mem (K.mul_mem (K.inv_mem (K.mul_mem hk'K hkK)) hy) (K.mul_mem hk'K hkK)
      have h := E _ hu
      have e : (k' * k) * ((k' * k)⁻¹ * y * (k' * k)) * (k' * k)⁻¹ = y := by group
      rw [e] at h
      calc ((k * k') * (k' * k)⁻¹) * y
          = ((k * k') * ((k' * k)⁻¹ * y * (k' * k)) * (k * k')⁻¹) * ((k * k') * (k' * k)⁻¹) := by
            group
        _ = y * ((k * k') * (k' * k)⁻¹) := by rw [h]
    exact mul_inv_eq_one.mp hc1
  have h1 : x' * k⁻¹ = k⁻¹ * x' := by
    have h := hk' k⁻¹ (K.inv_mem hkK)
    have hk'k : k' * k⁻¹ * k'⁻¹ = k⁻¹ := by
      have : k' * k⁻¹ = k⁻¹ * k' := (Commute.inv_right (show Commute k' k from hkk'.symm)).eq
      rw [this]
      group
    calc x' * k⁻¹ = (x' * k⁻¹ * x'⁻¹) * x' := by group
      _ = k⁻¹ * x' := by rw [h, hk'k]
  calc (k⁻¹ * x) * x' = k⁻¹ * (x * x') := by group
    _ = k⁻¹ * (x' * x) := by rw [hxx']
    _ = (k⁻¹ * x') * x := by group
    _ = (x' * k⁻¹) * x := by rw [h1]
    _ = x' * (k⁻¹ * x) := by group

theorem le_of_faithful_a10 {M : Type*} [Group M] [Finite M] (N Y A : Subgroup M) [N.Normal]
    [Y.Normal] (hN : ¬ 3 ∣ Nat.card N) (hNY : N ≤ Y) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA3 : ∀ a ∈ A, a ^ 3 = 1)
    (hmax : ∀ x : M, orderOf x = 3 → x ∈ Subgroup.centralizer (A : Set M) → x ∈ A)
    (φ : ↥(Y.map (QuotientGroup.mk' N)) ≃* alternatingGroup (Fin 10))
    (hfaith : ∀ a ∈ A, a ≠ 1 → ∃ y ∈ Y, ⁅y, a⁆ ∉ N) : A ≤ Y := by
  haveI hKn : (Y.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.Normal.map ‹Y.Normal› _ (QuotientGroup.mk'_surjective N)
  have hÂab : ∀ x ∈ A.map (QuotientGroup.mk' N), ∀ y ∈ A.map (QuotientGroup.mk' N), x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAab a ha b hb]
  have hÂ3 : ∀ x ∈ A.map (QuotientGroup.mk' N), x ^ 3 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hA3 a ha, map_one]
  have hA3' : IsPGroup 3 A := fun a => ⟨1, by
    refine Subtype.ext ?_
    simpa using hA3 a a.2⟩
  have hNc : (Nat.card N).Coprime 3 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN).symm
  intro a ha
  obtain ⟨k, hkK, hzK, hz3, hzÂ⟩ := decompose_of_aut_a10 (Y.map (QuotientGroup.mk' N))
    (A.map (QuotientGroup.mk' N)) φ hÂab hÂ3 (QuotientGroup.mk' N a) ⟨a, ha, rfl⟩
  have hz1 : k⁻¹ * QuotientGroup.mk' N a = 1 := by
    by_contra hne
    have horder : orderOf (k⁻¹ * QuotientGroup.mk' N a) = 3 := by
      have hd : orderOf (k⁻¹ * QuotientGroup.mk' N a) ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
      rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hne
      · exact h
    obtain ⟨w, hwA, hwz⟩ := F153Obs.lift_of_maximal N hNc A hA3' hmax _ horder
      (fun a' ha' => hzÂ _ ⟨a', ha', rfl⟩)
    have hw1 : w = 1 := by
      by_contra hw
      obtain ⟨y, hyY, hy⟩ := hfaith w hwA hw
      apply hy
      have hc : (QuotientGroup.mk' N w) * QuotientGroup.mk' N y =
          QuotientGroup.mk' N y * QuotientGroup.mk' N w := by
        have := hzK _ ⟨y, hyY, rfl⟩
        have hwz' : QuotientGroup.mk' N w = k⁻¹ * QuotientGroup.mk' N a := hwz
        rw [hwz']
        exact this
      have h1 : QuotientGroup.mk' N ⁅y, w⁆ = 1 := by
        rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
        have : QuotientGroup.mk' N y * QuotientGroup.mk' N w =
            QuotientGroup.mk' N w * QuotientGroup.mk' N y := hc.symm
        rw [this]
        group
      exact (QuotientGroup.eq_one_iff _).mp h1
    apply hne
    have hwz' : QuotientGroup.mk' N w = k⁻¹ * QuotientGroup.mk' N a := hwz
    rw [← hwz', hw1, map_one]
  have hak : QuotientGroup.mk' N a = k := by
    have := congrArg (fun t => k * t) hz1
    simpa using this
  obtain ⟨y, hyY, hy⟩ := (show QuotientGroup.mk' N a ∈ Y.map (QuotientGroup.mk' N) from hak ▸ hkK)
  have hyn : y⁻¹ * a ∈ N := QuotientGroup.eq.mp hy
  have : a = y * (y⁻¹ * a) := by group
  rw [this]
  exact Y.mul_mem hyY (hNY hyn)

end CFSG.RankThree.PartTwo.Sec15.ThmD
