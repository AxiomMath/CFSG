module

public import CFSG.RankThree.PartOne.TCX.RankInterface
public import CFSG.RankThree.PartOne.K128.F4Syl
public import CFSG.RankThree.PartOne.S11d.LieGoodConclusion
public import CFSG.RankThree.PartOne.TCF.Ree
public import CFSG.RankThree.PartOne.TCF.TitsPair
public import CFSG.RankThree.PartOne.TCF.TitsFixed
public import CFSG.RankThree.PartOne.TCF.Model

public section

namespace CFSG.RankThree.PartOne.TCX

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag CFSG.RankThree.PartOne.Sec66T
  CFSG.RankThree.PartOne.FieldFix CFSG.RankThree.PartOne.K128

theorem twoExcPair :
    TwoExcPair := by
  intro T _ _ p hp hp5 _ hpr hM α hαp hαinn _ _ x hxp hx1 hαx D hD hDα
  classical
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, K, _, _, _, β, φ, ha, hpa, hK, hβord, hφα, hk2, hchar, ⟨eC⟩⟩ :=
    TCF.exists_twoExc_model hp hp5 hM α hαp hαinn
  have : Finite (ModGL ReeTag.F4.tag K) := finite_modGL
  have : Finite (ReeTag.F4.reeGamma K a) := Subtype.finite
  have hp3 : 3 < p := by omega
  have hxo : orderOf x = p := orderOf_eq_prime hxp hx1
  have hp5' : p = 5 := by
    have hpr' : 2 ≤ CFSG.pRank p (ReeTag.F4.reeGamma K a) := by
      rw [← pRank_eq_of_mulEquiv_of_one_lt hp.one_lt φ]
      exact hpr
    obtain ⟨d, hd, hpd⟩ := ree_class hK hp hp5 hpr'
    have hQ : 2 ^ (2 * a + 1) = (2 ^ 1) ^ p := by rw [← hpa, pow_one]
    have hq1 : 1 ≤ 2 ^ 1 := by norm_num
    have hpdq : p ∣ phiF4 d (2 ^ 1) :=
      dvd_phiF4_of_dvd_pow hp hq1 hd (by rw [← hQ]; exact hpd)
    rcases hd with rfl | rfl | rfl
    · simp only [phiF4] at hpdq
      have := Nat.le_of_dvd (by norm_num) hpdq
      omega
    · simp only [phiF4] at hpdq
      have := Nat.le_of_dvd (by norm_num) hpdq
      omega
    · simp only [phiF4] at hpdq
      have h5 : p ∣ 5 := by simpa using hpdq
      exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h5
  generalize hφβ : ReeTag.F4.reeGammaFieldAut K a β = φβ at hφα eC
  have hφapp : ∀ t : T, φβ (φ t) = φ (α t) := fun t => by
    rw [← hφα]
    simp [MulAut.congr_apply]
  have hx'o : orderOf (φ x) = p := by rw [MulEquiv.orderOf_eq]; exact hxo
  have hx'fix : φβ (φ x) = φ x := by rw [hφapp, hαx]
  have hxF : φ x ∈ fixSub φβ := hx'fix
  have : Finite (fixSubfield β) := Subtype.finite
  have : CharP (fixSubfield β) ReeTag.F4.prime := hchar
  obtain ⟨eT, hodd, hres⟩ := TCF.tits_of_fixed (α := φβ) hk2 eC
  have hx''o : orderOf (⟨φ x, hxF⟩ : ↥(fixSub φβ)) = 5 := by
    rw [Subgroup.orderOf_mk, hx'o, hp5']
  have hxc : (⟨φ x, hxF⟩ : ↥(fixSub φβ)) ∈ commutator ↥(fixSub φβ) :=
    hodd _ 5 (by decide) (by rw [← hx''o]; exact pow_orderOf_eq_one _)
  have hy₀o : orderOf (eT ⟨⟨φ x, hxF⟩, hxc⟩) = 5 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx''o]
  obtain ⟨u₁, u₂, ⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩, hc₁, hc₂, hnc⟩ :=
    TCF.tits_two_pair (eT ⟨⟨φ x, hxF⟩, hxc⟩) hy₀o
  let r : ↥(commutator ↥(fixSub φβ)) → ReeTag.F4.reeGamma K a :=
    fun s => ((s : ↥(fixSub φβ)) : ReeTag.F4.reeGamma K a)
  have hr_mul : ∀ s s' : ↥(commutator ↥(fixSub φβ)), r (s * s') = r s * r s' := fun s s' => rfl
  have hr_inj : Function.Injective r := fun s s' h => Subtype.ext (Subtype.ext h)
  have hr_ord : ∀ s : ↥(commutator ↥(fixSub φβ)), orderOf (r s) = orderOf s := fun s => by
    show orderOf (((s : ↥(fixSub φβ)) : ReeTag.F4.reeGamma K a)) = _
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe]
  have hr_fix : ∀ s : ↥(commutator ↥(fixSub φβ)), φβ (r s) = r s := fun s =>
    (s : ↥(fixSub φβ)).2
  have hr_x : ∀ s : ↥(commutator ↥(fixSub φβ)), s * ⟨⟨φ x, hxF⟩, hxc⟩ = ⟨⟨φ x, hxF⟩, hxc⟩ * s →
      r s * φ x = φ x * r s := fun s h => congrArg r h
  obtain ⟨N, -, hN2, hNcomp, -⟩ := TCF.largeRee_component_data ha hK hp hp3 (φ x) hx'o
  have hD' : IsComponentOf (Subgroup.centralizer ({φ x} : Set (ReeTag.F4.reeGamma K a)))
      (D.map φ.toMonoidHom) := by
    have h := isComponentOf_map_mulEquiv φ hD
    rwa [map_centralizer_singleton_mulEquiv_good φ x] at h
  have hDN : D.map φ.toMonoidHom = N := hNcomp _ hD'
  have lift : ∀ s : ↥(commutator ↥(fixSub φβ)),
      s * ⟨⟨φ x, hxF⟩, hxc⟩ = ⟨⟨φ x, hxF⟩, hxc⟩ * s → (∃ k : ℕ, orderOf s = 2 ^ k) →
      ∃ t ∈ D ⊓ fixRes α, α t = t ∧ φ t = r s ∧ ∃ k : ℕ, orderOf t = 2 ^ k := by
    intro s hs ⟨k, hk⟩
    have hCr : r s ∈ Subgroup.centralizer ({φ x} : Set (ReeTag.F4.reeGamma K a)) :=
      Subgroup.mem_centralizer_singleton_iff.2 (hr_x s hs)
    have hrN : r s ∈ N := hN2 (r s) hCr ⟨k, by rw [hr_ord, hk]⟩
    rw [← hDN] at hrN
    obtain ⟨t, htD, htr⟩ := hrN
    have htr' : φ t = r s := htr
    refine ⟨t, Subgroup.mem_inf.2 ⟨htD, ?_⟩, ?_, htr', k, ?_⟩
    · have hres' : r s ∈ fixRes φβ := hres s
      rw [← hφα, ← fixRes_map_congr] at hres'
      obtain ⟨y, hy, hyr⟩ := hres'
      have : y = t := φ.injective (hyr.trans htr'.symm)
      exact this ▸ hy
    · apply φ.injective
      rw [← hφapp, htr', hr_fix]
    · rw [← MulEquiv.orderOf_eq φ, htr', hr_ord, hk]
  obtain ⟨t₁, ht₁, hα₁, hφ₁, o₁⟩ := lift (eT.symm u₁)
    (eT.injective (by rw [map_mul, map_mul, MulEquiv.apply_symm_apply]; exact hc₁))
    ⟨k₁, by rw [MulEquiv.orderOf_eq, hk₁]⟩
  obtain ⟨t₂, ht₂, hα₂, hφ₂, o₂⟩ := lift (eT.symm u₂)
    (eT.injective (by rw [map_mul, map_mul, MulEquiv.apply_symm_apply]; exact hc₂))
    ⟨k₂, by rw [MulEquiv.orderOf_eq, hk₂]⟩
  refine ⟨t₁, ht₁, hα₁, t₂, ht₂, hα₂, o₁, o₂, fun h => hnc ?_⟩
  have h' : r (eT.symm u₁) * r (eT.symm u₂) = r (eT.symm u₂) * r (eT.symm u₁) := by
    rw [← hφ₁, ← hφ₂, ← map_mul, ← map_mul, h]
  have h'' : eT.symm u₁ * eT.symm u₂ = eT.symm u₂ * eT.symm u₁ :=
    hr_inj (by rw [hr_mul, hr_mul]; exact h')
  have := congrArg eT h''
  simpa using this

end CFSG.RankThree.PartOne.TCX
