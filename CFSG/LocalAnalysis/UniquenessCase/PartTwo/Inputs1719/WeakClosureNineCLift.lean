module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCBar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNIrred

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open CFSG.LocalAnalysis.WeakClosure81.NFW

theorem barSub_pCoreOf_liftSub_le {G : Type} [Group G] [Finite G] {N : Subgroup G} {X : Type}
    [Group X] [Finite X] {π : ↥N →* X} (hπ : Function.Surjective π) (Kb : Subgroup X) :
    barSub π (pCoreOf 2 (liftSub π Kb)) ≤ pCoreOf 2 Kb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : pCoreOf 2 (liftSub π Kb) ≤ N :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (liftSub_le Kb)
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 ?_ ?_
    (isPGroup_barSub (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _))
  · rw [barSub_le_iff hle]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 _
  · have h := barSub_le_normalizer (π := π)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (liftSub π Kb))
    rwa [barSub_liftSub hπ Kb] at h

variable {X : Type} [Group X] [Finite X] {B : Type} [Group B] [Finite B]

namespace TCBar

variable {Lb Tb : Subgroup X} {π : ↥(tcN1 Lb Tb) →* B} {Es : Subgroup B}
variable (c : TCBar Lb Tb π Es)
include c

omit [Finite B] in
theorem liftSub_inf_T (K : Subgroup B) :
    liftSub π (K ⊓ barSub π Tb) = liftSub π K ⊓ Tb := by
  rw [liftSub_inf, c.liftSub_barSub_T]
  refine le_antisymm (inf_le_inf_left _ inf_le_left) fun x hx => ?_
  exact ⟨hx.1, hx.2, (sup_le le_normalizer inf_le_right) (liftSub_le K hx.1)⟩

theorem lift_twoPTwoIrred {K Y : Subgroup B} {p : ℕ} (h : TwoPTwoIrred K (K ⊓ barSub π Tb) Y p) :
    ∃ Yb : Subgroup X, TwoPTwoIrred (liftSub π K) (liftSub π K ⊓ Tb) Yb p ∧ barSub π Yb = Y ∧
      Yb ≤ tcN1 Lb Tb := by
  obtain ⟨Yb, hY, hYb, -⟩ := twoPTwoIrred_liftSub c.ker c.surj h
  rw [c.liftSub_inf_T] at hY
  exact ⟨Yb, hY, hYb, hY.sylowP.le.trans (liftSub_le K)⟩

omit [Finite B] c in
theorem three_of {Y : Subgroup B} {Yb : Subgroup X} (hYb : barSub π Yb = Y)
    (h : ∃ y ∈ closure {z | ∃ d ∈ barSub π Tb, ∃ x ∈ Y, z = d * x * d⁻¹}, orderOf y = 3) :
    ∀ J : Subgroup X, Tb ≤ normalizer (J : Set X) → Yb ≤ J → ∃ x ∈ J, orderOf x = 3 := by
  intro J hTJ hYJ
  obtain ⟨y, hy, hy3⟩ := h
  have hcl : closure {z | ∃ d ∈ barSub π Tb, ∃ x ∈ Y, z = d * x * d⁻¹} ≤ barSub π J := by
    rw [closure_le]
    rintro _ ⟨d, ⟨t, ht, rfl⟩, x, hx, rfl⟩
    rw [← hYb] at hx
    obtain ⟨yb, hyb, rfl⟩ := hx
    refine ⟨t * yb * t⁻¹, ?_, by simp only [map_mul, map_inv]⟩
    rw [SetLike.mem_coe, mem_subgroupOf] at ht hyb ⊢
    simpa using (mem_normalizer_iff.mp (hTJ ht) yb).mp (hYJ hyb)
  exact exists_orderOf_eq_of_barSub (hcl hy) hy3

theorem fix_lift {A : Subgroup X} (hA : A ≤ tcN1 Lb Tb) {K Y : Subgroup B} {p : ℕ}
    (hw : FixWit914 (barSub π Tb) (barSub π A) K Y p) :
    ∃ Yb : Subgroup X, TwoPTwoIrred (liftSub π K) (liftSub π K ⊓ Tb) Yb p ∧
      A ≤ liftSub π K ∧ ¬ A ≤ pCoreOf 2 (liftSub π K) ∧
      (p = 3 ∨ ∀ J : Subgroup X, Tb ≤ normalizer (J : Set X) → Yb ≤ J →
        ∃ x ∈ J, orderOf x = 3) := by
  obtain ⟨Yb, hY, hYb, -⟩ := c.lift_twoPTwoIrred hw.irr
  refine ⟨Yb, hY, (barSub_le_iff hA).1 hw.le, fun hAO => hw.not_le ?_, ?_⟩
  · exact (barSub_mono hAO).trans (barSub_pCoreOf_liftSub_le c.surj K)
  · rcases hw.three with h3 | h3
    · exact Or.inl h3
    · exact Or.inr (three_of hYb h3)

omit [Finite B] in
theorem Lb_le_of_closing {Ks : Finset (Subgroup B)} (hgen : (⨆ K ∈ Ks, K) ⊔ barSub π Tb = ⊤) :
    Lb ≤ (⨆ K ∈ Ks, liftSub π K) ⊔ Tb := by
  set J := (⨆ K ∈ Ks, liftSub π K) ⊔ tcT1 Lb Tb with hJ
  have hJN : J ≤ tcN1 Lb Tb := sup_le (iSup₂_le fun K _ => liftSub_le K) le_sup_right
  have hbar : barSub π J = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine sup_le (iSup₂_le fun K hK => ?_) ?_
    · rw [← barSub_liftSub c.surj K]
      exact barSub_mono ((le_iSup₂_of_le (f := fun K _ => liftSub π K) K hK le_rfl).trans
        le_sup_left)
    · rw [barSub_tcT1]
      exact barSub_mono le_sup_right
  have hJ1 : liftSub π (barSub π J) = J :=
    liftSub_barSub c.ker (c.pCore_le_T1.trans le_sup_right) hJN
  have hJ2 : J = tcN1 Lb Tb := by rw [← hJ1, hbar, liftSub_top]
  calc Lb ≤ tcN1 Lb Tb := le_sup_left
    _ = J := hJ2.symm
    _ ≤ (⨆ K ∈ Ks, liftSub π K) ⊔ Tb := sup_le_sup_left inf_le_left _

omit [Finite X] [Finite B] c in
theorem mem_centralizer_conj_iff {x s : X} :
    x ∈ centralizer (conjSubgroup Lb s : Set X) ↔ s * x * s⁻¹ ∈ centralizer (Lb : Set X) := by
  rw [← E3.conjSubgroup_centralizer, mem_conjSubgroup_iff]

omit [Finite X] [Finite B] c in
theorem eq_one_of_pow {x : X} {j k : ℕ} (h2 : x ^ 2 ^ j = 1) (h3 : x ^ 3 ^ k = 1) : x = 1 := by
  have hcop : Nat.Coprime (2 ^ j) (3 ^ k) := Nat.Coprime.pow j k (by norm_num)
  rw [← orderOf_eq_one_iff]
  exact Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h2)
    (orderOf_dvd_of_pow_eq_one h3))

omit [Finite X] [Finite B] in
theorem eq_one_of_mem_center {x : X} (hxT : x ∈ Tb) (hxL : x ∈ Lb)
    (hxc : ∀ y ∈ Lb, x * y = y * x) : x = 1 := by
  have hz : (⟨x, hxL⟩ : ↥Lb) ∈ center ↥Lb :=
    mem_center_iff.mpr fun y => Subtype.ext (hxc y y.2).symm
  obtain ⟨k, hk⟩ := c.center3 ⟨⟨x, hxL⟩, hz⟩
  obtain ⟨j, hj⟩ := c.sylow.isPGroup ⟨x, hxT⟩
  refine eq_one_of_pow (j := j) (k := k) ?_ ?_
  · simpa using congrArg Subtype.val hj
  · simpa using congrArg (fun z : ↥(center ↥Lb) => ((z : ↥Lb) : X)) hk

omit [Finite B] in
theorem exists_sq_ne_one : ∃ l ∈ Tb, l ∈ Lb ∧ l ^ 2 ≠ 1 := by
  obtain ⟨d, ⟨hdD, hdL⟩, hd2⟩ := c.facts.sq
  obtain ⟨l, hl, rfl⟩ := hdL
  obtain ⟨t, ht, htl⟩ := hdD
  rw [SetLike.mem_coe, mem_subgroupOf] at hl ht
  have h1 : π (t⁻¹ * l) = 1 := by rw [map_mul, map_inv, htl, inv_mul_cancel]
  have h3 : ((t⁻¹ * l : ↥(tcN1 Lb Tb)) : X) ∈ Tb := (c.mem_of_ker h1).1.1
  have hlT : (l : X) ∈ Tb := by
    have := mul_mem ht h3
    simpa using this
  refine ⟨l, hlT, hl, fun h => hd2 ?_⟩
  have h2 : l ^ 2 = 1 := Subtype.ext (by simpa using h)
  rw [← map_pow, h2, map_one]

omit [Finite B] in
theorem le_normalizer_of_normal {E : Subgroup X} (hET : E ≤ Tb)
    (hTE : Tb ≤ normalizer (E : Set X)) (hE : IsElemAbelian 2 E) :
    E ≤ normalizer (Lb : Set X) := by
  intro e he
  by_contra hne
  obtain ⟨l, hlT, hlL, hl2⟩ := c.exists_sq_ne_one
  have heT : e ∈ Tb := hET he
  have hne' : conjSubgroup Lb e⁻¹ ≠ conjSubgroup Lb 1 := by
    rw [CFSG.Quasithin.conjSubgroup_one]
    intro h
    exact hne (by simpa using conjSubgroup_eq_iff_mem_normalizer.1 h)
  have hcomm := c.comm e⁻¹ (inv_mem heT) 1 Tb.one_mem hne'
  have helL : e * l * e⁻¹ ∈ conjSubgroup Lb e⁻¹ := by
    rw [mem_conjSubgroup_iff]
    simpa [mul_assoc] using hlL
  have hL1 : ∀ y ∈ Lb, y ∈ conjSubgroup Lb 1 := fun y hy => by
    rwa [CFSG.Quasithin.conjSubgroup_one]
  have hcE : e * l * e⁻¹ * l⁻¹ ∈ E := by
    have h1 : l * e⁻¹ * l⁻¹ ∈ E := (mem_normalizer_iff.mp (hTE hlT) e⁻¹).mp (inv_mem he)
    simpa [mul_assoc] using mul_mem he h1
  have hsq := hE.2 _ hcE
  have hc1 := hcomm _ helL _ (hL1 _ (inv_mem hlL))
  have hl2e : e * l ^ 2 * e⁻¹ = l ^ 2 := by
    have : (e * l * e⁻¹ * l⁻¹) ^ 2 = e * l ^ 2 * e⁻¹ * (l ^ 2)⁻¹ := by
      rw [pow_two, pow_two]
      calc e * l * e⁻¹ * l⁻¹ * (e * l * e⁻¹ * l⁻¹)
          = (e * l * e⁻¹) * (l⁻¹ * (e * l * e⁻¹)) * l⁻¹ := by group
        _ = (e * l * e⁻¹) * ((e * l * e⁻¹) * l⁻¹) * l⁻¹ := by rw [← hc1]
        _ = e * (l * l) * e⁻¹ * (l * l)⁻¹ := by group
    rw [this] at hsq
    exact mul_inv_eq_one.mp hsq
  have hl2c : l ^ 2 ∈ conjSubgroup Lb e⁻¹ := by
    rw [← hl2e, mem_conjSubgroup_iff]
    simpa [mul_assoc] using pow_mem hlL 2
  exact hl2 (c.eq_one_of_mem_center (pow_mem hlT 2) (pow_mem hlL 2)
    fun y hy => hcomm _ hl2c y (hL1 y hy))

omit [Finite B] in
theorem eq_bot_of_barSub_eq_bot {E : Subgroup X} (hET : E ≤ tcT1 Lb Tb)
    (hTE : Tb ≤ normalizer (E : Set X)) (hπ : barSub π E = ⊥) : E = ⊥ := by
  have hC : ∀ e ∈ E, e ∈ centralizer (Lb : Set X) := by
    intro e he
    have h1 : π ⟨e, mem_sup_right (hET he)⟩ = 1 := by
      have := mem_barSub_of_mem (π := π) (mem_sup_right (hET he)) he
      rwa [hπ, mem_bot] at this
    exact (c.mem_of_ker h1).2
  rw [eq_bot_iff]
  intro e he
  rw [mem_bot]
  refine c.eq_one_of_centralizes (hET he).1 fun s hs => ?_
  rw [mem_centralizer_conj_iff]
  exact hC _ ((mem_normalizer_iff.mp (hTE hs) e).mp he)

end TCBar

end CFSG.LocalAnalysis.WeakClosure81
