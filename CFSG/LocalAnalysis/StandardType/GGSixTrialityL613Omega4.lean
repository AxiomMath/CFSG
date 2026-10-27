module

public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613Omega4Std
public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613Omega4Frame
public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613Cfg
public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613C3

public section

namespace CFSG.StandardType

namespace L613O4

open Multiplicative CFSG.StandardType.Triality CFSG.StandardType.D4Rank
  CFSG.StandardType.L613KG CFSG.StandardType.NoOffOm CFSG.StandardType.OrthD4
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData QuadraticMap

variable {K : Type} [Field K]

section Weight

theorem eq_conj_dg [Finite K] [CharP K 2] {u w : Fin 4 → Fin (2 * 4) → K} {h g : Om8 K}
    {i : Fin 4} {c : Fin 4 → Kˣ} (hci : c i = 1)
    (hh : ∀ m, m ≠ i → act h (AutOm.pvec m true) = u m ∧ act h (AutOm.pvec m false) = w m)
    (hhi : (act h (AutOm.pvec i true) = u i ∧ act h (AutOm.pvec i false) = w i) ∨
      (act h (AutOm.pvec i true) = w i ∧ act h (AutOm.pvec i false) = u i))
    (hg : ∀ m, act g (u m) = (c m : K) • u m ∧ act g (w m) = (((c m)⁻¹ : Kˣ) : K) • w m) :
    g = h * dg c * h⁻¹ := by
  have hdt : ∀ m, act (dg c) (AutOm.pvec m true) = (c m : K) • AutOm.pvec m true := fun m => by
    rw [AutOm.pvec_true, act_dg_single, twHom_ie]
  have hdf : ∀ m, act (dg c) (AutOm.pvec m false) = (((c m)⁻¹ : Kˣ) : K) • AutOm.pvec m false :=
    fun m => by rw [AutOm.pvec_false, act_dg_single, twHom_jf]
  have hui : act g (u i) = u i := by rw [(hg i).1, hci, Units.val_one, one_smul]
  have hwi : act g (w i) = w i := by rw [(hg i).2, hci, inv_one, Units.val_one, one_smul]
  have hbasis : ∀ (m : Fin 4) (r : Bool),
      act g (act h (AutOm.pvec m r)) = act h (act (dg c) (AutOm.pvec m r)) := by
    intro m r
    by_cases hm : m = i
    · subst hm
      have hdi : act (dg c) (AutOm.pvec m r) = AutOm.pvec m r := by
        cases r
        · rw [hdf, hci, inv_one, Units.val_one, one_smul]
        · rw [hdt, hci, Units.val_one, one_smul]
      rw [hdi]
      rcases hhi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases r <;>
        simp only [h1, h2, hui, hwi]
    · cases r
      · rw [hdf, act_smul, (hh m hm).2, (hg m).2]
      · rw [hdt, act_smul, (hh m hm).1, (hg m).1]
  have key : ∀ v, act g (act h v) = act h (act (dg c) v) := by
    have hW : LinearMap.ker ((omRep g).comp (omRep h) - (omRep h).comp (omRep (dg c))) = ⊤ :=
      AutOm.eq_top_of_pvec_mem fun m r => by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
          sub_eq_zero, omRep_apply, omRep_apply, omRep_apply, omRep_apply]
        exact hbasis m r
    intro v
    have hv : v ∈ LinearMap.ker ((omRep g).comp (omRep h) - (omRep h).comp (omRep (dg c))) := by
      rw [hW]
      exact Submodule.mem_top
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      sub_eq_zero, omRep_apply, omRep_apply, omRep_apply, omRep_apply] at hv
    exact hv
  refine eq_mul_inv_of_mul_eq (om8_ext fun v => ?_)
  rw [act_mul, act_mul, key]

theorem weight_mul {u w : Fin 4 → Fin (2 * 4) → K} {g g' : Om8 K} {c c' : Fin 4 → Kˣ}
    (hg : ∀ m, act g (u m) = (c m : K) • u m ∧ act g (w m) = (((c m)⁻¹ : Kˣ) : K) • w m)
    (hg' : ∀ m, act g' (u m) = (c' m : K) • u m ∧ act g' (w m) = (((c' m)⁻¹ : Kˣ) : K) • w m) :
    ∀ m, act (g * g') (u m) = ((c * c') m : K) • u m ∧
      act (g * g') (w m) = ((((c * c') m)⁻¹ : Kˣ) : K) • w m := by
  intro m
  refine ⟨?_, ?_⟩
  · rw [act_mul, (hg' m).1, act_smul, (hg m).1, smul_smul, Pi.mul_apply, Units.val_mul,
      mul_comm (c' m : K)]
  · rw [act_mul, (hg' m).2, act_smul, (hg m).2, smul_smul, Pi.mul_apply, mul_inv,
      Units.val_mul, mul_comm (((c' m)⁻¹ : Kˣ) : K)]

theorem weight_inv {u w : Fin 4 → Fin (2 * 4) → K} {g : Om8 K} {c : Fin 4 → Kˣ}
    (hg : ∀ m, act g (u m) = (c m : K) • u m ∧ act g (w m) = (((c m)⁻¹ : Kˣ) : K) • w m) :
    ∀ m, act g⁻¹ (u m) = ((c⁻¹ m : Kˣ) : K) • u m ∧
      act g⁻¹ (w m) = ((((c⁻¹) m)⁻¹ : Kˣ) : K) • w m := by
  intro m
  have e : ∀ (a : Fin (2 * 4) → K) (t : Kˣ), act g a = (t : K) • a →
      act g⁻¹ a = ((t⁻¹ : Kˣ) : K) • a := by
    intro a t ha
    have h1 := act_inv_act g a
    rw [ha, act_smul] at h1
    calc act g⁻¹ a = ((t⁻¹ : Kˣ) : K) • ((t : K) • act g⁻¹ a) := by
          rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
      _ = ((t⁻¹ : Kˣ) : K) • a := by rw [h1]
  refine ⟨?_, ?_⟩
  · rw [e _ _ (hg m).1, Pi.inv_apply]
  · rw [e _ _ (hg m).2, Pi.inv_apply]

end Weight


section CommFix

@[expose] def commFix (y : Om8 K) : Subgroup (Om8 K) where
  carrier := {g | ∀ v, act g (act y v - v) = act y v - v}
  mul_mem' := fun {g g'} hg hg' v => by rw [act_mul, hg' v, hg v]
  one_mem' := fun v => act_one _
  inv_mem' := fun {g} hg v => by
    conv_lhs => rw [← hg v]
    rw [act_inv_act]

theorem act_eq_of_mem_commFix {y g : Om8 K} (hg : g ∈ commFix y) {a : Fin (2 * 4) → K} {l : K}
    (ha : act y a = l • a) (hl : l - 1 ≠ 0) : act g a = a := by
  have e : a = act y ((l - 1)⁻¹ • a) - (l - 1)⁻¹ • a := by
    rw [act_smul, ha, smul_smul, ← sub_smul,
      show (l - 1)⁻¹ * l - (l - 1)⁻¹ = (l - 1)⁻¹ * (l - 1) by ring, inv_mul_cancel₀ hl, one_smul]
  rw [e]
  exact hg _

end CommFix

section Main

variable [Finite K] [CharP K 2]

theorem omegaFour_factor (hK3 : 3 ∣ Nat.card K - 1)
    {ι₁ : Multiplicative (Fin 4 → ZMod 3) →* Om8 K}
    (hfr : ∀ s s' : Fin 4 → ZMod 3,
      (∀ v, act (ι₁ (ofAdd s')) v = v → act (ι₁ (ofAdd s)) v = v) ↔ SuppLE s s')
    (hdim : ∀ s : Fin 4 → ZMod 3, omFixDim (ι₁ (ofAdd s)) + 2 * (supp s).card = 8)
    {i j k l : Fin 4} (hij : i ≠ j) (hkl : k ≠ l) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) {J : Subgroup (Om8 K)}
    (hJ : CFSG.Assembly.IsComponentOf J (Subgroup.centralizer
      {ι₁ (ofAdd (Pi.single i 1)), ι₁ (ofAdd (Pi.single j 1))}))
    (htriv : ∀ g ∈ J, ∀ w, act g (act (ι₁ (ofAdd (Pi.single i 1 + Pi.single j 1))) w - w) =
      act (ι₁ (ofAdd (Pi.single i 1 + Pi.single j 1))) w - w) :
    J ≤ Subgroup.centralizer {ι₁ (ofAdd (Pi.single k 1 + Pi.single l 1))} ∨
      J ≤ Subgroup.centralizer {ι₁ (ofAdd (Pi.single k 1 - Pi.single l 1))} := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hω⟩ : ∃ ω : Kˣ, orderOf ω = 3 :=
    exists_prime_orderOf_dvd_card' 3 (by rw [Nat.card_units]; exact hK3)
  obtain ⟨hω1, hωi1, -⟩ := units_facts hω
  have hq : 4 ≤ Nat.card K := by
    have h1 : 1 < Nat.card K := Finite.one_lt_card
    have h3 : 3 ≤ Nat.card K - 1 := Nat.le_of_dvd (by omega) hK3
    omega
  have hl1 : (ω : K) - 1 ≠ 0 := sub_ne_zero.mpr fun h => hω1 (Units.ext (by rw [h, Units.val_one]))
  have hl2 : ((ω⁻¹ : Kˣ) : K) - 1 ≠ 0 :=
    sub_ne_zero.mpr fun h => hωi1 (Units.ext (by rw [h, Units.val_one]))
  obtain ⟨u, w, hu, hw, huwo, hframe⟩ := exists_frame_eigen hfr hdim hω
  obtain ⟨h, hh, hhi⟩ := exists_om8_of_hypFrame hframe i
  have hwb : ∀ n m, act (ι₁ (ofAdd (Pi.single n 1))) (u m) =
        (((Pi.mulSingle n ω : Fin 4 → Kˣ) m : Kˣ) : K) • u m ∧
      act (ι₁ (ofAdd (Pi.single n 1))) (w m) =
        ((((Pi.mulSingle n ω : Fin 4 → Kˣ) m)⁻¹ : Kˣ) : K) • w m := by
    intro n m
    by_cases hmn : m = n
    · subst hmn
      rw [Pi.mulSingle_eq_same]
      exact ⟨hu m, hw m⟩
    · rw [Pi.mulSingle_eq_of_ne hmn, inv_one, Units.val_one, one_smul, one_smul]
      exact huwo m n (Ne.symm hmn)
  have hy : ι₁ (ofAdd (Pi.single i 1 + Pi.single j 1)) =
      ι₁ (ofAdd (Pi.single i 1)) * ι₁ (ofAdd (Pi.single j 1)) := by
    rw [ofAdd_add, map_mul]
  have hzp : ι₁ (ofAdd (Pi.single k 1 + Pi.single l 1)) =
      ι₁ (ofAdd (Pi.single k 1)) * ι₁ (ofAdd (Pi.single l 1)) := by
    rw [ofAdd_add, map_mul]
  have hzm : ι₁ (ofAdd (Pi.single k 1 - Pi.single l 1)) =
      ι₁ (ofAdd (Pi.single k 1)) * (ι₁ (ofAdd (Pi.single l 1)))⁻¹ := by
    rw [ofAdd_sub, map_div, div_eq_mul_inv]
  have hzp' : ι₁ (ofAdd (Pi.single k 1 + Pi.single l 1)) =
      h * dg (Pi.mulSingle k ω * Pi.mulSingle l ω) * h⁻¹ := by
    rw [hzp]
    exact eq_conj_dg (mulSingle_two_of_ne hik hil ω ω) hh hhi
      (weight_mul (fun m => hwb k m) (fun m => hwb l m))
  have hzm' : ι₁ (ofAdd (Pi.single k 1 - Pi.single l 1)) =
      h * dg (Pi.mulSingle k ω * Pi.mulSingle l ω⁻¹) * h⁻¹ := by
    rw [hzm, Pi.mulSingle_inv]
    exact eq_conj_dg (by rw [← Pi.mulSingle_inv]; exact mulSingle_two_of_ne hik hil ω ω⁻¹) hh hhi
      (weight_mul (fun m => hwb k m) (weight_inv (fun m => hwb l m)))
  set y := ι₁ (ofAdd (Pi.single i 1 + Pi.single j 1)) with hydef
  have hwy := weight_mul (fun m => hwb i m) (fun m => hwb j m)
  rw [← hy] at hwy
  have hcy : ∀ m, (m = i ∨ m = j) → (Pi.mulSingle i ω * Pi.mulSingle j ω : Fin 4 → Kˣ) m = ω := by
    rintro m (rfl | rfl)
    · rw [mulSingle_two_left hij]
    · rw [mulSingle_two_right hij]
  have hfixe : ∀ g ∈ commFix y, ∀ m, (m = i ∨ m = j) → act g (u m) = u m ∧ act g (w m) = w m := by
    intro g hg m hm
    refine ⟨act_eq_of_mem_commFix hg (hwy m).1 ?_, act_eq_of_mem_commFix hg (hwy m).2 ?_⟩
    · rw [hcy m hm]
      exact hl1
    · rw [hcy m hm]
      exact hl2
  have hconjfix : ∀ g ∈ commFix y, ∀ m, (m = i ∨ m = j) → ∀ r,
      act (h⁻¹ * g * h) (AutOm.pvec m r) = AutOm.pvec m r := by
    intro g hg m hm r
    rw [act_mul, act_mul]
    suffices hs : act g (act h (AutOm.pvec m r)) = act h (AutOm.pvec m r) by
      rw [hs, act_inv_act]
    obtain ⟨hgu, hgw⟩ := hfixe g hg m hm
    rcases hm with rfl | rfl
    · rcases hhi with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> cases r <;> simp only [h1, h2, hgu, hgw]
    · obtain ⟨h1, h2⟩ := hh m (Ne.symm hij)
      cases r <;> simp only [h1, h2, hgu, hgw]
  set Y : Subgroup (Om8 K) := (rootPlus k l).comap (MulAut.conj h⁻¹).toMonoidHom with hYdef
  have hYmem : ∀ g, g ∈ Y ↔ h⁻¹ * g * h ∈ rootPlus k l := fun g => by
    rw [hYdef, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
  set H := Subgroup.centralizer
    ({ι₁ (ofAdd (Pi.single i 1)), ι₁ (ofAdd (Pi.single j 1))} : Set (Om8 K)) with hHdef
  have hJN : J ≤ commFix y := fun g hg => htriv g hg
  have hJM : CFSG.Assembly.IsComponentOf J (H ⊓ commFix y) := by
    refine ⟨le_inf hJ.1 hJN, ?_, hJ.2.2⟩
    have hs := L613Cfg.isSubnormal_inf_right hJ.2.1 (commFix y)
    rwa [inf_eq_left.mpr hJN] at hs
  have hYn : (Y.subgroupOf (H ⊓ commFix y)).Normal := by
    constructor
    intro a ha g
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hYmem]
    rw [hYmem] at ha
    have hg : (g : Om8 K) ∈ commFix y := g.2.2
    have e : h⁻¹ * ((g : Om8 K) * (a : Om8 K) * (g : Om8 K)⁻¹) * h =
        (h⁻¹ * g * h) * (h⁻¹ * a * h) * (h⁻¹ * g * h)⁻¹ := by group
    rw [e]
    exact conj_mem_rootPlus hq hij hkl hik hil hjk hjl (hconjfix g hg i (Or.inl rfl))
      (hconjfix g hg j (Or.inr rfl)) ha
  rcases ggComponent_le_or_commute hJM hYn.isSubnormal with hle | hc
  ·
    right
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff, hzm']
    have hcomm := rootMinus_commute hkl (dg_mem_rootMinus hkl ω) ((hYmem g).mp (hle hg))
    calc g * (h * dg (Pi.mulSingle k ω * Pi.mulSingle l ω⁻¹) * h⁻¹) =
          h * ((h⁻¹ * g * h) * dg (Pi.mulSingle k ω * Pi.mulSingle l ω⁻¹)) * h⁻¹ := by group
      _ = h * (dg (Pi.mulSingle k ω * Pi.mulSingle l ω⁻¹) * (h⁻¹ * g * h)) * h⁻¹ := by
          rw [hcomm]
      _ = h * dg (Pi.mulSingle k ω * Pi.mulSingle l ω⁻¹) * h⁻¹ * g := by group
  ·
    left
    intro g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hdisj : ∀ x, (Pi.single k 1 + Pi.single l 1 : Fin 4 → ZMod 3) x ≠ 0 →
        (Pi.single i 1 + Pi.single j 1 : Fin 4 → ZMod 3) x = 0 := by
      intro x hx
      rw [Pi.add_apply] at hx ⊢
      by_cases hxi : x = i
      · subst hxi
        rw [Pi.single_eq_of_ne hik, Pi.single_eq_of_ne hil, add_zero] at hx
        exact absurd rfl hx
      · by_cases hxj : x = j
        · subst hxj
          rw [Pi.single_eq_of_ne hjk, Pi.single_eq_of_ne hjl, add_zero] at hx
          exact absurd rfl hx
        · rw [Pi.single_eq_of_ne hxi, Pi.single_eq_of_ne hxj, add_zero]
    have hzH : ι₁ (ofAdd (Pi.single k 1 + Pi.single l 1)) ∈ H := by
      rw [hHdef, Subgroup.mem_centralizer_iff]
      rintro x (rfl | rfl)
      · exact L613Cfg.frame_comm ι₁ _ _
      · exact L613Cfg.frame_comm ι₁ _ _
    have hzN : ι₁ (ofAdd (Pi.single k 1 + Pi.single l 1)) ∈ commFix y :=
      fun v => L613Cfg.act_comm_of_disjoint hfr hdim hdisj v
    have hzY : ι₁ (ofAdd (Pi.single k 1 + Pi.single l 1)) ∈ Y := by
      rw [hYmem, hzp']
      have e : h⁻¹ * (h * dg (Pi.mulSingle k ω * Pi.mulSingle l ω) * h⁻¹) * h =
          dg (Pi.mulSingle k ω * Pi.mulSingle l ω) := by group
      rw [e]
      exact dg_mem_rootPlus hkl ω
    exact hc g hg _ (Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hzH, hzN⟩, hzY⟩)

end Main

end L613O4

open L613O4

theorem ggOmegaFourFactorInput_holds : GGOmegaFourFactorInput := by
  intro K _ _ _ hK3 ι₁ hfr hdim i j k l hij hkl hik hil hjk hjl J hJ htriv
  exact omegaFour_factor hK3 hfr hdim hij hkl hik hil hjk hjl hJ htriv

section Assembly

theorem ggSixTrialityDClassThreeInput_holds : GGSixTrialityDClassThreeInput :=
  ggSixTrialityDClassThreeInput_of_omegaFour ggOmegaFourFactorInput_holds

theorem ggSixTrialityInput_of_lSixEleven (h611 : GGSixLSixElevenInput) : GGSixTrialityInput :=
  ggSixTrialityInput_of_lSixEleven_dClassThree h611 ggSixTrialityDClassThreeInput_holds

end Assembly

end CFSG.StandardType
