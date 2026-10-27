module

public import CFSG.LocalAnalysis.StandardType.PhanELocalSigma
import CFSG.LocalAnalysis.StandardType.PhanELocalFlag

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.Monster.B.Geometry Module

namespace Exch

section Line

variable {K : Type} [Field K]

@[expose] noncomputable def ofPoint (z : Submodule K (Fin 2 → K)) (hz : finrank K z = 1) :
    FlagK K 2 where
  E j := if j = 0 then ⊥ else if j = 1 then z else ⊤
  mono := by
    intro a b hab
    change (if a = 0 then ⊥ else if a = 1 then z else ⊤) ≤
      (if b = 0 then ⊥ else if b = 1 then z else ⊤)
    by_cases hb0 : b = 0
    · subst hb0
      have ha0 : a = 0 := by omega
      subst ha0
      simp
    · by_cases hb1 : b = 1
      · subst hb1
        have ha : a = 0 ∨ a = 1 := by omega
        rcases ha with rfl | rfl <;> simp
      · have hEb : (if b = 0 then ⊥ else if b = 1 then z else ⊤) = ⊤ := by
          rw [if_neg hb0, if_neg hb1]
        rw [hEb]
        exact le_top
  dim := by
    intro j hj
    interval_cases j <;> simp [hz, Module.finrank_fin_fun]
  top := by
    intro j hj
    change (if j = 0 then ⊥ else if j = 1 then z else ⊤) = ⊤
    rw [if_neg (show ¬ j = 0 by omega), if_neg (show ¬ j = 1 by omega)]

theorem ofPoint_E_one (z : Submodule K (Fin 2 → K)) (hz : finrank K z = 1) :
    (ofPoint z hz).E 1 = z := by
  show (if (1 : ℕ) = 0 then ⊥ else if (1 : ℕ) = 1 then z else ⊤) = z
  simp

theorem flag_ext {x y : FlagK K 2} (h : x.E 1 = y.E 1) : x = y := by
  apply FlagK.ext_of_mid
  intro j hj1 hj2
  have : j = 1 := by omega
  subst this
  exact h

theorem finrank_E_one (x : FlagK K 2) : finrank K (x.E 1) = 1 :=
  x.dim 1 (by norm_num)

end Line

variable (K : Type) [Field K] [Finite K] (f : ℕ) [CharP K 2]

@[expose] noncomputable def dirZ (z : Submodule K (Fin 2 → K)) : Submodule K (Fin 3 → K) :=
  Vsub 3 1 ⊔ Submodule.span K ((fun v : Fin 2 → K => (![0, sg K f (v 0), sg K f (v 1)] :
    Fin 3 → K)) '' (z : Set (Fin 2 → K)))

variable {K f}

private noncomputable def plxd_phi (v : Fin 2 → K) : Fin 3 → K :=
  ![0, sg K f (v 0), sg K f (v 1)]

private theorem plxd_dirZ_eq (z : Submodule K (Fin 2 → K)) :
    dirZ K f z = Vsub 3 1 ⊔ Submodule.span K (plxd_phi (K := K) (f := f) '' z) := rfl

private theorem plxd_phi_smul (c : K) (u : Fin 2 → K) :
    plxd_phi (K := K) (f := f) (c • u) = sg K f c • plxd_phi (K := K) (f := f) u := by
  ext i
  fin_cases i <;> simp [plxd_phi, Pi.smul_apply, smul_eq_mul, map_mul]

private theorem plxd_phi_not_mem_Vsub {u : Fin 2 → K} (hu : u ≠ 0) :
    plxd_phi (K := K) (f := f) u ∉ Vsub 3 1 := by
  intro hmem
  apply hu
  funext i
  fin_cases i
  · have h1 : plxd_phi (K := K) (f := f) u 1 = 0 := hmem 1 (by norm_num)
    have : sg K f (u 0) = 0 := by simpa [plxd_phi] using h1
    exact (sg K f).injective (by simpa using this)
  · have h2 : plxd_phi (K := K) (f := f) u 2 = 0 := hmem 2 (by norm_num)
    have : sg K f (u 1) = 0 := by simpa [plxd_phi] using h2
    exact (sg K f).injective (by simpa using this)

private theorem plxd_span_phi_span_singleton {u : Fin 2 → K} (hu : u ≠ 0) :
    Submodule.span K (plxd_phi (K := K) (f := f) '' (Submodule.span K {u})) =
      Submodule.span K {plxd_phi (K := K) (f := f) u} := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hv
    exact Submodule.mem_span_singleton.mpr
      ⟨sg K f c, (plxd_phi_smul (K := K) (f := f) c u).symm⟩
  · rw [Submodule.span_le]
    rintro _ hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    exact Submodule.subset_span ⟨u, Submodule.mem_span_singleton_self u, rfl⟩

theorem Vsub_le_dirZ (z : Submodule K (Fin 2 → K)) : Vsub 3 1 ≤ dirZ K f z := by
  rw [dirZ]
  exact le_sup_left

theorem finrank_dirZ (hK : Nat.card K = (2 ^ f) ^ 2) {z : Submodule K (Fin 2 → K)}
    (hz : finrank K z = 1) : finrank K (dirZ K f z) = 2 := by
  obtain ⟨u, huz, hu0⟩ : ∃ u ∈ z, u ≠ 0 := by
    have hne : z ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hz
      omega
    exact Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hzspan : z = Submodule.span K {u} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hz huz hu0
  have hdirZ : dirZ K f z = Vsub 3 1 ⊔ Submodule.span K {plxd_phi (K := K) (f := f) u} := by
    rw [plxd_dirZ_eq, hzspan, plxd_span_phi_span_singleton hu0]
  have hw0 : plxd_phi (K := K) (f := f) u ≠ 0 := by
    intro h
    exact plxd_phi_not_mem_Vsub hu0 (h ▸ Submodule.zero_mem _)
  have hinf : Vsub 3 1 ⊓ Submodule.span K {plxd_phi (K := K) (f := f) u} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨hvV, hvspan⟩ := hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hvspan
    by_cases hc : c = 0
    · rw [hc, zero_smul]
    · exfalso
      apply plxd_phi_not_mem_Vsub hu0
      have hw' : plxd_phi (K := K) (f := f) u =
          c⁻¹ • (c • plxd_phi (K := K) (f := f) u) := by
        rw [smul_smul, inv_mul_cancel₀ hc, one_smul]
      rw [hw']
      exact Submodule.smul_mem _ _ hvV
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (Vsub (K := K) 3 1)
    (Submodule.span K {plxd_phi (K := K) (f := f) u})
  rw [hinf, finrank_bot, add_zero, finrank_Vsub (K := K) (n := 3) (c := 1) (by norm_num),
    finrank_span_singleton hw0] at hsum
  rw [hdirZ]
  omega

theorem dirZ_inj (hK : Nat.card K = (2 ^ f) ^ 2) {z z' : Submodule K (Fin 2 → K)}
    (hz : finrank K z = 1) (hz' : finrank K z' = 1) (h : dirZ K f z = dirZ K f z') : z = z' := by
  obtain ⟨u, huz, hu0⟩ : ∃ u ∈ z, u ≠ 0 := by
    have hne : z ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hz
      omega
    exact Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨u', hu'z', hu'0⟩ : ∃ u ∈ z', u ≠ 0 := by
    have hne : z' ≠ ⊥ := by
      intro h
      rw [h, finrank_bot] at hz'
      omega
    exact Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hzspan : z = Submodule.span K {u} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hz huz hu0
  have hz'span : z' = Submodule.span K {u'} :=
    eq_span_singleton_of_mem_of_finrank_eq_one hz' hu'z' hu'0
  have hsup : Vsub 3 1 ⊔ Submodule.span K {plxd_phi (K := K) (f := f) u} =
      Vsub 3 1 ⊔ Submodule.span K {plxd_phi (K := K) (f := f) u'} := by
    simpa only [plxd_dirZ_eq, hzspan, hz'span, plxd_span_phi_span_singleton hu0,
      plxd_span_phi_span_singleton hu'0] using h
  have hwmem : plxd_phi (K := K) (f := f) u ∈
      Vsub 3 1 ⊔ Submodule.span K {plxd_phi (K := K) (f := f) u'} := by
    rw [← hsup]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  rw [Submodule.mem_sup] at hwmem
  obtain ⟨x, hxV, y, hy, hxy⟩ := hwmem
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  have hx0 : x 0 = 0 := by
    have h0 := congrFun hxy 0
    simp [plxd_phi] at h0
    simpa using h0
  have hx : x = 0 := by
    funext i
    fin_cases i
    · exact hx0
    · exact hxV 1 (by norm_num)
    · exact hxV 2 (by norm_num)
  have hbw : plxd_phi (K := K) (f := f) u = b • plxd_phi (K := K) (f := f) u' := by
    rw [← hxy, hx, zero_add]
  have hb0 : b ≠ 0 := by
    intro hb
    exact plxd_phi_not_mem_Vsub hu0 (by rw [hbw, hb, zero_smul]; exact Submodule.zero_mem _)
  have hcoord : ∀ i : Fin 2, u i = sg K f b * u' i := by
    intro i
    fin_cases i
    · have hi := congrFun hbw 1
      change sg K f (u 0) = b * sg K f (u' 0) at hi
      have h2 := congrArg (sg K f) hi
      rw [map_mul, sg_sg hK, sg_sg hK] at h2
      exact h2
    · have hi := congrFun hbw 2
      change sg K f (u 1) = b * sg K f (u' 1) at hi
      have h2 := congrArg (sg K f) hi
      rw [map_mul, sg_sg hK, sg_sg hK] at h2
      exact h2
  have hu : u = sg K f b • u' := by
    funext i
    rw [hcoord i, Pi.smul_apply, smul_eq_mul]
  have hsgb : sg K f b ≠ 0 := fun hb => hb0 ((sg K f).injective (by simpa using hb))
  have hu' : u' = (sg K f b)⁻¹ • u := by
    rw [hu, smul_smul, inv_mul_cancel₀ hsgb, one_smul]
  have hspan : Submodule.span K {u} = Submodule.span K {u'} := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact Submodule.mem_span_singleton.mpr ⟨sg K f b, hu.symm⟩
    · rw [Submodule.span_le]
      intro v hv
      rw [Set.mem_singleton_iff] at hv
      subst hv
      exact Submodule.mem_span_singleton.mpr ⟨(sg K f b)⁻¹, hu'.symm⟩
  rw [hzspan, hz'span, hspan]

theorem exists_z_avoid (hK : Nat.card K = (2 ^ f) ^ 2) (hq : 4 ≤ 2 ^ f)
    (D : Finset (Submodule K (Fin 3 → K))) (hD : D.card ≤ 4) :
    ∃ z : Submodule K (Fin 2 → K), finrank K z = 1 ∧ ∀ d ∈ D, dirZ K f z ≠ d := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  let zOf : K → Submodule K (Fin 2 → K) := fun a => Submodule.span K {![1, a]}
  have hfin : ∀ a : K, finrank K (zOf a) = 1 := by
    intro a
    change finrank K (Submodule.span K {![1, a]}) = 1
    apply finrank_span_singleton
    intro h
    have := congrFun h 0
    simp at this
  have hinj : Function.Injective (fun a : K => dirZ K f (zOf a)) := by
    intro a a' h
    have hzz := dirZ_inj hK (hfin a) (hfin a') h
    have hmem : (![1, a] : Fin 2 → K) ∈ zOf a' := by
      rw [← hzz]
      exact Submodule.mem_span_singleton_self _
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hmem
    have h0 : c = 1 := by
      have := congrFun hc 0
      simpa using this
    have h1 : c * a' = a := by
      have := congrFun hc 1
      simpa using this
    rw [h0, one_mul] at h1
    exact h1.symm
  let bad : Finset K := D.biUnion fun d => Finset.univ.filter (fun a : K => dirZ K f (zOf a) = d)
  have hbad : bad.card ≤ 4 := by
    have h1 : bad.card ≤ D.card * 1 := by
      dsimp only [bad]
      apply Finset.card_biUnion_le_card_mul
      intro d _
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      exact hinj (ha.trans hb.symm)
    omega
  have hcardK : 16 ≤ Nat.card K := by
    rw [hK, pow_two]
    calc 16 = 4 * 4 := by norm_num
      _ ≤ 2 ^ f * 2 ^ f := Nat.mul_le_mul hq hq
  have hlt : bad.card < (Finset.univ : Finset K).card := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    omega
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  refine ⟨zOf a, hfin a, ?_⟩
  intro d hd hEq
  apply ha
  exact Finset.mem_biUnion.mpr ⟨d, hd, Finset.mem_filter.mpr ⟨Finset.mem_univ a, hEq⟩⟩

end Exch

end CFSG.ClassicalInvolution.Phan.PhanE

end
