module

public import CFSG.Quasithin.Vol2.Ch10SecEE3C
public import CFSG.Quasithin.Vol2.Ch10SecFX

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem pCoreOf_L0T_eq_inf
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (hyp : Hyp10 G T L I)
    (h12 : (∃ n, Ch10.Case10_1_1One T L I n) ∨ Ch10.Case10_1_1Two T L I) :
    pCoreOf 2 (fsuL0 T L ⊔ T) = T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) := by
  rw [(h3228 G T L I hyp.fsu).2.2, SecA.fsuV_eq_of_cases12 h37 h38 hyp h12]

theorem exists_mul_of_mem_inf_centralizer (h113 : ASInputs.AS_C_1_13)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    (hb : IsShort2 L ∧ IsAltType L 5) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) {x : G}
    (hx : x ∈ T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) :
    ∃ v ∈ fsuVM T L I, ∃ c ∈ T ⊓ Subgroup.centralizer (fsuL0 T L : Set G), x = v * c := by
  have hOeq := pCoreOf_L0T_eq_inf h37 h38 h3228 hyp (Or.inr h2)
  have hO : x ∈ pCoreOf 2 (fsuL0 T L ⊔ T) := hOeq ▸ hx
  have hTN : T ≤ Subgroup.normalizer (pCoreOf 2 (fsuL0 T L ⊔ T) : Set G) :=
    le_sup_right.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hO' : t * x * t⁻¹ ∈ pCoreOf 2 (fsuL0 T L ⊔ T) :=
    (Subgroup.mem_normalizer_iff.mp (hTN ht) x).mp hO
  obtain ⟨u, hu, c, hc, hxu⟩ :=
    SecE.exists_mul_of_mem_pCoreOf h113 hyp h2 hb (SecE.pCoreOf_L0T_le_pCoreOf hyp hO)
  obtain ⟨u', hu', c', hc', hxu'⟩ :=
    SecE.exists_mul_of_mem_pCoreOf h113 hyp h2 hb (SecE.pCoreOf_L0T_le_pCoreOf hyp hO')
  set u₂ := t⁻¹ * u' * t with hu₂def
  set c₂ := t⁻¹ * c' * t with hc₂def
  have hxu₂ : x = u₂ * c₂ := by
    have : x = t⁻¹ * (t * x * t⁻¹) * t := by group
    rw [this, hxu', hu₂def, hc₂def]
    group
  have hu₂ : u₂ ∈ CFSG.conjugate (fsuUL T L I) t := by
    rw [mem_conjugate_iff']
    simpa [hu₂def, mul_assoc] using hu'
  have hc₂ : c₂ ∈ Subgroup.centralizer (CFSG.conjugate L t : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' := mem_conjugate_iff'.mp hl
    have h1 := Subgroup.mem_centralizer_iff.mp hc'.2 _ hl'
    calc l * c₂ = t⁻¹ * ((t * l * t⁻¹) * c') * t := by rw [hc₂def]; group
      _ = t⁻¹ * (c' * (t * l * t⁻¹)) * t := by rw [h1]
      _ = c₂ * l := by rw [hc₂def]; group
  have hVL : fsuUL T L I ≤ fsuVM T L I := SecA.fsuUL_le_fsuVM T L I
  have hV₂ : CFSG.conjugate (fsuUL T L I) t ≤ fsuVM T L I :=
    SecA.conjugate_fsuUL_le (SecA.le_fsuM T L ht)
  have hcomm : u * u₂ = u₂ * u := SecA.comm_of_mem_fsuVM hyp (hVL hu) (hV₂ hu₂)
  obtain ⟨_, -, -, ha, -⟩ := hyp.three
  have hu₁C : u ∈ Subgroup.centralizer (CFSG.conjugate L t : Set G) := (ha t ht htn).2.2 hu
  have hu₂C : u₂ ∈ Subgroup.centralizer (L : Set G) :=
    SecA.conjugate_fsuUL_le_centralizer h37 h38 hyp ht htn hu₂
  refine ⟨u * u₂, (fsuVM T L I).mul_mem (hVL hu) (hV₂ hu₂), u₂⁻¹ * c, ⟨?_, ?_⟩, ?_⟩
  · exact T.mul_mem (T.inv_mem (SecA.fsuVM_le_T hyp (hV₂ hu₂))) hc.1.1
  · have hdL : u₂⁻¹ * c ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hu₂C) hc.2
    have hd : u₂⁻¹ * c = u⁻¹ * c₂ := by
      have h1 : u * c = u₂ * c₂ := hxu.symm.trans hxu₂
      calc u₂⁻¹ * c = u₂⁻¹ * (u⁻¹ * (u * c)) := by group
        _ = u₂⁻¹ * (u⁻¹ * (u₂ * c₂)) := by rw [h1]
        _ = u₂⁻¹ * (u⁻¹ * u₂) * c₂ := by group
        _ = u₂⁻¹ * (u₂ * u⁻¹) * c₂ := by
          rw [show u⁻¹ * u₂ = u₂ * u⁻¹ by
            calc u⁻¹ * u₂ = u⁻¹ * (u₂ * u) * u⁻¹ := by group
              _ = u⁻¹ * (u * u₂) * u⁻¹ := by rw [hcomm]
              _ = u₂ * u⁻¹ := by group]
        _ = u⁻¹ * c₂ := by group
    have hdLt : u₂⁻¹ * c ∈ Subgroup.centralizer (CFSG.conjugate L t : Set G) :=
      hd ▸ Subgroup.mul_mem _ (Subgroup.inv_mem _ hu₁C) hc₂
    show u₂⁻¹ * c ∈ Subgroup.centralizer (fsuL0 T L : Set G)
    rw [SecA.fsuL0_eq_sup h37 h38 hyp ht htn, Subgroup.mem_centralizer_iff]
    intro y hy
    have hle : L ⊔ CFSG.conjugate L t ≤ Subgroup.centralizer ({u₂⁻¹ * c} : Set G) := by
      refine sup_le (fun l hl => ?_) (fun l hl => ?_)
      · rw [Subgroup.mem_centralizer_iff]
        rintro _ rfl
        exact (Subgroup.mem_centralizer_iff.mp hdL l hl).symm
      · rw [Subgroup.mem_centralizer_iff]
        rintro _ rfl
        exact (Subgroup.mem_centralizer_iff.mp hdLt l hl).symm
    exact (Subgroup.mem_centralizer_iff.mp (hle hy) _ rfl).symm
  · rw [hxu]
    group

theorem eq_of_mul_eq_mul (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I) {v v' c c' : G}
    (hv : v ∈ fsuVM T L I) (hv' : v' ∈ fsuVM T L I)
    (hc : c ∈ Subgroup.centralizer (fsuL0 T L : Set G))
    (hc' : c' ∈ Subgroup.centralizer (fsuL0 T L : Set G)) (h : v * c = v' * c') : v = v' := by
  have h1 : v'⁻¹ * v = c' * c⁻¹ := by
    calc v'⁻¹ * v = v'⁻¹ * (v * c) * c⁻¹ := by group
      _ = v'⁻¹ * (v' * c') * c⁻¹ := by rw [h]
      _ = c' * c⁻¹ := by group
  have hmem : v'⁻¹ * v ∈ fsuCVM T L I :=
    ⟨(fsuVM T L I).mul_mem ((fsuVM T L I).inv_mem hv') hv,
      h1 ▸ Subgroup.mul_mem _ hc' (Subgroup.inv_mem _ hc)⟩
  rw [fsuCVM_eq_bot_case2 h37 h38 hyp h2] at hmem
  have : v'⁻¹ * v = 1 := hmem
  calc v = v' * (v'⁻¹ * v) := by group
    _ = v' := by rw [this, mul_one]

omit [Finite G] in
theorem omegaOneCenterOf_le_centerOf (X : Subgroup G) :
    omegaOneCenterOf X ≤ X ⊓ Subgroup.centralizer (X : Set G) :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

theorem exists_mul_of_mem_omegaOneCenterOf (h113 : ASInputs.AS_C_1_13)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h3228 : Ch10.TmpL6_3_2_2_eight) (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I)
    (hb : IsShort2 L ∧ IsAltType L 5) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) (hVS : fsuVM T L I ≤ baum T) {e : G}
    (he : e ∈ omegaOneCenterOf (baum T)) :
    ∃ v ∈ fsuVM T L I, ∃ c ∈ T ⊓ Subgroup.centralizer (fsuL0 T L : Set G), e = v * c ∧
      v ∈ Subgroup.centralizer (baum T : Set G) := by
  have he' := omegaOneCenterOf_le_centerOf (baum T) he
  have heT : e ∈ T := he'.1.1
  have heV : e ∈ Subgroup.centralizer (fsuVM T L I : Set G) := Subgroup.centralizer_le hVS he'.2
  obtain ⟨v, hv, c, hc, rfl⟩ :=
    exists_mul_of_mem_inf_centralizer h113 h37 h38 h3228 hyp h2 hb ht htn ⟨heT, heV⟩
  refine ⟨v, hv, c, hc, rfl, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hsT : s ∈ T := hs.1
  have hsc := Subgroup.mem_centralizer_iff.mp he'.2 s hs
  have hv' : s * v * s⁻¹ ∈ fsuVM T L I :=
    (Subgroup.mem_normalizer_iff.mp (SecA.le_normalizer_fsuVM T L I hsT) v).mp hv
  have hc' : s * c * s⁻¹ ∈ Subgroup.centralizer (fsuL0 T L : Set G) :=
    (Subgroup.mem_normalizer_iff.mp (SecA.le_normalizer_centralizer le_rfl
      (SecA.le_fsuM T L hsT)) c).mp hc.2
  have heq : (s * v * s⁻¹) * (s * c * s⁻¹) = v * c := by
    calc (s * v * s⁻¹) * (s * c * s⁻¹) = s * (v * c) * s⁻¹ := by group
      _ = (v * c) * s * s⁻¹ := by rw [hsc]
      _ = v * c := by group
  have h1 := eq_of_mul_eq_mul h37 h38 hyp h2 hv' hv hc' hc.2 heq
  calc s * v = (s * v * s⁻¹) * s := by group
    _ = v * s := by rw [h1]

end CFSG.Quasithin.Vol2.Ch10.SecF
