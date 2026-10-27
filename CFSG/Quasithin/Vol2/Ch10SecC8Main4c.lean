module

public import CFSG.Quasithin.Vol2.Ch10SecC8Data
public import CFSG.Quasithin.Vol2.Ch10SecC8UR

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 SecB.L32 L3F
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem inf_V2_le_fsuCVM (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1) {t : G} (ht : t ∈ T)
    (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    fsuUL T L I ⊓ ⁅fsuVM T L I, CFSG.conjugate L t⁆ ≤ fsuCVM T L I := by
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨-, -, -, hcap⟩ := hdec t ht htn
  intro v hv
  rw [← hcap]
  exact ⟨Subgroup.mem_sup_left hv.1, Subgroup.mem_sup_left hv.2⟩

theorem mem_T1_of_fix (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {v : G}
    (hv : v ∈ ⁅fsuVM T L I, CFSG.conjugate L t⁆)
    (hvC : v ∉ Subgroup.centralizer (fsuL0 T L : Set G)) {s : G} (hs : s ∈ T)
    (hsv : s * v * s⁻¹ = v) : s ∈ T1 T L := by
  refine ⟨hs, ?_⟩
  rcases SecA.conjugate_eq_or h37 h38 hyp ht htn (SecA.le_fsuM T L hs) with h | h
  · exact SecA.conjugate_eq_self_iff.mp h
  · exfalso
    apply hvC
    have hV2s : ⁅fsuVM T L I, CFSG.conjugate L t⁆ = CFSG.conjugate (fsuUL T L I) s := by
      rw [SecA.conjugate_commutator_fsuVM (SecA.le_fsuM T L hs), h]
    have h1 : s * v * s⁻¹ ∈ fsuUL T L I := by
      have hv' := hv
      rw [hV2s] at hv'
      exact SecA.mem_conjugate_iff.mp hv'
    rw [hsv] at h1
    exact (inf_V2_le_fsuCVM hyp h1011 ht htn ⟨h1, hv⟩).2

omit [Finite G] in
theorem mul_conj_eq_of_mem_centralizer {s v : G} (h : s ∈ Subgroup.centralizer ({v} : Set G)) :
    s * v * s⁻¹ = v := by
  rw [← Subgroup.mem_centralizer_iff.mp h v rfl, mul_inv_cancel_right]

omit [Finite G] in
theorem mem_centralizer_of_mul_conj_eq {s v : G} (h : s * v * s⁻¹ = v) :
    s ∈ Subgroup.centralizer ({v} : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  rw [hw]
  calc v * s = s * v * s⁻¹ * s := by rw [h]
    _ = s * v := by group

omit [Finite G] in
theorem coord_eq_e0 {K : Subgroup G} [IsMulCommutative ↥(Vi T L I K)]
    {D : L3Data (autOn K (Vi T L I K)) ⊤
      ((Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (Vi T L I K))}
    (hF : CompFacts T L I K D) {U : Subgroup G} (hU : IsU10_2_8 T L I K U) {v : G} (hvU : v ∈ U)
    (hvC : v ∉ Subgroup.centralizer (fsuL0 T L : Set G)) :
    coordOf D ⟨v, hU.1 hvU⟩ = e0 := by
  obtain ⟨-, hKN, hTK, hD, hact, -⟩ := hF
  rcases (mem_U_iff D hKN hD hTK hact hU (hU.1 hvU)).mp hvU with h | h
  · exact absurd (Subgroup.mem_subgroupOf.mp ((coordOf_eq_zero_iff D _).mp h)) hvC
  · exact h

theorem mem_R_of_fix {K K' : Subgroup G} [IsMulCommutative ↥(Vi T L I K)]
    {D : L3Data (autOn K (Vi T L I K)) ⊤
      ((Subgroup.centralizer (fsuL0 T L : Set G)).subgroupOf (Vi T L I K))}
    (hF : CompFacts T L I K D) (hV : fsuVM T L I = Vi T L I K ⊔ Vi T L I K')
    (hW'K : Vi T L I K' ≤ Subgroup.centralizer (K : Set G)) {U R : Subgroup G}
    (hU : IsU10_2_8 T L I K U) (hR : IsR10_2_8 T L I K U R) {v : G} (hvU : v ∈ U)
    (hvC : v ∉ Subgroup.centralizer (fsuL0 T L : Set G)) {d : G} (hd : d ∈ T ⊓ K)
    (hdv : d * v * d⁻¹ = v) : d ∈ R := by
  have hcv := coord_eq_e0 hF hU hvU hvC
  obtain ⟨hKL0, hKN, hTK, hD, hact, hsq, hfix, hZc, hFF, hE4⟩ := hF
  rw [mem_R_iff D hKN hKL0 hD hTK hact hV hW'K hU hR hd.1]
  refine ⟨d, hd.2, fun w _ => rfl, ?_⟩
  have hdN : d ∈ Subgroup.normalizer (Vi T L I K : Set G) :=
    SecA.le_normalizer_commutator hKN Subgroup.le_normalizer hd.2
  obtain ⟨γ, hγ⟩ := D.π_surj ⟨conjAct (Vi T L I K) ⟨d, hdN⟩,
    SecB.mem_autOn_iff.mpr ⟨⟨d, hdN⟩, hd.2, rfl⟩⟩
  have hγU : IsU γ := by
    rw [← mem_U3, ← hD, hγ]
    exact SecB.mem_autOn_iff.mpr ⟨⟨d, hdN⟩, hd, rfl⟩
  have hγK : IsKa γ := by
    rw [← fixes_iff_ka D hsq hfix hFF hZc hcv γ, hγ]
    exact Subtype.ext hdv
  exact ⟨γ, u_ka γ hγU hγK, hdN, (congrArg Subtype.val hγ).symm⟩

theorem centralizer_v2_eq (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) (h1011 : Stmt10_1_1)
    (h484 : ASInputs.AS_B_4_8_four) (h3 : Case10_1_1Three T L I) (hne : cV1 T L I ≠ ⊥) {t : G}
    (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) {U₂ R₂ : Subgroup G}
    (hU₂ : IsU10_2_8 T L I (CFSG.conjugate L t) U₂)
    (hR₂ : IsR10_2_8 T L I (CFSG.conjugate L t) U₂ R₂) {v : G} (hvU : v ∈ U₂)
    (hvC : v ∉ Subgroup.centralizer (fsuL0 T L : Set G)) :
    T ⊓ Subgroup.centralizer ({v} : Set G) =
      (T ⊓ L) ⊔ R₂ ⊔ (T ⊓ Subgroup.centralizer (fsuVM T L I : Set G)) := by
  obtain ⟨hc1, hc2, D, D₂, hF1, hF2⟩ := exists_comp_data h37 h38 hyp h1011 h484 h3 hne ht htn
  obtain ⟨-, -, hdec, -⟩ := h1011 G T L I hyp
  obtain ⟨hVeq, hV1, hV2, -⟩ := hdec t ht htn
  have hVsup : fsuVM T L I = Vi T L I (CFSG.conjugate L t) ⊔ Vi T L I L := by
    rw [hVeq, sup_comm]
  have hvW : v ∈ Vi T L I (CFSG.conjugate L t) := hU₂.1 hvU
  have hvV : v ∈ fsuVM T L I := commutator_le_left_of_le_normalizer hF2.2.1 hvW
  apply le_antisymm
  · rintro s ⟨hsT, hsv⟩
    have hsv' := mul_conj_eq_of_mem_centralizer hsv
    have hsT1 := mem_T1_of_fix h37 h38 hyp h1011 ht htn hvW hvC hsT hsv'
    obtain ⟨d₁, hd₁, d₂, hd₂, hsd⟩ :=
      exists_decomp_T1 h37 h38 hyp h1011 h3 D hF1.2.2.2.1 ht htn hsT1
    have hd2v : d₂ * v * d₂⁻¹ = v := by
      have h1 := hsd v hvV
      rw [hsv'] at h1
      have h2 : d₂ * v * d₂⁻¹ ∈ Vi T L I (CFSG.conjugate L t) :=
        (Subgroup.mem_normalizer_iff.mp (SecA.le_normalizer_commutator hF2.2.1
          Subgroup.le_normalizer hd₂.2) v).mp hvW
      have h3' : d₁ * (d₂ * v * d₂⁻¹) * d₁⁻¹ = d₂ * v * d₂⁻¹ := by
        rw [Subgroup.mem_centralizer_iff.mp (hV2 h2) d₁ hd₁.2, mul_inv_cancel_right]
      calc d₂ * v * d₂⁻¹ = d₁ * (d₂ * v * d₂⁻¹) * d₁⁻¹ := h3'.symm
        _ = (d₁ * d₂) * v * (d₁ * d₂)⁻¹ := by group
        _ = v := h1.symm
    have hd2R := mem_R_of_fix hF2 hVsup hV1 hU₂ hR₂ hvU hvC hd₂ hd2v
    have hq : (d₁ * d₂)⁻¹ * s ∈ T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) := by
      refine ⟨T.mul_mem (T.inv_mem (T.mul_mem hd₁.1 hd₂.1)) hsT,
        Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have h1 := hsd w hw
      calc w * ((d₁ * d₂)⁻¹ * s) = (d₁ * d₂)⁻¹ * ((d₁ * d₂) * w * (d₁ * d₂)⁻¹) * s := by group
        _ = (d₁ * d₂)⁻¹ * (s * w * s⁻¹) * s := by rw [h1]
        _ = ((d₁ * d₂)⁻¹ * s) * w := by group
    have e : s = d₁ * d₂ * ((d₁ * d₂)⁻¹ * s) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hd₁))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right hd2R))) (Subgroup.mem_sup_right hq)
  · refine sup_le (sup_le ?_ ?_) ?_
    · rintro x ⟨hxT, hxL⟩
      refine ⟨hxT, mem_centralizer_of_mul_conj_eq ?_⟩
      rw [Subgroup.mem_centralizer_iff.mp (hV2 hvW) x hxL, mul_inv_cancel_right]
    · intro x hx
      obtain ⟨hKL0, hKN, hTK, hD, hact, hsq, hfix, hZc, hFF, hE4⟩ := hF2
      have hxT := hR₂.1 hx
      obtain ⟨k, hk, hkx, γ, hγE, hkN, hkγ⟩ :=
        (mem_R_iff D₂ hKN hKL0 hD hTK hact hVsup hV1 hU₂ hR₂ hxT).mp hx
      have hcv := coord_eq_e0 ⟨hKL0, hKN, hTK, hD, hact, hsq, hfix, hZc, hFF, hE4⟩ hU₂ hvU hvC
      have hfixv := π_fix_of_ka D₂ hsq hfix (ea_le γ hγE).1 hcv
      rw [← hkγ] at hfixv
      refine ⟨hxT, mem_centralizer_of_mul_conj_eq ?_⟩
      rw [hkx v hvV]
      exact congrArg Subtype.val hfixv
    · rintro x ⟨hxT, hxV⟩
      refine ⟨hxT, mem_centralizer_of_mul_conj_eq ?_⟩
      rw [← Subgroup.mem_centralizer_iff.mp hxV v hvV, mul_inv_cancel_right]

end CFSG.Quasithin.Vol2.Ch10.SecC
