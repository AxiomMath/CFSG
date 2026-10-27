module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Even6
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListFlag3
public import CFSG.Quasithin.EmptyFaithful.LRed5Models
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FR

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

section Conj

variable {V : Type*} [CommGroup V]

theorem fix_of_conj_ch615 {D : FFModel} {H : Subgroup (MulAut V)} {W : Subgroup V}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H W ⊥ π) (ρ : D.Gam →* MulAut D.Amb)
    (hρ : ∀ γ m, D.act γ m = ρ γ m) (hker : ∀ γ, ∀ k ∈ D.ker, ρ γ k ∈ D.ker)
    (h₀ : D.Gam) {S : Subgroup (MulAut V)} {T₀ R₀ : Subgroup D.Gam}
    (hS : ∀ t ∈ T₀, ((π (h₀ * t * h₀⁻¹) : ↥H) : MulAut V) ∈ S)
    (hR : ∀ m ∈ D.sec, (∀ t ∈ T₀, ρ t m * m⁻¹ ∈ D.ker) → ∀ y ∈ R₀, ρ y m * m⁻¹ ∈ D.ker)
    {w : V} (hwW : w ∈ W) (hw : ∀ s ∈ S, s w = w) :
    ∀ y ∈ R₀, ((π (h₀ * y * h₀⁻¹) : ↥H) : MulAut V) w = w := by
  have hsec : ∀ γ, ∀ m ∈ D.sec, ρ γ m ∈ D.sec := fun γ m hm => by
    rw [← hρ]
    exact h.2.2.2.2.2.1 γ m hm
  set f : D.Gam →* D.Gam := (MulAut.conj h₀).toMonoidHom with hf
  have hfa : ∀ z, f z = h₀ * z * h₀⁻¹ := fun z => by simp [hf, MulAut.conj_apply]
  have hconj : ∀ z m, ρ (h₀ * z * h₀⁻¹) m = ρ h₀ (ρ z (ρ h₀⁻¹ m)) := fun z m => by
    simp only [map_mul, MulAut.mul_apply]
  have hinv : ∀ m, ρ h₀ (ρ h₀⁻¹ m) = m := fun m => by
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  have hinv' : ∀ m, ρ h₀⁻¹ (ρ h₀ m) = m := fun m => by
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  have key := fix_of_realizesVia_ch615 h (S' := T₀.map f) (R' := R₀.map f) ?_ hwW ?_
  · intro y hy
    exact (congrArg (fun γ => ((π γ : ↥H) : MulAut V) w) (hfa y)).symm.trans
      (key _ ⟨y, hy, rfl⟩)
  · intro m hm hmS γ hγ
    obtain ⟨y, hy, rfl⟩ := hγ
    set m' := ρ h₀⁻¹ m with hm'
    have hm'S : ∀ t ∈ T₀, ρ t m' * m'⁻¹ ∈ D.ker := by
      intro t ht
      have h1 := hmS _ ⟨t, ht, rfl⟩
      rw [hρ, hfa, hconj] at h1
      have h2 := hker h₀⁻¹ _ h1
      have e : ρ h₀⁻¹ (ρ h₀ (ρ t m') * m⁻¹) = ρ t m' * m'⁻¹ := by
        rw [(ρ h₀⁻¹).map_mul, (ρ h₀⁻¹).map_inv, hinv']
      rwa [e] at h2
    have h3 := hR m' (hsec _ m hm) hm'S y hy
    rw [hρ, hfa, hconj]
    have h4 := hker h₀ _ h3
    rwa [(ρ h₀).map_mul, (ρ h₀).map_inv, hinv] at h4
  · rintro _ ⟨t, ht, rfl⟩
    exact (congrArg (fun γ => ((π γ : ↥H) : MulAut V) w) (hfa t)).trans (hw _ (hS t ht))

end Conj

section A6Model

open Equiv CFSG.QuasithinUnique.L246C127 CFSG.QuasithinUnique.Vol2Native.A312L.PermLat

theorem mem_zpowers_allOnes_iff_ch615 (x : Perm (Fin 6)) (m : G6.PermMod 6) :
    G6.permAct 6 x m * m⁻¹ ∈ Subgroup.zpowers (G6.allOnes 6) ↔
      (∀ i, Multiplicative.toAdd m (x⁻¹ i) + Multiplicative.toAdd m i = 0) ∨
        ∀ i, Multiplicative.toAdd m (x⁻¹ i) + Multiplicative.toAdd m i = 1 := by
  have key : ∀ i, Multiplicative.toAdd (G6.permAct 6 x m * m⁻¹) i =
      Multiplicative.toAdd m (x⁻¹ i) + Multiplicative.toAdd m i := fun i => by
    rw [toAdd_mul, toAdd_inv, Pi.add_apply, Pi.neg_apply, G6.permAct_apply]
    exact congrArg (Multiplicative.toAdd m (x⁻¹ i) + ·) (ZMod.neg_eq_self_mod_two _)
  rw [B5FinPerm.mem_zpowers_allOnes_iff]
  constructor
  · rintro (h | h)
    · exact Or.inl fun i => by rw [← key, h]; rfl
    · exact Or.inr fun i => by rw [← key, h]; rfl
  · rintro (h | h)
    · exact Or.inl (Multiplicative.toAdd.injective (funext fun i => by rw [key, h]; rfl))
    · exact Or.inr (Multiplicative.toAdd.injective (funext fun i => by rw [key, h]; rfl))

theorem fix_l2_gen_ch615 : ∀ m : Fin 6 → ZMod 2,
    ((∀ i, m ((permOf 6 [[0,1],[4,5]])⁻¹ i) + m i = 0) ∨
      ∀ i, m ((permOf 6 [[0,1],[4,5]])⁻¹ i) + m i = 1) →
    ((∀ i, m ((permOf 6 [[0,2],[1,3]])⁻¹ i) + m i = 0) ∨
      ∀ i, m ((permOf 6 [[0,2],[1,3]])⁻¹ i) + m i = 1) →
    (∀ i, m ((permOf 6 [[1,2],[4,5]])⁻¹ i) + m i = 0) ∨
      ∀ i, m ((permOf 6 [[1,2],[4,5]])⁻¹ i) + m i = 1 := by
  decide

theorem zmod2_add_self_ch615 : ∀ a : ZMod 2, a + a = 0 := by decide

@[expose] def FixMod6_ch615 (v : Fin 6 → ZMod 2) (x : Perm (Fin 6)) : Prop :=
  ∃ c : ZMod 2, ∀ i, v (x⁻¹ i) + v i = c

@[expose] def fixModSub_ch615 (v : Fin 6 → ZMod 2) : Subgroup (Perm (Fin 6)) where
  carrier := {x | FixMod6_ch615 v x}
  one_mem' := ⟨0, fun i => by simpa using zmod2_add_self_ch615 (v i)⟩
  mul_mem' := by
    rintro x y ⟨c₁, h₁⟩ ⟨c₂, h₂⟩
    refine ⟨c₂ + c₁, fun i => ?_⟩
    have e1 := h₂ (x⁻¹ i)
    have e2 := h₁ i
    rw [mul_inv_rev, Perm.mul_apply]
    calc v (y⁻¹ (x⁻¹ i)) + v i = (v (y⁻¹ (x⁻¹ i)) + v (x⁻¹ i)) + (v (x⁻¹ i) + v i) := by
          rw [add_assoc, ← add_assoc (v (x⁻¹ i)), zmod2_add_self_ch615, zero_add]
      _ = c₂ + c₁ := by rw [e1, e2]
  inv_mem' := by
    rintro x ⟨c, h⟩
    refine ⟨c, fun i => ?_⟩
    have := h (x i)
    have e : x⁻¹ (x i) = i := by simp
    rw [e, add_comm] at this
    rw [inv_inv]
    exact this

theorem mem_zpowers_iff_fixMod_ch615 (x : Perm (Fin 6)) (m : G6.PermMod 6) :
    G6.permAct 6 x m * m⁻¹ ∈ Subgroup.zpowers (G6.allOnes 6) ↔
      FixMod6_ch615 (Multiplicative.toAdd m) x := by
  rw [mem_zpowers_allOnes_iff_ch615]
  constructor
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  · rintro ⟨c, h⟩
    rcases CFSG.QuasithinUnique.Vol2Native.A312L.eq_zero_or_eq_one_of_card_two (Nat.card_zmod 2) c
      with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h

theorem fix_closure_l2_ch615 {v : Fin 6 → ZMod 2} (hT : ∀ t ∈ Even6.D, FixMod6_ch615 v t) :
    Subgroup.closure {g | g ∈ Even6.L2} ≤ fixModSub_ch615 v := by
  have h1 : permOf 6 [[0,1],[4,5]] ∈ Even6.D := Subgroup.subset_closure (by simp [Even6.tGens])
  have h2 : permOf 6 [[0,2],[1,3]] ∈ Even6.D := Subgroup.subset_closure (by simp [Even6.tGens])
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_ofPred_eq, Even6.L2, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact hT _ h1
  · exact hT _ h2
  · obtain ⟨c₁, hc₁⟩ := hT _ h1
    obtain ⟨c₂, hc₂⟩ := hT _ h2
    have := fix_l2_gen_ch615 v
    rcases CFSG.QuasithinUnique.Vol2Native.A312L.eq_zero_or_eq_one_of_card_two (Nat.card_zmod 2)
      c₁ with rfl | rfl <;>
    rcases CFSG.QuasithinUnique.Vol2Native.A312L.eq_zero_or_eq_one_of_card_two (Nat.card_zmod 2)
      c₂ with rfl | rfl <;>
    · rcases this (by tauto) (by tauto) with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩

theorem overgroup_cases_a6_ch615 {Y : Subgroup (Perm (Fin 6))} (hDY : Even6.D ≤ Y)
    (hYA : Y ≤ alternatingGroup (Fin 6)) (hYs : Group.IsSolvable ↥Y) (hYD : Y ≠ Even6.D) :
    Y = Subgroup.closure {g | g ∈ Even6.L1} ∨ Y = Subgroup.closure {g | g ∈ Even6.L2} := by
  have hYM : Y ≤ Subgroup.closure {g | g ∈ Even6.cert.mGens} := by
    rw [show Even6.cert.mGens = Even6.mGens from rfl, Even6.closure_mGens]
    exact hYA
  obtain ⟨Lj, hLj, hYL⟩ := Even6.cert.overgroups (rawIsEnc 6) Even6.cert_check Y hDY hYM
  have hl : Even6.cert.tGens :: Even6.cert.lat = [Even6.tGens, Even6.L1, Even6.L2, Even6.L3] := rfl
  rw [hl] at hLj
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hLj
  rcases hLj with rfl | rfl | rfl | rfl
  · exact absurd hYL hYD
  · exact Or.inl hYL
  · exact Or.inr hYL
  · exfalso
    have hcl := Even6.cert.closedOK_of_check Even6.cert_check
    have hsz := Even6.cert.sizesOK_of_check Even6.cert_check
    have hc3 := Even6.cert.card_member_idx (rawIsEnc 6) hcl hsz 3 (by rw [hl]; simp)
    have hL3 : (Even6.cert.tGens :: Even6.cert.lat)[3]'(by rw [hl]; simp) = Even6.L3 := by
      simp [hl]
    rw [hL3] at hc3
    have hcard : Nat.card ↥Y = 360 := by
      rw [hYL, hc3]
      rfl
    have hYA6 : Y = alternatingGroup (Fin 6) :=
      Subgroup.eq_of_le_of_card_ge hYA (by rw [hcard, Even6.card_alt])
    rw [hYA6] at hYs
    exact not_isSolvable_alt_six_ch615 hYs

end A6Model

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

open Equiv CFSG.QuasithinUnique.L246C127

theorem false_of_case1_alt_six_nofix_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H))
    (hN : ¬ borelL T L ≤ Subgroup.normalizer ((kStar615 T L H : Subgroup G) : Set G))
    (h1 : B56Case1 (ffJ (autI hU (borelL T L ⊔ H))))
    (e : ↥(quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) ≃* ↥(alternatingGroup (Fin 6)))
    (hfix : fixV (quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H)))) = ⊥) : False := by
  classical
  set F := quasithinGenFitting (ffJ (autI hU (borelL T L ⊔ H))) with hFdef
  have hs : IsSimpleGroup ↥F := by
    have := isSimpleGroup_alt_six_ch615
    exact e.isSimpleGroup
  have hdl := dLemmaFacts_alt_six_ch615 e
  have hZ := center_of_isSimpleGroup_ch615 hs hdl.1
  have hFX : F ≤ autI hU (borelL T L ⊔ H) := (quasithinGenFitting_le _).trans (B6.ffJ_le _)
  have hXF := le_normalizer_genFitting_ch615 hU
  have hKF := c.autI_oTwoUpper_le_genFitting_ch615 hU hdl.2.1
  have hS := c.isSylowTwoOf_genFitting_ch615 hU
  have h360 : Nat.card ↥F = 360 := by rw [Nat.card_congr e.toEquiv, card_alt_six_ch615]
  have htr : ∀ w : IntMod (UX615 T L H) hU, (∀ s ∈ autI hU T ⊓ F, s w = w) → w ∈ commV F :=
    fun w hw => by
      have := mem_commV_sup_fixV_ch615 IntMod.sq_eq_one hS.2.2 hw
      rwa [hfix, sup_bot_eq] at this
  rcases LRed5.b51_cases (Or.inr h360) h1.2.1.1 with ⟨h168, -⟩ | ⟨-, π, hπ⟩
  · omega
  rw [hfix, bot_inf_eq] at hπ
  have hinj := FFC.injective_of_faithful_sec (FFC.altDn_faithful (by norm_num)) hπ
  set ψ : ↥(alternatingGroup (Fin 6)) ≃* ↥F := MulEquiv.ofBijective π ⟨hinj, hπ.1⟩ with hψ
  obtain ⟨h₀, -, hh₀⟩ := Even6.isSylow_D.exists_conj (isSylowTwoOf_map_ch615 ψ.symm hS)
  set D' := Even6.D.subgroupOf (alternatingGroup (Fin 6)) with hD'
  set φ : ↥(alternatingGroup (Fin 6)) ≃* ↥F := (MulAut.conj h₀).trans ψ with hφ
  have hφa : ∀ y, φ y = π (h₀ * y * h₀⁻¹) := fun _ => rfl
  have hg : ∀ t ∈ D', ((π (h₀ * t * h₀⁻¹) : ↥F) : MulAut (IntMod (UX615 T L H) hU)) ∈
      autI hU T ⊓ F := by
    intro t ht
    have h2 : h₀ * t * h₀⁻¹ ∈ (((autI hU T ⊓ F).subgroupOf F).map ψ.symm.toMonoidHom) := by
      rw [hh₀]
      exact ⟨t, ht, by simp [MulAut.conj_apply]⟩
    obtain ⟨s', hs', hs'e⟩ := h2
    have : π (h₀ * t * h₀⁻¹) = s' := by
      rw [← hs'e]
      exact ψ.apply_symm_apply s'
    rw [this]
    exact Subgroup.mem_subgroupOf.mp hs'
  set img : Subgroup (MulAut (IntMod (UX615 T L H) hU)) → Subgroup (Perm (Fin 6)) := fun R =>
    ((R.subgroupOf F).map φ.symm.toMonoidHom).map (alternatingGroup (Fin 6)).subtype with himgdef
  have hcard_img : ∀ R : Subgroup (MulAut (IntMod (UX615 T L H) hU)), R ≤ F →
      Nat.card ↥(img R) = Nat.card ↥R := fun R hRF => by
    rw [himgdef, Subgroup.card_map_of_injective (alternatingGroup (Fin 6)).subtype_injective,
      Subgroup.card_map_of_injective φ.symm.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRF).toEquiv]
  have hmem_img : ∀ R : Subgroup (MulAut (IntMod (UX615 T L H) hU)),
      ∀ y : ↥(alternatingGroup (Fin 6)),
      ((φ y : ↥F) : MulAut (IntMod (UX615 T L H) hU)) ∈ R → (y : Perm (Fin 6)) ∈ img R := by
    intro R y hy
    exact ⟨y, ⟨φ y, Subgroup.mem_subgroupOf.mpr hy, by simp⟩, rfl⟩
  have hDimg : ∀ R : Subgroup (MulAut (IntMod (UX615 T L H) hU)), autI hU T ⊓ F ≤ R →
      Even6.D ≤ img R := by
    intro R hSR d hd
    have hdA := Even6.D_le hd
    refine hmem_img R ⟨d, hdA⟩ (hSR ?_)
    rw [hφa]
    exact hg _ (Subgroup.mem_subgroupOf.mpr hd)
  have hSD : Nat.card ↥(autI hU T ⊓ F) = Nat.card ↥Even6.D := by
    have h1 := hcard_img (autI hU T ⊓ F) inf_le_right
    have h2 : img (autI hU T ⊓ F) = Even6.D := by
      refine le_antisymm ?_ (hDimg _ le_rfl)
      rintro _ ⟨y, ⟨s, hs, hse⟩, rfl⟩
      have hsF := Subgroup.mem_subgroupOf.mp hs
      have hy : φ y = s := by rw [← hse]; simp
      have hy' : h₀ * y * h₀⁻¹ ∈ D'.map (MulAut.conj h₀).toMonoidHom := by
        rw [← hh₀]
        refine ⟨s, hs, ?_⟩
        rw [← hy, hφa]
        exact ψ.symm_apply_apply _
      obtain ⟨t, ht, hte⟩ := hy'
      have : y = t := by
        have := congrArg (fun z => h₀⁻¹ * z * h₀) hte
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
        have e1 : h₀⁻¹ * (h₀ * t * h₀⁻¹) * h₀ = t := by group
        have e2 : h₀⁻¹ * (h₀ * y * h₀⁻¹) * h₀ = y := by group
        rw [e1, e2] at this
        exact this.symm
      rw [this]
      exact Subgroup.mem_subgroupOf.mp ht
    rw [← h1, h2]
  have hcases : ∀ R : Subgroup (MulAut (IntMod (UX615 T L H) hU)), autI hU T ⊓ F ≤ R → R ≤ F →
      R ≠ autI hU T ⊓ F → Group.IsSolvable ↥R →
      img R = Subgroup.closure {g | g ∈ Even6.L1} ∨
        img R = Subgroup.closure {g | g ∈ Even6.L2} := by
    intro R hSR hRF hRS hRs
    refine overgroup_cases_a6_ch615 (hDimg R hSR) (Subgroup.map_le_iff_le_comap.mpr
      fun y _ => y.2) ?_ fun hD => hRS ?_
    · have := isSolvable_map_ch615 φ.symm hRF hRs
      exact Group.isSolvable_of_surjective
        ((alternatingGroup (Fin 6)).subtype.subgroupMap_surjective _)
    · refine (Subgroup.eq_of_le_of_card_ge hSR ?_).symm
      rw [← hcard_img R hRF, hD, hSD]
  have hinj_img : ∀ R₁ R₂ : Subgroup (MulAut (IntMod (UX615 T L H) hU)), R₁ ≤ F → R₂ ≤ F →
      img R₁ = img R₂ → R₁ = R₂ := by
    intro R₁ R₂ h₁ h₂ heq
    have h3 := Subgroup.map_injective (alternatingGroup (Fin 6)).subtype_injective heq
    have h4 := Subgroup.map_injective φ.symm.injective h3
    rwa [Subgroup.subgroupOf_inj, inf_eq_left.mpr h₁, inf_eq_left.mpr h₂] at h4
  set ρ6 : ↥(alternatingGroup (Fin 6)) →* MulAut (G6.PermMod 6) :=
    (G6.permAct 6).comp (alternatingGroup (Fin 6)).subtype with hρ6
  have hker : ∀ γ : ↥(alternatingGroup (Fin 6)), ∀ k ∈ (FFModel.altDn 6).ker,
      ρ6 γ k ∈ (FFModel.altDn 6).ker := by
    rintro γ k ⟨⟨j, rfl⟩, hk⟩
    refine ⟨⟨j, ?_⟩, G6.permAct_mem_coreMod _ hk⟩
    simp only [hρ6, MonoidHom.coe_comp, Function.comp_apply]
    rfl
  have hfixR : ∀ R : Subgroup (MulAut (IntMod (UX615 T L H) hU)), R ≤ F →
      img R = Subgroup.closure {g | g ∈ Even6.L2} →
      ∀ w : IntMod (UX615 T L H) hU, (∀ s ∈ autI hU T ⊓ F, s w = w) → ∀ x ∈ R, x w = w := by
    intro R hRF hR w hw x hx
    have key := fix_of_conj_ch615 hπ ρ6 (fun _ _ => rfl) hker h₀ (T₀ := D')
      (R₀ := (R.subgroupOf F).map φ.symm.toMonoidHom) hg ?_ (htr w hw) hw
    · have hy : φ.symm ⟨x, hRF hx⟩ ∈ (R.subgroupOf F).map φ.symm.toMonoidHom :=
        ⟨⟨x, hRF hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
      have e2 : φ (φ.symm ⟨x, hRF hx⟩) = ⟨x, hRF hx⟩ := φ.apply_symm_apply _
      calc x w = ((φ (φ.symm ⟨x, hRF hx⟩) : ↥F) : MulAut (IntMod (UX615 T L H) hU)) w := by
            rw [e2]
        _ = w := key _ hy
    · intro m hm hmT y hy
      have hT' : ∀ t ∈ Even6.D, FixMod6_ch615 (Multiplicative.toAdd m) t := by
        intro t ht
        exact (mem_zpowers_iff_fixMod_ch615 _ m).mp
          (hmT ⟨t, Even6.D_le ht⟩ (Subgroup.mem_subgroupOf.mpr ht)).1
      have hyL2 : (alternatingGroup (Fin 6)).subtype y ∈
          Subgroup.closure {g | g ∈ Even6.L2} := by
        rw [← hR]
        exact ⟨y, hy, rfl⟩
      refine ⟨(mem_zpowers_iff_fixMod_ch615 _ m).mpr (fix_closure_l2_ch615 hT' hyL2), ?_⟩
      exact Subgroup.mul_mem _ (G6.permAct_mem_coreMod _ hm) (Subgroup.inv_mem _ hm)
  refine c.false_of_two_overgroups_ch615 hU hN hFX hXF hdl hZ hKF
    fun R₁ R₂ h1S h1F h1ne h1s h2S h2F h2ne h2s hne => ?_
  rcases hcases R₁ h1S h1F h1ne h1s with ha | ha <;>
    rcases hcases R₂ h2S h2F h2ne h2s with hb | hb
  · exact absurd (hinj_img _ _ h1F h2F (ha.trans hb.symm)) hne
  · exact Or.inr (hfixR R₂ h2F hb)
  · exact Or.inl (hfixR R₁ h1F ha)
  · exact absurd (hinj_img _ _ h1F h2F (ha.trans hb.symm)) hne

end Cx615C

end CFSG.Quasithin.H13
