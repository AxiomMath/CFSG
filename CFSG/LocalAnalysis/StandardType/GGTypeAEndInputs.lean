module

public import CFSG.LocalAnalysis.StandardType.GGTypeAEndInputsUnique

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal.SpecialLinear Matrix

@[expose] def GGTypeACompatFarExInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeASplitNbr p B Bs x L D J n f y K →
    ∃ φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₁.range = L ∧
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      φ₂.range = K ∧
      φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J ∧
      φ₁.comp (slLowerBlockHom n (GaloisField 2 f)) =
        φ₂.comp (slUpperBlockHom n (GaloisField 2 f)) ∧
      ∀ i j : Fin n, i.val = 0 → j.val + 1 = n →
        Commute (φ₂ (weylRep n (GaloisField 2 f) j)) (φ₁ (weylRep n (GaloisField 2 f) i))

theorem ggTypeAEndBlockLExInput_of_compatFarEx (h : GGTypeACompatFarExInput) :
    GGTypeAEndBlockLExInput := by
  intro G _ _ p B Bs x L D J n f y K hN
  obtain ⟨φ₁, -, hφ₁, hk₁, -, -, hJ, -, -⟩ := h G p B Bs x L D J n f y K hN
  exact ⟨φ₁, hφ₁, hk₁, hJ⟩

theorem ggTypeAEndBlockKInput_of_compatFarEx (h : GGTypeACompatFarExInput) :
    GGTypeAEndBlockKInput := by
  intro G _ _ p B Bs x L D J n f y K hN
  obtain ⟨φ₁, φ₂, -, -, hφ₂, hk₂, hJ, hc, -⟩ := h G p B Bs x L D J n f y K hN
  exact ⟨φ₂, hφ₂, hk₂, by rw [← hc]; exact hJ⟩

@[expose] def GGTypeAFarCommuteSomeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeASplitNbr p B Bs x L D J n f y K →
    ∀ ψ₁ ψ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, ψ₁.range = L →
      ψ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) →
      ψ₂.range = K →
      ψ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) →
      (ψ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J →
      ψ₁.comp (slLowerBlockHom n (GaloisField 2 f)) =
        ψ₂.comp (slUpperBlockHom n (GaloisField 2 f)) →
      ∃ φ₁ φ₂ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₁.range = L ∧
        φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
        φ₂.range = K ∧
        φ₂.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
        (φ₁.comp (slLowerBlockHom n (GaloisField 2 f))).range = J ∧
        φ₁.comp (slLowerBlockHom n (GaloisField 2 f)) =
          φ₂.comp (slUpperBlockHom n (GaloisField 2 f)) ∧
        ∀ i j : Fin n, i.val = 0 → j.val + 1 = n →
          Commute (φ₂ (weylRep n (GaloisField 2 f) j)) (φ₁ (weylRep n (GaloisField 2 f) i))

theorem ggTypeAFarCommuteSomeInput_of_compatFarEx (h : GGTypeACompatFarExInput) :
    GGTypeAFarCommuteSomeInput := fun G _ _ p B Bs x L D J n f y K hN _ _ _ _ _ _ _ _ =>
  h G p B Bs x L D J n f y K hN

theorem ggTypeAFarCommuteInput_of_some (h : GGTypeAFarCommuteSomeInput) :
    GGTypeAFarCommuteInput := by
  intro G _ _ p B Bs x L D J n f y K hN ψ₁ ψ₂ hψL hl₁ hψK hl₂ hψJ hc' i j hi hj
  obtain ⟨-, -, -, -, hmod, -, hn, -⟩ := id hN
  have hf : 1 ≤ f := hmod.1.2.1
  have h2 : (2 : GaloisField 2 f) = 0 :=
    two_eq_zero_of_card (GaloisField.card 2 f (by omega)) hf
  obtain ⟨φ₁, φ₂, hφL, hk₁, hφK, hk₂, hφJ, hc, hfar⟩ :=
    h G p B Bs x L D J n f y K hN ψ₁ ψ₂ hψL hl₁ hψK hl₂ hψJ hc'
  have h0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have h1 : n - 1 < n := Nat.sub_lt h0 Nat.one_pos
  rw [show i = ⟨0, h0⟩ from Fin.ext hi, show j = ⟨n - 1, h1⟩ from Fin.ext (by simp only; omega)]
  exact slCompat_far_of_far h2 hn hk₁ hk₂ hl₁ hl₂ (hφL.trans hψL.symm) (hφK.trans hψK.symm) hc hc'
    (hψJ.trans hφJ.symm) (hfar _ _ rfl (by simp only; omega))

theorem ggTypeAFarCommuteInput_of_compatFarEx (h : GGTypeACompatFarExInput) :
    GGTypeAFarCommuteInput :=
  ggTypeAFarCommuteInput_of_some (ggTypeAFarCommuteSomeInput_of_compatFarEx h)

theorem ggTypeAEndNodeInput_of_compatFarEx (h : GGTypeACompatFarExInput)
    (hD : GGTypeAJoinInput) : GGTypeAEndNodeInput :=
  ggTypeAEndNodeInput_of_inputs' (ggTypeAEndBlockLExInput_of_compatFarEx h)
    (ggTypeAEndBlockKInput_of_compatFarEx h) (ggTypeAFarCommuteInput_of_compatFarEx h) hD

theorem ggTypeACompatFarExInput_of_inputs (hA : GGTypeAEndBlockLExInput)
    (hB : GGTypeAEndBlockKInput) (hC : GGTypeAFarCommuteInput) : GGTypeACompatFarExInput := by
  intro G _ _ p B Bs x L D J n f y K hN
  obtain ⟨-, -, -, -, -, -, hn, -⟩ := id hN
  obtain ⟨φ₁, hφL, hk₁, hJ₁⟩ := hA G p B Bs x L D J n f y K hN
  obtain ⟨φ₂₀, hφK, hk₂, hJ₂⟩ := hB G p B Bs x L D J n f y K hN
  obtain ⟨φ₂, hφK', hk₂', hc⟩ := exists_slCompat_lift hn hk₁ hk₂ (hJ₁.trans hJ₂.symm)
  rw [hφK] at hφK'
  exact ⟨φ₁, φ₂, hφL, hk₁, hφK', hk₂', hJ₁, hc,
    hC G p B Bs x L D J n f y K hN φ₁ φ₂ hφL hk₁ hφK' hk₂' hJ₁ hc⟩

section Model

variable {F : Type} [Field F]

theorem slUpperBlockHom_comp_slLowerBlockHom (n : ℕ) :
    (slUpperBlockHom (n + 1) F).comp (slLowerBlockHom n F) =
      (slLowerBlockHom (n + 1) F).comp (slUpperBlockHom n F) := by
  refine MonoidHom.eq_of_eqOn_dense
    (SpecialLinearGroup.closure_range_toSpecialLinearGroup_eq_top_of_field (ι := Fin n) (K := F))
    ?_
  rintro _ ⟨⟨a, b, hab, c⟩, rfl⟩
  simp only [TransvectionStruct.toSpecialLinearGroup_mk, MonoidHom.comp_apply,
    slLowerBlockHom_transvection, slUpperBlockHom_transvection]

theorem commute_slUpperBlockHom_weylRep_slLowerBlockHom_weylRep {n : ℕ} (hn : 2 ≤ n) :
    Commute (slUpperBlockHom (n + 1) F (weylRep n F ⟨0, by omega⟩))
      (slLowerBlockHom (n + 1) F (weylRep n F ⟨n - 1, by omega⟩)) := by
  have key : ∀ {i j k l : Fin (n + 1 + 1)} (hij : i ≠ j) (hkl : k ≠ l), i.val < 2 → j.val < 2 →
      n ≤ k.val → n ≤ l.val → ∀ c d : F,
        Commute (SpecialLinearGroup.transvection hij c) (SpecialLinearGroup.transvection hkl d) :=
    fun hij hkl hi hj hk hl c d => commute_transvection_of_ne hij hkl
      (Fin.ne_of_val_ne (by omega)) (Fin.ne_of_val_ne (by omega)) c d
  simp only [weylRep, map_mul, slUpperBlockHom_transvection, slLowerBlockHom_transvection]
  refine Commute.mul_left (Commute.mul_left ?_ ?_) ?_ <;>
    refine Commute.mul_right (Commute.mul_right ?_ ?_) ?_ <;>
    exact key _ _ (by simp) (by simp) (by simp; omega) (by simp; omega) _ _

end Model

@[expose] def GGTypeAModelInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeASplitNbr p B Bs x L D J n f y K →
    ∃ π : SpecialLinearGroup (Fin (n + 1 + 1)) (GaloisField 2 f) →* G,
      π.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1 + 1)) (GaloisField 2 f)) ∧
      (π.comp (slUpperBlockHom (n + 1) (GaloisField 2 f))).range = L ∧
      (π.comp (slLowerBlockHom (n + 1) (GaloisField 2 f))).range = K ∧
      ((π.comp (slUpperBlockHom (n + 1) (GaloisField 2 f))).comp
        (slLowerBlockHom n (GaloisField 2 f))).range = J

theorem ggTypeACompatFarExInput_of_model (h : GGTypeAModelInput) : GGTypeACompatFarExInput := by
  intro G _ _ p B Bs x L D J n f y K hN
  obtain ⟨-, -, -, -, -, -, hn, -⟩ := id hN
  obtain ⟨π, hπ, hL, hK, hJ⟩ := h G p B Bs x L D J n f y K hN
  refine ⟨π.comp (slUpperBlockHom (n + 1) _), π.comp (slLowerBlockHom (n + 1) _), hL, ?_, hK, ?_,
    hJ, ?_, ?_⟩
  · intro g hg
    rw [eq_one_of_slUpperBlockHom_mem_center (hπ (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hg)))]
    exact Subgroup.one_mem _
  · intro g hg
    rw [eq_one_of_slLowerBlockHom_mem_center (hπ (MonoidHom.mem_ker.mpr (MonoidHom.mem_ker.mp hg)))]
    exact Subgroup.one_mem _
  · rw [MonoidHom.comp_assoc, MonoidHom.comp_assoc, slUpperBlockHom_comp_slLowerBlockHom]
  · intro i j hi hj
    have h0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
    have h1 : n - 1 < n := Nat.sub_lt h0 Nat.one_pos
    rw [show i = ⟨0, h0⟩ from Fin.ext hi, show j = ⟨n - 1, h1⟩ from Fin.ext (by simp only; omega)]
    exact ((commute_slUpperBlockHom_weylRep_slLowerBlockHom_weylRep (by omega)).map π).symm

@[expose] def GGTypeAJoinAutInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeASplitNbr p B Bs x L D J n f y K →
    ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
      ggAutomizer K' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs → K' ≤ L ⊔ K

@[expose] def GGTypeAJoinReflInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (n f : ℕ) (y : G) (K : Subgroup G), GGTypeASplitNbr p B Bs x L D J n f y K →
    ∀ (y' : G) (K' : Subgroup G), GGNbr p B x D J y' K' →
      ¬ ggAutomizer K' Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs → p ∣ n + 3

theorem ggTypeAJoinInput_of_aut_refl (h₁ : GGTypeAJoinAutInput) (h₂ : GGTypeAJoinReflInput) :
    GGTypeAJoinInput := by
  intro G _ _ p B Bs x L D J n f y K hN y' K' hK'
  obtain ⟨-, -, -, -, -, -, -, hp3, -⟩ := id hN
  by_contra hle
  exact hp3 (h₂ G p B Bs x L D J n f y K hN y' K' hK'
    fun hA => hle (h₁ G p B Bs x L D J n f y K hN y' K' hK' hA))

end CFSG.StandardType
