module

public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicSixTransport
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicSixDescent
public import CFSG.RankThree.Chevalley.SteinbergBUF4CyclotomicSixStructure

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley F4Weyl RootSpace SteinbergBN
  CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.Classical Matrix
open scoped Pointwise

theorem even_F4_cyclotomic_six_nonregular_derived_centralizer {f : ℕ} (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = 2 ^ f) (Ω : Type) [Field Ω] [Algebra K Ω]
    [IsAlgClosure K Ω] (F : Ω →+* Ω) (hF : ∀ c, F c = c ^ Nat.card K) {p : ℕ} (hp : p.Prime)
    (hp3 : 3 < p) (hpd : p ∣ Nat.card K ^ 2 - Nat.card K + 1) (K₆ : IntermediateField K Ω)
    (hK₆ : Module.finrank K K₆ = 6) (K₂ K₃ : IntermediateField K K₆)
    (h2 : Module.finrank K K₂ = 2) (h3 : Module.finrank K K₃ = 3) (σ₂ : K₂ ≃+* K₂)
    (hσ₂ : ∀ b, σ₂ b = b ^ Nat.card K) (n g : ModGL .F4 Ω)
    (hn : n = canonicalRep (coxeterSystem .F4) Ω f4PhiSix) (hg : g ∈ adjointGroup .F4 Ω)
    (hgn : g⁻¹ * Units.map (entrywiseHom F) g = n) (Γ T₀ : Subgroup (ModGL .F4 Ω))
    (hΓ : Γ = conjEntrywiseImage K g⁻¹) (hT₀ : T₀ = torusGroup .F4 Ω ⊓ Γ) (x : ModGL .F4 Ω)
    (hx : x ∈ T₀) (hxp : orderOf x = p) (u : WeylGroup .F4) (κ : F4A2Kind) (ε : ℤ)
    (hε : ε = 1 ∨ ε = -1)
    (hu : (fun α => u • α) '' {α | IsRoot .F4 α ∧ torusRootChar x α = 1} =
      parabolicRoots .F4 {κ.i, κ.j})
    (huw : ∀ z ∈ Submodule.span ℝ (ofLattice '' parabolicRoots .F4 {κ.i, κ.j}),
      weylAct .F4 (u * f4PhiSix * u⁻¹) z =
        -weylAct .F4 ((simple .F4 κ.i * simple .F4 κ.j) ^ ε) z)
    (h y : ModGL .F4 Ω) (hh : h = canonicalRep (coxeterSystem .F4) Ω u) (hy : y = h * x * h⁻¹)
    (Γ₁ D R : Subgroup (ModGL .F4 Ω)) (hΓ₁ : Γ₁ = Γ.map (MulAut.conj h).toMonoidHom)
    (hD : D = Γ₁ ⊓ Subgroup.centralizer {y}) (hR : R = ⁅D, D⁆)
    (U : Subgroup (ModGL .F4 K₂))
    (hU : ∀ w, w ∈ U ↔ ∃ hw : w ∈ subsystemGroup .F4 K₂ {κ.i, κ.j},
      ((f4A2Equiv K₂ κ ⟨w, hw⟩ : Matrix (Fin 3) (Fin 3) K₂).map σ₂)ᵀ *
        (f4A2Equiv K₂ κ ⟨w, hw⟩ : Matrix (Fin 3) (Fin 3) K₂) = 1) :
    4 ≤ Nat.card K ∧
    (((adjointGroup .F4 K₆).map (baseChangeGL (algebraMap K₆ Ω)) ⊓ Subgroup.centralizer {y} :
        Subgroup (ModGL .F4 Ω)) : Set (ModGL .F4 Ω)) =
      ((torusGroup .F4 K₆).map (baseChangeGL (algebraMap K₆ Ω)) : Set (ModGL .F4 Ω)) *
        ((subsystemGroup .F4 K₆ {κ.i, κ.j}).map (baseChangeGL (algebraMap K₆ Ω)) :
          Set (ModGL .F4 Ω)) ∧
    (∀ A : Matrix.SpecialLinearGroup (Fin 3) K₂,
      ((A : Matrix (Fin 3) (Fin 3) K₂).map σ₂)ᵀ * A = 1 ↔
        ∃ g : subsystemGroup .F4 K₂ {κ.i, κ.j}, (g : ModGL .F4 K₂) ∈ U ∧
          f4A2Equiv K₂ κ g = A) ∧
    ∃ a ∈ subsystemGroup .F4 K₃ {κ.i, κ.j},
      R = (subsystemGroup .F4 K₆ {κ.i, κ.j}).map (baseChangeGL (algebraMap K₆ Ω)) ⊓ Γ₁ ∧
      R = (U.map ((MulAut.conj (baseChangeGL (algebraMap K₃ K₆) a)).toMonoidHom.comp
        (baseChangeGL (algebraMap K₂ K₆)))).map (baseChangeGL (algebraMap K₆ Ω)) ∧
      (∃ e : U ≃* R,
        (∀ u : U, (e u : ModGL .F4 Ω) = baseChangeGL (algebraMap K₆ Ω)
          (baseChangeGL (algebraMap K₃ K₆) a * baseChangeGL (algebraMap K₂ K₆) u *
            (baseChangeGL (algebraMap K₃ K₆) a)⁻¹)) ∧
        ∀ (g : subsystemGroup .F4 K₂ {κ.i, κ.j}) (hg : (g : ModGL .F4 K₂) ∈ U),
          e ⟨g, hg⟩ ∈ Subgroup.center R ↔ ∃ t : K₂, t ^ (Nat.card K + 1) = 1 ∧ t ^ 3 = 1 ∧
            (f4A2Equiv K₂ κ g : Matrix (Fin 3) (Fin 3) K₂) = Matrix.scalar (Fin 3) t) ∧
      CFSG.IsQuasisimple R ∧ Group.IsPerfect R ∧ CFSG.layer R = ⊤ ∧ R ≠ ⊥ ∧
      D ⊓ Subgroup.centralizer (R : Set (ModGL .F4 Ω)) = (Subgroup.center D).map D.subtype ∧
      (Subgroup.center D).map D.subtype ≤
        (torusGroup .F4 K₆).map (baseChangeGL (algebraMap K₆ Ω)) ∧
      Odd (Nat.card (Subgroup.center D)) ∧
      ∃ x₀ : adjointGroup .F4 K,
        baseChangeGL (algebraMap K Ω) (x₀ : ModGL .F4 K) = g * x * g⁻¹ ∧
        (Subgroup.centralizer {x₀}).map
            ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup .F4 K).subtype) =
          D.map (MulAut.conj (g * h⁻¹)).toMonoidHom ∧
        ∃ R₀ : Subgroup (adjointGroup .F4 K),
          R₀ ≤ ⁅Subgroup.centralizer {x₀}, Subgroup.centralizer {x₀}⁆ ∧
          ∃ k ∈ adjointGroup .F4 K₆, ∃ P : GL (Fin 2) K₂,
            (R₀.map ((baseChangeGL (algebraMap K K₆)).comp (adjointGroup .F4 K).subtype)).map
                (MulAut.conj k).toMonoidHom =
              ((Matrix.SpecialLinearGroup.map (algebraMap K K₆)).range.map
                (conjSL (Matrix.GeneralLinearGroup.map (algebraMap K₂ K₆) P))).map
                  (rootSL2 .F4 K₆ (Pi.single κ.i 1)) := by
  classical
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hK
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have h4 : 4 ≤ Nat.card K := by
    rcases Nat.lt_or_ge f 2 with hf2 | hf2
    · have hf1 : f = 1 := by omega
      rw [hK, hf1] at hpd
      have hp3' : p ∣ 3 := by norm_num at hpd; exact hpd
      have := Nat.le_of_dvd (by norm_num) hp3'
      omega
    · rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  obtain ⟨hgK₆, hC, σ, hσ, hΓ₁ch, hDeq⟩ := cyclotomic_six_centralizer_and_D K Ω F hF hp hp3 K₆ hK₆ n
    g hn hg hgn Γ T₀ hΓ hT₀ x hx hxp u hu h y hh hy Γ₁ D hΓ₁ hD
  have hv : ∀ k ∈ ({κ.i, κ.j} : Set (Fin Tag.F4.rank)),
      (u * f4PhiSix * u⁻¹) • (Pi.single k 1 : Fin Tag.F4.rank → ℤ) =
        -(((simple .F4 κ.i * simple .F4 κ.j) ^ ε) • (Pi.single k 1 : Fin Tag.F4.rank → ℤ)) :=
    fun k hk => smul_eq_neg_smul_of_weylAct_eq_neg huw
      ⟨isRoot_single _ k, fun l hl => Pi.single_eq_of_ne (fun e : l = k => hl (e ▸ hk)) 1⟩
  obtain ⟨hSU, a, ha, hRQ, hRU, hE, hRqs, hRp, hlayer, hRbot, hcent, hcenH, hodd, P, hP⟩ :=
    cyclotomic_six_D_structure K h4 Ω K₆ hK₆ K₂ K₃ h2 h3 σ hσ σ₂ hσ₂ κ ε hε
      (u * f4PhiSix * u⁻¹) hv U hU Γ₁ D R hΓ₁ch hDeq hR
  have hxΓ : x ∈ Γ := (hT₀ ▸ hx).2
  have hhK₆ : h ∈ (adjointGroup .F4 K₆).map (baseChangeGL (algebraMap K₆ Ω)) :=
    ⟨_, canonicalRep_mem_adjointGroup _ K₆ u, by rw [hh]; exact baseChangeGL_canonicalRep _ u⟩
  have ha₆ : baseChangeGL (algebraMap K₃ K₆) a ∈ adjointGroup .F4 K₆ :=
    EvenF4QPlus.subsystemGroup_le_adjointGroup' _ (baseChangeGL_mem_subsystemGroup _ ha)
  have hSD : ∀ s ∈ ((Matrix.SpecialLinearGroup.map (algebraMap K K₆)).range.map
      (conjSL (Matrix.GeneralLinearGroup.map (algebraMap K₂ K₆) P))).map
        (rootSL2 .F4 K₆ (Pi.single κ.i 1)),
      baseChangeGL (algebraMap K₆ Ω) (baseChangeGL (algebraMap K₃ K₆) a * s *
        (baseChangeGL (algebraMap K₃ K₆) a)⁻¹) ∈ ⁅D, D⁆ := by
    rintro _ ⟨_, ⟨_, ⟨A, rfl⟩, rfl⟩, rfl⟩
    rw [← hR]
    have hA := hP A
    rwa [map_conjSL_ringHom, specialLinearGroup_map_algebraMap_tower] at hA
  obtain ⟨x₀, hx₀, hCx, R₀, hR₀, k, hk, hRk⟩ := cyclotomic_transport_derived K Ω K₆ g hgK₆ Γ hΓ
    x hxΓ h y hhK₆ hy Γ₁ D hΓ₁ hD _ ha₆ _ hSD
  exact ⟨h4, hC, hSU, a, ha, hRQ, hRU, hE, hRqs, hRp, hlayer, hRbot, hcent, hcenH, hodd, x₀, hx₀,
    hCx, R₀, hR₀, k, hk, P, hRk⟩

end CFSG.RankThree.Chevalley
