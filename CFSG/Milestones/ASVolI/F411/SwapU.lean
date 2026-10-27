module

public import CFSG.Milestones.ASVolI.F411.SwapIdx
public import CFSG.Milestones.ASVolI.F45.U
public import CFSG.Timmesfeld.ARS.CaseOADegSUAlign
import all CFSG.Milestones.ASVolI.F4

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF CFSG.GH74.BNPair CFSG.Quasithin.H13.F431.BN

section Card

theorem burnsideF411_card_map_of_inf_ker {X Y : Type*} [Group X] [Group Y] (π : X →* Y)
    {H K : Subgroup X} (hHK : H ≤ K) (hK : K ⊓ π.ker = ⊥) :
    Nat.card (H.map π) = Nat.card H := by
  have hinj : Set.InjOn π (H : Set X) := by
    intro x hx y hy hxy
    have hm : x⁻¹ * y ∈ K ⊓ π.ker :=
      Subgroup.mem_inf.mpr ⟨K.mul_mem (K.inv_mem (hHK hx)) (hHK hy), MonoidHom.mem_ker.mpr (by
        rw [map_mul, map_inv, hxy, inv_mul_cancel])⟩
    rw [hK, Subgroup.mem_bot] at hm
    exact inv_mul_eq_one.mp hm
  have := Nat.card_image_of_injOn hinj
  rw [← Subgroup.coe_map] at this
  exact this

end Card

section RootGroups

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Quasithin.H13.F431.Un
  CFSG.GH74.GLS.SP CFSG.Timmesfeld.ARS.CaseOADeg

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]
  (hF : Nat.card F = (p ^ f) ^ 2)

include hF in
theorem burnsideF411_card_le_unOct_one : Nat.card F ≤ Nat.card (unOct hF 1) := by
  have hσ := unitaryInvolution_involutive hF
  have h01 : (0 : Fin 4) ≠ 1 := by decide
  have h0 : (0 : Fin 4) ≠ Fin.rev 0 := by decide
  have h1 : (1 : Fin 4) ≠ Fin.rev 1 := by decide
  have h10 : (1 : Fin 4) ≠ Fin.rev 0 := by decide
  have hw : weight 4 0 - weight 4 1 = toStd 4 (octRoot 1) := by
    rw [octRoot_one]
    funext c
    fin_cases c <;> simp [weight, toStd, CFSG.LieType.Universal.Symplectic.toStd, Nat.even_iff]
  let φ : Multiplicative F → unOct hF 1 := fun c =>
    ⟨rootHom (unitaryInvolution F p f) hσ h01 h0 h1 c, SUExtras.rootHom_mem hσ h01 h0 h1 h10 hw c⟩
  have hφ : Function.Injective φ := by
    intro c d hcd
    have h := congrArg (fun x : unOct hF 1 =>
      SUExtras.mat (unitaryInvolution F p f) 4 (x : SU (unitaryInvolution F p f) 4) 0 1) hcd
    simp only [φ, SUExtras.mat_apply, coe_rootHom, SUExtras.rootMatrix_apply_pq h01 h10] at h
    exact Multiplicative.toAdd.injective h
  calc Nat.card F = Nat.card (Multiplicative F) := rfl
    _ ≤ Nat.card (unOct hF 1) := Nat.card_le_card_of_injective φ hφ

include hF in
theorem burnsideF411_unOct_four_le :
    unOct hF 4 ≤ (longRootHom (unitaryInvolution F p f) (i := (1 : Fin 4)) (by decide)).range := by
  have hσ := unitaryInvolution_involutive hF
  have hγ : toStd 4 (octRoot 4) = 2 • weight 4 (1 : Fin 4) := by
    rw [octRoot_four]
    funext c
    fin_cases c <;> simp [weight, toStd, CFSG.LieType.Universal.Symplectic.toStd, Nat.even_iff]
  show CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F p f) hσ 4 (octRoot 4) ≤ _
  refine sup_le (sup_le ?_ ?_) ?_
  · exact iSup_le fun a => iSup_le fun b => iSup_le fun _ => iSup_le fun _ =>
      iSup_le fun _ => iSup_le fun hba => iSup_le fun hw =>
        absurd (hw.trans hγ) (weight_four_check a b 1 hba)
  · exact iSup_le fun a => iSup_le fun _ => iSup_le fun hw => by
      obtain rfl := two_weight_four_check a 1 (hw.trans hγ)
      exact le_rfl
  · exact iSup_le fun _ => iSup_le fun k => iSup_le fun _ => iSup_le fun _ =>
      iSup_le fun hk => absurd hk (rev_ne_self_four k)

include hF in
theorem burnsideF411_card_unOct_four_le : Nat.card (unOct hF 4) ≤ p ^ f := by
  calc Nat.card (unOct hF 4)
      ≤ Nat.card (longRootHom (unitaryInvolution F p f) (i := (1 : Fin 4)) (by decide)).range :=
        Subgroup.card_le_of_le (burnsideF411_unOct_four_le hF)
    _ ≤ Nat.card (Multiplicative (traceZero (unitaryInvolution F p f))) :=
        Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
    _ = Nat.card (traceZero (unitaryInvolution F p f)) := rfl
    _ = p ^ f := CFSG.LieType.Steinberg.card_traceZero hF

theorem burnsideF411_check5 (a b : Fin 5) (h1 : a ≠ b) (h2 : a ≠ Fin.rev a)
    (h3 : b ≠ Fin.rev b) (h4 : b ≠ Fin.rev a)
    (hw : weight 5 a - weight 5 b = toStd 5 (octRootB 1)) :
      (a = 0 ∧ b = 1) ∨ (a = 3 ∧ b = 4) := by
  rw [octRootB_one] at hw
  have e0 := congrFun hw 0
  have e1 := congrFun hw 1
  fin_cases a <;> fin_cases b <;> simp_all [weight, toStd, Nat.even_iff, Fin.rev] <;> omega

include hF in
theorem burnsideF411_un5Oct_one_le :
    un5Oct hF 1 ≤ (rootHom (unitaryInvolution F p f) (unitaryInvolution_involutive hF)
      (i := (0 : Fin 5)) (j := 1) (by decide) (by decide) (by decide)).range := by
  have hσ := unitaryInvolution_involutive hF
  show CFSG.LieType.Universal.Unitary.rootGroup (unitaryInvolution F p f) hσ 5 (octRootB 1) ≤ _
  refine sup_le (sup_le ?_ ?_) ?_
  · refine iSup_le fun a => iSup_le fun b => iSup_le fun hab => iSup_le fun ha =>
      iSup_le fun hb => iSup_le fun hba => iSup_le fun hw => ?_
    rcases burnsideF411_check5 a b hab ha hb hba hw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact le_rfl
    · rintro _ ⟨c, rfl⟩
      refine ⟨Multiplicative.ofAdd (-(unitaryInvolution F p f c.toAdd)), ?_⟩
      apply SUExtras.mat_injective
      rw [SUExtras.mat_apply, SUExtras.mat_apply, coe_rootHom, coe_rootHom]
      have r0 : Fin.rev (0 : Fin 5) = 4 := by decide
      have r1 : Fin.rev (1 : Fin 5) = 3 := by decide
      have r3 : Fin.rev (3 : Fin 5) = 1 := by decide
      have r4 : Fin.rev (4 : Fin 5) = 0 := by decide
      simp only [rootMatrix, toAdd_ofAdd, map_neg, hσ, r0, r1, r3, r4]
      ext x y
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply]
      split_ifs <;> simp_all <;> ring
  · refine iSup_le fun a => iSup_le fun _ => iSup_le fun hw => ?_
    exfalso
    have e0 := congrFun hw 0
    rw [octRootB_one] at e0
    simp [toStd, Nat.even_iff] at e0
    omega
  · refine iSup_le fun a => iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
      iSup_le fun _ => iSup_le fun hw => ?_
    exfalso
    rw [octRootB_one] at hw
    have e0 := congrFun hw 0
    have e1 := congrFun hw 1
    fin_cases a <;> simp_all [weight, toStd, Nat.even_iff]

include hF in
theorem burnsideF411_card_un5Oct_one_le : Nat.card (un5Oct hF 1) ≤ Nat.card F := by
  calc Nat.card (un5Oct hF 1)
      ≤ Nat.card (rootHom (unitaryInvolution F p f) (unitaryInvolution_involutive hF)
          (i := (0 : Fin 5)) (j := 1) (by decide) (by decide) (by decide)).range :=
        Subgroup.card_le_of_le (burnsideF411_un5Oct_one_le hF)
    _ ≤ Nat.card (Multiplicative F) :=
        Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
    _ = Nat.card F := rfl

theorem burnsideF411_heisenbergMatrix_apply_irev {σ : F ≃+* F} (a b : F) :
    heisenbergMatrix σ (1 : Fin 5) 2 a b 1 (Fin.rev 1) = b := by
  have r1 : Fin.rev (1 : Fin 5) = 3 := by decide
  rw [r1]
  simp [heisenbergMatrix, Matrix.add_apply, Matrix.sub_apply, Matrix.single_apply,
    Matrix.one_apply]

include hF in
theorem burnsideF411_card_un5Oct_four_ge : Nat.card F * p ^ f ≤ Nat.card (un5Oct hF 4) := by
  set σ := unitaryInvolution F p f with hσdef
  have hσ := unitaryInvolution_involutive hF
  have hσ' := CFSG.ClassicalGroups.Unitary.isUnitaryInvolution_unitaryInvolution hF
  have hi : (1 : Fin 5) ≠ Fin.rev 1 := by decide
  have hik : (1 : Fin 5) ≠ 2 := by decide
  have hk : Fin.rev (2 : Fin 5) = 2 := by decide
  have hw : weight 5 1 = toStd 5 (octRootB 4) := by
    rw [octRootB_four]
    funext c
    fin_cases c <;> simp [weight, toStd, Nat.even_iff]
  have hle : heisenbergSubgroup σ hσ hi hik hk ≤ un5Oct hF 4 :=
    SUExtras.heisenberg_le hσ hi hik hk hw
  have hb₀ : ∀ a : F, ∃ b : F, b + σ b + σ a * a = 0 := by
    intro a
    have hfix : σ (-(σ a * a)) = -(σ a * a) := by rw [map_neg, map_mul, hσ, mul_comm]
    obtain ⟨c, hc⟩ := hσ'.trace_surj _ hfix
    exact ⟨c, by rw [hc]; ring⟩
  choose b₀ hb₀ using hb₀
  have hab : ∀ x : F × traceZero σ, (b₀ x.1 + (x.2 : F)) + σ (b₀ x.1 + (x.2 : F)) +
      σ x.1 * x.1 = 0 := by
    intro x
    have h2 : (x.2 : F) + σ (x.2 : F) = 0 := x.2.2
    have h1 := hb₀ x.1
    rw [map_add]
    linear_combination h1 + h2
  have hconstr : ∀ x : F × traceZero σ, ∃ g : SU σ 5,
      ((g : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
        heisenbergMatrix σ 1 2 x.1 (b₀ x.1 + (x.2 : F)) := by
    intro x
    set a := x.1
    set b := b₀ x.1 + (x.2 : F)
    refine ⟨⟨⟨heisenbergMatrix σ 1 2 a b, heisenbergMatrix σ 1 2 (-a) (-b - a * σ a), ?_, ?_⟩,
      det_heisenbergMatrix σ hi hik hk a b, heisenbergMatrix_isometry σ hσ hi hik hk (hab x)⟩, rfl⟩
    · rw [heisenbergMatrix_mul σ hi hik hk, map_neg]
      have e1 : a + -a = 0 := add_neg_cancel a
      have e2 : b + (-b - a * σ a) - a * -σ a = 0 := by ring
      rw [e1, e2, heisenbergMatrix_zero]
    · rw [heisenbergMatrix_mul σ hi hik hk]
      have e1 : -a + a = 0 := neg_add_cancel a
      have e2 : -b - a * σ a + b - -a * σ a = 0 := by ring
      rw [e1, e2, heisenbergMatrix_zero]
  choose g hg using hconstr
  let φ : F × traceZero σ → heisenbergSubgroup σ hσ hi hik hk := fun x =>
    ⟨g x, x.1, b₀ x.1 + (x.2 : F), hab x, hg x⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    have hm : ((g x : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) =
        ((g y : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F) := by
      have := congrArg (fun z : heisenbergSubgroup σ hσ hi hik hk =>
        (((z : SU σ 5) : GL (Fin 5) F) : Matrix (Fin 5) (Fin 5) F)) hxy
      exact this
    rw [hg, hg] at hm
    have e1 := congrFun (congrFun hm 1) 2
    have e2 := congrFun (congrFun hm 1) (Fin.rev 1)
    rw [SUExtras.heisenbergMatrix_apply_ik hik hk, SUExtras.heisenbergMatrix_apply_ik hik hk] at e1
    rw [burnsideF411_heisenbergMatrix_apply_irev, burnsideF411_heisenbergMatrix_apply_irev] at e2
    have h1 : x.1 = y.1 := e1
    have h2 : (x.2 : F) = y.2 := by rw [h1] at e2; exact add_left_cancel e2
    exact Prod.ext h1 (Subtype.ext h2)
  calc Nat.card F * p ^ f = Nat.card (F × traceZero σ) := by
        rw [Nat.card_prod, CFSG.LieType.Steinberg.card_traceZero hF]
    _ ≤ Nat.card (heisenbergSubgroup σ hσ hi hik hk) := Nat.card_le_card_of_injective φ hφ
    _ ≤ Nat.card (un5Oct hF 4) := Subgroup.card_le_of_le hle

end RootGroups

section Swap

open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Quasithin.H13.F431.Un
  CFSG.GH74.GLS.SP CFSG.ASVolI.ChF.ClassicalRoots


theorem burnsideF411_relIndex_ne_U4 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U4 p f Gp M₁ M₂) :
    (Gp ⊓ (M₁ ⊓ M₂)).relIndex (Gp ⊓ M₁) ≠ (Gp ⊓ (M₁ ⊓ M₂)).relIndex (Gp ⊓ M₂) := by
  haveI : Finite E := hyp.finite
  have hp : p.Prime := burnsideF4a_prime_of_isGenLie hyp.model
  haveI : Fact p.Prime := ⟨hp⟩
  have hP := burnsideF4j_parabolics ChF.nativeChartCompatibility hyp
  obtain ⟨marking⟩ := burnsideF45U_nonempty_marking (c := .U4) hyp.toHypF_4_4g
  have hF : Nat.card marking.field = (p ^ f) ^ 2 := marking.field_card.trans (if_pos (Or.inl rfl))
  haveI : CharP marking.field p := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  haveI : Fact ((ζ : marking.field) ≠ 0) := ⟨hζ⟩
  let θ₀ : StatedProj (StatedSU 4 (p ^ f) marking.field) ≃* ↥Gp :=
    (MulEquiv.refl _ : StatedProj (StatedSU 4 (p ^ f) marking.field) ≃*
      StatedProj (nativeGroup .U4 (p ^ f) marking.field)).trans marking.identification
  haveI : Finite (StatedProj (StatedSU 4 (p ^ f) marking.field)) :=
    Finite.of_equiv ↥Gp θ₀.symm.toEquiv
  refine burnsideF411_relIndex_ne_of_system hp hP θ₀ (burnsideF45U4_system hF ζ)
    (burnsideF45U4_system_isSylow hF ζ) ?_
  rw [P_true, P_false, burnsideF4h_ree_relIndex_P₁, burnsideF4h_ree_relIndex_P₂]
  have hker := burnsideF45U_unU_inf_ker hF (n := 4) (by norm_num)
  have c1 : Nat.card ((burnsideF45U4_system hF ζ).root 1) = Nat.card (unOct hF 1) :=
    burnsideF411_card_map_of_inf_ker (burnsideF45U_proj hF 4)
      (CFSG.GH74.GLS.SP.root_le_U_of_isRootGroupSystem (unPre hF ζ).roots (k := 1)
        (by norm_num) (by norm_num)) hker
  have c4 : Nat.card ((burnsideF45U4_system hF ζ).root ((4 : ℕ) : ℤ)) = Nat.card (unOct hF 4) :=
    burnsideF411_card_map_of_inf_ker (burnsideF45U_proj hF 4)
      (CFSG.GH74.GLS.SP.root_le_U_of_isRootGroupSystem (unPre hF ζ).roots (k := 4)
        (by norm_num) (by norm_num)) hker
  rw [c1, c4]
  have h1 := burnsideF411_card_le_unOct_one hF
  have h4 := burnsideF411_card_unOct_four_le hF
  have hq := CFSG.ClassicalGroups.Unitary.one_lt_pow_of_card hF
  rw [hF] at h1
  intro h
  have hle : (p ^ f) ^ 2 ≤ p ^ f := by omega
  nlinarith

theorem burnsideF411_swap_U4 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U4 p f Gp M₁ M₂) : burnsideF411_Swap M₁ M₂ := by
  haveI : Finite E := hyp.finite
  exact burnsideF411_swap_of_relIndex_ne hyp.normal hyp.split (burnsideF411_relIndex_ne_U4 hyp)

theorem burnsideF411_relIndex_ne_U5 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 p f Gp M₁ M₂) :
    (Gp ⊓ (M₁ ⊓ M₂)).relIndex (Gp ⊓ M₁) ≠ (Gp ⊓ (M₁ ⊓ M₂)).relIndex (Gp ⊓ M₂) := by
  haveI : Finite E := hyp.finite
  have hp : p.Prime := burnsideF4a_prime_of_isGenLie hyp.model
  haveI : Fact p.Prime := ⟨hp⟩
  have hP := burnsideF4j_parabolics ChF.nativeChartCompatibility hyp
  obtain ⟨marking⟩ := burnsideF45U_nonempty_marking (c := .U5) hyp.toHypF_4_4g
  have hF : Nat.card marking.field = (p ^ f) ^ 2 := marking.field_card.trans (if_pos (Or.inr rfl))
  haveI : CharP marking.field p := CFSG.ClassicalGroups.Unitary.charP_of_card_sq hF
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  haveI : Fact ((ζ : marking.field) ≠ 0) := ⟨hζ⟩
  let θ₀ : StatedProj (StatedSU 5 (p ^ f) marking.field) ≃* ↥Gp :=
    (MulEquiv.refl _ : StatedProj (StatedSU 5 (p ^ f) marking.field) ≃*
      StatedProj (nativeGroup .U5 (p ^ f) marking.field)).trans marking.identification
  haveI : Finite (StatedProj (StatedSU 5 (p ^ f) marking.field)) :=
    Finite.of_equiv ↥Gp θ₀.symm.toEquiv
  refine burnsideF411_relIndex_ne_of_system hp hP θ₀ (burnsideF45U5_system hF ζ)
    (burnsideF45U5_system_isSylow hF ζ) ?_
  rw [P_true, P_false, burnsideF4h_ree_relIndex_P₁, burnsideF4h_ree_relIndex_P₂]
  have hker := burnsideF45U_unU_inf_ker hF (n := 5) (by norm_num)
  have c1 : Nat.card ((burnsideF45U5_system hF ζ).root 1) = Nat.card (un5Oct hF 1) :=
    burnsideF411_card_map_of_inf_ker (burnsideF45U_proj hF 5)
      (CFSG.GH74.GLS.SP.root_le_U_of_isRootGroupSystem (un5Pre hF ζ).roots (k := 1)
        (by norm_num) (by norm_num)) hker
  have c4 : Nat.card ((burnsideF45U5_system hF ζ).root ((4 : ℕ) : ℤ)) = Nat.card (un5Oct hF 4) :=
    burnsideF411_card_map_of_inf_ker (burnsideF45U_proj hF 5)
      (CFSG.GH74.GLS.SP.root_le_U_of_isRootGroupSystem (un5Pre hF ζ).roots (k := 4)
        (by norm_num) (by norm_num)) hker
  rw [c1, c4]
  have h1 := burnsideF411_card_un5Oct_one_le hF
  have h4 := burnsideF411_card_un5Oct_four_ge hF
  have hq := CFSG.ClassicalGroups.Unitary.one_lt_pow_of_card hF
  rw [hF] at h1 h4
  intro h
  have hle : (p ^ f) ^ 2 * p ^ f ≤ (p ^ f) ^ 2 := by omega
  nlinarith

theorem burnsideF411_swap_U5 {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 p f Gp M₁ M₂) : burnsideF411_Swap M₁ M₂ := by
  haveI : Finite E := hyp.finite
  exact burnsideF411_swap_of_relIndex_ne hyp.normal hyp.split (burnsideF411_relIndex_ne_U5 hyp)

end Swap

end CFSG.ASVolI
