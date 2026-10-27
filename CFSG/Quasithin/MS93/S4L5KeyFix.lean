module

public import CFSG.Quasithin.MS93.S4L5KeyLift
public import CFSG.Quasithin.MS93.S4LCoreC
import CFSG.Quasithin.MS93.S33SpCoord
import CFSG.Quasithin.MS93.S5AGeo
public import CFSG.Quasithin.MS93.S4L5Stmt

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem exists_coordHom_sp (h : PUHyp M T L) {F : Type} [Field F]
    {a : ↥L →* ↥(StatedSp 2 F)}
    {β : ↥(Uq M T L) →* Multiplicative (Fin 1 → Fin 2 ⊕ Fin 2 → F)} (hβ : Function.Surjective β)
    (hβα : ∀ (l : ↥L) (u v : ↥(Uq M T L)), (v : G) = l * u * l⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        (moduleAct false (a l : GL (Fin 2 ⊕ Fin 2) F)).mulVec (Multiplicative.toAdd (β u) i))
    {E₀ : Subgroup G} (hE₀ : E₀ ≤ L ⊔ pCoreOf 2 M) :
    ∃ ψ : ↥E₀ →* ↥(StatedSp 2 F), ∀ e : ↥E₀, IsCoordAct β (e : G) (MSP.mat (ψ e)).mulVec := by
  have hMV : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hE₀M : E₀ ≤ M := hE₀.trans (sup_le h.L_le (pCoreOf_le' M))
  have hmat : ∀ e : ↥E₀, ∃ γ : ↥(StatedSp 2 F), IsCoordAct β (e : G) (MSP.mat γ).mulVec :=
    fun e => (sup_le_coordGroup_sp h hβα (hE₀ e.2)).2
  choose γ hγ using hmat
  have huniq : ∀ (e : ↥E₀) (g : ↥(StatedSp 2 F)), IsCoordAct β (e : G) (MSP.mat g).mulVec →
      γ e = g := fun e g hg =>
    Subtype.ext (Units.ext (IsCoordAct.matrix_eq hβ (hMV (hE₀M e.2)) (hγ e) hg))
  refine ⟨{ toFun := γ, map_one' := ?_, map_mul' := ?_ }, hγ⟩
  · exact huniq 1 1 (by simpa [MSP.mat_one] using (isCoordAct_one_mulVec (β := β)))
  · intro e₁ e₂
    refine huniq (e₁ * e₂) (γ e₁ * γ e₂) ?_
    have := (hγ e₁).mul (hMV (hE₀M e₂.2)) (hγ e₂)
    convert this using 1
    funext x
    simp [MSP.mat_mul, Matrix.mulVec_mulVec]

theorem le_sup_of_le_centralizer_fix_sp (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L)
    {E₀ : Subgroup G} (hE₀T : E₀ ≤ T) (hE₀ : E₀ ≤ L ⊔ pCoreOf 2 M)
    (hT : T ≤ Subgroup.centralizer
      ((Uq M T L ⊓ Subgroup.centralizer (E₀ : Set G) : Subgroup G) : Set G)) :
    T ≤ L ⊔ pCoreOf 2 M := by
  have hUE := hU
  obtain ⟨m, F, _, _, a, hm, hcard, ha, hLV, hZV, β, hβ, hβker, hβα⟩ := hU
  have hcard' : Fintype.card F = 2 ^ (2 * m) := by rw [hcard, S34F.four_pow_eq]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow hcard'
  have hMV : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hTV : T ≤ Subgroup.normalizer (Uq M T L : Set G) := h.le.trans hMV
  have hTZ : T ≤ Subgroup.normalizer
      ((Uq M T L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    h.le.trans (le_normalizer_inf (le_normalizer_Uq h.le_normalizer)
      (le_normalizer_centralizer h.le_normalizer))
  obtain ⟨ψ, hψ⟩ := exists_coordHom_sp h hβ hβα hE₀
  have hE₀2 : IsPGroup 2 ↥E₀ := h.isPGroup.to_le hE₀T
  have hR : IsPGroup 2 ↥ψ.range :=
    IsPGroup.of_surjective hE₀2 ψ.rangeRestrict ψ.rangeRestrict_surjective
  obtain ⟨x₀, hx₀R, hx₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (S5.fixSp_ne_bot hR)
  have hfix₀ : ∀ e : ↥E₀, MSP.mat (ψ e) *ᵥ x₀ = x₀ := fun e =>
    MSP.mem_fixSp.mp hx₀R _ ⟨e, rfl⟩
  have hscal : ∀ c : F, ∃ u : ↥(Uq M T L), Multiplicative.toAdd (β u) 0 = c • x₀ ∧
      (u : G) ∈ Subgroup.centralizer (E₀ : Set G) := by
    intro c
    obtain ⟨u, hu⟩ := exists_coord_eq hβ (c • x₀)
    refine ⟨u, hu, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    set v : ↥(Uq M T L) :=
      ⟨e * u * e⁻¹, conj_mem_of_mem_normalizer (hMV (h.le (hE₀T he))) u⟩ with hvdef
    have hv := hψ ⟨e, he⟩ u v rfl
    rw [hu, Matrix.mulVec_smul, hfix₀, ← hu] at hv
    have hk := mul_inv_mem_of_coord_eq hβker hv.symm
    have hvU : (v : G) ∈ Uq M T L := v.2
    have hcomm : (u : G)⁻¹ * v = v * (u : G)⁻¹ := Sp4L.uq_comm h (inv_mem u.2) hvU
    have hmem : e * (u : G) * e⁻¹ * (u : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
      have := hk.2
      rw [hcomm] at this
      exact this
    have h1 := IsSp4UEven.lift_flat h hUE (hE₀ he) u.2 hmem
    calc e * (u : G) = e * u * e⁻¹ * e := by group
      _ = u * e := by rw [h1]
  intro t ht
  obtain ⟨f, hf⟩ := exists_isCoordAct hβ hβker (hTV ht) (hTZ ht)
  obtain ⟨f', hf'⟩ := exists_isCoordAct hβ hβker (inv_mem (hTV ht)) (hTZ (inv_mem ht))
  obtain ⟨σ, hσ⟩ := S33.exists_semilinear_sp ha hLV hβ (S33.isCoordAct_of_natSp hβα) (hTV ht)
    (h.le_normalizer (h.le ht)) hf hf'
  have hfix : ∀ c : F, f (c • x₀) = c • x₀ := by
    intro c
    obtain ⟨u, hu, huC⟩ := hscal c
    have htu : t * (u : G) * t⁻¹ = u := by
      have := Subgroup.mem_centralizer_iff.mp (hT ht) u ⟨u.2, huC⟩
      rw [← this, mul_inv_cancel_right]
    have := hf u u htu.symm
    rw [hu] at this
    exact this.symm
  have hσid := MSP.semilinear_eq_id_of_fix hσ hx₀ hfix
  have hlin : ∀ (c : F) (x : MSP.V4 F), f (c • x) = c • f x := fun c x => by rw [hσ, hσid]
  obtain ⟨γ, hγ⟩ := S34R.exists_gl_of_linear hβ hβker (hTV ht) (hTZ ht) hf hlin
  exact S34D.mem_sup_of_isCoordAct_sp h hcard' ha hβ hβker hβα ht hγ

theorem le_flat_of_qv_le_centralizer_sp (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L)
    {E : Subgroup (puAmalgam h.le).Universal}
    (hEβ : E ≤ Qv (puAmalgam h.le) (baseB _)) (hEf : E ≤ S34F.flat h (baseA _))
    (hT : Qv (puAmalgam h.le) (baseB _) ≤ Subgroup.centralizer
      ((Uloc h.le L (baseA _) ⊓ Subgroup.centralizer (E : Set _) : Subgroup _) : Set _)) :
    T ≤ L ⊔ pCoreOf 2 M := by
  have hEM : E ≤ imM h.le M :=
    hEβ.trans (by rw [puAmalgam.qv_baseB]; exact imM_mono h.le h.le)
  have himE : imM h.le (S33.pre h.le E) = E := S33.imM_pre h.le hEM
  have hE₀T : S33.pre h.le E ≤ T := Core.pre_le_of_le_qv_baseB h hEβ
  have hE₀ : S33.pre h.le E ≤ L ⊔ pCoreOf 2 M := by
    intro x hx
    obtain ⟨m, hmE, rfl⟩ := (S33.mem_pre_iff' h.le).mp hx
    have hm := hEf hmE
    rw [S34F.flat, puTrans_baseA h.le (S34F.flat_subgroupOf_normal h)] at hm
    exact (S33.ofA_mem_imM_iff h.le m).mp hm
  set S₀ := Uq M T L ⊓ Subgroup.centralizer (S33.pre h.le E : Set G) with hS₀
  have hS₀M : S₀ ≤ M := inf_le_left.trans (Uq_le h.L_le)
  have himS : imM h.le S₀ ≤
      Uloc h.le L (baseA _) ⊓ Subgroup.centralizer (E : Set (puAmalgam h.le).Universal) := by
    refine le_inf ?_ ?_
    · rw [Uloc, puTrans_baseA h.le (S4A.Uq_normal h)]
      exact imM_mono h.le inf_le_left
    · rw [← himE]
      exact S34E.imM_le_centralizer h inf_le_right
  have hTS : T ≤ Subgroup.centralizer (S₀ : Set G) := by
    refine S34E.le_centralizer_of_imM h h.le hS₀M ?_
    rw [← puAmalgam.qv_baseB]
    exact hT.trans (Subgroup.centralizer_le himS)
  exact le_sup_of_le_centralizer_fix_sp h hU hE₀T hE₀ hTS

end CFSG.Quasithin.MS93.S4L
