module

public import CFSG.Quasithin.MS93.S34FFlat
public import CFSG.Quasithin.MS93.S34FPar
import CFSG.Quasithin.MS93.S34EAB
import CFSG.Quasithin.MS93.S33LamW

public section

namespace CFSG.Quasithin.MS93.S4L

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G]

theorem isCoordAct_id_of_mem_centralizer {V : Subgroup G} {ι F : Type} [Field F]
    {β : ↥V →* Multiplicative (Fin 1 → ι → F)} {m : G}
    (hm : m ∈ Subgroup.centralizer (V : Set G)) : IsCoordAct β m id := by
  intro u v huv
  have : v = u := by
    apply Subtype.ext
    rw [huv, ← Subgroup.mem_centralizer_iff.mp hm u u.2, mul_inv_cancel_right]
  rw [this]
  rfl

variable [Finite G] {M T L : Subgroup G}

theorem exists_natural_flat_sp (h : PUHyp M T L) {F : Type} [Field F]
    {a : ↥L →* ↥(StatedSp 2 F)} (ha : Function.Surjective a)
    (hnat : IsSumOfNaturalModulesVia L (Uq M T L)
      (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) a false 1) :
    ∃ φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSp 2 F), Function.Surjective φ ∧
      IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L)
        (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) φ false 1 := by
  obtain ⟨hLV, hZV, β, hβ, hβker, hβα⟩ := hnat
  have hQV : pCoreOf 2 M ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    (pCoreOf_le' M).trans (le_normalizer_Uq h.le_normalizer)
  exact exists_natural_of_coordAct (Γ := StatedSp 2 F) (A := L) (M := L ⊔ pCoreOf 2 M)
    (T := pCoreOf 2 M) rfl ha hLV hZV hβ hβker hβα hQV fun t ht =>
      ⟨1, (isCoordAct_id_of_mem_centralizer (S34F.pCoreOf_le_centralizer_Uq h ht)).congr
        fun x => by simp⟩

theorem IsSp4UEven.exists_natural_flat (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L) :
    ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
      (φ : ↥(L ⊔ pCoreOf 2 M) →* ↥(StatedSp 2 F)), 1 ≤ m ∧ Fintype.card F = 4 ^ m ∧
      Function.Surjective φ ∧ IsSumOfNaturalModulesVia (L ⊔ pCoreOf 2 M) (Uq M T L)
        (Uq M T L ⊓ Subgroup.centralizer (L : Set G)) φ false 1 := by
  obtain ⟨m, F, _, _, a, hm, hcard, ha, hnat⟩ := hU
  obtain ⟨φ, hφ, hφnat⟩ := exists_natural_flat_sp h ha hnat
  exact ⟨m, F, inferInstance, inferInstance, φ, hm, hcard, hφ, hφnat⟩

theorem pre_zm_le_flat_sp (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L)
    {μ : Vtx (puAmalgam h.le)} (hcμ : IsCritical (puAmalgam h.le) μ (baseA _))
    (hμβ : geo _ (baseA (puAmalgam h.le)) μ 1 = baseB _) :
    S33.pre h.le (ZM _ μ) ≤ L ⊔ pCoreOf 2 M := by
  obtain ⟨m, F, _, _, a, hm, hcard, ha, hLV, hZV, β, hβ, hβker, hβα⟩ := hU
  have hcard' : Fintype.card F = 2 ^ (2 * m) := by rw [hcard, S34F.four_pow_eq]
  have hF4 : 4 ≤ Fintype.card F := by
    rw [hcard]
    calc 4 = 4 ^ 1 := by norm_num
      _ ≤ 4 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hET := (S34E.pre_zm_le_not_le h hcμ hμβ).1
  have hTV : T ≤ Subgroup.normalizer (Uq M T L : Set G) :=
    h.le.trans (le_normalizer_Uq h.le_normalizer)
  have hTZ : T ≤ Subgroup.normalizer
      ((Uq M T L ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
    h.le.trans (le_normalizer_inf (le_normalizer_Uq h.le_normalizer)
      (le_normalizer_centralizer h.le_normalizer))
  have hβker' : β.ker = (Uq M T L ⊓ Zq M L).subgroupOf (Uq M T L) := by
    rw [h.Uq_inf_Zq]
    exact hβker
  intro e heE
  have heT := hET heE
  obtain ⟨f, hf⟩ := exists_isCoordAct hβ hβker (hTV heT) (hTZ heT)
  have hlin := S33.linear_of_isCritical_sp h ha hβ hβker' (S33.isCoordAct_of_natSp hβα) hcard'
    hF4 hcμ e heE f hf
  obtain ⟨γ₀, hγ₀⟩ := S34R.exists_gl_of_linear hβ hβker (hTV heT) (hTZ heT) hf hlin
  exact S34D.mem_sup_of_isCoordAct_sp h hcard' ha hβ hβker hβα heT hγ₀

theorem zm_le_flat_sp (h : PUHyp M T L) (hU : S34F.IsSp4UEven M T L)
    {μ δ : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) μ δ) :
    ZM _ μ ≤ S34F.flat h δ := by
  obtain ⟨k, hkα, -, hcμ, hμβ⟩ := S33.exists_conj_of_isCritical _ h.hyp20 h.critDist_pos hc
  obtain ⟨-, -, -, -, hEim⟩ := S33.pre_zm_props h hcμ
  have hZ : ZM (puAmalgam h.le) (k⁻¹ • μ) ≤ S34F.flat h (baseA _) := by
    rw [← hEim, S34F.flat, puTrans_baseA h.le (S34F.flat_subgroupOf_normal h)]
    exact imM_mono h.le (pre_zm_le_flat_sp h hU hcμ hμβ)
  have hZμ : ZM (puAmalgam h.le) μ =
      (ZM (puAmalgam h.le) (k⁻¹ • μ)).map (MulAut.conj k).toMonoidHom := by
    rw [← zm_smul, smul_inv_smul]
  rw [hZμ, ← hkα, S34F.flat, puTrans_smul h.le (S34F.flat_subgroupOf_normal h)]
  exact Subgroup.map_mono hZ

theorem qv_inf_centralizer_critR_le_flat_base_sp (h : PUHyp M T L)
    (hU : S34F.IsSp4UEven M T L) {μ : Vtx (puAmalgam h.le)}
    (hcμ : IsCritical (puAmalgam h.le) μ (baseA _))
    (hμβ : geo _ (baseA (puAmalgam h.le)) μ 1 = baseB _) :
    Qv (puAmalgam h.le) (baseB _) ⊓
        Subgroup.centralizer (critR (puAmalgam h.le) μ (baseA _) : Set _) ≤
      S34F.flat h (baseA _) := by
  obtain ⟨m, F, _, _, a, hm, hcard, ha, hLV, hZV, β, hβ, hβker, hβα⟩ := hU
  have hcard' : Fintype.card F = 2 ^ (2 * m) := by rw [hcard, S34F.four_pow_eq]
  have hk : 2 ≤ 2 * m := by omega
  have hET := (S34E.pre_zm_le_not_le h hcμ hμβ).1
  obtain ⟨e, heE, g₀, hg₀, hmv⟩ := S34E.exists_crit_mat_sp h hk hcard' ha hβ hβker hβα hcμ hμβ
  have hRM : ⁅Uq M T L, S33.pre h.le (ZM _ μ)⁆ ≤ M :=
    S33.commutator_le_of_le (Uq_le h.L_le) (S33.pre_le h.le _)
  rintro x ⟨hxT, hxC⟩
  rw [puAmalgam.qv_baseB, imM_of_le h.le le_rfl] at hxT
  obtain ⟨t, -, rfl⟩ := hxT
  rw [← S33.imM_commutator_pre h hcμ hET] at hxC
  have htC := S34E.mem_centralizer_of_ofT h hRM t hxC
  have hlin := S34E.mem_linPart_of_centralizer_sp h ha hβ hβker hβα (hET heE) hg₀ hmv
    (fun u hu => by
      rw [← commutatorElement_inv]
      exact inv_mem (Subgroup.commutator_mem_commutator hu heE)) t.2 htC
  obtain ⟨-, γ, hγ⟩ := hlin
  have hsup := S34D.mem_sup_of_isCoordAct_sp h hcard' ha hβ hβker hβα t.2 hγ
  rw [S34F.flat, puTrans_baseA h.le (S34F.flat_subgroupOf_normal h), S34E.ofT_mem_imM_iff h]
  exact hsup

end CFSG.Quasithin.MS93.S4L
