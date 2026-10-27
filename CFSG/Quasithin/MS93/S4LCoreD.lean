module

public import CFSG.Quasithin.MS93.S4LCoreC
public import CFSG.Quasithin.MS93.S34FFlat
public import CFSG.Quasithin.MS93.S33SL

public section

namespace CFSG.Quasithin.MS93.S4L.Core

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem inf_centralizer_ne_bot_of_le {P W : Subgroup G} (hP : IsPGroup 2 P) (hWP : W ≤ P)
    (hnorm : P ≤ Subgroup.normalizer (W : Set G)) (hW : W ≠ ⊥) :
    W ⊓ Subgroup.centralizer (P : Set G) ≠ ⊥ := by
  have : Group.IsNilpotent P := hP.isNilpotent
  have hnormal : (W.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnorm
  have hne : W.subgroupOf P ≠ ⊥ := by
    intro h0
    apply hW
    rw [← Subgroup.map_subgroupOf_eq_of_le hWP, h0, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  have hyC : (y : G) ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)
  intro h0
  have hmem : (y : G) ∈ W ⊓ Subgroup.centralizer (P : Set G) := ⟨hy.1, hyC⟩
  rw [h0, Subgroup.mem_bot] at hmem
  exact hy1 (Subtype.ext (Subtype.ext hmem))

section Linear

variable (h : PUHyp M T L) (hU : IsSL3U M T L)
include h hU

theorem le_sup_of_le_centralizer_fix {E₀ : Subgroup G} (hE₀T : E₀ ≤ T)
    (hE₀ : E₀ ≤ L ⊔ pCoreOf 2 M)
    (hT : T ≤ Subgroup.centralizer
      ((Uq M T L ⊓ Subgroup.centralizer (E₀ : Set G) : Subgroup G) : Set G)) :
    T ≤ L ⊔ pCoreOf 2 M := by
  obtain ⟨-, -, n, F, _, _, a, hcard, ha, -, -, β, hβ, hβker, hβα⟩ := hU
  have hMV : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hTV : T ≤ Subgroup.normalizer (Uq M T L : Set G) := h.le.trans hMV
  have hX : L ⊔ pCoreOf 2 M ≤ coordGroup β ⊤ M hMV := by
    refine sup_le (fun l hl => ?_) (fun x hx => ?_)
    · refine ⟨h.L_le hl, ⟨(a ⟨l, hl⟩ : GL (Fin 3) F), Subgroup.mem_top _⟩, ?_⟩
      intro u v huv
      simpa [moduleAct] using hβα ⟨l, hl⟩ u v huv 0
    · exact ⟨pCoreOf_le' M hx, (S34R.pCoreOf_le_linPart h β hx).2⟩
  have hUT : Uq M T L ≤ T := (h.Uq_le_Xq.trans (Xq_le_pCoreOf M)).trans h.pCore_le
  have hne := inf_centralizer_ne_bot_of_le h.isPGroup hUT hTV h.Uq_ne_bot
  obtain ⟨⟨s₀, hs₀U, hs₀C⟩, hs₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hs₀1' : s₀ ≠ 1 := fun he => hs₀1 (Subtype.ext he)
  set x₀ : Fin 3 → F := Multiplicative.toAdd (β ⟨s₀, hs₀U⟩) 0 with hx₀def
  have hx₀ : x₀ ≠ 0 := by
    intro h0
    apply hs₀1'
    have hβ1 : β ⟨s₀, hs₀U⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      rw [Fin.fin_one_eq_zero i]
      exact h0
    have hker : (⟨s₀, hs₀U⟩ : ↥(Uq M T L)) ∈ β.ker := hβ1
    rw [hβker, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hker
    exact hker
  have hscal : ∀ c : F, ∃ u : ↥(Uq M T L), Multiplicative.toAdd (β u) 0 = c • x₀ ∧
      (u : G) ∈ Subgroup.centralizer (E₀ : Set G) := by
    intro c
    obtain ⟨u, hu⟩ := exists_coord_eq hβ (c • x₀)
    refine ⟨u, hu, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    obtain ⟨-, γ, hγ⟩ := hX (hE₀ he)
    have hes : e * s₀ * e⁻¹ = s₀ := by
      have := Subgroup.mem_centralizer_iff.mp hs₀C e (hE₀T he)
      rw [this, mul_inv_cancel_right]
    have hfix : ((γ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x₀ = x₀ := by
      have := hγ ⟨s₀, hs₀U⟩ ⟨s₀, hs₀U⟩ hes.symm
      exact this.symm
    set v : ↥(Uq M T L) := ⟨e * u * e⁻¹, conj_mem_of_mem_normalizer (hMV (h.le (hE₀T he))) u⟩
      with hvdef
    have hv := hγ u v rfl
    rw [hu, Matrix.mulVec_smul, hfix, ← hu] at hv
    have hβv : β v = β u := by
      apply Multiplicative.toAdd.injective
      funext i
      rw [Fin.fin_one_eq_zero i]
      exact hv
    have hvu : v = u := by
      have hk : v * u⁻¹ ∈ β.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hβv, mul_inv_cancel]
      rw [hβker, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at hk
      exact mul_inv_eq_one.mp (Subtype.ext hk)
    have h1 : e * (u : G) * e⁻¹ = u := congrArg Subtype.val hvu
    calc e * (u : G) = e * u * e⁻¹ * e := by group
      _ = u * e := by rw [h1]
  have hbot : ∀ g : G, g ∈ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun g => by
    rw [Subgroup.normalizer_eq_top]
    trivial
  intro t ht
  obtain ⟨f, hf⟩ := S33.exists_isCoordAct' hβ hβker (hTV ht)
  have hfix : ∀ c : F, f (c • x₀) = c • x₀ := by
    intro c
    obtain ⟨u, hu, huC⟩ := hscal c
    have htu : t * (u : G) * t⁻¹ = u := by
      have := Subgroup.mem_centralizer_iff.mp (hT ht) u ⟨u.2, huC⟩
      rw [← this, mul_inv_cancel_right]
    have := hf u u htu.symm
    rw [hu] at this
    exact this.symm
  have hl := S33.linear_of_fix h ha hβ hβker hβα (h.le ht) hf hx₀ hfix
  obtain ⟨γ, hγ⟩ := S34R.exists_gl_of_linear hβ hβker (hTV ht) (hbot t) hf hl
  exact S34D.mem_sup_of_isCoordAct_sl h hcard ha hβ hβker hβα ht hγ

theorem sl3Full_of_qv_le_centralizer {E : Subgroup (puAmalgam h.le).Universal}
    (hEβ : E ≤ Qv (puAmalgam h.le) (baseB _)) (hEf : E ≤ S34F.flat h (baseA _))
    (hT : Qv (puAmalgam h.le) (baseB _) ≤ Subgroup.centralizer
      ((Uloc h.le L (baseA _) ⊓ Subgroup.centralizer (E : Set _) : Subgroup _) : Set _)) :
    IsSL3Full M T L := by
  have hEM : E ≤ imM h.le M :=
    hEβ.trans (by rw [puAmalgam.qv_baseB]; exact imM_mono h.le h.le)
  have himE : imM h.le (S33.pre h.le E) = E := S33.imM_pre h.le hEM
  have hE₀T : S33.pre h.le E ≤ T := pre_le_of_le_qv_baseB h hEβ
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
  exact S34D.sl3Full_of_le_sup h hU (le_sup_of_le_centralizer_fix h hU hE₀T hE₀ hTS)

end Linear

end CFSG.Quasithin.MS93.S4L.Core
