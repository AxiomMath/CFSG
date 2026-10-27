module

public import CFSG.Quasithin.MS93.S46R468Q2B
public import CFSG.Quasithin.MS93.S46R468Q2A

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem vv_le_qv_of_adj_isMVtx (c : Hyp46 M T L φ) {α β : Vtx (puAmalgam c.pu.le)}
    (hα : IsMVtx (puAmalgam c.pu.le) α) (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) :
    Vv (puAmalgam c.pu.le) α ≤ Qv _ β := by
  rw [vv_eq_iSup_vv hα]
  refine iSup₂_le fun k hαk => vv_le_qv_of_dist_le_two c.b4 ((isMVtx_iff_of_adj _ hαk).mp hα) ?_
  have h1 := dist_triangle (puAmalgam c.pu.le) k α β
  rw [tdist_comm (puAmalgam c.pu.le) k α, dist_eq_one_of_adj _ hαk,
    dist_eq_one_of_adj _ hαβ] at h1
  exact h1

theorem exists_mem_vv_ptQ_of_sup_eq (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) {α β x : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β)
    (hV : Vv (puAmalgam c.pu.le) α ⊔ Qv _ x = Qv _ β) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hP : IsPtOn (puAmalgam c.pu.le) x β P) :
    ∃ y ∈ Vv (puAmalgam c.pu.le) α, y ∈ ptQ (puAmalgam c.pu.le) x P ∧
      y ∉ Qv (puAmalgam c.pu.le) x := by
  have h464' := h464 G M T L F φ c
  obtain ⟨t, ⟨htβ, htP⟩, htx⟩ := exists_mem_qv_inf_ptQ h464 h465 h466a c hx hxβ hP
  have hVs : Vv (puAmalgam c.pu.le) α ≤ stab _ x :=
    (le_sup_left.trans hV.le).trans (qv_le_stab_of_adj _ hxβ.symm)
  have hn : Vv (puAmalgam c.pu.le) α ≤ Subgroup.normalizer (Qv (puAmalgam c.pu.le) x : Set _) :=
    hVs.trans (stab_le_normalizer_qv _ x)
  rw [← hV] at htβ
  have hmem := (Subgroup.coe_mul_of_left_le_normalizer_right _ _ hn) ▸ (SetLike.mem_coe.mpr htβ)
  obtain ⟨v, hv, q, hq, rfl⟩ := Set.mem_mul.mp hmem
  have hPZ : P ≤ ZM (puAmalgam c.pu.le) x := by
    obtain ⟨β', -, -, hPe⟩ := hP
    exact hPe ▸ inf_le_left.trans ((h464' x β hx hxβ).trans (zh_le_zm _ hxβ))
  have hqP : q ∈ ptQ (puAmalgam c.pu.le) x P := qv_le_ptQ c hx hPZ hq
  refine ⟨v, hv, ?_, fun hvx => htx (Subgroup.mul_mem _ hvx hq)⟩
  have : v = v * q * q⁻¹ := by group
  rw [this]
  exact Subgroup.mul_mem _ htP (Subgroup.inv_mem _ hqP)

theorem mem_or_inv_mul_mem_of_relIndex_two {𝔾 : Type*} [Group 𝔾] {H K : Subgroup 𝔾}
    (h2 : H.relIndex K = 2) {k₀ k : 𝔾} (hk₀ : k₀ ∈ K) (hk₀H : k₀ ∉ H) (hk : k ∈ K) :
    k ∈ H ∨ k₀⁻¹ * k ∈ H := by
  have hi : (H.subgroupOf K).index = 2 := h2
  have h := Subgroup.mul_mem_iff_of_index_two hi (a := (⟨k₀, hk₀⟩ : K)⁻¹) (b := ⟨k, hk⟩)
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
    Subgroup.inv_mem_iff] at h
  by_cases hkH : k ∈ H
  · exact Or.inl hkH
  · exact Or.inr (h.mpr (iff_of_false hk₀H hkH))

theorem commute_zm_pencil_of_root_elts (h463 : I463) (h464 : I464) (h465 : I465)
    (h466a : I466a) (c : Hyp46 M T L φ) (hq : Fintype.card F = 2)
    {α β x : Vtx (puAmalgam c.pu.le)} (hα : IsMVtx (puAmalgam c.pu.le) α)
    (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β)
    (hbad : ∀ μ A, (puAmalgam c.pu.le).treeGraph.Adj x μ → IsPtOn (puAmalgam c.pu.le) x μ A →
      ¬ ⁅Vv (puAmalgam c.pu.le) μ, ptQ _ x A⁆ ≤ bzero c x)
    {A B : Subgroup (puAmalgam c.pu.le).Universal} (hA : IsPtOn (puAmalgam c.pu.le) x β A)
    (hB : IsPtOn (puAmalgam c.pu.le) x β B) (hAB : A ≠ B) {yA yB : (puAmalgam c.pu.le).Universal}
    (hyAV : yA ∈ Vv (puAmalgam c.pu.le) α) (hyAP : yA ∈ ptQ (puAmalgam c.pu.le) x A)
    (hyAx : yA ∉ Qv (puAmalgam c.pu.le) x) (hyBV : yB ∈ Vv (puAmalgam c.pu.le) α)
    (hyBP : yB ∈ ptQ (puAmalgam c.pu.le) x B) (hyBx : yB ∉ Qv (puAmalgam c.pu.le) x) :
    ∀ u ∈ pencil (puAmalgam c.pu.le) x A, ∀ z ∈ ZM (puAmalgam c.pu.le) α, z * u = u * z := by
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  have hyAβ : yA ∈ Qv (puAmalgam c.pu.le) β := vv_le_qv_of_adj_isMVtx c hα hαβ hyAV
  have hyBβ : yB ∈ Qv (puAmalgam c.pu.le) β := vv_le_qv_of_adj_isMVtx c hα hαβ hyBV
  have hAc : Nat.card A = 2 := by rw [card_of_isPtOn h464 h465 c hx hxβ hA, hq]
  obtain ⟨μ, hxμ, hneμ, hAe⟩ := hA
  have hAμ : A ≤ Usup (puAmalgam c.pu.le) x μ := hAe ▸ inf_le_right
  have hAβ : A ≤ Usup (puAmalgam c.pu.le) x β := hAe ▸ inf_le_left
  have hys : yB ∈ stab (puAmalgam c.pu.le) x := qv_le_stab_of_adj _ hxβ.symm hyBβ
  have hyx : yB • x = x := MulAction.mem_stabilizer_iff.mp hys
  set μ' := yB • μ with hμ'
  have hxμ' : (puAmalgam c.pu.le).treeGraph.Adj x μ' := by
    have := (adj_smul _ yB x μ).mpr hxμ
    rwa [hyx] at this
  have hUμ' : Usup (puAmalgam c.pu.le) x μ' =
      (Usup (puAmalgam c.pu.le) x μ).map (MulAut.conj yB).toMonoidHom := by
    rw [hμ', ← usup_smul, hyx]
  have hVμ' : Vv (puAmalgam c.pu.le) μ' =
      (Vv (puAmalgam c.pu.le) μ).map (MulAut.conj yB).toMonoidHom := vi_smul _ yB μ 2
  have hne' : Usup (puAmalgam c.pu.le) x μ' ≠ Usup _ x μ :=
    usup_smul_ne h464 h465 c hx hxβ hxμ (Ne.symm hneμ) hB (by rw [← hAe]; exact Ne.symm hAB)
      hyBβ hyBP hyBx
  have hAμ' : A ≤ Usup (puAmalgam c.pu.le) x μ' := by
    intro a ha
    rw [hUμ']
    have hca : yB * a = a * yB := Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ β
      ((h464 G M T L F φ c x β hx hxβ) (hAβ ha))) yB hyBβ
    refine ⟨a, hAμ ha, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hca, mul_assoc, mul_inv_cancel, mul_one]
  have hcμμ' := card_usup_inf_usup h464 h465 c hx hxμ hxμ' (Ne.symm hne')
  have : Finite ↥(Usup (puAmalgam c.pu.le) x μ ⊓ Usup _ x μ') :=
    Nat.finite_of_card_ne_zero (by rw [hcμμ']; exact Fintype.card_ne_zero)
  have hAe' : A = Usup (puAmalgam c.pu.le) x μ ⊓ Usup _ x μ' :=
    Subgroup.eq_of_le_of_card_ge (le_inf hAμ hAμ') (by rw [hcμμ', hAc, hq])
  have hO : ⁅Vv (puAmalgam c.pu.le) μ, ptQ _ x A⁆ ≤
      Subgroup.centralizer (pencil (puAmalgam c.pu.le) x A : Set _) :=
    commutator_vv_ptQ_le_centralizer_pencil h464 h465 h466a c hq hx hxμ hAμ hAc
  have hO' : ⁅Vv (puAmalgam c.pu.le) μ', ptQ _ x A⁆ ≤
      Subgroup.centralizer (pencil (puAmalgam c.pu.le) x A : Set _) :=
    commutator_vv_ptQ_le_centralizer_pencil h464 h465 h466a c hq hx hxμ' hAμ' hAc
  have hnμ : yA ∈ Subgroup.normalizer (Vv (puAmalgam c.pu.le) μ : Set _) :=
    ptQ_le_normalizer_vv h464 h465 h466a c hx hxμ hAμ hyAP
  have hnμ' : yA ∈ Subgroup.normalizer (Vv (puAmalgam c.pu.le) μ' : Set _) :=
    ptQ_le_normalizer_vv h464 h465 h466a c hx hxμ' hAμ' hyAP
  have hVαn : Vv (puAmalgam c.pu.le) x ≤ Subgroup.normalizer (Vv (puAmalgam c.pu.le) α : Set _) :=
    ((vv_le_qv_of_adj_isMVtx c hx hxβ).trans (qv_le_stab_of_adj _ hαβ.symm)).trans
      (stab_le_normalizer_of_smul _ (fun g δ => vi_smul _ g δ 2) α)
  have key : ∀ w ∈ Vv (puAmalgam c.pu.le) μ,
      ⁅⁅w, yB⁆, yA⁆ ∈ ZM (puAmalgam c.pu.le) α ∧
      ⁅⁅w, yB⁆, yA⁆ ∈ Subgroup.centralizer (pencil (puAmalgam c.pu.le) x A : Set _) ∧
      yB * w⁻¹ * yB⁻¹ ∈ Vv (puAmalgam c.pu.le) μ' ∧
      ⁅⁅w, yB⁆, yA⁆ = ⁅yB * w⁻¹ * yB⁻¹, yA⁆ * ⁅w, yA⁆ := by
    intro w hw
    have hv₂ : yB * w⁻¹ * yB⁻¹ ∈ Vv (puAmalgam c.pu.le) μ' := by
      rw [hVμ']; exact ⟨w⁻¹, Subgroup.inv_mem _ hw, rfl⟩
    have hk₁ : ⁅w, yA⁆ ∈ Subgroup.centralizer (pencil (puAmalgam c.pu.le) x A : Set _) :=
      hO (Subgroup.commutator_mem_commutator hw hyAP)
    have hk₂ : ⁅yB * w⁻¹ * yB⁻¹, yA⁆ ∈
        Subgroup.centralizer (pencil (puAmalgam c.pu.le) x A : Set _) :=
      hO' (Subgroup.commutator_mem_commutator hv₂ hyAP)
    have hwY : w ∈ pencil (puAmalgam c.pu.le) x A := vv_le_pencil hxμ hAμ hw
    have hcomm : w * ⁅yB * w⁻¹ * yB⁻¹, yA⁆ = ⁅yB * w⁻¹ * yB⁻¹, yA⁆ * w :=
      Subgroup.mem_centralizer_iff.mp hk₂ w hwY
    have he : ⁅⁅w, yB⁆, yA⁆ = ⁅yB * w⁻¹ * yB⁻¹, yA⁆ * ⁅w, yA⁆ := by
      have e1 : ⁅⁅w, yB⁆, yA⁆ =
          w * ⁅yB * w⁻¹ * yB⁻¹, yA⁆ * w⁻¹ * ⁅w, yA⁆ := by
        simp only [commutatorElement_def]; group
      rw [e1, hcomm, mul_assoc _ w w⁻¹, mul_inv_cancel, mul_one]
    refine ⟨?_, ?_, hv₂, he⟩
    · have hwV : w ∈ Vv (puAmalgam c.pu.le) x := I466b.vv_le_vv_of_adj c.pu hx hxμ hw
      have h1 : ⁅w, yB⁆ ∈ Vv (puAmalgam c.pu.le) α := by
        have e : ⁅w, yB⁆ = (w * yB * w⁻¹) * yB⁻¹ := by rw [commutatorElement_def]
        rw [e]
        exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hVαn hwV) yB).mp hyBV)
          (Subgroup.inv_mem _ hyBV)
      exact (h463 G M T L F φ c α hα).2 (Subgroup.commutator_mem_commutator h1 hyAV)
    · rw [he]; exact Subgroup.mul_mem _ hk₂ hk₁
  by_cases hcase : ∃ w ∈ Vv (puAmalgam c.pu.le) μ, ⁅⁅w, yB⁆, yA⁆ ∉ ZM (puAmalgam c.pu.le) x
  · obtain ⟨w, hw, hwx⟩ := hcase
    obtain ⟨hcα, hcY, -, -⟩ := key w hw
    have hcβ : ⁅⁅w, yB⁆, yA⁆ ∉ ZH (puAmalgam c.pu.le) β := fun h => hwx (zh_le_zm _ hxβ h)
    have h2 : (ZH (puAmalgam c.pu.le) β).relIndex (ZM _ α) = 2 := by
      rw [(h465 G M T L F φ c α β hα hαβ).2.1, hq]
    intro u hu z hz
    have huT : u ∈ Qv (puAmalgam c.pu.le) β := pencil_le_qv c hx hxβ A hu
    have hZβ : ∀ z' ∈ ZH (puAmalgam c.pu.le) β, z' * u = u * z' := fun z' hz' =>
      (Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ β hz') u huT).symm
    have hcu : ⁅⁅w, yB⁆, yA⁆ * u = u * ⁅⁅w, yB⁆, yA⁆ :=
      (Subgroup.mem_centralizer_iff.mp hcY u hu).symm
    rcases mem_or_inv_mul_mem_of_relIndex_two h2 hcα hcβ hz with hzβ | hzβ
    · exact hZβ z hzβ
    · have e : z = ⁅⁅w, yB⁆, yA⁆ * (⁅⁅w, yB⁆, yA⁆⁻¹ * z) := by group
      rw [e, mul_assoc, hZβ _ hzβ, ← mul_assoc, hcu, mul_assoc]
  · push Not at hcase
    exfalso
    have hBz : ∀ w ∈ Vv (puAmalgam c.pu.le) μ, ⁅w, yA⁆ ∈ bzero c x := by
      intro w hw
      obtain ⟨-, -, hv₂, he⟩ := key w hw
      have hk₁ : ⁅w, yA⁆ ∈ Vv (puAmalgam c.pu.le) μ := by
        have e : ⁅w, yA⁆ = w * (yA * w * yA⁻¹)⁻¹ := by rw [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ hw (Subgroup.inv_mem _
          ((Subgroup.mem_normalizer_iff.mp hnμ w).mp hw))
      have hk₂ : ⁅yB * w⁻¹ * yB⁻¹, yA⁆⁻¹ ∈ Vv (puAmalgam c.pu.le) μ' := by
        refine Subgroup.inv_mem _ ?_
        have e : ⁅yB * w⁻¹ * yB⁻¹, yA⁆ =
            (yB * w⁻¹ * yB⁻¹) * (yA * (yB * w⁻¹ * yB⁻¹) * yA⁻¹)⁻¹ := by
          rw [commutatorElement_def]; group
        rw [e]
        exact Subgroup.mul_mem _ hv₂ (Subgroup.inv_mem _
          ((Subgroup.mem_normalizer_iff.mp hnμ' _).mp hv₂))
      refine mem_bzero_of_mem_vv_mul h464 h465 c hq hx hxμ hxμ' (Ne.symm hne') hk₁ hk₂
        (zm_le_bzero c hx (hcase w hw)) (by rw [he]; group) fun k hxk hk v hv => ?_
      rw [← hAe'] at hk
      have hc1 : ⁅⁅w, yA⁆, v⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_centralizer_iff.mp (hO (Subgroup.commutator_mem_commutator hw hyAP))
          v (vv_le_pencil hxk hk hv)).symm
      rw [hc1]
      exact Subgroup.one_mem _
    have hle := commutator_vv_ptQ_le_bzero_of h464 h465 h466a c hq hx hxβ hxμ (Ne.symm hneμ)
      hyAβ (by rw [← hAe]; exact hyAP) hyAx hBz
    rw [← hAe] at hle
    exact hbad μ A hxμ ⟨β, hxβ, Ne.symm hneμ, by rw [hAe, inf_comm]⟩ hle

theorem exists_pencil_of_three (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    (hq : Fintype.card F = 2) {β x : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β)
    {P₁ P₂ P₃ : Subgroup (puAmalgam c.pu.le).Universal} (h₁ : IsPtOn (puAmalgam c.pu.le) x β P₁)
    (h₂ : IsPtOn (puAmalgam c.pu.le) x β P₂) (h₃ : IsPtOn (puAmalgam c.pu.le) x β P₃)
    (n₁₂ : P₁ ≠ P₂) (n₁₃ : P₁ ≠ P₃) (n₂₃ : P₂ ≠ P₃) {k : Vtx (puAmalgam c.pu.le)}
    (hxk : (puAmalgam c.pu.le).treeGraph.Adj x k) :
    Vv (puAmalgam c.pu.le) k ≤ pencil _ x P₁ ∨ Vv (puAmalgam c.pu.le) k ≤ pencil _ x P₂ ∨
      Vv (puAmalgam c.pu.le) k ≤ pencil _ x P₃ := by
  by_cases he : Usup (puAmalgam c.pu.le) x k = Usup _ x β
  · left
    obtain ⟨_, _, _, hPe⟩ := h₁
    exact vv_le_pencil hxk (by rw [he, hPe]; exact inf_le_left)
  · have hP : IsPtOn (puAmalgam c.pu.le) x β (Usup _ x β ⊓ Usup _ x k) := ⟨k, hxk, he, rfl⟩
    rcases eq_of_isPtOn_three h464 h465 c hq hx hxβ h₁ h₂ h₃ hP n₁₂ n₁₃ n₂₃ with h | h | h
    · exact Or.inl (vv_le_pencil hxk (h ▸ inf_le_right))
    · exact Or.inr (Or.inl (vv_le_pencil hxk (h ▸ inf_le_right)))
    · exact Or.inr (Or.inr (vv_le_pencil hxk (h ▸ inf_le_right)))

theorem zm_le_centralizer_vv_of_three (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    (hq : Fintype.card F = 2) {β x : Vtx (puAmalgam c.pu.le)}
    (hx : IsMVtx (puAmalgam c.pu.le) x) (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β)
    {P₁ P₂ P₃ : Subgroup (puAmalgam c.pu.le).Universal} (h₁ : IsPtOn (puAmalgam c.pu.le) x β P₁)
    (h₂ : IsPtOn (puAmalgam c.pu.le) x β P₂) (h₃ : IsPtOn (puAmalgam c.pu.le) x β P₃)
    (n₁₂ : P₁ ≠ P₂) (n₁₃ : P₁ ≠ P₃) (n₂₃ : P₂ ≠ P₃) {S : Subgroup (puAmalgam c.pu.le).Universal}
    (hS : ∀ P ∈ ({P₁, P₂, P₃} : Set (Subgroup (puAmalgam c.pu.le).Universal)),
      pencil (puAmalgam c.pu.le) x P ≤ Subgroup.centralizer (S : Set _)) :
    Vv (puAmalgam c.pu.le) x ≤ Subgroup.centralizer (S : Set _) := by
  rw [vv_eq_iSup_vv hx]
  refine iSup₂_le fun k hxk => ?_
  rcases exists_pencil_of_three h464 h465 c hq hx hxβ h₁ h₂ h₃ n₁₂ n₁₃ n₂₃ hxk with h | h | h
  · exact h.trans (hS P₁ (by simp))
  · exact h.trans (hS P₂ (by simp))
  · exact h.trans (hS P₃ (by simp))

theorem zm_le_centralizer_vv_of_sup_eq (h463 : I463) (h464 : I464) (h465 : I465)
    (h466a : I466a) (c : Hyp46 M T L φ) (hq : Fintype.card F = 2)
    {α β x : Vtx (puAmalgam c.pu.le)} (hα : IsMVtx (puAmalgam c.pu.le) α)
    (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) (hx : IsMVtx (puAmalgam c.pu.le) x)
    (hxβ : (puAmalgam c.pu.le).treeGraph.Adj x β)
    (hbad : ∀ μ A, (puAmalgam c.pu.le).treeGraph.Adj x μ → IsPtOn (puAmalgam c.pu.le) x μ A →
      ¬ ⁅Vv (puAmalgam c.pu.le) μ, ptQ _ x A⁆ ≤ bzero c x)
    (hV : Vv (puAmalgam c.pu.le) α ⊔ Qv _ x = Qv _ β) :
    Vv (puAmalgam c.pu.le) x ≤ Subgroup.centralizer (ZM (puAmalgam c.pu.le) α : Set _) := by
  obtain ⟨P₁, P₂, P₃, h₁, h₂, h₃, n₁₂, n₁₃, n₂₃⟩ := exists_three_isPtOn h464 h465 c hx hxβ
  obtain ⟨y₁, hy₁V, hy₁P, hy₁x⟩ := exists_mem_vv_ptQ_of_sup_eq h464 h465 h466a c hx hxβ hV h₁
  obtain ⟨y₂, hy₂V, hy₂P, hy₂x⟩ := exists_mem_vv_ptQ_of_sup_eq h464 h465 h466a c hx hxβ hV h₂
  obtain ⟨y₃, hy₃V, hy₃P, hy₃x⟩ := exists_mem_vv_ptQ_of_sup_eq h464 h465 h466a c hx hxβ hV h₃
  have hpen : ∀ {A B : Subgroup (puAmalgam c.pu.le).Universal} {yA yB},
      IsPtOn (puAmalgam c.pu.le) x β A → IsPtOn (puAmalgam c.pu.le) x β B → A ≠ B →
      yA ∈ Vv (puAmalgam c.pu.le) α → yA ∈ ptQ (puAmalgam c.pu.le) x A →
      yA ∉ Qv (puAmalgam c.pu.le) x → yB ∈ Vv (puAmalgam c.pu.le) α →
      yB ∈ ptQ (puAmalgam c.pu.le) x B → yB ∉ Qv (puAmalgam c.pu.le) x →
      pencil (puAmalgam c.pu.le) x A ≤ Subgroup.centralizer (ZM (puAmalgam c.pu.le) α : Set _) :=
    fun hA hB hAB hyAV hyAP hyAx hyBV hyBP hyBx u hu =>
      Subgroup.mem_centralizer_iff.mpr fun z hz =>
        commute_zm_pencil_of_root_elts h463 h464 h465 h466a c hq hα hαβ hx hxβ hbad hA hB hAB
          hyAV hyAP hyAx hyBV hyBP hyBx u hu z hz
  refine zm_le_centralizer_vv_of_three h464 h465 c hq hx hxβ h₁ h₂ h₃ n₁₂ n₁₃ n₂₃ ?_
  intro P hP
  rcases hP with rfl | rfl | rfl
  · exact hpen h₁ h₂ n₁₂ hy₁V hy₁P hy₁x hy₂V hy₂P hy₂x
  · exact hpen h₂ h₁ (Ne.symm n₁₂) hy₂V hy₂P hy₂x hy₁V hy₁P hy₁x
  · exact hpen h₃ h₁ (Ne.symm n₁₃) hy₃V hy₃P hy₃x hy₁V hy₁P hy₁x

end CFSG.Quasithin.MS93.S46R
