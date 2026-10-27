module

public import CFSG.Quasithin.MS93.S512NAm
public import CFSG.Quasithin.MS93.S310MV

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S512N

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem le_relIndex_qv_zm (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {μ γ : Vtx (puAmalgam h.le)} (hc : IsCritical _ μ γ) :
    2 ^ k ≤ (Qv _ γ).relIndex (ZM _ μ) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hμ : IsMVtx _ μ := hc.1
  have hγ : IsMVtx _ γ := hc.isMVtx_right _ hyp
  have hc' : IsCritical _ γ μ := ms22_iii _ hyp hb0 h.centHyp hc
  have hZγμ : ZM _ γ ≤ stab _ μ := zm_le_stab_of_isCritical _ hyp hb0 hc
  have hb2 := two_le_critDist _ hyp hb0
  have hdist : (puAmalgam h.le).treeGraph.dist μ γ = critDist (puAmalgam h.le) := hc.2.1
  obtain ⟨ν, hν⟩ : ∃ ν, ν = geo _ γ μ 1 := ⟨_, rfl⟩
  have hγν : (puAmalgam h.le).treeGraph.Adj γ ν := by
    rw [hν]
    exact adj_geo_one _ (by rw [SimpleGraph.dist_comm, hdist]; omega)
  have hνM : ¬ IsMVtx _ ν := (isMVtx_iff_of_adj _ hγν).1 hγ
  have hZγν : ZM _ γ ≤ Qv _ ν := (zm_le_qv_self _ hγ hb0).trans (qv_le_qv _ hyp hγ hγν)
  have hdμν : (puAmalgam h.le).treeGraph.dist μ ν < critDist (puAmalgam h.le) := by
    have h1 := dist_geo_right (puAmalgam h.le) (u := γ) (w := μ) (i := 1)
      (by rw [SimpleGraph.dist_comm, hdist]; omega)
    rw [SimpleGraph.dist_comm] at h1
    rw [hν, h1, SimpleGraph.dist_comm, hdist]
    omega
  have hZμν : ZM _ μ ≤ Qv _ ν := zm_le_qv_of_dist_lt _ hμ hdμν
  have hZγ2 : IsPGroup 2 (ZM _ γ) := (isPGroup_qv _ hyp hνM).to_le hZγν
  have := S310.finite_stab_of_isMVtx h hμ
  have : Finite ↥(ZM (puAmalgam h.le) μ) :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      ((zm_le_qv_self _ hμ hb0).trans (qv_le_stab _ _)))
  have h1 := S5B.le_relIndex_centralizer h hd hμ hZγμ hZγ2 hc'.2.2
  have h2 : (Subgroup.centralizer (ZM _ γ : Set (puAmalgam h.le).Universal)).relIndex
        (S5.uSub h.le L μ) ≤
      (Subgroup.centralizer (ZM _ γ : Set (puAmalgam h.le).Universal)).relIndex (ZM _ μ) :=
    Subgroup.relIndex_le_of_le_right (S5B.uSub_le_zm h.le μ) Subgroup.FiniteIndex.index_ne_zero
  have h3 : Subgroup.centralizer (ZM _ γ : Set (puAmalgam h.le).Universal) ⊓ ZM _ μ =
      Qv _ γ ⊓ ZM _ μ := by
    ext z
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hzc, hz⟩
      rw [← h.centHyp γ ν hγ hγν]
      exact ⟨⟨hZμν hz, hzc⟩, hz⟩
    · rintro ⟨hzQ, hz⟩
      refine ⟨Subgroup.mem_centralizer_iff.2 fun w hw => ?_, hz⟩
      exact ((Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hγ hw)) z hzQ).symm
  rw [← Subgroup.inf_relIndex_right, ← h3, Subgroup.inf_relIndex_right]
  exact h1.trans h2

omit [Finite G] in
theorem nclStab_map_conj_of_mem {A B : Type} {C : Type} [Group A] [Group C] [Group B]
    {X : GoldAmalgam A C B} {δ : Vtx X} {y : X.Universal} (hy : y ∈ stab X δ)
    (K : Subgroup X.Universal) :
    S5.nclStab X δ (K.map (MulAut.conj y).toMonoidHom) = S5.nclStab X δ K := by
  have h1 := S5B.nclStab_smul X y δ K
  rw [(mem_stab _).1 hy] at h1
  rw [h1, map_conj_eq_of_mem_normalizer (S310.stab_le_normalizer_nclStab X δ K hy)]

omit [Finite G] in
theorem le_nclStab {A B : Type} {C : Type} [Group A] [Group C] [Group B]
    (X : GoldAmalgam A C B) (δ : Vtx X) (K : Subgroup X.Universal) : K ≤ S5.nclStab X δ K := by
  have := le_iSup (fun y : ↥(stab X δ) => K.map (MulAut.conj (y : X.Universal)).toMonoidHom) 1
  rwa [OneMemClass.coe_one, map_conj_one] at this

omit [Finite G] in
theorem commutator_iSup_le {Γ : Type*} [Group Γ] {ι : Sort*} {H : ι → Subgroup Γ}
    {A N : Subgroup Γ} (hN : ∀ i, H i ≤ Subgroup.normalizer (N : Set Γ))
    (h : ∀ i, ⁅H i, A⁆ ≤ N) : ⁅⨆ i, H i, A⁆ ≤ N := by
  let S : Subgroup Γ :=
    { carrier := {y | y ∈ Subgroup.normalizer (N : Set Γ) ∧ ∀ x ∈ A, ⁅y, x⁆ ∈ N}
      one_mem' := ⟨one_mem _, fun x _ => by simp⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
        refine ⟨mul_mem hy₁ hy₂, fun x hx => ?_⟩
        have e : ⁅y₁ * y₂, x⁆ = (y₁ * ⁅y₂, x⁆ * y₁⁻¹) * ⁅y₁, x⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem ((Subgroup.mem_normalizer_iff.1 hy₁ _).1 (h₂ x hx)) (h₁ x hx)
      inv_mem' := by
        rintro y ⟨hy, h₁⟩
        refine ⟨inv_mem hy, fun x hx => ?_⟩
        have e : ⁅y⁻¹, x⁆ = y⁻¹ * ⁅y, x⁆⁻¹ * y := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hy) _).1 (inv_mem (h₁ x hx))
        simpa using this }
  have hS : (⨆ i, H i) ≤ S := iSup_le fun i y hy =>
    ⟨hN i hy, fun x hx => h i (Subgroup.commutator_mem_commutator hy hx)⟩
  rw [Subgroup.commutator_le]
  intro y hy x hx
  exact (hS hy).2 x hx

omit [Finite G] in
theorem inf_eq_of_relIndex_eq {Γ : Type*} [Group Γ] {H K Z : Subgroup Γ} [Finite Z]
    (hHK : H ≤ K) (he : H.relIndex Z = K.relIndex Z) : Z ⊓ H = Z ⊓ K := by
  have hle : H ⊓ Z ≤ K ⊓ Z := inf_le_inf_right _ hHK
  have e1 := Subgroup.relIndex_mul_card (H := H) (K := Z)
  have e2 := Subgroup.relIndex_mul_card (H := K) (K := Z)
  have hne : K.relIndex Z ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hc : Nat.card ↥(H ⊓ Z) = Nat.card ↥(K ⊓ Z) := by
    rw [he] at e1
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) (e1.trans e2.symm)
  have : Finite ↥(K ⊓ Z) := Finite.of_injective _ (Subgroup.inclusion_injective
    (inf_le_right : K ⊓ Z ≤ Z))
  rw [inf_comm Z H, inf_comm Z K]
  exact Subgroup.eq_of_le_of_card_ge hle hc.ge

omit [Finite G] in
theorem inf_eq_of_inf_le_of_relIndex_eq {Γ : Type*} [Group Γ] {H K Z : Subgroup Γ} [Finite Z]
    (hHK : Z ⊓ H ≤ K) (he : H.relIndex Z = K.relIndex Z) : Z ⊓ H = Z ⊓ K := by
  have h1 : (Z ⊓ H).relIndex Z = K.relIndex Z := by rw [Subgroup.inf_relIndex_left, he]
  have := inf_eq_of_relIndex_eq hHK h1
  rwa [← inf_assoc, inf_idem] at this

section Config

variable (h : PUHyp M T L)

theorem finite_zm {ρ : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ) : Finite ↥(ZM (puAmalgam h.le) ρ) :=
  have := S310.finite_stab_of_isMVtx h hρ
  Finite.of_injective _ (Subgroup.inclusion_injective
    ((zm_le_qv_self _ hρ h.critDist_pos).trans (qv_le_stab _ _)))

theorem zm_inf_bSub_eq (hb : 2 < critDist (puAmalgam h.le)) {α δ μ : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) (hδ : IsMVtx _ δ) (hαδ : (puAmalgam h.le).treeGraph.dist α δ = 2)
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ α) (hμ : μ = y • δ)
    (he : (S5.bSub h.le L α).relIndex (ZM _ μ) = (Qv _ δ).relIndex (ZM _ μ)) :
    ZM _ μ ⊓ S5.bSub h.le L α = ZM _ μ ⊓ Qv _ δ := by
  have hμM : IsMVtx _ μ := by rw [hμ]; exact (isMVtx_smul _ y δ).2 hδ
  have := finite_zm h hμM
  refine inf_eq_of_inf_le_of_relIndex_eq ?_ he
  rw [hμ]
  exact inf_bSub_le_qv h hb hα hδ hαδ hy

end Config

end S512N

end CFSG.Quasithin.MS93
