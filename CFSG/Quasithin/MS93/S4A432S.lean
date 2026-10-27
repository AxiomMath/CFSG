module

public import CFSG.Quasithin.MS93.S4AL3
public import CFSG.Quasithin.MS93.S4A431
public import CFSG.Quasithin.MS93.S4ABridge
public import CFSG.Quasithin.MS93.S4AL1

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix Pointwise

section Pt

variable {F : Type} [Field F]

theorem mem_ptLevi_iff {g : SL3 F} :
    g ∈ (ptLevi : Subgroup (SL3 F)) ↔
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = ![1, 0, 0] := by
  constructor
  · intro hg
    have h0 : (![1, 0, 0] : Fin 3 → F) ∈ fixN (ptLevi : Subgroup (SL3 F)) := by
      rw [ptLevi, fixN_ptLevi, mem_pt0]
      simp
    exact h0 g hg
  · exact mem_ptLevi_of_mulVec_e0

theorem conj_mem_ptLevi {k g : SL3 F} (hk : k ∈ (ptStab : Subgroup (SL3 F)))
    (hg : g ∈ (ptLevi : Subgroup (SL3 F))) : k⁻¹ * g * k ∈ (ptLevi : Subgroup (SL3 F)) := by
  rw [mem_ptLevi_iff] at hg ⊢
  rw [mem_ptStab_iff_mulVec_e0] at hk
  have hk0 := eq_smul_e0_of_mem_pt0 hk
  have hc : (((k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) 0 ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hk0
    have := congrArg (fun v => ((k⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) hk0
    simp only [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, Matrix.mulVec_zero] at this
    have h1 := congrFun this 0
    simp at h1
  set c := (((k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0]) 0 with hcdef
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hk0, Matrix.mulVec_smul, Matrix.mulVec_smul,
    hg]
  have hinv : ((k⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] = c⁻¹ • ![1, 0, 0] := by
    have := congrArg (fun v => c⁻¹ • ((k⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) hk0
    simp only [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec, Matrix.mulVec_smul, smul_smul,
      inv_mul_cancel₀ hc, one_smul] at this
    exact this.symm
  rw [hinv, smul_smul, mul_inv_cancel₀ hc, one_smul]

end Pt

section Move

variable {G : Type} [Group G] {K V C : Subgroup G} {F : Type} [Field F]

theorem exists_conjSL_levi {ψ : ↥K →* ↥(StatedSL 3 F)}
    (hV : IsSumOfNaturalModulesVia K V C ψ false 1) {x : G} (hxV : x ∈ V) (hxC : x ∉ C) :
    ∃ s : SL3 F, ∀ k : ↥K, toSL3 (conjSL s ψ) k ∈ (ptLevi : Subgroup (SL3 F)) →
      x⁻¹ * ((k : G) * x * (k : G)⁻¹) ∈ C := by
  obtain ⟨hKV, hCV, β, -, hβk, hβc⟩ := hV
  set v₀ := Multiplicative.toAdd (β ⟨x, hxV⟩) 0 with hv₀
  have hv0 : v₀ ≠ 0 := by
    intro h0
    apply hxC
    have : β ⟨x, hxV⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      fin_cases i
      exact h0
    have hmem : (⟨x, hxV⟩ : ↥V) ∈ β.ker := this
    rw [hβk, Subgroup.mem_subgroupOf] at hmem
    exact hmem
  obtain ⟨g, hg⟩ := exists_mulVec_e0_eq hv0
  refine ⟨g⁻¹, fun k hk => ?_⟩
  rw [toSL3_conjSL, mem_ptLevi_iff] at hk
  have hk' : ((toSL3 ψ k : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v₀ = v₀ := by
    have e1 : g⁻¹ * toSL3 ψ k * g⁻¹⁻¹ = g⁻¹ * (toSL3 ψ k * g) := by group
    rw [e1, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec] at hk
    have e2 := congrArg (fun w => ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ w) hk
    simp only [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel_left] at e2
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hg] at e2
    exact e2
  have hkx : (k : G) * x * (k : G)⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hKV k.2) x).mp hxV
  have h1 := hβc k ⟨x, hxV⟩ ⟨_, hkx⟩ rfl 0
  simp only [moduleAct, Bool.false_eq_true, ite_false] at h1
  rw [← toSL3_mat, hk'] at h1
  have h2 : β (⟨x, hxV⟩⁻¹ * ⟨_, hkx⟩) = 1 := by
    rw [map_mul, map_inv]
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    simp only [toAdd_mul, toAdd_inv, toAdd_one]
    change -(v₀) + Multiplicative.toAdd (β ⟨_, hkx⟩) 0 = 0
    rw [h1, neg_add_cancel]
  have hmem : (⟨x, hxV⟩⁻¹ * ⟨_, hkx⟩ : ↥V) ∈ β.ker := h2
  rw [hβk, Subgroup.mem_subgroupOf] at hmem
  simpa using hmem

end Move

section Vertex

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem card_usup_le_sq {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
    (hφ : IsSL3FullVia M T L φ) {ρ ν : Vtx (puAmalgam h.le)} (hρ : IsMVtx _ ρ)
    (hρν : (puAmalgam h.le).treeGraph.Adj ρ ν) :
    Nat.card ↥(Usup (puAmalgam h.le) ρ ν) ≤ Fintype.card F ^ 2 := by
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  have hνH : ¬ IsMVtx (puAmalgam h.le) ν := by
    rw [← isMVtx_iff_of_adj _ hρν]
    exact hρ
  have hνs : Qv (puAmalgam h.le) ν ≤ stab _ ρ := qv_le_stab_of_adj _ hρν.symm
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc h hφ hρ
  rw [usup_eq_commutator_uloc h hfull hρ hρν, card_commutator_eq hψ hνs,
    ← Nat.card_eq_fintype_card]
  have hT : IsPGroup 2 ↥((Qv (puAmalgam h.le) ν).subgroupOf (stab (puAmalgam h.le) ρ)) :=
    (isPGroup_qv _ h.hyp20 hνH).of_equiv (Subgroup.subgroupOfEquivOfLe hνs).symm
  exact card_commN_le_sq (hT.map _)

theorem uloc_le_of_normal {F : Type} [Field F] [Fintype F] {φ : ↥M →* ↥(StatedSL 3 F)}
    (hφ : IsSL3FullVia M T L φ) {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ)
    {Y : Subgroup (puAmalgam h.le).Universal} (hYZ : Y ≤ ZM (puAmalgam h.le) μ)
    (hYn : stab (puAmalgam h.le) μ ≤ Subgroup.normalizer (Y : Set (puAmalgam h.le).Universal))
    (hYW : ¬ Y ≤ Zloc h.le L μ) : Uloc h.le L μ ≤ Y := by
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hμ
  have hUn : stab (puAmalgam h.le) μ ≤
      Subgroup.normalizer (Uloc h.le L μ : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) μ
  have hZs : ZM (puAmalgam h.le) μ ≤ stab _ μ :=
    (zm_le_qv_self _ hμ h.critDist_pos).trans (qv_le_stab _ μ)
  have hWc := zloc_le_centralizer_stab h hfull hμ
  obtain ⟨y, hyY, hyW⟩ := Set.not_subset.mp hYW
  have hyZ := hYZ hyY
  rw [zm_eq_uloc_sup_zloc h hfull hμ] at hyZ
  have hUW : Uloc h.le L μ ≤ Subgroup.normalizer (Zloc h.le L μ : Set _) :=
    le_normalizer_of_le_centralizer (Subgroup.le_centralizer_iff.mp
      (hWc.trans (Subgroup.centralizer_le ((uloc_le_zm h hfull hμ).trans hZs))))
  have hyZ' : y ∈ ((Uloc h.le L μ ⊔ Zloc h.le L μ : Subgroup _) : Set _) := hyZ
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hUW] at hyZ'
  obtain ⟨u, hu, w, hw, rfl⟩ := hyZ'
  have hu1 : u ≠ 1 := by
    rintro rfl
    exact hyW (by simpa using hw)
  have hv0 : natVec hψ ⟨u, hu⟩ ≠ 0 := by
    intro h0
    apply hu1
    have := natVec_injective hψ (h0.trans (natVec_one hψ).symm)
    exact congrArg Subtype.val this
  obtain ⟨g, hg⟩ : ∃ g : SL3 F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ natVec hψ ⟨u, hu⟩ ≠
      natVec hψ ⟨u, hu⟩ := by
    by_contra hcon
    push Not at hcon
    exact hv0 (eq_zero_of_forall_mulVec_eq hcon)
  obtain ⟨l, rfl⟩ := toSL3_surjective hψs g
  set S : Set (Fin 3 → F) := {v | ∃ x : ↥(Uloc h.le L μ),
    ((x : ↥(Uloc h.le L μ)) : (puAmalgam h.le).Universal) ∈ Y ∧ natVec hψ x = v} with hS
  have hSinv : ∀ g : SL3 F, ∀ v ∈ S, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ S := by
    rintro g _ ⟨x, hxY, rfl⟩
    obtain ⟨k, rfl⟩ := toSL3_surjective hψs g
    have hkx : (k : (puAmalgam h.le).Universal) * x * (k : _)⁻¹ ∈ Uloc h.le L μ :=
      (Subgroup.mem_normalizer_iff.mp (hUn k.2) _).mp x.2
    exact ⟨⟨_, hkx⟩, (Subgroup.mem_normalizer_iff.mp (hYn k.2) _).mp hxY,
      natVec_conj hψ k x ⟨_, hkx⟩ rfl⟩
  have hlu : (l : (puAmalgam h.le).Universal) * u * (l : (puAmalgam h.le).Universal)⁻¹ ∈
      Uloc h.le L μ := (Subgroup.mem_normalizer_iff.mp (hUn l.2) _).mp hu
  set l₀ : (puAmalgam h.le).Universal := (l : (puAmalgam h.le).Universal) with hl₀
  have ht : l₀ * (u * w) * l₀⁻¹ * (u * w)⁻¹ = l₀ * u * l₀⁻¹ * u⁻¹ := by
    have hlw : l₀ * w * l₀⁻¹ = w := by
      rw [show l₀ * w = w * l₀ from Subgroup.mem_centralizer_iff.mp (hWc hw) l₀ l.2]
      group
    calc l₀ * (u * w) * l₀⁻¹ * (u * w)⁻¹ = (l₀ * u * l₀⁻¹) * (l₀ * w * l₀⁻¹) * w⁻¹ * u⁻¹ := by
          group
      _ = (l₀ * u * l₀⁻¹) * w * w⁻¹ * u⁻¹ := by rw [hlw]
      _ = l₀ * u * l₀⁻¹ * u⁻¹ := by group
  have htY : l₀ * u * l₀⁻¹ * u⁻¹ ∈ Y := by
    rw [← ht]
    exact Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hYn l.2) _).mp hyY)
      (Subgroup.inv_mem _ hyY)
  have htU : l₀ * u * l₀⁻¹ * u⁻¹ ∈ Uloc h.le L μ :=
    Subgroup.mul_mem _ hlu (Subgroup.inv_mem _ hu)
  have htv : natVec hψ ⟨_, htU⟩ = ((toSL3 ψ l : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
      natVec hψ ⟨u, hu⟩ - natVec hψ ⟨u, hu⟩ := by
    have e : (⟨_, htU⟩ : ↥(Uloc h.le L μ)) = ⟨_, hlu⟩ * (⟨u, hu⟩ : ↥(Uloc h.le L μ))⁻¹ := rfl
    rw [e, natVec_mul, natVec_inv, natVec_conj hψ l ⟨u, hu⟩ ⟨_, hlu⟩ rfl, sub_eq_add_neg]
  have htS : natVec hψ ⟨_, htU⟩ ∈ S := ⟨⟨_, htU⟩, htY, rfl⟩
  have ht0 : natVec hψ ⟨_, htU⟩ ≠ 0 := by
    rw [htv, sub_ne_zero]
    exact hg
  intro x hx
  by_cases hx0 : natVec hψ ⟨x, hx⟩ = 0
  · have : (⟨x, hx⟩ : ↥(Uloc h.le L μ)) = 1 :=
      natVec_injective hψ (hx0.trans (natVec_one hψ).symm)
    have hx1 : x = 1 := congrArg Subtype.val this
    rw [hx1]
    exact Y.one_mem
  · obtain ⟨x', hx'Y, hx'v⟩ := mem_of_forall_mulVec_mem hSinv htS ht0 hx0
    have : x' = ⟨x, hx⟩ := natVec_injective hψ hx'v
    have hx' : ((x' : ↥(Uloc h.le L μ)) : (puAmalgam h.le).Universal) = x := by rw [this]
    rw [← hx']
    exact hx'Y

theorem commutator_le_line_of_levi {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) {μ : Vtx (puAmalgam h.le)}
    (hμ : IsMVtx _ μ) (hb : 2 < critDist (puAmalgam h.le))
    (hVQ : ⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ≤ ZM (puAmalgam h.le) μ)
    {ψ' : ↥(stab (puAmalgam h.le) μ) →* ↥(StatedSL 3 F)} (hψ's : Function.Surjective ψ')
    (hψ' : IsSumOfNaturalModulesVia (stab _ μ) (Uloc h.le L μ) ⊥ ψ' false 1)
    {x : (puAmalgam h.le).Universal} (hxV : x ∈ Vv (puAmalgam h.le) μ)
    (hF1 : ∀ k : ↥(stab (puAmalgam h.le) μ), toSL3 ψ' k ∈ (ptLevi : Subgroup (SL3 F)) →
      x⁻¹ * ((k : (puAmalgam h.le).Universal) * x * (k : (puAmalgam h.le).Universal)⁻¹) ∈
        ZM (puAmalgam h.le) μ)
    {R' : Subgroup (puAmalgam h.le).Universal} [Finite ↥R']
    (hxR : ∀ y ∈ Qv (puAmalgam h.le) μ, ⁅x, y⁆ ∈ R') (hR : Nat.card ↥R' < Fintype.card F ^ 3) :
    ∃ S₀ : Subgroup (puAmalgam h.le).Universal, S₀ ≤ Uloc h.le L μ ∧
      Nat.card ↥S₀ = Fintype.card F ∧
      (∀ k : ↥(stab (puAmalgam h.le) μ), toSL3 ψ' k ∈ (ptStab : Subgroup (SL3 F)) →
        ∀ u ∈ S₀, (k : (puAmalgam h.le).Universal) * u * (k : (puAmalgam h.le).Universal)⁻¹ ∈ S₀) ∧
      ∀ y ∈ Qv (puAmalgam h.le) μ, ⁅x, y⁆ ∈ S₀ ⊔ Zloc h.le L μ := by
  classical
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨n, hn⟩ := hφ.1
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hn]
  have : CharP F 2 := FFC.charP_two_of_card_pow hFn
  have hUn : stab (puAmalgam h.le) μ ≤
      Subgroup.normalizer (Uloc h.le L μ : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) μ
  have hZs : ZM (puAmalgam h.le) μ ≤ stab _ μ :=
    (zm_le_qv_self _ hμ hb0).trans (qv_le_stab _ μ)
  have hQs : Qv (puAmalgam h.le) μ ≤ stab _ μ := qv_le_stab _ μ
  have hVs : Vv (puAmalgam h.le) μ ≤ stab _ μ := (vv_le_qv h hb hμ).trans hQs
  have hWc := zloc_le_centralizer_stab h hfull hμ
  have hWn : stab (puAmalgam h.le) μ ≤
      Subgroup.normalizer (Zloc h.le L μ : Set (puAmalgam h.le).Universal) :=
    le_normalizer_of_le_centralizer (Subgroup.le_centralizer_iff.mp hWc)
  have hZcQ : ZM (puAmalgam h.le) μ ≤ Subgroup.centralizer (Qv (puAmalgam h.le) μ : Set _) :=
    zm_le_centralizer_qv _ h20 hμ
  set R₀ : Set (puAmalgam h.le).Universal := {r | ∃ y ∈ Qv (puAmalgam h.le) μ, ⁅x, y⁆ = r}
    with hR₀
  set R := Subgroup.closure R₀ with hRdef
  have hRR' : R ≤ R' := (Subgroup.closure_le _).mpr fun _ ⟨y, hy, hr⟩ => hr ▸ hxR y hy
  have hRZ : R ≤ ZM (puAmalgam h.le) μ := (Subgroup.closure_le _).mpr fun _ ⟨y, hy, hr⟩ =>
    hr ▸ hVQ (Subgroup.commutator_mem_commutator hxV hy)
  have hkR : ∀ k : ↥(stab (puAmalgam h.le) μ), toSL3 ψ' k ∈ (ptLevi : Subgroup (SL3 F)) →
      ∀ r ∈ R, (k : (puAmalgam h.le).Universal) * r * (k : (puAmalgam h.le).Universal)⁻¹ ∈ R := by
    intro k hk r hr
    induction hr using Subgroup.closure_induction with
    | mem r hr =>
      obtain ⟨y, hy, rfl⟩ := hr
      set k₀ : (puAmalgam h.le).Universal := (k : (puAmalgam h.le).Universal)
      have hz := hF1 k hk
      have hy' : k₀ * y * k₀⁻¹ ∈ Qv (puAmalgam h.le) μ :=
        (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_qv _ μ k.2) y).mp hy
      have hzy : ⁅x⁻¹ * (k₀ * x * k₀⁻¹), k₀ * y * k₀⁻¹⁆ = 1 := by
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_centralizer_iff.mp (hZcQ hz) _ hy').symm
      have e : k₀ * ⁅x, y⁆ * k₀⁻¹ = ⁅x, k₀ * y * k₀⁻¹⁆ := by
        have e1 : k₀ * ⁅x, y⁆ * k₀⁻¹ = ⁅k₀ * x * k₀⁻¹, k₀ * y * k₀⁻¹⁆ := by
          simp only [commutatorElement_def]
          group
        have e2 : k₀ * x * k₀⁻¹ = x * (x⁻¹ * (k₀ * x * k₀⁻¹)) := by group
        rw [e1, e2]
        have e3 : ⁅x * (x⁻¹ * (k₀ * x * k₀⁻¹)), k₀ * y * k₀⁻¹⁆ =
            x * ⁅x⁻¹ * (k₀ * x * k₀⁻¹), k₀ * y * k₀⁻¹⁆ * x⁻¹ * ⁅x, k₀ * y * k₀⁻¹⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e3, hzy, mul_one, mul_inv_cancel, one_mul]
      rw [e]
      exact Subgroup.subset_closure ⟨_, hy', rfl⟩
    | one => simp
    | mul a b _ _ ha hb =>
      have : (k : (puAmalgam h.le).Universal) * (a * b) * (k : (puAmalgam h.le).Universal)⁻¹ =
          ((k : (puAmalgam h.le).Universal) * a * (k : (puAmalgam h.le).Universal)⁻¹) *
          ((k : (puAmalgam h.le).Universal) * b * (k : (puAmalgam h.le).Universal)⁻¹) := by group
      rw [this]
      exact R.mul_mem ha hb
    | inv a _ ha =>
      have : (k : (puAmalgam h.le).Universal) * a⁻¹ * (k : (puAmalgam h.le).Universal)⁻¹ =
          ((k : (puAmalgam h.le).Universal) * a * (k : (puAmalgam h.le).Universal)⁻¹)⁻¹ := by
        group
      rw [this]
      exact R.inv_mem ha
  set T := Uloc h.le L μ ⊓ (R ⊔ Zloc h.le L μ) with hTdef
  let Tc : AddSubgroup (Fin 3 → F) :=
    { carrier := {v | ∃ u : ↥(Uloc h.le L μ), (u : (puAmalgam h.le).Universal) ∈ T ∧
        natVec hψ' u = v}
      add_mem' := by
        rintro _ _ ⟨u, hu, rfl⟩ ⟨u', hu', rfl⟩
        exact ⟨u * u', T.mul_mem hu hu', natVec_mul hψ' u u'⟩
      zero_mem' := ⟨1, T.one_mem, natVec_one hψ'⟩
      neg_mem' := by
        rintro _ ⟨u, hu, rfl⟩
        exact ⟨u⁻¹, T.inv_mem hu, natVec_inv hψ' u⟩ }
  have hTc : ∀ g ∈ (ptLevi : Subgroup (SL3 F)), ∀ v ∈ Tc,
      ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ Tc := by
    rintro g hg _ ⟨u, hu, rfl⟩
    obtain ⟨k, rfl⟩ := toSL3_surjective hψ's g
    have hku : (k : (puAmalgam h.le).Universal) * u * (k : (puAmalgam h.le).Universal)⁻¹ ∈
        Uloc h.le L μ := (Subgroup.mem_normalizer_iff.mp (hUn k.2) _).mp u.2
    refine ⟨⟨_, hku⟩, ⟨hku, ?_⟩, (natVec_conj hψ' k u ⟨_, hku⟩ rfl)⟩
    have hRW : ((R ⊔ Zloc h.le L μ : Subgroup _) : Set (puAmalgam h.le).Universal) =
        (R : Set _) * (Zloc h.le L μ : Set _) :=
      Subgroup.coe_mul_of_left_le_normalizer_right R _ ((hRZ.trans hZs).trans hWn)
    have hu2 : (u : (puAmalgam h.le).Universal) ∈
        ((R ⊔ Zloc h.le L μ : Subgroup _) : Set (puAmalgam h.le).Universal) := hu.2
    rw [hRW] at hu2
    obtain ⟨r, hr, w, hw, hrw⟩ := hu2
    have e : (k : (puAmalgam h.le).Universal) * u * (k : (puAmalgam h.le).Universal)⁻¹ =
        ((k : (puAmalgam h.le).Universal) * r * (k : (puAmalgam h.le).Universal)⁻¹) *
        ((k : (puAmalgam h.le).Universal) * w * (k : (puAmalgam h.le).Universal)⁻¹) := by
      rw [← hrw]
      group
    show (k : (puAmalgam h.le).Universal) * u * (k : (puAmalgam h.le).Universal)⁻¹ ∈
      R ⊔ Zloc h.le L μ
    rw [e]
    exact Subgroup.mul_mem_sup (hkR k hg r hr)
      ((Subgroup.mem_normalizer_iff.mp (hWn k.2) w).mp hw)
  have hUW : Uloc h.le L μ ⊓ Zloc h.le L μ = ⊥ := uloc_inf_zloc h hfull μ
  have hfinZ : Finite ↥(ZM (puAmalgam h.le) μ) := by
    obtain ⟨ν, hν⟩ := exists_adj (puAmalgam h.le) μ
    have hνH : ¬ IsMVtx (puAmalgam h.le) ν := by
      rw [← isMVtx_iff_of_adj _ hν]
      exact hμ
    have := finite_qv _ h20 hνH
    exact Finite.of_injective _ (Subgroup.inclusion_injective
      ((zm_le_qv_self _ hμ hb0).trans (qv_le_qv _ h20 hμ hν)))
  have hWZ : Zloc h.le L μ ≤ ZM (puAmalgam h.le) μ := zloc_le_zm h hfull hμ
  have hUZ : Uloc h.le L μ ≤ ZM (puAmalgam h.le) μ := uloc_le_zm h hfull hμ
  have hfinW : Finite ↥(Zloc h.le L μ) := Finite.of_injective _ (Subgroup.inclusion_injective hWZ)
  have hfinR : Finite ↥R := Finite.of_injective _ (Subgroup.inclusion_injective hRZ)
  have hTcard : Nat.card ↥T ≤ Nat.card ↥R := by
    have hTW : T ⊓ Zloc h.le L μ = ⊥ := by
      rw [eq_bot_iff, ← hUW]
      exact inf_le_inf_right _ inf_le_left
    have hcT : Zloc h.le L μ ≤ Subgroup.centralizer (T : Set (puAmalgam h.le).Universal) :=
      hWc.trans (Subgroup.centralizer_le ((inf_le_left.trans hUZ).trans hZs))
    have h1 := card_sup_of_commute hcT hTW
    have hle : T ⊔ Zloc h.le L μ ≤ R ⊔ Zloc h.le L μ := sup_le inf_le_right le_sup_right
    have hfin2 : Finite ↥(R ⊔ Zloc h.le L μ) :=
      Finite.of_injective _ (Subgroup.inclusion_injective (sup_le hRZ hWZ))
    have h2 := Subgroup.card_le_of_le hle
    have hRW : ((R ⊔ Zloc h.le L μ : Subgroup _) : Set (puAmalgam h.le).Universal) =
        (R : Set _) * (Zloc h.le L μ : Set _) :=
      Subgroup.coe_mul_of_left_le_normalizer_right R _ ((hRZ.trans hZs).trans hWn)
    have h3 : Nat.card ↥(R ⊔ Zloc h.le L μ) ≤ Nat.card ↥R * Nat.card ↥(Zloc h.le L μ) := by
      rw [← Nat.card_prod]
      refine Nat.card_le_card_of_surjective (fun p : ↥R × ↥(Zloc h.le L μ) =>
        (⟨(p.1 : (puAmalgam h.le).Universal) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ :
          ↥(R ⊔ Zloc h.le L μ))) ?_
      rintro ⟨z, hz⟩
      have hz' : z ∈ ((R ⊔ Zloc h.le L μ : Subgroup _) : Set (puAmalgam h.le).Universal) := hz
      rw [hRW] at hz'
      obtain ⟨r, hr, w, hw, rfl⟩ := hz'
      exact ⟨(⟨r, hr⟩, ⟨w, hw⟩), rfl⟩
    have hpos : 0 < Nat.card ↥(Zloc h.le L μ) := Nat.card_pos
    rw [h1] at h2
    exact Nat.le_of_mul_le_mul_right (h2.trans h3) hpos
  have hTc0 : ∀ v ∈ Tc, v ∈ pt0 := by
    rcases ptLevi_invariant_cases Tc hTc with hT | hT
    · exact hT
    · exfalso
      have hUT : Uloc h.le L μ ≤ T := by
        intro u hu
        obtain ⟨u', hu'T, hu'v⟩ := hT (natVec hψ' ⟨u, hu⟩)
        have : u' = ⟨u, hu⟩ := natVec_injective hψ' hu'v
        rw [this] at hu'T
        exact hu'T
      have hfinU : Finite ↥(Uloc h.le L μ) :=
        Finite.of_injective _ (Subgroup.inclusion_injective hUZ)
      have hfinT : Finite ↥T := Finite.of_injective _ (Subgroup.inclusion_injective inf_le_left)
      have h1 := Subgroup.card_le_of_le hUT
      have h2 := Subgroup.card_le_of_le hRR'
      rw [card_eq_of_natural hψ', Nat.card_eq_fintype_card (α := F)] at h1
      omega
  let S₀ : Subgroup (puAmalgam h.le).Universal :=
    { carrier := {u | ∃ hu : u ∈ Uloc h.le L μ, natVec hψ' ⟨u, hu⟩ ∈ pt0}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨(Uloc h.le L μ).mul_mem ha hb, ?_⟩
        have : (⟨a * b, (Uloc h.le L μ).mul_mem ha hb⟩ : ↥(Uloc h.le L μ)) =
            ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
        rw [this, natVec_mul]
        exact pt0.add_mem ha' hb'
      one_mem' := by
        refine ⟨(Uloc h.le L μ).one_mem, ?_⟩
        have : (⟨1, (Uloc h.le L μ).one_mem⟩ : ↥(Uloc h.le L μ)) = 1 := rfl
        rw [this, natVec_one]
        exact pt0.zero_mem
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨(Uloc h.le L μ).inv_mem ha, ?_⟩
        have : (⟨a⁻¹, (Uloc h.le L μ).inv_mem ha⟩ : ↥(Uloc h.le L μ)) = (⟨a, ha⟩)⁻¹ := rfl
        rw [this, natVec_inv]
        exact Submodule.neg_mem _ ha' }
  have hS₀U : S₀ ≤ Uloc h.le L μ := fun u hu => hu.1
  refine ⟨S₀, hS₀U, ?_, ?_, ?_⟩
  ·
    rw [← Nat.card_eq_fintype_card (α := F), ← ML3.card_pt0 (F := F)]
    refine Nat.card_congr
      { toFun := fun u => ⟨natVec hψ' ⟨u, u.2.1⟩, u.2.2⟩
        invFun := fun v => ⟨((natVec_surjective hψ' v).choose : _),
          (natVec_surjective hψ' v).choose.2, by
            rw [show (⟨((natVec_surjective hψ' v).choose : _),
              (natVec_surjective hψ' v).choose.2⟩ : ↥(Uloc h.le L μ)) =
                (natVec_surjective hψ' v).choose from rfl,
              (natVec_surjective hψ' v).choose_spec]
            exact v.2⟩
        left_inv := fun u => by
          have := (natVec_surjective hψ' (natVec hψ' ⟨u, u.2.1⟩)).choose_spec
          have h' := natVec_injective hψ' this
          apply Subtype.ext
          simp only
          exact congrArg Subtype.val h'
        right_inv := fun v => by
          apply Subtype.ext
          exact (natVec_surjective hψ' v).choose_spec }
  ·
    rintro k hk u ⟨hu, hu0⟩
    have hku : (k : (puAmalgam h.le).Universal) * u * (k : (puAmalgam h.le).Universal)⁻¹ ∈
        Uloc h.le L μ := (Subgroup.mem_normalizer_iff.mp (hUn k.2) _).mp hu
    refine ⟨hku, ?_⟩
    rw [natVec_conj hψ' k ⟨u, hu⟩ ⟨_, hku⟩ rfl, eq_smul_e0_of_mem_pt0 hu0, Matrix.mulVec_smul]
    exact pt0.smul_mem _ (mem_ptStab_iff_mulVec_e0.mp hk)
  ·
    intro y hy
    have hxy : ⁅x, y⁆ ∈ ZM (puAmalgam h.le) μ := hVQ (Subgroup.commutator_mem_commutator hxV hy)
    have hZset : ((Uloc h.le L μ ⊔ Zloc h.le L μ : Subgroup _) : Set (puAmalgam h.le).Universal) =
        (Uloc h.le L μ : Set _) * (Zloc h.le L μ : Set _) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ ((hUZ.trans hZs).trans hWn)
    have hxy' : ⁅x, y⁆ ∈ ((Uloc h.le L μ ⊔ Zloc h.le L μ : Subgroup _) :
        Set (puAmalgam h.le).Universal) := by
      rw [← zm_eq_uloc_sup_zloc h hfull hμ]
      exact hxy
    rw [hZset] at hxy'
    obtain ⟨u, hu, w, hw, huw⟩ := hxy'
    have huT : u ∈ T := by
      refine ⟨hu, ?_⟩
      have : u = ⁅x, y⁆ * w⁻¹ := by rw [← huw]; group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.subset_closure ⟨y, hy, rfl⟩))
        (Subgroup.mem_sup_right (Subgroup.inv_mem _ hw))
    have hu0 : natVec hψ' ⟨u, hu⟩ ∈ pt0 := hTc0 _ ⟨⟨u, hu⟩, huT, rfl⟩
    rw [← huw]
    exact Subgroup.mul_mem_sup ⟨hu, hu0⟩ hw

theorem linear_of_sameType (h17 : MS17i) (hb : 2 < critDist (puAmalgam h.le))
    {μ : Vtx (puAmalgam h.le)} (hμ : IsMVtx _ μ) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ)
    (hc : IsC1 h.le L (Fintype.card F) μ (Vv (puAmalgam h.le) μ) (ZM (puAmalgam h.le) μ))
    (hVab : ⁅Vv (puAmalgam h.le) μ, Vv (puAmalgam h.le) μ⁆ = ⊥)
    (hVQ : ⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ≤ ZM (puAmalgam h.le) μ)
    {ψ : ↥(stab (puAmalgam h.le) μ) →* ↥(StatedSL 3 F)} (hψs : Function.Surjective ψ)
    (hψ : IsSumOfNaturalModulesVia (stab _ μ) (Uloc h.le L μ) ⊥ ψ false 1)
    (hPK : IsSumOfNaturalModulesVia (stab (puAmalgam h.le) μ)
      (⁅Vv (puAmalgam h.le) μ, stab (puAmalgam h.le) μ⁆ ⊔ ZM (puAmalgam h.le) μ)
      (⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ⊔ ZM (puAmalgam h.le) μ) ψ false 1)
    {ν ρ : Vtx (puAmalgam h.le)} (hμν : (puAmalgam h.le).treeGraph.Adj μ ν)
    (hνρ : (puAmalgam h.le).treeGraph.Adj ν ρ) {x : (puAmalgam h.le).Universal}
    (hxρ : x ∈ ZM (puAmalgam h.le) ρ) (hxV : x ∈ Vv (puAmalgam h.le) μ)
    (hxB : x ∉ Bloc h.le L μ) {y₀ : (puAmalgam h.le).Universal}
    (hy₀ : y₀ ∈ Qv (puAmalgam h.le) μ) (hxy₀ : ⁅x, y₀⁆ ∉ Dloc h.le L μ) :
    ∃ U' : Subgroup (puAmalgam h.le).Universal, x ∈ U' ∧ U' ≤ Vv (puAmalgam h.le) μ ∧
      Uloc h.le L μ ≤ U' ∧
      stab (puAmalgam h.le) μ ≤ Subgroup.normalizer (U' : Set (puAmalgam h.le).Universal) ∧
      ∀ y ∈ Qv (puAmalgam h.le) μ, (∀ u ∈ U', ⁅u, y⁆ ∈ Dloc h.le L μ) ∨
        (∀ u ∈ U', ⁅u, y⁆ ∈ Dloc h.le L μ → u ∈ Bloc h.le L μ) := by
  classical
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  obtain ⟨n, hn⟩ := hφ.1
  have hQs : Qv (puAmalgam h.le) μ ≤ stab _ μ := qv_le_stab _ μ
  have hVs : Vv (puAmalgam h.le) μ ≤ stab _ μ := (vv_le_qv h hb hμ).trans hQs
  have hVn := stab_le_normalizer_vv h μ
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) μ
  have hZs : ZM (puAmalgam h.le) μ ≤ stab _ μ :=
    (zm_le_qv_self _ hμ hb0).trans hQs
  have hBn : stab (puAmalgam h.le) μ ≤
      Subgroup.normalizer (Bloc h.le L μ : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_of_smul (F := fun δ => Bloc h.le L δ) _ (fun g δ => bloc_smul h g δ) μ
  have hDn : stab (puAmalgam h.le) μ ≤
      Subgroup.normalizer (Dloc h.le L μ : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le (S4A.Dq_normal h) μ
  have hUn : stab (puAmalgam h.le) μ ≤
      Subgroup.normalizer (Uloc h.le L μ : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) μ
  have hBV : Bloc h.le L μ ≤ Vv _ μ := bloc_le_vv h μ
  have hDs : Dloc h.le L μ ≤ stab _ μ := puTrans_le_stab h.le _ μ
  have hUZ : Uloc h.le L μ ≤ ZM (puAmalgam h.le) μ := uloc_le_zm h hfull hμ
  have hWD : Zloc h.le L μ ≤ Dloc h.le L μ := zloc_le_dloc h μ
  have hZUD : ZM (puAmalgam h.le) μ ≤ Uloc h.le L μ ⊔ Dloc h.le L μ := by
    rw [zm_eq_uloc_sup_zloc h hfull hμ]
    exact sup_le_sup_left hWD _
  have hρ : IsMVtx (puAmalgam h.le) ρ := by
    have h1 := isMVtx_iff_of_adj _ hμν
    have h2 := isMVtx_iff_of_adj _ hνρ
    tauto
  obtain ⟨-, -, -, -, -, -, -, hPiB, hPB, hBG, -⟩ := isC1_normal h hfull hb hμ hc
  have hK : ⁅Vv (puAmalgam h.le) μ, Qv (puAmalgam h.le) μ⁆ ⊔ ZM (puAmalgam h.le) μ =
      ZM (puAmalgam h.le) μ := sup_eq_right.mpr hVQ
  have hPV : ⁅Vv (puAmalgam h.le) μ, stab (puAmalgam h.le) μ⁆ ⊔ ZM (puAmalgam h.le) μ ≤
      Vv _ μ := sup_le (Subgroup.le_normalizer_iff_commutator_le_left.mp hVn) (zm_le_vv h hμ)
  have hPBn : ⁅Vv (puAmalgam h.le) μ, stab (puAmalgam h.le) μ⁆ ⊔ ZM (puAmalgam h.le) μ ≤
      Subgroup.normalizer (Bloc h.le L μ : Set (puAmalgam h.le).Universal) :=
    (hPV.trans hVs).trans hBn
  have hVBnat : IsSumOfNaturalModulesVia (stab (puAmalgam h.le) μ) (Vv (puAmalgam h.le) μ)
      (Vv (puAmalgam h.le) μ ⊓ Bloc h.le L μ) ψ false 1 :=
    isSumOfNaturalModulesVia_transfer hPK hPB hPiB le_rfl (sup_eq_left.mpr hBV) hVn hBn hPBn
  obtain ⟨s₀, hs₀⟩ := exists_conjSL_levi hVBnat hxV (fun h' => hxB h'.2)
  set ψ' := conjSL s₀ ψ with hψ'def
  have hψ's : Function.Surjective ψ' := conjSL_surjective hψs
  have hψ' := isSumOfNaturalModulesVia_conjSL hψ s₀
  have hPK' := isSumOfNaturalModulesVia_conjSL hPK s₀
  have hF1 : ∀ k : ↥(stab (puAmalgam h.le) μ), toSL3 ψ' k ∈ (ptLevi : Subgroup (SL3 F)) →
      x⁻¹ * ((k : (puAmalgam h.le).Universal) * x * (k : (puAmalgam h.le).Universal)⁻¹) ∈
        ZM (puAmalgam h.le) μ := by
    intro k hk
    have h1 := (hs₀ k hk).2
    have h2 : x⁻¹ * ((k : (puAmalgam h.le).Universal) * x * (k : (puAmalgam h.le).Universal)⁻¹) ∈
        ⁅Vv (puAmalgam h.le) μ, stab (puAmalgam h.le) μ⁆ ⊔ ZM (puAmalgam h.le) μ := by
      refine Subgroup.mem_sup_left ?_
      have e : x⁻¹ * ((k : (puAmalgam h.le).Universal) * x * (k : (puAmalgam h.le).Universal)⁻¹) =
          ⁅x⁻¹, (k : (puAmalgam h.le).Universal)⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hxV) k.2
    rw [← hK, ← hPiB]
    exact ⟨h2, h1⟩
  have hRfin : Finite ↥(Usup (puAmalgam h.le) ρ ν) := by
    have hνH : ¬ IsMVtx (puAmalgam h.le) ν := by
      rw [← isMVtx_iff_of_adj _ hμν]
      exact hμ
    have := finite_qv _ h20 hνH
    have hle : Usup (puAmalgam h.le) ρ ν ≤ Qv _ ν := by
      rw [Usup, zv_of_isMVtx _ hρ]
      exact commutator_le_of_le ((zm_le_qv_self _ hρ hb0).trans (qv_le_qv _ h20 hρ hνρ.symm))
        le_rfl
    exact Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hxR : ∀ y ∈ Qv (puAmalgam h.le) μ, ⁅x, y⁆ ∈ Usup (puAmalgam h.le) ρ ν := by
    intro y hy
    rw [Usup, zv_of_isMVtx _ hρ]
    exact Subgroup.commutator_mem_commutator hxρ (qv_le_qv _ h20 hμ hμν hy)
  have hRq : Nat.card ↥(Usup (puAmalgam h.le) ρ ν) < Fintype.card F ^ 3 := by
    have h1 := card_usup_le_sq h hfull hφ hρ hνρ.symm
    have hq : 1 < Fintype.card F := by
      have := Fintype.one_lt_card (α := F)
      exact this
    have : Fintype.card F ^ 2 < Fintype.card F ^ 3 := Nat.pow_lt_pow_right hq (by norm_num)
    omega
  obtain ⟨S₀, hS₀U, hS₀card, hS₀stab, hxS₀⟩ :=
    commutator_le_line_of_levi h hfull hφ hμ hb hVQ hψ's hψ' hxV hF1 hxR hRq
  set X : Subgroup (puAmalgam h.le).Universal :=
    Subgroup.closure {u | ∃ k : ↥(stab (puAmalgam h.le) μ),
      toSL3 ψ' k ∈ (ptStab : Subgroup (SL3 F)) ∧
        (k : (puAmalgam h.le).Universal) * x * (k : (puAmalgam h.le).Universal)⁻¹ = u}
    with hXdef
  set U' : Subgroup (puAmalgam h.le).Universal :=
    Subgroup.closure {u | ∃ k : ↥(stab (puAmalgam h.le) μ),
      ∃ y ∈ X, (k : (puAmalgam h.le).Universal) * y * (k : (puAmalgam h.le).Universal)⁻¹ = u}
    with hU'def
  have hXV : X ≤ Vv (puAmalgam h.le) μ := by
    rw [hXdef, Subgroup.closure_le]
    rintro _ ⟨k, -, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hVn k.2) x).mp hxV
  have hxX : x ∈ X := Subgroup.subset_closure ⟨1, by simp, by simp⟩
  have hXstab : ∀ k : ↥(stab (puAmalgam h.le) μ), toSL3 ψ' k ∈ (ptStab : Subgroup (SL3 F)) →
      ∀ y ∈ X, (k : (puAmalgam h.le).Universal) * y * (k : (puAmalgam h.le).Universal)⁻¹ ∈ X := by
    intro k hk y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨k', hk', rfl⟩ := hy
      refine Subgroup.subset_closure ⟨k * k', ?_, ?_⟩
      · rw [map_mul]
        exact Subgroup.mul_mem _ hk hk'
      · simp only [Subgroup.coe_mul, mul_inv_rev]
        group
    | one => simp
    | mul a b _ _ ha hb =>
      have e : (k : (puAmalgam h.le).Universal) * (a * b) * (k : (puAmalgam h.le).Universal)⁻¹ =
          ((k : (puAmalgam h.le).Universal) * a * (k : (puAmalgam h.le).Universal)⁻¹) *
          ((k : (puAmalgam h.le).Universal) * b * (k : (puAmalgam h.le).Universal)⁻¹) := by group
      rw [e]
      exact X.mul_mem ha hb
    | inv a _ ha =>
      have e : (k : (puAmalgam h.le).Universal) * a⁻¹ * (k : (puAmalgam h.le).Universal)⁻¹ =
          ((k : (puAmalgam h.le).Universal) * a * (k : (puAmalgam h.le).Universal)⁻¹)⁻¹ := by group
      rw [e]
      exact X.inv_mem ha
  have hXU' : X ≤ U' := fun y hy => Subgroup.subset_closure ⟨1, y, hy, by simp⟩
  have hxU' : x ∈ U' := hXU' hxX
  have hU'V : U' ≤ Vv (puAmalgam h.le) μ := by
    rw [hU'def, Subgroup.closure_le]
    rintro _ ⟨k, y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hVn k.2) y).mp (hXV hy)
  have hU'n : stab (puAmalgam h.le) μ ≤
      Subgroup.normalizer (U' : Set (puAmalgam h.le).Universal) := by
    have key : ∀ g ∈ stab (puAmalgam h.le) μ, ∀ u ∈ U', g * u * g⁻¹ ∈ U' := by
      intro g hg u hu
      induction hu using Subgroup.closure_induction with
      | mem u hu =>
        obtain ⟨k, y, hy, rfl⟩ := hu
        refine Subgroup.subset_closure ⟨⟨g, hg⟩ * k, y, hy, ?_⟩
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group
      | one => simp
      | mul a b _ _ ha hb =>
        have e : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        rw [e]
        exact U'.mul_mem ha hb
      | inv a _ ha =>
        have e : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
        rw [e]
        exact U'.inv_mem ha
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · exact key g hg u
    · intro hu
      have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hu
      simpa [mul_assoc] using this
  have hU'B : U' ⊔ Bloc h.le L μ = Vv (puAmalgam h.le) μ :=
    (isC1_bloc h hfull hb hμ hc).2.2 U' hU'n hU'V (fun hle => hxB (hle hxU'))
  let SZ : Subgroup (puAmalgam h.le).Universal :=
    { carrier := {y | y ∈ Vv (puAmalgam h.le) μ ∧ ∀ k : ↥(stab (puAmalgam h.le) μ),
        toSL3 ψ' k ∈ (ptLevi : Subgroup (SL3 F)) →
          y⁻¹ * ((k : (puAmalgam h.le).Universal) * y * (k : (puAmalgam h.le).Universal)⁻¹) ∈
            ZM (puAmalgam h.le) μ}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Subgroup.mul_mem _ ha hb, fun k hk => ?_⟩
        have e : (a * b)⁻¹ * ((k : (puAmalgam h.le).Universal) * (a * b) *
            (k : (puAmalgam h.le).Universal)⁻¹) =
            b⁻¹ * (a⁻¹ * ((k : (puAmalgam h.le).Universal) * a *
              (k : (puAmalgam h.le).Universal)⁻¹)) * b *
            (b⁻¹ * ((k : (puAmalgam h.le).Universal) * b *
              (k : (puAmalgam h.le).Universal)⁻¹)) := by
          group
        rw [e]
        refine Subgroup.mul_mem _ ?_ (hb' k hk)
        have := (Subgroup.mem_normalizer_iff.mp (hZn (hVs (Subgroup.inv_mem _ hb))) _).mp
          (ha' k hk)
        simpa [mul_assoc] using this
      one_mem' := ⟨Subgroup.one_mem _, fun k _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Subgroup.inv_mem _ ha, fun k hk => ?_⟩
        have e : a⁻¹⁻¹ * ((k : (puAmalgam h.le).Universal) * a⁻¹ *
            (k : (puAmalgam h.le).Universal)⁻¹) =
            a * (a⁻¹ * ((k : (puAmalgam h.le).Universal) * a *
              (k : (puAmalgam h.le).Universal)⁻¹))⁻¹ * a⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hZn (hVs ha)) _).mp (Subgroup.inv_mem _ (ha' k hk)) }
  have hXSZ : X ≤ SZ := by
    rw [hXdef, Subgroup.closure_le]
    rintro _ ⟨k', hk', rfl⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hVn k'.2) x).mp hxV, fun k hk => ?_⟩
    have hl : toSL3 ψ' (k'⁻¹ * k * k') ∈ (ptLevi : Subgroup (SL3 F)) := by
      rw [map_mul, map_mul, map_inv]
      exact conj_mem_ptLevi hk' hk
    have h1 := hF1 _ hl
    have e : ((k' : (puAmalgam h.le).Universal) * x * (k' : (puAmalgam h.le).Universal)⁻¹)⁻¹ *
        ((k : (puAmalgam h.le).Universal) * ((k' : (puAmalgam h.le).Universal) * x *
          (k' : (puAmalgam h.le).Universal)⁻¹) * (k : (puAmalgam h.le).Universal)⁻¹) =
        (k' : (puAmalgam h.le).Universal) * (x⁻¹ * (((k'⁻¹ * k * k' : ↥(stab _ μ)) :
          (puAmalgam h.le).Universal) * x * ((k'⁻¹ * k * k' : ↥(stab _ μ)) :
            (puAmalgam h.le).Universal)⁻¹)) * (k' : (puAmalgam h.le).Universal)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hZn k'.2) _).mp h1
  have hlevi : ∀ k : ↥(stab (puAmalgam h.le) μ), toSL3 ψ' k ∈ (ptLevi : Subgroup (SL3 F)) →
      ∀ y ∈ X, y⁻¹ * ((k : (puAmalgam h.le).Universal) * y * (k : (puAmalgam h.le).Universal)⁻¹) ∈
        U' ⊓ Bloc h.le L μ ⊔ Dloc h.le L μ := by
    intro k hk y hy
    refine Subgroup.mem_sup_left ⟨?_, zm_le_bloc h hb hμ ((hXSZ hy).2 k hk)⟩
    exact Subgroup.mul_mem _ (U'.inv_mem (hXU' hy))
      ((Subgroup.mem_normalizer_iff.mp (hU'n k.2) _).mp (hXU' hy))
  have hS₀D : X ≤ Subgroup.normalizer ((S₀ ⊔ Dloc h.le L μ : Subgroup _) :
      Set (puAmalgam h.le).Universal) := by
    have hXc : X ≤ Subgroup.centralizer (S₀ : Set (puAmalgam h.le).Universal) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h1 : ⁅y, u⁆ = 1 := by
        have := Subgroup.commutator_mem_commutator (hXV hy)
          (zm_le_vv h hμ (hUZ (hS₀U hu)))
        rw [hVab] at this
        exact this
      rw [commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1.symm
    exact (le_inf (le_normalizer_of_le_centralizer hXc) ((hXV.trans hVs).trans hDn)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hXQ : ⁅X, Qv (puAmalgam h.le) μ⁆ ≤ S₀ ⊔ Dloc h.le L μ := by
    rw [hXdef]
    refine commutator_closure_le_of ?_ (by rw [← hXdef]; exact hS₀D)
    rintro _ ⟨k, hk, rfl⟩ y hy
    have hy' : (k : (puAmalgam h.le).Universal)⁻¹ * y * (k : (puAmalgam h.le).Universal) ∈
        Qv (puAmalgam h.le) μ := by
      have := (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_qv _ μ (Subgroup.inv_mem _ k.2))
        y).mp hy
      simpa using this
    have e : ⁅(k : (puAmalgam h.le).Universal) * x * (k : (puAmalgam h.le).Universal)⁻¹, y⁆ =
        (k : (puAmalgam h.le).Universal) * ⁅x, (k : (puAmalgam h.le).Universal)⁻¹ * y *
          (k : (puAmalgam h.le).Universal)⁆ * (k : (puAmalgam h.le).Universal)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have hm := hxS₀ _ hy'
    have hSZ : ((S₀ ⊔ Zloc h.le L μ : Subgroup _) : Set (puAmalgam h.le).Universal) =
        (S₀ : Set _) * (Zloc h.le L μ : Set _) :=
      Subgroup.coe_mul_of_left_le_normalizer_right _ _ ((hS₀U.trans (hUZ.trans hZs)).trans
        (le_normalizer_of_le_centralizer (Subgroup.le_centralizer_iff.mp
          (zloc_le_centralizer_stab h hfull hμ))))
    have hm' : ⁅x, (k : (puAmalgam h.le).Universal)⁻¹ * y * (k : (puAmalgam h.le).Universal)⁆ ∈
        ((S₀ ⊔ Zloc h.le L μ : Subgroup _) : Set (puAmalgam h.le).Universal) := hm
    rw [hSZ] at hm'
    obtain ⟨u, hu, w, hw, huw⟩ := hm'
    rw [← huw]
    have e2 : (k : (puAmalgam h.le).Universal) * (u * w) * (k : (puAmalgam h.le).Universal)⁻¹ =
        ((k : (puAmalgam h.le).Universal) * u * (k : (puAmalgam h.le).Universal)⁻¹) *
        ((k : (puAmalgam h.le).Universal) * w * (k : (puAmalgam h.le).Universal)⁻¹) := by group
    rw [e2]
    exact Subgroup.mul_mem_sup (hS₀stab k hk u hu)
      ((Subgroup.mem_normalizer_iff.mp (hDn k.2) w).mp (hWD hw))
  have hne : ¬ ⁅X, Qv (puAmalgam h.le) μ⁆ ≤ Dloc h.le L μ := fun hle =>
    hxy₀ (hle (Subgroup.commutator_mem_commutator hxX hy₀))
  have hDc : Dloc h.le L μ ≤
      Subgroup.centralizer (Ltil h.le L μ : Set (puAmalgam h.le).Universal) := by
    rw [Dloc, h.puTrans_Dq hμ]
    exact inf_le_right
  have hDV : Dloc h.le L μ ⊓ Vv (puAmalgam h.le) μ ≤ Bloc h.le L μ := by
    rintro v ⟨hvD, hvV⟩
    refine (mem_bloc_iff h hb hμ).mpr ⟨hvV, fun l hl => ?_⟩
    have h1 := Subgroup.mem_centralizer_iff.mp (hDc hvD) l hl
    have : ⁅v, l⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact h1.symm
    rw [this]
    exact Subgroup.one_mem _
  have hUN : U' ⊓ Dloc h.le L μ ≤ U' ⊓ Bloc h.le L μ := fun v hv =>
    ⟨hv.1, hDV ⟨hv.2, hU'V hv.1⟩⟩
  have hUU' : Uloc h.le L μ ≤ U' := by
    have hY := uloc_le_of_normal h hfull hφ hμ (Y := U' ⊓ ZM (puAmalgam h.le) μ) inf_le_right
      (le_normalizer_inf hU'n hZn) ?_
    · exact hY.trans inf_le_left
    · intro hle
      apply hxy₀
      have hmem : ⁅x, y₀⁆ ∈ U' ⊓ ZM (puAmalgam h.le) μ := by
        refine ⟨?_, hVQ (Subgroup.commutator_mem_commutator hxV hy₀)⟩
        have e : ⁅x, y₀⁆ = x * (y₀ * x⁻¹ * y₀⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact U'.mul_mem hxU' ((Subgroup.mem_normalizer_iff.mp (hU'n (hQs hy₀)) _).mp
          (U'.inv_mem hxU'))
      exact hWD (hle hmem)
  have hZC : Uloc h.le L μ ≤ U' ⊓ Bloc h.le L μ ⊔ Dloc h.le L μ :=
    (le_inf hUU' (hUZ.trans (zm_le_bloc h hb hμ))).trans le_sup_left
  have hCK : ⁅U' ⊓ Bloc h.le L μ, stab (puAmalgam h.le) μ⁆ ≤ Uloc h.le L μ ⊔ Dloc h.le L μ := by
    refine (Subgroup.commutator_mono inf_le_right le_rfl).trans ?_
    refine hBG.trans ?_
    rw [hK]
    exact hZUD
  have hZU : ⁅Uloc h.le L μ, U'⁆ ≤ Dloc h.le L μ := by
    have : ⁅Uloc h.le L μ, U'⁆ ≤ ⁅Vv (puAmalgam h.le) μ, Vv (puAmalgam h.le) μ⁆ :=
      Subgroup.commutator_mono (hUZ.trans (zm_le_vv h hμ)) hU'V
    rw [hVab] at this
    exact this.trans bot_le
  have hZW : ⁅Uloc h.le L μ, Qv (puAmalgam h.le) μ⁆ ≤ Dloc h.le L μ := by
    rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).mpr
      (hUZ.trans (zm_le_centralizer_qv _ h20 hμ))]
    exact bot_le
  have hUW : ⁅U', Qv (puAmalgam h.le) μ⁆ ≤ Uloc h.le L μ ⊔ Dloc h.le L μ :=
    ((Subgroup.commutator_mono hU'V le_rfl).trans hVQ).trans hZUD
  have hUC : IsSumOfNaturalModulesVia (stab (puAmalgam h.le) μ) U' (U' ⊓ Bloc h.le L μ) ψ'
      false 1 := isSumOfNaturalModulesVia_transfer hPK' hPB hPiB hU'V hU'B hU'n hBn hPBn
  have hNψ : ∀ k : ↥(stab (puAmalgam h.le) μ), (k : (puAmalgam h.le).Universal) ∈
      Dloc h.le L μ → ψ' k = 1 := by
    intro k hk
    have hkQ : (k : (puAmalgam h.le).Universal) ∈ Qv (puAmalgam h.le) μ := by
      rw [Dloc, h.puTrans_Dq hμ] at hk
      exact hk.1
    have h1 := (S46.toSL3_eq_one_iff_mem_qv h hφ hμ hψ k).mpr hkQ
    have h2 : ψ k = 1 := by
      have := congrArg (specialLinearGroupEquivStatedSL 3 F) h1
      simpa [toSL3] using this
    rw [hψ'def, conjSL, MonoidHom.comp_apply, h2, map_one]
  have hZD : Uloc h.le L μ ⊓ Dloc h.le L μ = ⊥ := by
    have hUD : Uq M T L ⊓ Dq M L = ⊥ := by
      rw [h.Uq_inf_Dq, ← h.Uq_inf_Zq, inf_comm]
      exact hφ.2.2.2.1
    rw [Uloc, Dloc, ← puTrans_inf, hUD, puTrans, Subgroup.bot_subgroupOf, transN_bot]
  have : ((Dloc h.le L μ).subgroupOf (stab (puAmalgam h.le) μ)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hDn
  have : Finite ↥(stab (puAmalgam h.le) μ) := finite_stab h hμ
  have : Finite ↥S₀ := Finite.of_injective _ (Subgroup.inclusion_injective (hS₀U.trans
    ((uloc_le_zm h hfull hμ).trans hZs)))
  have hcard : Nat.card ↥S₀ ≤ Nat.card F ^ 2 := by
    rw [hS₀card, Nat.card_eq_fintype_card]
    exact Nat.le_self_pow (by norm_num) _
  obtain ⟨c1, c2, -, -⟩ := ms17i_bar h17 hDs hn hψ's hNψ (hUZ.trans hZs) (hU'V.trans hVs) hQs
    hψ' hZD hUC hUN hZC hCK (stab_le_normalizer_qv _ μ) hZU hZW hUW hXU' rfl
    (fun k hk y hy => Subgroup.mem_sup_left (hXstab k hk y hy)) hlevi hne
    (hS₀U.trans (hUZ.trans hZs)) hXQ hcard
  refine ⟨U', hxU', hU'V, hUU', hU'n, fun y hy => ?_⟩
  have hirr : ∀ N : Subgroup (puAmalgam h.le).Universal,
      stab (puAmalgam h.le) μ ≤ Subgroup.normalizer (N : Set (puAmalgam h.le).Universal) →
      U' ⊓ Bloc h.le L μ ≤ N → N ≤ U' → N = U' ⊓ Bloc h.le L μ ∨ N = U' := by
    intro N hNn hBN hNU
    by_cases hNB : N ≤ Bloc h.le L μ
    · exact Or.inl (le_antisymm (le_inf hNU hNB) hBN)
    · right
      refine le_antisymm hNU fun u hu => ?_
      have hNBV := (isC1_bloc h hfull hb hμ hc).2.2 N hNn (hNU.trans hU'V) hNB
      have hu' : u ∈ ((N ⊔ Bloc h.le L μ : Subgroup _) : Set (puAmalgam h.le).Universal) := by
        rw [hNBV]
        exact hU'V hu
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (((hNU.trans hU'V).trans hVs).trans
        hBn)] at hu'
      obtain ⟨a, ha, b, hb', rfl⟩ := hu'
      have hbU : b ∈ U' := by
        have := U'.mul_mem (U'.inv_mem (hNU ha)) hu
        simpa using this
      exact N.mul_mem ha (hBN ⟨hbU, hb'⟩)
  have hAL : ⁅U', ⁅Qv (puAmalgam h.le) μ, Ltil h.le L μ⁆⁆ ≤ Dloc h.le L μ := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono (Subgroup.commutator_mono le_rfl (ltil_le_stab h μ))
      le_rfl).trans c2
  rcases commutator_dloc_dichotomy h hfull hμ (hU'V.trans hVs) hU'n inf_le_left hirr c1
    (hUW.trans (sup_le_sup_right hUZ _)) hAL hy with h1 | h1
  · exact Or.inl h1
  · exact Or.inr fun u hu hud => (h1 u hu hud).2

end Vertex

end CFSG.Quasithin.MS93.S4A
