module

public import CFSG.Quasithin.MS93.ML3Sec
public import CFSG.Quasithin.MS93.S4AVtx

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

section SecVec

variable {G : Type} [Group G] {K V Z : Subgroup G} {F : Type} [Field F]
  {φ : ↥K →* ↥(StatedSL 3 F)}

@[expose] noncomputable def secVec (h : IsSumOfNaturalModulesVia K V Z φ false 1) (v : ↥V) :
    Fin 3 → F :=
  Multiplicative.toAdd (Classical.choose h.2.2 v) 0

theorem secVec_mul (h : IsSumOfNaturalModulesVia K V Z φ false 1) (v w : ↥V) :
    secVec h (v * w) = secVec h v + secVec h w := by
  simp [secVec]

theorem secVec_inv (h : IsSumOfNaturalModulesVia K V Z φ false 1) (v : ↥V) :
    secVec h v⁻¹ = - secVec h v := by
  simp [secVec]

theorem secVec_surjective (h : IsSumOfNaturalModulesVia K V Z φ false 1) :
    Function.Surjective (secVec h) := by
  intro x
  obtain ⟨v, hv⟩ := (Classical.choose_spec h.2.2).1 (Multiplicative.ofAdd (fun _ => x))
  refine ⟨v, ?_⟩
  unfold secVec
  rw [hv]
  rfl

theorem secVec_eq_zero_iff (h : IsSumOfNaturalModulesVia K V Z φ false 1) (v : ↥V) :
    secVec h v = 0 ↔ (v : G) ∈ Z := by
  have hker := (Classical.choose_spec h.2.2).2.1
  have hmem : (v : G) ∈ Z ↔ v ∈ (Classical.choose h.2.2).ker := by
    rw [hker, Subgroup.mem_subgroupOf]
  rw [hmem, MonoidHom.mem_ker]
  constructor
  · intro h0
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    exact h0
  · intro h1
    unfold secVec
    rw [h1]
    rfl

theorem secVec_conj (h : IsSumOfNaturalModulesVia K V Z φ false 1) (a : ↥K) (u v : ↥V)
    (huv : (v : G) = a * u * a⁻¹) :
    secVec h v = ((toSL3 φ a : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ secVec h u := by
  rw [toSL3_mat]
  exact (Classical.choose_spec h.2.2).2.2 a u v huv 0

end SecVec

section Vec

variable {F : Type} [Field F]

theorem eq_zero_of_forall_mulVec_eq {v : Fin 3 → F}
    (hv : ∀ g : SL3 F, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = v) : v = 0 := by
  by_contra hne
  have h1 := hv (rootElt 1 0 1)
  have h2 := hv (rootElt 2 1 1)
  have h3 := hv (rootElt 0 2 1)
  rw [rootElt_mulVec (by decide)] at h1 h2 h3
  apply hne
  funext k
  have e1 := congrFun h1 1
  have e2 := congrFun h2 2
  have e3 := congrFun h3 0
  simp at e1 e2 e3
  fin_cases k <;> simp_all

theorem mem_of_forall_mulVec_mem {S : Set (Fin 3 → F)}
    (hS : ∀ g : SL3 F, ∀ x ∈ S, ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ x ∈ S)
    {v : Fin 3 → F} (hv : v ∈ S) (hv0 : v ≠ 0) {u : Fin 3 → F} (hu : u ≠ 0) : u ∈ S := by
  obtain ⟨g₁, hg₁⟩ := exists_mulVec_e0_eq hv0
  obtain ⟨g₂, hg₂⟩ := exists_mulVec_e0_eq hu
  have hgu : ((g₂ * g₁⁻¹ : SL3 F) : Matrix (Fin 3) (Fin 3) F) *ᵥ v = u := by
    rw [← hg₁, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right,
      hg₂]
  rw [← hgu]
  exact hS _ v hv

end Vec

section C1

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
  (hfull : IsSL3Full M T L)
include h hfull

theorem isC1_normal (hb : 2 < critDist (puAmalgam h.le)) {α : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) {q : ℕ}
    (hc : IsC1 h.le L q α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α)) :
    ∃ (F' : Type) (_ : Field F') (_ : Fintype F')
      (ψ' : ↥(stab (puAmalgam h.le) α) →* ↥(StatedSL 3 F')),
      Fintype.card F' = q ∧ Function.Surjective ψ' ∧
      IsSumOfNaturalModulesVia (stab (puAmalgam h.le) α)
        (⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α)
        (⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α) ψ' false 1 ∧
      (⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α) ⊓
          Bloc h.le L α = ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α ∧
      (⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α) ⊔
          Bloc h.le L α = Vv (puAmalgam h.le) α ∧
      ⁅Bloc h.le L α, stab (puAmalgam h.le) α⁆ ≤
        ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α ∧
      ⁅⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆, Ltil h.le L α⁆ ≤
        ZM (puAmalgam h.le) α := by
  obtain ⟨hc1, C, hKC, hCV, hCG, hPC, hPiC, F', _, _, ψ', hcard, hsurj, hnat⟩ := hc
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  have hVn := stab_le_normalizer_vv h α
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) α
  have hQs : Qv (puAmalgam h.le) α ≤ stab _ α := qv_le_stab _ α
  have hQn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (Qv (puAmalgam h.le) α : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_qv _ α
  have hLs := ltil_le_stab h α
  have hZV : ZM (puAmalgam h.le) α ≤ Vv _ α := zm_le_vv h hα
  have hVQV : ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ≤ Vv _ α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hQs.trans hVn)
  have hVGV : ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ≤ Vv _ α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hVn
  have hKn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer
      ((⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :
        Subgroup _) : Set _) :=
    (le_inf (le_normalizer_commutator hVn hQn) hZn).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hPn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer
      ((⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :
        Subgroup _) : Set _) :=
    (le_inf (le_normalizer_commutator hVn Subgroup.le_normalizer) hZn).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hPV : ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α ≤
      Vv _ α := sup_le hVGV hZV
  have hVQB : ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ≤ Bloc h.le L α := by
    intro x hx
    refine (mem_bloc_iff h hb hα).mpr ⟨hVQV hx, fun l hl => ?_⟩
    exact hc1 (Subgroup.commutator_mem_commutator hx hl)
  have hZB : ZM (puAmalgam h.le) α ≤ Bloc h.le L α := zm_le_bloc h hb hα
  have hCs : C ≤ stab (puAmalgam h.le) α := hCV.trans hVs
  have hKL : ⁅⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α,
      Ltil h.le L α⁆ ≤ ZM _ α :=
    S4A.commutator_sup_le_of hc1
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hZn))
      ((hVQV.trans hVs).trans hZn) ((hZV.trans hVs).trans hZn)
  have hCLL : ⁅⁅C, Ltil h.le L α⁆, Ltil h.le L α⁆ ≤ ZM (puAmalgam h.le) α :=
    (Subgroup.commutator_mono ((Subgroup.commutator_mono le_rfl hLs).trans hCG) le_rfl).trans
      hKL
  have hCL : ⁅C, Ltil h.le L α⁆ ≤ ZM (puAmalgam h.le) α := by
    have h3 : ⁅⁅Ltil h.le L α, Ltil h.le L α⁆, C⁆ ≤ ZM (puAmalgam h.le) α :=
      three_subgroups_le (hLs.trans hZn) (hLs.trans hZn) (hCs.trans hZn)
        (by rw [Subgroup.commutator_comm (Ltil h.le L α) C]; exact hCLL) hCLL
    rw [ltil_perfect h hα, Subgroup.commutator_comm] at h3
    exact h3
  have hCB : C ≤ Bloc h.le L α := fun c hc =>
    (mem_bloc_iff h hb hα).mpr ⟨hCV hc, fun l hl => hCL (Subgroup.commutator_mem_commutator hc hl)⟩
  have hVPC : ∀ v ∈ Vv (puAmalgam h.le) α, ∃ p ∈ ⁅Vv (puAmalgam h.le) α,
      stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α, ∃ c ∈ C, v = p * c := by
    intro v hv
    have hv' : v ∈ ((⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔
        ZM (puAmalgam h.le) α ⊔ C : Subgroup _) : Set _) := by
      rw [hPC]
      exact hv
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hCs.trans hPn)] at hv'
    obtain ⟨p, hp, c, hc, rfl⟩ := hv'
    exact ⟨p, hp, c, hc, rfl⟩
  have hstab : stab (puAmalgam h.le) α = Ltil h.le L α ⊔ Qv (puAmalgam h.le) α :=
    stab_eq_ltil_sup_qv h hfull hα
  have hconjK : ∀ p ∈ ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α,
      (∀ l ∈ Ltil h.le L α, ⁅l, p⁆ ∈ ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔
        ZM (puAmalgam h.le) α) →
      ∀ s ∈ stab (puAmalgam h.le) α, s * p * s⁻¹ * p⁻¹ ∈
        ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α := by
    intro p hp hpl s hs
    have hs' : s ∈ ((Ltil h.le L α ⊔ Qv (puAmalgam h.le) α : Subgroup _) : Set _) := hstab ▸ hs
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hLs.trans hQn)] at hs'
    obtain ⟨l, hl, t, ht, rfl⟩ := hs'
    have hpV := hPV hp
    have h1 : t * p * t⁻¹ * p⁻¹ ∈ ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔
        ZM (puAmalgam h.le) α := by
      refine Subgroup.mem_sup_left ?_
      have : t * p * t⁻¹ * p⁻¹ = ⁅p, t⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator hpV ht)
    have hrw : l * t * p * (l * t)⁻¹ * p⁻¹ =
        (l * (t * p * t⁻¹ * p⁻¹) * l⁻¹) * (l * p * l⁻¹ * p⁻¹) := by group
    rw [hrw]
    refine Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hKn (hLs hl)) _).mp h1) ?_
    have : l * p * l⁻¹ * p⁻¹ = ⁅l, p⁆ := by simp only [commutatorElement_def]
    rw [this]
    exact hpl l hl
  have hBC : Bloc h.le L α ≤ C := by
    intro x hx
    obtain ⟨p, hp, c, hc, rfl⟩ := hVPC x ((bloc_le_vv h α) hx)
    have hpB : p ∈ Bloc h.le L α := by
      have := Subgroup.mul_mem _ hx (Subgroup.inv_mem _ (hCB hc))
      simpa using this
    have hpl : ∀ l ∈ Ltil h.le L α, ⁅l, p⁆ ∈ ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔
        ZM (puAmalgam h.le) α := by
      intro l hl
      have := ((mem_bloc_iff h hb hα).mp hpB).2 l hl
      rw [← commutatorElement_inv]
      exact Subgroup.mem_sup_right (Subgroup.inv_mem _ this)
    have hfix : ∀ g : SL3 F', ((g : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ secVec hnat ⟨p, hp⟩ =
        secVec hnat ⟨p, hp⟩ := by
      intro g
      obtain ⟨s, rfl⟩ := toSL3_surjective hsurj g
      have hk := hconjK p hp hpl s s.2
      have hsp : (s : (puAmalgam h.le).Universal) * p * (s : (puAmalgam h.le).Universal)⁻¹ ∈
          ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :=
        (Subgroup.mem_normalizer_iff.mp (hPn s.2) _).mp hp
      rw [← secVec_conj hnat s ⟨p, hp⟩ ⟨_, hsp⟩ rfl]
      have hdiff : secVec hnat (⟨_, hsp⟩ * (⟨p, hp⟩ : ↥(⁅Vv (puAmalgam h.le) α,
          stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α))⁻¹) = 0 :=
        (secVec_eq_zero_iff hnat _).mpr hk
      rw [secVec_mul, secVec_inv, add_neg_eq_zero] at hdiff
      exact hdiff
    have hp0 := eq_zero_of_forall_mulVec_eq hfix
    have hpK := (secVec_eq_zero_iff hnat _).mp hp0
    exact Subgroup.mul_mem _ (hKC hpK) hc
  have hBeq : Bloc h.le L α = C := le_antisymm hBC hCB
  subst hBeq
  exact ⟨F', inferInstance, inferInstance, ψ', hcard, hsurj, hnat, hPiC, hPC, hCG, hc1⟩

theorem isC1_bloc (hb : 2 < critDist (puAmalgam h.le)) {α : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) {q : ℕ}
    (hc : IsC1 h.le L q α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α)) :
    ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ≤ Bloc h.le L α ∧
      Bloc h.le L α ≠ Vv (puAmalgam h.le) α ∧
      ∀ N : Subgroup (puAmalgam h.le).Universal,
        stab (puAmalgam h.le) α ≤ Subgroup.normalizer (N : Set (puAmalgam h.le).Universal) →
        N ≤ Vv (puAmalgam h.le) α → ¬ N ≤ Bloc h.le L α →
        N ⊔ Bloc h.le L α = Vv (puAmalgam h.le) α := by
  obtain ⟨F', _, _, ψ', -, hsurj, hnat, hPiB, hPB, -, hc1⟩ := isC1_normal h hfull hb hα hc
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  have hVn := stab_le_normalizer_vv h α
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) α
  have hZV : ZM (puAmalgam h.le) α ≤ Vv _ α := zm_le_vv h hα
  have hVGV : ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ≤ Vv _ α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hVn
  have hPn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer
      ((⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :
        Subgroup _) : Set _) :=
    (le_inf (le_normalizer_commutator hVn Subgroup.le_normalizer) hZn).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hPV : ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α ≤
      Vv _ α := sup_le hVGV hZV
  have hBn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (Bloc h.le L α : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_of_smul (F := fun δ => Bloc h.le L δ) _ (fun g δ => bloc_smul h g δ) α
  have hBs : Bloc h.le L α ≤ stab _ α := (bloc_le_vv h α).trans hVs
  have hKB : ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α ≤
      Bloc h.le L α := hPiB ▸ inf_le_right
  have hVPB : ∀ v ∈ Vv (puAmalgam h.le) α, ∃ p ∈ ⁅Vv (puAmalgam h.le) α,
      stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α, ∃ c ∈ Bloc h.le L α, v = p * c := by
    intro v hv
    have hv' : v ∈ ((⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔
        ZM (puAmalgam h.le) α ⊔ Bloc h.le L α : Subgroup _) : Set _) := by
      rw [hPB]
      exact hv
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hBs.trans hPn)] at hv'
    obtain ⟨p, hp, c, hc, rfl⟩ := hv'
    exact ⟨p, hp, c, hc, rfl⟩
  refine ⟨le_sup_left.trans hKB, ?_, ?_⟩
  ·
    intro hBV
    obtain ⟨v, hv⟩ := secVec_surjective hnat ![1, 0, 0]
    have hvK : (v : (puAmalgam h.le).Universal) ∈
        ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :=
      hPiB ▸ ⟨v.2, hBV.ge (hPV v.2)⟩
    have := (secVec_eq_zero_iff hnat v).mpr hvK
    rw [hv] at this
    have h0 := congrFun this 0
    simp at h0
  ·
    intro N hNn hNV hNB
    refine le_antisymm (sup_le hNV (bloc_le_vv h α)) ?_
    have hN'n : stab (puAmalgam h.le) α ≤ Subgroup.normalizer
        ((N ⊔ Bloc h.le L α : Subgroup _) : Set (puAmalgam h.le).Universal) :=
      (le_inf hNn hBn).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    set S : Set (Fin 3 → F') := {x | ∃ p : ↥(⁅Vv (puAmalgam h.le) α,
      stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α),
        (p : (puAmalgam h.le).Universal) ∈ N ⊔ Bloc h.le L α ∧ secVec hnat p = x} with hS
    have hSinv : ∀ g : SL3 F', ∀ x ∈ S, ((g : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ x ∈ S := by
      rintro g _ ⟨p, hpN, rfl⟩
      obtain ⟨s, rfl⟩ := toSL3_surjective hsurj g
      have hsp : (s : (puAmalgam h.le).Universal) * p * (s : (puAmalgam h.le).Universal)⁻¹ ∈
          ⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :=
        (Subgroup.mem_normalizer_iff.mp (hPn s.2) _).mp p.2
      refine ⟨⟨_, hsp⟩, (Subgroup.mem_normalizer_iff.mp (hN'n s.2) _).mp hpN, ?_⟩
      exact secVec_conj hnat s p ⟨_, hsp⟩ rfl
    obtain ⟨p₀, hp₀N, hp₀⟩ : ∃ p : ↥(⁅Vv (puAmalgam h.le) α, stab (puAmalgam h.le) α⁆ ⊔
        ZM (puAmalgam h.le) α), (p : (puAmalgam h.le).Universal) ∈ N ⊔ Bloc h.le L α ∧
          secVec hnat p ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hNB
      intro n hn
      obtain ⟨p, hp, c, hc, rfl⟩ := hVPB n (hNV hn)
      have hpN : p ∈ N ⊔ Bloc h.le L α := by
        have := Subgroup.mul_mem _ (Subgroup.mem_sup_left (T := Bloc h.le L α) hn)
          (Subgroup.inv_mem _ (Subgroup.mem_sup_right (S := N) hc))
        simpa using this
      have hp0 := hcon ⟨p, hp⟩ hpN
      exact Subgroup.mul_mem _ (hKB ((secVec_eq_zero_iff hnat _).mp hp0)) hc
    intro v hv
    obtain ⟨p, hp, c, hc, rfl⟩ := hVPB v hv
    refine Subgroup.mul_mem _ ?_ (Subgroup.mem_sup_right hc)
    by_cases hpz : secVec hnat ⟨p, hp⟩ = 0
    · exact Subgroup.mem_sup_right (hKB ((secVec_eq_zero_iff hnat _).mp hpz))
    · obtain ⟨p', hp'N, hp'⟩ := mem_of_forall_mulVec_mem hSinv ⟨p₀, hp₀N, rfl⟩ hp₀ hpz
      have hdiff : secVec hnat (⟨p, hp⟩ * p'⁻¹) = 0 := by
        rw [secVec_mul, secVec_inv, hp', add_neg_cancel]
      have hK := (secVec_eq_zero_iff hnat _).mp hdiff
      have : p = (p * (p' : (puAmalgam h.le).Universal)⁻¹) * p' := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hKB hK)) hp'N

end C1

end CFSG.Quasithin.MS93.S4A
