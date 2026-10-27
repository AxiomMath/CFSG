module

public import CFSG.Quasithin.MS93.S4A431D
public import CFSG.Quasithin.MS93.S34FFlat

public section

namespace CFSG.Quasithin.MS93.S43F

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

section Flat

variable (h : PUHyp M T L)
include h

theorem flat_le_stab (δ : Vtx (puAmalgam h.le)) : S34F.flat h δ ≤ stab _ δ :=
  puTrans_le_stab h.le _ δ

theorem stab_le_normalizer_flat (δ : Vtx (puAmalgam h.le)) :
    stab _ δ ≤ Subgroup.normalizer (S34F.flat h δ : Set (puAmalgam h.le).Universal) :=
  stab_le_normalizer_puTrans h.le (S34F.flat_subgroupOf_normal h) δ

theorem ltil_le_flat (δ : Vtx (puAmalgam h.le)) : Ltil h.le L δ ≤ S34F.flat h δ :=
  puTrans_mono h.le le_sup_left δ

theorem qv_le_flat {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) : Qv _ δ ≤ S34F.flat h δ := by
  rw [h.qv_eq hδ]
  exact puTrans_mono h.le le_sup_right δ

theorem flat_eq_ltil_sup_qv {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    S34F.flat h δ = Ltil h.le L δ ⊔ Qv _ δ := by
  rw [S34F.flat, puTrans_sup h.le h.L_le (pCoreOf_le' M), ← h.qv_eq hδ]

end Flat

@[expose] def IsC1Flat (h : PUHyp M T L) (q : ℕ) (δ : Vtx (puAmalgam h.le))
    (A B : Subgroup (puAmalgam h.le).Universal) : Prop :=
  ⁅⁅A, Qv (puAmalgam h.le) δ⁆, Ltil h.le L δ⁆ ≤ B ∧
    ∃ C : Subgroup (puAmalgam h.le).Universal, ⁅A, Qv (puAmalgam h.le) δ⁆ ⊔ B ≤ C ∧ C ≤ A ∧
      ⁅C, S34F.flat h δ⁆ ≤ ⁅A, Qv (puAmalgam h.le) δ⁆ ⊔ B ∧
      (⁅A, S34F.flat h δ⁆ ⊔ B) ⊔ C = A ∧
      (⁅A, S34F.flat h δ⁆ ⊔ B) ⊓ C = ⁅A, Qv (puAmalgam h.le) δ⁆ ⊔ B ∧
      ∃ (F : Type) (_ : Field F) (_ : Fintype F)
        (ψ : ↥(S34F.flat h δ) →* ↥(StatedSL 3 F)),
        Fintype.card F = q ∧ Function.Surjective ψ ∧
        IsSumOfNaturalModulesVia (S34F.flat h δ) (⁅A, S34F.flat h δ⁆ ⊔ B)
          (⁅A, Qv (puAmalgam h.le) δ⁆ ⊔ B) ψ false 1

section C1

variable (h : PUHyp M T L)
include h

theorem isC1Flat_normal (hb : 2 < critDist (puAmalgam h.le)) {α : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) {q : ℕ}
    (hc : IsC1Flat h q α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α)) :
    ∃ (F' : Type) (_ : Field F') (_ : Fintype F')
      (ψ' : ↥(S34F.flat h α) →* ↥(StatedSL 3 F')),
      Fintype.card F' = q ∧ Function.Surjective ψ' ∧
      IsSumOfNaturalModulesVia (S34F.flat h α)
        (⁅Vv (puAmalgam h.le) α, S34F.flat h α⁆ ⊔ ZM (puAmalgam h.le) α)
        (⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α) ψ' false 1 ∧
      (⁅Vv (puAmalgam h.le) α, S34F.flat h α⁆ ⊔ ZM (puAmalgam h.le) α) ⊓
          Bloc h.le L α = ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α ∧
      (⁅Vv (puAmalgam h.le) α, S34F.flat h α⁆ ⊔ ZM (puAmalgam h.le) α) ⊔
          Bloc h.le L α = Vv (puAmalgam h.le) α ∧
      ⁅Bloc h.le L α, S34F.flat h α⁆ ≤
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
  have hLf := ltil_le_flat h α
  have hfs := flat_le_stab h α
  have hZV : ZM (puAmalgam h.le) α ≤ Vv _ α := zm_le_vv h hα
  have hVQV : ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ≤ Vv _ α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hQs.trans hVn)
  have hVGV : ⁅Vv (puAmalgam h.le) α, S34F.flat h α⁆ ≤ Vv _ α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hfs.trans hVn)
  have hKn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer
      ((⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α :
        Subgroup _) : Set _) :=
    (le_inf (le_normalizer_commutator hVn hQn) hZn).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hPn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer
      ((⁅Vv (puAmalgam h.le) α, S34F.flat h α⁆ ⊔ ZM (puAmalgam h.le) α :
        Subgroup _) : Set _) :=
    (le_inf (le_normalizer_commutator hVn (stab_le_normalizer_flat h α)) hZn).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hPV : ⁅Vv (puAmalgam h.le) α, S34F.flat h α⁆ ⊔ ZM (puAmalgam h.le) α ≤ Vv _ α :=
    sup_le hVGV hZV
  have hVQB : ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ≤ Bloc h.le L α := by
    intro x hx
    refine (mem_bloc_iff h hb hα).mpr ⟨hVQV hx, fun l hl => ?_⟩
    exact hc1 (Subgroup.commutator_mem_commutator hx hl)
  have hCs : C ≤ stab (puAmalgam h.le) α := hCV.trans hVs
  have hKL : ⁅⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α,
      Ltil h.le L α⁆ ≤ ZM _ α :=
    S4A.commutator_sup_le_of hc1
      (Subgroup.le_normalizer_iff_commutator_le_left.mp (hLs.trans hZn))
      ((hVQV.trans hVs).trans hZn) ((hZV.trans hVs).trans hZn)
  have hCLL : ⁅⁅C, Ltil h.le L α⁆, Ltil h.le L α⁆ ≤ ZM (puAmalgam h.le) α :=
    (Subgroup.commutator_mono ((Subgroup.commutator_mono le_rfl hLf).trans hCG) le_rfl).trans
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
      S34F.flat h α⁆ ⊔ ZM (puAmalgam h.le) α, ∃ c ∈ C, v = p * c := by
    intro v hv
    have hv' : v ∈ ((⁅Vv (puAmalgam h.le) α, S34F.flat h α⁆ ⊔
        ZM (puAmalgam h.le) α ⊔ C : Subgroup _) : Set _) := by
      rw [hPC]
      exact hv
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ (hCs.trans hPn)] at hv'
    obtain ⟨p, hp, c, hc, rfl⟩ := hv'
    exact ⟨p, hp, c, hc, rfl⟩
  have hflat : S34F.flat h α = Ltil h.le L α ⊔ Qv (puAmalgam h.le) α :=
    flat_eq_ltil_sup_qv h hα
  have hconjK : ∀ p ∈ ⁅Vv (puAmalgam h.le) α, S34F.flat h α⁆ ⊔ ZM (puAmalgam h.le) α,
      (∀ l ∈ Ltil h.le L α, ⁅l, p⁆ ∈ ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔
        ZM (puAmalgam h.le) α) →
      ∀ s ∈ S34F.flat h α, s * p * s⁻¹ * p⁻¹ ∈
        ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α := by
    intro p hp hpl s hs
    have hs' : s ∈ ((Ltil h.le L α ⊔ Qv (puAmalgam h.le) α : Subgroup _) : Set _) := hflat ▸ hs
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
          ⁅Vv (puAmalgam h.le) α, S34F.flat h α⁆ ⊔ ZM (puAmalgam h.le) α :=
        (Subgroup.mem_normalizer_iff.mp (hPn (hfs s.2)) _).mp hp
      rw [← secVec_conj hnat s ⟨p, hp⟩ ⟨_, hsp⟩ rfl]
      have hdiff : secVec hnat (⟨_, hsp⟩ * (⟨p, hp⟩ : ↥(⁅Vv (puAmalgam h.le) α,
          S34F.flat h α⁆ ⊔ ZM (puAmalgam h.le) α))⁻¹) = 0 :=
        (secVec_eq_zero_iff hnat _).mpr hk
      rw [secVec_mul, secVec_inv, add_neg_eq_zero] at hdiff
      exact hdiff
    have hp0 := eq_zero_of_forall_mulVec_eq hfix
    have hpK := (secVec_eq_zero_iff hnat _).mp hp0
    exact Subgroup.mul_mem _ (hKC hpK) hc
  have hBeq : Bloc h.le L α = C := le_antisymm hBC hCB
  subst hBeq
  exact ⟨F', inferInstance, inferInstance, ψ', hcard, hsurj, hnat, hPiC, hPC, hCG, hc1⟩

theorem isC1Flat_bloc (hb : 2 < critDist (puAmalgam h.le)) {α : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) {q : ℕ}
    (hc : IsC1Flat h q α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α)) :
    ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ≤ Bloc h.le L α ∧
      Bloc h.le L α ≠ Vv (puAmalgam h.le) α ∧
      ∀ N : Subgroup (puAmalgam h.le).Universal,
        S34F.flat h α ≤ Subgroup.normalizer (N : Set (puAmalgam h.le).Universal) →
        N ≤ Vv (puAmalgam h.le) α → ¬ N ≤ Bloc h.le L α →
        N ⊔ Bloc h.le L α = Vv (puAmalgam h.le) α := by
  obtain ⟨F', _, _, ψ', -, hsurj, hnat, hPiB, hPB, -, hc1⟩ := isC1Flat_normal h hb hα hc
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  have hVn := stab_le_normalizer_vv h α
  have hZn := stab_le_normalizer_zm (puAmalgam h.le) α
  have hZV : ZM (puAmalgam h.le) α ≤ Vv _ α := zm_le_vv h hα
  have hfs := flat_le_stab h α
  have hVGV : ⁅Vv (puAmalgam h.le) α, S34F.flat h α⁆ ≤ Vv _ α :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hfs.trans hVn)
  have hPn : stab (puAmalgam h.le) α ≤ Subgroup.normalizer
      ((⁅Vv (puAmalgam h.le) α, S34F.flat h α⁆ ⊔ ZM (puAmalgam h.le) α :
        Subgroup _) : Set _) :=
    (le_inf (le_normalizer_commutator hVn (stab_le_normalizer_flat h α)) hZn).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hPV : ⁅Vv (puAmalgam h.le) α, S34F.flat h α⁆ ⊔ ZM (puAmalgam h.le) α ≤ Vv _ α :=
    sup_le hVGV hZV
  have hBn : stab (puAmalgam h.le) α ≤
      Subgroup.normalizer (Bloc h.le L α : Set (puAmalgam h.le).Universal) :=
    stab_le_normalizer_of_smul (F := fun δ => Bloc h.le L δ) _ (fun g δ => bloc_smul h g δ) α
  have hBs : Bloc h.le L α ≤ stab _ α := (bloc_le_vv h α).trans hVs
  have hKB : ⁅Vv (puAmalgam h.le) α, Qv (puAmalgam h.le) α⁆ ⊔ ZM (puAmalgam h.le) α ≤
      Bloc h.le L α := hPiB ▸ inf_le_right
  have hVPB : ∀ v ∈ Vv (puAmalgam h.le) α, ∃ p ∈ ⁅Vv (puAmalgam h.le) α,
      S34F.flat h α⁆ ⊔ ZM (puAmalgam h.le) α, ∃ c ∈ Bloc h.le L α, v = p * c := by
    intro v hv
    have hv' : v ∈ ((⁅Vv (puAmalgam h.le) α, S34F.flat h α⁆ ⊔
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
    have hN'n : S34F.flat h α ≤ Subgroup.normalizer
        ((N ⊔ Bloc h.le L α : Subgroup _) : Set (puAmalgam h.le).Universal) :=
      (le_inf hNn (hfs.trans hBn)).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    set S : Set (Fin 3 → F') := {x | ∃ p : ↥(⁅Vv (puAmalgam h.le) α,
      S34F.flat h α⁆ ⊔ ZM (puAmalgam h.le) α),
        (p : (puAmalgam h.le).Universal) ∈ N ⊔ Bloc h.le L α ∧ secVec hnat p = x} with hS
    have hSinv : ∀ g : SL3 F', ∀ x ∈ S, ((g : SL3 F') : Matrix (Fin 3) (Fin 3) F') *ᵥ x ∈ S := by
      rintro g _ ⟨p, hpN, rfl⟩
      obtain ⟨s, rfl⟩ := toSL3_surjective hsurj g
      have hsp : (s : (puAmalgam h.le).Universal) * p * (s : (puAmalgam h.le).Universal)⁻¹ ∈
          ⁅Vv (puAmalgam h.le) α, S34F.flat h α⁆ ⊔ ZM (puAmalgam h.le) α :=
        (Subgroup.mem_normalizer_iff.mp (hPn (hfs s.2)) _).mp p.2
      refine ⟨⟨_, hsp⟩, (Subgroup.mem_normalizer_iff.mp (hN'n s.2) _).mp hpN, ?_⟩
      exact secVec_conj hnat s p ⟨_, hsp⟩ rfl
    obtain ⟨p₀, hp₀N, hp₀⟩ : ∃ p : ↥(⁅Vv (puAmalgam h.le) α, S34F.flat h α⁆ ⊔
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

theorem vcirc_le_conjCl_flat (hb : 2 < critDist (puAmalgam h.le)) {α : Vtx (puAmalgam h.le)}
    (hα : IsMVtx _ α) {q : ℕ}
    (hc : IsC1Flat h q α (Vv (puAmalgam h.le) α) (ZM (puAmalgam h.le) α))
    {δ : Vtx (puAmalgam h.le)} (hδ : δ ∈ nablaSet h.le L α) :
    Vcirc h.le L α ≤ conjCl (stab _ α) (ZM (puAmalgam h.le) δ) := by
  obtain ⟨hd, hZB⟩ := hδ
  have hδM : IsMVtx (puAmalgam h.le) δ := by
    have hev : Even ((puAmalgam h.le).treeGraph.dist α δ) := ⟨1, by rw [hd]⟩
    exact ((even_dist_iff (puAmalgam h.le) α δ).mp hev).1 hα
  have hVs : Vv (puAmalgam h.le) α ≤ stab _ α := (vv_le_qv h hb hα).trans (qv_le_stab _ α)
  have hVn := stab_le_normalizer_vv h α
  have hNn := le_normalizer_conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) δ)
  have hZδV : ZM (puAmalgam h.le) δ ≤ Vv _ α := by
    rw [← zv_of_isMVtx _ hδM]
    exact zv_le_vv h hd.le
  have hNV : conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) δ) ≤ Vv _ α := by
    refine iSup₂_le fun g hg => ?_
    rintro _ ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hVn hg) z).mp (hZδV hz)
  have hNB : ¬ conjCl (stab (puAmalgam h.le) α) (ZM (puAmalgam h.le) δ) ≤ Bloc h.le L α := by
    intro hle
    apply hZB
    rw [zv_of_isMVtx _ hδM]
    exact (le_conjCl _ _).trans hle
  have hNBV := (isC1Flat_bloc h hb hα hc).2.2 _ ((flat_le_stab h α).trans hNn) hNV hNB
  have hZN := zm_le_conjCl_zm h hd
  have hBV : Bloc h.le L α ≤ Vv _ α := bloc_le_vv h α
  rw [Vcirc, ← hNBV]
  refine S4A.commutator_sup_le_of ?_ ?_ ?_ ?_
  · exact Subgroup.le_normalizer_iff_commutator_le_left.mp ((ltil_le_stab h α).trans hNn)
  · exact (commutator_bloc_le h hb hα).trans hZN
  · exact Subgroup.le_normalizer
  · exact (hBV.trans hVs).trans hNn

end C1

end CFSG.Quasithin.MS93.S43F
