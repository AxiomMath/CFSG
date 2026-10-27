module

public import CFSG.Quasithin.MS93.S46RIdx
public import CFSG.Quasithin.MS93.S46I466aQSec

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

section Perp

variable {𝔾 : Type} [Group 𝔾]

@[expose] def perpIn (N K : Subgroup 𝔾) (hNK : N ≤ Subgroup.normalizer (K : Set 𝔾)) :
    Subgroup 𝔾 where
  carrier := {v | v ∈ N ∧ ∀ w ∈ N, ⁅v, w⁆ ∈ K}
  one_mem' := ⟨N.one_mem, fun w _ => by rw [commutatorElement_one_left]; exact K.one_mem⟩
  mul_mem' := fun {v v'} hv hv' => ⟨N.mul_mem hv.1 hv'.1, fun w hw => by
    have e : ⁅v * v', w⁆ = v * ⁅v', w⁆ * v⁻¹ * ⁅v, w⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact K.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNK hv.1) _).mp (hv'.2 w hw)) (hv.2 w hw)⟩
  inv_mem' := fun {v} hv => ⟨N.inv_mem hv.1, fun w hw => by
    have e : ⁅v⁻¹, w⁆ = v⁻¹ * ⁅v, w⁆⁻¹ * v⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hNK (N.inv_mem hv.1)) _).mp (K.inv_mem (hv.2 w hw))⟩

theorem mem_perpIn {N K : Subgroup 𝔾} {hNK : N ≤ Subgroup.normalizer (K : Set 𝔾)} {v : 𝔾} :
    v ∈ perpIn N K hNK ↔ v ∈ N ∧ ∀ w ∈ N, ⁅v, w⁆ ∈ K :=
  Iff.rfl

theorem le_normalizer_perpIn {X N K : Subgroup 𝔾} {hNK : N ≤ Subgroup.normalizer (K : Set 𝔾)}
    (hXN : X ≤ Subgroup.normalizer (N : Set 𝔾)) (hXK : X ≤ Subgroup.normalizer (K : Set 𝔾)) :
    X ≤ Subgroup.normalizer (perpIn N K hNK : Set 𝔾) := by
  have key : ∀ y ∈ X, ∀ v ∈ perpIn N K hNK, y * v * y⁻¹ ∈ perpIn N K hNK := by
    intro y hy v hv
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hXN hy) v).mp hv.1, fun w hw => ?_⟩
    have hw' : y⁻¹ * w * y⁻¹⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hXN (X.inv_mem hy)) w).mp hw
    have e : ⁅y * v * y⁻¹, w⁆ = y * ⁅v, y⁻¹ * w * y⁻¹⁻¹⁆ * y⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hXK hy) _).mp (hv.2 _ hw')
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨key g hg v, fun hv => ?_⟩
  have := key g⁻¹ (X.inv_mem hg) _ hv
  simpa [mul_assoc] using this

end Perp

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem vOrb_sup_le_vv' (c : Hyp46 M T L φ) {x γ : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx _ x)
    (hγ : IsMVtx _ γ) (hd : (puAmalgam c.pu.le).treeGraph.dist x γ ≤ 2) :
    vOrb (puAmalgam c.pu.le) x γ ⊔ ZM (puAmalgam c.pu.le) x ≤ Vv (puAmalgam c.pu.le) x := by
  have hZγ : ZM (puAmalgam c.pu.le) γ ≤ Vv (puAmalgam c.pu.le) x := by
    have := zv_le_vv c.pu (L := L) hd
    rwa [zv_of_isMVtx _ hγ] at this
  have hZx : ZM (puAmalgam c.pu.le) x ≤ Vv (puAmalgam c.pu.le) x := by
    have := zv_le_vv c.pu (L := L) (α := x) (ρ := x) (by simp)
    rwa [zv_of_isMVtx _ hx] at this
  refine sup_le (iSup₂_le fun g hg => ?_) hZx
  rw [zm_smul]
  rintro _ ⟨z, hz, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_vv c.pu x hg) z).mp (hZγ hz)

theorem commutator_le_uloc_of_orbit_offender (h14 : MS14AS) (hSQ : SQTKQuot) (h463 : I463)
    (c : Hyp46 M T L φ) {x ρ γ : Vtx (puAmalgam c.pu.le)} (hx : IsMVtx _ x)
    (hxρ : (puAmalgam c.pu.le).treeGraph.Adj x ρ) (hργ : (puAmalgam c.pu.le).treeGraph.Adj ρ γ)
    (hxγ : x ≠ γ) {A C₀ : Subgroup (puAmalgam c.pu.le).Universal}
    (hAρ : A ≤ Qv (puAmalgam c.pu.le) ρ)
    (hAQ : ¬ A ≤ Qv (puAmalgam c.pu.le) x) (hA2 : ∀ a ∈ A, a ^ 2 ∈ Qv (puAmalgam c.pu.le) x)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, ⁅a, b⁆ ∈ Qv (puAmalgam c.pu.le) x)
    (hZC : ZM (puAmalgam c.pu.le) x ≤ C₀)
    (hC₀ : C₀ ≤ vOrb (puAmalgam c.pu.le) x γ ⊔ ZM (puAmalgam c.pu.le) x)
    (hC₀A : ⁅C₀, A⁆ ≤ ZM (puAmalgam c.pu.le) x)
    (hidx : C₀.relIndex (vOrb (puAmalgam c.pu.le) x γ ⊔ ZM (puAmalgam c.pu.le) x) ≤
      (Qv (puAmalgam c.pu.le) x).relIndex A) :
    ⁅vOrb (puAmalgam c.pu.le) x γ ⊔ ZM (puAmalgam c.pu.le) x,
      vOrb (puAmalgam c.pu.le) x γ ⊔ ZM (puAmalgam c.pu.le) x⁆ ≤ Uloc c.pu.le L x := by
  have hVVx := (h463 G M T L F φ c x hx).2
  obtain ⟨h, hmin, hb4, hφ⟩ := c
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, hφ⟩
  have h20 := h.hyp20
  have hb : 2 < critDist (puAmalgam h.le) := by omega
  have hb0 : 0 < critDist (puAmalgam h.le) := by omega
  obtain ⟨n, hF⟩ := hφ.1
  obtain ⟨ψ, hψs, hψ⟩ := exists_natural_Uloc h hφ hx
  have hγ : IsMVtx (puAmalgam h.le) γ := by
    have h1 := (isMVtx_iff_of_adj _ hxρ).mp hx
    have h2 := isMVtx_iff_of_adj _ hργ
    tauto
  have hdxγ : (puAmalgam h.le).treeGraph.dist x γ = 2 := dist_eq_two_of_adj_adj _ hxρ hργ hxγ
  set N := vOrb (puAmalgam h.le) x γ ⊔ ZM (puAmalgam h.le) x with hNdef
  have hNn : stab (puAmalgam h.le) x ≤ Subgroup.normalizer (N : Set _) :=
    stab_le_normalizer_vOrb_sup x γ
  have hZN : ZM (puAmalgam h.le) x ≤ N := le_sup_right
  have hZγN : ZM (puAmalgam h.le) γ ≤ N := zm_le_vOrb_sup x γ
  have hNV : N ≤ Vv (puAmalgam h.le) x := vOrb_sup_le_vv' ⟨h, hmin, hb4, hφ⟩ hx hγ hdxγ.le
  have hVs : Vv (puAmalgam h.le) x ≤ stab _ x := (vv_le_qv h hb hx).trans (qv_le_stab _ x)
  have hNs : N ≤ stab _ x := hNV.trans hVs
  have hfinS : Finite ↥(stab (puAmalgam h.le) x) := finite_stab h hx
  have hfinN : Finite ↥N := Finite.of_injective _ (Subgroup.inclusion_injective hNs)
  set U := Uloc h.le L x with hUdef
  by_contra hnot
  have hNN : ⁅N, N⁆ ≤ ZM (puAmalgam h.le) x := (Subgroup.commutator_mono hNV hNV).trans hVVx
  have hUZ : U ≤ ZM (puAmalgam h.le) x := uloc_le_zm h hfull hx
  set K' := ⁅N, N⁆ ⊔ U with hK'def
  have hK'Z : K' ≤ ZM (puAmalgam h.le) x := sup_le hNN hUZ
  have hK'N : K' ≤ N := hK'Z.trans hZN
  have hZc : ZM (puAmalgam h.le) x ≤ Subgroup.centralizer (N : Set _) :=
    (zm_le_centralizer_qv _ h20 hx).trans
      (Subgroup.centralizer_le (hNV.trans (vv_le_qv h hb hx)))
  have hK'c : K' ≤ Subgroup.centralizer (N : Set _) := hK'Z.trans hZc
  have hcom : ∀ k ∈ K', ∀ k' ∈ K', k * k' = k' * k := fun k hk k' hk' =>
    (Subgroup.mem_centralizer_iff.mp (hK'c hk) k' (hK'N hk')).symm
  have hK'2 : ∀ k ∈ K', k ^ 2 = 1 := fun k hk =>
    (isElemAbelian_zm _ h20 hb0 hx).2 k (hK'Z hk)
  have hUn : stab (puAmalgam h.le) x ≤ Subgroup.normalizer (U : Set _) :=
    stab_le_normalizer_puTrans h.le (S4A.Uq_normal h) x
  have hK'n : stab (puAmalgam h.le) x ≤ Subgroup.normalizer (K' : Set _) := by
    have hcn : stab (puAmalgam h.le) x ≤ Subgroup.normalizer ((⁅N, N⁆ : Subgroup _) : Set _) := by
      refine le_normalizer_of_map_conj_le fun g hg => ?_
      rw [Subgroup.map_commutator, map_conj_eq_of_mem_normalizer (hNn hg)]
    exact (le_inf hcn hUn).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hfinKQ : Finite ↥(K' ⊔ Qv (puAmalgam h.le) x) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (sup_le (hK'N.trans hNs)
      (qv_le_stab _ x)))
  have hLK : ⁅K', Ltil h.le L x⁆ ≤ U := by
    refine (Subgroup.commutator_mono hK'Z le_rfl).trans ?_
    rw [commutator_zm_eq_uloc h hfull hx (ltil_le_stab h x)]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp ((ltil_le_stab h x).trans hUn)
  obtain ⟨K'', hUK'', hK''K', hK''n, hidx2, hK'X⟩ :=
    exists_inv_index_two (X := stab (puAmalgam h.le) x) (L := Ltil h.le L x)
      (Q := Qv (puAmalgam h.le) x) (K₀ := U) (K' := K') hcom hK'2
      (isPGroup_qv_of_isMVtx h hx) le_sup_right
      (fun hle => hnot (le_sup_left.trans hle)) (stab_eq_ltil_sup_qv h hfull hx) hUn hK'n
      (stab_le_normalizer_qv _ x) hLK
  have hNK'' : N ≤ Subgroup.normalizer (K'' : Set _) := hNs.trans hK''n
  set Ut := perpIn N K'' hNK'' with hUtdef
  have hUt : ∀ v, v ∈ Ut ↔ v ∈ N ∧ ∀ w ∈ N, ⁅v, w⁆ ∈ K'' := fun v => mem_perpIn
  have hUtN : Ut ≤ N := fun v hv => hv.1
  have hUtn : stab (puAmalgam h.le) x ≤ Subgroup.normalizer (Ut : Set _) :=
    le_normalizer_perpIn hNn hK''n
  have hZUt : ZM (puAmalgam h.le) x ≤ Ut := by
    intro z hz
    refine ⟨hZN hz, fun w hw => ?_⟩
    have : ⁅z, w⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.mp (hZc hz) w hw).symm
    rw [this]
    exact K''.one_mem
  have hAs : A ≤ stab (puAmalgam h.le) x := hAρ.trans (qv_le_stab_of_adj _ hxρ.symm)
  have hker := toSL3_eq_one_iff_mem_qv h hφ hx hψ
  have hBL : ⁅ZM (puAmalgam h.le) x, Ltil h.le L x⁆ ≤ Ut := by
    rw [commutator_zm_eq_uloc h hfull hx (ltil_le_stab h x)]
    exact (Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((ltil_le_stab h x).trans hUn)).trans (hUZ.trans hZUt)
  have hNL := sd_group h14 hSQ (sqtkGroup_SL3 h hφ hSQ) hF (X := stab (puAmalgam h.le) x) (V := N)
    (K' := K') (K'' := K'') (Ut := Ut) (Bh := ZM (puAmalgam h.le) x) (A := A)
    (Lg := Ltil h.le L x) (C₀ := C₀ ⊔ Ut)
    (toSL3 ψ) (toSL3_surjective hψs) (pow_two_pow_eq_one_of_toSL3_eq_one h hφ hx hψ)
    hNn hK'N hK'c le_sup_left hK''K' hK''n hidx2 hK'X hUt hZN (stab_le_normalizer_zm _ x)
    (ltil_le_stab h x) (ltil_perfect h hx) hBL hAs
    (fun a ha => by
      rw [← map_pow]
      exact (hker _).mpr (by simpa using hA2 a ha))
    (fun a b ha hb' => by
      have h1 : toSL3 ψ ⁅a, b⁆ = 1 := (hker _).mpr (by
        have := hAc a ha b hb'
        simpa [commutatorElement_def] using this)
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1)
    (by
      obtain ⟨a, haA, haQ⟩ := Set.not_subset.mp hAQ
      exact ⟨⟨a, hAs haA⟩, haA, fun h1 => haQ ((hker _).mp h1)⟩)
    (sup_le_sup_right hZC _) (sup_le hC₀ hUtN)
    (QMix.commutator_sup_le_of
      ((hC₀.trans hNs).trans ((le_inf (stab_le_normalizer_zm _ x) hUtn).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)))
      ((hUtN.trans hNs).trans ((le_inf (stab_le_normalizer_zm _ x) hUtn).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)))
      (hC₀A.trans le_sup_left)
      ((Subgroup.le_normalizer_iff_commutator_le_left.mp (hAs.trans hUtn)).trans le_sup_right))
    (by
      have h1 : (C₀ ⊔ Ut).relIndex N ≤ C₀.relIndex N :=
        Subgroup.relIndex_le_of_le_left le_sup_left (by
          rw [Subgroup.relIndex]; exact Subgroup.index_ne_zero_of_finite)
      have h2 := card_natImage_eq_relIndex h hφ hx hψ hAs
      exact h1.trans (hidx.trans h2.ge))
  set W := ZM (puAmalgam h.le) γ ⊔ Ut with hW
  have hWn : stab (puAmalgam h.le) x ≤ Subgroup.normalizer (W : Set _) := by
    rw [stab_eq_ltil_sup_qv_adj h hfull hx hxρ]
    refine sup_le ?_ ?_
    · rw [Subgroup.le_normalizer_iff_commutator_le_left]
      refine QMix.commutator_sup_le_of (le_sup_left.trans Subgroup.le_normalizer)
        (le_sup_right.trans Subgroup.le_normalizer) ?_ ?_
      · exact ((Subgroup.commutator_mono hZγN le_rfl).trans hNL).trans le_sup_right
      · exact (Subgroup.le_normalizer_iff_commutator_le_left.mp
          ((ltil_le_stab h x).trans hUtn)).trans le_sup_right
    · have hTγ : Qv (puAmalgam h.le) ρ ≤ stab _ γ := qv_le_stab_of_adj _ hργ
      have hTx : Qv (puAmalgam h.le) ρ ≤ stab _ x := qv_le_stab_of_adj _ hxρ.symm
      exact (le_inf (hTγ.trans (stab_le_normalizer_zm _ γ)) (hTx.trans hUtn)).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hNW : N ≤ W := by
    refine sup_le (iSup₂_le fun g hg => ?_) (hZUt.trans le_sup_right)
    rw [zm_smul]
    rintro _ ⟨z, hz, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hWn hg) z).mp (le_sup_left (b := Ut) hz)
  have hZγab : ∀ a ∈ ZM (puAmalgam h.le) γ, ∀ b ∈ ZM (puAmalgam h.le) γ, ⁅a, b⁆ ∈ K'' := by
    intro a ha b hb'
    have : ⁅a, b⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      have haQ : a ∈ Qv (puAmalgam h.le) γ := zm_le_qv_of_dist_le_three hb4 hγ (by simp) ha
      exact (Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hγ hb') a haQ)
    rw [this]
    exact K''.one_mem
  have hZγUt : ZM (puAmalgam h.le) γ ≤ Ut := by
    intro z hz
    refine ⟨hZγN hz, fun w hw => ?_⟩
    have hwW := hNW hw
    have hc : ⁅W, ZM (puAmalgam h.le) γ⁆ ≤ K'' := by
      refine QMix.commutator_sup_le_of ((hZγN.trans hNs).trans hK''n)
        ((hUtN.trans hNs).trans hK''n) ?_ ?_
      · rw [Subgroup.commutator_le]
        intro a ha b hb'
        exact hZγab a ha b hb'
      · rw [Subgroup.commutator_le]
        intro u hu b hb'
        exact hu.2 b (hZγN hb')
    have h1 := hc (Subgroup.commutator_mem_commutator hwW hz)
    rw [← commutatorElement_inv]
    exact K''.inv_mem h1
  have hNUt : N ≤ Ut := hNW.trans (sup_le hZγUt le_rfl)
  have hNNK : ⁅N, N⁆ ≤ K'' := by
    rw [Subgroup.commutator_le]
    intro v hv w hw
    exact (hNUt hv).2 w hw
  have : K'' = K' := le_antisymm hK''K' (sup_le hNNK hUK'')
  rw [this, Subgroup.relIndex_self] at hidx2
  omega

end CFSG.Quasithin.MS93.S46R
