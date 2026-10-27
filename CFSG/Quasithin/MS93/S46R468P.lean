module

public import CFSG.Quasithin.MS93.S46I469Loc
public import CFSG.Quasithin.MS93.S46I466bReal
public import CFSG.Quasithin.MS93.S46I467Dec
public import CFSG.Quasithin.MS93.S45Edge
public import CFSG.Quasithin.MS93.S45Path

public section

namespace CFSG.Quasithin.MS93.S46R

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S4A CFSG.Quasithin.MS93.S46
open scoped commutatorElement

section Def

universe u v

variable {A B : Type u} {C : Type v} [Group A] [Group C] [Group B] (X : GoldAmalgam A C B)

@[expose] def pencil (γ : Vtx X) (P : Subgroup X.Universal) : Subgroup X.Universal :=
  ⨆ β' ∈ X.treeGraph.neighborSet γ, ⨆ (_ : P ≤ Usup X γ β'), Vv X β'

variable {X}

theorem vv_le_pencil {γ β' : Vtx X} (hγβ' : X.treeGraph.Adj γ β') {P : Subgroup X.Universal}
    (hP : P ≤ Usup X γ β') : Vv X β' ≤ pencil X γ P :=
  le_iSup₂_of_le (f := fun β' (_ : β' ∈ X.treeGraph.neighborSet γ) =>
    ⨆ (_ : P ≤ Usup X γ β'), Vv X β') β' hγβ' (le_iSup_of_le hP le_rfl)

theorem pencil_le {γ : Vtx X} {P K : Subgroup X.Universal}
    (hK : ∀ β', X.treeGraph.Adj γ β' → P ≤ Usup X γ β' → Vv X β' ≤ K) : pencil X γ P ≤ K :=
  iSup₂_le fun β' hβ' => iSup_le fun hP => hK β' hβ' hP

end Def

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]
  {φ : ↥M →* ↥(StatedSL 3 F)}

theorem commutator_vv_vv_le_zh_inf (h464 : I464) (c : Hyp46 M T L φ)
    {β β' : Vtx (puAmalgam c.pu.le)} (hβ : ¬ IsMVtx (puAmalgam c.pu.le) β)
    (hβ' : ¬ IsMVtx (puAmalgam c.pu.le) β')
    (hd : (puAmalgam c.pu.le).treeGraph.dist β β' ≤ 2) :
    ⁅Vv (puAmalgam c.pu.le) β, Vv _ β'⁆ ≤ ZH _ β ⊓ ZH _ β' := by
  have h464' := h464 G M T L F φ c
  refine le_inf ?_ ?_
  · refine (Subgroup.commutator_mono le_rfl (vv_le_qv_of_dist_le_two c.b4 hβ' ?_)).trans
      (commutator_vv_qv_le_zh c.pu h464' hβ)
    rw [tdist_comm]
    exact hd
  · rw [Subgroup.commutator_comm]
    exact (Subgroup.commutator_mono le_rfl (vv_le_qv_of_dist_le_two c.b4 hβ hd)).trans
      (commutator_vv_qv_le_zh c.pu h464' hβ')

theorem card_usup_inf_usup (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {γ β β' : Vtx (puAmalgam c.pu.le)} (hγ : IsMVtx (puAmalgam c.pu.le) γ)
    (hγβ : (puAmalgam c.pu.le).treeGraph.Adj γ β) (hγβ' : (puAmalgam c.pu.le).treeGraph.Adj γ β')
    (hne : Usup (puAmalgam c.pu.le) γ β ≠ Usup _ γ β') :
    Nat.card ↥(Usup (puAmalgam c.pu.le) γ β ⊓ Usup _ γ β') = Fintype.card F := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc c.pu c.via hγ
  have hWU := usup_le_uloc' c.pu hfull hγ hγβ
  have hWU' := usup_le_uloc' c.pu hfull hγ hγβ'
  have hm := mem_usup_iff c.pu c.via h464' hsq hγ hγβ hψ
  have hm' := mem_usup_iff c.pu c.via h464' hsq hγ hγβ' hψ
  have hne' : fixN (natImage ψ (Qv (puAmalgam c.pu.le) β)) ≠ fixN (natImage ψ (Qv _ β')) :=
    fun heq => hne ((S45.eq_iff_of_natVec_iff hψ hWU hWU' hm hm').mpr heq)
  have h1 := S45.finrank_inf_eq_one (I466b.fixN_natImage_qv c.pu c.via h464' hsq hγ hγβ hψ).1
    (I466b.fixN_natImage_qv c.pu c.via h464' hsq hγ hγβ' hψ).1 hne'
  rw [S45.card_eq_of_natVec_iff hψ (inf_le_left.trans hWU)
    (W := fixN (natImage ψ (Qv _ β)) ⊓ fixN (natImage ψ (Qv _ β'))) (fun v => by
      rw [Subgroup.mem_inf, hm, hm', Submodule.mem_inf]), Module.natCard_eq_pow_finrank (K := F),
    h1, pow_one, Nat.card_eq_fintype_card]

theorem zh_inf_zh_eq (h464 : I464) (h465 : I465) (c : Hyp46 M T L φ)
    {γ β β' : Vtx (puAmalgam c.pu.le)} (hγ : IsMVtx (puAmalgam c.pu.le) γ)
    (hγβ : (puAmalgam c.pu.le).treeGraph.Adj γ β) (hγβ' : (puAmalgam c.pu.le).treeGraph.Adj γ β') :
    ZH (puAmalgam c.pu.le) β ⊓ ZH _ β' =
      (Usup (puAmalgam c.pu.le) γ β ⊓ Usup _ γ β') ⊔ Zloc c.pu.le L γ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  set U := Usup (puAmalgam c.pu.le) γ β with hUdef
  set U' := Usup (puAmalgam c.pu.le) γ β' with hU'def
  set Z := Zloc c.pu.le L γ with hZdef
  set W := Uloc c.pu.le L γ with hWdef
  have hUW : U ≤ W := usup_le_uloc' c.pu hfull hγ hγβ
  have hU'W : U' ≤ W := usup_le_uloc' c.pu hfull hγ hγβ'
  have hWs : W ≤ stab (puAmalgam c.pu.le) γ := puTrans_le_stab c.pu.le _ γ
  have hZc : Z ≤ Subgroup.centralizer (stab (puAmalgam c.pu.le) γ : Set _) :=
    zloc_le_centralizer_stab c.pu hfull hγ
  have hZnU : Z ≤ Subgroup.normalizer (U : Set _) :=
    (hZc.trans (Subgroup.centralizer_le (hUW.trans hWs))).trans
      (Subgroup.centralizer_le_normalizer _)
  have hU'nZ : U' ≤ Subgroup.normalizer (Z : Set _) :=
    (hU'W.trans hWs).trans ((Subgroup.le_centralizer_iff.mp hZc).trans
      (Subgroup.centralizer_le_normalizer _))
  have hWZ : Z ⊓ W = ⊥ := by rw [inf_comm]; exact uloc_inf_zloc c.pu hfull γ
  rw [zh_eq_usup_sup_zloc c.pu c.via h464' hsq hγ hγβ,
    zh_eq_usup_sup_zloc c.pu c.via h464' hsq hγ hγβ', ← hUdef, ← hU'def, ← hZdef]
  have h1 : (Z ⊔ U) ⊓ (U' ⊔ Z) = Z ⊔ (U ⊓ (U' ⊔ Z)) :=
    S45.sup_inf_eq_of_le le_sup_right hZnU
  have h2 : (U' ⊔ Z) ⊓ W = U' ⊔ (Z ⊓ W) := S45.sup_inf_eq_of_le hU'W hU'nZ
  have h3 : U ⊓ (U' ⊔ Z) = U ⊓ U' := by
    have e : U ⊓ (U' ⊔ Z) = U ⊓ ((U' ⊔ Z) ⊓ W) := by
      rw [inf_comm (U' ⊔ Z) W, ← inf_assoc, inf_of_le_left hUW]
    rw [e, h2, hWZ, sup_bot_eq]
  rw [sup_comm U Z, h1, h3, sup_comm]

theorem qv_eq_of_usup_eq (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {γ β β' : Vtx (puAmalgam c.pu.le)} (hγ : IsMVtx (puAmalgam c.pu.le) γ)
    (hγβ : (puAmalgam c.pu.le).treeGraph.Adj γ β) (hγβ' : (puAmalgam c.pu.le).treeGraph.Adj γ β')
    (heq : Usup (puAmalgam c.pu.le) γ β = Usup _ γ β') :
    Qv (puAmalgam c.pu.le) β = Qv _ β' := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have h464' := h464 G M T L F φ c
  have hsq : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      Nat.card ↥(Usup (puAmalgam c.pu.le) δ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    (h465 G M T L F φ c δ ρ hδ hδρ).1
  have h466 : ∀ δ ρ : Vtx (puAmalgam c.pu.le), IsMVtx _ δ → (puAmalgam c.pu.le).treeGraph.Adj δ ρ →
      (Qv (puAmalgam c.pu.le) δ).relIndex (Qv _ ρ) = Fintype.card F ^ 2 := fun δ ρ hδ hδρ =>
    h466a G M T L F φ c δ ρ hδ hδρ
  obtain ⟨ψ, -, hψ⟩ := exists_natural_Uloc c.pu c.via hγ
  have hm := mem_usup_iff c.pu c.via h464' hsq hγ hγβ hψ
  have hm' := mem_usup_iff c.pu c.via h464' hsq hγ hγβ' hψ
  have hfix : fixN (natImage ψ (Qv (puAmalgam c.pu.le) β)) = fixN (natImage ψ (Qv _ β')) :=
    (S45.eq_iff_of_natVec_iff hψ (usup_le_uloc' c.pu hfull hγ hγβ)
      (usup_le_uloc' c.pu hfull hγ hγβ') hm hm').mp heq
  have himg : natImage ψ (Qv (puAmalgam c.pu.le) β) = natImage ψ (Qv _ β') := by
    rw [I466b.natImage_qv_eq_axisGroup c.pu c.via h464' hsq h466 hγ hγβ hψ,
      I466b.natImage_qv_eq_axisGroup c.pu c.via h464' hsq h466 hγ hγβ' hψ, hfix]
  have key : ∀ {ρ ρ' : Vtx (puAmalgam c.pu.le)}, (puAmalgam c.pu.le).treeGraph.Adj γ ρ →
      (puAmalgam c.pu.le).treeGraph.Adj γ ρ' →
      natImage ψ (Qv (puAmalgam c.pu.le) ρ) = natImage ψ (Qv _ ρ') →
      Qv (puAmalgam c.pu.le) ρ ≤ Qv _ ρ' := by
    intro ρ ρ' hρ hρ' hi t ht
    have hts : t ∈ stab (puAmalgam c.pu.le) γ := qv_le_stab_of_adj _ hρ.symm ht
    have hmem : toSL3 ψ ⟨t, hts⟩ ∈ natImage ψ (Qv (puAmalgam c.pu.le) ρ') :=
      hi ▸ mem_natImage.mpr ⟨⟨t, hts⟩, ht, rfl⟩
    obtain ⟨a, ha, hae⟩ := mem_natImage.mp hmem
    have hk : ((a⁻¹ * ⟨t, hts⟩ : ↥(stab (puAmalgam c.pu.le) γ)) : (puAmalgam c.pu.le).Universal) ∈
        Qv (puAmalgam c.pu.le) γ :=
      (toSL3_eq_one_iff_mem_qv c.pu c.via hγ hψ _).mp
        (by rw [map_mul, map_inv, hae, inv_mul_cancel])
    have e : t = (a : (puAmalgam c.pu.le).Universal) *
        ((a⁻¹ * ⟨t, hts⟩ : ↥(stab (puAmalgam c.pu.le) γ)) : (puAmalgam c.pu.le).Universal) := by
      simp
    rw [e]
    exact Subgroup.mul_mem _ ha (qv_le_qv _ c.pu.hyp20 hγ hρ' hk)
  exact le_antisymm (key hγβ hγβ' himg) (key hγβ' hγβ himg.symm)

theorem vv_eq_of_usup_eq (h464 : I464) (h465 : I465) (h466a : I466a) (c : Hyp46 M T L φ)
    {γ β β' : Vtx (puAmalgam c.pu.le)} (hγ : IsMVtx (puAmalgam c.pu.le) γ)
    (hγβ : (puAmalgam c.pu.le).treeGraph.Adj γ β) (hγβ' : (puAmalgam c.pu.le).treeGraph.Adj γ β')
    (heq : Usup (puAmalgam c.pu.le) γ β = Usup _ γ β') :
    Vv (puAmalgam c.pu.le) β = Vv _ β' := by
  have hβ : ¬ IsMVtx (puAmalgam c.pu.le) β := (isMVtx_iff_of_adj _ hγβ).mp hγ
  obtain ⟨k, hk, rfl⟩ := I467.exists_mem_stab_smul_eq hγ hγβ hγβ'
  have hQ := qv_eq_of_usup_eq h464 h465 h466a c hγ hγβ hγβ' heq
  have hkn : k ∈ Subgroup.normalizer (Qv (puAmalgam c.pu.le) β : Set _) := by
    rw [Subgroup.mem_normalizer_iff]
    intro t
    have hmap : (Qv (puAmalgam c.pu.le) β).map (MulAut.conj k).toMonoidHom = Qv _ β := by
      rw [← qv_smul, ← hQ]
    constructor
    · intro ht
      rw [← hmap]
      exact ⟨t, ht, rfl⟩
    · intro ht
      rw [← hmap] at ht
      obtain ⟨t', ht', he⟩ := ht
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_left_inj, mul_right_inj] at he
      rwa [← he]
  exact (vv_smul_eq_of_mem_normalizer c.pu hβ hkn).symm

theorem commutator_vv_pencil_le (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) {γ β : Vtx (puAmalgam c.pu.le)} (hγ : IsMVtx (puAmalgam c.pu.le) γ)
    (hγβ : (puAmalgam c.pu.le).treeGraph.Adj γ β) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hPU : P ≤ Usup (puAmalgam c.pu.le) γ β) (hPc : Nat.card ↥P = Fintype.card F) :
    ⁅Vv (puAmalgam c.pu.le) β, pencil _ γ P⁆ ≤ P ⊔ Zloc c.pu.le L γ := by
  have hfull : IsSL3Full M T L := isSL3Full_iff_exists_via.mpr ⟨F, _, _, φ, c.via⟩
  have hb : 2 < critDist (puAmalgam c.pu.le) := by have := c.b4; omega
  have h464' := h464 G M T L F φ c
  have hβ : ¬ IsMVtx (puAmalgam c.pu.le) β := (isMVtx_iff_of_adj _ hγβ).mp hγ
  have hZc : Zloc c.pu.le L γ ≤ Subgroup.centralizer (stab (puAmalgam c.pu.le) γ : Set _) :=
    zloc_le_centralizer_stab c.pu hfull hγ
  rw [Subgroup.commutator_comm]
  have hpen : pencil (puAmalgam c.pu.le) γ P = ⨆ β', ⨆ (_ : (puAmalgam c.pu.le).treeGraph.Adj γ β' ∧
      P ≤ Usup (puAmalgam c.pu.le) γ β'), Vv (puAmalgam c.pu.le) β' := by
    refine le_antisymm (pencil_le fun β' hβ' hP => le_iSup₂_of_le β' ⟨hβ', hP⟩ le_rfl)
      (iSup₂_le fun β' h => vv_le_pencil h.1 h.2)
  rw [hpen]
  refine I467.commutator_biSup_le_of (fun β' hb' => ?_) (fun β' hb' => ?_)
  · obtain ⟨hγβ', hPβ'⟩ := hb'
    have hβ' : ¬ IsMVtx (puAmalgam c.pu.le) β' := (isMVtx_iff_of_adj _ hγβ').mp hγ
    by_cases hU : Usup (puAmalgam c.pu.le) γ β = Usup _ γ β'
    · rw [← vv_eq_of_usup_eq h464 h465 h466a c hγ hγβ hγβ' hU]
      have h1 : ⁅Vv (puAmalgam c.pu.le) β, Vv _ β⁆ = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
          (vv_le_centralizer_of_not_isMVtx c.pu.hyp20 hb hβ)
      rw [h1]
      exact bot_le
    · have hββ' : β ≠ β' := fun e => hU (e ▸ rfl)
      have hd : (puAmalgam c.pu.le).treeGraph.dist β' β ≤ 2 :=
        (dist_eq_two_of_adj_adj _ hγβ'.symm hγβ (Ne.symm hββ')).le
      have hcard := card_usup_inf_usup h464 h465 c hγ hγβ hγβ' hU
      have : Finite ↥(Usup (puAmalgam c.pu.le) γ β ⊓ Usup _ γ β') :=
        Nat.finite_of_card_ne_zero (by rw [hcard]; exact Fintype.card_ne_zero)
      have hPeq : P = Usup (puAmalgam c.pu.le) γ β ⊓ Usup _ γ β' :=
        Subgroup.eq_of_le_of_card_ge (le_inf hPU hPβ') (by rw [hcard, hPc])
      refine (commutator_vv_vv_le_zh_inf h464 c hβ' hβ hd).trans ?_
      rw [inf_comm, zh_inf_zh_eq h464 h465 c hγ hγβ hγβ', ← hPeq]
  · obtain ⟨hγβ', hPβ'⟩ := hb'
    have hβ' : ¬ IsMVtx (puAmalgam c.pu.le) β' := (isMVtx_iff_of_adj _ hγβ').mp hγ
    have hVT : Vv (puAmalgam c.pu.le) β' ≤ Qv _ β' := by
      have := vv_le_qv_of_dist_le_two c.b4 hβ' (μ := β') (by simp)
      exact this
    refine hVT.trans (le_trans (le_inf ?_ ?_) (Subgroup.inf_normalizer_le_normalizer_sup _ _))
    · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have hpZ : p ∈ ZH (puAmalgam c.pu.le) β' := h464' γ β' hγ hγβ' (hPβ' hp)
      exact (Subgroup.mem_centralizer_iff.mp (zh_le_centralizer _ β' hpZ) t ht).symm
    · exact (qv_le_stab_of_adj _ hγβ'.symm).trans ((Subgroup.le_centralizer_iff.mp hZc).trans
        (Subgroup.centralizer_le_normalizer _))

theorem commutator_zm_pencil_le (h464 : I464) (h465 : I465) (h466a : I466a)
    (c : Hyp46 M T L φ) {α γ β : Vtx (puAmalgam c.pu.le)} (hα : IsMVtx (puAmalgam c.pu.le) α)
    (hαβ : (puAmalgam c.pu.le).treeGraph.Adj α β) (hγ : IsMVtx (puAmalgam c.pu.le) γ)
    (hγβ : (puAmalgam c.pu.le).treeGraph.Adj γ β) {P : Subgroup (puAmalgam c.pu.le).Universal}
    (hPU : P ≤ Usup (puAmalgam c.pu.le) γ β) (hPc : Nat.card ↥P = Fintype.card F) :
    ⁅ZM (puAmalgam c.pu.le) α, pencil _ γ P⁆ ≤
      (P ⊔ Zloc c.pu.le L γ) ⊓ Usup (puAmalgam c.pu.le) α β := by
  have hβ : ¬ IsMVtx (puAmalgam c.pu.le) β := (isMVtx_iff_of_adj _ hγβ).mp hγ
  refine le_inf ((Subgroup.commutator_mono (zm_le_vv_of_adj hαβ.symm hα) le_rfl).trans
    (commutator_vv_pencil_le h464 h465 h466a c hγ hγβ hPU hPc)) ?_
  rw [Usup, zv_of_isMVtx _ hα]
  refine Subgroup.commutator_mono le_rfl (pencil_le fun β' hγβ' _ => ?_)
  have hβ' : ¬ IsMVtx (puAmalgam c.pu.le) β' := (isMVtx_iff_of_adj _ hγβ').mp hγ
  refine vv_le_qv_of_dist_le_two c.b4 hβ' ?_
  by_cases he : β' = β
  · rw [he]; simp
  · exact (dist_eq_two_of_adj_adj _ hγβ'.symm hγβ he).le
