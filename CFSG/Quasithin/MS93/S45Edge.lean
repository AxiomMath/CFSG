module

public import CFSG.Quasithin.MS93.S45Loc
import CFSG.Quasithin.MS93.S4A42i

public section

namespace CFSG.Quasithin.MS93.S45

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Fintype F]

theorem sup_inf_eq_of_le {K : Type*} [Group K] {A B C : Subgroup K} (hAC : A ≤ C)
    (hn : A ≤ Subgroup.normalizer (B : Set K)) : (A ⊔ B) ⊓ C = A ⊔ (B ⊓ C) := by
  have hn' : A ≤ Subgroup.normalizer ((B ⊓ C : Subgroup K) : Set K) := by
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simp only [Subgroup.mem_inf]
    constructor
    · rintro ⟨hxB, hxC⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hn ha) x).mp hxB,
        C.mul_mem (C.mul_mem (hAC ha) hxC) (C.inv_mem (hAC ha))⟩
    · rintro ⟨hxB, hxC⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hn ha) x).mpr hxB, ?_⟩
      have : x = a⁻¹ * (a * x * a⁻¹) * a := by group
      rw [this]
      exact C.mul_mem (C.mul_mem (C.inv_mem (hAC ha)) hxC) (hAC ha)
  apply SetLike.coe_injective
  rw [Subgroup.coe_inf, Subgroup.coe_mul_of_left_le_normalizer_right A B hn,
    Subgroup.coe_mul_of_left_le_normalizer_right A _ hn', Subgroup.mul_inf_assoc A B C hAC]

theorem fixN_eq_commN_of_card [CharP F 2] {A : Subgroup (SL3 F)} (hA2 : IsPGroup 2 A)
    (hA : Nat.card A = Fintype.card F ^ 2) (hfix : Fintype.card F ^ 2 ≤ Nat.card (fixN A)) :
    fixN A = commN A ∧ Module.finrank F (fixN A) = 2 := by
  have hq1 : 1 < Fintype.card F := Fintype.one_lt_card
  have hcardF : Nat.card F = Fintype.card F := Nat.card_eq_fintype_card
  have hne : fixN A ≠ ⊤ := by
    intro htop
    have h1 : A = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro g hg
      have hmat : ((g : SL3 F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
        ext i j
        have hx : Pi.single j 1 ∈ fixN A := htop ▸ Submodule.mem_top
        have := congrFun (hx g hg) i
        simpa [Matrix.mulVec_single_one, Matrix.one_apply, Pi.single_apply, eq_comm] using this
      exact Subtype.ext hmat
    rw [h1, Subgroup.card_bot] at hA
    have : 1 < Fintype.card F ^ 2 := Nat.one_lt_pow (by norm_num) hq1
    omega
  have hfr3 : Module.finrank F (Fin 3 → F) = 3 := Module.finrank_fin_fun F
  have hlt : Module.finrank F (fixN A) < 3 := by
    exact (Submodule.finrank_lt hne).trans_eq hfr3
  have hge : 2 ≤ Module.finrank F (fixN A) := by
    by_contra hlt2
    have h1 : Nat.card (fixN A) = Nat.card F ^ Module.finrank F (fixN A) :=
      Module.natCard_eq_pow_finrank
    rw [h1, hcardF] at hfix
    have := Nat.pow_lt_pow_right hq1 (show Module.finrank F (fixN A) < 2 by omega)
    omega
  have hfix2 : Module.finrank F (fixN A) = 2 := by omega
  have hcomm2 : Module.finrank F (commN A) = 2 := by
    have hle : Module.finrank F (commN A) ≤ 2 := by
      obtain ⟨x, hx⟩ := exists_conj_le_sStar hA2
      rw [← finrank_commN_map_conj x A, ← finrank_ln01 (F := F)]
      exact Submodule.finrank_mono (commN_le_ln01_of_le_sStar hx)
    have hbound := card_le_pow_finrank A
    rw [hfix2, hA, Nat.card_eq_fintype_card (α := F)] at hbound
    by_contra hne2
    have hlt2 : Module.finrank F (commN A) < 2 := by omega
    have := Nat.pow_lt_pow_right hq1 (show (3 - 2) * Module.finrank F (commN A) < 2 by omega)
    omega
  have hle : fixN A ≤ commN A :=
    le_commN_of_invariant hA2 hcomm2 (fun g hg x hx => by rw [hx g hg]; exact hx) hne
  exact ⟨Submodule.eq_of_le_of_finrank_eq hle (by rw [hfix2, hcomm2]), hfix2⟩

omit [Finite G] [Fintype F] in
theorem card_eq_of_natVec_iff {K V : Subgroup G} {ψ : ↥K →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia K V ⊥ ψ false 1) {S : Subgroup G} (hSV : S ≤ V)
    {W : Submodule F (Fin 3 → F)} (hW : ∀ v : ↥V, (v : G) ∈ S ↔ natVec hψ v ∈ W) :
    Nat.card ↥S = Nat.card ↥W := by
  let e1 : ↥S ≃ {v : ↥V // (v : G) ∈ S} :=
    { toFun := fun x => ⟨⟨x, hSV x.2⟩, x.2⟩
      invFun := fun x => ⟨x.1, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let e2 : {v : ↥V // (v : G) ∈ S} ≃ {x : Fin 3 → F // x ∈ W} :=
    Equiv.subtypeEquiv (Equiv.ofBijective (natVec hψ) (natVec_bijective hψ)) fun v => hW v
  rw [Nat.card_congr (e1.trans e2)]

omit [Finite G] [Fintype F] in
theorem eq_iff_of_natVec_iff {K V : Subgroup G} {ψ : ↥K →* ↥(StatedSL 3 F)}
    (hψ : IsSumOfNaturalModulesVia K V ⊥ ψ false 1) {S S' : Subgroup G} (hSV : S ≤ V)
    (hS'V : S' ≤ V) {W W' : Submodule F (Fin 3 → F)}
    (hW : ∀ v : ↥V, (v : G) ∈ S ↔ natVec hψ v ∈ W)
    (hW' : ∀ v : ↥V, (v : G) ∈ S' ↔ natVec hψ v ∈ W') : S = S' ↔ W = W' := by
  constructor
  · rintro rfl
    ext x
    obtain ⟨v, rfl⟩ := natVec_surjective hψ x
    rw [← hW, ← hW']
  · rintro rfl
    ext x
    constructor
    · intro hx
      have := (hW ⟨x, hSV hx⟩).mp hx
      exact (hW' ⟨x, hSV hx⟩).mpr this
    · intro hx
      have := (hW' ⟨x, hS'V hx⟩).mp hx
      exact (hW ⟨x, hS'V hx⟩).mpr this

omit [Fintype F] in
theorem finrank_inf_eq_one {W W' : Submodule F (Fin 3 → F)} (hW : Module.finrank F W = 2)
    (hW' : Module.finrank F W' = 2) (hne : W ≠ W') : Module.finrank F ↥(W ⊓ W') = 1 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq W W'
  have hle : Module.finrank F ↥(W ⊔ W') ≤ 3 := by
    have := Submodule.finrank_le (W ⊔ W')
    rwa [Module.finrank_fin_fun] at this
  have hlt : 2 < Module.finrank F ↥(W ⊔ W') := by
    by_contra hge
    have h1 : W = W ⊔ W' := Submodule.eq_of_le_of_finrank_le le_sup_left (by omega)
    have h2 : W' = W ⊔ W' := Submodule.eq_of_le_of_finrank_le le_sup_right (by omega)
    exact hne (h1.trans h2.symm)
  omega

namespace Ctx

variable {M T L : Subgroup G} {φ : ↥M →* ↥(StatedSL 3 F)} (c : Ctx M T L φ)
include c

theorem qv_inf_centralizer_uloc {δ ρ : Vtx (puAmalgam c.hyp.le)} (hδ : IsMVtx _ δ)
    (hρ : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ) :
    Qv _ ρ ⊓ Subgroup.centralizer (Uloc c.hyp.le L δ : Set (puAmalgam c.hyp.le).Universal) =
      Qv _ δ := by
  have hC := c.cent δ ρ hδ hρ
  have hT : Qv (puAmalgam c.hyp.le) ρ ≤ stab _ δ := qv_le_stab_of_adj _ hρ.symm
  rw [← hC]
  ext x
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hx, hxc⟩
    exact ⟨hx, (mem_centralizer_zm_iff c.hyp c.full hδ (hT hx)).mpr hxc⟩
  · rintro ⟨hx, hxc⟩
    exact ⟨hx, (mem_centralizer_zm_iff c.hyp c.full hδ (hT hx)).mp hxc⟩

variable {δ ρ : Vtx (puAmalgam c.hyp.le)} {ψ : ↥(stab (puAmalgam c.hyp.le) δ) →* ↥(StatedSL 3 F)}

theorem card_natImage_qv
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1)
    (hδ : IsMVtx _ δ) (hρ : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ) :
    Nat.card ↥(natImage ψ (Qv _ ρ)) = Fintype.card F ^ 2 := by
  have h20 := c.hyp.hyp20
  have hT : Qv (puAmalgam c.hyp.le) ρ ≤ stab _ δ := qv_le_stab_of_adj _ hρ.symm
  have h1 := card_natImage_mul hψ hT
  rw [c.qv_inf_centralizer_uloc hδ hρ] at h1
  have hQle : Qv (puAmalgam c.hyp.le) δ ≤ Qv _ ρ := qv_le_qv _ h20 hδ hρ
  have h2 := Subgroup.relIndex_mul_card (H := Qv (puAmalgam c.hyp.le) δ) (K := Qv _ ρ)
  rw [inf_of_le_left hQle, c.relIndex_qv hδ hρ] at h2
  have hfin : Finite ↥(Qv (puAmalgam c.hyp.le) δ) := by
    have := S4A.finite_stab c.hyp hδ
    exact Finite.of_injective _ (Subgroup.inclusion_injective (qv_le_stab _ δ))
  have hpos : 0 < Nat.card ↥(Qv (puAmalgam c.hyp.le) δ) := Nat.card_pos
  rw [← h2] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos h1

theorem le_card_fixN_qv
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1)
    (hδ : IsMVtx _ δ) (hρ : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ) :
    Fintype.card F ^ 2 ≤ Nat.card ↥(fixN (natImage ψ (Qv _ ρ))) := by
  have h := c.hyp
  have hT : Qv (puAmalgam h.le) ρ ≤ stab _ δ := qv_le_stab_of_adj _ hρ.symm
  rw [← card_inf_centralizer_eq hψ hT]
  set U := Uloc h.le L δ
  set Z := Zloc h.le L δ
  set C := Subgroup.centralizer (Qv (puAmalgam h.le) ρ : Set (puAmalgam h.le).Universal)
  have hZM : ZM (puAmalgam h.le) δ = U ⊔ Z := zm_eq_uloc_sup_zloc h c.full hδ
  have hUZ : U ⊓ Z = ⊥ := uloc_inf_zloc h c.full δ
  have hZc : Z ≤ C := (zloc_le_centralizer_stab h c.full hδ).trans
    (Subgroup.centralizer_le hT)
  have hZcU : Z ≤ Subgroup.centralizer (U : Set (puAmalgam h.le).Universal) :=
    (zloc_le_centralizer_stab h c.full hδ).trans (Subgroup.centralizer_le
      ((uloc_le_zm h c.full hδ).trans ((zm_le_qv_self _ hδ h.critDist_pos).trans
        (qv_le_stab _ δ))))
  have hZcU' : Z ≤ Subgroup.centralizer ((U ⊓ C : Subgroup _) : Set (puAmalgam h.le).Universal) :=
    hZcU.trans (Subgroup.centralizer_le inf_le_left)
  have hZρ : ZH (puAmalgam h.le) ρ ≤ (U ⊓ C) ⊔ Z := by
    have h1 : ZH (puAmalgam h.le) ρ ≤ ZM _ δ ⊓ C :=
      le_inf (zh_le_zm _ hρ) (zh_le_centralizer _ ρ)
    have h2 : ZM (puAmalgam h.le) δ ⊓ C = (U ⊓ C) ⊔ Z := by
      rw [hZM, sup_comm, sup_inf_eq_of_le hZc (hZcU.trans
        (Subgroup.centralizer_le_normalizer _)), sup_comm]
    exact h1.trans h2.le
  have hfinZ : Finite ↥(ZM (puAmalgam h.le) δ) := by
    have := S4A.finite_stab h hδ
    exact Finite.of_injective _ (Subgroup.inclusion_injective
      ((zm_le_qv_self _ hδ h.critDist_pos).trans (qv_le_stab _ δ)))
  have hfinZl : Finite ↥Z :=
    Finite.of_injective _ (Subgroup.inclusion_injective (zloc_le_zm h c.full hδ))
  have hcardZM : Nat.card ↥(ZM (puAmalgam h.le) δ) = Fintype.card F ^ 3 * Nat.card ↥Z := by
    rw [hZM, card_sup_of_commute hZcU hUZ, card_eq_of_natural hψ, Nat.card_eq_fintype_card]
  have hcardZρ : Nat.card ↥(ZH (puAmalgam h.le) ρ) * Fintype.card F =
      Nat.card ↥(ZM (puAmalgam h.le) δ) := by
    have := Subgroup.relIndex_mul_card (H := ZH (puAmalgam h.le) ρ) (K := ZM _ δ)
    rw [inf_of_le_left (zh_le_zm _ hρ), c.relIndex_zh hδ hρ] at this
    rw [← this, mul_comm]
  have hfinUC : Finite ↥((U ⊓ C) ⊔ Z) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (sup_le (inf_le_left.trans
      (uloc_le_zm h c.full hδ)) (zloc_le_zm h c.full hδ)))
  have hle := Subgroup.card_le_of_le hZρ
  rw [card_sup_of_commute hZcU' (by rw [inf_right_comm, hUZ, bot_inf_eq])] at hle
  have hZpos : 0 < Nat.card ↥Z := Nat.card_pos
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have key : Fintype.card F ^ 3 * Nat.card ↥Z ≤
      Fintype.card F * (Nat.card ↥(U ⊓ C) * Nat.card ↥Z) := by
    rw [← hcardZM, ← hcardZρ, mul_comm]
    exact Nat.mul_le_mul_left _ hle
  have key2 : Fintype.card F ^ 2 * Fintype.card F * Nat.card ↥Z ≤
      Nat.card ↥(U ⊓ C) * Fintype.card F * Nat.card ↥Z := by
    calc Fintype.card F ^ 2 * Fintype.card F * Nat.card ↥Z
        = Fintype.card F ^ 3 * Nat.card ↥Z := by ring
      _ ≤ Fintype.card F * (Nat.card ↥(U ⊓ C) * Nat.card ↥Z) := key
      _ = Nat.card ↥(U ⊓ C) * Fintype.card F * Nat.card ↥Z := by ring
  have := Nat.le_of_mul_le_mul_right key2 hZpos
  exact Nat.le_of_mul_le_mul_right this hq

theorem fixN_eq_commN_qv
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1)
    (hδ : IsMVtx _ δ) (hρ : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ) :
    fixN (natImage ψ (Qv _ ρ)) = commN (natImage ψ (Qv _ ρ)) ∧
      Module.finrank F (fixN (natImage ψ (Qv _ ρ))) = 2 := by
  have := c.charP
  have hρH : ¬ IsMVtx (puAmalgam c.hyp.le) ρ := by
    have := (isMVtx_iff_of_adj _ hρ).mp hδ; exact this
  have h2 : IsPGroup 2 ↥(natImage ψ (Qv (puAmalgam c.hyp.le) ρ)) := by
    have hp := isPGroup_qv _ c.hyp.hyp20 hρH
    have hT : Qv (puAmalgam c.hyp.le) ρ ≤ stab _ δ := qv_le_stab_of_adj _ hρ.symm
    exact (hp.of_equiv (Subgroup.subgroupOfEquivOfLe hT).symm).map (toSL3 ψ)
  exact fixN_eq_commN_of_card h2 (c.card_natImage_qv hψ hδ hρ) (c.le_card_fixN_qv hψ hδ hρ)

theorem usup_eq_uloc_inf_centralizer
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1)
    (hδ : IsMVtx _ δ) (hρ : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ) :
    Usup _ δ ρ = Uloc c.hyp.le L δ ⊓
      Subgroup.centralizer (Qv _ ρ : Set (puAmalgam c.hyp.le).Universal) := by
  have hT : Qv (puAmalgam c.hyp.le) ρ ≤ stab _ δ := qv_le_stab_of_adj _ hρ.symm
  have hE := (c.fixN_eq_commN_qv hψ hδ hρ).1
  rw [S4A.usup_eq_commutator_uloc c.hyp c.full hδ hρ]
  have hUT : ⁅Uloc c.hyp.le L δ, Qv (puAmalgam c.hyp.le) ρ⁆ ≤ Uloc c.hyp.le L δ :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (hT.trans hψ.1)
  ext x
  constructor
  · intro hx
    refine ⟨hUT hx, ?_⟩
    have := (S4A.mem_commutator_iff_natVec hψ hT ⟨x, hUT hx⟩).mp hx
    rw [← hE] at this
    exact (S4A.mem_centralizer_iff_natVec hψ hT ⟨x, hUT hx⟩).mpr this
  · rintro ⟨hxU, hxc⟩
    have := (S4A.mem_centralizer_iff_natVec hψ hT ⟨x, hxU⟩).mp hxc
    rw [hE] at this
    exact (S4A.mem_commutator_iff_natVec hψ hT ⟨x, hxU⟩).mpr this

theorem card_usup
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1)
    (hδ : IsMVtx _ δ) (hρ : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ) :
    Nat.card ↥(Usup (puAmalgam c.hyp.le) δ ρ) = Fintype.card F ^ 2 := by
  have hT : Qv (puAmalgam c.hyp.le) ρ ≤ stab _ δ := qv_le_stab_of_adj _ hρ.symm
  rw [c.usup_eq_uloc_inf_centralizer hψ hδ hρ, card_inf_centralizer_eq hψ hT, card_fixN,
    (c.fixN_eq_commN_qv hψ hδ hρ).2, Nat.card_eq_fintype_card]

theorem zh_eq_usup_sup_zloc
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1)
    (hδ : IsMVtx _ δ) (hρ : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ) :
    ZH _ ρ = Usup _ δ ρ ⊔ Zloc c.hyp.le L δ := by
  have h := c.hyp
  have hT : Qv (puAmalgam h.le) ρ ≤ stab _ δ := qv_le_stab_of_adj _ hρ.symm
  set U := Uloc h.le L δ
  set Z := Zloc h.le L δ
  have hZM : ZM (puAmalgam h.le) δ = U ⊔ Z := zm_eq_uloc_sup_zloc h c.full hδ
  have hUZ : U ⊓ Z = ⊥ := uloc_inf_zloc h c.full δ
  have hZcU : Z ≤ Subgroup.centralizer (U : Set (puAmalgam h.le).Universal) :=
    (zloc_le_centralizer_stab h c.full hδ).trans (Subgroup.centralizer_le
      ((uloc_le_zm h c.full hδ).trans ((zm_le_qv_self _ hδ h.critDist_pos).trans
        (qv_le_stab _ δ))))
  have hW := c.usup_eq_uloc_inf_centralizer hψ hδ hρ
  have hWU : Usup (puAmalgam h.le) δ ρ ≤ U := hW ▸ inf_le_left
  have hZc : Z ≤ Subgroup.centralizer (Qv (puAmalgam h.le) ρ : Set _) :=
    (zloc_le_centralizer_stab h c.full hδ).trans (Subgroup.centralizer_le hT)
  have hle : ZH (puAmalgam h.le) ρ ≤ Usup _ δ ρ ⊔ Z := by
    have h1 : ZH (puAmalgam h.le) ρ ≤ ZM _ δ ⊓ Subgroup.centralizer (Qv _ ρ : Set _) :=
      le_inf (zh_le_zm _ hρ) (zh_le_centralizer _ ρ)
    rw [hZM, sup_comm, sup_inf_eq_of_le hZc (hZcU.trans (Subgroup.centralizer_le_normalizer _)),
      sup_comm, ← hW] at h1
    exact h1
  have hfinZ : Finite ↥(ZM (puAmalgam h.le) δ) := by
    have := S4A.finite_stab h hδ
    exact Finite.of_injective _ (Subgroup.inclusion_injective
      ((zm_le_qv_self _ hδ h.critDist_pos).trans (qv_le_stab _ δ)))
  have hfinS : Finite ↥(Usup (puAmalgam h.le) δ ρ ⊔ Z) :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      (sup_le (hWU.trans (uloc_le_zm h c.full hδ)) (zloc_le_zm h c.full hδ)))
  have hfinZl : Finite ↥Z :=
    Finite.of_injective _ (Subgroup.inclusion_injective (zloc_le_zm h c.full hδ))
  have hcardZM : Nat.card ↥(ZM (puAmalgam h.le) δ) = Fintype.card F ^ 3 * Nat.card ↥Z := by
    rw [hZM, card_sup_of_commute hZcU hUZ, card_eq_of_natural hψ, Nat.card_eq_fintype_card]
  have hcardZρ : Nat.card ↥(ZH (puAmalgam h.le) ρ) * Fintype.card F =
      Nat.card ↥(ZM (puAmalgam h.le) δ) := by
    have := Subgroup.relIndex_mul_card (H := ZH (puAmalgam h.le) ρ) (K := ZM _ δ)
    rw [inf_of_le_left (zh_le_zm _ hρ), c.relIndex_zh hδ hρ] at this
    rw [← this, mul_comm]
  have hcardS : Nat.card ↥(Usup (puAmalgam h.le) δ ρ ⊔ Z) =
      Fintype.card F ^ 2 * Nat.card ↥Z := by
    rw [card_sup_of_commute (hZcU.trans (Subgroup.centralizer_le hWU))
      (eq_bot_mono (inf_le_inf_right _ hWU) hUZ), c.card_usup hψ hδ hρ]
  have hq : 0 < Fintype.card F := Fintype.card_pos
  have hcardZH : Nat.card ↥(ZH (puAmalgam h.le) ρ) = Fintype.card F ^ 2 * Nat.card ↥Z := by
    have h3 : Nat.card ↥(ZH (puAmalgam h.le) ρ) * Fintype.card F =
        Fintype.card F ^ 2 * Nat.card ↥Z * Fintype.card F := by
      rw [hcardZρ, hcardZM]; ring
    exact Nat.eq_of_mul_eq_mul_right hq h3
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcardS, hcardZH])

theorem uloc_inf_zh
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1)
    (hδ : IsMVtx _ δ) (hρ : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ) :
    Uloc c.hyp.le L δ ⊓ ZH _ ρ = Usup _ δ ρ := by
  have h := c.hyp
  have hW := c.usup_eq_uloc_inf_centralizer hψ hδ hρ
  have hWU : Usup (puAmalgam h.le) δ ρ ≤ Uloc h.le L δ := hW ▸ inf_le_left
  have hUs : Uloc h.le L δ ≤ stab (puAmalgam h.le) δ :=
    (uloc_le_zm h c.full hδ).trans ((zm_le_qv_self _ hδ h.critDist_pos).trans (qv_le_stab _ δ))
  have hn : Usup (puAmalgam h.le) δ ρ ≤ Subgroup.normalizer (Zloc h.le L δ : Set _) :=
    (hWU.trans hUs).trans ((Subgroup.le_centralizer_iff.mp
      (zloc_le_centralizer_stab h c.full hδ)).trans (Subgroup.centralizer_le_normalizer _))
  rw [c.zh_eq_usup_sup_zloc hψ hδ hρ, inf_comm, sup_inf_eq_of_le hWU hn, inf_comm,
    uloc_inf_zloc h c.full δ, sup_bot_eq]

theorem mem_usup_iff
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1)
    (hδ : IsMVtx _ δ) (hρ : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ) (v : ↥(Uloc c.hyp.le L δ)) :
    (v : (puAmalgam c.hyp.le).Universal) ∈ Usup _ δ ρ ↔
      natVec hψ v ∈ fixN (natImage ψ (Qv _ ρ)) := by
  have hT : Qv (puAmalgam c.hyp.le) ρ ≤ stab _ δ := qv_le_stab_of_adj _ hρ.symm
  rw [c.usup_eq_uloc_inf_centralizer hψ hδ hρ, Subgroup.mem_inf,
    ← S4A.mem_centralizer_iff_natVec hψ hT v]
  exact ⟨fun h => h.2, fun h => ⟨v.2, h⟩⟩

theorem card_usup_inf_usup {ρ' : Vtx (puAmalgam c.hyp.le)}
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1)
    (hδ : IsMVtx _ δ) (hρ : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ)
    (hρ' : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ') (hne : Usup _ δ ρ ≠ Usup _ δ ρ') :
    Nat.card ↥(Usup (puAmalgam c.hyp.le) δ ρ ⊓ Usup _ δ ρ') = Fintype.card F := by
  have hWU : Usup (puAmalgam c.hyp.le) δ ρ ≤ Uloc c.hyp.le L δ :=
    (c.usup_eq_uloc_inf_centralizer hψ hδ hρ) ▸ inf_le_left
  have hWU' : Usup (puAmalgam c.hyp.le) δ ρ' ≤ Uloc c.hyp.le L δ :=
    (c.usup_eq_uloc_inf_centralizer hψ hδ hρ') ▸ inf_le_left
  have hne' : fixN (natImage ψ (Qv (puAmalgam c.hyp.le) ρ)) ≠ fixN (natImage ψ (Qv _ ρ')) :=
    fun heq => hne ((eq_iff_of_natVec_iff hψ hWU hWU' (c.mem_usup_iff hψ hδ hρ)
      (c.mem_usup_iff hψ hδ hρ')).mpr heq)
  have h1 := finrank_inf_eq_one (c.fixN_eq_commN_qv hψ hδ hρ).2
    (c.fixN_eq_commN_qv hψ hδ hρ').2 hne'
  rw [card_eq_of_natVec_iff hψ (inf_le_left.trans hWU) (W := fixN (natImage ψ (Qv _ ρ)) ⊓
    fixN (natImage ψ (Qv _ ρ'))) (fun v => by
      rw [Subgroup.mem_inf, c.mem_usup_iff hψ hδ hρ, c.mem_usup_iff hψ hδ hρ',
        Submodule.mem_inf]), Module.natCard_eq_pow_finrank (K := F), h1, pow_one,
    Nat.card_eq_fintype_card]

theorem usup_eq_iff_zh_eq {ρ' : Vtx (puAmalgam c.hyp.le)}
    (hψ : IsSumOfNaturalModulesVia (stab _ δ) (Uloc c.hyp.le L δ) ⊥ ψ false 1)
    (hδ : IsMVtx _ δ) (hρ : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ)
    (hρ' : (puAmalgam c.hyp.le).treeGraph.Adj δ ρ') :
    Usup (puAmalgam c.hyp.le) δ ρ = Usup _ δ ρ' ↔ ZH (puAmalgam c.hyp.le) ρ = ZH _ ρ' := by
  constructor
  · intro heq
    rw [c.zh_eq_usup_sup_zloc hψ hδ hρ, c.zh_eq_usup_sup_zloc hψ hδ hρ', heq]
  · intro heq
    rw [← c.uloc_inf_zh hψ hδ hρ, ← c.uloc_inf_zh hψ hδ hρ', heq]

end Ctx

end CFSG.Quasithin.MS93.S45
