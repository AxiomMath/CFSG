module

public import CFSG.Quasithin.MS93.S4A39

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

section ConjCl

variable {G : Type*} [Group G]

theorem le_conjCl (H K : Subgroup G) : K ≤ conjCl H K :=
  le_iSup₂_of_le (f := fun g (_ : g ∈ H) => K.map (MulAut.conj g).toMonoidHom) 1 H.one_mem
    (map_conj_one K).ge

theorem conjCl_le_of_le {H K : Subgroup G} (hKH : K ≤ H) : conjCl H K ≤ H := by
  refine iSup₂_le fun t ht => ?_
  rintro _ ⟨k, hk, rfl⟩
  exact H.mul_mem (H.mul_mem ht (hKH hk)) (H.inv_mem ht)

theorem le_normalizer_conjCl (H K : Subgroup G) :
    H ≤ Subgroup.normalizer (conjCl H K : Set G) := by
  refine le_normalizer_of_map_conj_le fun s hs => ?_
  rw [conjCl, Subgroup.map_iSup]
  refine iSup_le fun u => ?_
  rw [Subgroup.map_iSup]
  refine iSup_le fun hu => ?_
  rw [map_conj_map_conj]
  exact le_iSup₂_of_le (f := fun g (_ : g ∈ H) => K.map (MulAut.conj g).toMonoidHom) (s * u)
    (H.mul_mem hs hu) le_rfl

theorem commutator_conjCl_le {H K L N : Subgroup G}
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) (hKL : ⁅K, L⁆ ≤ N) :
    ⁅conjCl H K, L⁆ ≤ N := by
  have hnorm : conjCl H K ≤ Subgroup.normalizer (N : Set G) := by
    refine iSup₂_le fun t ht => Subgroup.map_le_iff_le_comap.mpr fun k hk => ?_
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hHN ht) (hKN hk)) (Subgroup.inv_mem _ (hHN ht))
  have heq : conjCl H K = ⨆ t : ↥H, K.map (MulAut.conj (t : G)).toMonoidHom := by
    rw [conjCl, iSup_subtype']
  rw [heq] at hnorm ⊢
  refine commutator_iSup_le_of (fun t => ?_) hnorm
  calc ⁅K.map (MulAut.conj (t : G)).toMonoidHom, L⁆
        = (⁅K, L.map (MulAut.conj (t : G)⁻¹).toMonoidHom⁆).map
            (MulAut.conj (t : G)).toMonoidHom := by
          rw [Subgroup.map_commutator, map_conj_map_conj, mul_inv_cancel, map_conj_one]
      _ = (⁅K, L⁆).map (MulAut.conj (t : G)).toMonoidHom := by
          rw [map_conj_eq_of_mem_normalizer (hHL (H.inv_mem t.2))]
      _ ≤ N.map (MulAut.conj (t : G)).toMonoidHom := Subgroup.map_mono hKL
      _ = N := map_conj_eq_of_mem_normalizer (hHN t.2)

end ConjCl

section Perfect

variable {G : Type} [Group G] [Finite G]

theorem le_of_le_sup_pCoreL {L K : Subgroup G} (hperf : ⁅L, L⁆ = L) (hKL : K ≤ L)
    (hLK : L ≤ Subgroup.normalizer (K : Set G)) (h : L ≤ K ⊔ pCoreL L) : L ≤ K := by
  have : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hperf
  have : (K.subgroupOf L).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hKL).2 hLK
  have hPK : pCoreL L ≤ Subgroup.normalizer (K : Set G) := (pCoreL_le L).trans hLK
  have hset := Subgroup.coe_mul_of_left_le_normalizer_right (pCoreL L) K hPK
  have htop : K.subgroupOf L = ⊤ := by
    refine eq_top_of_pow_mem_of_isPerfect (K.subgroupOf L) fun g => ?_
    have hg : (g : G) ∈ ((pCoreL L ⊔ K : Subgroup G) : Set G) := by
      rw [sup_comm]
      exact h g.2
    rw [hset] at hg
    obtain ⟨p, hp, k, hk, hpk⟩ := hg
    obtain ⟨y, hy, rfl⟩ := hp
    have h2 : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := CFSG.pCore_isPGroup
    obtain ⟨m, hm⟩ := h2 ⟨y, hy⟩
    refine ⟨m, ?_⟩
    have hyk : g = y * ⟨k, hKL hk⟩ := Subtype.ext hpk.symm
    have hk' : (⟨k, hKL hk⟩ : ↥L) ∈ K.subgroupOf L := Subgroup.mem_subgroupOf.mpr hk
    have hy1 : y ^ 2 ^ m = 1 := by
      have := congrArg Subtype.val hm
      simpa using this
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hyk, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff _).mpr hk', mul_one, ← QuotientGroup.mk_pow, hy1,
      QuotientGroup.mk_one]
  intro x hx
  have := htop ▸ Subgroup.mem_top (⟨x, hx⟩ : ↥L)
  exact Subgroup.mem_subgroupOf.mp this

end Perfect

section Emb

variable {G : Type} [Group G] {M T : Subgroup G} (hTM : T ≤ M)

@[expose] noncomputable def vEmb (g : (puAmalgam hTM).Universal) :
    ↥M →* (puAmalgam hTM).Universal :=
  (MulAut.conj g).toMonoidHom.comp (puAmalgam hTM).ofA

theorem vEmb_injective (g : (puAmalgam hTM).Universal) : Function.Injective (vEmb hTM g) :=
  (MulAut.conj g).injective.comp (puAmalgam hTM).ofA_injective

theorem puTrans_eq_map_vEmb {N : Subgroup G} (hN : (N.subgroupOf M).Normal)
    (g : (puAmalgam hTM).Universal) :
    puTrans hTM N (g • baseA _) = (N.subgroupOf M).map (vEmb hTM g) := by
  rw [puTrans_smul_baseA hN, imM, Subgroup.map_map]
  rfl

theorem stab_eq_map_vEmb (g : (puAmalgam hTM).Universal) :
    stab (puAmalgam hTM) (g • baseA _) = (M.subgroupOf M).map (vEmb hTM g) := by
  rw [stab_smul, puAmalgam.stab_baseA, imM, Subgroup.map_map]
  rfl

@[expose] noncomputable def vPull (g : (puAmalgam hTM).Universal)
    (H : Subgroup (puAmalgam hTM).Universal) : Subgroup G :=
  (H.comap (vEmb hTM g)).map M.subtype

theorem vPull_le (g : (puAmalgam hTM).Universal) (H : Subgroup (puAmalgam hTM).Universal) :
    vPull hTM g H ≤ M :=
  Subgroup.map_subtype_le _

theorem vPull_subgroupOf (g : (puAmalgam hTM).Universal)
    (H : Subgroup (puAmalgam hTM).Universal) :
    (vPull hTM g H).subgroupOf M = H.comap (vEmb hTM g) :=
  PU.map_subtype_subgroupOf _

theorem map_vPull {g : (puAmalgam hTM).Universal} {H : Subgroup (puAmalgam hTM).Universal}
    (hH : H ≤ stab (puAmalgam hTM) (g • baseA _)) :
    ((vPull hTM g H).subgroupOf M).map (vEmb hTM g) = H := by
  rw [vPull_subgroupOf, Subgroup.map_comap_eq, inf_eq_right]
  refine hH.trans ?_
  rw [stab_eq_map_vEmb hTM g, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]

theorem vPull_mono (g : (puAmalgam hTM).Universal) {H K : Subgroup (puAmalgam hTM).Universal}
    (hHK : H ≤ K) : vPull hTM g H ≤ vPull hTM g K :=
  Subgroup.map_mono (Subgroup.comap_mono hHK)

theorem vPull_map {g : (puAmalgam hTM).Universal} {N : Subgroup G} (hN : N ≤ M) :
    vPull hTM g ((N.subgroupOf M).map (vEmb hTM g)) = N := by
  rw [vPull, Subgroup.comap_map_eq_self_of_injective (vEmb_injective hTM g),
    Subgroup.map_subgroupOf_eq_of_le hN]

theorem vPull_puTrans {g : (puAmalgam hTM).Universal} {N : Subgroup G} (hNM : N ≤ M)
    (hN : (N.subgroupOf M).Normal) :
    vPull hTM g (puTrans hTM N (g • baseA _)) = N := by
  rw [puTrans_eq_map_vEmb hTM hN, vPull_map hTM hNM]

theorem le_of_vPull_le {g : (puAmalgam hTM).Universal} {H K : Subgroup (puAmalgam hTM).Universal}
    (hH : H ≤ stab (puAmalgam hTM) (g • baseA _)) (hHK : vPull hTM g H ≤ vPull hTM g K) :
    H ≤ K := by
  rw [← map_vPull hTM hH]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hyK : ((y : ↥M) : G) ∈ vPull hTM g K := hHK (Subgroup.mem_subgroupOf.mp hy)
  obtain ⟨z, hz, hzy⟩ := hyK
  have : z = y := Subtype.ext hzy
  rw [← this]
  exact hz

theorem vPull_commutator {g : (puAmalgam hTM).Universal}
    {H K : Subgroup (puAmalgam hTM).Universal} (hH : H ≤ stab (puAmalgam hTM) (g • baseA _))
    (hK : K ≤ stab (puAmalgam hTM) (g • baseA _)) :
    vPull hTM g ⁅H, K⁆ = ⁅vPull hTM g H, vPull hTM g K⁆ := by
  conv_lhs => rw [← map_vPull hTM hH, ← map_vPull hTM hK, ← Subgroup.map_commutator,
    ← commutator_subgroupOf (vPull_le hTM g H) (vPull_le hTM g K)]
  exact vPull_map hTM (commutator_le_of_le (vPull_le hTM g H) (vPull_le hTM g K))

end Emb

section Structure

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} (h : PUHyp M T L)
include h

theorem ltil_perfect {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    ⁅Ltil h.le L δ, Ltil h.le L δ⁆ = Ltil h.le L δ := by
  rw [Ltil, ← puTrans_commutator h.L_le h.L_le h.le_normalizer h.le_normalizer hδ, h.perfect]

noncomputable abbrev pCoreLtil (δ : Vtx (puAmalgam h.le)) : Subgroup (puAmalgam h.le).Universal :=
  puTrans h.le (pCoreL L) δ

theorem pCoreL_normal : ((pCoreL L).subgroupOf M).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer ((pCoreL_le L).trans h.L_le)).2
    (le_normalizer_pCoreL h.le_normalizer)

theorem pCoreLtil_le_qv {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) :
    pCoreLtil h δ ≤ Qv _ δ := by
  rw [h.qv_eq hδ]
  exact puTrans_mono h.le (map_pCore_le_pCoreOf h.L_le h.le_normalizer) δ

theorem commutator_ltil_le_or {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    {K : Subgroup (puAmalgam h.le).Universal} (hKL : K ≤ Ltil h.le L δ)
    (hLK : Ltil h.le L δ ≤ Subgroup.normalizer (K : Set (puAmalgam h.le).Universal)) :
    ⁅K, Ltil h.le L δ⁆ ≤ pCoreLtil h δ ∨ Ltil h.le L δ ≤ K := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  have hLs := ltil_le_stab h (g • baseA _)
  have hKs := hKL.trans hLs
  have hvL : vPull h.le g (Ltil h.le L (g • baseA _)) = L :=
    vPull_puTrans h.le h.L_le (S4A.L_normal h)
  have hvO : vPull h.le g (pCoreLtil h (g • baseA _)) = pCoreL L :=
    vPull_puTrans h.le ((pCoreL_le L).trans h.L_le) (pCoreL_normal h)
  have hK' : vPull h.le g K ≤ L := (vPull_mono h.le g hKL).trans hvL.le
  have hLK' : L ≤ Subgroup.normalizer (vPull h.le g K : Set G) := by
    have key : ⁅vPull h.le g K, vPull h.le g (Ltil h.le L (g • baseA _))⁆ ≤ vPull h.le g K := by
      rw [← vPull_commutator h.le hKs hLs]
      exact vPull_mono h.le g (Subgroup.le_normalizer_iff_commutator_le_left.mp hLK)
    rw [hvL] at key
    exact Subgroup.le_normalizer_iff_commutator_le_left.mpr key
  by_cases hne : L ≤ vPull h.le g K ⊔ pCoreL L
  · right
    refine le_of_vPull_le h.le hLs ?_
    rw [hvL]
    exact le_of_le_sup_pCoreL h.perfect hK' hLK' hne
  · left
    have := commutator_le_pCoreL_of_quasisimple h.quasisimple hK' hLK' hne
    refine le_of_vPull_le h.le (commutator_le_of_le hKs hLs) ?_
    rw [vPull_commutator h.le hKs hLs, hvL, hvO]
    exact this

theorem stab_eq_ltil_sup_qv_adj (hfull : IsSL3Full M T L) {δ β : Vtx (puAmalgam h.le)}
    (hδ : IsMVtx _ δ) (hδβ : (puAmalgam h.le).treeGraph.Adj δ β) :
    stab _ δ = Ltil h.le L δ ⊔ Qv _ β := by
  apply le_antisymm
  · rw [stab_eq_ltil_sup_qv h hfull hδ]
    exact sup_le_sup_left (qv_le_qv _ h.hyp20 hδ hδβ) _
  · exact sup_le (ltil_le_stab h δ) (qv_le_stab_of_adj _ hδβ.symm)

theorem le_qv_of_commutator_le (hfull : IsSL3Full M T L) {δ β : Vtx (puAmalgam h.le)}
    (hδ : IsMVtx _ δ) (hδβ : (puAmalgam h.le).treeGraph.Adj δ β)
    {R : Subgroup (puAmalgam h.le).Universal} (hR : R ≤ Qv _ β)
    (hRL : ⁅R, Ltil h.le L δ⁆ ≤ Qv _ δ) : R ≤ Qv _ δ := by
  have hQδβ : Qv (puAmalgam h.le) δ ≤ Qv _ β := qv_le_qv _ h.hyp20 hδ hδβ
  have hβs : Qv (puAmalgam h.le) β ≤ stab _ δ := qv_le_stab_of_adj _ hδβ.symm
  have hQn : stab (puAmalgam h.le) δ ≤ Subgroup.normalizer (Qv _ δ : Set _) :=
    stab_le_normalizer_qv _ δ
  set W := conjCl (Qv (puAmalgam h.le) β) R ⊔ Qv _ δ with hW
  have hCl : conjCl (Qv (puAmalgam h.le) β) R ≤ Qv _ β := conjCl_le_of_le hR
  have hTW : Qv (puAmalgam h.le) β ≤ Subgroup.normalizer (W : Set _) :=
    (le_inf (le_normalizer_conjCl _ _) (hβs.trans hQn)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup _ _)
  have hLW : Ltil h.le L δ ≤ Subgroup.normalizer (W : Set _) := by
    rw [Subgroup.le_normalizer_iff_commutator_le_left]
    refine S4A.commutator_sup_le_of ?_ ?_ (le_sup_left.trans Subgroup.le_normalizer)
      (le_sup_right.trans Subgroup.le_normalizer)
    · exact (commutator_conjCl_le (hβs.trans hQn)
        (hβs.trans (stab_le_normalizer_ltil h δ)) ((hR.trans hβs).trans hQn) hRL).trans
          le_sup_right
    · exact (Subgroup.le_normalizer_iff_commutator_le_left.mp
        ((ltil_le_stab h δ).trans hQn)).trans le_sup_right
  have hsW : stab _ δ ≤ Subgroup.normalizer (W : Set _) := by
    rw [stab_eq_ltil_sup_qv_adj h hfull hδ hδβ]
    exact sup_le hLW hTW
  exact (le_conjCl _ _).trans (le_sup_left.trans
    (le_qv_of_normalizer _ h.hyp20 hδ hδβ (sup_le hCl hQδβ) hsW))

theorem finite_stab {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ) : Finite ↥(stab _ δ) := by
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hδ
  rw [stab_eq_map_vEmb h.le g]
  exact Finite.of_equiv _ (Subgroup.equivMapOfInjective _ _ (vEmb_injective h.le g)).toEquiv

theorem qv_eq_of_le {α δ : Vtx (puAmalgam h.le)} (hα : IsMVtx _ α) (hδ : IsMVtx _ δ)
    (hle : Qv _ δ ≤ Qv _ α) : Qv _ δ = Qv _ α := by
  have := finite_stab h hα
  have : Finite ↥(Qv (puAmalgam h.le) α) :=
    Finite.of_injective _ (Subgroup.inclusion_injective (qv_le_stab _ α))
  obtain ⟨g, rfl⟩ := exists_smul_eq_of_isMVtx _ hα hδ
  rw [qv_smul] at hle ⊢
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

theorem le_dloc_of_commutator_le {δ : Vtx (puAmalgam h.le)} (hδ : IsMVtx _ δ)
    {X : Subgroup (puAmalgam h.le).Universal} (hXQ : X ≤ Qv _ δ)
    (hXL : ⁅X, Ltil h.le L δ⁆ ≤ Dloc h.le L δ) : X ≤ Dloc h.le L δ := by
  have hD := h.puTrans_Dq hδ
  rw [Dloc, hD] at hXL ⊢
  refine le_inf hXQ ?_
  have hbot : ∀ H : Subgroup (puAmalgam h.le).Universal,
      H ≤ Subgroup.normalizer ((⊥ : Subgroup (puAmalgam h.le).Universal) : Set _) := fun H =>
    le_top.trans (Subgroup.normalizer_eq_top_iff.mpr inferInstance).ge
  have h1 : ⁅⁅X, Ltil h.le L δ⁆, Ltil h.le L δ⁆ ≤ ⊥ := by
    rw [le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hXL.trans inf_le_right
  have h3 := three_subgroups_le (N := ⊥) (H₁ := Ltil h.le L δ) (H₂ := Ltil h.le L δ) (H₃ := X)
    (hbot _) (hbot _) (hbot _) (by rw [Subgroup.commutator_comm (Ltil h.le L δ) X]; exact h1) h1
  rw [ltil_perfect h hδ, le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at h3
  exact Subgroup.le_centralizer_iff.mp h3

end Structure

end CFSG.Quasithin.MS93.S4A
