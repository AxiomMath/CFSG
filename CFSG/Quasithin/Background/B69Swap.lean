module

public import CFSG.Quasithin.Background.B69Par
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.Adapters.GeneralizedFittingTop

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace B69

variable {Y : Type} [Group Y] [Finite Y] {T M : Subgroup Y}

theorem component_is_factor (h : MinParabolic (⊤ : Subgroup Y) T M) (hJ : kerIn M ⊤ = ⊥)
    {L : Subgroup Y} (hL : CFSG.Open.IsComponentOf L ⊤) :
    IsSimpleGroup ↥L ∧ ¬ IsMulCommutative ↥L ∧ L ≤ twoResidual (⊤ : Subgroup Y) ∧
      twoResidual (⊤ : Subgroup Y) = ⨆ t ∈ T, conjSub t L ∧
      sSupIndep {S : Subgroup Y | ∃ t ∈ T, S = conjSub t L} ∧
      ∀ t ∈ T, ((conjSub t L).subgroupOf (twoResidual (⊤ : Subgroup Y))).Normal := by
  have hLq : CFSG.Open.IsQuasisimple ↥L := hL.2.2
  have hLperf : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hLq.1
  have hLnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hLq
  have hns : ¬ Group.IsSolvable Y := fun hY => by
    have : Group.IsSolvable ↥L := Group.isSolvable_of_isSolvable_injective (f := L.subtype)
      L.subtype_injective
    exact Group.IsPerfect.not_isSolvable ↥L this
  obtain ⟨F, hFs, hFn, hFK, hgen, hind, hnorm⟩ := exists_simple_factor h hJ hns
  set K := twoResidual (⊤ : Subgroup Y) with hKdef
  have hKn : K.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (le_normalizer_twoResidual ⊤))
  have hLK : L ≤ K := perfect_le_twoResidual
  have hsn : ∀ t ∈ T, (conjSub t F).IsSubnormal := fun t ht =>
    Subgroup.IsSubnormal.step _ K (conjSub_le_of_normal hKn hFK t) hKn.isSubnormal (hnorm t ht)
  have hL' : CFSG.GorensteinWalter.IsComponentOf L ⊤ := (CFSG.Adapters.isComponentOf_top_iff L).1 hL
  have hex : ∃ t ∈ T, L ≤ conjSub t F := by
    by_contra hcon
    push Not at hcon
    have hcent : K ≤ Subgroup.centralizer (L : Set Y) := by
      rw [hgen]
      refine iSup₂_le fun t ht => ?_
      have hc : ⁅L, conjSub t F⁆ = ⊥ :=
        (CFSG.GorensteinWalter.component_le_or_commutator_eq_bot hL' (hsn t ht)).resolve_left
          (hcon t ht)
      rw [← Subgroup.commutator_comm] at hc
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc
    refine Group.IsPerfect.not_isMulCommutative ↥L (IsMulCommutative.of_setLike_mul_comm fun a ha b hb => ?_)
    exact ((Subgroup.mem_centralizer_iff.mp (hcent (hLK ha))) b hb).symm
  obtain ⟨t₀, ht₀, hLF⟩ := hex
  have hFt₀s : IsSimpleGroup ↥(conjSub t₀ F) := isSimpleGroup_conjSub hFs t₀
  have hLeq : L = conjSub t₀ F := by
    refine le_antisymm hLF ?_
    have hU : (L.subgroupOf (conjSub t₀ F)).IsSubnormal :=
      ((CFSG.Adapters.isSubnormal_top_iff L).1 hL.2.1).subgroupOf
    rcases hU.eq_bot_or_top_of_isSimpleGroup hFt₀s with hbot | htop
    · exfalso
      have : L = ⊥ := by
        rw [Subgroup.subgroupOf_eq_bot] at hbot
        exact hbot.eq_bot_of_le hLF
      exact (Subgroup.nontrivial_iff_ne_bot L).1 hLnt this
    · intro x hx
      have : (⟨x, hx⟩ : ↥(conjSub t₀ F)) ∈ L.subgroupOf (conjSub t₀ F) := by rw [htop]; trivial
      exact this
  have hset : {S : Subgroup Y | ∃ t ∈ T, S = conjSub t L} =
      {S : Subgroup Y | ∃ t ∈ T, S = conjSub t F} := by
    ext S
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t * t₀, T.mul_mem ht ht₀, by rw [hLeq, conjSub_mul]⟩
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t * t₀⁻¹, T.mul_mem ht (T.inv_mem ht₀), ?_⟩
      rw [hLeq, ← conjSub_mul, mul_assoc, inv_mul_cancel, mul_one]
  have hgenL : K = ⨆ t ∈ T, conjSub t L := by
    apply le_antisymm
    · rw [hgen]
      refine iSup₂_le fun t ht => ?_
      refine le_iSup₂_of_le (t * t₀⁻¹) (T.mul_mem ht (T.inv_mem ht₀)) ?_
      rw [hLeq, ← conjSub_mul, mul_assoc, inv_mul_cancel, mul_one]
    · exact iSup₂_le fun t ht => conjSub_le_of_normal hKn hLK t
  have hsimple : IsSimpleGroup ↥L := by
    rw [hLeq]
    exact hFt₀s
  have hnc : ¬ IsMulCommutative ↥L := by
    intro hc
    apply hFn
    rw [hLeq] at hc
    have := isMulCommutative_conjSub hc t₀⁻¹
    rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this
  have hindL : sSupIndep {S : Subgroup Y | ∃ t ∈ T, S = conjSub t L} := by
    rw [hset]
    exact hind
  have hnormL : ∀ t ∈ T, ((conjSub t L).subgroupOf K).Normal := by
    intro t ht
    have := hnorm (t * t₀) (T.mul_mem ht ht₀)
    rw [hLeq, ← conjSub_mul]
    exact this
  exact ⟨hsimple, hnc, hLK, hgenL, hindL, hnormL⟩

@[expose] def SwapGeo (G₀ : Type) [Group G₀] (TP : MulAut G₀ → Prop) : Prop :=
  ∀ (Λ : Type) [Group Λ] [Finite Λ] [IsSimpleGroup Λ] (ι : Λ ≃* G₀) (S₀ : Subgroup Λ),
    IsPGroup 2 S₀ → ¬ 2 ∣ S₀.index → S₀ ≠ ⊥ →
    ∀ Ybar Tbar Mbar : Subgroup (MulAut Λ), (∀ x : Λ, MulAut.conj x ∈ Ybar) → Tbar ≤ Mbar →
      Mbar < Ybar → (∀ V : Subgroup (MulAut Λ), Tbar ≤ V → (∀ x : Λ, MulAut.conj x ∈ V) → Ybar ≤ V) →
      (∀ V : Subgroup (MulAut Λ), Tbar ≤ V → V < Ybar → V ≤ Mbar) →
      (∀ φ ∈ Tbar, S₀.map (φ : Λ →* Λ) = S₀) → ∃ φ ∈ Tbar, ¬ TP (MulAut.congr ι φ)

theorem swapGeo_sl3 {K : Type} [Field K] [Finite K] [CharP K 2] :
    SwapGeo (projectiveSL 3 K) TypePres := by
  intro Λ _ _ _ ι S₀ hS₀p hS₀i hS₀ne Ybar Tbar Mbar hInn hTM hMY hgen hmax hTS
  exact exists_not_typePres ι hS₀p hS₀i hS₀ne hInn hTM hMY hgen hmax hTS

omit [Finite Y] in
theorem innAut_eq_conj (L : Subgroup Y) (x : ↥L) : innAut L x = MulAut.conj x := by
  ext y
  rfl

theorem exists_swap_quot {G₀ : Type} [Group G₀] {TP : MulAut G₀ → Prop} (hgeo : SwapGeo G₀ TP)
    (hev : Even (Nat.card G₀)) (h : MinParabolic (⊤ : Subgroup Y) T M) (hJ : kerIn M ⊤ = ⊥)
    {L : Subgroup Y} (hL : CFSG.Open.IsComponentOf L ⊤) (ι : ↥L ≃* G₀) :
    ∃ t ∈ T, t ∈ Subgroup.normalizer (L : Set Y) ∧ ¬ TP (MulAut.congr ι (indAut L t)) := by
  obtain ⟨hs, hnc, hLK, hgen, hind, hnorm⟩ := component_is_factor h hJ hL
  have hKn : (⊤ : Subgroup Y) ≤ Subgroup.normalizer (twoResidual (⊤ : Subgroup Y) : Set Y) :=
    le_normalizer_twoResidual ⊤
  have hKnormal : (twoResidual (⊤ : Subgroup Y)).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr hKn)
  have hL2 : Even (Nat.card ↥L) := by rwa [Nat.card_congr ι.toEquiv]
  obtain ⟨C, d⟩ := exists_autData h.isSylow.2.1 hKnormal (sup_twoResidual_eq h.isSylow)
    (isSylowTwoOf_inf_normal h.isSylow le_top hKn) hs hnc hL2 hLK hgen hind hnorm
  have hU := (aut_clause h hs hnc hL2 hLK hgen hind hnorm).2
  have hMY : autOn M L < autOn ⊤ L := ((isUniqueMaxOver_iff.1 hU).1).1
  have hS₀p : IsPGroup 2 ((T ⊓ L).subgroupOf L) :=
    (h.isSylow.2.1.to_le (inf_le_left : T ⊓ L ≤ T)).of_equiv
      (Subgroup.subgroupOfEquivOfLe (inf_le_right : T ⊓ L ≤ L)).symm
  have hS₀i : ¬ 2 ∣ ((T ⊓ L).subgroupOf L).index := d.sylow_TL.2.2
  have hS₀ne : (T ⊓ L).subgroupOf L ≠ ⊥ := by
    intro hbot
    apply d.TL_ne_bot
    rw [Subgroup.subgroupOf_eq_bot] at hbot
    exact hbot.eq_bot_of_le inf_le_right
  have hinn : ∀ x : ↥L, MulAut.conj x ∈ autOn ⊤ L := fun x => by
    rw [← innAut_eq_conj, ← indAut_eq_innAut]
    exact indAut_mem_autOn (Subgroup.mem_top _) (Subgroup.le_normalizer x.2)
  have hmem : ∀ t ∈ T, t ∈ Subgroup.normalizer (L : Set Y) →
      ∀ x : ↥L, x ∈ (T ⊓ L).subgroupOf L → indAut L t x ∈ (T ⊓ L).subgroupOf L := by
    intro t ht htN x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨?_, (indAut L t x).2⟩
    rw [coe_indAut_apply htN]
    exact T.mul_mem (T.mul_mem ht hx.1) (T.inv_mem ht)
  have hTS : ∀ φ ∈ autOn T L, ((T ⊓ L).subgroupOf L).map (φ : ↥L →* ↥L) = (T ⊓ L).subgroupOf L := by
    intro φ hφ
    obtain ⟨t, ht, htN, rfl⟩ := mem_autOn_iff_indAut.mp hφ
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hmem t ht htN x hx
    · intro hy
      refine ⟨indAut L t⁻¹ y, hmem t⁻¹ (T.inv_mem ht) (inv_mem htN) y hy, ?_⟩
      rw [indAut_inv htN]
      exact (indAut L t).apply_symm_apply y
  obtain ⟨φ, hφ, hnot⟩ := hgeo ↥L ι _ hS₀p hS₀i hS₀ne (autOn ⊤ L) (autOn T L) (autOn M L) hinn
    (autOn_le_autOn_of_le h.le) hMY
    (fun V hTV hLV => d.autOn_top_le hTV (fun x => by rw [innAut_eq_conj]; exact hLV x))
    (fun V hTV hVA => d.le_autOn_M h hTV hVA) hTS
  obtain ⟨t, ht, htN, rfl⟩ := mem_autOn_iff_indAut.mp hφ
  exact ⟨t, ht, htN, hnot⟩

end B69

end CFSG.Quasithin
