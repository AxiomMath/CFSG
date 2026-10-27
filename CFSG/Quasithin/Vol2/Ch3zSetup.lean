module

public import CFSG.Quasithin.Vol2.Ch3yB69
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Ch3z

variable {G : Type} [Group G]

@[expose] def chiefMod (L N : Subgroup G) : Subgroup (SecQuot (Subgroup.normalizer (L : Set G)) L) :=
  secImg (Subgroup.normalizer (L : Set G)) L N

@[expose] noncomputable def chiefAut (H L N : Subgroup G) : Subgroup (MulAut ↥(chiefMod L N)) :=
  autOn (secImg (Subgroup.normalizer (L : Set G)) L H) (chiefMod L N)

section Hom

variable {H L N : Subgroup G}

@[expose] noncomputable def chiefPsi (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) : ↥H →* MulAut ↥(chiefMod L N) :=
  (conjAct (chiefMod L N)).comp
    (((secMk (Subgroup.normalizer (L : Set G)) L).comp (Subgroup.inclusion hHL)).codRestrict _
      fun g => secMk_mem_normalizer_secImg (hHN g.2))

theorem chiefPsi_mem (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (g : ↥H) : chiefPsi hHL hHN g ∈ chiefAut H L N := by
  refine Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
  exact secMk_mem_secImg (A := Subgroup.normalizer (L : Set G)) (B := L) (X := H)
    (x := Subgroup.inclusion hHL g) g.2

@[expose] noncomputable def chiefHom (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) : ↥H →* ↥(chiefAut H L N) :=
  (chiefPsi hHL hHN).codRestrict _ (chiefPsi_mem hHL hHN)

theorem chiefHom_surjective (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) : Function.Surjective (chiefHom hHL hHN) := by
  rintro ⟨x, hx⟩
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨a, haG, hay⟩ := mem_secImg.mp (Subgroup.mem_subgroupOf.mp hy)
  refine ⟨⟨a, haG⟩, Subtype.ext ?_⟩
  show conjAct (chiefMod L N) _ = conjAct (chiefMod L N) y
  congr 1
  exact Subtype.ext hay

theorem chiefHom_eq_one_iff (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (g : ↥H) : chiefHom hHL hHN g = 1 ↔ (g : G) ∈ centralizerMod L H N := by
  constructor
  · intro hg
    have hψ1 : chiefPsi hHL hHN g = 1 := congrArg Subtype.val hg
    have hcent := A4.conjAct_eq_one_iff.mp hψ1
    refine ⟨g.2, hHL g.2, fun n hn => ?_⟩
    have hnE : secMk (Subgroup.normalizer (L : Set G)) L ⟨n, hNL hn⟩ ∈ chiefMod L N :=
      secMk_mem_secImg (A := Subgroup.normalizer (L : Set G)) (B := L) (X := N)
        (x := ⟨n, hNL hn⟩) hn
    have hcomm := Subgroup.mem_centralizer_iff.mp hcent _ hnE
    exact commutator_mem_of_secMk_commute (A := Subgroup.normalizer (L : Set G)) (B := L)
      (x := ⟨(g : G), hHL g.2⟩) (y := ⟨n, hNL hn⟩) hcomm.symm
  · intro hg
    refine Subtype.ext (A4.conjAct_eq_one_iff.mpr ?_)
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    obtain ⟨n, hn, rfl⟩ := mem_secImg.mp hy
    exact (secMk_comm_of_commutator_mem (A := Subgroup.normalizer (L : Set G)) (K := L)
      (x := ⟨(g : G), hHL g.2⟩) (y := ⟨n, hNL (hn)⟩) (hg.2.2 n hn)).symm

end Hom

section Iota

variable {H U L N : Subgroup G}

@[expose] noncomputable def chiefIota (hNL : N ≤ Subgroup.normalizer (L : Set G)) :
    ↥N →* ↥(chiefMod L N) :=
  ((secMk (Subgroup.normalizer (L : Set G)) L).comp (Subgroup.inclusion hNL)).codRestrict _
    fun x => secMk_mem_secImg (A := Subgroup.normalizer (L : Set G)) (B := L) (X := N)
      (x := Subgroup.inclusion hNL x) x.2

theorem chiefIota_coe (hNL : N ≤ Subgroup.normalizer (L : Set G)) (x : ↥N) :
    ((chiefIota hNL x : ↥(chiefMod L N)) : SecQuot (Subgroup.normalizer (L : Set G)) L) =
      secMk (Subgroup.normalizer (L : Set G)) L (Subgroup.inclusion hNL x) := rfl

theorem chiefIota_surjective (hNL : N ≤ Subgroup.normalizer (L : Set G)) :
    Function.Surjective (chiefIota hNL) := by
  rintro ⟨y, hy⟩
  obtain ⟨a, haN, rfl⟩ := mem_secImg.mp hy
  exact ⟨⟨a, haN⟩, Subtype.ext rfl⟩

theorem chiefIota_eq_one_iff (hNL : N ≤ Subgroup.normalizer (L : Set G)) (x : ↥N) :
    chiefIota hNL x = 1 ↔ (x : G) ∈ L := by
  constructor
  · intro h
    have h1 := congrArg Subtype.val h
    rw [chiefIota_coe, OneMemClass.coe_one] at h1
    exact (secMk_eq_one_iff (A := Subgroup.normalizer (L : Set G)) (B := L)).mp h1
  · intro h
    apply Subtype.ext
    rw [chiefIota_coe, OneMemClass.coe_one]
    exact (secMk_eq_one_iff (A := Subgroup.normalizer (L : Set G)) (B := L)).mpr h

theorem chiefPsi_iota (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (g : ↥H) (n : ↥N) (hgn : (g : G) * (n : G) * (g : G)⁻¹ ∈ N) :
    chiefPsi hHL hHN g (chiefIota hNL n) = chiefIota hNL ⟨(g : G) * n * (g : G)⁻¹, hgn⟩ := by
  apply Subtype.ext
  show ((conjAct (chiefMod L N) _ (chiefIota hNL n) : ↥(chiefMod L N)) :
    SecQuot (Subgroup.normalizer (L : Set G)) L) = _
  rw [conjAct_apply_coe', chiefIota_coe, chiefIota_coe]
  have e : (Subgroup.inclusion hNL ⟨(g : G) * n * (g : G)⁻¹, hgn⟩ : Subgroup.normalizer (L : Set G)) =
      Subgroup.inclusion hHL g * Subgroup.inclusion hNL n * (Subgroup.inclusion hHL g)⁻¹ :=
    Subtype.ext rfl
  rw [e, map_mul, map_mul, map_inv]
  rfl

end Iota


section MinPar

variable {Γ : Type*} [Group Γ]

theorem minParabolic_map_subtype {X : Subgroup Γ} {S M' : Subgroup ↥X}
    (h : MinParabolic (⊤ : Subgroup ↥X) S M') :
    MinParabolic X (S.map X.subtype) (M'.map X.subtype) := by
  have hmem : ∀ (K : Subgroup ↥X) (z : ↥X), (z : Γ) ∈ K.map X.subtype ↔ z ∈ K := fun K z =>
    Subgroup.mem_map_iff_mem X.subtype_injective
  refine ⟨⟨Subgroup.map_subtype_le S, h.isSylow.2.1.map _, ?_⟩, ?_, ?_⟩
  · rw [map_subtype_subgroupOf' S]
    have h2 := h.isSylow.2.2
    change ¬ 2 ∣ S.relIndex ⊤ at h2
    rwa [Subgroup.relIndex_top_right] at h2
  · intro hX
    apply h.not_normal
    intro x _
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h1 := Subgroup.mem_normalizer_iff.mp (hX x.2) (y : Γ)
    have e : ((x : Γ) * (y : Γ) * (x : Γ)⁻¹) = ((x * y * x⁻¹ : ↥X) : Γ) := by simp
    rw [e, hmem, hmem] at h1
    exact h1
  · rw [isUniqueMaxOver_iff]
    refine ⟨B6.isMaxSubgroupIn_map_subtype h.maximal, Subgroup.map_mono h.le, fun N hN hSN => ?_⟩
    have hNX : N ≤ X := hN.1.le
    have hmax := B6.isMaxSubgroupIn_top_subgroupOf hN
    have hSle : S ≤ N.subgroupOf X := by
      intro s hs
      exact hSN ⟨s, hs, rfl⟩
    have := h.eq_of_maximal hmax hSle
    rw [← this, Subgroup.map_subgroupOf_eq_of_le hNX]

end MinPar

section Irr

variable {H U L N : Subgroup G}

@[expose] noncomputable def chiefPre (hNL : N ≤ Subgroup.normalizer (L : Set G)) (W : Subgroup ↥(chiefMod L N)) :
    Subgroup G :=
  (W.comap (chiefIota hNL)).map N.subtype

theorem mem_chiefPre (hNL : N ≤ Subgroup.normalizer (L : Set G)) (W : Subgroup ↥(chiefMod L N))
    {x : G} : x ∈ chiefPre hNL W ↔ ∃ hx : x ∈ N, chiefIota hNL ⟨x, hx⟩ ∈ W := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.2, hn⟩
  · rintro ⟨hx, hW⟩
    exact ⟨⟨x, hx⟩, hW, rfl⟩

theorem chiefPre_le (hNL : N ≤ Subgroup.normalizer (L : Set G)) (W : Subgroup ↥(chiefMod L N)) :
    chiefPre hNL W ≤ N := fun _ hx => ((mem_chiefPre hNL W).1 hx).1

theorem le_chiefPre (hNL : N ≤ Subgroup.normalizer (L : Set G)) (hLN : L ≤ N)
    (W : Subgroup ↥(chiefMod L N)) : L ≤ chiefPre hNL W := by
  intro l hl
  refine (mem_chiefPre hNL W).2 ⟨hLN hl, ?_⟩
  rw [(chiefIota_eq_one_iff hNL ⟨l, hLN hl⟩).2 hl]
  exact W.one_mem

theorem eq_bot_of_chiefPre_eq (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (W : Subgroup ↥(chiefMod L N)) (h : chiefPre hNL W = L) : W = ⊥ := by
  rw [eq_bot_iff]
  intro w hw
  obtain ⟨n, rfl⟩ := chiefIota_surjective hNL w
  have : (n : G) ∈ chiefPre hNL W := (mem_chiefPre hNL W).2 ⟨n.2, hw⟩
  rw [h] at this
  rw [Subgroup.mem_bot]
  exact (chiefIota_eq_one_iff hNL n).2 this

theorem eq_top_of_chiefPre_eq (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (W : Subgroup ↥(chiefMod L N)) (h : chiefPre hNL W = N) : W = ⊤ := by
  rw [eq_top_iff]
  intro w _
  obtain ⟨n, rfl⟩ := chiefIota_surjective hNL w
  have : (n : G) ∈ chiefPre hNL W := by rw [h]; exact n.2
  exact ((mem_chiefPre hNL W).1 this).2

theorem isNormalIn_chiefPre (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (hNL : N ≤ Subgroup.normalizer (L : Set G))
    (hNU : N ≤ U) (W : Subgroup ↥(chiefMod L N))
    (hW : ∀ x ∈ chiefAut H L N, ∀ w ∈ W, x w ∈ W) : IsNormalIn H U (chiefPre hNL W) := by
  refine ⟨(chiefPre_le hNL W).trans hNU, fun g hg x hx => ?_⟩
  obtain ⟨hxN, hxW⟩ := (mem_chiefPre hNL W).1 hx
  have hgx : g * x * g⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hHN hg) x).mp hxN
  refine (mem_chiefPre hNL W).2 ⟨hgx, ?_⟩
  have := chiefPsi_iota hHL hHN hNL ⟨g, hg⟩ ⟨x, hxN⟩ hgx
  rw [← this]
  exact hW _ (chiefPsi_mem hHL hHN ⟨g, hg⟩) _ hxW

theorem chiefMod_irr (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    (W : Subgroup ↥(chiefMod L N)) (hW : ∀ x ∈ chiefAut H L N, ∀ w ∈ W, x w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  have hHL : H ≤ Subgroup.normalizer (L : Set G) := D14.le_normalizer_of_isNormalIn hstep.2.1
  have hHN : H ≤ Subgroup.normalizer (N : Set G) := D14.le_normalizer_of_isNormalIn hstep.1
  have hNL : N ≤ Subgroup.normalizer (L : Set G) := (hstep.1.1.trans hUH).trans hHL
  have hnorm := isNormalIn_chiefPre hHL hHN hNL hstep.1.1 W hW
  rcases hstep.2.2.2 _ hnorm (le_chiefPre hNL hstep.2.2.1.le W) (chiefPre_le hNL W) with h | h
  · exact Or.inl (eq_bot_of_chiefPre_eq hNL W h)
  · exact Or.inr (eq_top_of_chiefPre_eq hNL W h)

theorem chiefAut_pCoreOf_eq_bot [Finite G] (hstep : IsChiefStep H U L N) (hUH : U ≤ H)
    (hE : IsElemAbelian 2 (chiefMod L N)) : pCoreOf 2 (chiefAut H L N) = ⊥ :=
  D15Proof.normal_two_eq_bot hUH hstep hE _ (pCoreOf_le 2 _) (normal_pCoreOf_subgroupOf _)
    (pCoreOf_isPGroup 2 _)

end Irr

section Parabolic

variable [Finite G] {H T M₂ U L N : Subgroup G}

@[expose] noncomputable def chiefImg (hHL : H ≤ Subgroup.normalizer (L : Set G))
    (hHN : H ≤ Subgroup.normalizer (N : Set G)) (K : Subgroup G) :
    Subgroup (MulAut ↥(chiefMod L N)) :=
  (K.subgroupOf H).map (chiefPsi hHL hHN)

theorem ker_chiefHom_le (hmp : MinParabolic H T M₂) (hUT : U ≤ T) (hstep : IsChiefStep H U L N)
    (hnc : ¬ IsCentralStep H L N) :
    (chiefHom (D14.le_normalizer_of_isNormalIn hstep.2.1)
      (D14.le_normalizer_of_isNormalIn hstep.1)).ker ≤ M₂.subgroupOf H := by
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  have hgC := (chiefHom_eq_one_iff (D14.le_normalizer_of_isNormalIn hstep.2.1)
    (D14.le_normalizer_of_isNormalIn hstep.1)
    ((hstep.1.1.trans (hUT.trans hmp.isSylow.1)).trans
      (D14.le_normalizer_of_isNormalIn hstep.2.1)) g).1 hg
  have hk := centralizerMod_le_kerIn hmp hUT hstep hnc hgC
  exact Subgroup.mem_subgroupOf.mpr (by simpa using hk 1 H.one_mem)

theorem chiefAut_minParabolic_top (hmp : MinParabolic H T M₂) (hUT : U ≤ T)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N) :
    MinParabolic (⊤ : Subgroup ↥(chiefAut H L N))
      ((T.subgroupOf H).map (chiefHom (D14.le_normalizer_of_isNormalIn hstep.2.1)
        (D14.le_normalizer_of_isNormalIn hstep.1)))
      ((M₂.subgroupOf H).map (chiefHom (D14.le_normalizer_of_isNormalIn hstep.2.1)
        (D14.le_normalizer_of_isNormalIn hstep.1))) :=
  MinParabolic.map_of_surjective hmp.subgroupOf
    (chiefHom_surjective _ _) (ker_chiefHom_le hmp hUT hstep hnc)

theorem chiefAut_minParabolic (hmp : MinParabolic H T M₂) (hUT : U ≤ T)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N) :
    MinParabolic (chiefAut H L N)
      (chiefImg (D14.le_normalizer_of_isNormalIn hstep.2.1)
        (D14.le_normalizer_of_isNormalIn hstep.1) T)
      (chiefImg (D14.le_normalizer_of_isNormalIn hstep.2.1)
        (D14.le_normalizer_of_isNormalIn hstep.1) M₂) := by
  have h := minParabolic_map_subtype (chiefAut_minParabolic_top hmp hUT hstep hnc)
  have e : (chiefAut H L N).subtype.comp (chiefHom (D14.le_normalizer_of_isNormalIn hstep.2.1)
      (D14.le_normalizer_of_isNormalIn hstep.1)) =
      chiefPsi (D14.le_normalizer_of_isNormalIn hstep.2.1)
        (D14.le_normalizer_of_isNormalIn hstep.1) := MonoidHom.ext fun _ => rfl
  simpa only [chiefImg, Subgroup.map_map, e] using h

theorem chiefAut_sqtk (hsq : IsSQTKSub H) (hstep : IsChiefStep H U L N) :
    ∃ (H₀ : Type) (_ : Group H₀) (_ : Finite H₀), CFSG.Open.SQTKTauCeti.StronglyQuasithin H₀ ∧
      CFSG.SectionRank.IsKGroupCat H₀ ∧ ∃ f : H₀ →* ↥(chiefAut H L N), Function.Surjective f :=
  ⟨↥H, inferInstance, inferInstance, hsq.2, hsq.1,
    chiefHom (D14.le_normalizer_of_isNormalIn hstep.2.1) (D14.le_normalizer_of_isNormalIn hstep.1),
    chiefHom_surjective _ _⟩

theorem ffModule_chiefAut (hUH : U ≤ H) (hstep : IsChiefStep H U L N)
    (hE : IsElemAbelian 2 (chiefMod L N)) {A : Subgroup G} (hAH : A ≤ H)
    (hAel : IsElemAbelian 2 A) (hnt : ¬ ∀ b ∈ A, ∀ e ∈ N, b * e * b⁻¹ * e⁻¹ ∈ L)
    (hle : (centralizerMod L N A).relIndex N ≤ (centralizerMod L A N).relIndex A) :
    @IsFFModule ↥(chiefMod L N) (commGroupOfElemAbelian hE) (chiefAut H L N) :=
  isFFModule_autOn_secImg hE ((hstep.1.1.trans hUH).trans (D14.le_normalizer_of_isNormalIn hstep.2.1))
    (D14.le_normalizer_of_isNormalIn hstep.2.1) (D14.le_normalizer_of_isNormalIn hstep.1) hAH hAel
    hnt hle

end Parabolic

end Ch3z

end CFSG.Quasithin
