module

public import CFSG.Quasithin.MS93.S38Base
public import CFSG.Quasithin.MS93.S38Crit

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

section Internal

@[expose] def IsXOff (M T F : Subgroup G) : Prop :=
  F ≤ T ∧ IsElemAbelian 2 F ∧ ¬ F ≤ pCoreOf 2 M ∧
    (Subgroup.centralizer (F : Set G)).relIndex (Xq M) ≤ (pCoreOf 2 M).relIndex F

structure XOffData (M T : Subgroup G) : Prop where
  uniq : ∀ F₁ F₂ : Subgroup G, IsXOff M T F₁ → IsXOff M T F₂ →
    F₁ ⊔ pCoreOf 2 M = F₂ ⊔ pCoreOf 2 M
  eq : ∀ F : Subgroup G, IsXOff M T F →
    (Subgroup.centralizer (F : Set G)).relIndex (Xq M) = (pCoreOf 2 M).relIndex F
  zc : ∀ F : Subgroup G, IsXOff M T F → ∃ Z : Subgroup G, Z ≤ Xq M ∧
    ¬ Z ≤ Subgroup.centralizer (F : Set G) ∧
    ∀ Y : Subgroup G, Y ≤ T → Y ≤ Subgroup.centralizer (F : Set G) →
      ⁅Y, Z⁆ ≤ ⁅Xq M, F⁆ ⊔ ⁅Y, Xq M ⊓ Subgroup.centralizer (F : Set G)⁆

theorem XOffData.of_cent (h : PUHyp M T L) (hcent : T ⊓ Subgroup.centralizer (Z0q M T : Set G) =
      pCoreOf 2 M)
    (huniq : ∀ F₁ F₂ : Subgroup G, IsXOff M T F₁ → IsXOff M T F₂ →
      F₁ ⊔ pCoreOf 2 M = F₂ ⊔ pCoreOf 2 M)
    (heq : ∀ F : Subgroup G, IsXOff M T F →
      (Subgroup.centralizer (F : Set G)).relIndex (Xq M) = (pCoreOf 2 M).relIndex F)
    (hC : ∀ F : Subgroup G, IsXOff M T F → ∀ y ∈ T, y ∈ Subgroup.centralizer (F : Set G) →
      y ∈ F ⊔ pCoreOf 2 M) : XOffData M T := by
  refine ⟨huniq, heq, fun F hF => ⟨Xq M, le_rfl, fun hle => hF.2.2.1 ?_, fun Y hYT hYF => ?_⟩⟩
  · rw [← hcent]
    refine le_inf hF.1 ?_
    rw [← Subgroup.le_centralizer_iff] at hle
    exact hle.trans (Subgroup.centralizer_le h.Z0q_le_Xq)
  · have hFn : F ≤ Subgroup.normalizer (Xq M : Set G) :=
      hF.1.trans (h.le.trans (le_normalizer_Xq M))
    have hQ : pCoreOf 2 M ≤ Subgroup.centralizer (Xq M : Set G) := by
      rw [← Subgroup.le_centralizer_iff]
      exact (PU.omegaOneCenterOf_le_centerOf _).trans inf_le_right
    have hY : Y ≤ F ⊔ pCoreOf 2 M := fun y hy => hC F hF y (hYT hy) (hYF hy)
    refine le_sup_of_le_left ?_
    rw [Subgroup.commutator_comm, ← commutator_sup_eq_of_le_centralizer hFn hQ]
    exact Subgroup.commutator_mono le_rfl hY

theorem PUHyp.mem_pCoreOf_of_comm_Uq_two (h : PUHyp M T L) {t : G} (htM : t ∈ M)
    (ht2 : ∃ e : ℕ, t ^ 2 ^ e = 1)
    (htU : ∀ u ∈ Uq M T L, ⁅u, t⁆ ∈ Subgroup.centralizer (L : Set G)) : t ∈ pCoreOf 2 M := by
  set CL := Subgroup.centralizer (L : Set G)
  have hCn : M ≤ Subgroup.normalizer (CL : Set G) := le_normalizer_centralizer h.le_normalizer
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  let D : Subgroup G :=
    { carrier := {m | m ∈ M ∧ ∀ u ∈ Uq M T L, ⁅u, m⁆ ∈ CL}
      one_mem' := ⟨M.one_mem, fun u _ => by simp [CL.one_mem]⟩
      mul_mem' := by
        rintro m n ⟨hm, hm'⟩ ⟨hn, hn'⟩
        refine ⟨M.mul_mem hm hn, fun u hu => ?_⟩
        have e : ⁅u, m * n⁆ = ⁅u, m⁆ * (m * ⁅u, n⁆ * m⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact CL.mul_mem (hm' u hu) ((Subgroup.mem_normalizer_iff.mp (hCn hm) _).mp (hn' u hu))
      inv_mem' := by
        rintro m ⟨hm, hm'⟩
        refine ⟨M.inv_mem hm, fun u hu => ?_⟩
        have e : ⁅u, m⁻¹⁆ = m⁻¹ * ⁅u, m⁆⁻¹ * m⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hCn (M.inv_mem hm)) _).mp
          (CL.inv_mem (hm' u hu)) }
  have hDn : M ≤ Subgroup.normalizer (D : Set G) := by
    have key : ∀ g ∈ M, ∀ m ∈ D, g * m * g⁻¹ ∈ D := by
      rintro g hg m ⟨hm, hm'⟩
      refine ⟨M.mul_mem (M.mul_mem hg hm) (M.inv_mem hg), fun u hu => ?_⟩
      have hu' : g⁻¹ * u * g⁻¹⁻¹ ∈ Uq M T L :=
        (Subgroup.mem_normalizer_iff.mp (hUn (M.inv_mem hg)) u).mp hu
      have e : ⁅u, g * m * g⁻¹⁆ = g * ⁅g⁻¹ * u * g⁻¹⁻¹, m⁆ * g⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp (hCn hg) _).mp (hm' _ hu')
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro m
    refine ⟨key g hg m, fun hm => ?_⟩
    have := key g⁻¹ (M.inv_mem hg) _ hm
    simpa [mul_assoc] using this
  have hLD : ¬ L ≤ D := by
    intro hL
    have hc : ⁅Uq M T L, L⁆ ≤ CL := by
      rw [Subgroup.commutator_le]
      intro u hu l hl
      exact (hL hl).2 u hu
    rw [h.Uq_comm] at hc
    apply h.Uq_ne_bot
    rw [← h.Uq_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hc
  have htD : t ∈ D := ⟨htM, htU⟩
  refine h.mem_pCoreOf_of_rel hDn hLD htM ht2 fun l hl => ?_
  have h1 : l * t⁻¹ * l⁻¹ ∈ D :=
    (Subgroup.mem_normalizer_iff.mp (hDn (h.L_le hl)) _).mp (D.inv_mem htD)
  have e : ⁅t, l⁆ = t * (l * t⁻¹ * l⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact D.mul_mem htD h1

theorem PUHyp.mem_pCoreOf_of_comm_Uq (h : PUHyp M T L) {t : G} (htT : t ∈ T)
    (htU : ∀ u ∈ Uq M T L, ⁅u, t⁆ ∈ Subgroup.centralizer (L : Set G)) : t ∈ pCoreOf 2 M := by
  obtain ⟨e, he⟩ := h.isPGroup ⟨t, htT⟩
  exact h.mem_pCoreOf_of_comm_Uq_two (h.le htT) ⟨e, by simpa using congrArg Subtype.val he⟩ htU

end Internal

section Dictionary

variable (hTM : T ≤ M)

omit [Finite G] in
theorem exists_imM_eq_of_le {F' : Subgroup (puAmalgam hTM).Universal}
    (hF : F' ≤ imM hTM T) : ∃ F : Subgroup G, F ≤ T ∧ imM hTM F = F' := by
  set f := (puAmalgam hTM).ofA
  set F : Subgroup G := (F'.comap f).map M.subtype with hFdef
  have hFM : F ≤ M := Subgroup.map_subtype_le _
  have hrange : F' ≤ f.range := hF.trans (Subgroup.map_le_range _ _)
  have himF : imM hTM F = F' := by
    rw [hFdef, imM_map_subtype, Subgroup.map_comap_eq, inf_eq_right.2 hrange]
  exact ⟨F, (imM_le_imM_iff hTM hFM).mp (himF ▸ hF), himF⟩

omit [Finite G] in
theorem imM_sup {K K' : Subgroup G} (hK : K ≤ M) (hK' : K' ≤ M) :
    imM hTM (K ⊔ K') = imM hTM K ⊔ imM hTM K' := by
  show ((K ⊔ K').subgroupOf M).map _ = (K.subgroupOf M).map _ ⊔ (K'.subgroupOf M).map _
  rw [Subgroup.subgroupOf_sup hK hK', Subgroup.map_sup]

omit [Finite G] in
theorem isElemAbelian_imM_iff {K : Subgroup G} (hK : K ≤ M) :
    IsElemAbelian 2 (imM hTM K) ↔ IsElemAbelian 2 K := by
  set f := (puAmalgam hTM).ofA
  have hmem : ∀ x (hx : x ∈ K), f ⟨x, hK hx⟩ ∈ imM hTM K := fun x hx =>
    ⟨⟨x, hK hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  constructor
  · intro hE
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · have hc := congrArg Subtype.val (hE.1.1.1 ⟨_, hmem x x.2⟩ ⟨_, hmem y y.2⟩)
      simp only [Subgroup.coe_mul] at hc
      rw [← map_mul, ← map_mul] at hc
      have := (puAmalgam hTM).ofA_injective hc
      exact congrArg (Subtype.val : ↥M → G) this
    · have h1 : f (⟨x, hK hx⟩ ^ 2) = 1 := by rw [map_pow]; exact hE.2 _ (hmem x hx)
      have h2 : (⟨x, hK hx⟩ : ↥M) ^ 2 = 1 :=
        (puAmalgam hTM).ofA_injective (h1.trans (map_one f).symm)
      exact congrArg (Subtype.val : ↥M → G) h2
  · intro hE
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha, hax⟩ := x.2
      obtain ⟨b, hb, hby⟩ := y.2
      have hc := congrArg Subtype.val
        (hE.1.1.1 ⟨a, Subgroup.mem_subgroupOf.mp ha⟩ ⟨b, Subgroup.mem_subgroupOf.mp hb⟩)
      simp only [Subgroup.coe_mul] at hc
      have hab : a * b = b * a := Subtype.ext hc
      simp only [Subgroup.coe_mul, ← hax, ← hby, ← map_mul, hab]
    · obtain ⟨a, ha, rfl⟩ := hx
      rw [← map_pow]
      have : a ^ 2 = 1 := Subtype.ext (by
        simpa using hE.2 (a : G) (Subgroup.mem_subgroupOf.mp ha))
      rw [this, map_one]

omit [Finite G] in
theorem imM_relIndex' (K : Subgroup G) {K' : Subgroup G} (hK' : K' ≤ M) :
    (imM hTM K).relIndex (imM hTM K') = K.relIndex K' := by
  unfold imM
  rw [Subgroup.relIndex_map_map_of_injective _ _ (puAmalgam hTM).ofA_injective,
    Subgroup.relIndex_subgroupOf hK']

omit [Finite G] in
theorem relIndex_centralizer_imM_eq {K F : Subgroup G} (hK : K ≤ M) (hF : F ≤ M) :
    (Subgroup.centralizer (imM hTM F : Set (puAmalgam hTM).Universal)).relIndex (imM hTM K) =
      (Subgroup.centralizer (F : Set G)).relIndex K := by
  rw [← Subgroup.inf_relIndex_right, inf_comm, ← imM_inf_centralizer hTM K hF,
    imM_relIndex' hTM _ hK, inf_comm, Subgroup.inf_relIndex_right]

omit [Finite G] in
theorem imM_le_centralizer_iff {K F : Subgroup G} (hK : K ≤ M) (hF : F ≤ M) :
    imM hTM K ≤ Subgroup.centralizer (imM hTM F : Set (puAmalgam hTM).Universal) ↔
      K ≤ Subgroup.centralizer (F : Set G) := by
  constructor
  · intro hle
    have h1 : imM hTM K ≤ imM hTM (K ⊓ Subgroup.centralizer (F : Set G)) := by
      rw [imM_inf_centralizer hTM K hF]
      exact le_inf le_rfl hle
    exact ((imM_le_imM_iff hTM hK).mp h1).trans inf_le_right
  · intro hle
    have h1 : imM hTM K = imM hTM (K ⊓ Subgroup.centralizer (F : Set G)) := by
      rw [inf_eq_left.2 hle]
    rw [h1, imM_inf_centralizer hTM K hF]
    exact inf_le_right

end Dictionary

section Edges

theorem PUHyp.xm_baseA_eq (h : PUHyp M T L) :
    XM (puAmalgam h.le) (baseA _) = imM h.le (Xq M) := by
  rw [puAmalgam.xm_baseA, h.normalCoreIn_eq]

theorem PUHyp.isOffAt_base_iff (h : PUHyp M T L) {F : Subgroup G} (hFT : F ≤ T) :
    IsOffAt (puAmalgam h.le) (baseA _) (baseB _) (imM h.le F) ↔ IsXOff M T F := by
  have hFM : F ≤ M := hFT.trans h.le
  rw [IsOffAt, IsXOff, puAmalgam.qv_baseB, puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le,
    h.xm_baseA_eq, imM_le_imM_iff h.le hFM, imM_le_imM_iff h.le hFM, isElemAbelian_imM_iff h.le hFM,
    relIndex_centralizer_imM_eq h.le (Xq_le M) hFM, imM_relIndex' h.le _ hFM]

theorem PUHyp.offDataAt_base (h : PUHyp M T L) (hD : XOffData M T) :
    OffDataAt (puAmalgam h.le) (baseA _) (baseB _) := by
  have hQ : Qv (puAmalgam h.le) (baseA _) = imM h.le (pCoreOf 2 M) :=
    puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le
  have pull : ∀ F' : Subgroup (puAmalgam h.le).Universal,
      IsOffAt (puAmalgam h.le) (baseA _) (baseB _) F' →
        ∃ F : Subgroup G, F ≤ T ∧ imM h.le F = F' ∧ IsXOff M T F := by
    intro F' hF'
    have hF'T : F' ≤ imM h.le T := by
      have := hF'.1
      rwa [puAmalgam.qv_baseB] at this
    obtain ⟨F, hFT, rfl⟩ := exists_imM_eq_of_le h.le hF'T
    exact ⟨F, hFT, rfl, (h.isOffAt_base_iff hFT).mp hF'⟩
  refine ⟨fun F₁' F₂' h₁ h₂ => ?_, fun F' hF' => ?_, fun F' hF' => ?_⟩
  · obtain ⟨F₁, hF₁T, rfl, hF₁⟩ := pull _ h₁
    obtain ⟨F₂, hF₂T, rfl, hF₂⟩ := pull _ h₂
    rw [hQ, ← imM_sup h.le (hF₁T.trans h.le) (pCoreOf_le' M),
      ← imM_sup h.le (hF₂T.trans h.le) (pCoreOf_le' M), hD.uniq _ _ hF₁ hF₂]
  · obtain ⟨F, hFT, rfl, hF⟩ := pull _ hF'
    rw [h.xm_baseA_eq, hQ, relIndex_centralizer_imM_eq h.le (Xq_le M) (hFT.trans h.le),
      imM_relIndex' h.le _ (hFT.trans h.le)]
    exact hD.eq F hF
  · obtain ⟨F, hFT, rfl, hF⟩ := pull _ hF'
    have hFM : F ≤ M := hFT.trans h.le
    obtain ⟨Z, hZX, hZF, hY⟩ := hD.zc F hF
    have hZM : Z ≤ M := hZX.trans (Xq_le M)
    refine ⟨imM h.le Z, ?_, ?_, fun Y' hY'β hY'F => ?_⟩
    · rw [h.xm_baseA_eq]
      exact imM_mono h.le hZX
    · rwa [imM_le_centralizer_iff h.le hZM hFM]
    · rw [puAmalgam.qv_baseB] at hY'β
      obtain ⟨Y, hYT, rfl⟩ := exists_imM_eq_of_le h.le hY'β
      have hYM : Y ≤ M := hYT.trans h.le
      have hYF : Y ≤ Subgroup.centralizer (F : Set G) :=
        (imM_le_centralizer_iff h.le hYM hFM).mp hY'F
      have key := imM_mono h.le (hY Y hYT hYF)
      have hXC : Xq M ⊓ Subgroup.centralizer (F : Set G) ≤ M := inf_le_left.trans (Xq_le M)
      rwa [imM_commutator h.le hYM hZM, imM_sup h.le (commutator_le_of_le (Xq_le M) hFM)
        (commutator_le_of_le hYM hXC), imM_commutator h.le (Xq_le M) hFM,
        imM_commutator h.le hYM hXC, imM_inf_centralizer h.le _ hFM, ← h.xm_baseA_eq] at key

theorem PUHyp.offDataAt (h : PUHyp M T L) (hD : XOffData M T) {γ ρ : Vtx (puAmalgam h.le)}
    (hγ : IsMVtx _ γ) (hγρ : (puAmalgam h.le).treeGraph.Adj γ ρ) :
    OffDataAt (puAmalgam h.le) γ ρ :=
  offDataAt_of_edge _ (PU.isMVtx_baseA _) (adj_baseA_baseB _) (h.offDataAt_base hD) hγ hγρ

theorem closure_conj_le_centralizer {X' : Type} [Group X'] {S A : Subgroup X'} {x : X'}
    (hS : S ≤ Subgroup.normalizer (A : Set X')) (hx : x ∈ Subgroup.centralizer (A : Set X')) :
    Subgroup.closure {y | ∃ k ∈ S, k * x * k⁻¹ = y} ≤ Subgroup.centralizer (A : Set X') := by
  rw [Subgroup.closure_le]
  rintro _ ⟨k, hk, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_centralizer hS hk) x).mp hx

theorem PUHyp.not_le_normalizer_commutator_xm_base (h : PUHyp M T L)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) α')
    (hgeo : geo _ (baseA _) α' 1 = baseB _) :
    ¬ stab _ (baseA _) ≤ Subgroup.normalizer
      ((⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆ :
        Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) := by
  intro hN
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  set Aα := ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆
  have hXβ : XM _ α' ≤ Qv (puAmalgam h.le) (baseB _) := by
    rw [← hgeo]
    exact xm_le_qv_geo_one _ h20 hb0 hC hc
  have hXn : ¬ XM _ α' ≤ Qv (puAmalgam h.le) (baseA _) := xm_not_le_qv_of_isCritical h20 hb0 hC hc
  obtain ⟨x, hxX, hxQ⟩ := Set.not_subset.mp hXn
  have hAX : Aα ≤ XM _ α' := commutator_xm_le_right _ h20 hb0 hC hc
  have hxC : x ∈ Subgroup.centralizer (Aα : Set (puAmalgam h.le).Universal) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (xm_le_centralizer _ α' hxX) y (xm_le_qv _ α' (hAX hy))
  have hL := h.puTrans_L_le_closure (PU.isMVtx_baseA _) (adj_baseA_baseB _) (hXβ hxX) hxQ
  have hLC := hL.trans (closure_conj_le_centralizer hN hxC)
  rw [puTrans_baseA h.le h.L_subgroupOf_normal] at hLC
  have hxT := hXβ hxX
  rw [puAmalgam.qv_baseB] at hxT
  obtain ⟨a, ha, rfl⟩ := hxT
  have haT : (a : G) ∈ T := Subgroup.mem_subgroupOf.mp ha
  rw [puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le] at hxQ
  have haQ : (a : G) ∉ pCoreOf 2 M := fun hq => hxQ ⟨a, Subgroup.mem_subgroupOf.mpr hq, rfl⟩
  apply haQ
  refine h.mem_pCoreOf_of_comm_Uq haT fun u hu => ?_
  have huM : u ∈ M := Uq_le h.L_le hu
  have hux : (puAmalgam h.le).ofA ⟨u, huM⟩ ∈ XM (puAmalgam h.le) (baseA _) := by
    rw [h.xm_baseA_eq]
    exact ⟨⟨u, huM⟩, Subgroup.mem_subgroupOf.mpr (h.Uq_le_Xq hu), rfl⟩
  have hcomm : ⁅(puAmalgam h.le).ofA ⟨u, huM⟩, (puAmalgam h.le).ofA a⁆ ∈ Aα :=
    Subgroup.commutator_mem_commutator hux hxX
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl' : (puAmalgam h.le).ofA ⟨l, h.L_le hl⟩ ∈ imM h.le L :=
    ⟨⟨l, h.L_le hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have := Subgroup.mem_centralizer_iff.mp (hLC hl') _ hcomm
  rw [← map_commutatorElement, ← map_mul, ← map_mul] at this
  exact (congrArg (Subtype.val : ↥M → G) ((puAmalgam h.le).ofA_injective this)).symm

theorem PUHyp.not_le_normalizer_commutator_xm (h : PUHyp M T L)
    {ε ε' : Vtx (puAmalgam h.le)} (hc : IsCritical _ ε ε') :
    ¬ stab _ ε ≤ Subgroup.normalizer
      ((⁅XM (puAmalgam h.le) ε, XM (puAmalgam h.le) ε'⁆ :
        Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) := by
  have hb0 := h.critDist_pos
  obtain ⟨g, rfl⟩ := exists_eq_smul_baseA _ hc.1
  set α₁ := g⁻¹ • ε'
  have hc₁ : IsCritical _ (baseA _) α₁ := by
    have := (isCritical_smul _ g⁻¹ _ _).mpr hc
    rwa [inv_smul_smul] at this
  obtain ⟨k, hk, hkβ⟩ := exists_mem_stab_smul _ (adj_geo_one_of_isCritical _ hb0 hc₁)
    (adj_baseA_baseB _)
  have hkα : k • baseA (puAmalgam h.le) = baseA _ := (mem_stab _).mp hk
  have hc₂ : IsCritical _ (baseA _) (k • α₁) := by
    have := (isCritical_smul _ k _ _).mpr hc₁
    rwa [hkα] at this
  have hgeo : geo _ (baseA _) (k • α₁) 1 = baseB _ := by
    conv_lhs => rw [← hkα]
    rw [geo_smul, hkβ]
  have key := h.not_le_normalizer_commutator_xm_base hc₂ hgeo
  have e1 : ε' = (g * k⁻¹) • (k • α₁) := by
    rw [smul_smul, inv_mul_cancel_right, smul_inv_smul]
  have e2 : g • baseA (puAmalgam h.le) = (g * k⁻¹) • baseA _ := by
    rw [mul_smul, ← hkα, inv_smul_smul, hkα]
  rw [e1, e2, xm_smul, xm_smul, ← Subgroup.map_commutator, stab_le_normalizer_map_iff]
  exact key

theorem PUHyp.puTrans_L_le_centralizer_commutator_xm (h : PUHyp M T L)
    {ε ε' : Vtx (puAmalgam h.le)} (hc : IsCritical _ ε ε')
    (hN : stab _ (geo _ ε ε' 2) ≤ Subgroup.normalizer
      ((⁅XM (puAmalgam h.le) ε, XM (puAmalgam h.le) ε'⁆ :
        Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal)) :
    puTrans h.le L (geo _ ε ε' 2) ≤ Subgroup.centralizer
      ((⁅XM (puAmalgam h.le) ε, XM (puAmalgam h.le) ε'⁆ :
        Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hC := h.centHyp
  have hb2 := two_le_critDist _ h20 hb0
  have hd : (puAmalgam h.le).treeGraph.dist ε ε' = critDist _ := hc.2.1
  set Aε := ⁅XM (puAmalgam h.le) ε, XM (puAmalgam h.le) ε'⁆
  set μ := geo _ ε ε' 2
  set ρ := geo _ ε ε' 1
  have hερ : (puAmalgam h.le).treeGraph.Adj ε ρ := adj_geo_one_of_isCritical _ hb0 hc
  have hρμ : (puAmalgam h.le).treeGraph.Adj ρ μ := adj_geo _ (i := 1) (by omega)
  have hμ : IsMVtx _ μ := isMVtx_geo_two _ h20 hb0 hc
  have : Finite (Qv (puAmalgam h.le) ρ) :=
    finite_qv _ h20 ((isMVtx_iff_of_adj _ hερ).mp hc.1)
  have hAε : Aε ≤ XM _ ε := Subgroup.le_normalizer_iff_commutator_le_left.mp
    ((xm_le_qv_geo_one _ h20 hb0 hC hc).trans ((qv_le_stab_of_adj _ hερ.symm).trans
      (stab_le_normalizer_xm _ ε)))
  have hAε' : Aε ≤ XM _ ε' := commutator_xm_le_right _ h20 hb0 hC hc
  set S := Qv (puAmalgam h.le) ε ⊔ XM _ ε'
  have hSρ : S ≤ Qv _ ρ := sup_le (qv_le_qv _ h20 hc.1 hερ) (xm_le_qv_geo_one _ h20 hb0 hC hc)
  have hSC : S ≤ Subgroup.centralizer (Aε : Set (puAmalgam h.le).Universal) := by
    refine sup_le ((qv_le_centralizer_xm _ ε).trans (Subgroup.centralizer_le hAε)) ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (xm_le_centralizer _ ε' hx) y (xm_le_qv _ ε' (hAε' hy))
  have hSμ : ¬ S ≤ Qv _ μ := by
    intro hle
    have : Finite S := Finite.of_injective _ (Subgroup.inclusion_injective hSρ)
    have : Finite (Qv (puAmalgam h.le) μ) := Finite.of_injective _
      (Subgroup.inclusion_injective (qv_le_qv _ h20 hμ hρμ.symm))
    obtain ⟨g, hg⟩ := exists_smul_eq_of_isMVtx _ hc.1 hμ
    have hcard : Nat.card (Qv (puAmalgam h.le) μ) = Nat.card (Qv (puAmalgam h.le) ε) := by
      rw [← hg, qv_smul, Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have hlt : Qv (puAmalgam h.le) ε < S :=
      lt_of_le_of_ne le_sup_left fun he =>
        xm_not_le_qv_of_isCritical h20 hb0 hC hc (he ▸ le_sup_right)
    have h1 := Subgroup.card_lt_of_lt hlt
    have h2 := Subgroup.card_le_of_le hle
    omega
  obtain ⟨x, hxS, hxμ⟩ := Set.not_subset.mp hSμ
  exact (h.puTrans_L_le_closure hμ hρμ.symm (hSρ hxS) hxμ).trans
    (closure_conj_le_centralizer hN (hSC hxS))

theorem PUHyp.ms23_of_xOffData (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (hD : XOffData M T) :
    critDist (puAmalgam h.le) = 4 ∧ ∀ ε ε' : Vtx (puAmalgam h.le), IsCritical _ ε ε' →
      stab _ (geo _ ε ε' 2) ≤ Subgroup.normalizer
        ((⁅XM (puAmalgam h.le) ε, XM (puAmalgam h.le) ε'⁆ :
          Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) ∧
      puTrans h.le L (geo _ ε ε' 2) ≤ Subgroup.centralizer
        ((⁅XM (puAmalgam h.le) ε, XM (puAmalgam h.le) ε'⁆ :
          Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) := by
  obtain ⟨h4, hN⟩ := ms23_of_offData h.hyp20 h.critDist_pos h.centHyp hb
    (fun γ ρ hγ hγρ => h.gen23At hγ hγρ) (fun γ ρ hγ hγρ => h.offDataAt hD hγ hγρ)
    (fun ε ε' hc => h.not_le_normalizer_commutator_xm hc)
  exact ⟨h4, fun ε ε' hc => ⟨hN ε ε' hc, h.puTrans_L_le_centralizer_commutator_xm hc
    (hN ε ε' hc)⟩⟩

end Edges

end CFSG.Quasithin.MS93
