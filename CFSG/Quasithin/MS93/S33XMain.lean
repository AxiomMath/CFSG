module

public import CFSG.Quasithin.MS93.S33XKF
public import CFSG.Quasithin.MS93.S33XSp
public import CFSG.Quasithin.MS93.S33XOm
public import CFSG.Quasithin.MS93.S33LamW
public import CFSG.Quasithin.MS93.Sec2Three

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

theorem two_mul_card_le_of_ne (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) (hk : 2 ≤ k)
    (hXL : ⁅Xq M, L⁆ ≤ Uq M T L) (hne : Xq M ≠ Uq M T L ⊔ Zq M L) {K : Subgroup G}
    {p : Submodule F (MSP.V4 F)} (hp : MSP.IsPoint p)
    (hpK : MSP.xPoint p ≤ (K.subgroupOf M).map a) :
    2 * Nat.card (MSP.V4 F) ≤ Nat.card (MSP.fixSp ((K.subgroupOf M).map a)) *
      (Subgroup.centralizer (K : Set G)).relIndex (Xq M) := by
  obtain ⟨c⟩ := MSP.nonempty_natCoord hd.2.2.2
  set W := Uq M T L ⊔ Zq M L with hW
  have hWX : W ≤ Xq M := sup_le h.Uq_le_Xq inf_le_left
  have hCW : Subgroup.centralizer (K : Set G) ⊓ Xq M ≤ W := by
    rintro x ⟨hxC, hxX⟩
    exact mem_sup_of_commute h hd hk hXL hp hpK hxX fun z hz =>
      (Subgroup.mem_centralizer_iff.mp hxC z hz)
  have hfin : ∀ {H K : Subgroup G}, H.relIndex K ≠ 0 := fun {_ _} =>
    Subgroup.index_ne_zero_of_finite
  have hW2 : 2 ≤ W.relIndex (Xq M) := by
    have h1 : W.relIndex (Xq M) ≠ 1 := by
      rw [Ne, Subgroup.relIndex_eq_one]
      exact fun hle => hne (le_antisymm hle hWX)
    have h0 : W.relIndex (Xq M) ≠ 0 := hfin
    omega
  have hUW : (Subgroup.centralizer (K : Set G)).relIndex (Uq M T L) ≤
      (Subgroup.centralizer (K : Set G) ⊓ Xq M).relIndex W := by
    have e : (Subgroup.centralizer (K : Set G) ⊓ Xq M).relIndex (Uq M T L) =
        (Subgroup.centralizer (K : Set G)).relIndex (Uq M T L) := by
      rw [← Subgroup.inf_relIndex_right, ← Subgroup.inf_relIndex_right
        (H := Subgroup.centralizer (K : Set G)), inf_assoc, inf_eq_right.2 h.Uq_le_Xq]
    rw [← e]
    exact Subgroup.relIndex_le_of_le_right le_sup_left hfin
  have hmul : (Subgroup.centralizer (K : Set G) ⊓ Xq M).relIndex W * W.relIndex (Xq M) =
      (Subgroup.centralizer (K : Set G)).relIndex (Xq M) := by
    rw [Subgroup.relIndex_mul_relIndex _ _ _ hCW hWX, Subgroup.inf_relIndex_right]
  have hV := c.card_le_relIndex (le_normalizer_Uq h.le_normalizer) K
  calc 2 * Nat.card (MSP.V4 F)
      ≤ 2 * (Nat.card (MSP.fixSp ((K.subgroupOf M).map a)) *
          (Subgroup.centralizer (K : Set G)).relIndex (Uq M T L)) :=
        Nat.mul_le_mul_left _ hV
    _ ≤ Nat.card (MSP.fixSp ((K.subgroupOf M).map a)) *
          ((Subgroup.centralizer (K : Set G) ⊓ Xq M).relIndex W * W.relIndex (Xq M)) := by
        rw [mul_comm 2, mul_assoc]
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul hUW hW2)
    _ = _ := by rw [hmul]

omit [Finite G] in
theorem relIndex_centralizer_imM {K F' : Subgroup G} (hTM : T ≤ M) (hK : K ≤ M) (hF : F' ≤ M) :
    (Subgroup.centralizer (imM hTM F' : Set (puAmalgam hTM).Universal)).relIndex (imM hTM K) =
      (Subgroup.centralizer (F' : Set G)).relIndex K := by
  rw [← Subgroup.inf_relIndex_right, inf_comm, ← imM_inf_centralizer hTM K hF,
    relIndex_imM hTM hK, inf_comm, Subgroup.inf_relIndex_right]

theorem finite_imM_of_finite (hTM : T ≤ M) (K : Subgroup G) : Finite ↥(imM hTM K) :=
  Finite.of_surjective (fun x : ↥(K.subgroupOf M) =>
    (⟨_, Subgroup.mem_map_of_mem (puAmalgam hTM).ofA x.2⟩ : ↥(imM hTM K)))
    (by rintro ⟨_, ⟨m, hm, rfl⟩⟩; exact ⟨⟨m, hm⟩, rfl⟩)

theorem relIndex_qv_baseA_eq_card (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {S : Subgroup (puAmalgam h.le).Universal} (hSs : S ≤ stab _ (baseA (puAmalgam h.le)))
    (hS2 : IsPGroup 2 S) :
    (Qv _ (baseA (puAmalgam h.le))).relIndex S = Nat.card (S5.vIm h.le a S) := by
  have hnat := hd.2.2.2
  rw [← h.Uq_inf_Zq] at hnat
  obtain ⟨c⟩ := MSP.nonempty_natCoord hnat
  have hSM : S ≤ imM h.le M := by rwa [← puAmalgam.stab_baseA]
  have hpre2 : IsPGroup 2 (pre h.le S) :=
    (hS2.comap_of_injective (puAmalgam h.le).ofA (puAmalgam h.le).ofA_injective).map M.subtype
  rw [vIm_eq_map_pre h a, card_image_eq_relIndex h le_rfl c (pre_le h.le S),
    puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le]
  conv_lhs => rw [← imM_pre h.le hSM]
  rw [relIndex_imM h.le (pre_le h.le S), ← Subgroup.inf_relIndex_right,
    ← Subgroup.inf_relIndex_right (H := actTriv h)]
  congr 1
  ext x
  constructor
  · rintro ⟨hxQ, hxS⟩
    refine ⟨⟨pCoreOf_le' M hxQ, fun u hu => ?_⟩, hxS⟩
    have hc := Subgroup.mem_centralizer_iff.mp (h.pCoreOf_le_centralizer_Z0q hxQ) u
      (Uq_le_Z0q h.L_le hu)
    rw [commutatorElement_eq_one_iff_mul_comm.2 hc]
    exact one_mem _
  · rintro ⟨hxA, hxS⟩
    refine ⟨?_, hxS⟩
    have hxM := pre_le h.le S hxS
    have h1 : a ⟨x, hxM⟩ = 1 := (image_eq_one_iff h le_rfl c ⟨x, hxM⟩).2 hxA
    obtain ⟨e, he⟩ := hpre2 ⟨x, hxS⟩
    exact S5B.mem_pCoreOf_of_ker h hd h1 ⟨e, by simpa using congrArg Subtype.val he⟩

theorem two_mul_card_le_crit (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) (hk : 2 ≤ k)
    (hXL : ⁅Xq M, L⁆ ≤ Uq M T L) (hne : Xq M ≠ Uq M T L ⊔ Zq M L)
    {β : Vtx (puAmalgam h.le)} (hc : IsCritical (puAmalgam h.le) (baseA _) β)
    (hrel : (Qv _ β).relIndex (ZM (puAmalgam h.le) (baseA _)) = 2 ^ k) :
    (∃ p : Submodule F (MSP.V4 F), MSP.IsPoint p ∧ S5.vIm h.le a (ZM _ β) = MSP.xPoint p) ∧
      2 * Nat.card (MSP.V4 F) ≤ Nat.card (MSP.fixSp (S5.vIm h.le a (XM _ β))) *
        (Qv _ β).relIndex (XM (puAmalgam h.le) (baseA _)) := by
  have h20 := h.hyp20
  have hb := h.critDist_pos
  obtain ⟨p, hp, hpZ⟩ : ∃ p : Submodule F (MSP.V4 F), MSP.IsPoint p ∧
      S5.vIm h.le a (ZM _ β) = MSP.xPoint p := by
    rcases shape_of_sp4Data h hd hc with ⟨-, -, hpZ⟩ | ⟨h1, -, -⟩
    · exact hpZ
    · exfalso
      rw [hrel] at h1
      have : 2 ≤ 2 ^ k := Nat.le_self_pow (by omega) 2
      nlinarith
  refine ⟨⟨p, hp, hpZ⟩, ?_⟩
  have hXs : XM (puAmalgam h.le) β ≤ stab _ (baseA (puAmalgam h.le)) :=
    (xm_le_qv_geo_one _ h20 hb h.centHyp hc).trans
      (qv_le_stab_of_adj _ (adj_geo_one_of_isCritical _ hb hc).symm)
  have hXM : XM (puAmalgam h.le) β ≤ imM h.le M := by rwa [← puAmalgam.stab_baseA]
  set K := pre h.le (XM (puAmalgam h.le) β) with hK
  have hpK : MSP.xPoint p ≤ (K.subgroupOf M).map a := by
    rw [← vIm_eq_map_pre h a, ← hpZ]
    exact Subgroup.map_mono (Subgroup.comap_mono (zm_le_xm _ h20 hb (hc.isMVtx_right _ h20)))
  have h1 := two_mul_card_le_of_ne h hd hk hXL hne hp hpK
  rw [← vIm_eq_map_pre h a] at h1
  have e : (Subgroup.centralizer (K : Set G)).relIndex (Xq M) =
      (Subgroup.centralizer (XM (puAmalgam h.le) β : Set _)).relIndex
        (XM (puAmalgam h.le) (baseA _)) := by
    rw [puAmalgam.xm_baseA, h.normalCoreIn_eq,
      ← relIndex_centralizer_imM h.le (Xq_le M) (pre_le h.le _), imM_pre h.le hXM]
  rw [e] at h1
  refine h1.trans (Nat.mul_le_mul_left _ ?_)
  have : Finite ↥(XM (puAmalgam h.le) (baseA _)) := by
    rw [puAmalgam.xm_baseA]
    exact finite_imM_of_finite h.le _
  exact Subgroup.relIndex_le_of_le_left (qv_le_centralizer_xm _ β) Subgroup.index_ne_zero_of_finite

omit [Fintype F] in
theorem isPGroup_vIm (h : PUHyp M T L) {S : Subgroup (puAmalgam h.le).Universal}
    (hS2 : IsPGroup 2 S) : IsPGroup 2 (S5.vIm h.le a S) :=
  (hS2.comap_of_injective (puAmalgam h.le).ofA (puAmalgam h.le).ofA_injective).map a

omit [Fintype F] in
theorem vIm_comm (h : PUHyp M T L) {S S' : Subgroup (puAmalgam h.le).Universal}
    (hSS' : S ≤ Subgroup.centralizer (S' : Set (puAmalgam h.le).Universal)) :
    ∀ y ∈ S5.vIm h.le a S, ∀ e ∈ S5.vIm h.le a S', y * e = e * y := by
  rintro _ ⟨y, hy, rfl⟩ _ ⟨e, he, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply (puAmalgam h.le).ofA_injective
  rw [map_mul, map_mul]
  exact (Subgroup.mem_centralizer_iff.mp (hSS' hy) _ he).symm

theorem s33X5_of_two_le (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a) (hk : 2 ≤ k)
    (hXL : ⁅Xq M, L⁆ ≤ Uq M T L) (hZc : Zq M L ≤ Subgroup.centralizer (M : Set G))
    {α' : Vtx (puAmalgam h.le)} {Y : Subgroup (puAmalgam h.le).Universal} (hS : S33Hyp h α' Y)
    (hYX : Y ≤ Subgroup.centralizer (XM (puAmalgam h.le) (baseA _) :
      Set (puAmalgam h.le).Universal))
    (hrel : (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) = 2 ^ k) :
    Xq M = Uq M T L ⊔ Zq M L := by
  by_contra hne
  have : CharP F 2 := S5B.charP_two_of_card hd.2.1
  have h20 := h.hyp20
  have hb := h.critDist_pos
  have hC := h.centHyp
  obtain ⟨hc, hYT, -, hY⟩ := hS
  obtain ⟨g, hgα, hgβ, hμ, -⟩ := exists_conj_of_isCritical _ h20 hb hc
  set μ := g⁻¹ • baseA (puAmalgam h.le) with hμdef
  have hcμ : IsCritical _ (baseA (puAmalgam h.le)) μ := ms22_iii _ h20 hb hC hμ
  have hgμ : g • μ = baseA (puAmalgam h.le) := smul_inv_smul g _
  have hconj : ∀ H K : Subgroup (puAmalgam h.le).Universal,
      (H.map (MulAut.conj g).toMonoidHom).relIndex (K.map (MulAut.conj g).toMonoidHom) =
        H.relIndex K := fun H K =>
    Subgroup.relIndex_map_map_of_injective _ _ (MulAut.conj g).injective
  have hst : ∀ {β : Vtx (puAmalgam h.le)}, IsCritical _ (baseA (puAmalgam h.le)) β →
      XM _ β ≤ stab _ (baseA (puAmalgam h.le)) ∧ IsPGroup 2 (XM (puAmalgam h.le) β) := by
    intro β hcβ
    have hle := xm_le_qv_geo_one _ h20 hb hC hcβ
    have hadj := adj_geo_one_of_isCritical _ hb hcβ
    refine ⟨hle.trans (qv_le_stab_of_adj _ hadj.symm),
      (isPGroup_qv _ h20 ((isMVtx_iff_of_adj _ hadj).1 (isMVtx_baseA _))).to_le hle⟩
  obtain ⟨hXs', hX2'⟩ := hst hc
  obtain ⟨hXs, hX2⟩ := hst hcμ
  have hZX' : ZM (puAmalgam h.le) α' ≤ XM _ α' := zm_le_xm _ h20 hb (hc.isMVtx_right _ h20)
  have hZXμ : ZM (puAmalgam h.le) μ ≤ XM _ μ := zm_le_xm _ h20 hb (hcμ.isMVtx_right _ h20)
  obtain ⟨⟨p', hp', hp'Z⟩, hcnt'⟩ := two_mul_card_le_crit h hd hk hXL hne hc hrel
  have hrelμ : (Qv _ μ).relIndex (ZM (puAmalgam h.le) (baseA _)) = 2 ^ k := by
    have e1 : (Qv _ μ).relIndex (ZM (puAmalgam h.le) (baseA _)) =
        (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ α') := by
      rw [← hconj (Qv _ μ) (ZM _ (baseA _)), ← qv_smul, ← zm_smul, hgμ, hgα]
    rw [e1, relIndex_qv_baseA_eq_card h hd (hZX'.trans hXs') (hX2'.to_le hZX'), hp'Z,
      MSP.card_xPoint hp', Nat.card_eq_fintype_card, hd.2.1]
  obtain ⟨⟨p, hp, hpZ⟩, hcnt⟩ := two_mul_card_le_crit h hd hk hXL hne hcμ hrelμ
  have e2 : (Qv _ α').relIndex (XM (puAmalgam h.le) (baseA _)) =
      Nat.card (S5.vIm h.le a (XM _ μ)) := by
    rw [← relIndex_qv_baseA_eq_card h hd hXs hX2, ← hconj (Qv _ (baseA _)) (XM _ μ),
      ← qv_smul, ← xm_smul, hgα, hgμ]
  have e3 : (Qv _ μ).relIndex (XM (puAmalgam h.le) (baseA _)) =
      Nat.card (S5.vIm h.le a (XM _ α')) := by
    rw [← relIndex_qv_baseA_eq_card h hd hXs' hX2', ← hconj (Qv _ μ) (XM _ (baseA _)),
      ← qv_smul, ← xm_smul, hgμ, hgα]
  rw [e2] at hcnt'
  rw [e3] at hcnt
  set Y' := Y.map (MulAut.conj g⁻¹).toMonoidHom with hY'
  have hYY : Y = Y'.map (MulAut.conj g).toMonoidHom := (map_conj_map_conj_inv Y g).symm
  have hY'T : Y' ≤ imM h.le T := by
    rw [← puAmalgam.qv_baseB, ← map_conj_le_map_conj_iff g, ← hYY, ← qv_smul, hgβ]
    exact hYT
  have hY'X : Y' ≤ Subgroup.centralizer (XM (puAmalgam h.le) μ : Set _) := by
    rw [← map_conj_le_map_conj_iff g, ← hYY, ← PU.centralizer_map_mulEquiv, ← xm_smul, hgμ]
    exact hYX
  have hY's : Y' ≤ stab _ (baseA (puAmalgam h.le)) := by
    rw [puAmalgam.stab_baseA]
    exact hY'T.trans (imM_mono h.le h.le)
  have hE : ∀ y ∈ S5.vIm h.le a Y', ∀ v : MSP.V4 F,
      MSP.mat y *ᵥ v - v ∈ MSP.commSp (S5.vIm h.le a (XM _ μ)) := by
    intro y hy v
    refine sub_mem_commSp_of_commute hp hp' (hpZ ▸ Subgroup.map_mono (Subgroup.comap_mono hZXμ))
      (hp'Z ▸ Subgroup.map_mono (Subgroup.comap_mono hZX')) (isPGroup_vIm h hX2) ?_ hcnt' hcnt
      (vIm_comm h hY'X y hy) v
    have hab := vIm_comm (a := a) h (S := XM _ μ) (S' := XM _ μ) fun x hx =>
      Subgroup.mem_centralizer_iff.mpr fun z hz =>
        ((isMulCommutative_subgroup_iff.mp (isElemAbelian_xm _ μ).1) _ hz _ hx)
    exact hab
  have hnat := hd.2.2.2
  rw [← h.Uq_inf_Zq] at hnat
  obtain ⟨-, -, β, hβ, hβker, hβα⟩ := id hnat
  have hAβ := isCoordAct_of_natSp hβα
  have hCfix : ∀ m ∈ M, ∀ z ∈ Uq M T L ⊓ Zq M L, m * z * m⁻¹ = z := fun m hm z hz => by
    rw [(Subgroup.mem_centralizer_iff.mp (hZc hz.2) m hm), mul_inv_cancel_right]
  have hpE : MSP.xPoint p ≤ ((pre h.le (XM _ μ)).subgroupOf M).map a := by
    rw [← vIm_eq_map_pre h a, ← hpZ]
    exact Subgroup.map_mono (Subgroup.comap_mono hZXμ)
  have hE' : ∀ y ∈ ((pre h.le Y').subgroupOf M).map a, ∀ v : MSP.V4 F,
      MSP.mat y *ᵥ v - v ∈ MSP.commSp (((pre h.le (XM _ μ)).subgroupOf M).map a) := by
    rw [← vIm_eq_map_pre h a, ← vIm_eq_map_pre h a]
    exact hE
  have hUY := commutator_le_of_commSp h le_rfl hβ hβker hAβ hk hd.2.1 h.L_le hd.2.2.1 hCfix
    (pre_le h.le (XM _ μ)) hp hpE (pre_le h.le Y') hE'
  have hXM : XM (puAmalgam h.le) μ ≤ imM h.le M := by rwa [← puAmalgam.stab_baseA]
  have hY'M : Y' ≤ imM h.le M := by rwa [← puAmalgam.stab_baseA]
  have h1 : ⁅ZM (puAmalgam h.le) (baseA _), Y'⁆ ≤ ⁅XM (puAmalgam h.le) μ, XM _ (baseA _)⁆ := by
    rw [puAmalgam.zm_baseA, ← imM_pre h.le hY'M, ← imM_commutator h.le (Z0q_le M T) (pre_le h.le _),
      Subgroup.commutator_comm (XM _ μ), puAmalgam.xm_baseA, h.normalCoreIn_eq,
      ← imM_pre h.le hXM, ← imM_commutator h.le (Xq_le M) (pre_le h.le _),
      commutator_Z0q_eq h (pre_le_of_le_imM h hY'T)]
    refine imM_mono h.le (hUY.trans (Subgroup.commutator_mono h.Uq_le_Xq le_rfl))
  have hL : ⁅ZM (puAmalgam h.le) α', Y⁆ =
      (⁅ZM (puAmalgam h.le) (baseA _), Y'⁆).map (MulAut.conj g).toMonoidHom := by
    rw [hYY, ← hgα, zm_smul, Subgroup.map_commutator]
  have hR : ⁅XM (puAmalgam h.le) (baseA _), XM (puAmalgam h.le) α'⁆ =
      (⁅XM (puAmalgam h.le) μ, XM _ (baseA _)⁆).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_commutator, ← xm_smul, ← xm_smul, hgμ, hgα]
  apply hY
  refine le_sup_of_le_left ?_
  rw [hL, hR]
  exact Subgroup.map_mono h1

end CFSG.Quasithin.MS93.S33
