module

public import CFSG.Quasithin.MS93.S38EAW
public import CFSG.Quasithin.MS93.S38EAOff
public import CFSG.Quasithin.MS93.S38EIdent
public import CFSG.Quasithin.MS93.S38EAQ
public import CFSG.Quasithin.MS93.S38EPU

public section

namespace CFSG.Quasithin.MS93.S38EA

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.S38E
  CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

omit [Finite G] in
theorem map_phiM_eq (hTM : T ≤ M) (K : Subgroup G) :
    (K.subgroupOf M).map (phiM hTM) =
      (imM hTM K).subgroupOf (stab (puAmalgam hTM) (baseA _)) := by
  ext g
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, hmg⟩
    exact ⟨m, hm, Subtype.ext hmg⟩

theorem exists_xOff_eq (h : PUHyp M T L) (hD : XOffData M T)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) α')
    (hgeo : geo _ (baseA _) α' 1 = baseB _) :
    ∃ F : Subgroup G, IsXOff M T F ∧ imM h.le F = XM (puAmalgam h.le) α' := by
  have hb0 := h.critDist_pos
  have hc' := ms22_iii _ h.hyp20 hb0 h.centHyp hc
  have hoff := (isOffAt_xm h.hyp20 hb0 h.centHyp hc
    (h.offDataAt hD (PU.isMVtx_baseA _) (adj_geo_one_of_isCritical _ hb0 hc))
    (h.offDataAt hD hc'.1 (adj_geo_one_of_isCritical _ hb0 hc'))).1
  rw [hgeo] at hoff
  have hXT : XM (puAmalgam h.le) α' ≤ imM h.le T := by
    have := hoff.1
    rwa [puAmalgam.qv_baseB] at this
  obtain ⟨F, hFT, hF⟩ := exists_imM_eq_of_le h.le hXT
  exact ⟨F, (h.isOffAt_base_iff hFT).mp (hF ▸ hoff), hF⟩

theorem e_eq_four (h : PUHyp M T L) (hD : XOffData M T)
    (hcase : IsHatA6U M T L ∨ IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) 1)
    (hnSp4 : ¬ IsSp4U M T L) {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) α')
    (hgeo : geo _ (baseA _) α' 1 = baseB _) :
    (Qv (puAmalgam h.le) (baseA _)).relIndex (XM _ α') = 4 := by
  obtain ⟨F, hF, he⟩ := relIndex_xm_eq h hD hc hgeo
  rw [he]
  rcases hcase with hX | hX
  · exact h.relIndex_eq_four_of_isHatA6U hX hF
  · obtain ⟨D⟩ := OffVI.PUHyp.nonempty_a6Data h hX hnSp4
    obtain ⟨-, -, -, -, -, -, -, -, -, -, h4⟩ := OffVI.exists_of_isXOff h D hF
    exact h4

variable (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)} {e : ℕ}
  (hS : EndSetup (Vv (puAmalgam h.le) (baseA _)) (stab _ (baseA _)) (puTrans h.le L (baseA _))
    (Qv _ (baseB _)) (Qv _ (baseA _)) (XM _ α') e)
  (lam : ↥⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆ →* ℂˣ)
  (hlam1 : ∀ c : ↥⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆,
    (c : (puAmalgam h.le).Universal) ∈
      ⁅⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆, Qv _ (baseB _)⁆ →
      lam c = 1)

section Vertex

theorem vb_le_vv : Vi (puAmalgam h.le) (baseB _) 1 ≤ Vv (puAmalgam h.le) (baseA _) :=
  vi_one_le_vv _ (adj_baseA_baseB _)

theorem tb_le_normalizer_vb :
    Qv (puAmalgam h.le) (baseB _) ≤
      Subgroup.normalizer ((Vi (puAmalgam h.le) (baseB _) 1 : Subgroup _) : Set _) :=
  (qv_le_stab _ (baseB _)).trans (stab_le_normalizer_of_smul _
    (F := fun ρ => Vi (puAmalgam h.le) ρ 1) (fun g ρ => vi_smul _ g ρ 1) (baseB _))

theorem vv_le_of_vb_le (K : Subgroup (puAmalgam h.le).Universal)
    (hK : stab (puAmalgam h.le) (baseA _) ≤ Subgroup.normalizer (K : Set _))
    (hVb : Vi (puAmalgam h.le) (baseB _) 1 ≤ K) : Vv (puAmalgam h.le) (baseA _) ≤ K :=
  vv_le_of_vi_le _ (adj_baseA_baseB _) hK hVb

theorem qa_le_tb : Qv (puAmalgam h.le) (baseA _) ≤ Qv (puAmalgam h.le) (baseB _) := by
  rw [puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le, puAmalgam.qv_baseB]
  exact Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.mpr (h.pCore_le (Subgroup.mem_subgroupOf.mp hx))

end Vertex

section W

variable (hb : critDist (puAmalgam h.le) = 4)
  (h8 : ∀ ε ε' : Vtx (puAmalgam h.le), IsCritical _ ε ε' →
    ¬ Vv (puAmalgam h.le) ε ≤ Qv (puAmalgam h.le) (geo _ ε' ε 2))
  (hc : IsCritical _ (baseA _) α')
  (hirr : IrrSec (hS.rho lam hlam1).range (commV (hS.kY lam hlam1))
    (commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1)))
  (he4 : e = 4)
include hb h8 hc hirr he4

theorem commutator_qa_le_base :
    ⁅Vv (puAmalgam h.le) (baseA _), Qv (puAmalgam h.le) (baseA _)⁆ ≤
      Subgroup.centralizer (Vv (puAmalgam h.le) (baseA _) : Set _) := by
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  have hnab : ⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆ ≠ ⊥ := by
    refine commutator_vv_ne_bot _ h.hyp20 hb h.centHyp hc ?_
    have h1 := h8 _ α' hc
    have hd : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb
    have e : geo _ α' (baseA _) 2 = geo _ (baseA _) α' 2 := by
      have := geo_symm _ (u := baseA (puAmalgam h.le)) (w := α') (i := 2) (by omega)
      rwa [hd] at this
    rwa [e] at h1
  exact commutator_qa_le hS lam hlam1 (vb_le_vv h) (tb_le_normalizer_vb h) (vv_le_of_vb_le h)
    hirr ⟨by omega, by omega⟩ (index_fixV_eS_eq_four hS lam hlam1 hirr he4)
    (commutator_vi_one_eq_bot _ h.hyp20 hb2 (baseB _)) (vv_le_qv _ hb2 (PU.isMVtx_baseA _))
    (qa_le_tb h) hnab

theorem rho_qa_eq_one {q : (puAmalgam h.le).Universal} (hq : q ∈ Qv (puAmalgam h.le) (baseA _)) :
    hS.rho lam hlam1 ⟨q, hS.qa_le hq⟩ = 1 := by
  have h7 := commutator_qa_le_base h hS lam hlam1 hb h8 hc hirr he4
  ext y
  induction y using QuotientGroup.induction_on with
  | H v =>
    rw [hS.rho_mk lam hlam1, MulAut.one_apply, QuotientGroup.eq]
    apply zc_le_zLam hS.cls2 lam
    rw [mem_zc]
    intro w
    have hc1 : ⁅(v : (puAmalgam h.le).Universal), q⁆ ∈
        Subgroup.centralizer (Vv (puAmalgam h.le) (baseA _) : Set _) :=
      h7 (Subgroup.commutator_mem_commutator v.2 hq)
    have hvc : (v : (puAmalgam h.le).Universal) * ⁅(v : (puAmalgam h.le).Universal), q⁆ =
        ⁅(v : (puAmalgam h.le).Universal), q⁆ * v := Subgroup.mem_centralizer_iff.mp hc1 v v.2
    have e : (((conjV hS.nV ⟨q, hS.qa_le hq⟩ v)⁻¹ * v : ↥(Vv (puAmalgam h.le) (baseA _))) :
        (puAmalgam h.le).Universal) = ⁅(v : (puAmalgam h.le).Universal), q⁆ := by
      have e1 : (((conjV hS.nV ⟨q, hS.qa_le hq⟩ v)⁻¹ * v : ↥(Vv (puAmalgam h.le) (baseA _))) :
          (puAmalgam h.le).Universal) =
          (v : (puAmalgam h.le).Universal)⁻¹ * ⁅(v : (puAmalgam h.le).Universal), q⁆ * v := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjV_apply_coe, commutatorElement_def]
        group
      rw [e1, mul_assoc, ← hvc, inv_mul_cancel_left]
    apply Subtype.ext
    show (w : (puAmalgam h.le).Universal) *
        (((conjV hS.nV ⟨q, hS.qa_le hq⟩ v)⁻¹ * v : ↥(Vv (puAmalgam h.le) (baseA _))) :
          (puAmalgam h.le).Universal) =
      (((conjV hS.nV ⟨q, hS.qa_le hq⟩ v)⁻¹ * v : ↥(Vv (puAmalgam h.le) (baseA _))) :
          (puAmalgam h.le).Universal) * w
    rw [e]
    exact Subgroup.mem_centralizer_iff.mp hc1 w w.2

noncomputable abbrev wRhoM : ↥M →* MulAut (WM hS lam hlam1) :=
  (wRho hS lam hlam1).comp (phiM h.le)

theorem isO2Rep_wRhoM : IsO2Rep L (wRhoM h hS lam hlam1) where
  pCore m hm := by
    have hmQ : ((phiM h.le m : ↥(stab _ _)) : (puAmalgam h.le).Universal) ∈
        Qv (puAmalgam h.le) (baseA _) := by
      rw [phiM_coe, puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le]
      exact ⟨m, Subgroup.mem_subgroupOf.mpr hm, rfl⟩
    have h1 := rho_qa_eq_one h hS lam hlam1 hb h8 hc hirr he4 hmQ
    ext w
    induction w using QuotientGroup.induction_on with
    | H w =>
      show QuotientGroup.mk (⟨hS.rho lam hlam1 (phiM h.le m) w, _⟩ : ↥(commV _)) = _
      congr 1
      apply Subtype.ext
      show hS.rho lam hlam1 ⟨_, hS.qa_le hmQ⟩ w = w
      rw [h1]
      rfl
  ne := by
    obtain ⟨g, hgL, hg1⟩ := hS.exists_lt_secRho_ne_one lam hlam1 hirr
    obtain ⟨m, rfl⟩ := phiM_surjective h.le g
    rw [phiM_coe, puTrans_baseA h.le h.L_subgroupOf_normal] at hgL
    obtain ⟨y, hy, hyx⟩ := hgL
    have hym : y = m := (puAmalgam h.le).ofA_injective hyx
    refine ⟨m, hym ▸ Subgroup.mem_subgroupOf.mp hy, fun h1 => hg1 ?_⟩
    exact secRho_eq_one_of_wRho hS lam hlam1 _ h1

theorem wRho_eq_one_of (g : ↥(stab (puAmalgam h.le) (baseA _)))
    (hgL : (g : (puAmalgam h.le).Universal) ∈ puTrans h.le L (baseA _))
    (hg : hS.secRho lam hlam1 g = 1) : wRho hS lam hlam1 g = 1 := by
  obtain ⟨m, rfl⟩ := phiM_surjective h.le g
  rw [phiM_coe, puTrans_baseA h.le h.L_subgroupOf_normal] at hgL
  obtain ⟨y, hy, hyx⟩ := hgL
  have hym : y = m := (puAmalgam h.le).ofA_injective hyx
  have hmL : (m : G) ∈ L := hym ▸ Subgroup.mem_subgroupOf.mp hy
  have hZ : ∀ m : ↥M, (m : G) ∈ L → ∀ z, qWS hS lam hlam1 z = 1 →
      wRhoM h hS lam hlam1 m z = z := by
    intro m' hm' z hz
    refine zW_le_fixV_kW hS lam hlam1 ((qWS_eq_one_iff hS lam hlam1 z).mp hz) _
      ⟨phiM h.le m', Subgroup.mem_subgroupOf.mpr ?_, rfl⟩
    rw [phiM_coe, puTrans_baseA h.le h.L_subgroupOf_normal]
    exact ⟨m', Subgroup.mem_subgroupOf.mpr hm', rfl⟩
  exact eq_one_of_ext h (sq_WM hS lam hlam1) (isO2Rep_wRhoM h hS lam hlam1 hb h8 hc hirr he4)
    (hS.isIrrRep_rhoM h lam hlam1 hirr).ne (qWS hS lam hlam1)
    (fun m' w => qWS_wRho hS lam hlam1 (phiM h.le m') w) hZ m hmL hg

theorem eW_le_kW (hD : XOffData M T)
    (hcase : IsHatA6U M T L ∨ IsSp4DerSec L (Uq M T L) (Uq M T L ⊓ Zq M L) 1)
    (hnSp4 : ¬ IsSp4U M T L) (hgeo : geo _ (baseA _) α' 1 = baseB _) :
    eW hS lam hlam1 ≤ kW hS lam hlam1 := by
  have hρ := isO2Rep_wRhoM h hS lam hlam1 hb h8 hc hirr he4
  obtain ⟨F, hF, hFX⟩ := exists_xOff_eq h hD hc hgeo
  have hF2 : ∀ m ∈ F, m * m = 1 := fun m hm => by
    have := hF.2.1.2 m hm
    rwa [pow_two] at this
  have hl : ∀ m ∈ F, ∃ l : ↥L, (∃ a : ℕ, l ^ 2 ^ a = 1) ∧ ∃ N : Subgroup G, N ≤ M ∧
      M ≤ Subgroup.normalizer (N : Set G) ∧ ¬ L ≤ N ∧ (l : G)⁻¹ * m ∈ N := by
    intro m hm
    rcases hcase with hX | hX
    · exact exists_l_of_isHatA6U h hX hF hm
    · obtain ⟨D⟩ := OffVI.PUHyp.nonempty_a6Data h hX hnSp4
      exact exists_l_of_a6Data h D hF hm
  have hle := hρ.map_le_imL h hF2 hl
  have e0 : (XM (puAmalgam h.le) α').subgroupOf (stab (puAmalgam h.le) (baseA _)) =
      (F.subgroupOf M).map (phiM h.le) := by
    rw [map_phiM_eq h.le F, hFX]
  have e1 : eW hS lam hlam1 = (F.subgroupOf M).map (wRhoM h hS lam hlam1) := by
    show ((XM _ α').subgroupOf _).map _ = _
    rw [e0, Subgroup.map_map]
  have e2 : kW hS lam hlam1 = (L.subgroupOf M).map (wRhoM h hS lam hlam1) := by
    show ((puTrans h.le L (baseA _)).subgroupOf _).map _ = _
    rw [← EndSetup.map_phiM_L h, Subgroup.map_map]
  rw [e1, e2]
  exact hle

end W

end CFSG.Quasithin.MS93.S38EA
