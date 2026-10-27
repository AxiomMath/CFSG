module

public import CFSG.Quasithin.MS93.Q2GOff
public import CFSG.Quasithin.MS93.S38EMain
public import CFSG.Quasithin.MS93.S38
public import CFSG.Quasithin.MS93.S512NFF
public import CFSG.Quasithin.MS93.S38EAFin
public import CFSG.Quasithin.MS93.S38EAPU
public import CFSG.Quasithin.MS93.S38EAZ

public section

namespace CFSG.Quasithin.MS93.Q2G

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93 CFSG.QuasithinUnique
  CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93.S38E CFSG.Quasithin.MS93.S38EA
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

section Comm

variable (h : PUHyp M T L)
  (h4 : ∀ {t : G}, t ∈ T → t ∉ pCoreOf 2 M →
    4 ≤ (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
      (Uq M T L))
include h4

theorem four_le_card_comm_base (hb2 : 2 < critDist (puAmalgam h.le))
    {z : (puAmalgam h.le).Universal} (hzB : z ∈ Qv (puAmalgam h.le) (baseB _))
    (hzA : z ∉ Qv (puAmalgam h.le) (baseA _)) :
    4 ≤ Nat.card ↥⁅ZM (puAmalgam h.le) (baseA _), Subgroup.zpowers z⁆ := by
  rw [puAmalgam.qv_baseB] at hzB
  obtain ⟨t, htT, rfl⟩ := hzB
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at htT
  have htO : (t : G) ∉ pCoreOf 2 M := fun ht => hzA (by
    rw [puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le]
    exact ⟨t, Subgroup.mem_subgroupOf.mpr ht, rfl⟩)
  have h4t := h4 htT htO
  have hUM : Uq M T L ≤ M := Uq_le h.L_le
  have htM : Subgroup.zpowers (t : G) ≤ M := (Subgroup.zpowers_le).mpr t.2
  have hzp : imM h.le (Subgroup.zpowers (t : G)) =
      Subgroup.zpowers ((puAmalgam h.le).ofA t) := by
    rw [imM, ← MonoidHom.map_zpowers,
      show Subgroup.zpowers (t : G) = (Subgroup.zpowers t).map M.subtype from
        (MonoidHom.map_zpowers M.subtype t).symm, PU.map_subtype_subgroupOf]
  have hrel := relIndex_centralizer_imM_eq h.le hUM htM
  rw [hzp] at hrel
  have hUZ : imM h.le (Uq M T L) ≤ ZM (puAmalgam h.le) (baseA _) := by
    rw [puAmalgam.zm_baseA]
    exact imM_mono h.le (Uq_le_Z0q h.L_le)
  have hZab := commutator_zm_eq_bot (puAmalgam h.le) h.hyp20 hb2 (isMVtx_baseA _)
    (isMVtx_baseA _) (by simp)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hZab
  have hab : ∀ a ∈ imM h.le (Uq M T L), ∀ b ∈ imM h.le (Uq M T L), a * b = b * a :=
    fun a ha b hb => (Subgroup.mem_centralizer_iff.mp (hZab (hUZ ha)) b (hUZ hb)).symm
  have key : ∀ m : ↥M, ∀ y ∈ imM h.le (Uq M T L),
      (puAmalgam h.le).ofA m * y * ((puAmalgam h.le).ofA m)⁻¹ ∈ imM h.le (Uq M T L) := by
    rintro m _ ⟨u, hu, rfl⟩
    refine ⟨m * u * m⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hu ⊢
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_Uq h.le_normalizer m.2) u).mp hu
  have hN : (puAmalgam h.le).ofA t ∈
      Subgroup.normalizer (imM h.le (Uq M T L) : Set (puAmalgam h.le).Universal) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key t x, fun hx => ?_⟩
    have := key t⁻¹ _ hx
    simpa [mul_assoc] using this
  have : Finite ↥(imM h.le (Uq M T L)) := finite_imM' h.le _
  have hc := relIndex_le_card_commutator hab hN
  rw [hrel] at hc
  have hle : ⁅imM h.le (Uq M T L), Subgroup.zpowers ((puAmalgam h.le).ofA t)⁆ ≤
      ⁅ZM (puAmalgam h.le) (baseA _), Subgroup.zpowers ((puAmalgam h.le).ofA t)⁆ :=
    Subgroup.commutator_mono hUZ le_rfl
  have hZn : Subgroup.zpowers ((puAmalgam h.le).ofA t) ≤
      Subgroup.normalizer (ZM (puAmalgam h.le) (baseA _) : Set (puAmalgam h.le).Universal) := by
    rw [Subgroup.zpowers_le]
    refine stab_le_normalizer_zm _ (baseA _) ?_
    rw [puAmalgam.stab_baseA]
    exact ⟨t, Subgroup.mem_subgroupOf.mpr t.2, rfl⟩
  have : Finite ↥(ZM (puAmalgam h.le) (baseA _)) := by
    rw [puAmalgam.zm_baseA]
    exact finite_imM' h.le _
  have : Finite ↥⁅ZM (puAmalgam h.le) (baseA _), Subgroup.zpowers ((puAmalgam h.le).ofA t)⁆ :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hZn))
  exact h4t.trans (hc.trans (Subgroup.card_le_of_le hle))

theorem four_le_card_comm_baseA (hb2 : 2 < critDist (puAmalgam h.le))
    {γ : Vtx (puAmalgam h.le)} (hγ : IsMVtx _ γ)
    (hγA : ¬ ZM (puAmalgam h.le) γ ≤ Qv (puAmalgam h.le) (baseA _))
    (hγB : (puAmalgam h.le).treeGraph.dist γ (baseB _) < critDist (puAmalgam h.le)) :
    4 ≤ Nat.card ↥⁅ZM (puAmalgam h.le) γ, ZM (puAmalgam h.le) (baseA _)⁆ := by
  obtain ⟨z, hzZ, hzA⟩ := Set.not_subset.mp hγA
  have hγQ : ZM (puAmalgam h.le) γ ≤ Qv (puAmalgam h.le) (baseB _) :=
    zm_le_qv_of_dist_lt _ hγ hγB
  have h4z := four_le_card_comm_base h h4 hb2 (hγQ hzZ) hzA
  have hle : ⁅ZM (puAmalgam h.le) (baseA _), Subgroup.zpowers z⁆ ≤
      ⁅ZM (puAmalgam h.le) γ, ZM (puAmalgam h.le) (baseA _)⁆ := by
    rw [Subgroup.commutator_comm (ZM (puAmalgam h.le) γ)]
    exact Subgroup.commutator_mono le_rfl ((Subgroup.zpowers_le).mpr hzZ)
  have hZn : ZM (puAmalgam h.le) γ ≤
      Subgroup.normalizer (ZM (puAmalgam h.le) (baseA _) : Set (puAmalgam h.le).Universal) :=
    (hγQ.trans (qv_le_stab_of_adj _ (adj_baseA_baseB _).symm)).trans
      (stab_le_normalizer_zm _ (baseA _))
  have : Finite ↥(ZM (puAmalgam h.le) (baseA _)) := by
    rw [puAmalgam.zm_baseA]
    exact finite_imM' h.le _
  have : Finite ↥⁅ZM (puAmalgam h.le) γ, ZM (puAmalgam h.le) (baseA _)⁆ := by
    rw [Subgroup.commutator_comm]
    exact Finite.of_injective _ (Subgroup.inclusion_injective
      (Subgroup.le_normalizer_iff_commutator_le_left.mp hZn))
  exact h4z.trans (Subgroup.card_le_of_le hle)

theorem four_le_card_comm_zm (hb : critDist (puAmalgam h.le) = 4)
    {γ δ : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ δ) :
    4 ≤ Nat.card ↥⁅ZM (puAmalgam h.le) γ, ZM (puAmalgam h.le) δ⁆ := by
  have hd : (puAmalgam h.le).treeGraph.dist γ δ = 4 := hc.2.1.trans hb
  have hδ : IsMVtx _ δ :=
    ((even_dist_iff _ γ δ).mp (by rw [hd]; decide)).mp hc.1
  have hδγ : (puAmalgam h.le).treeGraph.dist δ γ = 4 := by rw [tdist_comm]; exact hd
  have hadj : (puAmalgam h.le).treeGraph.Adj δ (geo _ δ γ 1) := adj_geo_one _ (by omega)
  have hνγ : (puAmalgam h.le).treeGraph.dist (geo _ δ γ 1) γ = 3 := by
    rw [dist_geo_right _ (by omega), hδγ]
  obtain ⟨g, hg⟩ := exists_smul_eq_of_isMVtx _ hδ (isMVtx_baseA _)
  have hadj' : (puAmalgam h.le).treeGraph.Adj (baseA _) (g • geo _ δ γ 1) := by
    rw [← hg]
    exact (adj_smul _ g _ _).mpr hadj
  obtain ⟨g', hg', hg'ν⟩ := exists_mem_stab_smul _ hadj' (adj_baseA_baseB _)
  have hkδ : (g' * g) • δ = baseA _ := by rw [mul_smul, hg, (mem_stab _).mp hg']
  have hkν : (g' * g) • geo _ δ γ 1 = baseB _ := by rw [mul_smul, hg'ν]
  have hc' : IsCritical _ ((g' * g) • γ) (baseA _) := by
    rw [← hkδ, isCritical_smul]
    exact hc
  have hdB : (puAmalgam h.le).treeGraph.dist ((g' * g) • γ) (baseB _) <
      critDist (puAmalgam h.le) := by
    rw [← hkν, MS93.dist_smul, tdist_comm, hνγ, hb]
    norm_num
  have h4γ := four_le_card_comm_baseA h h4 (by omega) hc'.1 hc'.2.2 hdB
  rw [← hkδ, zm_smul, zm_smul, ← Subgroup.map_commutator,
    Subgroup.card_map_of_injective (MulAut.conj (g' * g)).injective] at h4γ
  exact h4γ

end Comm

section W

variable (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)} {e : ℕ}
  (hS : EndSetup (Vv (puAmalgam h.le) (baseA _)) (stab _ (baseA _)) (puTrans h.le L (baseA _))
    (Qv _ (baseB _)) (Qv _ (baseA _)) (XM _ α') e)
  (lam : ↥⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆ →* ℂˣ)
  (hlam1 : ∀ c : ↥⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆,
    (c : (puAmalgam h.le).Universal) ∈
      ⁅⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆, Qv _ (baseB _)⁆ →
      lam c = 1)
  (hb : critDist (puAmalgam h.le) = 4)
  (h8 : ∀ ε ε' : Vtx (puAmalgam h.le), IsCritical _ ε ε' →
    ¬ Vv (puAmalgam h.le) ε ≤ Qv (puAmalgam h.le) (geo _ ε' ε 2))
  (hc : IsCritical _ (baseA _) α')
  (hirr : IrrSec (hS.rho lam hlam1).range (commV (hS.kY lam hlam1))
    (commV (hS.kY lam hlam1) ⊓ fixV (hS.kY lam hlam1)))
  (he4 : e = 4)
include hb h8 hc hirr he4

theorem eW_le_kW_of (hD : XOffData M T)
    (hl : ∀ F : Subgroup G, IsXOff M T F → ∀ m ∈ F, ∃ l : ↥L, (∃ e : ℕ, l ^ 2 ^ e = 1) ∧
      ∃ N : Subgroup G, N ≤ M ∧ M ≤ Subgroup.normalizer (N : Set G) ∧ ¬ L ≤ N ∧
        (l : G)⁻¹ * m ∈ N)
    (hgeo : geo _ (baseA _) α' 1 = baseB _) :
    eW hS lam hlam1 ≤ kW hS lam hlam1 := by
  have hρ := isO2Rep_wRhoM h hS lam hlam1 hb h8 hc hirr he4
  obtain ⟨F, hF, hFX⟩ := exists_xOff_eq h hD hc hgeo
  have hF2 : ∀ m ∈ F, m * m = 1 := fun m hm => by
    have := hF.2.1.2 m hm
    rwa [pow_two] at this
  have hle := hρ.map_le_imL h hF2 (hl F hF)
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

theorem false_of_d6 (h : PUHyp M T L) (hD : XOffData M T)
    (hCU : XOffCentU M T L)
    (hrel : ∀ F : Subgroup G, IsXOff M T F → (pCoreOf 2 M).relIndex F = 4)
    (hl : ∀ F : Subgroup G, IsXOff M T F → ∀ m ∈ F, ∃ l : ↥L, (∃ e : ℕ, l ^ 2 ^ e = 1) ∧
      ∃ N : Subgroup G, N ≤ M ∧ M ≤ Subgroup.normalizer (N : Set G) ∧ ¬ L ≤ N ∧
        (l : G)⁻¹ * m ∈ N)
    (h4 : ∀ {t : G}, t ∈ T → t ∉ pCoreOf 2 M →
      4 ≤ (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
        (Uq M T L))
    (hb : critDist (puAmalgam h.le) = 4)
    (hstar : ∀ ε ε' : Vtx (puAmalgam h.le), IsCritical _ ε ε' →
      stab _ (geo _ ε ε' 2) ≤ Subgroup.normalizer
        ((⁅XM (puAmalgam h.le) ε, XM (puAmalgam h.le) ε'⁆ :
          Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal) ∧
      puTrans h.le L (geo _ ε ε' 2) ≤ Subgroup.centralizer
        ((⁅XM (puAmalgam h.le) ε, XM (puAmalgam h.le) ε'⁆ :
          Subgroup (puAmalgam h.le).Universal) : Set (puAmalgam h.le).Universal))
    (h8 : ∀ ε ε' : Vtx (puAmalgam h.le), IsCritical _ ε ε' →
      ¬ Vv (puAmalgam h.le) ε ≤ Qv (puAmalgam h.le) (geo _ ε' ε 2))
    (α' : Vtx (puAmalgam h.le)) (hc : IsCritical _ (baseA _) α')
    (hgeo : geo _ (baseA _) α' 1 = baseB _)
    (lam : ↥⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆ →* ℂˣ)
    (hlam1 : ∀ c : ↥⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆,
      (c : (puAmalgam h.le).Universal) ∈
        ⁅⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆, Qv _ (baseB _)⁆ →
        lam c = 1)
    (hlamc : ∃ c : ↥⁅Vv (puAmalgam h.le) (baseA _), Vv (puAmalgam h.le) (baseA _)⁆,
      (c : (puAmalgam h.le).Universal) ∈
        ⁅⁅Vv (puAmalgam h.le) (baseA _), puTrans h.le L (baseA _)⁆,
          Vv (puAmalgam h.le) (baseA _)⁆ ∧ lam c ≠ 1)
    (hK : AlternatingNatural ((endSetup_base h hD hCU hb hstar h8 hc hgeo).kS lam hlam1) ⊤ ⊥ 6) :
    False := by
  have hS := endSetup_base h hD hCU hb hstar h8 hc hgeo
  have he4 : (Qv (puAmalgam h.le) (baseA _)).relIndex (XM _ α') = 4 := by
    obtain ⟨F, hF, he⟩ := relIndex_xm_eq h hD hc hgeo
    rw [he]
    exact hrel F hF
  have hirr := hS.irrSec lam hlam1 (Or.inr he4) hlamc
  have h4' := index_fixV_eS_eq_four hS lam hlam1 hirr he4
  have hinj := wRho_eq_one_of h hS lam hlam1 hb h8 hc hirr he4
  have hA0 := eW_le_kW_of h hS lam hlam1 hb h8 hc hirr he4 hD hl hgeo
  have hm0 := m0_eq_bot hS lam hlam1 hinj hirr he4 hA0 hK
  have hb2 : 2 < critDist (puAmalgam h.le) := by omega
  have hd : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb
  have hV : ¬ Vv (puAmalgam h.le) (baseA _) ≤ Qv _ (geo _ (baseA _) α' 2) := by
    have h1 := h8 _ α' hc
    have e : geo _ α' (baseA _) 2 = geo _ (baseA _) α' 2 := by
      have := geo_symm _ (u := baseA (puAmalgam h.le)) (w := α') (i := 2) (by omega)
      rwa [hd] at this
    rwa [e] at h1
  have hμ : IsMVtx _ (geo _ (baseA _) α' 2) := isMVtx_geo_two _ h.hyp20 (by omega) hc
  have hαμ : (puAmalgam h.le).treeGraph.dist (baseA _) (geo _ (baseA _) α' 2) = 2 :=
    dist_geo _ (by omega)
  obtain ⟨ρ, hρ, hρμ⟩ : ∃ ρ, (puAmalgam h.le).treeGraph.dist (baseA _) ρ ≤ 2 ∧
      ¬ Zv _ ρ ≤ Qv _ (geo _ (baseA _) α' 2) := by
    by_contra hcon
    push Not at hcon
    exact hV (iSup₂_le fun ρ hρ => hcon ρ hρ)
  obtain ⟨γ, hγ, hdγ, hle⟩ := exists_zv_le_zm _ hc.1 hρ
  have hγμ : ¬ ZM _ γ ≤ Qv _ (geo _ (baseA _) α' 2) := fun h' => hρμ (hle.trans h')
  have hdγμ : (puAmalgam h.le).treeGraph.dist γ (geo _ (baseA _) α' 2) = 4 := by
    have h1 : 4 ≤ (puAmalgam h.le).treeGraph.dist γ (geo _ (baseA _) α' 2) := by
      by_contra hlt
      exact hγμ (zm_le_qv_of_dist_lt _ hγ (by omega))
    have h2 := dist_triangle _ γ (baseA _) (geo _ (baseA _) α' 2)
    rw [tdist_comm _ γ (baseA _)] at h2
    omega
  have hcγ : IsCritical _ γ (geo _ (baseA _) α' 2) := ⟨hγ, by rw [hdγμ, hb], hγμ⟩
  have hge := four_le_card_comm_zm h h4 hb hcγ
  have hBμ : (puAmalgam h.le).treeGraph.dist (baseB _) (geo _ (baseA _) α' 2) ≤ 1 := by
    have := dist_geo_geo (puAmalgam h.le) (u := baseA _) (w := α') (i := 1) (j := 2)
      (by norm_num) (by omega)
    rw [hgeo] at this
    omega
  have hZ : ZM _ (geo _ (baseA _) α' 2) ≤ Vi (puAmalgam h.le) (baseB _) 1 :=
    le_iSup₂_of_le (f := fun ρ (_ : ρ ∈ {ρ : Vtx (puAmalgam h.le) |
      (puAmalgam h.le).treeGraph.dist (baseB _) ρ ≤ 1}) => Zv _ ρ) _ hBμ
      (zv_of_isMVtx _ hμ).ge
  have hle2 := card_commutator_le_two hS lam hlam1 (vb_le_vv h) (tb_le_normalizer_vb h)
    (vv_le_of_vb_le h) hK ⟨by omega, by omega⟩ h4' hm0
    (commutator_vi_one_eq_bot _ h.hyp20 hb2 (baseB _)) hZ
  have hsub : ⁅ZM _ γ, ZM _ (geo _ (baseA _) α' 2)⁆ ≤
      ⁅Vv (puAmalgam h.le) (baseA _), ZM _ (geo _ (baseA _) α' 2)⁆ :=
    Subgroup.commutator_mono (zm_le_vv _ hγ hdγ) le_rfl
  have : Finite ↥(stab (puAmalgam h.le) (baseA _)) := hS.finite
  have : Finite ↥⁅Vv (puAmalgam h.le) (baseA _), ZM _ (geo _ (baseA _) α' 2)⁆ :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      ((Subgroup.commutator_mono le_rfl (zm_le_vv _ hμ hαμ.le)).trans
        ((EndSetup.comm_le_self _).trans hS.v_le)))
  have := Subgroup.card_le_of_le hsub
  omega

theorem false_of_offData (h14 : MS14AS) (hSQ : SQTKQuot)
    (hT : S32.TypeFacts) (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (h360 : Nat.card (S32.Lstar L) = 360) (hD : XOffData M T) (hCU : XOffCentU M T L)
    (hrel : ∀ F : Subgroup G, IsXOff M T F → (pCoreOf 2 M).relIndex F = 4)
    (hl : ∀ F : Subgroup G, IsXOff M T F → ∀ m ∈ F, ∃ l : ↥L, (∃ e : ℕ, l ^ 2 ^ e = 1) ∧
      ∃ N : Subgroup G, N ≤ M ∧ M ≤ Subgroup.normalizer (N : Set G) ∧ ¬ L ≤ N ∧
        (l : G)⁻¹ * m ∈ N)
    (h4 : ∀ {t : G}, t ∈ T → t ∉ pCoreOf 2 M →
      4 ≤ (Subgroup.centralizer ((Subgroup.zpowers t : Subgroup G) : Set G)).relIndex
        (Uq M T L)) :
    False := by
  obtain ⟨hb4, hstar⟩ := h.ms23_of_xOffData hb hD
  have h8 : ∀ ε ε' : Vtx (puAmalgam h.le), IsCritical _ ε ε' →
      ¬ Vv (puAmalgam h.le) ε ≤ Qv (puAmalgam h.le) (geo _ ε' ε 2) :=
    fun ε ε' hc => h.not_vv_le_qv_of_xOffData hb hD hc
  obtain ⟨α', hc, hgeo⟩ := exists_isCritical_geo _ h.hyp20 h.critDist_pos (PU.isMVtx_baseA _)
    (adj_baseA_baseB _)
  have hS := endSetup_base h hD hCU hb4 hstar h8 hc hgeo
  obtain ⟨lam, hlam1, hlamc⟩ := hS.exists_lam
  have he2 := two_le_relIndex_xm h hc hgeo
  have he := e_eq_two_or_four h hD (fun F hF => (hrel F hF).le) hc hgeo
  have hirr := hS.irrSec lam hlam1 he hlamc
  have hconc := h14 _ (hS.sq_SM lam hlam1) _ _ (hS.ffHyp_rhoM h lam hlam1 hirr he2 hSQ)
  exact hS.false_of_ffConclusion h lam hlam1 hirr he2 hT hconc (Or.inl h360) fun _ halt =>
    false_of_d6 h hD hCU hrel hl h4 hb4 hstar h8 α' hc hgeo lam hlam1 hlamc halt

variable {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}
  {l : Submodule F (MSP.V4 F)}

theorem EvenData.false (h14 : MS14AS) (hSQ : SQTKQuot)
    (hT : S32.TypeFacts) (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    (D : EvenData M T L a l) : False := by
  have h360 : Nat.card (S32.Lstar L) = 360 := by
    rcases S512N.card_lstar_of_data h D.sp4 with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact h1
    · omega
  exact false_of_offData h14 hSQ hT h hb h360 (EvenData.xOffData h D)
    ((EvenData.xOffCent h D).xOffCentU L) (fun _ hF => EvenData.relIndex_eq_four h D hF)
    (fun _ hF _ hm => EvenData.exists_l h D hF hm)
    (fun htT htO => EvenData.four_le_relIndex h D htT htO)

end CFSG.Quasithin.MS93.Q2G
