
module


public import CFSG.Sporadic.Th.Max3.Core
public import Certificates.Certificate10091

public section

namespace CFSG.Sporadic.Th.Max3

open CFSG.Sporadic.Th.Native CFSG.ComponentClassification.PresentationLocal
open scoped commutatorElement

instance instNormalQSubgroupOfM :
    (Q.subgroupOf M).Normal := normal_Q_subgroupOf_M

namespace AltQuot

@[expose] noncomputable def carm
    (k : CarmichaelIndex 9) : J := wordProd (carmWord k.1)

theorem carm_mem_M
    (k : CarmichaelIndex 9) : carm k ∈ M := wordProd_mem_M _

@[expose] noncomputable def carmM
    (k : CarmichaelIndex 9) : ↥M := ⟨carm k, carm_mem_M k⟩

@[expose] noncomputable def waM : ↥M :=
  carmM (carmIdx 2) * carmM (carmIdx 3) ^ 2 * carmM (carmIdx 2) * carmM (carmIdx 4) *
    carmM (carmIdx 5) ^ 2 * carmM (carmIdx 4) * carmM (carmIdx 6) * carmM (carmIdx 7) ^ 2 *
    carmM (carmIdx 6)

@[expose] noncomputable def wbM : ↥M :=
  carmM (carmIdx 2) ^ 2 * carmM (carmIdx 3) * carmM (carmIdx 4) ^ 2 * carmM (carmIdx 3) *
    carmM (carmIdx 5) ^ 2 * carmM (carmIdx 6) * carmM (carmIdx 7) ^ 2 * carmM (carmIdx 8)

@[expose] noncomputable def carmBar
    (k : CarmichaelIndex 9) : MQ := proj (carmM k)

theorem proj_waM :
    proj waM = carmBar (carmIdx 2) * carmBar (carmIdx 3) ^ 2 * carmBar (carmIdx 2) *
      carmBar (carmIdx 4) * carmBar (carmIdx 5) ^ 2 * carmBar (carmIdx 4) * carmBar (carmIdx 6) *
      carmBar (carmIdx 7) ^ 2 * carmBar (carmIdx 6) := by
  simp only [waM, carmBar, map_mul, map_pow]

theorem proj_wbM :
    proj wbM = carmBar (carmIdx 2) ^ 2 * carmBar (carmIdx 3) * carmBar (carmIdx 4) ^ 2 *
      carmBar (carmIdx 3) * carmBar (carmIdx 5) ^ 2 * carmBar (carmIdx 6) *
      carmBar (carmIdx 7) ^ 2 * carmBar (carmIdx 8) := by
  simp only [wbM, carmBar, map_mul, map_pow]

theorem carmWord_eval : ∀ k : CarmichaelIndex 9,
    ((carmWord k.1).map (Gen.eval aPerm bPerm)).prod = carmichaelPerm k := by
  decide


end AltQuot

namespace AltQuot

theorem isRows_carm
    (k : CarmichaelIndex 9) : IsRows (carmRows k) (carm k) :=
  IsRows.word isRows_x isRows_y _

theorem isRows_wa :
    IsRows waRows (waM : J) :=
  (((((((((isRows_carm _).mul ((isRows_carm _).pow 2)).mul (isRows_carm _)).mul (isRows_carm _)).mul
    ((isRows_carm _).pow 2)).mul (isRows_carm _)).mul (isRows_carm _)).mul
    ((isRows_carm _).pow 2)).mul (isRows_carm _))

theorem isRows_wb :
    IsRows wbRows (wbM : J) :=
  ((((((((isRows_carm _).pow 2).mul (isRows_carm _)).mul ((isRows_carm _).pow 2)).mul
    (isRows_carm _)).mul ((isRows_carm _).pow 2)).mul (isRows_carm _)).mul
    ((isRows_carm _).pow 2)).mul (isRows_carm _)

theorem isRows_nfIdx
    (k : Fin 512) : IsRows (rowsNfIdx k) (nfAt k) := isRows_nfN _ _

private theorem native_quotient_facts :
    (∀ k : CarmichaelIndex 9,
      eqRows (powRows (carmRows k) 3) (rowsNfIdx (carmCubeIdx k)) = true) ∧
    (∀ j k : CarmichaelIndex 9, j.1 < k.1 →
      eqRows (powRows (mulRows (carmRows j) (carmRows k)) 2) (rowsNfIdx (carmPairIdx j k)) =
        true) ∧
    eqRows (mulRows rowsX waRows) (rowsNfIdx 299) = true ∧
    eqRows (mulRows (powRows rowsY 5) wbRows) (rowsNfIdx 201) = true ∧
    eqRows rowsCommXQ idRows = false ∧ eqRows rowsCommXQ rowsZ = false :=
  Certificates.certificate10091

theorem carm_pow_three_eq
    (k : CarmichaelIndex 9) : carm k ^ 3 = nfAt (carmCubeIdx k) := by
  obtain ⟨h, -⟩ := native_quotient_facts
  exact ((isRows_carm k).pow 3).eq_of_eqRows (isRows_nfIdx _) (h k)

theorem carm_pow_three_mem_Q
    (k : CarmichaelIndex 9) : carm k ^ 3 ∈ Q := by
  rw [carm_pow_three_eq]
  exact nfAt_mem_Q _

theorem carm_mul_sq_eq
    {j k : CarmichaelIndex 9} (h : j.1 < k.1) :
    (carm j * carm k) ^ 2 = nfAt (carmPairIdx j k) := by
  obtain ⟨-, h2, -⟩ := native_quotient_facts
  exact (((isRows_carm j).mul (isRows_carm k)).pow 2).eq_of_eqRows (isRows_nfIdx _) (h2 j k h)

theorem carm_mul_sq_mem_Q
    {j k : CarmichaelIndex 9} (h : j.1 < k.1) :
    (carm j * carm k) ^ 2 ∈ Q := by
  rw [carm_mul_sq_eq h]
  exact nfAt_mem_Q _

theorem x_inv_mul_wa_eq :
    x⁻¹ * (waM : J) = nfAt 299 := by
  obtain ⟨-, -, h, -⟩ := native_quotient_facts
  rw [x_inv]
  exact (isRows_x.mul isRows_wa).eq_of_eqRows (isRows_nfIdx _) h

theorem x_inv_mul_wa_mem_Q :
    x⁻¹ * (waM : J) ∈ Q := by
  rw [x_inv_mul_wa_eq]
  exact nfAt_mem_Q _

theorem y_inv_mul_wb_eq :
    y⁻¹ * (wbM : J) = nfAt 201 := by
  obtain ⟨-, -, -, h, -⟩ := native_quotient_facts
  rw [y_inv]
  exact ((isRows_y.pow 5).mul isRows_wb).eq_of_eqRows (isRows_nfIdx _) h

theorem y_inv_mul_wb_mem_Q :
    y⁻¹ * (wbM : J) ∈ Q := by
  rw [y_inv_mul_wb_eq]
  exact nfAt_mem_Q _

theorem comm_mem_zpowers
    {m g : J} (hm : m ∈ Q) (hg : g ∈ Q) : ⁅m, g⁆ ∈ Subgroup.zpowers z := by
  have h : ⁅(⟨m, hm⟩ : Q), (⟨g, hg⟩ : Q)⁆ ∈ Subgroup.center Q := by
    rw [← isExtraspecialPGroup_Q.2.1, _root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  rw [center_Q] at h
  exact h

theorem q_inv
    (i : Fin 8) : (q i)⁻¹ = q i := inv_eq_of_mul_eq_one_right (q_mul_self i)

theorem comm_x_q_one_eq :
    ⁅x, q 1⁆ = x * q 1 * x * q 1 := by
  rw [commutatorElement_def, x_inv, q_inv]

theorem comm_x_q_one_not_mem :
    ⁅x, q 1⁆ ∉ Subgroup.zpowers z := by
  obtain ⟨-, -, -, -, h1, h2⟩ := native_quotient_facts
  have hR : IsRows rowsCommXQ (x * q 1 * x * q 1) :=
    ((isRows_x.mul (isRows_q 1)).mul isRows_x).mul (isRows_q 1)
  intro hmem
  obtain ⟨b, hb⟩ := (CFSG.Certificates.ExtraspecialNF.mem_zpowers_iff_exists symplectic_rel).1 hmem
  rw [comm_x_q_one_eq] at hb
  rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases b with rfl | rfl
  · exact hR.ne_of_eqRows IsRows.one h1 (by simpa using hb.symm)
  · exact hR.ne_of_eqRows isRows_z h2
      (by simpa [CFSG.Certificates.ExtraspecialNF.val_one_two] using hb.symm)

theorem conj_zpowers
    {m : J} (hm : m ∈ M) {w : J} (hw : w ∈ Subgroup.zpowers z) :
    m * w * m⁻¹ = w := by
  have hz : z ∈ Subgroup.centralizer ({m} : Set J) := Subgroup.mem_centralizer_iff.2 fun h hh => by
    rw [Set.mem_singleton_iff.1 hh]
    exact (commute_z_of_mem_M hm).symm.eq
  have hw' := Subgroup.mem_centralizer_iff.1 (Subgroup.zpowers_le.2 hz hw) m rfl
  rw [hw', mul_inv_cancel_right]

theorem conj_mem_Q_of_mem_M
    {h : J} (hh : h ∈ M) {g : J} (hg : g ∈ Q) : h * g * h⁻¹ ∈ Q :=
  (Subgroup.mem_normalizer_iff.1 (M_le_normalizer_Q hh) g).1 hg

@[expose] def actKer :
    Subgroup ↥M where
  carrier := {m | ∀ g ∈ Q, ⁅(m : J), g⁆ ∈ Subgroup.zpowers z}
  one_mem' := fun g _ => by simp [commutatorElement_def]
  mul_mem' := fun {m m'} hm hm' g hg => by
    have e : ⁅((m * m' : ↥M) : J), g⁆ = (m : J) * ⁅(m' : J), g⁆ * (m : J)⁻¹ * ⁅(m : J), g⁆ := by
      simp only [commutatorElement_def, Subgroup.coe_mul]
      group
    rw [e, conj_zpowers m.2 (hm' g hg)]
    exact Subgroup.mul_mem _ (hm' g hg) (hm g hg)
  inv_mem' := fun {m} hm g hg => by
    have e : ⁅((m⁻¹ : ↥M) : J), g⁆ = (m : J)⁻¹ * ⁅(m : J), g⁆⁻¹ * ((m : J)⁻¹)⁻¹ := by
      simp only [commutatorElement_def, Subgroup.coe_inv]
      group
    rw [e, conj_zpowers (M.inv_mem m.2) (Subgroup.inv_mem _ (hm g hg))]
    exact Subgroup.inv_mem _ (hm g hg)

theorem actKer_normal :
    actKer.Normal := by
  refine ⟨fun n hn h g hg => ?_⟩
  have hg' : (h : J)⁻¹ * g * ((h : J)⁻¹)⁻¹ ∈ Q := conj_mem_Q_of_mem_M (M.inv_mem h.2) hg
  have e : ⁅((h * n * h⁻¹ : ↥M) : J), g⁆ =
      (h : J) * ⁅(n : J), (h : J)⁻¹ * g * ((h : J)⁻¹)⁻¹⁆ * (h : J)⁻¹ := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e, conj_zpowers h.2 (hn _ hg')]
  exact hn _ hg'

theorem Q_le_actKer :
    Q.subgroupOf M ≤ actKer := fun _ hm _ hg => comm_mem_zpowers hm hg

theorem x_not_mem_actKer :
    (⟨x, x_mem_M⟩ : ↥M) ∉ actKer :=
  fun h => comm_x_q_one_not_mem (h (q 1) (q_mem_Q 1))

end AltQuot

theorem x_not_mem_Q :
    x ∉ Q := fun h => AltQuot.x_not_mem_actKer (AltQuot.Q_le_actKer h)

namespace AltQuot

theorem carmBar_pow_three
    (k : CarmichaelIndex 9) : carmBar k ^ 3 = 1 := by
  rw [carmBar, ← map_pow, proj_eq_one_iff]
  exact carm_pow_three_mem_Q k

theorem carmBar_mul_sq_of_lt
    {j k : CarmichaelIndex 9} (h : j.1 < k.1) :
    (carmBar j * carmBar k) ^ 2 = 1 := by
  rw [carmBar, carmBar, ← map_mul, ← map_pow, proj_eq_one_iff]
  exact carm_mul_sq_mem_Q h

theorem carmBar_mul_sq
    {j k : CarmichaelIndex 9} (h : j ≠ k) : (carmBar j * carmBar k) ^ 2 = 1 := by
  have hne : j.1 ≠ k.1 := fun h' => h (Subtype.ext h')
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact carmBar_mul_sq_of_lt hlt
  · exact sq_swap_eq_one (carmBar_mul_sq_of_lt hgt)

theorem proj_x :
    proj ⟨x, x_mem_M⟩ = proj waM := by
  rw [proj_eq_proj_iff]
  exact x_inv_mul_wa_mem_Q

theorem proj_y :
    proj ⟨y, y_mem_M⟩ = proj wbM := by
  rw [proj_eq_proj_iff]
  exact y_inv_mul_wb_mem_Q

theorem phi_aPerm
    {φ : alternatingGroup (Fin 9) →* MQ}
    (hφ : ∀ k, φ (carmichaelCycle k) = carmBar k) :
    φ ⟨aPerm, aPerm_mem⟩ = proj ⟨x, x_mem_M⟩ := by
  rw [aPerm_eq_prod, proj_x, proj_waM]
  simp only [map_mul, map_pow, hφ]

theorem phi_bPerm
    {φ : alternatingGroup (Fin 9) →* MQ}
    (hφ : ∀ k, φ (carmichaelCycle k) = carmBar k) :
    φ ⟨bPerm, bPerm_mem⟩ = proj ⟨y, y_mem_M⟩ := by
  rw [bPerm_eq_prod, proj_y, proj_wbM]
  simp only [map_mul, map_pow, hφ]

end AltQuot

open AltQuot

theorem exists_quotient_equiv :
    ∃ κ : (↥M ⧸ Q.subgroupOf M) ≃* alternatingGroup (Fin 9),
      (κ (QuotientGroup.mk ⟨x, x_mem_M⟩) : Equiv.Perm (Fin 9)) = aPerm ∧
      (κ (QuotientGroup.mk ⟨y, y_mem_M⟩) : Equiv.Perm (Fin 9)) = bPerm := by
  obtain ⟨φ, hφ⟩ := exists_hom_carmichaelCycle (n := 9) (by norm_num) carmBar carmBar_pow_three
    (fun _ _ h => carmBar_mul_sq h)
  have hax := phi_aPerm hφ
  have hby := phi_bPerm hφ
  have : IsSimpleGroup (alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
  have hinj : Function.Injective φ := by
    rcases (MonoidHom.normal_ker φ).eq_bot_or_eq_top with h | h
    · exact (MonoidHom.ker_eq_bot_iff φ).mp h
    · exfalso
      have hk : (⟨aPerm, aPerm_mem⟩ : alternatingGroup (Fin 9)) ∈ φ.ker := h ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hax] at hk
      exact x_not_mem_Q ((proj_eq_one_iff (g := ⟨x, x_mem_M⟩)).1 hk)
  have hsurj : Function.Surjective φ := by
    intro t
    obtain ⟨⟨g, hg⟩, rfl⟩ := proj_surjective t
    exact proj_mem_of_generators (H := φ.range) ⟨_, hax⟩ ⟨_, hby⟩ g hg
  let e := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
  refine ⟨e.symm, ?_, ?_⟩
  · have h : e ⟨aPerm, aPerm_mem⟩ = QuotientGroup.mk ⟨x, x_mem_M⟩ := hax
    rw [← h, MulEquiv.symm_apply_apply]
  · have h : e ⟨bPerm, bPerm_mem⟩ = QuotientGroup.mk ⟨y, y_mem_M⟩ := hby
    rw [← h, MulEquiv.symm_apply_apply]

noncomputable def kappa :
    (↥M ⧸ Q.subgroupOf M) ≃* alternatingGroup (Fin 9) :=
  exists_quotient_equiv.choose

theorem kappa_mk_x :
    (kappa (QuotientGroup.mk ⟨x, x_mem_M⟩) : Equiv.Perm (Fin 9)) = aPerm :=
  exists_quotient_equiv.choose_spec.1

theorem kappa_mk_y :
    (kappa (QuotientGroup.mk ⟨y, y_mem_M⟩) : Equiv.Perm (Fin 9)) = bPerm :=
  exists_quotient_equiv.choose_spec.2

namespace AltQuot

theorem isSimpleGroup_MQ :
    IsSimpleGroup MQ := by
  have : IsSimpleGroup (alternatingGroup (Fin 9)) := alternatingGroup.isSimpleGroup (by simp)
  exact kappa.isSimpleGroup

theorem card_MQ :
    Nat.card MQ = 181440 := by
  rw [Nat.card_congr kappa.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
  decide

theorem actKer_le_Q :
    actKer ≤ Q.subgroupOf M := by
  have := isSimpleGroup_MQ
  have hn : (actKer.map proj).Normal := actKer_normal.map proj proj_surjective
  rcases hn.eq_bot_or_eq_top with h | h
  · intro m hm
    have hmem : proj m ∈ actKer.map proj := ⟨m, hm, rfl⟩
    rw [h, Subgroup.mem_bot, proj_eq_one_iff] at hmem
    exact hmem
  · exfalso
    have hx : proj ⟨x, x_mem_M⟩ ∈ actKer.map proj := by
      rw [h]
      exact Subgroup.mem_top _
    obtain ⟨m, hm, hmx⟩ := hx
    have h1 : m⁻¹ * ⟨x, x_mem_M⟩ ∈ Q.subgroupOf M := proj_eq_proj_iff.1 hmx
    exact x_not_mem_actKer (by simpa using actKer.mul_mem hm (Q_le_actKer h1))

theorem isPGroup_Q_subgroupOf_M :
    IsPGroup 2 (Q.subgroupOf M) :=
  isExtraspecialPGroup_Q.1.of_equiv (Subgroup.subgroupOfEquivOfLe Q_le_M).symm

end AltQuot

theorem mem_Q_iff_comm_mem_zpowers
    {m : J} (hm : m ∈ M) :
    m ∈ Q ↔ ∀ g ∈ Q, ⁅m, g⁆ ∈ Subgroup.zpowers z :=
  ⟨fun h _ hg => AltQuot.comm_mem_zpowers h hg,
    fun h => AltQuot.actKer_le_Q (show (⟨m, hm⟩ : ↥M) ∈ AltQuot.actKer from h)⟩

theorem card_M :
    Nat.card M = 92897280 := by
  have h1 : Nat.card ↥M = Nat.card (↥M ⧸ Q.subgroupOf M) * Nat.card (Q.subgroupOf M) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card (Q.subgroupOf M) = 512 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q_le_M).toEquiv]
    exact card_Q
  rw [h1, h2]
  exact congrArg (· * 512) AltQuot.card_MQ

theorem pCore_M :
    CFSG.pCore 2 M = Q.subgroupOf M := by
  have := AltQuot.isSimpleGroup_MQ
  refine le_antisymm ?_ (le_sSup ⟨normal_Q_subgroupOf_M, AltQuot.isPGroup_Q_subgroupOf_M⟩)
  have hPn : (CFSG.pCore 2 ↥M).Normal := CFSG.pCore_normal
  have hPp : IsPGroup 2 (CFSG.pCore 2 ↥M) := CFSG.pCore_isPGroup
  have hn : ((CFSG.pCore 2 ↥M).map AltQuot.proj).Normal :=
    hPn.map AltQuot.proj AltQuot.proj_surjective
  have hp : IsPGroup 2 ((CFSG.pCore 2 ↥M).map AltQuot.proj) := hPp.map AltQuot.proj
  rcases hn.eq_bot_or_eq_top with h | h
  · intro m hm
    have hmem : AltQuot.proj m ∈ (CFSG.pCore 2 ↥M).map AltQuot.proj := ⟨m, hm, rfl⟩
    rw [h, Subgroup.mem_bot, AltQuot.proj_eq_one_iff] at hmem
    exact hmem
  · exfalso
    rw [h] at hp
    have : Finite AltQuot.MQ := Finite.of_equiv _ kappa.symm.toEquiv
    obtain ⟨n, hn2⟩ := (IsPGroup.iff_card (p := 2)).1
      (hp.of_surjective (Subgroup.topEquiv : (⊤ : Subgroup AltQuot.MQ) ≃* AltQuot.MQ).toMonoidHom
        (Subgroup.topEquiv : (⊤ : Subgroup AltQuot.MQ) ≃* AltQuot.MQ).surjective)
    rw [AltQuot.card_MQ] at hn2
    have h3 : 3 ∣ 2 ^ n := hn2 ▸ (by norm_num : 3 ∣ 181440)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem map_pCore_M :
    (CFSG.pCore 2 M).map M.subtype = Q := by
  rw [pCore_M]
  exact Subgroup.map_subgroupOf_eq_of_le Q_le_M

theorem centralizer_Q_inf_M :
    Subgroup.centralizer (Q : Set J) ⊓ M = Subgroup.zpowers z := by
  refine le_antisymm ?_ ?_
  · rintro m ⟨hmc, hmM⟩
    have hmQ : m ∈ Q := (mem_Q_iff_comm_mem_zpowers hmM).2 fun g hg => by
      have h : ⁅m, g⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2
        (Subgroup.mem_centralizer_iff.1 hmc g hg).symm
      rw [h]
      exact Subgroup.one_mem _
    have hcen : (⟨m, hmQ⟩ : Q) ∈ Subgroup.center Q := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hmc g g.2)
    rw [center_Q] at hcen
    exact hcen
  · refine Subgroup.zpowers_le.2 ⟨?_, z_mem_M⟩
    exact Subgroup.mem_centralizer_iff.2 fun g hg => (commute_z_of_mem_M (Q_le_M hg)).symm.eq

theorem max3_alternating_quotient :
    (∃ κ : (↥M ⧸ Q.subgroupOf M) ≃* alternatingGroup (Fin 9),
      (κ (QuotientGroup.mk ⟨x, x_mem_M⟩) : Equiv.Perm (Fin 9)) = aPerm ∧
      (κ (QuotientGroup.mk ⟨y, y_mem_M⟩) : Equiv.Perm (Fin 9)) = bPerm) ∧
    (∀ m ∈ M, m ∈ Q ↔ ∀ g ∈ Q, ⁅m, g⁆ ∈ Subgroup.zpowers z) ∧
    Nat.card M = 92897280 ∧ CFSG.pCore 2 M = Q.subgroupOf M ∧
    Subgroup.centralizer (Q : Set J) ⊓ M = Subgroup.zpowers z :=
  ⟨exists_quotient_equiv, fun _ hm => mem_Q_iff_comm_mem_zpowers hm, card_M, pCore_M,
    centralizer_Q_inf_M⟩

end CFSG.Sporadic.Th.Max3
