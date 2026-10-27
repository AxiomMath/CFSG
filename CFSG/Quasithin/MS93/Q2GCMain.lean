module

public import CFSG.Quasithin.MS93.Q2GCEnd
public import CFSG.Quasithin.MS93.Q2GTv
public import CFSG.Quasithin.MS93.S5Q2UC
public import CFSG.Quasithin.MS93.S512NFF
public import CFSG.Quasithin.MS93.S5A55X
public import CFSG.Quasithin.MS93.S5A56

public section

namespace CFSG.Quasithin.MS93.Q2G

open CFSG.Quasithin CFSG.Quasithin.Fan86.Univ CFSG.Quasithin.MS93 CFSG.QuasithinUnique
  CFSG.Assembly.LowTwoRank
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped Matrix commutatorElement

section Group

variable {Γ : Type*} [Group Γ]

theorem commutator_sup_le_of {R K₁ K₂ N : Subgroup Γ}
    (hK₁ : K₁ ≤ Subgroup.normalizer (N : Set Γ)) (hK₂ : K₂ ≤ Subgroup.normalizer (N : Set Γ))
    (h₁ : ⁅R, K₁⁆ ≤ N) (h₂ : ⁅R, K₂⁆ ≤ N) : ⁅R, K₁ ⊔ K₂⁆ ≤ N := by
  let S : Subgroup Γ :=
    { carrier := {g | g ∈ Subgroup.normalizer (N : Set Γ) ∧ ∀ r ∈ R, ⁅r, g⁆ ∈ N}
      one_mem' := ⟨Subgroup.one_mem _, fun r _ => by simp [N.one_mem]⟩
      mul_mem' := by
        rintro g k ⟨hg, hg'⟩ ⟨hk, hk'⟩
        refine ⟨Subgroup.mul_mem _ hg hk, fun r hr => ?_⟩
        have e : ⁅r, g * k⁆ = ⁅r, g⁆ * (g * ⁅r, k⁆ * g⁻¹) := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact N.mul_mem (hg' r hr) ((Subgroup.mem_normalizer_iff.mp hg _).mp (hk' r hr))
      inv_mem' := by
        rintro g ⟨hg, hg'⟩
        refine ⟨Subgroup.inv_mem _ hg, fun r hr => ?_⟩
        have e : ⁅r, g⁻¹⁆ = g⁻¹ * ⁅r, g⁆⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) _).mp
          (N.inv_mem (hg' r hr)) }
  have hle : K₁ ⊔ K₂ ≤ S := sup_le
    (fun k hk => ⟨hK₁ hk, fun r hr => h₁ (Subgroup.commutator_mem_commutator hr hk)⟩)
    (fun k hk => ⟨hK₂ hk, fun r hr => h₂ (Subgroup.commutator_mem_commutator hr hk)⟩)
  rw [Subgroup.commutator_le]
  intro r hr x hx
  exact (hle hx).2 r hr

end Group

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

section Data

variable (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
include h hd

theorem le_of_imSp_le_of {E₁ E₂ : Subgroup G} (hE₁ : E₁ ≤ T) (hE₂ : E₂ ≤ T)
    (hQ : pCoreOf 2 M ≤ E₂) (hle : S5.imSp a E₁ ≤ S5.imSp a E₂) : E₁ ≤ E₂ := by
  intro e he
  have heM : e ∈ M := h.le (hE₁ he)
  obtain ⟨m, hm, hme⟩ := hle ⟨⟨e, heM⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
  have hmE : (m : G) ∈ E₂ := Subgroup.mem_subgroupOf.1 hm
  have hk : (m : G)⁻¹ * e ∈ T ⊓ S5.kerG a := by
    refine ⟨T.mul_mem (T.inv_mem (hE₂ hmE)) (hE₁ he), (S5.mem_kerG a).2 ⟨M.mul_mem
      (M.inv_mem m.2) heM, ?_⟩⟩
    have e1 : (⟨(m : G)⁻¹ * e, M.mul_mem (M.inv_mem m.2) heM⟩ : ↥M) = m⁻¹ * ⟨e, heM⟩ := rfl
    rw [e1, map_mul, map_inv, hme, inv_mul_cancel]
  rw [hd.inf_kerG h] at hk
  have := E₂.mul_mem hmE (hQ hk)
  rwa [mul_inv_cancel_left] at this

theorem imSp_sup_pCore_of {E : Subgroup G} (hEM : E ≤ M) :
    S5.imSp a (E ⊔ pCoreOf 2 M) = S5.imSp a E := by
  rw [S5.imSp, S5.imSp, Subgroup.subgroupOf_sup hEM (pCoreOf_le' M), Subgroup.map_sup]
  have hb : ((pCoreOf 2 M).subgroupOf M).map a = ⊥ := by
    refine eq_bot_iff.2 ?_
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨hmM, hm1⟩ :=
      (S5.mem_kerG a).1 (hd.pCoreOf_le_kerG h (Subgroup.mem_subgroupOf.1 hm))
    exact (Subgroup.mem_bot).2 hm1
  rw [hb, sup_bot_eq]

theorem relIndex_U_mul_of {E : Subgroup G} (hEM : E ≤ M) :
    (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) *
      Nat.card (MSP.fixSp (S5.imSp a E)) = 16 := by
  have hK : Nat.card F = 2 := by rw [hd.nat_card_eq, pow_one]
  obtain ⟨nv⟩ := hd.nonempty_natVec
  have h1 := Subgroup.relIndex_mul_card (Subgroup.centralizer (E : Set G)) (Uq M T L)
  rw [inf_comm, S5.card_uq_inf_centralizer h hd hEM, nv.card_Uq, MSP.card_V4, hK] at h1
  have hpos : 0 < Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := Nat.card_pos
  have : (Subgroup.centralizer (E : Set G)).relIndex (Uq M T L) *
      Nat.card (MSP.fixSp (S5.imSp a E)) * Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G))
      = 16 * Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) := by
    rw [mul_assoc, h1]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos this

theorem exists_l_of_mem_commutator {m : G} (hmT : m ∈ T)
    (hmc : a ⟨m, h.le hmT⟩ ∈ commutator (MSP.Sp4 F)) :
    ∃ l : ↥L, (∃ e : ℕ, l ^ 2 ^ e = 1) ∧ ∃ N : Subgroup G, N ≤ M ∧
      M ≤ Subgroup.normalizer (N : Set G) ∧ ¬ L ≤ N ∧ (l : G)⁻¹ * m ∈ N := by
  have hK : Nat.card F = 2 := by rw [hd.nat_card_eq, pow_one]
  have hmM : m ∈ M := h.le hmT
  have hLa := S5Q2.map_L_eq_commutator h hd
  rw [← hLa] at hmc
  obtain ⟨y, hy, hya⟩ := hmc
  let l₀ : ↥L := ⟨y, Subgroup.mem_subgroupOf.1 hy⟩
  let φ : ↥L →* ↥(StatedSp 2 F) := a.comp (Subgroup.inclusion h.L_le)
  have hφl₀ : φ l₀ = a ⟨m, hmM⟩ := hya
  obtain ⟨n, hn⟩ := h.isPGroup ⟨m, hmT⟩
  have hm2 : φ l₀ ^ 2 ^ n = 1 := by
    rw [hφl₀, ← map_pow]
    have : (⟨m, hmM⟩ : ↥M) ^ 2 ^ n = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hn)
    rw [this, map_one]
  obtain ⟨k, hk, f, hf⟩ := exists_pow_isTwoElt φ l₀ hm2
  refine ⟨l₀ ^ k, ⟨f, hf⟩, S5.kerG a, S5.kerG_le a, S5.le_normalizer_kerG a, fun hle => ?_, ?_⟩
  · obtain ⟨e, he, he1⟩ := Q2G.exists_ne_one hK (MSP.isLine_ln₀ (F := F))
    have he2 := he.2
    rw [← hLa] at he2
    obtain ⟨y', hy', rfl⟩ := he2
    obtain ⟨hy'M, hy'1⟩ := (S5.mem_kerG a).1 (hle (Subgroup.mem_subgroupOf.1 hy'))
    exact he1 hy'1
  · refine (S5.mem_kerG a).2 ⟨M.mul_mem (M.inv_mem (h.L_le (l₀ ^ k).2)) hmM, ?_⟩
    have e : (⟨((l₀ ^ k : ↥L) : G)⁻¹ * m, M.mul_mem (M.inv_mem (h.L_le (l₀ ^ k).2)) hmM⟩ : ↥M) =
        (⟨(l₀ ^ k : ↥L), h.L_le (l₀ ^ k).2⟩ : ↥M)⁻¹ * ⟨m, hmM⟩ := rfl
    rw [e, map_mul, map_inv]
    have : a ⟨(l₀ ^ k : ↥L), h.L_le (l₀ ^ k).2⟩ = φ (l₀ ^ k) := rfl
    rw [this, hk, hφl₀, inv_mul_cancel]

end Data

section Base

variable (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)

omit [Fintype F] in
theorem vIm_le_imSp_T {K : Subgroup (puAmalgam h.le).Universal}
    (hK : K ≤ Qv (puAmalgam h.le) (baseB _)) : S5.vIm h.le a K ≤ S5.imSp a T := by
  rintro _ ⟨m, hm, rfl⟩
  have hmT : (puAmalgam h.le).ofA m ∈ Qv _ (baseB (puAmalgam h.le)) := hK hm
  rw [puAmalgam.qv_baseB] at hmT
  obtain ⟨m', hm', he⟩ := hmT
  rw [(puAmalgam h.le).ofA_injective he] at hm'
  exact ⟨m, hm', rfl⟩

include hd in
theorem vIm_crit_eq (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G))
    {l₀ : Submodule F (MSP.V4 F)} (hl₀ : MSP.IsLine l₀) (hTl : S5.imSp a T ≤ MSP.stab l₀)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) α')
    (hgeo : geo _ (baseA _) α' 1 = baseB _) :
    S5.vIm h.le a (XM _ α') = MSP.qLine l₀ ⊓ commutator (MSP.Sp4 F) ∧
      S5.vIm h.le a (ZM _ α') = MSP.qLine l₀ ⊓ commutator (MSP.Sp4 F) := by
  have hK : Nat.card F = 2 := by rw [hd.nat_card_eq, pow_one]
  have : CharP F 2 := hd.charP
  obtain ⟨-, l, hl, hX, hZ⟩ := S5Q2.UC.shape_of_not_le h hd hC hc
  have hXβ : XM (puAmalgam h.le) α' ≤ Qv _ (baseB _) := by
    rw [← hgeo]
    exact xm_le_qv_geo_one _ h.hyp20 h.critDist_pos h.centHyp hc
  have hle := (vIm_le_imSp_T h hXβ).trans hTl
  rw [hX] at hle
  have hl0 : l₀ = l := eq_of_qLine_inf_commutator_le_stab hK hl hl₀ hle
  subst hl0
  exact ⟨hX, hZ.trans hX⟩

include hd in
theorem exists_pre_crit (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G))
    {l₀ : Submodule F (MSP.V4 F)} (hl₀ : MSP.IsLine l₀) (hTl : S5.imSp a T ≤ MSP.stab l₀)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) α')
    (hgeo : geo _ (baseA _) α' 1 = baseB _) :
    ∃ F₀ : Subgroup G, F₀ ≤ T ∧ imM h.le F₀ = XM (puAmalgam h.le) α' ∧
      S5.imSp a F₀ = MSP.qLine l₀ ⊓ commutator (MSP.Sp4 F) := by
  have hXβ : XM (puAmalgam h.le) α' ≤ imM h.le T := by
    rw [← puAmalgam.qv_baseB, ← hgeo]
    exact xm_le_qv_geo_one _ h.hyp20 h.critDist_pos h.centHyp hc
  obtain ⟨F₀, hF₀T, hF₀⟩ := exists_imM_eq_of_le h.le hXβ
  refine ⟨F₀, hF₀T, hF₀, ?_⟩
  rw [← S5.vIm_imM h, hF₀]
  exact (vIm_crit_eq h hd hC hl₀ hTl hc hgeo).1

include hd in
theorem sup_qv_eq_crit (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G))
    {l₀ : Submodule F (MSP.V4 F)} (hl₀ : MSP.IsLine l₀) (hTl : S5.imSp a T ≤ MSP.stab l₀)
    {α' δ' : Vtx (puAmalgam h.le)} (hcα : IsCritical _ (baseA _) α')
    (hcδ : IsCritical _ (baseA _) δ') (hgα : geo _ (baseA _) α' 1 = baseB _)
    (hgδ : geo _ (baseA _) δ' 1 = baseB _) :
    XM _ α' ⊔ Qv (puAmalgam h.le) (baseA _) = XM _ δ' ⊔ Qv (puAmalgam h.le) (baseA _) := by
  obtain ⟨F₁, hF₁T, hF₁, hi₁⟩ := exists_pre_crit h hd hC hl₀ hTl hcα hgα
  obtain ⟨F₂, hF₂T, hF₂, hi₂⟩ := exists_pre_crit h hd hC hl₀ hTl hcδ hgδ
  have e : ∀ {F₀ : Subgroup G}, F₀ ≤ T →
      imM h.le F₀ ⊔ Qv (puAmalgam h.le) (baseA _) = imM h.le (F₀ ⊔ pCoreOf 2 M) := by
    intro F₀ hF₀T
    rw [S5.qv_baseA_eq h, imM_sup h.le (hF₀T.trans h.le) (pCoreOf_le' M)]
  have hle : ∀ {E₁ E₂ : Subgroup G}, E₁ ≤ T → E₂ ≤ T → S5.imSp a E₁ = S5.imSp a E₂ →
      E₁ ⊔ pCoreOf 2 M ≤ E₂ ⊔ pCoreOf 2 M := by
    intro E₁ E₂ h₁ h₂ heq
    refine le_of_imSp_le_of h hd (sup_le h₁ h.pCore_le) (sup_le h₂ h.pCore_le) le_sup_right ?_
    rw [imSp_sup_pCore_of h hd (h₁.trans h.le), imSp_sup_pCore_of h hd (h₂.trans h.le), heq]
  rw [← hF₁, ← hF₂, e hF₁T, e hF₂T]
  congr 1
  exact le_antisymm (hle hF₁T hF₂T (hi₁.trans hi₂.symm)) (hle hF₂T hF₁T (hi₂.trans hi₁.symm))

include hd in
theorem comm_le_crit (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G))
    {l₀ : Submodule F (MSP.V4 F)} (hl₀ : MSP.IsLine l₀) (hTl : S5.imSp a T ≤ MSP.stab l₀)
    {γ₀ : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ₀ (baseA _))
    (hgeo : geo _ (baseA _) γ₀ 1 = baseB _) {Y : Subgroup (puAmalgam h.le).Universal}
    (hYβ : Y ≤ Qv (puAmalgam h.le) (baseB _))
    (hYc : Y ≤ Subgroup.centralizer (XM (puAmalgam h.le) γ₀ : Set (puAmalgam h.le).Universal)) :
    ⁅Y, S5.uSub h.le L (baseA _)⁆ ≤ ⁅XM (puAmalgam h.le) γ₀, S5.uSub h.le L (baseA _)⁆ := by
  have hK : Nat.card F = 2 := by rw [hd.nat_card_eq, pow_one]
  have : CharP F 2 := hd.charP
  have hc' : IsCritical _ (baseA _) γ₀ := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc
  obtain ⟨F₀, hF₀T, hF₀, hi⟩ := exists_pre_crit h hd hC hl₀ hTl hc' hgeo
  have hF₀M : F₀ ≤ M := hF₀T.trans h.le
  rw [puAmalgam.qv_baseB] at hYβ
  obtain ⟨Y₀, hY₀T, rfl⟩ := exists_imM_eq_of_le h.le hYβ
  have hY₀M : Y₀ ≤ M := hY₀T.trans h.le
  have hYF : ∀ y ∈ Y₀, ∀ f ∈ F₀, f * y = y * f := by
    intro y hy f hf
    rw [← hF₀] at hYc
    have h1 := Subgroup.mem_centralizer_iff.1
      (hYc ⟨⟨y, hY₀M hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩) _
      ⟨⟨f, hF₀M hf⟩, Subgroup.mem_subgroupOf.2 hf, rfl⟩
    have h2 : (⟨f, hF₀M hf⟩ : ↥M) * ⟨y, hY₀M hy⟩ = ⟨y, hY₀M hy⟩ * ⟨f, hF₀M hf⟩ :=
      (puAmalgam h.le).ofA_injective (by rw [map_mul, map_mul]; exact h1)
    exact congrArg Subtype.val h2
  have hT2 : IsPGroup 2 (S5.imSp a T) := S5.IsSp4Data.isPGroup_imSp (a := a) h
  have hl0 : l₀ ≠ ⊥ := by
    rintro rfl
    have := hl₀.1
    rw [finrank_bot] at this
    exact absurd this (by norm_num)
  obtain ⟨p, hpl, hp0, hpfix⟩ := MSP.exists_fixed_ne_zero hT2 hl0
    fun r hr w hw => MSP.mulVec_mem_of_mem_stab (hTl hr) hw
  have hYq : ∀ y (hy : y ∈ Y₀), a ⟨y, hY₀M hy⟩ ∈ MSP.qLine l₀ := by
    intro y hy
    have hyT : a ⟨y, hY₀M hy⟩ ∈ S5.imSp a T :=
      ⟨⟨y, hY₀M hy⟩, Subgroup.mem_subgroupOf.2 (hY₀T hy), rfl⟩
    refine mem_qLine_of_centralizer hK hl₀ (hTl hyT) hpl hp0 (hpfix _ hyT) ?_
    intro e he
    rw [← hi] at he
    obtain ⟨f, hf, rfl⟩ := he
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hYF y hy f (Subgroup.mem_subgroupOf.1 hf)).symm
  have hUY : ⁅Uq M T L, Y₀⁆ ≤ ⁅Uq M T L, F₀⁆ := by
    rw [Subgroup.commutator_le]
    intro u hu y hy
    exact comm_mem_of_mem_qLine h hd hl₀ hF₀M hi (y := ⟨y, hY₀M hy⟩) (hYq y hy) hu
  rw [S5.uSub_baseA h, ← hF₀, Subgroup.commutator_comm (imM h.le Y₀),
    Subgroup.commutator_comm (imM h.le F₀), ← imM_commutator h.le (Uq_le h.L_le) hY₀M,
    ← imM_commutator h.le (Uq_le h.L_le) hF₀M]
  exact imM_mono h.le hUY

end Base

theorem exists_conj_crit (h : PUHyp M T L) {γ γ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ γ') :
    ∃ g : (puAmalgam h.le).Universal, g • baseA (puAmalgam h.le) = γ' ∧
      g • baseB (puAmalgam h.le) = geo _ γ' γ 1 ∧ IsCritical _ (g⁻¹ • γ) (baseA _) ∧
      geo _ (baseA _) (g⁻¹ • γ) 1 = baseB _ := by
  have hc' := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc
  obtain ⟨g, hg1, hg2⟩ := exists_smul_edge_of_isMVtx _ (isMVtx_baseA _) (adj_baseA_baseB _)
    hc'.1 (adj_geo_one_of_isCritical _ h.critDist_pos hc')
  refine ⟨g, hg1, hg2, ?_, ?_⟩
  · rw [← isCritical_smul _ g, smul_inv_smul, hg1]
    exact hc
  · have h1 := geo_smul _ g (baseA (puAmalgam h.le)) (g⁻¹ • γ) 1
    rw [hg1, smul_inv_smul, ← hg2] at h1
    exact (MulAction.injective g h1).symm

section All

variable (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
include hd

theorem comm_le_crit_all (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G))
    {l₀ : Submodule F (MSP.V4 F)} (hl₀ : MSP.IsLine l₀) (hTl : S5.imSp a T ≤ MSP.stab l₀)
    {γ γ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ γ') {Y : Subgroup (puAmalgam h.le).Universal}
    (hY : Y ≤ Qv _ (geo _ γ' γ 1))
    (hYc : Y ≤ Subgroup.centralizer (XM (puAmalgam h.le) γ : Set (puAmalgam h.le).Universal)) :
    ⁅Y, S5.uSub h.le L γ'⁆ ≤ ⁅XM (puAmalgam h.le) γ, S5.uSub h.le L γ'⁆ := by
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  obtain ⟨g, hg1, hg2, hc₀, hgeo₀⟩ := exists_conj_crit h hc
  set Y' := Y.map (MulAut.conj g⁻¹).toMonoidHom with hY'def
  have hYY : Y = Y'.map (MulAut.conj g).toMonoidHom := (map_conj_map_conj_inv Y g).symm
  have hY' : Y' ≤ Qv _ (baseB _) := by
    rw [← hg2, qv_smul] at hY
    rw [hY'def, map_conj_le_iff, inv_inv]
    exact hY
  have hY'c : Y' ≤ Subgroup.centralizer (XM (puAmalgam h.le) (g⁻¹ • γ) :
      Set (puAmalgam h.le).Universal) := by
    rw [xm_smul, ← centralizer_map_mulEquiv]
    exact Subgroup.map_mono hYc
  have key := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom)
    (comm_le_crit h hd hC hl₀ hTl hc₀ hgeo₀ hY' hY'c)
  rw [Subgroup.map_commutator, Subgroup.map_commutator, ← hYY, ← S5B.uSub_smul h.le hLn, hg1,
    ← xm_smul, smul_inv_smul] at key
  exact key

theorem critUniq_of (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G))
    {l₀ : Submodule F (MSP.V4 F)} (hl₀ : MSP.IsLine l₀) (hTl : S5.imSp a T ≤ MSP.stab l₀) :
    CritUniq (puAmalgam h.le) := by
  intro γ γ' δ' hc hcd hgeo
  have hb0 := h.critDist_pos
  obtain ⟨g, hg1, hg2⟩ := exists_smul_edge_of_isMVtx _ (isMVtx_baseA _) (adj_baseA_baseB _)
    hc.1 (adj_geo_one_of_isCritical _ hb0 hc)
  have hcr : ∀ {δ : Vtx (puAmalgam h.le)}, IsCritical _ γ δ → IsCritical _ (baseA _) (g⁻¹ • δ) :=
    fun {δ} hδ => by
      rw [← isCritical_smul _ g, smul_inv_smul, hg1]
      exact hδ
  have hgr : ∀ {δ : Vtx (puAmalgam h.le)}, geo _ γ δ 1 = geo _ γ γ' 1 →
      geo _ (baseA _) (g⁻¹ • δ) 1 = baseB _ := fun {δ} hδ => by
    have h1 := geo_smul _ g (baseA (puAmalgam h.le)) (g⁻¹ • δ) 1
    rw [hg1, smul_inv_smul, hδ, ← hg2] at h1
    exact (MulAction.injective g h1).symm
  have key := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom)
    (sup_qv_eq_crit h hd hC hl₀ hTl (hcr hc) (hcr hcd) (hgr rfl) (hgr hgeo))
  rw [Subgroup.map_sup, Subgroup.map_sup, ← xm_smul, ← xm_smul, ← qv_smul, smul_inv_smul,
    smul_inv_smul, hg1] at key
  exact key

theorem zc23At_base (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G))
    {l₀ : Submodule F (MSP.V4 F)} (hl₀ : MSP.IsLine l₀) (hTl : S5.imSp a T ≤ MSP.stab l₀)
    {γ₀ : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ₀ (baseA _))
    (hgeo : geo _ (baseA _) γ₀ 1 = baseB _) :
    Zc23At _ γ₀ (baseA _) (S5.uSub h.le L (baseA _)) := by
  have hK : Nat.card F = 2 := by rw [hd.nat_card_eq, pow_one]
  have hUX : S5.uSub h.le L (baseA _) ≤ XM (puAmalgam h.le) (baseA _) := by
    rw [S5.uSub_baseA h, S5B.xm_baseA_eq h]
    exact imM_mono h.le h.Uq_le_Xq
  refine ⟨hUX, fun hle => ?_, fun Y hY hYe => ?_⟩
  ·
    have hc' : IsCritical _ (baseA _) γ₀ := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc
    obtain ⟨F₀, hF₀T, hF₀, hi⟩ := exists_pre_crit h hd hC hl₀ hTl hc' hgeo
    have hF₀M : F₀ ≤ M := hF₀T.trans h.le
    have h1 : S5.uSub h.le L (baseA _) ≤
        Subgroup.centralizer (XM (puAmalgam h.le) γ₀ : Set (puAmalgam h.le).Universal) :=
      hle.trans (qv_le_centralizer_xm _ γ₀)
    rw [S5.uSub_baseA h, ← hF₀] at h1
    have hUF : ∀ u ∈ Uq M T L, ∀ f ∈ F₀, f * u = u * f := by
      intro u hu f hf
      have h2 := Subgroup.mem_centralizer_iff.1
        (h1 ⟨⟨u, Uq_le h.L_le hu⟩, Subgroup.mem_subgroupOf.2 hu, rfl⟩) _
        ⟨⟨f, hF₀M hf⟩, Subgroup.mem_subgroupOf.2 hf, rfl⟩
      have h3 : (⟨f, hF₀M hf⟩ : ↥M) * ⟨u, Uq_le h.L_le hu⟩ = ⟨u, Uq_le h.L_le hu⟩ * ⟨f, hF₀M hf⟩ :=
        (puAmalgam h.le).ofA_injective (by rw [map_mul, map_mul]; exact h2)
      exact congrArg Subtype.val h3
    obtain ⟨nv⟩ := hd.nonempty_natVec
    have htop : MSP.fixSp (MSP.qLine l₀ ⊓ commutator (MSP.Sp4 F)) = ⊤ := by
      refine eq_top_iff.2 fun v _ => ?_
      obtain ⟨u, hu⟩ := nv.surj (Multiplicative.ofAdd v)
      have hv : nv.vec u = v := by
        rw [S5.NatVec.vec, hu]
        rfl
      rw [← hv, ← hi]
      rintro _ ⟨f, hf, rfl⟩
      exact nv.mat_mulVec_vec_of_commute f u (hUF u u.2 f (Subgroup.mem_subgroupOf.1 hf))
    have hbot := MSP.fixSp_eq_top_iff.1 htop
    obtain ⟨e, he, he1⟩ := exists_ne_one hK hl₀
    rw [hbot] at he
    exact he1 (Subgroup.mem_bot.1 he)
  ·
    have hYc : Y ≤ Subgroup.centralizer (XM (puAmalgam h.le) γ₀ :
        Set (puAmalgam h.le).Universal) := by
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have := hYe.1.1.1 ⟨x, Subgroup.mem_sup_right hx⟩ ⟨y, Subgroup.mem_sup_left hy⟩
      exact congrArg Subtype.val this
    rw [hgeo] at hY
    refine le_sup_of_le_left ((comm_le_crit h hd hC hl₀ hTl hc hgeo hY hYc).trans ?_)
    rw [Subgroup.commutator_comm (XM (puAmalgam h.le) γ₀),
      Subgroup.commutator_comm (XM (puAmalgam h.le) γ₀)]
    exact Subgroup.commutator_mono hUX le_rfl

theorem zc23At_of (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G))
    {l₀ : Submodule F (MSP.V4 F)} (hl₀ : MSP.IsLine l₀) (hTl : S5.imSp a T ≤ MSP.stab l₀)
    {γ γ' : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ γ') : ∃ Z, Zc23At _ γ γ' Z := by
  obtain ⟨g, hg1, -, hc₀, hgeo₀⟩ := exists_conj_crit h hc
  have key := zc23At_smul _ (zc23At_base h hd hC hl₀ hTl hc₀ hgeo₀) g
  rw [smul_inv_smul, hg1] at key
  exact ⟨_, key⟩

theorem commutator_le_centralizer_vv (h52 : S52) (hmin : PUMin M T L)
    (hb : critDist (puAmalgam h.le) = 4) (hXU : Xq M = Uq M T L ⊔ Zq M L)
    (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G))
    {l₀ : Submodule F (MSP.V4 F)} (hl₀ : MSP.IsLine l₀) (hTl : S5.imSp a T ≤ MSP.stab l₀)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) α') :
    ⁅Vv (puAmalgam h.le) (baseA _) ⊓ Qv _ (geo _ (baseA _) α' 2), XM _ α'⁆ ≤
      Subgroup.centralizer (Vv (puAmalgam h.le) (baseA _) : Set (puAmalgam h.le).Universal) := by
  have h20 := h.hyp20
  have hb0 := h.critDist_pos
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ h20
  have hd4 : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb
  have hVQ : Vv (puAmalgam h.le) (baseA _) ≤ Qv _ (baseA _) := S38E.vv_le_qv _ (by omega) hα
  set N := Subgroup.centralizer (Vv (puAmalgam h.le) (baseA _) : Set (puAmalgam h.le).Universal)
  set R := Vv (puAmalgam h.le) (baseA _) ⊓ Qv _ (geo _ (baseA _) α' 2)
  have hstN : stab (puAmalgam h.le) (baseA _) ≤ Subgroup.normalizer (N : Set _) :=
    le_normalizer_centralizer (stab_le_normalizer_of_smul _ (F := fun ρ => Vi _ ρ 2)
      (fun g ρ => vi_smul _ g ρ 2) (baseA _))
  have hUst : S5.uSub h.le L α' ≤ stab (puAmalgam h.le) (baseA _) := by
    have hUZ : S5.uSub h.le L α' ≤ ZM _ α' :=
      commutator_le_left_of_le_normalizer ((puTrans_le_stab h.le L α').trans
        (stab_le_normalizer_zm _ _))
    have hdβ : (puAmalgam h.le).treeGraph.dist α' (geo _ (baseA _) α' 1) <
        critDist (puAmalgam h.le) := by
      rw [tdist_comm, dist_geo_right _ (by omega), hd4]
      omega
    exact hUZ.trans ((zm_le_qv_of_dist_lt _ hα' hdβ).trans (qv_le_stab_of_adj _
      (adj_geo_one_of_isCritical _ hb0 hc).symm))
  have hX : XM _ α' ≤ S5.uSub h.le L α' ⊔ Qv (puAmalgam h.le) (baseA _) := by
    rw [S5Q2.xm_eq_uSub_sup_centralizer h hXU hα']
    refine sup_le_sup_left ?_ _
    refine S5Q2.UC.le_qv_of_dist_le h hd hC hα' hα ?_
    rw [SimpleGraph.dist_comm, hc.2.1]
  have h₁ : ⁅R, S5.uSub h.le L α'⁆ ≤ N := by
    have hRY : R ≤ Qv _ (geo _ α' (baseA _) 1) := by
      have hμ : IsMVtx _ (geo _ (baseA _) α' 2) := isMVtx_geo_two _ h20 hb0 hc
      have hν : geo _ α' (baseA _) 1 = geo _ (baseA _) α' 3 := by
        have := geo_symm _ (u := baseA (puAmalgam h.le)) (w := α') (i := 3) (by omega)
        rwa [hd4] at this
      rw [hν]
      exact inf_le_right.trans (qv_le_qv _ h20 hμ (adj_geo _ (i := 2) (by omega)))
    have hRc : R ≤ Subgroup.centralizer (XM (puAmalgam h.le) (baseA _) :
        Set (puAmalgam h.le).Universal) :=
      inf_le_left.trans (hVQ.trans (qv_le_centralizer_xm _ _))
    refine (comm_le_crit_all h hd hC hl₀ hTl hc hRY hRc).trans
      ((commutator_le_left_of_le_normalizer (hUst.trans (stab_le_normalizer_xm _ _))).trans ?_)
    exact (xm_le_centralizer _ _).trans (Subgroup.centralizer_le hVQ)
  have h₂ : ⁅R, Qv (puAmalgam h.le) (baseA _)⁆ ≤ N := by
    have h3 := (h52 G M T L h hmin (by omega) 1 F _ _ a hd α' hc).2.1
    exact (Subgroup.commutator_mono inf_le_left le_rfl).trans (h3.trans inf_le_right)
  exact (Subgroup.commutator_mono le_rfl hX).trans
    (commutator_sup_le_of (hUst.trans hstN) ((qv_le_stab _ _).trans hstN) h₁ h₂)

end All

section End

variable (h : PUHyp M T L) (hd : S5.IsSp4Data M T L 1 F a)
include hd

theorem relIndex_crit_eq_four (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G))
    {l₀ : Submodule F (MSP.V4 F)} (hl₀ : MSP.IsLine l₀) (hTl : S5.imSp a T ≤ MSP.stab l₀)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) α')
    (hgeo : geo _ (baseA _) α' 1 = baseB _) :
    (Qv (puAmalgam h.le) (baseA _)).relIndex (XM _ α') = 4 := by
  have hK : Nat.card F = 2 := by rw [hd.nat_card_eq, pow_one]
  have hXβ : XM (puAmalgam h.le) α' ≤ Qv _ (baseB _) := by
    rw [← hgeo]
    exact xm_le_qv_geo_one _ h.hyp20 h.critDist_pos h.centHyp hc
  have hX2 : IsPGroup 2 ↥(XM (puAmalgam h.le) α') :=
    (isPGroup_qv _ h.hyp20 (PU.not_isMVtx_baseB _)).to_le hXβ
  rw [← S5.card_vIm h hd (hXβ.trans (qv_le_stab_of_adj _ (adj_baseA_baseB _).symm)) hX2,
    (vIm_crit_eq h hd hC hl₀ hTl hc hgeo).1]
  exact MSP.card_qLine_inf_commutator hK hl₀

theorem exists_l_crit (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G))
    {l₀ : Submodule F (MSP.V4 F)} (hl₀ : MSP.IsLine l₀) (hTl : S5.imSp a T ≤ MSP.stab l₀)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) α')
    (hgeo : geo _ (baseA _) α' 1 = baseB _) {E : Subgroup G} (hET : E ≤ T)
    (hEX : imM h.le E = XM (puAmalgam h.le) α') {m : G} (hm : m ∈ E) :
    ∃ l : ↥L, (∃ e : ℕ, l ^ 2 ^ e = 1) ∧ ∃ N : Subgroup G, N ≤ M ∧
      M ≤ Subgroup.normalizer (N : Set G) ∧ ¬ L ≤ N ∧ (l : G)⁻¹ * m ∈ N := by
  refine exists_l_of_mem_commutator h hd (hET hm) ?_
  have hmem : a ⟨m, h.le (hET hm)⟩ ∈ S5.vIm h.le a (XM (puAmalgam h.le) α') := by
    rw [← hEX, S5.vIm_imM h]
    exact ⟨⟨m, h.le (hET hm)⟩, Subgroup.mem_subgroupOf.2 hm, rfl⟩
  rw [(vIm_crit_eq h hd hC hl₀ hTl hc hgeo).1] at hmem
  exact hmem.2

theorem four_le_relIndex_crit (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G))
    {l₀ : Submodule F (MSP.V4 F)} (hl₀ : MSP.IsLine l₀) (hTl : S5.imSp a T ≤ MSP.stab l₀)
    {γ : Vtx (puAmalgam h.le)} (hc : IsCritical _ γ (baseA _))
    (hγB : (puAmalgam h.le).treeGraph.dist γ (baseB _) < critDist (puAmalgam h.le))
    {t : ↥M} (htT : (t : G) ∈ T) (htZ : (puAmalgam h.le).ofA t ∈ ZM (puAmalgam h.le) γ)
    (htQ : (puAmalgam h.le).ofA t ∉ Qv (puAmalgam h.le) (baseA _)) :
    4 ≤ (Subgroup.centralizer ((Subgroup.zpowers (t : G) : Subgroup G) : Set G)).relIndex
      (Uq M T L) := by
  have hK : Nat.card F = 2 := by rw [hd.nat_card_eq, pow_one]
  have : CharP F 2 := hd.charP
  have hc' : IsCritical _ (baseA _) γ := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc
  have hgeo : geo _ (baseA _) γ 1 = baseB _ := by
    symm
    refine eq_geo_one _ (adj_baseA_baseB _) ?_
    have h1 := dist_triangle _ (baseA (puAmalgam h.le)) (baseB _) γ
    rw [dist_eq_one_of_adj _ (adj_baseA_baseB _), hc'.2.1] at h1
    have h2 := tdist_comm _ γ (baseB (puAmalgam h.le))
    rw [hc'.2.1]
    omega
  have hZ := (vIm_crit_eq h hd hC hl₀ hTl hc' hgeo).2
  have hat : a t ∈ MSP.qLine l₀ ⊓ commutator (MSP.Sp4 F) := by
    rw [← hZ]
    exact ⟨t, htZ, rfl⟩
  have hat1 : a t ≠ 1 := by
    intro h1
    apply htQ
    have hk : (t : G) ∈ T ⊓ S5.kerG a := ⟨htT, (S5.mem_kerG a).2 ⟨t.2, h1⟩⟩
    rw [hd.inf_kerG h] at hk
    rw [S5.qv_baseA_eq h]
    exact ⟨t, Subgroup.mem_subgroupOf.2 hk, rfl⟩
  have hEM : Subgroup.zpowers (t : G) ≤ M := (Subgroup.zpowers_le).2 t.2
  have hU := relIndex_U_mul_of h hd hEM
  have hfix : MSP.fixSp (S5.imSp a (Subgroup.zpowers (t : G))) = l₀ := by
    refine le_antisymm ?_ ?_
    · calc MSP.fixSp (S5.imSp a (Subgroup.zpowers (t : G)))
          ≤ MSP.fixSp (Subgroup.zpowers (a t)) := by
            refine MSP.fixSp_antitone ((Subgroup.zpowers_le).2 ?_)
            exact ⟨t, Subgroup.mem_subgroupOf.2 (Subgroup.mem_zpowers _), rfl⟩
        _ = l₀ := fixSp_zpowers_eq_of_mem hK hl₀ hat hat1
    · calc l₀ = MSP.fixSp (MSP.qLine l₀ ⊓ commutator (MSP.Sp4 F)) :=
          (fixSp_qLine_inf_commutator hK hl₀).symm
        _ ≤ MSP.fixSp (S5.imSp a (Subgroup.zpowers (t : G))) := by
          refine MSP.fixSp_antitone ?_
          rintro _ ⟨m, hm, rfl⟩
          obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_subgroupOf.1 hm)
          have e : m = t ^ n := Subtype.ext (by rw [Subgroup.coe_zpow, hn])
          rw [e, map_zpow]
          exact Subgroup.zpow_mem _ hat n
  rw [hfix, Module.natCard_eq_pow_finrank (K := F), hl₀.1, hK] at hU
  omega

end End

theorem false_of_not_le (h14 : MS14AS) (hSQ : SQTKQuot)
    (hT : S32.TypeFacts) (h54 : S54) (h52 : S52) (h : PUHyp M T L) (hmin : PUMin M T L)
    (hb : 2 < critDist (puAmalgam h.le)) (hd : S5.IsSp4Data M T L 1 F a)
    (hXU : Xq M = Uq M T L ⊔ Zq M L) (hC : ¬ Zq M L ≤ Subgroup.centralizer (M : Set G)) :
    False := by
  obtain ⟨-, ⟨l₀, hl₀, hTl', -⟩, -⟩ := (h54 G M T L h hmin hb 1 F _ _ a hd).resolve_right
    fun ⟨_, _, p, hp, hTq⟩ => S5Q2.X52.vIm_qv_baseB_ne_qPoint h hd hC hp hTq
  have hTl : S5.imSp a T ≤ MSP.stab l₀ := by
    rintro _ ⟨m, hm, rfl⟩
    have hmT : (puAmalgam h.le).ofA m ∈ Qv _ (baseB (puAmalgam h.le)) := by
      rw [puAmalgam.qv_baseB]
      exact ⟨m, hm, rfl⟩
    obtain ⟨m', hm', he⟩ := hTl' hmT
    rw [(puAmalgam h.le).ofA_injective he] at hm'
    exact hm'
  have h360 : Nat.card (S32.Lstar L) = 360 := by
    rcases S512N.card_lstar_of_data h hd with ⟨-, h1⟩ | ⟨h1, -⟩
    · exact h1
    · omega
  exact false_of_critData h14 hSQ hT h hb h360 (critUniq_of h hd hC hl₀ hTl)
    (fun γ γ' hc => zc23At_of h hd hC hl₀ hTl hc)
    (fun hb4 α' hc _ => commutator_le_centralizer_vv h hd h52 hmin hb4 hXU hC hl₀ hTl hc)
    (fun α' hc hgeo => relIndex_crit_eq_four h hd hC hl₀ hTl hc hgeo)
    (fun α' hc hgeo E hET hEX m hm => exists_l_crit h hd hC hl₀ hTl hc hgeo hET hEX hm)
    (fun γ hc hγB t htT htZ htQ => four_le_relIndex_crit h hd hC hl₀ hTl hc hγB htT htZ htQ)

theorem q2CentUC_of (h14 : MS14AS) (hSQ : SQTKQuot)
    (hT : S32.TypeFacts) (h54 : S54) (h52 : S52) : S5Q2.Q2CentUC := by
  intro G _ _ M T L h hmin hb F _ _ a hd hXU _ _
  by_contra hC
  exact false_of_not_le h14 hSQ hT h54 h52 h hmin hb hd hXU hC

end CFSG.Quasithin.MS93.Q2G
