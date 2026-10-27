module

public import CFSG.Quasithin.MS93.S33SpLin
public import CFSG.Quasithin.MS93.MSPBridge
public import CFSG.Quasithin.MS93.MSPOff

public section

namespace CFSG.Quasithin.MS93.S33

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

section Image

variable {F : Type} [Field F] [Fintype F] {A : Subgroup G} {αA : ↥A →* ↥(StatedSp 2 F)}

omit [Fintype F] in
theorem image_eq_one_iff (h : PUHyp M T L) (hAM : A ≤ M)
    (c : MSP.NatCoord A (Uq M T L) (Uq M T L ⊓ Zq M L) αA) (a : ↥A) :
    αA a = 1 ↔ (a : G) ∈ actTriv h := by
  have haV : (a : G) ∈ Subgroup.normalizer (Uq M T L : Set G) :=
    le_normalizer_Uq h.le_normalizer (hAM a.2)
  constructor
  · intro h1
    refine ⟨hAM a.2, fun u hu => ?_⟩
    have hconj : (a : G) * u * (a : G)⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.1 haV u).1 hu
    have hcomm := c.vec_commutator a ⟨u, hu⟩ hconj
    rw [h1] at hcomm
    simp only [MSP.mat, OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec, sub_self] at hcomm
    have hmem := (c.vec_eq_zero_iff _).1 hcomm
    simp only at hmem
    have hC : ⁅(a : G), u⁆ ∈ Uq M T L ⊓ Zq M L := by
      rw [commutatorElement_def]
      exact hmem
    rw [h.Uq_inf_Zq] at hC
    have : ⁅u, (a : G)⁆ = ⁅(a : G), u⁆⁻¹ := (commutatorElement_inv _ _).symm
    rw [this]
    exact inv_mem hC.2
  · intro ha
    refine MSP.ext_mulVec fun w => ?_
    obtain ⟨u, rfl⟩ := c.exists_vec_eq w
    have hconj : (a : G) * u * (a : G)⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.1 haV u).1 u.2
    have hcomm := c.vec_commutator a u hconj
    have hC : (a : G) * u * (a : G)⁻¹ * (u : G)⁻¹ ∈ Uq M T L ⊓ Zq M L := by
      rw [h.Uq_inf_Zq]
      have h1 := ha.2 u u.2
      have e : (a : G) * u * (a : G)⁻¹ * (u : G)⁻¹ = ⁅(u : G), (a : G)⁆⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [Subgroup.mem_inf, e]
      exact ⟨e ▸ mul_mem hconj (inv_mem u.2), inv_mem h1⟩
    rw [(c.vec_eq_zero_iff _).2 hC, eq_comm, sub_eq_zero] at hcomm
    simp only [MSP.mat, OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec]
    exact hcomm

omit [Fintype F] in
theorem card_image_eq_relIndex (h : PUHyp M T L) (hAM : A ≤ M)
    (c : MSP.NatCoord A (Uq M T L) (Uq M T L ⊓ Zq M L) αA) {K : Subgroup G} (hKA : K ≤ A) :
    Nat.card ((K.subgroupOf A).map αA) = (actTriv h).relIndex K := by
  let φ : ↥K →* ↥(StatedSp 2 F) := αA.comp (Subgroup.inclusion hKA)
  have hrange : φ.range = (K.subgroupOf A).map αA := by
    rw [MonoidHom.range_comp]
    congr 1
    ext x
    constructor
    · rintro ⟨k, rfl⟩
      exact Subgroup.mem_subgroupOf.2 k.2
    · intro hx
      exact ⟨⟨x, Subgroup.mem_subgroupOf.1 hx⟩, rfl⟩
  have hker : φ.ker = (actTriv h).subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact image_eq_one_iff h hAM c (Subgroup.inclusion hKA k)
  rw [← hrange, ← Subgroup.index_ker, hker]
  rfl

theorem card_le_fixSp_mul (h : PUHyp M T L) (hAM : A ≤ M)
    (c : MSP.NatCoord A (Uq M T L) (Uq M T L ⊓ Zq M L) αA) (K : Subgroup G) :
    Nat.card (MSP.V4 F) ≤ Nat.card (MSP.fixSp ((K.subgroupOf A).map αA)) *
      (Subgroup.centralizer (K : Set G)).relIndex (Uq M T L) :=
  c.card_le_relIndex (hAM.trans (le_normalizer_Uq h.le_normalizer)) K

end Image

theorem relIndex_qv_zm_eq (h : PUHyp M T L) {γ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) γ (baseA _)) :
    (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ γ) =
      (actTriv h).relIndex (pre h.le (ZM _ γ)) := by
  obtain ⟨-, -, -, hEQ, hEim⟩ := pre_zm_props h hc
  have e1 : (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ γ) =
      (pCoreOf 2 M).relIndex (pre h.le (ZM _ γ)) := by
    conv_lhs => rw [← hEim]
    rw [puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le,
      relIndex_imM h.le (pre_le h.le _)]
  rw [e1, ← Subgroup.inf_relIndex_right, ← Subgroup.inf_relIndex_right (H := actTriv h)]
  congr 1
  ext x
  constructor
  · rintro ⟨hxQ, hxE⟩
    refine ⟨⟨pCoreOf_le' M hxQ, fun u hu => ?_⟩, hxE⟩
    have hc := Subgroup.mem_centralizer_iff.mp (h.pCoreOf_le_centralizer_Z0q hxQ) u
      (Uq_le_Z0q h.L_le hu)
    rw [commutatorElement_eq_one_iff_mul_comm.2 hc]
    exact one_mem _
  · rintro ⟨hxA, hxE⟩
    exact ⟨hEQ x hxE (centralizer_of_actTriv h hxA), hxE⟩

theorem relIndex_centralizer_le (h : PUHyp M T L) {δ : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) (baseA _) δ) :
    (Subgroup.centralizer (pre h.le (ZM _ δ) : Set G)).relIndex (Uq M T L) ≤
      (Qv _ δ).relIndex (ZM (puAmalgam h.le) (baseA _)) := by
  have h20 := h.hyp20
  have hcδ := ms22_iii _ h20 h.critDist_pos h.centHyp hc
  have hle : pre h.le (Qv _ δ) ≤ Subgroup.centralizer (pre h.le (ZM _ δ) : Set G) := by
    intro x hx
    obtain ⟨x', hx', rfl⟩ := (mem_pre_iff' h.le).1 hx
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    obtain ⟨y', hy', rfl⟩ := (mem_pre_iff' h.le).1 hy
    have h1 := Subgroup.mem_centralizer_iff.mp (zm_le_centralizer_qv _ h20 hcδ.1 hy') _ hx'
    rw [← map_mul, ← map_mul] at h1
    have h2 := congrArg Subtype.val ((puAmalgam h.le).ofA_injective h1)
    simp only [Subgroup.coe_mul] at h2
    exact h2.symm
  calc (Subgroup.centralizer (pre h.le (ZM _ δ) : Set G)).relIndex (Uq M T L)
      ≤ (pre h.le (Qv _ δ)).relIndex (Uq M T L) :=
        Subgroup.relIndex_le_of_le_left hle Subgroup.index_ne_zero_of_finite
    _ ≤ (pre h.le (Qv _ δ)).relIndex (Z0q M T) :=
        Subgroup.relIndex_le_of_le_right (Uq_le_Z0q h.L_le) Subgroup.index_ne_zero_of_finite
    _ = (Qv _ δ).relIndex (ZM (puAmalgam h.le) (baseA _)) := by
        rw [relIndex_pre h.le _ (Z0q_le M T), ← puAmalgam.zm_baseA]

theorem exists_conj_vertex (h : PUHyp M T L) {α' : Vtx (puAmalgam h.le)}
    (hc : IsCritical (puAmalgam h.le) (baseA _) α') :
    ∃ μ : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) μ (baseA _) ∧
      (Qv _ α').relIndex (ZM (puAmalgam h.le) (baseA _)) =
        (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ μ) ∧
      (Qv _ (baseA (puAmalgam h.le))).relIndex (ZM _ α') =
        (Qv _ μ).relIndex (ZM (puAmalgam h.le) (baseA _)) := by
  obtain ⟨k, hkα, -, hcμ, -⟩ := exists_conj_of_isCritical _ h.hyp20 h.critDist_pos hc
  refine ⟨k⁻¹ • baseA _, hcμ, ?_, ?_⟩
  · rw [← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj k⁻¹).toMonoidHom) _ _
      (MulAut.conj k⁻¹).injective, ← qv_smul, ← zm_smul, ← hkα, inv_smul_smul]
  · rw [← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj k⁻¹).toMonoidHom) _ _
      (MulAut.conj k⁻¹).injective, ← qv_smul, ← zm_smul, ← hkα, inv_smul_smul]

section Shapes

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

omit [Fintype F] [CharP F 2] in
theorem finrank_fixSp_le_three {Γ : Subgroup (MSP.Sp4 F)} (hΓ : Γ ≠ ⊥) :
    Module.finrank F (MSP.fixSp Γ) ≤ 3 := by
  have hne : MSP.fixSp Γ ≠ ⊤ := by
    intro htop
    apply hΓ
    refine eq_bot_iff.2 fun g hg => ?_
    rw [Subgroup.mem_bot]
    refine MSP.ext_mulVec fun w => ?_
    have hw : w ∈ MSP.fixSp Γ := htop ▸ Submodule.mem_top
    have := hw g hg
    simpa [MSP.mat] using this
  have h4 := Submodule.finrank_lt hne
  have hV : Module.finrank F (MSP.V4 F) = 4 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  omega

omit [CharP F 2] in
theorem sp4_shapes {Γ Γ' : Subgroup (MSP.Sp4 F)} (hΓ : Γ ≠ ⊥) (hΓ' : Γ' ≠ ⊥)
    (h1 : Nat.card (MSP.V4 F) ≤ Nat.card (MSP.fixSp Γ') * Nat.card Γ)
    (h2 : Nat.card (MSP.V4 F) ≤ Nat.card (MSP.fixSp Γ) * Nat.card Γ') :
    ((∃ p : Submodule F (MSP.V4 F), MSP.IsPoint p ∧ Γ = MSP.xPoint p) ∧
        (∃ p' : Submodule F (MSP.V4 F), MSP.IsPoint p' ∧ Γ' = MSP.xPoint p')) ∨
      (Fintype.card F ^ 2 ≤ Nat.card Γ ∧ Fintype.card F ^ 2 ≤ Nat.card Γ' ∧
        Module.finrank F (MSP.fixSp Γ) ≤ 2 ∧ Module.finrank F (MSP.fixSp Γ') ≤ 2) := by
  set q := Fintype.card F with hq
  have hq1 : 1 < q := Fintype.one_lt_card
  have hqn : Nat.card F = q := Nat.card_eq_fintype_card
  rw [MSP.card_V4, hqn] at h1 h2
  rw [MSP.card_fixSp, hqn] at h1 h2
  set d := Module.finrank F (MSP.fixSp Γ)
  set d' := Module.finrank F (MSP.fixSp Γ')
  have hd := finrank_fixSp_le_three hΓ
  have hd' := finrank_fixSp_le_three hΓ'
  have hpt : ∀ {Δ : Subgroup (MSP.Sp4 F)}, Module.finrank F (MSP.fixSp Δ) = 3 →
      Nat.card Δ ≤ q := by
    intro Δ h3
    obtain ⟨p, hp, -, hle⟩ := MSP.exists_point_of_finrank_fixSp_three h3
    calc Nat.card Δ ≤ Nat.card (MSP.xPoint p) := Subgroup.card_le_of_le hle
      _ = q := by rw [MSP.card_xPoint hp, hqn]
  have pow_le : ∀ {e x : ℕ}, e ≤ 3 → q ^ 4 ≤ q ^ e * x → q ^ (4 - e) ≤ x := by
    intro e x he hx
    have : q ^ 4 = q ^ e * q ^ (4 - e) := by rw [← pow_add]; congr 1; omega
    rw [this] at hx
    exact Nat.le_of_mul_le_mul_left hx (pow_pos (by omega) e)
  rcases Nat.lt_or_ge d 3 with hd3 | hd3
  ·
    have hΓ'q : q ^ 2 ≤ Nat.card Γ' := by
      have := pow_le (by omega : d ≤ 3) h2
      calc q ^ 2 ≤ q ^ (4 - d) := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ _ := this
    have hd'3 : d' ≤ 2 := by
      by_contra hd'
      have h3 : d' = 3 := by omega
      have hA := hpt h3
      have hC : q < q ^ 2 := by nlinarith
      exact absurd (hC.trans_le (hΓ'q.trans hA)) (lt_irrefl q)
    have hΓq : q ^ 2 ≤ Nat.card Γ := by
      have := pow_le (by omega : d' ≤ 3) h1
      calc q ^ 2 ≤ q ^ (4 - d') := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ _ := this
    exact Or.inr ⟨hΓq, hΓ'q, by omega, hd'3⟩
  ·
    have h3 : d = 3 := by omega
    have hΓle := hpt h3
    have hd'3 : d' = 3 := by
      have hA := pow_le hd' h1
      by_contra hne
      have hB : q ^ 2 ≤ q ^ (4 - d') := Nat.pow_le_pow_right (by omega) (by omega)
      have hC : q < q ^ 2 := by nlinarith
      exact absurd (hC.trans_le (hB.trans (hA.trans hΓle))) (lt_irrefl q)
    have hΓ'q : q ≤ Nat.card Γ' := by
      have := pow_le (by omega : d ≤ 3) h2
      rw [h3] at this
      simpa using this
    have hΓq : q ≤ Nat.card Γ := by
      have := pow_le (by omega : d' ≤ 3) h1
      rw [hd'3] at this
      simpa using this
    obtain ⟨p, hp, hpe⟩ := MSP.eq_xPoint_of_finrank_fixSp_three h3 (by rw [hqn]; exact hΓq)
    obtain ⟨p', hp', hpe'⟩ :=
      MSP.eq_xPoint_of_finrank_fixSp_three hd'3 (by rw [hqn]; exact hΓ'q)
    exact Or.inl ⟨⟨p, hp, hpe⟩, ⟨p', hp', hpe'⟩⟩

end Shapes

end CFSG.Quasithin.MS93.S33
