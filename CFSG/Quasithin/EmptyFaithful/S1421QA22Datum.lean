module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List
public import CFSG.Quasithin.EmptyFaithful.S1421QA15Defs
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5112Bar

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 L M₁ : Subgroup G}

theorem Core3Ctx.comm_K1 (c : Core3Ctx T M H K1 L M₁) {z : G} (hz : z ∈ quasithinOmegaOneCenter T)
    {k : G} (hk : k ∈ K1) : z * k = k * z :=
  Subgroup.mem_centralizer_iff.mp (K1_le_mcOf c.st hk) z hz

theorem Core3Ctx.not_isSolvable_modO2Image (c : Core3Ctx T M H K1 L M₁) :
    ¬ Group.IsSolvable ↥(modO2Image L K1) := by
  intro hs
  have hK1L : K1 ≤ L := c.lt_L.le
  have hperf : Group.IsPerfect ↥K1 := Subgroup.isPerfect_iff.mpr
    (perfect_of_mem_cComp c.st.notation_.cComp_mem)
  have hker : Group.IsSolvable ↥(H13.barMap hK1L).ker := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (H13.isPGroup_ker_barMap hK1L).isNilpotent
    infer_instance
  have hK : Group.IsSolvable ↥K1 :=
    Group.isSolvable_of_ker_le_range (H13.barMap hK1L).ker.subtype (H13.barMap hK1L)
      (by rw [Subgroup.range_subtype])
  have hnt : Nontrivial ↥K1 :=
    (Subgroup.nontrivial_iff_ne_bot K1).mpr (ne_bot_of_mem_cComp c.st.notation_.cComp_mem)
  have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥K1
  rw [hperf.commutator_eq_top] at h1
  exact lt_irrefl _ h1

omit [Finite G] in
theorem false_of_centralizes {L : Subgroup G} {z : G} (hL : L ≠ ⊥)
    (hLz : ⁅L, Subgroup.zpowers z⁆ = L) (hcomm : ∀ x ∈ L, z * x = x * z) : False := by
  apply hL
  rw [← hLz, eq_bot_iff, Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hc : Commute z x := hcomm x hx
  have h1 : x * z ^ k = z ^ k * x := (hc.zpow_left k).symm.eq
  rw [Subgroup.mem_bot, commutatorElement_def, h1]
  group

theorem Core3Ctx.exists_inv_centralizing (c : Core3Ctx T M H K1 L M₁)
    (hc : Subgroup.center ↥L = CFSG.pCore 2 ↥L) {z : G} (hz : z ∈ quasithinOmegaOneCenter T)
    (hz2 : z ^ 2 = 1) (hLz : ⁅L, Subgroup.zpowers z⁆ = L) (hin : InducesInner z L) :
    ∃ t : ↥L ⧸ CFSG.pCore 2 ↥L, t ≠ 1 ∧ t * t = 1 ∧ ∀ g ∈ modO2Image L K1, g * t = t * g := by
  obtain ⟨l, hlL, hl⟩ := hin
  have hLbot : L ≠ ⊥ := ne_bot_of_mem_cComp c.mem
  have hzz : z * z = 1 := by rw [← sq]; exact hz2
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  refine ⟨QuotientGroup.mk ⟨l, hlL⟩, ?_, ?_, ?_⟩
  · intro h
    have h1 : (⟨l, hlL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff _).mp h
    rw [← hc, Subgroup.mem_center_iff] at h1
    refine false_of_centralizes hLbot hLz fun x hx => ?_
    have h2 := congrArg Subtype.val (h1 ⟨x, hx⟩)
    simp only [Subgroup.coe_mul] at h2
    have h3 := hl x hx
    have h4 : z⁻¹ * x * z = x := by
      rw [h3]
      calc l⁻¹ * x * l = l⁻¹ * (x * l) := by group
        _ = l⁻¹ * (l * x) := by rw [h2]
        _ = x := by group
    calc z * x = z * (z⁻¹ * x * z) := by rw [h4]
      _ = x * z := by group
  · rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, ← hc, Subgroup.mem_center_iff]
    intro x
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    have h1 := hl x x.2
    have hzL : z⁻¹ * (x : G) * z ∈ L := by
      rw [h1]
      exact L.mul_mem (L.mul_mem (L.inv_mem hlL) x.2) hlL
    have h2 := hl _ hzL
    have h3 : z⁻¹ * (z⁻¹ * (x : G) * z) * z = x := by
      rw [hzi]
      calc z * (z * (x : G) * z) * z = (z * z) * x * (z * z) := by group
        _ = x := by rw [hzz]; group
    rw [h3, h1] at h2
    calc (x : G) * (l * l) = l * l * (l⁻¹ * (l⁻¹ * x * l) * l) := by group
      _ = l * l * x := by rw [← h2]
  · intro g hg
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
    have hyK : (y : G) ∈ K1 := hy
    have hzc := c.comm_K1 hz hyK
    have h1 := hl y y.2
    have hy' : z⁻¹ * (y : G) * z = y := by
      rw [mul_assoc, ← hzc, ← mul_assoc, inv_mul_cancel, one_mul]
    have h5 : (y : G) = l⁻¹ * y * l := hy'.symm.trans h1
    have h6 : (y : G) * l = l * y := by
      calc (y : G) * l = l * (l⁻¹ * y * l) := by group
        _ = l * y := by rw [← h5]
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg QuotientGroup.mk (Subtype.ext h6)

theorem Core3Ctx.five_dvd_card_modO2Image (c : Core3Ctx T M H K1 L M₁)
    (hK : IsL2Quot 2 (OTwoQuot K1)) : 5 ∣ Nat.card ↥(modO2Image L K1) := by
  obtain ⟨e⟩ := Vol2.Ch11.SecA.modO2Image_quotEquiv c.lt_L.le
  have e2 : ModO2 K1 ≃* OTwoQuot K1 :=
    QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K1 2)
  have h60 : Nat.card (ModO2 K1) = 60 := by
    rw [Nat.card_congr e2.toEquiv, hK.card (by norm_num)]
    norm_num
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥(modO2Image L K1))
  rw [← Nat.card_congr e.toEquiv, h60] at h1
  exact (by norm_num : 5 ∣ 60).trans ⟨_, h1⟩

theorem Core3Ctx.perm_datum (c : Core3Ctx T M H K1 L M₁)
    (hc : Subgroup.center ↥L = CFSG.pCore 2 ↥L) {z : G} (hz : z ∈ quasithinOmegaOneCenter T)
    {n : ℕ} {φ : (↥L ⧸ Subgroup.center ↥L) ≃* alternatingGroup (Fin n)}
    {σ : Equiv.Perm (Fin n)} (hact : InducesPermAction z L φ σ) :
    ∃ ψ : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* alternatingGroup (Fin n), ∀ g ∈ modO2Image L K1,
      ((ψ g : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * σ =
        σ * ((ψ g : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := by
  refine ⟨(QuotientGroup.quotientMulEquivOfEq hc).symm.trans φ, fun g hg => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
  have hyK : (y : G) ∈ K1 := hy
  have hzc := c.comm_K1 hz hyK
  have hy' : z⁻¹ * (y : G) * z = y := by
    rw [mul_assoc, ← hzc, ← mul_assoc, inv_mul_cancel, one_mul]
  have h := hact.2 y y hy'.symm
  have e : ((QuotientGroup.quotientMulEquivOfEq hc).symm.trans φ) ((QuotientGroup.mk' _) y) =
      φ (QuotientGroup.mk y) := rfl
  rw [e]
  calc ((φ (QuotientGroup.mk y) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) * σ
      = σ * (σ⁻¹ * ((φ (QuotientGroup.mk y) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) *
          σ) := by group
    _ = σ * ((φ (QuotientGroup.mk y) : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)) := by
      rw [← h]

end S1421

end CFSG.Quasithin
