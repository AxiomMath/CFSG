module

public import CFSG.Quasithin.Vol2.E2TenSeven
public import CFSG.Quasithin.Vol2.E2TenEight
public import CFSG.Quasithin.Vol2.E2StatementsAS
public import CFSG.Quasithin.Background.E2TwoProofY
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiLayerKernelBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Setting

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem Hyp28.pair_of_member {H T M V I : Subgroup G} (h : Hyp28 H T M V)
    {N : ℕ∞} (hI : ASInputs.IsInIHTVNoRootAt H T M V I N) {g : G} (hg : g ∈ I) (hgen : I = V ⊔ B6.conjSub g V) :
    Pair I (T ⊓ I) (M ⊓ I) V g := by
  have hVI : V ≤ I := by rw [hgen]; exact le_sup_left
  refine ⟨hI.2.2.1, le_inf h.le_T hVI, inf_le_left.trans h.normal_T, h.elem,
    fun x hx => ⟨h.inf_normalizer_le ⟨hI.1 hx.1, hx.2⟩, hx.1⟩, inf_le_right, ?_,
    hI.2.2.2.1, hg, hgen⟩
  have hle : pCoreOf 2 M ⊓ I ≤ pCoreOf 2 (M ⊓ I) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (inf_le_inf_right I (CFSG.LieType.BorelTits.pCoreOf_le 2 M)) (fun x hx => ?_)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le inf_le_left)
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hx.1, Subgroup.le_normalizer hx.2⟩
  exact (le_inf h.le_pCoreOf hVI).trans hle

namespace Pair

variable {X T M V : Subgroup G} {g : G}

omit [Finite G] in
theorem forall_commutator_mem_iff [((PP M V X g).subgroupOf X).Normal] {x : G} (hx : x ∈ X) :
    (∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ PP M V X g) ↔
      piX M V X g ⟨x, hx⟩ ∈ Subgroup.center (Xbar M V X g) := by
  rw [Subgroup.mem_center_iff]
  constructor
  · intro hc q
    obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective ((PP M V X g).subgroupOf X) q
    have hc' := hc y hy
    have hmem : x * y * x⁻¹ * y⁻¹ ∈ X :=
      X.mul_mem (X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)) (X.inv_mem hy)
    have h1 := (piX_eq_one_iff hmem).2 hc'
    have e : (⟨x * y * x⁻¹ * y⁻¹, hmem⟩ : X) = ⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩ : X)⁻¹ *
        (⟨y, hy⟩ : X)⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have := mul_inv_eq_one.1 h1
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  · intro hc y hy
    have hmem : x * y * x⁻¹ * y⁻¹ ∈ X :=
      X.mul_mem (X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)) (X.inv_mem hy)
    rw [← piX_eq_one_iff hmem]
    have e : (⟨x * y * x⁻¹ * y⁻¹, hmem⟩ : X) = ⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩ : X)⁻¹ *
        (⟨y, hy⟩ : X)⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, ← hc (piX M V X g ⟨y, hy⟩),
      mul_inv_cancel_right, mul_inv_cancel]

theorem PP_eq_of_pCoreOf (h : Pair X T M V g) (hJ : pCoreOf 2 X = kerIn M X) :
    (pCoreOf 2 X ⊓ V) ⊔ (pCoreOf 2 X ⊓ conjSub g V) = PP M V X g := by
  rw [PP, h.conjSub_kerIn_inf_eq, hJ, inf_comm (conjSub g V)]

theorem five_of_center (h : Pair X T M V g) [((PP M V X g).subgroupOf X).Normal]
    (hZ : Subgroup.center (Xbar M V X g) = Jbar M V X g)
    (hsq : ∀ z ∈ Subgroup.center (Xbar M V X g), z * z = 1) (hJ : pCoreOf 2 X = kerIn M X) :
    pCoreOf 2 X = kerIn M X ∧
      (pCoreOf 2 X ⊓ V) ⊔ (pCoreOf 2 X ⊓ conjSub g V) ≤ pCoreOf 2 X ∧
      (∀ x ∈ X, (∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ (pCoreOf 2 X ⊓ V) ⊔ (pCoreOf 2 X ⊓ conjSub g V)) ↔
        x ∈ pCoreOf 2 X) ∧
      ∀ x ∈ pCoreOf 2 X, x ^ 2 ∈ (pCoreOf 2 X ⊓ V) ⊔ (pCoreOf 2 X ⊓ conjSub g V) := by
  rw [h.PP_eq_of_pCoreOf hJ]
  refine ⟨hJ, hJ ▸ h.P_le_J, fun x hx => ?_, fun x hxJ => ?_⟩
  · rw [forall_commutator_mem_iff hx, hZ, hJ]
    constructor
    · rintro ⟨y, hy0, hyx⟩
      have hy : (y : G) ∈ kerIn M X := hy0
      have hP : (y : G)⁻¹ * x ∈ PP M V X g := by
        have h1 := QuotientGroup.eq.1 hyx
        rw [Subgroup.mem_subgroupOf] at h1
        simpa using h1
      have e : x = (y : G) * ((y : G)⁻¹ * x) := by group
      rw [e]
      exact (kerIn M X).mul_mem hy (h.P_le_J hP)
    · intro hxJ
      exact ⟨⟨x, hx⟩, Subgroup.mem_subgroupOf.2 hxJ, rfl⟩
  · rw [hJ] at hxJ
    have hxX : x ∈ X := kerIn_le.trans h.le_X hxJ
    have hx2 : x ^ 2 ∈ X := X.pow_mem hxX 2
    rw [← piX_eq_one_iff hx2]
    have e : (⟨x ^ 2, hx2⟩ : X) = ⟨x, hxX⟩ * ⟨x, hxX⟩ := Subtype.ext (pow_two x)
    rw [e, map_mul]
    exact hsq _ (hZ ▸ ⟨⟨x, hxX⟩, Subgroup.mem_subgroupOf.2 hxJ, rfl⟩)

theorem five_of_dihedral (h : Pair X T M V g) (hP : PP M V X g = pCoreOf 2 X)
    (hJ : pCoreOf 2 X = kerIn M X) {m : ℕ} (hm : Odd m) (hm1 : m ≠ 1)
    (e : StarQuot M X ≃* DihedralGroup m) :
    pCoreOf 2 X = kerIn M X ∧
      (pCoreOf 2 X ⊓ V) ⊔ (pCoreOf 2 X ⊓ conjSub g V) ≤ pCoreOf 2 X ∧
      (∀ x ∈ X, (∀ y ∈ X, x * y * x⁻¹ * y⁻¹ ∈ (pCoreOf 2 X ⊓ V) ⊔ (pCoreOf 2 X ⊓ conjSub g V)) ↔
        x ∈ pCoreOf 2 X) ∧
      ∀ x ∈ pCoreOf 2 X, x ^ 2 ∈ (pCoreOf 2 X ⊓ V) ⊔ (pCoreOf 2 X ⊓ conjSub g V) := by
  rw [h.PP_eq_of_pCoreOf hJ, hP]
  refine ⟨hJ, le_rfl, fun x hx => ⟨fun hc => ?_, fun hxO y hy => ?_⟩, fun x hx =>
    (pCoreOf 2 X).pow_mem hx 2⟩
  ·
    have hJn := h.normal_J
    have hcen : QuotientGroup.mk' ((kerIn M X).subgroupOf X) (⟨x, hx⟩ : X) ∈
        Subgroup.center (StarQuot M X) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective ((kerIn M X).subgroupOf X) q
      have hc' := hc y hy
      have hmem : x * y * x⁻¹ * y⁻¹ ∈ X :=
        X.mul_mem (X.mul_mem (X.mul_mem hx hy) (X.inv_mem hx)) (X.inv_mem hy)
      have h1 : QuotientGroup.mk' ((kerIn M X).subgroupOf X) (⟨x * y * x⁻¹ * y⁻¹, hmem⟩ : X) =
          1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hJ ▸ hc'
      have e1 : (⟨x * y * x⁻¹ * y⁻¹, hmem⟩ : X) = ⟨x, hx⟩ * ⟨y, hy⟩ * (⟨x, hx⟩ : X)⁻¹ *
          (⟨y, hy⟩ : X)⁻¹ := Subtype.ext rfl
      rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      have := mul_inv_eq_one.1 h1
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    have hbot : Subgroup.center (StarQuot M X) = ⊥ := by
      have h0 := DihedralGroup.center_eq_bot_of_odd_ne_one hm hm1
      rw [eq_bot_iff]
      intro z hz
      have hz' : e z ∈ Subgroup.center (DihedralGroup m) := by
        rw [Subgroup.mem_center_iff] at hz ⊢
        intro w
        obtain ⟨u, rfl⟩ := e.surjective w
        rw [← map_mul, ← map_mul, hz u]
      rw [h0, Subgroup.mem_bot] at hz'
      rw [Subgroup.mem_bot]
      exact e.injective (by rw [hz', map_one])
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at hcen
    exact hJ ▸ hcen
  ·
    have h1 : y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 X :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hy) _).mp ((pCoreOf 2 X).inv_mem hxO)
    have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 X).mul_mem hxO h1

theorem center_eight
    (h : Pair X T M V g) {n : ℕ}
    (hY : IsPSp4 2 n (StarQuot M X)) [((PP M V X g).subgroupOf X).Normal] :
    Subgroup.center (Xbar M V X g) = Jbar M V X g ∧
      (∀ z ∈ Subgroup.center (Xbar M V X g), z * z = 1) ∧ pCoreOf 2 X = kerIn M X := by
  have hXs := isSimpleGroup_of_isPSp4 hY
  have hXp := commutator_eq_top_of_isPSp4 hY
  have := hXs.toNontrivial
  have hXna := nonabelian_of_commutator_eq_top hXp
  have := h.normal_Jbar
  set e := h.quotJbarEquiv
  have hS : commutator (Xbar M V X g ⧸ Jbar M V X g) = ⊤ := commutator_eq_top_of_mulEquiv e hXp
  have hsimp : IsSimpleGroup (Xbar M V X g ⧸ Jbar M V X g) := MulEquiv.isSimpleGroup e
  have hna : ∃ a b : Xbar M V X g ⧸ Jbar M V X g, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hXna
    exact ⟨e.symm a, e.symm b, fun hh => hab (by simpa using congrArg e hh)⟩
  obtain ⟨hLq, ⟨eL⟩⟩ := quasisimple_commutator _ h.Jbar_le_center hS hsimp hna
  have : Group.IsPerfect ↥(commutator (Xbar M V X g)) := hLq.1
  have hb := center_eq_bot_of_isPSp4 hY (eL.trans e)
  exact h.center_quot_facts hXs hXp hXna (lift_of_center_eq_bot hb)

end Pair

theorem eq_zero_of_add_self_eq_zero {m : ℕ} (hm : Odd m) {i : ZMod m} (h : i + i = 0) :
    i = 0 := by
  have hcop : Nat.Coprime 2 m := Nat.coprime_two_left.2 hm
  set u := ZMod.unitOfCoprime 2 hcop
  have hu : (u : ZMod m) = 2 := ZMod.coe_unitOfCoprime 2 hcop
  have h2 : (u : ZMod m) * i = 0 := by rw [hu, two_mul]; exact h
  calc i = ((u⁻¹ : (ZMod m)ˣ) : ZMod m) * ((u : ZMod m) * i) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = 0 := by rw [h2, mul_zero]

theorem dihedral_eq_of_commute {m : ℕ} (hm : Odd m) {x y : DihedralGroup m} (hx : x * x = 1)
    (hy : y * y = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hxy : x * y = y * x) : x = y := by
  have hr : ∀ i : ZMod m, DihedralGroup.r i * DihedralGroup.r i = 1 →
      DihedralGroup.r i = (1 : DihedralGroup m) := by
    intro i hi
    rw [DihedralGroup.r_mul_r, DihedralGroup.one_def, DihedralGroup.r.injEq] at hi
    rw [eq_zero_of_add_self_eq_zero hm hi, DihedralGroup.r_zero]
  rcases x with i | i
  · exact absurd (hr i hx) hx1
  rcases y with j | j
  · exact absurd (hr j hy) hy1
  rw [DihedralGroup.sr_mul_sr, DihedralGroup.sr_mul_sr, DihedralGroup.r.injEq] at hxy
  have h1 : (j - i) + (j - i) = 0 := by
    have : j - i = i - j := hxy
    calc (j - i) + (j - i) = (j - i) + (i - j) := by rw [← this]
      _ = 0 := by ring
  have h2 := eq_zero_of_add_self_eq_zero hm h1
  rw [sub_eq_zero] at h2
  rw [h2]

namespace Pair

variable {X T M V : Subgroup G} {g : G}

omit [Finite G] in
theorem relIndex_eq_two_of_dihedral (h : Pair X T M V g) {m : ℕ} (hm : Odd m)
    (e : StarQuot M X ≃* DihedralGroup m) : (kerIn M X ⊓ V).relIndex V = 2 := by
  have hJn := h.normal_J
  set q := QuotientGroup.mk' ((kerIn M X).subgroupOf X)
  have hout : ∀ v (hv : v ∈ V), v ∉ kerIn M X → e (q ⟨v, h.V_le hv⟩) ≠ 1 := by
    intro v hv hvJ h1
    apply hvJ
    have h2 : q ⟨v, h.V_le hv⟩ = 1 := e.injective (by rw [h1, map_one])
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    exact h2
  have hsq : ∀ v (hv : v ∈ V), e (q ⟨v, h.V_le hv⟩) * e (q ⟨v, h.V_le hv⟩) = 1 := by
    intro v hv
    rw [← map_mul, ← map_mul]
    have : (⟨v, h.V_le hv⟩ : X) * ⟨v, h.V_le hv⟩ = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]; exact h.elem.2 v hv)
    rw [this, map_one, map_one]
  obtain ⟨v₀, hv₀, hv₀J⟩ : ∃ v ∈ V, v ∉ kerIn M X := by
    by_contra hno
    push Not at hno
    have hXJ : X ≤ kerIn M X := by
      intro x hx
      rw [h.gen] at hx
      have hle : V ⊔ conjSub g V ≤ kerIn M X := by
        refine sup_le (fun v hv => hno v hv) ?_
        intro w hw
        rw [mem_conjSub] at hw
        have hw' := hno _ hw
        have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn M X h.mem) _).mp hw'
        simpa [mul_assoc] using this
      exact hle hx
    have htriv : ∀ z : StarQuot M X, z = 1 := by
      intro z
      obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective ((kerIn M X).subgroupOf X) z
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hXJ hx
    have hc : Nat.card (DihedralGroup m) = 1 := by
      rw [← Nat.card_congr e.toEquiv]
      have : Subsingleton (StarQuot M X) := ⟨fun a b => by rw [htriv a, htriv b]⟩
      exact Nat.card_eq_one_iff_unique.2 ⟨inferInstance, ⟨1⟩⟩
    rw [DihedralGroup.nat_card] at hc
    omega
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨v₀, hv₀⟩, fun b => ?_⟩
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf]
  have hb := b.2
  have hbv : (b : G) * v₀ ∈ V := V.mul_mem hb hv₀
  by_cases hbJ : (b : G) ∈ kerIn M X
  · have : (b : G) * v₀ ∉ kerIn M X := fun h1 => hv₀J (by
      have := (kerIn M X).mul_mem ((kerIn M X).inv_mem hbJ) h1
      simpa using this)
    simp [hbJ, this, hb, hbv]
  ·
    have heq := dihedral_eq_of_commute hm (hsq _ hb) (hsq _ hv₀) (hout _ hb hbJ) (hout _ hv₀ hv₀J)
      (by rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
          congr 2
          exact Subtype.ext (h.comm hb hv₀))
    have hprod : (b : G) * v₀ ∈ kerIn M X := by
      have h1 : q (⟨(b : G) * v₀, h.V_le hbv⟩ : X) = 1 := by
        have e1 : (⟨(b : G) * v₀, h.V_le hbv⟩ : X) = ⟨b, h.V_le hb⟩ * ⟨v₀, h.V_le hv₀⟩ :=
          Subtype.ext rfl
        rw [e1, map_mul]
        apply e.injective
        rw [map_mul, heq, hsq _ hv₀, map_one]
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      exact h1
    simp [hbJ, hprod, hb, hbv]

end Pair

theorem isSylowTwoOf_map_equiv {Y Y' : Type*} [Group Y] [Group Y'] (e : Y ≃* Y')
    {S : Subgroup Y} (hS : IsSylowTwoOf S ⊤) : IsSylowTwoOf (S.map (e : Y →* Y')) ⊤ := by
  refine ⟨le_top, hS.2.1.map _, ?_⟩
  have e1 : ((S.map (e : Y →* Y')).subgroupOf ⊤).index = (S.map (e : Y →* Y')).index :=
    Subgroup.relIndex_top_right _
  have e2 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right _
  rw [e1, Subgroup.index_map_equiv]
  have := hS.2.2
  rwa [e2] at this

theorem comm_of_mem_sylow_isPSL {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (hY : IsPSL 2 2 n Y) {S : Subgroup Y} (hS : IsSylowTwoOf S ⊤) {x y : Y} (hx : x ∈ S)
    (hy : y ∈ S) : x * y = y * x := by
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨eK⟩⟩ := hY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  have : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcardK : Fintype.card K = Fintype.card (GaloisField 2 n) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hK, GaloisField.card 2 n (by omega)]
  let ψ : K ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq hcardK
  let φ : Y ≃* CFSG.AGLEmbedding.PSL2GF 2 n :=
    (eK.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans
      (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv ψ (Fin 2))
  have hS' := isSylowTwoOf_map_equiv φ hS
  have hidx : ¬ 2 ∣ (S.map (φ : Y →* CFSG.AGLEmbedding.PSL2GF 2 n)).index := by
    have := hS'.2.2
    have e1 : ((S.map (φ : Y →* CFSG.AGLEmbedding.PSL2GF 2 n)).subgroupOf ⊤).index =
        (S.map (φ : Y →* CFSG.AGLEmbedding.PSL2GF 2 n)).index := Subgroup.relIndex_top_right _
    rwa [e1] at this
  set P := hS'.2.1.toSylow hidx
  obtain ⟨⟨hcomm⟩, -⟩ := CFSG.AGLEmbedding.psl2GF_sylow 2 n (by omega) P
  have hxP : φ x ∈ (P : Subgroup _) := ⟨x, hx, rfl⟩
  have hyP : φ y ∈ (P : Subgroup _) := ⟨y, hy, rfl⟩
  have h1 := congrArg Subtype.val (hcomm.is_comm.comm ⟨φ x, hxP⟩ ⟨φ y, hyP⟩)
  apply φ.injective
  simpa using h1

theorem comm_of_mem_sylow_isSz {Y : Type} [Group Y] [Finite Y]
    {n : ℕ} (hY : IsSz n Y) {S : Subgroup Y} (hS : IsSylowTwoOf S ⊤) {x y : Y} (hx : x ∈ S)
    (hx2 : x * x = 1) (hy : y ∈ S) : x * y = y * x := by
  obtain ⟨-, a, ha, K, _, _, hn, hK, ⟨eK⟩⟩ := hY
  rw [hn] at hK
  obtain ⟨U, hU⟩ := CFSG.ShultStronglyClosedTI.SuzukiModel.exists_sylow_eq_suzukiU hK
  have hS' := isSylowTwoOf_map_equiv eK hS
  have hU' : IsSylowTwoOf (U : Subgroup (CFSG.Blueprint.suzukiGroup a K)) ⊤ :=
    CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow U
  obtain ⟨c, -, hc⟩ := B6.isSylowTwoOf_exists_conj hU' hS'
  have hxS : eK x ∈ conjSub c (U : Subgroup _) := hc ▸ ⟨x, hx, rfl⟩
  have hyS : eK y ∈ conjSub c (U : Subgroup _) := hc ▸ ⟨y, hy, rfl⟩
  rw [mem_conjSub] at hxS hyS
  rw [hU] at hxS hyS
  set u := c⁻¹ * eK x * c
  set w := c⁻¹ * eK y * c
  have hu2 : u ^ 2 = 1 := by
    rw [pow_two]
    have : u * u = c⁻¹ * eK (x * x) * c := by simp only [u, map_mul]; group
    rw [this, hx2, map_one]
    group
  have huZ : u ∈ CFSG.LieType.Ree.suzukiZ0 a K :=
    (CFSG.ShultStronglyClosedTI.SuzukiLayerKernel.mem_suzukiZ0_iff_sq_eq_one hK).2 ⟨hxS, hu2⟩
  have hcen := CFSG.ShultStronglyClosedTI.SuzukiRootAutomorphism.center_suzukiU hK ha
  have huc : (⟨u, hxS⟩ : CFSG.LieType.Ree.suzukiU a K) ∈
      Subgroup.center (CFSG.LieType.Ree.suzukiU a K) := by
    rw [hcen, Subgroup.mem_subgroupOf]
    exact huZ
  have huw : u * w = w * u := by
    have := congrArg Subtype.val ((Subgroup.mem_center_iff.1 huc) ⟨w, hyS⟩)
    simpa using this.symm
  apply eK.injective
  have e1 : eK x = c * u * c⁻¹ := by simp only [u]; group
  have e2 : eK y = c * w * c⁻¹ := by simp only [w]; group
  rw [map_mul, map_mul, e1, e2]
  calc c * u * c⁻¹ * (c * w * c⁻¹) = c * (u * w) * c⁻¹ := by group
    _ = c * (w * u) * c⁻¹ := by rw [huw]
    _ = c * w * c⁻¹ * (c * u * c⁻¹) := by group

theorem comm_of_isPGroup_dihedral {m : ℕ} (hm : Odd m) {S : Subgroup (DihedralGroup m)}
    (hS : IsPGroup 2 S) {x y : DihedralGroup m} (hx : x ∈ S) (hy : y ∈ S) : x * y = y * x := by
  have hr : ∀ i : ZMod m, DihedralGroup.r i ∈ S → DihedralGroup.r i = 1 := by
    intro i hi
    obtain ⟨k, hk⟩ := hS ⟨_, hi⟩
    have hk' : (DihedralGroup.r i) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hm' : (DihedralGroup.r i) ^ m = 1 := by
      rw [DihedralGroup.r_pow, ZMod.natCast_self, mul_zero, DihedralGroup.r_zero]
    have h1 : orderOf (DihedralGroup.r i) ∣ Nat.gcd (2 ^ k) m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hm')
    rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_left k (Nat.coprime_two_left.2 hm)),
      Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  rcases x with i | i
  · rw [hr i hx, one_mul, mul_one]
  rcases y with j | j
  · rw [hr j hy, one_mul, mul_one]
  have hprod := hr (j - i) (by rw [← DihedralGroup.sr_mul_sr]; exact S.mul_mem hx hy)
  rw [DihedralGroup.one_def, DihedralGroup.r.injEq, sub_eq_zero] at hprod
  rw [hprod]

theorem le_of_normal_sylow' {Y : Type*} [Group Y] [Finite Y] {S N Q : Subgroup Y}
    (hS : IsSylowTwoOf S N) (hn : N ≤ Subgroup.normalizer (S : Set Y)) (hQN : Q ≤ N)
    (hQ : IsPGroup 2 Q) : Q ≤ S := by
  obtain ⟨S', hS', hQS'⟩ := B6.exists_isSylowTwoOf_ge hQ hQN
  obtain ⟨c, hc, hcS⟩ := B6.isSylowTwoOf_exists_conj hS hS'
  rw [hcS, B6.conjSub_eq_self (hn hc)] at hQS'
  exact hQS'

theorem center_eq_bot_of_simple {Y : Type*} [Group Y] (hs : IsSimpleGroup Y)
    (hna : ∃ a b : Y, a * b ≠ b * a) : Subgroup.center Y = ⊥ := by
  rcases (Subgroup.center Y).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have hb : b ∈ Subgroup.center Y := h ▸ Subgroup.mem_top b
    exact hab (Subgroup.mem_center_iff.1 hb a)

variable {H T M V I : Subgroup G} {g : G}

theorem isSylowTwoOf_star_inf (hsyl : IsSylowTwoOf (T ⊓ I) I) :
    IsSylowTwoOf (star (M ⊓ I) I (T ⊓ I)) ⊤ := by
  have hTI : T ⊓ I ≤ I := inf_le_right
  have h1 : IsSylowTwoOf ((T ⊓ I).subgroupOf I) ⊤ := by
    refine ⟨le_top, hsyl.2.1.of_injective (Subgroup.subgroupOfEquivOfLe hTI).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hTI).injective, ?_⟩
    have e : (((T ⊓ I).subgroupOf I).subgroupOf ⊤).index = ((T ⊓ I).subgroupOf I).index :=
      Subgroup.relIndex_top_right _
    rw [e]
    exact hsyl.2.2
  exact B6.isSylowTwoOf_map_top (E2P.starMap_surjective (M ⊓ I) I) h1

omit [Finite G] in
theorem mem_star {X : Subgroup G} {x : G} (hxI : x ∈ I) (hx : x ∈ X) :
    QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) (⟨x, hxI⟩ : I) ∈ star (M ⊓ I) I X :=
  ⟨⟨x, hxI⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩

omit [Finite G] in
theorem sq_eq_one_of_mem_star {X : Subgroup G} (hX : IsElemAbelian 2 X) {z : StarQuot (M ⊓ I) I}
    (hz : z ∈ star (M ⊓ I) I X) : z * z = 1 := by
  obtain ⟨y, hy, rfl⟩ := hz
  rw [← map_mul]
  have : y * y = 1 := Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]; exact hX.2 _ hy)
  rw [this, map_one]

omit [Finite G] in
theorem center_star_eq_bot
    {N : ℕ∞} (hI : ASInputs.IsInIHTVNoRootAt H T M V I N)
    (hS6 : IsEmpty (StarQuot (M ⊓ I) I ≃* Equiv.Perm (Fin 6))) :
    Subgroup.center (StarQuot (M ⊓ I) I) = ⊥ := by
  obtain ⟨-, -, -, -, k, -, hc⟩ := hI
  rcases hc with ⟨hk, hY, -⟩ | ⟨-, p, a, hp, hp2, ha, ⟨e⟩⟩ | ⟨-, -, hY, -⟩
  · exact center_eq_bot_of_simple (isSimpleGroup_of_psl_or_sz hY) (nonabelian_of_psl_or_sz hk hY)
  · have hodd : Odd (p ^ a) := (hp.odd_of_ne_two hp2).pow
    have hne : p ^ a ≠ 1 := by
      have : 1 < p ^ a := Nat.one_lt_pow (by omega) hp.one_lt
      omega
    have h0 := DihedralGroup.center_eq_bot_of_odd_ne_one hodd hne
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center (DihedralGroup (p ^ a)) := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro w
      obtain ⟨u, rfl⟩ := e.surjective w
      rw [← map_mul, ← map_mul, hz u]
    rw [h0, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot]
    exact e.injective (by rw [hz', map_one])
  · rcases hY with hY | ⟨-, ⟨e⟩⟩
    · have hs := isSimpleGroup_of_isPSp4 hY
      have := hs.toNontrivial
      exact center_eq_bot_of_simple hs (nonabelian_of_commutator_eq_top
        (commutator_eq_top_of_isPSp4 hY))
    · exact (hS6.false e).elim

theorem e2_11_two (h : Hyp28 H T M V)
    {N : ℕ∞} (hI : ASInputs.IsInIHTVNoRootAt H T M V I N) (hVI : V ≤ I) :
    star (M ⊓ I) I V ≤
      Subgroup.centralizer (star (M ⊓ I) I (T ⊓ I) : Set (StarQuot (M ⊓ I) I)) := by
  have hVT : star (M ⊓ I) I V ≤ star (M ⊓ I) I (T ⊓ I) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono I (le_inf h.le_T hVI))
  obtain ⟨-, -, hsyl, -, k, -, hc⟩ := hI
  have hS := isSylowTwoOf_star_inf (M := M) hsyl
  have := E2P.finite_starQuot (M ⊓ I) I
  rcases hc with ⟨-, hY, -⟩ | ⟨-, p, a, hp, hp2, -, ⟨e⟩⟩ | ⟨-, -, -, -, hcent⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    rcases hY with hY | hY
    · exact comm_of_mem_sylow_isPSL hY hS ht (hVT hx)
    · exact (comm_of_mem_sylow_isSz hY hS (hVT hx) (sq_eq_one_of_mem_star h.elem hx) ht).symm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have h2 : IsPGroup 2 ((star (M ⊓ I) I (T ⊓ I)).map
        (e : StarQuot (M ⊓ I) I →* DihedralGroup (p ^ a))) := hS.2.1.map _
    have h3 := comm_of_isPGroup_dihedral (hp.odd_of_ne_two hp2).pow h2 ⟨t, ht, rfl⟩
      ⟨x, hVT hx, rfl⟩
    apply e.injective
    rw [map_mul, map_mul]
    exact h3
  · exact hcent

theorem le_normalizer_star (h : Hyp28 H T M V) {N : ℕ∞} (hI : ASInputs.IsInIHTVNoRootAt H T M V I N) :
    star (M ⊓ I) I (M ⊓ I) ≤
      Subgroup.normalizer (star (M ⊓ I) I (T ⊓ I) : Set (StarQuot (M ⊓ I) I)) := by
  have hTM : star (M ⊓ I) I (T ⊓ I) ≤ star (M ⊓ I) I (M ⊓ I) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono I (inf_le_inf_right I h.minParabolic.le))
  obtain ⟨-, -, hsyl, -, k, -, hc⟩ := hI
  have hS := isSylowTwoOf_star_inf (M := M) hsyl
  have := E2P.finite_starQuot (M ⊓ I) I
  have hborel : E2.IsBorelIn ⊤ (star (M ⊓ I) I (M ⊓ I)) →
      star (M ⊓ I) I (M ⊓ I) ≤
        Subgroup.normalizer (star (M ⊓ I) I (T ⊓ I) : Set (StarQuot (M ⊓ I) I)) := by
    rintro ⟨S, hSsyl, hSeq⟩
    have hSB : S ≤ star (M ⊓ I) I (M ⊓ I) := by
      rw [hSeq]; exact le_inf le_top Subgroup.le_normalizer
    have hBN : star (M ⊓ I) I (M ⊓ I) ≤ Subgroup.normalizer (S : Set (StarQuot (M ⊓ I) I)) := by
      rw [hSeq]; exact inf_le_right
    have hTS : star (M ⊓ I) I (T ⊓ I) ≤ S :=
      le_of_normal_sylow' (B6.isSylowTwoOf_mono hSsyl hSB le_top) hBN hTM hS.2.1
    have hTeq : star (M ⊓ I) I (T ⊓ I) = S := by
      obtain ⟨c, -, hc⟩ := B6.isSylowTwoOf_exists_conj hS hSsyl
      refine Subgroup.eq_of_le_of_card_ge hTS ?_
      rw [hc]
      exact (Subgroup.card_map_of_injective (MulAut.conj c).injective).le
    rw [hTeq]
    exact hBN
  rcases hc with ⟨-, -, hB⟩ | ⟨-, p, a, hp, hp2, -, ⟨e⟩⟩ | ⟨-, -, -, hB, -⟩
  · exact hborel hB
  ·
    have hcore := E2P.kerIn_star (M ⊓ I) I
    have hM2 : ∀ x ∈ star (M ⊓ I) I (M ⊓ I), x * x = 1 := by
      intro x hx
      rcases hex : e x with i | i
      ·
        have hxk : x ∈ kerIn (star (M ⊓ I) I (M ⊓ I)) ⊤ := by
          intro b _
          rcases heb : e b with j | j
          · have : b * x * b⁻¹ = x := by
              apply e.injective
              rw [map_mul, map_mul, map_inv, heb, hex, DihedralGroup.r_mul_r, DihedralGroup.inv_r,
                DihedralGroup.r_mul_r]
              congr 1
              ring
            rw [this]; exact hx
          · have : b * x * b⁻¹ = x⁻¹ := by
              apply e.injective
              rw [map_mul, map_mul, map_inv, map_inv, heb, hex, DihedralGroup.sr_mul_r,
                DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr, DihedralGroup.inv_r]
              congr 1
              ring
            rw [this]; exact (star (M ⊓ I) I (M ⊓ I)).inv_mem hx
        rw [hcore, Subgroup.mem_bot] at hxk
        rw [hxk, one_mul]
      · apply e.injective
        rw [map_mul, hex, DihedralGroup.sr_mul_self, map_one]
    have hMp : IsPGroup 2 (star (M ⊓ I) I (M ⊓ I)) := fun x =>
      ⟨1, Subtype.ext (by simpa [pow_two] using hM2 x x.2)⟩
    have heq : star (M ⊓ I) I (T ⊓ I) = star (M ⊓ I) I (M ⊓ I) := by
      rw [A4.isSylowTwoOf_iff_maximal] at hS
      exact le_antisymm hTM (hS.2.2 _ le_top hMp hTM)
    rw [heq]
    exact Subgroup.le_normalizer
  · exact hborel hB

theorem e2_11_three (h : Hyp28 H T M V) {N : ℕ∞} (hI : ASInputs.IsInIHTVNoRootAt H T M V I N)
    (hJ : pCoreOf 2 I = kerIn (M ⊓ I) I) : T ⊓ I = pCoreOf 2 (M ⊓ I) := by
  have hsyl := hI.2.2.1
  have hTMI : T ⊓ I ≤ M ⊓ I := inf_le_inf_right I h.minParabolic.le
  have hN := le_normalizer_star h hI
  have hJT : kerIn (M ⊓ I) I ≤ T ⊓ I := hJ ▸ B6.pCoreOf_two_le_of_isSylowTwoOf hsyl
  have key : ∀ m ∈ M ⊓ I, ∀ t ∈ T ⊓ I, m * t * m⁻¹ ∈ T ⊓ I := by
    intro m hm t ht
    have hmI : m ∈ I := hm.2
    have htI : t ∈ I := ht.2
    have hy : m * t * m⁻¹ ∈ I := I.mul_mem (I.mul_mem hmI htI) (I.inv_mem hmI)
    have h1 : QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) (⟨m * t * m⁻¹, hy⟩ : I) ∈
        star (M ⊓ I) I (T ⊓ I) := by
      have e1 : (⟨m * t * m⁻¹, hy⟩ : I) = ⟨m, hmI⟩ * ⟨t, htI⟩ * (⟨m, hmI⟩ : I)⁻¹ :=
        Subtype.ext rfl
      rw [e1, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hN (mem_star hmI hm)) _).mp (mem_star htI ht)
    obtain ⟨t', ht', ht'e⟩ := h1
    have ht'' : (t' : G) ∈ T ⊓ I := ht'
    have hk : (t' : G)⁻¹ * (m * t * m⁻¹) ∈ kerIn (M ⊓ I) I := by
      have h2 := QuotientGroup.eq.1 ht'e
      rw [Subgroup.mem_subgroupOf] at h2
      simpa using h2
    have e2 : m * t * m⁻¹ = (t' : G) * ((t' : G)⁻¹ * (m * t * m⁻¹)) := by group
    rw [e2]
    exact (T ⊓ I).mul_mem ht'' (hJT hk)
  have hTN : M ⊓ I ≤ Subgroup.normalizer ((T ⊓ I : Subgroup G) : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨fun ht => key m hm t ht, fun ht => ?_⟩
    have := key m⁻¹ ((M ⊓ I).inv_mem hm) _ ht
    simpa [mul_assoc] using this
  apply le_antisymm
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hTMI hTN hsyl.2.1
  · exact B6.pCoreOf_two_le_of_isSylowTwoOf (B6.isSylowTwoOf_mono hsyl hTMI inf_le_right)

theorem e2_11_four
    (h : Hyp28 H T M V) {N : ℕ∞} (hI : ASInputs.IsInIHTVNoRootAt H T M V I N)
    (hS6 : IsEmpty (StarQuot (M ⊓ I) I ≃* Equiv.Perm (Fin 6))) (hg : g ∈ I)
    (hgen : I = V ⊔ B6.conjSub g V) (hJ : pCoreOf 2 I = kerIn (M ⊓ I) I) :
    B6.conjSub g V ⊓ pCoreOf 2 I = B6.conjSub g V ⊓ Subgroup.normalizer (V : Set G) := by
  have hp := h.pair_of_member hI hg hgen
  have hsyl := hI.2.2.1
  have hWI : B6.conjSub g V ≤ I := hp.conj_le
  have hVI : V ≤ I := hp.V_le
  apply le_antisymm
  · exact inf_le_inf_left _ ((B6.pCoreOf_two_le_of_isSylowTwoOf hsyl).trans
      (inf_le_left.trans h.normal_T))
  rintro u ⟨huW, huN⟩
  refine ⟨huW, ?_⟩
  have huI : u ∈ I := hWI huW
  have huM : u ∈ M ⊓ I := hp.normalizer_le ⟨huI, huN⟩
  set φ := QuotientGroup.mk' ((kerIn (M ⊓ I) I).subgroupOf I) with hφ
  have := E2P.finite_starQuot (M ⊓ I) I
  have hS := isSylowTwoOf_star_inf (M := M) hsyl
  have hu2 : φ ⟨u, huI⟩ * φ ⟨u, huI⟩ = 1 := by
    rw [← map_mul]
    have : (⟨u, huI⟩ : I) * ⟨u, huI⟩ = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      have huW' : u ∈ B6.conjSub g V := huW
      rw [B6.mem_conjSub] at huW'
      have hv2 := h.elem.2 _ huW'
      rw [pow_two] at hv2
      have e1 : u * u = g * ((g⁻¹ * u * g) * (g⁻¹ * u * g)) * g⁻¹ := by group
      rw [e1, hv2]
      group)
    rw [this, map_one]
  have huT : φ ⟨u, huI⟩ ∈ star (M ⊓ I) I (T ⊓ I) := by
    have hzM := mem_star (M := M) huI huM
    have hTM : star (M ⊓ I) I (T ⊓ I) ≤ star (M ⊓ I) I (M ⊓ I) :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono I (inf_le_inf_right I h.minParabolic.le))
    have hu2' : (φ ⟨u, huI⟩) ^ 2 ^ 1 = 1 := by
      rw [pow_one, pow_two]
      exact hu2
    have hle : Subgroup.zpowers (φ ⟨u, huI⟩) ≤ star (M ⊓ I) I (T ⊓ I) :=
      le_of_normal_sylow' (B6.isSylowTwoOf_mono hS hTM le_top) (le_normalizer_star h hI)
        (Subgroup.zpowers_le.2 hzM) (isPGroup_zpowers_of_pow hu2')
    exact hle (Subgroup.mem_zpowers _)
  have h2 := e2_11_two h hI hVI
  have hcV : star (M ⊓ I) I V ≤
      Subgroup.centralizer ({φ ⟨u, huI⟩} : Set (StarQuot (M ⊓ I) I)) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    exact (Subgroup.mem_centralizer_iff.1 (h2 hv) _ huT)
  have hcW : star (M ⊓ I) I (B6.conjSub g V) ≤
      Subgroup.centralizer ({φ ⟨u, huI⟩} : Set (StarQuot (M ⊓ I) I)) := by
    rintro _ ⟨⟨w, hwI⟩, hw, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ rfl
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hp.comm_conj huW (Subgroup.mem_subgroupOf.1 hw))
  have htop : star (M ⊓ I) I V ⊔ star (M ⊓ I) I (B6.conjSub g V) = ⊤ := by
    rw [← E2P.star_top (M ⊓ I) I]
    simp only [E2.star]
    rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup hVI hWI, ← hgen]
  have hcen : φ ⟨u, huI⟩ ∈ Subgroup.center (StarQuot (M ⊓ I) I) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have hz : z ∈ Subgroup.centralizer ({φ ⟨u, huI⟩} : Set (StarQuot (M ⊓ I) I)) :=
      (htop ▸ sup_le hcV hcW) (Subgroup.mem_top z)
    exact (Subgroup.mem_centralizer_iff.1 hz _ rfl).symm
  rw [center_star_eq_bot hI hS6, Subgroup.mem_bot, hφ, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hcen
  rw [hJ]
  exact hcen

theorem not_isSimpleGroup_perm_six : ¬ IsSimpleGroup (Equiv.Perm (Fin 6)) := by
  intro hs
  rcases (alternatingGroup.normal (α := Fin 6)).eq_bot_or_eq_top with h | h
  · have hmem : Equiv.swap (0 : Fin 6) 1 * Equiv.swap 1 2 ∈ alternatingGroup (Fin 6) := by
      rw [Equiv.Perm.mem_alternatingGroup, map_mul, Equiv.Perm.sign_swap (by decide),
        Equiv.Perm.sign_swap (by decide)]
      decide
    rw [h, Subgroup.mem_bot] at hmem
    exact absurd hmem (by decide)
  · have hmem : Equiv.swap (0 : Fin 6) 1 ∈ alternatingGroup (Fin 6) := h ▸ Subgroup.mem_top _
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_swap (by decide)] at hmem
    exact absurd hmem (by decide)

end E2

theorem ASInputs.e2_11C_of_not_S6
    (hKG1 : E2.KGSz8CoverInvolutions) (hKG3 : E2.KGI22One)
    {G : Type} [Group G] [Finite G] {H T M V I : Subgroup G} {g : G} (h : E2.Hyp28 H T M V)
    {N : ℕ∞} (hI : ASInputs.IsInIHTVNoRootAt H T M V I N)
    (hS6 : IsEmpty (E2.StarQuot (M ⊓ I) I ≃* Equiv.Perm (Fin 6))) (hg : g ∈ I)
    (hgen : I = V ⊔ B6.conjSub g V) :
    E2.Pair I (T ⊓ I) (M ⊓ I) V g ∧
      E2.star (M ⊓ I) I V ≤
        Subgroup.centralizer (E2.star (M ⊓ I) I (T ⊓ I) : Set (E2.StarQuot (M ⊓ I) I)) ∧
      T ⊓ I = pCoreOf 2 (M ⊓ I) ∧
      B6.conjSub g V ⊓ pCoreOf 2 I = B6.conjSub g V ⊓ Subgroup.normalizer (V : Set G) ∧
      pCoreOf 2 I = kerIn (M ⊓ I) I ∧
      (pCoreOf 2 I ⊓ V) ⊔ (pCoreOf 2 I ⊓ B6.conjSub g V) ≤ pCoreOf 2 I ∧
      (∀ x ∈ I, (∀ y ∈ I, x * y * x⁻¹ * y⁻¹ ∈ (pCoreOf 2 I ⊓ V) ⊔ (pCoreOf 2 I ⊓ B6.conjSub g V)) ↔
        x ∈ pCoreOf 2 I) ∧
      ∀ x ∈ pCoreOf 2 I, x ^ 2 ∈ (pCoreOf 2 I ⊓ V) ⊔ (pCoreOf 2 I ⊓ B6.conjSub g V) := by
  have hp := h.pair_of_member hI hg hgen
  have hVI : V ≤ I := hp.V_le
  have h5 : pCoreOf 2 I = kerIn (M ⊓ I) I ∧
      (pCoreOf 2 I ⊓ V) ⊔ (pCoreOf 2 I ⊓ B6.conjSub g V) ≤ pCoreOf 2 I ∧
      (∀ x ∈ I, (∀ y ∈ I, x * y * x⁻¹ * y⁻¹ ∈ (pCoreOf 2 I ⊓ V) ⊔ (pCoreOf 2 I ⊓ B6.conjSub g V)) ↔
        x ∈ pCoreOf 2 I) ∧
      ∀ x ∈ pCoreOf 2 I, x ^ 2 ∈ (pCoreOf 2 I ⊓ V) ⊔ (pCoreOf 2 I ⊓ B6.conjSub g V) := by
    obtain ⟨-, -, -, -, k, -, hc⟩ := hI
    rcases hc with ⟨hk, hY, -⟩ | ⟨-, p, a, hp', hp2, ha, ⟨e⟩⟩ | ⟨-, -, hY, -⟩
    · have := hp.normal_P
      obtain ⟨hZ, hsq, hJ⟩ := hp.center_seven hKG1 hKG3 hk hY
      exact hp.five_of_center hZ hsq hJ
    · have hodd : Odd (p ^ a) := (hp'.odd_of_ne_two hp2).pow
      have hidx := hp.relIndex_eq_two_of_dihedral hodd e
      obtain ⟨hP, hJ, -⟩ := hp.e2_10_six hidx
      have hne : p ^ a ≠ 1 := by
        have : 1 < p ^ a := Nat.one_lt_pow (by omega) hp'.one_lt
        omega
      exact hp.five_of_dihedral hP hJ hodd hne e
    · rcases hY with hY | ⟨-, ⟨e⟩⟩
      · have := hp.normal_P
        obtain ⟨hZ, hsq, hJ⟩ := hp.center_eight hY
        exact hp.five_of_center hZ hsq hJ
      · exact (hS6.false e).elim
  obtain ⟨hJ, h5b, h5c, h5d⟩ := h5
  exact ⟨hp, E2.e2_11_two h hI hVI, E2.e2_11_three h hI hJ, E2.e2_11_four h hI hS6 hg hgen hJ,
    hJ, h5b, h5c, h5d⟩

end CFSG.Quasithin
