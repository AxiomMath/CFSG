module

public import CFSG.RankThree.GF2n.Parrott.Section4CentreSylow
public import CFSG.RankThree.GF2n.Parrott.CaseIIDouble
public import CFSG.RankThree.GF2n.Parrott.LiftClaimC
public import CFSG.RankThree.GF2n.Parrott.Section4SpinGlue
public import CFSG.RankThree.GF2n.Parrott.SpinFixedCardMore
public import CFSG.RankThree.GF2n.Parrott.SpinConfig
public import CFSG.RankThree.GF2n.Parrott.ActionQAIdentificationOutsideEquality
public import CFSG.RankThree.GF2n.Parrott.ActionQAIdentification

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

section SylowProduct

variable [Fact (Nat.Prime 2)]

theorem relIndex_prod_top_eq {K Y : Subgroup G} (hYK : Y ≤ K) :
    (Y.prod (⊤ : Subgroup (Multiplicative (ZMod 2)))).relIndex
      (K.prod (⊤ : Subgroup (Multiplicative (ZMod 2)))) = Y.relIndex K := by
  have hle : Y.prod (⊤ : Subgroup (Multiplicative (ZMod 2))) ≤
      K.prod (⊤ : Subgroup (Multiplicative (ZMod 2))) := Subgroup.prod_mono hYK le_rfl
  have h1 : (Y.prod (⊤ : Subgroup (Multiplicative (ZMod 2)))).relIndex
        (K.prod (⊤ : Subgroup (Multiplicative (ZMod 2)))) *
        (K.prod (⊤ : Subgroup (Multiplicative (ZMod 2)))).relIndex ⊤ =
      (Y.prod (⊤ : Subgroup (Multiplicative (ZMod 2)))).relIndex ⊤ :=
    Subgroup.relIndex_mul_relIndex _ _ _ hle le_top
  rw [Subgroup.relIndex_top_right, Subgroup.relIndex_top_right, Subgroup.index_prod,
    Subgroup.index_prod, Subgroup.index_top, mul_one, mul_one] at h1
  have h2 : Y.relIndex K * K.index = Y.index := Subgroup.relIndex_mul_index hYK
  rw [← h2] at h1
  exact Nat.eq_of_mul_eq_mul_right
    (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := K))) h1

theorem isSylowOf_prod_top {K Y : Subgroup G} (hY : IsSylowOf 2 Y K) :
    IsSylowOf 2 (Y.prod (⊤ : Subgroup (Multiplicative (ZMod 2))))
      (K.prod (⊤ : Subgroup (Multiplicative (ZMod 2)))) := by
  rw [isSylowOf_iff]
  refine ⟨Subgroup.prod_mono hY.le le_rfl, ?_, ?_⟩
  · have htopcard : Nat.card (⊤ : Subgroup (Multiplicative (ZMod 2))) = 2 := by
      rw [Subgroup.card_top]
      simp
    obtain ⟨n, hn⟩ := hY.isPGroup.exists_card_eq
    apply IsPGroup.of_card (n := n + 1)
    rw [Nat.card_congr (Subgroup.prodEquiv Y ⊤).toEquiv, Nat.card_prod, hn, htopcard,
      pow_succ]
  · rw [relIndex_prod_top_eq hY.le]
    exact (isSylowOf_iff.mp hY).2.2

end SylowProduct

section PartOne


theorem exists_mul_inv_eq_of_fixDimV_eq_four_of_sq_mem (h : Tim79a.ParrottHyp z) {x : G}
    (hxH : x ∈ H z) (hxx : x * x ∈ J z) (hV : fixDimV h ⟨x, hxH⟩ = 4) {v : QuotientV.V z}
    (hv : conjV h ⟨x, hxH⟩ v = v) :
    ∃ u : QuotientV.V z, conjV h ⟨x, hxH⟩ u * u⁻¹ = v := by
  have hcomm : IsMulCommutative (QuotientV.V z) := QuotientV.isMulCommutative_V h
  have hc : ∀ a b : QuotientV.V z, a * b = b * a := fun a b => hcomm.is_comm.comm a b
  set σ : MulAut (QuotientV.V z) := conjV h ⟨x, hxH⟩ with hσ
  have hσσ : ∀ v, σ (σ v) = v := by
    intro v
    rw [hσ]
    exact conjV_conjV_of_sq_mem_J h hxH hxx v
  have hsq : ∀ v : QuotientV.V z, v * v = 1 := fun v => by
    have := QuotientV.pow_two_eq_one_V h v
    rwa [pow_two] at this
  let φ : QuotientV.V z →* QuotientV.V z :=
    MonoidHom.mk' (fun v => σ v * v⁻¹) (fun a b => by
      simp only [map_mul, mul_inv_rev]
      calc σ a * σ b * (b⁻¹ * a⁻¹) = σ a * ((σ b * b⁻¹) * a⁻¹) := by group
        _ = σ a * (a⁻¹ * (σ b * b⁻¹)) := by rw [hc (σ b * b⁻¹) a⁻¹]
        _ = σ a * a⁻¹ * (σ b * b⁻¹) := by group)
  have hker : ∀ v, v ∈ φ.ker ↔ σ v = v := by
    intro v
    rw [MonoidHom.mem_ker]
    exact mul_inv_eq_one
  have hkerEq : φ.ker = autFixedSubgroup σ := Subgroup.ext fun v => by
    rw [hker, mem_autFixedSubgroup]
  have hkcard : Nat.card φ.ker = 2 ^ 4 := by
    rw [hkerEq, card_fix h ⟨x, hxH⟩, hV]
  have hrle : φ.range ≤ φ.ker := by
    rintro _ ⟨v, rfl⟩
    rw [hker]
    show σ (σ v * v⁻¹) = σ v * v⁻¹
    rw [map_mul, map_inv, hσσ]
    have h1 : v = v⁻¹ := (inv_eq_of_mul_eq_one_left (hsq v)).symm
    have h2 : σ v = (σ v)⁻¹ := (inv_eq_of_mul_eq_one_left (hsq (σ v))).symm
    rw [← h1, ← h2]
    exact hc _ _
  have hcard : Nat.card φ.ker * Nat.card φ.range = 2 ^ 8 := by
    rw [Subgroup.card_ker_mul_card_range φ, QuotientV.card_V h]
  have hrcard : Nat.card φ.range = 2 ^ 4 := by
    rw [hkcard] at hcard
    omega
  have hreq : φ.range = φ.ker :=
    Subgroup.eq_of_le_of_card_ge hrle (by rw [hkcard, hrcard])
  have hvker : v ∈ φ.ker := (hker v).mpr hv
  rw [← hreq] at hvker
  exact hvker

theorem exists_involution_lift_of_fixed_of_qVZMod_eq_zero_of_sq_mem (h : Tim79a.ParrottHyp z)
    {x : G} (hxH : x ∈ H z) (hxx : x * x ∈ centerIn (J z)) (hV : fixDimV h ⟨x, hxH⟩ = 4)
    {v : QuotientV.V z} (hv : conjV h ⟨x, hxH⟩ v = v) (hq : qVZMod h v = 0) :
    ∃ (j : G) (hj : j ∈ J z), QuotientV.pi z ⟨j, hj⟩ = v ∧ j * j = 1 ∧ x * j = j * x := by
  have hxxJ : x * x ∈ J z := (inf_le_left : centerIn (J z) ≤ J z) hxx
  obtain ⟨ū, hū⟩ := exists_mul_inv_eq_of_fixDimV_eq_four_of_sq_mem h hxH hxxJ hV hv
  obtain ⟨u, rfl⟩ := QuotientV.pi_surjective z ū
  let c : G := x * x
  have hc : x * x = c := rfl
  have hcJ : c ∈ centerIn (J z) := hc ▸ hxx
  have hcu : c * (u : G) = (u : G) * c :=
    (Subgroup.mem_centralizer_iff.mp hcJ.2 (u : G) u.2).symm
  have hcxinv : c * x⁻¹ = x := by
    rw [show c = x * x from hc.symm]
    group
  let j' : J z := conjJ' z ⟨x, hxH⟩ u * u⁻¹
  have hj'G : (j' : G) = x * (u : G) * x⁻¹ * (u : G)⁻¹ := by
    simp only [j', Subgroup.coe_mul, Subgroup.coe_inv, conjJ'_apply_coe]
  have hpi : QuotientV.pi z j' = v := by
    show QuotientV.pi z (conjJ' z ⟨x, hxH⟩ u * u⁻¹) = v
    rw [map_mul, map_inv, ← conjV_mk h ⟨x, hxH⟩ u]
    exact hū
  have hsq : (j' : G) * (j' : G) = 1 := by
    have h1 : ((qV h (QuotientV.pi z j') : Subgroup.zpowers z) : G) = 1 := by
      rw [hpi, (qVZMod_eq_zero_iff h v).mp hq]
      rfl
    rw [qV_pi_coe, pow_two] at h1
    exact h1
  have hxjx : x * (j' : G) * x⁻¹ = (j' : G)⁻¹ := by
    rw [hj'G]
    calc x * (x * (u : G) * x⁻¹ * (u : G)⁻¹) * x⁻¹
        = (x * x) * (u : G) * x⁻¹ * (u : G)⁻¹ * x⁻¹ := by group
      _ = c * (u : G) * x⁻¹ * (u : G)⁻¹ * x⁻¹ := by rw [hc]
      _ = (u : G) * c * x⁻¹ * (u : G)⁻¹ * x⁻¹ := by rw [hcu]
      _ = (u : G) * x * (u : G)⁻¹ * x⁻¹ := by
          have hmove : (u : G) * c * x⁻¹ = (u : G) * x := by
            rw [mul_assoc, hcxinv]
          rw [hmove]
      _ = (x * (u : G) * x⁻¹ * (u : G)⁻¹)⁻¹ := by group
  have hjinv : (j' : G)⁻¹ = (j' : G) := inv_eq_of_mul_eq_one_right hsq
  refine ⟨(j' : G), j'.2, hpi, hsq, ?_⟩
  rw [hjinv] at hxjx
  exact mul_inv_eq_iff_eq_mul.mp hxjx

end PartOne

section Centre


theorem mem_J_or_mul_of_mem_centre_sylow_of_sq_mem
    (D : QuotientData (z := z) (J_subgroupOf_normal z)) (h : Tim79a.ParrottHyp z) {x : G}
    (hxH : x ∈ H z) (hxx : x * x ∈ centerIn (J z)) (hV : fixDimV h ⟨x, hxH⟩ = 4)
    (hV4 : ∀ y : ↥(H z), qH D ⟨x, hxH⟩ * qH D y = qH D y * qH D ⟨x, hxH⟩ →
      (∀ v : QuotientV.V z, conjV h ⟨x, hxH⟩ v = v → qVZMod h v = 0 → conjV h y v = v) →
        qH D y = 1 ∨ qH D y = qH D ⟨x, hxH⟩)
    {Y : Subgroup G} (hY : IsSylowOf 2 Y (H z ⊓ centralizer ({x} : Set G))) :
    ∀ w ∈ Y ⊓ centralizer (Y : Set G), w ∈ J z ∨ ∃ j ∈ J z, w = x * j := by
  intro w hw
  obtain ⟨hwY, hwc⟩ := mem_inf.mp hw
  obtain ⟨hwH, hwx⟩ := mem_inf.mp (hY.le hwY)
  have hHN : H z ≤ normalizer (J z : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (J_le_H (z := z))).mp (J_subgroupOf_normal z)
  have hJY : J z ⊓ centralizer ({x} : Set G) ≤ Y := by
    refine le_isSylowOf_of_isPGroup_of_le_normalizer hY
      (fun j hj => mem_inf.mpr ⟨J_le_H hj.1, hj.2⟩) ?_ (isPGroup_J h).to_inf_left
    have key : ∀ c ∈ H z ⊓ centralizer ({x} : Set G), ∀ j ∈ J z ⊓ centralizer ({x} : Set G),
        c * j * c⁻¹ ∈ J z ⊓ centralizer ({x} : Set G) := by
      intro c hc j hj
      refine mem_inf.mpr ⟨(mem_normalizer_iff.mp (hHN hc.1) j).mp hj.1, ?_⟩
      rw [mem_centralizer_singleton_iff]
      have hcx : c * x = x * c := mem_centralizer_singleton_iff.mp hc.2
      have hjx : j * x = x * j := mem_centralizer_singleton_iff.mp hj.2
      have hcx' : c⁻¹ * x = x * c⁻¹ := by
        calc c⁻¹ * x = c⁻¹ * (x * c) * c⁻¹ := by group
          _ = c⁻¹ * (c * x) * c⁻¹ := by rw [hcx]
          _ = x * c⁻¹ := by group
      calc c * j * c⁻¹ * x = c * j * (c⁻¹ * x) := by group
        _ = c * j * (x * c⁻¹) := by rw [hcx']
        _ = c * (j * x) * c⁻¹ := by group
        _ = c * (x * j) * c⁻¹ := by rw [hjx]
        _ = (c * x) * j * c⁻¹ := by group
        _ = (x * c) * j * c⁻¹ := by rw [hcx]
        _ = x * (c * j * c⁻¹) := by group
    intro c hc
    rw [mem_normalizer_iff]
    intro j
    refine ⟨key c hc j, fun hj => ?_⟩
    have h1 := key c⁻¹ (inv_mem hc) _ hj
    simpa [mul_assoc] using h1
  have hfix : ∀ v : QuotientV.V z, conjV h ⟨x, hxH⟩ v = v → qVZMod h v = 0 →
      conjV h ⟨w, hwH⟩ v = v := by
    intro v hv hq
    obtain ⟨j, hj, hjv, hjj, hxj⟩ :=
      exists_involution_lift_of_fixed_of_qVZMod_eq_zero_of_sq_mem h hxH hxx hV hv hq
    have hjY : j ∈ Y := hJY (mem_inf.mpr ⟨hj, mem_centralizer_singleton_iff.mpr hxj.symm⟩)
    have hjw : j * w = w * j := mem_centralizer_iff.mp hwc j hjY
    rw [← hjv, conjV_mk]
    congr 1
    apply Subtype.ext
    rw [conjJ'_apply_coe]
    calc w * j * w⁻¹ = j * w * w⁻¹ := by rw [← hjw]
      _ = j := by group
  have hcomm : qH D ⟨x, hxH⟩ * qH D ⟨w, hwH⟩ = qH D ⟨w, hwH⟩ * qH D ⟨x, hxH⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact (mem_centralizer_singleton_iff.mp hwx).symm
  rcases hV4 ⟨w, hwH⟩ hcomm hfix with h1 | h1
  · exact Or.inl ((J_mem_iff D _).mpr h1)
  · right
    have h2 : qH D ((⟨x, hxH⟩ : ↥(H z))⁻¹ * ⟨w, hwH⟩) = 1 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : x⁻¹ * w ∈ J z := (J_mem_iff D _).mpr h2
    exact ⟨x⁻¹ * w, h3, by group⟩

end Centre

section PartTwo


theorem mem_J_or_mul_of_mem_centre_sylow_uv_A (h : Tim79a.ParrottHypA z)
    (D : QuotientData (z := z) (J_subgroupOf_normal z))
    (hIII : ¬ ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂)
    {x : G} (hxH : x ∈ H z) (hxx : x * x ∈ zpowers z)
    (hxuv : IsConj (qH D ⟨x, hxH⟩)
      ((⟨u, u_mem_A⟩ : ↥QA45.originalSubgroup) * ⟨v, v_mem_A⟩))
    {Y : Subgroup G} (hY : IsSylowOf 2 Y (H z ⊓ centralizer ({x} : Set G))) :
    ∀ w ∈ Y ⊓ centralizer (Y : Set G), w ∈ J z ∨ ∃ j ∈ J z, w = x * j := by
  let h2 : Tim79a.ParrottHyp (CaseIIDouble.zz z) := CaseIIDouble.parrottHyp_zz h
  let D2 : QuotientData (z := CaseIIDouble.zz z) (J_subgroupOf_normal (CaseIIDouble.zz z)) :=
    CaseIIDouble.quotientDataZZ D
  have hIII2 : ¬ ParrottEqualityBranch (z := CaseIIDouble.zz z) (D := D2) h2 :=
    fun hb => hIII ((CaseIIDouble.parrottEqualityBranch_zz_iff h2 D).mp hb)
  obtain ⟨P, -, hP⟩ := (generatorConjugacy_iff_actionQA45_eq_conj_rhoAct h2 D2).mp
    (generatorConjugacy_of_not_equalityBranch h2 D2 hIII2)
  have hP' : ∀ a : A45, actionQA45 (z := CaseIIDouble.zz z) h2 D2 a = P * rhoA a * P⁻¹ :=
    fun a => by simpa [rhoA, toQAct] using hP a
  have hx'H : ((x, 1) : CaseIIDouble.D2 G) ∈ H (CaseIIDouble.zz z) :=
    CaseIIDouble.mk_mem_H_zz hxH
  have hqx' : qH D2 ⟨((x, 1) : CaseIIDouble.D2 G), hx'H⟩ = qH D ⟨x, hxH⟩ := by
    rw [CaseIIDouble.qH_zz D x 1 hx'H]
  have hxuv' : IsConj (qH D2 ⟨((x, 1) : CaseIIDouble.D2 G), hx'H⟩) (uA * vA) := by
    rw [hqx']
    exact hxuv
  have hxx' : ((x, 1) : CaseIIDouble.D2 G) * ((x, 1) : CaseIIDouble.D2 G) ∈
      centerIn (J (CaseIIDouble.zz z)) := by
    rw [CaseIIDouble.centerIn_J_zz, Subgroup.mem_prod]
    refine ⟨?_, Subgroup.mem_top _⟩
    rw [centerIn_J_eq_zpowers_A h]
    simpa using hxx
  have hV : fixDimV h2 ⟨((x, 1) : CaseIIDouble.D2 G), hx'H⟩ = 4 := by
    have hV2 := fixDimV_eq_of_conj_rep D2 h2 rhoA P hP' (fun a => IsConj a (uA * vA)) 4
      (fun a ha => by simpa using spinFixedCard_uv a ha)
    exact hV2 _ hxuv'
  have hV4 : ∀ y : ↥(H (CaseIIDouble.zz z)),
      qH D2 ⟨((x, 1) : CaseIIDouble.D2 G), hx'H⟩ * qH D2 y =
        qH D2 y * qH D2 ⟨((x, 1) : CaseIIDouble.D2 G), hx'H⟩ →
      (∀ v : QuotientV.V (CaseIIDouble.zz z),
        conjV h2 ⟨((x, 1) : CaseIIDouble.D2 G), hx'H⟩ v = v → qVZMod h2 v = 0 →
          conjV h2 y v = v) →
        qH D2 y = 1 ∨ qH D2 y = qH D2 ⟨((x, 1) : CaseIIDouble.D2 G), hx'H⟩ :=
    fun y' => fixed_space_faithful_of_spin D2 h2 P hP' spinFaithful_uv
      ⟨((x, 1) : CaseIIDouble.D2 G), hx'H⟩ y' hxuv'
  have hK : H (CaseIIDouble.zz z) ⊓ centralizer ({((x, 1) : CaseIIDouble.D2 G)} :
        Set (CaseIIDouble.D2 G)) =
      (H z ⊓ centralizer ({x} : Set G)).prod (⊤ : Subgroup (Multiplicative (ZMod 2))) := by
    rw [CaseIIDouble.H_zz]
    ext p
    constructor
    · intro hp
      obtain ⟨hp1, hpc⟩ := Subgroup.mem_inf.mp hp
      obtain ⟨hp1H, -⟩ := Subgroup.mem_prod.mp hp1
      refine Subgroup.mem_prod.mpr ⟨Subgroup.mem_inf.mpr ⟨hp1H, ?_⟩, Subgroup.mem_top p.2⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hpc ⊢
      exact congrArg Prod.fst hpc
    · intro hp
      obtain ⟨hp1, hp2⟩ := Subgroup.mem_prod.mp hp
      obtain ⟨hp1H, hp1c⟩ := Subgroup.mem_inf.mp hp1
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_prod.mpr ⟨hp1H, Subgroup.mem_top p.2⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hp1c ⊢
      ext
      · simpa using hp1c
      · simp
  have hY' : IsSylowOf 2 (Y.prod (⊤ : Subgroup (Multiplicative (ZMod 2))))
      (H (CaseIIDouble.zz z) ⊓ centralizer ({((x, 1) : CaseIIDouble.D2 G)} :
        Set (CaseIIDouble.D2 G))) := by
    rw [hK]
    exact isSylowOf_prod_top hY
  intro w hw
  obtain ⟨hwY, hwc⟩ := Subgroup.mem_inf.mp hw
  have hw'Y : ((w, 1) : CaseIIDouble.D2 G) ∈
      Y.prod (⊤ : Subgroup (Multiplicative (ZMod 2))) :=
    Subgroup.mem_prod.mpr ⟨hwY, Subgroup.mem_top _⟩
  have hw'c : ((w, 1) : CaseIIDouble.D2 G) ∈
      centralizer ((Y.prod (⊤ : Subgroup (Multiplicative (ZMod 2))) :
        Subgroup (CaseIIDouble.D2 G)) : Set (CaseIIDouble.D2 G)) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro ⟨y, c⟩ hy
    obtain ⟨hyY, -⟩ := Subgroup.mem_prod.mp hy
    have hcomm := Subgroup.mem_centralizer_iff.mp hwc y hyY
    exact Prod.ext hcomm (by simp)
  have hmem : ((w, 1) : CaseIIDouble.D2 G) ∈
      Y.prod (⊤ : Subgroup (Multiplicative (ZMod 2))) ⊓
        centralizer ((Y.prod (⊤ : Subgroup (Multiplicative (ZMod 2))) :
          Subgroup (CaseIIDouble.D2 G)) : Set (CaseIIDouble.D2 G)) :=
    Subgroup.mem_inf.mpr ⟨hw'Y, hw'c⟩
  have hres := mem_J_or_mul_of_mem_centre_sylow_of_sq_mem (z := CaseIIDouble.zz z) D2 h2
    hx'H hxx' hV hV4 hY' ((w, 1) : CaseIIDouble.D2 G) hmem
  rcases hres with hJ | ⟨jj, hjjJ, hjeq⟩
  · exact Or.inl (CaseIIDouble.mem_J_of_zz hJ)
  · right
    refine ⟨(jj : CaseIIDouble.D2 G).1, CaseIIDouble.mem_J_of_zz hjjJ, ?_⟩
    have hfirst := congrArg Prod.fst hjeq
    simpa using hfirst

theorem exists_uv_lift_sq_mem_A (h : Tim79a.ParrottHypA z)
    (D : QuotientData (z := z) (J_subgroupOf_normal z))
    (hIII : ¬ ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂) :
    ∃ (x : G) (hxH : x ∈ H z), x * x ∈ zpowers z ∧
      qH D ⟨x, hxH⟩ = (⟨u, u_mem_A⟩ : ↥QA45.originalSubgroup) * ⟨v, v_mem_A⟩ := by
  let h2 : Tim79a.ParrottHyp (CaseIIDouble.zz z) := CaseIIDouble.parrottHyp_zz h
  let D2 : QuotientData (z := CaseIIDouble.zz z) (J_subgroupOf_normal (CaseIIDouble.zz z)) :=
    CaseIIDouble.quotientDataZZ D
  have hIII2 : ¬ ParrottEqualityBranch (z := CaseIIDouble.zz z) (D := D2) h2 :=
    fun hb => hIII ((CaseIIDouble.parrottEqualityBranch_zz_iff h2 D).mp hb)
  obtain ⟨P, -, hP⟩ := (generatorConjugacy_iff_actionQA45_eq_conj_rhoAct h2 D2).mp
    (generatorConjugacy_of_not_equalityBranch h2 D2 hIII2)
  have hP' : ∀ a : A45, actionQA45 (z := CaseIIDouble.zz z) h2 D2 a = P * rhoA a * P⁻¹ :=
    fun a => by simpa [rhoA, toQAct] using hP a
  obtain ⟨x₀, hx₀q⟩ := qH_surjective D (uA * vA)
  have hx₀sqJ : (x₀ : G) * x₀ ∈ J z := by
    have h1 : (x₀ * x₀ : ↥(H z)) ∈ (J z).subgroupOf (H z) :=
      (J_mem_iff D _).mpr (by rw [map_mul, hx₀q, uv_mul_self_A])
    exact Subgroup.mem_subgroupOf.mp h1
  let x₀' : ↥(H (CaseIIDouble.zz z)) :=
    ⟨((x₀ : G), 1), CaseIIDouble.mk_mem_H_zz x₀.2⟩
  have hx₀'q : qH D2 x₀' = qH D x₀ := by
    have hzz := CaseIIDouble.qH_zz D (x₀ : G) 1 x₀'.2
    rw [hzz]
  have hx₀'uv : IsConj (qH D2 x₀') (uA * vA) := by
    rw [hx₀'q, hx₀q]
  have hV₀ : fixDimV h2 x₀' = 4 := by
    have hV2 := fixDimV_eq_of_conj_rep D2 h2 rhoA P hP' (fun a => IsConj a (uA * vA)) 4
      (fun a ha => by simpa using spinFixedCard_uv a ha)
    exact hV2 _ hx₀'uv
  have hx₀'sqJ : ((x₀' : CaseIIDouble.D2 G) * x₀') ∈ J (CaseIIDouble.zz z) := by
    show ((x₀ : G), (1 : Multiplicative (ZMod 2))) *
        ((x₀ : G), (1 : Multiplicative (ZMod 2))) ∈ J (CaseIIDouble.zz z)
    rw [CaseIIDouble.J_zz, Subgroup.mem_prod]
    refine ⟨?_, Subgroup.mem_top _⟩
    simpa using hx₀sqJ
  obtain ⟨jj, hjjJ, hjj_sq⟩ := exists_lift_sq_mem_centerIn h2 x₀' hV₀ hx₀'sqJ
  refine ⟨(x₀ : G) * (jj : CaseIIDouble.D2 G).1,
    (H z).mul_mem x₀.2 (J_le_H (CaseIIDouble.mem_J_of_zz hjjJ)), ?_, ?_⟩
  · have hcenter : ((x₀ : G) * (jj : CaseIIDouble.D2 G).1) *
        ((x₀ : G) * (jj : CaseIIDouble.D2 G).1) ∈ centerIn (J z) := by
      have h := hjj_sq
      rw [CaseIIDouble.centerIn_J_zz, Subgroup.mem_prod] at h
      exact h.1
    rwa [centerIn_J_eq_zpowers_A h] at hcenter
  · have hmem : (⟨(x₀ : G) * (jj : CaseIIDouble.D2 G).1,
        (H z).mul_mem x₀.2 (J_le_H (CaseIIDouble.mem_J_of_zz hjjJ))⟩ : ↥(H z)) =
        x₀ * ⟨(jj : CaseIIDouble.D2 G).1,
          J_le_H (CaseIIDouble.mem_J_of_zz hjjJ)⟩ := Subtype.ext rfl
    rw [hmem, map_mul, hx₀q]
    have hqj : qH D ⟨(jj : CaseIIDouble.D2 G).1,
        J_le_H (CaseIIDouble.mem_J_of_zz hjjJ)⟩ = 1 :=
      (J_mem_iff D _).mp (Subgroup.mem_subgroupOf.mpr (CaseIIDouble.mem_J_of_zz hjjJ))
    rw [hqj, mul_one]

end PartTwo

end CFSG.RankThree.GF2n.Parrott
