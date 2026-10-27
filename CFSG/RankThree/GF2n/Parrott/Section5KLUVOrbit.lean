module

public import CFSG.RankThree.GF2n.Parrott.Section5KLFixed
public import CFSG.RankThree.GF2n.Parrott.Section5LocalW
public import CFSG.RankThree.GF2n.Parrott.CentralizerJoinH

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal] (D : QuotientData (z := z) hN)

local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "s2A" => (⟨sigma2, sigma2_mem_A⟩ : A45)

omit [Finite G]
  in
private theorem ncard_conj_orbit_mul_card_centralizer_kl (Q : Subgroup G) (x : G) :
    (Set.image (fun q : Q => (q : G) * x * (q : G)⁻¹) Set.univ).ncard *
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({x} : Set G)) = Nat.card Q := by
  let : MulAction Q G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp Q.subtype)
  have hsmul : ∀ q : Q, q • x = (q : G) * x * (q : G)⁻¹ := by
    intro q
    simp only [MulAction.compHom_smul_def, MulAut.smul_def, MonoidHom.comp_apply,
      Subgroup.coe_subtype, MulAut.conj_apply]
  have horbit : Set.image (fun q : Q => (q : G) * x * (q : G)⁻¹) Set.univ =
      MulAction.orbit Q x := by
    ext y
    simp only [Set.mem_image, Set.mem_univ, true_and, MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q, (hsmul q).symm⟩
    · rintro ⟨q, rfl⟩
      exact ⟨q, hsmul q⟩
  rw [horbit]
  have hstab : Nat.card ↥(MulAction.stabilizer Q x) =
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({x} : Set G)) := by
    refine Nat.card_congr ?_
    refine
      { toFun := fun y =>
          ⟨(y.1 : G), y.1.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        invFun := fun z =>
          ⟨⟨(z.1 : G), z.2.1⟩, ?_⟩
        left_inv := ?_
        right_inv := ?_ }
    · have h := MulAction.mem_stabilizer_iff.mp y.2
      rw [hsmul] at h
      exact mul_inv_eq_iff_eq_mul.mp h
    · rw [MulAction.mem_stabilizer_iff, hsmul]
      exact mul_inv_eq_of_eq_mul (Subgroup.mem_centralizer_singleton_iff.mp z.2.2)
    · intro y
      apply Subtype.ext
      rfl
    · intro z
      apply Subtype.ext
      rfl
  rw [← hstab, Nat.mul_comm, ← MulAction.index_stabilizer Q x]
  exact Subgroup.card_mul_index _

theorem exists_conj_eq_mul_of_qH_eq_uv (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {x : ↥(H z)}
    (hxσ : (x : G) ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (hx2 : x * x = 1) (hqx : qH (z := z) D x = uA * vA) {c : G}
    (hc : c ∈ J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
      centralizer ({(x : G)} : Set G)) :
    ∃ q ∈ J z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G),
      q * (x : G) * q⁻¹ = (x : G) * c := by
  let σ : G := ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)
  let Q₀ : Subgroup G := J z ⊓ centralizer ({σ} : Set G)
  let C : Subgroup G := Q₀ ⊓ centralizer ({(x : G)} : Set G)
  change ∃ q ∈ Q₀, q * (x : G) * q⁻¹ = (x : G) * c
  have hQ₀card : Nat.card Q₀ = 64 := by
    simpa [Q₀, σ] using card_J_inf_centralizer_sigma1Nine_mul_inv_eq (D := D) h P hP hσ₂ hq₂ hc₂
  have hCcard : Nat.card C = 8 := by
    simpa [C, Q₀, σ] using
      card_J_inf_centralizer_inf_centralizer_eq_eight (D := D) h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂
        hxσ hx2 (Or.inl hqx)
  have hx2' : (x : G) * (x : G) = 1 := by simpa using congrArg Subtype.val hx2
  have hxH : (x : G) ∈ H z := x.2
  have hsub : Set.image (fun q : Q₀ => (q : G) * (x : G) * (q : G)⁻¹) Set.univ ⊆
      Set.image (fun c : G => (x : G) * c) (C : Set G) := by
    rintro y ⟨q, -, rfl⟩
    obtain ⟨hqJ, hqσ⟩ := Subgroup.mem_inf.mp q.2
    have hqH : (q : G) ∈ H z := J_le_H hqJ
    set c' : G := (x : G)⁻¹ * (q : G) * (x : G) * (q : G)⁻¹ with hc'def
    have hc'J : c' ∈ J z := by
      have h1 : (x : G)⁻¹ * (q : G) * (x : G) ∈ J z := by
        have h2 := (Subgroup.mem_normalizer_iff.mp (J_le_normalizer_A ((H z).inv_mem hxH))
          (q : G)).mp hqJ
        simpa using h2
      rw [hc'def]
      exact (J z).mul_mem h1 ((J z).inv_mem hqJ)
    have hc'σ : c' ∈ centralizer ({σ} : Set G) := by
      rw [hc'def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.inv_mem _ hxσ) hqσ) hxσ) (Subgroup.inv_mem _ hqσ)
    have hxc' : (x : G) * c' = (q : G) * (x : G) * (q : G)⁻¹ := by
      rw [hc'def]; group
    have hqinv2 : ((q : G) * (x : G) * (q : G)⁻¹) * ((q : G) * (x : G) * (q : G)⁻¹) = 1 := by
      have h3 : ((q : G) * (x : G) * (q : G)⁻¹) * ((q : G) * (x : G) * (q : G)⁻¹) =
          (q : G) * ((x : G) * (x : G)) * (q : G)⁻¹ := by group
      rw [h3, hx2']; group
    have hsq : ((x : G) * c') * ((x : G) * c') = 1 := by
      rw [hxc']; exact hqinv2
    have hxc'x : (x : G) * c' * (x : G) = c'⁻¹ := by
      calc (x : G) * c' * (x : G) = ((x : G) * c' * ((x : G) * c')) * c'⁻¹ := by group
        _ = 1 * c'⁻¹ := by rw [hsq]
        _ = c'⁻¹ := one_mul _
    have hfix : conjV h x (QuotientV.pi z ⟨c', hc'J⟩) = QuotientV.pi z ⟨c', hc'J⟩ := by
      rw [conjV_mk]
      have hval : ((conjJ' z x ⟨c', hc'J⟩ : J z) : G) = c'⁻¹ := by
        rw [conjJ'_apply_coe]
        have hxinv : (x : G)⁻¹ = (x : G) := inv_eq_of_mul_eq_one_right hx2'
        rw [hxinv]
        exact hxc'x
      have heq : conjJ' z x ⟨c', hc'J⟩ = ⟨c'⁻¹, (J z).inv_mem hc'J⟩ := Subtype.ext hval
      rw [heq]
      have heq2 : (⟨c'⁻¹, (J z).inv_mem hc'J⟩ : J z) = ⟨c', hc'J⟩⁻¹ := rfl
      rw [heq2, map_inv]
      exact inv_eq_of_mul_eq_one_right
        (by simpa [pow_two] using QuotientV.pow_two_eq_one_V h (QuotientV.pi z ⟨c', hc'J⟩))
    have hmul : c' * c' = 1 := by
      have h4 := mul_self_eq_one_of_conjV_pi_eq_of_qH_eq_uv (z := z) D h P hP hq₂ hqx
        (b := ⟨c', hc'J⟩) hc'σ hfix
      simpa using h4
    have hcinv : c'⁻¹ = c' := inv_eq_of_mul_eq_one_right hmul
    have hcomm : c' * (x : G) = (x : G) * c' := by
      have h5 : (x : G) * c' * (x : G) = c' := by rw [hxc'x, hcinv]
      calc c' * (x : G) = ((x : G) * (x : G)) * (c' * (x : G)) := by rw [hx2', one_mul]
        _ = (x : G) * ((x : G) * c' * (x : G)) := by group
        _ = (x : G) * c' := by rw [h5]
    refine ⟨c', ?_, hxc'⟩
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_inf.mpr ⟨hc'J, hc'σ⟩, Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
  have hcount : (Set.image (fun q : Q₀ => (q : G) * (x : G) * (q : G)⁻¹) Set.univ).ncard *
      Nat.card C = Nat.card Q₀ :=
    ncard_conj_orbit_mul_card_centralizer_kl (Q := Q₀) (x := (x : G))
  rw [hQ₀card, hCcard] at hcount
  have hOcard : (Set.image (fun q : Q₀ => (q : G) * (x : G) * (q : G)⁻¹) Set.univ).ncard = 8 := by
    omega
  have himgcard : (Set.image (fun c : G => (x : G) * c) (C : Set G)).ncard = 8 := by
    rw [Set.ncard_image_of_injective _ (fun a b hab => mul_left_cancel hab)]
    exact (Nat.card_coe_set_eq (C : Set G)).symm.trans hCcard
  have heq : Set.image (fun q : Q₀ => (q : G) * (x : G) * (q : G)⁻¹) Set.univ =
      Set.image (fun c : G => (x : G) * c) (C : Set G) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [himgcard, hOcard])
  have hcC : c ∈ C := hc
  have hmem : (x : G) * c ∈ Set.image (fun c : G => (x : G) * c) (C : Set G) :=
    ⟨c, hcC, rfl⟩
  rw [← heq] at hmem
  obtain ⟨q, -, hq⟩ := hmem
  exact ⟨(q : G), q.2, hq⟩

theorem exists_mem_centralizer_qH_eq_t_of_qH_eq_uv (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {x : ↥(H z)}
    (hxσ : (x : G) ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (hx2 : x * x = 1) (hqx : qH (z := z) D x = uA * vA) :
    ∃ k : ↥(H z),
      (k : G) ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ∧
        (k : G) ∈ centralizer ({(x : G)} : Set G) ∧ qH (z := z) D k = tA := by
  let σh : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  let σ : G := (σh : G)
  have hx2' : (x : G) * (x : G) = 1 := by simpa using congrArg Subtype.val hx2
  have hqσ : qH (z := z) D σh = (⟨sigma1, sigma1_mem_A⟩ : A45) * s2A⁻¹ := by
    show qH (z := z) D (sigma1Nine (z := z) D * σ₂⁻¹) = _
    rw [map_mul, map_inv, qH_sigma1Nine, hq₂]
  have hσ3 : orderOf σh = 3 := by
    have h1 : orderOf (σh : G) = 3 :=
      orderOf_sigma1Nine_mul_inv (z := z) D h hσ₂ hq₂ hc₂
    have h2 : orderOf (σh : G) = orderOf σh :=
      orderOf_injective (H z).subtype (H z).subtype_injective σh
    rw [h2] at h1
    exact h1
  have htcomm : tA * ((⟨sigma1, sigma1_mem_A⟩ : A45) * s2A⁻¹) =
      ((⟨sigma1, sigma1_mem_A⟩ : A45) * s2A⁻¹) * tA := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    decide +kernel
  obtain ⟨y, hqy, hyσ⟩ := exists_lift_centralizer (z := z) (D := D)
    (r := sigma1Nine (z := z) D * σ₂⁻¹) (g := tA) hσ3 (by rw [hqσ]; exact htcomm)
  set yx : G := (y : G) * (x : G) * (y : G)⁻¹ with hyxdef
  have hyxH : yx ∈ H z := (H z).mul_mem ((H z).mul_mem y.2 x.2) ((H z).inv_mem y.2)
  have hyx2 : yx * yx = 1 := by
    rw [hyxdef]
    rw [show ((y : G) * (x : G) * (y : G)⁻¹) * ((y : G) * (x : G) * (y : G)⁻¹) =
      (y : G) * ((x : G) * (x : G)) * (y : G)⁻¹ by group]
    rw [hx2', mul_one, mul_inv_cancel]
  set b : ↥(H z) := ⟨(x : G)⁻¹ * yx, (H z).mul_mem ((H z).inv_mem x.2) hyxH⟩ with hbdef
  have hbval : (b : G) = (x : G)⁻¹ * yx := rfl
  have hqyx : qH (z := z) D ⟨yx, hyxH⟩ = uA * vA := by
    have h1 : (⟨yx, hyxH⟩ : ↥(H z)) = y * x * y⁻¹ := Subtype.ext rfl
    rw [h1, map_mul, map_mul, map_inv, hqy, hqx]
    rw [show tA * (uA * vA) = (uA * vA) * tA from tA_mul_uvA_comm]
    group
  have hqb : qH (z := z) D b = 1 := by
    have h1 : b = (⟨(x : G), x.2⟩ : ↥(H z))⁻¹ * ⟨yx, hyxH⟩ := Subtype.ext rfl
    rw [h1, map_mul, map_inv, hqyx, hqx]
    group
  have hbJ : (b : G) ∈ J z := by
    have h1 : b ∈ (J z).subgroupOf (H z) := (J_mem_iff (z := z) D b).mpr hqb
    exact Subgroup.mem_subgroupOf.mp h1
  have hxσh : x ∈ centralizer ({σh} : Set ↥(H z)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hxσ)
  have hyσh : y ∈ centralizer ({σh} : Set ↥(H z)) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hyσ
  have hyxσh : (⟨yx, hyxH⟩ : ↥(H z)) ∈ centralizer ({σh} : Set ↥(H z)) := by
    have h1 : (⟨yx, hyxH⟩ : ↥(H z)) = y * x * y⁻¹ := Subtype.ext rfl
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hyσh hxσh) (Subgroup.inv_mem _ hyσh)
  have hbσh : b ∈ centralizer ({σh} : Set ↥(H z)) := by
    have h1 : b = (⟨(x : G), x.2⟩ : ↥(H z))⁻¹ * ⟨yx, hyxH⟩ := Subtype.ext rfl
    rw [h1]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hxσh) hyxσh
  have hbσ : (b : G) ∈ centralizer ({σ} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hbσh)
  have hbconj : (x : G) * (b : G) * (x : G)⁻¹ = (b : G)⁻¹ := by
    have hxinv : (x : G)⁻¹ = (x : G) := inv_eq_of_mul_eq_one_right hx2'
    have hyxinv : yx⁻¹ = yx := inv_eq_of_mul_eq_one_right hyx2
    rw [hbval, mul_inv_rev, hxinv, hyxinv, hxinv]
    calc (x : G) * ((x : G) * yx) * (x : G) =
        ((x : G) * (x : G)) * (yx * (x : G)) := by group
      _ = yx * (x : G) := by rw [hx2', one_mul]
  have hfix : conjV h x (QuotientV.pi z ⟨(b : G), hbJ⟩) = QuotientV.pi z ⟨(b : G), hbJ⟩ := by
    rw [conjV_mk]
    have hval : ((conjJ' z x ⟨(b : G), hbJ⟩ : J z) : G) = (b : G)⁻¹ := by
      rw [conjJ'_apply_coe]; exact hbconj
    have heq : conjJ' z x ⟨(b : G), hbJ⟩ = ⟨(b : G)⁻¹, (J z).inv_mem hbJ⟩ := Subtype.ext hval
    rw [heq]
    have heq2 : (⟨(b : G)⁻¹, (J z).inv_mem hbJ⟩ : J z) = ⟨(b : G), hbJ⟩⁻¹ := rfl
    rw [heq2, map_inv]
    exact inv_eq_of_mul_eq_one_right
      (by simpa [pow_two] using QuotientV.pow_two_eq_one_V h (QuotientV.pi z ⟨(b : G), hbJ⟩))
  have hbsq : (b : G) * (b : G) = 1 := by
    have h4 := mul_self_eq_one_of_conjV_pi_eq_of_qH_eq_uv (z := z) D h P hP hq₂ hqx
      (b := ⟨(b : G), hbJ⟩) hbσ hfix
    simpa using h4
  have hbx : (b : G) ∈ centralizer ({(x : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hbinv : (b : G)⁻¹ = (b : G) := inv_eq_of_mul_eq_one_right hbsq
    have hxinv : (x : G)⁻¹ = (x : G) := inv_eq_of_mul_eq_one_right hx2'
    have h5 : (x : G) * (b : G) * (x : G) = (b : G) := by
      calc (x : G) * (b : G) * (x : G) = (x : G) * (b : G) * (x : G)⁻¹ := by rw [hxinv]
        _ = (b : G) := by rw [hbconj, hbinv]
    calc (b : G) * (x : G) = ((x : G) * (x : G)) * ((b : G) * (x : G)) := by rw [hx2', one_mul]
      _ = (x : G) * ((x : G) * (b : G) * (x : G)) := by group
      _ = (x : G) * (b : G) := by rw [h5]
  have hc1 : (b : G) ∈ J z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({(x : G)} : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hbJ, hbσ⟩, hbx⟩
  obtain ⟨q, hqQ, hqxq⟩ := exists_conj_eq_mul_of_qH_eq_uv (z := z) D h hZ hz₁ hz₁z hord
    P hP hσ₂ hq₂ hc₂ hxσ hx2 hqx hc1
  obtain ⟨hqJ, hqσ⟩ := Subgroup.mem_inf.mp hqQ
  have hqH : (q : G) ∈ H z := J_le_H hqJ
  have hqinvH : (q : G)⁻¹ ∈ H z := (H z).inv_mem hqH
  have hkmem : (q : G)⁻¹ * (y : G) ∈ H z := (H z).mul_mem hqinvH y.2
  refine ⟨⟨(q : G)⁻¹ * (y : G), hkmem⟩, ?_, ?_, ?_⟩
  · have hqσh : (⟨(q : G), hqH⟩ : ↥(H z)) ∈ centralizer ({σh} : Set ↥(H z)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hqσ)
    have hkc : (⟨(q : G)⁻¹ * (y : G), hkmem⟩ : ↥(H z)) ∈ centralizer ({σh} : Set ↥(H z)) := by
      have hk : (⟨(q : G)⁻¹ * (y : G), hkmem⟩ : ↥(H z)) =
          (⟨(q : G), hqH⟩ : ↥(H z))⁻¹ * y := Subtype.ext rfl
      rw [hk]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hqσh) hyσh
    rw [Subgroup.mem_centralizer_singleton_iff] at hkc ⊢
    exact congrArg Subtype.val hkc
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have hqyx : (q : G) * (x : G) * (q : G)⁻¹ = yx := by
      rw [hqxq, hbval]; group
    have hconj : ((⟨(q : G)⁻¹ * (y : G), hkmem⟩ : ↥(H z)) : G) * (x : G) *
        ((⟨(q : G)⁻¹ * (y : G), hkmem⟩ : ↥(H z)) : G)⁻¹ = (x : G) := by
      show ((q : G)⁻¹ * (y : G)) * (x : G) * ((q : G)⁻¹ * (y : G))⁻¹ = (x : G)
      calc ((q : G)⁻¹ * (y : G)) * (x : G) * ((q : G)⁻¹ * (y : G))⁻¹
          = (q : G)⁻¹ * yx * (q : G) := by rw [hyxdef]; group
        _ = (q : G)⁻¹ * ((q : G) * (x : G) * (q : G)⁻¹) * (q : G) := by rw [← hqyx]
        _ = (x : G) := by group
    exact mul_inv_eq_iff_eq_mul.mp hconj
  · have hk : (⟨(q : G)⁻¹ * (y : G), hkmem⟩ : ↥(H z)) =
        (⟨(q : G)⁻¹, hqinvH⟩ : ↥(H z)) * y := Subtype.ext rfl
    rw [hk, map_mul, hqy]
    have hq1 : qH (z := z) D ⟨(q : G), hqH⟩ = 1 :=
      (J_mem_iff (z := z) D ⟨(q : G), hqH⟩).mp (Subgroup.mem_subgroupOf.mpr hqJ)
    have hqinv1 : qH (z := z) D ⟨(q : G)⁻¹, hqinvH⟩ = 1 := by
      rw [show (⟨(q : G)⁻¹, hqinvH⟩ : ↥(H z)) = (⟨(q : G), hqH⟩ : ↥(H z))⁻¹ from rfl,
        map_inv, hq1, inv_one]
    rw [hqinv1, one_mul]

omit [Finite G]
  in
private theorem lemma54T₂_le_H_kl {σ : G} {y : G} (hy : y ∈ lemma54T₂ D σ) : y ∈ H z :=
  (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hy).1).1

omit [Finite G]
  in
private theorem lemma54T₂_centralizes_kl {σ : G} {y : G} (hy : y ∈ lemma54T₂ D σ) :
    y ∈ centralizer ({σ} : Set G) :=
  (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hy).1).2

omit [Finite G]
  in
private theorem lemma54T₂_qH_mem_kl {σ : G} {y : G} (hy : y ∈ lemma54T₂ D σ) (hyH : y ∈ H z) :
    qH (z := z) D ⟨y, hyH⟩ ∈ Subgroup.closure ({tA, uA * vA} : Set A45) := by
  obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp hy).2
  rw [Subgroup.mem_comap] at hw
  rw [show (⟨y, hyH⟩ : ↥(H z)) = w from Subtype.ext hwy.symm]
  exact hw

private noncomputable def qHsub_kl (E : Subgroup G) (hE : E ≤ H z) : E →* A45 where
  toFun y := qH (z := z) D ⟨(y : G), hE y.2⟩
  map_one' := by
    rw [show (⟨((1 : E) : G), _⟩ : ↥(H z)) = 1 from Subtype.ext rfl, map_one]
  map_mul' a b := by
    rw [show (⟨((a * b : E) : G), _⟩ : ↥(H z)) =
      (⟨(a : G), _⟩ : ↥(H z)) * ⟨(b : G), _⟩ from Subtype.ext rfl, map_mul]

private theorem qHsub_ker_kl (E : Subgroup G) (hE : E ≤ H z) :
    (qHsub_kl (z := z) (D := D) E hE).ker = (J z).comap E.subtype := by
  ext y
  show qH (z := z) D ⟨(y : G), hE y.2⟩ = 1 ↔ (y : G) ∈ J z
  rw [← J_mem_iff (z := z) D ⟨(y : G), hE y.2⟩, Subgroup.mem_subgroupOf]

private theorem card_eq_card_inf_mul_card_range_kl (E : Subgroup G) (hE : E ≤ H z) :
    Nat.card E = Nat.card ↥(E ⊓ J z) * Nat.card ↥(qHsub_kl (z := z) (D := D) E hE).range := by
  have h := Subgroup.card_ker_mul_card_range (qHsub_kl (z := z) (D := D) E hE)
  rw [qHsub_ker_kl] at h
  have hker : Nat.card ↥((J z).comap E.subtype) = Nat.card ↥(E ⊓ J z) := by
    rw [Subgroup.comap_subtype, ← Subgroup.inf_subgroupOf_left (H := J z) (K := E)]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hker] at h
  exact h.symm

private theorem card_centralizer_s1s2inv_kl :
    Nat.card (Subgroup.centralizer ({(⟨sigma1, sigma1_mem_A⟩ : A45) * s2A⁻¹} : Set A45)) =
      108 := by
  have hm : sigma1 * sigma2⁻¹ ∈ QA45.originalSubgroup :=
    QA45.originalSubgroup.mul_mem sigma1_mem_A (QA45.originalSubgroup.inv_mem sigma2_mem_A)
  exact (card_centralizer_QA45_eq_filter (sigma1 * sigma2⁻¹) hm).trans
    Certificates.certificate946005.centralizer_sigma1sigma2inv

private theorem card_le_four_of_isPGroup_le_centralizer_kl (T : Subgroup A45)
    (hT : IsPGroup 2 T)
    (hle : T ≤ Subgroup.centralizer ({(⟨sigma1, sigma1_mem_A⟩ : A45) * s2A⁻¹} : Set A45)) :
    Nat.card T ≤ 4 := by
  have hdvd : Nat.card T ∣ 108 := by
    have h1 : Nat.card T ∣ Nat.card ↥(Subgroup.centralizer
        ({(⟨sigma1, sigma1_mem_A⟩ : A45) * s2A⁻¹} : Set A45)) := by
      have h2 := Subgroup.card_subgroup_dvd_card
        (T.subgroupOf (Subgroup.centralizer ({(⟨sigma1, sigma1_mem_A⟩ : A45) * s2A⁻¹} : Set A45)))
      rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h2
    rwa [card_centralizer_s1s2inv_kl] at h1
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq (p := 2) hT
  rw [hn] at hdvd ⊢
  have h3 : ¬ (3 ≤ n) := by
    intro h4
    have h8 : (8 : ℕ) ∣ 108 := (pow_dvd_pow 2 h4).trans hdvd
    norm_num at h8
  have h5 : n ≤ 2 := by omega
  calc 2 ^ n ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) h5
    _ = 4 := by norm_num

theorem isSylowOf_lemma54T₂_inf_centralizer_of_qH_eq_uv (h : Tim79a.ParrottHyp z)
    (hZ : centerIn (J z) ≠ centerIn (H z)) {z₁ : G} (hz₁ : z₁ ∈ centerIn (J z))
    (hz₁z : z₁ ∉ Subgroup.zpowers z) (hord : orderOf z₁ = 2)
    (P : GL8) (hP : ∀ a : A45, actionQA45 (z := z) h D a = P * rhoA a * P⁻¹)
    {σ₂ : ↥(H z)} (hσ₂ : orderOf σ₂ = 3) (hq₂ : qH (z := z) D σ₂ = s2A)
    (hc₂ : σ₂ * sigma1Nine (z := z) D = sigma1Nine (z := z) D * σ₂) {x : ↥(H z)}
    (hxσ : (x : G) ∈ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G))
    (hx2 : x * x = 1) (hqx : qH (z := z) D x = uA * vA) :
    IsSylowOf 2 (lemma54T₂ D ((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G) ⊓
        centralizer ({(x : G)} : Set G))
      (H z ⊓ centralizer ({((sigma1Nine (z := z) D * σ₂⁻¹ : ↥(H z)) : G)} : Set G) ⊓
        centralizer ({(x : G)} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let σh : ↥(H z) := sigma1Nine (z := z) D * σ₂⁻¹
  let σ : G := (σh : G)
  let Y : Subgroup G := H z ⊓ centralizer ({σ} : Set G)
  let Z : Subgroup G := Y ⊓ centralizer ({(x : G)} : Set G)
  let T₂ : Subgroup G := lemma54T₂ D σ
  let K₀ : Subgroup G := T₂ ⊓ centralizer ({(x : G)} : Set G)
  let C : Subgroup G := J z ⊓ centralizer ({σ} : Set G) ⊓ centralizer ({(x : G)} : Set G)
  change IsSylowOf 2 K₀ Z
  have hT : IsSylowOf 2 T₂ Y := by
    simpa [T₂, Y, σ, σh] using isSylowOf_lemma54T₂ (z := z) D h P hP hσ₂ hq₂ hc₂
  have hqσ : qH (z := z) D σh = (⟨sigma1, sigma1_mem_A⟩ : A45) * s2A⁻¹ := by
    show qH (z := z) D (sigma1Nine (z := z) D * σ₂⁻¹) = _
    rw [map_mul, map_inv, qH_sigma1Nine, hq₂]
  have hCcard : Nat.card C = 8 := by
    simpa [C, Y, σ, σh] using
      card_J_inf_centralizer_inf_centralizer_eq_eight (D := D) h hZ hz₁ hz₁z hord P hP
        hσ₂ hq₂ hc₂ hxσ hx2 (Or.inl hqx)
  have hK₀p : IsPGroup 2 K₀ := by
    simpa [K₀, T₂] using hT.isPGroup.to_inf_left (K := centralizer ({(x : G)} : Set G))
  have hK₀le : K₀ ≤ Z := by
    intro g hg
    obtain ⟨hgT, hgx⟩ := Subgroup.mem_inf.mp hg
    exact Subgroup.mem_inf.mpr ⟨hT.le hgT, hgx⟩
  have hK₀Jeq : K₀ ⊓ J z = C := by
    ext g
    constructor
    · rintro ⟨⟨hgT, hgx⟩, hgJ⟩
      exact Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_inf.mpr ⟨hgJ, lemma54T₂_centralizes_kl (z := z) (D := D) hgT⟩, hgx⟩
    · rintro ⟨⟨hgJ, hgσ⟩, hgx⟩
      have hgH : g ∈ H z := J_le_H hgJ
      have hgT : g ∈ T₂ := by
        refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hgH, hgσ⟩, ?_⟩
        exact Subgroup.mem_map.mpr ⟨⟨g, hgH⟩, by
          rw [Subgroup.mem_comap,
            (J_mem_iff (z := z) D ⟨g, hgH⟩).mp (Subgroup.mem_subgroupOf.mpr hgJ)]
          exact Subgroup.one_mem _, rfl⟩
      exact ⟨⟨hgT, hgx⟩, hgJ⟩
  have hK₀H : K₀ ≤ H z := by
    intro g hg
    exact lemma54T₂_le_H_kl (z := z) (D := D) (Subgroup.mem_inf.mp hg).1
  obtain ⟨k, hkσ, hkx, hqk⟩ :=
    exists_mem_centralizer_qH_eq_t_of_qH_eq_uv (D := D) h hZ hz₁ hz₁z hord P hP hσ₂ hq₂ hc₂
      hxσ hx2 hqx
  have hkH : (k : G) ∈ H z := k.2
  have hkT : (k : G) ∈ T₂ := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hkH, hkσ⟩, ?_⟩
    exact Subgroup.mem_map.mpr ⟨k, by
      rw [Subgroup.mem_comap, hqk]
      exact Subgroup.subset_closure (by simp), rfl⟩
  have hkK₀ : (k : G) ∈ K₀ := Subgroup.mem_inf.mpr ⟨hkT, hkx⟩
  have hxK₀ : (x : G) ∈ K₀ := by
    have hxT : (x : G) ∈ T₂ := by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨x.2, hxσ⟩, ?_⟩
      exact Subgroup.mem_map.mpr ⟨x, by
        rw [Subgroup.mem_comap, hqx]
        exact Subgroup.subset_closure (by simp), rfl⟩
    exact Subgroup.mem_inf.mpr ⟨hxT, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
  have hrangeK : Nat.card ↥(qHsub_kl (z := z) (D := D) K₀ hK₀H).range = 4 := by
    have hr : (qHsub_kl (z := z) (D := D) K₀ hK₀H).range =
        Subgroup.closure ({tA, uA * vA} : Set A45) := by
      refine le_antisymm ?_ ?_
      · rintro g ⟨y, rfl⟩
        exact lemma54T₂_qH_mem_kl (z := z) (D := D) (Subgroup.mem_inf.mp y.2).1 (hK₀H y.2)
      · rw [Subgroup.closure_le]
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl
        · exact MonoidHom.mem_range.mpr ⟨⟨(k : G), hkK₀⟩, hqk⟩
        · exact MonoidHom.mem_range.mpr ⟨⟨(x : G), hxK₀⟩, hqx⟩
    rw [hr]
    exact qa45_sigma_centralizer_sylow.2.1.2.2
  have hK₀card : Nat.card K₀ = 32 := by
    have h := card_eq_card_inf_mul_card_range_kl (z := z) (D := D) K₀ hK₀H
    rw [hK₀Jeq, hCcard, hrangeK] at h
    exact h.trans (by norm_num)
  obtain ⟨Q, hQle⟩ :=
    IsPGroup.exists_le_sylow (p := 2) (P := K₀.subgroupOf Z) hK₀p.comap_subtype
  let S : Subgroup G := (Q : Subgroup ↥Z).map Z.subtype
  have hS : IsSylowOf 2 S Z := ⟨Q, rfl⟩
  have hK₀S : K₀ ≤ S := by
    intro g hg
    exact Subgroup.mem_map.mpr ⟨⟨g, hK₀le hg⟩, hQle (Subgroup.mem_subgroupOf.mpr hg), rfl⟩
  have hS_card : Nat.card S ≤ 32 := by
    have hSZ : S ≤ Z := hS.le
    have hSH : S ≤ H z := fun g hg =>
      (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp (hSZ hg)).1).1
    have hSp : IsPGroup 2 S := hS.isPGroup
    have h := card_eq_card_inf_mul_card_range_kl (z := z) (D := D) S hSH
    have hSJ : Nat.card ↥(S ⊓ J z) ≤ 8 := by
      have hle : S ⊓ J z ≤ C := by
        rintro g ⟨hgS, hgJ⟩
        obtain ⟨hgY, hgx⟩ := Subgroup.mem_inf.mp (hSZ hgS)
        obtain ⟨-, hgσ⟩ := Subgroup.mem_inf.mp hgY
        exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hgJ, hgσ⟩, hgx⟩
      have h1 : Nat.card ↥(S ⊓ J z) ≤ Nat.card C :=
        Nat.card_le_card_of_injective (fun y : ↥(S ⊓ J z) => (⟨(y : G), hle y.2⟩ : ↥C))
          (fun a b hab => Subtype.ext (congrArg (fun z : ↥C => (z : G)) hab))
      rw [hCcard] at h1
      exact h1
    have himg : Nat.card ↥(qHsub_kl (z := z) (D := D) S hSH).range ≤ 4 := by
      have hp : IsPGroup 2 ↥(qHsub_kl (z := z) (D := D) S hSH).range :=
        IsPGroup.of_surjective hSp (MonoidHom.rangeRestrict (qHsub_kl (z := z) (D := D) S hSH))
          (MonoidHom.rangeRestrict_surjective _)
      refine card_le_four_of_isPGroup_le_centralizer_kl _ hp ?_
      rintro g ⟨y, rfl⟩
      have hyS : (y : G) ∈ S := y.2
      have hyY : (y : G) ∈ Y := (Subgroup.mem_inf.mp (hSZ hyS)).1
      have hyσ : (y : G) ∈ centralizer ({σ} : Set G) := (Subgroup.mem_inf.mp hyY).2
      let yh : ↥(H z) := ⟨(y : G), hSH hyS⟩
      have hyσh : yh ∈ centralizer ({σh} : Set ↥(H z)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hyσ)
      rw [Subgroup.mem_centralizer_singleton_iff]
      change qH (z := z) D yh * ((⟨sigma1, sigma1_mem_A⟩ : A45) * s2A⁻¹) =
        ((⟨sigma1, sigma1_mem_A⟩ : A45) * s2A⁻¹) * qH (z := z) D yh
      calc qH (z := z) D yh * ((⟨sigma1, sigma1_mem_A⟩ : A45) * s2A⁻¹)
          = qH (z := z) D (yh * σh) := by rw [map_mul, hqσ]
        _ = qH (z := z) D (σh * yh) := by
            rw [Subgroup.mem_centralizer_singleton_iff.mp hyσh]
        _ = ((⟨sigma1, sigma1_mem_A⟩ : A45) * s2A⁻¹) * qH (z := z) D yh := by
            rw [map_mul, hqσ]
    rw [h]
    exact le_trans (Nat.mul_le_mul hSJ himg) (by norm_num)
  have hS_le : Nat.card S ≤ Nat.card K₀ := by rw [hK₀card]; exact hS_card
  have hEq : K₀ = S := Subgroup.eq_of_le_of_card_ge hK₀S hS_le
  rw [hEq]
  exact hS

end CFSG.RankThree.GF2n.Parrott
