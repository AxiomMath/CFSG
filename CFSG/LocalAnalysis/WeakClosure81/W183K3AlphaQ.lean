module

public import CFSG.LocalAnalysis.WeakClosure81.W183Br1Alpha
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Dyn
public import CFSG.LocalAnalysis.WeakClosure81.W183K3Grp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Open Subgroup
open W183K3

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {Y T L₁ L₂ A : Subgroup (LGL 2 V)}

private theorem w183k3_inf_centralizer_eq_quasiCentre {L : Subgroup (LGL 2 V)} :
    L ⊓ Subgroup.centralizer (L : Set (LGL 2 V)) = quasiCentre L := by
  ext z
  rw [Subgroup.mem_inf, mem_quasiCentre, Subgroup.mem_centralizer_iff]
  exact ⟨fun h => ⟨h.1, fun l hl => (h.2 l hl).symm⟩,
    fun h => ⟨h.1, fun l hl => (h.2 l hl).symm⟩⟩

private theorem w183k3_conj_mem_centralizer {L : Subgroup (LGL 2 V)} {g c : LGL 2 V}
    (hg : g ∈ Subgroup.normalizer (L : Set (LGL 2 V)))
    (hc : c ∈ Subgroup.centralizer (L : Set (LGL 2 V))) :
    g * c * g⁻¹ ∈ Subgroup.centralizer (L : Set (LGL 2 V)) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro l hl
  have hl' : g⁻¹ * l * g ∈ L := ((Subgroup.mem_normalizer_iff''.mp hg) l).mp hl
  calc l * (g * c * g⁻¹)
      = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [hc (g⁻¹ * l * g) hl']
    _ = (g * c * g⁻¹) * l := by group

private theorem w183k3_cj_eq_components (htwo : Br3TwoComp Y T L₁ L₂) {x : LGL 2 V}
    (hx : x ∈ alphaX Y L₁) : cj x L₁ = L₁ ∧ cj x L₂ = L₂ := by
  have hcj1 : cj x L₁ = L₁ :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := L₁) (g := x)).mp hx.2
  rcases htwo.perm x hx.1 with h | h
  · exact h
  · exact absurd (hcj1.symm.trans h.1) htwo.ne

private theorem w183k3_commutator_mem_centralizer {L : Subgroup (LGL 2 V)} {w a : LGL 2 V}
    (hw : w ∈ Subgroup.centralizer (L : Set (LGL 2 V)))
    (ha : a ∈ Subgroup.normalizer (L : Set (LGL 2 V))) :
    w * a * w⁻¹ * a⁻¹ ∈ Subgroup.centralizer (L : Set (LGL 2 V)) := by
  have hwfix : ∀ m ∈ L, w * m * w⁻¹ = m := by
    intro m hm
    have h := Subgroup.mem_centralizer_iff.mp hw m hm
    calc w * m * w⁻¹ = (m * w) * w⁻¹ := by rw [← h]
      _ = m := by group
  have hwfix' : ∀ m ∈ L, w⁻¹ * m * w = m := by
    intro m hm
    have h := hwfix m hm
    have hcomm : w * m = m * w := by
      calc w * m = (w * m * w⁻¹) * w := by group
        _ = m * w := by rw [h]
    calc w⁻¹ * m * w = w⁻¹ * (m * w) := by group
      _ = w⁻¹ * (w * m) := by rw [← hcomm]
      _ = m := by group
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hal : a⁻¹ * l * a ∈ L := ((Subgroup.mem_normalizer_iff''.mp ha) l).mp hl
  have hkey : (w * a * w⁻¹ * a⁻¹) * l * (w * a * w⁻¹ * a⁻¹)⁻¹ = l := by
    calc (w * a * w⁻¹ * a⁻¹) * l * (w * a * w⁻¹ * a⁻¹)⁻¹
        = w * a * (w⁻¹ * (a⁻¹ * l * a) * w) * a⁻¹ * w⁻¹ := by group
      _ = w * a * (a⁻¹ * l * a) * a⁻¹ * w⁻¹ := by rw [hwfix' _ hal]
      _ = w * l * w⁻¹ := by group
      _ = l := hwfix l hl
  have hxl : (w * a * w⁻¹ * a⁻¹) * l = l * (w * a * w⁻¹ * a⁻¹) := by
    calc (w * a * w⁻¹ * a⁻¹) * l
        = ((w * a * w⁻¹ * a⁻¹) * l * (w * a * w⁻¹ * a⁻¹)⁻¹) *
            (w * a * w⁻¹ * a⁻¹) := by group
      _ = l * (w * a * w⁻¹ * a⁻¹) := by rw [hkey]
  exact hxl.symm

theorem w183k3_alpha_normal_cent {L : Subgroup (LGL 2 V)} (hq : CFSG.Open.IsQuasisimple ↥L)
    (hLY : L ≤ Y) :
    (alphaL Y L).Normal ∧ Subgroup.centralizer (alphaL Y L : Set (alphaQuot Y L)) = ⊥ := by
  have hLX : L ≤ alphaX Y L := le_inf hLY L.le_normalizer
  have hLnorm : (L.subgroupOf (alphaX Y L)).Normal := by
    refine (Subgroup.normal_subgroupOf_iff hLX).mpr ?_
    intro l x hl hx
    exact ((Subgroup.mem_normalizer_iff.mp hx.2) l).mp hl
  constructor
  · exact hLnorm.map (alphaMk Y L) (QuotientGroup.mk'_surjective _)
  · rw [Subgroup.eq_bot_iff_forall]
    intro q hq_cent
    obtain ⟨xX, rfl⟩ := QuotientGroup.mk'_surjective _ q
    have hxL_norm : ∀ l ∈ L, xX.1 * l * xX.1⁻¹ ∈ L :=
      fun l hl => ((Subgroup.mem_normalizer_iff.mp xX.2.2) l).mp hl
    have hxL_mod : ∀ l ∈ L, xX.1 * l * xX.1⁻¹ * l⁻¹ ∈ quasiCentre L := by
      intro l hl
      have hlX : (⟨l, hLX hl⟩ : ↥(alphaX Y L)) ∈ L.subgroupOf (alphaX Y L) :=
        Subgroup.mem_subgroupOf.mpr hl
      have hcomm := hq_cent (alphaMk Y L ⟨l, hLX hl⟩)
        (Subgroup.mem_map_of_mem (alphaMk Y L) hlX)
      have hd : xX * ⟨l, hLX hl⟩ * xX⁻¹ * ⟨l, hLX hl⟩⁻¹ ∈
          (alphaC Y L).subgroupOf (alphaX Y L) := by
        have hker : alphaMk Y L (xX * ⟨l, hLX hl⟩ * xX⁻¹ * ⟨l, hLX hl⟩⁻¹) = 1 := by
          simp only [map_mul, map_inv]
          rw [← hcomm]
          group
        exact (QuotientGroup.eq_one_iff (N := (alphaC Y L).subgroupOf (alphaX Y L)) _).mp hker
      have hdC : (xX * ⟨l, hLX hl⟩ * xX⁻¹ * ⟨l, hLX hl⟩⁻¹).1 ∈
          Subgroup.centralizer (L : Set (LGL 2 V)) := (Subgroup.mem_inf.mp hd).2
      have hdL : (xX * ⟨l, hLX hl⟩ * xX⁻¹ * ⟨l, hLX hl⟩⁻¹).1 ∈ L := by
        have h1 : xX * ⟨l, hLX hl⟩ * xX⁻¹ ∈ L.subgroupOf (alphaX Y L) := by
          rw [Subgroup.mem_subgroupOf]
          exact ((Subgroup.mem_normalizer_iff.mp xX.2.2) l).mp hl
        exact (L.subgroupOf (alphaX Y L)).mul_mem h1
          ((L.subgroupOf (alphaX Y L)).inv_mem hlX)
      rw [mem_quasiCentre]
      exact ⟨hdL, fun l' hl' => (Subgroup.mem_centralizer_iff.mp hdC l' hl').symm⟩
    have hxX_cent : xX.1 ∈ Subgroup.centralizer (L : Set (LGL 2 V)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact (quasi_comm_of_comm_mod_centre hq hxL_norm hxL_mod l hl).symm
    exact (QuotientGroup.eq_one_iff (N := (alphaC Y L).subgroupOf (alphaX Y L)) xX).mpr
      ⟨xX.2.1, hxX_cent⟩

theorem w183k3_alpha_shape {L : Subgroup (LGL 2 V)} (hLY : L ≤ Y) :
    Nonempty (↥L ⧸ Subgroup.center ↥L ≃* ↥(alphaL Y L)) := by
  have hLX : L ≤ alphaX Y L := le_inf hLY L.le_normalizer
  let φ : ↥L →* alphaQuot Y L := (alphaMk Y L).comp (Subgroup.inclusion hLX)
  have hker : φ.ker = Subgroup.center ↥L := by
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
    constructor
    · intro hl m
      have hl' : Subgroup.inclusion hLX l ∈ (alphaC Y L).subgroupOf (alphaX Y L) :=
        (QuotientGroup.eq_one_iff (N := (alphaC Y L).subgroupOf (alphaX Y L))
          (Subgroup.inclusion hLX l)).mp hl
      apply Subtype.ext
      have hlC : (l : LGL 2 V) ∈ Subgroup.centralizer (L : Set (LGL 2 V)) :=
        (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hl')).2
      exact Subgroup.mem_centralizer_iff.mp hlC m m.2
    · intro hl
      refine (QuotientGroup.eq_one_iff (N := (alphaC Y L).subgroupOf (alphaX Y L))
        (Subgroup.inclusion hLX l)).mpr ?_
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨((Subgroup.inclusion hLX l).2).1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact congrArg Subtype.val (hl ⟨m, hm⟩)
  have hrange : φ.range = alphaL Y L := by
    ext q
    constructor
    · intro hq
      obtain ⟨l, rfl⟩ := MonoidHom.mem_range.mp hq
      exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hLX l,
        Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
    · intro hq
      obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp hq
      refine MonoidHom.mem_range.mpr ⟨⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩, ?_⟩
      show alphaMk Y L (Subgroup.inclusion hLX ⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩) = q
      rw [show Subgroup.inclusion hLX ⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩ = x from
        Subtype.ext rfl, hxq]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrange))⟩

theorem w183k3_alpha_dynkin {L : Subgroup (LGL 2 V)} [Finite (alphaQuot Y L)] (hLY : L ≤ Y)
    {τ : LGL 2 V} (hτY : τ ∈ Y) (hτ : ActsOnDynkinMod (quasiCentre L) L τ) :
    ∃ τ' : alphaQuot Y L, ActsOnDynkinMod ⊥ (alphaL Y L) τ' := by
  haveI : Finite ↥(alphaX Y L) := Subtype.finite
  have hLX : L ≤ alphaX Y L := le_inf hLY L.le_normalizer
  have hτX : τ ∈ alphaX Y L := ⟨hτY, hτ.1⟩
  have hker : (alphaMk Y L).ker ⊓ (L.subgroupOf (alphaX Y L)) ≤
      (quasiCentre L).subgroupOf (alphaX Y L) := by
    intro z hz
    rw [Subgroup.mem_inf] at hz
    obtain ⟨hzk, hzL⟩ := hz
    rw [MonoidHom.mem_ker] at hzk
    have hzk' : z ∈ (alphaC Y L).subgroupOf (alphaX Y L) :=
      (QuotientGroup.eq_one_iff (N := (alphaC Y L).subgroupOf (alphaX Y L)) z).mp hzk
    rw [Subgroup.mem_subgroupOf] at hzk' hzL ⊢
    rw [mem_quasiCentre]
    refine ⟨hzL, ?_⟩
    have hzk'' : z.1 ∈ Subgroup.centralizer (L : Set (LGL 2 V)) :=
      (Subgroup.mem_inf.mp hzk').2
    rw [Subgroup.mem_centralizer_iff] at hzk''
    intro l hl
    exact (hzk'' l hl).symm
  have hqc : ((quasiCentre L).subgroupOf (alphaX Y L)).map (alphaMk Y L) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    intro z hz
    rw [MonoidHom.mem_ker]
    refine (QuotientGroup.eq_one_iff (N := (alphaC Y L).subgroupOf (alphaX Y L)) z).mpr ?_
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    refine Subgroup.mem_inf.mpr ⟨z.2.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact ((mem_quasiCentre.mp hz).2 l hl).symm
  have hsub := actsOnDynkinMod_subgroupOf (alphaX Y L) hLX hτX hτ
  have hmap := actsOnDynkinMod_map (alphaMk Y L) hker hsub
  rw [hqc] at hmap
  exact ⟨alphaMk Y L ⟨τ, hτX⟩, hmap⟩

private theorem w183k3_cent_inf_le_normalizer (htwo : Br3TwoComp Y T L₁ L₂) :
    Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ⊓
      Subgroup.centralizer (L₂ : Set (LGL 2 V)) ≤ alphaX Y L₁ := by
  intro z hz
  obtain ⟨hz₁, _⟩ := Subgroup.mem_inf.mp hz
  obtain ⟨hzY, hzC₁⟩ := Subgroup.mem_inf.mp hz₁
  exact Subgroup.mem_inf.mpr ⟨hzY, Subgroup.centralizer_le_normalizer _ hzC₁⟩

private theorem w183k3_cent_inf_normal (htwo : Br3TwoComp Y T L₁ L₂) :
    ((Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ⊓
      Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf (alphaX Y L₁)).Normal := by
  refine (Subgroup.normal_subgroupOf_iff (w183k3_cent_inf_le_normalizer htwo)).mpr ?_
  intro n g hn hg
  obtain ⟨hnY, hnC₁, hnC₂⟩ : n ∈ Y ∧ n ∈ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ∧
      n ∈ Subgroup.centralizer (L₂ : Set (LGL 2 V)) := by
    obtain ⟨⟨hnY, hnC₁⟩, hnC₂⟩ := Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hn)
    exact ⟨hnY, hnC₁, hnC₂⟩
  refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · exact Y.mul_mem (Y.mul_mem hg.1 hnY) (Y.inv_mem hg.1)
  · exact w183k3_conj_mem_centralizer hg.2 hnC₁
  · exact w183k3_conj_mem_centralizer
      ((Subgroup.mem_normalizer_iff_map_conj_eq (H := L₂) (g := g)).mpr
        (w183k3_cj_eq_components htwo hg).2) hnC₂

private theorem w183k3_cent_inf_odd (htwo : Br3TwoComp Y T L₁ L₂) :
    Odd (Nat.card ↥((Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ⊓
      Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf (alphaX Y L₁))) := by
  have h := htwo.odd_card_cent
  rwa [← Nat.card_congr
    (Subgroup.subgroupOfEquivOfLe (w183k3_cent_inf_le_normalizer htwo)).toEquiv] at h

theorem w183k3_alpha_ti (htwo : Br3TwoComp Y T L₁ L₂) (hA : A ≤ Y) (hA2 : IsPGroup 2 ↥A)
    (hAn₁ : A ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    (hC₂ : A ≤ Subgroup.centralizer (L₂ : Set (LGL 2 V)))
    (hTI : IsTISub ↥Y (A.subgroupOf Y)) : IsTISub (alphaQuot Y L₁) (alphaA Y L₁ A) := by
  haveI : Finite ↥(alphaX Y L₁) := Subtype.finite
  intro t ht ht1 g hgt
  obtain ⟨tX, htXA, rfl⟩ := Subgroup.mem_map.mp ht
  obtain ⟨xX, rfl⟩ := QuotientGroup.mk'_surjective _ g
  have ht0A : tX.1 ∈ A := Subgroup.mem_subgroupOf.mp htXA
  have ht0Y : tX.1 ∈ Y := tX.2.1
  have hxY : xX.1 ∈ Y := xX.2.1
  have ht0ne : tX.1 ≠ 1 := by
    intro h
    exact ht1 (by rw [show tX = 1 from Subtype.ext h, map_one])
  have hd : xX * tX * xX⁻¹ * tX⁻¹ ∈ (alphaC Y L₁).subgroupOf (alphaX Y L₁) := by
    have hker : alphaMk Y L₁ (xX * tX * xX⁻¹ * tX⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hgt]
      group
    exact (QuotientGroup.eq_one_iff (N := (alphaC Y L₁).subgroupOf (alphaX Y L₁)) _).mp hker
  have hdC₁ : (xX * tX * xX⁻¹ * tX⁻¹).1 ∈
      Subgroup.centralizer (L₁ : Set (LGL 2 V)) := (Subgroup.mem_inf.mp hd).2
  have hdY : (xX * tX * xX⁻¹ * tX⁻¹).1 ∈ Y := (Subgroup.mem_inf.mp hd).1
  have hxN₂ : xX.1 ∈ Subgroup.normalizer (L₂ : Set (LGL 2 V)) :=
    (Subgroup.mem_normalizer_iff_map_conj_eq (H := L₂) (g := xX.1)).mpr
      (w183k3_cj_eq_components htwo xX.2).2
  have hdC₂ : (xX * tX * xX⁻¹ * tX⁻¹).1 ∈
      Subgroup.centralizer (L₂ : Set (LGL 2 V)) :=
    (Subgroup.centralizer (L₂ : Set (LGL 2 V))).mul_mem
      (w183k3_conj_mem_centralizer hxN₂ (hC₂ ht0A))
      ((Subgroup.centralizer (L₂ : Set (LGL 2 V))).inv_mem (hC₂ ht0A))
  have hdK : xX * tX * xX⁻¹ * tX⁻¹ ∈
      (Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ⊓
        Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf (alphaX Y L₁) :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_inf.mpr ⟨hdY, hdC₁⟩, hdC₂⟩)
  haveI : ((Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ⊓
      Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf (alphaX Y L₁)).Normal :=
    w183k3_cent_inf_normal htwo
  obtain ⟨m, hm⟩ := hA2 ⟨tX.1, ht0A⟩
  have htXpow : tX ^ (2 ^ m) = 1 := by
    apply Subtype.ext
    have h := congrArg (fun x : ↥A => (x : LGL 2 V)) hm
    simpa using h
  obtain ⟨k, hkK, hkcomm⟩ := w183k3_exists_cent_mul (w183k3_cent_inf_odd htwo) htXpow hdK
  have hkK₀ : k.1 ∈ Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ⊓
      Subgroup.centralizer (L₂ : Set (LGL 2 V)) := Subgroup.mem_subgroupOf.mp hkK
  have hkY : k.1 ∈ Y := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hkK₀).1).1
  have hwY : (xX * k).1 ∈ Y := Y.mul_mem hxY hkY
  have hwcomm : (xX * k).1 * tX.1 = tX.1 * (xX * k).1 := by
    have h := congrArg (fun z : ↥(alphaX Y L₁) => z.1) hkcomm
    simpa using h
  have hN := hTI ⟨tX.1, ht0Y⟩ (Subgroup.mem_subgroupOf.mpr ht0A)
    (fun h => ht0ne (congrArg Subtype.val h)) ⟨(xX * k).1, hwY⟩ (Subtype.ext hwcomm)
  have hwN : (xX * k).1 ∈ Subgroup.normalizer (A : Set (LGL 2 V)) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hA] at hN
    exact Subgroup.mem_subgroupOf.mp hN
  have hwNX : xX * k ∈ Subgroup.normalizer
      (A.subgroupOf (alphaX Y L₁) : Set ↥(alphaX Y L₁)) := by
    rw [← Subgroup.subgroupOf_normalizer_eq (le_inf hA hAn₁)]
    exact Subgroup.mem_subgroupOf.mpr hwN
  have hmem := Subgroup.le_normalizer_map (alphaMk Y L₁)
    (Subgroup.mem_map_of_mem (alphaMk Y L₁) hwNX)
  have hkker : alphaMk Y L₁ k = 1 := by
    refine (QuotientGroup.eq_one_iff (N := (alphaC Y L₁).subgroupOf (alphaX Y L₁)) k).mpr ?_
    rw [Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_inf.mp hkK).1
  simpa [map_mul, hkker] using hmem

theorem w183k3_diag_ti (htwo : Br3TwoComp Y T L₁ L₂) (hA : A ≤ Y) (hA2 : IsPGroup 2 ↥A)
    (hAn₁ : A ≤ Subgroup.normalizer (L₁ : Set (LGL 2 V)))
    (hAn₂ : A ≤ Subgroup.normalizer (L₂ : Set (LGL 2 V)))
    (hC₂ : A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) = ⊥)
    (hTI : IsTISub ↥Y (A.subgroupOf Y)) :
    ∀ t ∈ alphaA Y L₁ A, t ≠ 1 → ∀ g ∈ alphaL Y L₁, g * t = t * g →
      ∀ a ∈ alphaA Y L₁ A, g * a = a * g := by
  haveI : Finite ↥(alphaX Y L₁) := Subtype.finite
  intro t ht ht1 g hg hgt a ha
  obtain ⟨tX, htXA, rfl⟩ := Subgroup.mem_map.mp ht
  obtain ⟨lX, hlXL, rfl⟩ := Subgroup.mem_map.mp hg
  obtain ⟨aX, haXA, rfl⟩ := Subgroup.mem_map.mp ha
  have ht0A : tX.1 ∈ A := Subgroup.mem_subgroupOf.mp htXA
  have ht0Y : tX.1 ∈ Y := tX.2.1
  have hl0L₁ : lX.1 ∈ L₁ := Subgroup.mem_subgroupOf.mp hlXL
  have hl0Y : lX.1 ∈ Y := htwo.le₁ hl0L₁
  have ha0A : aX.1 ∈ A := Subgroup.mem_subgroupOf.mp haXA
  have ht0ne : tX.1 ≠ 1 := by
    intro h
    exact ht1 (by rw [show tX = 1 from Subtype.ext h, map_one])
  have hd : lX * tX * lX⁻¹ * tX⁻¹ ∈ (alphaC Y L₁).subgroupOf (alphaX Y L₁) := by
    have hker : alphaMk Y L₁ (lX * tX * lX⁻¹ * tX⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [hgt]
      group
    exact (QuotientGroup.eq_one_iff (N := (alphaC Y L₁).subgroupOf (alphaX Y L₁)) _).mp hker
  have hdC₁ : (lX * tX * lX⁻¹ * tX⁻¹).1 ∈
      Subgroup.centralizer (L₁ : Set (LGL 2 V)) := (Subgroup.mem_inf.mp hd).2
  have hdL₁ : (lX * tX * lX⁻¹ * tX⁻¹).1 ∈ L₁ := by
    have h1 : tX.1 * lX.1⁻¹ * tX.1⁻¹ ∈ L₁ :=
      ((Subgroup.mem_normalizer_iff.mp (hAn₁ ht0A)) lX.1⁻¹).mp (L₁.inv_mem hl0L₁)
    have heq : (lX * tX * lX⁻¹ * tX⁻¹).1 = lX.1 * (tX.1 * lX.1⁻¹ * tX.1⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [heq]
    exact L₁.mul_mem hl0L₁ h1
  have hdqc : (lX * tX * lX⁻¹ * tX⁻¹).1 ∈ quasiCentre L₁ := by
    rw [← w183k3_inf_centralizer_eq_quasiCentre]
    exact ⟨hdL₁, hdC₁⟩
  have hdK : lX * tX * lX⁻¹ * tX⁻¹ ∈
      (Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ⊓
        Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf (alphaX Y L₁) := by
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
    · exact htwo.le₁ (mem_quasiCentre.mp hdqc).1
    · rw [Subgroup.mem_centralizer_iff]
      exact fun l hl => ((mem_quasiCentre.mp hdqc).2 l hl).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact (htwo.comm _ (mem_quasiCentre.mp hdqc).1 l hl).symm
  haveI : ((Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ⊓
      Subgroup.centralizer (L₂ : Set (LGL 2 V))).subgroupOf (alphaX Y L₁)).Normal :=
    w183k3_cent_inf_normal htwo
  obtain ⟨m, hm⟩ := hA2 ⟨tX.1, ht0A⟩
  have htXpow : tX ^ (2 ^ m) = 1 := by
    apply Subtype.ext
    have h := congrArg (fun x : ↥A => (x : LGL 2 V)) hm
    simpa using h
  obtain ⟨k, hkK, hkcomm⟩ :=
    w183k3_exists_cent_mul (w183k3_cent_inf_odd htwo) htXpow hdK
  have hkK₀ : k.1 ∈ Y ⊓ Subgroup.centralizer (L₁ : Set (LGL 2 V)) ⊓
      Subgroup.centralizer (L₂ : Set (LGL 2 V)) := Subgroup.mem_subgroupOf.mp hkK
  have hkY : k.1 ∈ Y := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hkK₀).1).1
  have hkC₂ : k.1 ∈ Subgroup.centralizer (L₂ : Set (LGL 2 V)) :=
    (Subgroup.mem_inf.mp hkK₀).2
  have hwY : (lX * k).1 ∈ Y := Y.mul_mem hl0Y hkY
  have hwcomm : (lX * k).1 * tX.1 = tX.1 * (lX * k).1 := by
    have h := congrArg (fun z : ↥(alphaX Y L₁) => z.1) hkcomm
    simpa using h
  have hwC₂ : (lX * k).1 ∈ Subgroup.centralizer (L₂ : Set (LGL 2 V)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : lX.1 * l = l * lX.1 := htwo.comm lX.1 hl0L₁ l hl
    have h2 : l * k.1 = k.1 * l := Subgroup.mem_centralizer_iff.mp hkC₂ l hl
    show l * (lX.1 * k.1) = (lX.1 * k.1) * l
    calc l * (lX.1 * k.1) = (l * lX.1) * k.1 := by group
      _ = (lX.1 * l) * k.1 := by rw [← h1]
      _ = lX.1 * (l * k.1) := by group
      _ = lX.1 * (k.1 * l) := by rw [h2]
      _ = (lX.1 * k.1) * l := by group
  have hN := hTI ⟨tX.1, ht0Y⟩ (Subgroup.mem_subgroupOf.mpr ht0A)
    (fun h => ht0ne (congrArg Subtype.val h)) ⟨(lX * k).1, hwY⟩ (Subtype.ext hwcomm)
  have hwN : (lX * k).1 ∈ Subgroup.normalizer (A : Set (LGL 2 V)) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hA] at hN
    exact Subgroup.mem_subgroupOf.mp hN
  have hbA : (lX * k).1 * aX.1 * (lX * k)⁻¹ ∈ A :=
    (Subgroup.mem_normalizer_iff.mp hwN aX.1).mp ha0A
  have hcommut : (lX * k).1 * aX.1 * (lX * k)⁻¹ * aX.1⁻¹ ∈
      Subgroup.centralizer (L₂ : Set (LGL 2 V)) :=
    w183k3_commutator_mem_centralizer hwC₂ (hAn₂ ha0A)
  have hbA' : (lX * k).1 * aX.1 * (lX * k)⁻¹ * aX.1⁻¹ ∈ A :=
    A.mul_mem hbA (A.inv_mem ha0A)
  have hbone : (lX * k).1 * aX.1 * (lX * k)⁻¹ * aX.1⁻¹ = 1 := by
    have hmem : (lX * k).1 * aX.1 * (lX * k)⁻¹ * aX.1⁻¹ ∈
        A ⊓ Subgroup.centralizer (L₂ : Set (LGL 2 V)) := ⟨hbA', hcommut⟩
    rw [hC₂, Subgroup.mem_bot] at hmem
    exact hmem
  have hwcomm_a : (lX * k).1 * aX.1 = aX.1 * (lX * k).1 := by
    have hbone' : (lX * k) * aX * (lX * k)⁻¹ * aX⁻¹ = 1 := by
      apply Subtype.ext
      simpa using hbone
    have hsub : (lX * k) * aX = aX * (lX * k) := by
      have h : (lX * k) * aX * (lX * k)⁻¹ = aX := mul_inv_eq_one.mp hbone'
      calc (lX * k) * aX = ((lX * k) * aX * (lX * k)⁻¹) * (lX * k) := by group
        _ = aX * (lX * k) := by rw [h]
    exact congrArg Subtype.val hsub
  have hkker : alphaMk Y L₁ k = 1 := by
    refine (QuotientGroup.eq_one_iff (N := (alphaC Y L₁).subgroupOf (alphaX Y L₁)) k).mpr ?_
    rw [Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_inf.mp hkK₀).1
  have hcommq : alphaMk Y L₁ (lX * k) * alphaMk Y L₁ aX =
      alphaMk Y L₁ aX * alphaMk Y L₁ (lX * k) := by
    rw [← map_mul, ← map_mul]
    exact congrArg (alphaMk Y L₁) (Subtype.ext hwcomm_a)
  rw [map_mul, hkker, mul_one] at hcommq
  exact hcommq

end CFSG.LocalAnalysis.WeakClosure81

end
