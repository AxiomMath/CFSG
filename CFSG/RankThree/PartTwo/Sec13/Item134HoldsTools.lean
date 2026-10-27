module

public import CFSG.RankThree.PartTwo.Sec13.Item13Plane
import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec13.Holds134

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

section Transvection

variable {G : Type*} [Group G] {A : Subgroup G} {d : A}

theorem apply_eq_of_mem_zpowers {σ : MulAut A} (hσ : σ ∈ Sec12.transvectionGroup A d)
    {y : A} (hy : y ∈ Subgroup.zpowers d) : σ y = y := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [map_zpow, hσ.1]

theorem pow_apply {σ : MulAut A} (hσ : σ ∈ Sec12.transvectionGroup A d) (x : A) (n : ℕ) :
    (σ ^ n) x = (σ x * x⁻¹) ^ n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hu := apply_eq_of_mem_zpowers hσ (hσ.2 x)
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hu, pow_succ]
    group

theorem commute {σ τ : MulAut A} (hσ : σ ∈ Sec12.transvectionGroup A d)
    (hτ : τ ∈ Sec12.transvectionGroup A d) : σ * τ = τ * σ := by
  refine MulEquiv.ext fun x => ?_
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hσ.2 x)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hτ.2 x)
  have hσx : σ x = d ^ i * x := by rw [hi, inv_mul_cancel_right]
  have hτx : τ x = d ^ j * x := by rw [hj, inv_mul_cancel_right]
  rw [MulAut.mul_apply, MulAut.mul_apply, hτx, hσx, map_mul, map_mul, map_zpow, map_zpow, hσ.1,
    hτ.1, hσx, hτx, ← mul_assoc, ← mul_assoc, ← zpow_add, ← zpow_add, add_comm]

theorem pow_three_eq_one {σ : MulAut A} (hσ : σ ∈ Sec12.transvectionGroup A d) (hd : d ^ 3 = 1) :
    σ ^ 3 = 1 := by
  refine MulEquiv.ext fun x => ?_
  rw [pow_apply hσ x 3, MulAut.one_apply]
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hσ.2 x)
  rw [← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hd, one_zpow,
    one_mul]

theorem isElemAbelian (hd : d ^ 3 = 1) :
    CFSG.Assembly.IsElemAbelian 3 (Sec12.transvectionGroup A d) :=
  ⟨⟨⟨fun σ τ => Subtype.ext (commute σ.2 τ.2)⟩⟩, fun _ hσ => pow_three_eq_one hσ hd⟩

theorem conj_mem {ρ σ : MulAut A}
    (hρ : ∀ y : A, y ∈ Subgroup.zpowers d ↔ ρ y ∈ Subgroup.zpowers d)
    (hσ : σ ∈ Sec12.transvectionGroup A d) : ρ * σ * ρ⁻¹ ∈ Sec12.transvectionGroup A d := by
  refine ⟨?_, fun x => ?_⟩
  · have h1 : ρ⁻¹ d ∈ Subgroup.zpowers d := by
      rw [hρ, MulAut.apply_inv_self]
      exact Subgroup.mem_zpowers d
    rw [MulAut.mul_apply, MulAut.mul_apply, apply_eq_of_mem_zpowers hσ h1, MulAut.apply_inv_self]
  · have h' : ρ (σ (ρ⁻¹ x) * (ρ⁻¹ x)⁻¹) ∈ Subgroup.zpowers d := (hρ _).mp (hσ.2 (ρ⁻¹ x))
    rw [map_mul, map_inv, MulAut.apply_inv_self] at h'
    simpa only [MulAut.mul_apply] using h'

end Transvection

section Move

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem card_le_three_of_forall_fix (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27) {d x : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hxA : x ∈ A)
    (hxd : x ∉ Subgroup.zpowers d)
    (hfix : ∀ σ ∈ Sec12.transvectionGroup A ⟨d, hdA⟩, σ ⟨x, hxA⟩ = ⟨x, hxA⟩) :
    Nat.card (Sec12.transvectionGroup A ⟨d, hdA⟩) ≤ 3 := by
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hd3 : d ^ 3 = 1 := hA.2 d hdA
  have hx3 : x ^ 3 = 1 := hA.2 x hxA
  have hx1 : x ≠ 1 := fun h => hxd (h ▸ one_mem _)
  set B := Subgroup.zpowers x ⊔ Subgroup.zpowers d with hBdef
  have hBA : B ≤ A := sup_le (Subgroup.zpowers_le.mpr hxA) (Subgroup.zpowers_le.mpr hdA)
  have hB9 : Nat.card B = 9 := by
    have hcomm' : ∀ u ∈ Subgroup.zpowers x, ∀ v ∈ Subgroup.zpowers d, u * v = v * u :=
      fun u hu v hv => hcomm u (Subgroup.zpowers_le.mpr hxA hu) v (Subgroup.zpowers_le.mpr hdA hv)
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm'
    rw [Sec13.zpowers_inf_eq_bot hx3 hxd, Subgroup.card_bot, mul_one,
      Sec13.card_zpowers_of_pow_three hx3 hx1, Sec13.card_zpowers_of_pow_three hd3 hd1] at hcard
    exact hcard
  obtain ⟨y, hyA, hyB⟩ : ∃ y ∈ A, y ∉ B := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show A ≤ B from hcon)
    omega
  have hAy : A = Subgroup.zpowers y ⊔ B :=
    (Sec12.eq_of_card_nine_lt h27 (sup_le (Subgroup.zpowers_le.mpr hyA) hBA) le_sup_right hB9
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers y)) hyB).symm
  have hmem : ∀ σ ∈ Sec12.transvectionGroup A ⟨d, hdA⟩, σ ∈ Sec13.transvAxis A B := by
    intro σ hσ
    refine ⟨fun z hz => ?_, fun z => ?_⟩
    · have hle : B ≤ (MonoidHom.eqLocus (σ : A →* A) (MonoidHom.id A)).map A.subtype :=
        sup_le (Subgroup.zpowers_le.mpr ⟨⟨x, hxA⟩, hfix σ hσ, rfl⟩)
          (Subgroup.zpowers_le.mpr ⟨⟨d, hdA⟩, hσ.1, rfl⟩)
      obtain ⟨z', hz', hzz⟩ := hle hz
      have : z' = z := Subtype.ext hzz
      rw [← this]
      exact hz'
    · have h1 := Sec12.mem_zpowers_subtype_iff.mp (hσ.2 z)
      exact Subgroup.mem_sup_right h1
  set y' : A := ⟨y, hyA⟩
  let f : Sec12.transvectionGroup A ⟨d, hdA⟩ → Subgroup.zpowers (⟨d, hdA⟩ : A) := fun σ =>
    ⟨(σ : MulAut A) y' * y'⁻¹, σ.2.2 y'⟩
  have hf : Function.Injective f := by
    rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ hστ
    have h1 : σ y' = τ y' := by
      have := congrArg Subtype.val hστ
      simpa [f] using this
    exact Subtype.ext (Sec13.transvAxis_ext hA hyA hAy (hmem σ hσ) (hmem τ hτ) h1)
  have hd'3 : orderOf (⟨d, hdA⟩ : A) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime hd3 hd1
  calc Nat.card (Sec12.transvectionGroup A ⟨d, hdA⟩)
      ≤ Nat.card (Subgroup.zpowers (⟨d, hdA⟩ : A)) := Nat.card_le_card_of_injective f hf
    _ = 3 := by rw [Nat.card_zpowers, hd'3]

theorem exists_apply_eq_mul (hA : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27)
    {d x : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hxA : x ∈ A) (hxd : x ∉ Subgroup.zpowers d)
    (hcard : 3 < Nat.card (Sec12.transvectionGroup A ⟨d, hdA⟩)) {b : G}
    (hb : b ∈ Subgroup.zpowers d) :
    ∃ σ ∈ Sec12.transvectionGroup A ⟨d, hdA⟩, ((σ ⟨x, hxA⟩ : A) : G) = b * x := by
  obtain ⟨σ₀, hσ₀, hmove⟩ : ∃ σ ∈ Sec12.transvectionGroup A ⟨d, hdA⟩,
      σ ⟨x, hxA⟩ ≠ ⟨x, hxA⟩ := by
    by_contra hcon
    push Not at hcon
    have := card_le_three_of_forall_fix hA h27 hdA hd1 hxA hxd hcon
    omega
  set x' : A := ⟨x, hxA⟩ with hx'
  set d' : A := ⟨d, hdA⟩ with hd'
  set u : A := σ₀ x' * x'⁻¹ with hu
  have hud : u ∈ Subgroup.zpowers d' := hσ₀.2 x'
  have hu1 : u ≠ 1 := fun h => hmove (by rw [hu, mul_inv_eq_one] at h; exact h)
  have hu3 : u ^ 3 = 1 := Subtype.ext (by simpa using hA.2 _ u.2)
  have hd'3 : d' ^ 3 = 1 := Subtype.ext (by simpa using hA.2 d hdA)
  have hd'1 : d' ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hzu : Subgroup.zpowers u = Subgroup.zpowers d' :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hud) (by
      rw [Sec13.card_zpowers_of_pow_three hu3 hu1, Sec13.card_zpowers_of_pow_three hd'3 hd'1])
  have hbA : b ∈ A := Subgroup.zpowers_le.mpr hdA hb
  have hb' : (⟨b, hbA⟩ : A) ∈ Subgroup.zpowers d' := Sec12.mem_zpowers_subtype_iff.mpr hb
  rw [← hzu, ← mem_powers_iff_mem_zpowers] at hb'
  obtain ⟨n, hn⟩ := hb'
  change u ^ n = ⟨b, hbA⟩ at hn
  refine ⟨σ₀ ^ n, pow_mem hσ₀ n, ?_⟩
  rw [pow_apply hσ₀ x' n, ← hu, hn]
  rfl

end Move

section WStar

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

omit [Finite G] in
theorem mem_oThreeWPre_iff {w : G} :
    w ∈ oThreeWPre A ↔ ∃ hw : w ∈ Subgroup.normalizer (A : Set G),
      A.normalizerMonoidHom ⟨w, hw⟩ ∈ oThreeWStar A := by
  constructor
  · rintro ⟨⟨p, hp⟩, hmem, rfl⟩
    exact ⟨hp, hmem⟩
  · rintro ⟨hw, hmem⟩
    exact ⟨⟨w, hw⟩, hmem, rfl⟩

omit [Finite G] in
theorem autIn_le_wStar (X : Subgroup G) : Sec4.autIn X A ≤ wStar A := fun σ hσ => by
  obtain ⟨h, hN, -, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
  exact Sec4.mem_autIn_iff.mpr ⟨h, hN, Subgroup.mem_top h, rfl⟩

theorem isSylowOf_autIn_wStar {P : Subgroup G}
    (hP : IsSylowOf 3 P (Subgroup.normalizer (A : Set G))) :
    IsSylowOf 3 (Sec4.autIn P A) (wStar A) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set W := Subgroup.normalizer (A : Set G) with hW
  have hPW : P ≤ W := hP.le
  have h1 : IsSylowOf 3 (P.subgroupOf W) ⊤ := by
    rw [← CFSG.ABGLocalTools.isSylowOf_map_subtype_iff W, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hPW, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hP
  have h2 := Sec12.IsSylowOf.map h1 A.normalizerMonoidHom
  have e1 : Sec4.autIn P A = (P.subgroupOf W).map A.normalizerMonoidHom := by
    rw [Sec4.autIn, inf_eq_left.mpr hPW]
  have e2 : wStar A = (⊤ : Subgroup W).map A.normalizerMonoidHom := by
    rw [wStar, Sec4.autIn, top_inf_eq, Subgroup.subgroupOf_self]
  rw [e1, e2]
  exact h2

omit [Finite G] in
theorem oThreeWStar_eq_of_normal {T : Subgroup (MulAut A)} (hTsyl : IsSylowOf 3 T (wStar A))
    (hTn : ∀ g ∈ wStar A, ∀ σ ∈ T, g * σ * g⁻¹ ∈ T) : oThreeWStar A = T := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hTW : T ≤ wStar A := hTsyl.le
  obtain ⟨Q, hQ⟩ := hTsyl.exists_sylow_eq_subgroupOf
  have : (CFSG.pCore 3 (wStar A)).Normal := CFSG.pCore_normal
  have hle1 : CFSG.pCore 3 (wStar A) ≤ T.subgroupOf (wStar A) := by
    rw [← hQ]
    exact IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup Q
  have hnorm : (T.subgroupOf (wStar A)).Normal :=
    ⟨fun x hx g => Subgroup.mem_subgroupOf.mpr (hTn g g.2 x (Subgroup.mem_subgroupOf.mp hx))⟩
  have hp : IsPGroup 3 (T.subgroupOf (wStar A)) := by
    rw [← hQ]
    exact Q.isPGroup'
  have hle2 : T.subgroupOf (wStar A) ≤ CFSG.pCore 3 (wStar A) := le_sSup ⟨hnorm, hp⟩
  rw [oThreeWStar, le_antisymm hle1 hle2, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTW]

end WStar

section Orbit

variable {G : Type} [Group G] [Finite G] {A : Subgroup G}

theorem ncard_pointsOff_zpowers (hA : CFSG.Assembly.IsElemAbelian 3 A) {d x : G} (hdA : d ∈ A)
    (hd1 : d ≠ 1) (hxA : x ∈ A) (hxd : x ∉ Subgroup.zpowers d) :
    (Sec13.pointsOff (Subgroup.zpowers x ⊔ Subgroup.zpowers d) (Subgroup.zpowers d)).ncard = 3 := by
  set B := Subgroup.zpowers x ⊔ Subgroup.zpowers d with hBdef
  have hBA : B ≤ A := sup_le (Subgroup.zpowers_le.mpr hxA) (Subgroup.zpowers_le.mpr hdA)
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun u v => Subtype.ext (show (u : G) * v = v * u from congrArg Subtype.val
      (hA.1.is_comm.comm ⟨u, hBA u.2⟩ ⟨v, hBA v.2⟩))⟩⟩, fun u hu => hA.2 u (hBA hu)⟩
  have hxB : x ∈ B := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  have heq : Sec13.pointsOff B (Subgroup.zpowers d) =
      (fun b : Subgroup.zpowers d => Subgroup.zpowers (x * b)) '' Set.univ := by
    ext F
    rw [Sec13.mem_pointsOff_iff hBe hxB rfl hxd]
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact ⟨⟨b, hb⟩, Set.mem_univ _, rfl⟩
    · rintro ⟨b, -, rfl⟩
      exact ⟨b, b.2, rfl⟩
  rw [heq, Set.ncard_image_of_injective _ (fun b b' h => Subtype.ext
    (Sec13.zpowers_mul_injOn hBe hxB rfl hxd b.2 b'.2 h)), Set.ncard_univ,
    Sec13.card_zpowers_of_pow_three (hA.2 d hdA) hd1]

theorem orbitIn_eq_pointsOff (hA : CFSG.Assembly.IsElemAbelian 3 A) (h27 : Nat.card A = 27)
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hO3 : oThreeWStar A = Sec12.transvectionGroup A ⟨d, hdA⟩) {Q : Subgroup G}
    (hQ : Sec4.autIn Q A = Sec12.transvectionGroup A ⟨d, hdA⟩)
    (hcard : 3 < Nat.card (Sec12.transvectionGroup A ⟨d, hdA⟩)) {x : G} (hxA : x ∈ A)
    (hxd : x ∉ Subgroup.zpowers d) :
    orbitIn (oThreeWPre A) (Subgroup.zpowers x) =
      Sec13.pointsOff (Subgroup.zpowers x ⊔ Subgroup.zpowers d) (Subgroup.zpowers d) := by
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  set B := Subgroup.zpowers x ⊔ Subgroup.zpowers d with hBdef
  have hBA : B ≤ A := sup_le (Subgroup.zpowers_le.mpr hxA) (Subgroup.zpowers_le.mpr hdA)
  have hBe : CFSG.Assembly.IsElemAbelian 3 B :=
    ⟨⟨⟨fun u v => Subtype.ext (show (u : G) * v = v * u from congrArg Subtype.val
      (hA.1.is_comm.comm ⟨u, hBA u.2⟩ ⟨v, hBA v.2⟩))⟩⟩, fun u hu => hA.2 u (hBA hu)⟩
  have hxB : x ∈ B := Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  ext F
  rw [Sec13.mem_pointsOff_iff hBe hxB rfl hxd]
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨hwN, hmem⟩ := mem_oThreeWPre_iff.mp hw
    rw [hO3] at hmem
    have h1 := Sec12.mem_zpowers_subtype_iff.mp (hmem.2 ⟨x, hxA⟩)
    have hwx : w * x * w⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hwN x).mp hxA
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Sec4.normalizerMonoidHom_apply_coe] at h1
    refine ⟨w * x * w⁻¹ * x⁻¹, h1, ?_⟩
    rw [MonoidHom.map_zpowers]
    congr 1
    change w * x * w⁻¹ = x * (w * x * w⁻¹ * x⁻¹)
    rw [← mul_assoc, ← hcomm _ hwx _ hxA, mul_inv_cancel_right]
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨σ, hσ, hσx⟩ := exists_apply_eq_mul hA h27 hdA hd1 hxA hxd hcard hb
    rw [← hQ] at hσ
    obtain ⟨w, hwN, hwQ, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    have hwO : w ∈ oThreeWPre A := by
      refine mem_oThreeWPre_iff.mpr ⟨hwN, ?_⟩
      rw [hO3, ← hQ]
      exact Sec4.mem_autIn_iff.mpr ⟨w, hwN, hwQ, rfl⟩
    refine ⟨w, hwO, ?_⟩
    rw [MonoidHom.map_zpowers]
    congr 1
    rw [Sec4.normalizerMonoidHom_apply_coe] at hσx
    change x * b = w * x * w⁻¹
    rw [hσx]
    exact hcomm x hxA b (Subgroup.zpowers_le.mpr hdA hb)

end Orbit

end CFSG.RankThree.PartTwo.Sec13.Holds134
