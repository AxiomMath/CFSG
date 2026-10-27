module

public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.Quasithin.Vol2.Ch6Vocab

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

variable {G : Type} [Group G]

@[expose] def conjSubEquiv (U : Subgroup G) (h : G) (hh : h ∈ Subgroup.normalizer (U : Set G)) :
    ↥U ≃* ↥U where
  toFun u := ⟨h * u * h⁻¹, (Subgroup.mem_normalizer_iff.mp hh u).mp u.2⟩
  invFun u := ⟨h⁻¹ * u * h, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hh) u).mp u.2
    simpa using this⟩
  left_inv u := Subtype.ext (by simp [mul_assoc])
  right_inv u := Subtype.ext (by simp [mul_assoc])
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjSubEquiv_apply (U : Subgroup G) (h : G) (hh : h ∈ Subgroup.normalizer (U : Set G))
    (u : ↥U) : ((conjSubEquiv U h hh u : ↥U) : G) = h * u * h⁻¹ := rfl

section Quot

variable (U Z : Subgroup G) [(Z.subgroupOf U).Normal]

theorem conj_mem_iff_of_normal_ch611 {x u : G} (hx : x ∈ U) (hu : u ∈ U) :
    u * x * u⁻¹ ∈ Z ↔ x ∈ Z := by
  have hN : (Z.subgroupOf U).Normal := inferInstance
  constructor
  · intro h1
    have := hN.conj_mem ⟨u * x * u⁻¹, U.mul_mem (U.mul_mem hu hx) (U.inv_mem hu)⟩
      (Subgroup.mem_subgroupOf.mpr h1) (⟨u, hu⟩ : ↥U)⁻¹
    rw [Subgroup.mem_subgroupOf] at this
    simpa [mul_assoc] using this
  · intro h1
    have := hN.conj_mem ⟨x, hx⟩ (Subgroup.mem_subgroupOf.mpr h1) ⟨u, hu⟩
    rw [Subgroup.mem_subgroupOf] at this
    simpa [mul_assoc] using this

omit [(Z.subgroupOf U).Normal] in
theorem map_conjSubEquiv_subgroupOf (h : G) (hU : h ∈ Subgroup.normalizer (U : Set G))
    (hZ : h ∈ Subgroup.normalizer (Z : Set G)) :
    (Z.subgroupOf U).map (conjSubEquiv U h hU : ↥U →* ↥U) = Z.subgroupOf U := by
  ext x
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MonoidHom.coe_ofClass]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hZ y).mp hy
  · intro hx
    refine ⟨(conjSubEquiv U h hU).symm x, ?_, by simp⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hZ) x).mp hx
    rw [inv_inv] at this
    exact this

@[expose] noncomputable def conjQuotEquiv (h : G) (hU : h ∈ Subgroup.normalizer (U : Set G))
    (hZ : h ∈ Subgroup.normalizer (Z : Set G)) :
    (↥U ⧸ Z.subgroupOf U) ≃* (↥U ⧸ Z.subgroupOf U) :=
  QuotientGroup.congr (Z.subgroupOf U) (Z.subgroupOf U) (conjSubEquiv U h hU)
    (map_conjSubEquiv_subgroupOf U Z h hU hZ)

theorem conjQuotEquiv_mk (h : G) (hU : h ∈ Subgroup.normalizer (U : Set G))
    (hZ : h ∈ Subgroup.normalizer (Z : Set G)) (u : ↥U) :
    conjQuotEquiv U Z h hU hZ (u : ↥U ⧸ Z.subgroupOf U) =
      ((conjSubEquiv U h hU u : ↥U) : ↥U ⧸ Z.subgroupOf U) :=
  QuotientGroup.congr_mk _ _ _ _ u

@[expose] noncomputable def actQuot (K : Subgroup G) (hKU : K ≤ Subgroup.normalizer (U : Set G))
    (hKZ : K ≤ Subgroup.normalizer (Z : Set G)) : ↥K →* MulAut (↥U ⧸ Z.subgroupOf U) where
  toFun k := conjQuotEquiv U Z k (hKU k.2) (hKZ k.2)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H u =>
      rw [conjQuotEquiv_mk, MulAut.one_apply]
      congr 1
      exact Subtype.ext (by simp [conjSubEquiv_apply])
  map_mul' a b := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H u =>
      rw [MulAut.mul_apply, conjQuotEquiv_mk, conjQuotEquiv_mk, conjQuotEquiv_mk]
      congr 1
      exact Subtype.ext (by simp [conjSubEquiv_apply, mul_assoc])

variable {U Z} {K : Subgroup G} {hKU : K ≤ Subgroup.normalizer (U : Set G)}
  {hKZ : K ≤ Subgroup.normalizer (Z : Set G)}

theorem actQuot_mk (k : ↥K) (u : ↥U) :
    actQuot U Z K hKU hKZ k (u : ↥U ⧸ Z.subgroupOf U) =
      ((⟨(k : G) * u * (k : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKU k.2) u).mp u.2⟩ : ↥U) :
        ↥U ⧸ Z.subgroupOf U) :=
  conjQuotEquiv_mk U Z (k : G) (hKU k.2) (hKZ k.2) u

theorem actQuot_mk_eq_iff (k : ↥K) (u : ↥U) :
    actQuot U Z K hKU hKZ k (u : ↥U ⧸ Z.subgroupOf U) = (u : ↥U ⧸ Z.subgroupOf U) ↔
      (k : G) * u * (k : G)⁻¹ * (u : G)⁻¹ ∈ Z := by
  rw [actQuot_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hku : (k : G) * u * (k : G)⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hKU k.2) u).mp u.2
  have e : (((⟨(k : G) * u * (k : G)⁻¹, hku⟩ : ↥U)⁻¹ * u : ↥U) : G) =
      ((u : G)⁻¹ * ((k : G) * u * (k : G)⁻¹))⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e, Z.inv_mem_iff, ← conj_mem_iff_of_normal_ch611 U Z
    (U.mul_mem (U.inv_mem u.2) hku) u.2]
  have e2 : (u : G) * ((u : G)⁻¹ * ((k : G) * u * (k : G)⁻¹)) * (u : G)⁻¹ =
      (k : G) * u * (k : G)⁻¹ * (u : G)⁻¹ := by group
  rw [e2]

theorem actQuot_eq_one_iff (k : ↥K) :
    actQuot U Z K hKU hKZ k = 1 ↔ ∀ u ∈ U, (k : G) * u * (k : G)⁻¹ * u⁻¹ ∈ Z := by
  constructor
  · intro h1 u hu
    have := congrArg (fun φ : MulAut (↥U ⧸ Z.subgroupOf U) => φ (⟨u, hu⟩ : ↥U)) h1
    simp only [MulAut.one_apply] at this
    exact (actQuot_mk_eq_iff k ⟨u, hu⟩).mp this
  · intro h1
    ext x
    induction x using QuotientGroup.induction_on with
    | H u =>
      rw [MulAut.one_apply]
      exact (actQuot_mk_eq_iff k u).mpr (h1 u u.2)

theorem mem_centralizerMod_iff_actQuot {k : G} (hk : k ∈ K) :
    k ∈ centralizerMod Z K U ↔ actQuot U Z K hKU hKZ ⟨k, hk⟩ = 1 := by
  rw [actQuot_eq_one_iff, mem_centralizerMod]
  exact ⟨fun h1 => h1.2.2, fun h1 => ⟨hk, hKZ hk, h1⟩⟩

theorem mem_centralizerMod_iff_actQuot' (k : ↥K) :
    (k : G) ∈ centralizerMod Z K U ↔ actQuot U Z K hKU hKZ k = 1 :=
  mem_centralizerMod_iff_actQuot k.2

variable (U Z)

@[expose] noncomputable def quotSub (X : Subgroup G) : Subgroup (↥U ⧸ Z.subgroupOf U) :=
  (X.subgroupOf U).map (QuotientGroup.mk' (Z.subgroupOf U))

variable {U Z}

theorem mem_quotSub_iff {X : Subgroup G} (hZX : Z ≤ X) (u : ↥U) :
    (u : ↥U ⧸ Z.subgroupOf U) ∈ quotSub U Z X ↔ (u : G) ∈ X := by
  constructor
  · rintro ⟨y, hy, hyu⟩
    have hy' : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
    have h1 := QuotientGroup.eq.mp hyu
    rw [Subgroup.mem_subgroupOf] at h1
    have h2 : (u : G) = (y : G) * ((y⁻¹ * u : ↥U) : G) := by simp
    rw [h2]
    exact X.mul_mem hy' (hZX h1)
  · intro hu
    exact ⟨u, Subgroup.mem_subgroupOf.mpr hu, rfl⟩

theorem eq_of_quotSub_eq {X Y : Subgroup G} (hZX : Z ≤ X) (hZY : Z ≤ Y) (hXU : X ≤ U)
    (hYU : Y ≤ U) (hXY : quotSub U Z X = quotSub U Z Y) : X = Y := by
  ext x
  constructor
  · intro hx
    have h1 := (mem_quotSub_iff hZX ⟨x, hXU hx⟩).mpr hx
    rw [hXY] at h1
    exact (mem_quotSub_iff hZY ⟨x, hXU hx⟩).mp h1
  · intro hx
    have h1 := (mem_quotSub_iff hZY ⟨x, hYU hx⟩).mpr hx
    rw [← hXY] at h1
    exact (mem_quotSub_iff hZX ⟨x, hYU hx⟩).mp h1

theorem map_actQuot_quotSub (k : ↥K) (X : Subgroup G) :
    (quotSub U Z X).map (actQuot U Z K hKU hKZ k : MulAut (↥U ⧸ Z.subgroupOf U)).toMonoidHom =
      quotSub U Z (conjSubgroup X (k : G)⁻¹) := by
  ext q
  constructor
  · rintro ⟨p, ⟨y, hy, rfl⟩, rfl⟩
    have hy' : (y : G) ∈ X := Subgroup.mem_subgroupOf.mp hy
    refine ⟨⟨(k : G) * y * (k : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hKU k.2) y).mp y.2⟩,
      ?_, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf, mem_conjSubgroup_iff]
      simpa [mul_assoc] using hy'
    · simp only [QuotientGroup.mk'_apply, MulEquiv.coe_toMonoidHom]
      rw [actQuot_mk]
  · rintro ⟨p, hp, rfl⟩
    have hp' : (k : G)⁻¹ * p * (k : G)⁻¹⁻¹ ∈ X :=
      mem_conjSubgroup_iff.mp (Subgroup.mem_subgroupOf.mp hp)
    rw [inv_inv] at hp'
    refine ⟨((⟨(k : G)⁻¹ * p * k, ?_⟩ : ↥U) : ↥U ⧸ Z.subgroupOf U), ⟨⟨(k : G)⁻¹ * p * k, ?_⟩,
      ?_, rfl⟩, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (K.inv_mem k.2 |> hKU) p).mp p.2
      simpa using this
    · have := (Subgroup.mem_normalizer_iff.mp (K.inv_mem k.2 |> hKU) p).mp p.2
      simpa using this
    · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      exact hp'
    · simp only [MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
      rw [actQuot_mk]
      congr 1
      exact Subtype.ext (by simp [mul_assoc])

theorem card_quotSub [Finite G] {X : Subgroup G} (hZX : Z ≤ X) (hXU : X ≤ U) :
    Nat.card (quotSub U Z X) * Nat.card Z = Nat.card X := by
  set X' := X.subgroupOf U with hX'
  set f := (QuotientGroup.mk' (Z.subgroupOf U)).comp X'.subtype with hf
  have hrange : f.range = quotSub U Z X := by
    rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have hker : f.ker = (Z.subgroupOf U).subgroupOf X' := by
    rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    rfl
  have hZX' : Z.subgroupOf U ≤ X' := fun z hz => by
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    exact hZX hz
  have e1 : Nat.card ↥X' = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXU).toEquiv
  have e2 : Nat.card ↥((Z.subgroupOf U).subgroupOf X') = Nat.card Z := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZX').toEquiv]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hZX.trans hXU)).toEquiv
  have e3 : Nat.card (quotSub U Z X) = Nat.card (↥X' ⧸ (Z.subgroupOf U).subgroupOf X') := by
    rw [← hrange, ← hker]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv).symm
  rw [e3, ← e2, ← e1, ← Subgroup.card_eq_card_quotient_mul_card_subgroup]

theorem pCoreOf_range_actQuot_eq_bot [Finite G] (hO2 : IsO2Trivial K (centralizerMod Z K U)) :
    pCoreOf 2 (actQuot U Z K hKU hKZ).range = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := actQuot U Z K hKU hKZ with hρ
  set P := pCoreOf 2 ρ.range with hP
  have hPR : P ≤ ρ.range := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRP : ρ.range ≤ Subgroup.normalizer (P : Set _) :=
    CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 _
  set P' : Subgroup G := (P.comap ρ).map K.subtype with hP'
  have hP'K : P' ≤ K := Subgroup.map_subtype_le _
  have hKP' : K ≤ Subgroup.normalizer (P' : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hgR : ρ ⟨g, hg⟩ ∈ ρ.range := ⟨⟨g, hg⟩, rfl⟩
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨g, hg⟩ * k * (⟨g, hg⟩ : ↥K)⁻¹, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hRP hgR) _).mp hk
    · rintro ⟨k, hk, hkx⟩
      refine ⟨(⟨g, hg⟩ : ↥K)⁻¹ * k * ⟨g, hg⟩, ?_, ?_⟩
      · rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_inv]
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hRP hgR)) _).mp hk
        simpa using this
      · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hkx ⊢
        rw [hkx]
        group
  have hpow : ∀ p ∈ P', ∃ n : ℕ, p ^ 2 ^ n ∈ centralizerMod Z K U := by
    rintro _ ⟨k, hk, rfl⟩
    obtain ⟨n, hn⟩ := hP2 ⟨ρ k, hk⟩
    refine ⟨n, ?_⟩
    have h1 : ρ (k ^ 2 ^ n) = 1 := by
      have h0' := congrArg (Subtype.val : ↥P → MulAut (↥U ⧸ Z.subgroupOf U)) hn
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h0'
      rw [map_pow]
      exact h0'
    have h2 := (mem_centralizerMod_iff_actQuot' (hKU := hKU) (hKZ := hKZ) (k ^ 2 ^ n)).mpr h1
    rw [Subgroup.coe_pow] at h2
    exact h2
  have hle := hO2 P' hP'K hKP' hpow
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := hPR hx
  have hk : (k : G) ∈ P' := ⟨k, hx, rfl⟩
  exact Subgroup.mem_bot.mpr ((mem_centralizerMod_iff_actQuot' (hKU := hKU) (hKZ := hKZ)
    k).mp (hle hk))

end Quot

section Comm

class CommModCh611 (U Z : Subgroup G) : Prop where
  comm : ∀ a ∈ U, ∀ b ∈ U, a * b * a⁻¹ * b⁻¹ ∈ Z

variable {U Z : Subgroup G} [(Z.subgroupOf U).Normal]

instance commGroupQuot [hc : CommModCh611 U Z] : CommGroup (↥U ⧸ Z.subgroupOf U) :=
  { (inferInstance : Group (↥U ⧸ Z.subgroupOf U)) with
    mul_comm := fun x y => by
      induction x using QuotientGroup.induction_on with
      | H a =>
      induction y using QuotientGroup.induction_on with
      | H b =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have h1 := hc.comm _ (U.inv_mem b.2) _ (U.inv_mem a.2)
      simpa [mul_assoc] using h1 }

end Comm

end CFSG.Quasithin.H13
