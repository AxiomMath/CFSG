module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRestL7Cyclo
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRestL7Model
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRestL7Order
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight6xCRestL7Torus
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWJLangG2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KGD CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
  CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open Subgroup

namespace TrialityL7

private noncomputable abbrev torusEps_l7z {L : Type} [Field L]
    (Fr : L →+* L) (eps : ℤ) : Subgroup (ModGL TwistTag.D4.tag L) :=
  twistedTorusOf (canonicalRep (coxeterSystem TwistTag.D4.tag) L (twEps eps))
    (twistHom TwistTag.D4 L Fr)

private theorem three_dvd_pow_sub_eps_l7z {p f : ℕ} {eps : ℤ}
    (hq : (p : ZMod 3) ^ f = (eps : ZMod 3)) :
    (3 : ℤ) ∣ (p : ℤ) ^ f - eps := by
  have h : (((3 : ℕ) : ℤ)) ∣ (p : ℤ) ^ f - eps := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hq, sub_self]
  simpa using h

private theorem one_le_padicValNat_pow_sub_eps_l7z {p f : ℕ} (hp2 : 2 ≤ p ^ f) {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1) (hdvd : (3 : ℤ) ∣ (p : ℤ) ^ f - eps) :
    1 ≤ padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : ((p : ℤ) ^ f - eps) ≠ 0 := by
    have hpz : (2 : ℤ) ≤ (p : ℤ) ^ f := by exact_mod_cast hp2
    rcases heps with rfl | rfl <;> omega
  refine one_le_padicValNat_of_dvd (Int.natAbs_ne_zero.mpr hne) ?_
  exact (Int.natCast_dvd (m := 3)).mp hdvd

private theorem mem_ker_pow_map_l7z {A C : Type*} [CommGroup A] [Group C]
    (ψ : A →* C) (hψ : Function.Injective ψ) (t : C) :
    t ∈ ((powMonoidHom 3 : A →* A).ker).map ψ ↔ t ∈ ψ.range ∧ t ^ 3 = 1 := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨MonoidHom.mem_range.mpr ⟨x, rfl⟩, ?_⟩
    have hx3 : x ^ 3 = 1 := by
      have hx' := hx
      change (powMonoidHom 3) x = 1 at hx'
      simpa [powMonoidHom_apply] using hx'
    rw [← map_pow, hx3, map_one]
  · rintro ⟨⟨x, hx⟩, ht3⟩
    refine ⟨x, ?_, hx⟩
    change (powMonoidHom 3) x = 1
    rw [powMonoidHom_apply]
    apply hψ
    rw [map_pow, hx, ht3, map_one]

private theorem normalize_l7z {L : Type} [Field L] {C : Type} [Group C]
    {M : Subgroup (ModGL TwistTag.D4.tag L)} (e : C ≃* ↥M) {A : Type*} [CommGroup A]
    (ψ : A →* ↥M) {a : ℕ} {Tε : Subgroup (ModGL TwistTag.D4.tag L)}
    (hψrange : ∀ t : ↥M, t ∈ ψ.range ↔
      (t : ModGL TwistTag.D4.tag L) ∈ Tε ∧
        (t : ModGL TwistTag.D4.tag L) ^ (3 ^ (a + 1)) = 1)
    {yElt : ModGL TwistTag.D4.tag L} (hmem : yElt ∈ M)
    (hyT : ∀ t ∈ Tε, yElt * t * yElt⁻¹ ∈ Tε) :
    ∀ t ∈ (e.symm.toMonoidHom.comp ψ).range,
      (e.symm ⟨yElt, hmem⟩) * t * (e.symm ⟨yElt, hmem⟩)⁻¹ ∈
        (e.symm.toMonoidHom.comp ψ).range := by
  intro t ht
  obtain ⟨x, rfl⟩ := ht
  have hxT : (ψ x : ModGL TwistTag.D4.tag L) ∈ Tε :=
    ((hψrange (ψ x)).mp (MonoidHom.mem_range.mpr ⟨x, rfl⟩)).1
  have hxN : (ψ x : ModGL TwistTag.D4.tag L) ^ (3 ^ (a + 1)) = 1 :=
    ((hψrange (ψ x)).mp (MonoidHom.mem_range.mpr ⟨x, rfl⟩)).2
  let s : ↥M := ⟨yElt, hmem⟩ * ψ x * ⟨yElt, hmem⟩⁻¹
  have hsT : (s : ModGL TwistTag.D4.tag L) ∈ Tε := by
    have hcoe : (s : ModGL TwistTag.D4.tag L) =
        yElt * (ψ x : ModGL TwistTag.D4.tag L) * yElt⁻¹ := rfl
    rw [hcoe]
    exact hyT _ hxT
  have hsN : (s : ModGL TwistTag.D4.tag L) ^ (3 ^ (a + 1)) = 1 := by
    have hcoe : (s : ModGL TwistTag.D4.tag L) =
        yElt * (ψ x : ModGL TwistTag.D4.tag L) * yElt⁻¹ := rfl
    rw [hcoe, conj_pow, hxN, mul_one, mul_inv_cancel]
  obtain ⟨x', hx'⟩ := MonoidHom.mem_range.mp ((hψrange s).mpr ⟨hsT, hsN⟩)
  have hyx : (e.symm ⟨yElt, hmem⟩) * ((e.symm.toMonoidHom.comp ψ) x) *
      (e.symm ⟨yElt, hmem⟩)⁻¹ = e.symm s := by
    change e.symm ⟨yElt, hmem⟩ * e.symm (ψ x) * (e.symm ⟨yElt, hmem⟩)⁻¹ = e.symm s
    rw [← map_mul, ← map_inv, ← map_mul]
  rw [hyx, ← hx']
  exact MonoidHom.mem_range.mpr ⟨x', rfl⟩

private theorem moved_l7z {L : Type} [Field L] {C : Type} [Group C]
    {M : Subgroup (ModGL TwistTag.D4.tag L)} (e : C ≃* ↥M) {A : Type*} [CommGroup A]
    (ψ : A →* ↥M) (hψ : Function.Injective ψ) {a : ℕ}
    {Tε : Subgroup (ModGL TwistTag.D4.tag L)}
    (hψrange : ∀ t : ↥M, t ∈ ψ.range ↔
      (t : ModGL TwistTag.D4.tag L) ∈ Tε ∧
        (t : ModGL TwistTag.D4.tag L) ^ (3 ^ (a + 1)) = 1)
    {yElt : ModGL TwistTag.D4.tag L} (hmem : yElt ∈ M)
    {v₀ : ModGL TwistTag.D4.tag L} (hv₀T : v₀ ∈ Tε) (hv₀M : v₀ ∈ M) (hv₀3 : v₀ ^ 3 = 1)
    (hmove : yElt * v₀ * yElt⁻¹ ≠ v₀) :
    ∃ v ∈ ((powMonoidHom 3 : A →* A).ker).map (e.symm.toMonoidHom.comp ψ),
      (e.symm ⟨yElt, hmem⟩) * v * (e.symm ⟨yElt, hmem⟩)⁻¹ ≠ v := by
  have hpow : v₀ ^ (3 ^ (a + 1)) = 1 := by
    rw [pow_succ', pow_mul, hv₀3, one_pow]
  have hv₀range : (⟨v₀, hv₀M⟩ : ↥M) ∈ ψ.range :=
    (hψrange ⟨v₀, hv₀M⟩).mpr ⟨hv₀T, hpow⟩
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hv₀range
  have hx3 : x ^ 3 = 1 := by
    apply hψ
    rw [map_pow, hx, map_one]
    exact Subtype.ext (by simpa using hv₀3)
  refine ⟨e.symm ⟨v₀, hv₀M⟩, ?_, ?_⟩
  · refine Subgroup.mem_map.mpr ⟨x, ?_, ?_⟩
    · change (powMonoidHom 3) x = 1
      rw [powMonoidHom_apply]
      exact hx3
    · change e.symm (ψ x) = e.symm ⟨v₀, hv₀M⟩
      rw [hx]
  · intro hcon
    apply hmove
    have h := congrArg (fun z : C => (e z : ModGL TwistTag.D4.tag L)) hcon
    simp only [MulEquiv.map_mul, MulEquiv.map_inv, MulEquiv.apply_symm_apply] at h
    exact h

private theorem orderOf_symm_l7z {L : Type} [Field L] {C : Type} [Group C]
    {M : Subgroup (ModGL TwistTag.D4.tag L)} (e : C ≃* ↥M)
    {yElt : ModGL TwistTag.D4.tag L} (hmem : yElt ∈ M) (hyElt3 : orderOf yElt = 3) :
    orderOf (e.symm ⟨yElt, hmem⟩) = 3 := by
  rw [MulEquiv.orderOf_eq e.symm ⟨yElt, hmem⟩]
  rw [← Subgroup.orderOf_coe (⟨yElt, hmem⟩ : ↥M)]
  exact hyElt3

private theorem scalarAction_l7z {L : Type} [Field L] {C : Type} [Group C]
    {M : Subgroup (ModGL TwistTag.D4.tag L)} (e : C ≃* ↥M) (φ : MulAut C)
    (P : ModGL TwistTag.D4.tag L)
    (heP : ∀ x : C, (e (φ x) : ModGL TwistTag.D4.tag L) =
      P⁻¹ * (e x : ModGL TwistTag.D4.tag L) * P)
    {A : Type*} [CommGroup A] (ψ : A →* ↥M)
    {yElt : ModGL TwistTag.D4.tag L} (hmem : yElt ∈ M)
    (hyP : P⁻¹ * yElt * P = yElt) {k : ℤ}
    (hPt : ∀ x : A, P⁻¹ * (ψ x : ModGL TwistTag.D4.tag L) * P =
      (ψ x : ModGL TwistTag.D4.tag L) ^ k) :
    ScalarAction (e.symm.toMonoidHom.comp ψ).range φ (e.symm ⟨yElt, hmem⟩) k := by
  constructor
  · apply e.injective
    have h1 : (e (φ (e.symm ⟨yElt, hmem⟩)) : ModGL TwistTag.D4.tag L) = yElt := by
      rw [heP, e.apply_symm_apply]
      exact hyP
    have h2 : (e (e.symm ⟨yElt, hmem⟩) : ModGL TwistTag.D4.tag L) = yElt := by
      rw [e.apply_symm_apply]
    exact Subtype.ext (h1.trans h2.symm)
  · intro t ht
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp ht
    rw [← hx]
    apply e.injective
    have h1 : (e (φ ((e.symm.toMonoidHom.comp ψ) x)) : ModGL TwistTag.D4.tag L) =
        (ψ x : ModGL TwistTag.D4.tag L) ^ k := by
      change (e (φ (e.symm (ψ x))) : ModGL TwistTag.D4.tag L) =
        (ψ x : ModGL TwistTag.D4.tag L) ^ k
      rw [heP, e.apply_symm_apply, hPt]
    have h2 : (e (((e.symm.toMonoidHom.comp ψ) x) ^ k) : ModGL TwistTag.D4.tag L) =
        (ψ x : ModGL TwistTag.D4.tag L) ^ k := by
      change (e ((e.symm (ψ x)) ^ k) : ModGL TwistTag.D4.tag L) =
        (ψ x : ModGL TwistTag.D4.tag L) ^ k
      rw [map_zpow, e.apply_symm_apply, Subgroup.coe_zpow]
    exact Subtype.ext (h1.trans h2.symm)

private theorem fusion_l7z {L : Type} [Field L] {C : Type} [Group C] [Finite C]
    {M : Subgroup (ModGL TwistTag.D4.tag L)} (e : C ≃* ↥M)
    {W : Subgroup (ModGL TwistTag.D4.tag L)} (hW : MovingE9 M W)
    {Q T V : Subgroup C} {y : C} {e1 e2 : ℕ} (hSD : SD3 C Q T V y e1 e2) :
    ∀ z ∈ V, z ≠ 1 → y * z * y⁻¹ = z → Fusion27 z := by
  let ι : C →* ModGL TwistTag.D4.tag L := M.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := fun a b h => e.injective (Subtype.ext h)
  have hM : M ≤ ι.range := by
    intro x hx
    refine MonoidHom.mem_range.mpr ⟨e.symm ⟨x, hx⟩, ?_⟩
    change (e (e.symm ⟨x, hx⟩) : ModGL TwistTag.D4.tag L) = x
    rw [e.apply_symm_apply]
  exact fusion27_of_movingE9 hSD (hW.comap hι hM)

private theorem codRestrict_range_l7z {L : Type} [Field L]
    {M : Subgroup (ModGL TwistTag.D4.tag L)} {A : Type*} [CommGroup A]
    (ψ : A →* ModGL TwistTag.D4.tag L) (hψ : Function.Injective ψ) (hψM : ∀ x, ψ x ∈ M)
    {Tε : Subgroup (ModGL TwistTag.D4.tag L)} {a : ℕ}
    (hψrange : ∀ t : ModGL TwistTag.D4.tag L,
      t ∈ ψ.range ↔ t ∈ Tε ∧ t ^ (3 ^ (a + 1)) = 1) :
    ∃ ψD : A →* ↥M, Function.Injective ψD ∧
      ∀ t : ↥M, t ∈ ψD.range ↔
        (t : ModGL TwistTag.D4.tag L) ∈ Tε ∧
          (t : ModGL TwistTag.D4.tag L) ^ (3 ^ (a + 1)) = 1 := by
  refine ⟨ψ.codRestrict M hψM, ?_, ?_⟩
  · intro x y h
    exact hψ (congrArg Subtype.val h)
  · intro t
    constructor
    · rintro ⟨x, hx⟩
      have hx' : (t : ModGL TwistTag.D4.tag L) = ψ x := (congrArg Subtype.val hx).symm
      rw [hx']
      exact (hψrange (ψ x)).mp (MonoidHom.mem_range.mpr ⟨x, rfl⟩)
    · rintro ⟨htT, ht3⟩
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp ((hψrange _).mpr ⟨htT, ht3⟩)
      exact MonoidHom.mem_range.mpr ⟨x, Subtype.ext hx⟩

private theorem scalar_range_l7z {L : Type} [Field L]
    {p f a : ℕ} [IsAlgClosed L] [CharP L p] {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ (p ^ f)) {eps : ℤ} (heps : eps = 1 ∨ eps = -1)
    {K : Type} [Field K] [Finite K] [Algebra K L]
    (σ : K ≃+* K) (D : LangDatum TwistTag.D4.tag L)
    (e : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃* ↥D.model)
    {g0 : ModGL TwistTag.D4.tag L}
    (he : ∀ x, (e x : ModGL TwistTag.D4.tag L) = g0⁻¹ * triEmb K σ L x * g0)
    (hP : diagramMap TwistTag.D4 L * g0 = g0 * diagramMap TwistTag.D4 L)
    {A : Type} [CommGroup A] (ψD : A →* ↥D.model)
    (hψrange : ∀ t : ↥D.model, t ∈ ψD.range ↔
      (t : ModGL TwistTag.D4.tag L) ∈ torusEps_l7z Fr eps ∧
        (t : ModGL TwistTag.D4.tag L) ^ (3 ^ (a + 1)) = 1)
    (hyEltM : yElt L ∈ D.model) :
    ScalarAction (e.symm.toMonoidHom.comp ψD).range (fieldActor (t := TwistTag.D4) σ σ)
      (e.symm ⟨yElt L, hyEltM⟩) (eps * (p : ℤ) ^ f) := by
  have hyP : (diagramMap TwistTag.D4 L)⁻¹ * yElt L * diagramMap TwistTag.D4 L = yElt L := by
    rw [mul_assoc, ← diagramMap_comm_yElt, ← mul_assoc, inv_mul_cancel, one_mul]
  exact scalarAction_l7z e (fieldActor (t := TwistTag.D4) σ σ) (diagramMap TwistTag.D4 L)
    (fun x => modelEquiv_fieldActor e he hP x) ψD hyEltM hyP
    (fun x => diagramMap_conj_of_mem_twistedTorus hFr heps
      ((hψrange (ψD x)).mp (MonoidHom.mem_range.mpr ⟨x, rfl⟩)).1)

private theorem torus_data_l7z {L : Type} [Field L]
    {p f a : ℕ} [IsAlgClosed L] [CharP L p] [Fact p.Prime] (hf : 1 ≤ f) {Fr : L →+* L}
    (hFr : ∀ c, Fr c = c ^ (p ^ f)) {eps : ℤ} (heps : eps = 1 ∨ eps = -1)
    (hq : (p : ZMod 3) ^ f = (eps : ZMod 3)) (h3 : (3 : L) ≠ 0)
    {K : Type} [Field K] [Finite K] [Algebra K L] [IsAlgClosure K L]
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) (hK : Nat.card K = (p ^ f) ^ 3)
    (ha : a = padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps))) (ha1 : 1 ≤ a)
    (D : LangDatum TwistTag.D4.tag L)
    (e : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom) ≃* ↥D.model)
    {g0 : ModGL TwistTag.D4.tag L}
    (he : ∀ x, (e x : ModGL TwistTag.D4.tag L) = g0⁻¹ * triEmb K σ L x * g0)
    (hP : diagramMap TwistTag.D4 L * g0 = g0 * diagramMap TwistTag.D4 L)
    {ψ : Multiplicative (ZMod (3 ^ (a + 1))) × Multiplicative (ZMod (3 ^ a)) →*
      ModGL TwistTag.D4.tag L} (hψinj : Function.Injective ψ)
    (hψrange : ∀ t : ModGL TwistTag.D4.tag L, t ∈ ψ.range ↔
      t ∈ torusEps_l7z Fr eps ∧ t ^ (3 ^ (a + 1)) = 1)
    (hyEltM : yElt L ∈ D.model) (hTε : D.torus = torusEps_l7z Fr eps)
    (hyEltT : ∀ t ∈ torusEps_l7z Fr eps, yElt L * t * (yElt L)⁻¹ ∈ torusEps_l7z Fr eps) :
    ∃ (Q T V : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      SD3 _ Q T V y (a + 1) a ∧
        ScalarAction T (fieldActor (t := TwistTag.D4) σ σ) y (eps * (p : ℤ) ^ f) := by
  let C : Subgroup (ModGL TwistTag.D4.tag K) := graphFixedRootGroup TwistTag.D4 K σ.toRingHom
  let A := Multiplicative (ZMod (3 ^ (a + 1))) × Multiplicative (ZMod (3 ^ a))
  have hψM : ∀ x : A, ψ x ∈ D.model := fun x =>
    D.torus_le_model (by rw [hTε]; exact ((hψrange (ψ x)).mp
      (MonoidHom.mem_range.mpr ⟨x, rfl⟩)).1)
  obtain ⟨ψD, hψD, hψrangeD⟩ := codRestrict_range_l7z ψ hψinj hψM hψrange
  let ψC : A →* ↥C := e.symm.toMonoidHom.comp ψD
  have hψC : Function.Injective ψC := e.symm.injective.comp hψD
  let T : Subgroup ↥C := ψC.range
  let V : Subgroup ↥C := ((powMonoidHom 3 : A →* A).ker).map ψC
  let y : ↥C := e.symm ⟨yElt L, hyEltM⟩
  have hV : ∀ t : ↥C, t ∈ V ↔ t ∈ T ∧ t ^ 3 = 1 := mem_ker_pow_map_l7z ψC hψC
  have hT : Nonempty (A ≃* T) := ⟨MonoidHom.ofInjective hψC⟩
  have hyT : ∀ t ∈ T, y * t * y⁻¹ ∈ T := normalize_l7z e ψD hψrangeD hyEltM hyEltT
  have hy3 : orderOf y = 3 := orderOf_symm_l7z e hyEltM (orderOf_yElt h3)
  obtain ⟨v₀, hv₀T, hv₀3, hv₀ne⟩ := exists_moved_by_yElt (L := L) h3 hFr heps hq
  have hv₀M : v₀ ∈ D.model := D.torus_le_model (by rw [hTε]; exact hv₀T)
  have hmove : ∃ v ∈ V, y * v * y⁻¹ ≠ v :=
    moved_l7z e ψD hψD hψrangeD hyEltM hv₀T hv₀M hv₀3 hv₀ne
  have hp : p.Prime := Fact.out
  have hcard : padicValNat 3 (Nat.card ↥C) = 2 * a + 2 := by
    rw [ha]
    exact padicValNat_card_graphFixedRootGroup_D4 (K := K) hp hf hK σ hσ heps hq
  have hSD : SD3 ↥C (T ⊔ Subgroup.zpowers y) T V y (a + 1) a :=
    sd3_of_torus (by omega) ha1 hT hV hyT hy3 hmove (by rw [hcard]; omega) rfl
  have hScalar := scalar_range_l7z (L := L) (p := p) (f := f) (a := a) hFr heps σ D e he hP
    ψD hψrangeD hyEltM
  exact ⟨T ⊔ Subgroup.zpowers y, T, V, y, hSD, hScalar⟩

private theorem lang_torus_l7z {L : Type} [Field L]
    {p f : ℕ} [IsAlgClosed L] [CharP L p] [Fact p.Prime] (hf : 1 ≤ f) {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1) (hq : (p : ZMod 3) ^ f = (eps : ZMod 3)) (h3 : (3 : L) ≠ 0)
    {K : Type} [Field K] [Finite K] [Algebra K L] [IsAlgClosure K L] (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (p ^ f)) (hK : Nat.card K = (p ^ f) ^ 3) {a : ℕ} (ha1 : 1 ≤ a)
    (ha : a = padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps))) :
    ∃ (Q T V : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom))
      (y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)),
      SD3 _ Q T V y (a + 1) a ∧
        ScalarAction T (fieldActor (t := TwistTag.D4) σ σ) y (eps * (p : ℤ) ^ f) := by
  let Fr : L →+* L := iterateFrobenius L p f
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hp : p.Prime := Fact.out
  obtain ⟨g0, hg0C, hP, hg0⟩ := exists_lang_g2_D4 (ℓ := p) (f := f) (L := L) hf
    (canonicalRep (coxeterSystem TwistTag.D4.tag) L (twEps eps))
    (canonicalRep_mem_adjointGroup (coxeterSystem TwistTag.D4.tag) L (twEps eps))
    (diagramMap_comm_canonicalRep (twEps_mem_relWeylTwist eps))
  let D := LangDatum.ofTwist TwistTag.D4 Fr (p ^ f) hFr (twEps eps) hg0C hg0
  obtain ⟨e, he⟩ := exists_modelEquiv (K := K) (σ := σ) (L := L) hp hf hK hσ Fr hFr
    (twEps eps) hg0C hg0
  obtain ⟨ψ, hψinj, hψrange⟩ :=
    exists_torusCoords (L := L) h3 hp hf Fr hFr heps hq (a := a) ha
  have hyEltM : yElt L ∈ D.model :=
    tw_mem_model D (yElt_mem_monomialSubgroup (L := L)) (yElt_fixed (L := L) Fr eps)
  have hyEltT : ∀ t ∈ torusEps_l7z Fr eps, yElt L * t * (yElt L)⁻¹ ∈ torusEps_l7z Fr eps :=
    fun t ht =>
      tw_conj_mem_torus D (yElt_mem_monomialSubgroup (L := L)) (yElt_fixed (L := L) Fr eps) ht
  exact torus_data_l7z (L := L) (p := p) (f := f) (a := a) hf hFr heps hq h3 σ hσ hK ha ha1
    D e he hP hψinj hψrange hyEltM rfl hyEltT

private theorem lang_fusion_l7z {L : Type} [Field L]
    {p f : ℕ} [IsAlgClosed L] [CharP L p] [Fact p.Prime] (hf : 1 ≤ f) {eps : ℤ}
    (heps : eps = 1 ∨ eps = -1) (hq : (p : ZMod 3) ^ f = (eps : ZMod 3)) (h3 : (3 : L) ≠ 0)
    (h2 : 2 ≤ p ^ f) {K : Type} [Field K] [Finite K] [Algebra K L] [IsAlgClosure K L]
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (p ^ f)) (hK : Nat.card K = (p ^ f) ^ 3)
    {a : ℕ} {Q T V : Subgroup ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    {y : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hSD : SD3 _ Q T V y (a + 1) a) :
    ∀ z ∈ V, z ≠ 1 → y * z * y⁻¹ = z → Fusion27 z := by
  let Fr : L →+* L := iterateFrobenius L p f
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hp : p.Prime := Fact.out
  obtain ⟨g0', hg0C', hg0'⟩ := lang_conjugator_D4 (K := K) (ℓ := p) (f := f) (L := L) hf
    (canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps)))
    (canonicalRep_mem_adjointGroup (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps)))
  obtain ⟨e', _⟩ := exists_modelEquiv (K := K) (σ := σ) (L := L) hp hf hK hσ Fr hFr
    ((coxeterSystem TwistTag.D4.tag).wordProd (cycWord eps)) hg0C' hg0'
  obtain ⟨W, hW⟩ :=
    movingE9_cyc (L := L) h3 h2 Fr hFr heps (by push_cast; exact hq) hg0C' hg0'
  exact fusion_l7z e' hW hSD

end TrialityL7

open TrialityL7

theorem trialityTarget_holds : TrialityTarget := by
  intro K _ _ p f hp hp3 hf hK σ hσ eps heps hq
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype K := Fintype.ofFinite K
  have : CharP K p := charP_of_card_eq_prime_pow (f := f * 3)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  let L := AlgebraicClosure K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : CharP L p := charP_of_injective_algebraMap (algebraMap K L).injective p
  let Fr : L →+* L := iterateFrobenius L p f
  have hFr : ∀ c, Fr c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have h3 : (3 : L) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : L) = 0 := h
    rw [CharP.cast_eq_zero_iff L p 3] at h'
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h')
  have h2 : 2 ≤ p ^ f := by
    have h := Nat.one_lt_pow (a := p) (n := f) (by omega) hp.one_lt
    omega
  have hdvd : (3 : ℤ) ∣ (p : ℤ) ^ f - eps := three_dvd_pow_sub_eps_l7z hq
  let a := padicValNat 3 (Int.natAbs ((p : ℤ) ^ f - eps))
  have ha1 : 1 ≤ a := one_le_padicValNat_pow_sub_eps_l7z h2 heps hdvd
  obtain ⟨Q, T, V, y, hSD, hScalar⟩ :=
    lang_torus_l7z (L := L) (p := p) (f := f) hf heps hq h3 (K := K) σ hσ hK
      (a := a) ha1 rfl
  have hFus : ∀ z ∈ V, z ≠ 1 → y * z * y⁻¹ = z → Fusion27 z :=
    lang_fusion_l7z (L := L) (p := p) (f := f) hf heps hq h3 h2 (K := K) σ hσ hK hSD
  exact ⟨Q, T, V, y, hSD, hScalar, hFus⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
