module

public import CFSG.LocalAnalysis.StandardType.SupportedTorusFixedKernel
public import CFSG.RankThree.PartOne.KE6.E8T3E6
public import CFSG.RankThree.PartOne.KE.D4TranspositionInterface
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117

public section

namespace CFSG.StandardType

open Matrix CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.RankThree.PartOne.KE6 CFSG.RankThree.PartOne.KE

theorem seven_sq_dvd_card_rootSpan_inf_twistedFixedPoints {L : Type} [Field L] [IsAlgClosed L]
    [CharP L 2] (n : ModGL Tag.E8 L) (hnm : n ∈ monomialSubgroup Tag.E8 L)
    {J : Set (Fin Tag.E8.rank)} (hJ : J = e6Nodes Tag.E8 ∨ J = d4Nodes Tag.E8)
    (hmaps : ∀ β ∈ parabolicRoots Tag.E8 J,
      weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • β ∈ parabolicRoots Tag.E8 J)
    (hrel : ∀ x : Fin Tag.E8.rank → ℤ,
      weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x +
        weylQuotientHom Tag.E8 L ⟨n, hnm⟩ • x + x = 0) :
    7 ^ 2 ∣ Nat.card ↥(rootSpan Tag.E8 L (parabolicRoots Tag.E8 J) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L 2 1)))) := by
  classical
  have hFr : ∀ c : L, iterateFrobenius L 2 1 c = c ^ (2 : ℕ) := fun c => by
    rw [iterateFrobenius_def, pow_one]
  have hq : (((2 : ℕ) : L) ^ 2 + ((2 : ℕ) : L) + 1) ≠ 0 := by
    rw [CharP.cast_eq_zero L 2]
    simp
  rcases hJ with rfl | rfl
  · haveI : Fintype ↥(e6Nodes Tag.E8) := Fintype.ofFinite _
    obtain ⟨E, hE, hcard⟩ := exists_subgroup_le_rootSpan_inf_twistedFixedPoints (τ := Tag.E8)
      (Ω := L) (J := e6Nodes Tag.E8) rfl hFr n hnm hmaps hrel
      (by rw [det_cartanBlock_e6Nodes]; norm_num) hq
      (by rw [det_cartanBlock_e6Nodes]; decide)
    have h343 : Nat.card E = 343 := by
      have h : Nat.card E ^ 2 = 343 ^ 2 := by
        rw [hcard, card_e6Nodes]
        norm_num
      exact Nat.pow_left_injective (by norm_num) h
    exact (by rw [h343]; norm_num : 7 ^ 2 ∣ Nat.card E).trans (Subgroup.card_dvd_of_le hE)
  · haveI : Fintype ↥(d4Nodes Tag.E8) := Fintype.ofFinite _
    obtain ⟨E, hE, hcard⟩ := exists_subgroup_le_rootSpan_inf_twistedFixedPoints (τ := Tag.E8)
      (Ω := L) (J := d4Nodes Tag.E8) rfl hFr n hnm hmaps hrel
      (by rw [det_cartanBlock_d4Nodes]; norm_num) hq
      (by rw [det_cartanBlock_d4Nodes]; decide)
    have h49 : Nat.card E = 49 := by
      have h : Nat.card E ^ 2 = 49 ^ 2 := by
        rw [hcard, card_d4Nodes]
        norm_num
      exact Nat.pow_left_injective (by norm_num) h
    exact (by rw [h49]; norm_num : 7 ^ 2 ∣ Nat.card E).trans (Subgroup.card_dvd_of_le hE)

theorem eq_one_of_pow_seven_of_mem_center_rootSpan {L : Type} [Field L]
    {J : Set (Fin Tag.E8.rank)} (hJ : J = e6Nodes Tag.E8 ∨ J = d4Nodes Tag.E8)
    {z : ModGL Tag.E8 L} (hzQ : z ∈ rootSpan Tag.E8 L (parabolicRoots Tag.E8 J))
    (hzC : z ∈ Subgroup.centralizer
      (rootSpan Tag.E8 L (parabolicRoots Tag.E8 J) : Set (ModGL Tag.E8 L)))
    (hz7 : z ^ 7 = 1) : z = 1 := by
  classical
  rcases hJ with rfl | rfl
  · haveI : Fintype ↥(e6Nodes Tag.E8) := Fintype.ofFinite _
    exact eq_one_of_pow_eq_one_of_mem_center_rootSpan (J := e6Nodes Tag.E8) rfl hzQ hzC
      (by rw [det_cartanBlock_e6Nodes]; decide) hz7
  · haveI : Fintype ↥(d4Nodes Tag.E8) := Fintype.ofFinite _
    exact eq_one_of_pow_eq_one_of_mem_center_rootSpan (J := d4Nodes Tag.E8) rfl hzQ hzC
      (by rw [det_cartanBlock_d4Nodes]; decide) hz7

theorem map_conj_rootSpan_inf_twistedFixedPoints {L : Type} [Field L] (Fr : L →+* L)
    (hFr : Function.Bijective Fr) (v : WeylGroup Tag.E8) (n : ModGL Tag.E8 L)
    {S₀ : Set (Fin Tag.E8.rank → ℤ)} (hS₀ : ∀ r ∈ S₀, IsRoot Tag.E8 r) :
    (rootSpan Tag.E8 L S₀ ⊓ twistedFixedPoints
        ((canonicalRep (coxeterSystem Tag.E8) L v)⁻¹ * n * canonicalRep (coxeterSystem Tag.E8) L v)
        (Units.map (entrywiseHom Fr))).map
      (MulAut.conj (canonicalRep (coxeterSystem Tag.E8) L v)).toMonoidHom =
    rootSpan Tag.E8 L ((fun γ => v • γ) '' S₀) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom Fr)) := by
  classical
  set Φ : ModGL Tag.E8 L →* ModGL Tag.E8 L := Units.map (entrywiseHom Fr) with hΦ
  set V : ModGL Tag.E8 L := canonicalRep (coxeterSystem Tag.E8) L v with hV
  have hΦV : Φ V = V := by
    have h1 := entrywise_canonicalRep (RingEquiv.ofBijective Fr hFr) v
    have h2 : (RingEquiv.ofBijective Fr hFr).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at h1
    exact h1
  set c₀ : ModGL Tag.E8 L →* ModGL Tag.E8 L := (MulAut.conj V).toMonoidHom with hc₀
  have hcapp : ∀ x, c₀ x = V * x * V⁻¹ := fun x => by simp [hc₀, MulAut.conj_apply]
  have hQ : (rootSpan Tag.E8 L S₀).map c₀ = rootSpan Tag.E8 L ((fun γ => v • γ) '' S₀) :=
    map_conj_rootSpan v hS₀
  have hR : (twistedFixedPoints (V⁻¹ * n * V) Φ).map c₀ = twistedFixedPoints n Φ := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hcapp]
      exact (mem_twistedFixedPoints_conj hΦV).1 hx
    · intro hy
      refine ⟨V⁻¹ * y * V, (mem_twistedFixedPoints_conj hΦV).2 ?_, ?_⟩
      · have e : V * (V⁻¹ * y * V) * V⁻¹ = y := by group
        rw [e]
        exact hy
      · rw [hcapp]
        group
  rw [Subgroup.map_inf _ _ c₀ (MulAut.conj V).injective, hQ, hR]

theorem seven_sq_dvd_card_rootSpan_image_inf_twistedFixedPoints {L : Type} [Field L]
    [IsAlgClosed L] [CharP L 2] (v : WeylGroup Tag.E8) (n : ModGL Tag.E8 L)
    (hnm : n ∈ monomialSubgroup Tag.E8 L) {J : Set (Fin Tag.E8.rank)}
    (hJ : J = e6Nodes Tag.E8 ∨ J = d4Nodes Tag.E8)
    (hmaps : ∀ β ∈ parabolicRoots Tag.E8 J,
      (v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * v) • β ∈ parabolicRoots Tag.E8 J)
    (hrel : ∀ x : Fin Tag.E8.rank → ℤ,
      (v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * v) •
          (v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * v) • x +
        (v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * v) • x + x = 0) :
    7 ^ 2 ∣ Nat.card ↥(rootSpan Tag.E8 L ((fun γ => v • γ) '' parabolicRoots Tag.E8 J) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L 2 1)))) := by
  classical
  set Fr : L →+* L := iterateFrobenius L 2 1 with hFrdef
  have hFr : ∀ c : L, Fr c = c ^ 2 := fun c => by rw [hFrdef, iterateFrobenius_def, pow_one]
  have hFrbij : Function.Bijective Fr := ⟨Fr.injective, fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y (show 0 < 2 by norm_num)
    exact ⟨x, by rw [hFr, hx]⟩⟩
  set V : ModGL Tag.E8 L := canonicalRep (coxeterSystem Tag.E8) L v with hV
  have hVm : V ∈ monomialSubgroup Tag.E8 L := canonicalRep_mem_monomialSubgroup L v
  set n' : ModGL Tag.E8 L := V⁻¹ * n * V with hn'
  have hn'm : n' ∈ monomialSubgroup Tag.E8 L := mul_mem (mul_mem (inv_mem hVm) hnm) hVm
  have hπV : weylQuotientHom Tag.E8 L ⟨V, hVm⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn' : weylQuotientHom Tag.E8 L ⟨n', hn'm⟩ =
      v⁻¹ * weylQuotientHom Tag.E8 L ⟨n, hnm⟩ * v := by
    have : (⟨n', hn'm⟩ : monomialSubgroup Tag.E8 L) = ⟨V, hVm⟩⁻¹ * ⟨n, hnm⟩ * ⟨V, hVm⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hπV]
  have hdvd := seven_sq_dvd_card_rootSpan_inf_twistedFixedPoints n' hn'm hJ
    (by rw [hπn']; exact hmaps) (fun x => by rw [hπn']; exact hrel x)
  have hroots : ∀ r ∈ parabolicRoots Tag.E8 J, IsRoot Tag.E8 r := fun r hr => hr.1
  have hmap := map_conj_rootSpan_inf_twistedFixedPoints Fr hFrbij v n hroots
  rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj V).injective]
  exact hdvd

theorem eq_one_of_pow_seven_of_central_of_centralizer {L : Type} [Field L] (v : WeylGroup Tag.E8)
    {J : Set (Fin Tag.E8.rank)} (hJ : J = e6Nodes Tag.E8 ∨ J = d4Nodes Tag.E8)
    {P : Subgroup (ModGL Tag.E8 L)}
    (hPQ : P ≤ rootSpan Tag.E8 L ((fun γ => v • γ) '' parabolicRoots Tag.E8 J))
    (hPC : ∀ y ∈ P, (∀ u ∈ P, y * u = u * y) → y ∈ Subgroup.centralizer
      (rootSpan Tag.E8 L ((fun γ => v • γ) '' parabolicRoots Tag.E8 J) : Set (ModGL Tag.E8 L))) :
    ∀ z ∈ P, (∀ w ∈ P, z * w = w * z) → z ^ 7 = 1 → z = 1 := by
  classical
  intro z hz hzc hz7
  set V : ModGL Tag.E8 L := canonicalRep (coxeterSystem Tag.E8) L v with hV
  set c₀ : ModGL Tag.E8 L →* ModGL Tag.E8 L := (MulAut.conj V).toMonoidHom with hc₀
  have hcapp : ∀ x, c₀ x = V * x * V⁻¹ := fun x => by simp [hc₀, MulAut.conj_apply]
  have hcinj : Function.Injective c₀ := (MulAut.conj V).injective
  have hroots : ∀ r ∈ parabolicRoots Tag.E8 J, IsRoot Tag.E8 r := fun r hr => hr.1
  have hQ : (rootSpan Tag.E8 L (parabolicRoots Tag.E8 J)).map c₀ =
      rootSpan Tag.E8 L ((fun γ => v • γ) '' parabolicRoots Tag.E8 J) :=
    map_conj_rootSpan v hroots
  have hzQ : z ∈ (rootSpan Tag.E8 L (parabolicRoots Tag.E8 J)).map c₀ := by
    rw [hQ]
    exact hPQ hz
  obtain ⟨q, hq, hqz⟩ := hzQ
  have hzC := hPC z hz hzc
  have hqC : q ∈ Subgroup.centralizer
      (rootSpan Tag.E8 L (parabolicRoots Tag.E8 J) : Set (ModGL Tag.E8 L)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q' hq'
    have h1 : c₀ q' ∈ rootSpan Tag.E8 L ((fun γ => v • γ) '' parabolicRoots Tag.E8 J) := by
      rw [← hQ]
      exact ⟨q', hq', rfl⟩
    have h2 := Subgroup.mem_centralizer_iff.1 hzC _ h1
    rw [← hqz, ← map_mul, ← map_mul] at h2
    exact hcinj h2
  have hq7 : q ^ 7 = 1 := by
    apply hcinj
    rw [map_pow, hqz, hz7, map_one]
  have hq1 := eq_one_of_pow_seven_of_mem_center_rootSpan hJ hq hqC hq7
  rw [← hqz, hq1, map_one]

end CFSG.StandardType
