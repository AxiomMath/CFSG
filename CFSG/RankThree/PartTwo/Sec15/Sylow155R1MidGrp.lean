module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155E0Defs
import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG.GH74.GLS
open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_with_same_image_of_trivial_quotient_action)

variable {G : Type} [Group G] [Finite G]

private theorem mem_layerOddPreimage_iff {H : Subgroup G} {x : G} :
    x ∈ layerOddPreimage H ↔ ∃ hx : x ∈ H,
      QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨x, hx⟩ ∈ layer (↥H ⧸ pPrimeCore 2 ↥H) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, h⟩
    exact ⟨⟨x, hx⟩, h, rfl⟩

private theorem characteristic_comap_layer (H : Subgroup G) :
    ((layer (↥H ⧸ pPrimeCore 2 ↥H)).comap
      (QuotientGroup.mk' (pPrimeCore 2 ↥H))).Characteristic := by
  refine Subgroup.characteristic_iff_le_comap.mpr fun φ x hx => ?_
  have hx' : QuotientGroup.mk' (pPrimeCore 2 ↥H) x ∈ layer (↥H ⧸ pPrimeCore 2 ↥H) := hx
  have hchar := CFSG.LocalCores.layer_characteristic (G := ↥H ⧸ pPrimeCore 2 ↥H)
  exact (Subgroup.characteristic_iff_le_comap.mp hchar)
    (QuotientGroup.congr (pPrimeCore 2 ↥H) (pPrimeCore 2 ↥H) φ (pPrimeCore_map_iso 2 φ)) hx'

theorem layerOddPreimage_le_self (H : Subgroup G) : layerOddPreimage H ≤ H :=
  Subgroup.map_subtype_le _

theorem pPrimeCoreOf_two_le_layerOddPreimage (H : Subgroup G) :
    pPrimeCoreOf 2 H ≤ layerOddPreimage H :=
  Subgroup.map_mono ((QuotientGroup.ker_mk' (pPrimeCore 2 ↥H)).symm.le.trans
    (MonoidHom.ker_le_comap _ _))

theorem normalizer_le_normalizer_layerOddPreimage (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (layerOddPreimage H : Set G) := by
  haveI := characteristic_comap_layer H
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    ((layer (↥H ⧸ pPrimeCore 2 ↥H)).comap (QuotientGroup.mk' (pPrimeCore 2 ↥H)))

theorem normalizer_le_normalizer_pPrimeCoreOf_two (H : Subgroup G) :
    Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (pPrimeCoreOf 2 H : Set G) :=
  CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (pPrimeCore 2 ↥H)

theorem layerOddPreimage_le_centralizer {H Z : Subgroup G} (hZ2 : IsPGroup 2 Z) (hZH : Z ≤ H)
    (hHZ : H ≤ Subgroup.normalizer (Z : Set G)) :
    layerOddPreimage H ≤ Subgroup.centralizer (Z : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro e he
  obtain ⟨heH, hel⟩ := mem_layerOddPreimage_iff.mp he
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  set O : Subgroup ↥H := pPrimeCore 2 ↥H
  set π : ↥H →* ↥H ⧸ O := QuotientGroup.mk' O
  set Z' : Subgroup ↥H := Z.subgroupOf H
  have hZ'n : Z'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hZH).mpr hHZ
  have hZ'2 : IsPGroup 2 Z' := hZ2.of_equiv (Subgroup.subgroupOfEquivOfLe hZH).symm
  have hzZ' : (⟨z, hZH hz⟩ : ↥H) ∈ Z' := hz
  have hmem : Z'.map π ∈ {K : Subgroup (↥H ⧸ O) | K.Normal ∧ IsPGroup 2 K} :=
    ⟨hZ'n.map π (QuotientGroup.mk'_surjective O), hZ'2.map π⟩
  have himg : π ⟨z, hZH hz⟩ ∈ CFSG.pCore 2 (↥H ⧸ O) :=
    le_sSup hmem (Subgroup.mem_map_of_mem π hzZ')
  have hcomm : π ⟨e, heH⟩ * π ⟨z, hZH hz⟩ = π ⟨z, hZH hz⟩ * π ⟨e, heH⟩ :=
    Subgroup.mem_centralizer_iff.mp (CFSG.WholeGroup.pCore_le_centralizer_layer 2 himg) _ hel
  set w : ↥H := ⟨e, heH⟩ * ⟨z, hZH hz⟩ * ⟨e, heH⟩⁻¹ * ⟨z, hZH hz⟩⁻¹ with hw
  have hwO : w ∈ O := by
    rw [← QuotientGroup.ker_mk' O, MonoidHom.mem_ker]
    change π w = 1
    simp only [hw, map_mul, map_inv, hcomm]
    group
  have hwZ : w ∈ Z' := by
    have h1 : (e : G) * z * (e : G)⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hHZ heH) z).mp hz
    exact Z.mul_mem h1 (Z.inv_mem hz)
  have hcop : Nat.Coprime (Nat.card Z') (Nat.card O) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hZ'2
    rw [hn]
    exact pPrimeCore_coprime_card.pow_left n
  have hw1 : w = 1 := Subgroup.disjoint_def.mp (Subgroup.disjoint_of_coprime_natCard hcop) hwZ hwO
  have hw2 : (e : G) * z * (e : G)⁻¹ * z⁻¹ = 1 := congrArg Subtype.val hw1
  have hw3 : (e : G) * z = z * e := by
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hw2
    exact hw2
  exact hw3.symm

theorem layerOddPreimage_eq_of_isSolvable {H : Subgroup G}
    (hs : Group.IsSolvable ↥(layerOddPreimage H)) : layerOddPreimage H = pPrimeCoreOf 2 H := by
  set O : Subgroup ↥H := pPrimeCore 2 ↥H
  set π : ↥H →* ↥H ⧸ O := QuotientGroup.mk' O with hπ
  set E₀ : Subgroup ↥H := (layer (↥H ⧸ O)).comap π with hEdef
  haveI : Group.IsSolvable ↥(E₀.map H.subtype) := hs
  have hE₀ : Group.IsSolvable ↥E₀ :=
    Group.isSolvable_of_surjective
      (f := (E₀.equivMapOfInjective H.subtype H.subtype_injective).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hL : Group.IsSolvable ↥(layer (↥H ⧸ O)) := by
    refine Group.isSolvable_of_surjective
      (f := (π.comp E₀.subtype).codRestrict (layer (↥H ⧸ O)) fun x => Subgroup.mem_comap.mp x.2)
      fun y => ?_
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective O (y : ↥H ⧸ O)
    exact ⟨⟨x, show π x ∈ layer (↥H ⧸ O) by rw [hπ, hx]; exact y.2⟩, Subtype.ext hx⟩
  have hbot : layer (↥H ⧸ O) = ⊥ := by
    by_contra hne
    haveI : Nontrivial ↥(layer (↥H ⧸ O)) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    haveI : Group.IsPerfect ↥(layer (↥H ⧸ O)) := CFSG.LocalCores.layer_isPerfect
    exact Group.IsPerfect.not_isSolvable _ hL
  show E₀.map H.subtype = (pPrimeCore 2 ↥H).map H.subtype
  rw [hEdef, hbot, MonoidHom.comap_bot, hπ, QuotientGroup.ker_mk']

theorem isSolvable_of_ker_odd_eq_one {K Q : Type*} [Group K] [Group Q] [Finite K] (f : K →* Q)
    (hf : Group.IsSolvable f.range) (hk : ∀ x ∈ f.ker, Odd (orderOf x) → x = 1) :
    Group.IsSolvable K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : IsPGroup 2 f.ker := by
    intro x
    obtain ⟨k, m, hm, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (x : K)).ne'
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : orderOf ((x : K) ^ 2 ^ k) = m := by
      rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) ⟨m, hord⟩, hord,
        Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
    exact hk _ (f.ker.pow_mem x.2 _) (h1 ▸ hm)
  haveI : Group.IsNilpotent f.ker := hker.isNilpotent
  haveI := hf
  exact Group.isSolvable_of_ker_le_range f.ker.subtype f.rangeRestrict
    ((MonoidHom.ker_rangeRestrict f).le.trans (Subgroup.range_subtype f.ker).ge)

theorem le_centralizer_of_cent_inf_le {R A O : Subgroup G} (hR2 : IsPGroup 2 R)
    (hA3 : IsPGroup 3 A) (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hRO : R ≤ Subgroup.normalizer (O : Set G)) (hOA : O ≤ Subgroup.centralizer (A : Set G))
    (hCO : R ⊓ Subgroup.centralizer (A : Set G) ≤ Subgroup.centralizer (O : Set G)) :
    R ≤ Subgroup.centralizer (O : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : ↥R →* MulAut ↥O := O.normalizerMonoidHom.comp (Subgroup.inclusion hRO)
  have hφ : ∀ (r : ↥R) (o : ↥O), ((φ r o : ↥O) : G) = (r : G) * o * (r : G)⁻¹ := fun r o =>
    O.normalizerMonoidHom_apply_apply_coe ⟨r, hRO r.2⟩ o
  have htrivial : ∀ (a : ↥A) (r : ↥R),
      φ ⟨(a : G) * r * (a : G)⁻¹, Subgroup.le_normalizer_iff.mp hAR a a.2 r r.2⟩ = φ r := by
    intro a r
    refine MulEquiv.ext fun o => Subtype.ext ?_
    rw [hφ, hφ]
    have ha : ∀ x ∈ O, (a : G) * x * (a : G)⁻¹ = x := fun x hx => by
      rw [Subgroup.mem_centralizer_iff.mp (hOA hx) a a.2, mul_inv_cancel_right]
    have hc : (a : G) * o = o * a := Subgroup.mem_centralizer_iff.mp (hOA o.2) a a.2
    have h2 : (a : G)⁻¹ * o * a = o := by
      rw [mul_assoc, ← hc, inv_mul_cancel_left]
    have hx : (r : G) * o * (r : G)⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hRO r.2) (o : G)).mp o.2
    calc (a : G) * r * (a : G)⁻¹ * (o : G) * ((a : G) * r * (a : G)⁻¹)⁻¹
        = (a : G) * ((r : G) * ((a : G)⁻¹ * o * a) * (r : G)⁻¹) * (a : G)⁻¹ := by group
      _ = (a : G) * ((r : G) * o * (r : G)⁻¹) * (a : G)⁻¹ := by rw [h2]
      _ = (r : G) * o * (r : G)⁻¹ := ha _ hx
  have hker : ¬ 3 ∣ Nat.card φ.ker := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hR2.to_subgroup φ.ker)
    rw [hn]
    intro h3
    have := Nat.prime_three.dvd_of_dvd_pow h3
    omega
  intro r hr
  obtain ⟨f, hfc, hf⟩ := exists_centralizer_with_same_image_of_trivial_quotient_action
    3 Nat.prime_three A R hA3 hAR φ hker htrivial ⟨r, hr⟩
  have hfO : (f : G) ∈ Subgroup.centralizer (O : Set G) := hCO ⟨f.2, hfc⟩
  have hφf : φ f = 1 := by
    refine MulEquiv.ext fun o => Subtype.ext ?_
    rw [hφ, MulAut.one_apply, ← Subgroup.mem_centralizer_iff.mp hfO o o.2, mul_inv_cancel_right]
  rw [hf] at hφf
  rw [Subgroup.mem_centralizer_iff]
  intro o ho
  have h := congrArg (fun m : MulAut ↥O => ((m ⟨o, ho⟩ : ↥O) : G)) hφf
  simp only [hφ, MulAut.one_apply] at h
  rw [mul_inv_eq_iff_eq_mul] at h
  exact h.symm

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
