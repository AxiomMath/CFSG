module

public import CFSG.RankThree.PartTwo.Sec19.KF1923ParSmallCore
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K21dStmt

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {X : Type} [Group X] [Finite X]

@[expose] def ksmOrbit (N : Subgroup X) (x : X) : Set X :=
  {g | ∃ n ∈ N, n * x * n⁻¹ = g}

@[expose] def ksmT (E : Subgroup X) : Set X := (E : Set X) \ {1}

@[expose] def ksmS (w z : X) : Set X := {z, z⁻¹, w * z * w⁻¹, (w * z * w⁻¹)⁻¹}

theorem ksm_conj_inv (w z : X) : w * z⁻¹ * w⁻¹ = (w * z * w⁻¹)⁻¹ := by group

theorem ksm_card_centralizer_mul_orbit (N : Subgroup X) (x : X) :
    Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set X)) * Nat.card ↥(ksmOrbit N x) =
      Nat.card N := by
  letI : MulAction N X := MulAction.compHom X ((MulAut.conj : X →* MulAut X).comp N.subtype)
  have hsmul : ∀ (n : N) (a : X), n • a = (n : X) * a * (n : X)⁻¹ := fun n a => rfl
  have horb : MulAction.orbit N x = ksmOrbit N x := by
    ext g
    constructor
    · rintro ⟨n, rfl⟩
      exact ⟨(n : X), n.2, (hsmul n x).symm⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨⟨n, hn⟩, hsmul ⟨n, hn⟩ x⟩
  have hstab : (MulAction.stabilizer N x).map N.subtype =
      N ⊓ Subgroup.centralizer ({x} : Set X) := by
    ext g
    constructor
    · intro hg
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.1 hg
      have hnx : (n : X) * x * (n : X)⁻¹ = x := by
        rw [← hsmul]
        exact MulAction.mem_stabilizer_iff.1 hn
      refine Subgroup.mem_inf.2 ⟨n.2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      exact (mul_inv_eq_iff_eq_mul.1 hnx).symm
    · intro hg
      obtain ⟨hgN, hgC⟩ := Subgroup.mem_inf.1 hg
      rw [Subgroup.mem_centralizer_iff] at hgC
      have hxg : x * g = g * x := hgC x (Set.mem_singleton x)
      refine Subgroup.mem_map.2 ⟨⟨g, hgN⟩, ?_, rfl⟩
      rw [MulAction.mem_stabilizer_iff, hsmul]
      show g * x * g⁻¹ = x
      rw [mul_inv_eq_iff_eq_mul]
      exact hxg.symm
  have h1 : Nat.card ↥((MulAction.stabilizer N x).map N.subtype) =
      Nat.card ↥(MulAction.stabilizer N x) :=
    Subgroup.card_map_of_injective N.subtype_injective
  rw [hstab] at h1
  have h2 : Nat.card ↥(MulAction.orbit N x) = (MulAction.stabilizer N x).index := by
    rw [Subgroup.index]
    exact Nat.card_congr (MulAction.orbitEquivQuotientStabilizer N x)
  have h3 := Subgroup.card_mul_index (MulAction.stabilizer N x)
  rw [horb] at h2
  rw [h1, h2]
  exact h3

theorem ksm_orbit_eq_of_mem {N : Subgroup X} {z g : X} (hg : g ∈ ksmOrbit N z) :
    ksmOrbit N g = ksmOrbit N z := by
  obtain ⟨m, hm, rfl⟩ := hg
  ext h
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n * m, N.mul_mem hn hm, by group⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n * m⁻¹, N.mul_mem hn (N.inv_mem hm), by group⟩

theorem ksm_orbit_subset_T {N E : Subgroup X} (hNE : N ≤ Subgroup.normalizer (E : Set X))
    {z : X} (hz : z ∈ E) (hz1 : z ≠ 1) : ksmOrbit N z ⊆ ksmT E := by
  rintro g ⟨n, hn, rfl⟩
  refine Set.mem_diff_of_mem ((Subgroup.mem_normalizer_iff.1 (hNE hn) z).1 hz) ?_
  intro h
  apply hz1
  have h1 : n * z * n⁻¹ = 1 := Set.mem_singleton_iff.1 h
  calc z = n⁻¹ * (n * z * n⁻¹) * n := by group
    _ = 1 := by rw [h1]; group

theorem ksm_mem_T {E : Subgroup X} {g : X} (hg : g ∈ E) (hg1 : g ≠ 1) : g ∈ ksmT E :=
  Set.mem_diff_of_mem hg (fun h => hg1 (Set.mem_singleton_iff.1 h))

theorem ksm_ne_inv_of_three {z : X} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) : z ≠ z⁻¹ := by
  intro h
  apply hz1
  have h2 : z ^ 2 = 1 := by
    rw [pow_two]
    calc z * z = z * z⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel z
  calc z = z ^ 3 * (z ^ 2)⁻¹ := by group
    _ = 1 := by rw [hz3, h2]; simp

theorem ksm_sig_mem {N E : Subgroup X} (hNE : N ≤ Subgroup.normalizer (E : Set X)) {w : X}
    (hwN : w ∈ N) {z : X} (hz : z ∈ E) : w * z * w⁻¹ ∈ E :=
  (Subgroup.mem_normalizer_iff.1 (hNE hwN) z).1 hz

theorem ksm_sig_ne_one {w z : X} (hz1 : z ≠ 1) : w * z * w⁻¹ ≠ 1 := by
  intro h
  apply hz1
  calc z = w⁻¹ * (w * z * w⁻¹) * w := by group
    _ = 1 := by rw [h]; group

theorem ksm_sig2 {E : Subgroup X} {w : X} (hw2 : ∀ e ∈ E, w ^ 2 * e * (w ^ 2)⁻¹ = e⁻¹)
    {u : X} (hu : u ∈ E) : w * (w * u * w⁻¹) * w⁻¹ = u⁻¹ := by
  have h1 : w * (w * u * w⁻¹) * w⁻¹ = w ^ 2 * u * (w ^ 2)⁻¹ := by
    simp only [pow_two, mul_inv_rev, mul_assoc]
  rw [h1]
  exact hw2 u hu

theorem ksmS_subset_orbit {N E : Subgroup X} {w z : X} (hwN : w ∈ N)
    (hw2 : ∀ e ∈ E, w ^ 2 * e * (w ^ 2)⁻¹ = e⁻¹) (hz : z ∈ E) :
    ksmS w z ⊆ ksmOrbit N z := by
  rintro g (hg | hg | hg | hg)
  · rw [hg]
    exact ⟨1, N.one_mem, by simp⟩
  · rw [hg]
    exact ⟨w ^ 2, pow_mem hwN 2, hw2 z hz⟩
  · rw [hg]
    exact ⟨w, hwN, rfl⟩
  · rw [hg]
    refine ⟨w ^ 3, pow_mem hwN 3, ?_⟩
    calc w ^ 3 * z * (w ^ 3)⁻¹ = w * (w ^ 2 * z * (w ^ 2)⁻¹) * w⁻¹ := by group
      _ = w * z⁻¹ * w⁻¹ := by rw [hw2 z hz]
      _ = (w * z * w⁻¹)⁻¹ := ksm_conj_inv w z

theorem ksmS_subset_T {N E : Subgroup X} (hNE : N ≤ Subgroup.normalizer (E : Set X)) {w z : X}
    (hwN : w ∈ N) (hz : z ∈ E) (hz1 : z ≠ 1) : ksmS w z ⊆ ksmT E := by
  have hσ : w * z * w⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 (hNE hwN) z).1 hz
  have hσ1 : w * z * w⁻¹ ≠ 1 := by
    intro h
    apply hz1
    calc z = w⁻¹ * (w * z * w⁻¹) * w := by group
      _ = 1 := by rw [h]; group
  rintro g (hg | hg | hg | hg)
  · rw [hg]
    exact ksm_mem_T hz hz1
  · rw [hg]
    exact ksm_mem_T (E.inv_mem hz) (inv_ne_one.2 hz1)
  · rw [hg]
    exact ksm_mem_T hσ hσ1
  · rw [hg]
    exact ksm_mem_T (E.inv_mem hσ) (inv_ne_one.2 hσ1)

theorem ksmS_ncard {w z : X} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hσ3 : (w * z * w⁻¹) ^ 3 = 1) (hσ1 : w * z * w⁻¹ ≠ 1)
    (hsig2 : w * (w * z * w⁻¹) * w⁻¹ = z⁻¹) : (ksmS w z).ncard = 4 := by
  have hI : z ≠ z⁻¹ := ksm_ne_inv_of_three hz3 hz1
  have hII : z ≠ w * z * w⁻¹ := by
    intro h
    apply hI
    have h3 := hsig2
    rw [← h] at h3
    rw [← h] at h3
    exact h3
  have hIII : z⁻¹ ≠ w * z * w⁻¹ := by
    intro h
    apply hI
    have h3 := hsig2
    rw [← h] at h3
    rw [ksm_conj_inv, ← h, inv_inv] at h3
    exact h3
  have hIV : w * z * w⁻¹ ≠ (w * z * w⁻¹)⁻¹ := ksm_ne_inv_of_three hσ3 hσ1
  have had : z ≠ (w * z * w⁻¹)⁻¹ := by
    intro h
    apply hIII
    calc z⁻¹ = ((w * z * w⁻¹)⁻¹)⁻¹ := by rw [← h]
      _ = w * z * w⁻¹ := inv_inv _
  have hbd : z⁻¹ ≠ (w * z * w⁻¹)⁻¹ := by
    intro h
    exact hII (inv_inj.1 h)
  have h1 : z ∉ ({z⁻¹, w * z * w⁻¹, (w * z * w⁻¹)⁻¹} : Set X) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hI, hII, had⟩
  have h2 : z⁻¹ ∉ ({w * z * w⁻¹, (w * z * w⁻¹)⁻¹} : Set X) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hIII, hbd⟩
  unfold ksmS
  rw [Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_pair hIV]

theorem ksm_card_S {N E : Subgroup X} (hNE : N ≤ Subgroup.normalizer (E : Set X)) {w : X}
    (hwN : w ∈ N) (hE3 : CFSG.Open.IsElemAbelian 3 E)
    (hw2 : ∀ e ∈ E, w ^ 2 * e * (w ^ 2)⁻¹ = e⁻¹) {z : X} (hz : z ∈ E) (hz1 : z ≠ 1) :
    Nat.card ↥(ksmS w z) = 4 := by
  rw [Nat.card_coe_set_eq]
  exact ksmS_ncard (hE3.2 z hz) hz1 (hE3.2 _ (ksm_sig_mem hNE hwN hz)) (ksm_sig_ne_one hz1)
    (ksm_sig2 hw2 hz)

theorem ksmS_closed {w z y : X} (hsig2 : w * (w * z * w⁻¹) * w⁻¹ = z⁻¹)
    (hy : y ∈ ksmS w z) : ksmS w y = ksmS w z := by
  unfold ksmS at hy ⊢
  rcases hy with hy | hy | hy | hy
  · rw [hy]
  · rw [hy]
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, inv_inv, ksm_conj_inv]
    tauto
  · rw [hy]
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, inv_inv, hsig2]
    tauto
  · rw [hy]
    ext g
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, inv_inv, ksm_conj_inv, hsig2]
    tauto

theorem ksmT_ncard (E : Subgroup X) (hE9 : Nat.card E = 9) : (ksmT E).ncard = 8 := by
  have hE : (E : Set X).ncard = 9 := by
    rw [← Nat.card_coe_set_eq]
    exact hE9
  unfold ksmT
  rw [Set.ncard_diff_singleton_of_mem E.one_mem, hE]

theorem ksm_orbit_cases {N E : Subgroup X} (hNE : N ≤ Subgroup.normalizer (E : Set X)) {w : X}
    (hwN : w ∈ N) (hE9 : Nat.card E = 9) (hz3E : ∀ e ∈ E, e ^ 3 = 1)
    (hw2 : ∀ e ∈ E, w ^ 2 * e * (w ^ 2)⁻¹ = e⁻¹) {z : X} (hz : z ∈ E) (hz1 : z ≠ 1) :
    ksmOrbit N z = ksmS w z ∨ ksmOrbit N z = ksmT E := by
  have hsig : w * z * w⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 (hNE hwN) z).1 hz
  have hsig1 : w * z * w⁻¹ ≠ 1 := by
    intro h
    apply hz1
    calc z = w⁻¹ * (w * z * w⁻¹) * w := by group
      _ = 1 := by rw [h]; group
  have hsig2 : ∀ u ∈ E, w * (w * u * w⁻¹) * w⁻¹ = u⁻¹ := fun u hu => ksm_sig2 hw2 hu
  by_cases h : ksmOrbit N z ⊆ ksmS w z
  · left
    exact Set.Subset.antisymm h (ksmS_subset_orbit hwN hw2 hz)
  · right
    obtain ⟨u, hu, hu'⟩ := Set.not_subset.1 h
    have huT : u ∈ ksmT E := ksm_orbit_subset_T hNE hz hz1 hu
    have huE : u ∈ E := huT.1
    have hu1 : u ≠ 1 := fun h1 => huT.2 (Set.mem_singleton_iff.2 h1)
    have hOu : ksmOrbit N u = ksmOrbit N z := ksm_orbit_eq_of_mem hu
    have hSu : ksmS w u ⊆ ksmOrbit N z := by
      rw [← hOu]
      exact ksmS_subset_orbit hwN hw2 huE
    have hdisj : Disjoint (ksmS w z) (ksmS w u) := by
      rw [Set.disjoint_left]
      intro v hvz hvu
      have e1 := ksmS_closed (hsig2 z hz) hvz
      have e2 := ksmS_closed (hsig2 u huE) hvu
      apply hu'
      have hself : u ∈ ksmS w u := by unfold ksmS; simp
      rw [← e1, e2]
      exact hself
    have hcard : (ksmS w z ∪ ksmS w u).ncard = 8 := by
      rw [Set.ncard_union_eq hdisj]
      rw [ksmS_ncard (hz3E z hz) hz1 (hz3E _ hsig) hsig1 (hsig2 z hz),
        ksmS_ncard (hz3E u huE) hu1 (hz3E _ (ksm_sig_mem hNE hwN huE)) (ksm_sig_ne_one hu1)
          (hsig2 u huE)]
    have hsub : ksmS w z ∪ ksmS w u ⊆ ksmT E :=
      Set.union_subset (ksmS_subset_T hNE hwN hz hz1) (ksmS_subset_T hNE hwN huE hu1)
    have heq : ksmS w z ∪ ksmS w u = ksmT E :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [ksmT_ncard E hE9, hcard])
    apply Set.Subset.antisymm (ksm_orbit_subset_T hNE hz hz1)
    rw [← heq]
    exact Set.union_subset (ksmS_subset_orbit hwN hw2 hz) hSu

theorem ksm_homog (N E : Subgroup X) (hNE : N ≤ Subgroup.normalizer (E : Set X))
    (hE3 : CFSG.Open.IsElemAbelian 3 E) (hE9 : Nat.card E = 9) {w : X} (hwN : w ∈ N)
    (hw2 : ∀ e ∈ E, w ^ 2 * e * (w ^ 2)⁻¹ = e⁻¹) {x y : X} (hx : x ∈ E) (hx1 : x ≠ 1)
    (hy : y ∈ E) (hy1 : y ≠ 1) :
    Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set X)) =
      Nat.card ↥(N ⊓ Subgroup.centralizer ({y} : Set X)) := by
  have hz3E : ∀ e ∈ E, e ^ 3 = 1 := fun e he => hE3.2 e he
  have hOrbEq : Nat.card ↥(ksmOrbit N x) = Nat.card ↥(ksmOrbit N y) := by
    by_cases hyx : y ∈ ksmOrbit N x
    · rw [ksm_orbit_eq_of_mem hyx]
    · have hxT : x ∈ ksmT E := ksm_mem_T hx hx1
      have hyT : y ∈ ksmT E := ksm_mem_T hy hy1
      rcases ksm_orbit_cases hNE hwN hE9 hz3E hw2 hx hx1 with hXS | hXT
      · by_cases hxy : x ∈ ksmOrbit N y
        · rw [ksm_orbit_eq_of_mem hxy]
        · rcases ksm_orbit_cases hNE hwN hE9 hz3E hw2 hy hy1 with hYS | hYT
          · rw [hXS, hYS, ksm_card_S hNE hwN hE3 hw2 hx hx1, ksm_card_S hNE hwN hE3 hw2 hy hy1]
          · exact absurd (by rw [hYT]; exact hxT) hxy
      · exact absurd (by rw [hXT]; exact hyT) hyx
  have hA := ksm_card_centralizer_mul_orbit N x
  have hB := ksm_card_centralizer_mul_orbit N y
  have hpos : 0 < Nat.card ↥(ksmOrbit N y) := by
    haveI : Nonempty ↥(ksmOrbit N y) := ⟨⟨y, ⟨1, N.one_mem, by simp⟩⟩⟩
    exact Nat.card_pos
  rw [hOrbEq] at hA
  exact Nat.eq_of_mul_eq_mul_right hpos (hA.trans hB.symm)

theorem ksm_noSq_of_K21 (hK : CFSG.LocalAnalysis.RankThreeUC.S15.K21dGeomAt X)
    (hZ : Subgroup.center X = ⊥) : NoSquareInvertingInParabolic X := by
  unfold NoSquareInvertingInParabolic
  intro P D hP hDH hD3 hD9 hDO t htP htN hinv
  obtain ⟨y, hyP, rfl⟩ := Subgroup.mem_map.1 htP
  obtain ⟨m, hm, hw⟩ := ksm_two_part y
  have hwP : y ^ m ∈ P := pow_mem hyP m
  obtain ⟨U, S, hU, hwU, hSsolv, hUS, hES⟩ := ksm_reduction hP hDH hDO hwP hw
  haveI := hSsolv
  have hsurj : ∀ d ∈ D, ∃ x : X, MulAut.conj x = d := fun d hd => by
    obtain ⟨z, -, hz⟩ := Subgroup.mem_map.1 (hDH hd)
    exact ⟨z, hz⟩
  have hwsq : ∀ d ∈ D, ((MulAut.conj y) ^ 2) ^ m * d * (((MulAut.conj y) ^ 2) ^ m)⁻¹ = d⁻¹ :=
    ksm_pow_odd_inverts hinv hm
  have hpowN : ∀ d ∈ D, (MulAut.conj y) ^ m * d * ((MulAut.conj y) ^ m)⁻¹ ∈ D := fun d hd =>
    (Subgroup.mem_normalizer_iff.1 (pow_mem htN m) d).1 hd
  have hconjw : MulAut.conj (y ^ m) = (MulAut.conj y) ^ m := map_pow _ _ _
  set E : Subgroup X := D.comap (MulAut.conj : X →* MulAut X) with hEdef
  have hE3 : CFSG.Open.IsElemAbelian 3 E := ksm_comap_isElemAbelian hZ hD3
  have hE9 : Nat.card E = 9 := (ksm_comap_card hZ hsurj).trans hD9
  have hwNE : y ^ m ∈ Subgroup.normalizer (E : Set X) := by
    apply ksm_mem_normalizer_of_map_le
    intro x hx
    have hx' : MulAut.conj x ∈ D := Subgroup.mem_comap.1 hx
    show MulAut.conj (y ^ m * x * (y ^ m)⁻¹) ∈ D
    simp only [map_mul, map_inv, hconjw]
    exact hpowN _ hx'
  have hw2 : ∀ e ∈ E, (y ^ m) ^ 2 * e * ((y ^ m) ^ 2)⁻¹ = e⁻¹ := by
    intro e he
    apply ksm_conj_injective hZ
    have he' : MulAut.conj e ∈ D := Subgroup.mem_comap.1 he
    simp only [map_mul, map_inv, map_pow]
    have hpow : ((MulAut.conj y) ^ m) ^ 2 = ((MulAut.conj y) ^ 2) ^ m := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    rw [hpow]
    exact hwsq _ he'
  obtain ⟨x, hxE, x', hx'E, hx1, hx'1, hne⟩ := hK U S E hU hUS hSsolv hES hE3 hE9
    ⟨(y ^ m) ^ 2, Subgroup.mem_inf.2 ⟨pow_mem hwU 2, pow_mem hwNE 2⟩, hw2⟩
  apply hne
  exact ksm_homog (U ⊓ Subgroup.normalizer (E : Set X)) E inf_le_right hE3 hE9
    (Subgroup.mem_inf.2 ⟨hwU, hwNE⟩) hw2 hxE hx1 hx'E hx'1

end CFSG.RankThree.PartTwo.Late
