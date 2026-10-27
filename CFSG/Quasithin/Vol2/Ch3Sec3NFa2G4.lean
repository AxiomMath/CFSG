module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Defs
public import CFSG.Milestones.ASVolI.A1

public section

namespace CFSG.Quasithin.H13.NFa2

theorem leafG4_dih6_centre (c : DihedralGroup 6) (hc : ∀ d : DihedralGroup 6, c * d = d * c) :
    c = 1 ∨ c = DihedralGroup.r 3 := by
  have key : ∀ c' : DihedralGroup 6, (∀ d : DihedralGroup 6, c' * d = d * c') →
      c' = 1 ∨ c' = DihedralGroup.r 3 := by
    decide
  exact key c hc

theorem leafG4_dih6_noncomm :
    DihedralGroup.r 1 * DihedralGroup.sr 0 ≠ DihedralGroup.sr 0 * DihedralGroup.r (1 : ZMod 6) := by
  decide

theorem leafG4_alt4 (x : alternatingGroup (Fin 4)) : x ^ 2 = 1 ∨ x ^ 3 = 1 := by
  have key : ∀ y : alternatingGroup (Fin 4), y ^ 2 = 1 ∨ y ^ 3 = 1 := by
    decide
  exact key x

theorem leafG4_alt5 (x : alternatingGroup (Fin 5)) : x ^ 2 = 1 ∨ x ^ 3 = 1 ∨ x ^ 5 = 1 := by
  have key : ∀ y : alternatingGroup (Fin 5), y ^ 2 = 1 ∨ y ^ 3 = 1 ∨ y ^ 5 = 1 := by
    decide +kernel
  exact key x

theorem leafG4_comm_of_isCyclic {X : Type} [Group X] (h : IsCyclic X) (x y : X) :
    x * y = y * x := by
  haveI : IsMulCommutative X := IsCyclic.commutative
  exact Std.Commutative.comm x y

theorem leafG4_iso_pow_ne_one {X Y : Type} [Group X] [Group Y] (ι : X ≃* Y) (x : X) (n : ℕ)
    (h : x ^ n ≠ 1) : (ι x) ^ n ≠ 1 := by
  intro h'
  apply h
  apply ι.injective
  rw [map_pow, map_one]
  exact h'

theorem leafG4_sub_pow_ne {X : Type} [Group X] (F : Subgroup X) (t : X) (ht : t ∈ F) (n : ℕ)
    (h : t ^ n ≠ 1) : (⟨t, ht⟩ : ↥F) ^ n ≠ 1 := by
  intro h'
  apply h
  have := congrArg Subtype.val h'
  simpa using this

theorem leafG4_comm_of_cyclic_quot {X : Type} [Group X] (P : Subgroup X) [P.Normal]
    (hc : IsCyclic (X ⧸ P)) (D : Subgroup X) (hcop : Nat.Coprime (Nat.card ↥D) (Nat.card ↥P)) :
    ∀ x ∈ D, ∀ y ∈ D, x * y = y * x := by
  have hbot : D ⊓ P = ⊥ := by
    rw [← Subgroup.card_eq_one]
    have h1 : Nat.card ↥(D ⊓ P) ∣ Nat.card ↥D := Subgroup.card_dvd_of_le inf_le_left
    have h2 : Nat.card ↥(D ⊓ P) ∣ Nat.card ↥P := Subgroup.card_dvd_of_le inf_le_right
    have h3 := Nat.dvd_gcd h1 h2
    rw [hcop.gcd_eq_one] at h3
    exact Nat.dvd_one.mp h3
  intro x hx y hy
  have hxy : ((x * y : X) : X ⧸ P) = ((y * x : X) : X ⧸ P) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact leafG4_comm_of_isCyclic hc _ _
  have hmem : (x * y)⁻¹ * (y * x) ∈ P := QuotientGroup.eq.mp hxy
  have hmemD : (x * y)⁻¹ * (y * x) ∈ D :=
    D.mul_mem (D.inv_mem (D.mul_mem hx hy)) (D.mul_mem hy hx)
  have h1 : (x * y)⁻¹ * (y * x) ∈ D ⊓ P := ⟨hmemD, hmem⟩
  rw [hbot, Subgroup.mem_bot] at h1
  exact inv_mul_eq_one.mp h1

theorem leafG4_two_mul_val {z : ℕ} [NeZero z] (x : ZMod z) (hx : 2 * x = 0) :
    x.val = 0 ∨ 2 * x.val = z := by
  have h1 : ((2 * x.val : ℕ) : ZMod z) = 0 := by
    rw [Nat.cast_mul, Nat.cast_ofNat, ZMod.natCast_zmod_val]
    exact hx
  rw [ZMod.natCast_eq_zero_iff] at h1
  obtain ⟨m, hm⟩ := h1
  have hlt : x.val < z := ZMod.val_lt x
  rcases m with _ | _ | m
  · left
    simpa using hm
  · right
    simpa using hm
  · exfalso
    nlinarith [Nat.zero_le (z * m)]

theorem leafG4_two_torsion {z : ℕ} [NeZero z] (i c : ZMod z) (hi : 2 * i = 0) (hc : 2 * c = 0)
    (hc0 : c ≠ 0) : i = 0 ∨ i = c := by
  rcases leafG4_two_mul_val i hi with hi0 | hi2
  · left
    exact (ZMod.val_eq_zero i).mp hi0
  · rcases leafG4_two_mul_val c hc with hc0' | hc2
    · exact absurd ((ZMod.val_eq_zero c).mp hc0') hc0
    · right
      apply ZMod.val_injective z
      omega

theorem leafG4_rot_pow_eq_one {z : ℕ} (k : ZMod z) (n : ℕ) :
    DihedralGroup.r k ^ n = 1 ↔ k * (n : ZMod z) = 0 := by
  rw [DihedralGroup.r_pow, ← DihedralGroup.r_zero, DihedralGroup.r.injEq]

theorem leafG4_r_central {z : ℕ} (k : ZMod z) (h6 : k * 6 = 0) (d : DihedralGroup z) :
    DihedralGroup.r (k * 3) * d = d * DihedralGroup.r (k * 3) := by
  cases d with
  | r i => rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r, add_comm]
  | sr j =>
    rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r]
    congr 1
    linear_combination (-1 : ZMod z) * h6

theorem leafG4_dih_central {z : ℕ} [NeZero z] (k : ZMod z) (h6 : k * 6 = 0) (h2 : k * 2 ≠ 0)
    (h3 : k * 3 ≠ 0) (x : DihedralGroup z) (hx : ∀ d : DihedralGroup z, x * d = d * x) :
    x = 1 ∨ x = DihedralGroup.r (k * 3) := by
  cases x with
  | r i =>
    have h := hx (DihedralGroup.sr 0)
    rw [DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r] at h
    have hi : 2 * i = 0 := by
      have h' := DihedralGroup.sr.inj h
      linear_combination (-1 : ZMod z) * h'
    have hc : 2 * (k * 3) = 0 := by linear_combination h6
    rcases leafG4_two_torsion i (k * 3) hi hc h3 with h0 | hk
    · left
      rw [h0, DihedralGroup.r_zero]
    · right
      rw [hk]
  | sr j =>
    exfalso
    have h := hx (DihedralGroup.r 1)
    rw [DihedralGroup.sr_mul_r, DihedralGroup.r_mul_sr] at h
    have h' := DihedralGroup.sr.inj h
    have h2z : (2 : ZMod z) = 0 := by linear_combination h'
    apply h2
    linear_combination k * h2z

theorem leafG4_dihedral_overgroup {G : Type} [Group G] (F : Subgroup G) (t : G) (ht : t ∈ F) {z : ℕ}
    (hz : z ≠ 0) (φ : ↥F ≃* DihedralGroup z) (ht6 : t ^ 6 = 1) (ht2 : t ^ 2 ≠ 1)
    (ht3 : t ^ 3 ≠ 1) :
    F ≤ Subgroup.centralizer {t ^ 3} ∧
      ∀ x ∈ F, (∀ y ∈ F, x * y = y * x) → x = 1 ∨ x = t ^ 3 := by
  haveI : NeZero z := ⟨hz⟩
  obtain ⟨tF, htF⟩ : ∃ tF : ↥F, (tF : G) = t := ⟨⟨t, ht⟩, rfl⟩
  have hF6 : tF ^ 6 = 1 := Subtype.ext (by simp [htF, ht6])
  have hF2 : tF ^ 2 ≠ 1 := fun h => ht2 (by
    have := congrArg Subtype.val h
    simpa [htF] using this)
  have hF3 : tF ^ 3 ≠ 1 := fun h => ht3 (by
    have := congrArg Subtype.val h
    simpa [htF] using this)
  obtain ⟨k, hk⟩ : ∃ k : ZMod z, φ tF = DihedralGroup.r k := by
    have hcases : ∀ d : DihedralGroup z,
        (∃ j, d = DihedralGroup.sr j) ∨ (∃ k, d = DihedralGroup.r k) := by
      intro d
      cases d with
      | r k => exact Or.inr ⟨k, rfl⟩
      | sr j => exact Or.inl ⟨j, rfl⟩
    rcases hcases (φ tF) with ⟨j, hj⟩ | ⟨k, hk⟩
    · exfalso
      apply hF2
      apply φ.injective
      rw [map_pow, hj, map_one, sq, DihedralGroup.sr_mul_self]
    · exact ⟨k, hk⟩
  have hφ6 : (φ tF) ^ 6 = 1 := by rw [← map_pow, hF6, map_one]
  have hφ2 : (φ tF) ^ 2 ≠ 1 := fun h => hF2 (φ.injective (by rw [map_pow, map_one]; exact h))
  have hφ3 : (φ tF) ^ 3 ≠ 1 := fun h => hF3 (φ.injective (by rw [map_pow, map_one]; exact h))
  rw [hk] at hφ6 hφ2 hφ3
  have hk6 : k * 6 = 0 := by
    have := (leafG4_rot_pow_eq_one k 6).mp hφ6
    simpa using this
  have hk2 : k * 2 ≠ 0 := fun h => hφ2 ((leafG4_rot_pow_eq_one k 2).mpr (by simpa using h))
  have hk3 : k * 3 ≠ 0 := fun h => hφ3 ((leafG4_rot_pow_eq_one k 3).mpr (by simpa using h))
  have hφa : φ (tF ^ 3) = DihedralGroup.r (k * 3) := by
    rw [map_pow, hk, DihedralGroup.r_pow]
    norm_num
  have hcen_a : ∀ y : ↥F, (tF ^ 3) * y = y * (tF ^ 3) := by
    intro y
    apply φ.injective
    rw [map_mul, map_mul, hφa]
    exact leafG4_r_central k hk6 (φ y)
  have hcentre_F : F ≤ Subgroup.centralizer {t ^ 3} := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have := congrArg Subtype.val (hcen_a ⟨x, hx⟩)
    simpa [htF] using this
  refine ⟨hcentre_F, fun x hx hxc => ?_⟩
  obtain ⟨xF, hxF⟩ : ∃ xF : ↥F, (xF : G) = x := ⟨⟨x, hx⟩, rfl⟩
  have hxc' : ∀ y : ↥F, xF * y = y * xF := fun y =>
    Subtype.ext (by simpa [hxF] using hxc y.1 y.2)
  have hφx : ∀ d : DihedralGroup z, φ xF * d = d * φ xF := by
    intro d
    obtain ⟨y, rfl⟩ := φ.surjective d
    rw [← map_mul, ← map_mul, hxc' y]
  rcases leafG4_dih_central k hk6 hk2 hk3 (φ xF) hφx with h1 | h1
  · left
    have h2 : xF = 1 := φ.injective (by rw [h1, map_one])
    have := congrArg Subtype.val h2
    simpa [hxF] using this
  · right
    have h2 : xF = tF ^ 3 := φ.injective (by rw [h1, hφa])
    have := congrArg Subtype.val h2
    simpa [hxF, htF] using this

theorem leafG4_core (q : ℕ) [Fact q.Prime] (hq24 : q % 24 = 11 ∨ q % 24 = 13)
    (E F : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField q 1)))
    (a : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField q 1))
    (e6 : ↥E ≃* DihedralGroup 6) (haE : a ∈ E)
    (hcomm : ∀ x ∈ E, a * x = x * a) (ha2 : orderOf a = 2) (hEF : E ≤ F) (hF : F ≠ ⊤) :
    F ≤ Subgroup.centralizer {a} ∧ ∀ z ∈ F, (∀ f ∈ F, z * f = f * z) → z = 1 ∨ z = a := by
  have hq : q.Prime := Fact.out
  have hq11 : 11 ≤ q := by omega
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  obtain ⟨tE, htE⟩ : ∃ x : ↥E, e6 x = DihedralGroup.r 1 :=
    ⟨e6.symm (DihedralGroup.r 1), e6.apply_symm_apply _⟩
  obtain ⟨sE, hsE⟩ : ∃ x : ↥E, e6 x = DihedralGroup.sr 0 :=
    ⟨e6.symm (DihedralGroup.sr 0), e6.apply_symm_apply _⟩
  obtain ⟨t, ht⟩ : ∃ t : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField q 1),
      t = (tE : Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField q 1)) := ⟨_, rfl⟩
  have htE_mem : t ∈ E := by
    rw [ht]
    exact tE.2
  have htF : t ∈ F := hEF htE_mem
  have htord : orderOf t = 6 := by
    rw [ht, Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq e6, htE, DihedralGroup.orderOf_r_one]
  have ht6 : t ^ 6 = 1 := by
    rw [← htord]
    exact pow_orderOf_eq_one t
  have ht2 : t ^ 2 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [htord]; norm_num)
  have ht5 : t ^ 5 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [htord]; norm_num)
  have hcenter_a : e6 ⟨a, haE⟩ = DihedralGroup.r 3 := by
    have hc := leafG4_dih6_centre (e6 ⟨a, haE⟩) (by
      intro d
      obtain ⟨y, rfl⟩ := e6.surjective d
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm y.1 y.2))
    rcases hc with h1 | h1
    · exfalso
      apply ha1
      have h2 : (⟨a, haE⟩ : ↥E) = 1 := e6.injective (by rw [h1, map_one])
      exact congrArg Subtype.val h2
    · exact h1
  have hta : t ^ 3 = a := by
    have h3 : (DihedralGroup.r 1 : DihedralGroup 6) ^ 3 = DihedralGroup.r 3 := by
      simp
    have h1 : tE ^ 3 = ⟨a, haE⟩ := by
      apply e6.injective
      rw [map_pow, htE, hcenter_a, h3]
    have h2 := congrArg Subtype.val h1
    rw [ht]
    simpa using h2
  have ht3 : t ^ 3 ≠ 1 := by
    rw [hta]
    exact ha1
  have hnc : ¬ ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
    intro h
    apply leafG4_dih6_noncomm
    have hts : tE * sE = sE * tE := Subtype.ext (h tE.1 tE.2 sE.1 sE.2)
    have := congrArg e6 hts
    simpa [map_mul, htE, hsE] using this
  have hEcard : Nat.card ↥E = 12 := by
    rw [Nat.card_congr e6.toEquiv, DihedralGroup.nat_card]
  have hdvd : Nat.card ↥E ∣ Nat.card ↥F := Subgroup.card_dvd_of_le hEF
  have hcardD : Nat.card ↥(E.subgroupOf F) = 12 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEF).toEquiv, hEcard]
  have hnd : ¬ q ∣ 12 := by
    intro hd
    have hle : q ≤ 12 := Nat.le_of_dvd (by norm_num) hd
    interval_cases q <;> omega
  have h12q : Nat.Coprime 12 q := ((Nat.Prime.coprime_iff_not_dvd hq).mpr hnd).symm
  have hD := CFSG.ASVolI.as_A_1_3 q 1 le_rfl F
  rcases hD with ⟨-, m, hm, hFcard⟩ | ⟨hFcyc, -⟩ | ⟨z, hz, ⟨φ⟩⟩ | ⟨-, ⟨ι⟩⟩ | ⟨h16, -⟩ |
    ⟨-, ⟨ι⟩⟩ | ⟨m, t', P, hPn, -, hPcard, hPcyc, -, -, -⟩ | ⟨m, hm, ⟨φ⟩⟩ | ⟨m, hm, -⟩
  ·
    exfalso
    have h1 : Nat.card ↥E ∣ q ^ m := by
      rw [← hFcard]
      exact hdvd
    rw [hEcard] at h1
    have h2 : 2 ∣ q := Nat.prime_two.dvd_of_dvd_pow (dvd_trans (by norm_num) h1)
    omega
  ·
    exfalso
    apply hnc
    intro x hx y hy
    have := leafG4_comm_of_isCyclic hFcyc ⟨x, hEF hx⟩ ⟨y, hEF hy⟩
    exact congrArg Subtype.val this
  ·
    have hg : Nat.gcd 2 (q ^ 1 - 1) = 2 := by
      rw [pow_one]
      exact Nat.gcd_eq_left (by omega)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [hg, pow_one] at hz
      rcases hz with h | h <;> rw [zero_dvd_iff] at h <;> omega
    have key := leafG4_dihedral_overgroup F t htF hz0 φ ht6 ht2 ht3
    rw [hta] at key
    exact key
  ·
    exfalso
    have h2 : (⟨t, htF⟩ : ↥F) ^ 2 ≠ 1 := leafG4_sub_pow_ne F t htF 2 ht2
    have h3 : (⟨t, htF⟩ : ↥F) ^ 3 ≠ 1 := leafG4_sub_pow_ne F t htF 3 ht3
    rcases leafG4_alt4 (ι ⟨t, htF⟩) with h | h
    · exact leafG4_iso_pow_ne_one ι _ 2 h2 h
    · exact leafG4_iso_pow_ne_one ι _ 3 h3 h
  ·
    exfalso
    have hq2 : q ^ (2 * 1) % 16 = 9 := by
      rw [Nat.pow_mod]
      have : q % 16 = 3 ∨ q % 16 = 5 ∨ q % 16 = 11 ∨ q % 16 = 13 := by omega
      rcases this with h | h | h | h <;> rw [h] <;> norm_num
    omega
  ·
    exfalso
    have h2 : (⟨t, htF⟩ : ↥F) ^ 2 ≠ 1 := leafG4_sub_pow_ne F t htF 2 ht2
    have h3 : (⟨t, htF⟩ : ↥F) ^ 3 ≠ 1 := leafG4_sub_pow_ne F t htF 3 ht3
    have h5 : (⟨t, htF⟩ : ↥F) ^ 5 ≠ 1 := leafG4_sub_pow_ne F t htF 5 ht5
    rcases leafG4_alt5 (ι ⟨t, htF⟩) with h | h | h
    · exact leafG4_iso_pow_ne_one ι _ 2 h2 h
    · exact leafG4_iso_pow_ne_one ι _ 3 h3 h
    · exact leafG4_iso_pow_ne_one ι _ 5 h5 h
  ·
    exfalso
    have hcop : Nat.Coprime (Nat.card ↥(E.subgroupOf F)) (Nat.card ↥P) := by
      rw [hcardD, hPcard]
      exact Nat.Coprime.pow_right m h12q
    have hcommD := leafG4_comm_of_cyclic_quot P hPcyc (E.subgroupOf F) hcop
    apply hnc
    intro x hx y hy
    have := hcommD ⟨x, hEF hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨y, hEF hy⟩
      (Subgroup.mem_subgroupOf.mpr hy)
    exact congrArg Subtype.val this
  ·
    have hm1 : m = 1 := Nat.dvd_one.mp hm
    subst hm1
    exfalso
    have hcardF : Nat.card ↥F = Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField q 1)) :=
      Nat.card_congr φ.toEquiv
    exact hF ((Subgroup.card_eq_iff_eq_top F).mp hcardF)
  ·
    exfalso
    have h2m : 2 * m = 1 := Nat.dvd_one.mp hm
    omega

theorem nfa2_G4 : Leaf_G4 := by
  intro q hq hq24 Kb _ hM E F a _hE12 hE6 haE hcomm ha2 hEF hF
  haveI : Fact q.Prime := ⟨hq⟩
  obtain ⟨-, K, hKF, hKfin, hK, ⟨e⟩⟩ := hM
  obtain ⟨e6⟩ := hE6
  let ψ : Kb ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField q 1) :=
    e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL K 2 q 1 (by norm_num) hK)
  have hψ : Function.Injective ψ.toMonoidHom := ψ.injective
  have hE1 : ↥(E.map ψ.toMonoidHom) ≃* DihedralGroup 6 :=
    (E.equivMapOfInjective ψ.toMonoidHom hψ).symm.trans e6
  have hcomm1 : ∀ x ∈ E.map ψ.toMonoidHom, ψ a * x = x * ψ a := by
    rintro _ ⟨y, hy, rfl⟩
    show ψ a * ψ y = ψ y * ψ a
    rw [← map_mul, ← map_mul, hcomm y hy]
  have hord1 : orderOf (ψ a) = 2 := by
    rw [MulEquiv.orderOf_eq, ha2]
  have hF1 : F.map ψ.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hF
    have hcomap := Subgroup.comap_map_eq_self_of_injective (f := ψ.toMonoidHom) hψ F
    rw [← hcomap, htop, Subgroup.comap_top]
  obtain ⟨hcen, hcentre⟩ := leafG4_core q hq24 (E.map ψ.toMonoidHom) (F.map ψ.toMonoidHom) (ψ a) hE1
    (Subgroup.mem_map_of_mem ψ.toMonoidHom haE) hcomm1 hord1 (Subgroup.map_mono hEF) hF1
  refine ⟨fun f hf => ?_, fun z hz hzc => ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    have h1 : ψ a * ψ f = ψ f * ψ a :=
      Subgroup.mem_centralizer_iff.mp (hcen (Subgroup.mem_map_of_mem ψ.toMonoidHom hf)) (ψ a)
        (Set.mem_singleton _)
    apply ψ.injective
    simpa only [map_mul] using h1
  · have hz1 : ψ z ∈ F.map ψ.toMonoidHom := Subgroup.mem_map_of_mem ψ.toMonoidHom hz
    have hzc' : ∀ w ∈ F.map ψ.toMonoidHom, ψ z * w = w * ψ z := by
      rintro _ ⟨y, hy, rfl⟩
      show ψ z * ψ y = ψ y * ψ z
      rw [← map_mul, ← map_mul, hzc y hy]
    rcases hcentre (ψ z) hz1 hzc' with h1 | h1
    · left
      exact ψ.injective (by rw [h1, map_one])
    · right
      exact ψ.injective h1

end CFSG.Quasithin.H13.NFa2
