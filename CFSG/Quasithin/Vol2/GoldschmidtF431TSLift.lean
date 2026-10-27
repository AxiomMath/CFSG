module

public import CFSG.Quasithin.Vol2.GoldschmidtF431F45L3Ctx

public section

namespace CFSG.Quasithin.H13.F431.Lift

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin.H13.F431.F45

variable {D : Type} [Group D] (A : LieAmalgamExt D)

section Inn

variable (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K)

@[expose] noncomputable def iK : D →* ↥A.K := innHom A hgen (MulEquiv.refl D)

theorem iK_coe (d : D) : ((iK A hgen d : ↥A.K) : MulAut D) = MulAut.conj d := rfl

theorem iK_injective (hcen : Subgroup.center D = ⊥) : Function.Injective (iK A hgen) := by
  intro a b h
  exact conj_injective_of_center hcen (congrArg (fun k : ↥A.K => (k : MulAut D)) h)

theorem aut_conj_conj (k : MulAut D) (d : D) :
    k * MulAut.conj d * k⁻¹ = MulAut.conj (k d) := by
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply]

theorem range_normal : ((iK A hgen).range).Normal := by
  refine ⟨fun n hn k => ?_⟩
  obtain ⟨d, rfl⟩ := hn
  refine ⟨(k : MulAut D) d, ?_⟩
  apply Subtype.ext
  have := aut_conj_conj (k : MulAut D) d
  simpa [iK_coe] using this.symm

variable [Finite D]

theorem exists_inn_mul (k : ↥A.K) :
    ∃ (d : D) (φ : MulAut D), φ ∈ A.N1 ⊓ A.N2 ∧ (k : MulAut D) = MulAut.conj d * φ := by
  have hg := LieAmalgamExt.K_le_inn_sup A k.2
  have : ((MulAut.conj : D →* MulAut D).range).Normal := innRange_normal
  obtain ⟨n, ⟨d, rfl⟩, b, hb, hnb⟩ := Subgroup.mem_sup_of_normal_left.mp hg
  exact ⟨d, b, hb, hnb.symm⟩

omit [Finite D] in
theorem inn_mem_autStab {P : Subgroup D} {d : D} (hd : d ∈ P) : MulAut.conj d ∈ autStab P := by
  intro x
  rw [MulAut.conj_apply]
  constructor
  · intro hx
    exact P.mul_mem (P.mul_mem hd hx) (P.inv_mem hd)
  · intro hx
    have := P.mul_mem (P.mul_mem (P.inv_mem hd) hx) hd
    simpa [mul_assoc] using this

omit [Finite D] in
theorem TD_le_P1 : A.TD ≤ A.P1 :=
  Subgroup.le_normalizer.trans ((A.yam.2.2 A.P1).mpr (Or.inl rfl)).2

omit [Finite D] in
theorem TD_le_P2 : A.TD ≤ A.P2 :=
  Subgroup.le_normalizer.trans ((A.yam.2.2 A.P2).mpr (Or.inr rfl)).2

omit [Finite D] in
theorem iK_mem_Mb1 {d : D} (hd : d ∈ A.P1) : iK A hgen d ∈ A.Mb1 :=
  ⟨A.inn_le ⟨d, rfl⟩, inn_mem_autStab hd⟩

omit [Finite D] in
theorem iK_mem_Mb2 {d : D} (hd : d ∈ A.P2) : iK A hgen d ∈ A.Mb2 :=
  ⟨A.inn_le ⟨d, rfl⟩, inn_mem_autStab hd⟩

theorem stab_of_fix {P : Subgroup D} (hP : P = A.P1 ∨ P = A.P2) {w : D}
    (hC : Subgroup.centralizer ({w} : Set D) ≤ P)
    (haut : ∀ φ ∈ A.N1 ⊓ A.N2, ∃ b ∈ A.P1 ⊓ A.P2, φ w = b * w * b⁻¹)
    (k : ↥A.K) (hk : (k : MulAut D) w = w) : (k : MulAut D) ∈ autStab P := by
  obtain ⟨d, φ, hφ, hkφ⟩ := exists_inn_mul A k
  obtain ⟨b, hb, hφw⟩ := haut φ hφ
  have hbP : b ∈ P := by
    rcases hP with rfl | rfl
    · exact hb.1
    · exact hb.2
  have hφP : φ ∈ autStab P := by
    rcases hP with rfl | rfl
    · exact hφ.1.2
    · exact hφ.2.2
  have h1 : d * (b * w * b⁻¹) * d⁻¹ = w := by
    have := hk
    rw [hkφ, MulAut.mul_apply, hφw, MulAut.conj_apply] at this
    exact this
  have h2 : d * b ∈ Subgroup.centralizer ({w} : Set D) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have : d * b * w * (d * b)⁻¹ = w := by simpa [mul_assoc] using h1
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have hdP : d ∈ P := by
    have := hC h2
    have h3 := P.mul_mem this (P.inv_mem hbP)
    simpa using h3
  rw [hkφ]
  exact (autStab P).mul_mem (inn_mem_autStab hdP) hφP

omit [Finite D] in
theorem mem_centralizer_iK_iff (hcen : Subgroup.center D = ⊥) (w : D) (k : ↥A.K) :
    k ∈ Subgroup.centralizer ({iK A hgen w} : Set ↥A.K) ↔ (k : MulAut D) w = w := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : (k : MulAut D) * MulAut.conj w = MulAut.conj w * (k : MulAut D) := by
      have := congrArg (fun x : ↥A.K => (x : MulAut D)) h
      simp only [iK_coe, Subgroup.coe_mul] at this
      exact this
    have h1 : (k : MulAut D) * MulAut.conj w * (k : MulAut D)⁻¹ = MulAut.conj w :=
      mul_inv_eq_iff_eq_mul.mpr h'
    rw [aut_conj_conj] at h1
    exact conj_injective_of_center hcen h1
  · intro h
    apply Subtype.ext
    have h1 : (k : MulAut D) * MulAut.conj w * (k : MulAut D)⁻¹ = MulAut.conj w := by
      rw [aut_conj_conj, h]
    have h2 := mul_inv_eq_iff_eq_mul.mp h1
    simp only [iK_coe, Subgroup.coe_mul]
    exact h2

omit [Finite D] in
theorem K_le_Mbar : A.K ≤ A.Mbar := sup_le inf_le_left inf_le_left

omit [Finite D] in
theorem mem_Mb1_of_stab {k : ↥A.K} (h : (k : MulAut D) ∈ autStab A.P1) : k ∈ A.Mb1 :=
  ⟨K_le_Mbar A k.2, h⟩

omit [Finite D] in
theorem mem_Mb2_of_stab {k : ↥A.K} (h : (k : MulAut D) ∈ autStab A.P2) : k ∈ A.Mb2 :=
  ⟨K_le_Mbar A k.2, h⟩

omit [Finite D] in
open CFSG.Quasithin.F7 in
theorem isSylowTwoOf_map (hcen : Subgroup.center D = ⊥)
    (hodd : ¬ 2 ∣ (iK A hgen).range.index) {U : Subgroup D} (hU : IsSylowTwoOf U ⊤) :
    IsSylowTwoOf (U.map (iK A hgen)) ⊤ := by
  have hinj := iK_injective A hgen hcen
  have hpU : IsPGroup 2 ↥(U.map (iK A hgen)) :=
    hU.2.1.of_equiv (Subgroup.equivMapOfInjective U _ hinj)
  refine isSylowTwoOf_of_relIndex le_top hpU ?_
  have h1 : (U.map (iK A hgen)).relIndex (iK A hgen).range = U.relIndex ⊤ := by
    rw [MonoidHom.range_eq_map]
    exact Subgroup.relIndex_map_map_of_injective _ _ hinj
  have hU1 : ¬ 2 ∣ U.relIndex ⊤ := isSylowTwoOf_odd_relIndex hU
  have hle : U.map (iK A hgen) ≤ (iK A hgen).range := Subgroup.map_le_range _ _
  have h2 := Subgroup.relIndex_mul_relIndex (U.map (iK A hgen)) (iK A hgen).range ⊤ hle le_top
  rw [Subgroup.relIndex_top_right] at h2
  rw [← h2]
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with h | h
  · rw [h1] at h
    exact hU1 h
  · exact hodd h

omit [Finite D] in
theorem mem_range_of_sq_eq_one (hodd : ¬ 2 ∣ (iK A hgen).range.index) {x : ↥A.K}
    (hx : x ^ 2 = 1) : x ∈ (iK A hgen).range := by
  have hN := range_normal A hgen
  have h1 : orderOf (QuotientGroup.mk x : ↥A.K ⧸ (iK A hgen).range) ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, hx, QuotientGroup.mk_one]
  have h2 : orderOf (QuotientGroup.mk x : ↥A.K ⧸ (iK A hgen).range) ∣
      (iK A hgen).range.index := by
    rw [Subgroup.index]
    exact orderOf_dvd_natCard _
  have h3 : orderOf (QuotientGroup.mk x : ↥A.K ⧸ (iK A hgen).range) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact h
    · rw [h] at h2
      exact absurd h2 hodd
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff x).mp h3

omit [Finite D] in
theorem not_isConj_iK {z0 t0 : D} (hcen : Subgroup.center D = ⊥)
    (hnc : ∀ φ : MulAut D, φ z0 ≠ t0) : ¬ IsConj (iK A hgen z0) (iK A hgen t0) := by
  intro h
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  have h1 : (c : MulAut D) * MulAut.conj z0 * (c : MulAut D)⁻¹ = MulAut.conj t0 := by
    have := congrArg (fun x : ↥A.K => (x : MulAut D)) hc
    simpa [iK_coe] using this
  rw [aut_conj_conj] at h1
  exact hnc c (conj_injective_of_center hcen h1)

end Inn

section Datum

structure TwoClassD (z0 t0 : D) : Prop where
  z_mem : z0 ∈ A.TD
  t_mem : t0 ∈ A.TD
  z_two : orderOf z0 = 2
  t_two : orderOf t0 = 2
  cls : ∀ x : D, orderOf x = 2 → IsConj z0 x ∨ IsConj t0 x
  noconj : ∀ φ : MulAut D, φ z0 ≠ t0
  center : ∀ w ∈ A.TD, (∀ y ∈ A.TD, y * w = w * y) → w ≠ 1 →
    ∃ h ∈ A.P1 ⊓ A.P2, h * z0 * h⁻¹ = w
  aut_z : ∀ φ ∈ A.N1 ⊓ A.N2, ∃ b ∈ A.P1 ⊓ A.P2, φ z0 = b * z0 * b⁻¹
  aut_t : ∀ φ ∈ A.N1 ⊓ A.N2, ∃ b ∈ A.P1 ⊓ A.P2, φ t0 = b * t0 * b⁻¹
  cent_z : ∃ P : Subgroup D, (P = A.P1 ∨ P = A.P2) ∧ Subgroup.centralizer ({z0} : Set D) ≤ P
  cent_t : ∃ P : Subgroup D, (P = A.P1 ∨ P = A.P2) ∧ Subgroup.centralizer ({t0} : Set D) ≤ P

variable [Finite D] (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K)

theorem cent_le_Mb (hcen : Subgroup.center D = ⊥) {w : D} {P : Subgroup D}
    (hP : P = A.P1 ∨ P = A.P2) (hC : Subgroup.centralizer ({w} : Set D) ≤ P)
    (haut : ∀ φ ∈ A.N1 ⊓ A.N2, ∃ b ∈ A.P1 ⊓ A.P2, φ w = b * w * b⁻¹) :
    Subgroup.centralizer ({iK A hgen w} : Set ↥A.K) ≤ A.Mb1 ∨
      Subgroup.centralizer ({iK A hgen w} : Set ↥A.K) ≤ A.Mb2 := by
  rcases hP with rfl | rfl
  · left
    intro k hk
    exact mem_Mb1_of_stab A
      (stab_of_fix A (Or.inl rfl) hC haut k ((mem_centralizer_iK_iff A hgen hcen w k).mp hk))
  · right
    intro k hk
    exact mem_Mb2_of_stab A
      (stab_of_fix A (Or.inr rfl) hC haut k ((mem_centralizer_iK_iff A hgen hcen w k).mp hk))

open scoped Classical in
theorem f431LieK_of_twoClassD (hcen : Subgroup.center D = ⊥)
    (hodd : ¬ 2 ∣ (iK A hgen).range.index) {z0 t0 : D} (H : TwoClassD A z0 t0)
    (hag : ∀ E : Subgroup ↥A.K, IsAGMember (A.TD.map (iK A hgen)) E →
      Subgroup.normalizer (E : Set ↥A.K) ≤ A.Mb1 ∨ Subgroup.normalizer (E : Set ↥A.K) ≤ A.Mb2) :
    F431LieK (A.TD.map (iK A hgen)) A.Mb1 A.Mb2 {iK A hgen z0, iK A hgen t0} (iK A hgen z0) := by
  have hinj := iK_injective A hgen hcen
  have hne : iK A hgen z0 ≠ iK A hgen t0 := fun h => H.noconj 1 (by simpa using hinj h)
  have hord : ∀ d : D, orderOf (iK A hgen d) = orderOf d := fun d =>
    orderOf_injective (iK A hgen) hinj d
  have hcentz : Subgroup.centralizer ({iK A hgen z0} : Set ↥A.K) ≤ A.Mb1 ∨
      Subgroup.centralizer ({iK A hgen z0} : Set ↥A.K) ≤ A.Mb2 := by
    obtain ⟨P, hP, hC⟩ := H.cent_z
    exact cent_le_Mb A hgen hcen hP hC H.aut_z
  have hcentt : Subgroup.centralizer ({iK A hgen t0} : Set ↥A.K) ≤ A.Mb1 ∨
      Subgroup.centralizer ({iK A hgen t0} : Set ↥A.K) ≤ A.Mb2 := by
    obtain ⟨P, hP, hC⟩ := H.cent_t
    exact cent_le_Mb A hgen hcen hP hC H.aut_t
  refine ⟨isSylowTwoOf_map A hgen hcen hodd A.yam.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hcentz, ?_,
    hag⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact iK_mem_Mb1 A hgen (TD_le_P1 A hu)
  · rintro _ ⟨u, hu, rfl⟩
    exact iK_mem_Mb2 A hgen (TD_le_P2 A hu)
  · intro i hi
    rw [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact ⟨z0, H.z_mem, rfl⟩
    · exact ⟨t0, H.t_mem, rfl⟩
  · intro i hi
    rw [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · rw [hord, H.z_two]
    · rw [hord, H.t_two]
  · exact Finset.mem_insert_self _ _
  · rw [Finset.card_pair hne]
  · intro x hx
    have hxsq : x ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hx])
    obtain ⟨d, hd⟩ := mem_range_of_sq_eq_one A hgen hodd hxsq
    have hd2 : orderOf d = 2 := by rw [← hord d, hd, hx]
    have hnc := not_isConj_iK A hgen hcen H.noconj
    rcases H.cls d hd2 with h | h
    · refine ⟨iK A hgen z0, ⟨Finset.mem_insert_self _ _, ?_⟩, ?_⟩
      · rw [← hd]
        exact (iK A hgen).map_isConj h
      · rintro i ⟨hi, hix⟩
        rw [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · rfl
        · exfalso
          apply hnc
          have h1 : IsConj (iK A hgen z0) x := by
            rw [← hd]
            exact (iK A hgen).map_isConj h
          exact h1.trans hix.symm
    · refine ⟨iK A hgen t0, ⟨Finset.mem_insert_of_mem (Finset.mem_singleton_self _), ?_⟩, ?_⟩
      · rw [← hd]
        exact (iK A hgen).map_isConj h
      · rintro i ⟨hi, hix⟩
        rw [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl
        · exfalso
          apply hnc
          have h1 : IsConj (iK A hgen t0) x := by
            rw [← hd]
            exact (iK A hgen).map_isConj h
          exact hix.trans h1.symm
        · rfl
  · intro i hi
    rw [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact hcentz
    · exact hcentt
  · rintro _ ⟨u, hu, rfl⟩ hcu hu1
    obtain ⟨h, hh, hhu⟩ := H.center u hu (fun y hy => by
      have := hcu (iK A hgen y) ⟨y, hy, rfl⟩
      exact hinj (by simpa using this)) (fun h1 => hu1 (by rw [h1, map_one]))
    exact ⟨iK A hgen h, ⟨iK_mem_Mb1 A hgen hh.1, iK_mem_Mb2 A hgen hh.2⟩, by
      rw [← map_mul, ← map_inv, ← map_mul, hhu]⟩

end Datum

end CFSG.Quasithin.H13.F431.Lift
