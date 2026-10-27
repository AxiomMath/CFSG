module

public import CFSG.Quasithin.Vol2.Ch3B513NDual

public section

namespace CFSG.Quasithin.B513N

variable {W : Type*} [CommGroup W]

@[expose] def cmHom (a : MulAut W) : W →* W where
  toFun w := a w * w⁻¹
  map_one' := by simp
  map_mul' u v := by
    simp only [map_mul, mul_inv_rev]
    rw [mul_comm v⁻¹ u⁻¹]
    exact mul_mul_mul_comm _ _ _ _

theorem cmHom_apply (a : MulAut W) (w : W) : cmHom a w = a w * w⁻¹ := rfl

theorem ker_cmHom (a : MulAut W) : (cmHom a).ker = fixV (Subgroup.zpowers a) := by
  ext w
  rw [MonoidHom.mem_ker, cmHom_apply, mul_inv_eq_one, mem_fixV]
  exact ⟨fun h => B1.zpowers_fix h, fun h => h a (Subgroup.mem_zpowers a)⟩

theorem cm_mem_of_mem_closure {S : Set (MulAut W)} {R : Subgroup W}
    (hS : ∀ s ∈ S, ∀ w : W, s w * w⁻¹ ∈ R) :
    ∀ x ∈ Subgroup.closure S, ∀ w : W, x w * w⁻¹ ∈ R := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hS y hy
  | one => intro w; simp
  | mul y z _ _ hy hz =>
    intro w
    have : (y * z) w * w⁻¹ = (y (z w) * (z w)⁻¹) * (z w * w⁻¹) := by
      rw [MulAut.mul_apply]
      group
    rw [this]
    exact R.mul_mem (hy (z w)) (hz w)
  | inv y _ hy =>
    intro w
    have : y⁻¹ w * w⁻¹ = (y (y⁻¹ w) * (y⁻¹ w)⁻¹)⁻¹ := by
      rw [MulAut.apply_inv_self]
      group
    rw [this]
    exact R.inv_mem (hy _)

theorem commV_zpowers_le_range (a : MulAut W) :
    commV (Subgroup.zpowers a) ≤ (cmHom a).range := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨x, hx, w, rfl⟩
  rw [Subgroup.zpowers_eq_closure] at hx
  refine cm_mem_of_mem_closure ?_ x hx w
  rintro s rfl v
  exact ⟨v, rfl⟩

omit [CommGroup W] in
theorem card_range_cmHom [CommGroup W] [Finite W] (a : MulAut W) :
    Nat.card (cmHom a).range = (fixV (Subgroup.zpowers a)).index := by
  rw [← ker_cmHom, Subgroup.index_ker]

theorem card_commV_zpowers_le [Finite W] (a : MulAut W) :
    Nat.card (commV (Subgroup.zpowers a)) ≤ (fixV (Subgroup.zpowers a)).index := by
  rw [← card_range_cmHom]
  exact Subgroup.card_le_of_le (commV_zpowers_le_range a)

theorem cmHom_cmHom {a : MulAut W} (ha : a ^ 2 = 1) (hW : ∀ w : W, w ^ 2 = 1) (w : W) :
    cmHom a (cmHom a w) = 1 := by
  rw [cmHom_apply, cmHom_apply, map_mul, map_inv]
  have h2 : a (a w) = w := by
    rw [← MulAut.mul_apply, ← pow_two, ha]
    rfl
  rw [h2, mul_inv_rev, inv_inv, ← pow_two, hW]

theorem commV_zpowers_le_fixV {a : MulAut W} (ha : a ^ 2 = 1) (hW : ∀ w : W, w ^ 2 = 1) :
    commV (Subgroup.zpowers a) ≤ fixV (Subgroup.zpowers a) := by
  refine (commV_zpowers_le_range a).trans ?_
  rintro _ ⟨w, rfl⟩
  rw [← ker_cmHom, MonoidHom.mem_ker]
  exact cmHom_cmHom ha hW w

theorem commV_sup_le (B C : Subgroup (MulAut W)) : commV (B ⊔ C) ≤ commV B ⊔ commV C :=
  CFSG.Quasithin.FixVLat.commV_sup_le B C

theorem card_sup_le [Finite W] (S T : Subgroup W) :
    Nat.card ↥(S ⊔ T) ≤ Nat.card ↥S * Nat.card ↥T := by
  have hsurj : Function.Surjective (fun p : ↥S × ↥T =>
      (⟨(p.1 : W) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩ : ↥(S ⊔ T))) := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hx
    exact ⟨(⟨y, hy⟩, ⟨z, hz⟩), rfl⟩
  have := Nat.card_le_card_of_surjective _ hsurj
  rwa [Nat.card_prod] at this

theorem exists_index_two {D : Subgroup (MulAut W)} [Finite W] {r : ℕ} (hr : Nat.card D = 2 ^ r)
    (hpos : 0 < r) : ∃ B : Subgroup (MulAut W), ∃ d ∈ D, B ≤ D ∧ Nat.card B = 2 ^ (r - 1) ∧
      B ⊔ Subgroup.zpowers d = D := by
  have hfac : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥D) 2 (n := r - 1)
    (by rw [hr]; exact pow_dvd_pow 2 (Nat.sub_le r 1))
  refine ⟨K.map D.subtype, ?_⟩
  have hBD : K.map D.subtype ≤ D := by rintro _ ⟨x, -, rfl⟩; exact x.2
  have hBcard : Nat.card (K.map D.subtype) = 2 ^ (r - 1) := by
    rw [Subgroup.card_map_of_injective D.subtype_injective, hK]
  have hD2 : Nat.card D = 2 * Nat.card (K.map D.subtype) := by
    rw [hr, hBcard, ← pow_succ']
    congr 1
    omega
  have hlt : Nat.card (K.map D.subtype) < Nat.card D := by
    rw [hD2]
    have : 0 < Nat.card (K.map D.subtype) := Nat.card_pos
    omega
  obtain ⟨d, hdD, hdB⟩ : ∃ d ∈ D, d ∉ K.map D.subtype := by
    by_contra hcon
    push Not at hcon
    exact absurd (Subgroup.card_le_of_le (show D ≤ K.map D.subtype from hcon)) (not_le.2 hlt)
  refine ⟨d, hdD, hBD, hBcard, ?_⟩
  set B := K.map D.subtype
  have hle : B ⊔ Subgroup.zpowers d ≤ D := sup_le hBD (Subgroup.zpowers_le.2 hdD)
  have hBs : B < B ⊔ Subgroup.zpowers d := lt_of_le_of_ne le_sup_left fun h =>
    hdB (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers d))
  obtain ⟨c, hc⟩ : Nat.card B ∣ Nat.card ↥(B ⊔ Subgroup.zpowers d) :=
    Subgroup.card_dvd_of_le le_sup_left
  obtain ⟨e, he⟩ : Nat.card ↥(B ⊔ Subgroup.zpowers d) ∣ Nat.card D := Subgroup.card_dvd_of_le hle
  have h3 : Nat.card B < Nat.card ↥(B ⊔ Subgroup.zpowers d) := Subgroup.card_lt_of_lt hBs
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hce : c * e = 2 := by
    have : Nat.card B * (c * e) = Nat.card B * 2 := by
      rw [← mul_assoc, ← hc, ← he, hD2, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hBpos this
  have hc2 : c = 2 := by
    have hc1 : c ≠ 1 := by rintro rfl; rw [mul_one] at hc; omega
    have hc0 : c ≠ 0 := by rintro rfl; omega
    have : c ∣ 2 := ⟨e, hce.symm⟩
    rcases (Nat.dvd_prime Nat.prime_two).1 this with h | h
    · exact absurd h hc1
    · exact h
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc, hc2, hD2, mul_comm])

theorem card_commV_le_index_pow [Finite W] :
    ∀ (r : ℕ) (D : Subgroup (MulAut W)), Nat.card D = 2 ^ r →
      Nat.card (commV D) ≤ (fixV D).index ^ r := by
  intro r
  induction r with
  | zero =>
    intro D hD
    have hbot : D = ⊥ := Subgroup.eq_bot_of_card_eq D (by simpa using hD)
    subst hbot
    have : commV (⊥ : Subgroup (MulAut W)) = ⊥ := by
      refine le_bot_iff.1 ((Subgroup.closure_le _).2 ?_)
      rintro _ ⟨x, hx, w, rfl⟩
      rw [Subgroup.mem_bot.1 hx]
      simp
    rw [this, Subgroup.card_bot, pow_zero]
  | succ r ih =>
    intro D hD
    obtain ⟨B, d, hdD, hBD, hBcard, hsup⟩ := exists_index_two hD (Nat.succ_pos r)
    rw [Nat.add_sub_cancel] at hBcard
    have hidxB : (fixV B).index ≤ (fixV D).index :=
      Subgroup.index_antitone (B1.fixV_le_fixV hBD)
    have hidxd : (fixV (Subgroup.zpowers d)).index ≤ (fixV D).index :=
      Subgroup.index_antitone (B1.fixV_le_fixV (Subgroup.zpowers_le.2 hdD))
    calc Nat.card (commV D) ≤ Nat.card ↥(commV B ⊔ commV (Subgroup.zpowers d)) := by
          rw [← hsup]
          exact Subgroup.card_le_of_le (commV_sup_le _ _)
      _ ≤ Nat.card (commV B) * Nat.card (commV (Subgroup.zpowers d)) := card_sup_le _ _
      _ ≤ (fixV D).index ^ r * (fixV D).index :=
          Nat.mul_le_mul ((ih B hBcard).trans (Nat.pow_le_pow_left hidxB _))
            ((card_commV_zpowers_le d).trans hidxd)
      _ = (fixV D).index ^ (r + 1) := (pow_succ _ _).symm

theorem isGood_zpowers [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {G : Subgroup (MulAut W)}
    {a : MulAut W} (haG : a ∈ G) (ha1 : a ≠ 1) (ha : a ^ 2 = 1)
    (hcard : Nat.card (commV (Subgroup.zpowers a)) ≤ 4) : IsGood G (Subgroup.zpowers a) := by
  have hord : orderOf a = 2 := orderOf_eq_prime ha ha1
  have hcardA : Nat.card (Subgroup.zpowers a) = 2 := by rw [Nat.card_zpowers, hord]
  refine ⟨Subgroup.zpowers_le.2 haG, fun h => ha1 ?_, ⟨fun x hx y hy => ?_, fun x hx => ?_⟩,
    Or.inr ⟨commV_zpowers_le_fixV ha hW, by rw [hcardA]; exact hcard⟩⟩
  · rw [Subgroup.zpowers_eq_bot] at h
    exact h
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact zpow_mul_comm a m n
  · obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ha, one_zpow]

theorem HasGood.of_zpowers [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {G : Subgroup (MulAut W)}
    {a : MulAut W} (haG : a ∈ G) (ha1 : a ≠ 1) (ha : a ^ 2 = 1)
    (hcard : Nat.card (commV (Subgroup.zpowers a)) ≤ 4) : HasGood G :=
  ⟨_, isGood_zpowers hW haG ha1 ha hcard⟩

theorem hasGood_of_isFFStarMin {G D : Subgroup (MulAut W)} [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hD : IsFFStarMin G D) (hidx : (fixV D).index ≤ 4) : HasGood G := by
  have hel := hD.1.2.2.1
  have hquad : IsQuadratic D := B1_4_3 hW hD
  refine ⟨D, hD.1.1, hD.1.2.1, hel, Or.inr ⟨hquad, ?_⟩⟩
  calc Nat.card (commV D) ≤ (fixV D).index ^ rk D :=
        card_commV_le_index_pow _ D (B1.card_elemAbelian hel)
    _ ≤ 4 ^ rk D := Nat.pow_le_pow_left hidx _
    _ = Nat.card D ^ 2 := by
      rw [B1.card_elemAbelian hel, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul,
        mul_comm]

end CFSG.Quasithin.B513N
