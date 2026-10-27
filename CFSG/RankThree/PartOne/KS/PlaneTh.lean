module

public import CFSG.RankThree.PartOne.KS.ThPlaneQuot
public import CFSG.RankThree.PartOne.KS.PlaneOddGeneric
public import CFSG.RankThree.PartOne.KS.Assembly
public import CFSG.Sporadic.Th.Max3.Maximal
public import CFSG.Sporadic.ThSchreier.ThSchreierCase

public section

namespace CFSG.RankThree.PartOne.ThPlane

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Certificates.ExtraspecialNF
open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.Sporadic.ThSchreier (ctuc_Th_full_automorphism_group)

section Generic

variable {G : Type} [Group G]

@[expose] def InvCentConj (M : Subgroup G) : Prop :=
  ∀ v : G, orderOf v = 2 →
    ∃ g : G, Subgroup.centralizer ({v} : Set G) = M.map (MulAut.conj g).toMonoidHom

theorem q1_gen {M : Subgroup G} (h : InvCentConj M) {p : ℕ} (hM : ¬ p ^ 2 ∣ Nat.card M)
    (E : Subgroup G) (hEcard : Nat.card E = p ^ 2) (v : G) (hv2 : v ^ 2 = 1)
    (hc : ∀ a ∈ E, a * v = v * a) : v = 1 := by
  by_contra hv1
  have hvo : orderOf v = 2 := orderOf_eq_prime hv2 hv1
  obtain ⟨g, hg⟩ := h v hvo
  have hEle : E ≤ Subgroup.centralizer ({v} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hc a ha)
  rw [hg] at hEle
  have hdvd : Nat.card E ∣ Nat.card (M.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.card_dvd_of_le hEle
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hEcard] at hdvd
  exact hM hdvd

theorem exists_conj_into_M_gen {M : Subgroup G} (h : InvCentConj M) {t : G} (V : Subgroup G)
    (hV : V ≠ ⊥) (hVt : ∀ x ∈ V, x * t = t * x) (hVe : IsElementaryAbelian 2 V) :
    ∃ g : G, g⁻¹ * t * g ∈ M ∧ ∀ x ∈ V, g⁻¹ * x * g ∈ M := by
  obtain ⟨⟨v, hvV⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV
  have hv2 : v ^ 2 = 1 := by
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 V) ⟨v, hvV⟩
    simpa using congrArg Subtype.val this
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hvo : orderOf v = 2 := orderOf_eq_prime hv2 hv1'
  obtain ⟨g, hg⟩ := h v hvo
  have key : ∀ y : G, y ∈ Subgroup.centralizer ({v} : Set G) → g⁻¹ * y * g ∈ M := by
    intro y hy
    rw [hg] at hy
    obtain ⟨m, hm, hmy⟩ := Subgroup.mem_map.mp hy
    have : g⁻¹ * y * g = m := by
      rw [← hmy]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [this]
    exact hm
  refine ⟨g, key t (Subgroup.mem_centralizer_singleton_iff.mpr (hVt v hvV).symm),
    fun x hx => key x (Subgroup.mem_centralizer_singleton_iff.mpr ?_)⟩
  have hcomm := hVe.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : V) ⟨v, hvV⟩
  have := congrArg Subtype.val hcomm
  simpa only [Subgroup.coe_mul] using this

theorem conj_subgroup_le_M_gen {M V : Subgroup G} {g : G} (hgV : ∀ x ∈ V, g⁻¹ * x * g ∈ M) :
    V.map (MulAut.conj g⁻¹).toMonoidHom ≤ M := by
  rintro _ ⟨x, hx, rfl⟩
  have := hgV x hx
  simpa [MulAut.conj_apply] using this

theorem conj_commute_gen {g t x : G} (h : x * t = t * x) :
    (g⁻¹ * x * g⁻¹⁻¹) * (g⁻¹ * t * g) = (g⁻¹ * t * g) * (g⁻¹ * x * g⁻¹⁻¹) := by
  calc g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * t * g) = g⁻¹ * (x * t) * g := by group
    _ = g⁻¹ * (t * x) * g := by rw [h]
    _ = g⁻¹ * t * g * (g⁻¹ * x * g⁻¹⁻¹) := by group

theorem conj_commute_gen' {g x y : G} (h : x * y = y * x) :
    (g⁻¹ * x * g⁻¹⁻¹) * (g⁻¹ * y * g⁻¹⁻¹) = (g⁻¹ * y * g⁻¹⁻¹) * (g⁻¹ * x * g⁻¹⁻¹) := by
  calc g⁻¹ * x * g⁻¹⁻¹ * (g⁻¹ * y * g⁻¹⁻¹) = g⁻¹ * (x * y) * g := by group
    _ = g⁻¹ * (y * x) * g := by rw [h]
    _ = g⁻¹ * y * g⁻¹⁻¹ * (g⁻¹ * x * g⁻¹⁻¹) := by group

theorem orderOf_conj_gen (g t : G) {n : ℕ} (ht : orderOf t = n) : orderOf (g⁻¹ * t * g) = n := by
  have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) t
  simpa [MulAut.conj_apply, ht] using this

theorem card_mulAut_eq_of_bijective {T : Type} [Group T]
    (hinj : Function.Injective (MulAut.conj : T →* MulAut T))
    (hsurj : Function.Surjective (MulAut.conj : T →* MulAut T)) :
    Nat.card (MulAut T) = Nat.card T :=
  Nat.card_congr (MulEquiv.ofBijective (MulAut.conj : T →* MulAut T) ⟨hinj, hsurj⟩).symm.toEquiv

variable [Finite G] (D : ExtQuotData G (alternatingGroup (Fin 9)))

theorem q2_five (h : InvCentConj D.M) {w : G} (hw : w ∈ D.M) (hπw : orderOf (D.π ⟨w, hw⟩) = 5)
    (hfix : ∀ v, D.act w v = v → v = 0) (t : G) (ht : orderOf t = 5) (V : Subgroup G)
    (hV : V ≤ Subgroup.centralizer ({t} : Set G)) (hVe : IsElementaryAbelian 2 V)
    (hmod : Nat.card V ≡ 1 [MOD 5]) : V = ⊥ := by
  by_contra hVbot
  have hVt : ∀ x ∈ V, x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hV hx)
  obtain ⟨g, hgt, hgV⟩ := exists_conj_into_M_gen h V hVbot hVt hVe
  have hV2 : IsPGroup 2 V := IsElementaryAbelian.isPGroup 2 V
  have hle : Nat.card (V.map (MulAut.conj g⁻¹).toMonoidHom) ≤ 8 := by
    refine D.card_le_eight (t := g⁻¹ * t * g) (w := w) hgt hw hπw (orderOf_conj_gen g t ht) hfix
      (conj_subgroup_le_M_gen hgV) ?_ (hV2.map _)
    rintro _ ⟨x, hx, rfl⟩
    exact conj_commute_gen (hVt x hx)
  rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at hle
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV2
  have hk0 : 1 < Nat.card V := (Subgroup.one_lt_card_iff_ne_bot V).mpr hVbot
  rw [hk] at hle hmod hk0
  have hk3 : k ≤ 3 := by
    by_contra hcon
    have : 2 ^ 4 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> simp [Nat.ModEq] at hmod hk0

theorem q2_seven (h : InvCentConj D.M) {w : G} (hw : w ∈ D.M) (hπw : orderOf (D.π ⟨w, hw⟩) = 7)
    (D0 : Set (Fin 8 → ZMod 2)) (hD0 : ∀ v, D.act w v = v → v ∈ D0)
    (hpair : ∀ e ∈ D0, ∀ e' ∈ D0, e ≠ 0 → e' ≠ 0 → e ≠ e' → bil D.c e e' = 1)
    (t : G) (ht : orderOf t = 7) (V : Subgroup G) (hV : V ≤ Subgroup.centralizer ({t} : Set G))
    (hVe : IsElementaryAbelian 2 V) (hmod : Nat.card V ≡ 1 [MOD 7]) : V = ⊥ := by
  by_contra hVbot
  have hVt : ∀ x ∈ V, x * t = t * x := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mp (hV hx)
  obtain ⟨g, hgt, hgV⟩ := exists_conj_into_M_gen h V hVbot hVt hVe
  have hV2 : IsPGroup 2 V := IsElementaryAbelian.isPGroup 2 V
  have hle : Nat.card (V.map (MulAut.conj g⁻¹).toMonoidHom) ≤ 4 := by
    refine D.card_le_four (t := g⁻¹ * t * g) (w := w) hgt hw hπw (orderOf_conj_gen g t ht) D0 hD0
      hpair (conj_subgroup_le_M_gen hgV) ?_ ?_ (hV2.map _)
    · rintro _ ⟨x, hx, rfl⟩
      exact conj_commute_gen (hVt x hx)
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      have hcomm := hVe.toIsMulCommutative.is_comm.comm (⟨x, hx⟩ : V) ⟨y, hy⟩
      have h1 : x * y = y * x := by
        have := congrArg Subtype.val hcomm
        simpa only [Subgroup.coe_mul] using this
      exact conj_commute_gen' h1
  rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective] at hle
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV2
  have hk0 : 1 < Nat.card V := (Subgroup.one_lt_card_iff_ne_bot V).mpr hVbot
  rw [hk] at hle hmod hk0
  have hk3 : k ≤ 2 := by
    by_contra hcon
    have : 2 ^ 3 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases k <;> simp [Nat.ModEq] at hmod hk0

end Generic

section Data

@[expose] noncomputable def thData : ExtQuotData J (alternatingGroup (Fin 9)) where
  z := Max3.z
  q := Max3.q
  c := Max3.c
  M := Max3.M
  rel := symplectic_rel
  inj := nf_injective_generic
  Q_le := Q_le_M
  norm := fun m hm g hg => (Subgroup.mem_normalizer_iff.mp (M_le_normalizer_Q hm) g).mp hg
  zc := fun m hm => (commute_z_of_mem_M hm).eq.symm
  π := kappa.toMonoidHom.comp AltQuot.proj
  surj := kappa.surjective.comp AltQuot.proj_surjective
  ker := fun m => by
    have h1 : kappa (AltQuot.proj m) = 1 ↔ AltQuot.proj m = 1 := MulEquiv.map_eq_one_iff kappa
    exact h1.trans AltQuot.proj_eq_one_iff

theorem thData_π_x : thData.π ⟨x, x_mem_M⟩ = ⟨aPerm, aPerm_mem⟩ := Subtype.ext kappa_mk_x

theorem thData_π_y : thData.π ⟨y, y_mem_M⟩ = ⟨bPerm, bPerm_mem⟩ := Subtype.ext kappa_mk_y

theorem act_x (v : Fin 8 → ZMod 2) : thData.act x v = B1.mulVec v := by
  rw [thData.act_eq_mulVec x_mem_M xv ?_ v]
  · rfl
  · intro i
    show coord Max3.z Max3.q (x * Max3.q i * x⁻¹) = xv i
    rw [x_conj_q, nf_eq_generic, coord_nf nf_injective_generic]

theorem act_y (v : Fin 8 → ZMod 2) : thData.act y v = B2.mulVec v := by
  rw [thData.act_eq_mulVec y_mem_M yv ?_ v]
  · rfl
  · intro i
    show coord Max3.z Max3.q (y * Max3.q i * y⁻¹) = yv i
    rw [y_conj_q, nf_eq_generic, coord_nf nf_injective_generic]

end Data

section Words

@[expose] noncomputable def w5 : J := y ^ 4 * x * y ^ 3 * x * y ^ 2 * x

@[expose] noncomputable def w7 : J := y ^ 5 * x * y * x

theorem w5_mem : w5 ∈ M :=
  M.mul_mem (M.mul_mem (M.mul_mem (M.mul_mem (M.mul_mem (M.pow_mem y_mem_M 4) x_mem_M)
    (M.pow_mem y_mem_M 3)) x_mem_M) (M.pow_mem y_mem_M 2)) x_mem_M

theorem w7_mem : w7 ∈ M :=
  M.mul_mem (M.mul_mem (M.mul_mem (M.pow_mem y_mem_M 5) x_mem_M) y_mem_M) x_mem_M

theorem act_w5 (v : Fin 8 → ZMod 2) :
    thData.act w5 v = (B2 ^ 4 * B1 * B2 ^ 3 * B1 * B2 ^ 2 * B1).mulVec v := by
  have h4 := thData.act_pow_matrix y_mem_M act_y 4
  have h3 := thData.act_pow_matrix y_mem_M act_y 3
  have h2 := thData.act_pow_matrix y_mem_M act_y 2
  have m1 : ∀ v, thData.act (y ^ 4 * x) v = (B2 ^ 4 * B1).mulVec v :=
    thData.act_mul_matrix (M.pow_mem y_mem_M 4) x_mem_M h4 act_x
  have m2 : ∀ v, thData.act (y ^ 4 * x * y ^ 3) v = (B2 ^ 4 * B1 * B2 ^ 3).mulVec v :=
    thData.act_mul_matrix (M.mul_mem (M.pow_mem y_mem_M 4) x_mem_M) (M.pow_mem y_mem_M 3) m1 h3
  have m3 : ∀ v, thData.act (y ^ 4 * x * y ^ 3 * x) v =
      (B2 ^ 4 * B1 * B2 ^ 3 * B1).mulVec v :=
    thData.act_mul_matrix (M.mul_mem (M.mul_mem (M.pow_mem y_mem_M 4) x_mem_M)
      (M.pow_mem y_mem_M 3)) x_mem_M m2 act_x
  have m4 : ∀ v, thData.act (y ^ 4 * x * y ^ 3 * x * y ^ 2) v =
      (B2 ^ 4 * B1 * B2 ^ 3 * B1 * B2 ^ 2).mulVec v :=
    thData.act_mul_matrix (M.mul_mem (M.mul_mem (M.mul_mem (M.pow_mem y_mem_M 4) x_mem_M)
      (M.pow_mem y_mem_M 3)) x_mem_M) (M.pow_mem y_mem_M 2) m3 h2
  exact thData.act_mul_matrix (M.mul_mem (M.mul_mem (M.mul_mem (M.mul_mem (M.pow_mem y_mem_M 4)
    x_mem_M) (M.pow_mem y_mem_M 3)) x_mem_M) (M.pow_mem y_mem_M 2)) x_mem_M m4 act_x v

theorem act_w7 (v : Fin 8 → ZMod 2) :
    thData.act w7 v = (B2 ^ 5 * B1 * B2 * B1).mulVec v := by
  have h5 := thData.act_pow_matrix y_mem_M act_y 5
  have m1 : ∀ v, thData.act (y ^ 5 * x) v = (B2 ^ 5 * B1).mulVec v :=
    thData.act_mul_matrix (M.pow_mem y_mem_M 5) x_mem_M h5 act_x
  have m2 : ∀ v, thData.act (y ^ 5 * x * y) v = (B2 ^ 5 * B1 * B2).mulVec v :=
    thData.act_mul_matrix (M.mul_mem (M.pow_mem y_mem_M 5) x_mem_M) y_mem_M m1 act_y
  exact thData.act_mul_matrix (M.mul_mem (M.mul_mem (M.pow_mem y_mem_M 5) x_mem_M) y_mem_M)
    x_mem_M m2 act_x v

theorem thData_π_w5 : (thData.π ⟨w5, w5_mem⟩ : Equiv.Perm (Fin 9)) =
    bPerm ^ 4 * aPerm * bPerm ^ 3 * aPerm * bPerm ^ 2 * aPerm := by
  have e : (⟨w5, w5_mem⟩ : ↥thData.M) = ⟨y, y_mem_M⟩ ^ 4 * ⟨x, x_mem_M⟩ * ⟨y, y_mem_M⟩ ^ 3 *
      ⟨x, x_mem_M⟩ * ⟨y, y_mem_M⟩ ^ 2 * ⟨x, x_mem_M⟩ := Subtype.ext (by simp [w5])
  rw [e]
  simp only [map_mul, map_pow, thData_π_x, thData_π_y, Subgroup.coe_mul, Subgroup.coe_pow]

theorem thData_π_w7 : (thData.π ⟨w7, w7_mem⟩ : Equiv.Perm (Fin 9)) =
    bPerm ^ 5 * aPerm * bPerm * aPerm := by
  have e : (⟨w7, w7_mem⟩ : ↥thData.M) = ⟨y, y_mem_M⟩ ^ 5 * ⟨x, x_mem_M⟩ * ⟨y, y_mem_M⟩ *
      ⟨x, x_mem_M⟩ := Subtype.ext (by simp [w7])
  rw [e]
  simp only [map_mul, map_pow, thData_π_x, thData_π_y, Subgroup.coe_mul, Subgroup.coe_pow]

theorem orderOf_π_w5 : orderOf (thData.π ⟨w5, w5_mem⟩) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : (bPerm ^ 4 * aPerm * bPerm ^ 3 * aPerm * bPerm ^ 2 * aPerm) ^ 5 = 1 := by
    decide +kernel
  have h1 : bPerm ^ 4 * aPerm * bPerm ^ 3 * aPerm * bPerm ^ 2 * aPerm ≠ 1 := by
    decide +kernel
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    rw [Subgroup.coe_pow, thData_π_w5, h5]
    rfl
  · intro h
    apply h1
    rw [← thData_π_w5, h]
    rfl

theorem orderOf_π_w7 : orderOf (thData.π ⟨w7, w7_mem⟩) = 7 := by
  have : Fact (Nat.Prime 7) := ⟨by decide⟩
  have h7 : (bPerm ^ 5 * aPerm * bPerm * aPerm) ^ 7 = 1 := by decide +kernel
  have h1 : bPerm ^ 5 * aPerm * bPerm * aPerm ≠ 1 := by decide +kernel
  refine orderOf_eq_prime ?_ ?_
  · apply Subtype.ext
    rw [Subgroup.coe_pow, thData_π_w7, h7]
    rfl
  · intro h
    apply h1
    rw [← thData_π_w7, h]
    rfl

end Words

theorem fix5 : ∀ v : Fin 8 → ZMod 2,
    (B2 ^ 4 * B1 * B2 ^ 3 * B1 * B2 ^ 2 * B1).mulVec v = v → v = 0 := by decide +kernel

@[expose] def D7 : Finset (Fin 8 → ZMod 2) :=
  {0, ![1, 1, 0, 0, 0, 1, 0, 0], ![1, 1, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 1, 0, 1]}

theorem fix7 : ∀ v : Fin 8 → ZMod 2,
    (B2 ^ 5 * B1 * B2 * B1).mulVec v = v → v ∈ D7 := by decide +kernel

theorem pair7 : ∀ e ∈ D7, ∀ e' ∈ D7, e ≠ 0 → e' ≠ 0 → e ≠ e' → bil c e e' = 1 := by
  decide +kernel

section JLevel

theorem prime_dvd_card_J {p : ℕ} (hp : p.Prime) (h : p ∣ 90745943887872000) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 13 ∨ p = 19 ∨ p = 31 := by
  have e : (90745943887872000 : ℕ) = 2 ^ 15 * 3 ^ 10 * 5 ^ 3 * 7 ^ 2 * 13 * 19 * 31 := by
    norm_num
  rw [e] at h
  have key : ∀ a b : ℕ, p ∣ a * b → p ∣ a ∨ p ∣ b := fun a b hab => (Nat.Prime.dvd_mul hp).1 hab
  have hq : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hpq =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 hpq
  rcases key _ _ h with h | h
  · rcases key _ _ h with h | h
    · rcases key _ _ h with h | h
      · rcases key _ _ h with h | h
        · rcases key _ _ h with h | h
          · rcases key _ _ h with h | h
            · exact Or.inl (hq 2 Nat.prime_two (hp.dvd_of_dvd_pow h))
            · exact Or.inr (Or.inl (hq 3 Nat.prime_three (hp.dvd_of_dvd_pow h)))
          · exact Or.inr (Or.inr (Or.inl (hq 5 Nat.prime_five (hp.dvd_of_dvd_pow h))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (hq 7 (by norm_num) (hp.dvd_of_dvd_pow h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hq 13 (by norm_num) h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hq 19 (by norm_num) h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (hq 31 (by norm_num) h))))))

theorem not_sq_dvd_card_J {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) (h57 : ¬ (p = 5 ∨ p = 7)) :
    ¬ p ^ 2 ∣ 90745943887872000 := by
  intro h
  have h1 : p ∣ 90745943887872000 := (dvd_pow_self p two_ne_zero).trans h
  rcases prime_dvd_card_J hp h1 with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · omega
  · omega
  · exact h57 (Or.inl rfl)
  · exact h57 (Or.inr rfl)
  · norm_num at h
  · norm_num at h
  · norm_num at h

theorem J_nonabelian : ∃ a b : J, a * b ≠ b * a := by
  refine ⟨x, y, fun h => ?_⟩
  have h1 : (⟨x, x_mem_M⟩ : ↥thData.M) * ⟨y, y_mem_M⟩ = ⟨y, y_mem_M⟩ * ⟨x, x_mem_M⟩ :=
    Subtype.ext h
  have h2 := congrArg thData.π h1
  rw [map_mul, map_mul, thData_π_x, thData_π_y] at h2
  have h3 : aPerm * bPerm = bPerm * aPerm := congrArg Subtype.val h2
  have hne : aPerm * bPerm ≠ bPerm * aPerm := by decide +kernel
  exact hne h3

theorem invCentConj_J : InvCentConj thData.M := by
  intro v hv
  obtain ⟨g, hg⟩ := isConj_iff.mp (all_involutions_conjugate v hv)
  refine ⟨g, ?_⟩
  have h1 : Subgroup.centralizer ({v} : Set J) =
      (Subgroup.centralizer ({a} : Set J)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, centralizer_conj]
  exact h1.trans (congrArg (fun K : Subgroup J => K.map (MulAut.conj g).toMonoidHom)
    (CFSG.Sporadic.Th.Kernel.centralizer_a_eq_M CFSG.Sporadic.Th.th_kernel_facts))

theorem planeLocalCoreOdd_J {p : ℕ} (hp57 : p = 5 ∨ p = 7) : PlaneLocalCoreOdd p J := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hsimple : IsSimpleGroup J :=
    CFSG.Sporadic.Th.Kernel.isSimpleGroup_J CFSG.Sporadic.Th.th_kernel_facts
  have hinj := conj_injective_of_center_eq_bot (T := J)
    (center_eq_bot_of_simple (T := J) J_nonabelian)
  have hsurj := MonoidHom.range_eq_top.mp (ctuc_Th_full_automorphism_group.{0}.1 : inner J = ⊤)
  have hM : Nat.card thData.M = 92897280 := card_M
  have hnsq : ¬ p ^ 2 ∣ Nat.card thData.M := by
    rw [hM]
    rcases hp57 with rfl | rfl <;> norm_num
  refine planeLocalCoreOdd_of_centralizer_data (T := J) hp hinj hsurj
    (fun E _ hEcard v hv2 hc => q1_gen invCentConj_J hnsq E hEcard v hv2 hc)
    (fun t ht V hV hVe hmod => ?_)
  rcases hp57 with rfl | rfl
  · exact q2_five thData invCentConj_J w5_mem orderOf_π_w5
      (fun v hv => fix5 v (by rw [← act_w5]; exact hv)) t ht V hV hVe hmod
  · exact q2_seven thData invCentConj_J w7_mem orderOf_π_w7 (↑D7)
      (fun v hv => Finset.mem_coe.mpr (fix7 v (by rw [← act_w7]; exact hv)))
      (fun e he e' he' h0 h0' hne =>
        pair7 e (Finset.mem_coe.mp he) e' (Finset.mem_coe.mp he') h0 h0' hne)
      t ht V hV hVe hmod

theorem card_mulAut_J : Nat.card (MulAut J) = 90745943887872000 := by
  have hsimple : IsSimpleGroup J :=
    CFSG.Sporadic.Th.Kernel.isSimpleGroup_J CFSG.Sporadic.Th.th_kernel_facts
  have hinj := conj_injective_of_center_eq_bot (T := J)
    (center_eq_bot_of_simple (T := J) J_nonabelian)
  have hsurj := MonoidHom.range_eq_top.mp (ctuc_Th_full_automorphism_group.{0}.1 : inner J = ⊤)
  rw [← natCard_J]
  exact card_mulAut_eq_of_bijective (T := J) hinj hsurj

end JLevel

end CFSG.RankThree.PartOne.ThPlane

namespace CFSG.RankThree.PartOne

open CFSG.Blueprint.NativeSporadic (Carrier)
open CFSG.Sporadic.Th

theorem sporadicPlaneOdd_Th : SporadicPlaneOdd (Carrier .Th) := by
  intro T _ _ hs hnab ⟨e⟩ p hp hp3
  have e' : T ≃* J := e.trans thEquivJ
  refine PlaneLocalCoreOdd.of_mulEquiv (T' := J) hp e' ?_
  by_cases h57 : p = 5 ∨ p = 7
  · exact ThPlane.planeLocalCoreOdd_J h57
  · refine planeLocalCoreOdd_of_not_sq_dvd (T := J) ?_
    rw [ThPlane.card_mulAut_J]
    exact ThPlane.not_sq_dvd_card_J hp hp3 h57

end CFSG.RankThree.PartOne
