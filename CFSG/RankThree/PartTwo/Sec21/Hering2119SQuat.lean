module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119SPair

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open Module

section Quat

variable {V : Type*} [AddCommGroup V] [Module F3 V]

theorem unip_of_fix (ε : V →ₗ[F3] V) (hk : ∀ v, ε v = 0 → v ∈ LinearMap.range ε)
    (g : V ≃ₗ[F3] V) (hc : ∀ v, g (ε v) = ε (g v))
    (hfix : ∀ w ∈ LinearMap.range ε, g w = w) (v : V) :
    g v - v ∈ LinearMap.range ε := by
  apply hk
  rw [map_sub, ← hc, hfix _ ⟨v, rfl⟩, sub_self]

theorem pow3_of_fix (ε : V →ₗ[F3] V) (hk : ∀ v, ε v = 0 → v ∈ LinearMap.range ε)
    (g : V ≃ₗ[F3] V) (hc : ∀ v, g (ε v) = ε (g v))
    (hfix : ∀ w ∈ LinearMap.range ε, g w = w) : g * g * g = 1 := by
  set N : V →ₗ[F3] V := (g : V →ₗ[F3] V) - LinearMap.id with hN
  have hgN : ∀ v, g v = v + N v := fun v => by simp [hN]
  have hN2 : ∀ v, N (N v) = 0 := by
    intro v
    have h1 : N v ∈ LinearMap.range ε := by
      have := unip_of_fix ε hk g hc hfix v
      simpa [hN] using this
    have := hfix _ h1
    simpa [hN, sub_eq_zero] using this
  exact pow3_g g N hgN hN2

theorem eq_one_of_two_elt (ε : V →ₗ[F3] V) (hk : ∀ v, ε v = 0 → v ∈ LinearMap.range ε)
    (g : V ≃ₗ[F3] V) (hc : ∀ v, g (ε v) = ε (g v))
    (hfix : ∀ w ∈ LinearMap.range ε, g w = w) (k : ℕ) (hg2 : g ^ (2 ^ k) = 1) : g = 1 := by
  have h3 : g ^ 3 = 1 := by
    have := pow3_of_fix ε hk g hc hfix
    rw [pow_succ, pow_two]
    exact this
  have hd2 : orderOf g ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hg2
  have hd3 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h1 : orderOf g ∣ Nat.gcd (2 ^ k) 3 := Nat.dvd_gcd hd2 hd3
  have hg : Nat.gcd (2 ^ k) 3 = 1 := by
    apply Nat.Coprime.pow_left
    norm_num
  rw [hg] at h1
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)

theorem ker_form [Finite V] (hV : Nat.card V = 81) (ε : V →ₗ[F3] V) (hε : ∀ v, ε (ε v) = 0)
    (hk : ∀ v, ε v = 0 → v ∈ LinearMap.range ε) (K : Subgroup (V ≃ₗ[F3] V))
    (hcomm : ∀ h ∈ K, ∀ v, h (ε v) = ε (h v)) (u₁ : V ≃ₗ[F3] V)
    (hu₁ : ∀ v, u₁ v = v + ε v) (hu₁K : u₁ ∈ K)
    (htrans : ∀ w w' : V, w ∈ LinearMap.range ε → w' ∈ LinearMap.range ε → w ≠ 0 → w' ≠ 0 →
      ∃ h ∈ K, h w = w')
    (hord3 : ∃ s ∈ K, s ^ 3 = 1 ∧ ∃ w ∈ LinearMap.range ε, s w ≠ w)
    (hbound : ∀ X : Subgroup (V ≃ₗ[F3] V), X ≤ K → IsPGroup 3 X → u₁ ∈ X →
      (∀ x ∈ X, x * u₁ = u₁ * x) → Nat.card X ≤ 81)
    (k : V ≃ₗ[F3] V) (hkK : k ∈ K) (hfix : ∀ w ∈ LinearMap.range ε, k w = w) :
    ∃ c : F3, ∀ v, k v = v + c • ε v := by
  classical
  have hW := card_range_eq_nine hV ε hε hk
  set T : V →ₗ[F3] V := (k : V →ₗ[F3] V) - LinearMap.id with hT
  have hTv : ∀ v, T v = k v - v := fun v => by simp [hT]
  obtain ⟨ν, hν⟩ := exists_factor ε T
    (fun v => by rw [hTv]; exact unip_of_fix ε hk k (hcomm k hkK) hfix v)
    (fun v hv => by rw [hTv, hfix v (hk v hv), sub_self])
  have hkν : uEquiv ε hε ν = k := by
    apply LinearEquiv.ext
    intro v
    rw [uEquiv_apply, hν, hTv]
    abel
  by_cases hsc : ∃ c : F3, ν = c • (LinearMap.id : LinearMap.range ε →ₗ[F3] LinearMap.range ε)
  · obtain ⟨c, hc⟩ := hsc
    refine ⟨c, fun v => ?_⟩
    have h1 := hν v
    rw [hc, hTv] at h1
    have h2 : k v - v = c • ε v := by
      rw [← h1]
      simp [LinearMap.rangeRestrict]
    rw [← h2]
    abel
  · push Not at hsc
    exfalso
    obtain ⟨X, hXK, hX3, hX243, hu₁X, hXcomm⟩ :=
      na_core' ε hε hW hk K hcomm u₁ hu₁ hu₁K htrans hord3 ν (by rw [hkν]; exact hkK) hsc
    have := hbound X hXK hX3 hu₁X hXcomm
    omega

theorem q8_pre {W : Type*} [AddCommGroup W] [Module F3 W] (f : (W ≃ₗ[F3] W) →* Mat2)
    (I J : W ≃ₗ[F3] W) : ∀ w ∈ q8g (· * ·) (1 : Mat2) (f I) (f J), ∃ y ∈ q8 I J, f y = w := by
  intro w hw
  simp only [q8g, List.mem_cons, List.not_mem_nil, or_false] at hw
  simp only [q8, List.mem_cons, List.not_mem_nil, or_false]
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, Or.inl rfl, map_one f⟩
  · exact ⟨I, Or.inr (Or.inl rfl), rfl⟩
  · exact ⟨I * I, Or.inr (Or.inr (Or.inl rfl)), by rw [map_mul]⟩
  · exact ⟨I * I * I, Or.inr (Or.inr (Or.inr (Or.inl rfl))), by rw [map_mul, map_mul]⟩
  · exact ⟨J, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), rfl⟩
  · exact ⟨I * J, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), by rw [map_mul]⟩
  · exact ⟨I * I * J, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))), by
      rw [map_mul, map_mul]⟩
  · exact ⟨I * I * I * J, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))), by
      rw [map_mul, map_mul, map_mul]⟩

theorem norm_lem {W : Type*} [AddCommGroup W] [Module F3 W] (hW : Module.finrank F3 W = 2)
    (I J g : W ≃ₗ[F3] W) (hI : ∀ w, I (I w) = -w) (hJ : ∀ w, J (J w) = -w)
    (hIJ : ∀ w, I (J w) = -J (I w)) :
    (∃ y ∈ q8 I J, g * I = y * g) ∧ (∃ y ∈ q8 I J, g * J = y * g) := by
  haveI : Module.Finite F3 W := Module.finite_of_finrank_pos (by omega)
  let b : Basis (Fin 2) F3 W := Module.finBasisOfFinrankEq F3 W hW
  let Θ := eqvGL b
  let f : (W ≃ₗ[F3] W) →* Mat2 := (Units.coeHom Mat2).comp Θ.toMonoidHom
  have hf : ∀ x : W ≃ₗ[F3] W, f x = LinearMap.toMatrix b b (x : W →ₗ[F3] W) :=
    fun x => eqvGL_coe b x
  have hfinj : Function.Injective f := by
    intro x y h
    exact Θ.injective (Units.ext h)
  have hI2 : f I * f I = -1 := by
    rw [← map_mul, hf]
    have : ((I * I : W ≃ₗ[F3] W) : W →ₗ[F3] W) = -LinearMap.id :=
      LinearMap.ext fun w => by simp [hI]
    rw [this, map_neg, LinearMap.toMatrix_id]
  have hJ2 : f J * f J = -1 := by
    rw [← map_mul, hf]
    have : ((J * J : W ≃ₗ[F3] W) : W →ₗ[F3] W) = -LinearMap.id :=
      LinearMap.ext fun w => by simp [hJ]
    rw [this, map_neg, LinearMap.toMatrix_id]
  have hIJ' : f I * f J = -(f J * f I) := by
    rw [← map_mul, ← map_mul, hf, hf]
    have : ((I * J : W ≃ₗ[F3] W) : W →ₗ[F3] W) = -((J * I : W ≃ₗ[F3] W) : W →ₗ[F3] W) :=
      LinearMap.ext fun w => by simp [hIJ]
    rw [this, map_neg]
  have hdet : (f g).det ≠ 0 := by
    have h1 : IsUnit ((Θ g : GL (Fin 2) F3) : Mat2) := Units.isUnit _
    have h2 := (Matrix.isUnit_iff_isUnit_det _).mp h1
    exact h2.ne_zero
  obtain ⟨⟨y1, hy1, e1⟩, ⟨y2, hy2, e2⟩⟩ := norm_dec (f I) (mem_Q6 _ hI2) (f J) (mem_Q6 _ hJ2) hIJ'
    (f g) hdet
  obtain ⟨z1, hz1, hz1e⟩ := q8_pre f I J y1 hy1
  obtain ⟨z2, hz2, hz2e⟩ := q8_pre f I J y2 hy2
  refine ⟨⟨z1, hz1, hfinj ?_⟩, ⟨z2, hz2, hfinj ?_⟩⟩
  · rw [map_mul, map_mul, hz1e]; exact e1
  · rw [map_mul, map_mul, hz2e]; exact e2

@[expose] noncomputable def resK (ε : V →ₗ[F3] V) (K : Subgroup (V ≃ₗ[F3] V))
    (hcomm : ∀ h ∈ K, ∀ v, h (ε v) = ε (h v)) :
    K →* (LinearMap.range ε ≃ₗ[F3] LinearMap.range ε) where
  toFun h := hresEquiv ε h (hcomm h h.2)
  map_one' := LinearEquiv.ext fun w => Subtype.ext rfl
  map_mul' h h' := LinearEquiv.ext fun w => Subtype.ext rfl

theorem q8_pre_gen {G H : Type*} [Group G] [Group H] (f : G →* H) (I J : G) :
    ∀ w ∈ q8g (· * ·) (1 : H) (f I) (f J), ∃ y ∈ q8g (· * ·) (1 : G) I J, f y = w := by
  intro w hw
  simp only [q8g, List.mem_cons, List.not_mem_nil, or_false] at hw ⊢
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, Or.inl rfl, map_one f⟩
  · exact ⟨I, Or.inr (Or.inl rfl), rfl⟩
  · exact ⟨I * I, Or.inr (Or.inr (Or.inl rfl)), by rw [map_mul]⟩
  · exact ⟨I * I * I, Or.inr (Or.inr (Or.inr (Or.inl rfl))), by rw [map_mul, map_mul]⟩
  · exact ⟨J, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))), rfl⟩
  · exact ⟨I * J, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))), by rw [map_mul]⟩
  · exact ⟨I * I * J, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))), by
      rw [map_mul, map_mul]⟩
  · exact ⟨I * I * I * J, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))), by
      rw [map_mul, map_mul, map_mul]⟩

theorem q8g_coe_mem {K : Subgroup (V ≃ₗ[F3] V)} (I J : K) :
    ∀ w ∈ q8g (· * ·) (1 : K) I J, (w : V ≃ₗ[F3] V) ∈ q8 (I : V ≃ₗ[F3] V) (J : V ≃ₗ[F3] V) := by
  intro w hw
  simp only [q8g, List.mem_cons, List.not_mem_nil, or_false] at hw
  simp only [q8, List.mem_cons, List.not_mem_nil, or_false]
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))

theorem two_pow_of_mem {T : Subgroup (V ≃ₗ[F3] V)} (hT2 : IsPGroup 2 T) {x : V ≃ₗ[F3] V}
    (hx : x ∈ T) : ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
  obtain ⟨k, hk⟩ := hT2 ⟨x, hx⟩
  exact ⟨k, congrArg Subtype.val hk⟩

@[expose] def negE (V : Type*) [AddCommGroup V] [Module F3 V] : V ≃ₗ[F3] V := LinearEquiv.neg F3

theorem negE_apply (v : V) : negE V v = -v := rfl

theorem negE_comm (x : V ≃ₗ[F3] V) : negE V * x = x * negE V := by
  ext v
  show -(x v) = x (-v)
  rw [map_neg]

theorem negE_sq : negE V * negE V = 1 := by
  ext v
  show -(-v) = v
  rw [neg_neg]

theorem two_elt_mul {G : Type*} [Group G] {a b : G} (hab : Commute a b) {m n : ℕ}
    (ha : a ^ (2 ^ m) = 1) (hb : b ^ (2 ^ n) = 1) : (a * b) ^ (2 ^ (m + n)) = 1 := by
  have h1 : a ^ (2 ^ (m + n)) = 1 := by
    rw [pow_add, pow_mul, ha, one_pow]
  have h2 : b ^ (2 ^ (m + n)) = 1 := by
    rw [pow_add, pow_mul', hb, one_pow]
  rw [hab.mul_pow, h1, h2, one_mul]

theorem two_pow_neg_mul {T : Subgroup (V ≃ₗ[F3] V)} (hT2 : IsPGroup 2 T) {x : V ≃ₗ[F3] V}
    (hx : x ∈ T) : ∃ m : ℕ, (negE V * x) ^ (2 ^ m) = 1 := by
  obtain ⟨k, hk⟩ := two_pow_of_mem hT2 hx
  have h1 : (negE V) ^ (2 ^ 1) = 1 := by
    rw [pow_one, pow_two]
    exact negE_sq
  have := two_elt_mul (negE_comm x : Commute (negE V) x) h1 hk
  exact ⟨1 + k, this⟩

theorem eq_neg_of_neg_on_range (ε : V →ₗ[F3] V) (hk : ∀ v, ε v = 0 → v ∈ LinearMap.range ε)
    {T : Subgroup (V ≃ₗ[F3] V)} (hT2 : IsPGroup 2 T) {x : V ≃ₗ[F3] V} (hx : x ∈ T)
    (hxc : ∀ v, x (ε v) = ε (x v)) (hxW : ∀ w ∈ LinearMap.range ε, x w = -w) :
    ∀ v, x v = -v := by
  obtain ⟨m, hm⟩ := two_pow_neg_mul hT2 hx
  have h := eq_one_of_two_elt ε hk (negE V * x) (fun v => by
      show -(x (ε v)) = ε (-(x v))
      rw [hxc, map_neg]) (fun w hw => by
      show -(x w) = w
      rw [hxW w hw, neg_neg]) m hm
  intro v
  have h' : negE V (x v) = v := congrArg (fun f : V ≃ₗ[F3] V => f v) h
  rw [negE_apply] at h'
  exact neg_eq_iff_eq_neg.mp h'

theorem q8_mem_T {T : Subgroup (V ≃ₗ[F3] V)} {I J : V ≃ₗ[F3] V} (hI : I ∈ T) (hJ : J ∈ T) :
    ∀ y ∈ q8 I J, y ∈ T := by
  intro y hy
  simp only [q8, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact T.one_mem
  · exact hI
  · exact T.mul_mem hI hI
  · exact T.mul_mem (T.mul_mem hI hI) hI
  · exact hJ
  · exact T.mul_mem hI hJ
  · exact T.mul_mem (T.mul_mem hI hI) hJ
  · exact T.mul_mem (T.mul_mem (T.mul_mem hI hI) hI) hJ

theorem quat_rel (ε : V →ₗ[F3] V) (hk : ∀ v, ε v = 0 → v ∈ LinearMap.range ε)
    {T : Subgroup (V ≃ₗ[F3] V)} (hT2 : IsPGroup 2 T) (hTc : ∀ h ∈ T, ∀ v, h (ε v) = ε (h v))
    {I J : V ≃ₗ[F3] V} (hIT : I ∈ T) (hJT : J ∈ T)
    (hIW : ∀ w ∈ LinearMap.range ε, I (I w) = -w)
    (hJW : ∀ w ∈ LinearMap.range ε, J (J w) = -w)
    (hIJW : ∀ w ∈ LinearMap.range ε, I (J w) = -J (I w)) : QRelE I J := by
  have hWI : ∀ w ∈ LinearMap.range ε, I w ∈ LinearMap.range ε := by
    rintro _ ⟨x, rfl⟩
    exact ⟨I x, (hTc I hIT x).symm⟩
  have hII : ∀ v, I (I v) = -v :=
    eq_neg_of_neg_on_range ε hk hT2 (T.mul_mem hIT hIT) (hTc _ (T.mul_mem hIT hIT)) hIW
  have hJJ : ∀ v, J (J v) = -v :=
    eq_neg_of_neg_on_range ε hk hT2 (T.mul_mem hJT hJT) (hTc _ (T.mul_mem hJT hJT)) hJW
  have hIJIJ : ∀ v, I (J (I (J v))) = -v := by
    have hc : I * J * I * J ∈ T := T.mul_mem (T.mul_mem (T.mul_mem hIT hJT) hIT) hJT
    refine eq_neg_of_neg_on_range ε hk hT2 hc (hTc _ hc) (fun w hw => ?_)
    show I (J (I (J w))) = -w
    rw [hIJW w hw, map_neg, map_neg, hJW (I w) (hWI w hw), map_neg, neg_neg, hIW w hw]
  refine ⟨hII, hJJ, fun v => ?_⟩
  have h1 : J (I (J v)) = I v := by
    have := congrArg I (hIJIJ v)
    rw [hII, map_neg] at this
    exact neg_injective this
  have := congrArg J h1
  rw [hJJ] at this
  exact neg_eq_iff_eq_neg.mp this

theorem lift_step [Finite V] (hV : Nat.card V = 81) (ε : V →ₗ[F3] V) (hε : ∀ v, ε (ε v) = 0)
    (hk : ∀ v, ε v = 0 → v ∈ LinearMap.range ε) (K : Subgroup (V ≃ₗ[F3] V))
    (hcomm : ∀ h ∈ K, ∀ v, h (ε v) = ε (h v)) (u₁ : V ≃ₗ[F3] V)
    (hu₁ : ∀ v, u₁ v = v + ε v) (hu₁K : u₁ ∈ K)
    (htrans : ∀ w w' : V, w ∈ LinearMap.range ε → w' ∈ LinearMap.range ε → w ≠ 0 → w' ≠ 0 →
      ∃ h ∈ K, h w = w')
    (hord3 : ∃ s ∈ K, s ^ 3 = 1 ∧ ∃ w ∈ LinearMap.range ε, s w ≠ w)
    (hbound : ∀ X : Subgroup (V ≃ₗ[F3] V), X ≤ K → IsPGroup 3 X → u₁ ∈ X →
      (∀ x ∈ X, x * u₁ = u₁ * x) → Nat.card X ≤ 81)
    (T : Subgroup (V ≃ₗ[F3] V)) (hTK : T ≤ K) (hT2 : IsPGroup 2 T)
    (k x y : V ≃ₗ[F3] V) (hkK : k ∈ K) (hxT : x ∈ T) (hyT : y ∈ T)
    (h : ∀ w ∈ LinearMap.range ε, k (x w) = y (k w)) : k * x = y * k := by
  classical
  have hkk : ∀ w, k (k⁻¹ w) = w := fun w =>
    congrArg (fun f : V ≃ₗ[F3] V => f w) (mul_inv_cancel k)
  have hyy : ∀ w, y⁻¹ (y w) = w := fun w =>
    congrArg (fun f : V ≃ₗ[F3] V => f w) (inv_mul_cancel y)
  set z : V ≃ₗ[F3] V := y⁻¹ * (k * x * k⁻¹) with hz
  have hzK : z ∈ K := K.mul_mem (K.inv_mem (hTK hyT))
    (K.mul_mem (K.mul_mem hkK (hTK hxT)) (K.inv_mem hkK))
  have hWk : ∀ w ∈ LinearMap.range ε, k⁻¹ w ∈ LinearMap.range ε := by
    rintro _ ⟨v, rfl⟩
    exact ⟨k⁻¹ v, (hcomm k⁻¹ (K.inv_mem hkK) v).symm⟩
  have hzfix : ∀ w ∈ LinearMap.range ε, z w = w := by
    intro w hw
    have e : k (x (k⁻¹ w)) = y w := by
      have := h (k⁻¹ w) (hWk w hw)
      rwa [hkk] at this
    show y⁻¹ (k (x (k⁻¹ w))) = w
    rw [e, hyy]
  obtain ⟨c, hc⟩ := ker_form hV ε hε hk K hcomm u₁ hu₁ hu₁K htrans hord3 hbound z hzK hzfix
  have hzcomm : ∀ g ∈ K, ∀ v, g (z v) = z (g v) := by
    intro g hg v
    rw [hc, hc, map_add, map_smul, hcomm g hg]
  have hyz : y * z = z * y := by
    ext v
    exact hzcomm y (hTK hyT) v
  have hw : k * x * k⁻¹ = y * z := by
    rw [hz, mul_inv_cancel_left]
  have hcom : Commute y (k * x * k⁻¹) := by
    rw [hw]
    show y * (y * z) = y * z * y
    rw [mul_assoc, ← hyz]
  obtain ⟨m1, hm1⟩ := two_pow_of_mem hT2 hyT
  obtain ⟨m2, hm2⟩ := two_pow_of_mem hT2 hxT
  have hm1' : y⁻¹ ^ (2 ^ m1) = 1 := by rw [inv_pow, hm1, inv_one]
  have hm2' : (k * x * k⁻¹) ^ (2 ^ m2) = 1 := by rw [conj_pow, hm2, mul_one, mul_inv_cancel]
  have hz2 : z ^ (2 ^ (m1 + m2)) = 1 := two_elt_mul hcom.inv_left hm1' hm2'
  have hz1 : z = 1 := eq_one_of_two_elt ε hk z (hcomm z hzK) hzfix _ hz2
  have : k * x * k⁻¹ = y := by
    rw [hw, hz1, mul_one]
  exact mul_inv_eq_iff_eq_mul.mp this

theorem quat_line [Finite V] (hV : Nat.card V = 81) (ε : V →ₗ[F3] V) (hε : ∀ v, ε (ε v) = 0)
    (hk : ∀ v, ε v = 0 → v ∈ LinearMap.range ε) (K : Subgroup (V ≃ₗ[F3] V))
    (hcomm : ∀ h ∈ K, ∀ v, h (ε v) = ε (h v)) (u₁ : V ≃ₗ[F3] V)
    (hu₁ : ∀ v, u₁ v = v + ε v) (hu₁K : u₁ ∈ K)
    (htrans : ∀ w w' : V, w ∈ LinearMap.range ε → w' ∈ LinearMap.range ε → w ≠ 0 → w' ≠ 0 →
      ∃ h ∈ K, h w = w')
    (hord3 : ∃ s ∈ K, s ^ 3 = 1 ∧ ∃ w ∈ LinearMap.range ε, s w ≠ w)
    (hbound : ∀ X : Subgroup (V ≃ₗ[F3] V), X ≤ K → IsPGroup 3 X → u₁ ∈ X →
      (∀ x ∈ X, x * u₁ = u₁ * x) → Nat.card X ≤ 81)
    (T : Subgroup (V ≃ₗ[F3] V)) (hTK : T ≤ K) (hT2 : IsPGroup 2 T) (I J : V ≃ₗ[F3] V)
    (hIT : I ∈ T) (hJT : J ∈ T) (hIW : ∀ w ∈ LinearMap.range ε, I (I w) = -w)
    (hJW : ∀ w ∈ LinearMap.range ε, J (J w) = -w)
    (hIJW : ∀ w ∈ LinearMap.range ε, I (J w) = -J (I w)) :
    QRelE I J ∧ ∀ k ∈ K, (∃ y ∈ q8 I J, k * I = y * k) ∧ (∃ y ∈ q8 I J, k * J = y * k) := by
  classical
  refine ⟨quat_rel ε hk hT2 (fun h hh => hcomm h (hTK hh)) hIT hJT hIW hJW hIJW, ?_⟩
  intro k hkK
  have hW9 := card_range_eq_nine hV ε hε hk
  have hW2 := finrank_range_eq_two ε hW9
  set f := resK ε K hcomm with hf
  set IK : K := ⟨I, hTK hIT⟩ with hIK
  set JK : K := ⟨J, hTK hJT⟩ with hJK
  set kK : K := ⟨k, hkK⟩ with hkK'
  have hIr : ∀ w : LinearMap.range ε, f IK (f IK w) = -w := fun w =>
    Subtype.ext (hIW w w.2)
  have hJr : ∀ w : LinearMap.range ε, f JK (f JK w) = -w := fun w =>
    Subtype.ext (hJW w w.2)
  have hIJr : ∀ w : LinearMap.range ε, f IK (f JK w) = -f JK (f IK w) := fun w =>
    Subtype.ext (hIJW w w.2)
  obtain ⟨⟨yb₁, hyb₁, he₁⟩, ⟨yb₂, hyb₂, he₂⟩⟩ := norm_lem hW2 (f IK) (f JK) (f kK) hIr hJr hIJr
  obtain ⟨y₁, hy₁, hy₁e⟩ := q8_pre_gen f IK JK yb₁ hyb₁
  obtain ⟨y₂, hy₂, hy₂e⟩ := q8_pre_gen f IK JK yb₂ hyb₂
  have hy₁q := q8g_coe_mem IK JK y₁ hy₁
  have hy₂q := q8g_coe_mem IK JK y₂ hy₂
  have hy₁T := q8_mem_T hIT hJT _ hy₁q
  have hy₂T := q8_mem_T hIT hJT _ hy₂q
  refine ⟨⟨(y₁ : V ≃ₗ[F3] V), hy₁q, ?_⟩, ⟨(y₂ : V ≃ₗ[F3] V), hy₂q, ?_⟩⟩
  · refine lift_step hV ε hε hk K hcomm u₁ hu₁ hu₁K htrans hord3 hbound T hTK hT2 k I y₁ hkK hIT
      hy₁T (fun w hw => ?_)
    have := congrArg (fun g : LinearMap.range ε ≃ₗ[F3] LinearMap.range ε =>
      ((g ⟨w, hw⟩ : LinearMap.range ε) : V)) he₁
    rw [← hy₁e] at this
    exact this
  · refine lift_step hV ε hε hk K hcomm u₁ hu₁ hu₁K htrans hord3 hbound T hTK hT2 k J y₂ hkK hJT
      hy₂T (fun w hw => ?_)
    have := congrArg (fun g : LinearMap.range ε ≃ₗ[F3] LinearMap.range ε =>
      ((g ⟨w, hw⟩ : LinearMap.range ε) : V)) he₂
    rw [← hy₂e] at this
    exact this

end Quat

end CFSG.RankThree.PartTwo.Sec21.Hering2119S
