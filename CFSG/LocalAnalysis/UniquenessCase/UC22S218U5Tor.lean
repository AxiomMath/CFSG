module

public import CFSG.ClassicalGroups.UnitaryFlag.HyperbolicData
import CFSG.LocalAnalysis.UniquenessCase.UC22S218U5Cov
import CFSG.RankThree.CentralLiftU.UnitaryTorus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup Matrix CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.RankThree.CentralLiftU (tcoord coe_tcoord_of_diag hypSU_eq_of_diag)

private theorem u5t_dvd_sq (n : ℕ) : 2 ^ n + 1 ∣ 2 ^ (2 * n) - 1 := by
  have h : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have e : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [e]
  generalize 2 ^ n = x at h ⊢
  have h3 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ h
  refine Dvd.intro_left (x - 1) ?_
  zify [h, h3]
  ring

private theorem u5t_dvd25 {n : ℕ} (h5n : 5 ∣ n) (h5 : 5 ∣ 2 ^ n + 1) : 25 ∣ 2 ^ n + 1 := by
  have h1 : 2 ^ n % 25 = 2 ^ (n % 20) % 25 := by
    conv_lhs => rw [← Nat.mod_add_div n 20, pow_add, pow_mul]
    rw [Nat.mul_mod, Nat.pow_mod (2 ^ 20)]
    norm_num
  have h2 : n % 20 = 0 ∨ n % 20 = 5 ∨ n % 20 = 10 ∨ n % 20 = 15 := by omega
  rcases h2 with h2 | h2 | h2 | h2 <;> rw [h2] at h1 <;> norm_num at h1 <;> omega

section Torus

variable {n : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 n K)

private noncomputable def u5t_coord : ↥(hypTorus h 2 1) →* Kˣ × Kˣ :=
  (tcoord (r := 2) (ε := 1) h 0).prod (tcoord (r := 2) (ε := 1) h 1)

private theorem u5t_coord_eq {t : ↥(hypTorus h 2 1)} {a : Fin 2 → Kˣ} {d : Fin 1 → Kˣ}
    (hm : (((t : ↥(hypSU h 2 1)) : GL (HypIndex 2 1) K) :
      Matrix (HypIndex 2 1) (HypIndex 2 1) K) = diagonal (torusEntries h a d)) :
    u5t_coord h t = (a 0, a 1) :=
  Prod.ext (Units.ext (coe_tcoord_of_diag h 0 hm)) (Units.ext (coe_tcoord_of_diag h 1 hm))

private theorem u5t_torus_d {a : Fin 2 → Kˣ} {d : Fin 1 → Kˣ} (hp : torusRatio h a d = 1)
    (k : Fin 1) : (d k : K) = (∏ i, (a i : K) / h.bar (a i))⁻¹ := by
  rw [torusRatio] at hp
  have := eq_inv_of_mul_eq_one_right hp
  rw [Fin.prod_univ_one] at this
  rw [Fin.fin_one_eq_zero k]
  exact this

private theorem u5t_coord_injective : Function.Injective (u5t_coord h) := by
  intro t t' htt'
  obtain ⟨a, d, -, hp, hm⟩ := t.2
  obtain ⟨a', d', -, hp', hm'⟩ := t'.2
  rw [u5t_coord_eq h hm, u5t_coord_eq h hm'] at htt'
  have haa : a = a' := by
    funext i
    fin_cases i
    · exact (Prod.mk.inj htt').1
    · exact (Prod.mk.inj htt').2
  refine Subtype.ext (hypSU_eq_of_diag h hm hm' (fun x => ?_) (fun k => ?_))
  · simp only [torusEntries, haa]
  · simp only [torusEntries]
    rw [u5t_torus_d h hp k, u5t_torus_d h hp' k, haa]

private theorem u5t_coord_surjective : Function.Surjective (u5t_coord h) := by
  rintro ⟨u, v⟩
  have hbb : ∀ x : K, h.bar (h.bar x) = x := h.bar_bar
  have hu : (u : K) ≠ 0 := u.ne_zero
  have hv : (v : K) ≠ 0 := v.ne_zero
  have hu' : h.bar (u : K) ≠ 0 := by simp [hu]
  have hv' : h.bar (v : K) ≠ 0 := by simp [hv]
  let a : Fin 2 → Kˣ := ![u, v]
  let d : Fin 1 → Kˣ := fun _ => Units.map (h.bar : K →* K) (u * v) * (u * v)⁻¹
  have hd : ∀ k, h.norm (d k : K) = 1 := by
    intro k
    simp only [d, UnitaryFieldData.norm, Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass,
      Units.val_inv_eq_inv_val, map_mul, map_inv₀, hbb]
    field_simp
  have hp : torusRatio h a d = 1 := by
    rw [torusRatio, Fin.prod_univ_two, Fin.prod_univ_one]
    simp only [a, d, Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_mul, Units.coe_map,
      MonoidHom.coe_ofClass, Units.val_inv_eq_inv_val, map_mul]
    field_simp
  obtain ⟨g, hg, hm⟩ := torusMat_mem_hypSU h a hd hp
  refine ⟨⟨g, hg⟩, ?_⟩
  rw [u5t_coord_eq h hm]
  rfl

private noncomputable def u5t_torusEquiv : ↥(hypTorus h 2 1) ≃* Kˣ × Kˣ :=
  MulEquiv.ofBijective (u5t_coord h) ⟨u5t_coord_injective h, u5t_coord_surjective h⟩

private noncomputable def u5t_tau : Kˣ × Kˣ →* hypSU h 2 1 :=
  (hypTorus h 2 1).subtype.comp (u5t_torusEquiv h).symm.toMonoidHom

private theorem u5t_tau_injective : Function.Injective (u5t_tau h) :=
  Subtype.val_injective.comp (u5t_torusEquiv h).symm.injective

private theorem u5t_tau_entries (x : Kˣ × Kˣ) :
    ∃ (a : Fin 2 → Kˣ) (d : Fin 1 → Kˣ), a 0 = x.1 ∧ a 1 = x.2 ∧
      (∀ k, (d k : K) = (∏ i, (a i : K) / h.bar (a i))⁻¹) ∧
      (((u5t_tau h x : ↥(hypSU h 2 1)) : GL (HypIndex 2 1) K) :
        Matrix (HypIndex 2 1) (HypIndex 2 1) K) = diagonal (torusEntries h a d) := by
  set t := (u5t_torusEquiv h).symm x with ht
  obtain ⟨a, d, -, hp, hm⟩ := t.2
  have hco : u5t_coord h t = (a 0, a 1) := u5t_coord_eq h hm
  have hx : u5t_coord h t = x := (u5t_torusEquiv h).apply_symm_apply x
  refine ⟨a, d, ?_, ?_, fun k => u5t_torus_d h hp k, hm⟩
  · rw [← hx, hco]
  · rw [← hx, hco]

private theorem u5t_tau_mem_scalars {x : Kˣ × Kˣ} (hx : u5t_tau h x ∈ hypScalars h 2 1) :
    x.1 = x.2 ∧ x.1 ^ 5 = 1 := by
  obtain ⟨c, -, hc5, hmat⟩ := hx
  obtain ⟨a, d, ha0, ha1, -, hm⟩ := u5t_tau_entries h x
  have hM := congrArg (fun g : GL (HypIndex 2 1) K =>
    (g : Matrix (HypIndex 2 1) (HypIndex 2 1) K)) hmat
  simp only [hm, GeneralLinearGroup.coe_scalar] at hM
  have e0 : a 0 = c := Units.ext (by
    simpa [torusEntries, Matrix.scalar_apply] using congrFun (congrFun hM (.inl 0)) (.inl 0))
  have e1 : a 1 = c := Units.ext (by
    simpa [torusEntries, Matrix.scalar_apply] using congrFun (congrFun hM (.inl 1)) (.inl 1))
  refine ⟨ha0.symm.trans (e0.trans (e1.symm.trans ha1)), ?_⟩
  rw [← ha0, e0]
  exact hc5

private theorem u5t_tau_diag_mem_scalars {c : Kˣ} (hc5 : c ^ 5 = 1) (h5 : 5 ∣ 2 ^ n + 1) :
    u5t_tau h (c, c) ∈ hypScalars h 2 1 := by
  obtain ⟨a, d, ha0, ha1, hd, hm⟩ := u5t_tau_entries h (c, c)
  have hu : (c : K) ^ 5 = 1 := by simpa using congrArg Units.val hc5
  have hbar : h.bar (c : K) * c = 1 := by
    have h1 : (c : K) ^ (2 ^ n + 1) = 1 := by
      obtain ⟨m, hm'⟩ := h5
      rw [hm', pow_mul, hu, one_pow]
    rw [UnitaryFieldData.bar_apply, ← pow_succ]
    exact h1
  have hb : h.bar (c : K) = (c : K)⁻¹ := eq_inv_of_mul_eq_one_left hbar
  have ha0' : (a 0 : K) = c := congrArg Units.val ha0
  have ha1' : (a 1 : K) = c := congrArg Units.val ha1
  have hent : torusEntries h a d = fun _ => (c : K) := by
    funext y
    rcases y with i | k | i
    · fin_cases i
      · exact ha0'
      · exact ha1'
    · have hk := hd k
      rw [Fin.prod_univ_two, ha0', ha1', hb] at hk
      show (d k : K) = c
      rw [hk]
      apply inv_eq_of_mul_eq_one_right
      rw [div_inv_eq_mul]
      calc (c : K) * c * ((c : K) * c) * c = (c : K) ^ 5 := by ring
        _ = 1 := hu
    · fin_cases i
      · show (h.bar (a 0))⁻¹ = c
        rw [ha0', hb, inv_inv]
      · show (h.bar (a 1))⁻¹ = c
        rw [ha1', hb, inv_inv]
  refine ⟨c, ?_, hc5, ?_⟩
  · rw [UnitaryFieldData.norm, mul_comm]
    exact hbar
  · apply Units.ext
    rw [hm, hent, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]

private theorem u5t_exists_orderOf [Finite K] {d : ℕ} (hd : d ∣ Nat.card Kˣ) :
    ∃ t : Kˣ, orderOf t = d := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hg' : orderOf g = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers hg
  obtain ⟨m, hm⟩ := hd
  have hm0 : m ≠ 0 := by
    rintro rfl
    have : 0 < Nat.card Kˣ := Nat.card_pos
    omega
  refine ⟨g ^ m, ?_⟩
  rw [orderOf_pow_of_dvd hm0 (by rw [hg', hm]; exact Dvd.intro_left _ rfl), hg', hm,
    Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]

end Torus

private theorem u5t_pair {X : Type} [Group X] {ℓ : ℕ} (hℓ : ℓ.Prime) {u₁ u₂ : X}
    (hc : Commute u₁ u₂) (h₁ : u₁ ^ ℓ = 1) (h₂ : u₂ ^ ℓ = 1) (hn₁ : u₁ ≠ 1) (hn₂ : u₂ ≠ 1)
    (hind : ∀ i j : ℤ, u₁ ^ i * u₂ ^ j = 1 → u₁ ^ i = 1 ∧ u₂ ^ j = 1) :
    IsElemAbelian ℓ (zpowers u₁ ⊔ zpowers u₂) ∧ Nat.card ↥(zpowers u₁ ⊔ zpowers u₂) = ℓ ^ 2 := by
  have ho₁ : orderOf u₁ = ℓ :=
    ((Nat.dvd_prime hℓ).1 (orderOf_dvd_of_pow_eq_one h₁)).resolve_left fun h =>
      hn₁ (orderOf_eq_one_iff.1 h)
  have ho₂ : orderOf u₂ = ℓ :=
    ((Nat.dvd_prime hℓ).1 (orderOf_dvd_of_pow_eq_one h₂)).resolve_left fun h =>
      hn₂ (orderOf_eq_one_iff.1 h)
  have hcomm : ∀ (a b : X), a ∈ zpowers u₁ → b ∈ zpowers u₂ → Commute a b := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact hc.zpow_zpow i j
  let g : ↥(zpowers u₁) × ↥(zpowers u₂) →* X :=
    (zpowers u₁).subtype.noncommCoprod (zpowers u₂).subtype fun a b => hcomm a b a.2 b.2
  have hg : ∀ p, g p = (p.1 : X) * p.2 := fun p => rfl
  have hrange : g.range = zpowers u₁ ⊔ zpowers u₂ := by
    have := MonoidHom.noncommCoprod_range (zpowers u₁).subtype (zpowers u₂).subtype
      fun a b => hcomm a b a.2 b.2
    rwa [Subgroup.range_subtype, Subgroup.range_subtype] at this
  have hinj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ h1
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    obtain ⟨e1, e2⟩ := hind i j h1
    exact Prod.ext (Subtype.ext e1) (Subtype.ext e2)
  have hc₁ : Nat.card ↥(zpowers u₁) = ℓ := by rw [Nat.card_zpowers, ho₁]
  have hc₂ : Nat.card ↥(zpowers u₂) = ℓ := by rw [Nat.card_zpowers, ho₂]
  have hp₁ : ∀ a : ↥(zpowers u₁), a ^ ℓ = 1 := fun a => by
    rw [← hc₁]
    exact pow_card_eq_one'
  have hp₂ : ∀ a : ↥(zpowers u₂), a ^ ℓ = 1 := fun a => by
    rw [← hc₂]
    exact pow_card_eq_one'
  have hel : IsElemAbelian ℓ g.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨p, hp⟩ := x.2
      obtain ⟨q, hq⟩ := y.2
      apply Subtype.ext
      change (x : X) * y = y * x
      rw [← hp, ← hq, ← map_mul, ← map_mul]
      congr 1
      exact Prod.ext (mul_comm' p.1 q.1) (mul_comm' p.2 q.2)
    · obtain ⟨p, rfl⟩ := hx
      rw [← map_pow]
      have : p ^ ℓ = 1 := Prod.ext (hp₁ p.1) (hp₂ p.2)
      rw [this, map_one]
  rw [hrange] at hel
  refine ⟨hel, ?_⟩
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod, hc₁, hc₂,
    sq]

private theorem u5t_range_comm {A X : Type} [CommGroup A] [Group X] (ψ : A →* X) {x y : X}
    (hx : x ∈ ψ.range) (hy : y ∈ ψ.range) : x * y = y * x := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  rw [← map_mul, ← map_mul, mul_comm a b]

private theorem u5t_sup_le_range {A X : Type} [Group A] [Group X] (ψ : A →* X) (a b : A) :
    zpowers (ψ a) ⊔ zpowers (ψ b) ≤ ψ.range :=
  sup_le (Subgroup.zpowers_le.2 ⟨a, rfl⟩) (Subgroup.zpowers_le.2 ⟨b, rfl⟩)

section Pairs

variable {n : ℕ} {K : Type} [Field K] {X : Type} [Group X]

private theorem u5t_torus_pair {ℓ : ℕ} (hℓ : ℓ.Prime) (ψ : Kˣ × Kˣ →* X) {ζ : Kˣ}
    (hζ : orderOf ζ = ℓ) (hψ : ∀ i j : ℤ, ψ (ζ ^ i, ζ ^ j) = 1 → ζ ^ i = 1 ∧ ζ ^ j = 1) :
    IsElemAbelian ℓ (zpowers (ψ (ζ, 1)) ⊔ zpowers (ψ (1, ζ))) ∧
      Nat.card ↥(zpowers (ψ (ζ, 1)) ⊔ zpowers (ψ (1, ζ))) = ℓ ^ 2 := by
  have hζℓ : ζ ^ ℓ = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  have hn : ζ ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hζ
    exact hℓ.one_lt.ne hζ
  have hz1 : ∀ i : ℤ, ψ (ζ, 1) ^ i = ψ (ζ ^ i, 1) := fun i => by
    rw [← map_zpow]
    congr 1
    exact Prod.ext (by simp) (by simp)
  have hz2 : ∀ j : ℤ, ψ (1, ζ) ^ j = ψ (1, ζ ^ j) := fun j => by
    rw [← map_zpow]
    congr 1
    exact Prod.ext (by simp) (by simp)
  refine u5t_pair hℓ ((Commute.all ((ζ, 1) : Kˣ × Kˣ) (1, ζ)).map ψ) ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow]
    have : ((ζ, 1) : Kˣ × Kˣ) ^ ℓ = 1 := Prod.ext hζℓ (one_pow ℓ)
    rw [this, map_one]
  · rw [← map_pow]
    have : ((1, ζ) : Kˣ × Kˣ) ^ ℓ = 1 := Prod.ext (one_pow ℓ) hζℓ
    rw [this, map_one]
  · intro h1
    have := (hψ 1 0 (by simpa using h1)).1
    exact hn (by simpa using this)
  · intro h1
    have := (hψ 0 1 (by simpa using h1)).2
    exact hn (by simpa using this)
  · intro i j hij
    have h2 : ψ (ζ ^ i, ζ ^ j) = ψ (ζ, 1) ^ i * ψ (1, ζ) ^ j := by
      rw [hz1, hz2, ← map_mul]
      congr 1
      exact Prod.ext (by simp) (by simp)
    obtain ⟨e1, e2⟩ := hψ i j (h2.trans hij)
    refine ⟨?_, ?_⟩
    · rw [hz1, e1]
      exact map_one ψ ▸ rfl
    · rw [hz2, e2]
      exact map_one ψ ▸ rfl

private theorem u5t_E0 (ψ : Kˣ × Kˣ →* X) (hψ : ∀ x, ψ x = 1 → x.1 = x.2 ∧ x.1 ^ 5 = 1)
    {r : ℕ} (hr : r.Prime) (hr5 : r ≠ 5) {ζ : Kˣ} (hζ : orderOf ζ = r) :
    IsElemAbelian r (zpowers (ψ (ζ, 1)) ⊔ zpowers (ψ (1, ζ))) ∧
      Nat.card ↥(zpowers (ψ (ζ, 1)) ⊔ zpowers (ψ (1, ζ))) = r ^ 2 := by
  have hζr : ζ ^ r = 1 := by rw [← hζ]; exact pow_orderOf_eq_one ζ
  refine u5t_torus_pair hr ψ hζ fun i j hij => ?_
  obtain ⟨e1, e2⟩ := hψ _ hij
  have e1' : ζ ^ i = ζ ^ j := e1
  have hr' : (ζ ^ i) ^ r = 1 := by
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hζr,
      _root_.one_zpow]
  have hd : orderOf (ζ ^ i) ∣ Nat.gcd 5 r :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one e2) (orderOf_dvd_of_pow_eq_one hr')
  rw [((Nat.coprime_primes (by norm_num) hr).2 (Ne.symm hr5)).gcd_eq_one] at hd
  have h1 : ζ ^ i = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
  exact ⟨h1, e1'.symm.trans h1⟩

variable (h : UnitaryFieldData 2 n K) (α : hypSU h 2 1 →* X)

private theorem u5t_ker (hαc : ∀ s, α s ∈ Subgroup.center X ↔ s ∈ hypScalars h 2 1)
    (x : Kˣ × Kˣ) (hx : (α.comp (u5t_tau h)) x = 1) : x.1 = x.2 ∧ x.1 ^ 5 = 1 :=
  u5t_tau_mem_scalars h ((hαc _).1 (by rw [show α (u5t_tau h x) = 1 from hx]; exact one_mem _))

theorem uc22s218_u5_cover_pair_data (hαc : ∀ s, α s ∈ Subgroup.center X ↔ s ∈ hypScalars h 2 1)
    (h5 : 5 ∣ 2 ^ n + 1) {r : ℕ} (hr : r.Prime) (hr5 : r ≠ 5) (hrn : r ∣ 2 ^ n - 1) :
    ∃ (E₀ : Subgroup X) (y : X), IsElemAbelian r E₀ ∧ Nat.card E₀ = r ^ 2 ∧ orderOf y = 5 ∧
      (∀ e ∈ E₀, y * e = e * y) ∧ ∃ w : X, w * y ≠ y * w := by
  have := h.finite
  let ψ : Kˣ × Kˣ →* X := α.comp (u5t_tau h)
  have hψ := u5t_ker h α hαc
  have hcard : Nat.card Kˣ = 2 ^ (2 * n) - 1 := by rw [Nat.card_units, h.card]
  obtain ⟨ζr, hζr⟩ := u5t_exists_orderOf (K := K) (d := r) (by
    rw [hcard]
    exact hrn.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (Dvd.intro_left 2 rfl)))
  obtain ⟨ζ5, hζ5⟩ := u5t_exists_orderOf (K := K) (d := 5) (by
    rw [hcard]
    exact h5.trans (u5t_dvd_sq n))
  obtain ⟨hE, hEc⟩ := u5t_E0 ψ hψ hr hr5 hζr
  have hy5 : ψ (ζ5, 1) ^ 5 = 1 := by
    rw [← map_pow]
    have : ((ζ5, 1) : Kˣ × Kˣ) ^ 5 = 1 := Prod.ext (by rw [← hζ5]; exact pow_orderOf_eq_one ζ5)
      (one_pow 5)
    rw [this, map_one]
  have hyne : ψ (ζ5, 1) ≠ 1 := fun h1 => by
    have := (hψ _ h1).1
    rw [show ζ5 = 1 from this, orderOf_one] at hζ5
    omega
  refine ⟨_, ψ (ζ5, 1), hE, hEc, ?_, fun e he => ?_, ?_⟩
  · exact ((Nat.dvd_prime (by norm_num)).1 (orderOf_dvd_of_pow_eq_one hy5)).resolve_left
      fun h1 => hyne (orderOf_eq_one_iff.1 h1)
  · exact u5t_range_comm ψ ⟨_, rfl⟩ (u5t_sup_le_range ψ _ _ he)
  · by_contra hcon
    have hmem : ψ (ζ5, 1) ∈ Subgroup.center X :=
      Subgroup.mem_center_iff.2 fun w => by_contra fun hw => hcon ⟨w, hw⟩
    have h1 := (u5t_tau_mem_scalars h ((hαc _).1 hmem)).1
    rw [show ζ5 = 1 from h1, orderOf_one] at hζ5
    omega

theorem uc22s218_u5_cover_commuting_pair
    (hαc : ∀ s, α s ∈ Subgroup.center X ↔ s ∈ hypScalars h 2 1) (h5 : 5 ∣ 2 ^ n + 1)
    (hcase : Function.Injective α ∨ 5 ∣ n) {r : ℕ} (hr : r.Prime) (hr5 : r ≠ 5)
    (hrn : r ∣ 2 ^ n - 1) :
    ∃ E₀ Q₀ : Subgroup X, IsElemAbelian r E₀ ∧ Nat.card E₀ = r ^ 2 ∧ IsElemAbelian 5 Q₀ ∧
      Nat.card Q₀ = 5 ^ 2 ∧ ∀ x ∈ Q₀, ∀ e ∈ E₀, x * e = e * x := by
  have := h.finite
  let ψ : Kˣ × Kˣ →* X := α.comp (u5t_tau h)
  have hψ := u5t_ker h α hαc
  have hcard : Nat.card Kˣ = 2 ^ (2 * n) - 1 := by rw [Nat.card_units, h.card]
  obtain ⟨ζr, hζr⟩ := u5t_exists_orderOf (K := K) (d := r) (by
    rw [hcard]
    exact hrn.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 (Dvd.intro_left 2 rfl)))
  obtain ⟨hE, hEc⟩ := u5t_E0 ψ hψ hr hr5 hζr
  obtain ⟨Q, hQle, hQ, hQc⟩ : ∃ Q : Subgroup X, Q ≤ ψ.range ∧ IsElemAbelian 5 Q ∧
      Nat.card Q = 5 ^ 2 := by
    by_cases hinj : Function.Injective α
    · obtain ⟨ζ5, hζ5⟩ := u5t_exists_orderOf (K := K) (d := 5) (by
        rw [hcard]
        exact h5.trans (u5t_dvd_sq n))
      have hψinj : Function.Injective ψ := hinj.comp (u5t_tau_injective h)
      obtain ⟨hQ, hQc⟩ := u5t_torus_pair (by norm_num) ψ hζ5 fun i j hij => by
        have h1 := hψinj (hij.trans (map_one ψ).symm)
        exact ⟨congrArg Prod.fst h1, congrArg Prod.snd h1⟩
      exact ⟨_, u5t_sup_le_range ψ _ _, hQ, hQc⟩
    · have h25 : 25 ∣ 2 ^ n + 1 := u5t_dvd25 (hcase.resolve_left hinj) h5
      obtain ⟨ξ, hξ⟩ := u5t_exists_orderOf (K := K) (d := 25) (by
        rw [hcard]
        exact h25.trans (u5t_dvd_sq n))
      have hle := uc22s218_u5_scalars_le_ker h α hαc h5 hinj
      have hξ25 : ξ ^ 25 = 1 := by rw [← hξ]; exact pow_orderOf_eq_one ξ
      have hξ5 : (ξ ^ 5) ^ 5 = 1 := by rw [← pow_mul]; exact hξ25
      have hζo : orderOf (ξ ^ 5) = 5 := by
        rw [orderOf_pow_of_dvd (by norm_num) (by rw [hξ]; norm_num), hξ]
      have hψ55 : ψ (ξ ^ 5, ξ ^ 5) = 1 :=
        MonoidHom.mem_ker.1 (hle (u5t_tau_diag_mem_scalars h hξ5 h5))
      have hu₁ : ψ (ξ ^ 5, 1) ^ 5 = 1 := by
        rw [← map_pow]
        have : ((ξ ^ 5, 1) : Kˣ × Kˣ) ^ 5 = 1 := Prod.ext hξ5 (one_pow 5)
        rw [this, map_one]
      have hu₂ : ψ (ξ, ξ) ^ 5 = 1 := by
        rw [← map_pow]
        have : ((ξ, ξ) : Kˣ × Kˣ) ^ 5 = (ξ ^ 5, ξ ^ 5) := Prod.ext (by simp) (by simp)
        rw [this]
        exact hψ55
      have hn₁ : ψ (ξ ^ 5, 1) ≠ 1 := fun h1 => by
        have := (hψ _ h1).1
        rw [show ξ ^ 5 = 1 from this, orderOf_one] at hζo
        omega
      have hn₂ : ψ (ξ, ξ) ≠ 1 := fun h1 => by
        have := (hψ _ h1).2
        have h3 : orderOf ξ ∣ 5 := orderOf_dvd_of_pow_eq_one this
        rw [hξ] at h3
        omega
      obtain ⟨hQ, hQc⟩ := u5t_pair (by norm_num)
        ((Commute.all ((ξ ^ 5, 1) : Kˣ × Kˣ) (ξ, ξ)).map ψ) hu₁ hu₂ hn₁ hn₂ (fun i j hij => by
          have h2 : ψ (ξ ^ 5, 1) ^ i * ψ (ξ, ξ) ^ j = ψ ((ξ ^ 5) ^ i * ξ ^ j, ξ ^ j) := by
            rw [← map_zpow, ← map_zpow, ← map_mul]
            congr 1
            exact Prod.ext (by simp) (by simp)
          have h3 := (hψ _ (h2.symm.trans hij)).1
          have h4 : (ξ ^ 5) ^ i = 1 := by simpa using h3
          have h5' : ψ (ξ ^ 5, 1) ^ i = 1 := by
            rw [← map_zpow]
            have : ((ξ ^ 5, 1) : Kˣ × Kˣ) ^ i = 1 := Prod.ext h4 (_root_.one_zpow i)
            rw [this, map_one]
          exact ⟨h5', by rwa [h5', one_mul] at hij⟩)
      exact ⟨_, u5t_sup_le_range ψ _ _, hQ, hQc⟩
  exact ⟨_, Q, hE, hEc, hQ, hQc, fun x hx e he =>
    u5t_range_comm ψ (hQle hx) (u5t_sup_le_range ψ _ _ he)⟩

end Pairs

end CFSG.LocalAnalysis.UniquenessCase.UC22
