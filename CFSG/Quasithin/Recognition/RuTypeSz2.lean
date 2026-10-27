module

public import CFSG.Quasithin.EmptyFaithful.S1422Sz

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin Subgroup


@[expose] noncomputable def ruZpowersEquiv {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {x : G} {y : H} (h : orderOf x = orderOf y) : zpowers x ≃ zpowers y :=
  (finEquivZPowers (isOfFinOrder_of_finite x)).symm.trans
    ((finCongr h).trans (finEquivZPowers (isOfFinOrder_of_finite y)))

theorem ruZpowersEquiv_apply {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {x : G} {y : H} (h : orderOf x = orderOf y) (n : ℕ) :
    ruZpowersEquiv h ⟨x ^ n, n, zpow_natCast x n⟩ = ⟨y ^ n, n, zpow_natCast y n⟩ := by
  rw [ruZpowersEquiv, Equiv.trans_apply, Equiv.trans_apply, finEquivZPowers_symm_apply,
    ← Equiv.eq_symm_apply, finEquivZPowers_symm_apply]
  simp [h]

theorem ruZpowersEquiv_mul {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {x : G} {y : H} (h : orderOf x = orderOf y) (a b : zpowers x) :
    ruZpowersEquiv h (a * b) = ruZpowersEquiv h a * ruZpowersEquiv h b := by
  obtain ⟨a, ha⟩ := a
  obtain ⟨b, hb⟩ := b
  obtain ⟨n, rfl⟩ := mem_powers_iff_mem_zpowers.mpr ha
  obtain ⟨m, rfl⟩ := mem_powers_iff_mem_zpowers.mpr hb
  have e : (⟨x ^ n, ha⟩ : zpowers x) * ⟨x ^ m, hb⟩ =
      ⟨x ^ (n + m), ((n + m : ℕ) : ℤ), zpow_natCast x (n + m)⟩ := Subtype.ext (pow_add x n m).symm
  have e1 : (⟨x ^ n, ha⟩ : zpowers x) = ⟨x ^ n, (n : ℤ), zpow_natCast x n⟩ := rfl
  have e2 : (⟨x ^ m, hb⟩ : zpowers x) = ⟨x ^ m, (m : ℤ), zpow_natCast x m⟩ := rfl
  rw [e, e1, e2, ruZpowersEquiv_apply, ruZpowersEquiv_apply, ruZpowersEquiv_apply]
  exact Subtype.ext (pow_add y n m)

@[expose] noncomputable def ruZpowersMulEquiv {G H : Type*} [Group G] [Group H] [Finite G]
    [Finite H] {x : G} {y : H} (h : orderOf x = orderOf y) : zpowers x ≃* zpowers y :=
  MulEquiv.mk' (ruZpowersEquiv h) (ruZpowersEquiv_mul h)

theorem coe_ruZpowersMulEquiv_pow {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    {x : G} {y : H} (h : orderOf x = orderOf y) (n : ℕ) (hn : x ^ n ∈ zpowers x) :
    ((ruZpowersMulEquiv h ⟨x ^ n, hn⟩ : zpowers y) : H) = y ^ n := by
  have e : (⟨x ^ n, hn⟩ : zpowers x) = ⟨x ^ n, (n : ℤ), zpow_natCast x n⟩ := rfl
  show ((ruZpowersEquiv h ⟨x ^ n, hn⟩ : zpowers y) : H) = y ^ n
  rw [e, ruZpowersEquiv_apply]

theorem metaConj_pow_pow {X : Type*} [Group X] {u w : X} {k : ℕ} (hw : w * u * w⁻¹ = u ^ k) :
    ∀ j i : ℕ, w ^ j * u ^ i * (w ^ j)⁻¹ = u ^ (i * k ^ j) := by
  intro j
  induction j with
  | zero => intro i; simp
  | succ j ih =>
    intro i
    have e : w ^ (j + 1) * u ^ i * (w ^ (j + 1))⁻¹ = w * (w ^ j * u ^ i * (w ^ j)⁻¹) * w⁻¹ := by
      rw [pow_succ']
      group
    rw [e, ih, ← conj_pow, hw, ← pow_mul]
    congr 1
    ring

theorem frob20_key : ∀ n < 21, n ∣ 20 → 2 ^ n % 5 = 1 → n = 4 ∨ n = 20 := by decide

theorem frob20_orderOf_w {X : Type*} [Group X] [Finite X] (hX : Nat.card X = 20) {u w : X}
    (hu : orderOf u = 5) (hw : w * u * w⁻¹ = u ^ 2) : orderOf w = 4 := by
  have hdvd : orderOf w ∣ 20 := hX ▸ orderOf_dvd_natCard w
  have hc := metaConj_pow_pow hw (orderOf w) 1
  rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one, pow_one, one_mul] at hc
  have hpos : 1 ≤ 2 ^ orderOf w := Nat.one_le_two_pow
  have h5 : 2 ^ orderOf w % 5 = 1 := by
    have h1 : u ^ (2 ^ orderOf w - 1) = 1 := by
      have h2 := hc.symm
      rw [← Nat.sub_add_cancel hpos, pow_succ] at h2
      exact mul_eq_right.mp h2
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hu] at this
    omega
  rcases frob20_key _ (by have := Nat.le_of_dvd (by norm_num) hdvd; omega) hdvd h5 with h | h
  · exact h
  · exfalso
    have htop : zpowers w = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, h, hX]
    have hu' : u ∈ zpowers w := htop ▸ Subgroup.mem_top u
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu'
    have hcomm : w * w ^ k * w⁻¹ = w ^ k := by group
    rw [hcomm, pow_two] at hw
    have h1 : w ^ k = 1 := left_eq_mul.mp hw
    rw [h1, orderOf_one] at hu
    norm_num at hu

theorem meta_mem_normalizer {G : Type*} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (h : ∀ x ∈ H, g * x * g⁻¹ ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx
  have heq : H.map (MulAut.conj g).toMonoidHom = H :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact h x
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      simpa using h1
    rw [← this]
    exact hy

theorem meta_isComplement {X : Type*} [Group X] [Finite X] {m n : ℕ} (hmn : Nat.Coprime m n)
    {u w : X} (hu : orderOf u = m) (hw : orderOf w = n) (hX : Nat.card X = m * n) :
    (zpowers u).IsComplement' (zpowers w) := by
  apply Subgroup.isComplement'_of_card_mul_and_disjoint
  · rw [Nat.card_zpowers, Nat.card_zpowers, hu, hw, hX]
  · rw [Subgroup.disjoint_def]
    intro x hx1 hx2
    have h1 := Subgroup.orderOf_dvd_natCard _ hx1
    have h2 := Subgroup.orderOf_dvd_natCard _ hx2
    rw [Nat.card_zpowers, hu] at h1
    rw [Nat.card_zpowers, hw] at h2
    have := Nat.dvd_gcd h1 h2
    rw [hmn, Nat.dvd_one, orderOf_eq_one_iff] at this
    exact this

theorem meta_normal {X : Type*} [Group X] [Finite X] {m n k : ℕ} (hmn : Nat.Coprime m n)
    {u w : X} (hu : orderOf u = m) (hw : orderOf w = n) (hX : Nat.card X = m * n)
    (hr : w * u * w⁻¹ = u ^ k) : (zpowers u).Normal := by
  have hc := meta_isComplement hmn hu hw hX
  have hK : zpowers w ≤ Subgroup.normalizer (zpowers u : Set X) := by
    rw [Subgroup.zpowers_le]
    refine meta_mem_normalizer fun x hx => ?_
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    rw [← conj_zpow, hr]
    exact zpow_mem (pow_mem (Subgroup.mem_zpowers u) k) j
  have htop : Subgroup.normalizer (zpowers u : Set X) = ⊤ := by
    rw [eq_top_iff, ← hc.sup_eq_top]
    exact sup_le Subgroup.le_normalizer hK
  exact Subgroup.normalizer_eq_top_iff.mp htop

theorem nonempty_mulEquiv_of_meta {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    {m n k : ℕ} (hmn : Nat.Coprime m n) {u w : X} (hu : orderOf u = m) (hw : orderOf w = n)
    (hX : Nat.card X = m * n) (hr : w * u * w⁻¹ = u ^ k) {u' w' : Y} (hu' : orderOf u' = m)
    (hw' : orderOf w' = n) (hY : Nat.card Y = m * n) (hr' : w' * u' * w'⁻¹ = u' ^ k) :
    Nonempty (X ≃* Y) := by
  have := meta_normal hmn hu hw hX hr
  have := meta_normal hmn hu' hw' hY hr'
  refine ⟨((SemidirectProduct.mulEquivSubgroup (meta_isComplement hmn hu hw hX)).symm.trans
    (SemidirectProduct.congr (ruZpowersMulEquiv (hu.trans hu'.symm))
      (ruZpowersMulEquiv (hw.trans hw'.symm)) ?_)).trans
    (SemidirectProduct.mulEquivSubgroup (meta_isComplement hmn hu' hw' hY))⟩
  intro g
  ext p
  obtain ⟨g, hg⟩ := g
  obtain ⟨p, hp⟩ := p
  obtain ⟨j, rfl⟩ := mem_powers_iff_mem_zpowers.mpr hg
  obtain ⟨i, rfl⟩ := mem_powers_iff_mem_zpowers.mpr hp
  simp only [MulEquiv.trans_apply, MonoidHom.coe_comp, Function.comp_apply]
  have e : (zpowers u).normalizerMonoidHom (inclusion (Subgroup.normalizer_eq_top (H := zpowers u) ▸
      le_top) ⟨w ^ j, hg⟩) ⟨u ^ i, hp⟩ = ⟨u ^ (i * k ^ j), pow_mem (mem_zpowers u) _⟩ :=
    Subtype.ext (by
      show w ^ j * u ^ i * (w ^ j)⁻¹ = u ^ (i * k ^ j)
      exact metaConj_pow_pow hr j i)
  rw [e, coe_ruZpowersMulEquiv_pow]
  show u' ^ (i * k ^ j) =
    ((ruZpowersMulEquiv (hw.trans hw'.symm) ⟨w ^ j, hg⟩ : zpowers w') : Y) *
      ((ruZpowersMulEquiv (hu.trans hu'.symm) ⟨u ^ i, hp⟩ : zpowers u') : Y) *
      (((ruZpowersMulEquiv (hw.trans hw'.symm) ⟨w ^ j, hg⟩ : zpowers w') : Y))⁻¹
  rw [coe_ruZpowersMulEquiv_pow, coe_ruZpowersMulEquiv_pow, metaConj_pow_pow hr' j i]

theorem nonempty_mulEquiv_of_frob20 {X Y : Type*} [Group X] [Group Y] [Finite X] [Finite Y]
    (hX : Nat.card X = 20) (hY : Nat.card Y = 20) {u w : X} (hu : orderOf u = 5)
    (hw : w * u * w⁻¹ = u ^ 2) {u' w' : Y} (hu' : orderOf u' = 5)
    (hw' : w' * u' * w'⁻¹ = u' ^ 2) : Nonempty (X ≃* Y) :=
  nonempty_mulEquiv_of_meta (m := 5) (n := 4) (by norm_num) hu (frob20_orderOf_w hX hu hw)
    (by rw [hX]) hw hu' (frob20_orderOf_w hY hu' hw') (by rw [hY]) hw'

theorem frob20_exists_w {X : Type*} [Group X] [Finite X] (hX : Nat.card X = 20) {u : X}
    (hu : orderOf u = 5) (hN : ∀ x : X, x * u * x⁻¹ ∈ zpowers u)
    (hC : ∀ x : X, x * u = u * x → x ∈ zpowers u) : ∃ w : X, w * u * w⁻¹ = u ^ 2 := by
  classical
  have _ := Fintype.ofFinite X
  by_contra hne
  simp only [not_exists] at hne
  have hu5 : u ^ 5 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
  have hcover : ∀ x : X, x * u * x⁻¹ = u ∨ x * u * x⁻¹ = u ^ 3 ∨ x * u * x⁻¹ = u ^ 4 := by
    intro x
    obtain ⟨k, hk'⟩ := mem_powers_iff_mem_zpowers.mpr (hN x)
    have hk : u ^ k = x * u * x⁻¹ := hk'
    have hk5 : u ^ k = u ^ (k % 5) := by rw [← hu, pow_mod_orderOf]
    rw [hk5] at hk
    have hlt : k % 5 < 5 := Nat.mod_lt _ (by norm_num)
    interval_cases (k % 5)
    · exfalso
      rw [pow_zero] at hk
      have : u = 1 := by
        have h1 := congrArg (fun z => x⁻¹ * z * x) hk
        simpa [mul_assoc] using h1.symm
      rw [this, orderOf_one] at hu
      norm_num at hu
    · left; rw [← hk, pow_one]
    · exact absurd hk.symm (hne x)
    · right; left; exact hk.symm
    · right; right; exact hk.symm
  have hfib : ∀ v : X, (Finset.univ.filter (fun x : X => x * u * x⁻¹ = v)).card ≤ 5 := by
    intro v
    by_cases hv : ∃ x0 : X, x0 * u * x0⁻¹ = v
    · obtain ⟨x0, hx0⟩ := hv
      have hcard : (Subgroup.zpowers u : Set X).toFinset.card = 5 := by
        rw [Set.toFinset_card, ← Nat.card_eq_fintype_card, SetLike.coe_sort_coe,
          Nat.card_zpowers, hu]
      rw [← hcard]
      refine Finset.card_le_card_of_injOn (fun x => x0⁻¹ * x) ?_ ?_
      · intro x hx
        simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hx
        simp only [Set.coe_toFinset, SetLike.mem_coe]
        apply hC
        have h1 : x * u * x⁻¹ = x0 * u * x0⁻¹ := hx.trans hx0.symm
        have h2 : (x0⁻¹ * x) * u * (x0⁻¹ * x)⁻¹ = u := by
          calc (x0⁻¹ * x) * u * (x0⁻¹ * x)⁻¹ = x0⁻¹ * (x * u * x⁻¹) * x0 := by group
            _ = u := by rw [h1]; group
        calc (x0⁻¹ * x) * u = (x0⁻¹ * x) * u * (x0⁻¹ * x)⁻¹ * (x0⁻¹ * x) := by group
          _ = u * (x0⁻¹ * x) := by rw [h2]
      · intro a _ b _ hab
        simpa using hab
    · simp only [not_exists] at hv
      have : Finset.univ.filter (fun x : X => x * u * x⁻¹ = v) = ∅ := by
        ext x
        simp [hv x]
      rw [this, Finset.card_empty]
      norm_num
  have hunion : (Finset.univ : Finset X) ⊆ Finset.univ.filter (fun x : X => x * u * x⁻¹ = u) ∪
      Finset.univ.filter (fun x : X => x * u * x⁻¹ = u ^ 3) ∪
      Finset.univ.filter (fun x : X => x * u * x⁻¹ = u ^ 4) := by
    intro x _
    rcases hcover x with h | h | h <;> simp [h]
  have h1 := Finset.card_le_card hunion
  have h2 := (Finset.card_union_le
      (Finset.univ.filter (fun x : X => x * u * x⁻¹ = u) ∪
        Finset.univ.filter (fun x : X => x * u * x⁻¹ = u ^ 3))
      (Finset.univ.filter (fun x : X => x * u * x⁻¹ = u ^ 4))).trans
    (Nat.add_le_add_right (Finset.card_union_le _ _) _)
  have h3 : (Finset.univ : Finset X).card = 20 := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hX]
  have := hfib u
  have := hfib (u ^ 3)
  have := hfib (u ^ 4)
  omega

theorem perm3_meta : orderOf (finRotate 3) = 3 ∧ orderOf (Equiv.swap (0 : Fin 3) 1) = 2 ∧
    Equiv.swap (0 : Fin 3) 1 * finRotate 3 * (Equiv.swap (0 : Fin 3) 1)⁻¹ = finRotate 3 ^ 2 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨orderOf_eq_prime (by decide) (by decide), orderOf_eq_prime (by decide) (by decide),
    by decide⟩

theorem nonempty_mulEquiv_perm3 {X : Type*} [Group X] [Finite X] (hX : Nat.card X = 6)
    {u w : X} (hu : orderOf u = 3) (hw : orderOf w = 2) (hr : w * u * w⁻¹ = u ^ 2) :
    Nonempty (X ≃* Equiv.Perm (Fin 3)) :=
  nonempty_mulEquiv_of_meta (m := 3) (n := 2) (by norm_num) hu hw (by rw [hX]) hr
    perm3_meta.1 perm3_meta.2.1 (by rw [Nat.card_perm, Nat.card_fin]; rfl) perm3_meta.2.2

theorem sz_rel : uS10⁻¹ * (uW * uS01) * uS10⁻¹⁻¹ = (uW * uS01) ^ 2 := by
  apply Units.ext
  rw [inv_inv, Units.val_mul, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mul]
  show (!![1, 1, 1, 1; 0, 1, 1, 0; 0, 0, 1, 1; 0, 0, 0, 1] : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
      ((!![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
        !![1, 0, 1, 1; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1]) *
      !![1, 1, 0, 1; 0, 1, 1, 1; 0, 0, 1, 1; 0, 0, 0, 1] =
    ((!![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] : Matrix (Fin 4) (Fin 4) (ZMod 2)) *
      !![1, 0, 1, 1; 0, 1, 0, 1; 0, 0, 1, 0; 0, 0, 0, 1]) ^ 2
  decide +kernel

theorem szU_mem : szPsi.symm (uW * uS01) ∈ Sz 0 := by
  rw [map_mul]
  exact Subgroup.mul_mem _ uW_mem uS01_mem

theorem sz_zero_frob20 :
    orderOf (⟨szPsi.symm (uW * uS01), szU_mem⟩ : ↥(Sz 0)) = 5 ∧
      (⟨szPsi.symm uS10⁻¹, inv_mem uS10_mem⟩ : ↥(Sz 0)) *
        ⟨szPsi.symm (uW * uS01), szU_mem⟩ * (⟨szPsi.symm uS10⁻¹, inv_mem uS10_mem⟩ : ↥(Sz 0))⁻¹ =
        ⟨szPsi.symm (uW * uS01), szU_mem⟩ ^ 2 := by
  refine ⟨?_, Subtype.ext ?_⟩
  · rw [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, orderOf_uW_uS01]
  · simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow]
    rw [← map_inv, ← map_mul, ← map_mul, ← map_pow, sz_rel]

theorem nonempty_mulEquiv_sz_zero {X : Type*} [Group X] [Finite X] (hX : Nat.card X = 20)
    {u : X} (hu : orderOf u = 5) (hN : ∀ x : X, x * u * x⁻¹ ∈ zpowers u)
    (hC : ∀ x : X, x * u = u * x → x ∈ zpowers u) : Nonempty (X ≃* ↥(Sz 0)) := by
  obtain ⟨w, hw⟩ := frob20_exists_w hX hu hN hC
  exact nonempty_mulEquiv_of_frob20 hX card_Sz_zero hu hw sz_zero_frob20.1 sz_zero_frob20.2

end CFSG.Quasithin.RuType
