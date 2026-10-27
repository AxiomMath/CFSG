module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem4F1
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section

variable {G : Type*} [Group G]

theorem conj_mem_centralizer_of_mem_normalizer614 {y a x : G}
    (ha : a ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G))
    (hx : x ∈ Subgroup.centralizer ({y} : Set G)) :
    a * x * a⁻¹ ∈ Subgroup.centralizer ({y} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  have h1 : a⁻¹ * y * a ∈ Subgroup.zpowers y := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) y).mp
      (Subgroup.mem_zpowers y)
    simpa using this
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
  have hxk : x * y ^ k = y ^ k * x := ((Commute.zpow_left hx.symm k).symm).eq
  have e : y = a * y ^ k * a⁻¹ := by rw [hk]; group
  calc a * x * a⁻¹ * y = a * x * a⁻¹ * (a * y ^ k * a⁻¹) := by rw [← e]
    _ = a * (x * y ^ k) * a⁻¹ := by group
    _ = a * (y ^ k * x) * a⁻¹ := by rw [hxk]
    _ = a * y ^ k * a⁻¹ * (a * x * a⁻¹) := by group
    _ = y * (a * x * a⁻¹) := by rw [← e]

theorem exists_conj_le_of_conj_le_normalizer614 [Finite G] {N T E : Subgroup G} {y : G}
    (hNn : N.Normal) (hTs : IsSylowTwoOf T (N ⊔ T))
    (hTy : T ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G)) (hET : E ≤ T) {g : G}
    (hg : g ∈ N ⊔ T)
    (hEg : E.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G))
    (hEgc : ¬ E.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({y} : Set G)) :
    ∃ n ∈ N, E.map (MulAut.conj n).toMonoidHom ≤ T ∧
      ¬ E.map (MulAut.conj n).toMonoidHom ≤ Subgroup.centralizer ({y} : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := (N ⊔ T) ⊓ Subgroup.normalizer (Subgroup.zpowers y : Set G) with hM
  have hTM : T ≤ M := le_inf le_sup_right hTy
  have hMNT : M ≤ N ⊔ T := inf_le_left
  have hTsM : IsSylowTwoOf T M := by
    refine ⟨hTM, hTs.2.1, fun h2 => hTs.2.2 ?_⟩
    have := Subgroup.relIndex_mul_relIndex T M (N ⊔ T) hTM hMNT
    show 2 ∣ T.relIndex (N ⊔ T)
    rw [← this]
    exact dvd_mul_of_dvd_left h2 _
  have hEgM : E.map (MulAut.conj g).toMonoidHom ≤ M := by
    refine le_inf ?_ hEg
    rintro _ ⟨e, he, rfl⟩
    exact (N ⊔ T).mul_mem ((N ⊔ T).mul_mem hg ((le_sup_right : T ≤ N ⊔ T) (hET he)))
      ((N ⊔ T).inv_mem hg)
  have hEg2 : IsPGroup 2 (E.map (MulAut.conj g).toMonoidHom) :=
    (hTs.2.1.to_le hET).map _
  obtain ⟨S, hS, hES⟩ := EscapingLocal.exists_isSylowTwoOf_ge hEgM hEg2
  obtain ⟨c, hcM, hSc⟩ := hTsM.exists_conj hS
  have hcg : c⁻¹ * g ∈ N ⊔ T := (N ⊔ T).mul_mem ((N ⊔ T).inv_mem (hMNT hcM)) hg
  have hcg' : (c⁻¹ * g)⁻¹ ∈ ((N ⊔ T : Subgroup G) : Set G) := (N ⊔ T).inv_mem hcg
  rw [Subgroup.normal_mul] at hcg'
  obtain ⟨n, hn, t, ht, hnt⟩ := hcg'
  have hnt' : n * t = (c⁻¹ * g)⁻¹ := hnt
  have hg' : g = c * t⁻¹ * n⁻¹ := by
    have : c⁻¹ * g = t⁻¹ * n⁻¹ := by rw [← mul_inv_rev, hnt', inv_inv]
    calc g = c * (c⁻¹ * g) := by group
      _ = c * t⁻¹ * n⁻¹ := by rw [this]; group
  have hct : c * t⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G) :=
    Subgroup.mul_mem _ ((show M ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) from
      inf_le_right) hcM) (Subgroup.inv_mem _ (hTy ht))
  refine ⟨n⁻¹, N.inv_mem hn, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    have h1 : g * e * g⁻¹ ∈ S := hES ⟨e, he, rfl⟩
    rw [hSc] at h1
    obtain ⟨s, hs, hse⟩ := h1
    have hse' : c * s * c⁻¹ = g * e * g⁻¹ := hse
    have e2 : n⁻¹ * e * n⁻¹⁻¹ = t * s * t⁻¹ := by
      have : s = c⁻¹ * (g * e * g⁻¹) * c := by rw [← hse']; group
      rw [this, hg']
      group
    show n⁻¹ * e * n⁻¹⁻¹ ∈ T
    rw [e2]
    exact T.mul_mem (T.mul_mem ht hs) (T.inv_mem ht)
  · intro hle
    apply hEgc
    rintro _ ⟨e, he, rfl⟩
    have h1 : n⁻¹ * e * n⁻¹⁻¹ ∈ Subgroup.centralizer ({y} : Set G) := hle ⟨e, he, rfl⟩
    have h2 := conj_mem_centralizer_of_mem_normalizer614 hct h1
    have e2 : c * t⁻¹ * (n⁻¹ * e * n⁻¹⁻¹) * (c * t⁻¹)⁻¹ = g * e * g⁻¹ := by
      rw [hg']; group
    show g * e * g⁻¹ ∈ _
    rw [← e2]
    exact h2

theorem pCoreOf_le_centralizer614 [Finite G] {T : Subgroup G} {y : G} (hy : orderOf y = 5)
    (hTy : T ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G)) :
    pCoreOf 2 (Subgroup.zpowers y ⊔ T) ≤ Subgroup.centralizer ({y} : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro o ho
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hoXT : o ∈ Subgroup.zpowers y ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _ ho
  have hO2 : IsPGroup 2 (pCoreOf 2 (Subgroup.zpowers y ⊔ T)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hXN : Subgroup.zpowers y ⊔ T ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) :=
    sup_le Subgroup.le_normalizer hTy
  set c := o * y * o⁻¹ * y⁻¹ with hc
  have hc1 : c ∈ Subgroup.zpowers y := by
    have h := (Subgroup.mem_normalizer_iff.mp (hXN hoXT) y).mp (Subgroup.mem_zpowers y)
    exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ (Subgroup.mem_zpowers y))
  have hc2 : c ∈ pCoreOf 2 (Subgroup.zpowers y ⊔ T) := by
    have hy' : y ∈ Subgroup.zpowers y ⊔ T :=
      (le_sup_left : Subgroup.zpowers y ≤ Subgroup.zpowers y ⊔ T) (Subgroup.mem_zpowers y)
    have h := (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ hy') o⁻¹).mp
      (Subgroup.inv_mem _ ho)
    have e : c = o * (y * o⁻¹ * y⁻¹) := by rw [hc]; group
    rw [e]
    exact Subgroup.mul_mem _ ho h
  have hc3 : c = 1 := by
    obtain ⟨k, hk⟩ := hO2 ⟨c, hc2⟩
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h5 : c ^ 5 = 1 := by
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hc1
      rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hy,
        pow_orderOf_eq_one, one_zpow]
    have hd1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hd2 : orderOf c ∣ 5 := orderOf_dvd_of_pow_eq_one h5
    have hcop : Nat.Coprime (2 ^ k) 5 := Nat.Coprime.pow_left _ (by norm_num)
    have : orderOf c = 1 := Nat.eq_one_of_dvd_coprimes hcop hd1 hd2
    exact orderOf_eq_one_iff.mp this
  have e : o * y = y * o := by
    calc o * y = c * (y * o) := by rw [hc]; group
      _ = y * o := by rw [hc3, one_mul]
  exact e

end

section

variable {G : Type*} [Group G]

theorem eq_one_of_mem_zpowers_of_pow_two614 {y c : G} (hy : y ^ 5 = 1)
    (hc : c ∈ Subgroup.zpowers y) {k : ℕ} (hk : c ^ 2 ^ k = 1) : c = 1 := by
  have h5 : c ^ 5 = 1 := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hc
    rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hy, one_zpow]
  have hd1 : orderOf c ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hd2 : orderOf c ∣ 5 := orderOf_dvd_of_pow_eq_one h5
  have hcop : Nat.Coprime (2 ^ k) 5 := Nat.Coprime.pow_left _ (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)

theorem eq_one_of_pow_two_of_odd614 {p : G} {k m : ℕ} (hk : p ^ 2 ^ k = 1) (hm : p ^ m = 1)
    (hmo : Odd m) : p = 1 := by
  have hd1 : orderOf p ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hd2 : orderOf p ∣ m := orderOf_dvd_of_pow_eq_one hm
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hmo)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)

theorem exists_eq_zpowers_of_relIndex_five614 [Finite G] {N T X : Subgroup G}
    (hrank : ∀ V : Subgroup G, V ≤ N → IsElemAbelian 2 V → Nat.card V ≤ 4)
    (hcent : ∀ y u g : G, y ∈ N → u ∈ N → g ∈ N → orderOf y = 5 → orderOf u = 2 →
      Commute y u → Commute g u → g ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G))
    (hT2 : IsPGroup 2 T) (hXN : X ≤ N) (hXO : X = oTwoUpper X) (hX5 : (X ⊓ T).relIndex X = 5)
    (hXn : ((X ⊓ T).subgroupOf X).Normal) :
    ∃ y : G, orderOf y = 5 ∧ X = Subgroup.zpowers y := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set P := X ⊓ T with hP
  have hP2 : IsPGroup 2 P := hT2.to_le inf_le_right
  have hPX : P ≤ X := inf_le_left
  have hcardX : Nat.card X = 5 * Nat.card P := by
    have := Subgroup.relIndex_mul_card P X
    rw [hX5, inf_of_le_left hPX] at this
    exact this.symm
  obtain ⟨y', hy'⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 5
    (by rw [hcardX]; exact dvd_mul_right _ _)
  set y : G := (y' : G) with hydef
  have hyX : y ∈ X := y'.2
  have hy5 : orderOf y = 5 := by rw [hydef, Subgroup.orderOf_coe]; exact hy'
  have hy5' : y ^ 5 = 1 := by rw [← hy5]; exact pow_orderOf_eq_one y
  have hPy : ∀ c, c ∈ P → c ∈ Subgroup.zpowers y → c = 1 := by
    intro c hcP hcy
    obtain ⟨k, hk⟩ := hP2 ⟨c, hcP⟩
    exact eq_one_of_mem_zpowers_of_pow_two614 hy5' hcy (by simpa using congrArg Subtype.val hk)
  have hXP : ∀ g ∈ X, ∀ p ∈ P, g * p * g⁻¹ ∈ P := by
    intro g hg p hp
    have := hXn.conj_mem ⟨p, hp.1⟩ (show (⟨p, hp.1⟩ : ↥X) ∈ P.subgroupOf X from hp) ⟨g, hg⟩
    exact this
  have hycomm : ∀ p ∈ P, Commute y p := by
    by_cases hPb : P = ⊥
    · intro p hp
      rw [hPb, Subgroup.mem_bot] at hp
      rw [hp]
      exact Commute.one_right y
    let W : Subgroup G :=
      { carrier := {u | u ∈ P ∧ (∀ p ∈ P, Commute u p) ∧ u ^ 2 = 1}
        mul_mem' := by
          rintro a b ⟨haP, hac, ha2⟩ ⟨hbP, hbc, hb2⟩
          refine ⟨P.mul_mem haP hbP, fun p hp => (hac p hp).mul_left (hbc p hp), ?_⟩
          rw [pow_two, mul_assoc, ← mul_assoc b, ← (hac b hbP).eq, mul_assoc, ← pow_two b, hb2,
            mul_one, ← pow_two, ha2]
        one_mem' := ⟨P.one_mem, fun p _ => Commute.one_left p, one_pow 2⟩
        inv_mem' := by
          rintro a ⟨haP, hac, ha2⟩
          refine ⟨P.inv_mem haP, fun p hp => (hac p hp).inv_left, ?_⟩
          rw [inv_pow, ha2, inv_one] }
    have hWP : W ≤ P := fun u hu => hu.1
    have hWab : IsElemAbelian 2 W := by
      refine ⟨⟨⟨fun a b => Subtype.ext ((a.2.2.1 b (hWP b.2)).eq)⟩⟩, fun u hu => hu.2.2⟩
    have hW4 : Nat.card W ≤ 4 := hrank W ((hWP.trans hPX).trans hXN) hWab
    have hWne : ∃ u ∈ W, u ≠ 1 := by
      have : Nontrivial ↥P := (Subgroup.nontrivial_iff_ne_bot P).mpr hPb
      have hZ := hP2.center_nontrivial
      have hZ2 : IsPGroup 2 (Subgroup.center ↥P) := hP2.to_subgroup _
      have h2Z : 2 ∣ Nat.card (Subgroup.center ↥P) := by
        rcases hZ2.card_eq_or_dvd with h | h
        · exact absurd h (Finite.one_lt_card).ne'
        · exact h
      obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center ↥P)) 2 h2Z
      refine ⟨((u : ↥P) : G), ⟨(u : ↥P).2, fun p hp => ?_, ?_⟩, ?_⟩
      · have := (Subgroup.mem_center_iff.mp u.2 ⟨p, hp⟩)
        exact (congrArg Subtype.val this).symm
      · have : u ^ 2 = 1 := by rw [← hu]; exact pow_orderOf_eq_one u
        have := congrArg (fun v : ↥(Subgroup.center ↥P) => ((v : ↥P) : G)) this
        simpa using this
      · intro h1
        have : u = 1 := Subtype.ext (Subtype.ext h1)
        rw [this, orderOf_one] at hu
        exact absurd hu (by norm_num)
    obtain ⟨u, huW, hu1⟩ := hWne
    have hyW : ∀ w ∈ W, y * w * y⁻¹ ∈ W := by
      rintro w ⟨hwP, hwc, hw2⟩
      refine ⟨hXP y hyX w hwP, fun p hp => ?_, ?_⟩
      · have hp' : y⁻¹ * p * y⁻¹⁻¹ ∈ P := hXP y⁻¹ (X.inv_mem hyX) p hp
        have h1 := hwc _ hp'
        rw [inv_inv] at hp' h1
        have e : p = y * (y⁻¹ * p * y) * y⁻¹ := by group
        show y * w * y⁻¹ * p = p * (y * w * y⁻¹)
        rw [e]
        calc y * w * y⁻¹ * (y * (y⁻¹ * p * y) * y⁻¹) = y * (w * (y⁻¹ * p * y)) * y⁻¹ := by
              group
          _ = y * ((y⁻¹ * p * y) * w) * y⁻¹ := by rw [h1.eq]
          _ = y * (y⁻¹ * p * y) * y⁻¹ * (y * w * y⁻¹) := by group
      · have e : (y * w * y⁻¹) ^ 2 = y * w ^ 2 * y⁻¹ := by rw [pow_two, pow_two]; group
        rw [e, hw2]
        group
    have hyWinv : ∀ w ∈ W, y⁻¹ * w * y ∈ W := by
      intro w hw
      have h4 : ∀ n : ℕ, y ^ n * w * (y ^ n)⁻¹ ∈ W := by
        intro n
        induction n with
        | zero => simpa using hw
        | succ n ih =>
          have := hyW _ ih
          rw [pow_succ']
          convert this using 1
          group
      have := h4 4
      have e : y ^ 4 = y⁻¹ := by
        rw [eq_inv_iff_mul_eq_one, ← pow_succ, hy5']
      rw [e, inv_inv] at this
      exact this
    let σ : Equiv.Perm ↥W :=
      { toFun := fun w => ⟨y * w * y⁻¹, hyW w w.2⟩
        invFun := fun w => ⟨y⁻¹ * w * y, hyWinv w w.2⟩
        left_inv := fun w => Subtype.ext (by simp [mul_assoc])
        right_inv := fun w => Subtype.ext (by simp [mul_assoc]) }
    have hσpow : ∀ (n : ℕ) (w : ↥W), ((σ ^ n) w : G) = y ^ n * w * (y ^ n)⁻¹ := by
      intro n
      induction n with
      | zero => intro w; simp
      | succ n ih =>
        intro w
        rw [pow_succ', Equiv.Perm.mul_apply]
        show y * (((σ ^ n) w : ↥W) : G) * y⁻¹ = _
        rw [ih]
        group
    have hσ5 : σ ^ 5 = 1 := by
      ext w
      rw [hσpow, hy5']
      simp
    have hσ1 : σ = 1 := by
      have hd1 : orderOf σ ∣ 5 := orderOf_dvd_of_pow_eq_one hσ5
      have hd2 : orderOf σ ∣ (Nat.card W).factorial := by
        have := orderOf_dvd_natCard σ
        rwa [Nat.card_perm] at this
      have hd3 : (Nat.card W).factorial ∣ 24 := by
        have := Nat.factorial_dvd_factorial hW4
        rwa [show Nat.factorial 4 = 24 from rfl] at this
      have : orderOf σ = 1 := by
        rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hd1 with h | h
        · exact h
        · rw [h] at hd2
          have := hd2.trans hd3
          norm_num at this
      exact orderOf_eq_one_iff.mp this
    have hyu : Commute y u := by
      have := congrArg (fun τ : Equiv.Perm ↥W => ((τ ⟨u, huW⟩ : ↥W) : G)) hσ1
      simp only [Equiv.Perm.coe_one, id_eq] at this
      have e : y * u * y⁻¹ = u := this
      show y * u = u * y
      calc y * u = y * u * y⁻¹ * y := by group
        _ = u * y := by rw [e]
    have hu2 : orderOf u = 2 := orderOf_eq_prime huW.2.2 hu1
    have huN : u ∈ N := hXN (hPX (hWP huW))
    intro p hp
    have hpN : p ∈ N := hXN (hPX hp)
    have hpu : Commute p u := (huW.2.1 p hp).symm
    have hpy := hcent y u p (hXN hyX) huN hpN hy5 hu2 hyu hpu
    set c := p * y * p⁻¹ * y⁻¹ with hc
    have hc1 : c ∈ Subgroup.zpowers y := by
      have h := (Subgroup.mem_normalizer_iff.mp hpy y).mp (Subgroup.mem_zpowers y)
      exact Subgroup.mul_mem _ h (Subgroup.inv_mem _ (Subgroup.mem_zpowers y))
    have hc2 : c ∈ P := by
      have h := hXP y hyX p⁻¹ (P.inv_mem hp)
      have e : c = p * (y * p⁻¹ * y⁻¹) := by rw [hc]; group
      rw [e]
      exact P.mul_mem hp h
    have hc3 := hPy c hc2 hc1
    show y * p = p * y
    calc y * p = c⁻¹ * (p * y) := by rw [hc]; group
      _ = p * y := by rw [hc3, inv_one, one_mul]
  refine ⟨y, hy5, le_antisymm ?_ ?_⟩
  · rw [hXO, oTwoUpper, Subgroup.closure_le]
    rintro x ⟨hxX, hxo⟩
    set Q := ↥X ⧸ P.subgroupOf X
    have hQ : Nat.card Q = 5 := hX5
    have hyQ : ((y' : ↥X) : Q) ≠ 1 := by
      intro h
      rw [QuotientGroup.eq_one_iff] at h
      have := hPy y h (Subgroup.mem_zpowers y)
      rw [this, orderOf_one] at hy5
      exact absurd hy5 (by norm_num)
    have htop : Subgroup.zpowers ((y' : ↥X) : Q) = ⊤ :=
      zpowers_eq_top_of_prime_card (p := 5) hQ hyQ
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp
      (htop.symm ▸ Subgroup.mem_top (((⟨x, hxX⟩ : ↥X)) : Q))
    have hp : (y ^ i)⁻¹ * x ∈ P := by
      rw [← QuotientGroup.mk_zpow, QuotientGroup.eq] at hi
      have h2 : (((y' ^ i)⁻¹ * ⟨x, hxX⟩ : ↥X) : G) ∈ P := hi
      simpa [hydef] using h2
    set p := (y ^ i)⁻¹ * x with hpdef
    have hx : x = y ^ i * p := by rw [hpdef]; group
    have hpy : Commute (y ^ i) p := (hycomm p hp).zpow_left i
    obtain ⟨k, hk⟩ := hP2 ⟨p, hp⟩
    have hk' : p ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    set m := orderOf x with hmdef
    have hm : p ^ m = 1 := by
      have h1 : x ^ m = 1 := pow_orderOf_eq_one x
      rw [hx, hpy.mul_pow] at h1
      have h2 : (y ^ i) ^ m ∈ Subgroup.zpowers y := by
        rw [← zpow_natCast, ← zpow_mul]
        exact Subgroup.zpow_mem_zpowers _ _
      have h3 : p ^ m = ((y ^ i) ^ m)⁻¹ := eq_inv_of_mul_eq_one_right h1
      have h4 : p ^ m ∈ Subgroup.zpowers y := h3 ▸ Subgroup.inv_mem _ h2
      exact hPy _ (P.pow_mem hp _) h4
    have hp1 := eq_one_of_pow_two_of_odd614 hk' hm hxo
    rw [hx, hp1, mul_one]
    exact Subgroup.zpow_mem_zpowers y i
  · rw [Subgroup.zpowers_le]
    exact hyX

end

section

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]

theorem isSylowTwoOf_map_mulEquiv614 (Ψ : G₁ ≃* G₂) {S H : Subgroup G₁}
    (h : IsSylowTwoOf S H) : IsSylowTwoOf (S.map Ψ.toMonoidHom) (H.map Ψ.toMonoidHom) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map _, ?_⟩
  have e : ((S.map Ψ.toMonoidHom).subgroupOf (H.map Ψ.toMonoidHom)).index =
      (S.subgroupOf H).index := by
    show (S.map Ψ.toMonoidHom).relIndex (H.map Ψ.toMonoidHom) = S.relIndex H
    rw [Subgroup.relIndex_map_map]
    have hk : Ψ.toMonoidHom.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr Ψ.injective
    rw [hk, sup_bot_eq, sup_bot_eq]
  rw [e]
  exact h.2.2

theorem map_conj_map_mulEquiv614 (Ψ : G₁ ≃* G₂) (E : Subgroup G₁) (n : G₁) :
    (E.map (MulAut.conj n).toMonoidHom).map Ψ.toMonoidHom =
      (E.map Ψ.toMonoidHom).map (MulAut.conj (Ψ n)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply]

theorem locFus614_of_mulEquiv [Finite G₁] (Ψ : G₁ ≃* G₂) {N₁ : Subgroup G₁} {N₂ : Subgroup G₂}
    (hN : N₁.map Ψ.toMonoidHom = N₂) (h : LocFus614 G₂ N₂) : LocFus614 G₁ N₁ := by
  classical
  have hinj : Function.Injective Ψ.toMonoidHom := Ψ.injective
  intro T X E hTs hXN hXO hX5 hXn hTX hE hEa hE1
  set f := Ψ.toMonoidHom
  have hTs' : IsSylowTwoOf (T.map f) (N₂ ⊔ T.map f) := by
    rw [← hN, ← Subgroup.map_sup]
    exact isSylowTwoOf_map_mulEquiv614 Ψ hTs
  have hXN' : X.map f ≤ N₂ := hN ▸ Subgroup.map_mono hXN
  have hXO' : X.map f = oTwoUpper (X.map f) := by
    rw [oTwoUpper_map, ← hXO]
  have hinf : X.map f ⊓ T.map f = (X ⊓ T).map f := (Subgroup.map_inf_eq X T f hinj).symm
  have hX5' : (X.map f ⊓ T.map f).relIndex (X.map f) = 5 := by
    rw [hinf, Subgroup.relIndex_map_map]
    have hk : f.ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).mpr hinj
    rw [hk, sup_bot_eq, sup_bot_eq]
    exact hX5
  have hXn' : ((X.map f ⊓ T.map f).subgroupOf (X.map f)).Normal := by
    have hsub : ((X.map f ⊓ T.map f).subgroupOf (X.map f)) =
        ((X ⊓ T).subgroupOf X).map (Ψ.subgroupMap X).toMonoidHom := by
      rw [hinf]
      ext ⟨y, hy⟩
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx.1⟩, hx, rfl⟩
      · rintro ⟨x, hx, he⟩
        refine ⟨x, hx, ?_⟩
        have := congrArg Subtype.val he
        exact this
    rw [hsub]
    exact hXn.map _ (Ψ.subgroupMap X).surjective
  have hTX' : T.map f ≤ Subgroup.normalizer (X.map f : Set G₂) := by
    rw [← Subgroup.map_equiv_normalizer_eq X Ψ]
    exact Subgroup.map_mono hTX
  have hsup : X.map f ⊔ T.map f = (X ⊔ T).map f := (Subgroup.map_sup X T f).symm
  have hO : pCoreOf 2 (X.map f ⊔ T.map f) = (pCoreOf 2 (X ⊔ T)).map f := by
    rw [hsup]
    exact CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 Ψ (X ⊔ T)
  have hE' : E.map f ≤ pCoreOf 2 (X.map f ⊔ T.map f) := hO ▸ Subgroup.map_mono hE
  have hEa' : IsElemAbelian 2 (E.map f) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      apply Subtype.ext
      show f x * f y = f y * f x
      rw [← map_mul, ← map_mul]
      congr 1
      have := hEa.1.is_comm.comm (⟨x, hx⟩ : ↥E) ⟨y, hy⟩
      have h2 : x * y = y * x := congrArg Subtype.val this
      exact h2
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hEa.2 x hx, map_one]
  have hE1' : E.map f ≠ ⊥ := by
    intro hb
    apply hE1
    rwa [Subgroup.map_eq_bot_iff_of_injective _ hinj] at hb
  obtain ⟨n₂, hn₂, hT₂, hO₂⟩ := h (T.map f) (X.map f) (E.map f) hTs' hXN' hXO' hX5' hXn' hTX'
    hE' hEa' hE1'
  rw [← hN] at hn₂
  obtain ⟨n, hn, rfl⟩ := hn₂
  refine ⟨n, hn, ?_, ?_⟩
  · rw [← Subgroup.map_le_map_iff_of_injective hinj, map_conj_map_mulEquiv614]
    exact hT₂
  · intro hle
    apply hO₂
    rw [hO]
    have e := map_conj_map_mulEquiv614 Ψ E n
    calc (E.map f).map (MulAut.conj (f n)).toMonoidHom =
          (E.map (MulAut.conj n).toMonoidHom).map f := e.symm
      _ ≤ _ := Subgroup.map_mono hle

variable {G : Type*} [Group G]

@[expose] def FindFus614 (G : Type*) [Group G] (N : Subgroup G) : Prop :=
  ∀ (T E : Subgroup G) (y : G), IsSylowTwoOf T (N ⊔ T) → y ∈ N → orderOf y = 5 →
    T ≤ Subgroup.normalizer (Subgroup.zpowers y : Set G) → E ≤ T →
    E ≤ Subgroup.centralizer ({y} : Set G) → IsElemAbelian 2 E → E ≠ ⊥ →
      ∃ g ∈ N ⊔ T, E.map (MulAut.conj g).toMonoidHom ≤
          Subgroup.normalizer (Subgroup.zpowers y : Set G) ∧
        ¬ E.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer ({y} : Set G)

theorem locFus614_of_findFus [Finite G] {N : Subgroup G} (hNn : N.Normal)
    (hrank : ∀ V : Subgroup G, V ≤ N → IsElemAbelian 2 V → Nat.card V ≤ 4)
    (hcent : ∀ y u g : G, y ∈ N → u ∈ N → g ∈ N → orderOf y = 5 → orderOf u = 2 →
      Commute y u → Commute g u → g ∈ Subgroup.normalizer (Subgroup.zpowers y : Set G))
    (hfind : FindFus614 G N) : LocFus614 G N := by
  intro T X E hTs hXN hXO hX5 hXn hTX hE hEa hE1
  obtain ⟨y, hy5, rfl⟩ := exists_eq_zpowers_of_relIndex_five614 hrank hcent hTs.2.1 hXN hXO
    hX5 hXn
  have hyN : y ∈ N := hXN (Subgroup.mem_zpowers y)
  have hOC := pCoreOf_le_centralizer614 hy5 hTX
  have hTXs : IsSylowTwoOf T (Subgroup.zpowers y ⊔ T) := by
    refine ⟨le_sup_right, hTs.2.1, fun h2 => hTs.2.2 ?_⟩
    have hle : Subgroup.zpowers y ⊔ T ≤ N ⊔ T := sup_le_sup_right hXN T
    have := Subgroup.relIndex_mul_relIndex T (Subgroup.zpowers y ⊔ T) (N ⊔ T) le_sup_right hle
    show 2 ∣ T.relIndex (N ⊔ T)
    rw [← this]
    exact dvd_mul_of_dvd_left h2 _
  have hET : E ≤ T := hE.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hTXs)
  obtain ⟨g, hg, hEg, hEgc⟩ := hfind T E y hTs hyN hy5 hTX hET (hE.trans hOC) hEa hE1
  obtain ⟨n, hn, hnT, hnC⟩ :=
    exists_conj_le_of_conj_le_normalizer614 hNn hTs hTX hET hg hEg hEgc
  exact ⟨n, hn, hnT, fun h => hnC (h.trans hOC)⟩

end

end CFSG.Quasithin.H13
