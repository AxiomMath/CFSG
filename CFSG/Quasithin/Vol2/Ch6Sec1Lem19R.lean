module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19Aux

public section

namespace CFSG.Quasithin.H13.L619

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin

theorem transfer_eq_one_of_closure {E : Type*} [Group E] [Finite E] {p : ℕ} [hp : Fact p.Prime]
    (hp2 : p ≠ 2) (hgen : Subgroup.closure {x : E | ∃ k : ℕ, x ^ 2 ^ k = 1} = ⊤)
    (P : Sylow p E) :
    (Abelianization.of : (P : Subgroup E) →* Abelianization (P : Subgroup E)).transfer = 1 := by
  classical
  refine MonoidHom.eq_of_eqOn_dense hgen fun x hx => ?_
  obtain ⟨k, hk⟩ := hx
  set t := (Abelianization.of : (P : Subgroup E) →* Abelianization (P : Subgroup E)).transfer x
  have h1 : t ^ 2 ^ k = 1 := by rw [← map_pow, hk, map_one]
  have h2 : t ^ Nat.card (Abelianization (P : Subgroup E)) = 1 := pow_card_eq_one'
  have hab : IsPGroup p (Abelianization (P : Subgroup E)) :=
    IsPGroup.to_quotient P.isPGroup' _
  have hcop : Nat.Coprime (2 ^ k) (Nat.card (Abelianization (P : Subgroup E))) := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hab
    rw [hm]
    refine Nat.Coprime.pow _ _ ?_
    exact (Nat.coprime_primes Nat.prime_two hp.out).mpr (Ne.symm hp2)
  exact (pow_eq_one_iff_of_coprime hcop).mp ⟨h1, h2⟩

theorem central_mem_sylow_derived_of_closure {E : Type*} [Group E] [Finite E] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (hgen : Subgroup.closure {x : E | ∃ k : ℕ, x ^ 2 ^ k = 1} = ⊤)
    (P : Sylow p E) (a : (P : Subgroup E)) (hcentral : (a : E) ∈ Subgroup.center E) :
    a ∈ commutator (P : Subgroup E) := by
  let φ : (P : Subgroup E) →* Abelianization (P : Subgroup E) := Abelianization.of
  have htrivial : φ.transfer = 1 := transfer_eq_one_of_closure hp2 hgen P
  have hkey : ∀ (k : ℕ) (g : E),
      g⁻¹ * (a : E) ^ k * g ∈ (P : Subgroup E) →
        g⁻¹ * (a : E) ^ k * g = (a : E) ^ k := by
    intro k g _
    have hcomm := Subgroup.mem_center_iff.mp
      ((Subgroup.center E).pow_mem hcentral k) g
    calc
      g⁻¹ * (a : E) ^ k * g = g⁻¹ * (g * (a : E) ^ k) := by
        rw [mul_assoc, hcomm.symm]
      _ = (a : E) ^ k := inv_mul_cancel_left g _
  have hindex : (φ a) ^ (P : Subgroup E).index = 1 := by
    have hvalue : φ.transfer (a : E) = 1 :=
      congrArg (fun f : E →* Abelianization (P : Subgroup E) => f (a : E)) htrivial
    rw [MonoidHom.transfer_eq_pow φ (a : E) hkey] at hvalue
    change φ (a ^ (P : Subgroup E).index) = 1 at hvalue
    simpa only [map_pow] using hvalue
  have hcard : (φ a) ^ Nat.card (P : Subgroup E) = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  have hone : φ a = 1 :=
    (pow_eq_one_iff_of_coprime P.card_coprime_index).mp ⟨hcard, hindex⟩
  rw [← Abelianization.ker_of (P : Subgroup E)]
  exact hone

theorem central_ker_eq_bot_of_cyclic {E D : Type*} [Group E] [Finite E] [Group D] [Finite D]
    (η : E →* D) (hsurj : Function.Surjective η) (hcentral : η.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card η.ker))
    (hgen : Subgroup.closure {x : E | ∃ k : ℕ, x ^ 2 ^ k = 1} = ⊤)
    (hcyclic : ∀ p [Fact p.Prime], p ≠ 2 → ∀ P : Sylow p D, IsCyclic P) :
    η.ker = ⊥ := by
  classical
  apply le_antisymm _ bot_le
  intro x hx
  by_contra hxone
  have hcard : Nat.card η.ker ≠ 1 := by
    intro hcard
    have hbot : η.ker = ⊥ := Subgroup.card_eq_one.mp hcard
    exact hxone (hbot ▸ hx)
  obtain ⟨p, hp, hpdiv⟩ := Nat.exists_prime_and_dvd hcard
  let : Fact p.Prime := ⟨hp⟩
  have hpodd : p ≠ 2 := by
    intro heq
    exact hodd.not_two_dvd_nat (heq ▸ hpdiv)
  obtain ⟨a, haorder⟩ := exists_prime_orderOf_dvd_card' (G := η.ker) p hpdiv
  have haEorder : orderOf (a : E) = p := (Subgroup.orderOf_coe a).trans haorder
  have haPGroup : IsPGroup p (Subgroup.zpowers (a : E)) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, haEorder, pow_one]
  obtain ⟨P, hP⟩ := haPGroup.exists_le_sylow
  have haP : (a : E) ∈ (P : Subgroup E) := hP (Subgroup.mem_zpowers (a : E))
  let R : Sylow p D := Sylow.mapSurjective hsurj P
  let : IsCyclic R := hcyclic p hpodd R
  let φ : (P : Subgroup E) →* R :=
    (η.comp (P : Subgroup E).subtype).codRestrict (R : Subgroup D) (by
      intro b
      change η (b : E) ∈ (R : Subgroup D)
      rw [Sylow.coe_mapSurjective]
      exact Subgroup.mem_map_of_mem η b.property)
  have hφcentral : φ.ker ≤ Subgroup.center (P : Subgroup E) := by
    intro b hb
    have hbker : (b : E) ∈ η.ker := congrArg Subtype.val hb
    apply Subgroup.mem_center_iff.mpr
    intro c
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hcentral hbker)) (c : E))
  let : IsMulCommutative (P : Subgroup E) :=
    φ.isMulCommutative_of_isCyclic_of_ker_le_center hφcentral
  have haderived : (⟨(a : E), haP⟩ : (P : Subgroup E)) ∈ commutator (P : Subgroup E) :=
    central_mem_sylow_derived_of_closure hpodd hgen P ⟨(a : E), haP⟩ (hcentral a.property)
  rw [commutator_eq_bot] at haderived
  have haone : (a : E) = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp haderived)
  have hprimeone : p = 1 := by simpa only [haone, orderOf_one] using haEorder.symm
  exact hp.ne_one hprimeone


variable {G : Type} [Group G] [Finite G]


omit [Finite G] in
theorem exists_pow_mul_eq {N : Subgroup G} {o n : G} (ho : o ∈ Subgroup.normalizer (N : Set G))
    (hn : n ∈ N) (j : ℕ) : ∃ n' ∈ N, (n * o) ^ j = n' * o ^ j := by
  induction j with
  | zero => exact ⟨1, N.one_mem, by simp⟩
  | succ j ih =>
    obtain ⟨n', hn', he⟩ := ih
    refine ⟨n' * (o ^ j * n * (o ^ j)⁻¹), N.mul_mem hn' ?_, ?_⟩
    · have hoj : o ^ j ∈ Subgroup.normalizer (N : Set G) := Subgroup.pow_mem _ ho j
      exact (Subgroup.mem_normalizer_iff.mp hoj n).mp hn
    · rw [pow_succ, he, pow_succ]
      group

omit [Finite G] in
theorem mem_of_pow_three_eq_one {N O : Subgroup G} (hO : IsPGroup 2 O)
    (hON : O ≤ Subgroup.normalizer (N : Set G)) {x : G} (hx : x ∈ N ⊔ O) {k : ℕ}
    (hk : x ^ 3 ^ k = 1) : x ∈ N := by
  have hx' : x ∈ ((N ⊔ O : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left N O hON] at hx'
  obtain ⟨n, hn, o, ho, rfl⟩ := hx'
  show n * o ∈ N
  replace hk : (n * o) ^ 3 ^ k = 1 := hk
  obtain ⟨m, hm⟩ := hO ⟨o, ho⟩
  have hm' : o ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  obtain ⟨n', hn', he⟩ := exists_pow_mul_eq (hON ho) hn (2 ^ m)
  rw [hm', mul_one] at he
  have hcop : Nat.Coprime (2 ^ m) (orderOf (n * o)) := by
    have hdvd : orderOf (n * o) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
    exact Nat.Coprime.coprime_dvd_right hdvd (Nat.Coprime.pow _ _ (by norm_num))
  obtain ⟨j, hj⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hj, he]
  exact N.pow_mem hn' j

omit [Finite G] in
theorem mem_normalizer_sup {g : G} {X Y : Subgroup G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((X ⊔ Y : Subgroup G) : Set G) := by
  have key : ∀ h : G, h ∈ Subgroup.normalizer (X : Set G) → h ∈ Subgroup.normalizer (Y : Set G) →
      X ⊔ Y ≤ (X ⊔ Y).comap (MulAut.conj h).toMonoidHom := by
    intro h hX hY
    refine sup_le (fun x hx => ?_) (fun y hy => ?_)
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hX x).mp hx)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hY y).mp hy)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact key g hX hY hx
  · intro hx
    have := key g⁻¹ (Subgroup.inv_mem _ hX) (Subgroup.inv_mem _ hY) hx
    simpa [mul_assoc] using this

omit [Finite G] in
theorem eq_one_of_isPGroup_three_two {R O : Subgroup G} (hR : IsPGroup 3 R) (hO : IsPGroup 2 O)
    {x : G} (hxR : x ∈ R) (hxO : x ∈ O) : x = 1 := by
  obtain ⟨a, ha⟩ := hR ⟨x, hxR⟩
  obtain ⟨b, hb⟩ := hO ⟨x, hxO⟩
  have ha' : x ^ 3 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hb' : x ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have h1 : orderOf x ∣ 3 ^ a := orderOf_dvd_of_pow_eq_one ha'
  have h2 : orderOf x ∣ 2 ^ b := orderOf_dvd_of_pow_eq_one hb'
  have hcop : Nat.Coprime (3 ^ a) (2 ^ b) := Nat.Coprime.pow _ _ (by norm_num)
  have : orderOf x ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd h1 h2
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)

theorem exists_mem_sylow_of_orderOf {X N : Subgroup G} (hNX : N ≤ X)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (R : Sylow 3 ↥X) {a : G} (ha : a ∈ N)
    (h3 : orderOf a = 3) :
    ∃ x ∈ N, x ∈ (R : Subgroup ↥X).map X.subtype ∧ orderOf x = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set a' : ↥X := ⟨a, hNX ha⟩
  have hp : IsPGroup 3 (Subgroup.zpowers a') := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, pow_one, Subgroup.orderOf_mk, h3]
  obtain ⟨Q, hQ⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥X Q R
  refine ⟨(g : G) * a * (g : G)⁻¹, (Subgroup.mem_normalizer_iff.mp (hXN g.2) a).mp ha, ?_, ?_⟩
  · refine ⟨g * a' * g⁻¹, ?_, rfl⟩
    have hmem : g * a' * g⁻¹ ∈ ((g • Q : Sylow 3 ↥X) : Subgroup ↥X) :=
      Subgroup.smul_mem_pointwise_smul a' (MulAut.conj g) (Q : Subgroup ↥X)
        (hQ (Subgroup.mem_zpowers a'))
    rwa [hg] at hmem
  · rw [← h3]
    exact orderOf_injective (MulAut.conj (g : G)).toMonoidHom (MulAut.conj (g : G)).injective a

omit [Finite G] in
theorem pow_val_add_eq {x : G} (hx : x ^ 3 = 1) (a b : ZMod 3) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  rw [← pow_add, ← pow_mod_orderOf x (a.val + b.val)]
  have h3 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx
  rw [ZMod.val_add, ← pow_mod_orderOf x ((a.val + b.val) % 3)]
  congr 1
  exact (Nat.mod_mod_of_dvd _ h3)

theorem three_le_pRank_of_commute {H : Subgroup G} {x y w : G} (hxH : x ∈ H) (hyH : y ∈ H)
    (hwH : w ∈ H) (hxy : x * y = y * x) (hxw : x * w = w * x) (hyw : y * w = w * y)
    (hx : x ^ 3 = 1) (hy : y ^ 3 = 1) (hw : w ^ 3 = 1) (hx1 : x ≠ 1)
    (hyx : y ∉ Subgroup.zpowers x) (hwxy : w ∉ Subgroup.zpowers x ⊔ Subgroup.zpowers y) :
    3 ≤ CFSG.Open.pRank 3 H := by
  have hcxy : Commute x y := hxy
  have hcxw : Commute x w := hxw
  have hcyw : Commute y w := hyw
  let f : Multiplicative (Fin 3 → ZMod 3) → G := fun v =>
    x ^ (Multiplicative.toAdd v 0).val * y ^ (Multiplicative.toAdd v 1).val *
      w ^ (Multiplicative.toAdd v 2).val
  have hf1 : f 1 = 1 := by simp [f]
  have hfmul : ∀ u v, f (u * v) = f u * f v := by
    intro u v
    simp only [f, toAdd_mul, Pi.add_apply]
    rw [pow_val_add_eq hx, pow_val_add_eq hy, pow_val_add_eq hw]
    have h1 := (hcxy.pow_pow (Multiplicative.toAdd v 0).val (Multiplicative.toAdd u 1).val).eq
    have h2 := (hcxw.pow_pow (Multiplicative.toAdd v 0).val (Multiplicative.toAdd u 2).val).eq
    have h3 := (hcyw.pow_pow (Multiplicative.toAdd v 1).val (Multiplicative.toAdd u 2).val).eq
    set a := x ^ (Multiplicative.toAdd u 0).val
    set a' := x ^ (Multiplicative.toAdd v 0).val
    set b := y ^ (Multiplicative.toAdd u 1).val
    set b' := y ^ (Multiplicative.toAdd v 1).val
    set c := w ^ (Multiplicative.toAdd u 2).val
    set c' := w ^ (Multiplicative.toAdd v 2).val
    calc a * a' * (b * b') * (c * c') = a * (a' * b) * b' * c * c' := by group
      _ = a * (b * a') * b' * c * c' := by rw [h1]
      _ = a * b * a' * (b' * c) * c' := by group
      _ = a * b * a' * (c * b') * c' := by rw [h3]
      _ = a * b * (a' * c) * b' * c' := by group
      _ = a * b * (c * a') * b' * c' := by rw [h2]
      _ = a * b * c * (a' * b' * c') := by group
  let φ : Multiplicative (Fin 3 → ZMod 3) →* G :=
    { toFun := f, map_one' := hf1, map_mul' := hfmul }
  have hzp : ∀ {g : G} (hg : g ^ 3 = 1) {k : ℕ} (hk : k < 3) (hk0 : k ≠ 0)
      (S : Subgroup G), g ^ k ∈ S → g ∈ S := by
    intro g hg k hk hk0 S hS
    interval_cases k
    · exact absurd rfl hk0
    · simpa using hS
    · have : g = (g ^ 2) ^ 2 := by
        rw [← pow_mul]
        calc g = g ^ 3 * g := by rw [hg, one_mul]
          _ = g ^ 4 := by rw [← pow_succ]
      rw [this]
      exact S.pow_mem hS 2
  have hinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro v hv
    rw [MonoidHom.mem_ker] at hv
    change x ^ (Multiplicative.toAdd v 0).val * y ^ (Multiplicative.toAdd v 1).val *
      w ^ (Multiplicative.toAdd v 2).val = 1 at hv
    have hw2 : (Multiplicative.toAdd v 2).val = 0 := by
      by_contra hne
      apply hwxy
      refine hzp hw (ZMod.val_lt _) hne _ ?_
      have : w ^ (Multiplicative.toAdd v 2).val =
          (x ^ (Multiplicative.toAdd v 0).val * y ^ (Multiplicative.toAdd v 1).val)⁻¹ :=
        eq_inv_of_mul_eq_one_right hv
      rw [this]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _
        (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _))
        (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) _)))
    rw [hw2, pow_zero, mul_one] at hv
    have hy2 : (Multiplicative.toAdd v 1).val = 0 := by
      by_contra hne
      apply hyx
      refine hzp hy (ZMod.val_lt _) hne _ ?_
      rw [eq_inv_of_mul_eq_one_right hv]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _)
    rw [hy2, pow_zero, mul_one] at hv
    have hx2 : (Multiplicative.toAdd v 0).val = 0 := by
      by_contra hne
      have hord : orderOf x = 3 := orderOf_eq_prime hx hx1
      have := orderOf_dvd_of_pow_eq_one hv
      rw [hord] at this
      have hlt := ZMod.val_lt (Multiplicative.toAdd v 0)
      have hpos : 0 < (Multiplicative.toAdd v 0).val := Nat.pos_of_ne_zero hne
      exact absurd (Nat.le_of_dvd hpos this) (by omega)
    rw [Subgroup.mem_bot]
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact (ZMod.val_eq_zero _).mp hx2
    · exact (ZMod.val_eq_zero _).mp hy2
    · exact (ZMod.val_eq_zero _).mp hw2
  have hE : IsElemAbelian 3 φ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun g hg => ?_⟩
    · obtain ⟨u, hu⟩ := a.2
      obtain ⟨v, hv⟩ := b.2
      apply Subtype.ext
      show (a : G) * b = b * a
      rw [← hu, ← hv, ← map_mul, ← map_mul, mul_comm]
    · obtain ⟨u, rfl⟩ := hg
      rw [← map_pow]
      have : u ^ 3 = 1 := by
        apply Multiplicative.toAdd.injective
        funext i
        simp only [toAdd_pow, Pi.smul_apply, toAdd_one, Pi.zero_apply, nsmul_eq_mul]
        rw [show ((3 : ℕ) : ZMod 3) = 0 by rfl, zero_mul]
      rw [this, map_one]
  have hcard : Nat.card φ.range = 3 ^ 3 := by
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj, Subgroup.card_top,
      Nat.card_eq_fintype_card]
    rfl
  have hle : φ.range ≤ H := by
    rintro _ ⟨v, rfl⟩
    exact H.mul_mem (H.mul_mem (H.pow_mem hxH _) (H.pow_mem hyH _)) (H.pow_mem hwH _)
  exact CFSG.SectionRank.le_pRank (by norm_num) hle hE hcard

structure ThreeComp (J A : Subgroup G) : Prop where
  le : A ≤ J
  normal : J ≤ Subgroup.normalizer (A : Set G)
  gen : A ≤ Subgroup.closure {x | x ∈ A ∧ ∃ k : ℕ, x ^ 3 ^ k = 1}
  simple : ∀ N : Subgroup G, N ≤ A → A ≤ Subgroup.normalizer (N : Set G) →
    N ≤ pCoreOf 2 A ∨ N = A
  exists_three : ∃ a ∈ A, orderOf a = 3
  card_le : ∀ R : Subgroup G, R ≤ A → IsPGroup 3 R → Nat.card R ≤ 3

namespace ThreeComp

variable {J A B : Subgroup G}

theorem pCoreOf_le_pCoreOf (hA : ThreeComp J A) : pCoreOf 2 A ≤ pCoreOf 2 J :=
  F7.pCoreOf_mono_of_le_normalizer hA.le hA.normal

theorem le_of_le_sup (hA : ThreeComp J A) {B : Subgroup G}
    (hJB : J ≤ Subgroup.normalizer (B : Set G))
    (h : A ≤ B ⊔ pCoreOf 2 J) : A ≤ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine hA.gen.trans ((Subgroup.closure_le _).mpr ?_)
  rintro x ⟨hx, k, hk⟩
  exact mem_of_pow_three_eq_one (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J)
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 J).trans hJB) (h hx) hk

theorem inf_le_pCoreOf (hA : ThreeComp J A) (hB : ThreeComp J B) (hne : A ≠ B)
    (hcard : Nat.card A = Nat.card B) : A ⊓ B ≤ pCoreOf 2 A := by
  rcases hA.simple (A ⊓ B) inf_le_left
    (fun a ha => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ha, hB.normal (hA.le ha)⟩) with h | h
  · exact h
  · exfalso
    have hAB : A ≤ B := h ▸ inf_le_right
    exact hne (Subgroup.eq_of_le_of_card_ge hAB hcard.ge)

theorem commutator_mem (hA : ThreeComp J A) (hB : ThreeComp J B) (hne : A ≠ B)
    (hcard : Nat.card A = Nat.card B) {a b : G} (ha : a ∈ A) (hb : b ∈ B) :
    a * b * a⁻¹ * b⁻¹ ∈ pCoreOf 2 J := by
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ A ⊓ B := by
    constructor
    · have : b * a⁻¹ * b⁻¹ ∈ A :=
        (Subgroup.mem_normalizer_iff.mp (hA.normal (hB.le hb)) _).mp (A.inv_mem ha)
      have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
      rw [e]
      exact A.mul_mem ha this
    · have : a * b * a⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hB.normal (hA.le ha)) b).mp hb
      exact B.mul_mem this (B.inv_mem hb)
  exact hA.pCoreOf_le_pCoreOf (hA.inf_le_pCoreOf hB hne hcard h1)

omit [Finite G] in
theorem conj (hA : ThreeComp J A) {g : G} (hg : g ∈ Subgroup.normalizer (J : Set G)) :
    ThreeComp J (conjSub g A) := by
  have hgJ : conjSub g J = J := conjSub_eq_of_mem_normalizer' hg
  have hgJ' : conjSub g⁻¹ J = J := conjSub_eq_of_mem_normalizer' (Subgroup.inv_mem _ hg)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := conjSub_mono g hA.le
    rwa [hgJ] at this
  · intro j hj
    rw [conjSub_normalizer]
    refine mem_conjSub.mpr (hA.normal ?_)
    have : g⁻¹ * j * g ∈ conjSub g⁻¹ J := by
      rw [mem_conjSub, inv_inv]
      simpa [mul_assoc] using hj
    rwa [hgJ'] at this
  · intro x hx
    obtain ⟨a, ha, rfl⟩ := hx
    have hle : Subgroup.closure {x | x ∈ A ∧ ∃ k : ℕ, x ^ 3 ^ k = 1} ≤
        (Subgroup.closure {x | x ∈ conjSub g A ∧ ∃ k : ℕ, x ^ 3 ^ k = 1}).comap
          (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro y ⟨hy, k, hk⟩
      refine Subgroup.subset_closure ⟨⟨y, hy, rfl⟩, k, ?_⟩
      rw [← map_pow, hk, map_one]
    exact hle (hA.gen ha)
  · intro N hN hAN
    have hN' : conjSub g⁻¹ N ≤ A := by
      have := conjSub_mono g⁻¹ hN
      rwa [conjSub_conjSub_inv] at this
    have hAN' : A ≤ Subgroup.normalizer (conjSub g⁻¹ N : Set G) := by
      have := conjSub_mono g⁻¹ hAN
      rwa [conjSub_conjSub_inv, ← conjSub_normalizer] at this
    rcases hA.simple _ hN' hAN' with h | h
    · left
      have := conjSub_mono g h
      rwa [conjSub_inv_conjSub, ← pCoreOf_conjSub] at this
    · right
      have := congrArg (conjSub g) h
      rwa [conjSub_inv_conjSub] at this
  · obtain ⟨a, ha, h3⟩ := hA.exists_three
    refine ⟨g * a * g⁻¹, ⟨a, ha, rfl⟩, ?_⟩
    rw [← h3]
    exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective a
  · intro R hR hR3
    have hR' : conjSub g⁻¹ R ≤ A := by
      have := conjSub_mono g⁻¹ hR
      rwa [conjSub_conjSub_inv] at this
    have := hA.card_le _ hR' (hR3.map _)
    rwa [card_conjSub'] at this

theorem commutator_mem_of_ne (hB : ThreeComp J B) (hne : B ≠ A)
    (hcard : Nat.card B = Nat.card A) {P : Subgroup G}
    (hJP : J ≤ Subgroup.normalizer (P : Set G))
    (hP3 : ∀ x ∈ P, ∀ k : ℕ, x ^ 3 ^ k = 1 → x ∈ A) (hPJ : P ≤ J) {b p : G} (hb : b ∈ B)
    (hp : p ∈ P) : b * p * b⁻¹ * p⁻¹ ∈ pCoreOf 2 J := by
  have hBP : B ⊓ P ≤ pCoreOf 2 B := by
    rcases hB.simple (B ⊓ P) inf_le_left (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx, hJP (hB.le hx)⟩) with h | h
    · exact h
    · exfalso
      have hBP' : B ≤ P := inf_eq_left.mp h
      have hBA : B ≤ A := hB.gen.trans ((Subgroup.closure_le _).mpr fun x hx =>
        hP3 x (hBP' hx.1) hx.2.choose hx.2.choose_spec)
      exact hne (Subgroup.eq_of_le_of_card_ge hBA hcard.symm.le)
  have h1 : b * p * b⁻¹ * p⁻¹ ∈ B ⊓ P := by
    constructor
    · have : p * b⁻¹ * p⁻¹ ∈ B :=
        (Subgroup.mem_normalizer_iff.mp (hB.normal (hPJ hp)) _).mp (B.inv_mem hb)
      have e : b * p * b⁻¹ * p⁻¹ = b * (p * b⁻¹ * p⁻¹) := by group
      rw [e]
      exact B.mul_mem hb this
    · have : b * p * b⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hJP (hB.le hb)) p).mp hp
      exact P.mul_mem this (P.inv_mem hp)
  exact hB.pCoreOf_le_pCoreOf (hBP h1)

theorem conjSub_eq_of_pRank (hrk : CFSG.Open.pRank 3 J ≤ 2) (hA : ThreeComp J A)
    {P : Subgroup G} (hPJ : P ≤ J) (hJP : J ≤ Subgroup.normalizer (P : Set G))
    (hP3 : ∀ x ∈ P, ∀ k : ℕ, x ^ 3 ^ k = 1 → x ∈ A)
    (hwit : ∃ e ∈ P, ∃ a ∈ A, e * a * e⁻¹ * a⁻¹ ∉ pCoreOf 2 J)
    {d : G} (hdJ : d ∈ Subgroup.normalizer (J : Set G)) (hd3 : d ^ 3 = 1) :
    conjSub d A = A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  set A₁ := conjSub d A with hA₁def
  set A₂ := conjSub d A₁ with hA₂def
  have hA₁ := hA.conj hdJ
  have hA₂ := hA₁.conj hdJ
  have hc₁ : Nat.card A₁ = Nat.card A := card_conjSub' _ _
  have hc₂ : Nat.card A₂ = Nat.card A := by rw [hA₂def, card_conjSub', hc₁]
  have hdd : d * d = d⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_two, ← pow_succ, hd3]
  have hA₂eq : A₂ = conjSub d⁻¹ A := by
    rw [hA₂def, hA₁def, ← conjSub_mul, hdd]
  have hne01 : A ≠ A₁ := fun h => hne h.symm
  have hne12 : A₁ ≠ A₂ := by
    intro h
    apply hne
    have := congrArg (conjSub d⁻¹) h
    rw [hA₂def, conjSub_conjSub_inv, hA₁def, conjSub_conjSub_inv] at this
    exact this.symm
  have hne02 : A ≠ A₂ := by
    intro h
    apply hne
    rw [hA₂eq] at h
    have := congrArg (conjSub d) h
    rw [conjSub_inv_conjSub] at this
    exact this
  have hO2 : IsPGroup 2 (pCoreOf 2 J) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 J
  have hJO : J ≤ Subgroup.normalizer (pCoreOf 2 J : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 J
  by_cases hind : A₂ ⊓ (A ⊔ A₁ ⊔ pCoreOf 2 J) ≤ pCoreOf 2 A₂
  ·
    apply absurd hrk
    push Not
    set X := A ⊔ A₁ ⊔ A₂ with hX
    have hXJ : X ≤ J := sup_le (sup_le hA.le hA₁.le) hA₂.le
    obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow 3 ↥X))
    have hR3 : IsPGroup 3 ((R : Subgroup ↥X).map X.subtype) := R.2.map _
    obtain ⟨a₀, -, ha₀⟩ := hA.exists_three
    obtain ⟨a₁, -, ha₁⟩ := hA₁.exists_three
    obtain ⟨a₂, -, ha₂⟩ := hA₂.exists_three
    obtain ⟨x₀, hx₀A, hx₀R, hx₀3⟩ := exists_mem_sylow_of_orderOf
      (le_sup_left.trans le_sup_left) (hXJ.trans hA.normal) R (hA.exists_three.choose_spec.1)
      hA.exists_three.choose_spec.2
    obtain ⟨x₁, hx₁A, hx₁R, hx₁3⟩ := exists_mem_sylow_of_orderOf
      (le_sup_right.trans le_sup_left) (hXJ.trans hA₁.normal) R
      (hA₁.exists_three.choose_spec.1) hA₁.exists_three.choose_spec.2
    obtain ⟨x₂, hx₂A, hx₂R, hx₂3⟩ := exists_mem_sylow_of_orderOf le_sup_right
      (hXJ.trans hA₂.normal) R (hA₂.exists_three.choose_spec.1) hA₂.exists_three.choose_spec.2
    have hcommute : ∀ {u v : G}, u ∈ (R : Subgroup ↥X).map X.subtype →
        v ∈ (R : Subgroup ↥X).map X.subtype → u * v * u⁻¹ * v⁻¹ ∈ pCoreOf 2 J → u * v = v * u := by
      intro u v hu hv huv
      have h1 := eq_one_of_isPGroup_three_two hR3 hO2
        (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hu hv)
          (Subgroup.inv_mem _ hu)) (Subgroup.inv_mem _ hv)) huv
      calc u * v = u * v * u⁻¹ * v⁻¹ * (v * u) := by group
        _ = v * u := by rw [h1, one_mul]
    have h01 := hcommute hx₀R hx₁R (hA.commutator_mem hA₁ hne01 hc₁.symm hx₀A hx₁A)
    have h02 := hcommute hx₀R hx₂R (hA.commutator_mem hA₂ hne02 hc₂.symm hx₀A hx₂A)
    have h12 := hcommute hx₁R hx₂R (hA₁.commutator_mem hA₂ hne12 (by rw [hc₁, hc₂]) hx₁A hx₂A)
    have hpow : ∀ {u : G}, orderOf u = 3 → u ^ 3 = 1 := fun h => h ▸ pow_orderOf_eq_one _
    have hord1 : ∀ {u : G} {O : Subgroup G}, IsPGroup 2 O → u ∈ O → orderOf u = 3 → False := by
      intro u O hO hu h3
      obtain ⟨b, hb⟩ := hO ⟨u, hu⟩
      have hb' : u ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
      have := orderOf_dvd_of_pow_eq_one hb'
      rw [h3] at this
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three this)
      omega
    have hx₁ : x₁ ∉ Subgroup.zpowers x₀ := by
      intro h
      have hx₁A' : x₁ ∈ A := Subgroup.zpowers_le.mpr hx₀A h
      exact hord1 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A)
        (hA.inf_le_pCoreOf hA₁ hne01 hc₁.symm ⟨hx₁A', hx₁A⟩) hx₁3
    have hx₂ : x₂ ∉ Subgroup.zpowers x₀ ⊔ Subgroup.zpowers x₁ := by
      intro h
      have hle : Subgroup.zpowers x₀ ⊔ Subgroup.zpowers x₁ ≤ A ⊔ A₁ ⊔ pCoreOf 2 J :=
        sup_le ((Subgroup.zpowers_le.mpr hx₀A).trans (le_sup_left.trans le_sup_left))
          ((Subgroup.zpowers_le.mpr hx₁A).trans (le_sup_right.trans le_sup_left))
      exact hord1 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 A₂) (hind ⟨hx₂A, hle h⟩) hx₂3
    have hx₀1 : x₀ ≠ 1 := fun h => by rw [h, orderOf_one] at hx₀3; omega
    have hAX : A ≤ X := le_sup_left.trans le_sup_left
    have hA₁X : A₁ ≤ X := le_sup_right.trans le_sup_left
    have hA₂X : A₂ ≤ X := le_sup_right
    have := three_le_pRank_of_commute (hXJ (hAX hx₀A)) (hXJ (hA₁X hx₁A)) (hXJ (hA₂X hx₂A)) h01
      h02 h12 (hpow hx₀3) (hpow hx₁3) (hpow hx₂3) hx₀1 hx₁ hx₂
    omega
  ·
    have hN₁ : A₂ ≤ Subgroup.normalizer ((A ⊔ A₁ ⊔ pCoreOf 2 J : Subgroup G) : Set G) :=
      fun x hx => mem_normalizer_sup (mem_normalizer_sup (hA.normal (hA₂.le hx))
        (hA₁.normal (hA₂.le hx))) (hJO (hA₂.le hx))
    have hle : A₂ ≤ A ⊔ A₁ ⊔ pCoreOf 2 J := by
      rcases hA₂.simple (A₂ ⊓ (A ⊔ A₁ ⊔ pCoreOf 2 J)) inf_le_left
        (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hx, hN₁ hx⟩) with h | h
      · exact absurd h hind
      · exact inf_eq_left.mp h
    have hN₂ : A ≤ Subgroup.normalizer ((A₁ ⊔ A₂ ⊔ pCoreOf 2 J : Subgroup G) : Set G) :=
      fun x hx => mem_normalizer_sup (mem_normalizer_sup (hA₁.normal (hA.le hx))
        (hA₂.normal (hA.le hx))) (hJO (hA.le hx))
    rcases hA.simple (A ⊓ (A₁ ⊔ A₂ ⊔ pCoreOf 2 J)) inf_le_left
      (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx, hN₂ hx⟩) with h | h
    ·
      apply hne12
      have hA₂le : A₂ ≤ A₁ ⊔ pCoreOf 2 J := by
        intro x hx
        have hx' : x ∈ ((A ⊔ (A₁ ⊔ pCoreOf 2 J) : Subgroup G) : Set G) := by
          rw [← sup_assoc]
          exact hle hx
        rw [Subgroup.coe_mul_of_right_le_normalizer_left A (A₁ ⊔ pCoreOf 2 J)
          (sup_le (hA₁.le.trans hA.normal) ((CFSG.LieType.BorelTits.pCoreOf_le 2 J).trans
            hA.normal))] at hx'
        obtain ⟨a, ha, y, hy, rfl⟩ := hx'
        have haN : a ∈ A ⊓ (A₁ ⊔ A₂ ⊔ pCoreOf 2 J) := by
          refine ⟨ha, ?_⟩
          have e : a = (a * y) * y⁻¹ := by group
          rw [e]
          refine Subgroup.mul_mem _ ?_ ?_
          · exact Subgroup.mem_sup_left (Subgroup.mem_sup_right hx)
          · have hy' : y⁻¹ ∈ A₁ ⊔ pCoreOf 2 J := Subgroup.inv_mem _ hy
            exact (sup_le (le_sup_left.trans le_sup_left) le_sup_right :
              A₁ ⊔ pCoreOf 2 J ≤ A₁ ⊔ A₂ ⊔ pCoreOf 2 J) hy'
        have haO : a ∈ pCoreOf 2 J := hA.pCoreOf_le_pCoreOf (h haN)
        show a * y ∈ A₁ ⊔ pCoreOf 2 J
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_right haO) hy
      have := hA₂.le_of_le_sup hA₁.normal hA₂le
      exact (Subgroup.eq_of_le_of_card_ge this (by rw [hc₁, hc₂])).symm
    ·
      obtain ⟨e, he, a, ha, hea⟩ := hwit
      apply hea
      let C : Subgroup G := centralizerMod (pCoreOf 2 J) ⊤ (Subgroup.zpowers e)
      have hzp : Subgroup.zpowers e ≤ P := Subgroup.zpowers_le.mpr he
      have hB : ∀ {B : Subgroup G}, ThreeComp J B → B ≠ A → Nat.card B = Nat.card A → B ≤ C := by
        intro B hB hBA hBc x hx
        refine ⟨trivial, hJO (hB.le hx), fun u hu => ?_⟩
        exact hB.commutator_mem_of_ne hBA hBc hJP hP3 hPJ hx (hzp hu)
      have hOC : pCoreOf 2 J ≤ C := by
        intro x hx
        refine ⟨trivial, hJO ((CFSG.LieType.BorelTits.pCoreOf_le 2 J) hx), fun u hu => ?_⟩
        have hu' : u * x⁻¹ * u⁻¹ ∈ pCoreOf 2 J :=
          (Subgroup.mem_normalizer_iff.mp (hJO (hPJ (hzp hu))) _).mp (Subgroup.inv_mem _ hx)
        have e1 : x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) := by group
        rw [e1]
        exact Subgroup.mul_mem _ hx hu'
      have hAC : A ≤ C := (inf_eq_left.mp h : A ≤ A₁ ⊔ A₂ ⊔ pCoreOf 2 J).trans
        (sup_le (sup_le (hB hA₁ (Ne.symm hne01) hc₁) (hB hA₂ (Ne.symm hne02) hc₂)) hOC)
      have h1 := (hAC ha).2.2 e (Subgroup.mem_zpowers e)
      have h2 := Subgroup.inv_mem _ h1
      have e2 : (a * e * a⁻¹ * e⁻¹)⁻¹ = e * a * e⁻¹ * a⁻¹ := by group
      rwa [e2] at h2

end ThreeComp

end CFSG.Quasithin.H13.L619
