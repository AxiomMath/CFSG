module

public import CFSG.Quasithin.H13.A5S136ab1
public import CFSG.Quasithin.H13.A5W1620Tb
public import CFSG.Quasithin.H13.A5S1519
public import CFSG.Quasithin.H13.A5S1328Blk2

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

namespace ConfAB

theorem alt6_pow_eq_one : ∀ σ : alternatingGroup (Fin 6),
    σ ^ 2 = 1 ∨ σ ^ 3 = 1 ∨ σ ^ 4 = 1 ∨ σ ^ 5 = 1 := by decide +kernel

theorem eq_one_of_commute_of_alt6 {K : Type*} [Group K] (e : K ≃* alternatingGroup (Fin 6))
    {y x : K} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1) {k : ℕ} (hx : x ^ 2 ^ k = 1)
    (hxy : Commute x y) : x = 1 := by
  have hoy : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hx)
  have hcop : (orderOf x).Coprime (orderOf y) := by
    rw [hj, hoy]
    exact Nat.Coprime.pow_left _ (by norm_num)
  have hw : orderOf (e (x * y)) = 2 ^ j * 3 := by
    rw [MulEquiv.orderOf_eq, hxy.orderOf_mul_eq_mul_orderOf_of_coprime hcop, hj, hoy]
  have hle : 2 ^ j * 3 ≤ 5 := by
    rcases alt6_pow_eq_one (e (x * y)) with h | h | h | h <;>
    · have hd := orderOf_dvd_of_pow_eq_one h
      rw [hw] at hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
  have h1 : 2 ^ j = 1 := by
    have := Nat.one_le_two_pow (n := j)
    omega
  rw [← orderOf_eq_one_iff, hj, h1]

theorem card_modEq_one_of_fixed {G : Type} [Group G] [Finite G] {P : Subgroup G} {y : G}
    (hyN : y ∈ Subgroup.normalizer (P : Set G)) (hy3 : y ^ 3 = 1)
    (hfix : ∀ x ∈ P, x * y = y * x → x = 1) : Nat.card P ≡ 1 [MOD 3] := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let n : ↥(Subgroup.normalizer (P : Set G)) := ⟨y, hyN⟩
  let H : Subgroup ↥(Subgroup.normalizer (P : Set G)) := Subgroup.zpowers n
  let _ : MulAction ↥(Subgroup.normalizer (P : Set G)) ↥P :=
    MulAction.compHom ↥P P.normalizerMonoidHom
  have hn3 : n ^ 3 = 1 := Subtype.ext (by simpa [n] using hy3)
  have hH : IsPGroup 3 ↥H := by
    intro h
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, Subgroup.coe_pow, ← hi, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hn3, one_zpow]
    rfl
  have hfp : MulAction.fixedPoints ↥H ↥P = {1} := by
    ext x
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro hx
      have h1 := hx ⟨n, Subgroup.mem_zpowers n⟩
      have h2 : y * x * y⁻¹ = x := congrArg Subtype.val h1
      apply Subtype.ext
      refine hfix x x.2 ?_
      calc (x : G) * y = y * x * y⁻¹ * y := by rw [h2]
        _ = y * x := by group
    · rintro rfl h
      exact map_one (P.normalizerMonoidHom (h : ↥(Subgroup.normalizer (P : Set G))))
  have hmod := hH.card_modEq_card_fixedPoints ↥P
  rw [hfp] at hmod
  simpa using hmod

theorem eq_one_of_pow_two_pow_of_odd {X : Type*} [Monoid X] {a : X} {k m : ℕ}
    (hk : a ^ 2 ^ k = 1) (hm : a ^ m = 1) (hodd : Odd m) : a = 1 := by
  have hcop : Nat.Coprime (2 ^ k) m := Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one hm)
  rw [Nat.Coprime.gcd_eq_one hcop] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)

theorem two_pow_eq_one_or_four {n : ℕ} (hn : n ≤ 3) (hmod : 2 ^ n ≡ 1 [MOD 3]) :
    2 ^ n = 1 ∨ 2 ^ n = 4 := by
  have key : ∀ m ≤ 3, 2 ^ m % 3 = 1 % 3 → 2 ^ m = 1 ∨ 2 ^ m = 4 := by decide
  exact key n hn hmod

theorem eq_four_of_dvd_four {c : ℕ} (hdvd : c ∣ 4) (hmod : c ≡ 1 [MOD 3]) (h1 : c ≠ 1) :
    c = 4 := by
  have key : ∀ d ≤ 4, d ∣ 4 → d % 3 = 1 % 3 → d ≠ 1 → d = 4 := by decide
  exact key c (Nat.le_of_dvd (by norm_num) hdvd) hdvd hmod h1

end ConfAB

namespace Setting

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem pCoreOf_Gv_ne_bot' : pCoreOf 2 (Subgroup.centralizer ({S.v12} : Set G)) ≠ ⊥ := by
  have hvO : S.v12 ∈ pCoreOf 2 (Subgroup.centralizer ({S.v12} : Set G)) := by
    have hle : Subgroup.zpowers S.v12 ≤ Subgroup.centralizer ({S.v12} : Set G) :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
    have hN : Subgroup.centralizer ({S.v12} : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers S.v12 : Set G) := by
      intro g hgG
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ((Commute.zpow_left (Subgroup.mem_centralizer_singleton_iff.mp hgG).symm k).eq)
    have h2 : IsPGroup 2 (Subgroup.zpowers S.v12) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      exact orderOf_eq_prime (S.elemAbelian_V.2 _ S.v12_mem_V) S.v12_ne_one
    exact le_pCoreOf_of_normalizes hle hN h2 (Subgroup.mem_zpowers _)
  intro h
  rw [h, Subgroup.mem_bot] at hvO
  exact S.v12_ne_one hvO

theorem Lv_le_of_exclusion_quot (hF318 : A318Facts) (h36 : A36ForSQTK)
    (h38 : Vol2Native.A38ForSQTKCat) {K : Subgroup G}
    (hK : K ∈ cComp (Subgroup.centralizer ({S.v12} : Set G)))
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) {X : Type} [Group X] [Finite X]
    (e : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* X) (hX : A318Exclusion X) : S.Lv ≤ K := by
  have hGv : SQTKGroup ↥(Subgroup.centralizer ({S.v12} : Set G)) :=
    sqtkGroup_of_pCoreOf_ne_bot S.h13.qtke S.h13.simple S.h13.nonabelian S.pCoreOf_Gv_ne_bot'
  refine S.Lv_le_of_eq_oPrime_or_theta (Or.inl ?_)
  exact eq_oPrimeResidualOf_three_of_exclusion hF318 h36 (a38ForSQTK_of_cat h38) hGv hK hq e hX

theorem pCoreOf_L_le_pCoreOf_LT : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left)
    (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
      (S.T_le_NL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)

omit S in
theorem inf_pCoreOf_LT_le : L ⊓ pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 L :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
    (fun _ hl => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hl,
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T) (Subgroup.mem_sup_left hl)⟩)
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T)).to_le inf_le_right)

theorem pCoreOf_L_le_centralizer_V : pCoreOf 2 L ≤ Subgroup.centralizer (V : Set G) :=
  S.pCoreOf_L_le_pCoreOf_LT.trans (S.cLT ▸ inf_le_right)

theorem pCoreOf_L_le_normalizer_Lv : pCoreOf 2 L ≤ Subgroup.normalizer (S.Lv : Set G) := by
  refine le_normalizer_oTwoRes fun u hu => ?_
  have huL : u ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hu
  have huG : u ∈ Subgroup.centralizer ({S.v12} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (S.pCoreOf_L_le_centralizer_V hu) S.v12
      S.v12_mem_V).symm
  set Gv := Subgroup.centralizer ({S.v12} : Set G)
  refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
  · exact ⟨L.mul_mem (L.mul_mem huL hx.1) (L.inv_mem huL),
      Gv.mul_mem (Gv.mul_mem huG hx.2) (Gv.inv_mem huG)⟩
  · exact ⟨L.mul_mem (L.mul_mem (L.inv_mem huL) hx.1) huL,
      Gv.mul_mem (Gv.mul_mem (Gv.inv_mem huG) hx.2) huG⟩

theorem commutator_pCoreOf_L_le_V {K : Subgroup G} (hLvK : S.Lv ≤ K)
    (e : ↥K ≃* alternatingGroup (Fin 6)) : ⁅pCoreOf 2 L, L⁆ ≤ V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 L with hQdef
  have hQL : Q ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hLv : S.Lv ≤ L ⊓ Subgroup.centralizer ({S.v12} : Set G) := by
    rw [Lv, oTwoRes_eq_oTwoUpper]
    exact oTwoUpper_le _
  obtain ⟨l₀, hl₀L, hl₀σ⟩ := (S.frame.image_L c234).2 c234_sign
  have hl₀ : (l₀ : G) ∈ L ⊓ Subgroup.centralizer ({S.v12} : Set G) :=
    ⟨hl₀L, S.mem_centralizer_v12 l₀ (by rw [hl₀σ]; exact pact_c234_E12)⟩
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper _ hl₀
  rw [← oTwoRes_eq_oTwoUpper] at hk
  set g : ↥(Subgroup.normalizer (V : Set G)) := l₀ ^ 2 ^ k with hgdef
  set y : G := (g : G) with hydef
  have hyLv : y ∈ S.Lv := by
    have hk' : (l₀ : G) ^ 2 ^ k ∈ S.Lv := hk
    simpa [hydef, hgdef] using hk'
  have hρg : S.frame.ρ g = c234 ∨ S.frame.ρ g = c234⁻¹ := by
    rw [hgdef, map_pow, hl₀σ]
    exact c234_pow_two_pow k
  have hc : c234 ≠ 1 ∧ c234⁻¹ ≠ 1 ∧ c234 ^ 2 ≠ 1 ∧ c234⁻¹ ^ 2 ≠ 1 ∧ c234 ^ 4 ≠ 1 ∧
      c234⁻¹ ^ 4 ≠ 1 ∧ c234 ^ 5 ≠ 1 ∧ c234⁻¹ ^ 5 ≠ 1 := by decide
  have hρpow : ∀ j : ℕ, y ^ j = 1 → S.frame.ρ g ^ j = 1 := fun j hj => by
    have h1 : g ^ j = 1 := Subtype.ext (by simpa [hydef] using hj)
    rw [← map_pow, h1, map_one]
  have hyL : y ∈ L := (hLv hyLv).1
  have hyK : y ∈ K := hLvK hyLv
  have hy1 : y ≠ 1 := by
    intro h
    have := hρpow 1 (by rw [pow_one, h])
    rw [pow_one] at this
    rcases hρg with h' | h' <;> rw [h'] at this
    · exact hc.1 this
    · exact hc.2.1 this
  have hy3 : y ^ 3 = 1 := by
    have hK : ∀ j : ℕ, (⟨y, hyK⟩ : ↥K) ^ j = 1 → y ^ j = 1 := fun j hj => by
      simpa using congrArg Subtype.val hj
    rcases ConfAB.alt6_pow_eq_one (e ⟨y, hyK⟩) with h | h | h | h
    · exfalso
      have := hρpow 2 (hK 2 (e.injective (by rw [map_pow, h, map_one])))
      rcases hρg with h' | h' <;> rw [h'] at this
      · exact hc.2.2.1 this
      · exact hc.2.2.2.1 this
    · exact hK 3 (e.injective (by rw [map_pow, h, map_one]))
    · exfalso
      have := hρpow 4 (hK 4 (e.injective (by rw [map_pow, h, map_one])))
      rcases hρg with h' | h' <;> rw [h'] at this
      · exact hc.2.2.2.2.1 this
      · exact hc.2.2.2.2.2.1 this
    · exfalso
      have := hρpow 5 (hK 5 (e.injective (by rw [map_pow, h, map_one])))
      rcases hρg with h' | h' <;> rw [h'] at this
      · exact hc.2.2.2.2.2.2.1 this
      · exact hc.2.2.2.2.2.2.2 this
  have hfixK : ∀ x ∈ K, (∃ j : ℕ, x ^ 2 ^ j = 1) → x * y = y * x → x = 1 := by
    rintro x hxK ⟨j, hj⟩ hxy
    have h1 := ConfAB.eq_one_of_commute_of_alt6 e (y := ⟨y, hyK⟩) (x := ⟨x, hxK⟩)
      (Subtype.ext (by simpa using hy3)) (fun h => hy1 (by simpa using congrArg Subtype.val h))
      (k := j) (Subtype.ext (by simpa using hj)) (Subtype.ext hxy)
    simpa using congrArg Subtype.val h1
  have hQpow : ∀ x ∈ Q, ∃ j : ℕ, x ^ 2 ^ j = 1 := fun x hx => by
    obtain ⟨j, hj⟩ := hQ2 ⟨x, hx⟩
    exact ⟨j, by simpa using congrArg Subtype.val hj⟩
  set P := Q ⊓ S.Lv with hPdef
  have hPK : P ≤ K := inf_le_right.trans hLvK
  have hyNP : y ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hLQ hyL, Subgroup.le_normalizer hyLv⟩
  have hcardP : Nat.card P ≡ 1 [MOD 3] :=
    ConfAB.card_modEq_one_of_fixed hyNP hy3 fun x hx hxy =>
      hfixK x (hPK hx) (hQpow x hx.1) hxy
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hQ2.to_le (inf_le_left : P ≤ Q))
  have h360 : Nat.card P ∣ 360 := by
    have h1 : Nat.card P ∣ Nat.card K := Subgroup.card_dvd_of_le hPK
    rwa [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin] at h1
  have hn3 : n ≤ 3 := by
    by_contra hlt
    have h16 : 2 ^ 4 ∣ Nat.card P := hn ▸ pow_dvd_pow 2 (by omega)
    have := h16.trans h360
    omega
  have hP4 : Nat.card P = 1 ∨ Nat.card P = 4 := by
    rw [hn] at hcardP ⊢
    exact ConfAB.two_pow_eq_one_or_four hn3 hcardP
  set R := P ⊓ V with hRdef
  have hRP : R ≤ P := inf_le_left
  have hyNR : y ∈ Subgroup.normalizer (R : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hyNP, S.frame.L_le hyL⟩
  have hcardR : Nat.card R ≡ 1 [MOD 3] :=
    ConfAB.card_modEq_one_of_fixed hyNR hy3 fun x hx hxy =>
      hfixK x (hPK hx.1) (hQpow x hx.1.1) hxy
  obtain ⟨v', hv'V, hv'y⟩ : ∃ v' ∈ V, v' * y * v'⁻¹ * y⁻¹ ≠ 1 := by
    by_contra hall
    push Not at hall
    have hC : y ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      calc v * y = (v * y * v⁻¹ * y⁻¹) * y * v := by group
        _ = y * v := by rw [hall v hv, one_mul]
    have h1 := S.frame.rho_eq_one_of_mem g hC
    rcases hρg with h' | h' <;> rw [h'] at h1
    · exact hc.1 h1
    · exact hc.2.1 h1
  have hcR : v' * y * v'⁻¹ * y⁻¹ ∈ R := by
    have hv'Q : v' ∈ Q := S.V_le_pCoreOf_L hv'V
    have e1 : v' * y * v'⁻¹ * y⁻¹ = v' * (y * v'⁻¹ * y⁻¹) := by group
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [e1]
      exact Q.mul_mem hv'Q ((Subgroup.mem_normalizer_iff.mp (hLQ hyL) _).mp (Q.inv_mem hv'Q))
    · exact S.Lv.mul_mem ((Subgroup.mem_normalizer_iff.mp (S.V_le_normalizer_Lv hv'V) y).mp
        hyLv) (S.Lv.inv_mem hyLv)
    · rw [e1]
      exact V.mul_mem hv'V
        ((Subgroup.mem_normalizer_iff.mp (S.frame.L_le hyL) _).mp (V.inv_mem hv'V))
  have hR1 : Nat.card R ≠ 1 := by
    intro h
    have h1 := Subgroup.eq_bot_of_card_eq R h
    rw [h1] at hcR
    exact hv'y (Subgroup.mem_bot.mp hcR)
  have hRdvd : Nat.card R ∣ Nat.card P := Subgroup.card_dvd_of_le hRP
  have hP4' : Nat.card P = 4 := by
    rcases hP4 with h | h
    · rw [h, Nat.dvd_one] at hRdvd
      exact absurd hRdvd hR1
    · exact h
  have hR4 : Nat.card R = 4 :=
    ConfAB.eq_four_of_dvd_four (hP4' ▸ hRdvd) hcardR hR1
  have hPV : P ≤ V := by
    have hRP' : R = P := Subgroup.eq_of_le_of_card_ge hRP (by rw [hR4, hP4'])
    rw [← hRP']
    exact inf_le_right
  have hQy : ∀ q ∈ Q, q * y * q⁻¹ * y⁻¹ ∈ V := by
    intro q hq
    refine hPV ⟨?_, ?_⟩
    · have e1 : q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) := by group
      rw [e1]
      exact Q.mul_mem hq ((Subgroup.mem_normalizer_iff.mp (hLQ hyL) _).mp (Q.inv_mem hq))
    · exact S.Lv.mul_mem ((Subgroup.mem_normalizer_iff.mp (S.pCoreOf_L_le_normalizer_Lv hq)
        y).mp hyLv) (S.Lv.inv_mem hyLv)
  have hVN : ∀ a ∈ L, ∀ w ∈ V, a * w * a⁻¹ ∈ V := fun a ha w hw =>
    (Subgroup.mem_normalizer_iff.mp (S.frame.L_le ha) w).mp hw
  have hQN : ∀ a ∈ L, ∀ q ∈ Q, a⁻¹ * q * a ∈ Q := fun a ha q hq => by
    have := (Subgroup.mem_normalizer_iff.mp (hLQ (L.inv_mem ha)) q).mp hq
    simpa using this
  let C : Subgroup G :=
    { carrier := {x | x ∈ L ∧ ∀ q ∈ Q, q * x * q⁻¹ * x⁻¹ ∈ V}
      one_mem' := ⟨L.one_mem, fun q _ => by simp⟩
      mul_mem' := by
        rintro a b ⟨haL, ha⟩ ⟨hbL, hb⟩
        refine ⟨L.mul_mem haL hbL, fun q hq => ?_⟩
        have e1 : q * (a * b) * q⁻¹ * (a * b)⁻¹ =
            (q * a * q⁻¹ * a⁻¹) * (a * (q * b * q⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e1]
        exact V.mul_mem (ha q hq) (hVN a haL _ (hb q hq))
      inv_mem' := by
        rintro a ⟨haL, ha⟩
        refine ⟨L.inv_mem haL, fun q hq => ?_⟩
        have e1 : q * a⁻¹ * q⁻¹ * a⁻¹⁻¹ =
            ((a⁻¹ * q * a) * a * (a⁻¹ * q * a)⁻¹ * a⁻¹)⁻¹ := by group
        rw [e1]
        exact V.inv_mem (ha _ (hQN a haL q hq)) }
  have hCL : C ≤ L := fun x hx => hx.1
  have hyC : y ∈ C := ⟨hyL, hQy⟩
  have hLNC : L ≤ Subgroup.normalizer (C : Set G) := by
    intro a ha
    have key : ∀ b ∈ L, ∀ x ∈ C, b * x * b⁻¹ ∈ C := by
      rintro b hb x ⟨hxL, hx⟩
      refine ⟨L.mul_mem (L.mul_mem hb hxL) (L.inv_mem hb), fun q hq => ?_⟩
      have e1 : q * (b * x * b⁻¹) * q⁻¹ * (b * x * b⁻¹)⁻¹ =
          b * ((b⁻¹ * q * b) * x * (b⁻¹ * q * b)⁻¹ * x⁻¹) * b⁻¹ := by group
      rw [e1]
      exact hVN b hb _ (hx _ (hQN b hb q hq))
    refine B6.mem_normalizer_of_forall_mem (key a ha) fun x hx => ?_
    simpa using key a⁻¹ (L.inv_mem ha) x hx
  obtain ⟨φ, hφ, hker⟩ := S.exists_alt5
  have hCn : (C.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCL).mpr hLNC
  have himage : (C.subgroupOf L).map φ = ⊤ := by
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    have := hCn.map φ hφ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((C.subgroupOf L).map φ) with h | h
    · exfalso
      have h1 : φ ⟨y, hyL⟩ ∈ (C.subgroupOf L).map φ := ⟨⟨y, hyL⟩, hyC, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      have h2 : (⟨y, hyL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
        rw [← hker]
        exact h1
      have hyQ : y ∈ Q := (AppC.mem_pCore_iff_mem_blockQ _).mp h2
      obtain ⟨j, hj⟩ := hQpow y hyQ
      exact hy1 (ConfAB.eq_one_of_pow_two_pow_of_odd hj hy3 (by decide))
    · exact h
  have hLle : L ≤ C ⊔ Q := by
    intro x hx
    obtain ⟨c, hc, hcx⟩ : φ ⟨x, hx⟩ ∈ (C.subgroupOf L).map φ := by
      rw [himage]
      exact Subgroup.mem_top _
    have hck : c⁻¹ * ⟨x, hx⟩ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcx, inv_mul_cancel]
    rw [hker] at hck
    have hq : ((c⁻¹ * ⟨x, hx⟩ : ↥L) : G) ∈ Q := (AppC.mem_pCore_iff_mem_blockQ _).mp hck
    have e1 : x = (c : G) * ((c⁻¹ * ⟨x, hx⟩ : ↥L) : G) := by simp
    rw [e1]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right hq)
  have hLC : L ≤ C := by
    have heq : C ⊔ Q = L := le_antisymm (sup_le hCL hQL) hLle
    calc L = oTwoRes L := S.oTwoRes_L.symm
      _ = oTwoRes (C ⊔ Q) := by rw [heq]
      _ ≤ C := oTwoRes_sup_le hQ2 (hQL.trans hLNC)
  rw [Subgroup.commutator_le]
  intro q hq x hx
  rw [commutatorElement_def]
  exact (hLC hx).2 q hq

theorem blockU_eq_V_of_comm_le (h : ⁅pCoreOf 2 L, L⁆ ≤ V) : blockU L = V :=
  le_antisymm h (S.irr.2.2.2.1.symm.le.trans (Subgroup.commutator_mono S.V_le_pCoreOf_L le_rfl))

theorem blockZ_eq_bot_of_comm_le (h : ⁅pCoreOf 2 L, L⁆ ≤ V) : blockZ L = ⊥ := by
  show blockU L ⊓ Subgroup.centralizer (L : Set G) = ⊥
  rw [S.blockU_eq_V_of_comm_le h]
  exact S.V_inf_centralizer_L

theorem isShort2_of_comm_le (h : ⁅pCoreOf 2 L, L⁆ ≤ V) : IsShort2 L := by
  have hU := S.blockU_eq_V_of_comm_le h
  refine ⟨?_, S.charTwo_L, ?_, Or.inl S.isQuasisimple_L, ?_⟩
  ·
    intro N _ hp
    have hle : oTwoRes L ≤ N.map L.subtype := by
      rw [oTwoRes, Subgroup.closure_le]
      rintro x ⟨hxL, m, hm, hxm⟩
      obtain ⟨k, hk⟩ := hp (QuotientGroup.mk ⟨x, hxL⟩)
      have hm' : (QuotientGroup.mk ⟨x, hxL⟩ : ↥L ⧸ N) ^ m = 1 := by
        rw [← QuotientGroup.mk_pow]
        have : (⟨x, hxL⟩ : ↥L) ^ m = 1 := Subtype.ext (by simpa using hxm)
        rw [this, QuotientGroup.mk_one]
      have h1 := ConfAB.eq_one_of_pow_two_pow_of_odd hk hm' hm
      exact ⟨⟨x, hxL⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
    rw [S.oTwoRes_L] at hle
    rw [eq_top_iff]
    intro y _
    obtain ⟨y', hy', hyy'⟩ := hle y.2
    have : y' = y := Subtype.ext hyy'
    rw [← this]
    exact hy'
  · rw [hU]
    refine ⟨fun x hx => Subgroup.mem_inf.mpr ⟨S.V_le_pCoreOf_L hx,
      Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩, fun x hx => S.elemAbelian_V.2 x hx⟩
    exact (Subgroup.mem_centralizer_iff.mp (S.pCoreOf_L_le_centralizer_V hq) x hx).symm
  · rw [S.blockZ_eq_bot_of_comm_le h, hU]
    refine ⟨bot_lt_iff_ne_bot.2 S.irr.2.1, fun W hW1 hW2 hW3 => ?_⟩
    rcases S.irr.2.2.2.2.2.1 W (by rw [S.V_inf_centralizer_L]; exact hW1) hW2 hW3 with h' | h'
    · left
      rw [h', S.V_inf_centralizer_L]
    · right
      exact h'

theorem isAltType_of_comm_le (h : ⁅pCoreOf 2 L, L⁆ ≤ V) : IsAltType L 5 := by
  have hU := S.blockU_eq_V_of_comm_le h
  let e : ↥(blockU L) ≃* ↥V := MulEquiv.subgroupCongr hU
  refine ⟨S.rawData5.θ, S.rawData5.surj, ?_, S.rawData5.ψ.toMonoidHom.comp e.toMonoidHom,
    S.rawData5.ψ.surjective.comp e.surjective, ?_, ?_⟩
  · ext x
    rw [S.rawData5.ker_eq, Subgroup.mem_subgroupOf, AppC.mem_pCore_iff_mem_blockQ]
    constructor
    · intro hx
      exact inf_pCoreOf_LT_le ⟨x.2, hx⟩
    · intro hx
      exact S.pCoreOf_L_le_pCoreOf_LT hx
  · rw [S.blockZ_eq_bot_of_comm_le h, Subgroup.bot_subgroupOf]
    exact (MonoidHom.ker_eq_bot_iff _).2 (S.rawData5.ψ.injective.comp e.injective)
  · intro ℓ u v huv i
    have h2 : e v = conjAct V ⟨ℓ, S.rawData5.hnorm ℓ.2⟩ (e u) := by
      apply Subtype.ext
      rw [conjAct_coe_apply]
      exact huv
    show ((Multiplicative.toAdd (S.rawData5.ψ (e v)) : ↥Ev) : Fin 5 → ZMod 2) i = _
    rw [h2, S.rawData5.equiv, toAdd_pact, pw_coe]
    rfl

theorem isBlock2_of_comm_le (h : ⁅pCoreOf 2 L, L⁆ ≤ V) : IsBlock2 (L ⊔ T) L :=
  ⟨S.isShort2_of_comm_le h, le_sup_left,
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer S.T_le_NL)).isSubnormal⟩

theorem false_of_comm_le (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7) (h1336 : Input1336)
    (hab : IsElemAbelian 2 (conjClosure V S.G1)) (h : ⁅pCoreOf 2 L, L⁆ ≤ V) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hM
  have hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥ :=
    inf_centralizer_eq_bot_of S.isPGroup_T S.T_le_NL
      (S.omegaOneCenter_inf_centralizer_L h331 h1327)
  have hO : pCoreOf 2 (L ⊔ T) ≤ V :=
    S.pCoreOf_LT_le_V (S.isBlock2_of_comm_le h) (S.isAltType_of_comm_le h) hCTL
  have hOM : pCoreOf 2 M ≤ V := by
    refine le_trans ?_ hO
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (S.pCoreOf_M_le_T.trans le_sup_right)
      ((sup_le Subgroup.le_normalizer S.T_le_NL).trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M)
  have hCV : Subgroup.centralizer (V : Set G) ≤ V := by
    intro c hc
    have hcM : c ∈ M := S.NV_le_M (Subgroup.centralizer_le_normalizer _ hc)
    have hcC : c ∈ Subgroup.centralizer (pCoreOf 2 M : Set G) :=
      Subgroup.centralizer_le hOM hc
    exact hOM (S.charTwo_M ⟨hcM, hcC⟩)
  have hconj : ∀ g ∈ S.G1, ∀ v ∈ V, g * v * g⁻¹ ∈ V := by
    intro g hg v hv
    refine hCV ?_
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h1 : g * v * g⁻¹ ∈ conjClosure V S.G1 := mem_conjClosure hg hv
    have h2 : u ∈ conjClosure V S.G1 := le_conjClosure _ _ hu
    exact congrArg Subtype.val (hab.1.is_comm.comm ⟨u, h2⟩ ⟨_, h1⟩)
  refine h1336 G T L V S fun g hg => S.NV_le_M ?_
  refine B6.mem_normalizer_of_forall_mem (hconj g hg) fun v hv => ?_
  simpa using hconj g⁻¹ (S.G1.inv_mem hg) v hv

theorem false_of_alt6 (h331 : Stmt3_3_1) (h1327 : Stmt13_2_7) (h1336 : Input1336)
    (hF318 : A318Facts) (h36 : A36ForSQTK) (h38 : Vol2Native.A38ForSQTKCat)
    (hKF : KnownFacts15122Types) (hab : IsElemAbelian 2 (conjClosure V S.G1)) {K : Subgroup G}
    (hK : IsComponentIn K (Subgroup.centralizer ({S.v12} : Set G)))
    (e : ↥K ≃* alternatingGroup (Fin 6)) : False := by
  set Gv := Subgroup.centralizer ({S.v12} : Set G) with hGv
  have hKG : K ≤ Gv := hK.1
  have hKc : K ∈ cComp Gv := by
    have h2 := map_subtype_mem_cComp (mem_cComp_top_of_isComponent hK.2)
    rwa [Subgroup.map_subgroupOf_eq_of_le hKG] at h2
  have hqs : CFSG.IsQuasisimple ↥K :=
    (CFSG.LocalAnalysis.ComponentInitial.isQuasisimple_congr
      (Subgroup.subgroupOfEquivOfLe hKG)).1 hK.2.1
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hsimp : IsSimpleGroup ↥K := e.isSimpleGroup
  let e₀ : (↥K ⧸ CFSG.pCore 2 ↥K) ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq (ConfAB.pCore_two_eq_bot_of_simple hqs hsimp)).trans
      QuotientGroup.quotientBot
  have hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e₀.symm hqs
  have hLvK := S.Lv_le_of_exclusion_quot hF318 h36 h38 hKc hq (e₀.trans e) hKF.alt6
  exact S.false_of_comm_le h331 h1327 h1336 hab (S.commutator_pCoreOf_L_le_V hLvK e)

end Setting

end CFSG.Quasithin.H13.A5
