module

public import CFSG.Quasithin.Background.E2Pair
public import CFSG.Quasithin.Background.E2Thirteen

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

variable {G : Type*} [Group G]

theorem forall_commutator_mem_of_sup {X K P V W : Subgroup G} (hX : X = V ⊔ W)
    (hK : X ≤ Subgroup.normalizer (K : Set G)) (hP : X ≤ Subgroup.normalizer (P : Set G))
    (hV : ∀ v ∈ V, ∀ k ∈ K, v * k * v⁻¹ * k⁻¹ ∈ P)
    (hW : ∀ w ∈ W, ∀ k ∈ K, w * k * w⁻¹ * k⁻¹ ∈ P) :
    ∀ x ∈ X, ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ P := by
  let S : Subgroup G :=
    { carrier := {x | x ∈ X ∧ ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ P}
      one_mem' := ⟨X.one_mem, fun k _ => by simp⟩
      mul_mem' := by
        rintro x y ⟨hx, hxk⟩ ⟨hy, hyk⟩
        refine ⟨X.mul_mem hx hy, fun k hk => ?_⟩
        have e : x * y * k * (x * y)⁻¹ * k⁻¹ =
            x * (y * k * y⁻¹ * k⁻¹) * x⁻¹ * (x * k * x⁻¹ * k⁻¹) := by group
        rw [e]
        exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hP hx) _).mp (hyk k hk)) (hxk k hk)
      inv_mem' := by
        rintro x ⟨hx, hxk⟩
        refine ⟨X.inv_mem hx, fun k hk => ?_⟩
        have hk' : x⁻¹ * k * x ∈ K := by
          simpa using (Subgroup.mem_normalizer_iff.mp (hK (X.inv_mem hx)) k).mp hk
        have e : x⁻¹ * k * x⁻¹⁻¹ * k⁻¹ = (x * (x⁻¹ * k * x) * x⁻¹ * (x⁻¹ * k * x)⁻¹)⁻¹ := by
          group
        rw [e]
        exact P.inv_mem (hxk _ hk') }
  have hVS : V ≤ S := fun v hv => ⟨hX.ge (Subgroup.mem_sup_left hv), hV v hv⟩
  have hWS : W ≤ S := fun w hw => ⟨hX.ge (Subgroup.mem_sup_right hw), hW w hw⟩
  intro x hx
  exact ((sup_le hVS hWS) (hX.le hx)).2

theorem exists_pow_two_pow_eq_one_of_stable [Finite G] {H V₁ : Subgroup G}
    (hHV₁ : H ≤ Subgroup.normalizer (V₁ : Set G)) (hV₁ : IsPGroup 2 V₁) (hchar : CharTwo H)
    {d : G} (hdH : d ∈ H) (hdC : d ∈ Subgroup.centralizer (V₁ : Set G))
    (hd : ∀ q ∈ pCoreOf 2 H, d * q * d⁻¹ * q⁻¹ ∈ V₁) : ∃ n : ℕ, d ^ 2 ^ n = 1 := by
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hV₁
  have key : ∀ q ∈ pCoreOf 2 H, d ^ 2 ^ a * q = q * d ^ 2 ^ a := by
    intro q hq
    have hqH : q ∈ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H hq
    set z : G := q⁻¹ * (d * q * d⁻¹ * q⁻¹) * q with hz
    have hzV₁ : z ∈ V₁ := by
      have := (Subgroup.mem_normalizer_iff.mp (hHV₁ (H.inv_mem hqH)) _).mp (hd q hq)
      simpa [hz] using this
    have hdz : d * z * d⁻¹ = z := by
      have := Subgroup.mem_centralizer_iff.mp hdC z hzV₁
      calc d * z * d⁻¹ = z * d * d⁻¹ := by rw [this]
        _ = z := by group
    have hdq : d * q * d⁻¹ = q * z := by simp only [hz]; group
    have hpow : ∀ n : ℕ, d ^ n * q * (d ^ n)⁻¹ = q * z ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have e : d ^ (n + 1) * q * (d ^ (n + 1))⁻¹ = d * (d ^ n * q * (d ^ n)⁻¹) * d⁻¹ := by
          rw [pow_succ']; group
        rw [e, ih]
        have e2 : d * (q * z ^ n) * d⁻¹ = (d * q * d⁻¹) * (d * z ^ n * d⁻¹) := by group
        rw [e2, hdq]
        have e3 : d * z ^ n * d⁻¹ = z ^ n := by
          have := conj_pow (a := d) (b := z) (i := n)
          rw [hdz] at this
          exact this.symm
        rw [e3, pow_succ']
        group
    have hz1 : z ^ 2 ^ a = 1 := by
      have := pow_card_eq_one' (G := V₁) (x := ⟨z, hzV₁⟩)
      rw [ha] at this
      simpa using congrArg Subtype.val this
    have := hpow (2 ^ a)
    rw [hz1, mul_one] at this
    calc d ^ 2 ^ a * q = (d ^ 2 ^ a * q * (d ^ 2 ^ a)⁻¹) * d ^ 2 ^ a := by group
      _ = q * d ^ 2 ^ a := by rw [this]
  have hmem : d ^ 2 ^ a ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (key q hq).symm
  have hQ := hchar ⟨H.pow_mem hdH _, hmem⟩
  obtain ⟨m, hm⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨_, hQ⟩
  refine ⟨a + m, ?_⟩
  rw [pow_add, pow_mul]
  simpa using congrArg Subtype.val hm

theorem isPGroup_zpowers_of_pow [Finite G] {a : G} {k : ℕ} (h : a ^ 2 ^ k = 1) :
    IsPGroup 2 (Subgroup.zpowers a) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine IsPGroup.of_card (n := padicValNat 2 (orderOf a)) ?_
  rw [Nat.card_zpowers]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h)
  rw [hi, padicValNat.prime_pow]

namespace Pair

variable [Finite G] {X T M V : Subgroup G} {g : G}

theorem commutator_mem_P_of_mem_pCoreOf (h : Pair X T M V g) {x q : G} (hx : x ∈ X)
    (hq : q ∈ pCoreOf 2 X) :
    x * q * x⁻¹ * q⁻¹ ∈ (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) :=
  forall_commutator_mem_of_sup h.gen (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
    h.le_normalizer_P (fun _ hv _ hq => Subgroup.mem_sup_left (h.commutator_mem_B hv hq))
    (fun _ hw _ hq => Subgroup.mem_sup_right (h.commutator_mem_A hw hq)) x hx q hq

theorem commutator_kerIn_mem_pCoreOf (h : Pair X T M V g) {v j : G} (hv : v ∈ V)
    (hj : j ∈ kerIn M X) : v * j * v⁻¹ * j⁻¹ ∈ pCoreOf 2 X := by
  set c := v * j * v⁻¹ * j⁻¹ with hc
  have hjM : j ∈ M := kerIn_le hj
  have hcM : c ∈ pCoreOf 2 M := by
    have h1 : j * v⁻¹ * j⁻¹ ∈ pCoreOf 2 M :=
      (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hjM)
        _).mp ((pCoreOf 2 M).inv_mem (h.le_pCoreOf hv))
    have e : c = v * (j * v⁻¹ * j⁻¹) := by rw [hc]; group
    rw [e]
    exact (pCoreOf 2 M).mul_mem (h.le_pCoreOf hv) h1
  have hcJ : c ∈ kerIn M X := by
    have h1 : v * j * v⁻¹ ∈ kerIn M X :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_kerIn M X (h.V_le hv)) j).mp hj
    exact (kerIn M X).mul_mem h1 ((kerIn M X).inv_mem hj)
  have hS : IsPGroup 2 (Subgroup.zpowers c) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).to_le (Subgroup.zpowers_le.2 hcM)
  exact h.le_pCoreOf_of_le_kerIn hS (Subgroup.zpowers_le.2 hcJ) (Subgroup.mem_zpowers c)

theorem commutator_kerIn_mem_P (h : Pair X T M V g) {x j : G} (hx : x ∈ X)
    (hj : j ∈ kerIn M X) :
    x * j * x⁻¹ * j⁻¹ ∈ (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) := by
  set P := (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) with hP
  set J := kerIn M X with hJ
  have hPX : X ≤ Subgroup.normalizer (P : Set G) := h.le_normalizer_P
  have hJX : X ≤ Subgroup.normalizer (J : Set G) := le_normalizer_kerIn M X
  have hPQ : P ≤ pCoreOf 2 X := h.P_le_pCoreOf
  have hQX : pCoreOf 2 X ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hJXle : J ≤ X := kerIn_le.trans h.le_X
  have hN : (P.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hPQ.trans hQX)).2 hPX
  set π : X →* X ⧸ P.subgroupOf X := QuotientGroup.mk' (P.subgroupOf X) with hπ
  have hπ1 : ∀ w : X, π w = 1 ↔ (w : G) ∈ P := fun w => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hodd : ∀ v ∈ V, ∀ b ∈ J, Odd (orderOf b) → v * b * v⁻¹ * b⁻¹ ∈ P := by
    intro v hv b hb hbo
    have hvX := h.V_le hv
    have hbX := hJXle hb
    set c := b * v * b⁻¹ * v⁻¹ with hc
    have hcQ : c ∈ pCoreOf 2 X := by
      have := (pCoreOf 2 X).inv_mem (h.commutator_kerIn_mem_pCoreOf hv hb)
      have e : c = (v * b * v⁻¹ * b⁻¹)⁻¹ := by rw [hc]; group
      rw [e]
      exact this
    have hy : Odd (orderOf (π ⟨b, hbX⟩)) := by
      refine Odd.of_dvd_nat ?_ (orderOf_map_dvd π _)
      rwa [Subgroup.orderOf_mk]
    have hcπ : π ⟨b, hbX⟩ * π ⟨v, hvX⟩ * (π ⟨b, hbX⟩)⁻¹ * (π ⟨v, hvX⟩)⁻¹ =
        π ⟨c, hQX hcQ⟩ := by
      simp only [← map_inv, ← map_mul]
      rfl
    have hcomm : π ⟨b, hbX⟩ * π ⟨c, hQX hcQ⟩ = π ⟨c, hQX hcQ⟩ * π ⟨b, hbX⟩ := by
      have h1 := h.commutator_mem_P_of_mem_pCoreOf hbX hcQ
      have h2 : π (⟨b, hbX⟩ * ⟨c, hQX hcQ⟩ * ⟨b, hbX⟩⁻¹ * ⟨c, hQX hcQ⟩⁻¹) = 1 := (hπ1 _).2 h1
      simp only [map_mul, map_inv] at h2
      calc π ⟨b, hbX⟩ * π ⟨c, hQX hcQ⟩ =
            (π ⟨b, hbX⟩ * π ⟨c, hQX hcQ⟩ * (π ⟨b, hbX⟩)⁻¹ * (π ⟨c, hQX hcQ⟩)⁻¹) *
              (π ⟨c, hQX hcQ⟩ * π ⟨b, hbX⟩) := by group
        _ = π ⟨c, hQX hcQ⟩ * π ⟨b, hbX⟩ := by rw [h2, one_mul]
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X ⟨c, hcQ⟩
    have hc2 : (π ⟨c, hQX hcQ⟩) ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨c, hQX hcQ⟩ : X) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [this, map_one]
    have key := commute_of_odd_of_commutator hy (by rw [hcπ]; exact hcomm)
      ⟨k, by rw [hcπ]; exact hc2⟩
    have h3 : π (⟨b, hbX⟩ * ⟨v, hvX⟩ * ⟨b, hbX⟩⁻¹ * ⟨v, hvX⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv, key]
      group
    have h4 := (hπ1 _).1 h3
    have e : v * b * v⁻¹ * b⁻¹ = (b * v * b⁻¹ * v⁻¹)⁻¹ := by group
    rw [e]
    exact P.inv_mem h4
  have hVJ : ∀ v ∈ V, ∀ j ∈ J, v * j * v⁻¹ * j⁻¹ ∈ P := by
    intro v hv j hj
    obtain ⟨a, b, rfl, ha, hb, ⟨k, hk⟩, hbo⟩ := exists_two_part_odd_part j
    have haJ : a ∈ J := Subgroup.zpowers_le.2 hj ha
    have hbJ : b ∈ J := Subgroup.zpowers_le.2 hj hb
    have haQ : a ∈ pCoreOf 2 X :=
      h.le_pCoreOf_of_le_kerIn (isPGroup_zpowers_of_pow hk) (Subgroup.zpowers_le.2 haJ)
        (Subgroup.mem_zpowers a)
    have h1 := hodd v hv b hbJ hbo
    have h2 := h.commutator_mem_P_of_mem_pCoreOf (h.V_le hv) haQ
    have h3 : b * (v * a * v⁻¹ * a⁻¹) * b⁻¹ ∈ P :=
      (Subgroup.mem_normalizer_iff.mp (hPX (hJXle hbJ)) _).mp h2
    have e : v * (b * a) * v⁻¹ * (b * a)⁻¹ =
        (v * b * v⁻¹ * b⁻¹) * (b * (v * a * v⁻¹ * a⁻¹) * b⁻¹) := by group
    rw [e]
    exact P.mul_mem h1 h3
  have hWJ : ∀ w ∈ conjSub g V, ∀ j ∈ J, w * j * w⁻¹ * j⁻¹ ∈ P := by
    intro w hw j hj
    have hv : g⁻¹ * w * g ∈ V := mem_conjSub.mp hw
    have hj' : g⁻¹ * j * g ∈ J := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hJX (X.inv_mem h.mem)) j).mp hj
    have h1 := hVJ _ hv _ hj'
    have h2 := (Subgroup.mem_normalizer_iff.mp (hPX h.mem) _).mp h1
    have e : w * j * w⁻¹ * j⁻¹ =
        g * ((g⁻¹ * w * g) * (g⁻¹ * j * g) * (g⁻¹ * w * g)⁻¹ * (g⁻¹ * j * g)⁻¹) * g⁻¹ := by
      group
    rw [e]
    exact h2
  exact forall_commutator_mem_of_sup h.gen hJX hPX hVJ hWJ x hx j hj

theorem not_le_centralizer (h : Pair X T M V g) (hchar : CharTwo X) (hXV : X ≠ V) :
    ¬ conjSub g (kerIn M X ⊓ V) ≤ Subgroup.centralizer (V : Set G) := by
  set P := (kerIn M X ⊓ V) ⊔ conjSub g (kerIn M X ⊓ V) with hP
  set Q := pCoreOf 2 X with hQ
  have hPX : X ≤ Subgroup.normalizer (P : Set G) := h.le_normalizer_P
  have hQX : X ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hP2 : IsPGroup 2 P :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le h.P_le_pCoreOf
  have hVQ : ¬ V ≤ Q := by
    intro hVQ
    have hWQ : conjSub g V ≤ Q := by
      have h1 := (conjSub g).monotone hVQ
      rwa [hQ, h.conjSub_pCoreOf] at h1
    have hXQ : X ≤ Q := by
      rw [h.gen]
      exact sup_le hVQ hWQ
    have hX2 : IsPGroup 2 X := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).to_le hXQ
    have hTX : T = X := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hX2
      have hdvd : T.relIndex X ∣ 2 ^ n := by
        rw [← hn]
        have h1 := Subgroup.relIndex_mul_card T X
        rw [inf_eq_left.2 h.sylow.1] at h1
        exact Dvd.intro _ h1
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      have hi0 : i = 0 := by
        by_contra hi0
        apply h.sylow.2.2
        show 2 ∣ T.relIndex X
        rw [hi]
        exact dvd_pow_self 2 hi0
      rw [hi0, pow_zero] at hi
      exact le_antisymm h.sylow.1 (Subgroup.relIndex_eq_one.1 hi)
    have hgV : conjSub g V = V := conjSub_eq_self (h.normal_T (hTX ▸ h.mem))
    apply hXV
    rw [h.gen, hgV, sup_idem]
  intro hAC
  let D : Subgroup G :=
    { carrier := {x | x ∈ X ∧ x ∈ Subgroup.centralizer (P : Set G) ∧
        ∀ q ∈ Q, x * q * x⁻¹ * q⁻¹ ∈ P}
      one_mem' := ⟨X.one_mem, Subgroup.one_mem _, fun q _ => by simp⟩
      mul_mem' := by
        rintro x y ⟨hx, hxC, hxq⟩ ⟨hy, hyC, hyq⟩
        refine ⟨X.mul_mem hx hy, Subgroup.mul_mem _ hxC hyC, fun q hq => ?_⟩
        have e : x * y * q * (x * y)⁻¹ * q⁻¹ =
            x * (y * q * y⁻¹ * q⁻¹) * x⁻¹ * (x * q * x⁻¹ * q⁻¹) := by group
        rw [e]
        exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hPX hx) _).mp (hyq q hq)) (hxq q hq)
      inv_mem' := by
        rintro x ⟨hx, hxC, hxq⟩
        refine ⟨X.inv_mem hx, Subgroup.inv_mem _ hxC, fun q hq => ?_⟩
        have hq' : x⁻¹ * q * x ∈ Q := by
          simpa using (Subgroup.mem_normalizer_iff.mp (hQX (X.inv_mem hx)) q).mp hq
        have e : x⁻¹ * q * x⁻¹⁻¹ * q⁻¹ = (x * (x⁻¹ * q * x) * x⁻¹ * (x⁻¹ * q * x)⁻¹)⁻¹ := by
          group
        rw [e]
        exact P.inv_mem (hxq _ hq') }
  have hDX : D ≤ X := fun x hx => hx.1
  have hXD : X ≤ Subgroup.normalizer (D : Set G) := by
    have key : ∀ y ∈ X, ∀ d ∈ D, y * d * y⁻¹ ∈ D := by
      intro y hy d hd
      obtain ⟨hdX, hdC, hdq⟩ := hd
      refine ⟨X.mul_mem (X.mul_mem hy hdX) (X.inv_mem hy), ?_, fun q hq => ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro p hp
        have hp' : y⁻¹ * p * y ∈ P := by
          simpa using (Subgroup.mem_normalizer_iff.mp (hPX (X.inv_mem hy)) p).mp hp
        have h1 := Subgroup.mem_centralizer_iff.1 hdC _ hp'
        calc p * (y * d * y⁻¹) = y * ((y⁻¹ * p * y) * d) * y⁻¹ := by group
          _ = y * (d * (y⁻¹ * p * y)) * y⁻¹ := by rw [h1]
          _ = y * d * y⁻¹ * p := by group
      · have hq' : y⁻¹ * q * y ∈ Q := by
          simpa using (Subgroup.mem_normalizer_iff.mp (hQX (X.inv_mem hy)) q).mp hq
        have h1 := (Subgroup.mem_normalizer_iff.mp (hPX hy) _).mp (hdq _ hq')
        have e : y * d * y⁻¹ * q * (y * d * y⁻¹)⁻¹ * q⁻¹ =
            y * (d * (y⁻¹ * q * y) * d⁻¹ * (y⁻¹ * q * y)⁻¹) * y⁻¹ := by group
        rw [e]
        exact h1
    exact fun y hy => mem_normalizer_of_forall_mem (key y hy)
      (fun d hd => by simpa using key y⁻¹ (X.inv_mem hy) d hd)
  have hD2 : IsPGroup 2 D := by
    rintro ⟨d, hdX, hdC, hdq⟩
    obtain ⟨n, hn⟩ := exists_pow_two_pow_eq_one_of_stable hPX hP2 hchar hdX hdC hdq
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hDQ : D ≤ Q := CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 D X hDX
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hDX).2 hXD) hD2
  apply hVQ
  intro v hv
  refine hDQ ⟨h.V_le hv, ?_, fun q hq => h.commutator_mem_P_of_mem_pCoreOf (h.V_le hv) hq⟩
  have hvB : v ∈ Subgroup.centralizer ((kerIn M X ⊓ V : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun b hb => h.comm hb.2 hv
  have hvA : v ∈ Subgroup.centralizer ((conjSub g (kerIn M X ⊓ V) : Subgroup G) : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun a ha => (Subgroup.mem_centralizer_iff.1 (hAC ha) v hv).symm
  exact B2F.mem_centralizer_sup hvB hvA

end Pair

end E2

end CFSG.Quasithin
