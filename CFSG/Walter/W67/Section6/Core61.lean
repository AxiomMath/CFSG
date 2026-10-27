module

public import CFSG.Walter.JRFacts
public import CFSG.Walter.W67.Section5.Sylow52
public import CFSG.Walter.W67.Section6.Util
public import CFSG.Walter.W67.W1Basic

public section

namespace CFSG.Walter.W67

namespace Sec6

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_of_cj_eq {g : G} {H : Subgroup G} (h : cj g H = H) :
    g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have : g * x * g⁻¹ ∈ cj g H := conj_mem_cj hx
    rwa [h] at this
  · intro hx
    rw [← h, mem_cj] at hx
    simpa [mul_assoc] using hx

omit [Finite G] in
theorem mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  have h1 := hA x
  have h2 := hB x
  simp only [Subgroup.mem_inf] at h1 h2 ⊢
  exact and_congr h1 h2

omit [Finite G] in
theorem mem_normalizer_sup {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply mem_normalizer_of_cj_eq
  rw [cj_sup, cj_eq_self_of_mem_normalizer hA, cj_eq_self_of_mem_normalizer hB]

omit [Finite G] in
theorem inf_sup_of_le {T A B : Subgroup G} (hBT : B ≤ T)
    (hBA : B ≤ Subgroup.normalizer (A : Set G)) : T ⊓ (A ⊔ B) = (T ⊓ A) ⊔ B := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxT, hxAB⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer hBA).mp hxAB
    have haT : a ∈ T := by
      have : a = a * b * b⁻¹ := by group
      rw [this]
      exact T.mul_mem hxT (T.inv_mem (hBT hb))
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨haT, ha⟩))
      (Subgroup.mem_sup_right hb)
  · exact sup_le (inf_le_inf_left T le_sup_left) (le_inf hBT le_sup_right)

theorem card_sup_of_inf_eq_bot {A B : Subgroup G} (hBA : B ≤ Subgroup.normalizer (A : Set G))
    (hAB : A ⊓ B = ⊥) : Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have h := Sec52.card_sup_mul_card_inf hBA
  rwa [hAB, Subgroup.card_bot, mul_one, sup_comm] at h

omit [Finite G] in
theorem inf_eq_bot_of_coprime {A B : Subgroup G} (h : Nat.Coprime (Nat.card A) (Nat.card B)) :
    A ⊓ B = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.mp hx
  have h1 := Subgroup.orderOf_dvd_natCard A hxA
  have h2 := Subgroup.orderOf_dvd_natCard B hxB
  rw [Subgroup.mem_bot]
  exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 h) h2)

theorem relIndex_eq_of_card {A B : Subgroup G} (hAB : A ≤ B) {n : ℕ}
    (h : Nat.card B = Nat.card A * n) : A.relIndex B = n := by
  have h1 := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [inf_eq_left.mpr hAB, h, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1

theorem eq_of_normal_hall {A B A' : Subgroup G} (hAB : A ≤ B)
    (hB : B ≤ Subgroup.normalizer (A : Set G)) (hcop : Nat.Coprime (Nat.card A) (A.relIndex B))
    (hA'B : A' ≤ B) (hcard : Nat.card A' = Nat.card A) : A' = A := by
  have h1 := Sec52.card_sup_mul_card_inf (hA'B.trans hB)
  have hrel : A.relIndex B * Nat.card A = Nat.card B := by
    have := Subgroup.relIndex_mul_card (H := A) (K := B)
    rwa [inf_eq_left.mpr hAB] at this
  obtain ⟨m, hm⟩ : Nat.card ↥(A ⊓ A') ∣ Nat.card A' := Subgroup.card_dvd_of_le inf_le_right
  have hsup : Nat.card ↥(A' ⊔ A) = Nat.card A * m := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos : 0 < Nat.card ↥(A ⊓ A'))
    rw [h1, hm]
    ring
  have hmB : Nat.card A * m ∣ A.relIndex B * Nat.card A := by
    rw [hrel, ← hsup]
    exact Subgroup.card_dvd_of_le (sup_le hA'B hAB)
  have hmrel : m ∣ A.relIndex B := by
    rw [mul_comm] at hmB
    exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos hmB
  have hmA : m ∣ Nat.card A := by
    rw [← hcard, hm]
    exact dvd_mul_left _ _
  have hm1 : m = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hmA hcop) hmrel
  rw [hm1, mul_one] at hm
  have hle : A' ≤ A := by
    have : A ⊓ A' = A' := Subgroup.eq_of_le_of_card_ge inf_le_right hm.le
    rw [← this]
    exact inf_le_left
  exact Subgroup.eq_of_le_of_card_ge hle hcard.ge

omit [Finite G] in
theorem mem_of_odd_of_mem_zpowers_sup' {J : G} (hJ : orderOf J = 2) {K' : Subgroup G}
    (hK' : K' ≤ Subgroup.centralizer ({J} : Set G)) (hJK' : J ∉ K') {x : G}
    (hx : x ∈ Subgroup.zpowers J ⊔ K') (hodd : Odd (orderOf x)) : x ∈ K' := by
  have hJJ : J * J = 1 := by rw [← pow_two, ← hJ, pow_orderOf_eq_one]
  have hC : K' ≤ Subgroup.centralizer ((Subgroup.zpowers J : Subgroup G) : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hkJ : Commute k J := Subgroup.mem_centralizer_singleton_iff.mp (hK' hk)
    exact (hkJ.zpow_right n).symm.eq
  have hN : K' ≤ Subgroup.normalizer ((Subgroup.zpowers J : Subgroup G) : Set G) :=
    hC.trans (Subgroup.centralizer_le_normalizer _)
  obtain ⟨j, hj, k, hk, rfl⟩ := (mem_sup_iff_of_le_normalizer hN).mp hx
  rcases CFSG.Walter.eq_one_or_eq_of_mem_zpowers hJ hj with rfl | rfl
  · rwa [one_mul]
  exfalso
  obtain ⟨n, hn⟩ := hodd
  have hc : Commute j k := (Subgroup.mem_centralizer_singleton_iff.mp (hK' hk)).symm
  have h1 : (j * k) ^ orderOf (j * k) = 1 := pow_orderOf_eq_one _
  rw [hc.mul_pow, hn, pow_succ, pow_mul, pow_two, hJJ, one_pow, one_mul] at h1
  have hJ' : j = (k ^ (2 * n + 1))⁻¹ := eq_inv_of_mul_eq_one_left h1
  exact hJK' (hJ' ▸ K'.inv_mem (K'.pow_mem hk _))

omit [Finite G] in
theorem comm_of_isCyclic {W : Subgroup G} (hW : IsCyclic W) :
    ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := by
  intro a ha b hb
  let _ : CommGroup W := IsCyclic.commGroup
  exact congrArg Subtype.val (mul_comm (⟨a, ha⟩ : W) ⟨b, hb⟩)

theorem mem_centralizer_of_odd_of_cyclic {W : Subgroup G} (hW : IsCyclic W)
    (htot : (Nat.card W).totient ∣ 4) {e : G} (he : e ∈ Subgroup.normalizer (W : Set G))
    (hodd : Odd (orderOf e)) : e ∈ Subgroup.centralizer (W : Set G) := by
  have hmem : ∀ w ∈ W, e * w * e⁻¹ ∈ W := fun w hw => (Subgroup.mem_normalizer_iff.mp he w).mp hw
  have hmem' : ∀ w ∈ W, e⁻¹ * w * e ∈ W := fun w hw => by
    have := (Subgroup.mem_normalizer_iff.mp he (e⁻¹ * w * e)).mpr (by simpa [mul_assoc] using hw)
    exact this
  let σ : MulAut W :=
    { toFun := fun w => ⟨e * w * e⁻¹, hmem w w.2⟩
      invFun := fun w => ⟨e⁻¹ * w * e, hmem' w w.2⟩
      left_inv := fun w => Subtype.ext (by simp [mul_assoc])
      right_inv := fun w => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun v w => Subtype.ext (by simp [mul_assoc]) }
  have hσn : ∀ (n : ℕ) (w : W), ((σ ^ n) w : G) = e ^ n * w * (e ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro w; simp
    | succ n ih =>
      intro w
      rw [pow_succ', MulAut.mul_apply]
      change e * ((σ ^ n) w : G) * e⁻¹ = _
      rw [ih, pow_succ']
      group
  have hσk : σ ^ orderOf e = 1 := by
    refine MulEquiv.ext fun w => Subtype.ext ?_
    rw [hσn, pow_orderOf_eq_one, one_mul, inv_one, mul_one]
    rfl
  have hcard : Nat.card (MulAut W) = (Nat.card W).totient := IsCyclic.card_mulAut ↥W
  have : Finite (MulAut W) := Nat.finite_of_card_ne_zero (by
    rw [hcard]
    exact (Nat.totient_pos.mpr Nat.card_pos).ne')
  have h1 : orderOf σ ∣ orderOf e := orderOf_dvd_of_pow_eq_one hσk
  have h2 : orderOf σ ∣ 4 := (orderOf_dvd_natCard σ).trans (hcard ▸ htot)
  have hcop : Nat.Coprime (orderOf e) 4 := by
    have : Nat.Coprime (orderOf e) (2 ^ 2) :=
      Nat.Coprime.pow_right 2 (Nat.coprime_two_right.mpr hodd)
    simpa using this
  have hσ1 : σ = 1 :=
    orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 hcop) h2)
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h3 := congrArg Subtype.val (DFunLike.congr_fun hσ1 ⟨w, hw⟩)
  change e * w * e⁻¹ = w at h3
  calc w * e = e * w * e⁻¹ * e := by rw [h3]
    _ = e * w := by group

omit [Finite G] in
theorem isSolvable_sup_of_comm {L E : Subgroup G} (hE : E ≤ Subgroup.normalizer (L : Set G))
    (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hL : Group.IsSolvable L) :
    Group.IsSolvable ↥(L ⊔ E) := by
  have hLM : L ≤ L ⊔ E := le_sup_left
  have hMN : L ⊔ E ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hE
  have hnorm : (L.subgroupOf (L ⊔ E)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).mpr hMN
  have hrep : ∀ x : ↥(L ⊔ E), ∃ e : G, ∃ he : e ∈ E,
      (QuotientGroup.mk x : ↥(L ⊔ E) ⧸ L.subgroupOf (L ⊔ E)) =
        QuotientGroup.mk ⟨e, le_sup_right (a := L) he⟩ := by
    intro x
    obtain ⟨l, hl, e, he, hx⟩ := (mem_sup_iff_of_le_normalizer hE).mp x.2
    refine ⟨e, he, ?_⟩
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : ((x⁻¹ * ⟨e, le_sup_right (a := L) he⟩ : ↥(L ⊔ E)) : G) = e⁻¹ * l⁻¹ * (e⁻¹)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, ← hx]
      group
    rw [this]
    exact (Subgroup.mem_normalizer_iff.mp (hE (E.inv_mem he)) l⁻¹).mp (L.inv_mem hl)
  have hcomm : ∀ a b : ↥(L ⊔ E) ⧸ L.subgroupOf (L ⊔ E), a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨e₁, he₁, h₁⟩ := hrep x
    obtain ⟨e₂, he₂, h₂⟩ := hrep y
    rw [h₁, h₂, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hEc e₁ he₁ e₂ he₂)
  have hQ : Group.IsSolvable (↥(L ⊔ E) ⧸ L.subgroupOf (L ⊔ E)) := Group.isSolvable_of_comm hcomm
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hLM)
    (QuotientGroup.mk' (L.subgroupOf (L ⊔ E))) ?_
  intro x hx
  rw [QuotientGroup.ker_mk'] at hx
  exact ⟨⟨x, hx⟩, rfl⟩

structure GData (L : Subgroup G) (J : G) (p r : ℕ) (P C W : Subgroup G) : Prop where
  C_le : C ≤ L
  W_le : W ≤ L
  P_le_C : P ≤ C
  P_card : Nat.card P = r ^ (Nat.card L).factorization r
  P_ne : P ≠ ⊥
  C_comm : ∀ a ∈ C, ∀ b ∈ C, a * b = b * a
  C_hall : Nat.Coprime (Nat.card C) (C.subgroupOf L).index
  C_cent : ∀ c ∈ C, c ≠ 1 → L ⊓ Subgroup.centralizer ({c} : Set G) = C
  CW_inf : C ⊓ W = ⊥
  CW_sup : C ⊔ W = L ⊓ Subgroup.normalizer (P : Set G)
  C_norm : L ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (C : Set G)
  W_cyc : IsCyclic W
  W_card : Nat.card W = 6 ∨ (p = 5 ∧ r = 11 ∧ Nat.card W = 10)
  J_mem : J ∈ W

namespace GData

variable {L : Subgroup G} {J : G} {p r : ℕ} {P C W : Subgroup G}

omit [Finite G] in
theorem P_le (hD : GData L J p r P C W) : P ≤ L := hD.P_le_C.trans hD.C_le

omit [Finite G] in
theorem C_le_N (hD : GData L J p r P C W) : C ≤ L ⊓ Subgroup.normalizer (P : Set G) :=
  hD.CW_sup ▸ le_sup_left

omit [Finite G] in
theorem W_le_N (hD : GData L J p r P C W) : W ≤ L ⊓ Subgroup.normalizer (P : Set G) :=
  hD.CW_sup ▸ le_sup_right

omit [Finite G] in
theorem two_dvd_card_W (hD : GData L J p r P C W) : 2 ∣ Nat.card W := by
  rcases hD.W_card with h | ⟨-, -, h⟩ <;> rw [h] <;> norm_num

omit [Finite G] in
theorem totient_dvd (hD : GData L J p r P C W) : (Nat.card W).totient ∣ 4 := by
  rcases hD.W_card with h | ⟨-, -, h⟩ <;> rw [h] <;> decide

theorem card_N (hD : GData L J p r P C W) :
    Nat.card ↥(L ⊓ Subgroup.normalizer (P : Set G)) = Nat.card C * Nat.card W := by
  rw [← hD.CW_sup]
  exact card_sup_of_inf_eq_bot (hD.W_le_N.trans hD.C_norm) hD.CW_inf

theorem card_W_dvd (hD : GData L J p r P C W) : Nat.card W ∣ (C.subgroupOf L).index := by
  change Nat.card W ∣ C.relIndex L
  have h1 := Subgroup.relIndex_mul_card (H := C) (K := L)
  rw [inf_eq_left.mpr hD.C_le] at h1
  have h2 : Nat.card C * Nat.card W ∣ Nat.card L :=
    hD.card_N ▸ Subgroup.card_dvd_of_le inf_le_left
  rw [← h1, mul_comm] at h2
  exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos h2

theorem coprime_C_W (hD : GData L J p r P C W) : Nat.Coprime (Nat.card C) (Nat.card W) :=
  Nat.Coprime.coprime_dvd_right hD.card_W_dvd hD.C_hall

theorem odd_card_C (hD : GData L J p r P C W) : Odd (Nat.card C) :=
  Nat.coprime_two_right.mp (Nat.Coprime.coprime_dvd_right hD.two_dvd_card_W hD.coprime_C_W)

theorem cj (hD : GData L J p r P C W) {ℓ : G} (hℓ : ℓ ∈ L) :
    GData L (ℓ * J * ℓ⁻¹) p r (cj ℓ P) (cj ℓ C) (cj ℓ W) where
  C_le := cj_eq_self_of_mem hℓ ▸ cj_mono hD.C_le
  W_le := cj_eq_self_of_mem hℓ ▸ cj_mono hD.W_le
  P_le_C := cj_mono hD.P_le_C
  P_card := by rw [card_cj]; exact hD.P_card
  P_ne := fun h => hD.P_ne (cj_eq_bot_iff.mp h)
  C_comm := comm_cj hD.C_comm
  C_hall := by
    change Nat.Coprime _ ((Sec6.cj ℓ C).relIndex L)
    rw [relIndex_cj hℓ, card_cj]
    exact hD.C_hall
  C_cent := by
    rintro _ ⟨c, hc, rfl⟩ hc1
    have hc1' : c ≠ 1 := fun h => hc1 (by rw [h]; simp)
    rw [← hD.C_cent c hc hc1', cj_inf, cj_eq_self_of_mem hℓ, cj_centralizer_singleton]
    rfl
  CW_inf := by rw [← cj_inf, hD.CW_inf, cj_bot]
  CW_sup := by rw [← cj_sup, hD.CW_sup, cj_inf, cj_eq_self_of_mem hℓ, cj_normalizer]
  C_norm := by
    rw [← cj_eq_self_of_mem hℓ, ← cj_normalizer, ← cj_inf, ← cj_normalizer]
    exact cj_mono hD.C_norm
  W_cyc := isCyclic_cj hD.W_cyc
  W_card := by rw [card_cj]; exact hD.W_card
  J_mem := conj_mem_cj hD.J_mem

omit [Finite G] in
theorem C_inf_normalizer_W (hD : GData L J p r P C W) (hJ : orderOf J = 2) :
    C ⊓ Subgroup.normalizer (W : Set G) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  obtain ⟨hcC, hcW⟩ := Subgroup.mem_inf.mp hc
  rw [Subgroup.mem_bot]
  by_contra hc1
  have hJW := hD.J_mem
  have h1 : c * J * c⁻¹ * J⁻¹ ∈ W :=
    W.mul_mem ((Subgroup.mem_normalizer_iff.mp hcW J).mp hJW) (W.inv_mem hJW)
  have h2 : c * J * c⁻¹ * J⁻¹ ∈ C := by
    have : J * c⁻¹ * J⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.mp (hD.C_norm (hD.W_le_N hJW)) c⁻¹).mp (C.inv_mem hcC)
    have e : c * J * c⁻¹ * J⁻¹ = c * (J * c⁻¹ * J⁻¹) := by group
    rw [e]
    exact C.mul_mem hcC this
  have h3 : c * J * c⁻¹ * J⁻¹ = 1 := by
    have := Subgroup.mem_inf.mpr ⟨h2, h1⟩
    rwa [hD.CW_inf, Subgroup.mem_bot] at this
  have hJc : J ∈ L ⊓ Subgroup.centralizer ({c} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨hD.W_le hJW, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc J * c = c * J * c⁻¹ * J⁻¹ * (J * c) := by rw [h3, one_mul]
      _ = c * J := by group
  rw [hD.C_cent c hcC hc1] at hJc
  have : J ∈ C ⊓ W := Subgroup.mem_inf.mpr ⟨hJc, hJW⟩
  rw [hD.CW_inf, Subgroup.mem_bot] at this
  rw [this, orderOf_one] at hJ
  exact absurd hJ (by norm_num)

end GData

theorem exists_adjust {L E K' P C W : Subgroup G} {J : G} {p r : ℕ} [Fact r.Prime]
    (hEL : E ≤ Subgroup.normalizer (L : Set G)) (hLE : L ⊓ E = ⊥) (hJ : orderOf J = 2)
    (hEJ : E ≤ Subgroup.centralizer ({J} : Set G))
    (hLJ : L ⊓ Subgroup.centralizer ({J} : Set G) = Subgroup.zpowers J ⊔ K')
    (hK'J : K' ≤ Subgroup.centralizer ({J} : Set G)) (hJK' : J ∉ K')
    (hEK' : E ≤ Subgroup.normalizer (K' : Set G))
    (hcopK : Nat.Coprime (Nat.card K') (Nat.card E))
    (hcopW : Nat.Coprime (Nat.card W) (Nat.card E)) (hD : GData L J p r P C W) :
    ∃ k ∈ K', E ≤ Subgroup.normalizer ((Sec6.cj k⁻¹ P : Subgroup G) : Set G) ∧
      E ≤ Subgroup.normalizer ((Sec6.cj k⁻¹ W : Subgroup G) : Set G) := by
  have hJW := hD.J_mem
  have hLM : L ≤ L ⊔ E := le_sup_left
  have hMN : L ⊔ E ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hEL
  have hCN₁ := hD.C_le_N
  have hWN₁ := hD.W_le_N
  have hEodd : Odd (Nat.card E) :=
    Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_left hD.two_dvd_card_W hcopW)
  set N₁ := L ⊓ Subgroup.normalizer (P : Set G) with hN₁def
  set N := (L ⊔ E) ⊓ Subgroup.normalizer (P : Set G) with hNdef
  have hNN₁ : ∀ n ∈ N, Sec6.cj n N₁ = N₁ := fun n hn =>
    cj_eq_self_of_mem_normalizer (mem_normalizer_inf (hMN (Subgroup.mem_inf.mp hn).1)
      (Subgroup.le_normalizer (Subgroup.mem_inf.mp hn).2))
  have hrelN₁ : C.relIndex N₁ = Nat.card W := relIndex_eq_of_card hCN₁ hD.card_N
  have hcopN₁ : Nat.Coprime (Nat.card C) (C.relIndex N₁) := by
    rw [hrelN₁]
    exact hD.coprime_C_W
  have hCn : ∀ n ∈ N, Sec6.cj n C = C := fun n hn =>
    eq_of_normal_hall hCN₁ hD.C_norm hcopN₁ (hNN₁ n hn ▸ cj_mono hCN₁) (card_cj n C)
  have hNC : N ≤ Subgroup.normalizer (C : Set G) := fun n hn => mem_normalizer_of_cj_eq (hCn n hn)
  have hCN : C ≤ N := le_inf (hD.C_le.trans hLM) (hCN₁.trans inf_le_right)
  have hconj : ∀ n ∈ N, ∃ c ∈ C, c⁻¹ * n ∈ Subgroup.normalizer (W : Set G) := by
    intro n hn
    obtain ⟨c, hcC, hc⟩ := exists_conj_complement_in hCN₁ hD.C_norm hcopN₁ hWN₁
      (hNN₁ n hn ▸ cj_mono hWN₁) hD.CW_inf hD.CW_sup
      (by rw [← hCn n hn, ← cj_inf, hD.CW_inf, cj_bot])
      (by rw [← hCn n hn, ← cj_sup, hD.CW_sup, hNN₁ n hn])
    refine ⟨c, hcC, mem_normalizer_of_cj_eq ?_⟩
    rw [cj_mul, hc, cj_inv_cj]
  set Y := N ⊓ Subgroup.normalizer (W : Set G) with hYdef
  have hCY : C ⊔ Y = N := by
    apply le_antisymm (sup_le hCN inf_le_left)
    intro n hn
    obtain ⟨c, hcC, hc⟩ := hconj n hn
    have hy : c⁻¹ * n ∈ Y := Subgroup.mem_inf.mpr ⟨N.mul_mem (N.inv_mem (hCN hcC)) hn, hc⟩
    have e : n = c * (c⁻¹ * n) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hcC) (Subgroup.mem_sup_right hy)
  have hCYi : C ⊓ Y = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left C inf_le_right).trans (hD.C_inf_normalizer_W hJ).le)
  have hNcard1 : Nat.card N = Nat.card C * Nat.card Y := by
    rw [← hCY]
    exact card_sup_of_inf_eq_bot (inf_le_left.trans hNC) hCYi
  have hLN : L ⊔ N = L ⊔ E := by
    apply le_antisymm (sup_le hLM inf_le_left)
    intro m hm
    obtain ⟨ℓ, hℓL, hℓm⟩ := exists_mul_mem_normalizer_of_sylowIn hD.P_le hD.P_card (hMN hm)
    have hN' : ℓ * m ∈ N := Subgroup.mem_inf.mpr ⟨(L ⊔ E).mul_mem (hLM hℓL) hm, hℓm⟩
    have e : m = ℓ⁻¹ * (ℓ * m) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (L.inv_mem hℓL)) (Subgroup.mem_sup_right hN')
  have hMcard : Nat.card ↥(L ⊔ E) = Nat.card L * Nat.card E := card_sup_of_inf_eq_bot hEL hLE
  have hNcard2 : Nat.card N = Nat.card N₁ * Nat.card E := by
    have h := Sec52.card_sup_mul_card_inf (A := L) (C := N) (inf_le_left.trans hMN)
    have hLN₁ : L ⊓ N = N₁ := by rw [hNdef, ← inf_assoc, inf_eq_left.mpr hLM]
    rw [sup_comm, hLN, hLN₁, hMcard] at h
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos : 0 < Nat.card L)
    rw [← h]
    ring
  have hYcard : Nat.card Y = Nat.card W * Nat.card E := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos : 0 < Nat.card C)
    rw [← hNcard1, hNcard2, hD.card_N]
    ring
  have hWY : W ≤ Y := le_inf (le_inf (hD.W_le.trans hLM) (hWN₁.trans inf_le_right))
    Subgroup.le_normalizer
  obtain ⟨E₁, hE₁Y, -, -, hE₁card⟩ := exists_complement_in hWY inf_le_right
    (by rw [relIndex_eq_of_card hWY hYcard]; exact hcopW)
  have hE₁ : Nat.card E₁ = Nat.card E :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos (hE₁card.trans hYcard)
  have hYJ : Y ≤ Subgroup.centralizer ({J} : Set G) := by
    intro y hy
    have hyW : y * J * y⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp (inf_le_right (a := N) hy) J).mp hJW
    have h2 : orderOf (y * J * y⁻¹) = 2 := by rw [orderOf_conj_mul, hJ]
    have := eq_of_mem_of_cyclic_of_orderOf_two hD.W_cyc hyW hJW h2 hJ
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc y * J = y * J * y⁻¹ * y := by group
      _ = J * y := by rw [this]
  have hMJ : (L ⊔ E) ⊓ Subgroup.centralizer ({J} : Set G) ≤ Subgroup.zpowers J ⊔ (K' ⊔ E) := by
    intro x hx
    obtain ⟨hxM, hxJ⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨l, hl, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hEL).mp hxM
    have hlJ : l ∈ Subgroup.centralizer ({J} : Set G) := by
      have e' : l = l * e * e⁻¹ := by group
      rw [e']
      exact Subgroup.mul_mem _ hxJ (Subgroup.inv_mem _ (hEJ he))
    have hl' : l ∈ Subgroup.zpowers J ⊔ K' := hLJ ▸ Subgroup.mem_inf.mpr ⟨hl, hlJ⟩
    have h1 : Subgroup.zpowers J ⊔ K' ≤ Subgroup.zpowers J ⊔ (K' ⊔ E) :=
      sup_le_sup_left le_sup_left _
    exact Subgroup.mul_mem _ (h1 hl') (Subgroup.mem_sup_right (Subgroup.mem_sup_right he))
  have hK'E : K' ⊓ E = ⊥ := inf_eq_bot_of_coprime hcopK
  have hJKE : J ∉ K' ⊔ E := by
    intro hJm
    obtain ⟨k, hk, e, he, hke⟩ := (mem_sup_iff_of_le_normalizer hEK').mp hJm
    have he' : e ∈ Subgroup.zpowers J ⊔ K' := by
      have e' : e = k⁻¹ * J := by rw [← hke]; group
      rw [e']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (K'.inv_mem hk))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers J))
    have heK : e ∈ K' := mem_of_odd_of_mem_zpowers_sup' hJ hK'J hJK' he'
      (hEodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard E he))
    have he1 : e = 1 := by
      have := Subgroup.mem_inf.mpr ⟨heK, he⟩
      rwa [hK'E, Subgroup.mem_bot] at this
    rw [he1, mul_one] at hke
    exact hJK' (hke ▸ hk)
  have hE₁KE : E₁ ≤ K' ⊔ E := by
    intro x hx
    have hxY := hE₁Y hx
    have hxM : x ∈ L ⊔ E := (inf_le_left.trans inf_le_left : Y ≤ L ⊔ E) hxY
    have hx' := hMJ (Subgroup.mem_inf.mpr ⟨hxM, hYJ hxY⟩)
    have hodd : Odd (orderOf x) := hEodd.of_dvd_nat (hE₁ ▸ Subgroup.orderOf_dvd_natCard E₁ hx)
    exact mem_of_odd_of_mem_zpowers_sup' hJ (sup_le hK'J hEJ) hJKE hx' hodd
  have hZN : K' ⊔ E ≤ Subgroup.normalizer (K' : Set G) := sup_le Subgroup.le_normalizer hEK'
  have hZcard : Nat.card ↥(K' ⊔ E) = Nat.card K' * Nat.card E := card_sup_of_inf_eq_bot hEK' hK'E
  have hK'E₁ : K' ⊓ E₁ = ⊥ := inf_eq_bot_of_coprime (by rw [hE₁]; exact hcopK)
  have hK'E₁s : K' ⊔ E₁ = K' ⊔ E := by
    apply Subgroup.eq_of_le_of_card_ge (sup_le le_sup_left hE₁KE)
    rw [card_sup_of_inf_eq_bot (hE₁KE.trans hZN) hK'E₁, hE₁, hZcard]
  obtain ⟨k, hkK, hk⟩ := exists_conj_complement_in le_sup_left hZN
    (by rw [relIndex_eq_of_card le_sup_left hZcard]; exact hcopK)
    le_sup_right hE₁KE hK'E rfl hK'E₁ hK'E₁s
  have hE : E = Sec6.cj k⁻¹ E₁ := by rw [hk, cj_inv_cj]
  refine ⟨k, hkK, ?_, ?_⟩
  · rw [hE, ← cj_normalizer]
    exact cj_mono (hE₁Y.trans (inf_le_left.trans inf_le_right))
  · rw [hE, ← cj_normalizer]
    exact cj_mono (hE₁Y.trans inf_le_right)

end Sec6

end CFSG.Walter.W67
