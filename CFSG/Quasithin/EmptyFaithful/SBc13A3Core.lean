module

public import CFSG.Quasithin.Background.A1cRank
public import CFSG.Quasithin.EmptyFaithful.S146P7

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace SBc13

section Conj

variable {Γ : Type*} [Group Γ]

theorem conj_eq_of_mem_zpowers_prime_A3 {p : ℕ} (hp : p.Prime) {a x : Γ} (ha : a ^ p = 1)
    (ha1 : a ≠ 1) (hx : x ^ p = 1) (h : x * a * x⁻¹ ∈ Subgroup.zpowers a) :
    x * a * x⁻¹ = a := by
  have : Fact p.Prime := ⟨hp⟩
  have hord : orderOf a = p := orderOf_eq_prime ha ha1
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h
  have key : ∀ k : ℕ, x ^ k * a * (x ^ k)⁻¹ = a ^ (n ^ k) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc x ^ (k + 1) * a * (x ^ (k + 1))⁻¹ = x * (x ^ k * a * (x ^ k)⁻¹) * x⁻¹ := by group
        _ = x * a ^ (n ^ k) * x⁻¹ := by rw [ih]
        _ = (x * a * x⁻¹) ^ (n ^ k) := conj_zpow.symm
        _ = (a ^ n) ^ (n ^ k) := by rw [← hn]
        _ = a ^ (n ^ (k + 1)) := by rw [← zpow_mul, pow_succ']
  have h1 : a ^ (1 : ℤ) = a ^ (n ^ p) := by
    have := key p
    rw [hx, inv_one, mul_one, one_mul] at this
    rw [zpow_one]
    exact this
  have h2 : (1 : ℤ) ≡ n ^ p [ZMOD p] := by
    have := zpow_eq_zpow_iff_modEq.mp h1
    rwa [hord] at this
  have h3 : (n : ZMod p) = 1 := by
    have h4 : ((1 : ℤ) : ZMod p) = ((n ^ p : ℤ) : ZMod p) :=
      (ZMod.intCast_eq_intCast_iff _ _ _).mpr h2
    push_cast at h4
    rw [ZMod.pow_card] at h4
    exact h4.symm
  have h5 : n ≡ 1 [ZMOD p] := (ZMod.intCast_eq_intCast_iff _ _ _).mp (by simpa using h3)
  have h6 : a ^ n = a ^ (1 : ℤ) := by
    rw [zpow_eq_zpow_iff_modEq, hord]
    exact h5
  rw [← hn, h6, zpow_one]

end Conj

section Lift

theorem pow_eq_one_of_mem_closure_A3 {Γ : Type*} [Group Γ] {p : ℕ} {s : Set Γ}
    (hs : ∀ g ∈ s, g ^ p = 1) (hsc : ∀ g ∈ s, ∀ h ∈ s, g * h = h * g) :
    ∀ y ∈ Subgroup.closure s, y ^ p = 1 := by
  intro y hy
  have key : y ^ p = 1 ∧ ∀ g ∈ s, Commute y g := by
    induction hy using Subgroup.closure_induction with
    | mem x hx => exact ⟨hs x hx, fun g hg => hsc x hx g hg⟩
    | one => exact ⟨by simp, fun g _ => Commute.one_left g⟩
    | mul x y' hx hy' ihx ihy =>
      have hle : Subgroup.closure s ≤ Subgroup.centralizer {x} := by
        rw [Subgroup.closure_le]
        intro g hg
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact (ihx.2 g hg).eq
      have hcom : Commute x y' := by
        have := Subgroup.mem_centralizer_iff.mp (hle hy') x rfl
        exact this
      exact ⟨by rw [hcom.mul_pow, ihx.1, ihy.1, one_mul],
        fun g hg => (ihx.2 g hg).mul_left (ihy.2 g hg)⟩
    | inv x hx ih => exact ⟨by rw [inv_pow, ih.1, inv_one], fun g hg => (ih.2 g hg).inv_left⟩
  exact key.1

variable {Y : Type*} [Group Y] [Finite Y]

theorem lift_three_prime_A3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Subgroup Y} [R.Normal]
    (hR2 : IsPGroup 2 R) {g₁ g₂ g₃ : Y} (h₁ : g₁ ^ p ∈ R) (h₂ : g₂ ^ p ∈ R) (h₃ : g₃ ^ p ∈ R)
    (c₁₂ : g₁ * g₂ * g₁⁻¹ * g₂⁻¹ ∈ R) (c₁₃ : g₁ * g₃ * g₁⁻¹ * g₃⁻¹ ∈ R)
    (c₂₃ : g₂ * g₃ * g₂⁻¹ * g₃⁻¹ ∈ R) :
    ∃ b₁ b₂ b₃ : Y, b₁ * g₁⁻¹ ∈ R ∧ b₂ * g₂⁻¹ ∈ R ∧ b₃ * g₃⁻¹ ∈ R ∧
      b₁ ^ p = 1 ∧ b₂ ^ p = 1 ∧ b₃ ^ p = 1 ∧
      b₁ * b₂ = b₂ * b₁ ∧ b₁ * b₃ = b₃ * b₁ ∧ b₂ * b₃ = b₃ * b₂ := by
  classical
  let π : Y →* Y ⧸ R := QuotientGroup.mk' R
  have hπ1 : ∀ y : Y, π y = 1 ↔ y ∈ R := fun y => QuotientGroup.eq_one_iff y
  have hcomΓ : ∀ y z : Y, y * z * y⁻¹ * z⁻¹ ∈ R → π y * π z = π z * π y := by
    intro y z h
    have h1 := (hπ1 _).mpr h
    simp only [map_mul, map_inv] at h1
    have h2 : π y * π z * (π y)⁻¹ = π z := mul_inv_eq_one.mp h1
    calc π y * π z = (π y * π z * (π y)⁻¹) * π y := by group
      _ = π z * π y := by rw [h2]
  have hpow : ∀ y : Y, y ^ p ∈ R → π y ^ p = 1 := by
    intro y h
    rw [← map_pow]
    exact (hπ1 _).mpr h
  set s : Set (Y ⧸ R) := {π g₁, π g₂, π g₃} with hs
  have hs3 : ∀ g ∈ s, g ^ p = 1 := by
    intro g hg
    rcases hg with rfl | rfl | rfl
    · exact hpow _ h₁
    · exact hpow _ h₂
    · exact hpow _ h₃
  have hsc : ∀ g ∈ s, ∀ h ∈ s, g * h = h * g := by
    intro g hg h hh
    have hc₁₂ := hcomΓ _ _ c₁₂
    have hc₁₃ := hcomΓ _ _ c₁₃
    have hc₂₃ := hcomΓ _ _ c₂₃
    rcases hg with rfl | rfl | rfl <;> rcases hh with rfl | rfl | rfl
    · rfl
    · exact hc₁₂
    · exact hc₁₃
    · exact hc₁₂.symm
    · rfl
    · exact hc₂₃
    · exact hc₁₃.symm
    · exact hc₂₃.symm
    · rfl
  set X : Subgroup Y := (Subgroup.closure s).comap π with hX
  have hXnQ : ∀ g ∈ X, ∀ q ∈ R, g * q * g⁻¹ ∈ R := fun g _ q hq =>
    Subgroup.Normal.conj_mem inferInstance q hq g
  have hXQ : ∀ x ∈ X, ∃ k : ℕ, x ^ p ^ k ∈ R := by
    intro x hx
    refine ⟨1, ?_⟩
    have := pow_eq_one_of_mem_closure_A3 hs3 hsc _ hx
    rw [pow_one, ← hπ1, map_pow]
    exact this
  obtain ⟨P, hPX, hPodd, hPQ⟩ := exists_pComplement_P7 hp hp2 hXnQ hXQ
  have hPR : ∀ z ∈ P, z ∈ R → z = 1 := by
    intro z hzP hzR
    have hd1 : orderOf z ∣ Nat.card P := by
      have := Subgroup.orderOf_dvd_natCard P hzP
      exact this
    have hodd : Odd (orderOf z) := hPodd.of_dvd_nat hd1
    obtain ⟨k, hk⟩ := hR2 ⟨z, hzR⟩
    have hk' : z ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hd2 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hcop : Nat.Coprime (orderOf z) (2 ^ k) := (Odd.coprime_two_right hodd).pow_right k
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcop hd2)
  have hg₁X : g₁ ∈ X := Subgroup.mem_comap.mpr (Subgroup.subset_closure (by simp [hs]))
  have hg₂X : g₂ ∈ X := Subgroup.mem_comap.mpr (Subgroup.subset_closure (by simp [hs]))
  have hg₃X : g₃ ∈ X := Subgroup.mem_comap.mpr (Subgroup.subset_closure (by simp [hs]))
  obtain ⟨b₁, hb₁P, q₁, hq₁, e₁⟩ := hPQ g₁ hg₁X
  obtain ⟨b₂, hb₂P, q₂, hq₂, e₂⟩ := hPQ g₂ hg₂X
  obtain ⟨b₃, hb₃P, q₃, hq₃, e₃⟩ := hPQ g₃ hg₃X
  have hbπ : ∀ (b g q : Y), g = b * q → q ∈ R → π b = π g := by
    intro b g q h hq
    rw [h, map_mul, (hπ1 q).mpr hq, mul_one]
  have hπ₁ := hbπ _ _ _ e₁ hq₁
  have hπ₂ := hbπ _ _ _ e₂ hq₂
  have hπ₃ := hbπ _ _ _ e₃ hq₃
  have hbR : ∀ (b g : Y), π b = π g → b * g⁻¹ ∈ R := by
    intro b g h
    apply (hπ1 _).mp
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have hpowb : ∀ (b g : Y), π b = π g → g ^ p ∈ R → b ∈ P → b ^ p = 1 := by
    intro b g h hg3 hbP
    apply hPR _ (P.pow_mem hbP p)
    apply (hπ1 _).mp
    rw [map_pow, h, ← map_pow]
    exact (hπ1 _).mpr hg3
  have hcommb : ∀ (u v u' v' : Y), π u = π u' → π v = π v' →
      u' * v' * u'⁻¹ * v'⁻¹ ∈ R → u ∈ P → v ∈ P → u * v = v * u := by
    intro u v u' v' hu hv hc huP hvP
    have h1 : u * v * u⁻¹ * v⁻¹ ∈ R := by
      apply (hπ1 _).mp
      have := (hπ1 _).mpr hc
      simp only [map_mul, map_inv] at this ⊢
      rw [hu, hv]
      exact this
    have h2 : u * v * u⁻¹ * v⁻¹ ∈ P :=
      P.mul_mem (P.mul_mem (P.mul_mem huP hvP) (P.inv_mem huP)) (P.inv_mem hvP)
    have h3 := hPR _ h2 h1
    have h4 : u * v * u⁻¹ = v := mul_inv_eq_one.mp h3
    calc u * v = (u * v * u⁻¹) * u := by group
      _ = v * u := by rw [h4]
  refine ⟨b₁, b₂, b₃, hbR _ _ hπ₁, hbR _ _ hπ₂, hbR _ _ hπ₃, hpowb _ _ hπ₁ h₁ hb₁P,
    hpowb _ _ hπ₂ h₂ hb₂P, hpowb _ _ hπ₃ h₃ hb₃P, hcommb _ _ _ _ hπ₁ hπ₂ c₁₂ hb₁P hb₂P,
    hcommb _ _ _ _ hπ₁ hπ₃ c₁₃ hb₁P hb₃P, hcommb _ _ _ _ hπ₂ hπ₃ c₂₃ hb₂P hb₃P⟩

end Lift

section Rank

variable {Y : Type*} [Group Y] [Finite Y]

theorem false_of_three_commuting_prime_A3 {p : ℕ} (hp : p.Prime)
    (hY : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2) {x₁ x₂ x₃ : Y} (h₂ : orderOf x₂ = p)
    (h₃ : orderOf x₃ = p) (h₁ : orderOf x₁ = p) (c₁₂ : Commute x₁ x₂) (c₁₃ : Commute x₁ x₃)
    (c₂₃ : Commute x₂ x₃) (i₃ : x₃ ∉ Subgroup.zpowers x₂)
    (i₁ : x₁ ∉ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hbot : IsElemAbelian p (⊥ : Subgroup Y) :=
    ⟨inferInstance, fun x hx => by rw [Subgroup.mem_bot.1 hx, one_pow]⟩
  have hx₂ : x₂ ∉ (⊥ : Subgroup Y) := fun h => by
    have := Subgroup.mem_bot.1 h
    rw [this] at h₂
    simp only [orderOf_one] at h₂
    exact hp.one_lt.ne h₂
  obtain ⟨hE₁, hc₁⟩ := exists_elemAbelian_sup_zpowers hbot h₂
    (fun e he => by rw [Subgroup.mem_bot.1 he]; exact Commute.one_left _) hx₂
  have hcomm₃ : ∀ e ∈ (⊥ ⊔ Subgroup.zpowers x₂ : Subgroup Y), Commute e x₃ := by
    intro e he
    rw [bot_sup_eq] at he
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 he
    exact c₂₃.zpow_left k
  have hx₃ : x₃ ∉ (⊥ ⊔ Subgroup.zpowers x₂ : Subgroup Y) := by
    rw [bot_sup_eq]
    exact i₃
  obtain ⟨hE₂, hc₂⟩ := exists_elemAbelian_sup_zpowers hE₁ h₃ hcomm₃ hx₃
  have hcomm₁ : ∀ e ∈ (⊥ ⊔ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃ : Subgroup Y),
      Commute e x₁ := by
    intro e he
    rw [bot_sup_eq] at he
    have hle : Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃ ≤ Subgroup.centralizer {x₁} := by
      refine sup_le ?_ ?_
      · refine Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
        rw [Set.mem_singleton_iff.1 hh]
        exact c₁₂.eq
      · refine Subgroup.zpowers_le.2 (Subgroup.mem_centralizer_iff.2 fun h hh => ?_)
        rw [Set.mem_singleton_iff.1 hh]
        exact c₁₃.eq
    exact (Subgroup.mem_centralizer_iff.1 (hle he) x₁ rfl).symm
  have hx₁ : x₁ ∉ (⊥ ⊔ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃ : Subgroup Y) := by
    rw [bot_sup_eq]
    exact i₁
  obtain ⟨hE₃, hc₃⟩ := exists_elemAbelian_sup_zpowers hE₂ h₁ hcomm₁ hx₁
  have hcard : Nat.card ↥(⊥ ⊔ Subgroup.zpowers x₂ ⊔ Subgroup.zpowers x₃ ⊔ Subgroup.zpowers x₁ :
      Subgroup Y) = p ^ 3 := by
    rw [hc₃, hc₂, hc₁, Subgroup.card_bot]
    ring
  have h3 : 3 ≤ CFSG.Open.pRank p (⊤ : Subgroup Y) := le_pRank hp le_top hE₃ hcard
  omega

end Rank

section Core

variable {Y : Type*} [Group Y] [Finite Y]

theorem core_prime_A3 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K R : Subgroup Y} {a₁ a₂ x : Y}
    (hrank : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 2) (hR2 : IsPGroup 2 R)
    (hRn : ∀ g : Y, ∀ r ∈ R, g * r * g⁻¹ ∈ R) (hRK : R ≤ K) (ha₁K : a₁ ∈ K) (ha₂K : a₂ ∈ K)
    (ha₁p : a₁ ^ p = 1) (ha₂p : a₂ ^ p = 1) (ha₁R : a₁ ∉ R) (ha₂R : a₂ ∉ R)
    (hcomm : a₁ * a₂ * a₁⁻¹ * a₂⁻¹ ∈ R) (hind : ∀ m : ℤ, a₁ ^ m * a₂⁻¹ ∈ R → False)
    (hxp : x ^ p = 1) (hxK : x ∉ K) (hxa₁ : ∃ n : ℤ, x * a₁ * x⁻¹ * (a₁ ^ n)⁻¹ ∈ R)
    (hxa₂ : ∃ n : ℤ, x * a₂ * x⁻¹ * (a₂ ^ n)⁻¹ ∈ R) : False := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : R.Normal := ⟨fun n hn g => hRn g n hn⟩
  let π : Y →* Y ⧸ R := QuotientGroup.mk' R
  have hπ1 : ∀ y : Y, π y = 1 ↔ y ∈ R := fun y => QuotientGroup.eq_one_iff y
  have hxR : x ∉ R := fun h => hxK (hRK h)
  have hxΓ : π x ^ p = 1 := by rw [← map_pow, hxp, map_one]
  have hconj : ∀ a : Y, a ^ p = 1 → a ∉ R → (∃ n : ℤ, x * a * x⁻¹ * (a ^ n)⁻¹ ∈ R) →
      a * x * a⁻¹ * x⁻¹ ∈ R := by
    intro a hap haR hn
    obtain ⟨n, hn⟩ := hn
    have h1 : π x * π a * (π x)⁻¹ ∈ Subgroup.zpowers (π a) := by
      have h0 := (hπ1 _).mpr hn
      simp only [map_mul, map_inv, map_zpow] at h0
      exact ⟨n, (mul_inv_eq_one.mp h0).symm⟩
    have h2 := conj_eq_of_mem_zpowers_prime_A3 hp (by rw [← map_pow, hap, map_one])
      (fun h => haR ((hπ1 _).mp h)) hxΓ h1
    apply (hπ1 _).mp
    simp only [map_mul, map_inv]
    have h3 : π x * π a = π a * π x := by
      calc π x * π a = (π x * π a * (π x)⁻¹) * π x := by group
        _ = π a * π x := by rw [h2]
    calc π a * π x * (π a)⁻¹ * (π x)⁻¹ = (π x * π a) * (π a)⁻¹ * (π x)⁻¹ := by rw [h3]
      _ = 1 := by group
  have hc13 := hconj a₁ ha₁p ha₁R hxa₁
  have hc23 := hconj a₂ ha₂p ha₂R hxa₂
  obtain ⟨b₁, b₂, b₃, hb₁, hb₂, hb₃, hb₁p, hb₂p, hb₃p, hb₁₂, hb₁₃, hb₂₃⟩ :=
    lift_three_prime_A3 hp hp2 hR2 (g₁ := a₁) (g₂ := a₂) (g₃ := x)
      (by rw [ha₁p]; exact R.one_mem) (by rw [ha₂p]; exact R.one_mem)
      (by rw [hxp]; exact R.one_mem) hcomm hc13 hc23
  have hπb : ∀ b g : Y, b * g⁻¹ ∈ R → π b = π g := by
    intro b g h
    have := (hπ1 _).mpr h
    simp only [map_mul, map_inv] at this
    exact mul_inv_eq_one.mp this
  have hπb₁ := hπb _ _ hb₁
  have hπb₂ := hπb _ _ hb₂
  have hπb₃ := hπb _ _ hb₃
  have hb₁1 : b₁ ≠ 1 := fun h => ha₁R ((hπ1 _).mp (by rw [← hπb₁, h, map_one]))
  have hb₂1 : b₂ ≠ 1 := fun h => ha₂R ((hπ1 _).mp (by rw [← hπb₂, h, map_one]))
  have hb₃1 : b₃ ≠ 1 := fun h => hxR ((hπ1 _).mp (by rw [← hπb₃, h, map_one]))
  have hb₁K : b₁ ∈ K := by
    have e : b₁ = (b₁ * a₁⁻¹) * a₁ := by group
    rw [e]
    exact K.mul_mem (hRK hb₁) ha₁K
  have hb₂K : b₂ ∈ K := by
    have e : b₂ = (b₂ * a₂⁻¹) * a₂ := by group
    rw [e]
    exact K.mul_mem (hRK hb₂) ha₂K
  refine false_of_three_commuting_prime_A3 hp hrank (x₁ := b₃) (x₂ := b₁) (x₃ := b₂)
    (orderOf_eq_prime hb₁p hb₁1) (orderOf_eq_prime hb₂p hb₂1) (orderOf_eq_prime hb₃p hb₃1)
    hb₁₃.symm hb₂₃.symm hb₁₂ ?_ ?_
  · intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h
    refine hind k ((hπ1 _).mp ?_)
    rw [map_mul, map_inv, map_zpow, ← hπb₁, ← hπb₂, ← hk, map_zpow, mul_inv_cancel]
  · intro h
    have hle : Subgroup.zpowers b₁ ⊔ Subgroup.zpowers b₂ ≤ K :=
      sup_le (Subgroup.zpowers_le.mpr hb₁K) (Subgroup.zpowers_le.mpr hb₂K)
    have hb₃K : b₃ ∈ K := hle h
    apply hxK
    have e : x = (x * b₃⁻¹) * b₃ := by group
    rw [e]
    refine K.mul_mem (hRK ?_) hb₃K
    have := R.inv_mem hb₃
    simpa using this

end Core

end SBc13

end CFSG.Quasithin
