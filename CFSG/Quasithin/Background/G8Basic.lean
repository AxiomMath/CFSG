module

public import CFSG.LocalAnalysis.ComponentClassification.CoprimeAutomorphisms
public import CFSG.Quasithin.Background.A1cRank
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

open scoped Pointwise

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type*} [Group G]

structure G81 (X P A : Subgroup G) : Prop where
  elemAbelian : IsElemAbelian 2 A
  le_pGroup : A ≤ P
  pGroup : IsPGroup 2 P
  le_normalizer : P ≤ Subgroup.normalizer (X : Set G)
  nilpotent : Group.IsNilpotent X
  odd : Odd (Nat.card X)
  ne_bot : X ≠ ⊥

namespace G8

theorem eq_one_of_mem_of_odd {R X : Subgroup G} (hR : IsPGroup 2 R) (hX : Odd (Nat.card X))
    {x : G} (hxR : x ∈ R) (hxX : x ∈ X) : x = 1 := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hR ⟨x, hxR⟩
  have h1 : orderOf x = 2 ^ k := by rw [← Subgroup.orderOf_mk x hxR]; exact hk
  have h2 : orderOf x ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hxX
  have hcop : Nat.Coprime (2 ^ k) (Nat.card X) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hX)
  have h3 : orderOf x ∣ 1 := by
    have h4 : orderOf x ∣ 2 ^ k := by rw [h1]
    have := Nat.dvd_gcd h4 h2
    rwa [hcop.gcd_eq_one] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem eq_one_of_pow_two_pow_eq_one {X : Subgroup G} (hX : Odd (Nat.card X)) {x : G}
    (hx : x ∈ X) {m : ℕ} (h : x ^ 2 ^ m = 1) : x = 1 := by
  have h1 : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h
  have h2 : orderOf x ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X hx
  have hcop : Nat.Coprime (2 ^ m) (Nat.card X) :=
    Nat.Coprime.pow_left m (Nat.coprime_two_left.mpr hX)
  have h3 := Nat.dvd_gcd h1 h2
  rw [hcop.gcd_eq_one] at h3
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3)

theorem mem_normalizer_of_conj_mem {H : Subgroup G} {g : G} (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) : g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  simpa [mul_assoc] using this

theorem centralizer_sup (U N : Subgroup G) :
    Subgroup.centralizer ((U ⊔ N : Subgroup G) : Set G) =
      Subgroup.centralizer (U : Set G) ⊓ Subgroup.centralizer (N : Set G) := by
  apply le_antisymm
  · exact le_inf (Subgroup.centralizer_le (by exact_mod_cast le_sup_left))
      (Subgroup.centralizer_le (by exact_mod_cast le_sup_right))
  · intro x hx
    have hU : U ≤ Subgroup.centralizer {x} := fun u hu =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hx.1 u hu)
    have hN : N ≤ Subgroup.centralizer {x} := fun u hu =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hx.2 u hu)
    intro y hy
    have := sup_le hU hN hy
    exact Subgroup.mem_centralizer_singleton_iff.mp this

section Finite

variable [Finite G]

theorem centralizes_of_self_centralizing {X U R : Subgroup G} (hXn : Group.IsNilpotent X)
    (hXodd : Odd (Nat.card X)) (hUX : U ≤ X)
    (hself : X ⊓ Subgroup.centralizer (U : Set G) ≤ U) (hR : IsPGroup 2 R)
    (hRX : R ≤ Subgroup.normalizer (X : Set G)) (hRU : R ≤ Subgroup.centralizer (U : Set G)) :
    R ≤ Subgroup.centralizer (X : Set G) := by
  intro r hr
  have hK : Subgroup.zpowers r ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.zpowers_le.mpr (hRX hr)
  set α : MulAut X := conjAut hK ⟨r, Subgroup.mem_zpowers r⟩ with hα
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hR ⟨r, hr⟩
  have hord : orderOf r = 2 ^ k := by rw [← Subgroup.orderOf_mk r hr]; exact hk
  have hpow : α ^ orderOf r = 1 := by
    have : (⟨r, Subgroup.mem_zpowers r⟩ : Subgroup.zpowers r) ^ orderOf r = 1 := by
      apply Subtype.ext
      simp [pow_orderOf_eq_one]
    rw [hα, ← map_pow, this, map_one]
  have hcop : (orderOf r).Coprime (Nat.card X) := by
    rw [hord]; exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hXodd)
  have hself' : Subgroup.centralizer ((U.subgroupOf X : Subgroup X) : Set X) ≤ U.subgroupOf X := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    apply hself
    refine ⟨x.2, ?_⟩
    show (x : G) ∈ Subgroup.centralizer (U : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have := Subgroup.mem_centralizer_iff.mp hx ⟨u, hUX hu⟩ (Subgroup.mem_subgroupOf.mpr hu)
    exact congrArg Subtype.val this
  have hfix : ∀ u ∈ U.subgroupOf X, α u = u := by
    intro u hu
    apply Subtype.ext
    have hu' : (u : G) ∈ U := Subgroup.mem_subgroupOf.mp hu
    have hc := Subgroup.mem_centralizer_iff.mp (hRU hr) (u : G) hu'
    have hcoe : ((α u : X) : G) = r * (u : G) * r⁻¹ := by
      rw [hα]; exact conjAut_apply_coe hK ⟨r, Subgroup.mem_zpowers r⟩ u
    rw [hcoe, ← hc]
    simp
  have : Group.IsNilpotent X := hXn
  have h1 : α = 1 :=
    CFSG.ComponentClassification.CoprimeAutomorphisms.eq_one_of_self_centralizing_nilpotent
      (U.subgroupOf X) hself' α (orderOf r) hpow hcop hfix
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have h2 := congrArg (fun β : MulAut X => ((β ⟨x, hx⟩ : X) : G)) h1
  have h3 : r * x * r⁻¹ = x := by
    have h4 : ((α ⟨x, hx⟩ : X) : G) = r * x * r⁻¹ := by
      rw [hα]; exact conjAut_apply_coe hK ⟨r, Subgroup.mem_zpowers r⟩ ⟨x, hx⟩
    rw [← h4]
    exact h2
  calc x * r = r * x * r⁻¹ * r := by rw [h3]
    _ = r * x := by group

theorem g8_3_of {X P U : Subgroup G} (hXn : Group.IsNilpotent X) (hXodd : Odd (Nat.card X))
    (hP : IsPGroup 2 P) (hPX : P ≤ Subgroup.normalizer (X : Set G)) (hUX : U ≤ X) :
    pCoreOf 2 (Subgroup.centralizer (U : Set G) ⊓ (X ⊔ P)) = pCoreOf 2 (X ⊔ P) := by
  set M := X ⊔ P with hM
  have hXM : X ≤ M := le_sup_left
  have hPM : P ≤ M := le_sup_right
  have hMX : M ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hPX
  set K := Subgroup.centralizer (U : Set G) ⊓ M with hK
  have hKM : K ≤ M := inf_le_right
  apply le_antisymm
  · set R := pCoreOf 2 K with hR
    have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 K
    have hRK : R ≤ K := pCoreOf_le 2 K
    have hRnorm : K ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pCoreOf 2 K
    set N := X ⊓ Subgroup.centralizer (U : Set G) with hN
    have hNK : N ≤ K := fun n hn => ⟨hn.2, hXM hn.1⟩
    have hKN : K ≤ Subgroup.normalizer (N : Set G) := by
      have key : ∀ k' ∈ K, ∀ n ∈ N, k' * n * k'⁻¹ ∈ N := by
        intro k' hk' n hn
        have hk'X : k' ∈ Subgroup.normalizer (X : Set G) := hMX hk'.2
        refine ⟨(Subgroup.mem_normalizer_iff.mp hk'X n).mp hn.1, ?_⟩
        show k' * n * k'⁻¹ ∈ Subgroup.centralizer (U : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have h1 : Commute u k' := Subgroup.mem_centralizer_iff.mp hk'.1 u hu
        have h2 : Commute u n := Subgroup.mem_centralizer_iff.mp hn.2 u hu
        exact (h1.mul_right h2).mul_right h1.inv_right
      intro k hk
      exact mem_normalizer_of_conj_mem (key k hk) (by
        intro x hx
        have := key k⁻¹ (K.inv_mem hk) x hx
        simpa using this)
    have hRN : R ≤ Subgroup.centralizer (N : Set G) := by
      intro r hr
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have hc : r * n * r⁻¹ * n⁻¹ = 1 := by
        apply eq_one_of_mem_of_odd (R := R) hR2 hXodd (X := X)
        · have h1 : n * r⁻¹ * n⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hRnorm (hNK hn)) r⁻¹).mp
            (R.inv_mem hr)
          have := R.mul_mem hr h1
          simpa [mul_assoc] using this
        · have h1 : r * n * r⁻¹ ∈ N := by
            have hrK := hRK hr
            exact (Subgroup.mem_normalizer_iff.mp (hKN hrK) n).mp hn
          exact (N.mul_mem h1 (N.inv_mem hn)).1
      have h2 : r * n * r⁻¹ = n := mul_inv_eq_one.mp hc
      calc n * r = r * n * r⁻¹ * r := by rw [h2]
        _ = r * n := by group
    have hRU : R ≤ Subgroup.centralizer (U : Set G) := hRK.trans inf_le_left
    have hUN : U ⊔ N ≤ X := sup_le hUX inf_le_left
    have hself : X ⊓ Subgroup.centralizer ((U ⊔ N : Subgroup G) : Set G) ≤ U ⊔ N := by
      intro x hx
      rw [centralizer_sup] at hx
      exact le_sup_right (a := U) (b := N) ⟨hx.1, hx.2.1⟩
    have hRC : R ≤ Subgroup.centralizer ((U ⊔ N : Subgroup G) : Set G) := by
      rw [centralizer_sup]; exact le_inf hRU hRN
    have hRX : R ≤ Subgroup.centralizer (X : Set G) :=
      centralizes_of_self_centralizing hXn hXodd hUN hself hR2 (hRK.trans (hKM.trans hMX)) hRC
    have hRP : R ≤ P := by
      intro r hr
      have hrM : r ∈ M := hKM (hRK hr)
      have hcoe : (↑(X ⊔ P) : Set G) = (X : Set G) * (P : Set G) :=
        Subgroup.coe_mul_of_right_le_normalizer_left X P hPX
      have hrM' : r ∈ ((X : Set G) * (P : Set G)) := by rw [← hcoe]; exact hrM
      obtain ⟨x, hx, p, hp, rfl⟩ := Set.mem_mul.mp hrM'
      have hcomm : Commute x p := by
        have h1 := Subgroup.mem_centralizer_iff.mp (hRX hr) x hx
        have h2 : x * (x * p) = x * (p * x) := h1.trans (mul_assoc x p x)
        exact mul_left_cancel h2
      obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.mp hR2 ⟨x * p, hr⟩
      obtain ⟨b, hb⟩ := IsPGroup.iff_orderOf.mp hP ⟨p, hp⟩
      have hra : (x * p) ^ 2 ^ a = 1 := by
        have : orderOf (x * p) = 2 ^ a := by rw [← Subgroup.orderOf_mk (x * p) hr]; exact ha
        rw [← this]; exact pow_orderOf_eq_one _
      have hpb : p ^ 2 ^ b = 1 := by
        have : orderOf p = 2 ^ b := by rw [← Subgroup.orderOf_mk p hp]; exact hb
        rw [← this]; exact pow_orderOf_eq_one _
      have hxm : x ^ 2 ^ (a + b) = 1 := by
        have h1 : (x * p) ^ 2 ^ (a + b) = 1 := by
          rw [pow_add, pow_mul, hra, one_pow]
        have h2 : p ^ 2 ^ (a + b) = 1 := by
          rw [pow_add, mul_comm, pow_mul, hpb, one_pow]
        rw [hcomm.mul_pow, h2, mul_one] at h1
        exact h1
      have hx1 : x = 1 := eq_one_of_pow_two_pow_eq_one hXodd hx hxm
      rw [hx1, one_mul]; exact hp
    set T := P ⊓ Subgroup.centralizer (X : Set G) with hT
    have hTM : T ≤ M := inf_le_left.trans hPM
    have hTX : ∀ t ∈ T, ∀ y ∈ X, Commute y t := fun t ht y hy =>
      Subgroup.mem_centralizer_iff.mp ht.2 y hy
    have hXT : X ≤ Subgroup.normalizer (T : Set G) := by
      intro x hx
      refine mem_normalizer_of_conj_mem (fun t ht => ?_) (fun t ht => ?_)
      · have h := (hTX t ht x hx).eq
        rw [h]; simpa using ht
      · have h := (hTX t ht x⁻¹ (X.inv_mem hx)).eq
        rw [h]; simpa using ht
    have hPT : P ≤ Subgroup.normalizer (T : Set G) := by
      have key : ∀ p' ∈ P, ∀ t ∈ T, p' * t * p'⁻¹ ∈ T := by
        intro p' hp' t ht
        refine ⟨?_, ?_⟩
        · exact P.mul_mem (P.mul_mem hp' ht.1) (P.inv_mem hp')
        · show p' * t * p'⁻¹ ∈ Subgroup.centralizer (X : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          have hy' : p'⁻¹ * y * p' ∈ X := (Subgroup.mem_normalizer_iff''.mp (hPX hp') y).mp hy
          have hc := (hTX t ht _ hy').eq
          calc y * (p' * t * p'⁻¹) = p' * ((p'⁻¹ * y * p') * t) * p'⁻¹ := by group
            _ = p' * (t * (p'⁻¹ * y * p')) * p'⁻¹ := by rw [hc]
            _ = (p' * t * p'⁻¹) * y := by group
      intro p' hp'
      exact mem_normalizer_of_conj_mem (key p' hp') (by
        intro t ht
        have := key p'⁻¹ (P.inv_mem hp') t ht
        simpa using this)
    have hMT : M ≤ Subgroup.normalizer (T : Set G) := sup_le hXT hPT
    have hTle : T ≤ pCoreOf 2 M :=
      le_pCoreOf_of_le_normalizer 2 hTM hMT (hP.to_le inf_le_left)
    intro r hr
    exact hTle ⟨hRP hr, hRX hr⟩
  ·
    set R₀ := pCoreOf 2 M with hR₀
    have hR02 : IsPGroup 2 R₀ := pCoreOf_isPGroup 2 M
    have hR0M : R₀ ≤ M := pCoreOf_le 2 M
    have hR0norm : M ≤ Subgroup.normalizer (R₀ : Set G) := le_normalizer_pCoreOf 2 M
    have hR0X : R₀ ≤ Subgroup.centralizer (X : Set G) := by
      intro r hr
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hc : x * r * x⁻¹ * r⁻¹ = 1 := by
        apply eq_one_of_mem_of_odd (R := R₀) hR02 hXodd (X := X)
        · have h1 : x * r * x⁻¹ ∈ R₀ := (Subgroup.mem_normalizer_iff.mp (hR0norm (hXM hx)) r).mp hr
          exact R₀.mul_mem h1 (R₀.inv_mem hr)
        · have h1 : r * x⁻¹ * r⁻¹ ∈ X :=
            (Subgroup.mem_normalizer_iff.mp (hMX (hR0M hr)) x⁻¹).mp (X.inv_mem hx)
          have := X.mul_mem hx h1
          simpa [mul_assoc] using this
      have h2 : x * r * x⁻¹ = r := mul_inv_eq_one.mp hc
      calc x * r = x * r * x⁻¹ * x := by group
        _ = r * x := by rw [h2]
    have hR0K : R₀ ≤ K := fun r hr =>
      ⟨Subgroup.centralizer_le hUX (hR0X hr), hR0M hr⟩
    exact le_pCoreOf_of_le_normalizer 2 hR0K (hKM.trans hR0norm) hR02

theorem g8_4_of {X Q Y : Subgroup G} (hXn : Group.IsNilpotent X) (hXodd : Odd (Nat.card X))
    (hQ : IsPGroup 2 Q) (hQX : Q ≤ Subgroup.normalizer (X : Set G)) (hYX : Y ≤ X)
    (hQY : Q ≤ Subgroup.centralizer (Y : Set G))
    (hfaith : Q ⊓ Subgroup.centralizer (X : Set G) = ⊥) :
    Q ⊓ Subgroup.centralizer ((X ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G) = ⊥ := by
  set N := X ⊓ Subgroup.centralizer (Y : Set G) with hN
  set B := Q ⊓ Subgroup.centralizer (N : Set G) with hB
  have hBQ : B ≤ Q := inf_le_left
  have hUX : N ⊔ Y ≤ X := sup_le inf_le_left hYX
  have hself : X ⊓ Subgroup.centralizer ((N ⊔ Y : Subgroup G) : Set G) ≤ N ⊔ Y := by
    intro x hx
    rw [centralizer_sup] at hx
    exact le_sup_left (a := N) (b := Y) ⟨hx.1, hx.2.2⟩
  have hBc : B ≤ Subgroup.centralizer ((N ⊔ Y : Subgroup G) : Set G) := by
    rw [centralizer_sup]
    exact le_inf inf_le_right (hBQ.trans hQY)
  have := centralizes_of_self_centralizing hXn hXodd hUX hself (hQ.to_le hBQ)
    (hBQ.trans hQX) hBc
  rw [eq_bot_iff]
  intro x hx
  have hx1 : x ∈ Q ⊓ Subgroup.centralizer (X : Set G) := ⟨hx.1, this hx⟩
  rw [hfaith] at hx1
  exact hx1

end Finite

end G8

section Finite

variable [Finite G]

theorem g8_3 {X P A : Subgroup G} (h : G81 X P A) {U : Subgroup G} (hUX : U ≤ X) :
    pCoreOf 2 (Subgroup.centralizer (U : Set G) ⊓ (X ⊔ P)) = pCoreOf 2 (X ⊔ P) :=
  G8.g8_3_of h.nilpotent h.odd h.pGroup h.le_normalizer hUX

theorem g8_4 {X P A : Subgroup G} (h : G81 X P A) {Y : Subgroup G} (hYX : Y ≤ X)
    (hPY : P ≤ Subgroup.centralizer (Y : Set G))
    (hfaith : P ⊓ Subgroup.centralizer (X : Set G) = ⊥) :
    P ⊓ Subgroup.centralizer ((X ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G) = ⊥ :=
  G8.g8_4_of h.nilpotent h.odd h.pGroup h.le_normalizer hYX hPY hfaith

end Finite

end CFSG.Quasithin
