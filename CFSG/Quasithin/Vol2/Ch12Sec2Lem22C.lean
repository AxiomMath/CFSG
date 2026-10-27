module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderNilpotent
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Lem22

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_of_sq_mem {K : Subgroup G} {y : G} {p : ℕ} (hpodd : Odd p) (hyp : y ^ p = 1)
    (h2 : y ^ 2 ∈ K) : y ∈ K := by
  obtain ⟨k, hk⟩ := hpodd
  have e : y = (y ^ 2) ^ (k + 1) := by
    rw [← pow_mul]
    calc y = y ^ (p + 1) := by rw [pow_succ, hyp, one_mul]
      _ = y ^ (2 * (k + 1)) := by rw [hk]; ring_nf
  rw [e]
  exact K.pow_mem h2 _

theorem false_of_card_le {P A M : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hPe : ∀ x ∈ P, x ^ p = 1)
    (hcard : p ^ 2 ≤ Nat.card P) (hPM : P ⊓ M = ⊥) (hA : ¬ p ∣ Nat.card A)
    (hPA : P ≤ Subgroup.normalizer (A : Set G)) {n : G} (hninv : ∀ x ∈ P, n * x * n⁻¹ = x⁻¹)
    (hcM : ∀ w ∈ A, w * (n * w * n⁻¹)⁻¹ ≠ 1 →
      Subgroup.centralizer ({w * (n * w * n⁻¹)⁻¹} : Set G) ≤ M)
    {z : G} (hzA : z ∈ A) (hzM : Subgroup.centralizer ({z} : Set G) ≤ M) :
    False := by
  have : Fact p.Prime := ⟨hp⟩
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hPM' : ∀ x ∈ P, x ∈ M → x = 1 := fun x hxP hxM => by
    have : x ∈ P ⊓ M := ⟨hxP, hxM⟩
    rwa [hPM, Subgroup.mem_bot] at this
  have hconjA : ∀ g ∈ Subgroup.normalizer (A : Set G), ∀ w ∈ A, g * w * g⁻¹ ∈ A :=
    fun g hg w hw => (Subgroup.mem_normalizer_iff.mp hg w).mp hw
  let act : MulDistribMulAction ↥P ↥A :=
    { smul := fun x w => ⟨x * w * (x : G)⁻¹, hconjA x (hPA x.2) w w.2⟩
      one_smul := fun w => Subtype.ext (by
        change (1 : G) * (w : G) * (1 : G)⁻¹ = w
        simp)
      mul_smul := fun x y w => Subtype.ext (by
        change ((x : G) * y) * (w : G) * ((x : G) * y)⁻¹ =
          x * ((y : G) * w * (y : G)⁻¹) * (x : G)⁻¹
        group)
      smul_one := fun x => Subtype.ext (by
        change (x : G) * 1 * (x : G)⁻¹ = 1
        simp)
      smul_mul := fun x w₁ w₂ => Subtype.ext (by
        change (x : G) * ((w₁ : G) * w₂) * (x : G)⁻¹ =
          (x * w₁ * (x : G)⁻¹) * (x * w₂ * (x : G)⁻¹)
        group) }
  have : CFSG.IsElementaryAbelian p ↥P :=
    { toIsMulCommutative := ⟨⟨fun a b => Subtype.ext (hPc a a.2 b b.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hPe x x.2) }
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := p) (A := ↥P) (H := ↥A)
    hcard hA
  by_cases hcase : ∃ a ∈ P, a ≠ 1 ∧ ∃ w ∈ A, a * w * a⁻¹ = w ∧ n * w * n⁻¹ ≠ w
  · obtain ⟨a, haP, ha1, w, hwA, haw, hnw⟩ := hcase
    have hc1 : w * (n * w * n⁻¹)⁻¹ ≠ 1 := fun h0 =>
      hnw (by rw [mul_inv_eq_one] at h0; exact h0.symm)
    have hac : a ∈ Subgroup.centralizer ({w * (n * w * n⁻¹)⁻¹} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hna : n⁻¹ * a * n = a⁻¹ := by
        have h0 := hninv a haP
        calc n⁻¹ * a * n = (n⁻¹ * a⁻¹ * n)⁻¹ := by group
          _ = (n⁻¹ * (n * a * n⁻¹) * n)⁻¹ := by rw [h0]
          _ = a⁻¹ := by group
      have haw' : a⁻¹ * w * a = w := by
        calc a⁻¹ * w * a = a⁻¹ * (a * w * a⁻¹) * a := by rw [haw]
          _ = w := by group
      have h2 : a * w = w * a := by
        calc a * w = (a * w * a⁻¹) * a := by group
          _ = w * a := by rw [haw]
      set u := n * w * n⁻¹ with hu
      have h1 : a * u = u * a := by
        calc a * u = n * ((n⁻¹ * a * n) * w * (n⁻¹ * a * n)⁻¹) * n⁻¹ * a := by
              rw [hu]; group
          _ = n * (a⁻¹ * w * a) * n⁻¹ * a := by rw [hna, inv_inv]
          _ = u * a := by rw [haw', hu]
      have h1' : a * u⁻¹ = u⁻¹ * a := by
        calc a * u⁻¹ = u⁻¹ * (u * a) * u⁻¹ := by group
          _ = u⁻¹ * (a * u) * u⁻¹ := by rw [h1]
          _ = u⁻¹ * a := by group
      calc a * (w * u⁻¹) = (a * w) * u⁻¹ := (mul_assoc _ _ _).symm
        _ = (w * a) * u⁻¹ := by rw [h2]
        _ = w * (a * u⁻¹) := mul_assoc _ _ _
        _ = w * (u⁻¹ * a) := by rw [h1']
        _ = (w * u⁻¹) * a := (mul_assoc _ _ _).symm
    exact ha1 (hPM' a haP (hcM w hwA hc1 hac))
  · push Not at hcase
    have htop : (⊤ : Subgroup ↥A) ≤ (Subgroup.centralizer (P : Set G)).subgroupOf A := by
      rw [← hgen]
      refine iSup₂_le fun a ha w hw => ?_
      have haw : (a : G) * w * (a : G)⁻¹ = w := by
        have := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff a w).mp hw
        exact congrArg Subtype.val this
      have ha1 : (a : G) ≠ 1 := fun h0 => ha (Subtype.ext h0)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro y hy
      have hywA : y * w * y⁻¹ ∈ A := hconjA y (hPA hy) w w.2
      have hayw : (a : G) * (y * w * y⁻¹) * (a : G)⁻¹ = y * w * y⁻¹ := by
        have e := hPc a a.2 y hy
        calc (a : G) * (y * w * y⁻¹) * (a : G)⁻¹ = (a * y) * w * (a * y)⁻¹ := by group
          _ = (y * a) * w * (y * a)⁻¹ := by rw [e]
          _ = y * ((a : G) * w * (a : G)⁻¹) * y⁻¹ := by group
          _ = y * w * y⁻¹ := by rw [haw]
      have hn1 := hcase a a.2 ha1 w w.2 haw
      have hn2 := hcase a a.2 ha1 _ hywA hayw
      have hny := hninv y hy
      have hy2 : y⁻¹ * w * y = y * w * y⁻¹ := by
        have hn1' : n⁻¹ * w * n = w := by
          calc n⁻¹ * w * n = n⁻¹ * (n * w * n⁻¹) * n := by rw [hn1]
            _ = w := by group
        calc y⁻¹ * w * y = (n * y * n⁻¹) * w * (n * y * n⁻¹)⁻¹ := by rw [hny, inv_inv]
          _ = n * (y * (n⁻¹ * w * n) * y⁻¹) * n⁻¹ := by group
          _ = n * (y * w * y⁻¹) * n⁻¹ := by rw [hn1']
          _ = y * w * y⁻¹ := hn2
      have hsq : y ^ 2 ∈ Subgroup.centralizer ({(w : G)} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff, pow_two]
        calc y * y * w = y * (y * w * y⁻¹) * y := by group
          _ = y * (y⁻¹ * w * y) * y := by rw [hy2]
          _ = w * (y * y) := by group
      have hyC := mem_of_sq_mem hpodd (hPe y hy) hsq
      exact Subgroup.mem_centralizer_singleton_iff.mp hyC
    have hP1 : (⊥ : Subgroup G) ≠ P := by
      intro h0
      rw [← h0, Subgroup.card_bot] at hcard
      have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
      omega
    obtain ⟨⟨y, hyP⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Ne.symm hP1)
    have hyz : y ∈ Subgroup.centralizer ({z} : Set G) := by
      have h1 := htop (Subgroup.mem_top (⟨z, hzA⟩ : ↥A))
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at h1
      exact Subgroup.mem_centralizer_singleton_iff.mpr (h1 y hyP)
    exact hy1 (Subtype.ext (hPM' y hyP (hzM hyz)))

theorem exists_ne_one_mem_centralizer {T U : Subgroup G} (hT : IsPGroup 2 ↥T) (hUT : U ≤ T)
    (hUn : T ≤ Subgroup.normalizer (U : Set G)) (hU : U ≠ ⊥) :
    ∃ z ∈ U, z ≠ 1 ∧ z ∈ Subgroup.centralizer (T : Set G) := by
  have : Group.IsNilpotent ↥T := hT.isNilpotent
  have hnormal : (U.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hUn
  have hne : U.subgroupOf T ≠ ⊥ := by
    intro h
    apply hU
    rw [← Subgroup.map_subgroupOf_eq_of_le hUT, h, Subgroup.map_bot]
  obtain ⟨⟨y, hy⟩, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  refine ⟨y, hy.1, fun h0 => hy1 (Subtype.ext (Subtype.ext h0)), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy.2 ⟨t, ht⟩)

omit [Finite G] in
theorem frattini_eq_bot_of_isCyclic [Finite G] {P : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hPp : IsPGroup p ↥P) (hPcyc : IsCyclic ↥P) {h' : G} (hh'P : h' ∈ P) (hh'p : h' ^ p = 1)
    (hh'1 : h' ≠ 1) (hh'Φ : h' ∉ (frattini ↥P).map P.subtype) : frattini ↥P = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra hne
  have hΦp : IsPGroup p ↥(frattini ↥P) := hPp.to_subgroup _
  obtain ⟨k, hk⟩ := hΦp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hne (Subgroup.eq_bot_of_card_eq _ hk)
  have hzp : Nat.card (Subgroup.zpowers (⟨h', hh'P⟩ : ↥P)) = p := by
    rw [Nat.card_zpowers]
    refine orderOf_eq_prime (Subtype.ext (by simpa using hh'p)) fun h0 => hh'1 ?_
    exact congrArg Subtype.val h0
  have hle : Subgroup.zpowers (⟨h', hh'P⟩ : ↥P) ≤ frattini ↥P := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, hzp, hk]
    exact dvd_pow_self p hk0
  exact hh'Φ ⟨⟨h', hh'P⟩, hle (Subgroup.mem_zpowers _), rfl⟩

end Lem22

end CFSG.Quasithin.H13
