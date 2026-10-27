module

public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22G

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped commutatorElement

namespace Lem22

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_zpowers_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {y : G} {k : ℕ}
    (hy : y ^ p ^ k = 1) : y ∈ Subgroup.zpowers (y ^ 2) := by
  have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
  obtain ⟨m, hm⟩ := hodd
  have e : y = (y ^ 2) ^ (m + 1) := by
    rw [← pow_mul]
    calc y = y ^ (p ^ k + 1) := by rw [pow_succ, hy, one_mul]
      _ = y ^ (2 * (m + 1)) := by rw [hm]; ring_nf
  have h1 : (y ^ 2) ^ (m + 1) ∈ Subgroup.zpowers (y ^ 2) :=
    (Subgroup.zpowers (y ^ 2)).pow_mem (Subgroup.mem_zpowers (y ^ 2)) (m + 1)
  rwa [← e] at h1

omit [Finite G] in
theorem isCyclic_of_card_frattini_le {P : Subgroup G} [Finite ↥P] {p : ℕ} (hp : p.Prime)
    (hPp : IsPGroup p ↥P) (hle : Nat.card (↥P ⧸ frattini ↥P) ≤ p) : IsCyclic ↥P := by
  have : Fact p.Prime := ⟨hp⟩
  have hq : IsPGroup p (↥P ⧸ frattini ↥P) := hPp.to_quotient _
  obtain ⟨k, hk⟩ := hq.exists_card_eq
  have hcyc : IsCyclic (↥P ⧸ frattini ↥P) := by
    rcases Nat.lt_or_ge k 1 with h | h
    · have hk0 : k = 0 := by omega
      rw [hk0, pow_zero] at hk
      have : Subsingleton (↥P ⧸ frattini ↥P) := (Nat.card_eq_one_iff_unique.mp hk).1
      exact isCyclic_of_subsingleton
    · have hk1 : k = 1 := by
        by_contra hne
        have : p ^ 2 ≤ p ^ k := Nat.pow_le_pow_right hp.pos (by omega)
        have hp1 : p < p ^ 2 := by
          have := hp.one_lt
          nlinarith
        omega
      rw [hk1, pow_one] at hk
      exact isCyclic_of_prime_card hk
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
  refine ⟨⟨x, fun y => ?_⟩⟩
  have htop : Subgroup.zpowers x ⊔ frattini ↥P = ⊤ := by
    rw [eq_top_iff]
    intro z _
    obtain ⟨m, hm⟩ := hg (z : ↥P ⧸ frattini ↥P)
    have hz : (x ^ m)⁻¹ * z ∈ frattini ↥P := by
      rw [← QuotientGroup.eq]
      simpa [QuotientGroup.mk_zpow] using hm
    have e : z = x ^ m * ((x ^ m)⁻¹ * z) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers x m))
      (Subgroup.mem_sup_right hz)
  have hx := frattini_nongenerating htop
  have hy : y ∈ Subgroup.zpowers x := by rw [hx]; exact Subgroup.mem_top y
  exact Subgroup.mem_zpowers_iff.mp hy

theorem le_centralizer_of_inv_frattini {P A M : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hPp : IsPGroup p ↥P) (hPnc : ¬ IsCyclic ↥P)
    (hPM : P ⊓ M = (frattini ↥P).map P.subtype) (hA2 : IsPGroup 2 ↥A)
    (hPA : P ≤ Subgroup.normalizer (A : Set G)) {n : G}
    (hnP : n ∈ Subgroup.normalizer (P : Set G))
    (hninv : ∀ x ∈ P, n * x * n⁻¹ * x ∈ (frattini ↥P).map P.subtype)
    (hcM : ∀ w ∈ A, w * (n * w * n⁻¹)⁻¹ ≠ 1 →
      Subgroup.centralizer ({w * (n * w * n⁻¹)⁻¹} : Set G) ≤ M) :
    A ⊓ Subgroup.centralizer (((frattini ↥P).map P.subtype : Subgroup G) : Set G) ≤
      Subgroup.centralizer (P : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (IsPGroup p ↥P) := ⟨hPp⟩
  set Φ := (frattini ↥P).map P.subtype with hΦdef
  set A₀ := A ⊓ Subgroup.centralizer (Φ : Set G) with hA₀
  have hΦP : Φ ≤ P := frattini_map_le P
  have hconjA : ∀ g ∈ Subgroup.normalizer (A : Set G), ∀ w ∈ A, g * w * g⁻¹ ∈ A :=
    fun g hg w hw => (Subgroup.mem_normalizer_iff.mp hg w).mp hw
  have hΦc : ∀ f ∈ Φ, ∀ w ∈ A₀, f * w * f⁻¹ = w := fun f hf w hw => by
    rw [(Subgroup.mem_centralizer_iff.mp hw.2) f hf, mul_inv_cancel_right]
  have hPA₀ : ∀ x ∈ Subgroup.normalizer (P : Set G), x ∈ Subgroup.normalizer (A : Set G) →
      ∀ w ∈ A₀, x * w * x⁻¹ ∈ A₀ := by
    intro x hxP hxA w hw
    refine ⟨hconjA x hxA w hw.1, Subgroup.mem_centralizer_iff.mpr fun f hf => ?_⟩
    have hf' : x⁻¹ * f * x ∈ Φ := by
      have := conj_mem_frattini (Subgroup.inv_mem _ hxP) hf
      rwa [inv_inv] at this
    have h1 := hΦc _ hf' w hw
    calc f * (x * w * x⁻¹) = x * ((x⁻¹ * f * x) * w * (x⁻¹ * f * x)⁻¹) * x⁻¹ * f := by group
      _ = x * w * x⁻¹ * f := by rw [h1]
  have hPA₀' : ∀ x ∈ P, ∀ w ∈ A₀, x * w * x⁻¹ ∈ A₀ := fun x hx =>
    hPA₀ x (Subgroup.le_normalizer hx) (hPA hx)
  have hny : ∀ y ∈ P, ∃ f ∈ Φ, n * y * n⁻¹ = f * y⁻¹ := fun y hy =>
    ⟨n * y * n⁻¹ * y, hninv y hy, by group⟩
  have hPM' : ∀ x ∈ P, x ∈ M → x ∈ Φ := fun x hxP hxM => by
    rw [← hPM]
    exact ⟨hxP, hxM⟩
  let ρ₀ : ↥P → (↥A₀ ≃* ↥A₀) := fun x =>
    { toFun := fun w => ⟨x * w * (x : G)⁻¹, hPA₀' x x.2 w w.2⟩
      invFun := fun w => ⟨(x : G)⁻¹ * w * x, by
        have := hPA₀' _ (P.inv_mem x.2) w w.2
        simpa using this⟩
      left_inv := fun w => Subtype.ext (by simp [mul_assoc])
      right_inv := fun w => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun w₁ w₂ => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        group) }
  let ρ : ↥P →* MulAut ↥A₀ :=
    { toFun := ρ₀
      map_one' := by
        ext w
        simp [ρ₀]
      map_mul' := fun x y => by
        ext w
        simp only [MulAut.mul_apply]
        show (x : G) * y * w * ((x : G) * y)⁻¹ = x * ((y : G) * w * (y : G)⁻¹) * (x : G)⁻¹
        group }
  have hρ : ∀ (x : ↥P) (w : ↥A₀), ((ρ x w : ↥A₀) : G) = x * w * (x : G)⁻¹ := fun _ _ => rfl
  have hker : frattini ↥P ≤ ρ.ker := by
    intro f hf
    rw [MonoidHom.mem_ker]
    ext w
    rw [hρ, MulAut.one_apply]
    exact hΦc f ⟨f, hf, rfl⟩ w w.2
  let ρ' : (↥P ⧸ frattini ↥P) →* MulAut ↥A₀ := QuotientGroup.lift (frattini ↥P) ρ hker
  let _ : MulDistribMulAction (↥P ⧸ frattini ↥P) ↥A₀ := MulDistribMulAction.compHom ↥A₀ ρ'
  have hsmul : ∀ (x : ↥P) (w : ↥A₀),
      (((x : ↥P ⧸ frattini ↥P) • w : ↥A₀) : G) = x * w * (x : G)⁻¹ := fun _ _ => rfl
  have : CFSG.IsElementaryAbelian p (↥P ⧸ frattini ↥P) :=
    CFSG.isElementaryAbelian_quotient_frattini
  have hcard : p ^ 2 ≤ Nat.card (↥P ⧸ frattini ↥P) := by
    have hq : IsPGroup p (↥P ⧸ frattini ↥P) := hPp.to_quotient _
    obtain ⟨k, hk⟩ := hq.exists_card_eq
    by_contra hlt
    push Not at hlt
    apply hPnc
    refine isCyclic_of_card_frattini_le hp hPp ?_
    rw [hk] at hlt ⊢
    rcases Nat.lt_or_ge k 2 with h | h
    · rcases Nat.lt_or_ge k 1 with h' | h'
      · have : k = 0 := by omega
        rw [this, pow_zero]
        exact hp.one_lt.le
      · have : k = 1 := by omega
        rw [this, pow_one]
    · exact absurd (Nat.pow_le_pow_right hp.pos h) (not_le.mpr hlt)
  have hA₀p : ¬ p ∣ Nat.card ↥A₀ := by
    have hA₀2 : IsPGroup 2 ↥A₀ := hA2.to_le inf_le_left
    obtain ⟨k, hk⟩ := hA₀2.exists_card_eq
    rw [hk]
    intro hd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hd))
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (p := p)
    (A := ↥P ⧸ frattini ↥P) (H := ↥A₀) hcard hA₀p
  by_cases hcase : ∃ a ∈ P, a ∉ Φ ∧ ∃ w ∈ A₀, a * w * a⁻¹ = w ∧ n * w * n⁻¹ ≠ w
  · exfalso
    obtain ⟨a, haP, haΦ, w, hwA₀, haw, hnw⟩ := hcase
    have hc1 : w * (n * w * n⁻¹)⁻¹ ≠ 1 := fun h0 =>
      hnw (by rw [mul_inv_eq_one] at h0; exact h0.symm)
    have ha' : n⁻¹ * a * n ∈ P := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hnP) a).mp haP
      simpa using this
    obtain ⟨f', hf', hf'e⟩ : ∃ f' ∈ Φ, n⁻¹ * a * n = a⁻¹ * f' := by
      refine ⟨a * (n⁻¹ * a * n), ?_, by group⟩
      have := hninv _ ha'
      have e : n * (n⁻¹ * a * n) * n⁻¹ * (n⁻¹ * a * n) = a * (n⁻¹ * a * n) := by group
      rwa [e] at this
    have haw' : a⁻¹ * w * a = w := by
      calc a⁻¹ * w * a = a⁻¹ * (a * w * a⁻¹) * a := by rw [haw]
        _ = w := by group
    have hu : a * (n * w * n⁻¹) * a⁻¹ = n * w * n⁻¹ := by
      have h1 := hΦc f' hf' w hwA₀
      calc a * (n * w * n⁻¹) * a⁻¹
          = n * ((n⁻¹ * a * n) * w * (n⁻¹ * a * n)⁻¹) * n⁻¹ := by group
        _ = n * (a⁻¹ * (f' * w * f'⁻¹) * a) * n⁻¹ := by rw [hf'e]; group
        _ = n * w * n⁻¹ := by rw [h1, haw']
    have hac : a ∈ Subgroup.centralizer ({w * (n * w * n⁻¹)⁻¹} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h2 : a * w = w * a := by
        calc a * w = (a * w * a⁻¹) * a := by group
          _ = w * a := by rw [haw]
      set u := n * w * n⁻¹ with hu'
      have h1 : a * u = u * a := by
        calc a * u = (a * u * a⁻¹) * a := by group
          _ = u * a := by rw [hu]
      have h1' : a * u⁻¹ = u⁻¹ * a := by
        calc a * u⁻¹ = u⁻¹ * (u * a) * u⁻¹ := by group
          _ = u⁻¹ * (a * u) * u⁻¹ := by rw [h1]
          _ = u⁻¹ * a := by group
      calc a * (w * u⁻¹) = (a * w) * u⁻¹ := (mul_assoc _ _ _).symm
        _ = (w * a) * u⁻¹ := by rw [h2]
        _ = w * (a * u⁻¹) := mul_assoc _ _ _
        _ = w * (u⁻¹ * a) := by rw [h1']
        _ = (w * u⁻¹) * a := (mul_assoc _ _ _).symm
    exact haΦ (hPM' a haP (hcM w hwA₀.1 hc1 hac))
  · push Not at hcase
    intro w hw
    have htop : (⊤ : Subgroup ↥A₀) ≤ (Subgroup.centralizer (P : Set G)).subgroupOf A₀ := by
      rw [← hgen]
      refine iSup₂_le fun e he w₀ hw₀ => ?_
      obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective e
      have haw : (a : G) * w₀ * (a : G)⁻¹ = w₀ := by
        have := (CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff _ w₀).mp hw₀
        exact congrArg Subtype.val this
      have haΦ : (a : G) ∉ Φ := fun h0 => he (by
        rw [QuotientGroup.eq_one_iff]
        obtain ⟨b, hb, hbe⟩ := h0
        have : b = a := Subtype.ext hbe
        rw [← this]
        exact hb)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
      intro y hy
      have hywA : y * w₀ * y⁻¹ ∈ A₀ := hPA₀' y hy w₀ w₀.2
      have hayw : (a : G) * (y * w₀ * y⁻¹) * (a : G)⁻¹ = y * w₀ * y⁻¹ := by
        obtain ⟨c, hc, hce⟩ : ∃ c ∈ Φ, (a : G) * y = y * a * c := by
          refine ⟨(a : G)⁻¹ * y⁻¹ * a * y, ?_, by group⟩
          have hcomm : ⁅(⟨(a : G)⁻¹, P.inv_mem a.2⟩ : ↥P), (⟨y⁻¹, P.inv_mem hy⟩ : ↥P)⁆ ∈
              frattini ↥P :=
            CFSG.commutator_le_frattini_of_isPGroup (p := p)
              (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
          refine ⟨_, hcomm, ?_⟩
          simp [commutatorElement_def]
        have h1 := hΦc c hc w₀ w₀.2
        calc (a : G) * (y * w₀ * y⁻¹) * (a : G)⁻¹
            = ((a : G) * y) * w₀ * ((a : G) * y)⁻¹ := by group
          _ = (y * a * c) * w₀ * (y * a * c)⁻¹ := by rw [hce]
          _ = y * ((a : G) * (c * w₀ * c⁻¹) * (a : G)⁻¹) * y⁻¹ := by group
          _ = y * w₀ * y⁻¹ := by rw [h1, haw]
      have hn1 := hcase a a.2 haΦ w₀ w₀.2 haw
      have hn2 := hcase a a.2 haΦ _ hywA hayw
      obtain ⟨f, hf, hfe⟩ := hny y hy
      have hy2 : y⁻¹ * w₀ * y = y * w₀ * y⁻¹ := by
        have hyw' : y⁻¹ * w₀ * y ∈ A₀ := by
          have := hPA₀' _ (P.inv_mem hy) w₀ w₀.2
          simpa using this
        have h1 := hΦc f hf _ hyw'
        calc y⁻¹ * w₀ * y = f * (y⁻¹ * w₀ * y) * f⁻¹ := h1.symm
          _ = (f * y⁻¹) * w₀ * (f * y⁻¹)⁻¹ := by group
          _ = (n * y * n⁻¹) * (n * w₀ * n⁻¹) * (n * y * n⁻¹)⁻¹ := by rw [hfe, hn1]
          _ = n * (y * w₀ * y⁻¹) * n⁻¹ := by group
          _ = y * w₀ * y⁻¹ := hn2
      have hsq : y ^ 2 ∈ Subgroup.centralizer ({(w₀ : G)} : Set G) := by
        rw [Subgroup.mem_centralizer_singleton_iff, pow_two]
        calc y * y * w₀ = y * (y * w₀ * y⁻¹) * y := by group
          _ = y * (y⁻¹ * w₀ * y) * y := by rw [hy2]
          _ = w₀ * (y * y) := by group
      obtain ⟨k, hk⟩ := hPp ⟨y, hy⟩
      have hk' : y ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hyC : y ∈ Subgroup.centralizer ({(w₀ : G)} : Set G) :=
        (Subgroup.zpowers_le.mpr hsq) (mem_zpowers_sq hp hp2 hk')
      exact Subgroup.mem_centralizer_singleton_iff.mp hyC
    have h1 := htop (Subgroup.mem_top (⟨w, hw⟩ : ↥A₀))
    exact Subgroup.mem_subgroupOf.mp h1

end Lem22

end CFSG.Quasithin.H13
