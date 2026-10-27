module

public import Mathlib.GroupTheory.PGroup

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.FinalChain.IndexDichotomy

variable {G : Type*} [Group G]

theorem mem_of_conj_mem_coset [Finite G] {H M R X : Subgroup G} (hRM : R ≤ M)
    (hR2 : IsPGroup 2 R) (hRn : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) (hXH : X ≤ H)
    (hXodd : Odd (Nat.card X)) (hCX : ∀ x ∈ X, x ≠ 1 → ∀ g ∈ M, g * x = x * g → g ∈ R)
    {w : G} (hwX : w ∈ X) (hw1 : w ≠ 1) {m : G} (hmM : m ∈ M)
    (hfix : m⁻¹ * (w * m * w⁻¹) ∈ R) : m ∈ R := by
  let S : Subgroup G :=
    { carrier := {g | g ∈ H ∧ m⁻¹ * (g * m * g⁻¹) ∈ R}
      mul_mem' := by
        rintro a b ⟨haH, ha⟩ ⟨hbH, hb⟩
        refine ⟨H.mul_mem haH hbH, ?_⟩
        convert R.mul_mem ha (hRn a haH _ hb) using 1
        group
      one_mem' := ⟨H.one_mem, by simp⟩
      inv_mem' := by
        rintro a ⟨haH, ha⟩
        refine ⟨H.inv_mem haH, ?_⟩
        convert hRn a⁻¹ (H.inv_mem haH) _ (R.inv_mem ha) using 1
        group }
  have hwS : w ∈ S := ⟨hXH hwX, hfix⟩
  have hw0 : orderOf w ≠ 1 := fun h => hw1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hp, hpw⟩ : ∃ p : ℕ, p.Prime ∧ p ∣ orderOf w :=
    ⟨_, Nat.minFac_prime hw0, Nat.minFac_dvd _⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨w', hw'X, hw'S, hw'⟩ : ∃ w' : G, w' ∈ X ∧ w' ∈ S ∧ orderOf w' = p :=
    ⟨w ^ (orderOf w / p), X.pow_mem hwX _, S.pow_mem hwS _,
      orderOf_pow_orderOf_div (orderOf_pos w).ne' hpw⟩
  have hw'1 : w' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hw'
    exact hp.one_lt.ne hw'
  have hp2 : p ≠ 2 := by
    intro h2
    have hdvd : p ∣ Nat.card X := hpw.trans (Subgroup.orderOf_dvd_natCard X hwX)
    rw [h2] at hdvd
    exact (Nat.not_even_iff_odd.mpr hXodd) (even_iff_two_dvd.mpr hdvd)
  let P := Subgroup.zpowers w'
  have hPS : P ≤ S := Subgroup.zpowers_le.mpr hw'S
  have hP : IsPGroup p P := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hw', pow_one])
  have hact : ∀ c : P, ∀ a : {g : G // m⁻¹ * g ∈ R},
      m⁻¹ * ((c : G) * a * (c : G)⁻¹) ∈ R := by
    intro c a
    obtain ⟨hcH, hc⟩ := hPS c.2
    convert R.mul_mem hc (hRn c hcH _ a.2) using 1
    group
  let _ : MulAction P {g : G // m⁻¹ * g ∈ R} :=
    { smul := fun c a => ⟨(c : G) * a * (c : G)⁻¹, hact c a⟩
      one_smul := fun a => Subtype.ext (by
        change ((1 : P) : G) * a * ((1 : P) : G)⁻¹ = a
        simp)
      mul_smul := fun c d a => Subtype.ext (by
        change ((c * d : P) : G) * a * ((c * d : P) : G)⁻¹ = c * (d * a * (d : G)⁻¹) * (c : G)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group) }
  have hcard : Nat.card {g : G // m⁻¹ * g ∈ R} = Nat.card R :=
    Nat.card_congr
      { toFun := fun a => ⟨m⁻¹ * a, a.2⟩
        invFun := fun r => ⟨m * r, by simp⟩
        left_inv := fun a => Subtype.ext (by simp)
        right_inv := fun r => Subtype.ext (by simp) }
  obtain ⟨k, hk⟩ := hR2.exists_card_eq
  have hndvd : ¬p ∣ Nat.card {g : G // m⁻¹ * g ∈ R} := by
    rw [hcard, hk]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  obtain ⟨⟨g, hg⟩, hgfix⟩ := hP.nonempty_fixed_point_of_prime_not_dvd_card _ hndvd
  have hgw : w' * g * w'⁻¹ = g :=
    congrArg Subtype.val (hgfix ⟨w', Subgroup.mem_zpowers w'⟩)
  have hgM : g ∈ M := by
    have h := M.mul_mem hmM (hRM hg)
    rwa [mul_inv_cancel_left] at h
  have hgR : g ∈ R := hCX w' hw'X hw'1 g hgM (mul_inv_eq_iff_eq_mul.mp hgw).symm
  have h := R.mul_mem hgR (R.inv_mem hg)
  rwa [mul_inv_rev, inv_inv, mul_inv_cancel_left] at h

theorem eq_of_conj_mem_coset [Finite G] {H M R X : Subgroup G} (hRM : R ≤ M)
    (hR2 : IsPGroup 2 R) (hRn : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) (hXH : X ≤ H)
    (hXodd : Odd (Nat.card X)) (hCX : ∀ x ∈ X, x ≠ 1 → ∀ g ∈ M, g * x = x * g → g ∈ R)
    {m : G} (hmM : m ∈ M) (hmR : m ∉ R) {x y : G} (hx : x ∈ X) (hy : y ∈ X)
    (hxy : (x * m * x⁻¹)⁻¹ * (y * m * y⁻¹) ∈ R) : x = y := by
  by_contra hne
  refine hmR (mem_of_conj_mem_coset hRM hR2 hRn hXH hXodd hCX (X.mul_mem (X.inv_mem hx) hy)
    (fun h => hne (inv_mul_eq_one.mp h)) hmM ?_)
  convert hRn x⁻¹ (H.inv_mem (hXH hx)) _ hxy using 1
  group

theorem card_add_one_le_relIndex_of_not_mem [Finite G] {H M R X : Subgroup G} (hRM : R ≤ M)
    (hMn : ∀ h ∈ H, ∀ g ∈ M, h * g * h⁻¹ ∈ M) (hR2 : IsPGroup 2 R)
    (hRn : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) (hXH : X ≤ H) (hXodd : Odd (Nat.card X))
    (hCX : ∀ x ∈ X, x ≠ 1 → ∀ g ∈ M, g * x = x * g → g ∈ R) {m : G} (hmM : m ∈ M)
    (hmR : m ∉ R) :
    Nat.card X + 1 ≤ R.relIndex M ∧
      (R.relIndex M ≤ Nat.card X + 1 →
        ∀ m' ∈ M, m' ∉ R → ∃ x ∈ X, m'⁻¹ * (x * m * x⁻¹) ∈ R) := by
  have hmk : ∀ a b : M, (QuotientGroup.mk a : ↥M ⧸ R.subgroupOf M) = QuotientGroup.mk b ↔
      (a : G)⁻¹ * b ∈ R := fun a b => by
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
  have hout : ∀ x ∈ X, x * m * x⁻¹ ∉ R := by
    intro x hx hmem
    apply hmR
    convert hRn x⁻¹ (H.inv_mem (hXH hx)) _ hmem using 1
    group
  let f : Option X → ↥M ⧸ R.subgroupOf M := fun o =>
    o.elim (QuotientGroup.mk 1) fun x =>
      QuotientGroup.mk ⟨x * m * (x : G)⁻¹, hMn x (hXH x.2) m hmM⟩
  have hf : Function.Injective f := by
    rintro (_ | x) (_ | y) hxy
    · rfl
    · exfalso
      have h : (1 : G)⁻¹ * (y * m * (y : G)⁻¹) ∈ R := (hmk _ _).mp hxy
      rw [inv_one, one_mul] at h
      exact hout y y.2 h
    · exfalso
      have h : (x * m * (x : G)⁻¹)⁻¹ * 1 ∈ R := (hmk _ _).mp hxy
      rw [mul_one] at h
      exact hout x x.2 (inv_mem_iff.mp h)
    · have h : (x * m * (x : G)⁻¹)⁻¹ * (y * m * (y : G)⁻¹) ∈ R := (hmk _ _).mp hxy
      exact congrArg some
        (Subtype.ext (eq_of_conj_mem_coset hRM hR2 hRn hXH hXodd hCX hmM hmR x.2 y.2 h))
  have hcard := Nat.card_le_card_of_injective f hf
  rw [Finite.card_option] at hcard
  refine ⟨hcard, fun hle m' hm'M hm'R => ?_⟩
  have hbij := hf.bijective_of_nat_card_le (by rw [Finite.card_option]; exact hle)
  obtain ⟨o, ho⟩ := hbij.2 (QuotientGroup.mk ⟨m', hm'M⟩)
  cases o with
  | none =>
    have h : (1 : G)⁻¹ * m' ∈ R := (hmk _ _).mp ho
    rw [inv_one, one_mul] at h
    exact absurd h hm'R
  | some x =>
    have h : (x * m * (x : G)⁻¹)⁻¹ * m' ∈ R := (hmk _ _).mp ho
    refine ⟨x, x.2, ?_⟩
    convert R.inv_mem h using 1
    group

end CFSG.ShultStronglyClosedTI.FinalChain.IndexDichotomy
