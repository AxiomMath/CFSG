module

public import CFSG.Quasithin.Background.A1cA132Action

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.SectionRank.Ccomm

namespace A1c

section Irreducible

variable {G : Type*} [Group G]

@[expose] def IsNormalizerIrreducible (P : Subgroup G) : Prop :=
  frattiniIn P ≠ P ∧ ∀ U : Subgroup G, frattiniIn P ≤ U → U ≤ P →
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (U : Set G) →
    U = frattiniIn P ∨ U = P

theorem inf_le_frattiniIn_or_le [Finite G] {P M : Subgroup G} [M.Normal]
    (hirr : IsNormalizerIrreducible P) : (∀ y ∈ M, y ∈ P → y ∈ frattiniIn P) ∨ P ≤ M := by
  rcases eq_frattini_or_eq_top_of_ambient hirr.2 (U₀ := M.subgroupOf P ⊔ frattini ↥P)
    le_sup_right ((isNInv_subgroupOf ‹M.Normal›).sup (isNInv_frattini P)) with h | h
  · left
    intro y hy hyP
    have h1 : (⟨y, hyP⟩ : ↥P) ∈ M.subgroupOf P ⊔ frattini ↥P :=
      Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 hy)
    rw [h] at h1
    exact ⟨⟨y, hyP⟩, h1, rfl⟩
  · right
    exact Subgroup.subgroupOf_eq_top.1 (frattini_nongenerating h)

end Irreducible

section Rank

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime]

theorem two_lt_pRank_of_centralizing {Q : Subgroup G} (hQ : pRank p Q = 2) {x : G}
    (hxp : orderOf x = p) (hxc : ∀ y ∈ Q, x * y = y * x) (hxQ : x ∉ Q) :
    2 < pRank p (⊤ : Subgroup G) := by
  obtain ⟨E, hEQ, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.out.one_lt Q
  obtain ⟨hA, hAcard⟩ := exists_elemAbelian_sup_zpowers hE hxp
    (fun e he => (hxc e (hEQ he)).symm) (fun h => hxQ (hEQ h))
  have h3 := le_pRank hp.out (le_top : E ⊔ Subgroup.zpowers x ≤ ⊤) hA (k := 3)
    (by rw [hAcard, hcard, hQ]; ring)
  omega

end Rank

section Action

variable {G : Type*} [Group G] [Finite G] {r p : ℕ} [hr : Fact r.Prime] [hp : Fact p.Prime]

theorem conjNormal_mem_ker_of_irreducible (hr2 : r ≠ 2) (hp2 : p ≠ 2) {R : Subgroup G} [R.Normal]
    (hRr : IsPGroup r ↥R) (hRexp : ∀ x : ↥R, x ^ r = 1) (hRrk : pRank r (⊤ : Subgroup ↥R) ≤ 2)
    {P : Subgroup G} (hPexp : ∀ x ∈ P, x ^ p = 1) (hΦ : (frattini ↥P).index = p ^ 2)
    (hirr : ∀ U₀ : Subgroup ↥P, frattini ↥P ≤ U₀ → IsNInv P U₀ → U₀ = frattini ↥P ∨ U₀ = ⊤)
    {x : G} (hx : x ∈ P) :
    (MulAut.conjNormal x : MulAut ↥R) ∈ (autQuotient (frattini ↥R)).ker := by
  have : Fact (IsPGroup r ↥R) := ⟨hRr⟩
  have hWel := CFSG.isElementaryAbelian_quotient_frattini (R := ↥R) (p := r)
  have hWc : ∀ a b : ↥R ⧸ frattini ↥R, a * b = b * a := fun a b => mul_comm' a b
  have hWr : ∀ w : ↥R ⧸ frattini ↥R, w ^ r = 1 := fun w =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (CFSG.IsElementaryAbelian.exponent_dvd_p r _) w
  have hWcard : Nat.card (↥R ⧸ frattini ↥R) ≤ r ^ 2 :=
    (rank_two_exponent_prime_order_bound (p := r) hRr hRexp hRrk).2
  let ρ : G →* MulAut (↥R ⧸ frattini ↥R) :=
    (autQuotient (frattini ↥R)).comp MulAut.conjNormal
  exact action_trivial_of_irreducible hr2 hp2 hPexp hΦ hirr hWc hWr hWcard ρ hx

theorem conjNormal_eq_one_of_coprime (hrp : r ≠ p) {R : Subgroup G} [R.Normal]
    (hRr : IsPGroup r ↥R) {x : G} (hx : x ^ p = 1)
    (hker : (MulAut.conjNormal x : MulAut ↥R) ∈ (autQuotient (frattini ↥R)).ker) :
    (MulAut.conjNormal x : MulAut ↥R) = 1 := by
  have hK : IsPGroup r (autQuotient (frattini ↥R)).ker := isPGroup_ker_autQuotient_frattini hRr
  set g : (autQuotient (frattini ↥R)).ker := ⟨MulAut.conjNormal x, hker⟩ with hg
  have hgp : g ^ p = 1 := by
    apply Subtype.ext
    show (MulAut.conjNormal x : MulAut ↥R) ^ p = 1
    rw [← map_pow, hx, map_one]
  obtain ⟨k, hk⟩ := hK g
  have hcop : Nat.Coprime (r ^ k) p :=
    Nat.Coprime.pow_left k ((Nat.coprime_primes hr.out hp.out).2 hrp)
  have h1 : orderOf g = 1 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hk)
    (orderOf_dvd_of_pow_eq_one hgp)
  exact congrArg Subtype.val (orderOf_eq_one_iff.1 h1)

omit [Finite G] in
theorem conjNormal_eq_one_of_frattini_eq_bot {R : Subgroup G} [R.Normal] (hΦ : frattini ↥R = ⊥)
    {x : G} (hker : (MulAut.conjNormal x : MulAut ↥R) ∈ (autQuotient (frattini ↥R)).ker) :
    (MulAut.conjNormal x : MulAut ↥R) = 1 := by
  ext y
  have h := (mem_ker_autQuotient (frattini ↥R)).1 hker y
  rw [hΦ, Subgroup.mem_bot, inv_mul_eq_one] at h
  rw [MulAut.one_apply]
  exact congrArg Subtype.val h.symm

omit [Finite G] in
theorem mul_comm_of_conjNormal_eq_one {R : Subgroup G} [R.Normal] {x : G}
    (h : (MulAut.conjNormal x : MulAut ↥R) = 1) {y : G} (hy : y ∈ R) : x * y = y * x := by
  have h1 := congrArg (fun α : MulAut ↥R => ((α ⟨y, hy⟩ : ↥R) : G)) h
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1

theorem mem_sup_centralizer_of_isPOnePlusTwo {R : Subgroup G} [R.Normal] (hR : IsPOnePlusTwo p ↥R)
    {x : G} (hker : (MulAut.conjNormal x : MulAut ↥R) ∈ (autQuotient (frattini ↥R)).ker) :
    x ∈ R ⊔ Subgroup.centralizer (R : Set G) := by
  have := hR.1
  rw [← range_conj_eq_ker_autQuotient_frattini (p := p) (P := ↥R)] at hker
  obtain ⟨y, hy⟩ := hker
  have hz : (y : G)⁻¹ * x ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have h1 := congrArg (fun α : MulAut ↥R => ((α ⟨w, hw⟩ : ↥R) : G)) hy
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      at h1
    calc w * ((y : G)⁻¹ * x) = (y : G)⁻¹ * ((y : G) * w * (y : G)⁻¹) * x := by group
      _ = (y : G)⁻¹ * (x * w * x⁻¹) * x := by rw [h1]
      _ = ((y : G)⁻¹ * x) * w := by group
  have hxy : x = (y : G) * ((y : G)⁻¹ * x) := by group
  rw [hxy]
  exact Subgroup.mul_mem_sup y.2 hz

end Action

end A1c

end CFSG.Quasithin
