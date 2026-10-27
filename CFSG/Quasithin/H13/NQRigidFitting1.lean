module

public import CFSG.Quasithin.SteinbergBTTwoSpaceExponentPrime
public import CFSG.LocalAnalysis.SectionRank.Ccomm.Supercritical
public import CFSG.LocalAnalysis.SectionRank.Ccomm.RankTwo
public import CFSG.Quasithin.H13.NQSetupPlaneAction

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup Module
open scoped IsMulCommutative

variable {H : Type*} [Group H] [Finite H]

omit [Finite H] in
theorem mem_normalizer_of_conj_mem {Y : Subgroup H} {n : H}
    (h1 : ∀ y ∈ Y, n * y * n⁻¹ ∈ Y) (h2 : ∀ y ∈ Y, n⁻¹ * y * n⁻¹⁻¹ ∈ Y) :
    n ∈ normalizer (Y : Set H) := by
  rw [mem_normalizer_iff]
  intro y
  refine ⟨h1 y, fun hy => ?_⟩
  have := h2 _ hy
  simpa [mul_assoc] using this

theorem irreducible_Frattini_normalizer_coprime_two_space_triviality {p : ℕ} (hp : p.Prime)
    (_hp2 : p ≠ 2) {P : Subgroup H} (hP : IsPGroup p P) (hPexp : ∀ x ∈ P, x ^ p = 1)
    (hdim : p ^ 2 ≤ (frattini P).index)
    (hirr : ∀ Y : Subgroup H, (frattini P).map P.subtype ≤ Y → Y ≤ P →
      normalizer (P : Set H) ≤ normalizer (Y : Set H) →
      Y = (frattini P).map P.subtype ∨ Y = P)
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (hk : ringChar k ≠ p) (hV : finrank k V ≤ 2) (ρ : H →* LinearMap.GeneralLinearGroup k V) :
    P.map ρ = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set A := P.map ρ with hA
  have hAfin : Finite A := by
    have : Finite (Set.range fun x : P => ρ x) := Set.finite_range _ |>.to_subtype
    refine Finite.of_surjective (fun x : P => (⟨ρ x, x, x.2, rfl⟩ : A)) ?_
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hA2 : IsPGroup p A := hP.map ρ
  have hAexp : ∀ a ∈ A, a ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hPexp x hx, map_one]
  obtain ⟨-, -, hAcard, hAel, hline, -⟩ :=
    SteinbergBT.coprime_two_space_exponent_prime_determinant_bound hp hk hV A hA2 hAexp
  set f : P →* LinearMap.GeneralLinearGroup k V := ρ.comp P.subtype with hf
  have hfrange : f.range = A := by rw [hf, MonoidHom.range_comp, range_subtype]
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    have := hAel.toIsMulCommutative
    intro x hx y hy
    exact congrArg Subtype.val (mul_comm (⟨x, hx⟩ : A) ⟨y, hy⟩)
  have hΦker : frattini P ≤ f.ker := by
    have h1 := CFSG.SectionRank.Ccomm.frattini_le_ker_of_elementary (p := p) f.rangeRestrict
      (fun a b => Subtype.ext (hcommA _ (hfrange ▸ a.2) _ (hfrange ▸ b.2)))
      (fun a => Subtype.ext (hAexp _ (hfrange ▸ a.2)))
    rwa [MonoidHom.ker_rangeRestrict] at h1
  set Y₁ := f.ker.map P.subtype with hY₁
  have hY₁eq : Y₁ = P ⊓ ρ.ker := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    · rintro ⟨hyP, hyk⟩
      exact ⟨⟨y, hyP⟩, hyk, rfl⟩
  have hN₁ : normalizer (P : Set H) ≤ normalizer (Y₁ : Set H) := by
    rw [hY₁eq]
    have hktop : normalizer (ρ.ker : Set H) = ⊤ := normalizer_eq_top_iff.mpr inferInstance
    refine le_trans (le_inf le_rfl ?_) inf_normalizer_le_normalizer_inf
    rw [hktop]
    exact le_top
  rcases hirr Y₁ (map_mono hΦker) (map_subtype_le _) hN₁ with h1 | h1
  ·
    exfalso
    have hker : f.ker = frattini P := map_injective P.subtype_injective h1
    have hAcard2 : Nat.card A = p ^ 2 := by
      have e := (QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hfrange)
      have h2 : Nat.card (P ⧸ f.ker) = (frattini P).index := by rw [hker]; rfl
      rw [← Nat.card_congr e.toEquiv, h2]
      exact le_antisymm (h2 ▸ (Nat.card_congr e.toEquiv) ▸ hAcard) hdim
    obtain ⟨-, hΛcard, -, hΛn⟩ := hline hAcard2
    set Λ := A ⊓ (Units.map (LinearMap.det : (V →ₗ[k] V) →* k)).ker with hΛ
    set Y₂ := Λ.comap ρ ⊓ P with hY₂
    have hρN : ∀ n ∈ normalizer (P : Set H), ρ n ∈ normalizer (A : Set
        (LinearMap.GeneralLinearGroup k V)) := fun n hn => le_normalizer_map ρ ⟨n, hn, rfl⟩
    have hN₂ : normalizer (P : Set H) ≤ normalizer (Y₂ : Set H) := by
      intro n hn
      refine mem_normalizer_of_conj_mem (fun y hy => ?_) (fun y hy => ?_)
      · obtain ⟨hyΛ, hyP⟩ := mem_inf.mp hy
        refine mem_inf.mpr ⟨?_, (mem_normalizer_iff.mp hn y).mp hyP⟩
        rw [mem_comap, map_mul, map_mul, map_inv]
        exact hΛn _ (hρN n hn) _ hyΛ
      · obtain ⟨hyΛ, hyP⟩ := mem_inf.mp hy
        refine mem_inf.mpr ⟨?_, (mem_normalizer_iff.mp (inv_mem hn) y).mp hyP⟩
        rw [mem_comap, map_mul, map_mul, map_inv]
        have h3 := hΛn _ (inv_mem (hρN n hn)) _ hyΛ
        simp only [inv_inv] at h3 ⊢
        exact h3
    have hΦY₂ : (frattini P).map P.subtype ≤ Y₂ := by
      rintro _ ⟨x, hx, rfl⟩
      refine mem_inf.mpr ⟨?_, x.2⟩
      rw [mem_comap]
      have hx1 : ρ x = 1 := hΦker hx
      rw [show ρ (P.subtype x) = ρ x from rfl, hx1]
      exact one_mem _
    rcases hirr Y₂ hΦY₂ inf_le_right hN₂ with h2 | h2
    ·
      have hΛbot : Λ = ⊥ := by
        rw [eq_bot_iff]
        intro a ha
        obtain ⟨x, hx, rfl⟩ := (mem_inf.mp ha).1
        have hxY : x ∈ Y₂ := mem_inf.mpr ⟨ha, hx⟩
        rw [h2] at hxY
        obtain ⟨y, hy, rfl⟩ := hxY
        exact (mem_bot).mpr (hΦker hy)
      rw [hΛbot, card_bot] at hΛcard
      exact hp.one_lt.ne hΛcard
    ·
      have hAΛ : A ≤ Λ := by
        rintro _ ⟨x, hx, rfl⟩
        have hxY : x ∈ Y₂ := h2 ▸ hx
        exact (mem_inf.mp hxY).1
      have : Finite Λ := Nat.finite_of_card_ne_zero (by rw [hΛcard]; exact hp.ne_zero)
      have := card_le_of_le hAΛ
      rw [hAcard2, hΛcard] at this
      have h3 : p < p ^ 2 := by
        calc p = p ^ 1 := (pow_one p).symm
          _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      omega
  ·
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hxY : x ∈ Y₁ := h1 ▸ hx
    rw [hY₁eq] at hxY
    exact (mem_bot).mpr (mem_inf.mp hxY).2

theorem irreducible_exponent_prime_normalizer_centralizes_coprime_rank_two_core {p r : ℕ}
    (hp : p.Prime) (hr : r.Prime) (hp2 : p ≠ 2) (hr2 : r ≠ 2) (hpr : p ≠ r)
    {R : Subgroup H} [R.Normal] (hR : IsPGroup r R) (hRrk : CFSG.pRank r R ≤ 2)
    {P : Subgroup H} (hP : IsPGroup p P) (hPexp : ∀ x ∈ P, x ^ p = 1)
    (hdim : p ^ 2 ≤ (frattini P).index)
    (hirr : ∀ Y : Subgroup H, (frattini P).map P.subtype ≤ Y → Y ≤ P →
      normalizer (P : Set H) ≤ normalizer (Y : Set H) →
      Y = (frattini P).map P.subtype ∨ Y = P) :
    ⁅R, P⁆ = ⊥ := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have : Fact p.Prime := ⟨hp⟩
  by_cases hR1 : R = ⊥
  · rw [hR1, commutator_bot_left]
  have : Nontrivial R := (Subgroup.nontrivial_iff_ne_bot R).mpr hR1
  obtain ⟨D, hDc, -, hDexp, -, -, hker⟩ := CFSG.SectionRank.Ccomm.supercritical_witness hr2 hR
  have hDr : IsPGroup r D := hR.to_subgroup D
  have hDrk : CFSG.Open.pRank r (⊤ : Subgroup D) ≤ 2 := by
    refine (CFSG.SectionRank.pRank_top_le_of_injective hr.one_lt D.subtype
      D.subtype_injective).trans ?_
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact hRrk
  obtain ⟨-, hbound⟩ := CFSG.SectionRank.Ccomm.rank_two_exponent_prime_order_bound hDr
    (fun x => Subtype.ext (hDexp x x.2)) hDrk
  have : Fact (IsPGroup r D) := ⟨hDr⟩
  have hWel : CFSG.IsElementaryAbelian r (D ⧸ frattini D) :=
    CFSG.isElementaryAbelian_quotient_frattini
  have : Finite (Additive (D ⧸ frattini D)) := inferInstanceAs (Finite (D ⧸ frattini D))
  have : FiniteDimensional (ZMod r) (Additive (D ⧸ frattini D)) := Module.Finite.of_finite
  have hfin : finrank (ZMod r) (Additive (D ⧸ frattini D)) ≤ 2 := by
    have : Fintype (Additive (D ⧸ frattini D)) := Fintype.ofFinite _
    have h := Module.card_eq_pow_finrank (K := ZMod r) (V := Additive (D ⧸ frattini D))
    rw [ZMod.card, ← Nat.card_eq_fintype_card,
      show Nat.card (Additive (D ⧸ frattini D)) = Nat.card (D ⧸ frattini D) from rfl] at h
    rw [h] at hbound
    exact (Nat.pow_le_pow_iff_right hr.one_lt).mp hbound
  set ρ : H →* LinearMap.GeneralLinearGroup (ZMod r) (Additive (D ⧸ frattini D)) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv _ _).symm.toMonoidHom.comp
      ((NQSetup.mulAutLinear r (D ⧸ frattini D)).comp
        ((CFSG.SectionRank.Ccomm.frattiniAction D).comp MulAut.conjNormal)) with hρ
  have hρP := irreducible_Frattini_normalizer_coprime_two_space_triviality hp hp2 hP hPexp hdim
    hirr (k := ZMod r) (by rw [ZMod.ringChar_zmod_n]; exact hpr.symm) hfin ρ
  rw [commutator_eq_bot_iff_le_centralizer]
  intro y hy
  rw [mem_centralizer_iff]
  intro x hx
  have hρx : ρ x = 1 := by
    have : ρ x ∈ P.map ρ := ⟨x, hx, rfl⟩
    rwa [hρP, mem_bot] at this
  have hfx : CFSG.SectionRank.Ccomm.frattiniAction D (MulAut.conjNormal x) = 1 := by
    apply NQSetup.mulAutLinear_injective r (D ⧸ frattini D)
    apply (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod r) _).symm.injective
    rw [map_one, map_one]
    exact hρx
  obtain ⟨k, hk⟩ := hker ⟨_, hfx⟩
  obtain ⟨j, hj⟩ := hP ⟨x, hx⟩
  have hc1 : (MulAut.conjNormal x : MulAut R) ^ r ^ k = 1 := congrArg Subtype.val hk
  have hc2 : (MulAut.conjNormal x : MulAut R) ^ p ^ j = 1 := by
    rw [← map_pow]
    have : x ^ p ^ j = 1 := congrArg Subtype.val hj
    rw [this, map_one]
  have hord : orderOf (MulAut.conjNormal x : MulAut R) = 1 := by
    have h1 := orderOf_dvd_of_pow_eq_one hc1
    have h2 := orderOf_dvd_of_pow_eq_one hc2
    have hcop : Nat.Coprime (r ^ k) (p ^ j) :=
      Nat.Coprime.pow k j ((Nat.coprime_primes hr hp).mpr (Ne.symm hpr))
    exact Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have hc : (MulAut.conjNormal x : MulAut R) = 1 := orderOf_eq_one_iff.mp hord
  have h3 := congrArg (fun φ : MulAut R => ((φ ⟨y, hy⟩ : R) : H)) hc
  simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
  calc x * y = x * y * x⁻¹ * x := by group
    _ = y * x := by rw [h3]

end CFSG.Quasithin.H13.NQRigid
