module

public import CFSG.RankThree.PartOne.S12.Equivariance
public import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.RankThree.PartOne

theorem exists_commuting_conj_of_not_central {M : Type} [Group M] [Finite M] {t : M}
    (ht2 : t * t = 1)
    (hodd : ∀ N : Subgroup M, N.Normal → Odd (Nat.card N) → ∀ n ∈ N, n * t = t * n)
    (hnc : t ∉ Subgroup.center M) :
    ∃ g : M, g * t * g⁻¹ ≠ t ∧ (g * t * g⁻¹) * t = t * (g * t * g⁻¹) := by
  have : Fintype M := Fintype.ofFinite M
  by_contra hcon
  push Not at hcon
  have ht1 : t ≠ 1 := fun h => hnc (h ▸ Subgroup.one_mem _)
  obtain ⟨N, hNn, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar M t ht1 ht2
    (fun g hg => by
      by_contra hne
      exact hcon g hne hg)
  apply hnc
  rw [Subgroup.mem_center_iff]
  intro g
  set n := g * t * g⁻¹ * t⁻¹ with hn
  have hnN : n ∈ N := hN g
  have hcomm : n * t = t * n := hodd N hNn hNodd n hnN
  have hgt : g * t * g⁻¹ = n * t := by rw [hn]; group
  have hsq : (n * t) * (n * t) = 1 := by
    rw [← hgt]
    calc g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ := by group
      _ = 1 := by rw [ht2]; group
  have hnn : n * n = 1 := by
    calc n * n = n * n * (t * t) := by rw [ht2, mul_one]
      _ = n * (n * t) * t := by group
      _ = n * (t * n) * t := by rw [hcomm]
      _ = (n * t) * (n * t) := by group
      _ = 1 := hsq
  have hord : orderOf n = 1 := by
    have h2 : orderOf n ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hnn)
    have hdvd : orderOf n ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨n, hnN⟩ : N)
      rwa [Subgroup.orderOf_mk] at this
    have hodd' : Odd (orderOf n) := Odd.of_dvd_nat hNodd hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact h
    · rw [h] at hodd'
      exact absurd hodd' (by decide)
  have hn1 : n = 1 := orderOf_eq_one_iff.mp hord
  have : g * t * g⁻¹ = t := by rw [hgt, hn1, one_mul]
  calc g * t = g * t * g⁻¹ * g := by group
    _ = t * g := by rw [this]

theorem eq_of_commuting_involutions {E : Type*} [CommGroup E]
    (h1 : ∀ f : E, f * f = 1 → f = 1) (h2 : ∀ e : E, ∃ r : E, r * r = e)
    {u v : MulAut E} (hu : u * u = 1) (hv : v * v = 1) (huv : u * v = v * u)
    (hfix : ∀ x : E, u x = x ↔ v x = x) : u = v := by
  have hu' : ∀ x : E, u (u x) = x := fun x => by
    have := congrArg (fun φ : MulAut E => φ x) hu
    simpa using this
  have hv' : ∀ x : E, v (v x) = x := fun x => by
    have := congrArg (fun φ : MulAut E => φ x) hv
    simpa using this
  have huv' : ∀ x : E, u (v x) = v (u x) := fun x => by
    have := congrArg (fun φ : MulAut E => φ x) huv
    simpa using this
  have decomp : ∀ e : E, ∃ ep em : E, e = ep * em ∧ u ep = ep ∧ u em = em⁻¹ := by
    intro e
    obtain ⟨r, hr⟩ := h2 (e * u e)
    have h3 : u r * u r = e * u e := by
      rw [← map_mul, hr, map_mul, hu']
      exact mul_comm _ _
    have hur : u r = r := by
      have h : (u r * r⁻¹) * (u r * r⁻¹) = 1 := by
        calc (u r * r⁻¹) * (u r * r⁻¹) = (u r * u r) * (r * r)⁻¹ := by
              rw [mul_inv_rev]; ac_rfl
          _ = 1 := by rw [h3, hr, mul_inv_cancel]
      exact mul_inv_eq_one.mp (h1 _ h)
    refine ⟨r, e * r⁻¹, by simp, hur, ?_⟩
    have h4 : (e * r⁻¹) * u (e * r⁻¹) = 1 := by
      rw [map_mul, map_inv, hur]
      calc e * r⁻¹ * (u e * r⁻¹) = (e * u e) * (r * r)⁻¹ := by
            rw [mul_inv_rev]; ac_rfl
        _ = 1 := by rw [hr, mul_inv_cancel]
    exact eq_inv_of_mul_eq_one_right h4
  ext e
  obtain ⟨ep, em, rfl, hp, hm⟩ := decomp e
  have hvp : v ep = ep := (hfix ep).mp hp
  have hf : em * v em = 1 := by
    set f := em * v em with hf
    have huf : u f = f⁻¹ := by
      rw [hf, map_mul, huv', hm, map_inv, mul_inv_rev, mul_comm]
    have hvf : v f = f := by
      rw [hf, map_mul, hv']
      exact mul_comm _ _
    have hufix : u f = f := (hfix f).mpr hvf
    have : f * f = 1 := by
      calc f * f = f * u f := by rw [hufix]
        _ = 1 := by rw [huf, mul_inv_cancel]
    exact h1 f this
  have hvm : v em = em⁻¹ := eq_inv_of_mul_eq_one_right hf
  simp only [map_mul, hp, hm, hvp, hvm]

section StepE

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_autFixedInG_iff_apply {E : Subgroup G} (t : MulAut E) (x : E) :
    (x : G) ∈ autFixedInG E t ↔ t x = x := by
  unfold autFixedInG
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    subst hyx'
    exact hy
  · intro h
    exact ⟨x, h, rfl⟩

omit [Finite G] in
theorem fixedPoints_conj_eq_of_mem_cNormalizer {E : Subgroup G} {c : G} (u : MulAut E)
    (hfix : autFixedInG E u = Subgroup.zpowers c) {w : G}
    (hw : w ∈ Subgroup.normalizer (E : Set G)) (hwH : w ∈ cNormalizer c) (x : E) :
    u x = x ↔ (conjAut E w hw * u * (conjAut E w hw)⁻¹) x = x := by
  have hconj : autFixedInG E (conjAut E w hw * u * (conjAut E w hw)⁻¹) =
      Subgroup.zpowers c := by
    rw [Equivariance.autFixedInG_conj u hw, hfix]
    exact Equivariance.conjBy_eq_of_mem_normalizer hwH
  rw [← mem_autFixedInG_iff_apply, ← mem_autFixedInG_iff_apply, hfix, hconj]

theorem zStar_step {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {E : Subgroup G} [IsElementaryAbelian p E]
    {c : G} (u : MulAut E) (hu : u ∈ torusWeyl E) (hu2 : u * u = 1)
    (hfix : autFixedInG E u = Subgroup.zpowers c)
    (hnc : (⟨u, hu⟩ : ↥(torusWeyl E)) ∉ Subgroup.center ↥(torusWeyl E))
    (hodd : ∀ N : Subgroup ↥(torusWeyl E), N.Normal → Odd (Nat.card N) →
      ∀ n ∈ N, n * (⟨u, hu⟩ : ↥(torusWeyl E)) = ⟨u, hu⟩ * n) :
    ∃ (w : G) (hw : w ∈ Subgroup.normalizer (E : Set G)), w ∉ cNormalizer c ∧
      conjAut E w hw * u * (conjAut E w hw)⁻¹ ≠ u ∧
      (conjAut E w hw * u * (conjAut E w hw)⁻¹) * u =
        u * (conjAut E w hw * u * (conjAut E w hw)⁻¹) := by
  have : Finite (MulAut E) :=
    Finite.of_injective (fun φ : MulAut E => (φ : E → E)) (fun a b h => MulEquiv.ext (congrFun h))
  have : Finite ↥(torusWeyl E) := inferInstance
  have hu2' : (⟨u, hu⟩ : ↥(torusWeyl E)) * ⟨u, hu⟩ = 1 := Subtype.ext hu2
  obtain ⟨g, hg1, hg2⟩ := exists_commuting_conj_of_not_central hu2' hodd hnc
  obtain ⟨n, hn⟩ := MonoidHom.mem_range.mp g.2
  have hw : (n : G) ∈ Subgroup.normalizer (E : Set G) := n.2
  have hconj : conjAut E (n : G) hw = (g : MulAut E) := hn
  refine ⟨n, hw, ?_, ?_, ?_⟩
  · intro hwH
    refine hg1 (Subtype.ext ?_)
    have hv : (g : MulAut E) * u * (g : MulAut E)⁻¹ = u := by
      let _ : CommGroup ↥E :=
        { (inferInstance : Group ↥E) with
          mul_comm := fun a b => (IsMulCommutative.is_comm (M := ↥E)).comm a b }
      have hfixeq := fixedPoints_conj_eq_of_mem_cNormalizer u hfix hw hwH
      rw [hconj] at hfixeq
      have hpow : ∀ x : ↥E, x ^ p = 1 := fun x =>
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p E) x
      have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
      have h1 : ∀ f : ↥E, f * f = 1 → f = 1 := by
        intro f hf
        have h2 : orderOf f ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hf)
        have h3 : orderOf f ∣ p := orderOf_dvd_of_pow_eq_one (hpow f)
        have := Nat.dvd_gcd h2 h3
        rw [hcop.gcd_eq_one, Nat.dvd_one] at this
        exact orderOf_eq_one_iff.mp this
      have hodd_p : Odd p := hp.eq_two_or_odd'.resolve_left hp2
      have h2 : ∀ e : ↥E, ∃ r : ↥E, r * r = e := by
        intro e
        obtain ⟨k, hk⟩ := hodd_p
        refine ⟨e ^ (k + 1), ?_⟩
        calc e ^ (k + 1) * e ^ (k + 1) = e ^ (2 * k + 1) * e := by rw [← pow_add, ← pow_succ]; ring_nf
          _ = e := by rw [← hk, hpow e, one_mul]
      have hv2 : (g : MulAut E) * u * (g : MulAut E)⁻¹ * ((g : MulAut E) * u * (g : MulAut E)⁻¹) =
          1 := by
        calc (g : MulAut E) * u * (g : MulAut E)⁻¹ * ((g : MulAut E) * u * (g : MulAut E)⁻¹)
            = (g : MulAut E) * (u * u) * (g : MulAut E)⁻¹ := by group
          _ = 1 := by rw [hu2]; group
      exact (eq_of_commuting_involutions h1 h2 hu2 hv2 (congrArg Subtype.val hg2).symm
        fun x => hfixeq x).symm
    exact hv
  · rw [hconj]; exact fun h => hg1 (Subtype.ext h)
  · rw [hconj]; exact congrArg Subtype.val hg2

end StepE

end CFSG.RankThree.PartOne
