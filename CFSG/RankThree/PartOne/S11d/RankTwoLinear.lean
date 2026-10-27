module

public import CFSG.RankThree.PartOne.LIT.RankAbstract
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat

public section

namespace CFSG.RankThree.PartOne.LIT

open Module

universe u v

variable {K : Type u} [Field K] {V : Type v} [AddCommGroup V] [Module K V]

theorem two_mul_le_finrank [FiniteDimensional K V] {r : ℕ} (hr : r.Prime) (hrK : (r : K) ≠ 0)
    {d : ℕ} (hd : ∀ (W : Type v) [AddCommGroup W] [Module K W] [FiniteDimensional K W]
      (g : W ≃ₗ[K] W), g ^ r = 1 → g ≠ 1 → d ≤ finrank K W)
    (E : Subgroup (V ≃ₗ[K] V)) [Finite E] (hcomm : ∀ g ∈ E, ∀ h ∈ E, g * h = h * g)
    (hexp : ∀ g ∈ E, g ^ r = 1) (hcard : r ^ 2 ≤ Nat.card E) : 2 * d ≤ finrank K V := by
  classical
  obtain ⟨x, hxE, hx1, v, hv0, hxv⟩ := exists_fixed_of_sq_le_card hr hrK E hcomm hexp hcard
  have hc := isCompl_fixedSpace_commSpace hrK (hexp x hxE)
  have hxcomm : ∀ g ∈ E, g * x = x * g := fun g hg => hcomm g hg x hxE
  have hUinv : ∀ g : E, ∀ u ∈ fixedSpace x, (E.subtype g) u ∈ fixedSpace x :=
    fun g u hu => map_mem_fixedSpace (hxcomm g g.2) hu
  have hWinv : ∀ g : E, ∀ w ∈ commSpace x, (E.subtype g) w ∈ commSpace x :=
    fun g w hw => map_mem_commSpace (hxcomm g g.2) hw
  let ρ : E →* (V ≃ₗ[K] V) := E.subtype
  let ρU := restrictAction ρ (fixedSpace x) hUinv
  let ρW := restrictAction ρ (commSpace x) hWinv
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hext : ∀ g : E, ρU g = 1 → ρW g = 1 → g = 1 := by
    intro g h1 h2
    apply Subtype.ext
    apply LinearEquiv.ext
    intro y
    have hfun : (g : V ≃ₗ[K] V).toLinearMap = LinearMap.id := by
      apply ext_of_isCompl hc
      · intro u hu
        exact (restrictAction_apply ρ (fixedSpace x) hUinv g ⟨u, hu⟩).symm.trans
          (congrArg Subtype.val (LinearEquiv.congr_fun h1 ⟨u, hu⟩))
      · intro w hw
        exact (restrictAction_apply ρ (commSpace x) hWinv g ⟨w, hw⟩).symm.trans
          (congrArg Subtype.val (LinearEquiv.congr_fun h2 ⟨w, hw⟩))
    exact LinearMap.congr_fun hfun y
  have hρUpow : ∀ g : E, (ρU g) ^ r = 1 := fun g => by
    rw [← map_pow]
    have : g ^ r = 1 := Subtype.ext (hexp g g.2)
    rw [this, map_one]
  have hρWpow : ∀ g : E, (ρW g) ^ r = 1 := fun g => by
    rw [← map_pow]
    have : g ^ r = 1 := Subtype.ext (hexp g g.2)
    rw [this, map_one]
  have hρUx : ρU ⟨x, hxE⟩ = 1 := by
    apply LinearEquiv.ext
    intro u
    apply Subtype.ext
    exact mem_fixedSpace.mp u.2
  have hxne : (⟨x, hxE⟩ : E) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hρWx : ρW ⟨x, hxE⟩ ≠ 1 := fun h => hxne (hext _ hρUx h)
  by_cases hU : ∀ g : E, ρU g = 1
  ·
    have hinj : Function.Injective ρW := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro g hg
      exact Subgroup.mem_bot.2 (hext g (hU g) (MonoidHom.mem_ker.mp hg))
    let E' : Subgroup (↥(commSpace x) ≃ₗ[K] ↥(commSpace x)) := ρW.range
    have hE'fin : Finite E' :=
      Finite.of_surjective (ρW.rangeRestrict) (MonoidHom.rangeRestrict_surjective ρW)
    have hE'comm : ∀ g ∈ E', ∀ h ∈ E', g * h = h * g := by
      rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm a a.2 b b.2)
    have hE'exp : ∀ g ∈ E', g ^ r = 1 := by
      rintro _ ⟨a, rfl⟩
      exact hρWpow a
    have hE'card : r ^ 2 ≤ Nat.card E' := by
      have : Nat.card E' = Nat.card E := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
      rw [this]
      exact hcard
    obtain ⟨y', hy'E, hy'1, w, hw0, hyw⟩ :=
      exists_fixed_of_sq_le_card hr hrK E' hE'comm hE'exp hE'card
    obtain ⟨y, rfl⟩ := hy'E
    have hyne : y ≠ 1 := fun h => hy'1 (by rw [h, map_one])
    have hc2 := isCompl_fixedSpace_commSpace hrK (hρWpow y)
    have hycomm : ∀ g : E, ρW g * ρW y = ρW y * ρW g := fun g => by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hcomm g g.2 y y.2)
    have hFinv : ∀ g : E, ∀ f ∈ fixedSpace (ρW y), ρW g f ∈ fixedSpace (ρW y) :=
      fun g f hf => map_mem_fixedSpace (hycomm g) hf
    have hCinv : ∀ g : E, ∀ f ∈ commSpace (ρW y), ρW g f ∈ commSpace (ρW y) :=
      fun g f hf => map_mem_commSpace (hycomm g) hf
    let σF := restrictAction ρW (fixedSpace (ρW y)) hFinv
    let σC := restrictAction ρW (commSpace (ρW y)) hCinv
    have hsum2 := Submodule.finrank_add_eq_of_isCompl hc2
    have hxF : σF ⟨x, hxE⟩ ≠ 1 := by
      intro h
      apply hw0
      have h1 : ρW ⟨x, hxE⟩ w = w := by
        have := congrArg Subtype.val (LinearEquiv.congr_fun h ⟨w, mem_fixedSpace.mpr hyw⟩)
        exact this
      have h2 : x ∈ E := hxE
      have hwU : (w : V) ∈ fixedSpace x := by
        rw [mem_fixedSpace]
        exact congrArg Subtype.val h1
      have hwW : (w : V) ∈ commSpace x := w.2
      have := (Submodule.disjoint_def.mp hc.disjoint) (w : V) hwU hwW
      exact Subtype.ext this
    have hyC : σC y ≠ 1 := by
      intro h
      apply hyne
      have hF1 : σF y = 1 := by
        apply LinearEquiv.ext
        intro f
        apply Subtype.ext
        exact mem_fixedSpace.mp f.2
      have hfun : (ρW y).toLinearMap = LinearMap.id := by
        apply ext_of_isCompl hc2
        · intro u hu
          exact (restrictAction_apply ρW (fixedSpace (ρW y)) hFinv y ⟨u, hu⟩).symm.trans
            (congrArg Subtype.val (LinearEquiv.congr_fun hF1 ⟨u, hu⟩))
        · intro u hu
          exact (restrictAction_apply ρW (commSpace (ρW y)) hCinv y ⟨u, hu⟩).symm.trans
            (congrArg Subtype.val (LinearEquiv.congr_fun h ⟨u, hu⟩))
      exact hinj (LinearEquiv.ext fun a => LinearMap.congr_fun hfun a)
    have hσFpow : ∀ g : E, (σF g) ^ r = 1 := fun g => by
      rw [← map_pow]
      have : g ^ r = 1 := Subtype.ext (hexp g g.2)
      rw [this, map_one]
    have hσCpow : ∀ g : E, (σC g) ^ r = 1 := fun g => by
      rw [← map_pow]
      have : g ^ r = 1 := Subtype.ext (hexp g g.2)
      rw [this, map_one]
    have hdF := hd (fixedSpace (ρW y)) (σF ⟨x, hxE⟩) (hσFpow _) hxF
    have hdC := hd (commSpace (ρW y)) (σC y) (hσCpow _) hyC
    have hWV : finrank K (commSpace x) ≤ finrank K V := by omega
    omega
  · push Not at hU
    obtain ⟨g, hg⟩ := hU
    have hdU := hd (fixedSpace x) (ρU g) (hρUpow g) hg
    have hdW := hd (commSpace x) (ρW ⟨x, hxE⟩) (hρWpow _) hρWx
    omega

noncomputable def glEquiv (K : Type u) [Field K] (W : Type v) [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] : GL (Fin (finrank K W)) K ≃* (W ≃ₗ[K] W) :=
  (Matrix.GeneralLinearGroup.toLin' (Module.finBasis K W)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv K W)

theorem card_linearEquiv_eq_prod [Fintype K] {W : Type v} [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] :
    Nat.card (W ≃ₗ[K] W) =
      ∏ i : Fin (finrank K W), (Fintype.card K ^ finrank K W - Fintype.card K ^ (i : ℕ)) := by
  classical
  rw [← Nat.card_congr (glEquiv K W).toEquiv]
  exact Matrix.card_GL_field (finrank K W)

theorem pow_sub_pow_eq (q : ℕ) {m j : ℕ} (hj : j ≤ m) :
    q ^ m - q ^ (m - j) = q ^ (m - j) * (q ^ j - 1) := by
  rw [Nat.mul_sub, mul_one, ← pow_add, Nat.sub_add_cancel hj]

theorem exists_dim_of_order_dvd [Fintype K] {r : ℕ} (hr : r.Prime) (hrK : ¬ r ∣ Fintype.card K)
    {W : Type v} [AddCommGroup W] [Module K W] [FiniteDimensional K W] (g : W ≃ₗ[K] W)
    (hg : g ^ r = 1) (hg1 : g ≠ 1) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ finrank K W ∧ r ∣ Fintype.card K ^ j - 1 := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hord : orderOf g = r := orderOf_eq_prime hg hg1
  set m := finrank K W with hm
  have hdvd : r ∣ Nat.card (W ≃ₗ[K] W) := hord ▸ orderOf_dvd_natCard g
  rw [card_linearEquiv_eq_prod] at hdvd
  obtain ⟨i, -, hi⟩ := (Nat.Prime.prime hr).dvd_finsetProd_iff _ |>.mp hdvd
  have him : (i : ℕ) < m := i.2
  have hfac : Fintype.card K ^ m - Fintype.card K ^ (i : ℕ) =
      Fintype.card K ^ (i : ℕ) * (Fintype.card K ^ (m - (i : ℕ)) - 1) := by
    have := pow_sub_pow_eq (Fintype.card K) (m := m) (j := m - (i : ℕ)) (Nat.sub_le m i)
    rwa [Nat.sub_sub_self him.le] at this
  rw [hfac] at hi
  rcases (Nat.Prime.dvd_mul hr).mp hi with h | h
  · exact absurd (hr.dvd_of_dvd_pow h) hrK
  · exact ⟨m - i, by omega, by omega, h⟩

theorem exists_orderOf_prime_linearEquiv [Fintype K] {r : ℕ} (hr : r.Prime)
    {W : Type v} [AddCommGroup W] [Module K W] [FiniteDimensional K W] {j : ℕ} (hj1 : 1 ≤ j)
    (hjm : j ≤ finrank K W) (hdvd : r ∣ Fintype.card K ^ j - 1) :
    ∃ g : W ≃ₗ[K] W, orderOf g = r := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hfin : Finite (W ≃ₗ[K] W) := Finite.of_equiv _ (glEquiv K W).toEquiv
  set m := finrank K W with hm
  have hdvd' : r ∣ Nat.card (W ≃ₗ[K] W) := by
    rw [card_linearEquiv_eq_prod]
    have hi : m - j < m := by omega
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨m - j, hi⟩ : Fin m)))
    rw [pow_sub_pow_eq (Fintype.card K) hjm]
    exact dvd_mul_of_dvd_right hdvd _
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := W ≃ₗ[K] W) r hdvd'
  exact ⟨g, hg⟩

end CFSG.RankThree.PartOne.LIT
