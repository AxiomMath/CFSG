module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCasePSL2S0LeQuotientTorus
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Exact reflected tori for involutions of `PSL₂`

The existing reflected-join theorem supplies the geometry needed by the
normalizer argument.  This owner retains the exact split/nonsplit
half-cardinality needed by the semilinear fixed-field contradiction.
-/

noncomputable section

namespace CFSG.GorensteinWalter

open Matrix
open BenderSuzuki.External

universe u

private theorem psl2_reflected_torus_card_of_reflected
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    {t : PSL2 K} (ht : IsInvolution t)
    (U : Subgroup (PSL2 K)) (w : PSL2 K)
    (hUcyc : IsCyclic U) (hUeven : Even (Nat.card U))
    (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : PSL2 K, x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hnormalizer : ∀ R : Subgroup (PSL2 K), R ≤ U → R ≠ ⊥ →
      Subgroup.normalizer (R : Set (PSL2 K)) = U ⊔ Subgroup.zpowers w) :
    ∃ T : Subgroup (PSL2 K), ∃ s : PSL2 K,
      IsCyclic T ∧ t ∈ T ∧ IsInvolution s ∧ s ∉ T ∧
      (∀ x : PSL2 K, x ∈ T → s * x * s⁻¹ = x⁻¹) ∧
      Subgroup.centralizer ({t} : Set (PSL2 K)) = T ⊔ Subgroup.zpowers s ∧
      Nat.card T = Nat.card U := by
  classical
  let : Fintype U := Fintype.ofFinite U
  obtain ⟨sU, hsUord⟩ :=
    exists_prime_orderOf_dvd_card' (G := U) 2 hUeven.two_dvd
  let s0 : PSL2 K := sU
  have hs0U : s0 ∈ U := sU.2
  have hs0ord : orderOf s0 = 2 := by
    have h := (orderOf_injective U.subtype U.subtype_injective sU).trans hsUord
    simpa [s0] using h
  have hs0I : IsInvolution s0 := by
    constructor
    · intro h
      have hord1 : orderOf s0 = 1 := by rw [h]; simp
      rw [hs0ord] at hord1
      norm_num at hord1
    · exact (orderOf_dvd_iff_pow_eq_one).mp (by rw [hs0ord])
  obtain ⟨g, hgt⟩ := psl2_involutions_conjugate_of_odd_prime_power
    K hK s0 t hs0I ht
  let T : Subgroup (PSL2 K) := U.map (MulAut.conj g).toMonoidHom
  have hTcyc : IsCyclic T := by
    let eU : U ≃* T := Subgroup.equivMapOfInjective U
      (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    exact (MulEquiv.isCyclic eU).mp hUcyc
  have htT : t ∈ T := by
    rw [← hgt]
    exact Subgroup.mem_map.mpr ⟨s0, hs0U, rfl⟩
  let s : PSL2 K := g * w * g⁻¹
  let e : PSL2 K ≃* PSL2 K := MulAut.conj g
  have hsI : IsInvolution s := by
    constructor
    · intro h
      apply hwU
      have hw1 : w = 1 := by
        calc
          w = g⁻¹ * (g * w * g⁻¹) * g := by group
          _ = g⁻¹ * 1 * g := by
            change g⁻¹ * s * g = g⁻¹ * 1 * g
            rw [h]
          _ = 1 := by simp
      rw [hw1]
      exact U.one_mem
    · calc
        (g * w * g⁻¹) ^ 2 = g * (w ^ 2) * g⁻¹ := by
          rw [pow_two]
          calc
            (g * w * g⁻¹) * (g * w * g⁻¹) =
                g * w * (g⁻¹ * g) * w * g⁻¹ := by group
            _ = g * w * 1 * w * g⁻¹ := by rw [inv_mul_cancel]
            _ = g * (w * w) * g⁻¹ := by group
            _ = g * (w ^ 2) * g⁻¹ := by rw [pow_two]
        _ = 1 := by
          have hw2 : w ^ 2 = 1 := by simpa [pow_two] using hwsq
          rw [hw2]
          simp
  have hs_not_T : s ∉ T := by
    intro hsT
    dsimp [T] at hsT
    rcases Subgroup.mem_map.mp hsT with ⟨u, hu, hgu⟩
    have hwU' : w ∈ U := by
      have huw : u = w := by
        have h' := congrArg (fun z : PSL2 K => g⁻¹ * z * g) hgu
        calc
          u = g⁻¹ * (s * g) := by
            simpa [MulAut.conj_apply, s, mul_assoc] using h'
          _ = g⁻¹ * ((g * w * g⁻¹) * g) := by rfl
          _ = w := by group
      simpa [huw] using hu
    exact hwU hwU'
  have hinvT : ∀ x : PSL2 K, x ∈ T → s * x * s⁻¹ = x⁻¹ := by
    intro x hx
    dsimp [T] at hx
    rcases Subgroup.mem_map.mp hx with ⟨u, hu, rfl⟩
    have hwuinv : w * u * w⁻¹ = u⁻¹ := hwinv u hu
    calc
      (g * w * g⁻¹) * (g * u * g⁻¹) * (g * w * g⁻¹)⁻¹ =
          g * (w * u * w⁻¹) * g⁻¹ := by group
      _ = g * u⁻¹ * g⁻¹ := by rw [hwuinv]
      _ = (g * u * g⁻¹)⁻¹ := by group
  let R : Subgroup (PSL2 K) := Subgroup.zpowers s0
  have hRleU : R ≤ U := Subgroup.zpowers_le.mpr hs0U
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hs0R : s0 ∈ R := Subgroup.mem_zpowers s0
    have hs0bot : s0 ∈ (⊥ : Subgroup (PSL2 K)) := by simpa [hbot] using hs0R
    exact hs0I.1 (Subgroup.mem_bot.mp hs0bot)
  have hN0 : Subgroup.normalizer (R : Set (PSL2 K)) =
      U ⊔ Subgroup.zpowers w := hnormalizer R hRleU hRne
  let Zt : Subgroup (PSL2 K) := Subgroup.zpowers t
  have hZt_map : Zt = R.map e.toMonoidHom := by
    have hmap : R.map e.toMonoidHom = Subgroup.zpowers (e s0) := by
      simp [R, e]
    rw [hmap]
    dsimp [Zt, e]
    rw [hgt]
  have hN0map : (Subgroup.normalizer (R : Set (PSL2 K))).map e.toMonoidHom =
      Subgroup.normalizer (Zt : Set (PSL2 K)) := by
    rw [hZt_map]
    exact Subgroup.map_equiv_normalizer_eq R e
  have hUsup_map : (U ⊔ Subgroup.zpowers w).map e.toMonoidHom =
      T ⊔ Subgroup.zpowers s := by
    simpa [T, s, e, Subgroup.map_sup, MonoidHom.map_zpowers,
      MulAut.conj_apply]
  have hNt : Subgroup.normalizer (Zt : Set (PSL2 K)) =
      T ⊔ Subgroup.zpowers s := by
    calc
      Subgroup.normalizer (Zt : Set (PSL2 K)) =
          (Subgroup.normalizer (R : Set (PSL2 K))).map e.toMonoidHom :=
        hN0map.symm
      _ = (U ⊔ Subgroup.zpowers w).map e.toMonoidHom := by rw [hN0]
      _ = T ⊔ Subgroup.zpowers s := hUsup_map
  have hC : Subgroup.centralizer ({t} : Set (PSL2 K)) =
      T ⊔ Subgroup.zpowers s := by
    apply le_antisymm
    · intro x hx
      rw [← hNt]
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      dsimp [Zt]
      rw [MonoidHom.map_zpowers]
      have hxt : (MulAut.conj x) t = t := by
        have hcomm : x * t = t * x :=
          Subgroup.mem_centralizer_singleton_iff.mp hx
        calc
          (MulAut.conj x) t = x * t * x⁻¹ := by simp [MulAut.conj_apply]
          _ = t * x * x⁻¹ := by rw [hcomm]
          _ = t := by group
      exact congrArg Subgroup.zpowers hxt
    · apply sup_le
      · intro x hx
        rw [Subgroup.mem_centralizer_singleton_iff]
        rcases hTcyc with ⟨a, ha⟩
        rcases ha ⟨x, hx⟩ with ⟨n, hn⟩
        rcases ha ⟨t, htT⟩ with ⟨m, hm⟩
        have hab : (⟨x, hx⟩ : T) * (⟨t, htT⟩ : T) =
            (⟨t, htT⟩ : T) * (⟨x, hx⟩ : T) := by
          calc
            (⟨x, hx⟩ : T) * (⟨t, htT⟩ : T) = a ^ n * a ^ m := by
              simpa [hn, hm]
            _ = a ^ (n + m) := by rw [zpow_add]
            _ = a ^ (m + n) := by rw [add_comm]
            _ = a ^ m * a ^ n := by rw [zpow_add]
            _ = (⟨t, htT⟩ : T) * (⟨x, hx⟩ : T) := by
              simpa [← hm, ← hn]
        simpa using congrArg Subtype.val hab
      · rw [Subgroup.zpowers_le]
        rw [Subgroup.mem_centralizer_singleton_iff]
        have htinv : t⁻¹ = t := by
          have htt : t * t = 1 := by simpa [pow_two] using ht.2
          exact inv_eq_of_mul_eq_one_right htt
        calc
          s * t = t⁻¹ * s := by
            exact mul_inv_eq_iff_eq_mul.mp (hinvT t htT)
          _ = t * s := by rw [htinv]
  have hTcard : Nat.card T = Nat.card U :=
    Subgroup.card_map_of_injective (K := U) (MulAut.conj g).injective
  exact ⟨T, s, hTcyc, htT, hsI, hs_not_T, hinvT, hC, hTcard⟩

/-- Every involution of `PSL₂(K)` lies in a cyclic reflected torus whose
order is the even one of `(q-1)/2` and `(q+1)/2`; its centralizer is the
torus extended by an inverting reflection. -/
public theorem psl2_reflected_torus_card
    {K : Type u} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    {t : PSL2 K} (ht : IsInvolution t) :
    ∃ T : Subgroup (PSL2 K), ∃ s : PSL2 K,
      IsCyclic T ∧ t ∈ T ∧ IsInvolution s ∧ s ∉ T ∧
      (∀ x : PSL2 K, x ∈ T → s * x * s⁻¹ = x⁻¹) ∧
      Subgroup.centralizer ({t} : Set (PSL2 K)) = T ⊔ Subgroup.zpowers s ∧
      Even (Nat.card T) ∧
      (Nat.card T = (Nat.card K - 1) / 2 ∨
        Nat.card T = (Nat.card K + 1) / 2) := by
  classical
  have hqodd : Odd (Nat.card K) := by
    rcases hK with ⟨ell, n, hell, hellodd, hn, hKcard⟩
    rw [hKcard]
    exact hellodd.pow
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 :=
    gcd_sub_one_two_of_odd hqodd
  rcases hK with ⟨p, f, hp, hpOdd, hf, hcard⟩
  let : Fact p.Prime := ⟨hp⟩
  have hKcard : Nat.card K = p ^ f := hcard
  let hKfull : IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp, hpOdd, hf, hcard⟩
  rcases Nat.even_or_odd ((Nat.card K - 1) / 2) with hsplit | hnonsplit
  · obtain ⟨U, w, hUcyc, hUcard, _hwN, hwU, hwsq, hwinv,
      _hDcard, hnormalizer⟩ :=
      huppert_II_8_3_split_torus_reflection_data (F := K) (p := p) (f := f)
        hKcard
    have hUcard' : Nat.card U = (Nat.card K - 1) / 2 := by
      simpa [hgcd] using hUcard
    have hUeven : Even (Nat.card U) := by rwa [hUcard']
    obtain ⟨T, s, hTcyc, htT, hsI, hsT, hinv, hC, hTcard⟩ :=
      psl2_reflected_torus_card_of_reflected hKfull ht U w hUcyc hUeven
        hwU hwsq hwinv hnormalizer
    refine ⟨T, s, hTcyc, htT, hsI, hsT, hinv, hC, ?_, ?_⟩
    · rwa [hTcard]
    · exact Or.inl (hTcard.trans hUcard')
  · obtain ⟨U, w, hUcyc, hUcard, _hwN, hwU, hwsq, hwinv,
      _hDcard, hnormalizer⟩ :=
      huppert_II_8_4_nonsplit_torus_reflection_data (F := K) (p := p) (f := f)
        hKcard
    have hUcard' : Nat.card U = (Nat.card K + 1) / 2 := by
      simpa [hgcd] using hUcard
    have hhalfEven : Even ((Nat.card K + 1) / 2) := by
      rcases hnonsplit with ⟨k, hk⟩
      use k + 1
      omega
    have hUeven : Even (Nat.card U) := by rwa [hUcard']
    obtain ⟨T, s, hTcyc, htT, hsI, hsT, hinv, hC, hTcard⟩ :=
      psl2_reflected_torus_card_of_reflected hKfull ht U w hUcyc hUeven
        hwU hwsq hwinv hnormalizer
    refine ⟨T, s, hTcyc, htT, hsI, hsT, hinv, hC, ?_, ?_⟩
    · rwa [hTcard]
    · exact Or.inr (hTcard.trans hUcard')

end CFSG.GorensteinWalter
