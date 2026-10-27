module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseReflection
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralOddRotationCentralizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

open BenderSuzuki
open BenderSuzuki.External

/-!
# Section 4: the reflected torus node with a prescribed fixed Sylow subgroup

This module strengthens `secondCase_reflection_psl2_torus` by allowing the
reflection to be chosen inside a prescribed Sylow `2`-subgroup `P`, under
the hypothesis that `P` centralizes the distinguished involution `t`.

The mathematical core is the same reflected-torus decomposition as before.
Because `P ≤ C(t)`, the whole Sylow subgroup lies in the dihedral normalizer
`T ⊔ ⟨s⟩` of the cyclic torus containing `t`; since `P` is a noncyclic
dihedral `2`-group and `T` is cyclic, `P` contains an element outside `T`,
and every such element is a reflection inverting `T`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

private theorem odd_centralizer_le_torus_of_inverting_join_fixed
    {G : Type u} [Group G] [Finite G]
    (U : Subgroup G) (s w : G)
    (hsU : s ∈ U) (hsI : IsInvolution s)
    (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : G, x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hnormalizer : ∀ R : Subgroup G, R ≤ U → R ≠ ⊥ →
      Subgroup.normalizer (R : Set G) = U ⊔ Subgroup.zpowers w)
    (X : Subgroup G) (hXodd : ∀ x : G, x ∈ X → Odd (orderOf x))
    (hXcent : X ≤ Subgroup.centralizer ({s} : Set G)) :
    X ≤ U := by
  intro x hx
  have hxcent : x ∈ Subgroup.centralizer ({s} : Set G) := hXcent hx
  let R : Subgroup G := Subgroup.zpowers s
  have hRleU : R ≤ U := Subgroup.zpowers_le.mpr hsU
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hsR : s ∈ R := Subgroup.mem_zpowers s
    have hsbot : s ∈ (⊥ : Subgroup G) := by simpa [hbot] using hsR
    exact hsI.1 (Subgroup.mem_bot.mp hsbot)
  have hsingleton_subset_R : ({s} : Set G) ⊆ (R : Set G) := by
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact Subgroup.mem_zpowers s
  have hxcentR : x ∈ Subgroup.centralizer (R : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hxcent ⊢
    intro y hy
    rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
    have hcs : Commute x s := by
      have h : s * x = x * s := hxcent s (by simp)
      exact h.symm
    exact (hcs.zpow_right n).symm
  have hxN : x ∈ Subgroup.normalizer (R : Set G) :=
    (Subgroup.centralizer_le_normalizer (R : Set G)) hxcentR
  have hN : Subgroup.normalizer (R : Set G) = U ⊔ Subgroup.zpowers w :=
    hnormalizer R hRleU hRne
  have hxUw : x ∈ U ⊔ Subgroup.zpowers w := by
    rw [← hN]
    exact hxN
  rcases (mem_sup_zpowers_of_involution_inverts hwU hwsq hwinv).mp hxUw with
    ⟨u, hu, hx_or⟩
  rcases hx_or with hxu | hxuw
  · rw [hxu]
    exact hu
  · exfalso
    have hxodd : Odd (orderOf x) := hXodd x hx
    have hw_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hwsq
    have hwuw : w * u * w = u⁻¹ := by
      calc
        w * u * w = (w * u * w⁻¹) * w * w := by
          rw [hw_inv]
          simp [mul_assoc, hwsq]
        _ = u⁻¹ * w * w := by rw [hwinv u hu]
        _ = u⁻¹ := by rw [mul_assoc, hwsq, mul_one]
    have hx2 : (u * w) ^ 2 = 1 := by
      rw [pow_two]
      calc
        (u * w) * (u * w) = u * (w * u * w) := by group
        _ = u * u⁻¹ := by rw [hwuw]
        _ = 1 := by simp
    have hord2 : orderOf (u * w) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [hxuw] using hx2)
    have huw_ne : u * w ≠ 1 := by
      intro h1
      apply hwU
      have hw_eq : w = u⁻¹ := by
        calc
          w = u⁻¹ * (u * w) := by group
          _ = u⁻¹ * 1 := by rw [h1]
          _ = u⁻¹ := by simp
      simpa [hw_eq] using U.inv_mem hu
    have hord_eq : orderOf (u * w) = 2 :=
      orderOf_eq_prime (by simpa [hxuw] using hx2) huw_ne
    have h2dvd : 2 ∣ orderOf x := by
      rw [hxuw, hord_eq]
    exact hxodd.not_two_dvd_nat h2dvd

private lemma gcd_sub_one_two_of_odd_fixed (q : ℕ) (hq : Odd q) :
    Nat.gcd (q - 1) 2 = 2 := by
  have h2 : 2 ∣ q - 1 := by
    rcases hq with ⟨k, hk⟩
    use k
    omega
  exact Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
    (Nat.dvd_gcd h2 (dvd_refl 2))

private theorem centralizer_conj_mem_fixed
    {G : Type u} [Group G] (g t x : G)
    (hx : x ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set G)) :
    g⁻¹ * x * g ∈ Subgroup.centralizer ({t} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  have h' : g⁻¹ * (x * (g * t * g⁻¹)) * g =
      g⁻¹ * ((g * t * g⁻¹) * x) * g :=
    congrArg (fun z : G => g⁻¹ * z * g) hx
  simpa [mul_assoc] using h'

/-- The reflected-torus core with a fixed Sylow subgroup: given a reflected
cyclic torus `U` with involution `s₀` and reflecting involution `w`, the
conjugate torus containing `t` admits a reflection inside the prescribed
Sylow `P` whenever `P` centralizes `t`. -/
private theorem secondCase_fixedSylow_of_reflected_torus
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    {P : Sylow 2 (PSL2 K)} {t : PSL2 K}
    (ht : IsInvolution t)
    (hPcent : (P : Subgroup (PSL2 K)) ≤
      Subgroup.centralizer ({t} : Set (PSL2 K)))
    (U : Subgroup (PSL2 K)) (w : PSL2 K)
    (hUcyc : IsCyclic U) (hUeven : 2 ∣ Nat.card U)
    (hwU : w ∉ U) (hwsq : w * w = 1)
    (hwinv : ∀ x : PSL2 K, x ∈ U → w * x * w⁻¹ = x⁻¹)
    (hnormalizer : ∀ R : Subgroup (PSL2 K), R ≤ U → R ≠ ⊥ →
      Subgroup.normalizer (R : Set (PSL2 K)) =
        U ⊔ Subgroup.zpowers w) :
    ∃ T : Subgroup (PSL2 K), ∃ s : PSL2 K,
      IsCyclic T ∧ t ∈ T ∧ s ∈ (P : Subgroup (PSL2 K)) ∧ s ∉ T ∧
      IsInvolution s ∧
      (P : Subgroup (PSL2 K)) ≤ T ⊔ Subgroup.zpowers s ∧
      Subgroup.normalizer (Subgroup.zpowers t : Set (PSL2 K)) =
        T ⊔ Subgroup.zpowers s ∧
      (∀ x : PSL2 K, x ∈ T → s * x * s⁻¹ = x⁻¹) ∧
      ∀ X : Subgroup (PSL2 K),
        (∀ x : PSL2 K, x ∈ X → Odd (orderOf x)) →
          X ≤ Subgroup.centralizer ({t} : Set (PSL2 K)) → X ≤ T := by
  classical
  let : Fintype U := Fintype.ofFinite U
  obtain ⟨sU, hsUord⟩ := exists_prime_orderOf_dvd_card' (G := U) 2 hUeven
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
  have hbase :
      ∀ X : Subgroup (PSL2 K),
        (∀ x : PSL2 K, x ∈ X → Odd (orderOf x)) →
          X ≤ Subgroup.centralizer ({s0} : Set (PSL2 K)) → X ≤ U :=
    fun X hXodd hXcent =>
      odd_centralizer_le_torus_of_inverting_join_fixed U s0 w
        hs0U hs0I hwU hwsq hwinv hnormalizer X hXodd hXcent
  obtain ⟨g, hgt⟩ :=
    psl2_involutions_conjugate_of_odd_prime_power K hK s0 t hs0I ht
  let T : Subgroup (PSL2 K) := U.map (MulAut.conj g).toMonoidHom
  let s : PSL2 K := g * w * g⁻¹
  have hTcyc : IsCyclic T := by
    let eU : U ≃* T := Subgroup.equivMapOfInjective U (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective
    exact (MulEquiv.isCyclic eU).mp hUcyc
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
    rcases Subgroup.mem_map.mp hsT with ⟨u, hu, hgu⟩
    have hwU' : w ∈ U := by
      have huw : u = w := by
        have h' := congrArg (fun z : PSL2 K => g⁻¹ * z * g) hgu
        calc
          u = g⁻¹ * (s * g) := by simpa [MulAut.conj_apply, mul_assoc] using h'
          _ = g⁻¹ * ((g * w * g⁻¹) * g) := by
            rfl
          _ = w := by group
      simpa [huw] using hu
    exact hwU hwU'
  have hinvT : ∀ x : PSL2 K, x ∈ T → s * x * s⁻¹ = x⁻¹ := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨u, hu, rfl⟩
    have hwuinv : w * u * w⁻¹ = u⁻¹ := hwinv u hu
    calc
      (g * w * g⁻¹) * (g * u * g⁻¹) * (g * w * g⁻¹)⁻¹ =
          g * (w * u * w⁻¹) * g⁻¹ := by group
      _ = g * u⁻¹ * g⁻¹ := by rw [hwuinv]
      _ = (g * u * g⁻¹)⁻¹ := by group
  have hcontain :
      ∀ X : Subgroup (PSL2 K),
        (∀ x : PSL2 K, x ∈ X → Odd (orderOf x)) →
          X ≤ Subgroup.centralizer ({t} : Set (PSL2 K)) → X ≤ T := by
    intro X hXodd hXcent x hx
    let X0 : Subgroup (PSL2 K) :=
      X.map (MulAut.conj g⁻¹).toMonoidHom
    have hX0odd : ∀ y : PSL2 K, y ∈ X0 → Odd (orderOf y) := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨x0, hx0, rfl⟩
      have hord : orderOf ((MulAut.conj g⁻¹) x0) = orderOf x0 :=
        (MulAut.conj g⁻¹).orderOf_eq x0
      change Odd (orderOf ((MulAut.conj g⁻¹) x0))
      rw [hord]
      exact hXodd x0 hx0
    have hX0cent : X0 ≤ Subgroup.centralizer ({s0} : Set (PSL2 K)) := by
      intro y hy
      rcases Subgroup.mem_map.mp hy with ⟨x0, hx0, rfl⟩
      have hxcent : x0 ∈ Subgroup.centralizer ({t} : Set (PSL2 K)) :=
        hXcent hx0
      have hxcent' : x0 ∈ Subgroup.centralizer
          ({g * s0 * g⁻¹} : Set (PSL2 K)) := by
        simpa [hgt] using hxcent
      simpa [MulAut.conj_apply] using centralizer_conj_mem_fixed g s0 x0 hxcent'
    have hX0U : X0 ≤ U := hbase X0 hX0odd hX0cent
    have hy : g⁻¹ * x * g ∈ X0 :=
      Subgroup.mem_map.mpr ⟨x, hx, by simp⟩
    have hyU : g⁻¹ * x * g ∈ U := hX0U hy
    exact Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hyU, by
      simp [mul_assoc]⟩
  have htT : t ∈ T := by
    rw [← hgt]
    exact Subgroup.mem_map.mpr ⟨s0, hs0U, rfl⟩
  let R : Subgroup (PSL2 K) := Subgroup.zpowers s0
  have hRleU : R ≤ U := Subgroup.zpowers_le.mpr hs0U
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hs0R : s0 ∈ R := Subgroup.mem_zpowers s0
    have hs0bot : s0 ∈ (⊥ : Subgroup (PSL2 K)) := by simpa [hbot] using hs0R
    exact hs0I.1 (Subgroup.mem_bot.mp hs0bot)
  have hN0 : Subgroup.normalizer (R : Set (PSL2 K)) =
      U ⊔ Subgroup.zpowers w := hnormalizer R hRleU hRne
  let e : PSL2 K ≃* PSL2 K := MulAut.conj g
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
    dsimp [T, s, e]
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    simp [MulAut.conj_apply]
  have hNt : Subgroup.normalizer (Zt : Set (PSL2 K)) =
      T ⊔ Subgroup.zpowers s := by
    calc
      Subgroup.normalizer (Zt : Set (PSL2 K)) =
          (Subgroup.normalizer (R : Set (PSL2 K))).map e.toMonoidHom :=
        hN0map.symm
      _ = (U ⊔ Subgroup.zpowers w).map e.toMonoidHom := by rw [hN0]
      _ = T ⊔ Subgroup.zpowers s := hUsup_map
  have hPleNt : (P : Subgroup (PSL2 K)) ≤
      Subgroup.normalizer (Zt : Set (PSL2 K)) := by
    intro p hp
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (p * t * p⁻¹) = Subgroup.zpowers t
    have hcomm : p * t = t * p :=
      Subgroup.mem_centralizer_singleton_iff.mp (hPcent hp)
    have hconj : p * t * p⁻¹ = t := by
      calc
        p * t * p⁻¹ = t * p * p⁻¹ := by rw [hcomm]
        _ = t := by group
    rw [hconj]
  have hPleTS : (P : Subgroup (PSL2 K)) ≤ T ⊔ Subgroup.zpowers s := by
    rw [← hNt]
    exact hPleNt
  have hPnotcyc : ¬ IsCyclic (P : Subgroup (PSL2 K)) := by
    intro hPcyc
    rcases psl2_odd_hasDihedralSylowTwo_model K hK P with ⟨m, hm, ⟨eP⟩⟩
    have hdcyc : IsCyclic (DihedralGroup (2 ^ m)) := eP.isCyclic.mp hPcyc
    apply DihedralGroup.not_isCyclic
      (show 2 ^ m ≠ 1 by
        exact ne_of_gt
          (Nat.one_lt_pow (by omega : m ≠ 0) (by norm_num : 1 < 2)))
    exact hdcyc
  let : IsCyclic T := hTcyc
  have hPnotT : ¬ (P : Subgroup (PSL2 K)) ≤ T := by
    intro hPleT
    exact hPnotcyc (Subgroup.isCyclic_of_le hPleT)
  obtain ⟨s', hs'P, hs'T⟩ := SetLike.not_le_iff_exists.mp hPnotT
  have hs'sup : s' ∈ T ⊔ Subgroup.zpowers s := by
    rw [← hNt]
    exact hPleNt hs'P
  have hs'rep : ∃ u : PSL2 K, u ∈ T ∧ s' = u * s := by
    rcases (mem_sup_zpowers_of_involution_inverts hs_not_T
        (by simpa [pow_two] using hsI.2) hinvT).mp hs'sup with
      ⟨u, huT, hu | hus⟩
    · exact (hs'T (by simpa [hu] using huT)).elim
    · exact ⟨u, huT, hus⟩
  have hjoin : T ⊔ Subgroup.zpowers s = T ⊔ Subgroup.zpowers s' := by
    apply le_antisymm
    · apply sup_le
      · exact le_sup_left
      · apply Subgroup.zpowers_le.mpr
        rcases hs'rep with ⟨u, huT, hus⟩
        have hs_eq : s = u⁻¹ * s' := by
          rw [hus]
          group
        rw [hs_eq]
        exact (T ⊔ Subgroup.zpowers s').mul_mem
          ((le_sup_left : T ≤ T ⊔ Subgroup.zpowers s') (T.inv_mem huT))
          ((le_sup_right : Subgroup.zpowers s' ≤
            T ⊔ Subgroup.zpowers s') (Subgroup.mem_zpowers s'))
    · apply sup_le
      · exact le_sup_left
      · apply Subgroup.zpowers_le.mpr
        rcases hs'rep with ⟨u, huT, hus⟩
        rw [hus]
        exact (T ⊔ Subgroup.zpowers s).mul_mem
          ((le_sup_left : T ≤ T ⊔ Subgroup.zpowers s) huT)
          ((le_sup_right : Subgroup.zpowers s ≤
            T ⊔ Subgroup.zpowers s) (Subgroup.mem_zpowers s))
  have hPleTs' : (P : Subgroup (PSL2 K)) ≤
      T ⊔ Subgroup.zpowers s' := by
    rw [← hjoin]
    exact hPleTS
  have hNt' : Subgroup.normalizer (Zt : Set (PSL2 K)) =
      T ⊔ Subgroup.zpowers s' := hNt.trans hjoin
  have hsinv' : ∀ x : PSL2 K, x ∈ T → s' * x * s'⁻¹ = x⁻¹ := by
    intro x hx
    let : CommGroup T := IsCyclic.commGroup
    rcases hs'rep with ⟨u, huT, hus⟩
    rw [hus]
    have hsu : s * u * s = u⁻¹ := by
      calc
        s * u * s = (s * u * s⁻¹) * s * s := by
          rw [inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsI.2)]
          simp [mul_assoc, show s * s = 1 by simpa [pow_two] using hsI.2]
        _ = u⁻¹ * s * s := by rw [hinvT u huT]
        _ = u⁻¹ := by
          rw [mul_assoc]
          rw [show s * s = 1 by simpa [pow_two] using hsI.2]
          simp
    calc
      (u * s) * x * (u * s)⁻¹ = u * (s * x * s⁻¹) * u⁻¹ := by group
      _ = u * x⁻¹ * u⁻¹ := by rw [hinvT x hx]
      _ = x⁻¹ := by
        have hux : u * x⁻¹ = x⁻¹ * u := by
          have hc := mul_comm (⟨u, huT⟩ : T) (⟨x⁻¹, T.inv_mem hx⟩ : T)
          exact congrArg Subtype.val hc
        calc
          u * x⁻¹ * u⁻¹ = x⁻¹ * u * u⁻¹ := by rw [hux]
          _ = x⁻¹ := by group
  have hs'I : IsInvolution s' := by
    constructor
    · intro h
      exact hs'T (by rw [h]; exact T.one_mem)
    · rcases hs'rep with ⟨u, huT, hus⟩
      rw [hus, pow_two]
      have hsu : s * u * s = u⁻¹ := by
        calc
          s * u * s = (s * u * s⁻¹) * s * s := by
            rw [inv_eq_of_mul_eq_one_right (by simpa [pow_two] using hsI.2)]
            simp [mul_assoc, show s * s = 1 by simpa [pow_two] using hsI.2]
          _ = u⁻¹ * s * s := by rw [hinvT u huT]
          _ = u⁻¹ := by
            rw [mul_assoc]
            rw [show s * s = 1 by simpa [pow_two] using hsI.2]
            simp
      calc
        (u * s) * (u * s) = u * (s * u * s) := by group
        _ = u * u⁻¹ := by rw [hsu]
        _ = 1 := by simp
  exact ⟨T, s', hTcyc, htT, hs'P, hs'T, hs'I, hPleTs',
    (by simpa [Zt] using hNt'), hsinv', hcontain⟩

/-- In an odd `PSL₂(K)`, the reflected torus of the odd part of the
centralizer of an involution can be chosen together with a reflection lying
in any prescribed Sylow `2`-subgroup that centralizes that involution. -/
public theorem secondCase_reflection_psl2_torus_fixedSylow
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    (P : Sylow 2 (PSL2 K)) {t : PSL2 K}
    (ht : IsInvolution t)
    (hPcent : (P : Subgroup (PSL2 K)) ≤
      Subgroup.centralizer ({t} : Set (PSL2 K))) :
    ∃ T : Subgroup (PSL2 K), ∃ s : PSL2 K,
      IsCyclic T ∧ t ∈ T ∧ s ∈ (P : Subgroup (PSL2 K)) ∧ s ∉ T ∧
      IsInvolution s ∧
      (P : Subgroup (PSL2 K)) ≤ T ⊔ Subgroup.zpowers s ∧
      Subgroup.normalizer (Subgroup.zpowers t : Set (PSL2 K)) =
        T ⊔ Subgroup.zpowers s ∧
      (∀ x : PSL2 K, x ∈ T → s * x * s⁻¹ = x⁻¹) ∧
      ∀ X : Subgroup (PSL2 K),
        (∀ x : PSL2 K, x ∈ X → Odd (orderOf x)) →
          X ≤ Subgroup.centralizer ({t} : Set (PSL2 K)) → X ≤ T := by
  classical
  have hKfull : IsOddPrimePower (Nat.card K) := hK
  rcases hK with ⟨p, f, hp, hpodd, hf, hcard⟩
  let : Fact p.Prime := ⟨hp⟩
  have hoddK : Odd (Nat.card K) := by
    rw [hcard]
    exact hpodd.pow
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 :=
    gcd_sub_one_two_of_odd_fixed (Nat.card K) hoddK
  by_cases hsplit : Even ((Nat.card K - 1) / 2)
  · obtain ⟨U, w, hUcyc, hUcard, _hwN, hwU, hwsq, hwinv, _hDcard,
        hnormalizer⟩ :=
      huppert_II_8_3_split_torus_reflection_data
        (F := K) (p := p) (f := f) hcard
    have hUcard' : Nat.card U = (Nat.card K - 1) / 2 := by
      simpa [hgcd] using hUcard
    have hUeven : 2 ∣ Nat.card U := by
      rw [hUcard']
      exact hsplit.two_dvd
    exact secondCase_fixedSylow_of_reflected_torus K hKfull ht hPcent
      U w hUcyc hUeven hwU hwsq hwinv hnormalizer
  · obtain ⟨U, w, hUcyc, hUcard, _hwN, hwU, hwsq, hwinv, _hDcard,
        hnormalizer⟩ :=
      huppert_II_8_4_nonsplit_torus_reflection_data
        (F := K) (p := p) (f := f) hcard
    have hoddhalf : Odd ((Nat.card K - 1) / 2) :=
      Nat.not_even_iff_odd.mp hsplit
    have hEvenPlus : Even ((Nat.card K + 1) / 2) := by
      rcases hoddhalf with ⟨l, hl⟩
      use l + 1
      omega
    have hUcard' : Nat.card U = (Nat.card K + 1) / 2 := by
      simpa [hgcd] using hUcard
    have hUeven : 2 ∣ Nat.card U := by
      rw [hUcard']
      exact hEvenPlus.two_dvd
    exact secondCase_fixedSylow_of_reflected_torus K hKfull ht hPcent
      U w hUcyc hUeven hwU hwsq hwinv hnormalizer

end CFSG.GorensteinWalter
