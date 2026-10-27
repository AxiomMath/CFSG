module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2DihedralSylow
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2InvolutionFusion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralOddRotationCentralizer
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ConjugatedInvertedSubgroup
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4: the reflected torus node of equations (1)--(3)

The paper's first shared node selects a reflection `s` in the component and
a cyclic torus `T` in the central quotient so that the odd part of the
component lies in `T` and is inverted by `s`.

This module currently proves the `PSL₂(K)` model half of that node.  The
`A₇` model half needs an exact model theorem that is not present in the
repository; the smallest missing statement is recorded in
`/tmp/s4-reflection-report.md`.
-/

noncomputable section

open BenderSuzuki
open BenderSuzuki.External

namespace CFSG.GorensteinWalter

universe u

public theorem odd_centralizer_le_torus_of_inverting_join
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
  have hxcentR : x ∈ Subgroup.centralizer (R : Set G) :=
    by
      rw [Subgroup.mem_centralizer_iff] at hxcent ⊢
      intro y hy
      rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
      have hcs : Commute x s :=
        by
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

private lemma gcd_sub_one_two_of_odd (q : ℕ) (hq : Odd q) :
    Nat.gcd (q - 1) 2 = 2 := by
  have h2 : 2 ∣ q - 1 := by
    rcases hq with ⟨k, hk⟩
    use k
    omega
  exact Nat.dvd_antisymm (Nat.gcd_dvd_right _ _)
    (Nat.dvd_gcd h2 (dvd_refl 2))

private theorem centralizer_conj_mem
    {G : Type u} [Group G] (g t x : G)
    (hx : x ∈ Subgroup.centralizer ({g * t * g⁻¹} : Set G)) :
    g⁻¹ * x * g ∈ Subgroup.centralizer ({t} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
  have h' : g⁻¹ * (x * (g * t * g⁻¹)) * g =
      g⁻¹ * ((g * t * g⁻¹) * x) * g :=
    congrArg (fun z : G => g⁻¹ * z * g) hx
  simpa [mul_assoc] using h'

/-- In an odd `PSL₂(K)`, the odd part of the centralizer of any involution
lies in a cyclic torus, and the torus is inverted by an involution outside
it. -/
public theorem secondCase_reflection_psl2_torus
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K))
    {t : PSL2 K} (ht : IsInvolution t) :
    ∃ T : Subgroup (PSL2 K), ∃ s : PSL2 K,
      IsCyclic T ∧ t ∈ T ∧ s ∉ T ∧ IsInvolution s ∧
        (∀ x : PSL2 K, x ∈ T → s * x * s⁻¹ = x⁻¹) ∧
          ∀ X : Subgroup (PSL2 K),
            (∀ x : PSL2 K, x ∈ X → Odd (orderOf x)) →
              X ≤ Subgroup.centralizer ({t} : Set (PSL2 K)) → X ≤ T := by
  classical
  rcases hK with ⟨p, f, hp, hpodd, hf, hcard⟩
  have hKfull : IsOddPrimePower (Nat.card K) :=
    ⟨p, f, hp, hpodd, hf, hcard⟩
  let : Fact p.Prime := ⟨hp⟩
  have hoddK : Odd (Nat.card K) := by
    rw [hcard]
    exact hpodd.pow
  have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 :=
    gcd_sub_one_two_of_odd (Nat.card K) hoddK
  have hqOne : 1 < Nat.card K := by
    have hp2 : 2 ≤ p := hp.two_le
    have hpf2 : 2 ≤ p ^ f := by
      calc
        2 ≤ p := hp2
        _ = p ^ 1 := by simp
        _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf
    rw [hcard]
    omega
  by_cases hsplit : Even ((Nat.card K - 1) / 2)
  · obtain ⟨U, w, hUcyc, hUcard, _hwN, hwU, hwsq, hwinv, _hDcard, hnormalizer⟩ :=
      huppert_II_8_3_split_torus_reflection_data (F := K) (p := p) (f := f) hcard
    have hUcard' : Nat.card U = (Nat.card K - 1) / 2 := by
      simpa [hgcd] using hUcard
    have hUeven : 2 ∣ Nat.card U := by
      rw [hUcard']
      exact hsplit.two_dvd
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
        odd_centralizer_le_torus_of_inverting_join U s0 w
          hs0U hs0I hwU hwsq hwinv hnormalizer X hXodd hXcent
    obtain ⟨g, hgt⟩ :=
      psl2_involutions_conjugate_of_odd_prime_power K hKfull s0 t hs0I ht
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
        -- w = 1 would follow from g * w * g⁻¹ = 1
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
        simpa [MulAut.conj_apply] using centralizer_conj_mem g s0 x0 hxcent'
      have hX0U : X0 ≤ U := hbase X0 hX0odd hX0cent
      have hy : g⁻¹ * x * g ∈ X0 :=
        Subgroup.mem_map.mpr ⟨x, hx, by simp⟩
      have hyU : g⁻¹ * x * g ∈ U := hX0U hy
      exact Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hyU, by
        simp [mul_assoc]⟩
    have htT : t ∈ T := by
      rw [← hgt]
      exact Subgroup.mem_map.mpr ⟨s0, hs0U, rfl⟩
    exact ⟨T, s, hTcyc, htT, hs_not_T, hsI, hinvT, hcontain⟩
  · obtain ⟨U, w, hUcyc, hUcard, _hwN, hwU, hwsq, hwinv, _hDcard, hnormalizer⟩ :=
      huppert_II_8_4_nonsplit_torus_reflection_data (F := K) (p := p) (f := f) hcard
    have hUcard' : Nat.card U = (Nat.card K + 1) / 2 := by
      simpa [hgcd] using hUcard
    have hoddhalf : Odd ((Nat.card K - 1) / 2) :=
      Nat.not_even_iff_odd.mp hsplit
    have hEvenPlus : Even ((Nat.card K + 1) / 2) := by
      rcases hoddhalf with ⟨l, hl⟩
      use l + 1
      omega
    have hUeven : 2 ∣ Nat.card U := by
      rw [hUcard']
      exact hEvenPlus.two_dvd
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
        odd_centralizer_le_torus_of_inverting_join U s0 w
          hs0U hs0I hwU hwsq hwinv hnormalizer X hXodd hXcent
    obtain ⟨g, hgt⟩ :=
      psl2_involutions_conjugate_of_odd_prime_power K hKfull s0 t hs0I ht
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
        simpa [MulAut.conj_apply] using centralizer_conj_mem g s0 x0 hxcent'
      have hX0U : X0 ≤ U := hbase X0 hX0odd hX0cent
      have hy : g⁻¹ * x * g ∈ X0 :=
        Subgroup.mem_map.mpr ⟨x, hx, by simp⟩
      have hyU : g⁻¹ * x * g ∈ U := hX0U hy
      exact Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, hyU, by
        simp [mul_assoc]⟩
    have htT : t ∈ T := by
      rw [← hgt]
      exact Subgroup.mem_map.mpr ⟨s0, hs0U, rfl⟩
    exact ⟨T, s, hTcyc, htT, hs_not_T, hsI, hinvT, hcontain⟩

end CFSG.GorensteinWalter
