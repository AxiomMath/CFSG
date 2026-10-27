module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Finite.Defs

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section3.CyclicTwoCoreNormalizer

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-- A proper subgroup of a simple group is self-normalizing. -/
private theorem normalizer_eq_self_of_isCoatom_of_simple
    {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (hHcoatom : IsCoatom H) (hHne : H ≠ ⊥)
    (hsimple : IsSimpleGroup G) :
    Subgroup.normalizer (H : Set G) = H := by
  apply le_antisymm
  · intro g hg
    by_contra hgnot
    have hlt : H < Subgroup.normalizer (H : Set G) :=
      lt_of_le_of_ne (@Subgroup.le_normalizer G _ H) (by
        intro hEq
        apply hgnot
        rw [hEq]
        exact hg)
    have htop : Subgroup.normalizer (H : Set G) = ⊤ :=
      hHcoatom.2 (Subgroup.normalizer (H : Set G)) hlt
    have hnorm : H.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      exact htop
    rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hsimple H hnorm with hHbot | hHtop
    · exact hHne hHbot
    · exact hHcoatom.1 hHtop
  · exact @Subgroup.le_normalizer G _ H

/-- `H = C_G(t)` is self-normalizing in the cyclic branch. -/
private theorem firstCase_normalizer_H_eq_H
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (hHhat : c.Hhat = c.H) :
    Subgroup.normalizer (od.d.bg.H : Set G) = od.d.bg.H := by
  have hcoatom : IsCoatom od.d.bg.H := by
    simpa [od.d.H_eq, hHhat] using c.Hhat_maximal
  have hHne : od.d.bg.H ≠ ⊥ := by
    have htH : od.d.bg.t ∈ od.d.bg.H := by
      rw [od.d.bg.H_eq_centralizer]
      exact (Subgroup.mem_centralizer_singleton_iff).mpr rfl
    intro hbot
    exact od.d.bg.t_involution.1 (by simpa [hbot] using htH)
  exact normalizer_eq_self_of_isCoatom_of_simple od.d.bg.H hcoatom hHne
    (minimalCounterexample_isSimple hmin)

/-- A Klein-four subgroup containing a nontrivial element `t` has an element
different from both `1` and `t`. -/
public theorem kleinFour_exists_mem_ne_one_ne_t
    {G : Type u} [Group G]
    {V : Subgroup G} (hV : IsKleinFour V) {t : G} (htV : t ∈ V)
    (ht1 : t ≠ 1) :
    ∃ y : G, y ∈ V ∧ y ≠ 1 ∧ y ≠ t := by
  classical
  by_contra hno
  push Not at hno
  have hle : (V : Set G) ⊆ ({1, t} : Set G) := by
    intro y hy
    by_cases hy1 : y = 1
    · simp [hy1]
    · simp [hno y hy hy1]
  have hcard_le : (V : Set G).ncard ≤ ({1, t} : Set G).ncard :=
    Set.ncard_le_ncard hle
  have hcardV : Nat.card V = (V : Set G).ncard := by
    simpa using (Nat.card_coe_set_eq (V : Set G))
  have h1 : 4 = (V : Set G).ncard := hV.card_four.symm.trans hcardV
  have h2 : ({1, t} : Set G).ncard = 2 := Set.ncard_pair ht1.symm
  have h42 : (4 : ℕ) ≤ 2 := by
    rw [h1]
    exact hcard_le.trans (le_of_eq h2)
  omega

/-- There is `g ∈ N_G(V₁)` outside `H`. -/
private theorem firstCase_exists_g_outside_H
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G)
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (fd : FirstCaseFourData c od.d) :
    ∃ g : G, g ∈ Subgroup.normalizer (fd.V1 : Set G) ∧ g ∉ od.d.bg.H := by
  have hVtrans :=
    normalizer_transitive_on_kleinFour_pontset hmin c fd.V1_le_S fd.V1_klein
  obtain ⟨y, hyV, hy1, hyt⟩ := kleinFour_exists_mem_ne_one_ne_t fd.V1_klein
    (by simpa [od.d.t_eq] using fd.t_mem_V1) od.d.bg.t_involution.1
  obtain ⟨n, hnN, hn⟩ :=
    hVtrans od.d.bg.t y (by simpa [od.d.t_eq] using fd.t_mem_V1)
      hyV od.d.bg.t_involution.1 hy1
  refine ⟨n, hnN, ?_⟩
  intro hnH
  have hnCent : n ∈ Subgroup.centralizer ({od.d.bg.t} : Set G) := by
    rwa [← od.d.bg.H_eq_centralizer]
  have hnfix : n * od.d.bg.t * n⁻¹ = od.d.bg.t := by
    have hcomm : od.d.bg.t * n = n * od.d.bg.t :=
      (Subgroup.mem_centralizer_singleton_iff.mp hnCent).symm
    calc
      n * od.d.bg.t * n⁻¹ = (od.d.bg.t * n) * n⁻¹ := by rw [hcomm]
      _ = od.d.bg.t := by group
  have hyeq : y = od.d.bg.t := by
    calc
      y = n * od.d.bg.t * n⁻¹ := hn.symm
      _ = od.d.bg.t := hnfix
  exact hyt hyeq

/-- `P = O_p(U)` is normal in `H`. -/
public theorem firstCase_P_normal_in_H
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c) :
    IsNormalIn (qCoreOf od.d.bg.U od.p) od.d.bg.H := by
  let U0 : Subgroup G := od.d.bg.U
  let P0 : Subgroup U0 := pCore od.p U0
  have hUH : IsNormalIn U0 od.d.bg.H := @bg_U_normal_in_H G _ _ od.d.bg
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨u, _hu, rfl⟩
    exact hUH.1 (show (u : G) ∈ U0 from u.2)
  · intro h hh x hx
    rcases (Subgroup.mem_map).1 hx with ⟨u, hu, rfl⟩
    let φ : U0 ≃* U0 := {
      toFun := fun u => ⟨h * (u : G) * h⁻¹, hUH.2 h hh (u : G) u.2⟩
      invFun := fun u => ⟨h⁻¹ * (u : G) * h, by
        have hh' : h⁻¹ ∈ od.d.bg.H := od.d.bg.H.inv_mem hh
        have h' := hUH.2 h⁻¹ hh' (u : G) u.2
        simpa [mul_assoc] using h'⟩
      left_inv := by
        intro u
        apply Subtype.ext
        change h⁻¹ * (h * (u : G) * h⁻¹) * h = (u : G)
        group
      right_inv := by
        intro u
        apply Subtype.ext
        change h * (h⁻¹ * (u : G) * h) * h⁻¹ = (u : G)
        group
      map_mul' := by
        intro u v
        apply Subtype.ext
        change h * ((u : G) * (v : G)) * h⁻¹ =
          (h * (u : G) * h⁻¹) * (h * (v : G) * h⁻¹)
        group
    }
    have hfix : P0.comap φ.toMonoidHom = P0 :=
      (pCore_characteristic (G := U0) (p := od.p)).fixed φ
    have hu' : φ u ∈ P0 := by
      exact Subgroup.mem_comap.mp (by rw [hfix]; exact hu)
    exact Subgroup.mem_map.mpr ⟨φ u, hu', rfl⟩

/-- Since `H = C_G(t)`, the whole centralizer `H` normalizes the selected
odd prime core `P = O_p(U)`. -/
public theorem firstCase_H_le_normalizer_primeCore
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c) :
    od.d.bg.H ≤ Subgroup.normalizer (qCoreOf od.d.bg.U od.p : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact (firstCase_P_normal_in_H c od).2 h hh x hx
  · intro hx
    have hh' : h⁻¹ ∈ od.d.bg.H := od.d.bg.H.inv_mem hh
    have hback := (firstCase_P_normal_in_H c od).2 h⁻¹ hh' (h * x * h⁻¹) hx
    have hEq : h⁻¹ * (h * x * h⁻¹) * h = x := by group
    simpa [hEq] using hback

/-- Since `H = C_G(t)`, the centralizer of the distinguished involution
normalizes the selected odd prime core `P = O_p(U)`. -/
public theorem firstCase_centralizer_t_le_normalizer_primeCore
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c) :
    Subgroup.centralizer ({od.d.bg.t} : Set G) ≤
      Subgroup.normalizer (qCoreOf od.d.bg.U od.p : Set G) := by
  intro x hx
  have hxH : x ∈ od.d.bg.H := by
    rw [od.d.bg.H_eq_centralizer]
    exact hx
  exact firstCase_H_le_normalizer_primeCore c od hxH

/-- If `g` conjugates the distinguished involution `t` to `t₂`, then
`C_G(t₂)` normalizes the conjugate `O_p(U)^g`. -/
public theorem firstCase_centralizer_t2_le_normalizer_conjugate_primeCore
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (g : G) (hg : g * od.d.bg.t * g⁻¹ = od.d.bg.t2) :
    Subgroup.centralizer ({od.d.bg.t2} : Set G) ≤
      Subgroup.normalizer
        ((qCoreOf od.d.bg.U od.p).map (MulAut.conj g).toMonoidHom : Set G) := by
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  let Pg : Subgroup G := P.map (MulAut.conj g).toMonoidHom
  have hNP : Subgroup.centralizer ({od.d.bg.t} : Set G) ≤
      Subgroup.normalizer (P : Set G) :=
    firstCase_centralizer_t_le_normalizer_primeCore c od
  intro z hz
  have hzcomm : z * od.d.bg.t2 = od.d.bg.t2 * z :=
    Subgroup.mem_centralizer_singleton_iff.mp hz
  have ht_eq : od.d.bg.t = g⁻¹ * od.d.bg.t2 * g := by
    calc
      od.d.bg.t = g⁻¹ * (g * od.d.bg.t * g⁻¹) * g := by group
      _ = g⁻¹ * od.d.bg.t2 * g := by rw [hg]
  have hforward : ∀ w : G, w ∈ Subgroup.centralizer ({od.d.bg.t2} : Set G) →
      ∀ y : G, y ∈ Pg → w * y * w⁻¹ ∈ Pg := by
    intro w hw y hy
    rcases Subgroup.mem_map.mp hy with ⟨p, hp, rfl⟩
    have hwcomm : w * od.d.bg.t2 = od.d.bg.t2 * w :=
      Subgroup.mem_centralizer_singleton_iff.mp hw
    let a : G := g⁻¹ * w * g
    have haCent : a ∈ Subgroup.centralizer ({od.d.bg.t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc
        a * od.d.bg.t = (g⁻¹ * w * g) * (g⁻¹ * od.d.bg.t2 * g) := by rw [ht_eq]
        _ = g⁻¹ * (w * od.d.bg.t2) * g := by group
        _ = g⁻¹ * (od.d.bg.t2 * w) * g := by rw [hwcomm]
        _ = (g⁻¹ * od.d.bg.t2 * g) * (g⁻¹ * w * g) := by group
        _ = od.d.bg.t * a := by rw [← ht_eq]
    have haN : a ∈ Subgroup.normalizer (P : Set G) := hNP haCent
    have haP : a * (p : G) * a⁻¹ ∈ P :=
      ((Subgroup.mem_normalizer_iff.mp haN) (p : G)).1 hp
    have hw_eq : w = g * a * g⁻¹ := by
      dsimp [a]
      group
    have htarget : w * (g * (p : G) * g⁻¹) * w⁻¹ =
        g * (a * (p : G) * a⁻¹) * g⁻¹ := by
      calc
        w * (g * (p : G) * g⁻¹) * w⁻¹ =
            (g * a * g⁻¹) * (g * (p : G) * g⁻¹) * (g * a * g⁻¹)⁻¹ := by
          rw [hw_eq]
        _ = g * (a * (p : G) * a⁻¹) * g⁻¹ := by group
    refine Subgroup.mem_map.mpr ⟨a * (p : G) * a⁻¹, haP, ?_⟩
    change g * (a * (p : G) * a⁻¹) * g⁻¹ =
      w * (g * (p : G) * g⁻¹) * w⁻¹
    exact htarget.symm
  apply Subgroup.mem_normalizer_iff.mpr
  intro x
  constructor
  · intro hx
    exact hforward z hz x hx
  · intro hx
    have hz_inv_comm : z⁻¹ * od.d.bg.t2 = od.d.bg.t2 * z⁻¹ := by
      have h := congrArg Inv.inv hzcomm
      have ht2inv : od.d.bg.t2⁻¹ = od.d.bg.t2 :=
        inv_eq_of_mul_eq_one_right (by simpa [pow_two] using od.d.bg.t2_involution.2)
      simpa [mul_inv_rev, ht2inv] using h.symm
    have hz_inv : z⁻¹ ∈ Subgroup.centralizer ({od.d.bg.t2} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hz_inv_comm
    have hy := hforward z⁻¹ hz_inv (z * x * z⁻¹) hx
    have hEq : z⁻¹ * (z * x * z⁻¹) * z = x := by group
    simpa [Pg, hEq] using hy

/-- `P^g = O_p(U)^g` is normal in `H^g`. -/
public theorem firstCase_Pg_normal_in_Hg
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c) (g : G) :
    IsNormalIn ((qCoreOf od.d.bg.U od.p).map (MulAut.conj g).toMonoidHom)
      (od.d.bg.H.map (MulAut.conj g).toMonoidHom) := by
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  let Pg : Subgroup G := P.map (MulAut.conj g).toMonoidHom
  let Hg : Subgroup G := od.d.bg.H.map (MulAut.conj g).toMonoidHom
  have hPN : IsNormalIn P od.d.bg.H := firstCase_P_normal_in_H c od
  have hPleH : P ≤ od.d.bg.H := hPN.1
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases (Subgroup.mem_map).1 hx with ⟨y, hy, rfl⟩
    exact Subgroup.mem_map.mpr ⟨y, hPleH hy, rfl⟩
  · intro hg hhg xg hxg
    rcases (Subgroup.mem_map).1 hhg with ⟨h, hh, rfl⟩
    rcases (Subgroup.mem_map).1 hxg with ⟨x, hx, rfl⟩
    have hconj : h * x * h⁻¹ ∈ P := hPN.2 h hh x hx
    exact Subgroup.mem_map.mpr ⟨h * x * h⁻¹, hconj, by
      change g * (h * x * h⁻¹) * g⁻¹ =
        (g * h * g⁻¹) * (g * x * g⁻¹) * (g * h * g⁻¹)⁻¹
      group⟩

/-- Intersection of two normal-in-`K` subgroups is normal in `K`. -/
public theorem isNormalIn_inf
    {G : Type u} [Group G]
    {A B K : Subgroup G} (hA : IsNormalIn A K) (hB : IsNormalIn B K) :
    IsNormalIn (A ⊓ B) K := by
  refine ⟨?_, ?_⟩
  · intro x hx
    exact hA.1 (Subgroup.mem_inf.mp hx).1
  · intro k hk x hx
    have hxA : k * x * k⁻¹ ∈ A := hA.2 k hk x (Subgroup.mem_inf.mp hx).1
    have hxB : k * x * k⁻¹ ∈ B := hB.2 k hk x (Subgroup.mem_inf.mp hx).2
    exact Subgroup.mem_inf.mpr ⟨hxA, hxB⟩

/-- `P = O_p(U)` centralizes the Klein-four subgroup `V₁ = ⟨t, t₁⟩`:
`U` centralizes `t`, and `t₁` was chosen to centralize `P`. -/
public theorem firstCase_P_le_centralizer_V1
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (fd : FirstCaseFourData c od.d) :
    qCoreOf od.d.bg.U od.p ≤
      Subgroup.centralizer (fd.V1 : Set G) := by
  classical
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  have hPleU : P ≤ od.d.bg.U :=
    (fstar_qCoreOf_le_fittingSubgroupOf od.d.bg.U od.p od.p_prime).trans
      (fittingSubgroupOf_le (G := G) od.d.bg.U)
  have hPleCt1 : P ≤ Subgroup.centralizer ({od.d.bg.t1} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp
      (firstCase_t1_centralizes_primeCore c od)) x hx
  have hUleCt : od.d.bg.U ≤ Subgroup.centralizer ({od.d.bg.t} : Set G) := by
    intro x hx
    have hUleH : od.d.bg.U ≤ od.d.bg.H :=
      le_sup_left.trans (le_of_eq od.d.bg.H_eq_US)
    have hxH : x ∈ od.d.bg.H := hUleH hx
    rwa [← od.d.bg.H_eq_centralizer]
  have hV1eq : fd.V1 = Subgroup.closure ({od.d.bg.t, od.d.bg.t1} : Set G) := by
    have hcomm : Commute od.d.bg.t od.d.bg.t1 := by
      have ht1H : od.d.bg.t1 ∈ od.d.bg.H :=
        by
          have hle : (od.d.bg.S : Subgroup G) ≤
              od.d.bg.U ⊔ (od.d.bg.S : Subgroup G) :=
            le_sup_right
          rw [← od.d.bg.H_eq_US]
          exact hle od.d.bg.t1_mem_S
      rw [od.d.bg.H_eq_centralizer, Subgroup.mem_centralizer_singleton_iff]
        at ht1H
      exact ht1H.symm
    have hne : od.d.bg.t ≠ od.d.bg.t1 := by
      intro h
      apply od.d.bg.t1_not_mem_S0
      rw [← h]
      exact od.d.bg.t_mem_S0
    exact kleinFour_eq_closure_of_mem fd.V1_klein
      (by simpa [od.d.t_eq] using fd.t_mem_V1) fd.t1_mem_V1
      od.d.bg.t_involution.1 od.d.bg.t1_involution.1 hne hcomm
  intro x hx
  rw [hV1eq, Subgroup.centralizer_closure]
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases hy with hyt | hyt1
  · subst y
    exact (Subgroup.mem_centralizer_iff.mp (hUleCt (hPleU hx)))
      od.d.bg.t (by simp)
  · subst y
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hPleCt1 hx)).symm

/-- Conjugating by `g ∈ N_G(V₁)` preserves the containment
`P ≤ C_G(V₁)`. -/
private theorem firstCase_Pg_le_centralizer_V1
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (fd : FirstCaseFourData c od.d)
    {g : G} (hgN : g ∈ Subgroup.normalizer (fd.V1 : Set G)) :
    (qCoreOf od.d.bg.U od.p).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer (fd.V1 : Set G) := by
  classical
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  have hPleC : P ≤ Subgroup.centralizer (fd.V1 : Set G) :=
    firstCase_P_le_centralizer_V1 c od fd
  intro z hz
  rcases (Subgroup.mem_map).1 hz with ⟨y, hyP, rfl⟩
  have hyC : y ∈ Subgroup.centralizer (fd.V1 : Set G) := hPleC hyP
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hgv : g⁻¹ * v * g ∈ fd.V1 :=
    (Subgroup.mem_normalizer_iff''.mp hgN v).1 hv
  have hyv : y * (g⁻¹ * v * g) = (g⁻¹ * v * g) * y :=
    ((Subgroup.mem_centralizer_iff.mp hyC) (g⁻¹ * v * g) hgv).symm
  calc
    v * (g * y * g⁻¹) = g * ((g⁻¹ * v * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * v * g)) * g⁻¹ := by rw [hyv]
    _ = (g * y * g⁻¹) * v := by group

/-- For `g ∈ N_G(V₁)`, the conjugate `P^g = O_p(U)^g` of the `p`-core is
again contained in `U`: it centralizes `V₁` (so lies in `H`), and every odd
`p`-subgroup of `H` lies in `U`. -/
public theorem firstCase_Pg_le_U
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (fd : FirstCaseFourData c od.d)
    {g : G} (hgN : g ∈ Subgroup.normalizer (fd.V1 : Set G)) :
    (qCoreOf od.d.bg.U od.p).map (MulAut.conj g).toMonoidHom ≤
      od.d.bg.U := by
  classical
  let : Fintype G := Fintype.ofFinite G
  let : Fact od.p.Prime := ⟨od.p_prime⟩
  let P : Subgroup G := qCoreOf od.d.bg.U od.p
  have hPp : IsPGroup od.p P := qCoreOf_isPGroup od.d.bg.U od.p
  have hPgC : P.map (MulAut.conj g).toMonoidHom ≤
      Subgroup.centralizer (fd.V1 : Set G) :=
    firstCase_Pg_le_centralizer_V1 c od fd hgN
  have hPgH : P.map (MulAut.conj g).toMonoidHom ≤ od.d.bg.H := by
    intro z hz
    have hzC : z ∈ Subgroup.centralizer (fd.V1 : Set G) := hPgC hz
    have hzC' : z ∈ Subgroup.centralizer ({od.d.bg.t} : Set G) :=
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr
        (by simpa [od.d.t_eq] using fd.t_mem_V1))) hzC
    rwa [od.d.bg.H_eq_centralizer]
  exact pSubgroup_le_U_of_le_H od.d.bg od.p (firstCase_oriented_p_odd c od) hPgH
    (hPp.map (MulAut.conj g).toMonoidHom)

/-- For `g ∈ N_G(V₁)`, `P^g` lies in the `U`-centralizer of `V₁`. -/
public theorem firstCase_Pg_le_centralizerIn
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G)
    (od : FirstCaseOrientedPrimeData c)
    (fd : FirstCaseFourData c od.d)
    {g : G} (hgN : g ∈ Subgroup.normalizer (fd.V1 : Set G)) :
    (qCoreOf od.d.bg.U od.p).map (MulAut.conj g).toMonoidHom ≤
      od.d.bg.U ⊓ Subgroup.centralizer (fd.V1 : Set G) := by
  intro x hx
  exact Subgroup.mem_inf.mpr
    ⟨firstCase_Pg_le_U c od fd hgN hx,
      firstCase_Pg_le_centralizer_V1 c od fd hgN hx⟩

end CFSG.GorensteinWalter
