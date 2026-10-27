module

public import CFSG.Quasithin.H13.A6S1372L74u
public import CFSG.Quasithin.H13.A6S1372L74v

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.QuasithinUnique.Bridge
open scoped Pointwise IsMulCommutative commutatorElement

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

section Simple

variable (hNS : ¬ LieModel G .PSp 3 2 1) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
  {H : Subgroup G} (hH : H ∈ S.Hz) (hab : IsElemAbelian 2 (conjClosure S.V3 H)) {K : Subgroup G}
  (hKH : K ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G))
  (hKL1 : ∀ k ∈ K, ∀ l ∈ S.L1, k * l * k⁻¹ * l⁻¹ ∈ pCoreOf 2 K)
include hNS h13315 h1356two hH hab hKH hHK hKL1

theorem exists_U_simple (hhat : ¬ IsHatA6 L)
    (hK2 : oTwoRes K = K)
    (hKC : ∀ k ∈ K, ∀ u ∈ conjClosure S.V3 H,
      k * u * k⁻¹ * u⁻¹ ∈ Subgroup.centralizer (pCoreOf 2 H : Set G))
    (hKM : ¬ K ≤ Subgroup.normalizer (L : Set G))
    (hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) :
    ∃ U : Subgroup G,
      U ≤ conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ∧
      (K ⊔ pCoreOf 2 (S.L1 ⊔ T)) ⊔ Subgroup.zpowers (S.cL1 hhat : G) ≤
        Subgroup.normalizer (U : Set G) ∧
      K ⊓ Subgroup.centralizer (U : Set G) = pCoreOf 2 K ∧
      pCoreOf 2 (K ⊔ pCoreOf 2 (S.L1 ⊔ T)) ≤ Subgroup.centralizer (U : Set G) ∧
      ⁅U, K⁆ = U ∧
      ∀ u ∈ U, (S.cL1 hhat : G) * u * (S.cL1 hhat : G)⁻¹ = u → u = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hRK⟩ := pCoreOf_le_R1_and hH hKH hHK
  set R := pCoreOf 2 (S.L1 ⊔ T) with hRdef
  set X := K ⊔ R with hX
  set c : G := (S.cL1 hhat : G) with hcdef
  set X' := X ⊔ Subgroup.zpowers c with hX'
  have hcL : c ∈ S.L1 := S.cL1_mem hhat
  have hc3 : c ^ 3 = 1 := S.cL1_cube hhat
  have hF := S.hypF91 hNS h13315 h1356two hH
  have hL1H : S.L1 ≤ H := le_sup_left.trans hH.1.1
  have hRH : R ≤ H := (pCoreOf_le 2 _).trans hH.1.1
  have hL1K : S.L1 ≤ Subgroup.normalizer (K : Set G) := hL1H.trans hHK
  have hKL := K_le_normalizer_L1 hH hKH hHK hKL1
  have hOQ : pCoreOf 2 K ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans hKH)
      (hHK.trans (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  have hK1 : ¬ K ≤ pCoreOf 2 K := by
    intro h
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥K ⧸ CFSG.pCore 2 ↥K)
    induction x using QuotientGroup.induction_on with
    | H a =>
      apply hx
      rw [QuotientGroup.eq_one_iff]
      exact (A6L74.mem_pCoreOf_iff a).1 (h a.2)
  obtain ⟨U₁, hU₁U, -, hV3U₁, hU₁N, hfpf⟩ := exists_U1 hNS h13315 h1356two hH hab hhat
  have hKU₁ : K ≤ Subgroup.normalizer (U₁ : Set G) := fun k hk => hU₁N k (hKH hk) (hKL hk)
  have hHUH : H ≤ Subgroup.normalizer (conjClosure S.V3 H : Set G) :=
    le_normalizer_conjClosure S.V3 H
  have hMU₀ : ⁅U₁, K⁆ ≤ conjClosure S.V3 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    rw [Subgroup.commutator_le]
    intro u hu k hk
    have h1 : k * u * k⁻¹ * u⁻¹ ∈ conjClosure S.V3 H ⊓
        Subgroup.centralizer (pCoreOf 2 H : Set G) :=
      ⟨(conjClosure S.V3 H).mul_mem ((Subgroup.mem_normalizer_iff.mp (hHUH (hKH hk)) u).mp
        (hU₁U hu)) ((conjClosure S.V3 H).inv_mem (hU₁U hu)), hKC k hk u (hU₁U hu)⟩
    have e : ⁅u, k⁆ = (k * u * k⁻¹ * u⁻¹)⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.inv_mem _ h1
  have hMU₁ : ⁅U₁, K⁆ ≤ U₁ := Subgroup.le_normalizer_iff_commutator_le_left.mp hKU₁
  have hXK : X ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hRK
  have hL1X : S.L1 ≤ Subgroup.normalizer (X : Set G) := fun l hl =>
    A6L74.mem_normalizer_sup hRK (hL1K hl) (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hl))
  have hcZ : Subgroup.zpowers c ≤ S.L1 := Subgroup.zpowers_le.2 hcL
  have hX'X : X' ≤ Subgroup.normalizer (X : Set G) :=
    sup_le Subgroup.le_normalizer (hcZ.trans hL1X)
  have hX'H : X' ≤ H := sup_le (sup_le hKH hRH) (hcZ.trans hL1H)
  have hX'L : X' ≤ Subgroup.normalizer (S.L1 : Set G) :=
    sup_le (sup_le hKL R1_le_normalizer_L1) (hcZ.trans Subgroup.le_normalizer)
  have hX'K : X' ≤ Subgroup.normalizer (K : Set G) := sup_le hXK (hcZ.trans hL1K)
  have hX'W : X' ≤ Subgroup.normalizer ((⁅U₁, K⁆ : Subgroup G) : Set G) := fun g hg =>
    SBd5.mem_normalizer_commutator_of (hU₁N g (hX'H hg) (hX'L hg)) (hX'K hg)
  have hKX' : K ≤ X' := le_sup_left.trans le_sup_left
  have hWe : IsElemAbelian 2 ⁅U₁, K⁆ := A1b.isElemAbelian_of_le (hMU₀.trans inf_le_left) hab
  have hOW : pCoreOf 2 K ≤ Subgroup.centralizer ((⁅U₁, K⁆ : Subgroup G) : Set G) := fun o ho => by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (Subgroup.mem_centralizer_iff.mp (hMU₀ hw).2 o (hOQ ho)).symm
  have hquad : ∀ Y : Subgroup G, Y ≤ conjClosure S.V3 H → K ≤ Subgroup.normalizer (Y : Set G) →
      K ≤ Subgroup.centralizer ((⁅Y, K⁆ : Subgroup G) : Set G) →
      K ≤ Subgroup.centralizer (Y : Set G) := by
    intro Y hY hKY hKc
    refine A6L74.le_centralizer_of_quadratic (A1b.isElemAbelian_of_le hY hab) hKY hK2
      fun u hu k hk => ?_
    have h1 : ⁅u, k⁆ ∈ ⁅Y, K⁆ := Subgroup.commutator_mem_commutator hu hk
    have e : k * u * k⁻¹ * u⁻¹ = ⁅u, k⁆⁻¹ := by rw [commutatorElement_def]; group
    rw [e]
    exact Subgroup.inv_mem _ (Subgroup.le_centralizer_iff.mp hKc h1)
  have hCW : K ⊓ Subgroup.centralizer ((⁅U₁, K⁆ : Subgroup G) : Set G) = pCoreOf 2 K := by
    rcases A6L74.eq_pCoreOf_or_eq_of_simple hs inf_le_left
      (fun k hk => mem_normalizer_inf_of (Subgroup.le_normalizer hk)
        (InternalSec.le_normalizer_centralizer (hKX'.trans hX'W) hk))
      (le_inf (pCoreOf_le 2 K) hOW) with h | h
    · exact h
    · exfalso
      apply hKM
      have hKc : K ≤ Subgroup.centralizer ((⁅U₁, K⁆ : Subgroup G) : Set G) := fun k hk => by
        have hk' : k ∈ K ⊓ Subgroup.centralizer ((⁅U₁, K⁆ : Subgroup G) : Set G) := by
          rw [h]
          exact hk
        exact hk'.2
      have hKU1c := hquad U₁ hU₁U hKU₁ hKc
      have hKV : K ≤ Subgroup.centralizer (S.V3 : Set G) := fun k hk =>
        Subgroup.mem_centralizer_iff.mpr fun v hv =>
          Subgroup.mem_centralizer_iff.mp (hKU1c hk) v (hV3U₁ hv)
      exact hKV.trans ((S.centralizer_V3_le h13315).trans S.NV_le_M)
  obtain ⟨U, hUW, hX'U, hCU, hOXU, hmin⟩ :=
    A6L74.exists_minimal_centralizer le_sup_left hXK le_sup_left hX'X hX'W hWe hCW
  have hUU₀ := hUW.trans hMU₀
  have hUU₁ := hUW.trans hMU₁
  have hUe : IsElemAbelian 2 U := A1b.isElemAbelian_of_le hUW hWe
  have hKU : K ≤ Subgroup.normalizer (U : Set G) := hKX'.trans hX'U
  have hOU : pCoreOf 2 K ≤ Subgroup.centralizer (U : Set G) :=
    hOW.trans (Subgroup.centralizer_le hUW)
  have hUK : ⁅U, K⁆ = U := by
    have hle : ⁅U, K⁆ ≤ U := Subgroup.le_normalizer_iff_commutator_le_left.mp hKU
    have hKN : K ≤ Subgroup.normalizer ((⁅U, K⁆ : Subgroup G) : Set G) := fun k hk =>
      SBd5.mem_normalizer_commutator_of (hKU hk) (Subgroup.le_normalizer hk)
    refine hmin _ hle (fun g hg => SBd5.mem_normalizer_commutator_of (hX'U hg) (hX'K hg)) ?_
    rcases A6L74.eq_pCoreOf_or_eq_of_simple hs inf_le_left
      (fun k hk => mem_normalizer_inf_of (Subgroup.le_normalizer hk)
        (InternalSec.le_normalizer_centralizer hKN hk))
      (le_inf (pCoreOf_le 2 K) (hOU.trans (Subgroup.centralizer_le hle))) with h | h
    · exact h
    · exfalso
      have hKc : K ≤ Subgroup.centralizer ((⁅U, K⁆ : Subgroup G) : Set G) := fun k hk => by
        have hk' : k ∈ K ⊓ Subgroup.centralizer ((⁅U, K⁆ : Subgroup G) : Set G) := by
          rw [h]
          exact hk
        exact hk'.2
      apply hK1
      rw [← hCU]
      exact le_inf le_rfl (hquad U (hUU₀.trans inf_le_left) hKU hKc)
  have hcU : c ∈ Subgroup.normalizer (U : Set G) :=
    hX'U (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  have hXU : X ≤ Subgroup.normalizer (U : Set G) := le_sup_left.trans hX'U
  have hcomm : ∀ g ∈ X', ∀ u ∈ U, c * (g * u * g⁻¹) * c⁻¹ = g * (c * u * c⁻¹) * g⁻¹ := by
    set Sg : Subgroup G := ((Subgroup.centralizer
      {convI hUe ⟨c, hcU⟩}).comap (convI hUe)).map (Subgroup.normalizer (U : Set G)).subtype
      with hSg
    have hmemS : ∀ g (hg : g ∈ Subgroup.normalizer (U : Set G)),
        convI hUe ⟨g, hg⟩ * convI hUe ⟨c, hcU⟩ = convI hUe ⟨c, hcU⟩ * convI hUe ⟨g, hg⟩ →
        g ∈ Sg := fun g hg h => ⟨⟨g, hg⟩, Subgroup.mem_centralizer_singleton_iff.mpr h, rfl⟩
    have hXS : X' ≤ Sg := by
      refine sup_le (fun g hg => hmemS g (hXU hg) ?_) (Subgroup.zpowers_le.2 (hmemS c hcU rfl))
      exact (commute_convI_cL1 hH hKH hHK hKL1 hhat hUe hcU hXU hOU hOXU
        (convI_mem_autI hUe hg (hXU hg))).symm
    intro g hg u hu
    obtain ⟨g', hg', rfl⟩ := hXS hg
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hg'
    have h2 := congrArg (fun φ : MulAut (IntMod U hUe) => (φ (IntMod.mk hUe ⟨u, hu⟩)).val) h1
    simp only [MulAut.mul_apply, convI_apply_val] at h2
    exact h2.symm
  have hUab : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hUe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hsq : ∀ x ∈ U, x * x = 1 := fun x hx => by
    have := hUe.2 x hx
    rwa [pow_two] at this
  have h3 : ∀ x ∈ U, c * c * c * x * c⁻¹ * c⁻¹ * c⁻¹ = x := fun x _ => by
    have e : c * c * c = 1 := by rw [← pow_three', hc3]
    calc c * c * c * x * c⁻¹ * c⁻¹ * c⁻¹ = (c * c * c) * x * (c * c * c)⁻¹ := by group
      _ = x := by rw [e]; group
  obtain ⟨P, hP⟩ := A6L74.exists_tr3Pre hUab hcU (⊥ : Subgroup G)
  have hPU : P ≤ U := fun u hu => ((hP u).1 hu).1
  have hX'P : X' ≤ Subgroup.normalizer (P : Set G) := by
    intro g hg
    refine A6L19.mem_normalizer_of_conj fun u hu => ?_
    obtain ⟨huU, htr⟩ := (hP u).1 hu
    refine (hP _).2 ⟨(Subgroup.mem_normalizer_iff.mp (hX'U hg) u).mp huU, ?_⟩
    have hcuU : c * u * c⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp hcU u).mp huU
    have e : A6L74.tr3 c (g * u * g⁻¹) = g * A6L74.tr3 c u * g⁻¹ := by
      unfold A6L74.tr3
      have e1 : c * c * (g * u * g⁻¹) * c⁻¹ * c⁻¹ = c * (c * (g * u * g⁻¹) * c⁻¹) * c⁻¹ := by
        group
      have e2 : c * c * u * c⁻¹ * c⁻¹ = c * (c * u * c⁻¹) * c⁻¹ := by group
      rw [e1, hcomm g hg u huU, hcomm g hg _ hcuU, e2]
      group
    rw [e, Subgroup.mem_bot.mp htr, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hfixV1 : ∀ u ∈ U, c * u * c⁻¹ = u → u ∈ fsuV1 T V := fun u hu hcu =>
    hfpf u (hUU₁ hu) (by rw [hcu, mul_inv_cancel]; exact Subgroup.one_mem _)
  have hCP : K ⊓ Subgroup.centralizer (P : Set G) = pCoreOf 2 K := by
    refine le_antisymm (fun k hk => ?_)
      (le_inf (pCoreOf_le 2 K) (hOU.trans (Subgroup.centralizer_le hPU)))
    rw [← hCU]
    refine ⟨hk.1, Subgroup.mem_centralizer_iff.mpr fun u hu => ?_⟩
    obtain ⟨N, hNdef⟩ : ∃ N, N = A6L74.tr3 c u := ⟨_, rfl⟩
    have hN : N ∈ U := hNdef ▸ A6L74.tr3_mem hcU hu
    have hNc : c * N * c⁻¹ = N := hNdef ▸ A6L74.conj_tr3 hUab hcU h3 hu
    have hNV := hfixV1 N hN hNc
    have hmP : u * N ∈ P := (hP _).2 ⟨U.mul_mem hu hN, by
      rw [hNdef, A6L74.tr3_mul_tr3 hUab hcU h3 hsq hu]
      exact Subgroup.one_mem _⟩
    have e : u = u * N * N := by rw [mul_assoc, hsq N hN, mul_one]
    have hk1 : u * N * k = k * (u * N) := Subgroup.mem_centralizer_iff.mp hk.2 _ hmP
    have hk2 : N * k = k * N := by
      have h := hF.conj_eq_of_mem_V₁ (hKH hk.1) hNV
      calc N * k = (k * N * k⁻¹) * k := by rw [h]
        _ = k * N := by group
    calc u * k = u * N * N * k := by rw [← e]
      _ = u * N * (N * k) := by group
      _ = u * N * (k * N) := by rw [hk2]
      _ = u * N * k * N := by group
      _ = k * (u * N) * N := by rw [hk1]
      _ = k * (u * N * N) := by group
      _ = k * u := by rw [← e]
  have hPeq : P = U := hmin P hPU hX'P hCP
  refine ⟨U, hUU₀, hX'U, hCU, hOXU, hUK, fun u hu hcu => ?_⟩
  have hu' : u ∈ P := by rw [hPeq]; exact hu
  have h1 := ((hP u).1 hu').2
  rwa [A6L74.tr3_of_fixed hcu (hsq u hu), Subgroup.mem_bot] at h1

end Simple

end Setting4

end CFSG.Quasithin.H13.A6
