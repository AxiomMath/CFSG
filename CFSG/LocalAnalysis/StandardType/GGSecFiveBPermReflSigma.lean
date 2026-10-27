module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaForkCox
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
import CFSG.GroupTheory.SwapMulOrder
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGSignedCoordRefl
import CFSG.LocalAnalysis.StandardType.GGTBJTypeBFrameChange
import CFSG.LocalAnalysis.StandardType.GGSecFiveNSEnnolaTypeAAux

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord Multiplicative

@[expose] def GGNoReflFramePair {G : Type} [Group G] (p : ℕ) (Bs X : Subgroup G) : Prop :=
  ¬ ∃ c₁ ∈ ggAutomizer X Bs, ∃ c₂ ∈ ggAutomizer X Bs, GGIsReflection p c₁ ∧
      GGIsReflection p c₂ ∧ 4 ∣ orderOf (c₁ * c₂)

private theorem orderOf_swap_mul_swap_of_disjoint {n : ℕ} {a b c d : Fin n}
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    orderOf (Equiv.swap a b * Equiv.swap c d) = 2 := by
  have hcomm : Commute (Equiv.swap a b) (Equiv.swap c d) :=
    Equiv.Perm.Disjoint.commute (fun z => by
      by_cases hz : z = a ∨ z = b
      · right
        rcases hz with rfl | rfl
        · exact Equiv.swap_apply_of_ne_of_ne hac had
        · exact Equiv.swap_apply_of_ne_of_ne hbc hbd
      · left
        push Not at hz
        exact Equiv.swap_apply_of_ne_of_ne hz.1 hz.2)
  have hsq : (Equiv.swap a b * Equiv.swap c d) ^ 2 = 1 := by
    rw [hcomm.mul_pow, pow_two (Equiv.swap a b), pow_two (Equiv.swap c d),
      Equiv.swap_mul_self, Equiv.swap_mul_self, one_mul]
  have hne : Equiv.swap a b * Equiv.swap c d ≠ 1 := by
    intro h1
    have h2 := congrArg (fun σ : Equiv.Perm (Fin n) => σ a) h1
    rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hac had,
      Equiv.swap_apply_left, Equiv.Perm.one_apply] at h2
    exact hab h2.symm
  have hdvd := orderOf_dvd_of_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne
  · exact h

theorem eq_permAut_swap_of_mem_aPermutationFull {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {u : MulAut (Fin n → Multiplicative (ZMod p))} (hu : u ∈ aPermutationFull n p)
    (hu2 : u ^ 2 = 1)
    (hfix : Nat.card {f // u f = f} * p = Nat.card (Fin n → Multiplicative (ZMod p))) :
    ∃ a b : Fin n, a ≠ b ∧ u = permAut (Equiv.swap a b) := by
  let f₁ : Fin n → Multiplicative (ZMod p) := fun _ => Multiplicative.ofAdd (1 : ZMod p)
  have hf₁ : ∀ i, toAdd (f₁ i) = 1 := fun _ => rfl
  have hfix₁ : u f₁ = f₁ :=
    (forall_aPermutationFull_fix_iff f₁).mpr (fun _ _ => rfl) u hu
  rcases eq_sgnAut_or_swap_of_isRefl hp hp2 (aPermutationFull_le_bSignedFull hu) hu2 hfix with
    ⟨i, hi⟩ | ⟨a, b, hab, hi | hi⟩
  · exfalso
    rw [hi] at hfix₁
    have h := congrArg (fun g : Fin n → Multiplicative (ZMod p) => toAdd (g i)) hfix₁
    rw [sgnAut_apply, Function.update_self, toAdd_inv, hf₁ i] at h
    exact coord_zero_ne_one hp (coord_eq_zero_of_eq_neg hp hp2 h.symm).symm
  · exact ⟨a, b, hab, hi⟩
  · exfalso
    rw [hi] at hfix₁
    have h := congrArg (fun g : Fin n → Multiplicative (ZMod p) => toAdd (g a)) hfix₁
    rw [negTrans_apply (p := p) a b hab f₁ a, if_pos rfl, toAdd_inv, hf₁ b] at h
    exact coord_zero_ne_one hp (coord_eq_zero_of_eq_neg hp hp2 h.symm).symm

theorem swap_disjoint_of_two_dvd_orderOf {n : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (h : 2 ∣ orderOf (Equiv.swap a b * Equiv.swap c d)) : a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  have hmem := CFSG.GroupTheory.orderOf_mul_mem_of_isSwap
    (Equiv.Perm.swap_isSwap_iff.mpr hab) (Equiv.Perm.swap_isSwap_iff.mpr hcd)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  have h2 : orderOf (Equiv.swap a b * Equiv.swap c d) = 2 := by
    rcases hmem with h' | h' | h'
    · rw [h'] at h
      norm_num at h
    · exact h'
    · rw [h'] at h
      norm_num at h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hac
    rw [← hac] at h2 hcd
    by_cases hbd : b = d
    · rw [hbd, Equiv.swap_mul_self, orderOf_one] at h2
      omega
    · rw [(Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hcd hbd).orderOf] at h2
      omega
  · intro had
    rw [← had] at h2 hcd
    rw [Equiv.swap_comm c a] at h2
    by_cases hbc : b = c
    · rw [← hbc, Equiv.swap_mul_self, orderOf_one] at h2
      omega
    · rw [(Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hcd.symm hbc).orderOf] at h2
      omega
  · intro hbc
    rw [← hbc] at h2 hcd
    rw [Equiv.swap_comm a b] at h2
    by_cases had : a = d
    · rw [← had, Equiv.swap_mul_self, orderOf_one] at h2
      omega
    · rw [(Equiv.Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hab) hcd had).orderOf] at h2
      omega
  · intro hbd
    rw [← hbd] at h2 hcd
    rw [Equiv.swap_comm c b, Equiv.swap_comm a b] at h2
    by_cases hac : a = c
    · rw [hac, Equiv.swap_mul_self, orderOf_one] at h2
      omega
    · rw [(Equiv.Perm.isThreeCycle_swap_mul_swap_same (Ne.symm hab) hcd.symm hac).orderOf] at h2
      omega

theorem swap_meet_of_three_dvd_orderOf {n : ℕ} {a b c d : Fin n} (hab : a ≠ b) (hcd : c ≠ d)
    (h : 3 ∣ orderOf (Equiv.swap a b * Equiv.swap c d)) : a = c ∨ a = d ∨ b = c ∨ b = d := by
  have hmem := CFSG.GroupTheory.orderOf_mul_mem_of_isSwap
    (Equiv.Perm.swap_isSwap_iff.mpr hab) (Equiv.Perm.swap_isSwap_iff.mpr hcd)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  have h3 : orderOf (Equiv.swap a b * Equiv.swap c d) = 3 := by
    rcases hmem with h' | h' | h'
    · rw [h'] at h
      norm_num at h
    · rw [h'] at h
      norm_num at h
    · exact h'
  by_contra hcon
  simp only [not_or] at hcon
  obtain ⟨hac, had, hbc, hbd⟩ := hcon
  rw [orderOf_swap_mul_swap_of_disjoint hab hac had hbc hbd] at h3
  omega

variable {G : Type} [Group G]

private theorem permAutHom_injective {n p : ℕ} (hp : p.Prime) :
    Function.Injective (TypeBDatum.permAutHom n p) := by
  intro σ τ h
  apply Equiv.ext
  intro i
  have h1 : (TypeBDatum.permAutHom n p σ) (Pi.mulSingle i (ofAdd (1 : ZMod p))) =
      (TypeBDatum.permAutHom n p τ) (Pi.mulSingle i (ofAdd (1 : ZMod p))) := by
    rw [h]
  change permAut (p := p) σ (Pi.mulSingle i (ofAdd (1 : ZMod p))) =
      permAut (p := p) τ (Pi.mulSingle i (ofAdd (1 : ZMod p))) at h1
  rw [permAut_mulSingle, permAut_mulSingle] at h1
  exact (mulSingle_ofAdd_eq_iff (p := p)
    (fun h0 => coord_zero_ne_one hp h0.symm) h1).1

theorem exists_eq_permAut_swap_of_isReflection {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs L : Subgroup G} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hAut : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p)
    {c : MulAut ↥Bs} (hc : c ∈ ggAutomizer L Bs) (hr : GGIsReflection p c) :
    ∃ a b : Fin n, a ≠ b ∧ MulAut.congr eta c = permAut (Equiv.swap a b) := by
  have hu : MulAut.congr eta c ∈ aPermutationFull n p := by
    rw [← hAut]
    exact Subgroup.mem_map_of_mem (MulAut.congr eta).toMonoidHom hc
  have hu2 : (MulAut.congr eta c) ^ 2 = 1 := by
    have h := map_pow (MulAut.congr eta) c 2
    rw [hr.1, map_one] at h
    exact h.symm
  have hcongr : ∀ b : ↥Bs, MulAut.congr eta c (eta b) = eta (c b) := fun b => by
    rw [MulAut.congr_apply]
    simp
  have hcard : Nat.card {f : Fin n → Multiplicative (ZMod p) //
      MulAut.congr eta c f = f} = Nat.card {b : ↥Bs // c b = b} := by
    let e : {b : ↥Bs // c b = b} ≃
        {f : Fin n → Multiplicative (ZMod p) // MulAut.congr eta c f = f} :=
      { toFun := fun x => ⟨eta x.1, by rw [hcongr, x.2]⟩
        invFun := fun x => ⟨eta.symm x.1, by
          apply eta.injective
          rw [← hcongr]
          simpa using x.2⟩
        left_inv := fun x => Subtype.ext (by simp)
        right_inv := fun x => Subtype.ext (by simp) }
    exact Nat.card_congr e.symm
  have hfix : Nat.card {f : Fin n → Multiplicative (ZMod p) //
        MulAut.congr eta c f = f} * p =
      Nat.card (Fin n → Multiplicative (ZMod p)) := by
    rw [hcard, hr.2]
    exact Nat.card_congr eta.toEquiv
  exact eq_permAut_swap_of_mem_aPermutationFull hp hp2 hu hu2 hfix

theorem orderOf_mul_eq_orderOf_swap_mul_swap {p n : ℕ} (hp : p.Prime) {Bs : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {c₁ c₂ : MulAut ↥Bs} {a b c d : Fin n}
    (h₁ : MulAut.congr eta c₁ = permAut (Equiv.swap a b))
    (h₂ : MulAut.congr eta c₂ = permAut (Equiv.swap c d)) :
    orderOf (c₁ * c₂) = orderOf (Equiv.swap a b * Equiv.swap c d) := by
  have hperm : permAut (p := p) (Equiv.swap a b) * permAut (p := p) (Equiv.swap c d) =
      permAut (p := p) (Equiv.swap a b * Equiv.swap c d) := by
    change (TypeBDatum.permAutHom n p) (Equiv.swap a b) *
        (TypeBDatum.permAutHom n p) (Equiv.swap c d) =
      (TypeBDatum.permAutHom n p) (Equiv.swap a b * Equiv.swap c d)
    rw [← map_mul]
  calc orderOf (c₁ * c₂)
      = orderOf (MulAut.congr eta (c₁ * c₂)) :=
        (MulEquiv.orderOf_eq (MulAut.congr eta) (c₁ * c₂)).symm
    _ = orderOf (MulAut.congr eta c₁ * MulAut.congr eta c₂) := by rw [map_mul]
    _ = orderOf (permAut (p := p) (Equiv.swap a b) *
          permAut (p := p) (Equiv.swap c d)) := by rw [h₁, h₂]
    _ = orderOf (permAut (p := p) (Equiv.swap a b * Equiv.swap c d)) := by rw [hperm]
    _ = orderOf (Equiv.swap a b * Equiv.swap c d) :=
        orderOf_injective (TypeBDatum.permAutHom n p) (permAutHom_injective hp) _

theorem ggNoReflFramePair_of_aPermutationFull {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs L : Subgroup G} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hAut : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p) :
    GGNoReflFramePair p Bs L := by
  rintro ⟨c₁, hc₁, c₂, hc₂, hr₁, hr₂, h4⟩
  obtain ⟨a, b, hab, h₁⟩ := exists_eq_permAut_swap_of_isReflection hp hp2 eta hAut hc₁ hr₁
  obtain ⟨c, d, hcd, h₂⟩ := exists_eq_permAut_swap_of_isReflection hp hp2 eta hAut hc₂ hr₂
  rw [orderOf_mul_eq_orderOf_swap_mul_swap hp eta h₁ h₂] at h4
  have hmem := CFSG.GroupTheory.orderOf_mul_mem_of_isSwap
    (Equiv.Perm.swap_isSwap_iff.mpr hab) (Equiv.Perm.swap_isSwap_iff.mpr hcd)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h' | h' | h'
  · rw [h'] at h4
    norm_num at h4
  · rw [h'] at h4
    norm_num at h4
  · rw [h'] at h4
    norm_num at h4

theorem ggNoReflFork_of_aPermutationFull {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Bs L : Subgroup G} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (hAut : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = aPermutationFull n p) :
    GGNoReflFork p Bs L := by
  rintro ⟨c₀, hc₀, c₁, hc₁, c₂, hc₂, c₃, hc₃, hr₀, hr₁, hr₂, hr₃,
    h01, h02, h03, h12, h13, h23⟩
  obtain ⟨a₀, b₀, hab₀, h₀⟩ := exists_eq_permAut_swap_of_isReflection hp hp2 eta hAut hc₀ hr₀
  obtain ⟨a₁, b₁, hab₁, h₁⟩ := exists_eq_permAut_swap_of_isReflection hp hp2 eta hAut hc₁ hr₁
  obtain ⟨a₂, b₂, hab₂, h₂⟩ := exists_eq_permAut_swap_of_isReflection hp hp2 eta hAut hc₂ hr₂
  obtain ⟨a₃, b₃, hab₃, h₃⟩ := exists_eq_permAut_swap_of_isReflection hp hp2 eta hAut hc₃ hr₃
  rw [orderOf_mul_eq_orderOf_swap_mul_swap hp eta h₀ h₁] at h01
  rw [orderOf_mul_eq_orderOf_swap_mul_swap hp eta h₀ h₂] at h02
  rw [orderOf_mul_eq_orderOf_swap_mul_swap hp eta h₀ h₃] at h03
  rw [orderOf_mul_eq_orderOf_swap_mul_swap hp eta h₁ h₂] at h12
  rw [orderOf_mul_eq_orderOf_swap_mul_swap hp eta h₁ h₃] at h13
  rw [orderOf_mul_eq_orderOf_swap_mul_swap hp eta h₂ h₃] at h23
  have m1 := swap_meet_of_three_dvd_orderOf hab₀ hab₁ h01
  have m2 := swap_meet_of_three_dvd_orderOf hab₀ hab₂ h02
  have m3 := swap_meet_of_three_dvd_orderOf hab₀ hab₃ h03
  have d12 := swap_disjoint_of_two_dvd_orderOf hab₁ hab₂ h12
  have d13 := swap_disjoint_of_two_dvd_orderOf hab₁ hab₃ h13
  have d23 := swap_disjoint_of_two_dvd_orderOf hab₂ hab₃ h23
  exact ggNEA_meet_three_disjoint_pairs
    d12.1 d12.2.1 d12.2.2.1 d12.2.2.2
    d13.1 d13.2.1 d13.2.2.1 d13.2.2.2
    d23.1 d23.2.1 d23.2.2.1 d23.2.2.2
    m1 m2 m3

end CFSG.StandardType

end
