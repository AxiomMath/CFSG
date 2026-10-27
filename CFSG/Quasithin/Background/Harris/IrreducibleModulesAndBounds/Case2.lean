module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case2Model
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case2SelfDual
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case2End

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Blueprint CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Setup.Family CFSG.Sporadic.Schreier

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem case2_G93Case2
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .M22)
    (hZ : Nat.card (Subgroup.center ↥L) = 3) : G93Case2 Γ L m := by
  obtain ⟨hd12, ψ, hψ⟩ := case2_model h e hZ
  obtain ⟨hm5, hAL⟩ := case2_rank h e
  have hm : m = 5 := by have := h.bound; omega
  have hAL' := hAL hm
  have hLΓ : L ≤ Γ := h.L_comp.1
  have hLn : (L.subgroupOf Γ).Normal :=
    (Subgroup.normal_subgroupOf_iff hLΓ).2 fun l γ hl hγ => h.H_normal γ hγ l hl
  have hV : Nat.card V = 2 ^ 12 := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rwa [Nat.card_zmod, hd12] at this
  have hMcard : Nat.card (↥L ⧸ Subgroup.center ↥L) = 2 ^ 7 * 3465 := by
    rw [Nat.card_congr e.toEquiv]
    exact m22_card_eq
  have hLcard : Nat.card ↥L = 3 * (2 ^ 7 * 3465) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L), hMcard, hZ]
    ring
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 11 (by rw [hLcard]; norm_num)
  have hg : ((x : ↥L) : GLV V) ∈ L := x.2
  have hgo : orderOf ((x : ↥L) : GLV V) = 11 := by rw [Subgroup.orderOf_coe]; exact hx
  have : Nontrivial (Subgroup.center ↥L) :=
    Finite.one_lt_card_iff_nontrivial.1 (by rw [hZ]; norm_num)
  obtain ⟨zc, hzc1⟩ := exists_ne (1 : Subgroup.center ↥L)
  have hzcomm : ∀ l ∈ L, l * ((zc : ↥L) : GLV V) = ((zc : ↥L) : GLV V) * l := fun l hl => by
    have := Subgroup.mem_center_iff.1 zc.2 ⟨l, hl⟩
    exact congrArg Subtype.val this
  have hz1 : ((zc : ↥L) : GLV V) ≠ 1 := fun hh => hzc1 (Subtype.ext (Subtype.ext hh))
  have hF := natCard_endCommutant_eq_four h.H_irr hg hgo hzcomm hz1 hV
  have hEnd : EndIsField L 2 := endIsField_of_natCard h.H_irr (by rw [hF]; norm_num)
  have hSD : SelfDual L ⊤ := selfDual_of_hatM22 ψ hψ
  have hcentEq := centralizer_eq_center_of_card hF hZ
  have hcentle : Subgroup.centralizer (L : Set (GLV V)) ≤ L := by
    rw [hcentEq]
    rintro _ ⟨l, -, rfl⟩
    exact l.2
  have hcentΓ : Subgroup.centralizer (L : Set (GLV V)) ≤ Γ := hcentle.trans hLΓ
  have hcentcard : Nat.card (Subgroup.centralizer (L : Set (GLV V))) = 3 := by
    rw [hcentEq, Subgroup.card_map_of_injective (Subgroup.subtype_injective L), hZ]
  have hperf : Group.IsPerfect ↥L := ⟨h.L_comp.2.2.1⟩
  let α := actionOnCQ hLΓ hLn
  have hker : α.ker = (Subgroup.centralizer (L : Set (GLV V))).subgroupOf Γ := by
    ext γ
    rw [MonoidHom.mem_ker, actionOnCQ_eq_one_iff hLΓ hLn hperf γ, Subgroup.mem_subgroupOf]
  have hkercard : Nat.card α.ker = 3 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcentΓ).toEquiv, hcentcard]
  have hrange : Nat.card α.range ≤ 2 * (2 ^ 7 * 3465) := by
    have h1 : Nat.card α.range ≤ Nat.card (MulAut (CQ L)) :=
      Nat.card_le_card_of_injective _ Subtype.val_injective
    have h2 : Nat.card (MulAut (CQ L)) = Nat.card (MulAut (NativeSporadic.Carrier .M22)) :=
      Nat.card_congr (MulAut.congr e).toEquiv
    have h3 := m22_mulAut_card
    have h4 := m22_card_eq
    calc Nat.card α.range ≤ Nat.card (MulAut (NativeSporadic.Carrier .M22)) := h2 ▸ h1
      _ ≤ 2 * Nat.card S22 := h3
      _ = 2 * (2 ^ 7 * 3465) := by rw [h4]
  have hΓle : Nat.card ↥Γ ≤ 2 * (3 * (2 ^ 7 * 3465)) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup α.ker, hkercard,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange α).toEquiv]
    nlinarith [hrange]
  set N : Subgroup ↥Γ := L.subgroupOf Γ with hN
  have hNcard : Nat.card N = 3 * (2 ^ 7 * 3465) := by
    rw [← hLcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLΓ).toEquiv
  have hmulidx := Subgroup.card_mul_index N
  rw [hNcard] at hmulidx
  have hidx_le : N.index ≤ 2 := by
    by_contra hgt
    push Not at hgt
    have : 3 * (2 ^ 7 * 3465) * 3 ≤ Nat.card ↥Γ := by
      rw [← hmulidx]
      exact Nat.mul_le_mul_left _ hgt
    omega
  have hidx_ne_one : N.index ≠ 1 := by
    intro h1
    rw [Subgroup.index_eq_one] at h1
    apply hAL'
    intro a ha
    have : (⟨a, h.A_le ha⟩ : ↥Γ) ∈ N := by rw [h1]; trivial
    exact this
  have hidx_ne_zero : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have hidx : N.index = 2 := by omega
  rw [hidx] at hmulidx
  refine ⟨⟨hm, hd12, ⟨N, hLn, hidx, ?_, (Subgroup.map_subgroupOf_eq_of_le hLΓ).symm⟩, ?_⟩, hEnd, hSD⟩
  · exact CFSG.Quasithin.H.Mathieu.H12Pf.isHat_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hLΓ).symm (isHat_of_hyp h.L_comp.2.2 hZ e)
  · rw [← hmulidx]
    norm_num

theorem case2_HatM22
    {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hM : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier .M22))
    (hZ : Nat.card (Subgroup.center ↥L) = 3) : G93Concl Γ L m :=
  Or.inr (Or.inr (Or.inl (case2_G93Case2 h hM.some hZ)))

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
