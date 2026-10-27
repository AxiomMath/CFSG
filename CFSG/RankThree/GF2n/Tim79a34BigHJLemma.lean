module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.RankThree.GF2n.Tim79a

open scoped commutatorElement

namespace NormalSection

variable {Mg : Type*} [Group Mg] (P V : Subgroup Mg) [P.Normal] [V.Normal]

theorem map_conjNormal_subgroupOf (m : Mg) :
    (V.subgroupOf P).map ((MulAut.conjNormal (H := P) m : ↥P ≃* ↥P) : ↥P →* ↥P) =
      V.subgroupOf P := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    have hx' : (x : Mg) ∈ V := hx
    exact (inferInstance : V.Normal).conj_mem _ hx' m
  · intro y hy
    have hy' : (y : Mg) ∈ V := hy
    refine Subgroup.mem_map.mpr ⟨(MulAut.conjNormal m)⁻¹ y, ?_, ?_⟩
    · exact (inferInstance : V.Normal).conj_mem _ hy' m⁻¹
    · simp

@[expose] def conjEquiv (m : Mg) : (↥P ⧸ V.subgroupOf P) ≃* (↥P ⧸ V.subgroupOf P) :=
  QuotientGroup.congr (V.subgroupOf P) (V.subgroupOf P) (MulAut.conjNormal m)
    (map_conjNormal_subgroupOf P V m)

@[expose] def conjAction : Mg →* MulAut (↥P ⧸ V.subgroupOf P) where
  toFun := conjEquiv P V
  map_one' := MulEquiv.ext fun x => QuotientGroup.induction_on x fun y => by
    change (((MulAut.conjNormal (1 : Mg)) y : ↥P) : ↥P ⧸ V.subgroupOf P) = y
    rw [map_one]
    rfl
  map_mul' m n := MulEquiv.ext fun x => QuotientGroup.induction_on x fun y => by
    change (((MulAut.conjNormal (m * n)) y : ↥P) : ↥P ⧸ V.subgroupOf P) =
      (((MulAut.conjNormal m) ((MulAut.conjNormal n) y) : ↥P) : ↥P ⧸ V.subgroupOf P)
    rw [map_mul]
    rfl

theorem conjAction_mk (m : Mg) (y : ↥P) :
    conjAction P V m (y : ↥P ⧸ V.subgroupOf P) =
      ((MulAut.conjNormal m y : ↥P) : ↥P ⧸ V.subgroupOf P) := rfl

theorem conjAction_eq_one_iff (m : Mg) :
    conjAction P V m = 1 ↔ ∀ x ∈ P, ⁅m, x⁆ ∈ V := by
  constructor
  · intro h x hx
    have h1 := MulEquiv.congr_fun h ((⟨x⁻¹, P.inv_mem hx⟩ : ↥P) : ↥P ⧸ V.subgroupOf P)
    rw [conjAction_mk] at h1
    have h2 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h1)
    have h3 : ⁅m, x⁆ = (m * x⁻¹ * m⁻¹)⁻¹ * x⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h3]
    exact h2
  · intro h
    refine MulEquiv.ext fun u => QuotientGroup.induction_on u fun y => ?_
    rw [conjAction_mk]
    refine QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ?_)
    have h4 : ((((MulAut.conjNormal (H := P) m) y)⁻¹ * y : ↥P) : Mg) = ⁅m, (y : Mg)⁻¹⁆ := by
      rw [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
      group
    rw [h4]
    exact h _ (P.inv_mem y.2)

variable {P V}

theorem quot_mul_comm (hcomm : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ V) (a b : ↥P ⧸ V.subgroupOf P) :
    a * b = b * a := by
  induction a using QuotientGroup.induction_on with | H x => ?_
  induction b using QuotientGroup.induction_on with | H y => ?_
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  have h1 := hcomm (y : Mg)⁻¹ (P.inv_mem y.2) (x : Mg)⁻¹ (P.inv_mem x.2)
  have h2 : (((x * y)⁻¹ * (y * x) : ↥P) : Mg) = ⁅(y : Mg)⁻¹, (x : Mg)⁻¹⁆ := by
    rw [commutatorElement_def]
    simp [mul_assoc]
  rw [h2]
  exact h1

theorem quot_mul_self (hsq : ∀ x ∈ P, x * x ∈ V) (a : ↥P ⧸ V.subgroupOf P) : a * a = 1 := by
  induction a using QuotientGroup.induction_on with | H x => ?_
  rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact hsq x x.2

theorem quot_card [Finite Mg] (hVP : V ≤ P) (hcard : Nat.card P = 2 ^ 8 * Nat.card V) :
    Nat.card (↥P ⧸ V.subgroupOf P) = 2 ^ 8 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (V.subgroupOf P)
  have h2 : Nat.card (V.subgroupOf P) = Nat.card V :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVP).toEquiv
  have hpos : 0 < Nat.card V := Nat.card_pos
  rw [h2, hcard] at h1
  exact (Nat.eq_of_mul_eq_mul_right hpos h1).symm

end NormalSection

theorem hj_data_of_pq {Mg : Type} [Group Mg] [Finite Mg] (Q P V : Subgroup Mg)
    [Q.Normal] [P.Normal] [V.Normal] (Lb : Subgroup (Mg ⧸ Q)) (Jg : Type) [Group Jg]
    [IsSimpleGroup Jg] (e : ↥Lb ≃* Jg)
    (hVP : V ≤ P) (hPQ : P ≤ Q) (hsq : ∀ x ∈ P, x * x ∈ V)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ V) (hQ : ∀ q ∈ Q, ∀ x ∈ P, ⁅q, x⁆ ∈ V)
    (hcard : Nat.card P = 2 ^ 8 * Nat.card V)
    (hnt : ∃ m : Mg, (m : Mg ⧸ Q) ∈ Lb ∧ ∃ x ∈ P, ⁅m, x⁆ ∉ V) :
    ∃ ρ : Jg →* Matrix.GeneralLinearGroup (Fin 8) (ZMod 2), Function.Injective ρ := by
  obtain ⟨c⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2)
    (NormalSection.quot_mul_comm hcomm)
    (fun a => by rw [pow_two]; exact NormalSection.quot_mul_self hsq a)
    (NormalSection.quot_card hVP hcard)
  let ι := CFSG.SectionRank.Ccomm.elemAutEquivGL c
  let α : Mg ⧸ Q →* MulAut (↥P ⧸ V.subgroupOf P) :=
    QuotientGroup.lift Q (NormalSection.conjAction P V) fun q hq =>
      MonoidHom.mem_ker.mpr ((NormalSection.conjAction_eq_one_iff P V q).mpr (hQ q hq))
  let β : Jg →* MulAut (↥P ⧸ V.subgroupOf P) := (α.comp Lb.subtype).comp e.symm.toMonoidHom
  have hβ : Function.Injective β := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (MonoidHom.ker β) with h | h
    · exact (MonoidHom.ker_eq_bot_iff β).mp h
    · exfalso
      obtain ⟨m, hm, x, hx, hxV⟩ := hnt
      have hmem : e ⟨(m : Mg ⧸ Q), hm⟩ ∈ MonoidHom.ker β := by
        rw [h]
        exact Subgroup.mem_top _
      have h1 : β (e ⟨(m : Mg ⧸ Q), hm⟩) = NormalSection.conjAction P V m := by
        change α ((e.symm (e ⟨(m : Mg ⧸ Q), hm⟩) : ↥Lb) : Mg ⧸ Q) = NormalSection.conjAction P V m
        rw [MulEquiv.symm_apply_apply]
        exact QuotientGroup.lift_mk _ _ m
      exact hxV ((NormalSection.conjAction_eq_one_iff P V m).mp
        (h1 ▸ MonoidHom.mem_ker.mp hmem) x hx)
  exact ⟨ι.toMonoidHom.comp β, ι.injective.comp hβ⟩

end CFSG.RankThree.GF2n.Tim79a
