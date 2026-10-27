module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4BlkC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4BlkD

public section

namespace CFSG.Quasithin.H23P4

open scoped commutatorElement

variable {G : Type*} [Group G]

namespace ModData

variable {L U Z : Subgroup G} {y : G} (h : ModData L U Z y)
include h

theorem conj_Z {l z : G} (hl : l ∈ L) (hz : z ∈ Z) : l * z * l⁻¹ = z := by
  rw [h.cent z hz l hl, mul_assoc, mul_inv_cancel, mul_one]

private def conjU (l : L) (u : U) : U := ⟨(l : G) * u * (l : G)⁻¹, h.normU l l.2 u u.2⟩

private theorem coe_conjU (l : L) (u : U) :
    (conjU h l u : G) = (l : G) * u * (l : G)⁻¹ := rfl

private theorem conjU_inv_mul (l : L) (a b : U) :
    conjU h l (a⁻¹ * b) = (conjU h l a)⁻¹ * conjU h l b := by
  apply Subtype.ext
  simp only [coe_conjU, Subgroup.coe_mul, InvMemClass.coe_inv]
  group

private def actFn (l : L) : (↥U ⧸ Z.subgroupOf U) → (↥U ⧸ Z.subgroupOf U) :=
  Quotient.map' (conjU h l) (fun a b hab => by
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hab ⊢
    rw [← conjU_inv_mul, coe_conjU, h.conj_Z l.2 hab]
    exact hab)

private theorem actFn_mk (l : L) (u : U) :
    actFn h l (QuotientGroup.mk u) = QuotientGroup.mk (conjU h l u) := rfl

private theorem conjU_one (u : U) : conjU h 1 u = u := Subtype.ext (by simp [coe_conjU])

private theorem conjU_mul (a b : L) (u : U) :
    conjU h (a * b) u = conjU h a (conjU h b u) :=
  Subtype.ext (by simp [coe_conjU, mul_assoc])

@[instance_reducible] private def actMulAction : MulAction ↥L (↥U ⧸ Z.subgroupOf U) where
  smul := actFn h
  one_smul v := by
    induction v using QuotientGroup.induction_on with
    | H u => exact congrArg QuotientGroup.mk (conjU_one h u)
  mul_smul a b v := by
    induction v using QuotientGroup.induction_on with
    | H u => exact congrArg QuotientGroup.mk (conjU_mul h a b u)

private theorem actFn_mk_eq_iff (l : L) (u : U) :
    actFn h l (QuotientGroup.mk u) = QuotientGroup.mk u ↔ ⁅(l : G), (u : G)⁆ ∈ Z := by
  rw [actFn_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hc : ⁅(l : G), (u : G)⁆ ∈ U := mul_mem (h.normU l l.2 u u.2) (inv_mem u.2)
  have e : (((conjU h l u)⁻¹ * u : U) : G) = ⁅(l : G), (u : G)⁆⁻¹ := by
    have hcomm := h.abel _ hc u u.2
    have e1 : (l : G) * u * (l : G)⁻¹ = ⁅(l : G), (u : G)⁆ * u := by
      simp only [commutatorElement_def]
      group
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv, coe_conjU]
    rw [e1, hcomm]
    group
  rw [e, inv_mem_iff]

theorem comm_mem_of_twSub_eq [Finite G] (hperf : ⁅L, L⁆ = L) {k : ℕ} (hy : y ^ 5 ^ k = 1)
    (hW : h.twSub y = Z) (hd : Z.relIndex U = 16) : ∀ l ∈ L, ∀ u ∈ U, ⁅l, u⁆ ∈ Z := by
  let _ : MulAction ↥L (↥U ⧸ Z.subgroupOf U) := actMulAction h
  have hdich' : ∀ l ∈ L, h.twSub l = Z ∨ h.twSub l = U := fun l hl =>
    h.eq_or_eq_of_relIndex_sixteen (X := h.twSub l)
      (h.Z_le_twSub fun z hz => by rw [h.conj_Z hl hz]; exact hz) (h.twSub_le l)
      (fun x hx => h.yConj_twSub hl hx) hy hW hd
  have hperf' : commutator ↥L = ⊤ := Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr hperf)
  have hfix : ∀ (γ : ↥L) (u : U), γ • (QuotientGroup.mk u : ↥U ⧸ Z.subgroupOf U) =
      QuotientGroup.mk u ↔ ⁅(γ : G), (u : G)⁆ ∈ Z := fun γ u => actFn_mk_eq_iff h γ u
  have hall := perfect_action_trivial (Γ := ↥L) (V := ↥U ⧸ Z.subgroupOf U)
    (QuotientGroup.mk 1) hd (fun γ => by
      show actFn h γ (QuotientGroup.mk 1) = QuotientGroup.mk 1
      rw [actFn_mk]
      exact congrArg QuotientGroup.mk (Subtype.ext (by simp [coe_conjU]))) hperf' (fun γ => by
      rcases hdich' γ γ.2 with hZ | hU
      · right
        intro v
        induction v using QuotientGroup.induction_on with
        | H u =>
          intro hv
          have hu : (u : G) ∈ h.twSub (γ : G) := h.mem_twSub.2 ⟨u.2, (hfix γ u).1 hv⟩
          rw [hZ] at hu
          rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
          simpa using hu
      · left
        intro v
        induction v using QuotientGroup.induction_on with
        | H u =>
          exact (hfix γ u).2 (by
            have hu : (u : G) ∈ h.twSub (γ : G) := by rw [hU]; exact u.2
            exact (h.mem_twSub.1 hu).2))
  intro l hl u hu
  exact (hfix ⟨l, hl⟩ ⟨u, hu⟩).1 (hall ⟨l, hl⟩ _)

end ModData

end CFSG.Quasithin.H23P4
