module

public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsBasic
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorSide

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Dict

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

theorem comm_mem_sub_iff (M₀ : Tim79.QuadModel QF V K γ) {S : Subgroup G} (hVS : V ≤ S) {m x : G}
    (hx : x ∈ QF) (hm : m * x * m⁻¹ ∈ QF) :
    ⁅m, x⁆ ∈ S ↔ M₀.π (m * x * m⁻¹) - M₀.π x ∈ M₀.img S := by
  have h1 : ⁅m, x⁆ = (m * x * m⁻¹) * x⁻¹ := by rw [commutatorElement_def]
  have h2 : ⁅m, x⁆ ∈ QF := by rw [h1]; exact QF.mul_mem hm (QF.inv_mem hx)
  rw [← M₀.mem_img_iff hVS h2, h1, M₀.π_mul _ hm _ (QF.inv_mem hx),
    Tim79.QuadModel.pi_inv M₀ hx, sub_eq_add_neg]

end Dict

section Action

variable {E : Type*} [AddCommGroup E] {Γ : Type*} [Group Γ]

theorem act_symm_apply (ρ : Γ →* Multiplicative (AddAut E)) (g : Γ) (e : E) :
    (ρ g).toAdd.symm e = (ρ g⁻¹).toAdd e := by
  apply (ρ g).toAdd.injective
  rw [AddEquiv.apply_symm_apply, ← act_mul_apply, mul_inv_cancel, map_one]
  rfl

theorem act_commutator_apply (ρ : Γ →* Multiplicative (AddAut E)) (a b : Γ) (e : E) :
    (ρ ⁅a, b⁆).toAdd e =
      (ρ a).toAdd ((ρ b).toAdd ((ρ a).toAdd.symm ((ρ b).toAdd.symm e))) := by
  rw [commutatorElement_def, act_mul_apply, act_mul_apply, act_mul_apply, act_symm_apply,
    act_symm_apply]

end Action

section CommComm

variable {G : Type} [Group G] {M Q Z : Subgroup G}
  [(Q.subgroupOf M).Normal] {K : Type} [Field K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}
  {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}

theorem commutator_comm_mem_Z (hQM : M ≤ Subgroup.normalizer (Q : Set G))
    (hconj : ∀ (t : ↥M) (x : G), x ∈ Q →
      M₀.π ((t : G) * x * (t : G)⁻¹) = (ρ (QuotientGroup.mk t)).toAdd (M₀.π x))
    {V W : Subgroup G} (hZV : Z ≤ V) (hVW : V ≤ W) (hWQ : W ≤ Q) {a b : G} (ha : a ∈ M)
    (hb : b ∈ M) (haW : ∀ w ∈ W, a * w * a⁻¹ ∈ W) (haW' : ∀ w ∈ W, a⁻¹ * w * a ∈ W)
    (hbW : ∀ w ∈ W, b * w * b⁻¹ ∈ W) (hbW' : ∀ w ∈ W, b⁻¹ * w * b ∈ W)
    (haV : ∀ v ∈ V, ⁅a, v⁆ ∈ Z) (hbV : ∀ v ∈ V, ⁅b, v⁆ ∈ Z)
    (haWV : ∀ w ∈ W, ⁅a, w⁆ ∈ V) (hbWV : ∀ w ∈ W, ⁅b, w⁆ ∈ V) :
    ∀ w ∈ W, ⁅⁅a, b⁆, w⁆ ∈ Z := by
  intro w hw
  have hwQ : w ∈ Q := hWQ hw
  have hQc : ∀ m ∈ M, ∀ y ∈ Q, m * y * m⁻¹ ∈ Q := fun m hm y hy =>
    (Subgroup.mem_normalizer_iff.mp (hQM hm) y).mp hy
  set A : M₀.E ≃+ M₀.E := (ρ (QuotientGroup.mk (⟨a, ha⟩ : ↥M))).toAdd with hA
  set B : M₀.E ≃+ M₀.E := (ρ (QuotientGroup.mk (⟨b, hb⟩ : ↥M))).toAdd with hB
  have hAπ : ∀ x ∈ Q, A (M₀.π x) = M₀.π (a * x * a⁻¹) := fun x hx =>
    (hconj ⟨a, ha⟩ x hx).symm
  have hBπ : ∀ x ∈ Q, B (M₀.π x) = M₀.π (b * x * b⁻¹) := fun x hx =>
    (hconj ⟨b, hb⟩ x hx).symm
  have hsymm : ∀ (g : G) (hg : g ∈ M) (x : G), x ∈ Q →
      (ρ (QuotientGroup.mk (⟨g, hg⟩ : ↥M))).toAdd.symm (M₀.π x) = M₀.π (g⁻¹ * x * g) := by
    intro g hg x hx
    rw [act_symm_apply]
    have e : ((QuotientGroup.mk (⟨g, hg⟩ : ↥M) : Mbar M Q))⁻¹ =
        QuotientGroup.mk (⟨g⁻¹, M.inv_mem hg⟩ : ↥M) := rfl
    rw [e, ← hconj ⟨g⁻¹, M.inv_mem hg⟩ x hx]
    simp
  have hAs : ∀ x ∈ Q, A.symm (M₀.π x) = M₀.π (a⁻¹ * x * a) := hsymm a ha
  have hBs : ∀ x ∈ Q, B.symm (M₀.π x) = M₀.π (b⁻¹ * x * b) := hsymm b hb
  have hVQ : V ≤ Q := hVW.trans hWQ
  have hmemW : ∀ e ∈ M₀.img W, ∃ x ∈ W, M₀.π x = e := fun e ⟨x, hx, _, hxe⟩ => ⟨x, hx, hxe⟩
  have key := commutator_eq_one_on A B (M₀.img V) (M₀.img W)
    (fun e he => by
      obtain ⟨x, hx, rfl⟩ := hmemW e he
      rw [hAπ x (hWQ hx)]
      exact M₀.pi_mem_img (haW x hx) (hQc a ha x (hWQ hx)))
    (fun e he => by
      obtain ⟨x, hx, rfl⟩ := hmemW e he
      rw [hAs x (hWQ hx)]
      have hal : a⁻¹ * x * a ∈ Q := by
        have := hQc a⁻¹ (M.inv_mem ha) x (hWQ hx)
        simpa using this
      exact M₀.pi_mem_img (haW' x hx) hal)
    (fun e he => by
      obtain ⟨x, hx, rfl⟩ := hmemW e he
      rw [hBπ x (hWQ hx)]
      exact M₀.pi_mem_img (hbW x hx) (hQc b hb x (hWQ hx)))
    (fun e he => by
      obtain ⟨x, hx, rfl⟩ := hmemW e he
      rw [hBs x (hWQ hx)]
      have hbl : b⁻¹ * x * b ∈ Q := by
        have := hQc b⁻¹ (M.inv_mem hb) x (hWQ hx)
        simpa using this
      exact M₀.pi_mem_img (hbW' x hx) hbl)
    (fun e he => by
      obtain ⟨x, hx, hxQ, rfl⟩ := he
      rw [hAπ x hxQ]
      exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hxQ (hQc a ha x hxQ)).mp (haV x hx))
    (fun e he => by
      obtain ⟨x, hx, hxQ, rfl⟩ := he
      rw [hBπ x hxQ]
      exact (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hxQ (hQc b hb x hxQ)).mp (hbV x hx))
    (fun e he => by
      obtain ⟨x, hx, rfl⟩ := hmemW e he
      rw [hAπ x (hWQ hx)]
      exact (comm_mem_sub_iff M₀ hZV (hWQ hx) (hQc a ha x (hWQ hx))).mp (haWV x hx))
    (fun e he => by
      obtain ⟨x, hx, rfl⟩ := hmemW e he
      rw [hBπ x (hWQ hx)]
      exact (comm_mem_sub_iff M₀ hZV (hWQ hx) (hQc b hb x (hWQ hx))).mp (hbWV x hx))
    (M₀.π w) (M₀.pi_mem_img hw hwQ)
  have hcM : ⁅a, b⁆ ∈ M := by
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)
  have hmk : (QuotientGroup.mk (⟨⁅a, b⁆, hcM⟩ : ↥M) : Mbar M Q) =
      ⁅(QuotientGroup.mk (⟨a, ha⟩ : ↥M) : Mbar M Q),
        (QuotientGroup.mk (⟨b, hb⟩ : ↥M) : Mbar M Q)⁆ := by
    have e : (⟨⁅a, b⁆, hcM⟩ : ↥M) = ⁅(⟨a, ha⟩ : ↥M), (⟨b, hb⟩ : ↥M)⁆ := Subtype.ext rfl
    rw [e]
    exact map_commutatorElement (QuotientGroup.mk' (Q.subgroupOf M)) _ _
  have hcπ := hconj ⟨⁅a, b⁆, hcM⟩ w hwQ
  rw [hmk, act_commutator_apply] at hcπ
  have hcQ : ⁅a, b⁆ * w * ⁅a, b⁆⁻¹ ∈ Q := hQc _ hcM w hwQ
  refine (Tim79.QuadModel.comm_mem_iff (M₀ := M₀) hwQ hcQ).mpr ?_
  rw [hcπ]
  exact key

end CommComm

end CFSG.RankThree.GF2n.Stroth80
