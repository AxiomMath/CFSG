module

public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverTransferComparison

public section

namespace CFSG.RankThree.PartTwo.J2Residue.H2

open CFSG.ComponentClassification.CentralCover

variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

theorem neg_eq_self_zmod2 (v : V) : -v = v := by
  rw [neg_eq_iff_add_eq_zero, ← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 from rfl, zero_smul]

@[expose] def IsNormCoc (ρ : G →* Module.End (ZMod 2) V) (c : G → G → V) : Prop :=
  (∀ h, c 1 h = 0) ∧ (∀ g, c g 1 = 0) ∧
    ∀ g h k, ρ g (c h k) - c (g * h) k + c g (h * k) - c g h = 0

@[expose] def cob (ρ : G →* Module.End (ZMod 2) V) (b : G → V) (g h : G) : V :=
  ρ g (b h) - b (g * h) + b g

theorem isNormCoc_cob (ρ : G →* Module.End (ZMod 2) V) {b : G → V} (hb : b 1 = 0) :
    IsNormCoc ρ (cob ρ b) := by
  refine ⟨fun h => ?_, fun g => ?_, fun g h k => ?_⟩
  · simp only [cob, map_one, Module.End.one_apply, one_mul, hb, add_zero, sub_self]
  · simp only [cob, hb, map_zero, mul_one, zero_sub, neg_add_cancel]
  · simp only [cob, map_add, map_sub, map_mul, Module.End.mul_apply, mul_assoc]
    abel

theorem isNormCoc_zero (ρ : G →* Module.End (ZMod 2) V) : IsNormCoc ρ (0 : G → G → V) :=
  ⟨fun _ => rfl, fun _ => rfl, fun _ _ _ => by simp⟩

theorem IsNormCoc.add {ρ : G →* Module.End (ZMod 2) V} {c c' : G → G → V} (hc : IsNormCoc ρ c)
    (hc' : IsNormCoc ρ c') : IsNormCoc ρ (c + c') := by
  refine ⟨fun h => ?_, fun g => ?_, fun g h k => ?_⟩
  · simp [hc.1 h, hc'.1 h]
  · simp [hc.2.1 g, hc'.2.1 g]
  · have e : ρ g ((c + c') h k) - (c + c') (g * h) k + (c + c') g (h * k) - (c + c') g h =
        (ρ g (c h k) - c (g * h) k + c g (h * k) - c g h) +
          (ρ g (c' h k) - c' (g * h) k + c' g (h * k) - c' g h) := by
      simp only [Pi.add_apply, map_add]
      abel
    rw [e, hc.2.2, hc'.2.2, add_zero]

theorem IsNormCoc.smul {ρ : G →* Module.End (ZMod 2) V} {c : G → G → V} (hc : IsNormCoc ρ c)
    (a : ZMod 2) : IsNormCoc ρ (a • c) := by
  refine ⟨fun h => ?_, fun g => ?_, fun g h k => ?_⟩
  · simp [hc.1 h]
  · simp [hc.2.1 g]
  · simp only [Pi.smul_apply, map_smul]
    rw [← smul_sub, ← smul_add, ← smul_sub, hc.2.2 g h k, smul_zero]

theorem IsNormCoc.sum {ρ : G →* Module.End (ZMod 2) V} {ι : Type*} (s : Finset ι)
    {c : ι → G → G → V} (hc : ∀ i ∈ s, IsNormCoc ρ (c i)) : IsNormCoc ρ (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isNormCoc_zero ρ
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (hc a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hc i (Finset.mem_insert_of_mem hi))

theorem cob_add (ρ : G →* Module.End (ZMod 2) V) (b b' : G → V) :
    cob ρ (b + b') = cob ρ b + cob ρ b' := by
  funext g h
  simp only [cob, Pi.add_apply, map_add]
  abel

theorem cob_smul (ρ : G →* Module.End (ZMod 2) V) (a : ZMod 2) (b : G → V) :
    cob ρ (a • b) = a • cob ρ b := by
  funext g h
  simp only [cob, Pi.smul_apply, map_smul, smul_add, smul_sub]

theorem cob_neg (ρ : G →* Module.End (ZMod 2) V) (b : G → V) : cob ρ (-b) = -cob ρ b := by
  funext g h
  simp only [cob, Pi.neg_apply, map_neg]
  abel

theorem IsNormCoc.comp {H : Type*} [Group H] {ρ : G →* Module.End (ZMod 2) V} {c : G → G → V}
    (hc : IsNormCoc ρ c) (φ : H →* G) : IsNormCoc (ρ.comp φ) (fun a b => c (φ a) (φ b)) := by
  refine ⟨fun h => ?_, fun g => ?_, fun g h k => ?_⟩
  · simp only [map_one, hc.1]
  · simp only [map_one, hc.2.1]
  · simp only [MonoidHom.comp_apply, map_mul]
    exact hc.2.2 _ _ _

section Transfer

variable {S : Subgroup G} {I : Type*} [Fintype I] {r : I → G} (hr : IsRightTransversal S r)
include hr

@[expose] noncomputable def tr₂ (ρ : G →* Module.End (ZMod 2) V) (f : S → S → V) (g k : G) : V :=
  ∑ i, ρ (r i)⁻¹ (f (hr.coef i g) (hr.coef (hr.act i g) k))

@[expose] noncomputable def tr₁ (ρ : G →* Module.End (ZMod 2) V) (b : S → V) (g : G) : V :=
  ∑ i, ρ (r i)⁻¹ (b (hr.coef i g))

theorem rho_inv_mul_coef (ρ : G →* Module.End (ZMod 2) V) (i : I) (g : G) (v : V) :
    ρ (r i)⁻¹ (ρ (hr.coef i g) v) = ρ g (ρ (r (hr.act i g))⁻¹ v) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hr.coe_coef]
  congr 2
  group

theorem tr₂_cob (ρ : G →* Module.End (ZMod 2) V) (b : S → V) :
    tr₂ hr ρ (cob (ρ.comp S.subtype) b) = cob ρ (tr₁ hr ρ b) := by
  funext g k
  simp only [tr₂, tr₁, cob, MonoidHom.comp_apply, Subgroup.coe_subtype, map_add, map_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib, map_sum]
  rw [← hr.sum_act (fun i => ρ g (ρ (r i)⁻¹ (b (hr.coef i k)))) g]
  simp only [rho_inv_mul_coef, ← hr.coef_mul]

@[expose] noncomputable def compCochain (ρ : G →* Module.End (ZMod 2) V) (c : G → G → V)
    (g : G) : V :=
  ∑ i, ρ (r i)⁻¹ (c (r i) g - c (hr.coef i g) (r (hr.act i g)))

theorem coset_identity (ρ : G →* Module.End (ZMod 2) V) {c : G → G → V} (hc : IsNormCoc ρ c)
    (i : I) (g k : G) :
    (c (r i) g - c (hr.coef i g) (r (hr.act i g))) +
      ρ (hr.coef i g) (c (r (hr.act i g)) k -
        c (hr.coef (hr.act i g) k) (r (hr.act (hr.act i g) k))) +
      c (hr.coef i g) (hr.coef (hr.act i g) k) =
      ρ (r i) (c g k) + (c (r i) (g * k) - c (hr.coef i (g * k)) (r (hr.act i (g * k)))) := by
  have hpq : (hr.coef i (g * k) : G) = hr.coef i g * hr.coef (hr.act i g) k := by
    rw [hr.coef_mul, Subgroup.coe_mul]
  have hact : hr.act i (g * k) = hr.act (hr.act i g) k := hr.act_mul i g k
  have hag : r i * g = hr.coef i g * r (hr.act i g) := hr.r_mul i g
  have hbk : r (hr.act i g) * k = hr.coef (hr.act i g) k * r (hr.act (hr.act i g) k) :=
    hr.r_mul (hr.act i g) k
  have e1 := hc.2.2 (r i) g k
  have e2 := hc.2.2 (hr.coef i g) (r (hr.act i g)) k
  have e3 := hc.2.2 (hr.coef i g) (hr.coef (hr.act i g) k) (r (hr.act (hr.act i g) k))
  rw [hag] at e1
  rw [hbk] at e2
  rw [hpq, hact, map_sub]
  rw [← sub_eq_zero]
  have h : (c (r i) g - c (hr.coef i g) (r (hr.act i g)) +
      (ρ (hr.coef i g) (c (r (hr.act i g)) k) -
        ρ (hr.coef i g) (c (hr.coef (hr.act i g) k) (r (hr.act (hr.act i g) k)))) +
      c (hr.coef i g) (hr.coef (hr.act i g) k)) -
      (ρ (r i) (c g k) + (c (r i) (g * k) - c ((hr.coef i g : G) * hr.coef (hr.act i g) k)
        (r (hr.act (hr.act i g) k)))) =
      -(ρ (r i) (c g k) - c (hr.coef i g * r (hr.act i g)) k + c (r i) (g * k) - c (r i) g) +
      (ρ (hr.coef i g) (c (r (hr.act i g)) k) - c (hr.coef i g * r (hr.act i g)) k +
        c (hr.coef i g) (hr.coef (hr.act i g) k * r (hr.act (hr.act i g) k)) -
        c (hr.coef i g) (r (hr.act i g))) -
      (ρ (hr.coef i g) (c (hr.coef (hr.act i g) k) (r (hr.act (hr.act i g) k))) -
        c (hr.coef i g * hr.coef (hr.act i g) k) (r (hr.act (hr.act i g) k)) +
        c (hr.coef i g) (hr.coef (hr.act i g) k * r (hr.act (hr.act i g) k)) -
        c (hr.coef i g) (hr.coef (hr.act i g) k)) := by
    abel
  rw [h, e1, e2, e3]
  abel

theorem eq_tr₂_add_cob (ρ : G →* Module.End (ZMod 2) V)
    (hodd : ∀ v : V, Fintype.card I • v = v) {c : G → G → V} (hc : IsNormCoc ρ c) (g k : G) :
    c g k = tr₂ hr ρ (fun s t => c s t) g k + cob ρ (compCochain hr ρ c) g k := by
  have hsum := congrArg (fun F : I → V => ∑ i, ρ (r i)⁻¹ (F i))
    (funext (coset_identity hr ρ hc · g k))
  simp only [map_add, Finset.sum_add_distrib] at hsum
  have hmid : ∑ i, ρ (r i)⁻¹ (ρ (hr.coef i g) (c (r (hr.act i g)) k -
      c (hr.coef (hr.act i g) k) (r (hr.act (hr.act i g) k)))) =
      ρ g (compCochain hr ρ c k) := by
    rw [compCochain, map_sum, ← hr.sum_act (fun j => ρ g (ρ (r j)⁻¹ (c (r j) k -
      c (hr.coef j k) (r (hr.act j k))))) g]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [rho_inv_mul_coef]
  have hcard : ∑ i : I, ρ (r i)⁻¹ (ρ (r i) (c g k)) = c g k := by
    simp only [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      Finset.sum_const, Finset.card_univ]
    exact hodd _
  rw [hmid, hcard] at hsum
  change compCochain hr ρ c g + ρ g (compCochain hr ρ c k) + tr₂ hr ρ (fun s t => c s t) g k =
    c g k + compCochain hr ρ c (g * k) at hsum
  rw [cob, show c g k = compCochain hr ρ c g + ρ g (compCochain hr ρ c k) +
    tr₂ hr ρ (fun s t => c s t) g k - compCochain hr ρ c (g * k) by rw [hsum]; abel]
  abel

end Transfer

end CFSG.RankThree.PartTwo.J2Residue.H2
