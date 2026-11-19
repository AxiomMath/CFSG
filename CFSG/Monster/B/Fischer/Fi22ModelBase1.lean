
module

public import CFSG.Monster.B.Fischer.Fi22ModelBase

public import CFSG.Monster.B.Fischer.Fi22ModelCheck
public import CFSG.Monster.B.Fischer.Fi22Graph
public import CFSG.Monster.B.Fischer.Fi22GraphBoundBase
public import CFSG.Monster.B.Fischer.Fi22Local

@[expose] public noncomputable section

namespace CFSG.Monster.B.Fischer

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native

theorem fi22U_ne_one :
    fi22U ≠ 1 := fun h => by
  have := fi22Model_check.1
  rw [← Bool.not_eq_true, eqA_iff rep_fi22U rep_idA] at this
  exact this h

theorem fi22U_mul_self :
    fi22U * fi22U = 1 :=
  eq_of_eqA (rep_compA rep_fi22U rep_fi22U) rep_idA fi22Model_check.2.1

theorem fi22U_inv :
    fi22U⁻¹ = fi22U := inv_eq_of_mul_eq_one_left fi22U_mul_self

theorem orderOf_fi22U :
    orderOf fi22U = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact fi22U_mul_self) fi22U_ne_one

theorem fi22U_not_mem :
    fi22U ∉ fi22P := fun h => by
  have h1 := (siftA_iff_mem_originalSubgroup fi22ChainArrays (by norm_num) fi22Order_check.1
    rep_fi22U).2 h
  rw [fi22Model_check.2.2.1] at h1
  exact Bool.false_ne_true h1

theorem fi22U_conj_gen
    {k : ℕ} (hk : k < 2) : fi22U * fi22GenPerm k * fi22U⁻¹ ∈ fi22P := by
  rw [fi22U_inv]
  have hrep := rep_compA rep_fi22U (rep_compA (rep_fi22OrigArrs_nat k
    (by rw [fi22OrigArrs_size]; exact hk)) rep_fi22U)
  rw [← mul_assoc] at hrep
  exact mem_fi22P_of_siftA hrep (fi22Model_check.2.2.2.1 k hk)

theorem fi22U_conj_mem
    {g : Equiv.Perm (Fin 3510)} (hg : g ∈ fi22P) :
    fi22U * g * fi22U⁻¹ ∈ fi22P := by
  rw [fi22P_eq] at hg
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨k, rfl⟩ := hg
    exact fi22U_conj_gen k.2
  | one => rw [mul_one, mul_inv_cancel]; exact fi22P.one_mem
  | mul g h _ _ hg hh =>
    have e : fi22U * (g * h) * fi22U⁻¹ = (fi22U * g * fi22U⁻¹) * (fi22U * h * fi22U⁻¹) := by
      group
    rw [e]
    exact fi22P.mul_mem hg hh
  | inv g _ hg =>
    have e : fi22U * g⁻¹ * fi22U⁻¹ = (fi22U * g * fi22U⁻¹)⁻¹ := by group
    rw [e]
    exact fi22P.inv_mem hg

theorem fi22U_mem_normalizer :
    fi22U ∈ Subgroup.normalizer (fi22P : Set (Equiv.Perm (Fin 3510))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => fi22U_conj_mem hh, fun hh => ?_⟩
  have := fi22U_conj_mem hh
  rwa [fi22U_inv, show fi22U * (fi22U * h * fi22U) * fi22U = (fi22U * fi22U) * h * (fi22U * fi22U)
    by group, fi22U_mul_self, one_mul, mul_one] at this

theorem fi22U_conj_eq :
    fi22P.map (MulAut.conj fi22U).toMonoidHom = fi22P := by
  ext g
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact fi22U_conj_mem hh
  · intro hg
    refine ⟨fi22U * g * fi22U⁻¹, fi22U_conj_mem hg, ?_⟩
    change fi22U * (fi22U * g * fi22U⁻¹) * fi22U⁻¹ = g
    rw [fi22U_inv, show fi22U * (fi22U * g * fi22U) * fi22U = (fi22U * fi22U) * g * (fi22U * fi22U)
      by group, fi22U_mul_self, one_mul, mul_one]

theorem fi22M_fix_only_zero
    {p : Fin 3510} (hp : ∀ g ∈ fi22OuterM, g p = p) : p = 0 := by
  by_contra h0
  obtain ⟨k, hk, hmove⟩ := fi22Model_check.2.2.2.2 p p.2 (fun h => h0 (Fin.ext h))
  apply hmove
  have hrep := rep_fi22OuterMStrong (k := k) (by omega)
  have hmem : permOfArr 3510 (fi22OuterStrong3510 3)[k]! ∈ fi22OuterM := by
    rw [fi22OuterM, RawSchreierDatum.originalSubgroup]
    apply Subgroup.subset_closure
    rw [Set.mem_ofPred_eq, fi22OuterChainM, RawSchreierDatum.mem_ofArrays_original]
    exact ⟨k, hk, rfl⟩
  rw [hrep p, hp _ hmem]

theorem fi22P_centralizer :
    Subgroup.centralizer (fi22P : Set (Equiv.Perm (Fin 3510))) = ⊥ := by
  rw [eq_bot_iff]
  intro c hc
  rw [Subgroup.mem_bot]
  have hcomm : ∀ g ∈ fi22P, c * g = g * c := fun g hg =>
    (Subgroup.mem_centralizer_iff.1 hc g hg).symm
  have h0 : c 0 = 0 := by
    apply fi22M_fix_only_zero
    intro g hg
    have hg' := fi22OuterM_eq ▸ hg
    have hgP : g ∈ fi22P := hg'.1
    have hg0 : g 0 = 0 := MulAction.mem_stabilizer_iff.1 hg'.2
    have := congrArg (fun σ : Equiv.Perm (Fin 3510) => σ 0) (hcomm g hgP)
    simp only [Equiv.Perm.mul_apply, hg0] at this
    exact this.symm
  refine Equiv.ext fun x => ?_
  obtain ⟨g, hg, rfl⟩ := fi22P_exists_smul 0 x
  have := congrArg (fun σ : Equiv.Perm (Fin 3510) => σ 0) (hcomm g hg)
  simp only [Equiv.Perm.mul_apply, h0] at this
  exact this

theorem fi22R_le_normalizer :
    fi22R ≤ Subgroup.normalizer (fi22P : Set (Equiv.Perm (Fin 3510))) := by
  rw [fi22R, Subgroup.closure_le]
  rintro g (rfl | hg)
  · exact fi22U_mem_normalizer
  · exact Subgroup.le_normalizer hg

theorem mem_fi22R_iff
    (g : Equiv.Perm (Fin 3510)) : g ∈ fi22R ↔ g ∈ fi22P ∨ fi22U * g ∈ fi22P := by
  constructor
  · intro hg
    let S : Subgroup (Equiv.Perm (Fin 3510)) :=
      { carrier := {g | g ∈ fi22P ∨ fi22U * g ∈ fi22P}
        mul_mem' := by
          rintro a b (ha | ha) (hb | hb)
          · exact Or.inl (fi22P.mul_mem ha hb)
          · right
            have e : fi22U * (a * b) = (fi22U * a * fi22U⁻¹) * (fi22U * b) := by group
            rw [e]
            exact fi22P.mul_mem (fi22U_conj_mem ha) hb
          · right
            rw [← mul_assoc]
            exact fi22P.mul_mem ha hb
          · left
            have e : a * b = fi22U * (fi22U * a) * fi22U⁻¹ * (fi22U * b) := by
              rw [fi22U_inv, show fi22U * (fi22U * a) * fi22U * (fi22U * b) =
                (fi22U * fi22U) * a * (fi22U * fi22U) * b by group, fi22U_mul_self, one_mul,
                mul_one]
            rw [e]
            exact fi22P.mul_mem (fi22U_conj_mem ha) hb
        one_mem' := Or.inl fi22P.one_mem
        inv_mem' := by
          rintro a (ha | ha)
          · exact Or.inl (fi22P.inv_mem ha)
          · right
            have e : fi22U * a⁻¹ = fi22U * (fi22U * a)⁻¹ * fi22U⁻¹ := by
              rw [fi22U_inv]
              group
            rw [e]
            exact fi22U_conj_mem (fi22P.inv_mem ha) }
    have hle : fi22R ≤ S := by
      rw [fi22R, Subgroup.closure_le]
      rintro x (rfl | hx)
      · right
        show fi22U * fi22U ∈ fi22P
        rw [fi22U_mul_self]
        exact fi22P.one_mem
      · exact Or.inl hx
    exact hle hg
  · rintro (hg | hg)
    · exact fi22P_le_R hg
    · have : g = fi22U⁻¹ * (fi22U * g) := by group
      rw [this]
      exact fi22R.mul_mem (fi22R.inv_mem fi22U_mem_R) (fi22P_le_R hg)

theorem card_fi22R :
    Nat.card fi22R = 129123503308800 := by
  have hsplit : (fi22R : Set (Equiv.Perm (Fin 3510))) =
      (fi22P : Set (Equiv.Perm (Fin 3510))) ∪ (fun g => fi22U * g) '' (fi22P : Set _) := by
    ext g
    rw [SetLike.mem_coe, mem_fi22R_iff, Set.mem_union, Set.mem_image]
    constructor
    · rintro (hg | hg)
      · exact Or.inl hg
      · refine Or.inr ⟨fi22U * g, hg, ?_⟩
        rw [← mul_assoc, fi22U_mul_self, one_mul]
    · rintro (hg | ⟨h, hh, rfl⟩)
      · exact Or.inl hg
      · right
        rw [← mul_assoc, fi22U_mul_self, one_mul]
        exact hh
  have hdisj : Disjoint (fi22P : Set (Equiv.Perm (Fin 3510)))
      ((fun g => fi22U * g) '' (fi22P : Set _)) := by
    rw [Set.disjoint_left]
    rintro g hg ⟨h, hh, rfl⟩
    apply fi22U_not_mem
    have := fi22P.mul_mem hg (fi22P.inv_mem hh)
    rwa [mul_inv_cancel_right] at this
  rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq, hsplit, Set.ncard_union_eq hdisj,
    Set.ncard_image_of_injective _ (mul_right_injective fi22U), ← Nat.card_coe_set_eq,
    SetLike.coe_sort_coe, card_fi22P]

theorem fi22R_semidirect :
    (fi22P.subgroupOf fi22R).Normal ∧ fi22P ⊓ Subgroup.zpowers fi22U = ⊥ ∧
      fi22P ⊔ Subgroup.zpowers fi22U = fi22R := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun n hn r => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.1 (fi22R_le_normalizer r.2)
      (n : Equiv.Perm (Fin 3510))).1 hn
  · rw [eq_bot_iff]
    rintro g ⟨hgP, hgu⟩
    rw [Subgroup.mem_bot]
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hgu
    have hk : fi22U ^ k = fi22U ^ (k % 2) := by
      rw [← zpow_mod_orderOf, orderOf_fi22U]
      rfl
    rw [hk] at hgP ⊢
    have h2 : k % 2 = 0 ∨ k % 2 = 1 := by omega
    rcases h2 with h | h
    · rw [h, zpow_zero]
    · rw [h, zpow_one] at hgP
      exact absurd hgP fi22U_not_mem
  · apply le_antisymm
    · exact sup_le fi22P_le_R ((Subgroup.zpowers_le).2 fi22U_mem_R)
    · rw [fi22R, Subgroup.closure_le]
      rintro g (rfl | hg)
      · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      · exact Subgroup.mem_sup_left hg

def fi22ConjHom :
    fi22R →* MulAut fi22P :=
  (Subgroup.normalizerMonoidHom fi22P).comp (Subgroup.inclusion fi22R_le_normalizer)

theorem fi22ConjHom_apply
    (r : fi22R) (g : fi22P) :
    ((fi22ConjHom r g : fi22P) : Equiv.Perm (Fin 3510)) =
      (r : Equiv.Perm (Fin 3510)) * g * (r : Equiv.Perm (Fin 3510))⁻¹ := rfl

theorem fi22ConjHom_injective :
    Function.Injective fi22ConjHom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro r hr
  rw [MonoidHom.mem_ker] at hr
  rw [Subgroup.mem_bot]
  have hc : (r : Equiv.Perm (Fin 3510)) ∈ Subgroup.centralizer (fi22P : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := congrArg (fun α : MulAut fi22P => ((α ⟨g, hg⟩ : fi22P) : Equiv.Perm (Fin 3510))) hr
    rw [fi22ConjHom_apply] at this
    rw [eq_comm, ← mul_inv_eq_iff_eq_mul]
    exact this
  rw [fi22P_centralizer, Subgroup.mem_bot] at hc
  exact Subtype.ext hc

theorem fi22P_conj_injective :
    Function.Injective (MulAut.conj : fi22P →* MulAut fi22P) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker] at hg
  rw [Subgroup.mem_bot]
  have hc : (g : Equiv.Perm (Fin 3510)) ∈ Subgroup.centralizer (fi22P : Set _) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have := congrArg (fun α : MulAut fi22P => ((α ⟨h, hh⟩ : fi22P) : Equiv.Perm (Fin 3510))) hg
    simp only [MulAut.conj_apply, MulAut.one_apply, Subgroup.coe_mul, Subgroup.coe_inv] at this
    rw [eq_comm, ← mul_inv_eq_iff_eq_mul]
    exact this
  rw [fi22P_centralizer, Subgroup.mem_bot] at hc
  exact Subtype.ext hc

end CFSG.Monster.B.Fischer
