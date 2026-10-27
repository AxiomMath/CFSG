module

public import CFSG.Quasithin.Vol2.Ch12Sec2GlueIrr
public import CFSG.Quasithin.Vol2.Ch10StatementsA

public section

namespace CFSG.Quasithin.Vol2.Ch10

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13

namespace CW

variable {G : Type} [Group G]

theorem conjClosure_sup_eq_sup (L T : Subgroup G) : conjClosure L T ⊔ T = L ⊔ T := by
  apply le_antisymm
  · refine sup_le (conjClosure_le fun t ht l hl => ?_) le_sup_right
    exact (L ⊔ T).mul_mem ((L ⊔ T).mul_mem (Subgroup.mem_sup_right ht)
      (Subgroup.mem_sup_left hl)) ((L ⊔ T).inv_mem (Subgroup.mem_sup_right ht))
  · exact sup_le ((le_conjClosure L T).trans le_sup_left) le_sup_right

theorem noTwoQuotient_conjClosure {L T : Subgroup G}
    (hL : ∀ N : Subgroup G, N ≤ L → (N.subgroupOf L).Normal →
      (∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ N) → N = L) :
    ∀ N : Subgroup G, N ≤ conjClosure L T → (N.subgroupOf (conjClosure L T)).Normal →
      (∀ x ∈ conjClosure L T, ∃ k : ℕ, x ^ 2 ^ k ∈ N) → N = conjClosure L T := by
  intro N hN hNn h2
  refine le_antisymm hN (conjClosure_le fun t ht l hl => ?_)
  let K : Subgroup G := L ⊓ N.comap (MulAut.conj t).toMonoidHom
  have hmem : ∀ x : G, x ∈ K ↔ x ∈ L ∧ t * x * t⁻¹ ∈ N := fun x => by
    simp [K, Subgroup.mem_inf, Subgroup.mem_comap, MulAut.conj_apply]
  have hK : K = L := by
    refine hL K inf_le_left ⟨fun k hk g => ?_⟩ fun x hx => ?_
    · rw [Subgroup.mem_subgroupOf, hmem] at hk ⊢
      obtain ⟨hkL, hkN⟩ := hk
      refine ⟨L.mul_mem (L.mul_mem g.2 hkL) (L.inv_mem g.2), ?_⟩
      have hg : t * (g : G) * t⁻¹ ∈ conjClosure L T := mem_conjClosure ht g.2
      have h := hNn.conj_mem ⟨_, hN hkN⟩ (by rw [Subgroup.mem_subgroupOf]; exact hkN) ⟨_, hg⟩
      rw [Subgroup.mem_subgroupOf] at h
      have heq : t * ((g : G) * (k : G) * (g : G)⁻¹) * t⁻¹ =
          t * (g : G) * t⁻¹ * (t * (k : G) * t⁻¹) * (t * (g : G) * t⁻¹)⁻¹ := by group
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, heq]
      exact h
    · obtain ⟨k, hk⟩ := h2 _ (mem_conjClosure ht hx)
      refine ⟨k, (hmem _).mpr ⟨L.pow_mem hx _, ?_⟩⟩
      rwa [← conj_pow]
  exact ((hmem l).mp (hK ▸ hl)).2

end CW

theorem stmtIrrPlusNonempty_of_a36 (h36 : A36ForSQTK) : StmtIrrPlusNonempty := by
  intro G _ _ T L hs hnab hQ hT _ hf _
  obtain ⟨S, hS⟩ := CFSG.Quasithin.exists_sylow_of_quasithinIsSylowTwo hT
  have hInH : InH (S : Subgroup G) (L ⊔ T) := ⟨hS ▸ le_sup_right, hf.1.2.2.2⟩
  have hcc : L ∈ cComp (L ⊔ T) := hf.1.2.1
  have hf' : quasithinIsFaithfulLocal (S : Subgroup G) L := by rw [hS]; exact hf
  have hRL := ((lemma_1_2_10_of_a36 hQ hs hnab h36 S hInH hcc).out 1 3).mp hf'
  obtain ⟨-, hLR, ⟨-, hR2⟩, -⟩ := A4.isTwoReducedIn_twoReducedJoin (L ⊔ T)
  have hsup := CW.conjClosure_sup_eq_sup L T
  have hL0R : conjClosure L T ≤ Subgroup.normalizer (twoReducedJoin (L ⊔ T) : Set G) :=
    (le_sup_left.trans hsup.le).trans hLR
  have hne : ⁅twoReducedJoin (L ⊔ T), conjClosure L T⁆ ≠ ⊥ := fun h => hRL (eq_bot_iff.mpr
    (h ▸ Subgroup.commutator_mono le_rfl (le_conjClosure L T)))
  obtain ⟨I, hI⟩ := exists_irrPlusBase (CW.noTwoQuotient_conjClosure hf.2.1)
    (fun x hx => by rw [← pow_two]; exact hR2 x hx) hL0R hne
  refine ⟨I, ?_⟩
  rw [hsup, show reducedAggregate (L ⊔ T) = twoReducedJoin (L ⊔ T) from
    primeReducedAggregate_map_subtype_eq_twoReducedJoin (L ⊔ T)]
  exact hI

theorem stmtFSUChoice_of_a36 (h323 : Stmt3_2_3) (h36 : A36ForSQTK) : StmtFSUChoice :=
  stmtFSUChoice_of h323 (stmtIrrPlusNonempty_of_a36 h36)

end CFSG.Quasithin.Vol2.Ch10
