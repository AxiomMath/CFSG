module

public import CFSG.Milestones.ASVolI.C31.J4NP.PartI
public import CFSG.Milestones.ASVolI.C31.J4NP.HClDefs

public section

namespace CFSG.ASVolI

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2
open CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.J4M4
open CFSG.Quasithin.J4Loc (omegaZ)

variable {R : Subgroup J}

theorem burnsideJ4NP_CZ_max
    (hR : burnsideJ4NP_Hyp R)
    {Q : Subgroup J} (hQ : Q ≤ Subgroup.centralizer (omegaZ R : Set J)) (hQ2 : IsPGroup 2 ↥Q) :
    Nat.card ↥Q ≤ Nat.card ↥(P0 ⊓ Subgroup.centralizer (omegaZ R : Set J)) := by
  have hF := j4Facts
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := Subgroup.normalizer (R : Set J) with hL
  set CZ := Subgroup.centralizer (omegaZ R : Set J) with hCZ
  have hCZL : CZ ≤ L := by
    rw [hL, ← burnsideJ4NP_normalizer_Z hR]
    exact Subgroup.centralizer_le_normalizer _
  have hLCZ : L ≤ Subgroup.normalizer (CZ : Set J) := by
    rw [hL, ← burnsideJ4NP_normalizer_Z hR]
    exact burnsideJ4NP_normalizer_le_normalizer_centralizer _
  set T := P0 ⊓ L with hT
  have hTL : T ≤ L := inf_le_right
  have hT2 : IsPGroup 2 ↥T := (CFSG.Quasithin.J4Loc.isPGroup_P0 hF).to_le inf_le_left
  have hT2' : IsPGroup 2 ↥(T.subgroupOf L) := hT2.comap_subtype
  have hcardT : Nat.card ↥(T.subgroupOf L) = Nat.card ↥T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTL).toEquiv
  obtain ⟨S, hTS⟩ := hT2'.exists_le_sylow
  have hSle : Nat.card ↥(S : Subgroup ↥L) ≤ Nat.card ↥T := by
    have h1 := hR.syl ((S : Subgroup ↥L).map L.subtype) (S.isPGroup'.map _)
      (Subgroup.map_subtype_le _)
    rw [Subgroup.card_map_of_injective L.subtype_injective] at h1
    exact h1
  have hTeq : T.subgroupOf L = (S : Subgroup ↥L) := by
    refine Subgroup.eq_of_le_of_card_ge hTS ?_
    rw [hcardT]
    exact hSle
  have hQL : Q ≤ L := hQ.trans hCZL
  have hQ2' : IsPGroup 2 ↥(Q.subgroupOf L) := hQ2.comap_subtype
  obtain ⟨S', hQS'⟩ := hQ2'.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥L S S'
  have hQconj : Q ≤ (P0 ⊓ CZ).map (MulAut.conj (g : J)).toMonoidHom := by
    intro q hq
    have hq' : (⟨q, hQL hq⟩ : ↥L) ∈ (S' : Subgroup ↥L) := hQS' (Subgroup.mem_subgroupOf.mpr hq)
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hq'
    obtain ⟨t, ht, hte⟩ := hq'
    rw [← hTeq] at ht
    replace ht : (t : J) ∈ T := Subgroup.mem_subgroupOf.mp ht
    have hte' : (g : J) * (t : J) * (g : J)⁻¹ = q := by
      have := congrArg Subtype.val hte
      simpa [MulAut.conj_apply] using this
    refine ⟨(t : J), ⟨(Subgroup.mem_inf.mp ht).1, ?_⟩, ?_⟩
    · have hqC : q ∈ CZ := hQ hq
      have hgC : (g : J)⁻¹ ∈ Subgroup.normalizer (CZ : Set J) :=
        Subgroup.inv_mem _ (hLCZ g.2)
      have := (Subgroup.mem_normalizer_iff.mp hgC q).mp hqC
      rw [← hte'] at this
      simpa [mul_assoc] using this
    · simpa [MulAut.conj_apply] using hte'
  have h1 := Subgroup.card_le_of_le hQconj
  rwa [burnsideJ4KW_card_map_conj] at h1

theorem burnsideJ4NP_Z_Hclosed
    (hR : burnsideJ4NP_Hyp R) :
    omegaZ (P0 ⊓ Subgroup.centralizer (omegaZ R : Set J)) = omegaZ R ∧
      P0 ⊓ Subgroup.centralizer (omegaZ R : Set J) ≤
        Hj ⊓ Subgroup.centralizer (omegaZ R : Set J) ∧
      ∀ Q : Subgroup J, Q ≤ Hj ⊓ Subgroup.centralizer (omegaZ R : Set J) → IsPGroup 2 ↥Q →
        P0 ⊓ Subgroup.centralizer (omegaZ R : Set J) ≤ Q →
          Q = P0 ⊓ Subgroup.centralizer (omegaZ R : Set J) := by
  refine ⟨burnsideJ4NP_Z_closed hR, inf_le_inf_right _ P0_le_Hj, fun Q hQ hQ2 hPQ => ?_⟩
  exact (Subgroup.eq_of_le_of_card_ge hPQ
    (burnsideJ4NP_CZ_max hR (hQ.trans inf_le_right) hQ2)).symm

theorem burnsideJ4NP_exists_max {G : Type*} [Group G] [Finite G] {K P : Subgroup G}
    (hPK : P ≤ K) (hP2 : IsPGroup 2 ↥P) :
    ∃ M : Subgroup G, P ≤ M ∧ M ≤ K ∧ IsPGroup 2 ↥M ∧
      ∀ Q : Subgroup G, Q ≤ K → IsPGroup 2 ↥Q → M ≤ Q → Q = M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hPS⟩ := (hP2.comap_subtype (K := K)).exists_le_sylow
  refine ⟨(S : Subgroup ↥K).map K.subtype, fun x hx => ⟨⟨x, hPK hx⟩, hPS
    (Subgroup.mem_comap.mpr hx), rfl⟩, Subgroup.map_subtype_le _,
    S.isPGroup'.map _, fun Q hQK hQ2 hMQ => ?_⟩
  have hQ2' : IsPGroup 2 ↥(Q.subgroupOf K) := hQ2.comap_subtype
  have hSQ : (S : Subgroup ↥K) ≤ Q.subgroupOf K := by
    intro s hs
    rw [Subgroup.mem_subgroupOf]
    exact hMQ ⟨s, hs, rfl⟩
  have heq := S.is_maximal' hQ2' hSQ
  apply le_antisymm _ hMQ
  intro q hq
  have hq' : (⟨q, hQK hq⟩ : ↥K) ∈ Q.subgroupOf K := by
    rw [Subgroup.mem_subgroupOf]
    exact hq
  rw [heq] at hq'
  exact ⟨_, hq', rfl⟩

theorem burnsideJ4NP_W_eq_closure {R A : Subgroup J} (hAZ : A ≤ omegaZ R)
    (hWA : burnsideJ4NP_W R ≤ A) :
    burnsideJ4NP_W R = Subgroup.closure {x | x ∈ A ∧ burnsideJ4NP_Is2A x} := by
  apply le_antisymm
  · rw [burnsideJ4NP_W, Subgroup.closure_le]
    rintro x ⟨hxZ, g, rfl⟩
    exact Subgroup.subset_closure ⟨hWA (Subgroup.subset_closure ⟨hxZ, g, rfl⟩), g, rfl⟩
  · rw [Subgroup.closure_le]
    rintro x ⟨hxA, g, rfl⟩
    exact Subgroup.subset_closure ⟨hAZ hxA, g, rfl⟩

theorem burnsideJ4NP_normalizer_W_no_sylow
    (hR : burnsideJ4NP_Hyp R) (g : J) :
    ¬ P0.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (burnsideJ4NP_W R : Set J) := by
  rw [burnsideJ4NP_normalizer_W hR]
  exact hR.np g

end CFSG.ASVolI
