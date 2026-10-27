module

public import CFSG.Quasithin.EmptyFaithful.S143UF
public import CFSG.Quasithin.EmptyFaithful.R3c19A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Tight
  CFSG.QuasithinUnique.BenderBranch CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

@[expose] def Lemma14322InspectW3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G) (g : G) (A : Subgroup G) (t : G),
    Counter T M g → Concl14318 T M g A t → Concl14319 T M A →
      Subgroup.centralizer (A : Set G) = A → Concl14321 T M →
        ∀ d : G, dOf T M = Subgroup.zpowers d → orderOf d = 4 →
          ∀ x ∈ yOfL22 T M, orderOf x = 3 →
            IsSylowTwoOf (T ⊓ Subgroup.centralizer ({wOfX d x} : Set G))
              (Subgroup.centralizer ({wOfX d x} : Set G)) →
            (∀ y : G, y * (d * d) * y⁻¹ ≠ wOfX d x) →
            (∃ s : G, s * wOfX d x * s⁻¹ = wOfX d x * (d * d)) →
            IsZ4Sq ↥(rOf T M ⊓ Subgroup.centralizer ({wOfX d x} : Set G)) →
            IsZ4StarSL23 ↥(oTwoUpper (mcOf T) ⊓ Subgroup.centralizer ({wOfX d x} : Set G)) →
              ∃ L : Subgroup G, L ≤ Subgroup.centralizer ({wOfX d x} : Set G) ∧
                CFSG.Assembly.LowTwoRank.StatedClassicalModel ↥L .PSU 3 3 1 ∧
                T ⊓ Subgroup.centralizer ({wOfX d x} : Set G) ⊓ (rOf T M ⊔ qOf T) ≤
                  Subgroup.zpowers (wOfX d x) ⊔ L

theorem lemma14322InspectW2_of_inspectW3 (h : Lemma14322InspectW3) : Lemma14322InspectW2 := by
  intro G _ _ T M g A t c c18 c19 hΓ c21 d hD hd4 x hxL hx3 hSyl hN1 hN2 hR hO
  obtain ⟨L, hLC, hmod, hLT⟩ :=
    h G T M g A t c c18 c19 hΓ c21 d hD hd4 x hxL hx3 hSyl hN1 hN2 hR hO
  refine ⟨L, hLC, ?_, R3c19.exists_conj_of_u33_subgroup hmod, hLT⟩
  have hzZ := sq_mem_omegaOneCenter c hD hd4
  have hw2 : wOfX d x * wOfX d x = 1 := wOfX_sq c hD hd4 hxL hx3
  have hzw : (d * d) * wOfX d x = wOfX d x * (d * d) := by
    have hd : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
    have hzX : d * d ∈ Xgen T M := (Xgen T M).mul_mem (le_Wgen (dOf_mem_delta c) hd)
      (le_Wgen (dOf_mem_delta c) hd)
    exact Xgen_comm c hD hd4 _ hzX _ (wOfX_mem_Xgen c hD hxL)
  have hzT : d * d ∈ T := (Subgroup.closure_le _).2 (fun z hz => hz.1.1) hzZ
  have hzC : d * d ∈ Subgroup.centralizer ({wOfX d x} : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact hzw.symm
  have hzQ : d * d ∈ qOf T := by
    have hd : d ∈ dOf T M := hD ▸ Subgroup.mem_zpowers d
    exact (qOf T).mul_mem (Subgroup.mem_inf.mp hd).1 (Subgroup.mem_inf.mp hd).1
  have hzsup : d * d ∈ Subgroup.zpowers (wOfX d x) ⊔ L :=
    hLT ⟨⟨hzT, hzC⟩, Subgroup.mem_sup_right hzQ⟩
  have hcom : ∀ l ∈ L, wOfX d x * l = l * wOfX d x := fun l hl =>
    Subgroup.mem_centralizer_iff.mp (hLC hl) (wOfX d x) (Set.mem_singleton _)
  have hLN : L ≤ Subgroup.normalizer ((Subgroup.zpowers (wOfX d x) : Subgroup G) : Set G) := by
    intro l hl
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute (wOfX d x) l from hcom l hl) j).eq
  obtain ⟨wj, hwj, l, hl, hzeq⟩ := (Lin2.mem_sup_iff_of_le_normalizer hLN).1 hzsup
  rcases mem_zpowers_of_sq_eq_one hw2 hwj with h1 | h1
  · rw [h1, one_mul] at hzeq
    exact Or.inl (hzeq ▸ hl)
  · rw [h1] at hzeq
    refine Or.inr ?_
    have : wOfX d x * (d * d) = l := by rw [hzeq, ← mul_assoc, hw2, one_mul]
    exact this ▸ hl

end S143

end CFSG.Quasithin
