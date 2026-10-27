module

public import CFSG.Quasithin.H13.A6S1342
public import CFSG.Quasithin.H13.Sp62C3System
public import CFSG.Quasithin.H13.GoldschmidtI51

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Blueprint

@[expose] def Input1349 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting134 G T L V) (z : G),
    z ∈ fsuV1 T V → z ∉ Subgroup.centralizer (L : Set G) →
    ¬ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G) →
    Group.IsSolvable ↥(Subgroup.centralizer ({z} : Set G)) →
    ∃ E₂ : Subgroup G,
      IsDSystemIn .C3 ![Subgroup.normalizer (L : Set G), Subgroup.centralizer ({z} : Set G), E₂] ∧
      (LieModel ↥(Subgroup.normalizer (L : Set G) ⊔ Subgroup.centralizer ({z} : Set G) ⊔ E₂)
          .PSp 3 2 1 →
        (∀ a ∈ Subgroup.normalizer (L : Set G) ⊔ Subgroup.centralizer ({z} : Set G) ⊔ E₂,
          ∀ b ∈ Subgroup.normalizer (L : Set G) ⊔ Subgroup.centralizer ({z} : Set G) ⊔ E₂,
            orderOf a = 2 → IsConj a b →
              ∃ e ∈ Subgroup.normalizer (L : Set G) ⊔ Subgroup.centralizer ({z} : Set G) ⊔ E₂,
                e * a * e⁻¹ = b) ∧
        ∀ e : G, IsConj S.zV e → S.zV * e = e * S.zV → e ≠ S.zV →
          Subgroup.centralizer ({S.zV * e} : Set G) ≤
            Subgroup.normalizer (L : Set G) ⊔ Subgroup.centralizer ({z} : Set G) ⊔ E₂)

namespace Setting134

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting134 G T L V)
include S

theorem orderOf_zV : orderOf S.zV = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime S.zV_sq S.zV_ne_one

theorem centralizer_zV_eq :
    Subgroup.centralizer ({S.zV} : Set G) =
      Subgroup.centralizer ((V ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases S.mem_ZV_iff.1 hy with rfl | rfl
    · simp
    · exact (Subgroup.mem_centralizer_singleton_iff.1 hx).symm
  · exact Subgroup.centralizer_le (by
      rw [Set.singleton_subset_iff]
      exact S.mem_ZV_iff.2 (Or.inr rfl))

theorem centralizer_zV (h1222 : Stmt12_2_2) :
    Subgroup.centralizer ({S.zV} : Set G) = Subgroup.normalizer (L : Set G) := by
  have h := S.lemma13_4_2_one h1222
  rw [S.centralizer_zV_eq, ← h.2, ← h.1]

end Setting134

theorem prop_13_4_9
    (h1332 : Stmt13_3_2) (h1222 : Stmt12_2_2) (h1349 : Input1349) : Stmt13_4_9 := by
  have hI51 : StmtI_5_1 := stmtI_5_1_holds
  intro G _ _ T L V z h hV hZV hz hzL hCz hsol
  obtain ⟨S⟩ := exists_setting134 h1332 h hV hZV
  obtain ⟨E₂, hD, hfus⟩ := h1349 G T L V S z hz hzL hCz hsol
  have hLE := (hI51 _ .C3 _ hD.isDSystem).2 rfl
  obtain ⟨hf, hp⟩ := hfus hLE
  refine lieModel_psp_of_c3System hI51 h.simple h.nonabelian _ hD.isDSystem S.orderOf_zV ?_ hf hp
  rw [S.centralizer_zV h1222]
  exact le_sup_left.trans le_sup_left

end CFSG.Quasithin.H13.A6
