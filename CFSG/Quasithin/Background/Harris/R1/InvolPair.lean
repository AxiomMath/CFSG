module

public import CFSG.Quasithin.Background.Harris.R1.ParityPerm
public import CFSG.Quasithin.Recognition.SzR1Prep

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.F7

namespace FamCtxLemmas

variable {G : Type} [Group G] [Finite G] {K1 L2 S Zs : Subgroup G} {Ω : Type}
  (C : FamCtx K1 L2 S Zs Ω) [Fintype Ω] [DecidableEq Ω]

include C

omit [Fintype Ω] [DecidableEq Ω] in
theorem permHom_pt {b : G} (hb : b ∈ K1 ⊔ S)
    (hbV : ∀ v ∈ C.D.Vf (conjClosure Zs L2) C.D.pt, v * b = b * v) :
    permHom C ⟨b, hb⟩ C.D.pt = C.D.pt := by
  have hnorm : b ∈ Subgroup.normalizer (C.D.Vf (conjClosure Zs L2) C.D.pt : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr hbV)
  exact permOf_eq_of_conjSub C (conjSub_eq_of_mem_normalizer hnorm)

theorem permHom_eq_one_of_comm_Zs (hΩ : Fintype.card Ω = 5) {b : G} (hb : b ∈ K1 ⊔ S)
    (hbV : ∀ v ∈ C.D.Vf (conjClosure Zs L2) C.D.pt, v * b = b * v)
    (hcom : ∀ i j : Ω, i ≠ C.D.pt → j ≠ C.D.pt → i ≠ j →
      b * (C.zf i * C.zf j) * b⁻¹ * (C.zf i * C.zf j)⁻¹ ∈ Zs) :
    permHom C ⟨b, hb⟩ = 1 := by
  set σ := permHom C ⟨b, hb⟩ with hσ
  have hpt := permHom_pt C hb hbV
  refine Equiv.ext fun x => ?_
  by_cases hx : x = C.D.pt
  · rw [hx]; exact hpt
  · obtain ⟨j, k, hj, hk, hxj, hxk, hjk⟩ := exists_two_ne (by omega : 4 ≤ Fintype.card Ω) C.D.pt x
    have h1 := pair_perm hxj ((pair_parity_split C (by omega) hb x j).1 (hcom x j hx hj hxj))
    have h2 := pair_perm hxk ((pair_parity_split C (by omega) hb x k).1 (hcom x k hx hk hxk))
    show σ x = x
    rcases h1 with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · rcases h2 with ⟨h2, -⟩ | ⟨h2, -⟩
      · exact h2
      · exact absurd (h1.symm.trans h2) hjk

end FamCtxLemmas

end CFSG.Quasithin.Background.Harris.R1
