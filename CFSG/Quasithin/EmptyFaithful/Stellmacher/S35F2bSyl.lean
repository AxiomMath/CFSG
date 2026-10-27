module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin11

public section

namespace CFSG.Quasithin.F53.Stellmacher.S35.F2b

open Equiv CFSG.Quasithin CFSG.Quasithin.F53Mod CFSG.Quasithin.F53.Stellmacher.S35.Fin

theorem commW_mono {n : ℕ} (M : Model n) {B B' : Subgroup (Perm (Fin n))} {U U' : Subgroup M.W}
    (hB : B ≤ B') (hU : U ≤ U') : commW M B U ≤ commW M B' U' := by
  unfold commW
  exact Subgroup.closure_mono fun w ⟨b, hb, u, hu, hw⟩ => ⟨b, hB hb, u, hU hu, hw⟩

theorem nodup5 {a b c d p : Fin 5} (h : [a, b, c, d, p].Nodup) :
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ a ≠ p ∧ b ≠ c ∧ b ≠ d ∧ b ≠ p ∧ c ≠ d ∧ c ≠ p ∧ d ≠ p := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at h
  tauto

theorem ep_ne_ep {a b c d p : Fin 5} (h : [a, b, c, d, p].Nodup) : ep a b ≠ ep c d := by
  intro he
  have h1 := ep_mul_ep h
  rw [← he, ep_mul_self] at h1
  exact vp_ne_one p h1.symm

theorem exists_decomp {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) :
    ∃ a b c d : Fin 5, [a, b, c, d, fixPt D].Nodup ∧ zc D = swap a b * swap c d := by
  obtain ⟨a, b, c, d, p, h, hdec⟩ := exists_decomp_of_centInv hD (isCentInv_zc hD)
  have hp := isFixPt_of_decomp hD (isCentInv_zc hD) h hdec
  rw [fixPt_eq hD hp]
  exact ⟨a, b, c, d, h, hdec⟩

variable {D : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) {z : Perm (Fin 5)}
  (hz : IsCentInv D z) {a b c d p : Fin 5} (h : [a, b, c, d, p].Nodup)
  (hdec : z = swap a b * swap c d)

include hD hz h hdec

theorem isFixPt_p : IsFixPt D p := isFixPt_of_decomp hD hz h hdec

theorem act_ep_ab_iff {x : Perm (Fin 5)} (hx : x ∈ D) :
    orth.act x (ep a b) = ep a b ↔ x ∈ That D :=
  (mem_That_iff_act hD hz h hdec hx).symm

theorem act_ep_cd_iff {x : Perm (Fin 5)} (hx : x ∈ D) :
    orth.act x (ep c d) = ep c d ↔ x ∈ That D := by
  rw [← act_ep_ab_iff hD hz h hdec hx]
  rcases act_ep_of_mem hD hz h hdec hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun _ => h1, fun _ => h2⟩
  · constructor
    · intro h3; exact absurd (h2.symm.trans h3) (ep_ne_ep h)
    · intro h3; exact absurd (h1.symm.trans h3) (ep_ne_ep h).symm

theorem act_ep_ab_mul_inv {x : Perm (Fin 5)} (hx : x ∈ D) (hx' : x ∉ That D) :
    orth.act x (ep a b) * (ep a b)⁻¹ = vp p := by
  rcases act_ep_of_mem hD hz h hdec hx with ⟨h1, _⟩ | ⟨h1, _⟩
  · exact absurd ((mem_That_iff_act hD hz h hdec hx).mpr h1) hx'
  · rw [h1, inv_eq_of_mul_eq_one_right (ep_mul_self a b), mul_comm, ep_mul_ep h]

theorem act_ep_cd_mul_inv {x : Perm (Fin 5)} (hx : x ∈ D) (hx' : x ∉ That D) :
    orth.act x (ep c d) * (ep c d)⁻¹ = vp p := by
  rcases act_ep_of_mem hD hz h hdec hx with ⟨h1, _⟩ | ⟨_, h2⟩
  · exact absurd ((mem_That_iff_act hD hz h hdec hx).mpr h1) hx'
  · rw [h2, inv_eq_of_mul_eq_one_right (ep_mul_self c d), ep_mul_ep h]

theorem commW_That_eq_commW_z :
    commW orth (That D) ⊤ = commW orth (Subgroup.zpowers z) ⊤ := by
  have hz_mem : z ∈ That D := (mem_That_iff hD hz h hdec z).mpr (Or.inr (Or.inr (Or.inr rfl)))
  apply le_antisymm
  · unfold commW
    refine (Subgroup.closure_le _).mpr ?_
    rintro w ⟨x, hx, u, -, rfl⟩
    rw [SetLike.mem_coe]
    have hdbl := (mem_That_iff hD hz h hdec x).mp hx
    have hab : a ≠ b := (nodup5 h).1
    have hcd : c ≠ d := (nodup5 h).2.2.2.2.2.2.2.1
    have hep : ∀ s : Perm (Fin 5), s ∈ ({swap a b, swap c d} : Set (Perm (Fin 5))) →
        orth.act s u * u⁻¹ ∈ commW orth (Subgroup.zpowers z) ⊤ := by
      intro s hs
      have h1 : orth.act s u * u⁻¹ ∈ commW orth (Subgroup.zpowers s) ⊤ :=
        Subgroup.subset_closure ⟨s, Subgroup.mem_zpowers s, u, trivial, rfl⟩
      rcases hs with rfl | rfl
      · rw [commW_swap hab] at h1
        have : ep a b ∈ commW orth (Subgroup.zpowers z) ⊤ := by
          subst hdec; rw [mem_commW_double h]; tauto
        exact (Subgroup.zpowers_le.mpr this) h1
      · rw [commW_swap hcd] at h1
        have : ep c d ∈ commW orth (Subgroup.zpowers z) ⊤ := by
          subst hdec; rw [mem_commW_double h]; tauto
        exact (Subgroup.zpowers_le.mpr this) h1
    rcases hdbl with rfl | rfl | rfl | rfl
    · rw [map_one]; simp
    · exact hep _ (Set.mem_insert _ _)
    · exact hep _ (Set.mem_insert_of_mem _ rfl)
    · exact Subgroup.subset_closure ⟨_, Subgroup.mem_zpowers _, u, trivial, rfl⟩
  · exact commW_mono orth (Subgroup.zpowers_le.mpr hz_mem) le_rfl

theorem mem_commW_That_iff (w : orth.W) :
    w ∈ commW orth (That D) ⊤ ↔ w = 1 ∨ w = ep a b ∨ w = ep c d ∨ w = vp p := by
  rw [commW_That_eq_commW_z hD hz h hdec]
  subst hdec
  exact mem_commW_double h w

omit hz h hdec

omit hD

end CFSG.Quasithin.F53.Stellmacher.S35.F2b
