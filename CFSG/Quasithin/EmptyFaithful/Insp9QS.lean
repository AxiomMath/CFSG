module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin

namespace Insp9

variable {Q : Type*} [Group Q]

theorem qs_normal_le_center_or_top (hq : CFSG.IsQuasisimple Q) (K : Subgroup Q) [hK : K.Normal] :
    K ≤ Subgroup.center Q ∨ K = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := hq
  have hN : (K.map (QuotientGroup.mk' (Subgroup.center Q))).Normal :=
    Subgroup.Normal.map hK _ (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal (K.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · left
    intro k hk
    have h1 : QuotientGroup.mk' (Subgroup.center Q) k ∈ K.map (QuotientGroup.mk' (Subgroup.center Q)) :=
      Subgroup.mem_map_of_mem _ hk
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  · right
    have hcomm : commutator Q ≤ K := by
      refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
      have h1 : (QuotientGroup.mk' (Subgroup.center Q) a) ∈
          K.map (QuotientGroup.mk' (Subgroup.center Q)) := by rw [h]; trivial
      obtain ⟨k, hk, hka⟩ := Subgroup.mem_map.mp h1
      have hz : k⁻¹ * a ∈ Subgroup.center Q := by
        have := QuotientGroup.eq.mp (by simpa using hka : (k : Q ⧸ Subgroup.center Q) = a)
        exact this
      have haz : a = k * (k⁻¹ * a) := by group
      set z := k⁻¹ * a with hzdef
      have hzb : z * b * z⁻¹ = b := by
        rw [mul_inv_eq_iff_eq_mul]
        exact Subgroup.mem_center_iff.mp hz b |>.symm
      rw [haz, commutatorElement_def]
      have : k * z * b * (k * z)⁻¹ * b⁻¹ = k * (z * b * z⁻¹) * k⁻¹ * b⁻¹ := by group
      rw [this, hzb]
      have h2 : k * b * k⁻¹ * b⁻¹ = k * (b * k⁻¹ * b⁻¹) := by group
      rw [h2]
      exact K.mul_mem hk (hK.conj_mem _ (K.inv_mem hk) b)
    have htop : commutator Q = ⊤ := hperf.commutator_eq_top
    rw [htop] at hcomm
    exact top_le_iff.mp hcomm

theorem qs_not_commutative (hq : CFSG.IsQuasisimple Q) : ¬ ∀ a b : Q, a * b = b * a := by
  intro h
  obtain ⟨-, -, a, b, hab⟩ := hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])

theorem qs_center_ne_top (hq : CFSG.IsQuasisimple Q) : Subgroup.center Q ≠ ⊤ := by
  intro h
  apply qs_not_commutative hq
  intro a b
  have ha : a ∈ Subgroup.center Q := by rw [h]; trivial
  exact (Subgroup.mem_center_iff.mp ha b).symm

theorem perfect_sign_eq_one {G : Type*} [Group G] [Group.IsPerfect G] (f : G →* ℤˣ) (g : G) :
    f g = 1 := by
  have hg : g ∈ commutator G := Group.IsPerfect.mem_commutator
  have hle : commutator G ≤ f.ker := by
    refine Subgroup.commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)]
  exact hle hg

theorem not_qs_of_equiv_perm {n : ℕ} (hn : 2 ≤ n) (e : Q ≃* Equiv.Perm (Fin n)) :
    ¬ CFSG.IsQuasisimple Q := by
  intro hq
  have hp : Group.IsPerfect Q := hq.1
  let f : Q →* ℤˣ := Equiv.Perm.sign.comp e.toMonoidHom
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by simp [a, b, Fin.ext_iff]
  have h1 : f (e.symm (Equiv.swap a b)) = -1 := by
    simp [f, Equiv.Perm.sign_swap hab]
  have h2 := perfect_sign_eq_one f (e.symm (Equiv.swap a b))
  rw [h1] at h2
  exact absurd h2 (by decide)

end Insp9

end CFSG.Quasithin
