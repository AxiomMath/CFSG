module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.H13.Ch4.J4KX

open Subgroup
open scoped commutatorElement

section Generic

variable {Q : Type} [Group Q]

theorem commutatorElement_central_mul_left {z : Q} (hz : z ∈ Subgroup.center Q) (a b : Q) :
    ⁅z * a, b⁆ = ⁅a, b⁆ := by
  have hzX : ∀ X : Q, X * z = z * X := fun X => Subgroup.mem_center_iff.mp hz X
  rw [commutatorElement_def, commutatorElement_def]
  have hzi : ∀ X : Q, z⁻¹ * X = X * z⁻¹ := fun X =>
    (Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hz) X).symm
  calc z * a * b * (z * a)⁻¹ * b⁻¹ = z * a * b * a⁻¹ * (z⁻¹ * b⁻¹) := by group
    _ = z * a * b * a⁻¹ * (b⁻¹ * z⁻¹) := by rw [hzi b⁻¹]
    _ = z * (a * b * a⁻¹ * b⁻¹) * z⁻¹ := by group
    _ = (a * b * a⁻¹ * b⁻¹) * z * z⁻¹ := by rw [← hzX (a * b * a⁻¹ * b⁻¹)]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem commutatorElement_central_mul_right {w : Q} (hw : w ∈ Subgroup.center Q) (a b : Q) :
    ⁅a, w * b⁆ = ⁅a, b⁆ := by
  have hwX : ∀ X : Q, X * w = w * X := fun X => Subgroup.mem_center_iff.mp hw X
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (w * b) * a⁻¹ * (w * b)⁻¹ = a * w * (b * a⁻¹ * b⁻¹ * w⁻¹) := by group
    _ = w * a * (b * a⁻¹ * b⁻¹ * w⁻¹) := by rw [hwX a]
    _ = w * (a * b * a⁻¹ * b⁻¹) * w⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [← hwX (a * b * a⁻¹ * b⁻¹)]; group

theorem commutatorElement_mul_expand (x q₁ q₂ : Q) :
    ⁅x, q₁ * q₂⁆ = ⁅x, q₁⁆ * (q₁ * ⁅x, q₂⁆ * q₁⁻¹) := by
  simp only [commutatorElement_def]
  group

theorem hom_trivial_of_commuting_values {A : Type} [Group A] (hP : ⁅(⊤ : Subgroup Q), ⊤⁆ = (⊤ : Subgroup Q))
    (f : Q →* A) (S : Set A) (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a)
    (hf : ∀ q, f q ∈ S) : ∀ q, f q = 1 := by
  have hker : (⊤ : Subgroup Q) ≤ f.ker := by
    rw [← hP]
    refine commutator_le.mpr fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, commutatorElement_def]
    simp only [map_mul, map_inv]
    have h := hS _ (hf a) _ (hf b)
    calc f a * f b * (f a)⁻¹ * (f b)⁻¹ = (f b * f a) * (f a)⁻¹ * (f b)⁻¹ := by rw [h]
      _ = 1 := by group
  intro q
  exact MonoidHom.mem_ker.mp (hker (Subgroup.mem_top q))

theorem normal_le_center_or_top (hQ : CFSG.IsQuasisimple Q) (N : Subgroup Q) [N.Normal] :
    N ≤ Subgroup.center Q ∨ N = ⊤ := by
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2.1
  let π : Q →* Q ⧸ Subgroup.center Q := QuotientGroup.mk' (Subgroup.center Q)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hN' : (N.map π).Normal := Subgroup.Normal.map inferInstance π hπ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · left
    intro x hx
    have hmem : π x ∈ N.map π := Subgroup.mem_map_of_mem π hx
    rw [h, Subgroup.mem_bot] at hmem
    exact (QuotientGroup.eq_one_iff x).mp hmem
  · right
    have key : ∀ g : Q, ∃ n ∈ N, ∃ z ∈ Subgroup.center Q, g = n * z := by
      intro g
      have hg : π g ∈ N.map π := by rw [h]; exact Subgroup.mem_top (π g)
      obtain ⟨n, hn, hng⟩ := Subgroup.mem_map.mp hg
      refine ⟨n, hn, n⁻¹ * g, ?_, by group⟩
      exact QuotientGroup.eq.mp hng
    have hc : ⁅(⊤ : Subgroup Q), ⊤⁆ ≤ N := by
      refine commutator_le.mpr fun a _ b _ => ?_
      obtain ⟨n, hn, z, hz, rfl⟩ := key a
      obtain ⟨m, hm, w, hw, rfl⟩ := key b
      rw [Subgroup.mem_center_iff.mp hz n, Subgroup.mem_center_iff.mp hw m,
        commutatorElement_central_mul_left hz, commutatorElement_central_mul_right hw]
      have e : ⁅n, m⁆ = n * (m * n⁻¹ * m⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact N.mul_mem hn (Subgroup.Normal.conj_mem inferInstance n⁻¹ (N.inv_mem hn) m)
    have htop : (⊤ : Subgroup Q) ≤ N := by
      have h2 := hc
      rw [show ⁅(⊤ : Subgroup Q), ⊤⁆ = (⊤ : Subgroup Q) from hQ.1.commutator_eq_top] at h2
      exact h2
    exact top_le_iff.mp htop

theorem center_quot_eq (hP : ⁅(⊤ : Subgroup Q), ⊤⁆ = (⊤ : Subgroup Q)) (N : Subgroup Q) [N.Normal]
    (hN : N ≤ Subgroup.center Q) :
    Subgroup.center (Q ⧸ N) = (Subgroup.center Q).map (QuotientGroup.mk' N) := by
  have hπ : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective _
  apply le_antisymm
  · intro y hy
    obtain ⟨x, rfl⟩ := hπ y
    have hval : ∀ q : Q, ⁅x, q⁆ ∈ Subgroup.center Q := by
      intro q
      apply hN
      have h1 : (QuotientGroup.mk' N) ⁅x, q⁆ = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact (Subgroup.mem_center_iff.mp hy (QuotientGroup.mk' N q)).symm
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hmul : ∀ a b : Q, ⁅x, a * b⁆ = ⁅x, a⁆ * ⁅x, b⁆ := by
      intro a b
      have hconj : a * ⁅x, b⁆ * a⁻¹ = ⁅x, b⁆ := by
        rw [Subgroup.mem_center_iff.mp (hval b) a]
        group
      rw [commutatorElement_mul_expand, hconj]
    let f : Q →* Q := MonoidHom.mk' (fun q => ⁅x, q⁆) hmul
    have htriv := hom_trivial_of_commuting_values hP f (Subgroup.center Q : Set Q)
      (fun a ha b _ => (Subgroup.mem_center_iff.mp ha b).symm) hval
    have hxc : x ∈ Subgroup.center Q := by
      refine Subgroup.mem_center_iff.mpr fun g => ?_
      exact (commutatorElement_eq_one_iff_mul_comm.mp (htriv g)).symm
    exact Subgroup.mem_map.mpr ⟨x, hxc, rfl⟩
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    obtain ⟨q, rfl⟩ := hπ g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz q]

theorem nonabelian_transfer {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : ∃ a b : A, a * b ≠ b * a) : ∃ a b : B, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := h
  refine ⟨e a, e b, fun h' => hab ?_⟩
  apply e.injective
  simpa [map_mul] using h'

theorem isQuasisimple_quot_of_le_center (hQ : CFSG.IsQuasisimple Q) (N : Subgroup Q) [N.Normal]
    (hN : N ≤ Subgroup.center Q) : CFSG.IsQuasisimple (Q ⧸ N) := by
  have hπ : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective _
  have hcomm : commutator (Q ⧸ N) = ⊤ := by
    have h1 : Subgroup.map (QuotientGroup.mk' N) ⁅(⊤ : Subgroup Q), ⊤⁆ = (⊤ : Subgroup (Q ⧸ N)) := by
      rw [show ⁅(⊤ : Subgroup Q), ⊤⁆ = (⊤ : Subgroup Q) from hQ.1.commutator_eq_top]
      exact Subgroup.map_top_of_surjective _ hπ
    rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective _ hπ] at h1
    exact h1
  have hc := center_quot_eq hQ.1.commutator_eq_top N hN
  have e1 := QuotientGroup.quotientMulEquivOfEq hc
  have e2 := QuotientGroup.quotientQuotientEquivQuotient N (Subgroup.center Q) hN
  have ε := e1.trans e2
  refine ⟨⟨hcomm⟩, ?_, ?_⟩
  · haveI := hQ.2.1
    exact MulEquiv.isSimpleGroup ε
  · exact nonabelian_transfer ε.symm hQ.2.2

theorem isQuasisimple_of_quot_le_center (hP : Group.IsPerfect Q) (N : Subgroup Q)
    [N.Normal] (hN : N ≤ Subgroup.center Q) (hq : CFSG.IsQuasisimple (Q ⧸ N)) :
    CFSG.IsQuasisimple Q := by
  have hc := center_quot_eq hP.commutator_eq_top N hN
  have e1 := QuotientGroup.quotientMulEquivOfEq hc
  have e2 := QuotientGroup.quotientQuotientEquivQuotient N (Subgroup.center Q) hN
  have ε := e1.trans e2
  haveI := hq.2.1
  refine ⟨hP, ?_, ?_⟩
  · exact MulEquiv.isSimpleGroup ε.symm
  · exact nonabelian_transfer ε hq.2.2

theorem subgroup_eq_of_normal_quasisimple {X : Type} [Group X] {K' K : Subgroup X}
    (hK' : CFSG.IsQuasisimple ↥K') (hK : CFSG.IsQuasisimple ↥K) (hKK' : K ≤ K')
    (hn : (K.subgroupOf K').Normal) : K = K' := by
  rcases normal_le_center_or_top hK' (K.subgroupOf K') with hc | htop
  · exfalso
    obtain ⟨a, b, hab⟩ := hK.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hcomm : (a' : X) * b' = b' * a' := by
      have hmem : (⟨a', hKK' a'.2⟩ : ↥K') ∈ K.subgroupOf K' := Subgroup.mem_subgroupOf.mpr a'.2
      have hmem' : (⟨b', hKK' b'.2⟩ : ↥K') ∈ K.subgroupOf K' := Subgroup.mem_subgroupOf.mpr b'.2
      have := Subgroup.mem_center_iff.mp (hc hmem) ⟨b', hKK' b'.2⟩
      have h2 := congrArg Subtype.val this
      simpa using h2.symm
    have hcomm' : a' * b' = b' * a' := Subtype.ext (by simpa using hcomm)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcomm']
  · have hKtop : K' ≤ K := by
      rwa [Subgroup.subgroupOf_eq_top] at htop
    exact le_antisymm hKK' hKtop

end Generic

end CFSG.Quasithin.H13.Ch4.J4KX

end
