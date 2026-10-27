module

public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
import CFSG.LocalAnalysis.ComponentClassification.PSL3FourIndexTwoLocalB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.ThreeOC

open CFSG.ComponentClassification.PSL3Four

theorem g₄_mul_r₄ : g₄ * r₄ = r₄ * g₄ :=
  ((tabRep_g₄.comp tabRep_r₄).eq_iff (tabRep_r₄.comp tabRep_g₄)).1 (by decide)

theorem g₅_mul_r₄ : g₅ * r₄ = r₄ * g₅ :=
  ((tabRep_g₅.comp tabRep_r₄).eq_iff (tabRep_r₄.comp tabRep_g₅)).1 (by decide)

theorem g₆_mul_r₄ : g₆ * r₄ = r₄ * g₆ :=
  ((tabRep_g₆.comp tabRep_r₄).eq_iff (tabRep_r₄.comp tabRep_g₆)).1 (by decide)

theorem commutator_r₄_mem_S {c : Equiv.Perm (Fin 42)} (hc : c ∈ R) :
    c * r₄ * c⁻¹ * r₄⁻¹ ∈ S := by
  have hS : ∀ s ∈ S, s * r₄ * s⁻¹ * r₄⁻¹ ∈ S := fun s hs => by
    have h := S.mul_mem hs (conj_mem_S r₄_mem_R (S.inv_mem hs))
    rwa [show s * (r₄ * s⁻¹ * r₄⁻¹) = s * r₄ * s⁻¹ * r₄⁻¹ by group] at h
  have hcomm : ∀ g : Equiv.Perm (Fin 42), g * r₄ = r₄ * g → g * r₄ * g⁻¹ * r₄⁻¹ ∈ S :=
    fun g h => by rw [h, mul_inv_cancel_right, mul_inv_cancel]; exact S.one_mem
  rw [R] at hc
  induction hc using Subgroup.closure_induction with
  | mem s hs =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hS _ g₁_mem_S
    · exact hS _ g₂_mem_S
    · exact hS _ g₃_mem_S
    · exact hcomm _ g₄_mul_r₄
    · exact hcomm _ g₅_mul_r₄
    · exact hcomm _ g₆_mul_r₄
  | one => simp
  | mul x y hx _ ihx ihy =>
    have h := S.mul_mem (conj_mem_S hx ihy) ihx
    rwa [show x * (y * r₄ * y⁻¹ * r₄⁻¹) * x⁻¹ * (x * r₄ * x⁻¹ * r₄⁻¹) =
      x * y * r₄ * (x * y)⁻¹ * r₄⁻¹ by group] at h
  | inv x hx ihx =>
    have h := conj_mem_S (R.inv_mem hx) (S.inv_mem ihx)
    rwa [show x⁻¹ * (x * r₄ * x⁻¹ * r₄⁻¹)⁻¹ * x⁻¹⁻¹ = x⁻¹ * r₄ * x⁻¹⁻¹ * r₄⁻¹ by group] at h

theorem not_mem_S_and_mul_r₄_inv_mem_S {x : ↥R}
    (hx : orderOf x = 2)
    (h9 : 9 ∣ Nat.card ↥(Subgroup.centralizer {(x : Equiv.Perm (Fin 42))} ⊓ S)) :
    (x : Equiv.Perm (Fin 42)) ∉ S ∧ (x : Equiv.Perm (Fin 42)) * r₄⁻¹ ∈ S := by
  rcases (CFSG.ComponentClassification.PSL3Four.orderOf_eq_two_iff x).1 hx with h | h | h | h
  · obtain ⟨e⟩ := fixed_of_isConj h
    have hC : Nat.card ↥(Subgroup.centralizer {(r₁R : Equiv.Perm (Fin 42))} ⊓ S) = 64 := card_C₁
    rw [Nat.card_congr e.toEquiv, hC] at h9
    exact absurd h9 (by norm_num)
  · obtain ⟨e⟩ := fixed_of_isConj h
    have hC : Nat.card ↥(Subgroup.centralizer {(r₂R : Equiv.Perm (Fin 42))} ⊓ S) = 168 := card_C₂
    rw [Nat.card_congr e.toEquiv, hC] at h9
    exact absurd h9 (by norm_num)
  · obtain ⟨e⟩ := fixed_of_isConj h
    have hC : Nat.card ↥(Subgroup.centralizer {(r₃R : Equiv.Perm (Fin 42))} ⊓ S) = 60 := card_C₃
    rw [Nat.card_congr e.toEquiv, hC] at h9
    exact absurd h9 (by norm_num)
  · obtain ⟨c, hc, he⟩ := eq_conj_of_isConj h
    refine ⟨not_mem_S_of_isConj h not_mem_S_r₄, ?_⟩
    rw [he]
    exact commutator_r₄_mem_S hc

theorem exists_embedding_R {X : Type} [Group X] {K : Subgroup X}
    [K.Normal] (hKC : Subgroup.centralizer (K : Set X) = ⊥) (θ : ↥K ≃* ↥S) :
    ∃ ψ : X →* ↥R, Function.Injective ψ ∧
      (∀ x : X, ((ψ x : ↥R) : Equiv.Perm (Fin 42)) ∈ S ↔ x ∈ K) ∧
      ∀ (x : X) (k : ↥K), ((ψ x : ↥R) : Equiv.Perm (Fin 42)) * θ k *
        ((ψ x : ↥R) : Equiv.Perm (Fin 42))⁻¹ = θ (MulAut.conjNormal x k) := by
  obtain ⟨E, hE, -⟩ := full_automorphism_action
  let ψ : X →* ↥R := E.symm.toMonoidHom.comp ((MulAut.congr θ).toMonoidHom.comp MulAut.conjNormal)
  have hEψ : ∀ x : X, E (ψ x) = MulAut.congr θ (MulAut.conjNormal x) := fun x =>
    E.apply_symm_apply _
  have hc : ∀ (x : X) (k : ↥K), ((ψ x : ↥R) : Equiv.Perm (Fin 42)) * θ k *
      ((ψ x : ↥R) : Equiv.Perm (Fin 42))⁻¹ = θ (MulAut.conjNormal x k) := by
    intro x k
    have h := hE (ψ x) (θ k)
    have h' : ((MulAut.congr θ (MulAut.conjNormal x)) (θ k) : ↥S) = θ (MulAut.conjNormal x k) := by
      simp [MulAut.congr_apply]
    rw [hEψ x, h', Subgroup.coe_inv] at h
    exact h.symm
  have hK : ∀ k : ↥K, ψ (k : X) = ⟨θ k, S_le_R (θ k).2⟩ := by
    intro k
    apply E.injective
    refine MulEquiv.ext fun s => Subtype.ext ?_
    rw [hEψ, hE, MulAut.congr_apply]
    simp [MulAut.conjNormal_val]
  have hinj : Function.Injective ψ := by
    refine (injective_iff_map_eq_one ψ).2 fun x hx => ?_
    have hcomm : ∀ n ∈ (K : Set X), n * x = x * n := by
      intro n hn
      have h1 := hc x ⟨n, hn⟩
      rw [hx] at h1
      simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one] at h1
      have h4 := congrArg Subtype.val (θ.injective (Subtype.ext h1))
      simp only [MulAut.conjNormal_apply] at h4
      calc n * x = (x * n * x⁻¹) * x := by rw [← h4]
        _ = x * n := by group
    have hx' : x ∈ Subgroup.centralizer (K : Set X) := Subgroup.mem_centralizer_iff.2 hcomm
    rwa [hKC, Subgroup.mem_bot] at hx'
  refine ⟨ψ, hinj, fun x => ⟨fun hx => ?_, fun hx => ?_⟩, hc⟩
  · have hk : ψ ((θ.symm ⟨_, hx⟩ : ↥K) : X) = ψ x := by
      rw [hK]
      exact Subtype.ext (by simp)
    exact hinj hk ▸ (θ.symm ⟨_, hx⟩).2
  · have hk := hK ⟨x, hx⟩
    rw [hk]
    exact (θ ⟨x, hx⟩).2

theorem nine_dvd_card_fixed {X : Type} [Group X] {K Q : Subgroup X} [K.Normal] (θ : ↥K ≃* ↥S)
    {t : X} {r : Equiv.Perm (Fin 42)}
    (hθ : ∀ n : ↥K, r * (θ n : Equiv.Perm (Fin 42)) * r⁻¹ =
      (θ (MulAut.conjNormal t n) : Equiv.Perm (Fin 42)))
    (hQK : Q ≤ K) (hQ9 : Nat.card ↥Q = 9) (ht : ∀ q ∈ Q, t * q = q * t) :
    9 ∣ Nat.card ↥(Subgroup.centralizer {r} ⊓ S) := by
  rw [← Nat.card_congr (fixedEquiv K θ t r hθ).toEquiv]
  have hle : Q.subgroupOf K ≤ (Subgroup.centralizer {t}).subgroupOf K := fun q hq =>
    Subgroup.mem_subgroupOf.2 (Subgroup.mem_centralizer_singleton_iff.2
      (ht _ (Subgroup.mem_subgroupOf.1 hq)).symm)
  have h9 : Nat.card ↥(Q.subgroupOf K) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv, hQ9]
  exact h9 ▸ Subgroup.card_dvd_of_le hle

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.ThreeOC
