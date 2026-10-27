module

public import CFSG.Quasithin.Background.B1MoreElevenD
public import CFSG.Quasithin.Background.InternalSecIrr

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open
open scoped commutatorElement

variable {Ω : Type} [Group Ω]

theorem not_commute_of_isQuasisimple {K : Subgroup Ω} (hK : CFSG.IsQuasisimple ↥K)
    (h : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a) : False := by
  obtain ⟨a, b, hab⟩ := exists_noncomm_of_isQuasisimple hK
  exact hab (Subtype.ext (h a a.2 b b.2))

theorem le_quasithinGenFitting_of_normal {K J : Subgroup Ω} (hKJ : K ≤ J)
    (hn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hK : CFSG.IsQuasisimple ↥K) :
    K ≤ quasithinGenFitting J := by
  refine le_sup_of_le_right (le_sSup ⟨hKJ, ?_, B1Red.isQuasisimple_to_open hK⟩)
  refine IsSubnormal.step hKJ ?_ (IsSubnormal.refl _)
  exact (Subgroup.normal_subgroupOf_iff hKJ).2 fun l y hl hy => hn y hy l hl

theorem eq_of_le_quasisimple {K J : Subgroup Ω} (hKJ : K ≤ J)
    (hn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hK : CFSG.IsQuasisimple ↥K)
    (hE : CFSG.IsQuasisimple ↥(quasithinGenFitting J)) : quasithinGenFitting J = K := by
  set E := quasithinGenFitting J with hEdef
  have hKE : K ≤ E := le_quasithinGenFitting_of_normal hKJ hn hK
  have hEJ : E ≤ J := quasithinGenFitting_le J
  have hnorm : (K.subgroupOf E).Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hn g (hEJ g.2) k hk
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top
    (B1Red.isQuasisimple_to_open hE) (K.subgroupOf E) with hc | htop
  · exfalso
    refine not_commute_of_isQuasisimple hK fun a ha b hb => ?_
    have h1 : (⟨a, hKE ha⟩ : ↥E) ∈ Subgroup.center ↥E := hc ha
    have h2 := Subgroup.mem_center_iff.mp h1 ⟨b, hKE hb⟩
    exact (congrArg Subtype.val h2).symm
  · refine le_antisymm (fun e he => ?_) hKE
    have : (⟨e, he⟩ : ↥E) ∈ K.subgroupOf E := by rw [htop]; trivial
    exact this

theorem le_normalizer_of_commute {G₁ G₂ : Subgroup Ω}
    (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) :
    G₂ ≤ Subgroup.normalizer (G₁ : Set Ω) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [show b * g * b⁻¹ = g by rw [← hcomm g hg b hb]; group]
    exact hg
  · intro hg
    have h2 := hcomm _ hg b⁻¹ (G₂.inv_mem hb)
    have e : g = b * g * b⁻¹ := by
      calc g = b⁻¹ * (b * g * b⁻¹) * b := by group
        _ = (b * g * b⁻¹) * b⁻¹ * b := by rw [← h2]
        _ = b * g * b⁻¹ := by group
    rw [e]
    exact hg

theorem conj_mem_of_mem_sup_of_commute {G₁ G₂ : Subgroup Ω}
    (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) :
    ∀ x ∈ G₁ ⊔ G₂, ∀ g ∈ G₁, x * g * x⁻¹ ∈ G₁ := by
  intro x hx g hg
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    (B19Aux.mem_sup_iff_of_le_normalizer (le_normalizer_of_commute hcomm)).1 hx
  have e : a * b * g * (a * b)⁻¹ = a * g * a⁻¹ := by
    rw [show a * b * g * (a * b)⁻¹ = a * (b * g) * b⁻¹ * a⁻¹ by group, ← hcomm g hg b hb]
    group
  rw [e]
  exact G₁.mul_mem (G₁.mul_mem ha hg) (G₁.inv_mem ha)

theorem le_or_le_of_commute {K G₁ G₂ : Subgroup Ω} (hK : CFSG.IsQuasisimple ↥K)
    (hKG : K ≤ G₁ ⊔ G₂)
    (h₁ : ∀ g ∈ G₁, ∀ k ∈ K, g * k * g⁻¹ ∈ K) (h₂ : ∀ g ∈ G₂, ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (h₁' : ∀ k ∈ K, ∀ g ∈ G₁, k * g * k⁻¹ ∈ G₁) (h₂' : ∀ k ∈ K, ∀ g ∈ G₂, k * g * k⁻¹ ∈ G₂) :
    K ≤ G₁ ∨ K ≤ G₂ := by
  by_contra h
  push Not at h
  have hKo := B1Red.isQuasisimple_to_open hK
  have c₁ := B1Red.commute_of_normal_not_le hKo h₁ h₁' h.1
  have c₂ := B1Red.commute_of_normal_not_le hKo h₂ h₂' h.2
  have hcent : G₁ ⊔ G₂ ≤ Subgroup.centralizer (K : Set Ω) := by
    refine sup_le (fun g hg => ?_) (fun g hg => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      exact fun k hk => (c₁ g hg k hk).symm
    · rw [Subgroup.mem_centralizer_iff]
      exact fun k hk => (c₂ g hg k hk).symm
  exact not_commute_of_isQuasisimple hK fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hcent (hKG ha)) b hb |>.symm

theorem le_commutator_of_perfect {K J : Subgroup Ω} (hKJ : K ≤ J) (hK : Group.IsPerfect ↥K) :
    K ≤ ⁅J, J⁆ := by
  have h1 : ⁅K, K⁆ = K := by
    have h2 := Subgroup.map_commutator (⊤ : Subgroup ↥K) ⊤ K.subtype
    rw [← commutator_def, Group.IsPerfect.commutator_eq_top, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h2
    exact h2.symm
  rw [← h1]
  exact Subgroup.commutator_mono hKJ hKJ

theorem commutator_le_of_zpowers {N : Subgroup Ω} {t : Ω}
    (ht : t ∈ Subgroup.normalizer (N : Set Ω)) :
    ⁅N ⊔ Subgroup.zpowers t, N ⊔ Subgroup.zpowers t⁆ ≤ N := by
  have hz : Subgroup.zpowers t ≤ Subgroup.normalizer (N : Set Ω) := Subgroup.zpowers_le.2 ht
  have hconj : ∀ s ∈ Subgroup.zpowers t, ∀ n ∈ N, s * n * s⁻¹ ∈ N := fun s hs n hn =>
    (Subgroup.mem_normalizer_iff.mp (hz hs) n).mp hn
  rw [Subgroup.commutator_le]
  intro x hx y hy
  obtain ⟨n₁, hn₁, s, hs, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hz).1 hx
  obtain ⟨n₂, hn₂, r, hr, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hz).1 hy
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
  obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.1 hr
  have hsr : t ^ a * t ^ b = t ^ b * t ^ a := (Commute.zpow_zpow_self t a b).eq
  have e : ⁅n₁ * t ^ a, n₂ * t ^ b⁆ =
      n₁ * (t ^ a * n₂ * (t ^ a)⁻¹) * (t ^ b * n₁⁻¹ * (t ^ b)⁻¹) * n₂⁻¹ := by
    rw [commutatorElement_def]
    calc n₁ * t ^ a * (n₂ * t ^ b) * (n₁ * t ^ a)⁻¹ * (n₂ * t ^ b)⁻¹
        = n₁ * (t ^ a * n₂ * (t ^ a)⁻¹) * (t ^ a * t ^ b * (t ^ a)⁻¹) * n₁⁻¹ * (t ^ b)⁻¹ *
            n₂⁻¹ := by group
      _ = n₁ * (t ^ a * n₂ * (t ^ a)⁻¹) * (t ^ b * t ^ a * (t ^ a)⁻¹) * n₁⁻¹ * (t ^ b)⁻¹ *
            n₂⁻¹ := by rw [hsr]
      _ = n₁ * (t ^ a * n₂ * (t ^ a)⁻¹) * (t ^ b * n₁⁻¹ * (t ^ b)⁻¹) * n₂⁻¹ := by group
  rw [e]
  exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ (hconj _ (Subgroup.zpow_mem_zpowers t a) _ hn₂))
    (hconj _ (Subgroup.zpow_mem_zpowers t b) _ (N.inv_mem hn₁))) (N.inv_mem hn₂)

theorem not_le_of_card_prime {K X : Subgroup Ω} (hK : CFSG.IsQuasisimple ↥K) (hKX : K ≤ X)
    {p : ℕ} [Fact p.Prime] (hX : Nat.card ↥X = p) : False := by
  have : IsCyclic ↥X := isCyclic_of_prime_card hX
  let _ := IsCyclic.commGroup (α := ↥X)
  refine not_commute_of_isQuasisimple hK fun a ha b hb => ?_
  exact congrArg Subtype.val (mul_comm (⟨a, hKX ha⟩ : ↥X) ⟨b, hKX hb⟩)

theorem not_le_perm_three {K J : Subgroup Ω} (hK : CFSG.IsQuasisimple ↥K) (hKJ : K ≤ J)
    (e : ↥J ≃* Equiv.Perm (Fin 3)) : False := by
  have : Group.IsPerfect ↥K := hK.1
  set f : ↥K →* ℤˣ := Equiv.Perm.sign.comp (e.toMonoidHom.comp (Subgroup.inclusion hKJ))
  have hf : ∀ k : ↥K, f k = 1 := by
    intro k
    have h1 := Abelianization.commutator_subset_ker f
    rw [Group.IsPerfect.commutator_eq_top] at h1
    exact h1 (Subgroup.mem_top k)
  have hA3 : Nat.card ↥(alternatingGroup (Fin 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
    rfl
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : IsCyclic ↥(alternatingGroup (Fin 3)) := isCyclic_of_prime_card hA3
  let _ := IsCyclic.commGroup (α := ↥(alternatingGroup (Fin 3)))
  have hmem : ∀ k : ↥K, e (Subgroup.inclusion hKJ k) ∈ alternatingGroup (Fin 3) := fun k =>
    Equiv.Perm.mem_alternatingGroup.2 (hf k)
  refine not_commute_of_isQuasisimple hK fun a ha b hb => ?_
  have hc : e (Subgroup.inclusion hKJ ⟨a, ha⟩) * e (Subgroup.inclusion hKJ ⟨b, hb⟩) =
      e (Subgroup.inclusion hKJ ⟨b, hb⟩) * e (Subgroup.inclusion hKJ ⟨a, ha⟩) :=
    congrArg Subtype.val
      (mul_comm (⟨_, hmem ⟨a, ha⟩⟩ : ↥(alternatingGroup (Fin 3))) ⟨_, hmem ⟨b, hb⟩⟩)
  rw [← map_mul e, ← map_mul e] at hc
  exact congrArg Subtype.val (e.injective hc)

theorem mem_normalizer_sup {G₁ G₂ : Subgroup Ω} {t : Ω}
    (h₁ : t ∈ Subgroup.normalizer (G₁ : Set Ω)) (h₂ : t ∈ Subgroup.normalizer (G₂ : Set Ω)) :
    t ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup Ω) : Set Ω) := by
  have key : ∀ s ∈ Subgroup.normalizer (G₁ : Set Ω), s ∈ Subgroup.normalizer (G₂ : Set Ω) →
      ∀ n ∈ G₁ ⊔ G₂, s * n * s⁻¹ ∈ G₁ ⊔ G₂ := by
    intro s hs₁ hs₂
    have hle : G₁ ⊔ G₂ ≤ (G₁ ⊔ G₂).comap (MulAut.conj s).toMonoidHom := by
      refine sup_le (fun g hg => ?_) (fun g hg => ?_)
      · exact le_sup_left (a := G₁) (b := G₂) ((Subgroup.mem_normalizer_iff.mp hs₁ g).mp hg)
      · exact le_sup_right (a := G₁) (b := G₂) ((Subgroup.mem_normalizer_iff.mp hs₂ g).mp hg)
    exact fun n hn => hle hn
  rw [Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨fun hn => key t h₁ h₂ n hn, fun hn => ?_⟩
  have := key t⁻¹ (Subgroup.inv_mem _ h₁) (Subgroup.inv_mem _ h₂) _ hn
  simpa [mul_assoc] using this

theorem le_or_le_of_sup_eq {J K G₁ G₂ : Subgroup Ω} (hsup : G₁ ⊔ G₂ = J)
    (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) (hKJ : K ≤ J)
    (hn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hK : CFSG.IsQuasisimple ↥K) :
    K ≤ G₁ ∨ K ≤ G₂ := by
  have hcomm' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  subst hsup
  have hn₁ := conj_mem_of_mem_sup_of_commute hcomm
  have hn₂ : ∀ x ∈ G₁ ⊔ G₂, ∀ g ∈ G₂, x * g * x⁻¹ ∈ G₂ := by
    rw [sup_comm]
    exact conj_mem_of_mem_sup_of_commute hcomm'
  exact le_or_le_of_commute hK hKJ
    (fun g hg k hk => hn g (le_sup_left (a := G₁) (b := G₂) hg) k hk)
    (fun g hg k hk => hn g (le_sup_right (a := G₁) (b := G₂) hg) k hk)
    (fun k hk g hg => hn₁ k (hKJ hk) g hg) (fun k hk g hg => hn₂ k (hKJ hk) g hg)

theorem le_or_le_of_sup_zpowers {J K G₁ G₂ : Subgroup Ω} {t : Ω}
    (hJt : J = (G₁ ⊔ G₂) ⊔ Subgroup.zpowers t) (hcomm : ∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a)
    (ht₁ : t ∈ Subgroup.normalizer (G₁ : Set Ω)) (ht₂ : t ∈ Subgroup.normalizer (G₂ : Set Ω))
    (hKJ : K ≤ J) (hn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hK : CFSG.IsQuasisimple ↥K) :
    K ≤ G₁ ∨ K ≤ G₂ := by
  subst hJt
  have hcomm' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hcomm b hb a ha).symm
  have htN : t ∈ Subgroup.normalizer ((G₁ ⊔ G₂ : Subgroup Ω) : Set Ω) := mem_normalizer_sup ht₁ ht₂
  have hNJ : G₁ ⊔ G₂ ≤ (G₁ ⊔ G₂) ⊔ Subgroup.zpowers t := le_sup_left
  have hKN : K ≤ G₁ ⊔ G₂ :=
    (le_commutator_of_perfect hKJ hK.1).trans (commutator_le_of_zpowers htN)
  have hconj : ∀ G' : Subgroup Ω, t ∈ Subgroup.normalizer (G' : Set Ω) →
      (∀ x ∈ G₁ ⊔ G₂, ∀ g ∈ G', x * g * x⁻¹ ∈ G') →
      ∀ x ∈ (G₁ ⊔ G₂) ⊔ Subgroup.zpowers t, ∀ g ∈ G', x * g * x⁻¹ ∈ G' := by
    intro G' ht hN x hx g hg
    obtain ⟨m, hm, s, hs, rfl⟩ :=
      (B19Aux.mem_sup_iff_of_le_normalizer (Subgroup.zpowers_le.2 htN)).1 hx
    have hz : Subgroup.zpowers t ≤ Subgroup.normalizer (G' : Set Ω) := Subgroup.zpowers_le.2 ht
    have e2 : m * s * g * (m * s)⁻¹ = m * (s * g * s⁻¹) * m⁻¹ := by group
    rw [e2]
    exact hN m hm _ ((Subgroup.mem_normalizer_iff.mp (hz hs) g).mp hg)
  have hn₁ := hconj G₁ ht₁ (conj_mem_of_mem_sup_of_commute hcomm)
  have hn₂ := hconj G₂ ht₂ (by rw [sup_comm]; exact conj_mem_of_mem_sup_of_commute hcomm')
  exact le_or_le_of_commute hK hKN
    (fun g hg k hk => hn g (hNJ (le_sup_left (a := G₁) (b := G₂) hg)) k hk)
    (fun g hg k hk => hn g (hNJ (le_sup_right (a := G₁) (b := G₂) hg)) k hk)
    (fun k hk g hg => hn₁ k (hKJ hk) g hg) (fun k hk g hg => hn₂ k (hKJ hk) g hg)

end CFSG.Quasithin.InternalSec
