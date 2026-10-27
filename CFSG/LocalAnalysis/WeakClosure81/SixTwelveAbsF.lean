module

public import CFSG.CGT.Timmesfeld75.StrongClosure
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem exists_mul_mem_of_card_eq {T' T₁ Z : Subgroup X} (hZ : Z ≤ Subgroup.center X)
    (hT'Z : T' ⊓ Z = ⊥) (hT₁Z : T₁ ⊓ Z = ⊥) (hcard : Nat.card T₁ = Nat.card T')
    (hle : T₁ ≤ T' ⊔ Z) : ∀ t ∈ T', ∃ z ∈ Z, t * z ∈ T₁ := by
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  have hdecomp : ∀ s : T₁, ∃ y : T', ∃ z : Z, (y : X) * (z : X) = (s : X) := by
    intro s
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp (hle s.2)
    exact ⟨⟨y, hy⟩, ⟨z, hz⟩, hyz⟩
  choose F G hG using hdecomp
  have hfinj : Function.Injective F := by
    intro s s' hFF
    have hFF' : (F s : X) = (F s' : X) := congrArg Subtype.val hFF
    have h1 : (s : X)⁻¹ * (s' : X) = (G s : X)⁻¹ * (G s' : X) := by
      calc (s : X)⁻¹ * (s' : X)
          = ((F s : X) * (G s : X))⁻¹ * ((F s' : X) * (G s' : X)) := by
            rw [hG s, hG s']
        _ = (G s : X)⁻¹ * (G s' : X) := by rw [hFF']; group
    have hmemT₁ : (s : X)⁻¹ * (s' : X) ∈ T₁ := T₁.mul_mem (T₁.inv_mem s.2) s'.2
    have hmemZ : (G s : X)⁻¹ * (G s' : X) ∈ Z := Z.mul_mem (Z.inv_mem (G s).2) (G s').2
    rw [← h1] at hmemZ
    have hbot : (s : X)⁻¹ * (s' : X) ∈ (⊥ : Subgroup X) := by
      have h2 : (s : X)⁻¹ * (s' : X) ∈ T₁ ⊓ Z := Subgroup.mem_inf.2 ⟨hmemT₁, hmemZ⟩
      rwa [hT₁Z] at h2
    rw [Subgroup.mem_bot] at hbot
    exact Subtype.ext (eq_of_inv_mul_eq_one hbot)
  have hbij : Function.Bijective F := hfinj.bijective_of_nat_card_le hcard.symm.le
  intro t ht
  obtain ⟨s, hs⟩ := hbij.2 ⟨t, ht⟩
  refine ⟨(G s : X), (G s).2, ?_⟩
  have hFs : (F s : X) = t := congrArg Subtype.val hs
  have hGs := hG s
  rw [hFs] at hGs
  rw [hGs]
  exact s.2

theorem le_of_exists_mul_mem {T' T₁ Z : Subgroup X} (hT'el : IsElemAbelian 2 T')
    (hZ : Z ≤ Subgroup.center X) (hT'Z : T' ⊓ Z = ⊥) (hT₁Z : T₁ ⊓ Z = ⊥)
    (h4 : 4 ≤ Nat.card T')
    (hconj : ∀ t ∈ T', t ≠ 1 → ∀ t' ∈ T', t' ≠ 1 → ∃ g : X, g * t * g⁻¹ = t')
    (hstrong : StrongWC T₁) (hsurj : ∀ t ∈ T', ∃ z ∈ Z, t * z ∈ T₁) : T' ≤ T₁ := by
  have hc : ∀ z ∈ Z, ∀ x : X, x * z = z * x :=
    fun z hz x => (Subgroup.mem_center_iff.1 (hZ hz)) x
  have htz_ne : ∀ t ∈ T', t ≠ 1 → ∀ z ∈ Z, t * z ≠ 1 := by
    intro t ht ht1 z hz h
    have ht_eq : t = z⁻¹ := eq_inv_of_mul_eq_one_left h
    have htZ : t ∈ Z := by rw [ht_eq]; exact Z.inv_mem hz
    have hmem : t ∈ T' ⊓ Z := Subgroup.mem_inf.2 ⟨ht, htZ⟩
    rw [hT'Z] at hmem
    exact ht1 hmem
  have hA : ∀ t ∈ T', t ≠ 1 → ∀ t' ∈ T', t' ≠ 1 → ∀ z ∈ Z,
      t * z ∈ T₁ → t' * z ∈ T₁ := by
    intro t ht ht1 t' ht' ht'1 z hz htz
    obtain ⟨g, hg⟩ := hconj t ht ht1 t' ht' ht'1
    have hkey : g * (t * z) * g⁻¹ = t' * z := by
      calc g * (t * z) * g⁻¹ = g * t * (z * g⁻¹) := by group
        _ = g * t * (g⁻¹ * z) := by rw [← hc z hz g⁻¹]
        _ = (g * t * g⁻¹) * z := by group
        _ = t' * z := by rw [hg]
    have hcomm : Commute (t' * z) (t * z) :=
      Commute.mul_right (Commute.mul_left (hT'el.comm ht' ht) (hc z hz t).symm)
        (Commute.mul_left (hc z hz t') (Commute.refl z))
    have hmem : (g⁻¹)⁻¹ * (t * z) * g⁻¹ ∈ Subgroup.centralizer ({t * z} : Set X) := by
      rw [inv_inv, hkey, Subgroup.mem_centralizer_singleton_iff]
      exact hcomm.eq
    have happ := hstrong.2 (t * z) htz (htz_ne t ht ht1 z hz) (t * z) htz g⁻¹ hmem
    rwa [inv_inv, hkey] at happ
  have ht₁ex : ∃ t ∈ T', t ≠ 1 := by
    have hne : T' ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at h4
      omega
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    exact ⟨(a : X), a.2, fun h => ha1 (Subtype.ext h)⟩
  obtain ⟨t₁, ht₁, ht₁1⟩ := ht₁ex
  obtain ⟨c, hcz, hcT₁⟩ := hsurj t₁ ht₁
  have htwo : ∃ t₂ ∈ T', t₂ ≠ 1 ∧ t₂ ≠ t₁ := by
    by_contra hcon
    have hsub : (T' : Set X) ⊆ ({1, t₁} : Set X) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      by_cases hx1 : x = 1
      · exact Or.inl hx1
      · by_cases hxt : x = t₁
        · exact Or.inr hxt
        · exact absurd ⟨x, hx, hx1, hxt⟩ hcon
    have hcard2 : Nat.card T' ≤ 2 := by
      have h1 : Nat.card T' = (T' : Set X).ncard := rfl
      rw [h1]
      calc (T' : Set X).ncard ≤ ({1, t₁} : Set X).ncard := Set.ncard_le_ncard hsub
        _ ≤ 2 := by
          have h := Set.ncard_insert_le (1 : X) ({t₁} : Set X)
          rw [Set.ncard_singleton] at h
          simpa using h
    omega
  obtain ⟨t₂, ht₂, ht₂1, ht₂ne⟩ := htwo
  have ht₁t₂ : t₁ * t₂ ∈ T' := T'.mul_mem ht₁ ht₂
  have ht₁t₂1 : t₁ * t₂ ≠ 1 := by
    intro h
    apply ht₂ne
    have h2 : t₂ = t₁⁻¹ := eq_inv_of_mul_eq_one_right h
    have h3 : t₁⁻¹ = t₁ := inv_eq_of_mul_eq_one_right (hT'el.mul_self_eq_one ht₁)
    rw [h2, h3]
  have h2mem : t₂ * c ∈ T₁ := hA t₁ ht₁ ht₁1 t₂ ht₂ ht₂1 c hcz hcT₁
  have h3mem : (t₁ * t₂) * c ∈ T₁ :=
    hA t₁ ht₁ ht₁1 (t₁ * t₂) ht₁t₂ ht₁t₂1 c hcz hcT₁
  have hcmem : c ∈ T₁ := by
    have hprod : ((t₁ * t₂) * c)⁻¹ * ((t₁ * c) * (t₂ * c)) ∈ T₁ :=
      T₁.mul_mem (T₁.inv_mem h3mem) (T₁.mul_mem hcT₁ h2mem)
    have hceq : ((t₁ * t₂) * c)⁻¹ * ((t₁ * c) * (t₂ * c)) = c := by
      have h1 : (t₁ * c) * (t₂ * c) = ((t₁ * t₂) * c) * c := by
        calc (t₁ * c) * (t₂ * c) = t₁ * (c * t₂) * c := by group
          _ = t₁ * (t₂ * c) * c := by rw [← hc c hcz t₂]
          _ = ((t₁ * t₂) * c) * c := by group
      rw [h1]
      group
    rw [hceq] at hprod
    exact hprod
  have hc1 : c = 1 := by
    have hmem : c ∈ T₁ ⊓ Z := Subgroup.mem_inf.2 ⟨hcmem, hcz⟩
    rw [hT₁Z] at hmem
    exact hmem
  intro t ht
  by_cases ht1 : t = 1
  · rw [ht1]; exact T₁.one_mem
  · have hmem := hA t₁ ht₁ ht₁1 t ht ht1 c hcz hcT₁
    rw [hc1] at hmem
    simpa using hmem

theorem eq_of_le_sup_central {T' T₁ Z : Subgroup X} (hT'el : IsElemAbelian 2 T')
    (hZ : Z ≤ Subgroup.center X) (hT'Z : T' ⊓ Z = ⊥) (hT₁Z : T₁ ⊓ Z = ⊥)
    (hcard : Nat.card T₁ = Nat.card T') (h4 : 4 ≤ Nat.card T') (hle : T₁ ≤ T' ⊔ Z)
    (hconj : ∀ t ∈ T', t ≠ 1 → ∀ t' ∈ T', t' ≠ 1 → ∃ g : X, g * t * g⁻¹ = t')
    (hstrong : StrongWC T₁) : T₁ = T' :=
  (Subgroup.eq_of_le_of_card_ge
    (le_of_exists_mul_mem hT'el hZ hT'Z hT₁Z h4 hconj hstrong
      (exists_mul_mem_of_card_eq hZ hT'Z hT₁Z hcard hle)) hcard.le).symm

end CFSG.LocalAnalysis.WeakClosure81
