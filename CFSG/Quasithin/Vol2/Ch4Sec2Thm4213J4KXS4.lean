module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXS3A

public section

namespace CFSG.Quasithin.H13.Ch4.J4KX

open CFSG.Open
open scoped commutatorElement

theorem step4_normalizer {Γ : Type} [Group Γ] [Finite Γ] {KΓ : Subgroup Γ} {z : Γ}
    (hKq : CFSG.IsQuasisimple ↥KΓ) (hKz : Nat.card ↥(Subgroup.center ↥KΓ) = 6)
    (E0 : Subgroup (↥KΓ ⧸ Subgroup.center ↥KΓ)) (hE0 : IsElemAbelian 3 E0)
    (hE0c : Nat.card E0 = 9)
    (hK0 : CFSG.Open.IsComponentOf KΓ ⊤)
    (hzKX : z ∈ KΓ) (hzc : ∀ k ∈ KΓ, z * k = k * z)
    (hpz : CFSG.Open.pRank 3 (Subgroup.centralizer ({z} : Set Γ)) ≤ 2) :
    ∀ g : Γ, g ∈ Subgroup.normalizer (KΓ : Set Γ) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsnK : KΓ.IsSubnormal := CFSG.Quasithin.A3.subnormal_top_iff.mp hK0.2.1
  obtain ⟨A₁, hA₁el, hA₁c⟩ := exists_e9_of_quotient (Subgroup.center ↥KΓ) E0 hE0 hE0c
  have hA₁'el : IsElemAbelian 3 (A₁.map KΓ.subtype) := isElemAbelian_map_aux hA₁el KΓ.subtype
  have hA₁'c : Nat.card (A₁.map KΓ.subtype) = 9 := by
    rw [Subgroup.card_map_of_injective KΓ.subtype_injective, hA₁c]
  have hA₁'le : A₁.map KΓ.subtype ≤ KΓ := Subgroup.map_subtype_le A₁
  have hZKc : Nat.card ((Subgroup.center ↥KΓ).map KΓ.subtype) = 6 := by
    rw [Subgroup.card_map_of_injective KΓ.subtype_injective, hKz]
  have hkey : ∀ g : Γ, CFSG.conjugate KΓ g = KΓ := by
    intro g
    by_contra hne
    have hK' : CFSG.Open.IsComponentOf (CFSG.conjugate KΓ g) ⊤ :=
      isComponentOf_top_conj hsnK hKq g
    have hcomm0 := CFSG.ComponentClassification.LocalComponents.commute_of_ne KΓ
      (CFSG.conjugate KΓ g) hK0 hK' (Ne.symm hne)
    have hcomm : ∀ k ∈ KΓ, ∀ k' ∈ CFSG.conjugate KΓ g, k * k' = k' * k := by
      intro k hk k' hk'
      have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm0 hk
      exact (Subgroup.mem_centralizer_iff.mp hle k' hk').symm
    have hA₂le : (A₁.map KΓ.subtype).map (MulAut.conj g⁻¹).toMonoidHom ≤ CFSG.conjugate KΓ g := by
      rintro _ ⟨a, ha, rfl⟩
      exact Subgroup.mem_map_of_mem _ (hA₁'le ha)
    have hA₂el : IsElemAbelian 3 ((A₁.map KΓ.subtype).map (MulAut.conj g⁻¹).toMonoidHom) :=
      isElemAbelian_map_aux hA₁'el _
    have hA₂c : Nat.card ((A₁.map KΓ.subtype).map (MulAut.conj g⁻¹).toMonoidHom) = 9 := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hA₁'c]
    have hD : (A₁.map KΓ.subtype) ⊓ ((A₁.map KΓ.subtype).map (MulAut.conj g⁻¹).toMonoidHom) ≤
        (Subgroup.center ↥KΓ).map KΓ.subtype := by
      intro d hd
      obtain ⟨hdA, hdA2⟩ := Subgroup.mem_inf.mp hd
      have hdK : d ∈ KΓ := hA₁'le hdA
      have hdK' : d ∈ CFSG.conjugate KΓ g := hA₂le hdA2
      have hmem : (⟨d, hdK⟩ : ↥KΓ) ∈ Subgroup.center ↥KΓ := by
        rw [Subgroup.mem_center_iff]
        intro k
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        exact hcomm k.1 k.2 d hdK'
      exact Subgroup.mem_map.mpr ⟨⟨d, hdK⟩, hmem, rfl⟩
    have hint : Nat.card ↥((A₁.map KΓ.subtype) ⊓
        ((A₁.map KΓ.subtype).map (MulAut.conj g⁻¹).toMonoidHom)) ≤ 3 := by
      have h9 : Nat.card ↥((A₁.map KΓ.subtype) ⊓
          ((A₁.map KΓ.subtype).map (MulAut.conj g⁻¹).toMonoidHom)) ∣ 9 := by
        have h := Subgroup.card_dvd_of_le (inf_le_left :
          (A₁.map KΓ.subtype) ⊓ ((A₁.map KΓ.subtype).map (MulAut.conj g⁻¹).toMonoidHom) ≤
            A₁.map KΓ.subtype)
        rwa [hA₁'c] at h
      have h6 : Nat.card ↥((A₁.map KΓ.subtype) ⊓
          ((A₁.map KΓ.subtype).map (MulAut.conj g⁻¹).toMonoidHom)) ∣ 6 := by
        have h := Subgroup.card_dvd_of_le hD
        rwa [hZKc] at h
      have hg : Nat.card ↥((A₁.map KΓ.subtype) ⊓
          ((A₁.map KΓ.subtype).map (MulAut.conj g⁻¹).toMonoidHom)) ∣ Nat.gcd 9 6 :=
        Nat.dvd_gcd h9 h6
      have h3 : Nat.gcd 9 6 = 3 := by norm_num
      rw [h3] at hg
      exact Nat.le_of_dvd (by norm_num) hg
    have hA₁C : A₁.map KΓ.subtype ≤ Subgroup.centralizer ({z} : Set Γ) := by
      intro a ha
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hzc a (hA₁'le ha)).symm
    have hA₂C : (A₁.map KΓ.subtype).map (MulAut.conj g⁻¹).toMonoidHom ≤
        Subgroup.centralizer ({z} : Set Γ) := by
      intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm z hzKX b (hA₂le hb)).symm
    have hcomm12 : ∀ a ∈ A₁.map KΓ.subtype,
        ∀ b ∈ (A₁.map KΓ.subtype).map (MulAut.conj g⁻¹).toMonoidHom, a * b = b * a :=
      fun a ha b hb => hcomm a (hA₁'le ha) b (hA₂le hb)
    exact false_of_two_E9 hpz hA₁C hA₂C hA₁'el hA₂el hA₁'c hA₂c hcomm12 hint
  intro g
  have hg := hkey g⁻¹
  apply normalizer_of_map_eq
  have h := hg
  unfold CFSG.conjugate at h
  rw [inv_inv] at h
  exact h

end CFSG.Quasithin.H13.Ch4.J4KX

end
