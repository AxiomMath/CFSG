module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG.Quasithin

namespace SBd

section Perm3

theorem perm_three_aut_inner (α : MulAut (Equiv.Perm (Fin 3))) :
    ∃ g : Equiv.Perm (Fin 3), ∀ x, α x = g * x * g⁻¹ := by
  let a : Equiv.Perm (Fin 3) := Equiv.swap 0 1
  let c : Equiv.Perm (Fin 3) := Equiv.swap 0 1 * Equiv.swap 1 2
  have hall : ∀ x : Equiv.Perm (Fin 3), ∃ (i : Fin 2) (j : Fin 3), x = c ^ (j : ℕ) * a ^ (i : ℕ) := by
    decide
  have hrel : ∀ p q : Equiv.Perm (Fin 3),
      (p * p = 1 ∧ q * q * q = 1 ∧ p ≠ 1 ∧ q ≠ 1 ∧ p * q * p⁻¹ = q⁻¹) →
        ∃ g : Equiv.Perm (Fin 3), g * a * g⁻¹ = p ∧ g * c * g⁻¹ = q := by
    decide
  have ha2 : a * a = 1 := by decide
  have hc3 : c * c * c = 1 := by decide
  have ha1 : a ≠ 1 := by decide
  have hc1 : c ≠ 1 := by decide
  have hac : a * c * a⁻¹ = c⁻¹ := by decide
  have h1 : α a * α a = 1 := by rw [← map_mul, ha2, map_one]
  have h2 : α c * α c * α c = 1 := by rw [← map_mul, ← map_mul, hc3, map_one]
  have h3 : α a ≠ 1 := fun h => ha1 (α.injective (by rw [h, map_one]))
  have h4 : α c ≠ 1 := fun h => hc1 (α.injective (by rw [h, map_one]))
  have h5 : α a * α c * (α a)⁻¹ = (α c)⁻¹ := by rw [← map_inv, ← map_mul, ← map_mul, hac, map_inv]
  obtain ⟨g, hga, hgc⟩ := hrel _ _ ⟨h1, h2, h3, h4, h5⟩
  refine ⟨g, fun x => ?_⟩
  obtain ⟨i, j, rfl⟩ := hall x
  rw [map_mul, map_pow, map_pow, ← hga, ← hgc, conj_pow, conj_pow]
  group

noncomputable def conjEquivPerm3 : Equiv.Perm (Fin 3) ≃* MulAut (Equiv.Perm (Fin 3)) :=
  MulEquiv.ofBijective (MulAut.conj : Equiv.Perm (Fin 3) →* MulAut (Equiv.Perm (Fin 3)))
    ⟨by
      rw [injective_iff_map_eq_one]
      intro g hg
      have hcen : ∀ g : Equiv.Perm (Fin 3), (∀ x, g * x * g⁻¹ = x) → g = 1 := by decide
      exact hcen g fun x => by simpa using congrArg (fun α : MulAut (Equiv.Perm (Fin 3)) => α x) hg,
     fun α => by
      obtain ⟨g, hg⟩ := perm_three_aut_inner α
      exact ⟨g, MulEquiv.ext fun x => by simp [hg x]⟩⟩

theorem conjEquivPerm3_apply (g x : Equiv.Perm (Fin 3)) :
    conjEquivPerm3 g x = g * x * g⁻¹ := by
  show (MulAut.conj g) x = g * x * g⁻¹
  simp [MulAut.conj_apply]

theorem exists_hom_extending_perm_three {Q : Type*} [Group Q] (K : Subgroup Q) [K.Normal]
    (e : K ≃* Equiv.Perm (Fin 3)) :
    ∃ ψ : Q →* Equiv.Perm (Fin 3), ∀ k : K, ψ (k : Q) = e k := by
  let κ : Q →* MulAut K := MulAut.conjNormal
  let ψ : Q →* Equiv.Perm (Fin 3) :=
    (conjEquivPerm3.symm).toMonoidHom.comp ((MulAut.congr e).toMonoidHom.comp κ)
  refine ⟨ψ, fun k => ?_⟩
  have h : MulAut.congr e (κ (k : Q)) = conjEquivPerm3 (e k) := by
    refine MulEquiv.ext fun x => ?_
    rw [conjEquivPerm3_apply]
    show e (κ (k : Q) (e.symm x)) = e k * x * (e k)⁻¹
    have h1 : κ (k : Q) (e.symm x) = k * e.symm x * k⁻¹ :=
      Subtype.ext (by simp [κ, MulAut.conjNormal_apply])
    rw [h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  show conjEquivPerm3.symm (MulAut.congr e (κ (k : Q))) = e k
  rw [h, MulEquiv.symm_apply_apply]

theorem mem_zpowers_involution {K : Type*} [Group K] {s : K} (hs : s * s = 1) {x : K}
    (hx : x ∈ Subgroup.zpowers s) : x = 1 ∨ x = s := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have h2 : s ^ 2 = 1 := by rw [pow_two]; exact hs
  have : s ^ k = s ^ (k % 2) := by
    conv_lhs => rw [← Int.emod_add_mul_ediv k 2]
    rw [zpow_add, zpow_mul]
    simp [h2]
  rw [this]
  have hk : k % 2 = 0 ∨ k % 2 = 1 := by omega
  rcases hk with h | h <;> simp [h]

theorem nonempty_mulEquiv_perm_three_of_card_six {K : Type*} [Group K] [Finite K]
    (h6 : Nat.card K = 6) (hnc : ∃ x y : K, x * y ≠ y * x) :
    Nonempty (K ≃* Equiv.Perm (Fin 3)) := by
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s, hs⟩ := exists_prime_orderOf_dvd_card' 2 (by rw [h6]; norm_num : 2 ∣ Nat.card K)
  have hss : s * s = 1 := by rw [← pow_two]; exact hs ▸ pow_orderOf_eq_one s
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    omega
  set Hs : Subgroup K := Subgroup.zpowers s with hHs
  have hcardHs : Nat.card Hs = 2 := by rw [hHs, Nat.card_zpowers, hs]
  have hidx : Hs.index = 3 := by
    have := Hs.card_mul_index
    rw [hcardHs, h6] at this
    omega
  let π : K →* Equiv.Perm (K ⧸ Hs) := MulAction.toPermHom K (K ⧸ Hs)
  have hinj : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro x hx
    by_contra hx1
    have hker : Hs.normalCore = π.ker := Subgroup.normalCore_eq_ker Hs
    have hxcore : x ∈ Hs.normalCore := by rw [hker]; exact hx
    have hxH : x ∈ Hs := Subgroup.normalCore_le Hs hxcore
    have hxs : x = s := (mem_zpowers_involution hss hxH).resolve_left hx1
    have hscen : ∀ g : K, g * s * g⁻¹ = s := by
      intro g
      have hmem : g * s * g⁻¹ ∈ Hs.normalCore := by
        have := hxs ▸ hxcore
        exact (Subgroup.normalCore_normal Hs).conj_mem s this g
      have hmemH : g * s * g⁻¹ ∈ Hs := Subgroup.normalCore_le Hs hmem
      have hne : g * s * g⁻¹ ≠ 1 := fun h => hs1 (by
        have e : s = g⁻¹ * (g * s * g⁻¹) * g := by group
        rw [h] at e
        simpa using e)
      exact (mem_zpowers_involution hss hmemH).resolve_left hne
    have hsZ : s ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := hscen g
      calc g * s = g * s * g⁻¹ * g := by group
        _ = s * g := by rw [this]
    have hHsZ : Hs ≤ Subgroup.center K := (Subgroup.zpowers_le).mpr hsZ
    have hdvd : (Subgroup.center K).index ∣ 3 := hidx ▸ Subgroup.index_dvd_of_le hHsZ
    have hcyc : IsCyclic (K ⧸ Subgroup.center K) := isCyclic_of_card_dvd_prime (p := 3) hdvd
    obtain ⟨a, b, hab⟩ := hnc
    exact hab ((MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (QuotientGroup.mk' (Subgroup.center K)) (by rw [QuotientGroup.ker_mk'])).is_comm.comm a b)
  have hcardQ : Nat.card (K ⧸ Hs) = 3 := hidx
  have hbij : Function.Bijective π := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_perm, hcardQ, h6]
    decide
  let e₁ : K ≃* Equiv.Perm (K ⧸ Hs) := MulEquiv.ofBijective π hbij
  have hex : Nonempty ((K ⧸ Hs) ≃ Fin 3) :=
    ⟨(Finite.equivFin (K ⧸ Hs)).trans (finCongr hcardQ)⟩
  obtain ⟨f⟩ := hex
  exact ⟨e₁.trans (Equiv.permCongrHom f)⟩

theorem exists_mulEquiv_perm_three_prod {Q : Type*} [Group Q] [Finite Q]
    (ψ : Q →* Equiv.Perm (Fin 3)) (hψ : Function.Surjective ψ) (hcard : Nat.card Q ≤ 36)
    {z r : Q} (hzK : ψ z = 1) (hrK : ψ r = 1) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1) (hr2 : r ^ 2 = 1)
    (hr1 : r ≠ 1) (hnc : z * r ≠ r * z) :
    Nonempty (Q ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)) := by
  have hp2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  set K : Subgroup Q := ψ.ker with hK
  have hKcard : Nat.card K * 6 = Nat.card Q := by
    have := Subgroup.card_ker_mul_card_of_surjective hψ
    rwa [hcard6] at this
  have hzmem : z ∈ K := hzK
  have hrmem : r ∈ K := hrK
  have h3dvd : 3 ∣ Nat.card K := by
    have hz3' : orderOf z = 3 := orderOf_eq_prime hz3 hz1
    have := orderOf_dvd_natCard (⟨z, hzmem⟩ : K)
    rwa [Subgroup.orderOf_mk, hz3'] at this
  have h2dvd : 2 ∣ Nat.card K := by
    have hr2' : orderOf r = 2 := orderOf_eq_prime hr2 hr1
    have := orderOf_dvd_natCard (⟨r, hrmem⟩ : K)
    rwa [Subgroup.orderOf_mk, hr2'] at this
  have h6dvd : 6 ∣ Nat.card K :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2dvd h3dvd
  have hKle : Nat.card K ≤ 6 := by omega
  have hK6 : Nat.card K = 6 := le_antisymm hKle (Nat.le_of_dvd Nat.card_pos h6dvd)
  have hnc' : ∃ x y : K, x * y ≠ y * x :=
    ⟨⟨z, hzmem⟩, ⟨r, hrmem⟩, fun h => hnc (congrArg Subtype.val h)⟩
  obtain ⟨eK⟩ := nonempty_mulEquiv_perm_three_of_card_six hK6 hnc'
  have hKn : K.Normal := ψ.normal_ker
  obtain ⟨ψ₁, hψ₁⟩ := exists_hom_extending_perm_three K eK
  let φ : Q →* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3) := ψ₁.prod ψ
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have h1 : ψ₁ q = 1 := congrArg Prod.fst hq
    have h2 : ψ q = 1 := congrArg Prod.snd hq
    have hqK : q ∈ K := h2
    have h3 : eK ⟨q, hqK⟩ = 1 := by rw [← hψ₁ ⟨q, hqK⟩]; exact h1
    have h4 : (⟨q, hqK⟩ : K) = 1 := eK.injective (by rw [h3, map_one])
    exact congrArg Subtype.val h4
  have hbij : Function.Bijective φ := by
    refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_prod, hcard6]
    omega
  exact ⟨MulEquiv.ofBijective φ hbij⟩

theorem eq_one_of_inv_of_commutator_pow {Qs : Type*} [Group Qs] {z ρ : Qs} (hz3 : z ^ 3 = 1)
    (hρ : ρ * z * ρ⁻¹ = z⁻¹) {k : ℕ} (hk : (z * ρ * z⁻¹ * ρ⁻¹) ^ 2 ^ k = 1) : z = 1 := by
  have h1 : z * ρ * z⁻¹ * ρ⁻¹ = z ^ 2 := by
    calc z * ρ * z⁻¹ * ρ⁻¹ = z * (ρ * z * ρ⁻¹)⁻¹ := by group
      _ = z ^ 2 := by rw [hρ, inv_inv, pow_two]
  rw [h1, ← pow_mul, ← pow_succ'] at hk
  have h2 : orderOf z ∣ 2 ^ (k + 1) := orderOf_dvd_of_pow_eq_one hk
  have h3 : orderOf z ∣ 3 := orderOf_dvd_of_pow_eq_one hz3
  have hcop : Nat.Coprime (2 ^ (k + 1)) 3 := Nat.Coprime.pow_left (k + 1) (by norm_num)
  exact orderOf_eq_one_iff.mp
    (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h2 hcop) h3)

end Perm3

end SBd

end CFSG.Quasithin
