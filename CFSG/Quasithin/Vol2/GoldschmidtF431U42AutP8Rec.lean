module

public import CFSG.Quasithin.Background.I4Recognition

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

variable {X : Type} [Group X] [Finite X]

theorem psl3_two_or_alt_six_of_sylow
    (Q U : Subgroup X) (d : X) (m : ℕ) (hQ : Nat.card Q = 8 * m) (hm : Odd m) (hUQ : U ≤ Q)
    (hU8 : Nat.card U = 8) (hd : d ∈ U) (hd2 : d ^ 2 = 1) (hd1 : d ≠ 1)
    (hdc : ∀ x ∈ U, x * d = d * x) (hcen : ∀ x ∈ Q, x * d = d * x → x ∈ U)
    (hconj : ∀ y ∈ U, y ^ 2 = 1 → y ≠ 1 → ∃ q ∈ Q, q * d * q⁻¹ = y)
    (hUD : Nonempty (↥U ≃* DihedralGroup 4)) :
    Nonempty (↥Q ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) (ZMod 2)) ∨
      Nonempty (↥Q ≃* alternatingGroup (Fin 6)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdQ : d ∈ Q := hUQ hd
  let z0 : ↥Q := ⟨d, hdQ⟩
  have hz2 : z0 ^ 2 = 1 := Subtype.ext (by simpa using hd2)
  have hz1 : z0 ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hz : orderOf z0 = 2 := orderOf_eq_prime hz2 hz1
  have hU2 : IsPGroup 2 U := IsPGroup.of_card (n := 3) (by rw [hU8]; norm_num)
  let UQ : Subgroup ↥Q := U.subgroupOf Q
  have hUQcard : Nat.card UQ = 8 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUQ).toEquiv).trans hU8
  have hUQp : IsPGroup 2 UQ := IsPGroup.of_card (n := 3) (by rw [hUQcard]; norm_num)
  have hUQidx : UQ.index = m := by
    have h1 := Subgroup.card_mul_index UQ
    rw [hUQcard, hQ] at h1
    omega
  have hUQodd : ¬ 2 ∣ UQ.index := by
    rw [hUQidx]; exact Nat.two_dvd_ne_zero.2 (Nat.odd_iff.1 hm)
  let S : Sylow 2 ↥Q := hUQp.toSylow hUQodd
  have hS : (S : Subgroup ↥Q) = UQ := rfl
  have hconjz : ∀ u : ↥Q, orderOf u = 2 → IsConj z0 u := by
    intro u hu
    have hu2 : u ^ 2 = 1 := hu ▸ pow_orderOf_eq_one u
    have hu1 : u ≠ 1 := by
      intro h; rw [h, orderOf_one] at hu; norm_num at hu
    have hup : IsPGroup 2 (Subgroup.zpowers u) := by
      rw [IsPGroup.iff_card, Nat.card_zpowers, hu]; exact ⟨1, by simp⟩
    obtain ⟨P, hP⟩ := hup.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Q P S
    have hu' : g * u * g⁻¹ ∈ (S : Subgroup ↥Q) := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
      exact ⟨u, hP (Subgroup.mem_zpowers u), by simp [MulAut.conj_apply]⟩
    have hmemU : ((g * u * g⁻¹ : ↥Q) : X) ∈ U := by
      rw [hS] at hu'; exact Subgroup.mem_subgroupOf.1 hu'
    have hsq : (g * u * g⁻¹) ^ 2 = 1 := by
      calc (g * u * g⁻¹) ^ 2 = g * u ^ 2 * g⁻¹ := by rw [pow_two, pow_two]; group
        _ = 1 := by rw [hu2]; simp
    have hne : g * u * g⁻¹ ≠ 1 := by
      intro h; apply hu1
      calc u = g⁻¹ * (g * u * g⁻¹) * g := by group
        _ = 1 := by rw [h]; simp
    obtain ⟨q, hq, hqd⟩ := hconj _ hmemU (by simpa using congrArg Subtype.val hsq)
      (fun h => hne (Subtype.ext h))
    have hqz : (⟨q, hq⟩ : ↥Q) * z0 * (⟨q, hq⟩ : ↥Q)⁻¹ = g * u * g⁻¹ := Subtype.ext hqd
    refine isConj_iff.2 ⟨g⁻¹ * ⟨q, hq⟩, ?_⟩
    calc g⁻¹ * (⟨q, hq⟩ : ↥Q) * z0 * (g⁻¹ * (⟨q, hq⟩ : ↥Q))⁻¹
        = g⁻¹ * ((⟨q, hq⟩ : ↥Q) * z0 * (⟨q, hq⟩ : ↥Q)⁻¹) * g := by group
      _ = u := by rw [hqz]; group
  have hinv : ∀ u v : ↥Q, orderOf u = 2 → orderOf v = 2 → IsConj u v := fun u v hu hv =>
    (hconjz u hu).symm.trans (hconjz v hv)
  have hC : Nonempty (Subgroup.centralizer ({z0} : Set ↥Q) ≃* DihedralGroup 4) := by
    obtain ⟨e⟩ := hUD
    have hmem : ∀ x : ↥Q, x ∈ Subgroup.centralizer ({z0} : Set ↥Q) → (x : X) ∈ U := by
      intro x hx
      have := Subgroup.mem_centralizer_singleton_iff.1 hx
      exact hcen x x.2 (congrArg Subtype.val this)
    let F : Subgroup.centralizer ({z0} : Set ↥Q) ≃* ↥U :=
      { toFun := fun x => ⟨(x.1 : X), hmem x.1 x.2⟩
        invFun := fun u => ⟨⟨u.1, hUQ u.2⟩, Subgroup.mem_centralizer_singleton_iff.2
          (Subtype.ext (hdc u.1 u.2))⟩
        left_inv := fun x => rfl
        right_inv := fun u => rfl
        map_mul' := fun x y => rfl }
    exact ⟨F.trans e⟩
  exact CFSG.Quasithin.I4.lemma_I_4_1_two ↥Q hinv hz hC

end CFSG.Quasithin.H13.F431.U42Aut
