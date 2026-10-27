module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Shape
public import CFSG.GroupTheory.CentreOfMassModulo
public import CFSG.Quasithin.Recognition.Stroth.Str83G4C22

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str83G4_commutator_x_h_le_n
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) :
    ⁅str83X L1 L2 S, L1 ⊔ S⁆ ≤ str83N L1 L2 S := by
  have hH : L1 ⊔ S = oTwoUpper (L1 ⊔ S) ⊔ Q1 L1 L2 S :=
    (str83G4_oTwoUpper_sup_left hfr d).symm
  have hQ1N : Q1 L1 L2 S ≤ Subgroup.normalizer (oTwoUpper (L1 ⊔ S) : Set G) :=
    (str83G4_q1_le_s hfr).trans ((le_sup_right : S ≤ L1 ⊔ S).trans
      (CFSG.Quasithin.le_normalizer_oTwoUpper (L1 ⊔ S)))
  have hNH : L1 ⊔ S ≤ Subgroup.normalizer (str83N L1 L2 S : Set G) :=
    D14.le_normalizer_of_isNormalIn (str83N_normal hfr)
  refine Subgroup.commutator_le.mpr fun x hx h hh => ?_
  have hmem : h ∈ oTwoUpper (L1 ⊔ S) ⊔ Q1 L1 L2 S := by rw [← hH]; exact hh
  obtain ⟨g, hg, q, hq, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hQ1N).mp hmem
  have h1 : ⁅x, g⁆ ∈ str83N L1 L2 S := by
    have := Subgroup.commutator_mem_commutator hx hg
    exact (show ⁅str83X L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ ≤ str83N L1 L2 S from le_sup_left) this
  have h2 : ⁅x, q⁆ ∈ Z1 L1 L2 S :=
    str83G4_commutator_x_q1_le hfr (Subgroup.commutator_mem_commutator hx hq)
  have hgH : g ∈ L1 ⊔ S := (oTwoUpper_le (L1 ⊔ S)) hg
  have h3 : g * ⁅x, q⁆ * g⁻¹ ∈ str83N L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (hNH hgH) _).mp (str83Z1_le_n L1 L2 S h2)
  have h4 : ⁅x, g * q⁆ = ⁅x, g⁆ * (g * ⁅x, q⁆ * g⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [h4]
  exact (str83N L1 L2 S).mul_mem h1 h3

theorem str83G4_z2_le_n_sup_x1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S)) :
    Z2 L1 L2 S ≤ str83N L1 L2 S ⊔ str83X1 L1 L2 S := by
  intro z hzZ2
  have hzX : z ∈ str83X L1 L2 S := z2_le_str83X L1 L2 S hzZ2
  have hSyl := str83G4_isSylowTwoOf_sup_left (a := a) hfr
  have hodd : Odd (S.subgroupOf (L1 ⊔ S)).index := by
    have h2 : ¬ 2 ∣ (S.subgroupOf (L1 ⊔ S)).index := hSyl.2.2
    exact Nat.not_even_iff_odd.mp (by rwa [even_iff_two_dvd])
  have hA : ∀ a ∈ str83N L1 L2 S, a * a = 1 := fun a ha => by
    simpa [pow_two] using (CFSG.Quasithin.B6.isElemAbelian_iff.mp hX).2 a (str83N_le_x hfr ha)
  have hAc : ∀ a ∈ str83N L1 L2 S, ∀ b ∈ str83N L1 L2 S, a * b = b * a := fun a ha b hb =>
    (CFSG.Quasithin.B6.isElemAbelian_iff.mp hX).1 a (str83N_le_x hfr ha) b (str83N_le_x hfr hb)
  have hZA : Z1 L1 L2 S ≤ str83N L1 L2 S := str83Z1_le_n L1 L2 S
  have hXA : ∀ x ∈ L1 ⊔ S, ∀ a ∈ str83N L1 L2 S, x * a * x⁻¹ ∈ str83N L1 L2 S := by
    intro x hx a ha
    exact (Subgroup.mem_normalizer_iff.mp
      (D14.le_normalizer_of_isNormalIn (str83N_normal hfr) hx) a).mp ha
  have hXZ : ∀ x ∈ L1 ⊔ S, ∀ c ∈ Z1 L1 L2 S, x * c * x⁻¹ ∈ Z1 L1 L2 S := by
    intro x hx c hc
    exact (Subgroup.mem_normalizer_iff.mp (str83G4_sup_le_normalizer_z1 hfr hx) c).mp hc
  have hu : ∀ x ∈ L1 ⊔ S, z⁻¹ * (x * z * x⁻¹) ∈ str83N L1 L2 S := by
    intro x hx
    have h1 : ⁅z⁻¹, x⁆ ∈ ⁅str83X L1 L2 S, L1 ⊔ S⁆ :=
      Subgroup.commutator_mem_commutator
        (z2_le_str83X L1 L2 S ((Z2 L1 L2 S).inv_mem hzZ2)) hx
    have h2 : ⁅z⁻¹, x⁆ ∈ str83N L1 L2 S := str83G4_commutator_x_h_le_n hfr d h1
    simpa [commutatorElement_def, mul_assoc] using h2
  have hS : ∀ s ∈ S.subgroupOf (L1 ⊔ S), z⁻¹ * ((s : G) * z * (s : G)⁻¹) ∈ Z1 L1 L2 S := by
    intro s hs
    have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
    have h1 : ⁅z⁻¹, (s : G)⁆ ∈ ⁅Z2 L1 L2 S, S⁆ :=
      Subgroup.commutator_mem_commutator ((Z2 L1 L2 S).inv_mem hzZ2) hsS
    rw [str83G4_commutator_z2_s hfr] at h1
    simpa [commutatorElement_def, mul_assoc] using h1
  obtain ⟨a, haN, hfix⟩ :=
    CFSG.GroupTheory.exists_fixed_mod_of_odd_index hA hAc hZA hXA hXZ hu hS hodd
  have hyaX : z * a ∈ str83X L1 L2 S := (str83X L1 L2 S).mul_mem hzX (str83N_le_x hfr haN)
  have hyaN : z * a ∈ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    str83G4_sup_le_normalizer_z1 hfr (str83G4_x_le_sup hfr hyaX)
  have hyaZ : ∀ h ∈ L1 ⊔ S, (z * a) * h * (z * a)⁻¹ * h⁻¹ ∈ Z1 L1 L2 S := by
    intro h hh
    let e : G := (z * a)⁻¹ * (h * (z * a) * h⁻¹)
    have he : e ∈ Z1 L1 L2 S := hfix h hh
    have hone : (z * a) * h * (z * a)⁻¹ * h⁻¹ = (z * a) * e⁻¹ * (z * a)⁻¹ := by
      simp only [e]
      group
    have hye : (z * a) * e⁻¹ = e⁻¹ * (z * a) :=
      (CFSG.Quasithin.B6.isElemAbelian_iff.mp hX).1 (z * a) hyaX (e⁻¹)
        (str83G4_z1_le_x hfr ((Z1 L1 L2 S).inv_mem he))
    rw [hone, hye, mul_assoc, mul_inv_cancel, mul_one]
    exact (Z1 L1 L2 S).inv_mem he
  have hyaX1 : z * a ∈ str83X1 L1 L2 S := by
    rw [mem_str83X1]
    exact ⟨hyaX, hyaN, hyaZ⟩
  have hz : z = (z * a) * a⁻¹ := by group
  rw [hz]
  exact (str83N L1 L2 S ⊔ str83X1 L1 L2 S).mul_mem
    (Subgroup.mem_sup_right hyaX1) (Subgroup.mem_sup_left ((str83N L1 L2 S).inv_mem haN))

theorem str83G4_x_eq_n_sup_x1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S)) :
    str83X L1 L2 S = str83N L1 L2 S ⊔ str83X1 L1 L2 S := by
  refine le_antisymm ?_ (sup_le (str83N_le_x hfr) (str83G4_x1_le_x L1 L2 S))
  have hZ2K : Z2 L1 L2 S ≤ str83N L1 L2 S ⊔ str83X1 L1 L2 S :=
    str83G4_z2_le_n_sup_x1 hfr d hX
  have hHK : L1 ⊔ S ≤ Subgroup.normalizer
      (((str83N L1 L2 S ⊔ str83X1 L1 L2 S : Subgroup G)) : Set G) :=
    D14.le_normalizer_sup
      (D14.le_normalizer_of_isNormalIn (str83N_normal hfr))
      (D14.le_normalizer_of_isNormalIn (str83G4_x1_normal hfr))
  have hbigB : bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) := by
    have hB1 : borelOf L1 S ≤ Subgroup.normalizer (L1 : Set G) := by
      intro x hx
      exact Subgroup.le_normalizer ((F1.borelOf_le L1 S) hx)
    have hB2 : borelOf L2 S ≤ Subgroup.normalizer (L1 : Set G) := hfr.1.1.1.borel_le
    have hS : S ≤ Subgroup.normalizer (L1 : Set G) := hfr.1.1.1.normalizes
    exact sup_le (sup_le hB1 hB2) hS
  rw [show str83X L1 L2 S = CFSG.Quasithin.conjClosure (Z2 L1 L2 S) (P1 L1 L2 S) from rfl]
  refine CFSG.Quasithin.conjClosure_le ?_
  intro h hhP1 z hzZ2
  obtain ⟨l, hl, b, hb, rfl⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hbigB).mp hhP1
  have hbZ2 : b * z * b⁻¹ ∈ Z2 L1 L2 S :=
    (Subgroup.mem_normalizer_iff.mp (bigB_le_normalizer_z2 L1 L2 S hb) z).mp hzZ2
  have hK : l ∈ Subgroup.normalizer
      (((str83N L1 L2 S ⊔ str83X1 L1 L2 S : Subgroup G)) : Set G) :=
    hHK (Subgroup.mem_sup_left hl)
  simpa [mul_assoc] using (Subgroup.mem_normalizer_iff.mp hK (b * z * b⁻¹)).mp (hZ2K hbZ2)

private theorem isChiefStep_of_inf_chief {H U X X1 N N1 : Subgroup G}
    (hXeq : X = N ⊔ X1) (hN1eq : N1 = N ⊓ X1) (hX1n : IsNormalIn H U X1)
    (hXn : IsNormalIn H U X) (hlt : X1 < X) (hstepN : IsChiefStep H U N1 N)
    (hN1X1 : N1 ≤ X1) (hN1N : N1 ≤ N)
    (hNX1 : N ≤ Subgroup.normalizer (X1 : Set G)) :
    IsChiefStep H U X1 X := by
  refine ⟨hXn, hX1n, hlt, ?_⟩
  intro K hK hX1K hKX
  by_cases h1 : K = X1
  · exact Or.inl h1
  · refine Or.inr ?_
    have hmod : K = X1 ⊔ (K ⊓ N) := by
      refine le_antisymm ?_ (sup_le hX1K inf_le_left)
      intro k hk
      have hkX : k ∈ X := hKX hk
      have hkX' : k ∈ X1 ⊔ N := by
        rw [sup_comm, ← hXeq]
        exact hkX
      obtain ⟨a, haX1, b, hbN, hkab⟩ :=
        (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hNX1).mp hkX'
      rw [hkab]
      have hbK : b ∈ K := by
        have hb : b = a⁻¹ * k := by rw [hkab]; group
        rw [hb]
        exact K.mul_mem (K.inv_mem (hX1K haX1)) hk
      exact Subgroup.mul_mem_sup haX1 ⟨hbK, hbN⟩
    have hKNn : IsNormalIn H U (K ⊓ N) := F112W.isNormalIn_inf hK hstepN.1
    have hN1KN : N1 ≤ K ⊓ N := le_inf (hN1X1.trans hX1K) hN1N
    rcases hstepN.2.2.2 (K ⊓ N) hKNn hN1KN inf_le_right with h | h
    · exact absurd (by rw [hmod, h, sup_eq_left.mpr hN1X1] : K = X1) h1
    · rw [hmod, h, sup_comm, ← hXeq]

theorem str83G4_isChiefStep_x1_x
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (str83X1 L1 L2 S) (str83X L1 L2 S) := by
  have hx : str83X L1 L2 S = str83N L1 L2 S ⊔ str83X1 L1 L2 S :=
    str83G4_x_eq_n_sup_x1 hfr d hX
  have hstepN : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (str83N1 L1 L2 S) (str83N L1 L2 S) :=
    (str83G4_isChiefStep_n_n1 hfr d hX hB).1
  have hlt : str83X1 L1 L2 S < str83X L1 L2 S := by
    refine lt_of_le_of_ne (str83G4_x1_le_x L1 L2 S) fun heq => ?_
    have hNle : str83N L1 L2 S ≤ str83X1 L1 L2 S := heq ▸ str83N_le_x hfr
    exact (not_le_of_gt (str83N1_lt_n hfr hX)) (le_inf le_rfl hNle)
  exact isChiefStep_of_inf_chief hx rfl (str83G4_x1_normal hfr) (str83G4_x_normal hfr) hlt
    hstepN (str83N1_le_x1 L1 L2 S) (str83N1_le_n L1 L2 S)
    ((str83N_le_x hfr).trans ((str83G4_x_le_sup hfr).trans
      (D14.le_normalizer_of_isNormalIn (str83G4_x1_normal hfr))))

theorem str83G4_not_twoResidual_le_centralizerMod_x1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    ¬ twoResidual (L1 ⊔ S) ≤
      centralizerMod (str83X1 L1 L2 S) (L1 ⊔ S) (str83X L1 L2 S) := by
  intro hc
  rw [F6.twoResidual_eq_oTwoUpper] at hc
  have hXO : ⁅str83X L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ ≤ str83X1 L1 L2 S := by
    refine Subgroup.commutator_le.mpr fun x hx u hu => ?_
    have h1 : u * x * u⁻¹ * x⁻¹ ∈ str83X1 L1 L2 S := (hc hu).2.2 x hx
    have h2 := (str83X1 L1 L2 S).inv_mem h1
    change ⁅x, u⁆ ∈ str83X1 L1 L2 S
    rwa [show (u * x * u⁻¹ * x⁻¹)⁻¹ = ⁅x, u⁆ by
      simp only [commutatorElement_def]; group] at h2
  have hNle : str83N L1 L2 S ≤ str83X1 L1 L2 S := sup_le hXO (str83G4_z1_le_x1 hfr)
  have hXle : str83X L1 L2 S ≤ str83X1 L1 L2 S := by
    rw [str83G4_x_eq_n_sup_x1 hfr d hX]
    exact sup_le hNle le_rfl
  exact (not_le_of_gt (str83G4_isChiefStep_x1_x hfr d hX hB).2.2.1) hXle

theorem str83G4_isSzNaturalSection_x_x1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    IsSzNaturalSection (L1 ⊔ S) (str83X L1 L2 S) (str83X1 L1 L2 S) a :=
  str83G4_isSzNaturalSection_chiefStep hfr d hX hB (str83G4_isChiefStep_x1_x hfr d hX hB)
    (str83G4_z1_le_x1 hfr) (str83G4_not_twoResidual_le_centralizerMod_x1 hfr d hX hB)

end CFSG.Quasithin.Stroth

end
