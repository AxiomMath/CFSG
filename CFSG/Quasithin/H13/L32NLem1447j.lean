module

public import CFSG.Quasithin.H13.L32NLem1447g
public import CFSG.Quasithin.H13.L32N1447AModel
public import CFSG.Quasithin.H13.L32A1410e

public section

namespace CFSG.Quasithin.H13.L1447

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L14411 L144B L1442M Mat8Cert
  G5ACert Q1447A

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)}

theorem mem_of_central {Γ : Type*} [Group Γ] [Finite Γ] {K P : Subgroup Γ} (hKP : K ≤ P)
    (hK : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x) (hK8 : Nat.card K = 8) (hP16 : Nat.card P = 16)
    (hnc : ∃ p ∈ P, ∃ p' ∈ P, p * p' ≠ p' * p) {z : Γ} (hzP : z ∈ P)
    (hz : ∀ p ∈ P, z * p = p * z) : z ∈ K := by
  by_contra hzK
  set KZ : Subgroup Γ := K ⊔ Subgroup.zpowers z with hKZ
  have hKz : KZ ≤ P := sup_le hKP ((Subgroup.zpowers_le).mpr hzP)
  have hzc : Subgroup.zpowers z ≤ Subgroup.centralizer (KZ : Set Γ) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    exact fun p hp => (hz p (hKz hp)).symm
  have hKc : K ≤ Subgroup.centralizer (KZ : Set Γ) := by
    rw [Subgroup.le_centralizer_iff]
    refine sup_le (fun k hk => Subgroup.mem_centralizer_iff.mpr fun k' hk' => hK _ hk' _ hk) ?_
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    exact fun p hp => (hz p (hKP hp)).symm
  have hcomm : KZ ≤ Subgroup.centralizer (KZ : Set Γ) := sup_le hKc hzc
  have hlt : K < KZ :=
    lt_of_le_of_ne le_sup_left fun h => hzK (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  have hcard : Nat.card ↥KZ = 16 := by
    have h1 := Subgroup.card_dvd_of_le hKz
    rw [hP16] at h1
    have h2 := Subgroup.card_lt_of_lt hlt
    rw [hK8] at h2
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show _ ∣ 2 ^ 4 from h1)
    rw [hk'] at h2 ⊢
    interval_cases k <;> simp_all
  have hPeq : KZ = P := Subgroup.eq_of_le_of_card_ge hKz (by rw [hcard, hP16])
  obtain ⟨p, hp, p', hp', hpp'⟩ := hnc
  rw [← hPeq] at hp hp'
  exact hpp' (Subgroup.mem_centralizer_iff.mp (hcomm hp') p hp)


theorem facts_of_caseA (B : Base G T L V V₂ g) (h12213 : Stmt12_2_13) {b : Bool}
    {e₀ : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}
    (hiso : IsModelIso D (l32nH T V) e₀ (q5 false) (g5 b false))
    (hW8 : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 ^ 3) :
    F1 T V V₂ ∧ F2 T V V₂ g ∧ F3 T V V₂ g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have himgH := img8_eq_of_iso hiso
  have hZ2 : Nat.card ↥(centerOf (fsuU T V)) = 2 := by
    rw [l32n_card_centerOf]
    exact B.ext.2.2.2
  have hform₀ : ∀ x y, D.B x y = b5AV (e₀ x) (e₀ y) := fun x y =>
    form_of_quadOf D e₀ hZ2 B.comm_center hiso.quad x y
  have hT := B.card_imgT e₀ himgH (m := if b then 4 else 3) (k := 45)
    (by rw [card_gA5]; cases b <;> rfl) (by decide)
  have hP2 : IsPGroup 2 ↥(PA5 b) := IsPGroup.of_card (n := if b then 4 else 3)
    (by rw [card_PA5]; cases b <;> rfl)
  obtain ⟨e, himgH', hform, himgT⟩ := B.exists_normalized e₀ himgH hform₀ (PA5_le b) hP2
    (by rw [Q1410.relIndex_PA5]; decide) (by rw [hT, card_PA5]; cases b <;> rfl)
  obtain ⟨a, ha, haV⟩ := B.abs.exists_mem_not_mem
  have hva : e (D.π a) = vec8 vA := by
    rcases eq_of_fixed_PA5 b (e (D.π a))
        (fun γ hγ => B.T_fix e ha haV (by rw [himgT]; exact hγ)) with h | h
    · exact absurd ((map_eq_zero_iff e e.injective).mp h) (B.pi_a_ne D ha haV)
    · exact h
  have hWP : img8 D e (CFSG.conjugate (l32nW T V V₂) g) ≤ PA5 b := by
    rw [← himgT]
    exact img8_mono D e B.Wg_le_T
  have hW8' : Nat.card ↥(img8 D e (CFSG.conjugate (l32nW T V V₂) g)) = 8 := by
    rw [card_img8, hW8]
    norm_num
  have hZW : ∀ z : GL (Fin 8) (ZMod 2), colsOf (z : Matrix (Fin 8) (Fin 8) (ZMod 2)) ∈ zA b →
      z ∈ img8 D e (CFSG.conjugate (l32nW T V V₂) g) := by
    intro z hz
    cases b with
    | false =>
      have hWeq : img8 D e (CFSG.conjugate (l32nW T V V₂) g) = PA5 false :=
        Subgroup.eq_of_le_of_card_ge hWP (by rw [card_PA5, hW8']; rfl)
      rw [hWeq]
      exact zA_mem false hz
    | true =>
      exact mem_of_central hWP (B.img_Wg_comm e) hW8' (by rw [card_PA5]; rfl) not_comm_PA5
        (zA_mem true hz) fun p hp => zA_central true hz hp
  refine ⟨B.F1_of_coords_vec D e (matOf e) (matOf_mulVec e) ha haV hform fun γ hγ h1 h2 => ?_,
    B.F2_of_coords D e (matOf e) h12213 (matOf_mulVec e) ha haV fun γ hγ h1 h2 => ?_,
    B.F3_of_map D (matOf e) (matOf_injective e) ?_⟩
  · have hγ' : γ ∈ img8 D e (l32nH T V) := hγ
    rw [himgH'] at hγ'
    rw [hva]
    exact a5_vec b hγ' h1 h2
  · rw [hva]
    exact a5P_big b (hWP hγ) h1 h2
  · show oTwoUpper (img8 D e (l32nH T V)) ≤ _
    rw [himgH']
    refine (a5_oTwoUpper_le b).trans (Subgroup.closure_mono ?_)
    rintro y ⟨k, hk, z, hz, rfl⟩
    have hk' : k ∈ img8 D e (l32nH T V) := by rw [himgH']; exact hk
    exact ⟨k, hk', z, hZW z hz, rfl⟩

end CFSG.Quasithin.H13.L1447
