module

public import CFSG.Quasithin.Vol2.GoldschmidtP778A5E1
public import CFSG.Quasithin.Background.E1Amb

public section

namespace CFSG.Quasithin.E1.ThinA5

open Equiv CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.E1.LiftS5
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G] {H T A : Subgroup G} (ψ : ↥H →* Perm (Fin 5))

theorem sA_mem_Vo : sA ∈ Vo := by
  show sA ∈ volist
  simp [volist]

theorem sB_mem_Vo : sB ∈ Vo := by
  show sB ∈ volist
  simp [volist]

omit [Finite G] in
theorem relIndex_zA (hAH : A ≤ H) (hV : (A.subgroupOf H).map ψ = Vo) :
    (zA ψ).relIndex A = 2 := by
  have h1 : (zA ψ).subgroupOf H = Z01.comap ψ :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have h2 : (zA ψ).relIndex A = ((zA ψ).subgroupOf H).relIndex (A.subgroupOf H) :=
    (Subgroup.relIndex_subgroupOf hAH).symm
  rw [h2, h1, Subgroup.relIndex_comap, hV]
  have h3 := Subgroup.relIndex_mul_card Z01 Vo
  have h4 : Z01 ⊓ Vo = Z01 := inf_eq_left.mpr fun x hx => z01_le_vo x hx
  rw [h4, card_Z01, card_Vo] at h3
  omega

theorem eOneAmb_kA (hA5 : alternatingGroup (Fin 5) ≤ ψ.range) (hψ : ψ.range = ⊤)
    (hker : IsPGroup 2 ψ.ker) (hAH : A ≤ H) (hV : (A.subgroupOf H).map ψ = Vo) :
    EOneAmb (kA ψ) A := by
  have hO := pCoreOf_kA ψ hψ hker
  have hmem : ∀ z ∈ Vo, ∃ a : ↥H, (a : G) ∈ A ∧ ψ a = z := by
    intro z hz
    rw [← hV] at hz
    obtain ⟨a, ha, hz⟩ := hz
    exact ⟨a, ha, hz⟩
  refine ⟨3, Nat.prime_three, by norm_num, rA ψ, rA_le_kA ψ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s hs
    obtain ⟨hsH, hsc⟩ := (mem_kA ψ).1 hs
    have key : ∀ s ∈ kA ψ, ∀ r ∈ rA ψ, s * r * s⁻¹ ∈ rA ψ := by
      intro s hs r hr
      obtain ⟨hsH, hsc⟩ := (mem_kA ψ).1 hs
      obtain ⟨hrH, hrc⟩ := (mem_rA ψ).1 hr
      refine (mem_rA ψ).2 ⟨H.mul_mem (H.mul_mem hsH hrH) (H.inv_mem hsH), ?_⟩
      have : ψ ⟨s * r * s⁻¹, H.mul_mem (H.mul_mem hsH hrH) (H.inv_mem hsH)⟩ =
          ψ ⟨s, hsH⟩ * ψ ⟨r, hrH⟩ * (ψ ⟨s, hsH⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]; rfl
      rw [this]
      exact r1_normal _ hsc _ hrc
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => key s hs x hx
    · intro hx
      have := key s⁻¹ ((kA ψ).inv_mem hs) _ hx
      simpa [mul_assoc] using this
  · rw [hO]; exact zA_le_rA ψ
  · intro x hx
    refine ⟨1, ?_⟩
    rw [hO, pow_one]
    obtain ⟨hxH, hxc⟩ := (mem_rA ψ).1 hx
    refine (mem_zA ψ).2 ⟨H.pow_mem hxH 3, ?_⟩
    have : ψ ⟨x ^ 3, H.pow_mem hxH 3⟩ = (ψ ⟨x, hxH⟩) ^ 3 := by
      rw [← map_pow]; rfl
    rw [this]
    exact r1_cube _ hxc
  · intro s hs
    refine ⟨1, ?_⟩
    rw [pow_one]
    obtain ⟨hsH, hsc⟩ := (mem_kA ψ).1 hs
    refine (mem_rA ψ).2 ⟨H.pow_mem hsH 2, ?_⟩
    have : ψ ⟨s ^ 2, H.pow_mem hsH 2⟩ = (ψ ⟨s, hsH⟩) ^ 2 := by
      rw [← map_pow]; rfl
    rw [this]
    exact c1_sq _ hsc
  · rw [hO]
    intro heq
    obtain ⟨x, hx⟩ := hA5 (Perm.mem_alternatingGroup.mpr sign_c3)
    have hxR : (x : G) ∈ rA ψ := (mem_rA ψ).2 ⟨x.2, by simpa [hx] using c3_mem_r1⟩
    rw [heq] at hxR
    obtain ⟨hxH, hxc⟩ := (mem_zA ψ).1 hxR
    have : ψ x = c3 := hx
    have h3 : c3 ∈ z01list := by simpa [this] using hxc
    revert h3
    unfold z01list sA c3
    decide
  · rw [hO]
    intro r hr
    obtain ⟨hrH, hrc⟩ := (mem_rA ψ).1 hr
    obtain ⟨a, haA, haψ⟩ := hmem sB sB_mem_Vo
    have hcm : ⁅r, (a : G)⁆ ∈ ⁅rA ψ, A⁆ := Subgroup.commutator_mem_commutator hr haA
    have hy : r * ⁅r, (a : G)⁆ ∈ zA ψ := by
      have haH : (a : G) ∈ H := a.2
      have hcH : r * ⁅r, (a : G)⁆ ∈ H := by
        simp only [commutatorElement_def]
        exact H.mul_mem hrH (H.mul_mem (H.mul_mem (H.mul_mem hrH haH) (H.inv_mem hrH))
          (H.inv_mem haH))
      refine (mem_zA ψ).2 ⟨hcH, ?_⟩
      have : ψ ⟨r * ⁅r, (a : G)⁆, hcH⟩ =
          ψ ⟨r, hrH⟩ * (ψ ⟨r, hrH⟩ * ψ a * (ψ ⟨r, hrH⟩)⁻¹ * (ψ a)⁻¹) := by
        simp only [commutatorElement_def, ← map_inv, ← map_mul]; rfl
      rw [this, haψ]
      exact r1_comm _ hrc
    have : r = (r * ⁅r, (a : G)⁆) * (⁅r, (a : G)⁆)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hy)
      (Subgroup.inv_mem _ (Subgroup.mem_sup_left hcm))
  · rw [hO]
    exact relIndex_zA ψ hAH hV

omit [Finite G] in
theorem A_le_kA (hAH : A ≤ H) (hV : (A.subgroupOf H).map ψ = Vo) : A ≤ kA ψ := by
  intro a ha
  refine (mem_kA ψ).2 ⟨hAH ha, vo_le_c1 _ ?_⟩
  have : ψ ⟨a, hAH ha⟩ ∈ (A.subgroupOf H).map ψ := ⟨⟨a, hAH ha⟩, ha, rfl⟩
  rw [hV] at this
  exact this

theorem tauOf_le_kA (hA5 : alternatingGroup (Fin 5) ≤ ψ.range) (hTH : T ≤ H)
    (hV : (A.subgroupOf H).map ψ = Vo) : tauOf H T A ≤ T ⊓ kA ψ := by
  intro t ht
  obtain ⟨htT, -, htc⟩ := ht
  have htH : t ∈ H := hTH htT
  refine ⟨htT, (mem_kA ψ).2 ⟨htH, ?_⟩⟩
  obtain ⟨a, haA, haψ⟩ : ∃ a : ↥H, (a : G) ∈ A ∧ ψ a = sA := by
    have : sA ∈ (A.subgroupOf H).map ψ := hV ▸ sA_mem_Vo
    obtain ⟨a, ha, h⟩ := this
    exact ⟨a, ha, h⟩
  obtain ⟨hcH, hc1⟩ := psi_pCoreOf_eq_one ψ hA5 (htc a haA)
  have : ψ ⟨⁅t, (a : G)⁆, hcH⟩ = ⁅ψ ⟨t, htH⟩, ψ a⁆ := by
    simp only [commutatorElement_def, ← map_inv, ← map_mul]; rfl
  rw [this, haψ] at hc1
  have h2 : ψ ⟨t, htH⟩ * sA = sA * ψ ⟨t, htH⟩ := commutatorElement_eq_one_iff_mul_comm.mp hc1
  exact (c1list_iff _).1 h2.symm

omit [Finite G] in
theorem isSylowIn_inf_kA (hψ : ψ.range = ⊤) (hker : IsPGroup 2 ψ.ker) (hT : IsSylowIn 2 T H)
    (hAT : A ≤ T) (hV : (A.subgroupOf H).map ψ = Vo) :
    IsSylowIn 2 (T ⊓ kA ψ) (kA ψ) := by
  have hTH := hT.le
  refine ⟨inf_le_right, hT.isPGroup.to_le inf_le_left, ?_⟩
  rw [Subgroup.inf_relIndex_right]
  have h1 : T.relIndex (kA ψ) = (T.subgroupOf H).relIndex ((kA ψ).subgroupOf H) :=
    (Subgroup.relIndex_subgroupOf (kA_le ψ)).symm
  have h2 : (kA ψ).subgroupOf H = C1.comap ψ :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hkerT' : ψ.ker ≤ T.subgroupOf H := fun x hx => ker_le_T ψ hker hT ⟨x, hx, rfl⟩
  have h3 : T.subgroupOf H = ((T.subgroupOf H).map ψ).comap ψ := by
    rw [Subgroup.comap_map_eq, sup_eq_left.mpr hkerT']
  have h4 : ((T.subgroupOf H).map ψ).relIndex C1 * Nat.card ↥(((T.subgroupOf H).map ψ) ⊓ C1) =
      12 := by
    rw [Subgroup.relIndex_mul_card, card_C1]
  have hT2 : IsPGroup 2 ↥(T.subgroupOf H) :=
    hT.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hTH).symm
  have hD2 : IsPGroup 2 ↥(((T.subgroupOf H).map ψ) ⊓ C1) :=
    (hT2.map ψ).to_le inf_le_left
  have hVD : Vo ≤ ((T.subgroupOf H).map ψ) ⊓ C1 := by
    refine le_inf ?_ ?_
    · rw [← hV]
      exact Subgroup.map_mono (Subgroup.subgroupOf_mono _ hAT)
    · intro x hx
      exact vo_le_c1 _ hx
  have hcard4 : Nat.card ↥(((T.subgroupOf H).map ψ) ⊓ C1) = 4 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hD2
    have hle : Nat.card ↥Vo ≤ Nat.card ↥(((T.subgroupOf H).map ψ) ⊓ C1) :=
      Subgroup.card_le_of_le hVD
    rw [card_Vo] at hle
    have hdvd : Nat.card ↥(((T.subgroupOf H).map ψ) ⊓ C1) ∣ 12 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : ((T.subgroupOf H).map ψ) ⊓ C1 ≤ C1)
      rwa [card_C1] at this
    exact card_eq_four_of_two_power hk (by omega) (Or.inr hdvd)
  rw [hcard4] at h4
  have h5 : (T.subgroupOf H).relIndex (C1.comap ψ) =
      ((T.subgroupOf H).map ψ).relIndex C1 := by
    calc (T.subgroupOf H).relIndex (C1.comap ψ)
        = (((T.subgroupOf H).map ψ).comap ψ).relIndex (C1.comap ψ) := by rw [← h3]
      _ = ((T.subgroupOf H).map ψ).relIndex ((C1.comap ψ).map ψ) :=
          Subgroup.relIndex_comap _ _ _
      _ = ((T.subgroupOf H).map ψ).relIndex C1 := by
          rw [Subgroup.map_comap_eq, hψ, top_inf_eq]
  rw [h1, h2, h5]
  intro h2dvd
  omega

theorem isE_one_kA (hA5 : alternatingGroup (Fin 5) ≤ ψ.range) (hψ : ψ.range = ⊤)
    (hker : IsPGroup 2 ψ.ker) (hT : IsSylowIn 2 T H) (hAT : A ≤ T)
    (hV : (A.subgroupOf H).map ψ = Vo) : IsE 1 H T A (kA ψ) := by
  have hTH := hT.le
  have hAH : A ≤ H := hAT.trans hTH
  have hE := eOne_of_eOneAmb (A_le_kA ψ hAH hV) (eOneAmb_kA ψ hA5 hψ hker hAH hV)
  refine ⟨kA_le ψ, tauOf_le_kA ψ hA5 hTH hV, isSylowIn_inf_kA ψ hψ hker hT hAT hV,
    Or.inl ⟨hE, ?_⟩⟩
  obtain ⟨p, -, -, -, -, -, h4⟩ := hE
  rw [h4]
  norm_num

end CFSG.Quasithin.E1.ThinA5
