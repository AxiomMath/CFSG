module

public import CFSG.Quasithin.Vol2.Ch7Lem734Rows
public import CFSG.Quasithin.Background.HNPrimeMathieu
public import CFSG.Quasithin.Background.HNPrimeM22Hat
public import CFSG.Quasithin.Vol2.Ch7Setup

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.MathieuLat CFSG.Quasithin.H.NPrimeHall CFSG.Quasithin.H13.A5.M12
  CFSG.Monster.Code CFSG.Quasithin.Vol2.Ch10.SecA.C10P01
open scoped IsMulCommutative

section Transport

theorem nPrime_top_congr {Γ Γ' : Type*} [Group Γ] [Group Γ'] (e : Γ ≃* Γ') :
    nPrime (⊤ : Subgroup Γ) = nPrime (⊤ : Subgroup Γ') := by
  rw [← nPrime_map_of_injective (f := e.toMonoidHom) e.injective ⊤,
    Subgroup.map_top_of_surjective _ e.surjective]

theorem nPrime_eq_top {P : Type*} [Group P] (H : Subgroup P) :
    nPrime H = nPrime (⊤ : Subgroup ↥H) := by
  rw [← nPrime_map_of_injective H.subtype_injective ⊤, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype]

theorem nPrime_subgroupOf {P : Type*} [Group P] {H K : Subgroup P} (hHK : H ≤ K) :
    nPrime (H.subgroupOf K) = nPrime H := by
  rw [← nPrime_map_of_injective K.subtype_injective, Subgroup.map_subgroupOf_eq_of_le hHK]

theorem nPrime_top_eq_two {Γ : Type*} [Group Γ] [Finite Γ] (h3 : IndexThree (⊤ : Subgroup Γ))
    (h2 : 2 ≤ nPrime (⊤ : Subgroup Γ)) : nPrime (⊤ : Subgroup Γ) = 2 :=
  le_antisymm (nPrime_le_two h3) h2

variable {V W : Type*} [CommGroup V] [CommGroup W]

theorem nPrime_eq_of_rep {P : Type*} [Group P] {ρ : P →* MulAut W} (hρ : Function.Injective ρ)
    {L M : Subgroup (MulAut V)} (hLM : IsOver L M) {e : V ≃* W} {L₀ : Subgroup P}
    (he : L.map (congrHom e) = L₀.map ρ)
    (hN : Subgroup.normalizer ((L₀.map ρ : Subgroup (MulAut W)) : Set (MulAut W)) = ρ.range) :
    ∃ M₀ : Subgroup P, L₀ ≤ M₀ ∧ nPrime M = nPrime M₀ := by
  have hMr : M.map (congrHom e) ≤ ρ.range := map_le_of_normalizer hLM he hN le_rfl
  refine ⟨(M.map (congrHom e)).comap ρ, ?_, ?_⟩
  · rw [← Subgroup.map_le_iff_le_comap, ← he]
    exact Subgroup.map_mono hLM.1
  · rw [← nPrime_map_congrHom e M, ← nPrime_map_of_injective hρ,
      Subgroup.map_comap_eq_self hMr]

theorem nPrime_eq_of_rep_top {P : Type*} [Group P] {ρ : P →* MulAut W}
    (hρ : Function.Injective ρ) {L M : Subgroup (MulAut V)} (hLM : IsOver L M) {e : V ≃* W}
    (he : L.map (congrHom e) = ρ.range)
    (hN : Subgroup.normalizer ((ρ.range : Subgroup (MulAut W)) : Set (MulAut W)) = ρ.range) :
    nPrime M = nPrime (⊤ : Subgroup P) := by
  rw [MonoidHom.range_eq_map] at he hN
  obtain ⟨M₀, hM₀, h⟩ := nPrime_eq_of_rep hρ hLM he (by rw [hN, MonoidHom.range_eq_map])
  rw [h, top_le_iff.mp hM₀]

theorem nPrime_eq_two_of_rep_index_two {P : Type*} [Group P] [Finite P] {ρ : P →* MulAut W}
    (hρ : Function.Injective ρ) {L M : Subgroup (MulAut V)} (hLM : IsOver L M) {e : V ≃* W}
    {L₀ : Subgroup P} (he : L.map (congrHom e) = L₀.map ρ)
    (hN : Subgroup.normalizer ((L₀.map ρ : Subgroup (MulAut W)) : Set (MulAut W)) = ρ.range)
    (hi : L₀.index = 2) (hL₀ : nPrime L₀ = 2) (hP : 2 ≤ nPrime (⊤ : Subgroup P)) :
    nPrime M = 2 := by
  obtain ⟨M₀, hM₀, h⟩ := nPrime_eq_of_rep hρ hLM he hN
  rw [h]
  have hnorm : L₀.Normal := Subgroup.normal_of_index_eq_two hi
  have hle : nPrime M₀ ≤ nPrime L₀ := by
    refine nPrime_le_of_normal hM₀ (fun x _ => ?_) ?_
    · rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · exact fun hy => hnorm.conj_mem y hy x
      · intro hy
        have := hnorm.conj_mem _ hy x⁻¹
        simpa [mul_assoc] using this
    · refine sq_mem_of_relIndex_le_two hM₀ ?_ ?_
      · intro x _
        rw [Subgroup.mem_normalizer_iff]
        intro y
        constructor
        · exact fun hy => hnorm.conj_mem y hy x
        · intro hy
          have := hnorm.conj_mem _ hy x⁻¹
          simpa [mul_assoc] using this
      · have := Subgroup.relIndex_dvd_index_of_le hM₀
        rw [hi] at this
        exact Nat.le_of_dvd (by norm_num) this
  refine le_antisymm (hle.trans hL₀.le) ?_
  have h2 : L₀.relIndex M₀ * M₀.index = 2 := by
    rw [Subgroup.relIndex_mul_index hM₀, hi]
  rcases (Nat.dvd_prime Nat.prime_two).mp (Dvd.intro _ h2) with h1 | h1
  · rw [Subgroup.relIndex_eq_one] at h1
    rw [le_antisymm h1 hM₀, hL₀]
  · rw [h1] at h2
    have : M₀.index = 1 := by omega
    rw [Subgroup.index_eq_one] at this
    rw [this]
    exact hP

end Transport

theorem nPrime_autPerm :
    nPrime (⊤ : Subgroup ↥AutPerm) = 2 := by
  rw [nPrime_top_congr autPermEquivM24']
  exact nPrime_top_eq_two m24_indexThree m24_two_le_nPrime

theorem nPrime_mog23 :
    nPrime (⊤ : Subgroup ↥mog23) = 2 := by
  rw [nPrime_top_congr mog23EquivM23]
  exact nPrime_top_eq_two m23_indexThree m23_two_le_nPrime

theorem nPrime_mog22 :
    nPrime (mog22.subgroupOf mog22plus) = 2 := by
  rw [nPrime_subgroupOf mog22_le_mog22plus, nPrime_eq_top, nPrime_top_congr mog22EquivM22]
  exact nPrime_top_eq_two m22_indexThree m22_two_le_nPrime

theorem index_mog22 :
    (mog22.subgroupOf mog22plus).index = 2 := by
  have h := (mog22.subgroupOf mog22plus).card_mul_index
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe mog22_le_mog22plus).toEquiv, card_mog22,
    card_mog22plus] at h
  omega

theorem nPrime_m24Fix :
    nPrime ((m24Fix dodecadE).subgroupOf m24Pair) = 2 := by
  obtain ⟨⟨e⟩, -⟩ := m24Fix_dodecadE_props
  rw [nPrime_subgroupOf m24Fix_le_m24Pair, nPrime_eq_top, nPrime_top_congr e]
  exact nPrime_top_eq_two m12_indexThree m12_two_le_nPrime

theorem index_m24Fix :
    ((m24Fix dodecadE).subgroupOf m24Pair).index = 2 := by
  rw [← Subgroup.relIndex]
  exact relIndex_m24Fix

theorem range_rhoC12_m24Fix :
    (rhoC12 (m24Fix dodecadE) m24Fix_le_m24Pair).range =
      ((m24Fix dodecadE).subgroupOf m24Pair).map (rhoC12 m24Pair le_rfl) := by
  apply le_antisymm
  · rintro _ ⟨σ, rfl⟩
    exact ⟨⟨σ, m24Fix_le_m24Pair σ.2⟩, σ.2, rfl⟩
  · rintro _ ⟨σ, hσ, rfl⟩
    exact ⟨⟨σ, hσ⟩, rfl⟩

theorem stmt7_3_4_nPrime_Mathieu :
    Stmt7_3_4_nPrime_Mathieu := by
  intro G _ _ T L I _ hV _ hNM _ hrow
  have hLM : IsOver (autI hV (fsuL0 T L)) (autI hV ⊤) :=
    ⟨autI_fsuL0_le hV, autI_top_le_normalizer hV hNM⟩
  rcases hrow with h | h | h | h | h | h | h | h
  ·
    have hM : M12Ten (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ := h.1
    obtain ⟨e, he⟩ := m12_std hM
    rw [range_rhoC12_m24Fix] at he
    refine nPrime_eq_two_of_rep_index_two rhoC12_m24Pair_injective hLM he ?_ index_m24Fix
      nPrime_m24Fix ?_
    · have h' := normalizer_rhoC12
      rwa [range_rhoC12_m24Fix] at h'
    · rw [← nPrime_eq_top]
      exact m24Pair_two_le_nPrime
  ·
    have hM : Mhat22Twelve (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ := h
    obtain ⟨K, _, _, Γ₀, hK, hHat, -, hreal⟩ := hM
    obtain ⟨e, h1, h2⟩ := exists_transport_natural hreal hLM.1 hLM.2
    rw [← nPrime_map_congrHom e]
    exact M22HatN.nPrime_eq_two hK hHat h1 h2
  ·
    have hM : MathieuCode22 (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ := h
    obtain ⟨e, he⟩ := code22_std hM
    rw [range_rhoC10_mog22] at he
    refine nPrime_eq_two_of_rep_index_two rhoC10_mog22plus_injective hLM he ?_ index_mog22
      nPrime_mog22 ?_
    · have h' := normalizer_rhoC10_mog22
      rwa [range_rhoC10_mog22] at h'
    · rw [← nPrime_eq_top]
      exact mog22plus_two_le_nPrime
  ·
    have hM : MathieuCocode22 (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ := h
    obtain ⟨e, he⟩ := cocode22_std hM
    rw [range_rho10_mog22] at he
    refine nPrime_eq_two_of_rep_index_two rho10_mog22plus_injective hLM he ?_ index_mog22
      nPrime_mog22 ?_
    · have h' := normalizer_rho10_mog22
      rwa [range_rho10_mog22] at h'
    · rw [← nPrime_eq_top]
      exact mog22plus_two_le_nPrime
  ·
    have hM : MathieuCode23 (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ := h
    obtain ⟨e, he⟩ := code23_std hM
    rw [nPrime_eq_of_rep_top (rhoC11_injective mog23 inf_le_left) hLM he
      normalizer_rhoC11_mog23]
    exact nPrime_mog23
  ·
    have hM : MathieuCocode23 (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ := h
    obtain ⟨e, he⟩ := cocode23_std hM
    rw [nPrime_eq_of_rep_top (rho11_injective mog23 inf_le_left) hLM he
      normalizer_rho11_mog23]
    exact nPrime_mog23
  ·
    have hM : MathieuCode24 (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ := h
    obtain ⟨e, he⟩ := code24_std hM
    rw [nPrime_eq_of_rep_top (rhoC11_injective AutPerm le_rfl) hLM he
      normalizer_rhoC11_autPerm]
    exact nPrime_autPerm
  ·
    have hM : MathieuCocode24 (V := IntMod (fsuV T I) hV) (autI hV (fsuL0 T L)) ⊤ ⊥ := h
    obtain ⟨e, he⟩ := cocode24_std hM
    rw [nPrime_eq_of_rep_top (rho11_injective AutPerm le_rfl) hLM he
      normalizer_rho11_autPerm]
    exact nPrime_autPerm

end CFSG.Quasithin.H13
