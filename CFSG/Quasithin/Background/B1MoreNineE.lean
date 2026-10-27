module

public import CFSG.Quasithin.Background.B1MoreNineD
public import CFSG.Quasithin.Background.D2Offenders

public section

namespace CFSG.Quasithin

open CFSG.Open B19Aux

theorem exists_factor_of_card_two {M : Type*} [CommGroup M] [Finite M] {X : Subgroup (MulAut M)}
    {𝓗 : Finset (Subgroup (MulAut M))}
    (hchar : ∀ B, IsFFStarOffender X B ↔ ∃ a : Subgroup (MulAut M) → Subgroup (MulAut M),
      (∀ H ∈ 𝓗, a H = ⊥ ∨ CFSG.QuasithinUnique.IsSylowTwoOf (a H) H) ∧ (∃ H ∈ 𝓗, a H ≠ ⊥) ∧
        B = ⨆ H ∈ 𝓗, a H)
    {A' : Subgroup (MulAut M)} (hA' : IsFFStarOffender X A') (hcard : Nat.card A' = 2) :
    ∃ H ∈ 𝓗, A' ≤ H := by
  obtain ⟨a, hSyl, ⟨H₀, hH₀, hne⟩, hEq⟩ := (hchar A').1 hA'
  refine ⟨H₀, hH₀, ?_⟩
  have hle : a H₀ ≤ A' := by
    calc a H₀ ≤ ⨆ H ∈ 𝓗, a H := le_iSup₂ (f := fun H (_ : H ∈ 𝓗) => a H) H₀ hH₀
      _ = A' := hEq.symm
  have hsyl := (hSyl H₀ hH₀).resolve_left hne
  have hge : Nat.card A' ≤ Nat.card (a H₀) := by
    rw [hcard]
    have : 1 < Nat.card (a H₀) := (Subgroup.one_lt_card_iff_ne_bot _).2 hne
    omega
  have : a H₀ = A' := Subgroup.eq_of_le_of_card_ge hle hge
  rw [← this]
  exact hsyl.1

theorem conj_mem_factor {M : Type*} [CommGroup M] [Finite M] {X F A' : Subgroup (MulAut M)}
    {𝓗 : Finset (Subgroup (MulAut M))}
    (hchar : ∀ B, IsFFStarOffender X B ↔ ∃ a : Subgroup (MulAut M) → Subgroup (MulAut M),
      (∀ H ∈ 𝓗, a H = ⊥ ∨ CFSG.QuasithinUnique.IsSylowTwoOf (a H) H) ∧ (∃ H ∈ 𝓗, a H ≠ ⊥) ∧
        B = ⨆ H ∈ 𝓗, a H)
    (hcomm : ∀ H ∈ 𝓗, ∀ H' ∈ 𝓗, H ≠ H' → ∀ a ∈ H, ∀ b ∈ H', a * b = b * a)
    (hFX : F ≤ X) (hn : A' ≤ Subgroup.normalizer (F : Set (MulAut M)))
    (hFodd : ∀ x ∈ F, Odd (orderOf x)) (hA2 : ∀ a ∈ A', a ^ 2 = 1)
    (hoff : IsFFStarOffender X A') (hcard : Nat.card A' = 2)
    {H₀ : Subgroup (MulAut M)} (hH₀ : H₀ ∈ 𝓗) (hAH₀ : A' ≤ H₀) :
    ∀ f ∈ F, ∀ a ∈ A', f * a * f⁻¹ ∈ H₀ := by
  intro f hf a ha
  have hoffc : IsFFStarOffender X (B1.conjAut f A') := B1.isFFStarOffender_conjAut hoff (hFX hf)
  have hcardc : Nat.card (B1.conjAut f A') = 2 := by rw [B1.card_conjAut, hcard]
  obtain ⟨H', hH', hle'⟩ := exists_factor_of_card_two hchar hoffc hcardc
  have hmem : f * a * f⁻¹ ∈ B1.conjAut f A' := by
    rw [B1.mem_conjAut]
    simpa [mul_assoc] using ha
  by_cases hHH : H' = H₀
  · subst hHH
    exact hle' hmem
  · have hcm : (f * a * f⁻¹) * a = a * (f * a * f⁻¹) :=
      hcomm H' hH' H₀ hH₀ hHH _ (hle' hmem) a (hAH₀ ha)
    have hc : f * a * f⁻¹ * a⁻¹ ∈ F := by
      have e : f * a * f⁻¹ * a⁻¹ = f * (a * f⁻¹ * a⁻¹) := by group
      rw [e]
      exact F.mul_mem hf (conj_mem_of_le_normalizer hn ha (F.inv_mem hf))
    have ha2 : a * a = 1 := by rw [← pow_two]; exact hA2 a ha
    have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    have hx2 : (f * a * f⁻¹) * (f * a * f⁻¹) = 1 := by
      calc (f * a * f⁻¹) * (f * a * f⁻¹) = f * (a * a) * f⁻¹ := by group
        _ = 1 := by rw [ha2]; group
    have hsq : (f * a * f⁻¹ * a⁻¹) ^ 2 = 1 := by
      generalize f * a * f⁻¹ = x at hcm hx2 ⊢
      rw [hinv, pow_two]
      calc x * a * (x * a) = x * (a * x) * a := by group
        _ = x * (x * a) * a := by rw [hcm]
        _ = (x * x) * (a * a) := by group
        _ = 1 := by rw [hx2, ha2, one_mul]
    have h1 : f * a * f⁻¹ * a⁻¹ = 1 :=
      eq_one_of_odd_orderOf_of_pow (hFodd _ hc) (k := 1) (by simpa using hsq)
    have h2 : f * a * f⁻¹ = a := mul_inv_eq_one.1 h1
    rw [h2]
    exact hAH₀ ha

theorem mem_of_actsAsNaturalL2_top {M : Type*} [CommGroup M] {H : Subgroup (MulAut M)}
    (hH : ActsAsNaturalL2 H (⊤ : Subgroup M)) (ψ : MulAut M) : ψ ∈ H := by
  obtain ⟨e, φ, hφ⟩ := hH
  let φ' : M ≃* Multiplicative (Fin 2 → ZMod 2) := Subgroup.topEquiv.symm.trans φ
  let ψ' : MulAut (Multiplicative (Fin 2 → ZMod 2)) := φ'.symm.trans (ψ.trans φ')
  obtain ⟨M₀, hM₀⟩ := B1.slHom_surjective ψ'
  have key : ((e.symm M₀ : ↥H) : MulAut M) = ψ := by
    ext w
    have h1 := hφ (e.symm M₀) ⟨w, trivial⟩ trivial
    have h2 : e (e.symm M₀) = M₀ := e.apply_symm_apply M₀
    rw [h2] at h1
    have h3 : φ' ((e.symm M₀ : MulAut M) w) = φ' (ψ w) := by
      show φ ⟨((e.symm M₀ : ↥H) : MulAut M) w, trivial⟩ = _
      rw [h1]
      have h4 := congrArg (fun f : MulAut (Multiplicative (Fin 2 → ZMod 2)) => f (φ' w)) hM₀
      simp only [B1.slHom, MonoidHom.coe_mk, OneHom.coe_mk, B1.slAut_apply] at h4
      have h5 : ψ' (φ' w) = φ' (ψ w) := by simp [ψ']
      rw [← h5, ← h4]
      rfl
    exact φ'.injective h3
  rw [← key]
  exact (e.symm M₀).2

namespace B19Loc

variable {V : Type*} [CommGroup V] {G A : Subgroup (MulAut V)}

theorem Abar_min [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    IsFFStarMin (Hbar G A) (Abar G A) := by
  have h := (B1_5_2 hV P.hA (fun _ ha w hw => P.W_inv_A ha w hw) (P.commSub_W_A_ne_bot hV)).1
  exact isFFStarMin_of_le h Abar_le_Hbar P.Hbar_le_autSub

theorem Abar_card [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    Nat.card ↥(Abar G A) = 2 :=
  key_card_two (B1.sq_eq_one_sub hV (Wsub G A)) (P.Hbar_solvable hV) (P.O2_Hbar hV)
    (P.Abar_min hV)

theorem local_structure [Finite V] (hV : ∀ v : V, v ^ 2 = 1) (P : B19Loc G A) :
    Nat.card ↥A = 2 ∧ Nat.card ↥(FAsub G A) = 3 ∧ Nat.card ↥(commV (FAsub G A)) = 4 ∧
      Wsub G A = commV (FAsub G A) ∧ Bsub G A = ⊥ ∧ commV (FAsub G A) ⊔ fixV A = ⊤ ∧
      (∀ ψ : MulAut ↥(Wsub G A), ψ ∈ Hbar G A) ∧
      Nonempty (↥(Hbar G A) ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
  obtain ⟨𝓗, hHle, -, hcomm, -, -, -, hnat, ⟨-, hnoStrong⟩, hchar, -⟩ :=
    B1_8 (B1.sq_eq_one_sub hV (Wsub G A)) (P.Hbar_solvable hV) (P.O2_Hbar hV)
      (P.isFFModule_Hbar hV)
  have hcard := P.Abar_card hV
  obtain ⟨H₀, hH₀, hAH₀⟩ := exists_factor_of_card_two hchar (P.offender_Hbar hV) hcard
  have hconj := conj_mem_factor hchar hcomm Fbar_le_Hbar (Abar_normalizes_Fbar G A)
    (P.Fbar_odd hV) (P.Abar_sq hV) (P.offender_Hbar hV) hcard hH₀ hAH₀
  have hFA_pre : FAsub G A ≤ B1.preB (FAsub G A) (Wsub G A) H₀ := by
    calc FAsub G A = ⁅FAsub G A, A⁆ := P.FA_comm.symm
      _ ≤ B1.preB (FAsub G A) (Wsub G A) H₀ := by
        rw [Subgroup.commutator_le]
        intro f hf a ha
        show f * a * f⁻¹ * a⁻¹ ∈ B1.preB (FAsub G A) (Wsub G A) H₀
        let fS : ↥(stabSub (Wsub G A)) := ⟨f, FA_le_stab G A hf⟩
        let aS : ↥(stabSub (Wsub G A)) := ⟨a, P.A_le_stab ha⟩
        have hfbar : resHom (Wsub G A) fS ∈ Fbar G A := mem_autSub.2 ⟨fS, hf, rfl⟩
        have habar : resHom (Wsub G A) aS ∈ Abar G A := mem_autSub.2 ⟨aS, ha, rfl⟩
        have hc := hconj _ hfbar _ habar
        have hmem : resHom (Wsub G A) (fS * aS * fS⁻¹ * aS⁻¹) ∈ H₀ := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv]
          exact H₀.mul_mem hc (H₀.inv_mem (hAH₀ habar))
        have hFA : f * a * f⁻¹ * a⁻¹ ∈ FAsub G A := by
          have e : f * a * f⁻¹ * a⁻¹ = f * (a * f⁻¹ * a⁻¹) := by group
          rw [e]
          exact (FAsub G A).mul_mem hf (conj_FA ha ((FAsub G A).inv_mem hf))
        exact B1.mem_preB.2 ⟨hFA, (fS * aS * fS⁻¹ * aS⁻¹).2, hmem⟩
  have hF_le : Fbar G A ≤ H₀ := by
    intro φ hφ
    obtain ⟨g, hg, rfl⟩ := mem_autSub.1 hφ
    obtain ⟨-, h, hH⟩ := B1.mem_preB.1 (hFA_pre hg)
    exact hH
  have hHeq : Hbar G A = H₀ := le_antisymm (sup_le hF_le hAH₀) (hHle H₀ hH₀)
  obtain ⟨e, φ, -⟩ := hnat H₀ hH₀
  have hH6 : Nat.card ↥H₀ = 6 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  have hc4 : Nat.card ↥(commV H₀) = 4 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_eq_fintype_card]
    decide +kernel
  have hFdvd : Nat.card ↥(Fbar G A) ∣ 6 := by
    rw [← hH6]
    exact Subgroup.card_dvd_of_le hF_le
  have hFodd : Odd (Nat.card ↥(Fbar G A)) := by
    rw [P.Fbar_card hV]
    exact P.odd_card_FA
  have hF3 : Nat.card ↥(Fbar G A) = 3 := by
    have h3 : Nat.card ↥(Fbar G A) ∣ 3 :=
      Nat.Coprime.dvd_of_dvd_mul_right (Nat.coprime_two_left.2 hFodd).symm
        (by simpa using hFdvd)
    rcases (Nat.dvd_prime Nat.prime_three).1 h3 with h | h
    · exfalso
      rw [P.Fbar_card hV] at h
      exact P.hF (Subgroup.eq_bot_of_card_eq _ h)
    · exact h
  have hFA3 : Nat.card ↥(FAsub G A) = 3 := by
    rw [← P.Fbar_card hV]
    exact hF3
  have hcommF : commV (Fbar G A) = ⊤ := by
    have h1 := map_commSub_autSub (FA_le_stab G A) (⊤ : Subgroup ↥(Wsub G A))
    rw [Subgroup.map_top, Subgroup.range_subtype, P.comm_W_FA hV] at h1
    show commV (autSub (FAsub G A) (Wsub G A)) = ⊤
    rw [commV_eq_commSub]
    apply Subgroup.map_injective (Wsub G A).subtype_injective
    rw [h1, Subgroup.map_top, Subgroup.range_subtype]
  have hW4 : Nat.card ↥(Wsub G A) = 4 := by
    have hle : commV (Fbar G A) ≤ commV H₀ := commV_mono hF_le
    have htop : commV H₀ = ⊤ := top_le_iff.1 (hcommF ▸ hle)
    rw [← hc4, htop, Subgroup.card_top]
  have hns : ¬ IsStrongFFStarOffender (autSub G (Wsub G A)) (autSub A (Wsub G A)) := by
    rintro ⟨-, hr⟩
    exact hnoStrong _ ⟨P.offender_Hbar hV, hr⟩
  obtain ⟨hWsup, hAcent⟩ :=
    (B1_5_2 hV P.hA (fun _ ha w hw => P.W_inv_A ha w hw) (P.commSub_W_A_ne_bot hV)).2 hns
  have hB : Bsub G A = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun b hb => ?_
    have : b ∈ A ⊓ centSub (Wsub G A) := ⟨B_le_A hb, fun w hw => W_le_C hw b hb⟩
    rw [hAcent] at this
    exact this
  have hC : Csub G A = ⊤ := by
    show fixV (Bsub G A) = ⊤
    rw [hB, B1.fixV_bot]
  have hWcomm : Wsub G A = commV (FAsub G A) := by
    show commSub (Csub G A) (FAsub G A) = _
    rw [hC, commV_eq_commSub]
  have hA2 : Nat.card ↥A = 2 := by
    have h := card_autSub_mul P.A_le_stab
    rw [hAcent, Subgroup.card_bot, mul_one] at h
    rw [← h]
    exact hcard
  have hHtop : ∀ ψ : MulAut ↥(Wsub G A), ψ ∈ Hbar G A := by
    intro ψ
    have htop : commV H₀ = ⊤ := by
      have hle : commV (Fbar G A) ≤ commV H₀ := commV_mono hF_le
      exact top_le_iff.1 (hcommF ▸ hle)
    have := mem_of_actsAsNaturalL2_top (htop ▸ hnat H₀ hH₀) ψ
    rw [hHeq]
    exact this
  refine ⟨hA2, hFA3, by rw [← hWcomm]; exact hW4, hWcomm, hB, by rw [← hWcomm]; exact hWsup,
    hHtop, ⟨(MulEquiv.subgroupCongr hHeq).trans e⟩⟩

end B19Loc

end CFSG.Quasithin
