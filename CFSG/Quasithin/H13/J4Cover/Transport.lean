module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovQDef
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocTransport
public import CFSG.Quasithin.EmptyFaithful.ModJ4TLC
public import CFSG.HardMathSupport.Cooperstein.Proving.QuotientPCoreTransfer

public section

namespace CFSG.Quasithin.H13.J4Cover

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4Loc

theorem j4CoverFacts_of_model
    (ha : ∀ X : Subgroup J, P0 ≤ X → 5 ∣ Nat.card X → ¬ 9 ∣ Nat.card X →
      X ≤ Subgroup.centralizer ({z0} : Set J))
    (hb : ∀ B : Subgroup J, ⁅B, B⁆ = B → P0 ≤ Subgroup.normalizer (B : Set J) →
      CFSG.Quasithin.IsHat (↥B ⧸ CFSG.pCore 2 ↥B) (alternatingGroup (Fin 6)) →
      B ≤ Subgroup.centralizer ({z0} : Set J))
    (hc : ∃ (R : Type) (_ : Group R) (_ : Finite R)
      (ρ : ↥(Subgroup.centralizer ({z0} : Set J)) →* R), Function.Surjective ρ ∧
      (∀ d ∈ ρ.ker, ∃ n : ℕ, d ^ (2 ^ n) = 1) ∧
      ∃ N₀ : Subgroup R, N₀.Normal ∧ N₀.index = 2 ∧
        CFSG.Quasithin.IsHat ↥N₀ (CFSG.Blueprint.NativeSporadic.Carrier .M22)) :
    CFSG.Quasithin.H13.J4CoverFacts := by
  intro Q _ _ hQ S _ hScard
  have hF : J4Facts := j4Facts
  have hM : MatFacts := hF.mat
  obtain ⟨e₀⟩ := hQ
  let e : Q ≃* J := e₀.trans (seedEquiv hM)
  have hQcard : Nat.card Q = Nat.card J := Nat.card_congr e.toEquiv
  have hfac : (Nat.card Q).factorization 2 = 21 := by
    rw [hQcard]
    exact card_J_factorization hF
  have hSfac : Nat.card S = 2 ^ (Nat.card Q).factorization 2 := by
    rw [hfac, hScard]
  let Ss : Sylow 2 Q := Sylow.ofCard S hSfac
  have hSylow : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ := by
    have h := CFSG.QuasithinUnique.K1.isSylowTwoOf_top_iff.2
      ⟨Ss.isPGroup', Ss.not_dvd_index⟩
    rwa [Sylow.coe_ofCard] at h
  obtain ⟨ψ, hψ⟩ := sylow_transport (Γ := J) isSylowTwoOf_P0 e hSylow
  let z₁ : Q := ψ.symm z0
  have hz₁z0 : ψ z₁ = z0 := ψ.apply_symm_apply z0
  have hz0P : z0 ∈ P0 := (CFSG.Quasithin.ModJ4.tlc_z0_mem_center_P0).1
  have hz0c : ∀ y ∈ P0, y * z0 = z0 * y :=
    (CFSG.Quasithin.ModJ4.tlc_z0_mem_center_P0).2
  have hz0sq : z0 ^ 2 = 1 := by
    have hord : orderOf z0 = 2 := CFSG.Quasithin.ModJ4.tlc_orderOf_z0
    have h := pow_orderOf_eq_one z0
    rwa [hord] at h
  have hz₁S : z₁ ∈ S := by
    have h : z0 ∈ Subgroup.map (ψ : Q →* J) S := by
      rw [hψ]
      exact hz0P
    simpa [z₁] using (Subgroup.mem_map_equiv (f := ψ) (K := S) (x := z0)).mp h
  have hz₁ne : z₁ ≠ 1 := by
    intro h
    apply z0_ne_one hM
    rw [← hz₁z0, h, map_one]
  have hz₁sq : z₁ ^ 2 = 1 := by
    apply ψ.injective
    rw [map_pow, hz₁z0, map_one]
    exact hz0sq
  have hz₁c : ∀ s ∈ S, s * z₁ = z₁ * s := by
    intro s hs
    apply ψ.injective
    have hmem : ψ s ∈ P0 := by
      rw [← hψ]
      exact Subgroup.mem_map_of_mem (ψ : Q →* J) hs
    have hcomm := hz0c (ψ s) hmem
    rw [map_mul, map_mul, hz₁z0]
    exact hcomm
  have hcent : Subgroup.centralizer ({z0} : Set J) =
      Subgroup.map (ψ : Q →* J) (Subgroup.centralizer ({z₁} : Set Q)) := by
    rw [← MulEquiv.toMonoidHom_eq_coe]
    rw [CFSG.Quasithin.H13.J4.map_centralizer_mulEquiv, Set.image_singleton, hz₁z0]
  refine ⟨z₁, hz₁S, hz₁ne, hz₁sq, hz₁c, ?_, ?_, ?_⟩
  · intro X hSX h5 h9
    have hP0X : P0 ≤ Subgroup.map (ψ : Q →* J) X := by
      rw [← hψ]
      exact Subgroup.map_mono hSX
    have h5' : 5 ∣ Nat.card (Subgroup.map (ψ : Q →* J) X) := by
      rwa [Subgroup.card_map_of_injective ψ.injective]
    have h9' : ¬ 9 ∣ Nat.card (Subgroup.map (ψ : Q →* J) X) := by
      rwa [Subgroup.card_map_of_injective ψ.injective]
    have hle := ha (Subgroup.map (ψ : Q →* J) X) hP0X h5' h9'
    rw [hcent] at hle
    exact (Subgroup.map_le_map_iff_of_injective ψ.injective).mp hle
  · intro B hperf hPB hB
    let B' : Subgroup J := Subgroup.map (ψ : Q →* J) B
    have hperf' : ⁅B', B'⁆ = B' := by
      have h := Subgroup.map_commutator (f := (ψ : Q →* J)) (H₁ := B) (H₂ := B)
      rw [hperf] at h
      exact h.symm
    have hPB' : P0 ≤ Subgroup.normalizer (B' : Set J) := by
      have h := Subgroup.map_mono (f := (ψ : Q →* J)) hPB
      rw [hψ] at h
      rw [← MulEquiv.toMonoidHom_eq_coe] at h
      rw [Subgroup.map_equiv_normalizer_eq] at h
      exact h
    have hB' : CFSG.Quasithin.IsHat (↥B' ⧸ CFSG.pCore 2 ↥B')
        (alternatingGroup (Fin 6)) := by
      have hq := CFSG.HardMathSupport.Cooperstein.Proving.quotientPCoreMulEquiv
        (H := ↥B) (K := ↥(Subgroup.map (ψ : Q →* J) B)) 2
        (Subgroup.equivMapOfInjective B (ψ : Q →* J) ψ.injective)
      exact CFSG.Quasithin.IsHat.of_mulEquiv hq hB
    have hle := hb B' hperf' hPB' hB'
    rw [hcent] at hle
    exact (Subgroup.map_le_map_iff_of_injective ψ.injective).mp hle
  · obtain ⟨R, instR, finR, ρ, hsurj, hker, N₀, hN₀norm, hN₀idx, hN₀hat⟩ := hc
    have hC : Subgroup.map (ψ : Q →* J) (Subgroup.centralizer ({z₁} : Set Q)) =
        Subgroup.centralizer ({z0} : Set J) := hcent.symm
    let Φ : ↥(Subgroup.centralizer ({z₁} : Set Q)) ≃*
        ↥(Subgroup.centralizer ({z0} : Set J)) :=
      (Subgroup.equivMapOfInjective (Subgroup.centralizer ({z₁} : Set Q))
        (ψ : Q →* J) ψ.injective).trans (MulEquiv.subgroupCongr hC)
    refine ⟨R, instR, finR,
      ρ.comp (Φ : ↥(Subgroup.centralizer ({z₁} : Set Q)) →*
        ↥(Subgroup.centralizer ({z0} : Set J))), ?_, ?_, N₀, hN₀norm, hN₀idx, hN₀hat⟩
    · exact hsurj.comp Φ.surjective
    · intro d hd
      have hd' : Φ d ∈ ρ.ker := hd
      obtain ⟨n, hn⟩ := hker (Φ d) hd'
      refine ⟨n, ?_⟩
      apply Φ.injective
      rw [map_pow, hn, map_one]

end CFSG.Quasithin.H13.J4Cover
