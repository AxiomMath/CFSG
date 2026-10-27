module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ua
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uj
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Eq
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22u
public import CFSG.RankThree.PartTwo.Sec11.Item116E2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] [Finite G]

theorem uc22p22u_isCyclic_map_iff {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Injective f) (H : Subgroup A) : IsCyclic ↥(H.map f) ↔ IsCyclic ↥H := by
  have e := H.equivMapOfInjective f hf
  exact ⟨fun h => isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective,
    fun h => isCyclic_of_surjective e.toMonoidHom e.surjective⟩

theorem uc22p22u_fitting_isCyclic {Q : Type*} [Group Q] [Finite Q] (N : Subgroup Q) [N.Normal]
    (hQ2 : CFSG.pCore 2 Q = ⊥)
    (h : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ D : Subgroup Q, D.Normal → D ≤ N → IsPGroup r D →
      ¬ IsCyclic ↥D → (∀ x ∈ D, x ^ r = 1) → ⁅⁅D, D⁆, D⁆ = ⊥ → False) :
    IsCyclic ↥(CFSG.fittingSubgroup ↥N) := by
  haveI : IsZGroup ↥(CFSG.fittingSubgroup ↥N) := by
    refine ⟨fun ℓ hℓ P => ?_⟩
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    haveI hPchar : (P : Subgroup ↥(CFSG.fittingSubgroup ↥N)).Characteristic :=
      Sylow.characteristic_of_normal P inferInstance
    set P' : Subgroup ↥N := (P : Subgroup ↥(CFSG.fittingSubgroup ↥N)).map
      (CFSG.fittingSubgroup ↥N).subtype with hP'
    haveI hP'char : P'.Characteristic := inferInstance
    set R : Subgroup Q := P'.map N.subtype with hR
    haveI hRn : R.Normal := inferInstance
    have hRcyc : IsCyclic ↥R ↔ IsCyclic ↥(P : Subgroup ↥(CFSG.fittingSubgroup ↥N)) := by
      rw [hR, uc22p22u_isCyclic_map_iff _ N.subtype_injective, hP', uc22p22u_isCyclic_map_iff _
        (CFSG.fittingSubgroup ↥N).subtype_injective]
    have hRp : IsPGroup ℓ ↥R := by
      have h1 : IsPGroup ℓ ↥((P : Subgroup ↥(CFSG.fittingSubgroup ↥N)).map
          (CFSG.fittingSubgroup ↥N).subtype) := (P.isPGroup').map _
      exact h1.map _
    by_cases hℓ2 : ℓ = 2
    · subst hℓ2
      have hRle : R ≤ CFSG.pCore 2 Q := le_sSup ⟨hRn, hRp⟩
      rw [hQ2, le_bot_iff] at hRle
      refine hRcyc.1 ?_
      rw [hRle]
      infer_instance
    · by_contra hnc
      rw [← hRcyc] at hnc
      obtain ⟨D₀, hD₀c, hD₀nc, hD₀e, hD₀z⟩ :=
        uc22p22u_exists_noncyclic_critical hℓ hℓ2 hRp hnc
      haveI : D₀.Characteristic := hD₀c
      refine h ℓ hℓ hℓ2 (D₀.map R.subtype) inferInstance ?_ ?_ ?_ ?_ ?_
      · exact (Subgroup.map_subtype_le D₀).trans (Subgroup.map_subtype_le _)
      · exact (hRp.to_subgroup D₀).map _
      · rwa [uc22p22u_isCyclic_map_iff _ R.subtype_injective]
      · rintro _ ⟨d, hd, rfl⟩
        rw [← map_pow, hD₀e d hd, map_one]
      · rw [← Subgroup.map_commutator, ← Subgroup.map_commutator, eq_bot_iff]
        rintro _ ⟨x, hx, rfl⟩
        have hx1 : x = 1 := by
          have h2 : ⁅D₀, D₀⁆ ≤ Subgroup.centralizer (D₀ : Set ↥R) :=
            ((Subgroup.commutator_mono le_rfl le_top).trans hD₀z).trans inf_le_right
          have h3 : ⁅⁅D₀, D₀⁆, D₀⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 h2
          rw [h3] at hx
          exact hx
        rw [hx1, map_one]
        exact one_mem _
  infer_instance


theorem uc22p22u_no_critical (D : Data G) (hSig : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h63 : UC6.R6_3 D) (h77 : F07.R77Eq D) (h111 : F11.R111 D) (h112 : F11.R112 D) {V : Subgroup G}
    (hV : F11.Hyp11 D ⊥ V) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {D₁ : Subgroup (Bar2 D.M)} [D₁.Normal]
    (hD₁N : D₁ ≤ barImage D.M (F11.CTilde D.M ⊥ V)) (hD₁p : IsPGroup r ↥D₁) (hnc : ¬ IsCyclic ↥D₁)
    (hexp : ∀ x ∈ D₁, x ^ r = 1) (hcl : ⁅⁅D₁, D₁⁆, D₁⁆ = ⊥) : False := by
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨hW, hTI⟩ := uc22p22u_hyp11_W D hV
  have hVc := uc22p22u_cTilde_bot D.M V
  have h112V := h112 ⊥ V hV
  generalize hX : F11.CTilde D.M ⊥ V = X at hD₁N hVc h112V
  have hXM : X ≤ D.M := by rw [hVc]; exact inf_le_left
  have hXC : X ≤ centralizer (V : Set G) := by rw [hVc]; exact inf_le_right
  have hO : pCoreOf 2 D.M ≤ X := by
    rw [hVc]
    exact le_inf (uc22p21c_pCoreOf_le D.M) (uc22p22u_pCore_le_cent hW)
  have hYX : barPreimage D.M D₁ ≤ X := uc22p22u_barPreimage_le hO hD₁N
  have hYn := uc22p22u_barPreimage_normalizes (D := D₁)
  obtain ⟨P, hPsyl, hPbar, hPK⟩ := uc22p22u_exists_lift hr hr2 hD₁p
  have hPY : P ≤ barPreimage D.M D₁ := (CFSG.ABGLocalTools.isSylowOf_iff.1 hPsyl).1
  have hPp : IsPGroup r ↥P := (CFSG.ABGLocalTools.isSylowOf_iff.1 hPsyl).2.1
  have hPX : P ≤ X := hPY.trans hYX
  have hPM : P ≤ D.M := hPX.trans hXM
  obtain ⟨hPe, hPc, hPnc⟩ := uc22p22u_lift_props (r := r) hPbar hPK hPM
  have hPexp := hPe hexp
  have hPcl := hPc hcl
  have hPnc' := hPnc hnc
  have hcyc : (rankThreeGamma 1 r P ≤ D.M ∨ r ∈ D.sig) → False := fun hΓ => by
    have h1 := uc22p22u_isCyclic_inf_centralizer D h61 h63 hV hr hr2 hPM hPp hΓ
    have hPC : P ⊓ centralizer (V : Set G) = P := inf_eq_left.2 (hPX.trans hXC)
    rw [hPC] at h1
    exact hPnc' h1
  by_cases hrσ : r ∈ D.sig
  · exact hcyc (Or.inr hrσ)
  · by_cases hs2 : D.sig2.Nonempty
    · have h := h112V hs2
      have hN : barImage D.M X = ⊥ := by
        rw [h]
        exact uc22p22u_barImage_pCore D.M
      have hD1 : D₁ = ⊥ := le_bot_iff.1 (hN ▸ hD₁N)
      apply hnc
      rw [hD1]
      infer_instance
    · have h3 := h111 ⊥ V hV
      obtain ⟨p₁, hp₁⟩ := hSig.nonempty
      have hσ1 : D.sig ⊆ D.sig1 := by
        intro q hq
        have h4 : q ∈ D.sig1 ∪ D.sig2 ∪ D.sig3 := D.sig_sub ▸ hq
        rcases h4 with (h | h) | h
        · exact h
        · exact absurd ⟨q, h⟩ hs2
        · rw [h3] at h
          exact absurd h (Set.notMem_empty _)
      have hp₁1 : p₁ ∈ D.sig1 := hσ1 hp₁
      have hsp := hSig.sig1_sp p₁ hp₁1
      obtain ⟨hp₁pr, hp₁2⟩ := D.sig_prime p₁ hp₁
      have hcard := uc22p22u_card_barPreimage D.M D₁
      have hp₁Y : ¬ p₁ ∣ Nat.card ↥(barPreimage D.M D₁) := by
        rw [hcard]
        intro hd
        rcases (Nat.Prime.dvd_mul hp₁pr).1 hd with h | h
        · obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (uc22p21c_isPGroup_pCoreOf D.M)
          rw [hk] at h
          exact hp₁2 ((Nat.prime_dvd_prime_iff_eq hp₁pr Nat.prime_two).1 (hp₁pr.dvd_of_dvd_pow h))
        · obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hD₁p
          rw [hk] at h
          have : p₁ = r := (Nat.prime_dvd_prime_iff_eq hp₁pr hr).1 (hp₁pr.dvd_of_dvd_pow h)
          exact hrσ (this ▸ hp₁)
      have hrank := uc22p22u_pRank_le_normalizer_sylow hp₁pr hr (hYX.trans hXM) hYn hPsyl hp₁Y
      have hrank' : CFSG.Open.pRank p₁ (D.M ⊓ normalizer (P : Set G)) ≤ CFSG.Open.pRank p₁ D.M :=
        CFSG.SectionRank.pRank_mono hp₁pr.one_lt inf_le_left
      have hthree : 3 ≤ CFSG.Open.pRank p₁ D.M := hSig.three_le p₁ hp₁
      have hΓ := h77 hσ1 p₁ hp₁ hp₁2 hsp r hr hr2 hrσ P hPM hPp hPnc' hPexp hPcl (by omega)
        (le_antisymm hrank hrank')
      exact hcyc (Or.inl hΓ)

@[expose] def C116 (D : Data G) (V₀ V : Subgroup G) : Prop :=
  IsCyclic ↥(CFSG.fittingSubgroup ↥(barImage D.M (F11.CTilde D.M V₀ V))) ∧
    ⁅(⊤ : Subgroup (Bar2 D.M)), (⊤ : Subgroup (Bar2 D.M))⁆ ≤
      centralizer (((CFSG.fittingSubgroup ↥(barImage D.M (F11.CTilde D.M V₀ V))).map
        (barImage D.M (F11.CTilde D.M V₀ V)).subtype : Subgroup (Bar2 D.M)) : Set (Bar2 D.M))

@[expose] def R116W (D : Data G) : Prop := ∀ V : Subgroup G, F11.Hyp11 D ⊥ V → C116 D ⊥ V

theorem uc22p22u_c116W (D : Data G) (hSig : UC6S846.SigmaStd D) (h61 : UC6.R6_1 D)
    (h63 : UC6.R6_3 D) (h77 : F07.R77Eq D) (h111 : F11.R111 D) (h112 : F11.R112 D) : R116W D := by
  intro V hV
  obtain ⟨hW, -⟩ := uc22p22u_hyp11_W D hV
  have hVc := uc22p22u_cTilde_bot D.M V
  have hn : D.M ≤ normalizer ((F11.CTilde D.M ⊥ V : Subgroup G) : Set G) := by
    rw [hVc]
    exact uc22p22u_normalizes_cent hW.1.1.2.2.1
  haveI hNn : (barImage D.M (F11.CTilde D.M ⊥ V)).Normal := uc22p22u_barImage_normal hn
  have hQ2 : CFSG.pCore 2 (Bar2 D.M) = ⊥ := CFSG.RankThree.PartTwo.Sec11.pCore_quotient_pCore ↥D.M 2
  have hcyc : IsCyclic ↥(CFSG.fittingSubgroup ↥(barImage D.M (F11.CTilde D.M ⊥ V))) :=
    uc22p22u_fitting_isCyclic _ hQ2 fun r hr hr2 D₁ hD₁n hD₁N hD₁p hnc hexp hcl =>
      haveI := hD₁n
      uc22p22u_no_critical D hSig h61 h63 h77 h111 h112 hV hr hr2 hD₁N hD₁p hnc hexp hcl
  refine ⟨hcyc, ?_⟩
  haveI : ((CFSG.fittingSubgroup ↥(barImage D.M (F11.CTilde D.M ⊥ V))).map
      (barImage D.M (F11.CTilde D.M ⊥ V)).subtype).Normal := inferInstance
  haveI : IsCyclic ↥((CFSG.fittingSubgroup ↥(barImage D.M (F11.CTilde D.M ⊥ V))).map
      (barImage D.M (F11.CTilde D.M ⊥ V)).subtype) :=
    (uc22p22u_isCyclic_map_iff _ (Subgroup.subtype_injective _) _).2 hcyc
  exact uc22p21c_commutator_le_centralizer_of_cyclic _


end CFSG.LocalAnalysis.UniquenessCase.UC22
