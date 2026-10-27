module

public import CFSG.Quasithin.Vol2.Ch5Sec3Lemmas
public import CFSG.Quasithin.Vol2.GoldschmidtF431Datum
public import CFSG.Quasithin.Vol2.GoldschmidtF431LieW

public section

namespace CFSG.Quasithin.H13.F431

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

@[expose] def F431Recognition (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ) : Prop :=
  ∀ (D : Type) [Group D], LieModel D t m 2 f → ∀ (A : LieAmalgamExt D) (Y : Type) [Group Y]
    [Finite Y] (β1 : ↥A.N1 →* Y) (β2 : ↥A.N2 →* Y), Function.Injective β1 →
    Function.Injective β2 →
    (∀ (x : MulAut D) (h1 : x ∈ A.N1) (h2 : x ∈ A.N2), β1 ⟨x, h1⟩ = β2 ⟨x, h2⟩) →
    (∀ y : Y, y ∈ β1.range → y ∈ β2.range →
      ∃ (x : MulAut D) (h1 : x ∈ A.N1) (_ : x ∈ A.N2), β1 ⟨x, h1⟩ = y) →
    β1.range ⊔ β2.range = ⊤ → Nat.card Y ≤ Nat.card ↥A.K →
    Nat.card Y = Nat.card ↥A.K ∧ ∃ (Ġ : Type) (_ : Group Ġ) (ν : D →* Ġ), Function.Injective ν ∧
      ν.range.Normal ∧ Subgroup.centralizer (ν.range : Set Ġ) = ⊥ ∧ Nonempty (Y ≃* Ġ)

@[expose] def F431Out (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (M1 M2 : Subgroup G), F431Hyps M1 M2 t m f → ∀ (D : Type) [Group D],
      LieModel D t m 2 f → ∀ E : LieExt D M1 M2, Odd (Nat.card ↥E.K / Nat.card D)

@[expose] def F431Local (t : CFSG.Assembly.LowTwoRank.StatedLieTag) (m f : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (M1 M2 : Subgroup G), F431Hyps M1 M2 t m f → ∀ (D : Type) [Group D],
      LieModel D t m 2 f → ∀ E : LieExt D M1 M2, Odd (Nat.card ↥E.K / Nat.card D) →
      ∃ (T : Subgroup ↥E.K) (I : Finset ↥E.K) (z : ↥E.K), F431LieK T E.Mb1 E.Mb2 I z ∧
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
          ¬ IsConj (amalgamMap E.b1 E.b2 i) (amalgamMap E.b1 E.b2 j)) ∧
        (∀ i ∈ I, Subgroup.centralizer ({i} : Set ↥E.K) ≤ E.Mb1 →
          Subgroup.centralizer ({amalgamMap E.b1 E.b2 i} : Set G) ≤ M1) ∧
        (∀ i ∈ I, Subgroup.centralizer ({i} : Set ↥E.K) ≤ E.Mb2 →
          Subgroup.centralizer ({amalgamMap E.b1 E.b2 i} : Set G) ≤ M2)

@[expose] def F431SpLocal (f : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (M1 M2 : Subgroup G), F431Hyps M1 M2 .PSp 2 f → ∀ (D : Type) [Group D],
      LieModel D .PSp 2 2 f → ∀ E : LieExt D M1 M2, Odd (Nat.card ↥E.K / Nat.card D) →
      ∃ (T : Subgroup ↥E.K) (I : Finset ↥E.K), F431LieW T E.Mb1 E.Mb2 I ∧
        (∀ i ∈ I, ∀ j ∈ I, i ≠ j →
          ¬ IsConj (amalgamMap E.b1 E.b2 i) (amalgamMap E.b1 E.b2 j)) ∧
        (∀ i ∈ I,
          (Subgroup.centralizer ({i} : Set ↥E.K) ≤ E.Mb1 ∧
            Subgroup.centralizer ({amalgamMap E.b1 E.b2 i} : Set G) ≤ M1) ∨
          (Subgroup.centralizer ({i} : Set ↥E.K) ≤ E.Mb2 ∧
            Subgroup.centralizer ({amalgamMap E.b1 E.b2 i} : Set G) ≤ M2))

@[expose] def F431L3Order (f : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ (M1 M2 : Subgroup G), F431Hyps M1 M2 .PSL 3 f → ∀ (D : Type) [Group D],
      LieModel D .PSL 3 2 f → ∀ E : LieExt D M1 M2, Nat.card G ≤ Nat.card ↥E.K

theorem f431_of_card_le {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m f : ℕ}
    (hRec : F431Recognition t m f) (G : Type) [Group G] [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (M1 M2 : Subgroup G) (D : Type) [Group D]
    (hD : LieModel D t m 2 f) (E : LieExt D M1 M2) (hcard : Nat.card G ≤ Nat.card ↥E.K) :
    LieModel G t m 2 f := by
  have hY : Nat.card ↥(M1 ⊔ M2) ≤ Nat.card ↥E.K :=
    (Nat.card_le_card_of_injective _ (M1 ⊔ M2).subtype_injective).trans hcard
  obtain ⟨hYc, Ġ, _, ν, hνi, hνn, hνc, ⟨e⟩⟩ := hRec D hD E.toLieAmalgamExt ↥(M1 ⊔ M2) E.β1 E.β2
    E.β1_injective E.β2_injective E.β_agree E.β_inter E.β_gen hY
  have hYG : Nat.card ↥(M1 ⊔ M2) = Nat.card G :=
    le_antisymm (Nat.card_le_card_of_injective _ (M1 ⊔ M2).subtype_injective) (hcard.trans hYc.ge)
  have hYtop : M1 ⊔ M2 = ⊤ := (Subgroup.card_eq_iff_eq_top (M1 ⊔ M2)).mp hYG
  let eY : G ≃* ↥(M1 ⊔ M2) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hYtop.symm)
  let eG : G ≃* Ġ := eY.trans e
  have : IsSimpleGroup Ġ := eG.symm.isSimpleGroup
  have hnab' : ∃ a b : Ġ, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    refine ⟨eG a, eG b, fun h => hab (eG.injective ?_)⟩
    rw [map_mul, map_mul]
    exact h
  obtain ⟨eD⟩ := nonempty_mulEquiv_of_normal_range hnab' ν hνi hνn hνc
  exact CFSG.LieType.CurtisTits.lieModel_of_mulEquiv (eD.trans eG.symm) hD

theorem f431_nonL3_of_inputs {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {m f : ℕ}
    (hRec : F431Recognition t m f) (hOut : F431Out t m f) (hLoc : F431Local t m f)
    (G : Type) [Group G] [Finite G] (hG : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (M1 M2 : Subgroup G) (hyps : F431Hyps M1 M2 t m f) : LieModel G t m 2 f := by
  obtain ⟨D, _, hD, hext⟩ := hyps.1
  obtain ⟨E⟩ := isExtensionOfLieAmalgam_iff.mp hext
  have hodd := hOut G hG hnab M1 M2 hyps D hD E
  have hKne : Nat.card ↥E.K ≠ 0 := by
    intro h
    rw [h, Nat.zero_div] at hodd
    exact absurd hodd (by decide)
  have : Finite ↥E.K := Nat.finite_of_card_ne_zero hKne
  obtain ⟨T, I, z, hLK, hnf, hc1, hc2⟩ := hLoc G hG hnab M1 M2 hyps D hD E hodd
  have hcard : Nat.card ↥E.K = Nat.card G :=
    hLK.card_eq E.comp hnf (fun i hi h => (hc1 i hi h).trans E.range_b1.ge)
      (fun i hi h => (hc2 i hi h).trans E.range_b2.ge)
  exact f431_of_card_le hRec G hG hnab M1 M2 D hD E hcard.ge

theorem isSylowTwoOf_image_of_odd_index {Mb : Type*} [Group Mb] {G : Type*} [Group G]
    {T M1 M2 : Subgroup Mb} {M1G M2G : Subgroup G} {b1 : M1 →* G} {b2 : M2 →* G}
    (C : F431Comp M1 M2 b1 b2) (hb1 : b1.range = M1G) (hb2 : b2.range = M2G)
    (hT : IsSylowTwoOf T ⊤) (hT1 : T ≤ M1) (hT2 : T ≤ M2)
    (hodd : ¬ 2 ∣ (M1G ⊓ M2G).index) :
    IsSylowTwoOf ((T.subgroupOf M1).map b1) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P : Subgroup G := (T.subgroupOf M1).map b1 with hP
  have hTp : IsPGroup 2 (T.subgroupOf M1) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT1).symm
  have hPp : IsPGroup 2 P := hTp.of_equiv (Subgroup.equivMapOfInjective _ b1 C.inj₁)
  have hSylM1 : IsSylowTwoOf P b1.range := by
    refine F7.isSylowTwoOf_of_relIndex (Subgroup.map_le_range b1 _) hPp ?_
    have h1 : P.relIndex b1.range = (T.subgroupOf M1).relIndex ⊤ := by
      rw [hP, MonoidHom.range_eq_map]
      exact Subgroup.relIndex_map_map_of_injective _ _ C.inj₁
    rw [h1, Subgroup.relIndex_top_right]
    exact (F7.isSylowTwoOf_mono_right hT hT1 le_top).2.2
  have hPM2 : P ≤ M2G := by
    rintro _ ⟨y, hy, rfl⟩
    have hyT : (y : Mb) ∈ T := hy
    have hy2 : (y : Mb) ∈ M2 := hT2 hyT
    have := amalgamMap_of_mem₁ b1 b2 (y.2)
    rw [amalgamMap_of_mem₂ b1 b2 C.agree hy2] at this
    rw [← hb2]
    exact ⟨_, this⟩
  have hPM1 : P ≤ M1G := hb1 ▸ Subgroup.map_le_range b1 _
  have hSyl12 : IsSylowTwoOf P (M1G ⊓ M2G) :=
    F7.isSylowTwoOf_mono_right (hb1 ▸ hSylM1) (le_inf hPM1 hPM2) inf_le_left
  refine F7.isSylowTwoOf_of_relIndex le_top hPp ?_
  rw [Subgroup.relIndex_top_right,
    ← Subgroup.relIndex_mul_index (le_inf hPM1 hPM2 : P ≤ M1G ⊓ M2G)]
  intro hdvd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hdvd with h | h
  · exact hSyl12.2.2 h
  · exact hodd h

theorem f431_sp_of_inputs {f : ℕ} (hRec : F431Recognition .PSp 2 f) (hOut : F431Out .PSp 2 f)
    (hLoc : F431SpLocal f) (G : Type) [Group G] [Finite G] (hG : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (M1 M2 : Subgroup G) (hyps : F431Hyps M1 M2 .PSp 2 f) :
    LieModel G .PSp 2 2 f := by
  obtain ⟨D, _, hD, hext⟩ := hyps.1
  obtain ⟨E⟩ := isExtensionOfLieAmalgam_iff.mp hext
  have hodd := hOut G hG hnab M1 M2 hyps D hD E
  have hKne : Nat.card ↥E.K ≠ 0 := by
    intro h
    rw [h, Nat.zero_div] at hodd
    exact absurd hodd (by decide)
  have : Finite ↥E.K := Nat.finite_of_card_ne_zero hKne
  obtain ⟨T, I, hLW, hnf, hc⟩ := hLoc G hG hnab M1 M2 hyps D hD E hodd
  have hSyl := isSylowTwoOf_image_of_odd_index E.comp E.range_b1 E.range_b2 hLW.sylow hLW.T_le₁
    hLW.T_le₂ (hyps.2.2.2.2 rfl).2
  have hcard : Nat.card ↥E.K = Nat.card G :=
    hLW.card_eq E.comp hSyl hnf (fun i hi => by
      rcases hc i hi with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨h1, h2.trans E.range_b1.ge⟩
      · exact Or.inr ⟨h1, h2.trans E.range_b2.ge⟩)
  exact f431_of_card_le hRec G hG hnab M1 M2 D hD E hcard.ge

end CFSG.Quasithin.H13.F431
