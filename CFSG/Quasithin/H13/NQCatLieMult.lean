module

public import CFSG.Quasithin.Vol2.Ch7Sec77Inputs
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.LinearCentralCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.UnitaryCentralCover
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MatrixFieldTransport
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverLarge
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
public import CFSG.LieType.Chevalley.ExceptionalLargeEvenCoverSeries
public import CFSG.LieType.Chevalley.TrialityCover
public import CFSG.LieType.Ree.LargeReeCentralTwoCover
public import CFSG.LieType.Ree.LargeReeEightCentralTwoCover
public import CFSG.LieType.Simplicity.Suzuki
public import CFSG.LieType.Steinberg.CentralExt.SuzukiMultiplier
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82

public section

namespace CFSG.Quasithin.H13.NQCat.LieMult

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.LocalAnalysis.ComponentInitial

@[expose] def NoCentralE16 (S : Type) [Group S] : Prop :=
  ∀ P E : Subgroup S, IsSylowTwoOf P ⊤ → E ≤ P → IsElemAbelian 2 E → Nat.card E = 16 →
    E ≤ Subgroup.centralizer (P : Set S) → False

@[expose] def L34NoCentralE16 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsPSL 3 2 2 S → NoCentralE16 S

@[expose] def G24NoCentralE16 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsG2 2 2 S → NoCentralE16 S

@[expose] def Sz8NoCentralE16 : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSz 3 S → NoCentralE16 S

section NoCentral

variable {S T : Type} [Group S] [Group T]

theorem NoCentralE16.of_mulEquiv (e : S ≃* T) (h : NoCentralE16 T) : NoCentralE16 S := by
  intro P E hP hEP hE hcard hEZ
  refine h (P.map e.toMonoidHom) (E.map e.toMonoidHom) ⟨le_top, hP.2.1.map _, ?_⟩
    (Subgroup.map_mono hEP) ?_ ?_ ?_
  · have h1 := hP.2.2
    rw [show (P.subgroupOf ⊤).index = P.index from Subgroup.relIndex_top_right P] at h1
    rw [show ((P.map e.toMonoidHom).subgroupOf ⊤).index = (P.map e.toMonoidHom).index from
      Subgroup.relIndex_top_right _, MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
    exact h1
  · have := hE.1
    refine ⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩
    · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
      obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [← map_mul, ← map_mul]
      exact congrArg e.toMonoidHom (congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : E) ⟨y, hy⟩))
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hE.2 x hx, map_one]
  · rw [Subgroup.card_map_of_injective e.injective, hcard]
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨y, hy, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp (hEZ hx) y hy
    change e y * e x = e x * e y
    rw [← map_mul, ← map_mul, h1]

theorem noCentralE16_of_sylow [Finite S] {U : Subgroup S} (hU : IsSylowTwoOf U ⊤)
    (h : ∀ E : Subgroup S, E ≤ U → E ≤ Subgroup.centralizer (U : Set S) → Nat.card E < 16) :
    NoCentralE16 S := by
  intro P E hP hEP _ hcard hEZ
  obtain ⟨g, -, rfl⟩ := hU.exists_conj hP
  have hid : (MulAut.conj g⁻¹).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      MonoidHom.id S := by
    ext x
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, MonoidHom.id_apply]
    group
  have h1 := h (E.map (MulAut.conj g⁻¹).toMonoidHom) ?_ ?_
  · rw [Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hcard] at h1
    exact lt_irrefl _ h1
  · have h2 := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hEP
    rwa [Subgroup.map_map, hid, Subgroup.map_id] at h2
  · rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have h2 := Subgroup.mem_centralizer_iff.mp (hEZ hx) (g * u * g⁻¹) ⟨u, hu, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc u * (g⁻¹ * x * g⁻¹⁻¹) = g⁻¹ * ((g * u * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * u * g⁻¹)) * g := by rw [h2]
      _ = g⁻¹ * x * g⁻¹⁻¹ * u := by group

end NoCentral

theorem eq_bot_of_cover {X J : Type} [Group X] [Group J] {Z : Subgroup X} [Z.Normal]
    (hZ : Z ≤ Subgroup.center X) (h2 : IsPGroup 2 Z) (e : X ⧸ Z ≃* J)
    (h : ∀ η : X →* J, Function.Surjective η → η.ker ≤ Subgroup.center X → IsPGroup 2 η.ker →
      η.ker = ⊥) : Z = ⊥ := by
  have hker : (e.toMonoidHom.comp (QuotientGroup.mk' Z)).ker = Z := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have h1 := h _ (e.surjective.comp (QuotientGroup.mk'_surjective Z)) (by rw [hker]; exact hZ)
    (by rw [hker]; exact h2)
  rwa [hker] at h1

theorem charP_two_of_card {K : Type} [Field K] [Finite K] {k : ℕ} (hK : Nat.card K = 2 ^ k) :
    CharP K 2 := by
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow (f := k) (by rw [← Nat.card_eq_fintype_card, hK])

variable {X : Type} [Group X] [Finite X] [Group.IsPerfect X] {Z : Subgroup X} [Z.Normal]

theorem eq_bot_psl2 (hZ : Z ≤ Subgroup.center X) (h2 : IsPGroup 2 Z) {k : ℕ} (hk : 2 ≤ k)
    (hL : IsPSL 2 2 k (X ⧸ Z)) {E : Subgroup (X ⧸ Z)} (hE : Nat.card E = 16) : Z = ⊥ := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL
  rcases (by omega : k = 2 ∨ 3 ≤ k) with rfl | hk3
  · exfalso
    have hcard : Nat.card (X ⧸ Z) = 60 := by
      rw [Nat.card_congr e.toEquiv,
        ← Nat.card_congr (projectiveSpecialLinearGroupEquivStatedProj 2 K).toEquiv,
        CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear K 2 (by norm_num), hK]
      decide
    have h1 := Subgroup.card_subgroup_dvd_card E
    rw [hE, hcard] at h1
    norm_num at h1
  · have := charP_two_of_card hK
    exact eq_bot_of_cover hZ h2
      (e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
        CFSG.ShultStronglyClosedTI.glaSLQuotientEquivPSL.symm)) fun η hη hC hp =>
      (CFSG.ShultStronglyClosedTI.large_even_linear_central_two_cover_trivial k hk3 hK η hη hC
        hp).1

theorem eq_bot_psl3 (hZ : Z ≤ Subgroup.center X) (h2 : IsPGroup 2 Z) {k : ℕ} (hk : 3 ≤ k)
    (hL : IsPSL 3 2 k (X ⧸ Z)) : Z = ⊥ :=
  eq_bot_of_cover hZ h2 (MulEquiv.refl _) fun η hη hC hp =>
    (LinearCover.even_linear_three_large_field_catalog_central_two_cover_trivial η hη hC hp hk
      (Or.inl ⟨by decide, hL⟩)).1

theorem eq_bot_psu3 (hZ : Z ≤ Subgroup.center X) (h2 : IsPGroup 2 Z) {k : ℕ} (hk : 2 ≤ k)
    (hL : IsPSU 3 2 k (X ⧸ Z)) : Z = ⊥ := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hL
  have hK' : Nat.card K = 2 ^ (2 * k) := by rw [hK, ← pow_mul, mul_comm]
  have := charP_two_of_card hK'
  exact eq_bot_of_cover hZ h2 e fun η hη hC hp =>
    (CFSG.ShultStronglyClosedTI.even_unitary_three_perfect_central_two_cover_trivial k hk hK' η hη
      hC hp).1

theorem eq_bot_psp4 (hZ : Z ≤ Subgroup.center X) (h2 : IsPGroup 2 Z) {k : ℕ} (hk : 2 ≤ k)
    (hL : IsPSp4 2 k (X ⧸ Z)) : Z = ⊥ :=
  eq_bot_of_cover hZ h2 (MulEquiv.refl _) fun η hη hC hp =>
    (SymplecticCoverFour.even_symplectic_four_catalog_perfect_central_two_cover_trivial η hη hC
      hp hk (Or.inl ⟨by decide, hL⟩)).1

theorem eq_bot_g2
    (hZ : Z ≤ Subgroup.center X) (h2 : IsPGroup 2 Z) {k : ℕ} (hk : 3 ≤ k)
    (hL : IsG2 2 k (X ⧸ Z)) : Z = ⊥ := by
  obtain ⟨-, hm⟩ := hL
  exact eq_bot_of_cover hZ h2 (MulEquiv.refl _) fun η hη hC hp =>
    (CFSG.LieType.Chevalley.untwisted_large_even_central_two_cover_trivial (Or.inl rfl) η hη hC hp
      hk hm).1

theorem eq_bot_d4
    (hZ : Z ≤ Subgroup.center X) (h2 : IsPGroup 2 Z) {k : ℕ} (hk : 2 ≤ k)
    (hL : Is3D4 2 k (X ⧸ Z)) : Z = ⊥ :=
  eq_bot_of_cover hZ h2 (MulEquiv.refl _) fun η hη hC hp =>
    (CFSG.LieType.Chevalley.triality_nonprime_even_field_central_two_cover_trivial η hη hC hp hk
      (Or.inr (Or.inl ⟨rfl, by decide, hL⟩))).1

theorem eq_bot_f4
    (hZ : Z ≤ Subgroup.center X) (h2 : IsPGroup 2 Z) {k : ℕ} (hk : 2 ≤ k)
    (hL : Is2F4 k (X ⧸ Z)) : Z = ⊥ := by
  obtain ⟨a, rfl⟩ : ∃ a, k = 2 * a + 1 := by
    obtain ⟨-, a, ha, -⟩ := hL
    exact ⟨a, ha⟩
  have hLM : CFSG.Blueprint.LieModel (X ⧸ Z) .twistedF4 0 2 (2 * a + 1) :=
    Or.inr (Or.inr (Or.inl ⟨rfl, by decide, hL⟩))
  rcases (by omega : a = 1 ∨ 2 ≤ a) with rfl | ha
  · exact eq_bot_of_cover hZ h2 (MulEquiv.refl _) fun η hη hC hp =>
      (CFSG.LieType.Ree.large_Ree_field_eight_central_two_cover_trivial η hη hC hp hLM).1
  · exact eq_bot_of_cover hZ h2 (MulEquiv.refl _) fun η hη hC hp =>
      (CFSG.LieType.Ree.large_Ree_large_even_field_central_two_cover_trivial η hη hC hp
        (by omega) hLM).1

theorem eq_bot_sz (hZ : Z ≤ Subgroup.center X) (h2 : IsPGroup 2 Z) {k : ℕ} (hk : 4 ≤ k)
    (hL : IsSz k (X ⧸ Z)) : Z = ⊥ := by
  obtain ⟨-, a, ha, K, _, _, rfl, hK, ⟨e⟩⟩ := hL
  exact eq_bot_of_cover hZ h2 (e.trans ((MulEquiv.subgroupCongr
    (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K)).trans
    ((CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hK).trans
      (CFSG.ShultStronglyClosedTI.suzukiCoverNativeEquiv a)))) fun η hη hC hp =>
    CFSG.LieType.Steinberg.CentralExt.SuzukiClosed.suzuki_two_cover_trivial (m := a) (by omega) η
      hη hC hp

theorem lieMultiplierFact_of
    (hL34 : L34NoCentralE16) (hG24 : G24NoCentralE16) (hSz8 : Sz8NoCentralE16) :
    LieMultiplierFact := by
  intro X _ _ _ Z _ hZ h2 ⟨k, hk, hL⟩ P E hP hEP hE hcard hEZ
  rcases hL with h | h | h | h | h | h | h | h
  · exact eq_bot_psl2 hZ h2 hk h hcard
  · rcases (by omega : k = 2 ∨ 3 ≤ k) with rfl | hk3
    · exact (hL34 _ h P E hP hEP hE hcard hEZ).elim
    · exact eq_bot_psl3 hZ h2 hk3 h
  · exact eq_bot_psu3 hZ h2 hk h
  · exact eq_bot_psp4 hZ h2 hk h
  · rcases (by omega : k = 2 ∨ 3 ≤ k) with rfl | hk3
    · exact (hG24 _ h P E hP hEP hE hcard hEZ).elim
    · exact eq_bot_g2 hZ h2 hk3 h
  · exact eq_bot_d4 hZ h2 hk h
  · obtain ⟨a, rfl⟩ : ∃ a, k = 2 * a + 1 := by
      obtain ⟨-, a, -, -, -, -, ha, -⟩ := h
      exact ⟨a, ha⟩
    rcases (by omega : a = 1 ∨ 2 ≤ a) with rfl | ha
    · exact (hSz8 _ h P E hP hEP hE hcard hEZ).elim
    · exact eq_bot_sz hZ h2 (by omega) h
  · exact eq_bot_f4 hZ h2 hk h

end CFSG.Quasithin.H13.NQCat.LieMult
