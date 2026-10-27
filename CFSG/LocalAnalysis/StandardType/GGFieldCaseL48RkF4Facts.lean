module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBRkDefs
public import CFSG.LocalAnalysis.StandardType.GGSixTCResidualSkeleton
import CFSG.LocalAnalysis.StandardType.Marking
import CFSG.LocalAnalysis.StandardType.GGRecipeFieldExcInn
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBLemmas
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint Subgroup

@[expose] def GGF4TwoCentre : Prop :=
  ∀ (R : Type) [Group R] [Finite R], UntwistedChevalleyModel R .F4 2 →
    ∀ (L' : Type) [Group L'] [Finite L'] (_ : L' ⧸ Subgroup.center L' ≃* R),
      commutator L' = ⊤ → Nat.card (Subgroup.center L') ∣ 2

@[expose] def GGF4TwoRankFour : Prop :=
  ∀ (R : Type) [Group R] [Finite R], UntwistedChevalleyModel R .F4 2 →
    ∃ A : Subgroup R, IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 4

@[expose] def GGF4TwoInvolutionCommutes : Prop :=
  ∀ (R : Type) [Group R] [Finite R], UntwistedChevalleyModel R .F4 2 →
    ∃ y : R, y ^ 3 = 1 ∧ y ≠ 1 ∧ ∃ s : R, s ^ 2 = 1 ∧ s ≠ 1 ∧ y * s = s * y

@[expose] def GGF4TwoOutTwo : Prop :=
  ∀ (R : Type) [Group R] [Finite R], UntwistedChevalleyModel R .F4 2 →
    ∀ T : Subgroup (MulAut R), IsPGroup 2 T →
      (∀ φ ∈ T, φ ∈ (MulAut.conj : R →* MulAut R).range → φ = 1) → Nat.card T ≤ 2

@[expose] def GGF4TwoSCNoTwoLocal : Prop :=
  ∀ (R : Type) [Group R] [Finite R], UntwistedChevalleyModel R .F4 2 →
    ∀ E : Subgroup R, IsElemAbelian 3 E → Nat.card E = 3 ^ 3 →
      (∀ g : R, g ^ 3 = 1 → (∀ e ∈ E, g * e = e * g) → g ∈ E) →
      ∀ S : Subgroup R, IsPGroup 2 S → E ≤ Subgroup.normalizer (S : Set R) → S = ⊥

@[expose] def GGF4TwoFacts : Prop :=
  GGF4TwoCentre ∧ GGF4TwoRankFour ∧ GGF4TwoInvolutionCommutes ∧ GGF4TwoOutTwo ∧
    GGF4TwoSCNoTwoLocal

private theorem lab_tag_f4_of_raw
    {X : Type} [Group X] {lab₀ lab₁ : LargeEvenLabel}
    (hlab₀ : LargeEvenInLambda2 lab₀) (hlab₁ : LargeEvenInLambda2 lab₁)
    (hraw₀ : LargeEvenRawDatum lab₀ (fun R _ _ _ => Nonempty (X ≃* R)))
    (hraw₁ : LargeEvenRawDatum lab₁ (fun R _ _ _ => Nonempty (X ≃* R)))
    (h0 : lab₀ = ⟨.F4, 0, 1⟩) :
    lab₁.tag = .F4 := by
  have hiso := ggLabelRigidInput_holds lab₀ lab₁ X hlab₀ hlab₁ hraw₀ hraw₁
  rw [h0] at hiso
  rcases hiso with h | h | h | h | h | h | h | h
  · rw [← h]
  · exfalso; simpa using h.1
  · exfalso; simpa using h.1
  · exfalso; simpa using h.1
  · exfalso; simpa using h.1
  · exfalso; simpa using h.1
  · exfalso; simpa using h.1
  · exfalso; simpa using h.2

private theorem stage0_pack
    {G : Type} [Group G] [Finite G] {B : Subgroup G} {x : G} {L : Subgroup G}
    (hstd : LargeEvenStandardType 3 B x L)
    (hmark : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .F4 ∧ lab.n = 1)) :
    commutator L = ⊤ ∧ UntwistedChevalleyModel (L ⧸ Subgroup.center L) .F4 2 ∧
    B ≤ Subgroup.normalizer (L : Set G) ∧
    (∀ b ∈ B, ∃ l ∈ L, ∀ g ∈ L, b * g * b⁻¹ = l * g * l⁻¹) := by
  obtain ⟨hperf₀, lab₀, hlab₀, hraw₀⟩ := hmark
  obtain ⟨hperf₁, lab₁, hlab₁, hraw₁⟩ := hstd.1
  obtain ⟨R₀, _, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw₀
  obtain ⟨-, -, θ₀, htag₀, hn₀⟩ := hQ₀
  have h0 : lab₀ = ⟨.F4, 0, 1⟩ := by
    obtain ⟨t, l, n⟩ := lab₀
    have ht : t = .F4 := htag₀
    have hn : n = 1 := hn₀
    have hl : l = 0 := by
      have h := hlab₀
      dsimp only [LargeEvenInLambda2] at h
      rw [ht] at h
      exact h.2
    subst ht; subst hl; subst hn
    rfl
  have hmodel : UntwistedChevalleyModel (L ⧸ Subgroup.center L) .F4 2 := by
    have hraw₀' := hraw₀
    rw [h0] at hraw₀'
    dsimp only [LargeEvenRawDatum] at hraw₀'
    obtain ⟨K, _, _, hKcard, hq⟩ := hraw₀'
    obtain ⟨-, -, θ', -⟩ := hq
    obtain ⟨K', iF, iFi, hK', ⟨e⟩⟩ := untwistedChevalleyModel_largeEven .F4 (by simpa using hKcard)
    exact ⟨K', iF, iFi, hK', ⟨θ'.trans e⟩⟩
  have hraw₀N : LargeEvenRawDatum lab₀
      (fun R _ _ _ => Nonempty ((L ⧸ Subgroup.center L) ≃* R)) :=
    largeEvenRawDatum_mono (fun R _ I F h => by obtain ⟨-, -, θ, -⟩ := h; exact ⟨θ⟩) hraw₀
  have hraw₁N : LargeEvenRawDatum lab₁
      (fun R _ _ _ => Nonempty ((L ⧸ Subgroup.center L) ≃* R)) :=
    largeEvenRawDatum_mono (fun R _ I F h => by obtain ⟨-, -, θ, -⟩ := h; exact ⟨θ⟩) hraw₁
  have hlab₁_tag : lab₁.tag = .F4 := lab_tag_f4_of_raw hlab₀ hlab₁ hraw₀N hraw₁N h0
  obtain ⟨t₁, l₁, n₁⟩ := lab₁
  have ht₁ : t₁ = .F4 := hlab₁_tag
  subst ht₁
  dsimp only [LargeEvenRawDatum] at hraw₁
  obtain ⟨K₁, _, _, hK₁, hq₁⟩ := hraw₁
  obtain ⟨hs₁, hna₁, θ₁, hP₁⟩ := hq₁
  obtain ⟨hsplit₁, hBN, h3⟩ := hP₁
  have hInn : LargeEvenChevIDImage LargeEvenCartanF4 K₁
      (LargeEvenChevH LargeEvenCartanF4 K₁ false) ⊆
      (MulAut.conj : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K₁ false) →*
        MulAut (LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K₁ false))).range :=
    chevIDImage_subset_inn_of_top (τ := .F4)
      (TableB.torusSubgroup_eq_top_of_mul_eq_smul _ K₁ TableB.cartanF4_inv
        (fun s => ⟨s, pow_one s⟩))
  refine ⟨hperf₀, hmodel, hBN, ?_⟩
  intro b hb
  have hmem : ggLAut L θ₁ ⟨b, hBN hb⟩ ∈
      LargeEvenChevIDImage LargeEvenCartanF4 K₁ (LargeEvenChevH LargeEvenCartanF4 K₁ false) :=
    ggLAut_mem_of_induces L θ₁ hBN h3 hb
  obtain ⟨ρ, hρ⟩ := hInn hmem
  obtain ⟨q, hq⟩ := θ₁.surjective ρ
  obtain ⟨l', rfl⟩ := QuotientGroup.mk_surjective q
  have hl'N : (l' : G) ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer l'.2
  have hconj : ggLAut L θ₁ ⟨(l' : G), hl'N⟩ = MulAut.conj ρ := by
    rw [ggLAut_of_mem_conj θ₁ l' hl'N, hq]
  have h1 : ggLAut L θ₁ (⟨b, hBN hb⟩ * ⟨(l' : G), hl'N⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, hconj, ← hρ, mul_inv_cancel]
  have hc : (b * (l' : G)⁻¹) ∈ Subgroup.centralizer (L : Set G) :=
    mem_centralizer_of_ggLAut_eq_one L θ₁ hperf₀ h1
  refine ⟨(l' : G), l'.2, ?_⟩
  intro g hg
  have hmemL : (l' : G) * g * (l' : G)⁻¹ ∈ L :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ l'.2 hg) (Subgroup.inv_mem _ l'.2)
  have hcomm := (Subgroup.mem_centralizer_iff.mp hc) _ hmemL
  calc b * g * b⁻¹
      = ((b * (l' : G)⁻¹) * (l' : G)) * g * ((b * (l' : G)⁻¹) * (l' : G))⁻¹ := by group
    _ = (b * (l' : G)⁻¹) * ((l' : G) * g * (l' : G)⁻¹) * (b * (l' : G)⁻¹)⁻¹ := by group
    _ = ((l' : G) * g * (l' : G)⁻¹) * (b * (l' : G)⁻¹) * (b * (l' : G)⁻¹)⁻¹ := by
          rw [hcomm]
    _ = (l' : G) * g * (l' : G)⁻¹ := by group

private theorem stage1_arith
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L : Subgroup G}
    (hThm : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs) (hcardBs : Nat.card Bs = 3 ^ 4)
    (hZdv : Nat.card (Subgroup.center ↥L) ∣ 2) :
    B = Bs ∧ LargeEvenTwoLocalRank 3 G = 4 ∧
      B ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x ∧ x ∉ L := by
  have hsS : LargeEvenSStar 3 B x L := hThm.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hsS.2.2.1
  have hx3 : x ^ 3 = 1 := hsS.1.1.2 x hsS.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hsS.2.2.2.1.1
  have hcycL := hsS.2.2.2.2
  have hBsp : ∀ b ∈ B, b ^ 3 = 1 := fun b hb => hsS.1.1.2 b hb
  have hcardB : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hsS.1.2.1
  have hrank4 : 4 ≤ LargeEvenTwoLocalRank 3 G := hThm.2.2.2.2.2.1.2.2.2
  have hdvd : Nat.card B ∣ Nat.card Bs := Subgroup.card_dvd_of_le hBs.1
  have hm4 : LargeEvenTwoLocalRank 3 G = 4 := by
    have h1 : 3 ^ LargeEvenTwoLocalRank 3 G ∣ 3 ^ 4 := by
      rw [← hcardB, ← hcardBs]
      exact hdvd
    have h2 : 3 ^ LargeEvenTwoLocalRank 3 G ≤ 3 ^ 4 := Nat.le_of_dvd (by norm_num) h1
    have h3 : LargeEvenTwoLocalRank 3 G ≤ 4 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
    omega
  have hBcard : Nat.card B = 3 ^ 4 := by rw [hcardB, hm4]
  have hBeq : B = Bs := Subgroup.eq_of_le_of_card_ge hBs.1 (by rw [hBcard, hcardBs])
  have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  have hTp : IsPGroup 3 ↥(B ⊓ Subgroup.centralizer (L : Set G)) :=
    fun t => ⟨1, Subtype.ext (by simpa using hBsp _ t.2.1)⟩
  have hCx : B ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    le_antisymm
      (GGL48TW.Cent.le_zpowers_of_isCyclic Nat.prime_three
        (hcycL _ inf_le_right hTp) (fun t ht => hBsp t ht.1) ⟨hsS.2.1, hxC⟩ hx1)
      (Subgroup.zpowers_le.mpr ⟨hsS.2.1, hxC⟩)
  have hxL : x ∉ L := by
    intro hxL
    let xL : ↥L := ⟨x, hxL⟩
    have hxZ : xL ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hLx l.2))
    have h3dvd : 3 ∣ Nat.card (Subgroup.center ↥L) := by
      have hzo : orderOf (⟨xL, hxZ⟩ : Subgroup.center ↥L) = 3 := by
        apply orderOf_eq_prime
        · exact Subtype.ext (Subtype.ext (by simpa using hx3))
        · intro h
          exact hx1 (Subtype.ext_iff.mp (Subtype.ext_iff.mp h))
      have := orderOf_dvd_natCard (⟨xL, hxZ⟩ : Subgroup.center ↥L)
      rwa [hzo] at this
    have h32 : 3 ∣ 2 := h3dvd.trans hZdv
    omega
  exact ⟨hBeq, hm4, hCx, hxL⟩

private theorem stage2_center_bot
    {G : Type} [Group G] [Finite G] {x : G} {L : Subgroup G}
    (hCentre : GGF4TwoCentre) (hRank4 : GGF4TwoRankFour)
    (hperf : commutator ↥L = ⊤)
    (hmodelZ : UntwistedChevalleyModel (↥L ⧸ Subgroup.center ↥L) .F4 2)
    (hx3 : x ^ 3 = 1) (hxL : x ∉ L)
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G))
    (hrank_le : LargeEvenTwoLocalRank 3 G ≤ 4) :
    Subgroup.center ↥L = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZdv : Nat.card (Subgroup.center ↥L) ∣ 2 :=
    hCentre (↥L ⧸ Subgroup.center ↥L) hmodelZ ↥L (MulEquiv.refl _) hperf
  have h3Z : ¬ 3 ∣ Nat.card (Subgroup.center ↥L) := by
    intro h
    have : 3 ∣ 2 := h.trans hZdv
    omega
  obtain ⟨AQ, hAQab, hAQcard⟩ := hRank4 (↥L ⧸ Subgroup.center ↥L) hmodelZ
  have h4Q : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥L ⧸ Subgroup.center ↥L)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hAQab hAQcard
  have hpEq := CFSG.SectionRank.pRank_quotient_eq (G := ↥L) (p := 3)
    (Subgroup.center ↥L) h3Z
  have h4L : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) := by
    rw [← hpEq]; exact h4Q
  obtain ⟨E₀, -, hE₀ab, hE₀card⟩ :=
    CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) (⊤ : Subgroup ↥L)
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := E₀) 3 (n := 4)
    (by rw [hE₀card]; exact pow_dvd_pow 3 h4L)
  obtain ⟨A₀, -, hA₀ab, hA₀card⟩ : ∃ A : Subgroup ↥L,
      A ≤ (⊤ : Subgroup ↥L) ∧ CFSG.Assembly.IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 4 :=
    ⟨K.map E₀.subtype, le_top,
      CFSG.Open.IsElemAbelian.mono hE₀ab (Subgroup.map_subtype_le K),
      by rw [Subgroup.card_map_of_injective E₀.subtype_injective, hK]⟩
  by_contra hZne
  have hZcard2 : Nat.card (Subgroup.center ↥L) = 2 := by
    have h2 : Nat.card (Subgroup.center ↥L) ≤ 2 := Nat.le_of_dvd (by norm_num) hZdv
    have hne1 : Nat.card (Subgroup.center ↥L) ≠ 1 := fun h1 =>
      hZne (Subgroup.card_eq_one.mp h1)
    have hpos : 0 < Nat.card (Subgroup.center ↥L) := Nat.card_pos
    omega
  let U : Subgroup G := (Subgroup.center ↥L).map L.subtype
  have hUmap : Nat.card U = Nat.card (Subgroup.center ↥L) :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hU2 : IsPGroup 2 U := by
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [pow_one, hUmap, hZcard2]⟩
  have hUne : U ≠ ⊥ := by
    intro h
    apply hZne
    rw [eq_bot_iff]
    intro z hz
    have hzU : L.subtype z ∈ U := Subgroup.mem_map.mpr ⟨z, hz, rfl⟩
    rw [h, Subgroup.mem_bot] at hzU
    rw [Subgroup.mem_bot]
    exact L.subtype_injective (by simpa using hzU)
  have hUC : U ≤ Subgroup.centralizer (L : Set G) := by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hu
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz (⟨l, hl⟩ : ↥L))
  obtain ⟨A₀', hA₀'L, hA₀'ab, hA₀'card⟩ :
      ∃ A : Subgroup G, A ≤ L ∧ IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 4 :=
    ⟨A₀.map L.subtype, Subgroup.map_subtype_le A₀,
      CFSG.SectionRank.isElemAbelian_map hA₀ab _, by
        rw [Subgroup.card_map_of_injective L.subtype_injective, hA₀card]⟩
  have hxC : x ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  have hxA : x ∉ A₀' := fun h => hxL (hA₀'L h)
  have hAx : ∀ a ∈ A₀', a * x = x * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLx (hA₀'L ha))
  obtain ⟨hEab, hEcard⟩ :=
    isElemAbelian_sup_zpowers_of_card Nat.prime_three hA₀'ab hA₀'card hx3 hxA hAx
  have hAU : A₀' ≤ Subgroup.centralizer (U : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hu
    have hc := Subgroup.mem_center_iff.mp hz (⟨a, hA₀'L ha⟩ : ↥L)
    exact (congrArg Subtype.val hc).symm
  have hUL : U ≤ L := Subgroup.map_subtype_le _
  have hxU : x ∈ Subgroup.centralizer (U : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx (hUL hu))
  have hxN : x ∈ Subgroup.normalizer (U : Set G) :=
    Subgroup.centralizer_le_normalizer (U : Set G) hxU
  have hEN : A₀' ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (U : Set G) :=
    sup_le (fun a ha => Subgroup.centralizer_le_normalizer (U : Set G) (hAU ha))
      (Subgroup.zpowers_le.mpr hxN)
  have h5 := le_twoLocalRank_of_normalizes Nat.prime_three hUne hU2 hEab hEN
    (k := 5) (by simpa using hEcard)
  omega


private theorem stage3_hB0
    {G : Type} [Group G] [Finite G] {B : Subgroup G} {x : G} {L : Subgroup G}
    (hSC : GGF4TwoSCNoTwoLocal)
    (hmodelL : UntwistedChevalleyModel ↥L .F4 2)
    (hZbot : Subgroup.center ↥L = ⊥)
    (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hinner : ∀ b ∈ B, ∃ l ∈ L, ∀ g ∈ L, b * g * b⁻¹ = l * g * l⁻¹)
    (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hBcard : Nat.card B = 3 ^ 4)
    (hCx : B ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hBsp : ∀ b ∈ B, b ^ 3 = 1)
    (hBab : IsElemAbelian 3 B)
    (hBstar : ∀ g : G, g ∈ Subgroup.centralizer (B : Set G) → g ^ 3 = 1 → g ∈ B) :
    ∀ S : Subgroup G, S ≤ L → IsPGroup 2 S → B ≤ Subgroup.normalizer (S : Set G) → S = ⊥ := by
  classical
  let phi : B →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  let PB : Subgroup (MulAut ↥L) := phi.range
  have hphi_coe : ∀ (b : B) (m : ↥L),
      ((phi b m : ↥L) : G) = (b : G) * m * (b : G)⁻¹ := fun b m =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion hBN b) m
  have hBtop : IsElemAbelian 3 (⊤ : Subgroup B) := by
    have h := hBab.subgroupOf B
    rwa [Subgroup.subgroupOf_self] at h
  have hPBab : IsElemAbelian 3 PB := by
    have h := hBtop.map (phi : B →* MulAut ↥L)
    rwa [Subgroup.map_top] at h
  have hPBle : PB ≤ (MulAut.conj : ↥L →* MulAut ↥L).range := by
    rintro f ⟨b, rfl⟩
    obtain ⟨l, hl, hconj⟩ := hinner b b.2
    refine ⟨⟨l, hl⟩, ?_⟩
    ext m
    rw [MulAut.conj_apply, hphi_coe]
    exact (hconj m m.2).symm
  have hconj_inj : Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) := by
    intro a b hab
    have h1 : MulAut.conj (b⁻¹ * a) = 1 := by
      rw [map_mul, map_inv, hab]
      group
    have hz : b⁻¹ * a ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro m
      have hm := congrArg (fun f : MulAut ↥L => f m) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at hm
      have hcomm : (b⁻¹ * a) * m = m * (b⁻¹ * a) := by
        calc (b⁻¹ * a) * m = ((b⁻¹ * a) * m * (b⁻¹ * a)⁻¹) * (b⁻¹ * a) := by group
          _ = m * (b⁻¹ * a) := by rw [hm]
      exact hcomm.symm
    rw [hZbot, Subgroup.mem_bot] at hz
    calc a = b * (b⁻¹ * a) := by group
      _ = b * 1 := by rw [hz]
      _ = b := mul_one b
  let BL : Subgroup ↥L := PB.comap (MulAut.conj : ↥L →* MulAut ↥L)
  have hBLmap : BL.map (MulAut.conj : ↥L →* MulAut ↥L) = PB := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.mpr hPBle
  have hker : phi.ker = (B ⊓ Subgroup.centralizer (L : Set G)).subgroupOf B := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      refine ⟨b.2, ?_⟩
      change (b : G) ∈ Subgroup.centralizer (L : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have hb := congrArg (fun f : MulAut ↥L => f ⟨m, hm⟩) h
      simp only [MulAut.one_apply] at hb
      have hc := hphi_coe b ⟨m, hm⟩
      rw [hb] at hc
      have hm_eq : (m : G) = (b : G) * (m : G) * (b : G)⁻¹ := by simpa using hc
      calc (m : G) * (b : G) = ((b : G) * (m : G) * (b : G)⁻¹) * (b : G) := by
            conv_lhs => rw [hm_eq]
        _ = (b : G) * (m : G) := by group
    · intro h
      ext m
      have hm : (m : G) * (b : G) = (b : G) * m :=
        Subgroup.mem_centralizer_iff.mp h.2 m m.2
      rw [hphi_coe, MulAut.one_apply]
      change (b : G) * (m : G) * (b : G)⁻¹ = (m : G)
      rw [← hm]
      group
  have hker3 : Nat.card phi.ker = 3 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv, hCx,
      Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  have hBLcard : Nat.card BL = 3 ^ 3 := by
    have h1 : Nat.card (BL.map (MulAut.conj : ↥L →* MulAut ↥L)) = Nat.card BL :=
      Subgroup.card_map_of_injective hconj_inj
    rw [hBLmap] at h1
    have hrange : Nat.card PB * Nat.card phi.ker = Nat.card B :=
      TableB.card_range_mul_card_ker phi
    have hPBcard : Nat.card PB = 27 := by
      have h := hrange
      rw [hBcard, hker3] at h
      norm_num at h ⊢
      omega
    rw [← h1, hPBcard]
    norm_num
  have hBLab : IsElemAbelian 3 BL := by
    constructor
    · refine ⟨⟨fun a b => ?_⟩⟩
      apply Subtype.ext
      apply hconj_inj
      change MulAut.conj ((a : ↥L) * (b : ↥L)) = MulAut.conj ((b : ↥L) * (a : ↥L))
      rw [map_mul, map_mul]
      exact congrArg Subtype.val
        (hPBab.1.is_comm.comm ⟨MulAut.conj (a : ↥L), a.2⟩ ⟨MulAut.conj (b : ↥L), b.2⟩)
    · intro a ha
      have h3 : (MulAut.conj (a : ↥L)) ^ 3 = 1 :=
        hPBab.2 _ (Subgroup.mem_comap.mp ha)
      have h3' : ((a : ↥L) ^ 3) = 1 := by
        apply hconj_inj
        rw [map_pow, map_one]
        exact h3
      apply Subtype.ext
      exact congrArg (fun z : ↥L => (z : G)) h3'
  have hphi_eq_conj : ∀ (b : B) (l : ↥L),
      (∀ m ∈ L, (b : G) * m * (b : G)⁻¹ = l * m * l⁻¹) → phi b = MulAut.conj l := by
    intro b l hconj
    ext m
    rw [MulAut.conj_apply, hphi_coe]
    change (b : G) * (m : G) * (b : G)⁻¹ = (l : G) * (m : G) * (l : G)⁻¹
    exact hconj m m.2
  have hBLSC : ∀ g : ↥L, g ^ 3 = 1 → (∀ e ∈ BL, g * e = e * g) → g ∈ BL := by
    intro g hg3 hgc
    have hg_comm_B : (g : G) ∈ Subgroup.centralizer (B : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨l, hl, hconj⟩ := hinner b hb
      have hphi_eq : phi ⟨b, hb⟩ = MulAut.conj ⟨l, hl⟩ :=
        hphi_eq_conj ⟨b, hb⟩ ⟨l, hl⟩ hconj
      have hlBL : (⟨l, hl⟩ : ↥L) ∈ BL := by
        rw [show BL = PB.comap (MulAut.conj : ↥L →* MulAut ↥L) from rfl,
          Subgroup.mem_comap, ← hphi_eq]
        exact ⟨⟨b, hb⟩, rfl⟩
      have hgl : (g : G) * l = l * (g : G) := by
        have := congrArg (fun z : ↥L => (z : G)) (hgc ⟨l, hl⟩ hlBL)
        simpa using this
      have hcG_cent : (l : G)⁻¹ * (b : G) ∈ Subgroup.centralizer (L : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro m hm
        have hbm := hconj m hm
        have hcm : ((l : G)⁻¹ * (b : G)) * (m : G) * ((l : G)⁻¹ * (b : G))⁻¹ = (m : G) := by
          calc ((l : G)⁻¹ * (b : G)) * (m : G) * ((l : G)⁻¹ * (b : G))⁻¹
              = (l : G)⁻¹ * ((b : G) * (m : G) * (b : G)⁻¹) * (l : G) := by group
            _ = (l : G)⁻¹ * (l * (m : G) * l⁻¹) * (l : G) := by rw [hbm]
            _ = (m : G) := by group
        have hcomm : ((l : G)⁻¹ * (b : G)) * (m : G) = (m : G) * ((l : G)⁻¹ * (b : G)) := by
          have h2 := congrArg (fun x : G => x * ((l : G)⁻¹ * (b : G))) hcm
          simpa [mul_assoc] using h2
        exact hcomm.symm
      have hgc_c : (g : G) * ((l : G)⁻¹ * (b : G)) = ((l : G)⁻¹ * (b : G)) * (g : G) :=
        Subgroup.mem_centralizer_iff.mp hcG_cent g g.2
      calc (b : G) * g = (l * ((l : G)⁻¹ * (b : G))) * g := by
              rw [show (l : G) * ((l : G)⁻¹ * (b : G)) = (b : G) from by group]
        _ = l * (((l : G)⁻¹ * (b : G)) * g) := by group
        _ = l * (g * ((l : G)⁻¹ * (b : G))) := by rw [hgc_c]
        _ = (l * g) * ((l : G)⁻¹ * (b : G)) := by group
        _ = (g * l) * ((l : G)⁻¹ * (b : G)) := by rw [hgl]
        _ = g * (l * ((l : G)⁻¹ * (b : G))) := by group
        _ = g * (b : G) := by
              rw [show (l : G) * ((l : G)⁻¹ * (b : G)) = (b : G) from by group]
    have hgG3 : (g : G) ^ 3 = 1 := congrArg (fun z : ↥L => (z : G)) hg3
    have hgB : (g : G) ∈ B := hBstar g hg_comm_B hgG3
    have hconj_mem : MulAut.conj g ∈ PB := by
      have h_eq : phi ⟨(g : G), hgB⟩ = MulAut.conj g := by
        ext m
        rw [MulAut.conj_apply, hphi_coe]
        rfl
      rw [← h_eq]
      exact ⟨⟨(g : G), hgB⟩, rfl⟩
    rw [show BL = PB.comap (MulAut.conj : ↥L →* MulAut ↥L) from rfl, Subgroup.mem_comap]
    exact hconj_mem
  intro S hSL hS2 hBS
  let S' : Subgroup ↥L := S.subgroupOf L
  have hS'2 : IsPGroup 2 S' := by
    intro s
    obtain ⟨n, hn⟩ := hS2 ⟨(s.1 : G), Subgroup.mem_subgroupOf.mp s.2⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : S => (z : G)) hn
  have hBLN : BL ≤ Subgroup.normalizer (S' : Set ↥L) := by
    intro l hl
    rw [show BL = PB.comap (MulAut.conj : ↥L →* MulAut ↥L) from rfl, Subgroup.mem_comap] at hl
    obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp hl
    rw [Subgroup.mem_normalizer_iff]
    intro m
    have heq : ((l * m * l⁻¹ : ↥L) : G) = (b : G) * (m : G) * (b : G)⁻¹ := by
      have h := congrArg (fun f : MulAut ↥L => ((f m : ↥L) : G)) hb
      rw [hphi_coe] at h
      rw [MulAut.conj_apply] at h
      exact h.symm
    constructor
    · intro hm
      rw [Subgroup.mem_subgroupOf] at hm ⊢
      have hbm : (b : G) * (m : G) * (b : G)⁻¹ ∈ S :=
        (Subgroup.mem_normalizer_iff.mp (hBS b.2) (m : G)).mp hm
      rwa [heq]
    · intro hm
      rw [Subgroup.mem_subgroupOf] at hm ⊢
      have hbm : (b : G) * (m : G) * (b : G)⁻¹ ∈ S := by rwa [heq] at hm
      exact (Subgroup.mem_normalizer_iff.mp (hBS b.2) (m : G)).mpr hbm
  have hS'bot : S' = ⊥ :=
    hSC ↥L hmodelL BL hBLab hBLcard hBLSC S' hS'2 hBLN
  rw [eq_bot_iff]
  intro s hs
  have hs' : (⟨s, hSL hs⟩ : ↥L) ∈ S' := by
    rw [Subgroup.mem_subgroupOf]; exact hs
  rw [hS'bot, Subgroup.mem_bot] at hs'
  exact Subtype.ext_iff.mp hs'


theorem ggL48F4TwoThreeConfigInput_of_facts
    (h : GGF4TwoFacts) : GGL48F4TwoThreeConfigInput := by
  obtain ⟨hCentre, hRank4, hInv, hOut, hSC⟩ := h
  intro G _ _ B Bs x L hThm hBs hcardBs hmark
  classical
  have hstd : LargeEvenStandardType 3 B x L := hThm.2.2.2.2.2.2.2
  have hsS : LargeEvenSStar 3 B x L := hThm.2.2.2.2.2.2.1
  obtain ⟨hperf, hmodelZ, hBN, hinner⟩ := stage0_pack hstd hmark
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hsS.2.2.2.1.1
  have hx3 : x ^ 3 = 1 := hsS.1.1.2 x hsS.2.1
  have hBsp : ∀ b ∈ B, b ^ 3 = 1 := hsS.1.1.2
  have hBab : IsElemAbelian 3 B := hsS.1.1
  have hZdv : Nat.card (Subgroup.center ↥L) ∣ 2 :=
    hCentre (↥L ⧸ Subgroup.center ↥L) hmodelZ ↥L (MulEquiv.refl _) hperf
  obtain ⟨hBeq, hm4, hCx, hxL⟩ := stage1_arith hThm hBs hcardBs hZdv
  have hZbot : Subgroup.center ↥L = ⊥ :=
    stage2_center_bot hCentre hRank4 hperf hmodelZ hx3 hxL hLx (by omega)
  have hmodelL : UntwistedChevalleyModel ↥L .F4 2 := by
    obtain ⟨K, iF, iFi, hK, ⟨e⟩⟩ := hmodelZ
    exact ⟨K, iF, iFi, hK, ⟨(QuotientGroup.quotientBot (G := ↥L)).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hZbot).symm.trans e)⟩⟩
  have hBcard : Nat.card B = 3 ^ 4 := by rw [hsS.1.2.1, hm4]
  have hBstar : ∀ g : G, g ∈ Subgroup.centralizer (B : Set G) → g ^ 3 = 1 → g ∈ B := by
    intro g hg hg3
    have hg' : g ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hg ⊢
      intro b hb
      exact hg b (hBeq ▸ hb)
    have h := hBs.2.2.2 g hg' hg3
    rwa [hBeq]
  have hB0 := stage3_hB0 hSC hmodelL hZbot hBN hinner hsS.2.2.1 hx3 hBcard hCx hBsp hBab hBstar
  have hF1 : ∃ E ≤ L, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
    obtain ⟨A, hAab, hAcard⟩ := hRank4 ↥L hmodelL
    exact ⟨A.map L.subtype, Subgroup.map_subtype_le A,
      CFSG.SectionRank.isElemAbelian_map hAab _, by
        rw [Subgroup.card_map_of_injective L.subtype_injective, hAcard]⟩
  have hF1' : ∃ E ≤ L ⊔ Subgroup.zpowers x, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5 := by
    obtain ⟨E, hEL, hEab, hEcard⟩ := hF1
    have hxE : x ∉ E := fun h => hxL (hEL h)
    have hEx : ∀ e ∈ E, e * x = x * e := fun e he =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLx (hEL he))
    obtain ⟨hab, hcard⟩ :=
      isElemAbelian_sup_zpowers_of_card Nat.prime_three hEab hEcard hx3 hxE hEx
    exact ⟨E ⊔ Subgroup.zpowers x, sup_le (hEL.trans le_sup_left) le_sup_right, hab,
      by simpa using hcard⟩
  have hF2 : ∃ y ∈ L, y ^ 3 = 1 ∧ y ∉ Subgroup.centralizer (L : Set G) ∧
      ∃ s ∈ L, s ≠ 1 ∧ s ^ 2 = 1 ∧ y * s = s * y := by
    obtain ⟨y, hy3, hy1, s, hs2, hs1, hys⟩ := hInv ↥L hmodelL
    refine ⟨(y : G), y.2, congrArg (fun z : ↥L => (z : G)) hy3, ?_,
      (s : G), s.2, ?_, congrArg (fun z : ↥L => (z : G)) hs2,
      congrArg (fun z : ↥L => (z : G)) hys⟩
    · intro hyC
      have hyZ : y ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro m
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hyC m m.2)
      rw [hZbot, Subgroup.mem_bot] at hyZ
      exact hy1 hyZ
    · intro h
      exact hs1 (Subtype.ext (by simpa using h))
  have hOutFinal : ∀ T' : Subgroup G, IsPGroup 2 T' → T' ≤ Subgroup.normalizer (L : Set G) →
      (∀ t ∈ T', ∀ l ∈ L, (∀ g ∈ L, t * g * t⁻¹ = l * g * l⁻¹) →
        t ∈ Subgroup.centralizer (L : Set G)) →
      Nat.card T' ≤ 2 * Nat.card (T' ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) := by
    intro T' hT'2 hT'N hT'C
    let ψ : T' →* MulAut ↥L := L.normalizerMonoidHom.comp (Subgroup.inclusion hT'N)
    have hψ_coe : ∀ (t : T') (m : ↥L),
        ((ψ t m : ↥L) : G) = (t : G) * m * (t : G)⁻¹ := fun t m =>
      Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion hT'N t) m
    have hX2 : IsPGroup 2 ψ.range := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hT'2
      refine IsPGroup.of_card_dvd_pow (n := n) ?_
      have hd : Nat.card ψ.range ∣ Nat.card T' :=
        ⟨Nat.card ψ.ker, (TableB.card_range_mul_card_ker ψ).symm⟩
      rwa [hn] at hd
    have hXinn : ∀ φ ∈ ψ.range,
        φ ∈ (MulAut.conj : ↥L →* MulAut ↥L).range → φ = 1 := by
      rintro φ ⟨t, rfl⟩ ⟨l, hl_eq⟩
      have htC : (t : G) ∈ Subgroup.centralizer (L : Set G) := by
        apply hT'C t t.2 (l : G) l.2
        intro g hg
        have h1 := congrArg (fun f : MulAut ↥L => ((f ⟨g, hg⟩ : ↥L) : G)) hl_eq
        rw [MulAut.conj_apply] at h1
        rw [hψ_coe t ⟨g, hg⟩] at h1
        exact h1.symm
      ext g
      rw [hψ_coe t g, MulAut.one_apply]
      change (t : G) * (g : G) * (t : G)⁻¹ = (g : G)
      have hg_comm : (g : G) * (t : G) = (t : G) * (g : G) :=
        Subgroup.mem_centralizer_iff.mp htC g g.2
      rw [← hg_comm]
      group
    have hXle : Nat.card ψ.range ≤ 2 := hOut ↥L hmodelL ψ.range hX2 hXinn
    have hcard := TableB.card_range_mul_card_ker ψ
    have hψker : ψ.ker = (T' ⊓ Subgroup.centralizer (L : Set G)).subgroupOf T' := by
      ext t
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      constructor
      · intro h
        refine ⟨t.2, ?_⟩
        change (t : G) ∈ Subgroup.centralizer (L : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro m hm
        have hb := congrArg (fun f : MulAut ↥L => f ⟨m, hm⟩) h
        simp only [MulAut.one_apply] at hb
        have hc := hψ_coe t ⟨m, hm⟩
        rw [hb] at hc
        have hm_eq : (m : G) = (t : G) * (m : G) * (t : G)⁻¹ := by simpa using hc
        calc (m : G) * (t : G) = ((t : G) * (m : G) * (t : G)⁻¹) * (t : G) := by
              conv_lhs => rw [hm_eq]
          _ = (t : G) * (m : G) := by group
      · intro h
        ext m
        have hm : (m : G) * (t : G) = (t : G) * (m : G) :=
          Subgroup.mem_centralizer_iff.mp h.2 m m.2
        rw [hψ_coe, MulAut.one_apply]
        change (t : G) * (m : G) * (t : G)⁻¹ = (m : G)
        rw [← hm]
        group
    have hker : Nat.card ψ.ker = Nat.card (T' ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) := by
      rw [hψker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv]
    rw [hker] at hcard
    calc Nat.card T' = Nat.card ψ.range *
            Nat.card (T' ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) := hcard.symm
      _ ≤ 2 * Nat.card (T' ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) :=
          Nat.mul_le_mul_right _ hXle
  obtain ⟨T, hTx, hT2, hBT, hne⟩ := hstd.2.1
  exact hne (TCResidual.ggResidual_commutator_eq_bot (x := x) (L := L) (B := B) (T := T)
    (by omega) hsS.2.2.2.1 hBN hB0 hT2 hTx hBT hF1 hF1' hF2 hOutFinal)



end CFSG.StandardType

end
