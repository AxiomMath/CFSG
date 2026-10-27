module

public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFSeventeenTable

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Types

variable {G : Type} [Group G]

@[expose] def GGStepTwoExcThreeType (L₁ : Subgroup G) : Prop :=
  LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .PSU 4 2 1 ∨
    Nonempty ((↥L₁ ⧸ Subgroup.center ↥L₁) ≃* alternatingGroup (Fin 6)) ∨
    LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .POmegaPlus 4 2 1

@[expose] def GGStepTwoExcFiveType (L₁ : Subgroup G) : Prop :=
  Nonempty ((↥L₁ ⧸ Subgroup.center ↥L₁) ≃* alternatingGroup (Fin 5)) ∨
    LieModel (↥L₁ ⧸ Subgroup.center ↥L₁) .POmegaPlus 4 2 1

theorem ggFusionException_of_component {p : ℕ} {L₁ : Subgroup G} {W' : Type} [Group W']
    [Finite W'] {H E C : Subgroup W'} (hC : IsComponentOf C (H ⊓ CFSG.generalizedFitting W'))
    (he : Nonempty (↥L₁ ⧸ Subgroup.center ↥L₁ ≃* ↥C ⧸ Subgroup.center ↥C))
    (hex : GGFusionException p H E) :
    (p = 3 ∧ GGStepTwoExcThreeType L₁ ∧
        IsPGroup p ↥(CFSG.generalizedFitting W' ⊓ Subgroup.centralizer (E : Set W'))) ∨
      (p = 5 ∧ GGStepTwoExcFiveType L₁) := by
  obtain ⟨e⟩ := he
  rcases hex with ⟨-, -, hnc⟩ | ⟨hp5, -, hall⟩ |
      ⟨hpg, ⟨hp3, -, hall⟩ | ⟨hp3, -, hall⟩ | ⟨hp3, -, hall⟩ | ⟨-, -, hnc⟩ | ⟨-, -, hnc⟩⟩ |
      ⟨hp5, -, hall⟩
  · exact absurd hC (hnc C)
  · obtain ⟨e5⟩ := hall C hC
    exact Or.inr ⟨hp5, Or.inl ⟨e.trans e5⟩⟩
  · exact Or.inl ⟨hp3, Or.inr (Or.inr (lieModel_of_mulEquiv' e.symm (hall C hC))), hpg⟩
  · exact Or.inl ⟨hp3, Or.inl (lieModel_of_mulEquiv' e.symm (hall C hC)), hpg⟩
  · obtain ⟨e6⟩ := hall C hC
    exact Or.inl ⟨hp3, Or.inr (Or.inl ⟨e.trans e6⟩), hpg⟩
  · exact absurd hC (hnc C)
  · exact absurd hC (hnc C)
  · exact Or.inr ⟨hp5, Or.inr (lieModel_of_mulEquiv' e.symm (hall C hC))⟩

end Types

section Choice

variable {G : Type} [Group G]

theorem ggAutK_not_isPGroup [Finite G] {E₀ K M C L₁ : Subgroup G} (hL₁ : IsComponentOf L₁ C)
    (hL₁K : L₁ ≤ K) (hL₁M : L₁ ≤ M) (hH₀C : E₀ ⊔ (K ⊓ M) ≤ C)
    (hKq : CFSG.Assembly.IsQuasisimple ↥K) (hEK : E₀ ≤ Subgroup.normalizer (K : Set G))
    {W' : Type} [Group W'] [Finite W'] (π : ↥(E₀ ⊔ K) →* W') (hπ : Function.Surjective π)
    (hker : π.ker ≤ ((E₀ ⊔ (K ⊓ M)) ⊓ Subgroup.centralizer (K : Set G)).subgroupOf (E₀ ⊔ K))
    {p : ℕ} {g : G} (hgL : g ∈ L₁) (hgZ : ∃ l ∈ L₁, g * l ≠ l * g)
    (hgE : g ∈ Subgroup.centralizer (E₀ : Set G)) (hgp : Nat.Coprime (orderOf g) p) :
    ¬ IsPGroup p ↥(CFSG.generalizedFitting W' ⊓
      Subgroup.centralizer (((E₀.subgroupOf (E₀ ⊔ K)).map π : Subgroup W') : Set W')) := by
  intro hpg
  obtain ⟨hC, -⟩ := ggAutK_image_component hL₁ hL₁K hL₁M hH₀C hKq hEK π hπ hker
  have hgW : g ∈ E₀ ⊔ K := le_sup_right (a := E₀) (hL₁K hgL)
  set w : ↥(E₀ ⊔ K) := ⟨g, hgW⟩
  have hwF : π w ∈ CFSG.generalizedFitting W' :=
    (hC.1.trans inf_le_right) ⟨w, Subgroup.mem_subgroupOf.mpr hgL, rfl⟩
  have hwC : π w ∈ Subgroup.centralizer
      (((E₀.subgroupOf (E₀ ⊔ K)).map π : Subgroup W') : Set W') := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, hu, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hgE _ (Subgroup.mem_subgroupOf.mp hu)
  have hw1 : π w ≠ 1 := by
    intro h1
    have hwk : w ∈ π.ker := h1
    have hgK := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp (hker hwk))).2
    obtain ⟨l, hl, hgl⟩ := hgZ
    exact hgl (Subgroup.mem_centralizer_iff.mp hgK l (hL₁K hl)).symm
  obtain ⟨k, hk⟩ := hpg ⟨π w, hwF, hwC⟩
  have hk' : (π w) ^ p ^ k = 1 := congrArg Subtype.val hk
  have h1 : orderOf (π w) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk'
  have h2 : orderOf (π w) ∣ orderOf g := by
    have h := orderOf_map_dvd π w
    rwa [← Subgroup.orderOf_coe w] at h
  have hcop : Nat.Coprime (orderOf g) (p ^ k) := Nat.Coprime.pow_right k hgp
  have h3 : orderOf (π w) ∣ 1 := by
    have := Nat.dvd_gcd h2 h1
    rwa [hcop] at this
  exact hw1 (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3))

end Choice

section Inputs

@[expose] def GGSixAutKHypRestAtInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
      ∀ b ∈ Bs, b ≠ 1 → ∀ L₁ : Subgroup G,
      IsComponentOf L₁ (ggG0 p B x L D J ⊓ Subgroup.centralizer {b}) →
      ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer {b}) → L₁ ≤ K →
        ¬ K ≤ ggM p B x L D J →
        ∀ m ∈ ggM p B x L D J,
          D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b} →
          ∃ (W' : Type) (_ : Group W') (_ : Finite W') (π : ↥(ggAutKW D K m) →* W'),
            Function.Surjective π ∧
            π.ker ≤ (ggAutKH D K (ggM p B x L D J) m ⊓
              Subgroup.centralizer (K : Set G)).subgroupOf (ggAutKW D K m) ∧
            GGHypThreeSixteenRest p
              (((ggAutKH D K (ggM p B x L D J) m).subgroupOf (ggAutKW D K m)).map π)
              (((D.map (MulAut.conj m⁻¹).toMonoidHom).subgroupOf (ggAutKW D K m)).map π)

theorem ggStepTwo_map_conj_one_le {G : Type} [Group G] {p : ℕ} {Bs D : Subgroup G}
    (hBs : IsElemAbelian p Bs) (hDBs : D ≤ Bs) {b : G} (hb : b ∈ Bs) :
    D.map (MulAut.conj (1 : G)⁻¹).toMonoidHom ≤ Subgroup.centralizer {b} := by
  have := hBs.1
  rintro _ ⟨d, hd, rfl⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  simp only [inv_one, map_one, MulEquiv.coe_toMonoidHom, MulAut.one_apply]
  exact congrArg Subtype.val (mul_comm' (⟨d, hDBs hd⟩ : Bs) ⟨b, hb⟩)

theorem ggSixAutKHypRestInput_of_at (h : GGSixAutKHypRestAtInput) : GGSixAutKHypRestInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 b hb hb1 L₁ hL₁ K hK hLK hKM
  obtain ⟨⟨hBBs, hBsEl, -⟩, ⟨⟨hDB, -⟩, -⟩, -⟩ := hctx.2
  have hD := ggStepTwo_map_conj_one_le hBsEl (hDB.trans hBBs) hb
  exact ⟨1, (ggM p B x L D J).one_mem, hD,
    h G p B Bs x L D J t n f ψ hctx s1 b hb hb1 L₁ hL₁ K hK hLK hKM 1
      (ggM p B x L D J).one_mem hD⟩

@[expose] def GGStepTwoAutKFiveInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
      ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer {b}) → L₁ ≤ K →
        ¬ K ≤ ggM p B x L D J → p = 5 → ¬ GGStepTwoExcFiveType L₁

@[expose] def GGStepTwoAutKThreeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
      ∀ K : Subgroup G, IsComponentOf K (Subgroup.centralizer {b}) → L₁ ≤ K →
        ¬ K ≤ ggM p B x L D J → p = 3 → GGStepTwoExcThreeType L₁ →
          ∃ m ∈ ggM p B x L D J,
            D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b} ∧
            ∃ g ∈ L₁, (∃ l ∈ L₁, g * l ≠ l * g) ∧
              g ∈ Subgroup.centralizer (D.map (MulAut.conj m⁻¹).toMonoidHom : Set G) ∧
              Nat.Coprime (orderOf g) p

theorem ggStepTwoAutKRestInput_of_finer (hR : GGSixAutKHypRestAtInput)
    (h5 : GGStepTwoAutKFiveInput) (h3 : GGStepTwoAutKThreeInput) : GGStepTwoAutKRestInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair K hK hLK hKM
  have hchoice : ∃ m ∈ ggM p B x L D J,
      D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.centralizer {b} ∧
      (p = 3 → GGStepTwoExcThreeType L₁ → ∃ g ∈ L₁, (∃ l ∈ L₁, g * l ≠ l * g) ∧
        g ∈ Subgroup.centralizer (D.map (MulAut.conj m⁻¹).toMonoidHom : Set G) ∧
        Nat.Coprime (orderOf g) p) := by
    by_cases hT : p = 3 ∧ GGStepTwoExcThreeType L₁
    · obtain ⟨m, hm, hmC, hg⟩ :=
        h3 G p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair K hK hLK hKM hT.1 hT.2
      exact ⟨m, hm, hmC, fun _ _ => hg⟩
    · obtain ⟨⟨hBBs, hBsEl, -⟩, ⟨⟨hDB, -⟩, -⟩, -⟩ := hctx.2
      exact ⟨1, (ggM p B x L D J).one_mem,
        ggStepTwo_map_conj_one_le hBsEl (hDB.trans hBBs) hpair.1,
        fun hp3 hT' => absurd ⟨hp3, hT'⟩ hT⟩
  obtain ⟨m, hm, hEC, hgchoice⟩ := hchoice
  obtain ⟨W', _, _, π, hπ, hker, hrest⟩ :=
    hR G p B Bs x L D J t n f ψ hctx s1 b hpair.1 hpair.2.1 L₁ hpair.2.2.1 K hK hLK hKM m hm hEC
  refine ⟨m, hm, hEC, W', inferInstance, inferInstance, π, hπ, hker, hrest, fun hex => ?_⟩
  have : IsSimpleGroup G := hctx.1.1
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hctx.1.2.2.2.2.2.1.2.1
  obtain ⟨-, ⟨⟨-, hDel, hDcard, -⟩, -⟩, -⟩ := hctx.2
  have hfusE : GGControlsStrongFusion (ggM p B x L D J) (D.map (MulAut.conj m⁻¹).toMonoidHom) := by
    refine s1.2.1.of_map_conj_le ((ggM p B x L D J).inv_mem hm) ?_
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hd
  have hE0el : IsElemAbelian p (D.map (MulAut.conj m⁻¹).toMonoidHom) :=
    isElemAbelian_map_hom hDel _
  have hE0card : Nat.card (D.map (MulAut.conj m⁻¹).toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj m⁻¹).injective, hDcard]
  have hnorm : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ Subgroup.normalizer (K : Set G) :=
    ggLemmaThreeThirteenInput_holds G p hp hp2 (Subgroup.centralizer {b})
      (ggM p B x L D J ⊓ Subgroup.centralizer {b}) _
      (ggStepTwo_kGroup_of_ne_top hctx.1.2.2.1
        (ggStepTwo_centralizer_ne_top hctx.1.2.1 hpair.2.1))
      hE0el hE0card (hfusE.inf_in hEC) K hK (fun h => hKM (h.trans inf_le_left))
  have hEM : D.map (MulAut.conj m⁻¹).toMonoidHom ≤ ggM p B x L D J := hfusE.1
  have hH₀C : D.map (MulAut.conj m⁻¹).toMonoidHom ⊔ (K ⊓ ggM p B x L D J) ≤
      ggM p B x L D J ⊓ Subgroup.centralizer {b} :=
    sup_le (le_inf hEM hEC) (le_inf inf_le_right (inf_le_left.trans hK.1))
  obtain ⟨hC, he⟩ := ggAutK_image_component hpair.isComponentOf_inf hLK hpair.le_ggM hH₀C
    hK.2.2 hnorm π hπ hker
  rcases ggFusionException_of_component hC he hex with ⟨hp3, hT, hpg⟩ | ⟨hp5, hT⟩
  · obtain ⟨g, hgL, hgZ, hgE, hgp⟩ := hgchoice hp3 hT
    exact ggAutK_not_isPGroup hpair.isComponentOf_inf hLK hpair.le_ggM hH₀C hK.2.2 hnorm π hπ
      hker hgL hgZ hgE hgp hpg
  · exact h5 G p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair K hK hLK hKM hp5 hT

end Inputs

end CFSG.StandardType
