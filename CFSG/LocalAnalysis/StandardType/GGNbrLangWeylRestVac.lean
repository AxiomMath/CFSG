module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangRest
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestTwE6
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestSz
public import CFSG.LocalAnalysis.StandardType.GGRawAutRest
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestVac
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNine
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionDenominatorCyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley InndiagE6 RecipeFieldE6 RawAutTwE6

namespace NbrLangWeylRest

theorem largeEvenLabelAll_pow_mem_of_conj {p N : ℕ} {lab : LargeEvenLabel} (hodd : GGOddAutAt p lab)
    (hconj : LargeEvenLabelAll lab (GGRawFieldConj p))
    (hpow : LargeEvenLabelAll lab fun _ _ _ F => ∀ f ∈ F, f ^ N = 1) (hpN : ¬ p ∣ N) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I := by
  refine (largeEvenLabelAll_and (largeEvenLabelAll_and hodd hconj)
    hpow).mono ?_
  rintro R _ I F ⟨⟨hR, hcj⟩, hfp⟩ hs hna φ hφ
  obtain ⟨u, hu, f, hf, rfl⟩ := hR hs hna φ hφ
  by_contra hI
  obtain ⟨f', hf', u', -, hord, -⟩ := hcj hs hna u hu f hf hI hφ
  exact hpN (hord ▸ orderOf_dvd_of_pow_eq_one (hfp f' hf'))

theorem largeEvenLabelAll_pow_mem_of_field_one {p : ℕ} {lab : LargeEvenLabel}
    (hodd : GGOddAutAt p lab) (hF : LargeEvenLabelAll lab fun _ _ _ F => ∀ f ∈ F, f = 1) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I := by
  refine (largeEvenLabelAll_and hodd hF).mono ?_
  rintro R _ I F ⟨hR, hF1⟩ hs hna φ hφ
  obtain ⟨u, hu, f, hf, rfl⟩ := hR hs hna φ hφ
  rw [eq_one_of_mem_closure_of_forall hF1 hf, mul_one]
  exact hu

section E6


theorem pow_mem_E6 {f : ℕ} (K : Type) [Field K] [Finite K] (hK : Nat.card K = 2 ^ f) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpf : ¬ p ∣ f)
    (φ : MulAut (LargeEvenCenterQuot (LargeEvenChevH TwistTag.E6.tag.cartan K false)))
    (hφ : φ ^ p = 1) :
    φ ∈ LargeEvenChevIDImage TwistTag.E6.tag.cartan K
      (LargeEvenChevH TwistTag.E6.tag.cartan K false) := by
  have hQ := (e6QuotOn_isRoot K).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm
  unfold E6QuotOn at hQ
  rw [← diagHom_eq_markDiagUnit] at hQ
  suffices key : ∀ H : Subgroup (LargeEvenChevGL TwistTag.E6.tag.cartan K),
      H = MarkChev.chevH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K false →
      ∀ φ : MulAut (LargeEvenCenterQuot H), φ ^ p = 1 →
        φ ∈ LargeEvenChevIDImage TwistTag.E6.tag.cartan K H from
    key _ (largeEvenChevH_eq _ K false) φ hφ
  intro H hH
  subst hH
  obtain ⟨Ψ, hker, -⟩ := hQ
  intro φ hφ
  rw [mem_chevID_iff_isInnDiagOn, ← hker]
  have h1 : Ψ φ ^ p = 1 := by rw [← map_pow, hφ, map_one]
  refine Prod.ext ?_ ?_
  · have h2 : (Ψ φ).1 ^ p = 1 := congrArg Prod.fst h1
    exact NbrLangRest.eq_one_of_pow_ringAut hp hK hpf h2
  · have h2 : (Ψ φ).2 ^ p = 1 := congrArg Prod.snd h1
    have hx2 : (Ψ φ).2 ^ 2 = 1 := by
      have hall : ∀ y : Multiplicative (ZMod 2), y ^ 2 = 1 := by decide
      exact hall _
    have hcop : Nat.Coprime p 2 := Nat.coprime_two_right.mpr (hp.odd_of_ne_two hp2)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hx2))

theorem pow_mem_twE6 {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n)
    (φ : MulAut (LargeEvenCenterQuot
      (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n)))
    (hφ : φ ^ p = 1) :
    φ ∈ LargeEvenChevIDImage TwistTag.E6.tag.cartan K
      (LargeEvenTwistedH TwistTag.E6.tag.cartan K TwistTag.E6.perm n) := by
  have hQ := twE6Quot_recipe hn K hK
  suffices key : ∀ H : Subgroup (LargeEvenChevGL TwistTag.E6.tag.cartan K),
      H = MarkChev.twistedH TwistTag.E6.tag.cartan (LargeEvenIsRoot TwistTag.E6.tag.cartan) K
        TwistTag.E6.perm n →
      ∀ φ : MulAut (LargeEvenCenterQuot H), φ ^ p = 1 →
        φ ∈ LargeEvenChevIDImage TwistTag.E6.tag.cartan K H from
    key _ (largeEvenTwistedH_eq _ K _ n) φ hφ
  intro H hH
  subst hH
  obtain ⟨Θ, -, hker, -, -⟩ := hQ
  intro φ hφ
  rw [mem_chevID_iff_isInnDiagOn, ← hker]
  have h1 : Θ φ ^ p = 1 := by rw [← map_pow, hφ, map_one]
  have h2n : ¬ p ∣ 2 * n := fun h => ((Nat.Prime.dvd_mul hp).mp h).elim
    (fun h' => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h')) hpn
  exact NbrLangRest.eq_one_of_pow_ringAut (f := 2 * n) hp (by rw [hK, ← pow_mul, mul_comm]) h2n h1

theorem largeEvenLabelAll_pow_mem_e6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .E6 ∨ lab.tag = .twE6) (hpn : ¬ p ∣ lab.n) :
    LargeEvenLabelAll lab fun R _ I _ => ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  dsimp only at ht hpn
  intro Q hQ
  rcases ht with rfl | rfl <;> dsimp only [LargeEvenRawDatum] at hQ ⊢
  · exact recipeChevalley_and (P := fun R _ I _ => ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I)
      (fun K _ _ hK => pow_mem_E6 K hK hp hp2 hpn) hQ
  · exact recipeTwisted_and (P := fun R _ I _ => ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I)
      (fun K _ _ hK => pow_mem_twE6 hn K hK hp hp2 hpn) hQ

end E6

theorem ggAutRankLeTwo_of_pCyclic {R : Type} [Group R] [Finite R] {I F : Set (MulAut R)} {p : ℕ}
    (hp : p.Prime) (hPC : GGRawPCyclic p R I F)
    (hI : IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → ∀ E₀ : Subgroup (MulAut R),
      IsElemAbelian p E₀ → (∀ φ ∈ E₀, φ ∈ I) → Nat.card E₀ ≤ p) :
    GGAutRankLeTwo p R I F := by
  intro hs hna E hE
  obtain ⟨J, S, hJ, -, hnorm, ⟨g, hgS, hg⟩, hpS⟩ := hPC hs hna
  have hES : E ≤ S := fun φ hφ => hpS φ ⟨1, by rw [pow_one]; exact hE.2 φ hφ⟩
  have hQ : IsCyclic (↥S ⧸ J.subgroupOf S) := by
    refine ⟨⟨QuotientGroup.mk ⟨g, hgS⟩, fun q => ?_⟩⟩
    obtain ⟨s, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hg s s.2
    refine ⟨-k, ?_⟩
    change (QuotientGroup.mk (⟨g, hgS⟩ ^ (-k)) : ↥S ⧸ J.subgroupOf S) = QuotientGroup.mk s
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa [zpow_neg] using hk
  set χ : ↥E →* ↥S ⧸ J.subgroupOf S :=
    (QuotientGroup.mk' (J.subgroupOf S)).comp (Subgroup.inclusion hES) with hχ
  have hrange : Nat.card χ.range ≤ p := by
    refine TableB.card_le_of_isCyclic hp.pos inferInstance ?_
    rintro _ ⟨a, rfl⟩
    have ha : a ^ p = 1 := Subtype.ext (by simpa using hE.2 a a.2)
    rw [← map_pow, ha, map_one]
  set E₀ : Subgroup (MulAut R) := χ.ker.map E.subtype with hE₀
  have hE₀card : Nat.card E₀ = Nat.card χ.ker :=
    Subgroup.card_map_of_injective E.subtype_injective
  have hE₀E : E₀ ≤ E := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hE₀I : ∀ φ ∈ E₀, φ ∈ I := by
    rintro _ ⟨a, ha, rfl⟩
    have ha' : χ a = 1 := ha
    rw [hχ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at ha'
    rw [← hJ]
    exact ha'
  have hker : Nat.card χ.ker ≤ p :=
    hE₀card ▸ hI hs hna E₀ (NbrLangRest.isElemAbelian_of_le' hE hE₀E) hE₀I
  have h1 := Subgroup.card_ker_mul_card_range χ
  calc Nat.card E = Nat.card χ.ker * Nat.card χ.range := h1.symm
    _ ≤ p * p := Nat.mul_le_mul hker hrange
    _ = p ^ 2 := (sq p).symm

theorem card_le_of_inner_of_oddSylow {R : Type} [Group R] [Finite R] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2)
    (hsyl : ∀ (q : ℕ) [Fact q.Prime], q ≠ 2 → ∀ P : Sylow q R, IsCyclic P)
    (hs : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a) (E₀ : Subgroup (MulAut R))
    (hE : IsElemAbelian p E₀) (hEI : ∀ φ ∈ E₀, φ ∈ LargeEvenInnSet R) : Nat.card E₀ ≤ p := by
  have := Fact.mk hp
  have hinj := NbrLangRest.conj_injective_of_simple hs hna
  have hle : E₀ ≤ (MulAut.conj : R →* MulAut R).range := fun φ hφ => hEI φ hφ
  set P : Subgroup R := E₀.comap MulAut.conj with hP
  have hPE : Nat.card P = Nat.card E₀ := by
    rw [← Subgroup.card_map_of_injective hinj, hP, Subgroup.map_comap_eq_self hle]
  have hPp : ∀ r ∈ P, r ^ p = 1 := fun r hr =>
    hinj (by rw [map_pow, map_one]; exact hE.2 _ hr)
  have hPc : IsMulCommutative P := ⟨⟨fun x y => Subtype.ext (hinj (by
    have h1 := congrArg Subtype.val
      (hE.1.is_comm.comm ⟨MulAut.conj (x : R), x.2⟩ ⟨MulAut.conj (y : R), y.2⟩)
    simpa using h1))⟩⟩
  have hPg : IsPGroup p P := fun g => ⟨1, Subtype.ext (by simpa using hPp g g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPg
  have hodd : Odd (Nat.card P) := by
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  have hcyc := CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.odd_commutative_subgroup_cyclic
    P hodd hPc hsyl
  have h1 := TableB.card_le_of_isCyclic hp.pos hcyc hPp
  omega

theorem ggAutRankLeTwo_suzuki {a : ℕ}
    {K : Type} [Field K] [Finite K] (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    GGAutRankLeTwo p (LargeEvenCenterQuot (LargeEvenSzGroup a K)) (LargeEvenInnSet _)
      (LargeEvenMatFieldImage (LargeEvenCenterMk (LargeEvenSzGroup a K))) := by
  refine ggAutRankLeTwo_of_pCyclic hp (RawAutSz.ggRawPCyclic_suzuki ha hK) ?_
  suffices key : ∀ H : Subgroup (GL (Fin 4) K), H = suzukiGroup a K →
      IsSimpleGroup (LargeEvenCenterQuot H) → (∃ a b : LargeEvenCenterQuot H, a * b ≠ b * a) →
      ∀ E₀ : Subgroup (MulAut (LargeEvenCenterQuot H)), IsElemAbelian p E₀ →
        (∀ φ ∈ E₀, φ ∈ LargeEvenInnSet (LargeEvenCenterQuot H)) → Nat.card E₀ ≤ p from
    key _ (largeEvenSzGroup_eq a K)
  rintro H rfl hs hna E₀ hE hEI
  have hZ := CFSG.RankThree.PartOne.KE.suzuki_center_eq_bot ha hK
  have e : LargeEvenCenterQuot (suzukiGroup a K) ≃* CFSG.Open.GLASzGroup a K :=
    (centerQuotEquivOfBot hZ).trans
      (MulEquiv.subgroupCongr (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a K))
  exact card_le_of_inner_of_oddSylow hp hp2
    (CFSG.ProperTwoGeneratedCore.LocalCriterionDenominator.suzuki_model_oddSylow_cyclic a ha hK e)
    hs hna E₀ hE hEI

theorem largeEvenLabelAll_autRankLeTwo_twB2
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (ht : lab.tag = .twB2) :
    LargeEvenLabelAll lab (GGAutRankLeTwo p) := by
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  have hn3 : 3 ≤ n := hlab.2.2.2
  intro Q h
  dsimp only [LargeEvenRawDatum] at h ⊢
  obtain ⟨K, _, _, hK, hQ⟩ := h
  exact ⟨K, inferInstance, inferInstance, hK, hQ, ggAutRankLeTwo_suzuki (by omega) hK hp hp2⟩

theorem largeEvenLabelAll_autRankLeTwo_of_pow_card {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hpow : LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R →
      (∃ a b : R, a * b ≠ b * a) → ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I)
    (hcard : LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
        Nat.card X < p ^ 3) :
    LargeEvenLabelAll lab (GGAutRankLeTwo p) := by
  refine (largeEvenLabelAll_and hpow hcard).mono ?_
  rintro R _ I F ⟨hpw, hc⟩ hs hna E hE
  have hlt := hc hs hna E (fun φ hφ => hpw hs hna φ (hE.2 φ hφ)) hE
  rcases finite_or_infinite E with hfin | hinf
  · have hPg : IsPGroup p E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
    have := Fact.mk hp
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hPg
    rw [hk] at hlt ⊢
    have hk3 : k < 3 := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt
    exact Nat.pow_le_pow_right hp.pos (by omega)
  · rw [Nat.card_eq_zero_of_infinite]
    exact Nat.zero_le _

end NbrLangWeylRest

open NbrLangWeylRest NbrLangRest

@[expose] def GGNbrLangE6CoprimeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .E6 ∨ lab.tag = .twE6) ∧ ¬ p ∣ lab.n

@[expose] def GGNbrPowMemLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (GGNbrLangFieldTwoLabel lab ∨ GGLinearCoprimeDegLabel p lab ∨ GGSpOmegaCoprimeDegLabel p lab ∨
    GGExcCoprimeDegLabel p lab ∨ GGCorFourTwoOpenVacLabel p lab ∨ GGNbrLangE6CoprimeLabel p lab) ∧
    ¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3)

@[expose] def GGNbrInnerSmallLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  StdSubRestThree.GGTwoThreeSmallLabel p lab ∨ GGTableBNbrInnerA2Label p lab ∨
    (GGCorFourTwoSmallLabel p lab ∧ LargeEvenSplit p lab) ∨
    GGTableBNbrInnerNineSmallLabel p lab ∨ GGTableBNbrInnerNineClassicalLabel p lab

@[expose] def GGNbrWeylVacLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  lab.tag = .twB2 ∨ (GGNbrPowMemLabel p lab ∧ GGNbrInnerSmallLabel p lab)

section Labels


theorem ggOddAutAt_of_not_D4Three {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (hD : ¬ (lab.tag = .D ∧ lab.rank = 4 ∧ p = 3)) :
    GGOddAutAt p lab :=
  ggOddAutOn_true_of ggOddAutOn_done ggOddAutOn_rest5 p lab hp hp2 hlab trivial hD

theorem largeEvenLabelAll_pow_mem_powMem {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGNbrPowMemLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ φ : MulAut R, φ ^ p = 1 → φ ∈ I := by
  obtain ⟨h, hD⟩ := h
  have hodd := ggOddAutAt_of_not_D4Three hp hp2 hlab hD
  rcases h with h | h | h | h | h | h
  · exact largeEvenLabelAll_pow_mem_of_field_one hodd (largeEvenLabelAll_field_eq_one_two h)
  · exact largeEvenLabelAll_pow_mem_of_conj hodd
      (ggRawFieldConjOn_linear p hp hp2 lab hlab (h.1.elim Or.inl fun h' => Or.inr (Or.inl h')))
      (largeEvenLabelAll_field_pow_linear hlab h.1) h.2
  · refine largeEvenLabelAll_pow_mem_of_conj hodd ?_ (largeEvenLabelAll_field_pow_spOmega hlab h.1)
      h.2
    rcases h.1 with hB | hC | hDl
    · exact ggRawFieldConjOn_symplectic p hp hp2 lab hlab (Or.inl hB)
    · exact ggRawFieldConjOn_symplectic p hp hp2 lab hlab (Or.inr hC)
    · exact ggRawFieldConjOn_omegaPlus p hp hp2 lab hlab hDl
  · exact (largeEvenLabelAll_pow_mem_excCoprimeDeg hp hp2 hlab h).mono fun _ _ _ _ h' _ _ => h'
  · exact (largeEvenLabelAll_pow_mem_vac hp hlab h).mono fun _ _ _ _ h' _ _ => h'
  · exact (largeEvenLabelAll_pow_mem_e6 hp hp2 hlab h.1 h.2).mono fun _ _ _ _ h' _ _ => h'

theorem largeEvenLabelAll_card_lt_innerSmall {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGNbrInnerSmallLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) →
      ∀ X : Subgroup (MulAut R), (X : Set (MulAut R)) ⊆ I → IsElemAbelian p X →
        Nat.card X < p ^ 3 := by
  rcases h with h | h | h | h | h
  · exact (StdSubRestThree.largeEvenLabelAll_card_lt_twoThreeSmall h).mono
      fun _ _ _ _ hX _ _ => hX
  · exact (largeEvenLabelAll_card_lt_A2 hp h).mono fun _ _ _ _ hX _ _ => hX
  · exact (largeEvenLabelAll_card_lt_corFourTwoSmall hp hlab h.1 h.2).mono
      fun _ _ _ _ hX _ _ => hX
  · rcases h with h | h | h | h | h | h | h | h | ⟨ht, hl⟩
    · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab (Or.inl h)).mono
        fun _ _ _ _ hX _ _ => hX
    · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab (Or.inr (Or.inl h))).mono
        fun _ _ _ _ hX _ _ => hX
    · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab (Or.inr (Or.inr (Or.inl h)))).mono
        fun _ _ _ _ hX _ _ => hX
    · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab
        (Or.inr (Or.inr (Or.inr (Or.inl h))))).mono fun _ _ _ _ hX _ _ => hX
    · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))).mono fun _ _ _ _ hX _ _ => hX
    · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))).mono fun _ _ _ _ hX _ _ => hX
    · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))).mono
          fun _ _ _ _ hX _ _ => hX
    · exact (largeEvenLabelAll_card_lt_nineSmall hp hp2 hlab
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))).mono
          fun _ _ _ _ hX _ _ => hX
    · exact largeEvenLabelAll_card_lt_unitaryThree_all hp hp2 hlab ht hl
  · rcases h with ⟨h, hpe⟩ | ⟨h, hpe⟩ | ⟨ht, hpe⟩ | ⟨ht, hl, hpe⟩
    · exact (largeEvenLabelAll_card_lt_linear_of_ord hp hp2 h hpe).mono
        fun _ _ _ _ hX _ _ => hX
    · exact largeEvenLabelAll_card_lt_unitary_of_ord hp hp2 hlab h hpe
    · exact (largeEvenLabelAll_card_lt_symplectic_of_ord hp hp2 hlab ht hpe).mono
        fun _ _ _ _ hX _ _ => hX
    · exact largeEvenLabelAll_card_lt_orthogonal_of_ord hp hp2 ht hl hpe

theorem largeEvenLabelAll_autRankLeTwo_weylVac {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGNbrWeylVacLabel p lab) :
    LargeEvenLabelAll lab (GGAutRankLeTwo p) := by
  rcases h with h | ⟨h1, h2⟩
  · exact largeEvenLabelAll_autRankLeTwo_twB2 hp hp2 hlab h
  · exact largeEvenLabelAll_autRankLeTwo_of_pow_card hp
      (largeEvenLabelAll_pow_mem_powMem hp hp2 hlab h1)
      (largeEvenLabelAll_card_lt_innerSmall hp hp2 hlab h2)

theorem ggNbrInnerWeylOn_vac : GGNbrInnerWeylOn GGNbrWeylVacLabel :=
  ggNbrInnerWeylOn_of_autRankLeTwo fun _ _ hp hp2 hlab h =>
    largeEvenLabelAll_autRankLeTwo_weylVac hp hp2 hlab h

end Labels

theorem ggNbrLangTorusAxisOn_e6Coprime :
    GGNbrLangTorusAxisOn GGNbrLangE6CoprimeLabel :=
  ggNbrLangTorusAxisOn_of_pow_mem fun _ _ hp hp2 hlab h =>
    largeEvenLabelAll_pow_mem_e6 hp hp2 hlab h.1 h.2

theorem ggNbrLangTorusAxisOn_twB2 :
    GGNbrLangTorusAxisOn fun _ lab => lab.tag = .twB2 :=
  ggNbrLangTorusAxisOn_of_autRankLeTwo fun _ _ hp hp2 hlab h =>
    largeEvenLabelAll_autRankLeTwo_twB2 hp hp2 hlab h

end CFSG.StandardType

end
