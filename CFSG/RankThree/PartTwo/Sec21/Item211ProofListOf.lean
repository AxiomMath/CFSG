module

public import CFSG.RankThree.PartTwo.Sec21.Item211ProofList
public import CFSG.RankThree.PartTwo.Sec21.Item211ProofQuot
public import CFSG.RankThree.PartTwo.Sec4.Statements417
import CFSG.RankThree.PartTwo.Sec21.Item231Of
import CFSG.LocalAnalysis.SignalizerFunctor.InvariantSylowAmbient
import CFSG.RankThree.PartTwo.Sec4.LThreePiKind
import CFSG.Models.PGL

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

open CFSG.Blueprint

namespace Item211Proof

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G}

@[expose] noncomputable def slEquivOfRingEquiv {K K' : Type} [CommRing K] [CommRing K'] (n : ℕ)
    (κ : K ≃+* K') :
    Matrix.SpecialLinearGroup (Fin n) K ≃* Matrix.SpecialLinearGroup (Fin n) K' :=
  MonoidHom.toMulEquiv (Matrix.SpecialLinearGroup.map κ.toRingHom)
    (Matrix.SpecialLinearGroup.map κ.symm.toRingHom) (by ext x i j; simp) (by ext x i j; simp)

omit [Finite G] in
theorem nonempty_mulEquiv_SL3_of_isSLThreePiAt {X : Type} [Group X] {n : ℕ} (hn : 0 < n)
    (he : Even n) (h : Sec4.IsSLThreePiAt X (2 ^ n)) : Nonempty (X ≃* SL3 n) := by
  obtain ⟨K, _, _, h⟩ := h
  have hmod : 2 ^ n % 3 = 1 := by
    obtain ⟨k, rfl⟩ := he
    rw [← two_mul, pow_mul, Nat.pow_mod]
    norm_num
  rcases h with ⟨hK, -, ⟨f⟩⟩ | ⟨-, hq, -⟩
  · have := Fintype.ofFinite K
    have := Fintype.ofFinite (GaloisField 2 n)
    have hcard : Fintype.card K = Fintype.card (GaloisField 2 n) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, GaloisField.card 2 n hn.ne']
    exact ⟨f.trans ((Sec4.statedSLEquiv 3 K).trans
      (slEquivOfRingEquiv 3 (FiniteField.ringEquivOfCardEq hcard)))⟩
  · omega

theorem statedClassicalModel_PSL_of_mulEquiv {X : Type} [Group X] {n p f : ℕ} [Fact p.Prime]
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSL n p f)
    (e : X ≃* projSL n (GaloisField p f)) : StatedClassicalModel X .PSL n p f :=
  CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm e

theorem statedClassicalModel_PSp_of_mulEquiv {X : Type} [Group X] {n p f : ℕ} [Fact p.Prime]
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .PSp n p f)
    (e : X ≃* projSp n (GaloisField p f)) : StatedClassicalModel X .PSp n p f :=
  CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSp hadm e

theorem exists_eOne (hA : IsPGroup 3 A) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {E₀ : Subgroup G} (hE₀ : Late.IsE27 E₀) (hE₀A : E₀ ≤ A) {U : Subgroup G}
    (hU : U ∈ invariantPiSubgroups L E₀ (piOf 2))
    (hUE : ¬ ⁅U, E₀⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L) :
    Late.IsE27 ((E₀.subgroupOf (L ⊔ A)).map (piX L A)) ∧
      (E₀.subgroupOf (L ⊔ A)).map (piX L A) ≤ aOne L A ∧
      ∃ T ∈ invariantPiSubgroups (lOne L A) ((E₀.subgroupOf (L ⊔ A)).map (piX L A)) (piOf 2),
        ¬ T ≤ Subgroup.centralizer
          (((E₀.subgroupOf (L ⊔ A)).map (piX L A) : Subgroup (QuotX L A)) : Set (QuotX L A)) := by
  have hθ := inSubgroup_theta_sup hA hAL
  have hE₀M : E₀ ≤ L ⊔ A := hE₀A.trans le_sup_right
  have hE₀p : IsPGroup 3 E₀ := fun e => ⟨1, Subtype.ext (by simpa using hE₀.1.2 e e.2)⟩
  have hEM : IsPGroup 3 (E₀.subgroupOf (L ⊔ A)) :=
    hE₀p.comap_of_injective (L ⊔ A).subtype (L ⊔ A).subtype_injective
  set e := Sec13.mkEquivOfIsPGroup hEM with he
  obtain ⟨hUL, hU2, hEU⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hU
  refine ⟨⟨⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩, ?_, ?_⟩
  · obtain ⟨a, rfl⟩ := e.surjective x
    obtain ⟨b, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    apply Subtype.ext
    have := hE₀.1.1.is_comm.comm (⟨((a : ↥(L ⊔ A)) : G), Subgroup.mem_subgroupOf.mp a.2⟩ : E₀)
      ⟨((b : ↥(L ⊔ A)) : G), Subgroup.mem_subgroupOf.mp b.2⟩
    have h2 : ((a : ↥(L ⊔ A)) : G) * ((b : ↥(L ⊔ A)) : G) =
        ((b : ↥(L ⊔ A)) : G) * ((a : ↥(L ⊔ A)) : G) := congrArg Subtype.val this
    exact h2
  · obtain ⟨a, ha, rfl⟩ := hx
    rw [← map_pow]
    have h3 : a ^ 3 = 1 := Subtype.ext (hE₀.1.2 _ (Subgroup.mem_subgroupOf.mp ha))
    rw [h3, map_one]
  · rw [← Nat.card_congr e.toEquiv, ← hE₀.2]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hE₀M).toEquiv
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, Subgroup.mem_subgroupOf.mpr (hE₀A (Subgroup.mem_subgroupOf.mp ha)), rfl⟩
  · set UM := U.subgroupOf (L ⊔ A) with hUM
    have hEMN : E₀.subgroupOf (L ⊔ A) ≤ Subgroup.normalizer (UM : Set ↥(L ⊔ A)) := by
      intro x hx
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [hUM, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact Subgroup.mem_normalizer_iff.mp (hEU (Subgroup.mem_subgroupOf.mp hx)) y
    refine ⟨UM.map (piX L A), (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr
      ⟨Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
          (hUL (Subgroup.mem_subgroupOf.mp hx)),
        (hU2.comap_of_injective (L ⊔ A).subtype (L ⊔ A).subtype_injective).map _,
        (Subgroup.map_mono hEMN).trans (Subgroup.le_normalizer_map _)⟩, ?_⟩
    intro hc
    apply hUE
    rw [Subgroup.commutator_le]
    intro u hu x hx
    have h1 := Subgroup.mem_centralizer_iff.mp
      (hc ⟨⟨u, Subgroup.mem_sup_left (hUL hu)⟩, Subgroup.mem_subgroupOf.mpr hu, rfl⟩)
      (piX L A ⟨x, hE₀M hx⟩) ⟨⟨x, hE₀M hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have h2 : piX L A ((⟨u, Subgroup.mem_sup_left (hUL hu)⟩ : ↥(L ⊔ A)) *
        ⟨x, hE₀M hx⟩ * (⟨u, Subgroup.mem_sup_left (hUL hu)⟩ : ↥(L ⊔ A))⁻¹ *
          (⟨x, hE₀M hx⟩ : ↥(L ⊔ A))⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
      group
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
    have h3 : u * x * u⁻¹ * x⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) (L ⊔ A) := ⟨_, h2, rfl⟩
    rw [hθ] at h3
    rw [commutatorElement_def]
    exact h3

theorem quad_le_four (h611 : Sec6.Item6_11_1) (hst : PartTwoStanding G) :
    ∀ (A' E' : Subgroup (QuotX L A)) (c' : QuotX L A) (m : ℕ),
      Sec4.IsQuad417 (lOne L A) A' E' c' m → m ≤ 4 := by
  rintro A' E' c' m ⟨hmax, hcard, -, -, hE27, hEA, T, hT, hTc⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E'', -, hE''map, hE''card, hE''e⟩ := exists_lift_of_le (L := L) (A := A) (T := ⊥)
    IsPGroup.of_bot hE27.1 (by rw [Subgroup.map_bot]; exact bot_le)
  have hE''p : IsPGroup 3 E'' := fun x => ⟨1, Subtype.ext (by simpa using hE''e.2 x x.2)⟩
  obtain ⟨S, hE''S, -, hScard, hSe⟩ :=
    exists_lift_of_le hE''p hmax.prop (by rw [hE''map]; exact hEA)
  obtain ⟨-, hT2, hTN⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hT
  have hT1 : T ≠ ⊥ := fun h => hTc (h ▸ bot_le)
  set N := aschbacherSolvableCore 3 ↥(L ⊔ A) with hN
  set D : Subgroup ↥(L ⊔ A) := T.comap (piX L A) with hD
  have hDcard : Nat.card D = Nat.card N * Nat.card T :=
    QuotientGroup.card_preimage_mk N (T : Set (QuotX L A))
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT2
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact hT1 (Subgroup.card_eq_one.mp hk)
  have hcop : Nat.Coprime 3 (Nat.card D) := by
    rw [hDcard, hk]
    exact Nat.Coprime.mul_right
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
        three_not_dvd_card_aschbacherSolvableCore)
      (Nat.Coprime.pow_right k (by norm_num))
  have h2 : 2 ∣ Nat.card D := by
    rw [hDcard, hk]
    exact Dvd.dvd.mul_left (dvd_pow_self 2 hk0) _
  have hE''D : E'' ≤ Subgroup.normalizer (D : Set ↥(L ⊔ A)) := by
    intro x hx
    have hxE : piX L A x ∈ E' := by
      rw [← hE''map]
      exact ⟨x, hx, rfl⟩
    exact Subgroup.le_normalizer_comap (piX L A) (hTN hxE)
  obtain ⟨Q, hQN, hQ1⟩ :=
    CFSG.SignalizerFunctor.Helpers.normalized_subgroup_invariant_sylow_nontrivial
      3 2 Nat.prime_three Nat.prime_two E'' D hE''p hE''D hcop h2
  set U₁ : Subgroup G := ((Q : Subgroup D).map D.subtype).map (L ⊔ A).subtype with hU₁
  have hE₂ : E''.map (L ⊔ A).subtype ∈ partTwoE G := by
    refine ⟨isElemAbelian_map_subtype hE''e, ?_, U₁, ?_, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective (L ⊔ A).subtype_injective, hE''card, hE27.2]
    · intro h0
      apply hQ1
      rwa [hU₁, Subgroup.map_eq_bot_iff_of_injective _ (L ⊔ A).subtype_injective] at h0
    · exact (Q.isPGroup'.map D.subtype).map (L ⊔ A).subtype
    · exact (Subgroup.map_mono hQN).trans (Subgroup.le_normalizer_map _)
  obtain ⟨B, hSB, hBmax⟩ := Finite.exists_le_maximal
    (p := fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) (isElemAbelian_map_subtype hSe)
  have hBF : B ∈ partTwoF G :=
    ⟨hBmax.prop, fun B' hB' hBB' => le_antisymm (hBmax.2 hB' hBB') hBB', _, hE₂,
      (Subgroup.map_mono hE''S).trans hSB⟩
  have hrank := h611 G hst B hBF
  have hBp : IsPGroup 3 B := fun x => ⟨1, Subtype.ext (by simpa using hBmax.prop.2 x x.2)⟩
  obtain ⟨j, hj⟩ := hBp.exists_card_eq
  have hjle : j ≤ CFSG.Open.pRank 3 B :=
    le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three B)
      ⟨B, le_rfl, ⟨hBmax.prop.1, hBmax.prop.2⟩, hj⟩
  have hmS : 3 ^ m ≤ 3 ^ j := by
    rw [← hj, ← hcard, ← hScard, ← Subgroup.card_map_of_injective (L ⊔ A).subtype_injective]
    exact Subgroup.card_le_of_le hSB
  have := (Nat.pow_le_pow_iff_right (by norm_num)).mp hmS
  omega

theorem centralizer_ne_top (hG : TheoremFourHyp G) {c : G} (hc : c ≠ 1) :
    Subgroup.centralizer ({c} : Set G) ≠ ⊤ := by
  intro hCt
  have hcZ : c ∈ Subgroup.center G := Subgroup.mem_center_iff.mpr fun g => by
    have hg : g ∈ Subgroup.centralizer ({c} : Set G) := hCt ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  rcases hG.isSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h, Subgroup.mem_bot] at hcZ
    exact hc hcZ
  · obtain ⟨a, b, hab⟩ := hG.nonabelian
    exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)

omit [Finite G] in
theorem aOne_sup_lOne : aOne L A ⊔ lOne L A = ⊤ := by
  have h1 : L.subgroupOf (L ⊔ A) ⊔ A.subgroupOf (L ⊔ A) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left : L ≤ L ⊔ A) (le_sup_right : A ≤ L ⊔ A),
      Subgroup.subgroupOf_self]
  rw [sup_comm (aOne L A) (lOne L A), ← Subgroup.map_sup, h1, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top]
  exact QuotientGroup.mk'_surjective _

end Item211Proof

open Item211Proof

section Certs


variable {G : Type} [Group G] [Finite G] {L A : Subgroup G}

theorem list211_of_alt417 (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {c : G} {Φ₀ : lBar L ≃* lOne L A}
    (hΦ₀ : ∀ l : L, (Φ₀ (l : lBar L) : QuotX L A) = piX L A ⟨l, Subgroup.mem_sup_left l.2⟩)
    (eAut : Sec4.autIn (lOne L A) (aOne L A) ≃* starOf A L)
    (eX : QuotX L A ≃* ↥(Sec13.lBarA c L A)) {m : ℕ} (hm : Nat.card A = 3 ^ m)
    (h : Sec4.Alt417 (lOne L A) (aOne L A) m) : List211 A c L := by
  have htc : ∀ {Y : Type} [Group Y], Sec4.IsTripleCover ↥(lOne L A) Y →
      Sec4.IsTripleCover (lBar L) Y := fun h => Sec13.isTripleCover_of_mulEquiv Φ₀.symm h
  have hch : ∀ {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {p f : ℕ},
      ChevalleyExceptionalModel ↥(lOne L A) t p f → ChevalleyExceptionalModel (lBar L) t p f :=
    fun h => CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv Φ₀ h
  rcases h with ⟨x, hx, hk⟩ | ⟨rfl, hH, hT⟩ | ⟨rfl, p, hp, hp3, h3⟩ | ⟨rfl, h7, hZ4⟩ |
      ⟨rfl, h9, hS4⟩ | ⟨rfl, h6⟩ | ⟨rfl, hJ, hX⟩ | ⟨rfl, hON⟩ | ⟨rfl, ⟨n, hn, hne, h9⟩, hS3⟩ |
      ⟨rfl, ⟨n, hn, hne, h10⟩, hD12⟩ | ⟨rfl, h11, hD8⟩ | ⟨rfl, ⟨n, hn, h12⟩, hS4⟩ |
      ⟨rfl, h13, hZS⟩
  ·
    obtain ⟨a, haA, rfl⟩ := exists_eq_piX_of_mem_aOne hx
    exact Or.inl ⟨a, haA, hk.imp (inducesStdKind_of_lOne hAL hΦ₀ haA)
      (inducesStdKind_of_lOne hAL hΦ₀ haA)⟩
  ·
    have eH : ↥(aOne L A ⊔ lOne L A) ≃* ↥(Sec13.lBarA c L A) :=
      (MulEquiv.subgroupCongr aOne_sup_lOne).trans (Subgroup.topEquiv.trans eX)
    exact Or.inr (Or.inl ⟨hm, Sec13.isHeisCentral_of_mulEquiv eH Φ₀.symm hH, hT.imp htc htc⟩)
  ·
    refine Or.inr (Or.inr (Or.inl ⟨hm, p, hp, hp3, ?_⟩))
    rcases h3 with h | h | ⟨hp1, h⟩ | ⟨hp2, h⟩ | ⟨e, he, h⟩
    · exact Or.inl (hch h)
    · exact Or.inr (Or.inl ((h.map Φ₀.trans)))
    · exact Or.inr (Or.inr (Or.inl ⟨hp1, (h.map Φ₀.trans)⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp2, (h.map Φ₀.trans)⟩)))
    · refine Or.inr (Or.inr (Or.inr (Or.inr ⟨e, he, ?_⟩)))
      rcases h with h | h
      · exact Or.inl (isSLThreePiAt_of_mulEquiv Φ₀.symm h)
      · exact Or.inr (isoLThreePi_of_mulEquiv Φ₀.symm h)
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hm, (h7.map Φ₀.trans), (hZ4.map eAut.symm.trans)⟩)))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm, h9.map Φ₀.trans,
      hS4.map eAut.symm.trans⟩))))
  ·
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm, ?_⟩)))))
    rcases h6 with ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ | ⟨h, h'⟩ |
      ⟨h, h'⟩ | ⟨h, h'⟩
    · exact Or.inl ⟨(h.map Φ₀.trans), (h'.map eAut.symm.trans)⟩
    · exact Or.inr (Or.inl ⟨(h.map Φ₀.trans), (h'.map eAut.symm.trans)⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨(h.map Φ₀.trans), (h'.map eAut.symm.trans)⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h.map Φ₀.trans,
        h'.imp (Nonempty.map eAut.symm.trans) (Nonempty.map eAut.symm.trans)⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨(h.map Φ₀.trans), (h'.map eAut.symm.trans)⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.map Φ₀.trans,
        h'.map eAut.symm.trans⟩)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h.map Φ₀.trans,
        h'.map eAut.symm.trans⟩))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨h.map Φ₀.trans,
          h'.imp (Nonempty.map eAut.symm.trans) (Nonempty.map eAut.symm.trans)⟩)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h.map Φ₀.trans,
        h'.map eAut.symm.trans⟩)))))))
  ·
    obtain ⟨f⟩ := Nonempty.intro eAut
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm,
      hJ.imp (Nonempty.map Φ₀.trans) htc,
      isExtOf_of_mulEquiv f hX⟩))))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hm, htc hON⟩)))))))
  ·
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hm, ⟨n, hn, hne, ?_⟩, (hS3.map eAut.symm.trans)⟩))))))))
    rcases h9 with ⟨h, hC⟩ | ⟨h, hC⟩
    · exact Or.inl ⟨(h.map Φ₀.trans), isTypeCOn_of_lOne hAL hΦ₀ hC⟩
    · obtain ⟨f⟩ := nonempty_mulEquiv_SL3_of_isSLThreePiAt hn hne h
      exact Or.inr ⟨⟨Φ₀.trans f⟩, isTypeCOnBarSL_of_lOne hAL hΦ₀ hC⟩
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨hm, ⟨n, hn, hne, h10.imp hch hch⟩, (hD12.map eAut.symm.trans)⟩)))))))))
  ·
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨hm, ?_, (hD8.map eAut.symm.trans)⟩))))))))))
    rcases h11 with ⟨n, hn, hne, h⟩ | h | h4 | h5
    · exact Or.inl ⟨n, hn, hne, h.imp (Nonempty.map Φ₀.trans) (Nonempty.map Φ₀.trans)⟩
    · exact Or.inr (Or.inl ((h.map Φ₀.trans)))
    · obtain ⟨e4⟩ := h4
      exact Or.inr (Or.inr (Or.inl (statedClassicalModel_PSL_of_mulEquiv
        ⟨Nat.prime_two, le_rfl, by norm_num, by simp, by simp⟩ (Φ₀.trans e4))))
    · obtain ⟨e5⟩ := h5
      exact Or.inr (Or.inr (Or.inr (statedClassicalModel_PSL_of_mulEquiv
        ⟨Nat.prime_two, le_rfl, by norm_num, by simp, by simp⟩ (Φ₀.trans e5))))
  ·
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl ⟨hm, ⟨n, hn, (h12.map Φ₀.trans)⟩, (hS4.map eAut.symm.trans)⟩)))))))))))
  ·
    obtain ⟨e13⟩ := h13
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr ⟨hm, statedClassicalModel_PSp_of_mulEquiv
        ⟨Nat.prime_two, le_rfl, by norm_num, by simp⟩ (Φ₀.trans e13),
        hZS.map eAut.symm.trans⟩)))))))))))

theorem item211List_of (h417 : Sec4.Item4_17) (h611 : Sec6.Item6_11_1) (h45 : Sec4.Item4_5)
    (h66 : Sec6.Item6_6) (h41 : Sec4.Item4_1LargePrime) : Item211List := by
  intro G _ _ A E U c L hpair
  refine ⟨card_eq_of_mem_partTwoS h611 hpair.toSec21Std, ?_⟩
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := hpair.mem_S.1.1
  have hA : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a a.2)⟩
  have hLc : L ∈ thetaComponentsAt 3 c := (lZeroStarAt_subset A c) hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAe.1.is_comm.comm ⟨a, ha⟩ ⟨c, hcA⟩))
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hpair.standing.toTheoremFourHyp hAe hcA hc1
      L hLc
  have hq : IsQuasisimple (lBar L) := by
    obtain ⟨L', hL', hLL'⟩ := hLc
    rw [← hLL']
    exact LocalCores.isQuasisimple_of_mulEquiv (Sec13.thetaQuotEquivSub _ L') hL'.2.2
  have hCA : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c := by
    have hsc := Item211Proof.sectionCentralizer_eq h45 h66 hpair
    rw [Sec13.sectionCentralizer_eq_inf hAL] at hsc
    exact SetLike.coe_injective hsc
  have hΛ : SectionFourHyp ↥(L ⊔ A) := hpair.standing.toTheoremFourHyp.sectionFourHyp
    (fun htop => centralizer_ne_top hpair.standing.toTheoremFourHyp hc1
      (eq_top_iff.mpr (htop ▸ sup_le hLC hAC)))
  obtain ⟨Φ₀, hΦ₀⟩ := exists_lEquiv hAL
  have hX : SectionFourHyp (QuotX L A) := sectionFourHyp_quotX h41 hΛ hA hAL Φ₀ hq
  obtain ⟨eAut⟩ := nonempty_autIn_lOne_equiv hA hAL
  obtain ⟨eX⟩ := nonempty_quotX_equiv_lBarA hLc hAC hA hAL
  obtain ⟨m, hm⟩ := hA.exists_card_eq
  obtain ⟨E₀, hE₀, hE₀A, -, U₀, hU₀, hU₀E⟩ :=
    mem_lZeroUnion_iff.mp (lZeroStar_subset_lZeroUnion A (lZeroStarAt_subset_lZeroStar A c
      hpairs.2.2.1))
  obtain ⟨hE₁, hE₁A, T, hT, hTc⟩ :=
    exists_eOne hA hAL (Late.isE27_of_mem_partTwoE hE₀) hE₀A hU₀ hU₀E
  have hc₁ : orderOf (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) = 3 := by
    have h1 : (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) =
        ((aEquiv (L := L) hA ⟨c, hcA⟩ : aOne L A) : QuotX L A) := rfl
    rw [h1, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact orderOf_eq_prime (hAe.2 c hcA) hc1
  have hquad : Sec4.IsQuad417 (lOne L A) (aOne L A) ((E₀.subgroupOf (L ⊔ A)).map (piX L A))
      (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) m :=
    ⟨maximal_aOne hAe hpair.mem_S.1.2.1,
      by rw [← Nat.card_congr (aEquiv (L := L) hA).toEquiv, hm],
      aOne_inf_centralizer hA hAL hcA hCA, hc₁, hE₁, hE₁A, T, hT, hTc⟩
  have h417' := h417 (QuotX L A) hX pCore_two_quotX (lOne L A)
    (isComponent_lOne hAL Φ₀ hq) (quad_le_four h611 hpair.standing) (aOne L A)
    ((E₀.subgroupOf (L ⊔ A)).map (piX L A)) (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) m hquad
  exact list211_of_alt417 hAL hΦ₀ eAut eX hm h417'

end Certs

end CFSG.RankThree.PartTwo.Sec21
