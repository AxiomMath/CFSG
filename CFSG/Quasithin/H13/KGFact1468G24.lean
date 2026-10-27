module

public import CFSG.Quasithin.H13.KGFact1468Spor
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenShortCentralizer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenLongCentralizer
public import CFSG.Quasithin.H13.NQCatG2RadModel
public import CFSG.RankThree.Chevalley.EvenRealThreeCentralizingInvolution
public import CFSG.Quasithin.Background.A4FourQuot
public import CFSG.Quasithin.H13.U4ParLine
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.Quasithin.Background.F1Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieFrame

public section

namespace CFSG.Quasithin.H13.KG1468

open CFSG.Open CFSG.Quasithin CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.LieType.BorelTits

section Transport

variable {Y Y' : Type} [Group Y] [Group Y']

@[expose] def BadA (H : Subgroup Y) (y : Y) : Prop :=
  ∃ A : Subgroup Y, A ≤ pCoreOf 2 (oTwoUpper (H ⊓ Subgroup.centralizer ({y} : Set Y))) ∧
    (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) ∧
    oTwoUpper (H ⊓ Subgroup.centralizer ({y} : Set Y)) ≤ Subgroup.normalizer (A : Set Y) ∧
    16 ≤ (A ⊓ Subgroup.centralizer
      (pCoreOf 2 (oTwoUpper (H ⊓ Subgroup.centralizer ({y} : Set Y))) : Set Y)).relIndex A

theorem badA_top_of_bad {X : Type} [Group X] [Finite X] {x : X} (h : Bad x) : BadA ⊤ x := by
  obtain ⟨-, A, h1, h2, h3, h4⟩ := h
  simp only [BadA, top_inf_eq]
  exact ⟨A, h1, h2, h3, h4⟩

theorem map_inf_centralizer {ι : Y →* Y'} (hι : Function.Injective ι) (H : Subgroup Y) (y : Y) :
    (H ⊓ Subgroup.centralizer ({y} : Set Y)).map ι =
      H.map ι ⊓ Subgroup.centralizer ({ι y} : Set Y') := by
  ext z
  simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨w, ⟨hwH, hwC⟩, rfl⟩
    exact ⟨⟨w, hwH, rfl⟩, by rw [← map_mul, ← map_mul, hwC]⟩
  · rintro ⟨⟨w, hwH, rfl⟩, hwC⟩
    exact ⟨w, ⟨hwH, hι (by rw [map_mul, map_mul, hwC])⟩, rfl⟩

theorem map_inf_centralizer_subgroup {ι : Y →* Y'} (hι : Function.Injective ι)
    (A B : Subgroup Y) :
    (A ⊓ Subgroup.centralizer (B : Set Y)).map ι =
      A.map ι ⊓ Subgroup.centralizer (B.map ι : Set Y') := by
  ext z
  constructor
  · rintro ⟨w, ⟨hwA, hwC⟩, rfl⟩
    refine ⟨⟨w, hwA, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hwC b hb]
  · rintro ⟨⟨w, hwA, rfl⟩, hwC⟩
    refine ⟨w, ⟨hwA, Subgroup.mem_centralizer_iff.mpr fun b hb => hι ?_⟩, rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hwC _ (Subgroup.mem_map_of_mem ι hb)

theorem map_oTwoUpper {ι : Y →* Y'} (hι : Function.Injective ι) (X : Subgroup Y) :
    (oTwoUpper X).map ι = oTwoUpper (X.map ι) := by
  unfold oTwoUpper
  rw [MonoidHom.map_closure]
  congr 1
  ext z
  constructor
  · rintro ⟨w, ⟨hw, hodd⟩, rfl⟩
    exact ⟨⟨w, hw, rfl⟩, by rwa [orderOf_injective ι hι]⟩
  · rintro ⟨⟨w, hw, rfl⟩, hodd⟩
    exact ⟨w, ⟨hw, by rwa [orderOf_injective ι hι] at hodd⟩, rfl⟩

theorem pCoreOf_map_inj {ι : Y →* Y'} (hι : Function.Injective ι) (p : ℕ) (X : Subgroup Y) :
    pCoreOf p (X.map ι) = (pCoreOf p X).map ι := by
  let e : ↥X ≃* ↥(X.map ι) := X.equivMapOfInjective ι hι
  have h1 := CFSG.LieType.BorelTits.map_pCore_mulEquiv p e
  unfold pCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem badA_map {ι : Y →* Y'} (hι : Function.Injective ι) {H : Subgroup Y} {y : Y}
    (h : BadA H y) : BadA (H.map ι) (ι y) := by
  obtain ⟨A, hAR, hAab, hKA, hidx⟩ := h
  have hK₀ : oTwoUpper (H.map ι ⊓ Subgroup.centralizer ({ι y} : Set Y')) =
      (oTwoUpper (H ⊓ Subgroup.centralizer ({y} : Set Y))).map ι := by
    rw [← map_inf_centralizer hι, map_oTwoUpper hι]
  refine ⟨A.map ι, ?_, ?_, ?_, ?_⟩
  · rw [hK₀, pCoreOf_map_inj hι]
    exact Subgroup.map_mono hAR
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAab a ha b hb]
  · rw [hK₀]
    exact (Subgroup.map_mono hKA).trans (Subgroup.le_normalizer_map ι)
  · rw [hK₀, pCoreOf_map_inj hι, ← map_inf_centralizer_subgroup hι,
      Subgroup.relIndex_map_map_of_injective _ _ hι]
    exact hidx

theorem map_conj_eq_self {H : Subgroup Y} {g : Y} (hg : g ∈ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  apply le_antisymm
  · rintro _ ⟨h, hh, rfl⟩
    exact H.mul_mem (H.mul_mem hg hh) (H.inv_mem hg)
  · intro h hh
    refine ⟨g⁻¹ * h * g, H.mul_mem (H.mul_mem (H.inv_mem hg) hh) hg, ?_⟩
    simp [mul_assoc]

theorem badA_conj {H : Subgroup Y} {y g : Y} (hg : g ∈ H) (h : BadA H y) :
    BadA H (g * y * g⁻¹) := by
  have := badA_map (ι := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective h
  rwa [map_conj_eq_self hg] at this

end Transport

section Core

variable {Y : Type} [Group Y] [Finite Y]

theorem pCoreOf_oTwoUpper_sup_le {Q L : Subgroup Y} (hLQ : L ≤ Subgroup.normalizer (Q : Set Y))
    (hQ2 : IsPGroup 2 Q)
    (hL : ∀ N : Subgroup Y, N ≤ L → L ≤ Subgroup.normalizer (N : Set Y) → IsPGroup 2 N →
      N = ⊥) :
    pCoreOf 2 (oTwoUpper (Q ⊔ L)) ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (oTwoUpper (Q ⊔ L)) with hRdef
  have hCQ : Q ⊔ L ≤ Subgroup.normalizer (Q : Set Y) := sup_le Subgroup.le_normalizer hLQ
  have hCR : Q ⊔ L ≤ Subgroup.normalizer (R : Set Y) :=
    (le_normalizer_oTwoUpper (Q ⊔ L)).trans (normalizer_le_normalizer_pCoreOf 2 _)
  have hRC : R ≤ Q ⊔ L := (pCoreOf_le 2 _).trans (oTwoUpper_le _)
  have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 _
  have hRQ2 : IsPGroup 2 ↥(R ⊔ Q) := hR2.to_sup_of_normal_right' hQ2 (hRC.trans hCQ)
  have hLRQ : L ≤ Subgroup.normalizer ((R ⊔ Q : Subgroup Y) : Set Y) := by
    intro l hl
    have e₁ := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hCR ((le_sup_right : L ≤ Q ⊔ L) hl))
    have e₂ := Subgroup.mem_normalizer_iff_map_conj_eq.mp (hLQ hl)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, e₁, e₂]
  have hN : (R ⊔ Q) ⊓ L = ⊥ :=
    hL _ inf_le_right ((le_inf hLRQ Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf) (hRQ2.to_le inf_le_left)
  intro r hr
  obtain ⟨q, hq, l, hl, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hLQ).mp (hRC hr)
  have hlN : l ∈ (R ⊔ Q) ⊓ L := by
    refine ⟨?_, hl⟩
    have e : l = q⁻¹ * (q * l) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (inv_mem hq)) (Subgroup.mem_sup_left hr)
  rw [hN, Subgroup.mem_bot] at hlN
  rw [hlN, mul_one]
  exact hq

omit [Finite Y] in
theorem eq_bot_of_le_range_sl2 {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) {ρ : Matrix.SpecialLinearGroup (Fin 2) K →* Y}
    (hρ : Function.Injective ρ) {N : Subgroup Y} (hN : N ≤ ρ.range)
    (hnorm : ρ.range ≤ Subgroup.normalizer (N : Set Y)) (h2 : IsPGroup 2 N) : N = ⊥ := by
  have := H13.U4Par.isSimpleGroup_sl2_of_charTwo K hK
  have hNn : (N.comap ρ).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_comap] at hn ⊢
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hnorm ⟨g, rfl⟩) (ρ n)).mp hn⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap ρ) with h0 | h0
  · rw [← Subgroup.map_comap_eq_self hN, h0, Subgroup.map_bot]
  · exfalso
    apply H13.U4Par.not_isPGroup_sl2_of_charTwo K
    have h3 : IsPGroup 2 ↥(N.comap ρ) := h2.comap_of_injective ρ hρ
    rw [h0] at h3
    exact h3.of_equiv Subgroup.topEquiv

end Core

section Model

variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem not_badA_v
    (hK : 4 ≤ Nat.card K) :
    ¬ BadA (adjointGroup .G2 K) (pinnedX .G2 K g2v 1) := by
  have := finite_modGL (τ := .G2) (K := K)
  rintro ⟨A, hAR, -, -, hidx⟩
  obtain ⟨-, -, hEl, hC, -, hLn, -, ⟨ρ, -, -, hρr, hρ⟩, -⟩ :=
    even_G2_highest_short_root_centralizer K
  rw [hC] at hAR hidx
  have hR := pCoreOf_oTwoUpper_sup_le hLn (IsElementaryAbelian.isPGroup 2 _)
    (fun N hN hNn hN2 => eq_bot_of_le_range_sl2 hK hρ (hρr ▸ hN) (hρr ▸ hNn) hN2)
  have hAC : A ⊓ Subgroup.centralizer
      (pCoreOf 2 (oTwoUpper (g2ShortRadical K ⊔ g2RankOne K g2ia)) : Set (ModGL .G2 K)) = A := by
    refine inf_eq_left.mpr fun a ha => Subgroup.mem_centralizer_iff.mpr fun r hr => ?_
    have h1 := hR hr
    have h2 := hR (hAR ha)
    have h3 := hEl.toIsMulCommutative.is_comm.comm (⟨r, h1⟩ : ↥(g2ShortRadical K)) ⟨a, h2⟩
    have h4 := congrArg Subtype.val h3
    simpa using h4
  rw [hAC, Subgroup.relIndex_self] at hidx
  omega

omit [Finite K] in
theorem g2LongRadical_le_parabolicRadical :
    g2LongRadical K ≤ CFSG.LieType.Chevalley.parabolicRadical Tag.G2 K
      {CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2.i1} := by
  rintro _ ⟨B, C, D, E, F, rfl⟩
  have h0 : pinnedX .G2 K g2r 0 = 1 := pinnedX_zero (τ := Tag.G2) K g2r
  show pinnedX .G2 K g2r 0 * pinnedX .G2 K g2a B * pinnedX .G2 K g2u C * pinnedX .G2 K g2v D *
    pinnedX .G2 K g2b E * pinnedX .G2 K g2c F ∈ _
  rw [h0, one_mul]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (NQCat.G2Rad.memA B) (NQCat.G2Rad.memU C)) (NQCat.G2Rad.memV D)) (NQCat.G2Rad.memB E))
    (NQCat.G2Rad.memC F)

theorem not_badA_c
    (hK : 4 ≤ Nat.card K) :
    ¬ BadA (adjointGroup .G2 K) (pinnedX .G2 K g2c 1) := by
  have := finite_modGL (τ := .G2) (K := K)
  rintro ⟨A, hAR, hAab, hKA, hidx⟩
  obtain ⟨-, -, hQ2, hC, -, hLn, -, ⟨ρ, -, -, hρr, hρ⟩, hcent, -⟩ :=
    even_G2_highest_long_root_centralizer K
  have hR := pCoreOf_oTwoUpper_sup_le hLn hQ2
    (fun N hN hNn hN2 => eq_bot_of_le_range_sl2 hK hρ (hρr ▸ hN) (hρr ▸ hNn) hN2)
  set P := CFSG.LieType.Chevalley.parabolicSubgroup Tag.G2 K
    {CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2.i1} with hP
  have hPC : perfectCore P ≤ adjointGroup .G2 K ⊓
      Subgroup.centralizer ({pinnedX .G2 K g2c 1} : Set (ModGL .G2 K)) := by
    refine le_inf ((perfectCore_le P).trans
      (CFSG.LieType.Chevalley.parabolicSubgroup_le_adjointGroup Tag.G2 K _))
      (NQCat.G2Rad.perfectCore_le_centralizer.trans (Subgroup.centralizer_le ?_))
    rintro _ rfl
    exact Subgroup.subset_closure ⟨1, rfl⟩
  have hPK : perfectCore P ≤ oTwoUpper (adjointGroup .G2 K ⊓
      Subgroup.centralizer ({pinnedX .G2 K g2c 1} : Set (ModGL .G2 K))) :=
    perfect_le_oTwoUpper hPC (Subgroup.isPerfect_iff.mpr (perfectCore_perfect _))
  rw [hC] at hAR hKA hidx hPK
  have hAN : A ≤ CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2.N1 := by
    have h1 := NQCat.G2Rad.centerOf_le_of_le_normalizer hK
      ((hAR.trans hR).trans (g2LongRadical_le_parabolicRadical K)) (hPK.trans hKA)
    have hcen : A ≤ centerOf A := fun a ha =>
      Subgroup.mem_inf.mpr ⟨ha, Subgroup.mem_centralizer_iff.mpr fun b hb => hAab b hb a ha⟩
    exact hcen.trans h1
  have hNQ : (CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2.N1 : Subgroup (ModGL Tag.G2 K)) ≤
      Subgroup.centralizer (g2LongRadical K : Set (ModGL .G2 K)) := by
    rw [CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2.N1, Subgroup.closure_le]
    rintro _ ⟨y, rfl⟩
    exact Subgroup.mem_centralizer_iff.mpr fun q hq => ((hcent y).2 q hq).symm
  have hAC : A ⊓ Subgroup.centralizer
      (pCoreOf 2 (oTwoUpper (g2LongRadical K ⊔ g2RankOne K g2ir)) : Set (ModGL .G2 K)) = A :=
    inf_eq_left.mpr fun a ha => Subgroup.centralizer_le hR (hNQ (hAN ha))
  rw [hAC, Subgroup.relIndex_self] at hidx
  omega

end Model

theorem kg1468G24_holds :
    KG1468G24 := by
  intro X _ _ x hX hx hbad
  obtain ⟨-, hU⟩ := hX
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := CFSG.RankThree.Chevalley.exists_mulEquiv_adjointGroup_of_untwisted hU
  have := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2)
    (by rw [← Nat.card_eq_fintype_card, hK])
  have hch : ringChar K = 2 := ringChar.eq K 2
  let ι : X →* ModGL .G2 K := (adjointGroup .G2 K).subtype.comp e.symm.toMonoidHom
  have hι : Function.Injective ι := (adjointGroup .G2 K).subtype_injective.comp e.symm.injective
  have hrange : (⊤ : Subgroup X).map ι = adjointGroup .G2 K := by
    rw [← MonoidHom.range_eq_map]
    ext g
    constructor
    · rintro ⟨y, rfl⟩
      exact (e.symm y).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp [ι]⟩
  have h1 := badA_map hι (badA_top_of_bad hbad)
  rw [hrange] at h1
  have hz : orderOf (e.symm x) = 2 := by rw [MulEquiv.orderOf_eq]; exact hx
  rcases even_G2_involutions_conjugate_to_root_elements K hch (e.symm x) hz with hc | hv
  · obtain ⟨c, hcx⟩ := isConj_iff.mp hc
    have h2 := badA_conj c.2 h1
    have h3 : (c : ModGL .G2 K) * ι x * (c : ModGL .G2 K)⁻¹ = pinnedX .G2 K g2c 1 :=
      congrArg Subtype.val hcx
    rw [h3] at h2
    exact not_badA_c K (by omega) h2
  · obtain ⟨c, hcx⟩ := isConj_iff.mp hv
    have h2 := badA_conj c.2 h1
    have h3 : (c : ModGL .G2 K) * ι x * (c : ModGL .G2 K)⁻¹ = pinnedX .G2 K g2v 1 :=
      congrArg Subtype.val hcx
    rw [h3] at h2
    exact not_badA_v K (by omega) h2

theorem kg1468Ident_holds :
    KG1468Ident :=
  kg1468Ident_of kg1468G24_holds

end CFSG.Quasithin.H13.KG1468
