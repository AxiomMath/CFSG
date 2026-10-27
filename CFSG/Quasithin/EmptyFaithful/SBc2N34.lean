module

public import CFSG.Quasithin.EmptyFaithful.S153H34
public import CFSG.Quasithin.EmptyFaithful.SBc2Borel
public import CFSG.Quasithin.EmptyFaithful.S153D26

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace SBc2

section Abstract

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_borel {A X P : Subgroup G} (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) :
    A ≤ Subgroup.normalizer ((X ⊓ Subgroup.normalizer (P : Set G) : Subgroup G) : Set G) :=
  fun _ ha => Subgroup.inf_normalizer_le_normalizer_inf ⟨hAX ha, Subgroup.le_normalizer (hAP ha)⟩

theorem pCoreOf_borel {X P : Subgroup G} (hP : IsSylowTwoOf P X) :
    pCoreOf 2 (X ⊓ Subgroup.normalizer (P : Set G)) = P := by
  have hPB : IsSylowTwoOf P (X ⊓ Subgroup.normalizer (P : Set G)) :=
    A4.isSylowTwoOf_mono hP (le_inf hP.1 Subgroup.le_normalizer) inf_le_left
  refine le_antisymm (QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hPB) ?_
  exact le_pCoreOf_of_le_normalizer 2 hPB.1 inf_le_right hP.2.1

theorem le_normalizer_sylow_of_borel {A X P : Subgroup G} (hP : IsSylowTwoOf P X)
    (hA : A ≤ Subgroup.normalizer ((X ⊓ Subgroup.normalizer (P : Set G) : Subgroup G) : Set G)) :
    A ≤ Subgroup.normalizer (P : Set G) := by
  intro a ha
  have h := normalizer_le_normalizer_pCoreOf 2 _ (hA ha)
  rwa [pCoreOf_borel hP] at h

theorem mem_normalizer_sup {y : G} {L L' : Subgroup G} (h1 : y ∈ Subgroup.normalizer (L : Set G))
    (h2 : y ∈ Subgroup.normalizer (L' : Set G)) :
    y ∈ Subgroup.normalizer ((L ⊔ L' : Subgroup G) : Set G) := by
  refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
  have hle : L ⊔ L' ≤ (L ⊔ L').comap (MulAut.conj y).toMonoidHom := by
    refine sup_le (fun l hl => ?_) (fun l hl => ?_)
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp h1 l).mp hl)
    · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp h2 l).mp hl)
  exact hle hx

omit [Finite G] in
theorem mem_centralizer_sup {y : G} {L L' : Subgroup G}
    (h1 : y ∈ Subgroup.centralizer (L : Set G)) (h2 : y ∈ Subgroup.centralizer (L' : Set G)) :
    y ∈ Subgroup.centralizer ((L ⊔ L' : Subgroup G) : Set G) := by
  have hle : L ⊔ L' ≤ Subgroup.centralizer ({y} : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (Subgroup.mem_centralizer_iff.mp h1 x hx).symm
    · refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      rw [Set.mem_singleton_iff] at hz
      subst hz
      exact (Subgroup.mem_centralizer_iff.mp h2 x hx).symm
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  exact (Subgroup.mem_centralizer_iff.mp (hle hx) y (Set.mem_singleton y)).symm

omit [Finite G] in
theorem centerOf_map_conj (s : G) (L : Subgroup G) :
    centerOf (L.map (MulAut.conj s).toMonoidHom) =
      (centerOf L).map (MulAut.conj s).toMonoidHom := by
  ext x
  rw [Subgroup.mem_map]
  unfold centerOf
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, SetLike.mem_coe]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hc⟩
    refine ⟨y, ⟨hy, fun g hg => ?_⟩, rfl⟩
    have := hc _ (Subgroup.mem_map_of_mem _ hg)
    exact (MulAut.conj s).injective (by simpa using this)
  · rintro ⟨y, ⟨hy, hc⟩, rfl⟩
    refine ⟨Subgroup.mem_map_of_mem _ hy, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    simpa using congrArg (MulAut.conj s) (hc g hg)

omit [Finite G] in
theorem conj_props (s : G) {L : Subgroup G} (hq : CFSG.IsQuasisimple ↥L) (hZ : centerOf L = pCoreOf 2 L)
    (hsz : ∃ e : ℕ, IsSz e (↥L ⧸ Subgroup.center ↥L)) :
    CFSG.IsQuasisimple ↥(L.map (MulAut.conj s).toMonoidHom) ∧
      centerOf (L.map (MulAut.conj s).toMonoidHom) = pCoreOf 2 (L.map (MulAut.conj s).toMonoidHom) ∧
      ∃ e : ℕ, IsSz e (↥(L.map (MulAut.conj s).toMonoidHom) ⧸
        Subgroup.center ↥(L.map (MulAut.conj s).toMonoidHom)) := by
  let e : ↥L ≃* ↥(L.map (MulAut.conj s).toMonoidHom) := MulEquiv.subgroupMap (MulAut.conj s) L
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq, ?_, ?_⟩
  · rw [centerOf_map_conj, pCoreOf_map_mulEquiv, hZ]
  · obtain ⟨f, hf⟩ := hsz
    have hcen : (Subgroup.center ↥L).map (e : ↥L →* ↥(L.map (MulAut.conj s).toMonoidHom)) =
        Subgroup.center ↥(L.map (MulAut.conj s).toMonoidHom) := Subgroup.map_center_eq e
    exact ⟨f, IsSz.of_mulEquiv (QuotientGroup.congr _ _ e hcen) hf⟩

theorem borel_single {S I L Y : Subgroup G}
    (hSyl : IsSylowTwoOf S I) (hLI : L ≤ I) (hSL : S ≤ Subgroup.normalizer (L : Set G))
    (hYL : Y ≤ Subgroup.normalizer (L : Set G)) (hA : Group.IsSolvable ↥(Y ⊔ S))
    (hq : CFSG.IsQuasisimple ↥L) (hZ : centerOf L = pCoreOf 2 L)
    (hsz : ∃ e : ℕ, IsSz e (↥L ⧸ Subgroup.center ↥L)) :
    ∃ B : Subgroup G, B ≤ L ∧ (∃ P : Subgroup G, IsSylowTwoOf P L ∧ B = L ⊓ Subgroup.normalizer (P : Set G)) ∧
      Y ⊔ S ≤ Subgroup.normalizer (B : Set G) ∧ CharTwo B ∧
      ∀ X : Subgroup G, X ≤ L → S ≤ Subgroup.normalizer (X : Set G) → B ≤ X → X ≠ L → X = B := by
  have hP : IsSylowTwoOf (S ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
      (le_inf hLI Subgroup.le_normalizer) inf_le_right
  have hSz : SzLift L (S ⊓ L) := szLift_of_isSz hq hZ hsz hP
  have hAL : Y ⊔ S ≤ Subgroup.normalizer (L : Set G) := sup_le hYL hSL
  have hAP : Y ⊔ S ≤ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G) :=
    sup_le_normalizer_of_solv hP hAL hA (inf_le_left.trans le_sup_right) hSz.solv
  refine ⟨L ⊓ Subgroup.normalizer ((S ⊓ L : Subgroup G) : Set G), inf_le_left, ⟨S ⊓ L, hP, rfl⟩,
    le_normalizer_borel hAL hAP, charTwo_borel hP hSz, ?_⟩
  intro X hXL _ hBX hne
  exact (hSz.maximal X hXL hBX).resolve_right hne

theorem borel_prod_case {S I L L' Y : Subgroup G} {s : G}
    (hSyl : IsSylowTwoOf S I) (hL₀I : L ⊔ L' ≤ I) (hSL₀ : S ≤ Subgroup.normalizer ((L ⊔ L' : Subgroup G) : Set G))
    (hc : ⁅L, L'⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 L') (hs : s ∈ S)
    (hLL' : L' = L.map (MulAut.conj s).toMonoidHom)
    (hYL : Y ≤ Subgroup.normalizer (L : Set G)) (hYL' : Y ≤ Subgroup.normalizer (L' : Set G))
    (hA : Group.IsSolvable ↥(Y ⊔ S))
    (hq : CFSG.IsQuasisimple ↥L) (hZ : centerOf L = pCoreOf 2 L)
    (hsz : ∃ e : ℕ, IsSz e (↥L ⧸ Subgroup.center ↥L)) :
    ∃ B : Subgroup G, B ≤ L ⊔ L' ∧
      (∃ P : Subgroup G, IsSylowTwoOf P (L ⊔ L') ∧ B = (L ⊔ L') ⊓ Subgroup.normalizer (P : Set G)) ∧
      Y ⊔ S ≤ Subgroup.normalizer (B : Set G) ∧ CharTwo B ∧
      ∀ X : Subgroup G, X ≤ L ⊔ L' → S ≤ Subgroup.normalizer (X : Set G) → B ≤ X → X ≠ L ⊔ L' → X = B := by
  have hLN := le_normalizer_of_commutator_le hc
  have hP : IsSylowTwoOf (S ⊓ (L ⊔ L')) (L ⊔ L') :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL₀) inf_le_left)
      (le_inf hL₀I Subgroup.le_normalizer) inf_le_right
  obtain ⟨hq', hZ', hsz'⟩ := hLL' ▸ conj_props s hq hZ hsz
  have hSz : SzLift L (S ⊓ (L ⊔ L') ⊓ L) := szLift_of_isSz hq hZ hsz (sylow_inf_left hc hP)
  have hSz' : SzLift L' (S ⊓ (L ⊔ L') ⊓ L') := szLift_of_isSz hq' hZ' hsz' (sylow_inf_right hc hP)
  have hPS : S ⊓ (L ⊔ L') ≤ S := inf_le_left
  have hYL₀ : Y ≤ Subgroup.normalizer ((L ⊔ L' : Subgroup G) : Set G) := fun y hy =>
    mem_normalizer_sup (hYL hy) (hYL' hy)
  have hPL : S ⊓ (L ⊔ L') ≤ Subgroup.normalizer (L : Set G) := inf_le_right.trans
    (sup_le Subgroup.le_normalizer hLN.2)
  have hPL' : S ⊓ (L ⊔ L') ≤ Subgroup.normalizer (L' : Set G) := inf_le_right.trans
    (sup_le hLN.1 Subgroup.le_normalizer)
  have hYsolv : Group.IsSolvable ↥(Y ⊔ (S ⊓ (L ⊔ L'))) :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (sup_le_sup_left hPS Y))
      (Subgroup.inclusion_injective (sup_le_sup_left hPS Y))
  have hYP : Y ⊔ (S ⊓ (L ⊔ L')) ≤ Subgroup.normalizer ((S ⊓ (L ⊔ L') : Subgroup G) : Set G) :=
    prod_sup_le_normalizer hc hP hSz hSz' (sup_le hYL hPL) (sup_le hYL' hPL') hYsolv le_sup_right
  have hSP : S ≤ Subgroup.normalizer ((S ⊓ (L ⊔ L') : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hSL₀ hx⟩
  refine ⟨(L ⊔ L') ⊓ Subgroup.normalizer ((S ⊓ (L ⊔ L') : Subgroup G) : Set G), inf_le_left,
    ⟨S ⊓ (L ⊔ L'), hP, rfl⟩, le_normalizer_borel (sup_le hYL₀ hSL₀) (sup_le (le_sup_left.trans hYP) hSP),
    prod_charTwo hc hP hSz hSz' hZ hZ', ?_⟩
  intro X hX hSX hBX hne
  exact prod_maximal hc hP hSz hSz' hLL' hX (hSX hs) hBX hne

theorem pow_three_eq_one_of_odd {T Mc M : Subgroup G} (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    {y : G} (hy : y ∈ Y153 Mc M) (hodd : Odd (orderOf y)) : y ^ 3 = 1 := by
  have h1 := h.pow_three_mem_pCoreOf_Y153 h113 hy
  obtain ⟨k, hk⟩ := (pCoreOf_isPGroup 2 (Y153 Mc M) : IsPGroup 2 ↥(pCoreOf 2 (Y153 Mc M))) ⟨y ^ 3, h1⟩
  have hk' : (y ^ 3) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hord : orderOf (y ^ 3) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hdvd : orderOf (y ^ 3) ∣ orderOf y := orderOf_pow_dvd 3
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hord
  have hi0 : i = 0 := by
    by_contra hne
    have h2 : 2 ∣ orderOf (y ^ 3) := by rw [hi]; exact dvd_pow_self 2 hne
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hdvd))
  rw [hi0, pow_zero, orderOf_eq_one_iff] at hi
  exact hi

theorem isPGroup_two_of_le_Y153 {T Mc M : Subgroup G} (h113 : StageLemma14113) (h : Hyp153 G T Mc M)
    {K : Subgroup G} (hK : K ≤ Y153 Mc M) (h3 : ¬ 3 ∣ Nat.card ↥K) : IsPGroup 2 ↥K := by
  have hpr : ∀ p : ℕ, p.Prime → p ∣ Nat.card ↥K → p = 2 := by
    intro p hp hpd
    by_contra hp2
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) p hpd
    have hzG : orderOf (z : G) = p := by rw [Subgroup.orderOf_coe, hz]
    have hodd : Odd (orderOf (z : G)) := by rw [hzG]; exact hp.odd_of_ne_two hp2
    have hz3 := pow_three_eq_one_of_odd h113 h (hK z.2) hodd
    have h3dvd : p ∣ 3 := hzG ▸ orderOf_dvd_of_pow_eq_one hz3
    have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3dvd
    exact h3 (hp3 ▸ hpd)
  have hpos : Nat.card ↥K ≠ 0 := Nat.card_pos.ne'
  exact IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd hpos fun hd hdd => hpr _ hd hdd)


theorem centralizes_of_borel {Y L P : Subgroup G} (hP : IsSylowTwoOf P L) (hSz : SzLift L P)
    (hY2 : ∀ K : Subgroup G, K ≤ Y → ¬ 3 ∣ Nat.card ↥K → IsPGroup 2 ↥K)
    (hBY : L ⊓ Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Y : Set G))
    (hYL : Y ≤ Subgroup.normalizer (L : Set G)) (hYP : Y ≤ Subgroup.normalizer (P : Set G))
    {y : G} (hy : y ∈ Y) (hy3 : y ^ 3 = 1) : y ∈ Subgroup.centralizer (L : Set G) := by
  set B : Subgroup G := L ⊓ Subgroup.normalizer (P : Set G) with hB
  have hyL : y ∈ Subgroup.normalizer (L : Set G) := hYL hy
  have hyN : y ∈ Subgroup.normalizer (P : Set G) := hYP hy
  refine hSz.yLemma y hyL hy3 fun b hb => ?_
  have hb' : y * b⁻¹ * y⁻¹ ∈ B := by
    refine ⟨(Subgroup.mem_normalizer_iff.mp hyL _).mp (L.inv_mem hb.1), ?_⟩
    exact (Subgroup.normalizer (P : Set G)).mul_mem ((Subgroup.normalizer (P : Set G)).mul_mem hyN
      ((Subgroup.normalizer (P : Set G)).inv_mem hb.2)) ((Subgroup.normalizer (P : Set G)).inv_mem hyN)
  have hwB : b * y * b⁻¹ * y⁻¹ ∈ B := by
    have := B.mul_mem hb hb'
    simpa [mul_assoc] using this
  have hwY : b * y * b⁻¹ * y⁻¹ ∈ Y := by
    have hbN : b ∈ Subgroup.normalizer (Y : Set G) := hBY hb
    exact Y.mul_mem ((Subgroup.mem_normalizer_iff.mp hbN y).mp hy) (Y.inv_mem hy)
  have h3 : ¬ 3 ∣ Nat.card ↥(B ⊓ Y) := fun hd =>
    hSz.card3 (hd.trans (Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_left)))
  have hK2 : IsPGroup 2 ↥(B ⊓ Y) := hY2 _ inf_le_right h3
  have hPB : IsSylowTwoOf P B := A4.isSylowTwoOf_mono hP (le_inf hP.1 Subgroup.le_normalizer) inf_le_left
  exact le_of_normal_sylow hPB inf_le_right inf_le_left hK2 ⟨hwB, hwY⟩

theorem centralizer_single {Y L B : Subgroup G}
    (hB : ∃ P : Subgroup G, IsSylowTwoOf P L ∧ B = L ⊓ Subgroup.normalizer (P : Set G))
    (hYB : Y ≤ Subgroup.normalizer (B : Set G)) (hBY : B ≤ Subgroup.normalizer (Y : Set G))
    (hYL : Y ≤ Subgroup.normalizer (L : Set G))
    (hY2 : ∀ K : Subgroup G, K ≤ Y → ¬ 3 ∣ Nat.card ↥K → IsPGroup 2 ↥K)
    (hq : CFSG.IsQuasisimple ↥L) (hZ : centerOf L = pCoreOf 2 L)
    (hsz : ∃ e : ℕ, IsSz e (↥L ⧸ Subgroup.center ↥L)) {y : G} (hy : y ∈ Y) (hy3 : y ^ 3 = 1) :
    y ∈ Subgroup.centralizer (L : Set G) := by
  obtain ⟨P, hP, rfl⟩ := hB
  exact centralizes_of_borel hP (szLift_of_isSz hq hZ hsz hP) hY2 hBY hYL
    (le_normalizer_sylow_of_borel hP hYB) hy hy3

theorem centralizer_prod {Y L L' B P : Subgroup G} {s : G}
    (hc : ⁅L, L'⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 L') (hLL' : L' = L.map (MulAut.conj s).toMonoidHom)
    (hP : IsSylowTwoOf P (L ⊔ L')) (hB : B = (L ⊔ L') ⊓ Subgroup.normalizer (P : Set G))
    (hYB : Y ≤ Subgroup.normalizer (B : Set G)) (hBY : B ≤ Subgroup.normalizer (Y : Set G))
    (hYL : Y ≤ Subgroup.normalizer (L : Set G)) (hYL' : Y ≤ Subgroup.normalizer (L' : Set G))
    (hY2 : ∀ K : Subgroup G, K ≤ Y → ¬ 3 ∣ Nat.card ↥K → IsPGroup 2 ↥K)
    (hq : CFSG.IsQuasisimple ↥L) (hZ : centerOf L = pCoreOf 2 L)
    (hsz : ∃ e : ℕ, IsSz e (↥L ⧸ Subgroup.center ↥L)) {y : G} (hy : y ∈ Y) (hy3 : y ^ 3 = 1) :
    y ∈ Subgroup.centralizer ((L ⊔ L' : Subgroup G) : Set G) := by
  subst hB
  obtain ⟨hq', hZ', hsz'⟩ := hLL' ▸ conj_props s hq hZ hsz
  have hYP : Y ≤ Subgroup.normalizer (P : Set G) := le_normalizer_sylow_of_borel hP hYB
  have hP₁ := sylow_inf_left hc hP
  have hP₂ := sylow_inf_right hc hP
  have h1 : y ∈ Subgroup.centralizer (L : Set G) :=
    centralizes_of_borel hP₁ (szLift_of_isSz hq hZ hsz hP₁) hY2
      ((inf_normalizer_le_borel hc hP).trans hBY) hYL
      (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨hYP hx, hYL hx⟩) hy hy3
  have h2 : y ∈ Subgroup.centralizer (L' : Set G) :=
    centralizes_of_borel hP₂ (szLift_of_isSz hq' hZ' hsz' hP₂) hY2
      ((inf_normalizer_le_borel' hc hP).trans hBY) hYL'
      (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf ⟨hYP hx, hYL' hx⟩) hy hy3
  exact mem_centralizer_sup h1 h2

end Abstract

section Context

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem Yp_le_of_odd (hh : Hyp15310 G T Mc M V₁ V₂ Yp t) {C : Subgroup G}
    (hC : ∀ y ∈ Yp, Odd (orderOf y) → y ∈ C) : Yp ≤ C := by
  calc Yp = oTwoUpper Yp := hh.oTwoUpper_eq.symm
    _ ≤ C := by
      rw [oTwoUpper, Subgroup.closure_le]
      rintro x ⟨hx, hodd⟩
      exact hC x hx hodd

omit [Finite G] in
theorem conjClosure_eq_of_normalizes {S L : Subgroup G} (hS : S ≤ Subgroup.normalizer (L : Set G)) :
    conjClosure L S = L :=
  le_antisymm (conjClosure_le fun _ hg _ hl => (Subgroup.mem_normalizer_iff.mp (hS hg) _).mp hl)
    (le_conjClosure _ _)

theorem exists_pair (h37 : A37ForSQTK) (h38 : A38ForSQTK) (c : CtxComp T Mc M V₁ V₂ Yp I t)
    (hL : L ∈ cComp I) (hS : ¬ Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G)) :
    ∃ s ∈ Sgp153 T V₁, L ≠ L.map (MulAut.conj s).toMonoidHom ∧
      L.map (MulAut.conj s).toMonoidHom ∈ cComp I ∧
      conjClosure L (Sgp153 T V₁) = L ⊔ L.map (MulAut.conj s).toMonoidHom := by
  classical
  have hq := c.hyp.hyp.qtfe
  have hLle : L ≤ I := le_of_mem_cComp hL
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  obtain ⟨s, hs, hsn⟩ := Set.not_subset.mp hS
  have hL''mem : L.map (MulAut.conj s).toMonoidHom ∈ cComp I := map_conj_mem_cComp hL (hSI hs)
  have hLne : L ≠ L.map (MulAut.conj s).toMonoidHom := fun h => hsn (A38.map_conj_eq_iff.mp h.symm)
  have hL''mem' : L.map (MulAut.conj s).toMonoidHom ∈ conjSubgroupsBy I L := ⟨s, hSI hs, rfl⟩
  have hLmem' : L ∈ conjSubgroupsBy I L := ⟨1, I.one_mem, by ext x; simp⟩
  rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38 c.inH.1.2 hL with hn | ⟨hcard, -⟩
  · exact absurd (((Subgroup.normal_subgroupOf_iff_le_normalizer hLle).mp hn) (hSI hs)) hsn
  obtain ⟨x, y, hxy, hset⟩ := Set.ncard_eq_two.mp hcard
  have hmem : ∀ K ∈ conjSubgroupsBy I L, K = L ∨ K = L.map (MulAut.conj s).toMonoidHom := by
    intro K hK
    have hK' := hK
    have h1 := hLmem'
    have h2 := hL''mem'
    rw [hset] at hK' h1 h2
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hK' h1 h2
    rcases hK' with rfl | rfl <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      first | exact Or.inl h1.symm | exact Or.inr h2.symm | (exfalso; exact hLne (h1.trans h2.symm))
  refine ⟨s, hs, hLne, hL''mem, le_antisymm (conjClosure_le fun g hg l hl => ?_)
    (sup_le (le_conjClosure _ _) ?_)⟩
  · have hK : L.map (MulAut.conj g).toMonoidHom ∈ conjSubgroupsBy I L := ⟨g, hSI hg, rfl⟩
    have hgl : g * l * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := ⟨l, hl, rfl⟩
    rcases hmem _ hK with h | h
    · rw [h] at hgl
      exact Subgroup.mem_sup_left hgl
    · rw [h] at hgl
      exact Subgroup.mem_sup_right hgl
  · rintro _ ⟨l, hl, rfl⟩
    simpa [MulAut.conj_apply] using mem_conjClosure hs hl

theorem input34Borel_holds
    (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK) : Input34Borel := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hL hsz
  have hq := c.hyp.hyp.qtfe
  have hLI : L ∈ cComp I := hL.mem
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hYL : Yp ≤ Subgroup.normalizer (L : Set G) := S153D.Yp_le_normalizer h37 h38 c.hyp c.inH hLI
  have hA : Group.IsSolvable ↥(Yp ⊔ Sgp153 T V₁) := S153D.isSolvable_Yp_sup' h113 c.hyp
  by_cases hS : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G)
  · rw [conjClosure_eq_of_normalizes hS]
    exact borel_single c.facts.sylow hLle hS hYL hA hL.quasisimple hL.center_eq hsz
  · obtain ⟨s, hs, hne, hL'I, hcc⟩ := exists_pair h37 h38 c hLI hS
    rw [hcc]
    have hc := (lemma_1_2_1_two hq.qtke hq.simple hq.nonabelian h37 c.inH.1.2 hLI hL'I hne).1
    have hYL' : Yp ≤ Subgroup.normalizer ((L.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G) :=
      S153D.Yp_le_normalizer h37 h38 c.hyp c.inH hL'I
    have hSL₀ : Sgp153 T V₁ ≤ Subgroup.normalizer
        ((L ⊔ L.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G) := by
      rw [← hcc]
      exact le_normalizer_conjClosure L _
    exact borel_prod_case c.facts.sylow (sup_le hLle (le_of_mem_cComp hL'I)) hSL₀ hc hs rfl hYL hYL' hA
      hL.quasisimple hL.center_eq hsz

theorem input34Centralizer_holds
    (h113 : StageLemma14113) (h37 : A37ForSQTK) (h38 : A38ForSQTK) : Input34Centralizer := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hL hsz B hB hBn hBM
  have hq := c.hyp.hyp.qtfe
  have hLI : L ∈ cComp I := hL.mem
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hL₀I := S153H.conjClosure_le_I (T := T) (V₁ := V₁) hSI hLle
  have hYL : Yp ≤ Subgroup.normalizer (L : Set G) := S153D.Yp_le_normalizer h37 h38 c.hyp c.inH hLI
  have hY2 : ∀ K : Subgroup G, K ≤ Yp → ¬ 3 ∣ Nat.card ↥K → IsPGroup 2 ↥K := fun K hK h3 =>
    isPGroup_two_of_le_Y153 h113 c.hyp.hyp (hK.trans c.hyp.Yp_le_Y153) h3
  have hBY : B ≤ Subgroup.normalizer (Yp : Set G) := by
    intro b hb
    rw [hBM] at hb
    have hbMI : b ∈ M ⊓ I := ⟨hb.1, hL₀I hb.2⟩
    rw [← c.facts.norm_eq] at hbMI
    exact hbMI.2
  have hYB : Yp ≤ Subgroup.normalizer (B : Set G) := le_sup_left.trans hBn
  refine Yp_le_of_odd c.hyp fun y hy hodd => ?_
  have hy3 : y ^ 3 = 1 := pow_three_eq_one_of_odd h113 c.hyp.hyp (c.hyp.Yp_le_Y153 hy) hodd
  by_cases hS : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G)
  · rw [conjClosure_eq_of_normalizes hS] at hB ⊢
    exact centralizer_single hB hYB hBY hYL hY2 hL.quasisimple hL.center_eq hsz hy hy3
  · obtain ⟨s, hs, hne, hL'I, hcc⟩ := exists_pair h37 h38 c hLI hS
    rw [hcc] at hB ⊢
    have hc := (lemma_1_2_1_two hq.qtke hq.simple hq.nonabelian h37 c.inH.1.2 hLI hL'I hne).1
    have hYL' : Yp ≤ Subgroup.normalizer ((L.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G) :=
      S153D.Yp_le_normalizer h37 h38 c.hyp c.inH hL'I
    obtain ⟨P, hP, hBP⟩ := hB
    exact centralizer_prod hc rfl hP hBP hYB hBY hYL hYL' hY2 hL.quasisimple hL.center_eq hsz hy hy3

end Context

end SBc2

end CFSG.Quasithin
