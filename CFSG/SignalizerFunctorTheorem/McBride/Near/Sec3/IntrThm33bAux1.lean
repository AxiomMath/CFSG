module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33aAux3
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.FixedPoint
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.KGroup
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec3.IntrThm33aAux2

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33b

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv Thm33a

variable {Γ : Type u} [Group Γ] [Finite Γ] {p : ℕ} {A X Y X₁ X₂ N : Subgroup Γ}

theorem inf_le_of_inf_dsub_le
    (h : NearAsolvAction p A X) (hP : (X₁, X₂) ∈ iPairsY A X Y)
    (hX : Admits X N) (hA : Admits A N) (hN : N ⊓ cenIn X (A : Set Γ) ≤ Y) :
    N ⊓ X₁ ≤ X₂ := by
  by_contra hcon
  have hX₁X : X₁ ≤ X := pair_le hP
  have hHN : Admits (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) N :=
    sup_le (sup_le (hX₁X.trans hX) (inf_le_left.trans hX)) hA
  have hTadm : Admits (X₁ ⊔ cenIn X (A : Set Γ) ⊔ A) (N ⊓ X₁) := hHN.inf (pair_admits_H hP)
  rcases chief_dichotomy (pair_chief hP) hTadm inf_le_right with h1 | h1
  · exact hcon h1
  · refine not_isSolvable_qimg_pair hP ?_
    have hX₁n : X₁ ≤ AChief.nrm X₂ := pair_le_nrm hP
    have hA₁ : A ≤ Subgroup.normalizer (X₁ : Set Γ) := le_sup_right.trans (pair_admits_left hP)
    have hAX₂ : A ≤ AChief.nrm X₂ := le_sup_right.trans (pair_admits_H₂ hP)
    have hAT : A ≤ Subgroup.normalizer ((N ⊓ X₁ : Subgroup Γ) : Set Γ) :=
      (show Admits A N from hA).inf hA₁
    have hTn : N ⊓ X₁ ≤ AChief.nrm X₂ := inf_le_right.trans hX₁n
    have hQ : AChief.qimg X₂ X₁ = AChief.qimg X₂ (N ⊓ X₁) :=
      qimg_eq_of_sup_eq hP inf_le_right h1
    have hcop : Nat.Coprime p (Nat.card ↥(N ⊓ X₁)) :=
      h.nearPSolvable.1.coprime_dvd_right (Subgroup.card_dvd_of_le (inf_le_right.trans hX₁X))
    have hkey := AChief.qimg_inf_centralizer (N := X₂) h.prime h.elemAbelian hAT hAX₂ hTn hcop
    have hle : (N ⊓ X₁) ⊓ Subgroup.centralizer (A : Set Γ) ≤ X₂ := by
      intro x hx
      have hxD : x ∈ N ⊓ cenIn X (A : Set Γ) :=
        Subgroup.mem_inf.mpr ⟨hx.1.1, Subgroup.mem_inf.mpr ⟨hX₁X hx.1.2, hx.2⟩⟩
      exact pair_Y_le₂ hP (hN hxD)
    have hfix : AChief.qimg X₂ X₁ ⊓ Subgroup.centralizer
        ((AChief.qimg X₂ A : Subgroup (AChief.QG X₂)) : Set (AChief.QG X₂)) = ⊥ := by
      rw [hQ, ← hkey]
      have := SolQuot.qimg_mono (R := X₂) hle
      rwa [SolQuot.qimg_self, le_bot_iff] at this
    have hX₁near : NearAsolvAction p A X₁ := Thm211.nearAsolvAction_of_le h hX₁X hA₁
    have hQnear := (Thm211.nearAsolvAction_qimg hX₁near hX₁n hAX₂).nearPSolvable
    exact isSolvable_of_inf_centralizer_eq_bot h.prime (AChief.isElemAbelian_qimg h.elemAbelian)
      (AChief.qimg_le_normalizer hA₁) (signalizerMcBrideHypothesisB_of_nearPSolvable h.prime hQnear)
      hfix

omit [Finite Γ] in
theorem admits_iff_qimg {Q P : Subgroup Γ} (hQ : Q ≤ AChief.nrm N) (hP : P ≤ AChief.nrm N)
    (hNP : N ≤ P) : Admits Q P ↔ Admits (AChief.qimg N Q) (AChief.qimg N P) :=
  (SolQuot.qimg_le_normalizer_iff hP (inf_le_right.trans hNP) le_rfl hQ).symm

omit [Finite Γ] in
theorem qpre_mem_iPairsY (h : NearAsolvAction p A X) (hNX : N ≤ X) (hX : X ≤ AChief.nrm N)
    (hA : A ≤ AChief.nrm N) (hYD : Y ≤ cenIn X (A : Set Γ))
    (hND : N ⊓ cenIn X (A : Set Γ) ≤ Y) {M₁ M₂ : Subgroup (AChief.QG N)}
    (hM : (M₁, M₂) ∈ iPairsY (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y)) :
    (SolQuot.qpre N M₁, SolQuot.qpre N M₂) ∈ iPairsY A X Y := by
  obtain ⟨⟨⟨hM₁X, hM₁adm⟩, ⟨hM₂X, hM₂adm⟩, hch, hsec⟩, hinf⟩ := hM
  have hDX : cenIn X (A : Set Γ) ≤ X := inf_le_left
  have hDn : cenIn X (A : Set Γ) ≤ AChief.nrm N := hDX.trans hX
  have hYn : Y ≤ AChief.nrm N := hYD.trans hDn
  have hcen : cenIn (AChief.qimg N X)
      ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N)) =
        AChief.qimg N (cenIn X (A : Set Γ)) := cenIn_qimg h hX hA
  set P₁ := SolQuot.qpre N M₁ with hP₁
  set P₂ := SolQuot.qpre N M₂ with hP₂
  have hP₁n : P₁ ≤ AChief.nrm N := SolQuot.qpre_le_nrm M₁
  have hP₂n : P₂ ≤ AChief.nrm N := SolQuot.qpre_le_nrm M₂
  have hNP₁ : N ≤ P₁ := SolQuot.le_qpre M₁
  have hNP₂ : N ≤ P₂ := SolQuot.le_qpre M₂
  have hP₁X : P₁ ≤ X := by
    refine (SolQuot.qpre_mono hM₁X).trans ?_
    rw [SolQuot.qpre_qimg hX, sup_eq_left.mpr hNX]
  have hP₂X : P₂ ≤ X := by
    refine (SolQuot.qpre_mono hM₂X).trans ?_
    rw [SolQuot.qpre_qimg hX, sup_eq_left.mpr hNX]
  have hM₂M₁ : M₂ ≤ M₁ := hch.2.2.1.le
  have hP₂P₁ : P₂ ≤ P₁ := SolQuot.qpre_mono hM₂M₁
  have hDA : cenIn X (A : Set Γ) ⊔ A ≤ AChief.nrm N := sup_le hDn hA
  have hqDA : AChief.qimg N (cenIn X (A : Set Γ) ⊔ A) =
      cenIn (AChief.qimg N X)
        ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N)) ⊔ AChief.qimg N A := by
    rw [SolQuot.qimg_sup hDn hA, hcen]
  have hdaP : ∀ {M : Subgroup (AChief.QG N)},
      Admits (cenIn (AChief.qimg N X)
        ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N)) ⊔ AChief.qimg N A) M →
        Admits (cenIn X (A : Set Γ) ⊔ A) (SolQuot.qpre N M) := by
    intro M hMadm
    rw [admits_iff_qimg hDA (SolQuot.qpre_le_nrm M) (SolQuot.le_qpre M), SolQuot.qimg_qpre, hqDA]
    exact hMadm
  have hH₁n : P₁ ⊔ cenIn X (A : Set Γ) ⊔ A ≤ AChief.nrm N := sup_le (sup_le hP₁n hDn) hA
  have hqH : AChief.qimg N (P₁ ⊔ cenIn X (A : Set Γ) ⊔ A) =
      M₁ ⊔ cenIn (AChief.qimg N X)
        ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N)) ⊔ AChief.qimg N A := by
    rw [SolQuot.qimg_sup (sup_le hP₁n hDn) hA, SolQuot.qimg_sup hP₁n hDn, SolQuot.qimg_qpre, hcen]
  have hH₁adm : ∀ {P : Subgroup Γ}, N ≤ P → P ≤ AChief.nrm N →
      Admits (AChief.qimg N (P₁ ⊔ cenIn X (A : Set Γ) ⊔ A)) (AChief.qimg N P) →
        Admits (P₁ ⊔ cenIn X (A : Set Γ) ⊔ A) P := fun hNP hP hq =>
    (admits_iff_qimg hH₁n hP hNP).mpr hq
  refine ⟨⟨⟨hP₁X, hdaP hM₁adm⟩, ⟨hP₂X, hdaP hM₂adm⟩, ?_, ?_⟩, ?_⟩
  ·
    obtain ⟨⟨hM₂H, hHM₂⟩, ⟨hM₁H, hHM₁⟩, hlt, hmin⟩ := hch
    refine ⟨⟨hP₂P₁.trans (le_sup_left.trans le_sup_left), ?_⟩,
      ⟨le_sup_left.trans le_sup_left, ?_⟩, ?_, ?_⟩
    · refine hH₁adm hNP₂ hP₂n ?_
      rw [hqH, SolQuot.qimg_qpre]
      exact hHM₂
    · refine hH₁adm hNP₁ hP₁n ?_
      rw [hqH, SolQuot.qimg_qpre]
      exact hHM₁
    · refine lt_of_le_of_ne hP₂P₁ fun heq => hlt.ne ?_
      rw [← SolQuot.qimg_qpre M₂, ← SolQuot.qimg_qpre M₁]
      exact congrArg (AChief.qimg N) heq
    · intro K hK hP₂K hKP₁
      have hKX : K ≤ X := hKP₁.trans hP₁X
      have hKn : K ≤ AChief.nrm N := hKX.trans hX
      have hNK : N ≤ K := hNP₂.trans hP₂K
      have hKadm : Admits (AChief.qimg N (P₁ ⊔ cenIn X (A : Set Γ) ⊔ A)) (AChief.qimg N K) :=
        (admits_iff_qimg hH₁n hKn hNK).mp hK.2
      rw [hqH] at hKadm
      have hqK : IsNormalIn (AChief.qimg N K)
          (M₁ ⊔ cenIn (AChief.qimg N X)
            ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N)) ⊔
              AChief.qimg N A) := by
        refine ⟨?_, hKadm⟩
        refine (SolQuot.qimg_mono hKP₁).trans ?_
        rw [SolQuot.qimg_qpre]
        exact le_sup_left.trans le_sup_left
      have hlow : M₂ ≤ AChief.qimg N K := by
        have := SolQuot.qimg_mono (R := N) hP₂K
        rwa [SolQuot.qimg_qpre] at this
      have hup : AChief.qimg N K ≤ M₁ := by
        have := SolQuot.qimg_mono (R := N) hKP₁
        rwa [SolQuot.qimg_qpre] at this
      have hKeq : K = SolQuot.qpre N (AChief.qimg N K) := by
        rw [SolQuot.qpre_qimg hKn, sup_eq_left.mpr hNK]
      rcases hmin (AChief.qimg N K) hqK hlow hup with h2 | h2
      · left
        rw [hKeq, h2]
      · right
        rw [hKeq, h2]
  ·
    apply le_antisymm
    · intro g hg
      obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.mp hg
      obtain ⟨hgP₂, hgP₁, hgc⟩ := mem_sectionCentralizer_iff.mp hg2
      have hgn : g ∈ AChief.nrm N := by
        have : g ∈ P₁ ⊔ cenIn X (A : Set Γ) := hg1
        exact (sup_le hP₁n hDn) this
      have hqmem : AChief.qmap N ⟨g, hgn⟩ ∈ secCenIn (M₁ ⊔ cenIn (AChief.qimg N X)
          ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N))) M₁ M₂ := by
        refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
        · have : AChief.qimg N (P₁ ⊔ cenIn X (A : Set Γ)) =
              M₁ ⊔ cenIn (AChief.qimg N X)
                ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N)) := by
            rw [SolQuot.qimg_sup hP₁n hDn, SolQuot.qimg_qpre, hcen]
          rw [← this]
          exact (AChief.mem_qimg_iff N _ _).mpr ⟨⟨g, hgn⟩, hg1, rfl⟩
        · rw [mem_sectionCentralizer_iff]
          refine ⟨?_, ?_, fun z hz => ?_⟩
          · have := (SolQuot.mem_normalizer_qimg_iff (R := N) (Y := AChief.nrm N) hP₂n
              (inf_le_right.trans hNP₂) le_rfl hgn).mpr hgP₂
            rwa [SolQuot.qimg_qpre] at this
          · have := (SolQuot.mem_normalizer_qimg_iff (R := N) (Y := AChief.nrm N) hP₁n
              (inf_le_right.trans hNP₁) le_rfl hgn).mpr hgP₁
            rwa [SolQuot.qimg_qpre] at this
          · rw [← SolQuot.qimg_qpre M₁] at hz
            obtain ⟨y, hy, rfl⟩ := (AChief.mem_qimg_iff N P₁ z).mp hz
            rw [← map_commutatorElement]
            have hc := hgc (y : Γ) hy
            rw [← SolQuot.qimg_qpre M₂]
            exact (AChief.mem_qimg_iff N P₂ _).mpr ⟨⁅(⟨g, hgn⟩ : ↥(AChief.nrm N)), y⁆, hc, rfl⟩
      rw [hsec] at hqmem
      exact (SolQuot.mem_qpre_iff.mpr ⟨hgn, hqmem⟩)
    · intro x hx
      refine Subgroup.mem_inf.mpr ⟨(hP₂P₁.trans le_sup_left) hx, ?_⟩
      rw [mem_sectionCentralizer_iff]
      refine ⟨Subgroup.le_normalizer hx, Subgroup.le_normalizer (hP₂P₁ hx), fun y hy => ?_⟩
      have hyn : y ∈ Subgroup.normalizer (P₂ : Set Γ) := by
        have hH : P₁ ⊔ cenIn X (A : Set Γ) ⊔ A ≤ Subgroup.normalizer (P₂ : Set Γ) := by
          refine hH₁adm hNP₂ hP₂n ?_
          rw [hqH, SolQuot.qimg_qpre]
          exact hch.1.2
        exact hH ((le_sup_left.trans le_sup_left :
          P₁ ≤ P₁ ⊔ cenIn X (A : Set Γ) ⊔ A) hy)
      rw [commutatorElement_def]
      have h1 : y * x⁻¹ * y⁻¹ ∈ P₂ := (Subgroup.mem_normalizer_iff.mp hyn x⁻¹).mp (inv_mem hx)
      have : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) := by group
      rw [this]
      exact mul_mem hx h1
  ·
    apply le_antisymm
    · intro x hx
      obtain ⟨hxP, hxD⟩ := Subgroup.mem_inf.mp hx
      have hxn : x ∈ AChief.nrm N := hDn hxD
      have hmem : AChief.qmap N ⟨x, hxn⟩ ∈ M₂ ⊓ cenIn (AChief.qimg N X)
          ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N)) := by
        refine Subgroup.mem_inf.mpr ⟨(SolQuot.mem_qpre_iff.mp hxP).2, ?_⟩
        rw [hcen]
        exact (AChief.mem_qimg_iff N _ _).mpr ⟨⟨x, hxn⟩, hxD, rfl⟩
      rw [hinf] at hmem
      obtain ⟨y, hyY, hyx⟩ := (AChief.mem_qimg_iff N Y _).mp hmem
      obtain ⟨r, hrN, hr⟩ := Thm211.exists_mem_of_qmap_eq (R := N) (x := ⟨x, hxn⟩) (y := y) hyx.symm
      have hyD : (y : Γ) ∈ cenIn X (A : Set Γ) := hYD hyY
      have hrD : r ∈ cenIn X (A : Set Γ) := by
        have : r = x⁻¹ * (y : Γ) := by
          rw [hr]
          group
        rw [this]
        exact mul_mem (inv_mem hxD) hyD
      have hrY : r ∈ Y := hND (Subgroup.mem_inf.mpr ⟨hrN, hrD⟩)
      have : x = (y : Γ) * r⁻¹ := by
        rw [hr]
        group
      rw [this]
      exact mul_mem hyY (inv_mem hrY)
    · refine le_inf ?_ hYD
      have h1 : AChief.qimg N Y ≤ M₂ := by
        rw [← hinf]
        exact inf_le_left
      exact (SolQuot.qimg_le_iff hYn).mp h1

omit [Finite Γ] in
theorem qimg_mem_iEset (h : NearAsolvAction p A X) (hX : X ≤ AChief.nrm N)
    (hA : A ≤ AChief.nrm N) {Z : Subgroup Γ} (hZ : Z ∈ iEset A X Y) :
    AChief.qimg N Z ∈ iEset (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y) := by
  have hZX : Z ≤ X := hZ.1.1
  have hZn : Z ≤ AChief.nrm N := hZX.trans hX
  refine ⟨isDAIn_qimg h hX hA hZ.1, ?_⟩
  have hcop : Nat.Coprime p (Nat.card ↥Z) :=
    h.nearPSolvable.1.coprime_dvd_right (Subgroup.card_dvd_of_le hZX)
  have key := AChief.qimg_inf_centralizer (N := N) h.prime h.elemAbelian hZ.1.admits_left hA hZn
    hcop
  have h1 : AChief.qimg N Z ≤ AChief.qimg N X := SolQuot.qimg_mono hZX
  have h2 : Z ⊓ Subgroup.centralizer (A : Set Γ) = Y := by
    have h3 : Z ⊓ cenIn X (A : Set Γ) = Z ⊓ Subgroup.centralizer (A : Set Γ) := by
      unfold cenIn
      rw [← inf_assoc, inf_eq_left.mpr hZX]
    rw [← h3]
    exact hZ.2
  show AChief.qimg N Z ⊓ (AChief.qimg N X ⊓ Subgroup.centralizer
    ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N))) = AChief.qimg N Y
  rw [← inf_assoc, inf_eq_left.mpr h1, ← key, h2]

open CFSG.SignalizerFunctorTheorem.Nonsolvable (oStar oStar_eq_comap_layer)

theorem oStar_eq_top_iff_layer {H : Type*} [Group H] [Finite H] :
    oStar H = ⊤ ↔ CFSG.layer (H ⧸ CFSG.solvableRadical H) = ⊤ := by
  rw [oStar_eq_comap_layer]
  constructor
  · intro h
    have := congrArg (Subgroup.map (QuotientGroup.mk' (CFSG.solvableRadical H))) h
    rwa [Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _),
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at this
  · intro h
    rw [h, Subgroup.comap_top]

theorem oStar_eq_top_of_surjective {H H' : Type*} [Group H] [Group H'] [Finite H]
    (hH : oStar H = ⊤) {f : H →* H'} (hf : Function.Surjective f) : oStar H' = ⊤ := by
  have : Finite H' := Finite.of_surjective f hf
  rw [oStar_eq_top_iff_layer] at hH ⊢
  have hle : CFSG.solvableRadical H ≤ (CFSG.solvableRadical H').comap f :=
    Subgroup.map_le_iff_le_comap.mp (SolQuot.map_solvableRadical_le hf)
  let g : H ⧸ CFSG.solvableRadical H →* H' ⧸ CFSG.solvableRadical H' :=
    QuotientGroup.map _ _ f hle
  have hg : Function.Surjective g :=
    QuotientGroup.map_surjective_of_surjective _ _ f
      ((QuotientGroup.mk'_surjective _).comp hf) hle
  exact CFSG.LocalCores.layer_eq_top_of_surjective hH g hg

theorem qimg_kOf_le (hX : X ≤ AChief.nrm N) :
    AChief.qimg N (kOf X) ≤ kOf (AChief.qimg N X) := by
  have hK : kOf X ≤ AChief.nrm N := (kOf_le X).trans hX
  have hKo : oStar ↥(kOf X) = ⊤ := (kOf_eq_self_iff_oStar_eq_top _).mp (kOf_kOf X)
  have hq : oStar ↥(AChief.qimg N (kOf X)) = ⊤ :=
    oStar_eq_top_of_surjective hKo (SolQuot.qres_surjective hK)
  have hKS : IsKSubgroup (AChief.qimg N (kOf X)) :=
    (isKSubgroup_iff_kOf_eq_self _).mpr ((kOf_eq_self_iff_oStar_eq_top _).mpr hq)
  refine le_kOf_of_isKSubgroup (SolQuot.qimg_mono (kOf_le X)) ?_ hKS
  rw [SolQuot.subgroupOf_qimg hX (kOf_le X)]
  exact Subgroup.Normal.map (normal_kOf_subgroupOf X) _ (SolQuot.qres_surjective hX)

@[expose] def Concl (A X Y : Subgroup Γ) : Prop :=
  (iThetaM A X Y, iThetaL A X Y) ∈ iPairsY A X Y ∧ kOf X ≤ iThetaM A X Y ∧
    iThetaY A X Y ∈ iEset A X Y ∧ iThetaY A X Y ≤ iThetaM A X Y

theorem concl_of_quotient
    (h : NearAsolvAction p A X) (hP : (X₁, X₂) ∈ iPairsY A X Y)
    (hNX : N ≤ X) (hX : Admits X N) (hA : Admits A N) (hND : N ⊓ cenIn X (A : Set Γ) ≤ Y)
    (hbar : Concl (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y)) : Concl A X Y := by
  obtain ⟨hb, hc, hd, he⟩ := hbar
  have hXn : X ≤ AChief.nrm N := hX
  have hAn : A ≤ AChief.nrm N := hA
  have hYD : Y ≤ cenIn X (A : Set Γ) := pair_Y_le hP
  have hDn : cenIn X (A : Set Γ) ≤ AChief.nrm N := inf_le_left.trans hXn
  have himg : ∀ P ∈ iPairsY A X Y, (AChief.qimg N P.1, AChief.qimg N P.2) ∈
      iPairsY (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y) := fun P hP' =>
    qimg_mem_iPairsY h (X₁ := P.1) (X₂ := P.2) hP' hXn hAn
      (inf_le_of_inf_dsub_le h (X₁ := P.1) (X₂ := P.2) hP' hX hA hND)
  have hlift := qpre_mem_iPairsY h hNX hXn hAn hYD hND hb
  have hθM : iThetaM A X Y = SolQuot.qpre N (iThetaM (AChief.qimg N A) (AChief.qimg N X)
      (AChief.qimg N Y)) := by
    refine le_antisymm (iSup₂_le fun P hP' => ?_) ?_
    · have h1 := le_iSup₂ (f := fun (Q : Subgroup (AChief.QG N) × Subgroup (AChief.QG N))
        (_ : Q ∈ iPairsY (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y)) => Q.1)
        (AChief.qimg N P.1, AChief.qimg N P.2) (himg P hP')
      exact (SolQuot.qimg_le_iff ((pair_le (X₁ := P.1) (X₂ := P.2) hP').trans hXn)).mp h1
    · exact le_iSup₂ (f := fun (Q : Subgroup Γ × Subgroup Γ) (_ : Q ∈ iPairsY A X Y) => Q.1)
        (SolQuot.qpre N (iThetaM (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y)),
          SolQuot.qpre N (iThetaL (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y))) hlift
  have hθL : iThetaL A X Y = SolQuot.qpre N (iThetaL (AChief.qimg N A) (AChief.qimg N X)
      (AChief.qimg N Y)) := by
    refine le_antisymm (iSup₂_le fun P hP' => ?_) ?_
    · have h1 := le_iSup₂ (f := fun (Q : Subgroup (AChief.QG N) × Subgroup (AChief.QG N))
        (_ : Q ∈ iPairsY (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y)) => Q.2)
        (AChief.qimg N P.1, AChief.qimg N P.2) (himg P hP')
      exact (SolQuot.qimg_le_iff (((pair_le₂ (X₁ := P.1) (X₂ := P.2) hP').trans
        (pair_le (X₁ := P.1) (X₂ := P.2) hP')).trans hXn)).mp h1
    · exact le_iSup₂ (f := fun (Q : Subgroup Γ × Subgroup Γ) (_ : Q ∈ iPairsY A X Y) => Q.2)
        (SolQuot.qpre N (iThetaM (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y)),
          SolQuot.qpre N (iThetaL (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y))) hlift
  have hθY : AChief.qimg N (iThetaY A X Y) ≤
      iThetaY (AChief.qimg N A) (AChief.qimg N X) (AChief.qimg N Y) := by
    unfold iThetaY
    rw [SolQuot.qimg_biSup (fun Z hZ => hZ.1.1.trans hXn)]
    exact iSup₂_le fun Z hZ => le_iSup₂ (f := fun W (_ : W ∈ iEset (AChief.qimg N A)
      (AChief.qimg N X) (AChief.qimg N Y)) => W) (AChief.qimg N Z) (qimg_mem_iEset h hXn hAn hZ)
  have hYE : Y ∈ iEset A X Y :=
    ⟨⟨hYD.trans inf_le_left, pair_admits_Y hP⟩, inf_eq_left.mpr hYD⟩
  have hdE : iThetaY A X Y ∈ iEset A X Y := by
    refine ⟨⟨iSup₂_le fun Z hZ => hZ.1.1, Admits.iSup fun _ => Admits.iSup fun hZ => hZ.1.2⟩, ?_⟩
    refine le_antisymm (fun x hx => ?_) (le_inf (le_iSup₂ (f := fun Z (_ : Z ∈ iEset A X Y) => Z)
      Y hYE) hYD)
    obtain ⟨hxT, hxD⟩ := Subgroup.mem_inf.mp hx
    have hxn : x ∈ AChief.nrm N := hDn hxD
    have hmem : AChief.qmap N ⟨x, hxn⟩ ∈ iThetaY (AChief.qimg N A) (AChief.qimg N X)
        (AChief.qimg N Y) ⊓ cenIn (AChief.qimg N X)
          ((AChief.qimg N A : Subgroup (AChief.QG N)) : Set (AChief.QG N)) := by
      refine Subgroup.mem_inf.mpr ⟨hθY ((AChief.mem_qimg_iff N _ _).mpr ⟨⟨x, hxn⟩, hxT, rfl⟩), ?_⟩
      rw [cenIn_qimg h hXn hAn]
      exact (AChief.mem_qimg_iff N _ _).mpr ⟨⟨x, hxn⟩, hxD, rfl⟩
    rw [hd.2] at hmem
    obtain ⟨y, hyY, hyx⟩ := (AChief.mem_qimg_iff N Y _).mp hmem
    obtain ⟨r, hrN, hr⟩ := Thm211.exists_mem_of_qmap_eq (R := N) (x := ⟨x, hxn⟩) (y := y) hyx.symm
    have hyD : (y : Γ) ∈ cenIn X (A : Set Γ) := hYD hyY
    have hrD : r ∈ cenIn X (A : Set Γ) := by
      have : r = x⁻¹ * (y : Γ) := by
        rw [hr]
        group
      rw [this]
      exact mul_mem (inv_mem hxD) hyD
    have hrY : r ∈ Y := hND (Subgroup.mem_inf.mpr ⟨hrN, hrD⟩)
    have : x = (y : Γ) * r⁻¹ := by
      rw [hr]
      group
    rw [this]
    exact mul_mem hyY (inv_mem hrY)
  refine ⟨?_, ?_, hdE, ?_⟩
  · rw [hθM, hθL]
    exact hlift
  · rw [hθM]
    exact (SolQuot.qimg_le_iff ((kOf_le X).trans hXn)).mp ((qimg_kOf_le hXn).trans hc)
  · rw [hθM]
    exact (SolQuot.qimg_le_iff (hdE.1.1.trans hXn)).mp (hθY.trans he)

end CFSG.SignalizerFunctorTheorem.McBride.Near.Thm33b
