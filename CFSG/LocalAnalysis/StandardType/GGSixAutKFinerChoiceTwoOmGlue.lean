module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoOmCore
public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmGlue

public section

namespace CFSG.StandardType

namespace ChoiceTwoOm

open Module Multiplicative QuadraticMap ChoiceTwo Polynomial

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Basis

variable {G : Type} [Group G] {s : ℕ} {T : (Fin s → ZMod 3) → G} {Bs : Subgroup G}

@[expose] def expSubT (T : (Fin s → ZMod 3) → G) (hT0 : T 0 = 1)
    (hTadd : ∀ f f', T (f + f') = T f * T f') (X : Subgroup G) :
    AddSubgroup (Fin s → ZMod 3) where
  carrier := {f | T f ∈ X}
  add_mem' {f f'} hf hf' := by
    change T (f + f') ∈ X
    rw [hTadd]
    exact X.mul_mem hf hf'
  zero_mem' := by
    change T 0 ∈ X
    rw [hT0]
    exact X.one_mem
  neg_mem' {f} hf := by
    change T (-f) ∈ X
    have h1 : T (-f) = (T f)⁻¹ := by
      rw [eq_inv_iff_mul_eq_one, ← hTadd, neg_add_cancel, hT0]
    rw [h1]
    exact X.inv_mem hf

theorem smul_mem_expSubT (hT0 : T 0 = 1) (hTadd : ∀ f f', T (f + f') = T f * T f')
    {X : Subgroup G} {f : Fin s → ZMod 3} (hf : f ∈ expSubT T hT0 hTadd X) (c : ZMod 3) :
    c • f ∈ expSubT T hT0 hTadd X := by
  have := AddSubgroup.nsmul_mem _ hf c.val
  rwa [← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val] at this

theorem exists_basis_of_hom (hT0 : T 0 = 1) (hTadd : ∀ f f', T (f + f') = T f * T f')
    (hTinj : Function.Injective T) (hBs : ∀ g, g ∈ Bs ↔ ∃ f, T f = g) {D : Subgroup G}
    (hDB : D ≤ Bs) (hD9 : Nat.card D = 9) :
    ∃ t₁ t₂ : Fin s → ZMod 3, ∀ g, g ∈ D ↔ ∃ a, T (comb2 t₁ t₂ a) = g := by
  classical
  set KD := expSubT T hT0 hTadd D with hKD
  have hcard : Nat.card KD = 9 := by
    rw [← hD9]
    refine Nat.card_congr (Equiv.ofBijective (fun f => (⟨T f, f.2⟩ : D)) ⟨?_, ?_⟩)
    · intro f f' h
      exact Subtype.ext (hTinj (congrArg Subtype.val h))
    · intro d
      obtain ⟨f, hf⟩ := (hBs d).mp (hDB d.2)
      exact ⟨⟨f, show T f ∈ D by rw [hf]; exact d.2⟩, Subtype.ext hf⟩
  have hmult : ∀ t : Fin s → ZMod 3,
      Nat.card {f // ∃ c : ZMod 3, f = c • t} ≤ 3 := fun t => by
    have := Nat.card_le_card_of_surjective (fun c : ZMod 3 => (⟨c • t, c, rfl⟩ :
      {f // ∃ c : ZMod 3, f = c • t})) (fun ⟨f, c, hc⟩ => ⟨c, Subtype.ext hc.symm⟩)
    rwa [Nat.card_zmod] at this
  obtain ⟨t₁, ht₁K, ht₁⟩ : ∃ t ∈ KD, t ≠ 0 := by
    by_contra h
    push Not at h
    have : Nat.card KD ≤ 1 := by
      rw [Finite.card_le_one_iff_subsingleton]
      exact ⟨fun f f' => Subtype.ext ((h f f.2).trans (h f' f'.2).symm)⟩
    omega
  obtain ⟨t₂, ht₂K, ht₂⟩ : ∃ t ∈ KD, ∀ c : ZMod 3, t ≠ c • t₁ := by
    by_contra h
    push Not at h
    have : Nat.card KD ≤ Nat.card {f // ∃ c : ZMod 3, f = c • t₁} :=
      Nat.card_le_card_of_injective (fun f => (⟨f.1, h f.1 f.2⟩ : {f // ∃ c : ZMod 3, f = c • t₁}))
        fun f f' hff => Subtype.ext (Subtype.mk.inj hff)
    have := hmult t₁
    omega
  have hind : ∀ a, a ≠ 0 → comb2 t₁ t₂ a ≠ 0 := by
    intro a ha h0
    rw [comb2] at h0
    by_cases ha2 : a.2 = 0
    · have ha1 : a.1 ≠ 0 := fun h1 => ha (Prod.ext h1 ha2)
      rw [ha2, zero_smul, add_zero] at h0
      apply ht₁
      have := congrArg (fun f => a.1⁻¹ • f) h0
      simpa [smul_smul, inv_mul_cancel₀ ha1] using this
    · apply ht₂ (-(a.2⁻¹ * a.1))
      have h1 : a.2 • t₂ = -(a.1 • t₁) := eq_neg_of_add_eq_zero_right h0
      have := congrArg (fun f => a.2⁻¹ • f) h1
      simp only [smul_smul, inv_mul_cancel₀ ha2, one_smul, smul_neg] at this
      rw [this, neg_smul]
  refine ⟨t₁, t₂, fun g => ⟨fun hg => ?_, fun ⟨a, ha⟩ => ?_⟩⟩
  · obtain ⟨f, hf⟩ := (hBs g).mp (hDB hg)
    have hfK : f ∈ KD := show T f ∈ D by rw [hf]; exact hg
    have hinj : Function.Injective fun a : ZMod 3 × ZMod 3 =>
        (⟨comb2 t₁ t₂ a, KD.add_mem (smul_mem_expSubT hT0 hTadd ht₁K a.1)
          (smul_mem_expSubT hT0 hTadd ht₂K a.2)⟩ : KD) := by
      intro a a' h
      have h1 : comb2 t₁ t₂ a = comb2 t₁ t₂ a' := congrArg Subtype.val h
      by_contra hne
      apply hind (a - a') (sub_ne_zero.mpr hne)
      simp only [comb2] at h1 ⊢
      rw [Prod.fst_sub, Prod.snd_sub, sub_smul, sub_smul]
      rw [← sub_eq_zero] at h1
      rw [← h1]
      abel
    have hbij := hinj.bijective_of_nat_card_le (by rw [hcard, Nat.card_eq_fintype_card]; rfl)
    obtain ⟨a, ha⟩ := hbij.2 ⟨f, hfK⟩
    exact ⟨a, by rw [← hf]; exact congrArg T (congrArg Subtype.val ha)⟩
  · rw [← ha]
    exact KD.add_mem (smul_mem_expSubT hT0 hTadd ht₁K a.1) (smul_mem_expSubT hT0 hTadd ht₂K a.2)

end Basis

section Transport

variable {H G : Type} [Group H] [Group G] {Ω : Subgroup H} {φ : ↥Ω →* G}

theorem card_inf_centralizer_le' [Finite G] [Finite H] (hφ : Function.Injective φ)
    {A : Subgroup H} {Bs : Subgroup G} (hAΩ : A ≤ Ω)
    (hAB : ∀ g : ↥Ω, (g : H) ∈ A → φ g ∈ Bs) {X : Subgroup G} (hX : X ≤ φ.range) :
    Nat.card (A ⊓ Subgroup.centralizer (((X.comap φ).map Ω.subtype : Subgroup H) : Set H) :
      Subgroup H) ≤ Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := by
  classical
  have hmem : ∀ c : ↥(A ⊓ Subgroup.centralizer (((X.comap φ).map Ω.subtype : Subgroup H) :
      Set H)), φ ⟨c, hAΩ (Subgroup.mem_inf.mp c.2).1⟩ ∈
        Bs ⊓ Subgroup.centralizer (X : Set G) := by
    intro c
    refine Subgroup.mem_inf.mpr ⟨hAB _ (Subgroup.mem_inf.mp c.2).1,
      Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
    obtain ⟨w, rfl⟩ := hX hy
    have hw : (w : H) ∈ ((X.comap φ).map Ω.subtype : Subgroup H) := ⟨w, hy, rfl⟩
    have hc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp c.2).2 _ hw
    rw [← map_mul, ← map_mul]
    exact congrArg φ (Subtype.ext hc)
  refine Nat.card_le_card_of_injective (fun c => ⟨_, hmem c⟩) fun c c' h => ?_
  have h1 := hφ (congrArg Subtype.val h)
  have h2 : (c : H) = c' := congrArg (fun z : ↥Ω => (z : H)) h1
  exact Subtype.ext h2

end Transport

section Model

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.RankThree.PartOne.KCOrthComm CFSG.RankThree.Classical2 NoOffOm CFSG.Assembly.LowTwoRank
  SevOm

theorem choice_of_matrixModel {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {d : ℕ} {Q : QuadraticForm (GaloisField 2 1) (Fin d → GaloisField 2 1)}
    (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule (GaloisField 2 1) (Fin d → GaloisField 2 1),
      Module.finrank (GaloisField 2 1) T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (φ : matrixDerived Q →* G) (hφ : Function.Injective φ) (hrange : φ.range = ggG0 3 B x L D J)
    (hBs : GGBstar 3 B Bs) (hBφ : Bs ≤ φ.range) (hB4 : 3 ^ 4 ≤ Nat.card B)
    (hDB : D ≤ Bs) (hD9 : Nat.card D = 3 ^ 2) (hDJ : D = B ⊓ Subgroup.centralizer (J : Set G))
    (hJq : CFSG.IsQuasisimple J) (hJG : J ≤ ggG0 3 B x L D J)
    (hJD : J ≤ Subgroup.centralizer (D : Set G))
    (hJc : Nat.card (Bs ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) ≤ 3 ^ 3)
    {b : G} (hb : b ∈ Bs) (hb1 : b ≠ 1) {L₁ : Subgroup G}
    (hL₁ : CFSG.Assembly.IsComponentOf L₁ (ggG0 3 B x L D J ⊓ Subgroup.centralizer {b}))
    (hL₁c : Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ 3 ^ 2) :
    ∃ m ∈ ggG0 3 B x L D J ⊓ Subgroup.normalizer (Bs : Set G),
      ∃ g ∈ L₁, (∃ l ∈ L₁, g * l ≠ l * g) ∧
        g ∈ Subgroup.centralizer (D.map (MulAut.conj m⁻¹).toMonoidHom : Set G) ∧
        Nat.Coprime (orderOf g) 3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 (by norm_num), pow_one]
  have hA := genMax_of_orth hnd hT Nat.prime_three (by decide) hBs.2.1 hBs.2.2.2 φ hφ hBφ
  obtain ⟨r, ⟨F⟩⟩ := exists_frame_of_genMax hA
  set A := ((Bs.comap φ).map (matrixDerived Q).subtype).map
    (matrixLinearIso (d := d) (K := GaloisField 2 1)).toMonoidHom with hAdef
  set Ω := orthDerived Q with hΩ
  set φV : ↥Ω →* G := φ.comp (matrixDerivedEquiv Q).symm.toMonoidHom with hφVdef
  have hφV : Function.Injective φV := hφ.comp (matrixDerivedEquiv Q).symm.injective
  have hφVr : φV.range = φ.range := by
    ext g
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨X, rfl⟩
      exact ⟨matrixDerivedEquiv Q X, by simp [hφVdef]⟩
  have : Finite ((Fin d → GaloisField 2 1) ≃ₗ[GaloisField 2 1] (Fin d → GaloisField 2 1)) :=
    CFSG.RankThree.PartOne.KCOrthComm.finite_linearEquiv
  have hAB : ∀ g : ↥Ω, ((g : ↥Ω) : (Fin d → GaloisField 2 1) ≃ₗ[GaloisField 2 1]
      (Fin d → GaloisField 2 1)) ∈ A ↔ φV g ∈ Bs := by
    intro g
    constructor
    · rintro ⟨_, ⟨Y, hY, rfl⟩, hYg⟩
      have hYg' : (matrixDerivedEquiv Q).symm g = Y := by
        apply (matrixDerivedEquiv Q).injective
        rw [MulEquiv.apply_symm_apply]
        exact Subtype.ext hYg.symm
      show φ ((matrixDerivedEquiv Q).symm g) ∈ Bs
      rw [hYg']
      exact hY
    · intro hg
      exact ⟨((matrixDerivedEquiv Q).symm g).1, ⟨(matrixDerivedEquiv Q).symm g, hg, rfl⟩, by
        have h1 := coe_matrixDerivedEquiv Q ((matrixDerivedEquiv Q).symm g)
        rw [MulEquiv.apply_symm_apply] at h1
        exact h1.symm⟩
  have hAΩ : A ≤ Ω := by
    rintro _ ⟨_, ⟨Y, -, rfl⟩, rfl⟩
    have h1 := (matrixDerivedEquiv Q Y).2
    rwa [coe_matrixDerivedEquiv] at h1
  have hBφV : Bs ≤ φV.range := hφVr ▸ hBφ
  have hmax : ∀ g ∈ Ω, g ^ 3 = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A := by
    intro g hg hgp hgc
    refine (hAB ⟨g, hg⟩).mpr (hBs.2.2.2 _ (Subgroup.mem_centralizer_iff.mpr fun y hy => ?_) ?_)
    · obtain ⟨c, rfl⟩ := hBφV hy
      have h1 := hgc c ((hAB c).mpr hy)
      rw [← map_mul, ← map_mul]
      exact congrArg φV (Subtype.ext h1.symm)
    · rw [← map_pow]
      have h1 : (⟨g, hg⟩ : ↥Ω) ^ 3 = 1 := Subtype.ext (by simpa using hgp)
      rw [h1, map_one]
  obtain ⟨C, -⟩ := exists_coord hK hnd hT hAΩ F hmax
  set T : (Fin C.s → ZMod 3) → G := fun f => φV ⟨C.tor f, hAΩ (C.tor_mem f)⟩ with hTdef
  have hT0 : T 0 = 1 := by
    simp only [hTdef]
    rw [show (⟨C.tor 0, hAΩ (C.tor_mem 0)⟩ : ↥Ω) = 1 from Subtype.ext C.tor_zero, map_one]
  have hTadd : ∀ f f', T (f + f') = T f * T f' := by
    intro f f'
    simp only [hTdef]
    rw [← map_mul]
    congr 1
    exact Subtype.ext (C.tor_add f f')
  have hTinj : Function.Injective T := fun f f' h =>
    C.tor_injective (congrArg Subtype.val (hφV h))
  have hBsT : ∀ g, g ∈ Bs ↔ ∃ f, T f = g := by
    intro g
    constructor
    · intro hg
      obtain ⟨c, rfl⟩ := hBφV hg
      obtain ⟨f, hf⟩ := C.mem_tor _ ((hAB c).mpr hg)
      exact ⟨f, by simp only [hTdef]; congr 1; exact Subtype.ext hf⟩
    · rintro ⟨f, rfl⟩
      exact (hAB _).mp (C.tor_mem f)
  have hcardBs : Nat.card Bs = 3 ^ C.s := by
    have e := Equiv.ofBijective (fun f : Fin C.s → ZMod 3 => (⟨T f, (hBsT _).mpr ⟨f, rfl⟩⟩ : Bs))
      ⟨fun f f' h => hTinj (congrArg Subtype.val h), fun c => by
        obtain ⟨f, hf⟩ := (hBsT c).mp c.2
        exact ⟨f, Subtype.ext hf⟩⟩
    rw [← Nat.card_congr e, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin C.s),
      Fintype.card_fin]
  have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBs.1
  have hs : 4 ≤ C.s := (Nat.pow_le_pow_iff_right (by norm_num)).mp
    (hcardBs ▸ hB4.trans hBBs)
  obtain ⟨β, rfl⟩ := (hBsT b).mp hb
  have hβ : β ≠ 0 := fun h => hb1 (by rw [h, hT0])
  obtain ⟨t₁, t₂, hD⟩ := exists_basis_of_hom hT0 hTadd hTinj hBsT hDB (by rw [hD9]; norm_num)
  have hG₀ : φV.range = ggG0 3 B x L D J := hφVr.trans hrange
  rw [← hG₀] at hL₁ hJG
  obtain ⟨hL, hmapL⟩ := isComponentOf_transport hφV ⟨C.tor β, hAΩ (C.tor_mem β)⟩ hL₁
  have hL₁G : L₁ ≤ φV.range := hmapL ▸ Subgroup.map_le_range φV _
  have hAB' : ∀ g : ↥Ω, (g : (Fin d → GaloisField 2 1) ≃ₗ[GaloisField 2 1]
      (Fin d → GaloisField 2 1)) ∈ A → φV g ∈ Bs := fun g hg => (hAB g).mp hg
  have hL₁c' := (card_inf_centralizer_le' hφV hAΩ hAB' hL₁G).trans hL₁c
  set J' := (J.comap φV).map Ω.subtype with hJ'
  have hJmap : (J.comap φV).map φV = J := Subgroup.map_comap_eq_self hJG
  have hJ'q : CFSG.IsQuasisimple J' :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((MulEquiv.subgroupCongr hJmap).symm.trans
        (((J.comap φV).equivMapOfInjective φV hφV).symm.trans
          ((J.comap φV).equivMapOfInjective Ω.subtype Ω.subtype_injective))) hJq
  have hJ'O : J' ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
    (Subgroup.map_subtype_le _).trans
      CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup
  have hJ'c : ∀ a, ∀ g ∈ J', g * C.tor (comb2 t₁ t₂ a) = C.tor (comb2 t₁ t₂ a) * g := by
    rintro a _ ⟨w, hw, rfl⟩
    have hdD : T (comb2 t₁ t₂ a) ∈ D := (hD _).mpr ⟨a, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp (hJD hw) _ hdD
    have h2 : w * ⟨C.tor (comb2 t₁ t₂ a), hAΩ (C.tor_mem _)⟩ =
        ⟨C.tor (comb2 t₁ t₂ a), hAΩ (C.tor_mem _)⟩ * w :=
      hφV (by rw [map_mul, map_mul]; exact h1.symm)
    exact congrArg Subtype.val h2
  have hJA := (card_inf_centralizer_le' hφV hAΩ hAB' hJG).trans hJc
  have hJA4 : C.s = 4 → Nat.card (A ⊓ Subgroup.centralizer (J' : Set
      ((Fin d → GaloisField 2 1) ≃ₗ[GaloisField 2 1] (Fin d → GaloisField 2 1))) :
        Subgroup _) ≤ 3 ^ 2 := by
    intro h4
    have hBeq : B = Bs := Subgroup.eq_of_le_of_card_ge hBs.1 (by
      rw [hcardBs, h4]
      exact hB4)
    refine (card_inf_centralizer_le' hφV hAΩ hAB' hJG).trans ?_
    rw [← hBeq, ← hDJ, hD9]
  obtain ⟨π, η, hη, g', hg', ⟨l', hl', hgl⟩, hgg, hcomm⟩ :=
    C.choice_core hK hnd hT hs hβ hL hL₁c' t₁ t₂ hJ'q hJ'O hJ'c hJA hJA4
  obtain ⟨w, hw, rfl⟩ := hg'
  obtain ⟨wl, hwl, rfl⟩ := hl'
  have hMΩ : C.move π η ∈ Ω := C.move_mem hnd hT π hη
  set M : G := φV ⟨C.move π η, hMΩ⟩ with hM
  have hMconj : ∀ f, M * T f * M⁻¹ = T (moveExp π η f) := by
    intro f
    simp only [hM, hTdef]
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [C.move_conj, mul_inv_cancel_right]
  refine ⟨M⁻¹, ⟨hG₀ ▸ ⟨_, by rw [map_inv]⟩, Subgroup.inv_mem _
    (CFSG.StandardType.ChoiceTwo.mem_normalizer_of_conj_mem fun y hy => ?_)⟩, φV w, hw,
    ⟨φV wl, hwl, fun h => hgl (congrArg Subtype.val
      (hφV (show φV (w * wl) = φV (wl * w) by rw [map_mul, map_mul]; exact h)))⟩,
    ?_, CFSG.StandardType.ChoiceTwo.coprime_orderOf_three ?_⟩
  · obtain ⟨f, rfl⟩ := (hBsT y).mp hy
    rw [hMconj]
    exact (hBsT _).mpr ⟨_, rfl⟩
  · rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨a, rfl⟩ := (hD e).mp he
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [hMconj]
    simp only [hTdef]
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm a).symm
  · rw [← map_mul]
    rw [show w * w = 1 from Subtype.ext hgg, map_one]

end Model

end ChoiceTwoOm

end CFSG.StandardType
