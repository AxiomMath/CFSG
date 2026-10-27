module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcPlacementDefs
import CFSG.LocalAnalysis.StandardType.GGQ2CoverComponents
import CFSG.LocalAnalysis.StandardType.GGQ2AutomizerCover
import CFSG.LocalAnalysis.StandardType.GGQ2SpRealization

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG.Open (IsElemAbelian)

private theorem mfc_range_comp_inclusion {G : Type} [Group G] {H A : Subgroup G} {M : Type}
    [Group M] (hAH : A ≤ H) (π : ↥H →* M) :
    (π.comp (Subgroup.inclusion hAH)).range = (A.subgroupOf H).map π := by
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

private theorem mfc_cover_injective {G : Type} [Group G] {H E : Subgroup G} {M : Type} [Group M]
    (hEH : E ≤ H) (π : ↥H →* M) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEab : IsElemAbelian 3 E) :
    Function.Injective (π.comp (Subgroup.inclusion hEH)) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hmem : (Subgroup.inclusion hEH a : ↥H) ∈ π.ker := by
    rw [MonoidHom.mem_ker]
    exact ha
  have ha3 : a ^ 3 = 1 := Subtype.ext (by simpa using hEab.2 (a : G) a.2)
  have h3 : (Subgroup.inclusion hEH a : ↥H) ^ 3 = 1 := by rw [← map_pow, ha3, map_one]
  have hdvd3 : orderOf (Subgroup.inclusion hEH a : ↥H) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hdvdK : orderOf (Subgroup.inclusion hEH a : ↥H) ∣ Nat.card π.ker :=
    Subgroup.orderOf_dvd_natCard π.ker hmem
  have hcop : Nat.Coprime 3 (Nat.card π.ker) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hker3
  have hone : orderOf (Subgroup.inclusion hEH a : ↥H) = 1 :=
    Nat.dvd_one.mp (hcop ▸ Nat.dvd_gcd hdvd3 hdvdK)
  have ha1 : (Subgroup.inclusion hEH a : ↥H) = 1 := orderOf_eq_one_iff.mp hone
  exact Subtype.ext (congrArg (fun x : ↥H => (x : G)) ha1)

private noncomputable def mfc_cover_equiv {G : Type} [Group G] {H E : Subgroup G} {M : Type}
    [Group M] (hEH : E ≤ H) (π : ↥H →* M) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEab : IsElemAbelian 3 E) : ↥E ≃* ↥((E.subgroupOf H).map π) :=
  (MonoidHom.ofInjective (mfc_cover_injective hEH π hker3 hEab)).trans
    (MulEquiv.subgroupCongr (mfc_range_comp_inclusion hEH π))

private theorem mfc_cover_equiv_apply {G : Type} [Group G] {H E : Subgroup G} {M : Type} [Group M]
    (hEH : E ≤ H) (π : ↥H →* M) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEab : IsElemAbelian 3 E) (a : ↥E) :
    ((mfc_cover_equiv hEH π hker3 hEab a : ↥((E.subgroupOf H).map π)) : M) =
      π (Subgroup.inclusion hEH a) := by
  rw [mfc_cover_equiv, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MonoidHom.ofInjective_apply]
  rfl

private noncomputable def mfc_coord {G : Type} [Group G] {H E : Subgroup G} {M : Type} [Group M]
    {R : RawFrameData} (hEH : E ≤ H) (π : ↥H →* M) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEab : IsElemAbelian 3 E)
    (mf' : ModelFrame (⊤ : Subgroup M) ((E.subgroupOf H).map π) R) :
    Additive ↥E ≃+ R.V :=
  (MulEquiv.toAdditive (mfc_cover_equiv hEH π hker3 hEab)).trans mf'.coord

private theorem mfc_coord_ofMul {G : Type} [Group G] {H E : Subgroup G} {M : Type} [Group M]
    {R : RawFrameData} (hEH : E ≤ H) (π : ↥H →* M) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEab : IsElemAbelian 3 E)
    (mf' : ModelFrame (⊤ : Subgroup M) ((E.subgroupOf H).map π) R) (a : ↥E) :
    mfc_coord hEH π hker3 hEab mf' (Additive.ofMul a) =
      mf'.coord (Additive.ofMul (mfc_cover_equiv hEH π hker3 hEab a)) := rfl

private theorem mfc_equivariant {G : Type} [Group G] {H E A : Subgroup G} {M : Type} [Group M]
    (hEH : E ≤ H) (hAE : A ≤ E) (π : ↥H →* M) :
    CoverComponents.Equivariant ((hAE.trans hEH).trans Subgroup.le_normalizer) π
      (π.comp (Subgroup.inclusion (hAE.trans hEH))) := by
  intro x h
  have hcoe : H.normalizerMonoidHom
        ⟨(x : G), ((hAE.trans hEH).trans Subgroup.le_normalizer) x.2⟩ h =
      Subgroup.inclusion (hAE.trans hEH) x * h *
        (Subgroup.inclusion (hAE.trans hEH) x)⁻¹ := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
  rw [hcoe, map_mul, map_mul, map_inv]
  rfl

private theorem mfc_mulAut_congr_apply {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (φ : MulAut X) (y : Y) : (MulAut.congr e φ) y = e (φ (e.symm y)) := by
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]

private theorem mfc_mulAut_congr_symm {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (ψ : MulAut Y) (x : X) : ((MulAut.congr e).symm ψ) x = e.symm (ψ (e x)) := by
  have h := congrArg (fun f : MulAut Y => f (e x)) (MulEquiv.apply_symm_apply (MulAut.congr e) ψ)
  rw [mfc_mulAut_congr_apply] at h
  rw [← h]
  simp

private theorem mfc_ggLin_coord {G : Type} [Group G] {H E : Subgroup G} {M : Type} [Group M]
    {R : RawFrameData} (hEH : E ≤ H) (π : ↥H →* M) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEab : IsElemAbelian 3 E)
    (mf' : ModelFrame (⊤ : Subgroup M) ((E.subgroupOf H).map π) R) (φ : MulAut ↥E) :
    ggLin (p := 3) (mfc_coord hEH π hker3 hEab mf') φ =
      ggLin (p := 3) mf'.coord (MulAut.congr (mfc_cover_equiv hEH π hker3 hEab) φ) := by
  have h := ggLin_mulEquiv_congr (p := 3) (mfc_cover_equiv hEH π hker3 hEab).symm mf'.coord
    (MulAut.congr (mfc_cover_equiv hEH π hker3 hEab) φ)
  rw [MulEquiv.symm_symm] at h
  rw [show MulAut.congr (mfc_cover_equiv hEH π hker3 hEab).symm
      (MulAut.congr (mfc_cover_equiv hEH π hker3 hEab) φ) = φ from ?_] at h
  · exact h
  · ext a
    rw [mfc_mulAut_congr_apply, mfc_mulAut_congr_apply]
    simp

private theorem mfc_ggLin_coord_comp {G : Type} [Group G] {H E : Subgroup G} {M : Type} [Group M]
    {R : RawFrameData} (hEH : E ≤ H) (π : ↥H →* M) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEab : IsElemAbelian 3 E)
    (mf' : ModelFrame (⊤ : Subgroup M) ((E.subgroupOf H).map π) R) :
    ggLin (p := 3) (mfc_coord hEH π hker3 hEab mf') =
      (ggLin (p := 3) mf'.coord).comp
        (MulAut.congr (mfc_cover_equiv hEH π hker3 hEab)).toMonoidHom :=
  MonoidHom.ext fun φ => mfc_ggLin_coord hEH π hker3 hEab mf' φ

private theorem mfc_mem_subgroupOf_map {G : Type} [Group G] {H E : Subgroup G} {M : Type}
    [Group M] (hEH : E ≤ H) (π : ↥H →* M) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEab : IsElemAbelian 3 E) {A : Subgroup G} (hAE : A ≤ E) (a : ↥E) :
    (a : G) ∈ A ↔
      ((mfc_cover_equiv hEH π hker3 hEab a : ↥((E.subgroupOf H).map π)) : M) ∈
        (A.subgroupOf H).map π := by
  constructor
  · intro ha
    rw [mfc_cover_equiv_apply]
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr ha)
  · intro ha
    obtain ⟨x, hx, hxπ⟩ := Subgroup.mem_map.mp ha
    have hxE : (x : G) ∈ E := hAE (Subgroup.mem_subgroupOf.mp hx)
    have hAx : (x : G) ∈ A := Subgroup.mem_subgroupOf.mp hx
    have heq : mfc_cover_equiv hEH π hker3 hEab ⟨(x : G), hxE⟩ =
        mfc_cover_equiv hEH π hker3 hEab a := by
      apply Subtype.ext
      calc ((mfc_cover_equiv hEH π hker3 hEab ⟨(x : G), hxE⟩ :
            ↥((E.subgroupOf H).map π)) : M)
          = π (Subgroup.inclusion hEH ⟨(x : G), hxE⟩) := mfc_cover_equiv_apply hEH π hker3 hEab _
        _ = π x := by
            rw [show (Subgroup.inclusion hEH ⟨(x : G), hxE⟩ : ↥H) = x from Subtype.ext rfl]
        _ = ((mfc_cover_equiv hEH π hker3 hEab a : ↥((E.subgroupOf H).map π)) : M) := hxπ
    have hxa : (⟨(x : G), hxE⟩ : ↥E) = a :=
      (mfc_cover_equiv hEH π hker3 hEab).injective heq
    rw [← hxa]
    exact hAx

private theorem mfc_ggLinImage_eq {G : Type} [Group G] {H E : Subgroup G} {M : Type} [Group M]
    {R : RawFrameData} (hEH : E ≤ H) (π : ↥H →* M) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEab : IsElemAbelian 3 E)
    (mf' : ModelFrame (⊤ : Subgroup M) ((E.subgroupOf H).map π) R)
    {A : Subgroup G} (hAE : A ≤ E) :
    ggLinImage (p := 3) (mfc_coord hEH π hker3 hEab mf') A =
      ggLinImage (p := 3) mf'.coord ((A.subgroupOf H).map π) := by
  ext v
  obtain ⟨a, rfl⟩ : ∃ a : ↥E, mfc_coord hEH π hker3 hEab mf' (Additive.ofMul a) = v :=
    ⟨Additive.toMul ((mfc_coord hEH π hker3 hEab mf').symm v), by simp⟩
  rw [ofMul_mem_ggLinImage, mfc_coord_ofMul, ofMul_mem_ggLinImage]
  exact mfc_mem_subgroupOf_map hEH π hker3 hEab hAE a

private theorem mfc_ggLinImage_eq_range {G : Type} [Group G] {H E : Subgroup G} {M : Type}
    [Group M] {R : RawFrameData} (hEH : E ≤ H) (π : ↥H →* M) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEab : IsElemAbelian 3 E)
    (mf' : ModelFrame (⊤ : Subgroup M) ((E.subgroupOf H).map π) R)
    {A : Subgroup G} (hAE : A ≤ E) :
    ggLinImage (p := 3) (mfc_coord hEH π hker3 hEab mf') A =
      ggLinImage (p := 3) mf'.coord (π.comp (Subgroup.inclusion (hAE.trans hEH))).range := by
  rw [mfc_range_comp_inclusion (hAE.trans hEH) π]
  exact mfc_ggLinImage_eq hEH π hker3 hEab mf' hAE

private theorem mfc_mem_centralizer {G : Type} [Group G] [Finite G] {H E : Subgroup G} {M : Type}
    [Group M] (hEH : E ≤ H) (π : ↥H →* M) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥H) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEab : IsElemAbelian 3 E) {Y : Subgroup M} (hY : ⁅Y, Y⁆ = Y) (a : ↥E) :
    (a : G) ∈ Subgroup.centralizer
        (((⁅Y.comap π, Y.comap π⁆).map H.subtype : Subgroup G) : Set G) ↔
      ((mfc_cover_equiv hEH π hker3 hEab a : ↥((E.subgroupOf H).map π)) : M) ∈
        Subgroup.centralizer ((Y : Subgroup M) : Set M) := by
  obtain ⟨hmap, hperf⟩ := SpPlacement.derived_comap_perfect π hπ hker hY
  have hXtop : commutator ↥(⁅Y.comap π, Y.comap π⁆) = ⊤ :=
    Group.isPerfect_def.1 (Subgroup.isPerfect_iff.2 hperf)
  have hX := CoverComponents.commuteCoverIff_holds (hEH.trans Subgroup.le_normalizer) π
    (π.comp (Subgroup.inclusion hEH)) hker (mfc_equivariant hEH le_rfl π) _ hXtop a
  rw [hmap] at hX
  rw [show (π.comp (Subgroup.inclusion hEH)) a =
      ((mfc_cover_equiv hEH π hker3 hEab a : ↥((E.subgroupOf H).map π)) : M) from
    (mfc_cover_equiv_apply hEH π hker3 hEab a).symm] at hX
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  have h1 : (∀ x ∈ ((⁅Y.comap π, Y.comap π⁆).map H.subtype : Set G), x * (a : G) = (a : G) * x) ↔
      ∀ x ∈ ⁅Y.comap π, Y.comap π⁆, (a : G) * (x : G) = (x : G) * (a : G) := by
    constructor
    · intro h x hx
      exact (h (x : G) (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)).symm
    · intro h g hg
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hg
      exact (h x hx).symm
  refine h1.trans (hX.trans ?_)
  exact ⟨fun h y hy => (h y hy).symm, fun h y hy => (h y hy).symm⟩

private theorem mfc_mem_component {G : Type} [Group G] [Finite G] {H E : Subgroup G} {M : Type}
    [Group M] (hEH : E ≤ H) (π : ↥H →* M) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥H) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEab : IsElemAbelian 3 E) {Y : Subgroup M} (hY : ⁅Y, Y⁆ = Y) (a : ↥E) :
    (a : G) ∈ ((⁅Y.comap π, Y.comap π⁆).map H.subtype : Subgroup G) ↔
      ((mfc_cover_equiv hEH π hker3 hEab a : ↥((E.subgroupOf H).map π)) : M) ∈ Y := by
  have ha3 : (Subgroup.inclusion hEH a : ↥H) ^ 3 = 1 := by
    rw [← map_pow, show a ^ 3 = 1 from Subtype.ext (by simpa using hEab.2 (a : G) a.2),
      map_one]
  have hmem := CoverComponents.memDerivedComapIff_holds π hπ hker hker3 Y hY
    (Subgroup.inclusion hEH a) ha3
  rw [mfc_cover_equiv_apply]
  constructor
  · intro h
    rw [← hmem]
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp h
    rw [show Subgroup.inclusion hEH a = x from Subtype.ext hxa.symm]
    exact hx
  · intro h
    rw [← hmem] at h
    exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hEH a, h, rfl⟩

private theorem mfc_cent_eq {G : Type} [Group G] [Finite G] {H E : Subgroup G} {M : Type}
    [Group M] {R : RawFrameData} (hEH : E ≤ H) (π : ↥H →* M) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥H) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEab : IsElemAbelian 3 E)
    (mf' : ModelFrame (⊤ : Subgroup M) ((E.subgroupOf H).map π) R)
    (c : R.Code) (hc : R.admissible c) :
    ggLinImage (p := 3) (mfc_coord hEH π hker3 hEab mf')
        (Subgroup.centralizer
          (((⁅(mf'.component c).comap π, (mf'.component c).comap π⁆).map H.subtype :
            Subgroup G) : Set G)) = R.cent c := by
  have hYperf : ⁅mf'.component c, mf'.component c⁆ = mf'.component c :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 (mf'.marked c hc).1)
  ext v
  obtain ⟨a, rfl⟩ : ∃ a : ↥E, mfc_coord hEH π hker3 hEab mf' (Additive.ofMul a) = v :=
    ⟨Additive.toMul ((mfc_coord hEH π hker3 hEab mf').symm v), by simp⟩
  rw [ofMul_mem_ggLinImage, mfc_coord_ofMul, ← mf'.cent_eq c hc, ofMul_mem_ggLinImage]
  exact mfc_mem_centralizer hEH π hπ hker hker3 hEab hYperf a

private theorem mfc_inside_eq {G : Type} [Group G] [Finite G] {H E : Subgroup G} {M : Type}
    [Group M] {R : RawFrameData} (hEH : E ≤ H) (π : ↥H →* M) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥H) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEab : IsElemAbelian 3 E)
    (mf' : ModelFrame (⊤ : Subgroup M) ((E.subgroupOf H).map π) R)
    (c : R.Code) (hc : R.admissible c) :
    ggLinImage (p := 3) (mfc_coord hEH π hker3 hEab mf')
        (((⁅(mf'.component c).comap π, (mf'.component c).comap π⁆).map H.subtype :
          Subgroup G)) = R.inside c := by
  have hYperf : ⁅mf'.component c, mf'.component c⁆ = mf'.component c :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 (mf'.marked c hc).1)
  ext v
  obtain ⟨a, rfl⟩ : ∃ a : ↥E, mfc_coord hEH π hker3 hEab mf' (Additive.ofMul a) = v :=
    ⟨Additive.toMul ((mfc_coord hEH π hker3 hEab mf').symm v), by simp⟩
  rw [ofMul_mem_ggLinImage, mfc_coord_ofMul, ← mf'.inside_eq c hc, ofMul_mem_ggLinImage]
  exact mfc_mem_component hEH π hπ hker hker3 hEab hYperf a

private theorem mfc_marked {G : Type} [Group G] [Finite G] {H E : Subgroup G} {M : Type}
    [Group M] {R : RawFrameData} (π : ↥H →* M) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥H)
    (mf' : ModelFrame (⊤ : Subgroup M) ((E.subgroupOf H).map π) R)
    (c : R.Code) (hc : R.admissible c) :
    LargeEvenMarking
      ↥(((⁅(mf'.component c).comap π, (mf'.component c).comap π⁆).map H.subtype : Subgroup G))
      (fun lab _ _ _ _ _ => lab = R.label c) := by
  have hYperf : ⁅mf'.component c, mf'.component c⁆ = mf'.component c :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 (mf'.marked c hc).1)
  obtain ⟨hmap, hperf⟩ := SpPlacement.derived_comap_perfect π hπ hker hYperf
  have hY : LargeEvenMarking ↥((⁅(mf'.component c).comap π, (mf'.component c).comap π⁆).map π)
      (fun lab _ _ _ _ _ => lab = R.label c) := by
    rw [hmap]
    exact mf'.marked c hc
  have hX := (SCFourCover.largeEvenMarking_map_iff hker hperf
    (fun lab => lab = R.label c)).2 hY
  exact largeEvenMarking_congr
    ((⁅(mf'.component c).comap π, (mf'.component c).comap π⁆).equivMapOfInjective H.subtype
      H.subtype_injective).symm (fun _ _ _ _ _ _ h => h) hX

private theorem mfc_map_mem_normalizer {G : Type} [Group G] {H E : Subgroup G} {M : Type}
    [Group M] (hEH : E ≤ H) (π : ↥H →* M) {x : ↥H}
    (hx : (x : G) ∈ Subgroup.normalizer (E : Set G)) :
    (π x : M) ∈ Subgroup.normalizer (((E.subgroupOf H).map π : Subgroup M) : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
    have haE : (a : G) ∈ E := Subgroup.mem_subgroupOf.mp ha
    have hxaE : (x : G) * (a : G) * (x : G)⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp hx (a : G)).1 haE
    have harg : Subgroup.inclusion hEH ⟨(x : G) * (a : G) * (x : G)⁻¹, hxaE⟩ =
        x * a * x⁻¹ := Subtype.ext rfl
    have hval : π x * π a * (π x)⁻¹ =
        π (Subgroup.inclusion hEH ⟨(x : G) * (a : G) * (x : G)⁻¹, hxaE⟩) := by
      rw [harg, map_mul, map_mul, map_inv]
    rw [hval]
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hxaE)
  · intro hz
    obtain ⟨a, ha, haz⟩ := Subgroup.mem_map.mp hz
    have haE : (a : G) ∈ E := Subgroup.mem_subgroupOf.mp ha
    have hbE : (x : G)⁻¹ * (a : G) * (x : G) ∈ E := by
      have hmem := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) (a : G)).1 haE
      simpa using hmem
    have harg : Subgroup.inclusion hEH ⟨(x : G)⁻¹ * (a : G) * (x : G), hbE⟩ =
        x⁻¹ * a * x := Subtype.ext rfl
    have hz_eq : z = π (Subgroup.inclusion hEH ⟨(x : G)⁻¹ * (a : G) * (x : G), hbE⟩) := by
      rw [harg, map_mul, map_mul, map_inv, haz]
      group
    rw [hz_eq]
    exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hbE)

private theorem mfc_automizer_map_le {G : Type} [Group G] [Finite G] {H E : Subgroup G} {M : Type}
    [Group M] (hEH : E ≤ H) (π : ↥H →* M)
    (hker3 : ¬ 3 ∣ Nat.card π.ker) (hEab : IsElemAbelian 3 E)
    (X : Subgroup ↥H) :
    (ggAutomizer (X.map H.subtype) E).map
        (MulAut.congr (mfc_cover_equiv hEH π hker3 hEab)).toMonoidHom ≤
      ggAutomizer (X.map π) ((E.subgroupOf H).map π) := by
  intro ψ hψ
  obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp hψ
  rw [mem_ggAutomizer_iff] at hφ
  obtain ⟨g, hg, hgN, hgφ⟩ := hφ
  rw [Subgroup.mem_map] at hg
  obtain ⟨x, hxX, rfl⟩ := hg
  refine mem_ggAutomizer_iff.mpr ⟨π x, Subgroup.mem_map.mpr ⟨x, hxX, rfl⟩, ?_, ?_⟩
  · exact mfc_map_mem_normalizer hEH π hgN
  · intro b
    change ((MulAut.congr (mfc_cover_equiv hEH π hker3 hEab) φ b :
      ↥((E.subgroupOf H).map π)) : M) = π x * (b : M) * (π x)⁻¹
    obtain ⟨a, rfl⟩ : ∃ a : ↥E, mfc_cover_equiv hEH π hker3 hEab a = b :=
      ⟨(mfc_cover_equiv hEH π hker3 hEab).symm b, MulEquiv.apply_symm_apply _ _⟩
    have hinh : Subgroup.inclusion hEH (φ a) = x * Subgroup.inclusion hEH a * x⁻¹ := by
      apply Subtype.ext
      change ((φ a : ↥E) : G) = H.subtype x * (a : G) * (H.subtype x)⁻¹
      exact hgφ a
    rw [mfc_mulAut_congr_apply, MulEquiv.symm_apply_apply, mfc_cover_equiv_apply, hinh,
      map_mul, map_mul, map_inv, mfc_cover_equiv_apply]

private theorem mfc_automizer_map_ge {G : Type} [Group G] [Finite G] {H E : Subgroup G} {M : Type}
    [Group M] (hEH : E ≤ H) (π : ↥H →* M)
    (hker : π.ker ≤ Subgroup.center ↥H) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEab : IsElemAbelian 3 E) (hCov : CoverComponents.AutomizerCoverEq)
    (X : Subgroup ↥H) :
    ggAutomizer (X.map π) ((E.subgroupOf H).map π) ≤
      (ggAutomizer (X.map H.subtype) E).map
        (MulAut.congr (mfc_cover_equiv hEH π hker3 hEab)).toMonoidHom := by
  intro ψ hψ
  rw [mem_ggAutomizer_iff] at hψ
  obtain ⟨y, hy, -, hyψ⟩ := hψ
  refine Subgroup.mem_map.mpr
    ⟨(MulAut.congr (mfc_cover_equiv hEH π hker3 hEab)).symm ψ, ?_,
      MulEquiv.apply_symm_apply _ ψ⟩
  refine (hCov hEH π (π.comp (Subgroup.inclusion hEH)) (fun a => rfl) ?_ hker hker3 X
    ((MulAut.congr (mfc_cover_equiv hEH π hker3 hEab)).symm ψ)).2 ⟨y, hy, fun a => ?_⟩
  · intro z
    exact ⟨1, Subtype.ext (by simpa using hEab.2 (z : G) z.2)⟩
  · rw [MonoidHom.comp_apply, mfc_mulAut_congr_symm, ← mfc_cover_equiv_apply hEH π hker3 hEab
      ((mfc_cover_equiv hEH π hker3 hEab).symm (ψ (mfc_cover_equiv hEH π hker3 hEab a))),
      MulEquiv.apply_symm_apply, hyψ, MonoidHom.comp_apply, mfc_cover_equiv_apply]

private theorem mfc_automizer_map {G : Type} [Group G] [Finite G] {H E : Subgroup G} {M : Type}
    [Group M] (hEH : E ≤ H) (π : ↥H →* M)
    (hker : π.ker ≤ Subgroup.center ↥H) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEab : IsElemAbelian 3 E) (hCov : CoverComponents.AutomizerCoverEq)
    (X : Subgroup ↥H) :
    (ggAutomizer (X.map H.subtype) E).map
        (MulAut.congr (mfc_cover_equiv hEH π hker3 hEab)).toMonoidHom =
      ggAutomizer (X.map π) ((E.subgroupOf H).map π) :=
  le_antisymm (mfc_automizer_map_le hEH π hker3 hEab X)
    (mfc_automizer_map_ge hEH π hker hker3 hEab hCov X)

private theorem mfc_normalizer_eq {G : Type} [Group G] [Finite G] {H E : Subgroup G} {M : Type}
    [Group M] {R : RawFrameData} (hEH : E ≤ H) (π : ↥H →* M) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥H) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hEab : IsElemAbelian 3 E) (hCov : CoverComponents.AutomizerCoverEq)
    (mf' : ModelFrame (⊤ : Subgroup M) ((E.subgroupOf H).map π) R)
    (c : R.Code) (hc : R.admissible c) :
    (ggAutomizer
        (((⁅(mf'.component c).comap π, (mf'.component c).comap π⁆).map H.subtype :
          Subgroup G)) E).map
        (ggLin (p := 3) (mfc_coord hEH π hker3 hEab mf')) = R.normalizerGroup c := by
  have hYperf : ⁅mf'.component c, mf'.component c⁆ = mf'.component c :=
    Subgroup.isPerfect_iff.1 (Group.isPerfect_def.2 (mf'.marked c hc).1)
  obtain ⟨hmap, -⟩ := SpPlacement.derived_comap_perfect π hπ hker hYperf
  calc
    (ggAutomizer
        (((⁅(mf'.component c).comap π, (mf'.component c).comap π⁆).map H.subtype :
          Subgroup G)) E).map (ggLin (p := 3) (mfc_coord hEH π hker3 hEab mf'))
        = (ggAutomizer
            (((⁅(mf'.component c).comap π, (mf'.component c).comap π⁆).map H.subtype :
              Subgroup G)) E).map ((ggLin (p := 3) mf'.coord).comp
                (MulAut.congr (mfc_cover_equiv hEH π hker3 hEab)).toMonoidHom) := by
            rw [mfc_ggLin_coord_comp]
    _ = ((ggAutomizer
            (((⁅(mf'.component c).comap π, (mf'.component c).comap π⁆).map H.subtype :
              Subgroup G)) E).map
                (MulAut.congr (mfc_cover_equiv hEH π hker3 hEab)).toMonoidHom).map
              (ggLin (p := 3) mf'.coord) := by
            rw [Subgroup.map_map]
    _ = (ggAutomizer (mf'.component c) ((E.subgroupOf H).map π)).map
          (ggLin (p := 3) mf'.coord) := by
            rw [mfc_automizer_map hEH π hker hker3 hEab hCov, hmap]
    _ = R.normalizerGroup c := mf'.normalizer_eq c hc

private theorem mfc_ambient_normalizer_eq {G : Type} [Group G] [Finite G] {H E : Subgroup G}
    {M : Type} [Group M] {R : RawFrameData} (hEH : E ≤ H) (π : ↥H →* M)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center ↥H)
    (hker3 : ¬ 3 ∣ Nat.card π.ker) (hEab : IsElemAbelian 3 E)
    (hCov : CoverComponents.AutomizerCoverEq)
    (mf' : ModelFrame (⊤ : Subgroup M) ((E.subgroupOf H).map π) R) :
    (ggAutomizer H E).map (ggLin (p := 3) (mfc_coord hEH π hker3 hEab mf')) =
      R.ambientNormalizer := by
  have htop : ((⊤ : Subgroup ↥H).map H.subtype) = H := by
    rw [Subgroup.map_top, Subgroup.subtype_range]
  have htop' : ((⊤ : Subgroup ↥H).map π) = (⊤ : Subgroup M) := by
    rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr hπ]
  calc
    (ggAutomizer H E).map (ggLin (p := 3) (mfc_coord hEH π hker3 hEab mf'))
        = (ggAutomizer ((⊤ : Subgroup ↥H).map H.subtype) E).map
            (ggLin (p := 3) (mfc_coord hEH π hker3 hEab mf')) := by rw [htop]
    _ = (ggAutomizer ((⊤ : Subgroup ↥H).map H.subtype) E).map
          ((ggLin (p := 3) mf'.coord).comp
            (MulAut.congr (mfc_cover_equiv hEH π hker3 hEab)).toMonoidHom) := by
          rw [mfc_ggLin_coord_comp]
    _ = ((ggAutomizer ((⊤ : Subgroup ↥H).map H.subtype) E).map
              (MulAut.congr (mfc_cover_equiv hEH π hker3 hEab)).toMonoidHom).map
            (ggLin (p := 3) mf'.coord) := by
          rw [Subgroup.map_map]
    _ = (ggAutomizer (⊤ : Subgroup M) ((E.subgroupOf H).map π)).map
          (ggLin (p := 3) mf'.coord) := by
          rw [mfc_automizer_map hEH π hker hker3 hEab hCov (⊤ : Subgroup ↥H), htop']
    _ = R.ambientNormalizer := mf'.ambientNormalizer_eq

private theorem mfc_occurs_iff {G : Type} [Group G] [Finite G] {H E : Subgroup G} {M : Type}
    [Group M] {R : RawFrameData} (hEH : E ≤ H) (π : ↥H →* M) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center ↥H) (hker3 : ¬ 3 ∣ Nat.card π.ker)
    (hHperf : commutator H = ⊤) (hEab : IsElemAbelian 3 E)
    (mf' : ModelFrame (⊤ : Subgroup M) ((E.subgroupOf H).map π) R)
    (A : Subgroup G) (hAE : A ≤ E) (X : Subgroup G) :
    Assembly.IsComponentOf X (H ⊓ Subgroup.centralizer (A : Set G)) ↔
      ∃ c : R.Code, R.admissible c ∧
        R.occurs (ggLinImage (p := 3) (mfc_coord hEH π hker3 hEab mf') A) c ∧
        X = ((⁅(mf'.component c).comap π, (mf'.component c).comap π⁆).map H.subtype :
          Subgroup G) := by
  have hAN : A ≤ Subgroup.normalizer (H : Set G) := (hAE.trans hEH).trans Subgroup.le_normalizer
  have hp : IsPGroup 3 ↥A := fun z =>
    ⟨1, Subtype.ext (by simpa using hEab.2 (z : G) (hAE z.2))⟩
  have hA'E' : (π.comp (Subgroup.inclusion (hAE.trans hEH))).range ≤ (E.subgroupOf H).map π := by
    rw [mfc_range_comp_inclusion (hAE.trans hEH) π]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hAE)
  have hcov := CoverComponents.isComponentOfCoverIff_holds hAN π
    (π.comp (Subgroup.inclusion (hAE.trans hEH))) hp hπ hker hker3 hHperf
    (mfc_equivariant hEH hAE π) X
  constructor
  · intro h
    rw [hcov] at h
    obtain ⟨Y, hY, rfl⟩ := h
    have hY' : Assembly.IsComponentOf Y (⊤ ⊓ Subgroup.centralizer
        (((π.comp (Subgroup.inclusion (hAE.trans hEH))).range : Subgroup M) : Set M)) := by
      simpa using hY
    obtain ⟨c, hc, hocc, rfl⟩ := (mf'.occurs_iff _ hA'E' Y).mp hY'
    exact ⟨c, hc, by rwa [mfc_ggLinImage_eq_range hEH π hker3 hEab mf' hAE], rfl⟩
  · rintro ⟨c, hc, hocc, rfl⟩
    rw [hcov]
    have hocc' : R.occurs (ggLinImage (p := 3) mf'.coord
        (π.comp (Subgroup.inclusion (hAE.trans hEH))).range) c := by
      rwa [mfc_ggLinImage_eq_range hEH π hker3 hEab mf' hAE] at hocc
    exact ⟨mf'.component c, by
      simpa using (mf'.occurs_iff _ hA'E' (mf'.component c)).mpr ⟨c, hc, hocc', rfl⟩, rfl⟩

theorem modelFrameOfCover_holds : ModelFrameOfCover := by
  intro G _ _ H E M _ R hEH π hπ hker hker3 hHperf hEab mf'
  refine ⟨{ coord := mfc_coord hEH π hker3 hEab mf'
            component := fun c =>
              (⁅(mf'.component c).comap π, (mf'.component c).comap π⁆).map H.subtype
            component_le := ?_
            marked := mfc_marked π hπ hker mf'
            occurs_iff := mfc_occurs_iff hEH π hπ hker hker3 hHperf hEab mf'
            cent_eq := mfc_cent_eq hEH π hπ hker hker3 hEab mf'
            inside_eq := mfc_inside_eq hEH π hπ hker hker3 hEab mf'
            normalizer_eq := mfc_normalizer_eq hEH π hπ hker hker3 hEab
              CoverComponents.automizerCoverEq_holds mf'
            ambientNormalizer_eq := mfc_ambient_normalizer_eq hEH π hπ hker hker3 hEab
              CoverComponents.automizerCoverEq_holds mf' }⟩
  intro c _ z hz
  obtain ⟨y, -, rfl⟩ := Subgroup.mem_map.mp hz
  exact y.2

end CFSG.StandardType.GGQ2Frame
