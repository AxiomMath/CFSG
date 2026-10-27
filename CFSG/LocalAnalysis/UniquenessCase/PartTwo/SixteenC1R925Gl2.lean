module

public import CFSG.Quasithin.Background.DicksonPerfectSL2
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Models.PGLSimple
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalJ
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CharacterTheory.Semidihedral.ProjectiveSL2Cover
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Co2Cert.Order
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private lemma r925_three_dvd_mul_sq_sub_one (p : ℕ) : 3 ∣ p * (p ^ 2 - 1) := by
  rw [Nat.dvd_iff_mod_eq_zero]
  have hp3 : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hp3 with h | h | h
  · rw [Nat.mul_mod, h]; omega
  · have hp2 : p ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h]
    have h2 : (p ^ 2 - 1) % 3 = 0 := by omega
    rw [Nat.mul_mod, h, h2]
  · have hp2 : p ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h]
    have h2 : (p ^ 2 - 1) % 3 = 0 := by omega
    rw [Nat.mul_mod, h, h2]

private lemma r925_card_sl2 (p : ℕ) [Fact p.Prime] :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) = p * (p ^ 2 - 1) := by
  rw [← CFSG.Open.StatedAPI.card_statedSL 2 (ZMod p), CFSG.Open.StatedAPI.card_statedSL_two,
    Nat.card_zmod]

private lemma r925_three_dvd_card_sl2 {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
  rw [r925_card_sl2]
  exact r925_three_dvd_mul_sq_sub_one p

private lemma r925_card_center_sl2 {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) :
    Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) = 2 := by
  refine CFSG.Semidihedral.ProjectiveSL2Cover.center_card (ZMod p) ?_
  rw [ZMod.ringChar_zmod_n]
  omega

private lemma r925_range_le_toGL {K : Type} [Group K] (hK : commutator K = ⊤)
    {p : ℕ} [Fact p.Prime] (ψ : K →* GL (Fin 2) (ZMod p)) :
    ψ.range ≤ (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* GL (Fin 2) (ZMod p)).range := by
  rw [← CFSG.Open.StatedAPI.statedSL_eq_range_toGL 2 (ZMod p)]
  intro g hg
  rw [CFSG.Open.StatedAPI.mem_statedSL_iff]
  obtain ⟨k, rfl⟩ := MonoidHom.mem_range.1 hg
  have hker : ((Matrix.GeneralLinearGroup.det :
      GL (Fin 2) (ZMod p) →* (ZMod p)ˣ).comp ψ).ker = ⊤ := by
    rw [eq_top_iff, ← hK]
    exact Abelianization.commutator_subset_ker _
  have h1 : (Matrix.GeneralLinearGroup.det (ψ k) : ZMod p) = 1 := by
    have hmem : k ∈ ((Matrix.GeneralLinearGroup.det :
        GL (Fin 2) (ZMod p) →* (ZMod p)ˣ).comp ψ).ker := by
      rw [hker]; exact Subgroup.mem_top _
    have h2 : ((Matrix.GeneralLinearGroup.det :
        GL (Fin 2) (ZMod p) →* (ZMod p)ˣ).comp ψ) k = 1 := MonoidHom.mem_ker.mp hmem
    rw [MonoidHom.comp_apply] at h2
    rw [h2, Units.val_one]
  rwa [Matrix.GeneralLinearGroup.val_det_apply] at h1

private def r925_sl2Preimage {K : Type} [Group K] {p : ℕ} (ψ : K →* GL (Fin 2) (ZMod p)) :
    Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
  ψ.range.comap (Matrix.SpecialLinearGroup.toGL :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* GL (Fin 2) (ZMod p))

private lemma r925_sl2Preimage_map {K : Type} [Group K] (hK : commutator K = ⊤)
    {p : ℕ} [Fact p.Prime] (ψ : K →* GL (Fin 2) (ZMod p)) :
    (r925_sl2Preimage ψ).map (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* GL (Fin 2) (ZMod p)) = ψ.range :=
  Subgroup.map_comap_eq_self (r925_range_le_toGL hK ψ)

private lemma r925_sl2Preimage_commutator {K : Type} [Group K] (hK : commutator K = ⊤)
    {p : ℕ} [Fact p.Prime] (ψ : K →* GL (Fin 2) (ZMod p)) :
    ⁅r925_sl2Preimage ψ, r925_sl2Preimage ψ⁆ = r925_sl2Preimage ψ := by
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hK
  have hmap := Subgroup.map_commutator (r925_sl2Preimage ψ) (r925_sl2Preimage ψ)
    (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* GL (Fin 2) (ZMod p))
  rw [r925_sl2Preimage_map hK ψ] at hmap
  haveI : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
  rw [Subgroup.commutator_eq_self (H := ψ.range)] at hmap
  rw [← r925_sl2Preimage_map hK ψ] at hmap
  exact Subgroup.map_injective Matrix.SpecialLinearGroup.toGL_injective hmap

private lemma r925_card_sl2Preimage {K : Type} [Group K] (hK : commutator K = ⊤)
    {p : ℕ} [Fact p.Prime] (ψ : K →* GL (Fin 2) (ZMod p)) :
    Nat.card ↥(r925_sl2Preimage ψ) = Nat.card ↥ψ.range := by
  rw [← r925_sl2Preimage_map hK ψ]
  exact (Subgroup.card_map_of_injective (K := r925_sl2Preimage ψ)
    Matrix.SpecialLinearGroup.toGL_injective).symm

private lemma r925_range_eq_toGL_range {K : Type} [Group K] (hK : commutator K = ⊤)
    {p : ℕ} [Fact p.Prime] (ψ : K →* GL (Fin 2) (ZMod p))
    (htop : r925_sl2Preimage ψ = ⊤) :
    ψ.range = (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* GL (Fin 2) (ZMod p)).range := by
  rw [← r925_sl2Preimage_map hK ψ, htop, Subgroup.map_top]

private lemma r925_card_range_of_top {K : Type} [Group K] (hK : commutator K = ⊤)
    {p : ℕ} [Fact p.Prime] (ψ : K →* GL (Fin 2) (ZMod p))
    (htop : r925_sl2Preimage ψ = ⊤) :
    Nat.card ↥ψ.range = Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
  rw [r925_range_eq_toGL_range hK ψ htop]
  exact (Nat.card_congr (MonoidHom.ofInjective
    Matrix.SpecialLinearGroup.toGL_injective).toEquiv).symm

private lemma r925_card_range_of_equiv_sl2five {K : Type} [Group K] (hK : commutator K = ⊤)
    {p : ℕ} [Fact p.Prime] (ψ : K →* GL (Fin 2) (ZMod p))
    (e : r925_sl2Preimage ψ ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 5)) :
    Nat.card ↥ψ.range = 120 := by
  have h1 : Nat.card ↥(r925_sl2Preimage ψ) = 120 := by
    rw [Nat.card_congr e.toEquiv, r925_card_sl2 5]
    norm_num
  rw [← r925_card_sl2Preimage hK ψ, h1]

private noncomputable def r925_equiv_range_of_top {K : Type} [Group K]
    (hK : commutator K = ⊤) {p : ℕ} [Fact p.Prime] (ψ : K →* GL (Fin 2) (ZMod p))
    (htop : r925_sl2Preimage ψ = ⊤) :
    Matrix.SpecialLinearGroup (Fin 2) (ZMod p) ≃* ↥ψ.range := by
  have hrange := r925_range_eq_toGL_range hK ψ htop
  refine MulEquiv.ofBijective
    ((Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* GL (Fin 2) (ZMod p)).codRestrict
        ψ.range (fun x => ?_)) ?_
  · rw [hrange]; exact ⟨x, rfl⟩
  · constructor
    · intro x y hxy
      exact Matrix.SpecialLinearGroup.toGL_injective (Subtype.ext_iff.mp hxy)
    · intro y
      have hy : (y : GL (Fin 2) (ZMod p)) ∈ (Matrix.SpecialLinearGroup.toGL :
          Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* GL (Fin 2) (ZMod p)).range := by
        rw [← hrange]; exact y.2
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hy
      exact ⟨x, Subtype.ext hx⟩

private noncomputable def r925_equiv_sl2Preimage_range {K : Type} [Group K]
    (hK : commutator K = ⊤) {p : ℕ} [Fact p.Prime] (ψ : K →* GL (Fin 2) (ZMod p)) :
    ↥(r925_sl2Preimage ψ) ≃* ↥ψ.range := by
  have hrange := r925_sl2Preimage_map hK ψ
  refine MulEquiv.ofBijective
    (((Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* GL (Fin 2) (ZMod p)).comp
        (r925_sl2Preimage ψ).subtype).codRestrict ψ.range (fun x => ?_)) ?_
  · rw [← hrange]
    exact Subgroup.mem_map_of_mem _ x.2
  · constructor
    · intro x y hxy
      exact Subtype.ext (Matrix.SpecialLinearGroup.toGL_injective (Subtype.ext_iff.mp hxy))
    · intro y
      have hy : (y : GL (Fin 2) (ZMod p)) ∈ (r925_sl2Preimage ψ).map
          (Matrix.SpecialLinearGroup.toGL :
            Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* GL (Fin 2) (ZMod p)) := by
        rw [hrange]; exact y.2
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.1 hy
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩

private lemma r925_card_normal_sl2_dvd_two {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p)
    (N' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) [N'.Normal]
    (h3 : ∀ n ∈ N', ¬ 3 ∣ orderOf n) : Nat.card N' ∣ 2 := by
  have h4 : 4 ≤ Nat.card (ZMod p) := by rw [Nat.card_zmod]; omega
  rcases CFSG.ABGTheoremB.TotallyInverted.Sec11.sl2_normal_eq_top_or_le_center h4 N'
    inferInstance with h | h
  · exfalso
    have h3top : 3 ∣ Nat.card N' := by
      rw [h]
      simpa using r925_three_dvd_card_sl2 (p := p) hp
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3top
    exact h3 x x.2 (by simpa [hx] using dvd_refl 3)
  · exact (Subgroup.card_dvd_of_le h).trans (by rw [r925_card_center_sl2 hp])

private lemma r925_card_range_of_top_dvd_two {K : Type} [Group K] (hK : commutator K = ⊤)
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) (ψ : K →* GL (Fin 2) (ZMod p))
    (htop : r925_sl2Preimage ψ = ⊤) (N : Subgroup ↥ψ.range) [N.Normal]
    (hN3 : ∀ n ∈ N, ¬ 3 ∣ orderOf n) : Nat.card N ∣ 2 := by
  let e := r925_equiv_range_of_top hK ψ htop
  let N' : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := N.comap e.toMonoidHom
  haveI hN'normal : N'.Normal := (inferInstance : N.Normal).comap e.toMonoidHom
  have hN'3 : ∀ n ∈ N', ¬ 3 ∣ orderOf n := by
    intro n hn h3
    exact hN3 (e n) hn (by rw [MulEquiv.orderOf_eq e n]; exact h3)
  have hdvd := r925_card_normal_sl2_dvd_two hp N' hN'3
  have hcard : Nat.card N' = Nat.card N := by
    have h1 : N' = N.map e.symm := Subgroup.comap_equiv_eq_map_symm e N
    rw [h1]
    exact Subgroup.card_map_of_injective e.symm.injective
  rwa [hcard] at hdvd

private lemma r925_normal_3free_ne_top {B : Type} [Group B] [Finite B] (N : Subgroup B)
    [N.Normal] (hN3 : ∀ n ∈ N, ¬ 3 ∣ orderOf n) (hB3 : 3 ∣ Nat.card B) : N ≠ ⊤ := by
  intro htop
  have h3N : 3 ∣ Nat.card N := by
    rw [htop]
    simpa using hB3
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h3N
  exact hN3 x x.2 (by simpa [hx] using dvd_refl 3)

private lemma r925_quotient_card_eq {K : Type} [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime] (ψ : K →* GL (Fin 2) (ZMod p)) (W : Subgroup K) [W.Normal]
    (hsimple : IsSimpleGroup (K ⧸ W)) (hNne : W.map ψ.rangeRestrict ≠ ⊤) :
    Nat.card (↥ψ.range ⧸ W.map ψ.rangeRestrict) = Nat.card (K ⧸ W) := by
  let N : Subgroup ↥ψ.range := W.map ψ.rangeRestrict
  haveI hNnormal : N.Normal :=
    Subgroup.Normal.map (inferInstance : W.Normal) ψ.rangeRestrict
      ψ.rangeRestrict_surjective
  have hle : W ≤ N.comap ψ.rangeRestrict := fun w hw => Subgroup.mem_map_of_mem _ hw
  let φ : K ⧸ W →* ↥ψ.range ⧸ N := QuotientGroup.map W N ψ.rangeRestrict hle
  have hsurj : Function.Surjective φ :=
    QuotientGroup.map_surjective_of_surjective W N ψ.rangeRestrict
      ((QuotientGroup.mk'_surjective N).comp ψ.rangeRestrict_surjective) hle
  have hker : φ.ker = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact h
    · exfalso
      apply hNne
      rw [eq_top_iff]
      intro b _
      obtain ⟨k, rfl⟩ := ψ.rangeRestrict_surjective b
      have hmem : QuotientGroup.mk' W k ∈ φ.ker := by rw [h]; exact Subgroup.mem_top _
      have h1 : φ (QuotientGroup.mk' W k) = 1 := MonoidHom.mem_ker.mp hmem
      rw [QuotientGroup.map_mk'] at h1
      exact (QuotientGroup.eq_one_iff _).1 h1
  have hinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
  exact (Nat.card_congr (MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).toEquiv).symm

private lemma r925_le_center_of_normal_card_two {B : Type} [Group B] (N : Subgroup B) [N.Normal]
    (hN : Nat.card N = 2) : N ≤ Subgroup.center B := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : N)).mp hN
  intro n hn
  rw [Subgroup.mem_center_iff]
  intro b
  by_cases hn1 : n = 1
  · rw [hn1, mul_one, one_mul]
  · have hnne : (⟨n, hn⟩ : N) ≠ 1 := fun h => hn1 (Subtype.ext_iff.mp h)
    have hconj : b * n * b⁻¹ ∈ N := (inferInstance : N.Normal).conj_mem n hn b
    have hconjne : (⟨b * n * b⁻¹, hconj⟩ : N) ≠ 1 := by
      intro h
      have hval : b * n * b⁻¹ = 1 := congrArg Subtype.val h
      apply hn1
      have h2 := congrArg (fun x => b⁻¹ * x * b) hval
      simpa [mul_assoc] using h2
    have e1 : (⟨n, hn⟩ : N) = y := huniq _ hnne
    have e2 : (⟨b * n * b⁻¹, hconj⟩ : N) = y := huniq _ hconjne
    have hbn : b * n * b⁻¹ = n := by
      have h1 : b * n * b⁻¹ = (y : B) := Subtype.ext_iff.mp e2
      have h2 : n = (y : B) := Subtype.ext_iff.mp e1
      rw [h1, h2]
    calc b * n = (b * n * b⁻¹) * b := by group
      _ = n * b := by rw [hbn]

private lemma r925_le_center_of_dvd_two {B : Type} [Group B] (N : Subgroup B) [N.Normal]
    (h : Nat.card N ∣ 2) : N ≤ Subgroup.center B := by
  rcases (Nat.dvd_prime Nat.prime_two).mp h with h1 | h2
  · rw [Subgroup.eq_bot_of_card_eq N h1]; exact bot_le
  · exact r925_le_center_of_normal_card_two N h2

private lemma r925_comm_of_le_center {K : Type} [Group K] {p : ℕ} [Fact p.Prime]
    (ψ : K →* GL (Fin 2) (ZMod p)) (W : Subgroup K) [W.Normal]
    (h : W.map ψ.rangeRestrict ≤ Subgroup.center ↥ψ.range) :
    ∀ w ∈ W, ∀ k : K, ψ w * ψ k = ψ k * ψ w := by
  intro w hw k
  have hwN : ψ.rangeRestrict w ∈ W.map ψ.rangeRestrict := Subgroup.mem_map_of_mem _ hw
  have hc := (Subgroup.mem_center_iff.mp (h hwN)) (ψ.rangeRestrict k)
  have h1 : ψ.range.subtype (ψ.rangeRestrict w * ψ.rangeRestrict k) =
      ψ.range.subtype (ψ.rangeRestrict k * ψ.rangeRestrict w) := congrArg _ hc.symm
  simpa using h1

private lemma r925_isSimpleGroup_of_isL3Five {X : Type} [Group X] (h : IsL3Five X) :
    IsSimpleGroup X := by
  rcases h with ⟨-, hsc⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
  · obtain ⟨-, K, _, _, _, ⟨e⟩⟩ := hsc
    haveI : IsSimpleGroup (StatedProj (StatedSL 3 K)) :=
      CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL K (by norm_num) (by omega) (by omega)
    exact e.isSimpleGroup
  all_goals omega

private lemma r925_card_of_isL3Five {X : Type} [Group X] (h : IsL3Five X) :
    Nat.card X = 372000 := by
  rcases h with ⟨-, hsc⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩ | ⟨h0, -, -⟩
  · exact CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_five hsc
  all_goals omega

private lemma r925_isSimpleGroup_of_isAlt {X : Type} [Group X] (h : IsAlt X 5) :
    IsSimpleGroup X := by
  obtain ⟨e⟩ := h
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  exact e.isSimpleGroup

private lemma r925_card_of_isAlt {X : Type} [Group X] (h : IsAlt X 5) :
    Nat.card X = 60 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Dickson.card_alt_five]

private noncomputable def r925_equiv_sl2_statedSL (F : Type) [Field F] :
    Matrix.SpecialLinearGroup (Fin 2) F ≃* ↥(StatedSL 2 F) :=
  (MonoidHom.ofInjective (Matrix.SpecialLinearGroup.toGL_injective (n := Fin 2) (R := F))).trans
    (MulEquiv.subgroupCongr (CFSG.Open.StatedAPI.statedSL_eq_range_toGL 2 F)).symm

theorem r925_gl2_trivial_of_l35 {K : Type} [Group K] [Finite K]
    (hK : commutator K = ⊤) (W : Subgroup K) [W.Normal] (hW : ∀ w ∈ W, ¬ 3 ∣ orderOf w)
    (hq : IsL3Five (K ⧸ W)) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ψ : K →* GL (Fin 2) (ZMod p)) : ψ = 1 := by
  by_contra hψ
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hK
  have hBne : ψ.range ≠ ⊥ := fun h => hψ ((MonoidHom.range_eq_bot_iff).mp h)
  have hB'map : (r925_sl2Preimage ψ).map (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* GL (Fin 2) (ZMod p)) = ψ.range :=
    r925_sl2Preimage_map hK ψ
  have hB'perf : ⁅r925_sl2Preimage ψ, r925_sl2Preimage ψ⁆ = r925_sl2Preimage ψ :=
    r925_sl2Preimage_commutator hK ψ
  have hB'ne : r925_sl2Preimage ψ ≠ ⊥ := by
    intro h
    exact hBne (by rw [← hB'map, h, Subgroup.map_bot])
  let N : Subgroup ↥ψ.range := W.map ψ.rangeRestrict
  haveI hNnormal : N.Normal :=
    Subgroup.Normal.map (inferInstance : W.Normal) ψ.rangeRestrict
      ψ.rangeRestrict_surjective
  have hN3 : ∀ n ∈ N, ¬ 3 ∣ orderOf n := by
    intro n hn h3
    rw [Subgroup.mem_map] at hn
    obtain ⟨w, hw, rfl⟩ := hn
    exact hW w hw (h3.trans (orderOf_map_dvd ψ.rangeRestrict w))
  have hsimple : IsSimpleGroup (K ⧸ W) := r925_isSimpleGroup_of_isL3Five hq
  have hcardKW : Nat.card (K ⧸ W) = 372000 := r925_card_of_isL3Five hq
  rcases Dickson.perfect_subgroup_sl2_prime hp hB'perf hB'ne with htop | ⟨⟨e⟩, -, -, -, -⟩
  · have hB3 : 3 ∣ Nat.card ↥ψ.range := by
      rw [r925_card_range_of_top hK ψ htop]
      exact r925_three_dvd_card_sl2 (p := p) hp
    have hNne : N ≠ ⊤ := r925_normal_3free_ne_top N hN3 hB3
    have hcardBN : Nat.card (↥ψ.range ⧸ N) = 372000 :=
      (r925_quotient_card_eq ψ W hsimple hNne).trans hcardKW
    have hNcard : Nat.card N ∣ 2 := r925_card_range_of_top_dvd_two hK hp ψ htop N hN3
    have horder : Nat.card ↥ψ.range = Nat.card (↥ψ.range ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hpcard : p * (p ^ 2 - 1) = 372000 * Nat.card N := by
      rw [← r925_card_sl2 p, ← r925_card_range_of_top hK ψ htop, horder, hcardBN]
    have hNpos : 1 ≤ Nat.card N := Nat.card_pos
    have hNle : Nat.card N ≤ 2 := Nat.le_of_dvd (by norm_num) hNcard
    have hp_le : p ≤ 100 := by
      by_contra h
      have h101 : 101 ≤ p := by omega
      have hmono : 101 * (101 ^ 2 - 1) ≤ p * (p ^ 2 - 1) := by
        refine Nat.mul_le_mul h101 ?_
        have : 101 ^ 2 ≤ p ^ 2 := by nlinarith
        omega
      rw [hpcard] at hmono
      norm_num at hmono
      omega
    interval_cases p <;> omega
  · have hBcard : Nat.card ↥ψ.range = 120 := r925_card_range_of_equiv_sl2five hK ψ e
    have hB3 : 3 ∣ Nat.card ↥ψ.range := by rw [hBcard]; norm_num
    have hNne : N ≠ ⊤ := r925_normal_3free_ne_top N hN3 hB3
    have hcardBN : Nat.card (↥ψ.range ⧸ N) = 372000 :=
      (r925_quotient_card_eq ψ W hsimple hNne).trans hcardKW
    have horder : Nat.card ↥ψ.range = Nat.card (↥ψ.range ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [hBcard, hcardBN] at horder
    omega

theorem r925_gl2_of_a5 {K : Type} [Group K] [Finite K]
    (hK : commutator K = ⊤) (W : Subgroup K) [W.Normal] (hW : ∀ w ∈ W, ¬ 3 ∣ orderOf w)
    (hq : IsAlt (K ⧸ W) 5) (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p)
    (ψ : K →* GL (Fin 2) (ZMod p)) :
    ψ = 1 ∨ (IsSL2Prime ↥ψ.range 5 ∧ ∀ w ∈ W, ∀ k : K, ψ w * ψ k = ψ k * ψ w) := by
  by_cases hψ : ψ = 1
  · exact Or.inl hψ
  right
  haveI : Group.IsPerfect K := Group.isPerfect_def.mpr hK
  have hBne : ψ.range ≠ ⊥ := fun h => hψ ((MonoidHom.range_eq_bot_iff).mp h)
  have hB'map : (r925_sl2Preimage ψ).map (Matrix.SpecialLinearGroup.toGL :
      Matrix.SpecialLinearGroup (Fin 2) (ZMod p) →* GL (Fin 2) (ZMod p)) = ψ.range :=
    r925_sl2Preimage_map hK ψ
  have hB'perf : ⁅r925_sl2Preimage ψ, r925_sl2Preimage ψ⁆ = r925_sl2Preimage ψ :=
    r925_sl2Preimage_commutator hK ψ
  have hB'ne : r925_sl2Preimage ψ ≠ ⊥ := by
    intro h
    exact hBne (by rw [← hB'map, h, Subgroup.map_bot])
  let N : Subgroup ↥ψ.range := W.map ψ.rangeRestrict
  haveI hNnormal : N.Normal :=
    Subgroup.Normal.map (inferInstance : W.Normal) ψ.rangeRestrict
      ψ.rangeRestrict_surjective
  have hN3 : ∀ n ∈ N, ¬ 3 ∣ orderOf n := by
    intro n hn h3
    rw [Subgroup.mem_map] at hn
    obtain ⟨w, hw, rfl⟩ := hn
    exact hW w hw (h3.trans (orderOf_map_dvd ψ.rangeRestrict w))
  have hsimple : IsSimpleGroup (K ⧸ W) := r925_isSimpleGroup_of_isAlt hq
  have hcardKW : Nat.card (K ⧸ W) = 60 := r925_card_of_isAlt hq
  rcases Dickson.perfect_subgroup_sl2_prime hp hB'perf hB'ne with htop | ⟨⟨e⟩, -, -, -, -⟩
  · have hB3 : 3 ∣ Nat.card ↥ψ.range := by
      rw [r925_card_range_of_top hK ψ htop]
      exact r925_three_dvd_card_sl2 (p := p) hp
    have hNne : N ≠ ⊤ := r925_normal_3free_ne_top N hN3 hB3
    have hcardBN : Nat.card (↥ψ.range ⧸ N) = 60 :=
      (r925_quotient_card_eq ψ W hsimple hNne).trans hcardKW
    have hNcard : Nat.card N ∣ 2 := r925_card_range_of_top_dvd_two hK hp ψ htop N hN3
    have horder : Nat.card ↥ψ.range = Nat.card (↥ψ.range ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hpcard : p * (p ^ 2 - 1) = 60 * Nat.card N := by
      rw [← r925_card_sl2 p, ← r925_card_range_of_top hK ψ htop, horder, hcardBN]
    have hNle : Nat.card N ≤ 2 := Nat.le_of_dvd (by norm_num) hNcard
    have hp_le6 : p ≤ 6 := by
      by_contra h
      have hp7 : 7 ≤ p := by omega
      have hmono : 7 * (7 ^ 2 - 1) ≤ p * (p ^ 2 - 1) := by
        refine Nat.mul_le_mul hp7 ?_
        have : 7 ^ 2 ≤ p ^ 2 := by nlinarith
        omega
      rw [hpcard] at hmono
      norm_num at hmono
      omega
    have hp5 : p = 5 := by
      have hp_prime : Nat.Prime p := Fact.out
      have h56 : p = 5 ∨ p = 6 := by omega
      rcases h56 with h | h
      · exact h
      · exfalso
        rw [h] at hp_prime
        norm_num at hp_prime
    have hNcenter : N ≤ Subgroup.center ↥ψ.range := r925_le_center_of_dvd_two N hNcard
    have hIsSL : IsSL2Prime ↥ψ.range 5 := by
      refine ⟨ZMod p, inferInstance, inferInstance, by rw [Nat.card_zmod, hp5], ?_⟩
      exact ⟨MulEquiv.subgroupCongr ((r925_range_eq_toGL_range hK ψ htop).trans
        (CFSG.Open.StatedAPI.statedSL_eq_range_toGL 2 (ZMod p)).symm)⟩
    exact ⟨hIsSL, r925_comm_of_le_center ψ W hNcenter⟩
  · have hBcard : Nat.card ↥ψ.range = 120 := r925_card_range_of_equiv_sl2five hK ψ e
    have hB3 : 3 ∣ Nat.card ↥ψ.range := by rw [hBcard]; norm_num
    have hNne : N ≠ ⊤ := r925_normal_3free_ne_top N hN3 hB3
    have hcardBN : Nat.card (↥ψ.range ⧸ N) = 60 :=
      (r925_quotient_card_eq ψ W hsimple hNne).trans hcardKW
    have horder : Nat.card ↥ψ.range = Nat.card (↥ψ.range ⧸ N) * Nat.card N :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup N
    have hN2 : Nat.card N = 2 := by
      rw [hBcard, hcardBN] at horder
      omega
    have hNcenter : N ≤ Subgroup.center ↥ψ.range := r925_le_center_of_normal_card_two N hN2
    have hIsSL : IsSL2Prime ↥ψ.range 5 := by
      refine ⟨ZMod 5, inferInstance, inferInstance, by rw [Nat.card_zmod], ?_⟩
      exact ⟨(r925_equiv_sl2Preimage_range hK ψ).symm.trans
        (e.trans (r925_equiv_sl2_statedSL (ZMod 5)))⟩
    exact ⟨hIsSL, r925_comm_of_le_center ψ W hNcenter⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
