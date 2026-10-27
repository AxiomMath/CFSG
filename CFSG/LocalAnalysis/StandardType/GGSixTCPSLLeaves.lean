module

public import CFSG.LocalAnalysis.StandardType.TableC.HypDefs
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSLAux
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSLScalar
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSLBlock
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSLMatrix
public import CFSG.LocalAnalysis.StandardType.GGSixTCMarkDict
public import CFSG.LocalAnalysis.StandardType.GGSixLSixSevenCentJLieKnown
public import CFSG.LocalAnalysis.StandardType.GGLinearSemisimple
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotCatTypeDet
public import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TypeDet
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSL
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.BlockModelPSL
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs

public section

namespace CFSG.StandardType.TableCRes

section TwoLe

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

private lemma tcPSL_false_of_solvable_image {G Y : Type} [Group G] [Group.IsSolvable G] [Group Y]
    (θ : G →* Y) (H : Subgroup Y) (hH : θ.range = H)
    (hq : CFSG.Assembly.IsQuasisimple ↥H) : False := by
  subst hH
  have : Group.IsSolvable ↥(θ.range) := Group.isSolvable_of_surjective θ.rangeRestrict_surjective
  exact CFSG.StandardType.LinSemisimple.false_of_isQuasisimple_of_le_isSolvable hq le_rfl

private lemma tcPSL_nontrivial_of_quasisimple {G : Type} [Group G]
    (hq : CFSG.Assembly.IsQuasisimple G) : Nontrivial G := by
  have : Nontrivial (G ⧸ Subgroup.center G) := hq.2.toNontrivial
  exact (QuotientGroup.mk_surjective :
    Function.Surjective (QuotientGroup.mk : G → G ⧸ Subgroup.center G)).nontrivial

private lemma tcPSL_pow_two_eq_two {f : ℕ} (h : 2 ^ f = 2) : f = 1 := by
  have h' : 2 ^ f = 2 ^ 1 := by rw [h, pow_one]
  exact Nat.pow_right_injective (le_refl 2) h'

section WP1

variable {X : Type} [Group X] {m f p : ℕ}
  {G₀ B D J L : Subgroup X} {x : X}

local notation "𝔽" => GaloisField 2 f
local notation "SLm" => Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)

theorem two_le_blockDegree_PSL
    [Finite X]
    {ψ : (ggU .PSL (m + 1) f).K →* X} (h : GGTCHyp .PSL (m + 1) f ψ p G₀ B D J L x)
    {S : Set (GL (Fin (m + 1)) 𝔽)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    {J' : Subgroup SLm} {e : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽}
    (he : IsPrimIdemIn (Algebra.adjoin 𝔽 (Units.val '' S)) e)
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆) (hJ : J'.map ψ = J)
    (hF : GGSixLSevenFieldExtCase J .PSL f) :
    2 ≤ blockDegree (Algebra.adjoin 𝔽 (Units.val '' S)) e := by
  by_contra hlt
  have hdeg : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2 := by
    omega
  obtain ⟨k, ι, β₀, v, φ, v', φ', -, hcenter, hιr, -, -, -, -, -, -⟩ :=
    exists_blockModel_PSL m f S hS he hdeg hJe
  have hf1le : 1 ≤ f := by
    have hadm := h.adm
    unfold StatedLieAdmissible at hadm
    exact hadm.2.1
  have hf0 : f ≠ 0 := by omega
  have hθr : (ψ.comp ι).range = J := by
    rw [MonoidHom.range_comp, hιr, hJ]
  have hθker : (ψ.comp ι).ker ≤ Subgroup.center (ggU .PSL (k + 1) f).K := by
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hy
    exact hcenter y (h.ker (by rw [MonoidHom.mem_ker]; exact hy))
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := h.j_comp.2.2
  have : Nontrivial ↥J := tcPSL_nontrivial_of_quasisimple hJq
  have h2k : 2 ≤ k + 1 := by
    by_contra hk
    have : Subsingleton (ggU .PSL (k + 1) f).K :=
      CFSG.StandardType.subsingleton_specialLinear_of_card_le_one (Q := GaloisField 2 f)
        (by rw [Fintype.card_fin]; omega)
    have hsub : Subsingleton ↥J := by
      rw [← hθr]
      refine Subsingleton.intro fun a b => Subtype.ext ?_
      obtain ⟨y, hy⟩ := MonoidHom.mem_range.mp a.2
      obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp b.2
      rw [← hy, ← hz, Subsingleton.elim y z]
    exact (not_nontrivial_iff_subsingleton.mpr hsub) ‹Nontrivial ↥J›
  have hnot22 : ¬ (k + 1 = 2 ∧ f = 1) := by
    rintro ⟨hk2, hf1⟩
    have : Group.IsSolvable (ggU .PSL (k + 1) f).K :=
      CFSG.StandardType.isSolvable_specialLinear_of_card_eq_two (ι := Fin (k + 1))
        (Q := GaloisField 2 f) (by rw [Fintype.card_fin]; exact hk2)
        (by rw [GaloisField.card 2 f hf0, hf1, pow_one])
    exact tcPSL_false_of_solvable_image (ψ.comp ι) J hθr hJq
  have h22 : Fintype.card (Fin (k + 1)) ≠ 2 ∨ Nat.card (GaloisField 2 f) ≠ 2 := by
    rw [Fintype.card_fin, GaloisField.card 2 f hf0]
    by_cases hk2 : k + 1 = 2
    · right
      intro hpow
      exact hnot22 ⟨hk2, tcPSL_pow_two_eq_two hpow⟩
    · exact Or.inl hk2
  have hqSL : CFSG.Assembly.IsQuasisimple
      (Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 f)) :=
    CFSG.StandardType.isQuasisimple_specialLinear (ι := Fin (k + 1)) (Q := GaloisField 2 f)
      (by rw [Fintype.card_fin]; exact h2k) h22
  have : Group.IsPerfect (ggU .PSL (k + 1) f).K := ⟨hqSL.1⟩
  obtain ⟨eJ⟩ := quotCenter_mulEquiv_of_perfect (ψ.comp ι) hθker J hθr
  have hPSL : Nonempty (↥J ⧸ Subgroup.center ↥J ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL (k + 1) (GaloisField 2 f))) :=
    ⟨eJ.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj
      (k + 1) (GaloisField 2 f))⟩
  have hadm : CFSG.Open.StatedLieAdmissible .PSL (k + 1) 2 f := by
    unfold CFSG.Open.StatedLieAdmissible
    refine ⟨Nat.prime_two, by omega, h2k, ?_, ?_⟩
    · intro heq
      exact hnot22 ⟨(Prod.mk.inj heq).1, tcPSL_pow_two_eq_two (Prod.mk.inj heq).2⟩
    · intro heq
      have h2d : 2 ∣ 2 ^ f := dvd_pow_self 2 hf0
      rw [(Prod.mk.inj heq).2] at h2d
      norm_num at h2d
  have hX : CFSG.Blueprint.LieModel (↥J ⧸ Subgroup.center ↥J) .PSL (k + 1) 2 f := by
    refine Or.inl ⟨by decide, ?_⟩
    unfold CFSG.Open.StatedClassicalModel
    exact ⟨hadm, GaloisField 2 f, inferInstance, inferInstance, GaloisField.card 2 f hf0, hPSL⟩
  unfold GGSixLSevenFieldExtCase at hF
  obtain ⟨t', m', f', hlt', hM', -⟩ := hF
  by_cases hcl : t' ∈ CFSG.Blueprint.classicalTags ∨ t' = .twistedB2
  · have hff : f' = f := by
      rcases Nat.lt_or_ge (k + 1) 3 with h3 | h3
      · have hk2 : k + 1 = 2 := by omega
        rw [hk2] at hX
        exact (CFSG.SeitzReduction.RankOne.lieModel_PSL_two_two_unique_classicalOrSuzuki_of_card_eq
          hX hcl hM' rfl).2.2
      · exact (CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique_classicalOrSuzuki
          h3 hX hcl hM').2.2
    omega
  · have hff : f' = f := by
      rcases Nat.lt_or_ge (k + 1) 3 with h3 | h3
      · have hk2 : k + 1 = 2 := by omega
        rw [hk2] at hX
        exact (CFSG.SeitzReduction.RankOne.lieModel_PSL_two_two_unique_of_card_eq
          hX hM' rfl).2.2
      · exact (CFSG.SeitzReduction.LinearPilot.lieModel_PSL_two_unique h3 hX hM').2.2
    omega

end WP1

end TwoLe

section FalseDvd

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

section WP1

variable {X : Type} [Group X] {m f p : ℕ}
  {G₀ B D J L : Subgroup X} {x : X}

local notation "𝔽" => GaloisField 2 f
local notation "SLm" => Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)

theorem false_of_dvd_PSL
    [Finite X]
    {ψ : (ggU .PSL (m + 1) f).K →* X} (h : GGTCHyp .PSL (m + 1) f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .PSL f) (hp : p ∣ 2 ^ f - 1) : False := by
  classical
  have hf : f ≠ 0 := by have := h.adm.2.1; omega
  obtain ⟨σ, hσ, hcomm, hodd, J', hJ'comp, hJ'map⟩ := exists_lifts_PSL h
  have hDB : D ≤ B := h.d_le
  obtain ⟨e, he, hJe⟩ := exists_block_PSL hcomm hDB hJ'comp
  have hS : ∀ s ∈ σ '' (D : Set X), ∀ s' ∈ σ '' (D : Set X), Commute s s' := by
    rintro _ ⟨d, hd, rfl⟩ _ ⟨d', hd', rfl⟩
    exact hcomm d (hDB hd) d' (hDB hd')
  have hSodd : ∀ s ∈ σ '' (D : Set X), Odd (orderOf s) := by
    rintro _ ⟨d, hd, rfl⟩
    exact hodd d (hDB hd)
  have hdeg := two_le_blockDegree_PSL h hS he hJe hJ'map hF
  have hpowS : ∀ s ∈ σ '' (D : Set X), ∃ u : (GaloisField 2 f)ˣ,
      s ^ p = Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) u := by
    rintro _ ⟨d, hd, rfl⟩
    exact lift_pow_scalar_PSL m f p ψ h.ker (hσ d (hDB hd)) (h.b_elem.2 d (hDB hd))
  have hpF : p ∣ Nat.card (GaloisField 2 f)ˣ := by
    rw [Nat.card_units, GaloisField.card 2 f hf]
    exact hp
  obtain ⟨s, ⟨d₀, hd₀, rfl⟩, u, hsu, hnp⟩ :=
    exists_nonpow_lift h.prime hpF hS hSodd he hdeg hpowS
  have hpowB : ∀ b : B, ∃ w : (GaloisField 2 f)ˣ,
      σ b.1 ^ p = Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) w := fun b =>
    lift_pow_scalar_PSL m f p ψ h.ker (hσ b.1 b.2) (h.b_elem.2 b.1 b.2)
  obtain ⟨n, hn, hcard⟩ := card_le_of_nonpow_matrix (F := GaloisField 2 f) (N := m + 1) h.prime
    h.ne_two (σ d₀) u hsu hnp (ι := B) (fun b => σ b.1)
    (fun b b' => (hcomm b.1 b.2 b'.1 b'.2).eq)
    (fun b => (hcomm b.1 b.2 d₀ (hDB hd₀)).eq)
    hpowB
    (by
      intro i j w hij
      have hj' : IsGLLift Matrix.SpecialLinearGroup.toGL ψ
          (σ j.1 * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) w) j.1 :=
        isGLLift_mul_scalar (hσ j.1 j.2) w
      have hi' : IsGLLift Matrix.SpecialLinearGroup.toGL ψ
          (σ j.1 * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) w) i.1 := by
        rw [← hij]; exact hσ i.1 i.2
      have hmem := isGLLift_inj_centralizer Matrix.SpecialLinearGroup.toGL_injective hj' hi'
      have hB : i.1 * j.1⁻¹ ∈ B ⊓ Subgroup.centralizer (G₀ : Set X) :=
        ⟨B.mul_mem i.2 (B.inv_mem j.2), by rw [← h.range]; exact hmem⟩
      rw [h.b_faithful, Subgroup.mem_bot, mul_inv_eq_one] at hB
      exact Subtype.ext hB)
  have hHN : p ^ (m + 1 - 3) ≤ Nat.card B := h.b_HN (Or.inl ⟨rfl, hp⟩)
  have hp3 : 3 ≤ p := by
    have := h.prime.two_le
    have := h.ne_two
    omega
  have hpos : 1 < p := h.prime.one_lt
  have h1 : m + 1 - 3 ≤ n := (Nat.pow_le_pow_iff_right hpos).mp (hHN.trans hcard)
  have h2 : 4 ≤ n := (Nat.pow_le_pow_iff_right hpos).mp (h.b_card.trans hcard)
  have h3 : 3 * n ≤ p * n := Nat.mul_le_mul_right n hp3
  omega

end WP1

end FalseDvd

section FEq

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

private lemma tcPSL_eq_one_of_pow {F : Type} [Field F] [Finite F] {p : ℕ} (hp : p.Prime)
    (hpF : ¬ p ∣ Nat.card Fˣ) {c : F} (hc : c ^ p = 1) : c = 1 := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hc
    exact zero_ne_one hc
  let u : Fˣ := Units.mk0 c hc0
  have hu : u ^ p = 1 := Units.ext (by simpa [u] using hc)
  have hcop : Nat.Coprime p (Nat.card Fˣ) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpF
  have h1 : orderOf u ∣ p := orderOf_dvd_of_pow_eq_one hu
  have h2 : orderOf u ∣ Nat.card Fˣ := orderOf_dvd_natCard u
  have h3 : orderOf u = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
  have h4 : u = 1 := orderOf_eq_one_iff.mp h3
  simpa [u] using congrArg Units.val h4

private lemma tcPSL_commute_of_mem_adjoin_set {N : ℕ} {F : Type} [Field F]
    {T : Set (Matrix (Fin N) (Fin N) F)} {g : Matrix (Fin N) (Fin N) F}
    (hg : ∀ a ∈ T, g * a = a * g) {x : Matrix (Fin N) (Fin N) F}
    (hx : x ∈ Algebra.adjoin F T) : g * x = x * g := by
  have hle : Algebra.adjoin F T ≤
      Subalgebra.centralizer F ({g} : Set (Matrix (Fin N) (Fin N) F)) := by
    apply Algebra.adjoin_le
    intro a ha
    rw [SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.mp hz]
    exact hg a ha
  have hmem := hle hx
  rw [Subalgebra.mem_centralizer_iff] at hmem
  exact hmem _ rfl

private lemma tcPSL_mem_glBlock_iff' {N : ℕ} {F : Type} [Field F] (S : Set (GL (Fin N) F))
    (ε : Matrix (Fin N) (Fin N) F) (w : Matrix.SpecialLinearGroup (Fin N) F) :
    w ∈ glBlockCentralizer Matrix.SpecialLinearGroup.toGL S ε ↔
      Matrix.SpecialLinearGroup.toGL w ∈ Subgroup.centralizer S ∧
        (Matrix.SpecialLinearGroup.toGL w : Matrix (Fin N) (Fin N) F) * (1 - ε) = 1 - ε :=
  Iff.rfl

private lemma tcPSL_pow_mul_eq {N : ℕ} {F : Type} [Field F] (M : GL (Fin N) F)
    (e : Matrix (Fin N) (Fin N) F) (h : (M : Matrix (Fin N) (Fin N) F) * e = e) (j : ℕ) :
    ((M ^ j : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) * e = e := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ, Units.val_mul, mul_assoc, h, ih]

private lemma tcPSL_pow_mul_smul {N : ℕ} {F : Type} [Field F] (M : GL (Fin N) F)
    (e : Matrix (Fin N) (Fin N) F) (c : F)
    (h : (M : Matrix (Fin N) (Fin N) F) * e = c • e) (j : ℕ) :
    ((M ^ j : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) * e = c ^ j • e := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Units.val_mul, mul_assoc, h, Matrix.mul_smul, ih, smul_smul, ← pow_succ']

private lemma tcPSL_block_fixed_of_scalar {N : ℕ} {F : Type} [Field F] [Finite F] {p : ℕ}
    (hp : p.Prime) (hpF : ¬ p ∣ Nat.card Fˣ) (M : GL (Fin N) F) (hM : M ^ p = 1)
    (e : Matrix (Fin N) (Fin N) F) (he : e ≠ 0) (c : F)
    (h : (M : Matrix (Fin N) (Fin N) F) * e = c • e) :
    (M : Matrix (Fin N) (Fin N) F) * e = e := by
  have h1 := tcPSL_pow_mul_smul M e c h p
  rw [hM, Units.val_one, Matrix.one_mul] at h1
  have h2 : (c ^ p - 1) • e = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
  rcases smul_eq_zero.mp h2 with h3 | h3
  · have hcp : c ^ p = 1 := sub_eq_zero.mp h3
    have hc1 : c = 1 := tcPSL_eq_one_of_pow hp hpF hcp
    rw [h, hc1, one_smul]
  · exact absurd h3 he

section WP1

variable {X : Type} [Group X] {m f p : ℕ}
  {G₀ B D J L : Subgroup X} {x : X}

local notation "𝔽" => GaloisField 2 f
local notation "SLm" => Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)

theorem dvd_card_J_PSL
    [Finite X]
    {ψ : (ggU .PSL (m + 1) f).K →* X} (h : GGTCHyp .PSL (m + 1) f ψ p G₀ B D J L x)
    (hp : ¬ p ∣ 2 ^ f - 1)
    {S : Set (GL (Fin (m + 1)) 𝔽)} (hS : ∀ s ∈ S, ∀ s' ∈ S, Commute s s')
    (hodd : ∀ s ∈ S, Odd (orderOf s))
    {J' : Subgroup SLm} {e : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽}
    (he : IsPrimIdemIn (Algebra.adjoin 𝔽 (Units.val '' S)) e)
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL S e⁆) (hJ : J'.map ψ = J)
    (hdeg : 2 ≤ blockDegree (Algebra.adjoin 𝔽 (Units.val '' S)) e)
    (hpK : p ∣ 2 ^ (f * blockDegree (Algebra.adjoin 𝔽 (Units.val '' S)) e) - 1) :
    p ∣ Nat.card J := by
  classical
  have hf : f ≠ 0 := by have := h.adm.2.1; omega
  have : Fact p.Prime := ⟨h.prime⟩
  have hpF' : ¬ p ∣ Nat.card (GaloisField 2 f)ˣ := by
    rw [Nat.card_units, GaloisField.card 2 f hf]; exact hp
  set d := blockDegree (Algebra.adjoin 𝔽 (Units.val '' S)) e with hd
  have hfd : f * d ≠ 0 := Nat.mul_ne_zero hf (by omega)
  have hKcard : Nat.card (GaloisField 2 (f * d)) = 2 ^ (f * d) := GaloisField.card 2 (f * d) hfd
  obtain ⟨m', hm'2, ⟨φ⟩⟩ := fePSL_dualPair_blockGroup_iso m f (by omega) S hS hodd he hdeg hJe
    (GaloisField 2 (f * d)) hKcard
  have hK4 : 4 ≤ Nat.card (GaloisField 2 (f * d)) := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (f * d) := Nat.pow_le_pow_right (by norm_num) (by nlinarith [Nat.pos_of_ne_zero hf])
  have hJeq := fePSL_component_eq m f S hJe hm'2 hK4 ⟨φ⟩
  have hpSL : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin m') (GaloisField 2 (f * d))) :=
    dvd_card_specialLinear hm'2 (by rwa [hKcard])
  have hpJ' : p ∣ Nat.card J' := by
    have e1 : ↥J' ≃* Matrix.SpecialLinearGroup (Fin m') (GaloisField 2 (f * d)) :=
      (MulEquiv.subgroupCongr hJeq).trans φ
    rw [Nat.card_congr e1.toEquiv]
    exact hpSL
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpJ'
  have hgp : (g : SLm) ^ p = 1 := by
    have h1 : g ^ p = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
    have h2 := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow] at h2
  have hψg : ψ (g : SLm) ≠ 1 := by
    intro h1
    have hz : (g : SLm) ∈ Subgroup.center SLm := h.ker (MonoidHom.mem_ker.mpr h1)
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hz
    have h2 : ((g : SLm) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) ^ p = 1 := by
      rw [← Matrix.SpecialLinearGroup.coe_pow, hgp]
      rfl
    rw [← hr, ← map_pow] at h2
    have h3 : Matrix.scalar (Fin (m + 1)) (r ^ p) = Matrix.scalar (Fin (m + 1)) 1 := by
      rw [h2, map_one]
    have hr1 : r ^ p = 1 := (Matrix.scalar (Fin (m + 1))).injective h3
    have hr2 : r = 1 := tcPSL_eq_one_of_pow h.prime hpF' hr1
    have hg1 : g = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      rw [← hr, hr2, map_one]
      rfl
    rw [hg1, orderOf_one] at hg
    exact h.prime.one_lt.ne hg
  have hjmem : ψ (g : SLm) ∈ J := by rw [← hJ]; exact Subgroup.mem_map_of_mem ψ g.2
  let j : ↥J := ⟨ψ (g : SLm), hjmem⟩
  have hjp : j ^ p = 1 := by
    apply Subtype.ext
    have h1 : ψ ((g : SLm) ^ p) = ψ (g : SLm) ^ p := map_pow ψ _ p
    have h2 : ψ ((g : SLm) ^ p) = 1 := by rw [hgp]; exact map_one ψ
    exact h1.symm.trans h2
  have hj1 : j ≠ 1 := fun h1 => hψg (congrArg Subtype.val h1)
  have hordj : orderOf j = p := orderOf_eq_prime hjp hj1
  rw [← hordj]
  exact orderOf_dvd_natCard j

theorem f_eq_one_of_not_dvd_PSL
    [Finite X]
    {ψ : (ggU .PSL (m + 1) f).K →* X} (h : GGTCHyp .PSL (m + 1) f ψ p G₀ B D J L x)
    (hF : GGSixLSevenFieldExtCase J .PSL f) (hp : ¬ p ∣ 2 ^ f - 1) : f = 1 := by
  classical
  have hf : f ≠ 0 := by have := h.adm.2.1; omega
  have hpF' : ¬ p ∣ Nat.card (GaloisField 2 f)ˣ := by
    rw [Nat.card_units, GaloisField.card 2 f hf]; exact hp
  have hDB : D ≤ B := h.d_le
  obtain ⟨σ, hσ, hcomm, hodd, J', hJ'comp, hJ'map⟩ := exists_lifts_PSL h
  obtain ⟨e, he, hJe⟩ := exists_block_PSL hcomm hDB hJ'comp
  have hS : ∀ s ∈ σ '' (D : Set X), ∀ s' ∈ σ '' (D : Set X), Commute s s' := by
    rintro _ ⟨d, hd, rfl⟩ _ ⟨d', hd', rfl⟩
    exact hcomm d (hDB hd) d' (hDB hd')
  have hSodd : ∀ s ∈ σ '' (D : Set X), Odd (orderOf s) := by
    rintro _ ⟨d, hd, rfl⟩
    exact hodd d (hDB hd)
  have hdeg := two_le_blockDegree_PSL h hS he hJe hJ'map hF
  have h3 := three_le_blockDim_PSL h hσ hcomm hodd he hJe hJ'map
  have hrk6 : 6 ≤ e.rank := by omega
  have hBp : ∀ b ∈ B, b ^ p = 1 := h.b_elem.2
  obtain ⟨τ, w, hτσ, hτp, hτmul⟩ :=
    exists_orderp_lifts_PSL m f p hf h.prime hp ψ h.ker hBp hσ hcomm
  have hτlift : ∀ b ∈ B, IsGLLift Matrix.SpecialLinearGroup.toGL ψ (τ b) b := by
    intro b hb
    rw [hτσ b hb]
    exact isGLLift_mul_scalar (hσ b hb) (w b)
  have hscalar_comm : ∀ (a : GL (Fin (m + 1)) 𝔽) (v : 𝔽ˣ), Commute a
      (Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) v) := by
    intro a v
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    exact (Matrix.scalar_commute _ (fun r => Commute.all _ r) _).symm.eq
  have hτcomm : ∀ b ∈ B, ∀ b' ∈ B, Commute (τ b) (τ b') := by
    intro b hb b' hb'
    rw [hτσ b hb, hτσ b' hb']
    exact ((hcomm b hb b' hb').mul_right (hscalar_comm _ _)).mul_left
      ((hscalar_comm _ _).symm.mul_right ((Commute.all _ _).map _))
  have hτσcomm : ∀ y ∈ B, ∀ d ∈ B, Commute (τ y) (σ d) := by
    intro y hy d hd
    rw [hτσ y hy]
    exact (hcomm y hy d hd).mul_left (hscalar_comm (σ d) (w y)).symm
  have hτσD : ∀ b ∈ D, τ b = σ b * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) (w b) :=
    fun b hb => hτσ b (hDB hb)
  have hτpD : ∀ b ∈ D, τ b ^ p = 1 := fun b hb => hτp b (hDB hb)
  have hτmulD : ∀ b ∈ D, ∀ b' ∈ D, τ (b * b') = τ b * τ b' :=
    fun b hb b' hb' => hτmul b (hDB hb) b' (hDB hb')
  have hτ1 : τ 1 = 1 := by
    have h1 := hτmulD 1 D.one_mem 1 D.one_mem
    rw [mul_one] at h1
    have h2 : τ 1 * τ 1 = τ 1 * 1 := by rw [mul_one]; exact h1.symm
    exact mul_left_cancel h2
  have hτpow : ∀ y ∈ D, ∀ n : ℕ, τ (y ^ n) = τ y ^ n := by
    intro y hy n
    induction n with
    | zero => rw [pow_zero, pow_zero]; exact hτ1
    | succ n ih => rw [pow_succ, pow_succ, hτmulD _ (D.pow_mem hy n) _ hy, ih]
  obtain ⟨⟨y₁, hy₁D, hy₁⟩, g₀, hg₀D, hg₀1, hg₀e⟩ :=
    exists_fixed_PSL h.prime h.d_card hτσD hτpD hτmulD hS hSodd he hdeg
  have he0 : e ≠ 0 := he.2.2.1
  have heidem : IsIdempotentElem e := he.2.1
  have hτy_comm : ∀ y ∈ D, (τ y : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) * e =
      e * (τ y : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) := by
    intro y hy
    refine tcPSL_commute_of_mem_adjoin_set ?_ he.1
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    have h1 := congrArg Units.val (hτσcomm y (hDB hy) d (hDB hd)).eq
    rwa [Units.val_mul, Units.val_mul] at h1
  have hJ'GE : ∀ u ∈ J', u ∈ glBlockCentralizer Matrix.SpecialLinearGroup.toGL
      (σ '' (D : Set X)) e := by
    intro u hu
    have hu1 := hJe.1 hu
    have hcl : ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL (σ '' (D : Set X)) e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL (σ '' (D : Set X)) e⁆ ≤
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL (σ '' (D : Set X)) e := by
      rw [Subgroup.commutator_le]
      intro g₁ hg₁ g₂ hg₂
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hg₁ hg₂)
        (Subgroup.inv_mem _ hg₁)) (Subgroup.inv_mem _ hg₂)
    exact hcl hu1
  have hJ'D : ∀ u ∈ J', ∀ d ∈ D, Matrix.SpecialLinearGroup.toGL u * τ d =
      τ d * Matrix.SpecialLinearGroup.toGL u := by
    intro u hu d hd
    have hu1 := ((tcPSL_mem_glBlock_iff' _ _ u).mp (hJ'GE u hu)).1
    have hu2 : σ d * Matrix.SpecialLinearGroup.toGL u = Matrix.SpecialLinearGroup.toGL u * σ d :=
      Subgroup.mem_centralizer_iff.mp hu1 (σ d) ⟨d, hd, rfl⟩
    rw [hτσD d hd]
    exact ((Commute.symm (show Commute (σ d) (Matrix.SpecialLinearGroup.toGL u) from hu2)).mul_right
      (hscalar_comm _ _)).eq
  have hJ'e : ∀ u ∈ J', (Matrix.SpecialLinearGroup.toGL u : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) *
      (1 - e) = 1 - e := fun u hu => ((tcPSL_mem_glBlock_iff' _ _ u).mp (hJ'GE u hu)).2
  have hJq : CFSG.IsQuasisimple ↥J :=
    (CFSG.StandardType.TableBSymp.isQuasisimple_iff _).mp h.j_comp.2.2
  have hxB : x ∈ B := hDB h.x_mem
  have hxp : x ^ p = 1 := hBp x hxB
  by_cases hx : (τ x : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) * e = e
  ·
    obtain ⟨m', β, hrk', hlt', hinj, hJ'le, hperf, hcomp, hmodel, hconjB, hcentre, hscalB, hker⟩ :=
      blockData_PSL h hp hτlift hτp hτcomm he0 heidem h.x_mem h.x_ne hx
        (by rw [← hτy_comm x h.x_mem]; exact hx) hJ'D hJ'e (by omega)
    have hJle : J ≤ β.range.map ψ := by rw [← hJ'map]; exact Subgroup.map_mono hJ'le
    have hLeq : L = β.range.map ψ :=
      eq_of_isComponentOf_of_le h.l_comp hcomp hJq h.j_le_l hJle
    subst hLeq
    obtain ⟨lab, hlab, hspl, hM⟩ := exists_label_of_marking_tc h.l_split
    have hadm := CFSG.Blueprint.LieModel.admissible hmodel
    have hrank2 : 2 ≤ (ggU .PSL (m' + 1) f).D.rank := by
      show 2 ≤ m'
      omega
    obtain ⟨hmt, hmr, hmc, hmd⟩ := markData_of_lieModel hlab hM (Or.inl rfl) hadm hrank2 hmodel
    rcases split_of_markTag_PSL hmt hmr hmc hmd (by omega) hspl with h1 | ⟨h1, -⟩
    · exact absurd h1 hp
    · exact h1
  ·
    have hg₀x : g₀ ∉ Subgroup.zpowers x := by
      intro hmem
      obtain ⟨j, hj⟩ := exists_pow_eq_of_mem_zpowers h.prime h.x_ne hxp hg₀1 hmem
      apply hx
      have hτj : τ x = τ g₀ ^ j := by rw [hj]; exact hτpow g₀ hg₀D j
      rw [hτj]
      exact tcPSL_pow_mul_eq (τ g₀) e hg₀e j
    obtain ⟨m', β, hrk', hlt', hinj, hJ'le, hperf, hcomp, hmodel, hconjB, hcentre, hscalB, hker⟩ :=
      blockData_PSL h hp hτlift hτp hτcomm he0 heidem hg₀D hg₀1 hg₀e
        (by rw [← hτy_comm g₀ hg₀D]; exact hg₀e) hJ'D hJ'e (by omega)
    have hJK : J ≤ β.range.map ψ := by rw [← hJ'map]; exact Subgroup.map_mono hJ'le
    have hKJ : β.range.map ψ ≠ J := by
      intro hKJ
      have hle : β.range ≤ J' :=
        le_of_map_le_of_perfect ψ h.ker hperf (by rw [hJ'map]; exact hKJ.le)
      obtain ⟨c, hc⟩ := hscalB y₁ (hDB hy₁D)
        (fun u => hJ'D (β u) (hle ⟨u, rfl⟩) y₁ hy₁D)
      exact hy₁ (tcPSL_block_fixed_of_scalar h.prime hpF' (τ y₁) (hτpD y₁ hy₁D) e he0 c hc)
    have hpK : p ∣
        2 ^ (f * blockDegree (Algebra.adjoin 𝔽 (Units.val '' (σ '' (D : Set X)))) e) - 1 := by
      have h1 := dvd_card_pow_blockDegree_PSL h.prime hτσD hτpD hS hSodd he hy₁D hy₁
      rwa [GaloisField.card 2 f hf, ← pow_mul] at h1
    have hpJ : p ∣ Nat.card J := dvd_card_J_PSL h hp hS hSodd he hJe hJ'map hdeg hpK
    have hinner : GGInnerDiagOn (Subgroup.zpowers x) (β.range.map ψ) := by
      have h1 := ggInnerDiagOn_of_conj (m' := m') (f := f) (by omega) (by omega)
        (fun h1 => by omega) (ψ.comp β) (fun u hu => hker u (MonoidHom.mem_ker.mp hu))
        (Subgroup.zpowers x) (fun b hb => hconjB b (Subgroup.zpowers_le.mpr hxB hb))
      have h2 : (ψ.comp β).range = β.range.map ψ := MonoidHom.range_comp ψ β
      rw [h2] at h1
      exact h1
    obtain ⟨lab, hlab, hQ, hM⟩ :=
      exists_label_of_marking_tc (h.nbr g₀ hg₀D hg₀x _ hcomp hJK hKJ hpJ hinner)
    have hadm := CFSG.Blueprint.LieModel.admissible hmodel
    have hrank2 : 2 ≤ (ggU .PSL (m' + 1) f).D.rank := by
      show 2 ≤ m'
      omega
    obtain ⟨hmt, hmr, hmc, hmd⟩ := markData_of_lieModel hlab hM (Or.inl rfl) hadm hrank2 hmodel
    rcases halfSplit_of_markTag_PSL hmt hmr hmc hmd (by omega) hQ with
      h1 | ⟨h1, -⟩ | ⟨h6, hf2, hZ, -⟩ | ⟨-, h1, -⟩
    · exact absurd h1 hp
    · exact h1
    · exfalso
      have hcard4 : Nat.card 𝔽 = 4 := by rw [GaloisField.card 2 f hf, hf2]; norm_num
      have hcard3 : Nat.card 𝔽ˣ = 3 := by rw [Nat.card_units, hcard4]
      have : Nontrivial 𝔽ˣ := Finite.one_lt_card_iff_nontrivial.mp (by rw [hcard3]; norm_num)
      obtain ⟨u, hu⟩ := exists_ne (1 : 𝔽ˣ)
      have hu1 : (u : 𝔽) ≠ 1 := fun h1 => hu (Units.ext h1)
      have hu3 : u ^ 3 = 1 := by rw [← hcard3]; exact pow_card_eq_one'
      have hu6 : (u : 𝔽) ^ (m' + 1) = 1 := by
        rw [h6, ← Units.val_pow_eq_pow_val, show (6 : ℕ) = 3 * 2 from rfl, pow_mul, hu3, one_pow]
        rfl
      exact hcentre u hu1 hu6 hZ
    · exact h1

end WP1

end FEq

section Assm

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

theorem ggTCAt_PSL :
    GGTCAt .PSL := by
  intro X _ _ n f ψ p G₀ B D J L x h hF _
  refine ⟨rfl, ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := h.adm.2.2.1; omega⟩
  by_cases hp : p ∣ 2 ^ f - 1
  · exact (false_of_dvd_PSL h hF hp).elim
  · rw [f_eq_one_of_not_dvd_PSL h hF hp]
    simp

end Assm

end CFSG.StandardType.TableCRes
