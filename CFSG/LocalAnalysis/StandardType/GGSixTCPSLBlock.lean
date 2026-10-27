module

public import CFSG.LocalAnalysis.StandardType.TableC.HypDefs
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSLAux
public import CFSG.LocalAnalysis.StandardType.GGSixTCPSLEmbed
public import CFSG.LocalAnalysis.StandardType.GGSixTCBlockField
public import CFSG.LocalAnalysis.StandardType.GGSixTCLiftGroup
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDCommute
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPSL
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType.TableCRes

section Lifts

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

private lemma tcPSL_odd_order (m f p : ℕ) (hf : f ≠ 0) (hp : p.Prime) (hp2 : p ≠ 2) {X : Type}
    [Group X] (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* X)
    (hψ : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    {b : X} {s : GL (Fin (m + 1)) (GaloisField 2 f)}
    (hslift : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s b) (hbp : b ^ p = 1) :
    Odd (orderOf s) := by
  have hlift_one : IsGLLift Matrix.SpecialLinearGroup.toGL ψ
      (1 : GL (Fin (m + 1)) (GaloisField 2 f)) (1 : X) :=
    isGLLift_one (j := Matrix.SpecialLinearGroup.toGL) (ψ := ψ)
  have hslift_pow : IsGLLift Matrix.SpecialLinearGroup.toGL ψ (s ^ p) (b ^ p) :=
    hslift.pow p
  rw [hbp] at hslift_pow
  obtain ⟨c, hc⟩ :=
    isGLLift_unique_PSL m (GaloisField 2 f) ψ hψ hslift_pow hlift_one
  have hzmat : ((s ^ p : GL (Fin (m + 1)) (GaloisField 2 f)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) =
      Matrix.scalar (Fin (m + 1)) c := by
    simpa using hc
  have hunit_sp : IsUnit (((s ^ p : GL (Fin (m + 1)) (GaloisField 2 f)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))) :=
    ⟨s ^ p, rfl⟩
  have hscalar : IsUnit (Matrix.scalar (Fin (m + 1)) c) := hzmat ▸ hunit_sp
  have hcne : c ≠ 0 := by
    have hdiag : IsUnit (fun _ : Fin (m + 1) => c) :=
      (Matrix.isUnit_diagonal (v := fun _ : Fin (m + 1) => c)).mp hscalar
    exact IsUnit.ne_zero ((Pi.isUnit_iff.mp hdiag) ⟨0, Nat.succ_pos m⟩)
  let u : (GaloisField 2 f)ˣ := Units.mk0 c hcne
  have hscalar_eq : (s ^ p : GL (Fin (m + 1)) (GaloisField 2 f)) =
      Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) u := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.coe_scalar, hzmat]
    simp [u]
  have hspk : s ^ (p * Nat.card (GaloisField 2 f)ˣ) = 1 := by
    rw [pow_mul, hscalar_eq, ← map_pow,
      orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard u), map_one]
  have hdvd : orderOf s ∣ p * Nat.card (GaloisField 2 f)ˣ :=
    orderOf_dvd_iff_pow_eq_one.mpr hspk
  have hcard : Nat.card (GaloisField 2 f)ˣ = 2 ^ f - 1 := by
    rw [Nat.card_units, GaloisField.card 2 f hf]
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hodd2 : Odd (2 ^ f - 1) :=
    Nat.Even.sub_odd Nat.one_le_two_pow (even_iff_two_dvd.mpr (dvd_pow_self 2 hf)) odd_one
  have hoddprod : Odd (p * Nat.card (GaloisField 2 f)ˣ) := by
    rw [hcard]
    exact hpodd.mul hodd2
  exact Odd.of_dvd_nat hoddprod hdvd

section WP1

variable {X : Type} [Group X] {m f p : ℕ}
  {G₀ B D J L : Subgroup X} {x : X}

local notation "𝔽" => GaloisField 2 f

theorem exists_lifts_PSL
    [Finite X]
    {ψ : (ggU .PSL (m + 1) f).K →* X} (h : GGTCHyp .PSL (m + 1) f ψ p G₀ B D J L x) :
    ∃ σ : X → GL (Fin (m + 1)) 𝔽,
      (∀ b ∈ B, IsGLLift Matrix.SpecialLinearGroup.toGL ψ (σ b) b) ∧
      (∀ b ∈ B, ∀ b' ∈ B, Commute (σ b) (σ b')) ∧ (∀ b ∈ B, Odd (orderOf (σ b))) ∧
      ∃ J' : Subgroup (ggU .PSL (m + 1) f).K,
        IsComponentOf J' ((Subgroup.centralizer (σ '' (D : Set X))).comap
          Matrix.SpecialLinearGroup.toGL) ∧ J'.map ψ = J := by
  have hadm : StatedLieAdmissible .PSL (m + 1) 2 f := h.adm
  have hf : f ≠ 0 := by
    have := hadm.2.1
    omega
  have hψ : ψ.ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) := h.ker
  have hBN : B ≤ Subgroup.normalizer (ψ.range : Set X) := by
    rw [h.range]
    exact h.b_norm
  have hHN : p ∣ 2 ^ f - 1 → B ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥ ∧
      p ^ ((m + 1) - 3) ≤ Nat.card B := by
    intro hpdiv
    refine ⟨?_, h.b_HN (Or.inl ⟨rfl, hpdiv⟩)⟩
    rw [h.range]
    exact h.b_faithful
  have hJ : IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set X)) := by
    rw [h.range]
    exact h.j_comp
  have hex : ∀ b : X, ∃ s : GL (Fin (m + 1)) (GaloisField 2 f),
      b ∈ B → IsGLLift Matrix.SpecialLinearGroup.toGL ψ s b := by
    intro b
    by_cases hb : b ∈ B
    · obtain ⟨s, hs⟩ := exists_isGLLift_PSL m (GaloisField 2 f) ψ hψ (hBN hb) (h.b_diag b hb)
      exact ⟨s, fun _ => hs⟩
    · exact ⟨1, fun hb' => absurd hb' hb⟩
  choose σ hσ using hex
  refine ⟨σ, hσ, ?_, ?_, ?_⟩
  · intro b hb b' hb'
    exact isGLLift_commute_PSL m f ψ hψ hadm h.prime h.ne_two hBN
      (fun c hc => h.b_diag c hc) h.b_elem h.b_card hHN hb hb' (hσ b hb) (hσ b' hb')
  · intro b hb
    exact tcPSL_odd_order m f p hf h.prime h.ne_two ψ hψ (hσ b hb) (h.b_elem.2 b hb)
  · have hlift : ∀ d ∈ D, ∃ s : GL (Fin (m + 1)) (GaloisField 2 f),
        s ∈ σ '' (D : Set X) ∧ IsGLLift Matrix.SpecialLinearGroup.toGL ψ s d :=
      fun d hd => ⟨σ d, ⟨d, hd, rfl⟩, hσ d (h.d_le hd)⟩
    obtain ⟨J', hJ'comp, hJ'map⟩ :=
      StepA.exists_isComponentOf_comap_lift_of_isGLLift
        Matrix.SpecialLinearGroup.toGL Matrix.SpecialLinearGroup.toGL_injective
        ψ hψ (fun s => s ∈ σ '' (D : Set X)) hJ hlift
    have hset : {s : GL (Fin (m + 1)) (GaloisField 2 f) | s ∈ σ '' (D : Set X) ∧
        ∃ d ∈ D, IsGLLift Matrix.SpecialLinearGroup.toGL ψ s d} = σ '' (D : Set X) := by
      ext s
      constructor
      · rintro ⟨hs, -⟩
        exact hs
      · rintro ⟨d, hd, rfl⟩
        exact ⟨⟨d, hd, rfl⟩, d, hd, hσ d (h.d_le hd)⟩
    have key : ∀ S : Set (GL (Fin (m + 1)) (GaloisField 2 f)), S = σ '' (D : Set X) →
        IsComponentOf J' ((Subgroup.centralizer S).comap Matrix.SpecialLinearGroup.toGL) →
        IsComponentOf J' ((Subgroup.centralizer (σ '' (D : Set X))).comap
          Matrix.SpecialLinearGroup.toGL) := by
      rintro S rfl hS
      exact hS
    exact ⟨J', key _ hset hJ'comp, hJ'map⟩

end WP1

end Lifts

section ExistsBlock

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

section WP1

variable {X : Type} [Group X] {m f p : ℕ}
  {G₀ B D J L : Subgroup X} {x : X}

local notation "𝔽" => GaloisField 2 f
local notation "SLm" => Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)

theorem exists_block_PSL {σ : X → GL (Fin (m + 1)) 𝔽}
    (hcomm : ∀ b ∈ B, ∀ b' ∈ B, Commute (σ b) (σ b')) (hDB : D ≤ B)
    {J' : Subgroup SLm}
    (hJ' : IsComponentOf J' ((Subgroup.centralizer (σ '' (D : Set X))).comap
      Matrix.SpecialLinearGroup.toGL)) :
    ∃ e, IsPrimIdemIn (Algebra.adjoin 𝔽 (Units.val '' (σ '' (D : Set X)))) e ∧
      IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL (σ '' (D : Set X)) e,
        glBlockCentralizer Matrix.SpecialLinearGroup.toGL (σ '' (D : Set X)) e⁆ := by
  refine exists_isComponentOf_glBlockCentralizer_PSL m 𝔽 _ ?_ hJ'
  rintro _ ⟨b, hb, rfl⟩ _ ⟨b', hb', rfl⟩
  exact hcomm b (hDB hb) b' (hDB hb')

end WP1

end ExistsBlock

section BlockData

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

private lemma tcPSL_commute_of_mem_adjoin {N : ℕ} {F : Type} [Field F]
    {s g : Matrix (Fin N) (Fin N) F} (hgs : g * s = s * g) {a : Matrix (Fin N) (Fin N) F}
    (ha : a ∈ Algebra.adjoin F ({s} : Set (Matrix (Fin N) (Fin N) F))) : g * a = a * g := by
  have hle : Algebra.adjoin F ({s} : Set (Matrix (Fin N) (Fin N) F)) ≤
      Subalgebra.centralizer F ({g} : Set (Matrix (Fin N) (Fin N) F)) := by
    apply Algebra.adjoin_le
    rw [Set.singleton_subset_iff, SetLike.mem_coe, Subalgebra.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff.mp hx]
    exact hgs
  have hmem := hle ha
  rw [Subalgebra.mem_centralizer_iff] at hmem
  exact hmem _ rfl

theorem glBlockCentralizer_normal {N : ℕ} {F : Type} [Field F] (s : GL (Fin N) F)
    (ε : Matrix (Fin N) (Fin N) F)
    (hεA : ε ∈ Algebra.adjoin F ({(s : Matrix (Fin N) (Fin N) F)} :
      Set (Matrix (Fin N) (Fin N) F))) :
    glBlockCentralizer Matrix.SpecialLinearGroup.toGL ({s} : Set (GL (Fin N) F)) ε ≤
        (Subgroup.centralizer ({s} : Set (GL (Fin N) F))).comap Matrix.SpecialLinearGroup.toGL ∧
      ((glBlockCentralizer Matrix.SpecialLinearGroup.toGL ({s} : Set (GL (Fin N) F)) ε).subgroupOf
        ((Subgroup.centralizer ({s} : Set (GL (Fin N) F))).comap
          Matrix.SpecialLinearGroup.toGL)).Normal := by
  have hmemH : ∀ w : Matrix.SpecialLinearGroup (Fin N) F,
      w ∈ glBlockCentralizer Matrix.SpecialLinearGroup.toGL ({s} : Set (GL (Fin N) F)) ε ↔
        Matrix.SpecialLinearGroup.toGL w ∈ Subgroup.centralizer ({s} : Set (GL (Fin N) F)) ∧
          (Matrix.SpecialLinearGroup.toGL w : Matrix (Fin N) (Fin N) F) * (1 - ε) = 1 - ε :=
    fun w => Iff.rfl
  have hle : glBlockCentralizer Matrix.SpecialLinearGroup.toGL ({s} : Set (GL (Fin N) F)) ε ≤
      (Subgroup.centralizer ({s} : Set (GL (Fin N) F))).comap Matrix.SpecialLinearGroup.toGL := by
    intro u hu
    exact ((hmemH u).mp hu).1
  refine ⟨hle, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff hle]
  intro u k hu hk
  rw [Subgroup.mem_comap] at hk
  obtain ⟨hu1, hu2⟩ := (hmemH u).mp hu
  rw [hmemH]
  have hkc : Matrix.SpecialLinearGroup.toGL (k * u * k⁻¹) ∈
      Subgroup.centralizer ({s} : Set (GL (Fin N) F)) := by
    rw [map_mul, map_mul, map_inv]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hu1) (Subgroup.inv_mem _ hk)
  refine ⟨hkc, ?_⟩
  set kk : GL (Fin N) F := Matrix.SpecialLinearGroup.toGL k with hkk
  set uu : GL (Fin N) F := Matrix.SpecialLinearGroup.toGL u with huu
  have hks : (kk : Matrix (Fin N) (Fin N) F) * (s : Matrix (Fin N) (Fin N) F) =
      (s : Matrix (Fin N) (Fin N) F) * (kk : Matrix (Fin N) (Fin N) F) := by
    have := Subgroup.mem_centralizer_iff.mp hk s (Set.mem_singleton s)
    exact congrArg Units.val this.symm
  have hkε := tcPSL_commute_of_mem_adjoin hks hεA
  have hu2' : (uu : Matrix (Fin N) (Fin N) F) * (1 - ε) = 1 - ε := hu2
  have hKKi : (kk : Matrix (Fin N) (Fin N) F) * ((kk⁻¹ : GL (Fin N) F) :
      Matrix (Fin N) (Fin N) F) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hKiK : ((kk⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) *
      (kk : Matrix (Fin N) (Fin N) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hKie : ((kk⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) * ε =
      ε * ((kk⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) := by
    calc ((kk⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) * ε
        = ((kk⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) * ε *
          ((kk : Matrix (Fin N) (Fin N) F) * ((kk⁻¹ : GL (Fin N) F) :
            Matrix (Fin N) (Fin N) F)) := by rw [hKKi, mul_one]
      _ = ((kk⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) *
          ((kk : Matrix (Fin N) (Fin N) F) * ε) *
          ((kk⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) := by
          rw [hkε]; noncomm_ring
      _ = (((kk⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) *
          (kk : Matrix (Fin N) (Fin N) F)) * ε *
          ((kk⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) := by noncomm_ring
      _ = ε * ((kk⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) := by rw [hKiK, one_mul]
  have hk1 : (kk : Matrix (Fin N) (Fin N) F) * (1 - ε) =
      (1 - ε) * (kk : Matrix (Fin N) (Fin N) F) := by
    rw [mul_sub, sub_mul, mul_one, one_mul, hkε]
  rw [map_mul, map_mul, map_inv]
  change ((kk * uu * kk⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) * (1 - ε) = 1 - ε
  rw [Units.val_mul, Units.val_mul]
  calc (kk : Matrix (Fin N) (Fin N) F) * (uu : Matrix (Fin N) (Fin N) F) *
        ((kk⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) * (1 - ε)
      = (kk : Matrix (Fin N) (Fin N) F) * (uu : Matrix (Fin N) (Fin N) F) *
        (((kk⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) * (1 - ε)) := by noncomm_ring
    _ = (kk : Matrix (Fin N) (Fin N) F) * (uu : Matrix (Fin N) (Fin N) F) *
        ((1 - ε) * ((kk⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F)) := by
        rw [mul_sub, sub_mul, mul_one, one_mul, hKie]
    _ = (kk : Matrix (Fin N) (Fin N) F) * ((uu : Matrix (Fin N) (Fin N) F) * (1 - ε)) *
        ((kk⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) := by noncomm_ring
    _ = (kk : Matrix (Fin N) (Fin N) F) * (1 - ε) *
        ((kk⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) := by rw [hu2']
    _ = (1 - ε) * (kk : Matrix (Fin N) (Fin N) F) *
        ((kk⁻¹ : GL (Fin N) F) : Matrix (Fin N) (Fin N) F) := by rw [hk1]
    _ = 1 - ε := by rw [mul_assoc, hKKi, mul_one]

private lemma tcPSL_mem_glBlock_iff {N : ℕ} {F : Type} [Field F] (S : Set (GL (Fin N) F))
    (ε : Matrix (Fin N) (Fin N) F) (w : Matrix.SpecialLinearGroup (Fin N) F) :
    w ∈ glBlockCentralizer Matrix.SpecialLinearGroup.toGL S ε ↔
      Matrix.SpecialLinearGroup.toGL w ∈ Subgroup.centralizer S ∧
        (Matrix.SpecialLinearGroup.toGL w : Matrix (Fin N) (Fin N) F) * (1 - ε) = 1 - ε :=
  Iff.rfl

section BlockData

variable {X : Type} [Group X] {m f p : ℕ}
  {G₀ B D J L : Subgroup X} {x : X}

local notation "𝔽" => GaloisField 2 f

theorem blockData_PSL
    [Finite X]
    {ψ : (ggU .PSL (m + 1) f).K →* X} (h : GGTCHyp .PSL (m + 1) f ψ p G₀ B D J L x)
    (hpF : ¬ p ∣ 2 ^ f - 1)
    {τ : X → GL (Fin (m + 1)) 𝔽}
    (hτ : ∀ b ∈ B, IsGLLift Matrix.SpecialLinearGroup.toGL ψ (τ b) b)
    (hτp : ∀ b ∈ B, τ b ^ p = 1) (hτcomm : ∀ b ∈ B, ∀ b' ∈ B, Commute (τ b) (τ b'))
    {e : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽} (he0 : e ≠ 0) (heidem : IsIdempotentElem e)
    {y : X} (hyD : y ∈ D) (hy1 : y ≠ 1) (hye : (τ y : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) * e = e)
    (hey : e * (τ y : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) = e)
    {J' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) 𝔽)}
    (hJ'D : ∀ u ∈ J', ∀ d ∈ D, Matrix.SpecialLinearGroup.toGL u * τ d =
      τ d * Matrix.SpecialLinearGroup.toGL u)
    (hJ'e : ∀ u ∈ J', (Matrix.SpecialLinearGroup.toGL u : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) *
      (1 - e) = 1 - e)
    (hrk : 3 ≤ e.rank) :
    ∃ (m' : ℕ) (β : Matrix.SpecialLinearGroup (Fin (m' + 1)) 𝔽 →*
        Matrix.SpecialLinearGroup (Fin (m + 1)) 𝔽),
      e.rank ≤ m' + 1 ∧ m' + 1 < m + 1 ∧ Function.Injective β ∧ J' ≤ β.range ∧
      commutator ↥β.range = ⊤ ∧
      IsComponentOf (β.range.map ψ) (G₀ ⊓ Subgroup.centralizer ({y} : Set X)) ∧
      LieModel (↥(β.range.map ψ) ⧸ Subgroup.center ↥(β.range.map ψ)) .PSL (m' + 1) 2 f ∧
      (∀ b ∈ B, ∃ A : GL (Fin (m' + 1)) 𝔽, ∀ u, b⁻¹ * ψ (β u) * b =
        ψ (β (InnerDiagA.conjSL A u))) ∧
      (∀ c : 𝔽, c ≠ 1 → c ^ (m' + 1) = 1 → Subgroup.center ↥(β.range.map ψ) ≠ ⊥) ∧
      (∀ b ∈ B, (∀ u, Matrix.SpecialLinearGroup.toGL (β u) * τ b =
        τ b * Matrix.SpecialLinearGroup.toGL (β u)) →
        ∃ c : 𝔽, (τ b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) * e = c • e) ∧
      (∀ u, ψ (β u) = 1 → u ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m' + 1)) 𝔽)) := by
  classical
  have hf : f ≠ 0 := by have := h.adm.2.1; omega
  have hpF' : ¬ p ∣ Nat.card (GaloisField 2 f)ˣ := by
    rw [Nat.card_units, GaloisField.card 2 f hf]; exact hpF
  have hyB : y ∈ B := h.d_le hyD
  set s : GL (Fin (m + 1)) 𝔽 := τ y with hs
  have hsp : s ^ p = 1 := hτp y hyB
  have hsp' : (s : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hsp]; rfl
  obtain ⟨ε, hεA, hεi, hsε, hεv, hεsc, hεe⟩ :=
    exists_avgIdem h.prime h.ne_two (s : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) hsp'
  have hεe' : ε * e = e := hεe e hye
  have hε0 : ε ≠ 0 := fun h0 => he0 (by rw [← hεe', h0, zero_mul])
  have hee : e * e = e := heidem
  have heε : e * ε = e := by
    have hc : ∀ a ∈ Algebra.adjoin 𝔽 ({(s : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽)} :
        Set (Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽)), ∃ c : 𝔽, e * a = c • e := by
      intro a ha
      induction ha using Algebra.adjoin_induction with
      | mem x hx =>
        refine ⟨1, ?_⟩
        rw [Set.mem_singleton_iff.mp hx, one_smul]
        exact hey
      | algebraMap r =>
        refine ⟨r, ?_⟩
        rw [Algebra.algebraMap_eq_smul_one, Matrix.mul_smul, Matrix.mul_one]
      | add x y hx hy ihx ihy =>
        obtain ⟨c, hc⟩ := ihx
        obtain ⟨d, hd⟩ := ihy
        exact ⟨c + d, by rw [mul_add, hc, hd, add_smul]⟩
      | mul x y hx hy ihx ihy =>
        obtain ⟨c, hc⟩ := ihx
        obtain ⟨d, hd⟩ := ihy
        exact ⟨c * d, by rw [← mul_assoc, hc, Matrix.smul_mul, hd, smul_smul]⟩
    obtain ⟨c, hcε⟩ := hc ε hεA
    have h1 : e * ε * e = e := by rw [mul_assoc, hεe', hee]
    rw [hcε, Matrix.smul_mul, hee] at h1
    have h2 : (c - 1) • e = 0 := by rw [sub_smul, one_smul, h1, sub_self]
    rcases smul_eq_zero.mp h2 with h3 | h3
    · rw [hcε, sub_eq_zero.mp h3, one_smul]
    · exact absurd h3 he0
  obtain ⟨m', β, hrank, hlt, hinj, hrange, hcen, hscal, hconj⟩ :=
    exists_blockEmbedding_PSL s ε hεi hε0 hεA hεsc
  have hε1 : ε ≠ 1 := by
    intro h1
    have hs1 : s = 1 := by
      apply Units.ext
      have h2 := hsε
      rw [h1, Matrix.mul_one] at h2
      simpa using h2
    have hlift1 : IsGLLift Matrix.SpecialLinearGroup.toGL ψ (1 : GL (Fin (m + 1)) 𝔽) y := by
      rw [← hs1]; exact hτ y hyB
    have hmem := isGLLift_inj_centralizer Matrix.SpecialLinearGroup.toGL_injective
      (isGLLift_one (j := Matrix.SpecialLinearGroup.toGL) (ψ := ψ)) hlift1
    have hy' : y ∈ B ⊓ Subgroup.centralizer (G₀ : Set X) :=
      ⟨hyB, by rw [← h.range]; rwa [inv_one, mul_one] at hmem⟩
    rw [h.b_faithful, Subgroup.mem_bot] at hy'
    exact hy1 hy'
  have hrank_le : e.rank ≤ m' + 1 := by
    rw [hrank]
    calc e.rank = (ε * e).rank := by rw [hεe']
      _ ≤ ε.rank := Matrix.rank_mul_le_left ε e
  have hlt' : m' + 1 < m + 1 := hlt hε1
  have hJ'le : J' ≤ β.range := by
    rw [hrange]
    intro u hu
    rw [tcPSL_mem_glBlock_iff]
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff.mp hg]
      exact (hJ'D u hu y hyD).symm
    · have h1e : (1 - e) * (1 - ε) = 1 - ε := by
        calc (1 - e) * (1 - ε) = 1 - ε - e + e * ε := by noncomm_ring
          _ = 1 - ε := by rw [heε]; abel
      calc (Matrix.SpecialLinearGroup.toGL u : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) * (1 - ε)
          = (Matrix.SpecialLinearGroup.toGL u : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) *
            ((1 - e) * (1 - ε)) := by rw [h1e]
        _ = ((Matrix.SpecialLinearGroup.toGL u : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) * (1 - e)) *
            (1 - ε) := by rw [mul_assoc]
        _ = 1 - ε := by rw [hJ'e u hu, h1e]
  have hm'3 : 3 ≤ m' + 1 := le_trans hrk hrank_le
  have hqSL : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin (m' + 1)) 𝔽) :=
    CFSG.RankThree.Classical2.isQuasisimple_specialLinearGroup (n := m' + 1) (K := 𝔽) hm'3
  have hqH : CFSG.IsQuasisimple ↥β.range :=
    CFSG.IsQuasisimple.of_mulEquiv (MonoidHom.ofInjective hinj).symm hqSL
  obtain ⟨hHC, hHnorm⟩ := glBlockCentralizer_normal s ε hεA
  rw [← hrange] at hHC hHnorm
  have hcomp := isComponentOf_map_of_normal ψ h.ker hHC hHnorm hqH
  have hC : ((Subgroup.centralizer ({s} : Set (GL (Fin (m + 1)) 𝔽))).comap
      Matrix.SpecialLinearGroup.toGL).map ψ = G₀ ⊓ Subgroup.centralizer ({y} : Set X) := by
    rw [← comap_centralizer_eq_of_lift m f p h.prime hpF' ψ h.ker (hτ y hyB) hsp]
    exact (Subgroup.map_comap_eq ψ _).trans (by rw [h.range])
  rw [hC] at hcomp
  have hθr : (ψ.comp β).range = β.range.map ψ := MonoidHom.range_comp ψ β
  have hθker : (ψ.comp β).ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m' + 1)) 𝔽) := by
    intro v hv
    have hv' : ψ (β v) = 1 := hv
    exact hcen v (h.ker (MonoidHom.mem_ker.mpr hv'))
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin (m' + 1)) 𝔽) := hqSL.1
  obtain ⟨eK⟩ := quotCenter_mulEquiv_of_perfect (ψ.comp β) hθker (β.range.map ψ) hθr
  have hPSL : Nonempty (↥(β.range.map ψ) ⧸ Subgroup.center ↥(β.range.map ψ) ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedSL (m' + 1) 𝔽)) :=
    ⟨eK.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj (m' + 1) 𝔽)⟩
  have hadm : CFSG.Open.StatedLieAdmissible .PSL (m' + 1) 2 f := by
    unfold CFSG.Open.StatedLieAdmissible
    refine ⟨Nat.prime_two, by omega, by omega, ?_, ?_⟩
    · intro heq
      have := (Prod.mk.inj heq).1
      omega
    · intro heq
      have := (Prod.mk.inj heq).1
      omega
  have hmodel : LieModel (↥(β.range.map ψ) ⧸ Subgroup.center ↥(β.range.map ψ)) .PSL (m' + 1) 2
      f := by
    refine Or.inl ⟨by decide, ?_⟩
    unfold CFSG.Open.StatedClassicalModel
    exact ⟨hadm, 𝔽, inferInstance, inferInstance, GaloisField.card 2 f hf, hPSL⟩
  have hconjB : ∀ b ∈ B, ∃ A : GL (Fin (m' + 1)) 𝔽, ∀ u, b⁻¹ * ψ (β u) * b =
      ψ (β (InnerDiagA.conjSL A u)) := by
    intro b hb
    obtain ⟨A, hA1, -⟩ := hconj (τ b) (hτcomm b hb y hyB)
    refine ⟨A, fun u => ?_⟩
    obtain ⟨u', hu'1, hu'2⟩ := hτ b hb (β u)
    have hu' : u' = β (InnerDiagA.conjSL A u) := by
      apply Matrix.SpecialLinearGroup.toGL_injective
      rw [hu'1, ← hA1 u]
    exact hu'2.trans (congrArg ψ hu')
  have hcentre : ∀ c : 𝔽, c ≠ 1 → c ^ (m' + 1) = 1 → Subgroup.center ↥(β.range.map ψ) ≠ ⊥ := by
    intro c hc1 hcm
    have hdet : (Matrix.scalar (Fin (m' + 1)) c :
        Matrix (Fin (m' + 1)) (Fin (m' + 1)) 𝔽).det = 1 := by
      rw [Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin]
      exact hcm
    set z : Matrix.SpecialLinearGroup (Fin (m' + 1)) 𝔽 := ⟨Matrix.scalar (Fin (m' + 1)) c, hdet⟩
      with hz
    have hzc : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m' + 1)) 𝔽) :=
      Matrix.SpecialLinearGroup.mem_center_iff.mpr ⟨c, by simpa using hcm, rfl⟩
    have hnot := hscal hε1 z c hc1 rfl
    have hψz : ψ (β z) ≠ 1 := by
      intro h1
      exact hnot (h.ker (MonoidHom.mem_ker.mpr h1))
    intro hbot
    have hmem : (⟨ψ (β z), Subgroup.mem_map_of_mem ψ ⟨z, rfl⟩⟩ : ↥(β.range.map ψ)) ∈
        Subgroup.center ↥(β.range.map ψ) := by
      rw [Subgroup.mem_center_iff]
      rintro ⟨w, hw⟩
      obtain ⟨_, ⟨v, rfl⟩, rfl⟩ := hw
      apply Subtype.ext
      show (ψ.comp β) v * (ψ.comp β) z = (ψ.comp β) z * (ψ.comp β) v
      rw [← map_mul (ψ.comp β), ← map_mul (ψ.comp β), Subgroup.mem_center_iff.mp hzc v]
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hψz (congrArg Subtype.val hmem)
  have hscalarB : ∀ b ∈ B, (∀ u, Matrix.SpecialLinearGroup.toGL (β u) * τ b =
      τ b * Matrix.SpecialLinearGroup.toGL (β u)) →
      ∃ c : 𝔽, (τ b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) * e = c • e := by
    intro b hb hbc
    obtain ⟨A, hA1, hA2⟩ := hconj (τ b) (hτcomm b hb y hyB)
    have hAcomm : ∀ u : Matrix.SpecialLinearGroup (Fin (m' + 1)) 𝔽,
        (u : Matrix (Fin (m' + 1)) (Fin (m' + 1)) 𝔽) *
          (A : Matrix (Fin (m' + 1)) (Fin (m' + 1)) 𝔽) =
        (A : Matrix (Fin (m' + 1)) (Fin (m' + 1)) 𝔽) *
          (u : Matrix (Fin (m' + 1)) (Fin (m' + 1)) 𝔽) := by
      intro u
      have h1 : InnerDiagA.conjSL A u = u := by
        apply hinj
        apply Matrix.SpecialLinearGroup.toGL_injective
        rw [← hA1 u]
        have := hbc u
        calc τ b * Matrix.SpecialLinearGroup.toGL (β u) * (τ b)⁻¹
            = Matrix.SpecialLinearGroup.toGL (β u) * τ b * (τ b)⁻¹ := by rw [this]
          _ = Matrix.SpecialLinearGroup.toGL (β u) := by group
      have h2 : ((InnerDiagA.conjSL A u : Matrix.SpecialLinearGroup (Fin (m' + 1)) 𝔽) :
          Matrix (Fin (m' + 1)) (Fin (m' + 1)) 𝔽) =
          (u : Matrix (Fin (m' + 1)) (Fin (m' + 1)) 𝔽) := by rw [h1]
      rw [InnerDiagA.coe_conjSL] at h2
      have hA' : (A : Matrix (Fin (m' + 1)) (Fin (m' + 1)) 𝔽) *
          ((A⁻¹ : GL (Fin (m' + 1)) 𝔽) : Matrix (Fin (m' + 1)) (Fin (m' + 1)) 𝔽) = 1 := by
        rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
      calc (u : Matrix (Fin (m' + 1)) (Fin (m' + 1)) 𝔽) * (A : Matrix _ _ 𝔽)
          = ((A : Matrix (Fin (m' + 1)) (Fin (m' + 1)) 𝔽) * (u : Matrix _ _ 𝔽) *
            ((A⁻¹ : GL (Fin (m' + 1)) 𝔽) : Matrix _ _ 𝔽)) * (A : Matrix _ _ 𝔽) := by rw [h2]
        _ = (A : Matrix _ _ 𝔽) * (u : Matrix _ _ 𝔽) := by
          rw [mul_assoc, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
    have hAsc : (A : Matrix (Fin (m' + 1)) (Fin (m' + 1)) 𝔽) ∈
        Set.range (Matrix.scalar (Fin (m' + 1))) := by
      refine Matrix.mem_range_scalar_of_commute_transvectionStruct (fun t => ?_)
      have := hAcomm ⟨t.toMatrix, t.det⟩
      exact this
    obtain ⟨c, hc⟩ := hAsc
    exact ⟨c, by
      have h3 := hA2 c hc.symm
      calc (τ b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) * e
          = (τ b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) * (ε * e) := by rw [hεe']
        _ = ((τ b : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) * ε) * e := by rw [mul_assoc]
        _ = c • e := by rw [h3, Matrix.smul_mul, hεe']⟩
  exact ⟨m', β, hrank_le, hlt', hinj, hJ'le, hqH.1.commutator_eq_top, hcomp, hmodel, hconjB,
    hcentre, hscalarB, fun u hu => hcen u (h.ker (show β u ∈ ψ.ker from MonoidHom.mem_ker.mpr hu))⟩

end BlockData

end BlockData

section Item4

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType
  CFSG.StandardType.ClassicalPosition

private lemma tcPSL_commutator_self_le {G : Type} [Group G] (H : Subgroup G) : ⁅H, H⁆ ≤ H := by
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  rw [commutatorElement_def]
  exact H.mul_mem (H.mul_mem (H.mul_mem hg₁ hg₂) (H.inv_mem hg₁)) (H.inv_mem hg₂)

private lemma tcPSL_commute_of_mem_adjoin_set' {N : ℕ} {F : Type} [Field F]
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

section Item4

variable {X : Type} [Group X] {m f p : ℕ}
  {G₀ B D J L : Subgroup X} {x : X}

local notation "𝔽" => GaloisField 2 f
local notation "SLm" => Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)

theorem commute_of_lifts_PSL
    [Finite X]
    {ψ : (ggU .PSL (m + 1) f).K →* X} (h : GGTCHyp .PSL (m + 1) f ψ p G₀ B D J L x) {b b' : X}
    (hb : b ∈ B) (hb' : b' ∈ B) {s s' : GL (Fin (m + 1)) 𝔽}
    (hs : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s b)
    (hs' : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s' b') : Commute s s' := by
  have hBN : B ≤ Subgroup.normalizer (ψ.range : Set X) := by
    rw [h.range]
    exact h.b_norm
  have hHN : p ∣ 2 ^ f - 1 → B ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥ ∧
      p ^ ((m + 1) - 3) ≤ Nat.card B := by
    intro hpdiv
    refine ⟨?_, h.b_HN (Or.inl ⟨rfl, hpdiv⟩)⟩
    rw [h.range]
    exact h.b_faithful
  exact isGLLift_commute_PSL m f ψ h.ker h.adm h.prime h.ne_two hBN
    (fun c hc => h.b_diag c hc) h.b_elem h.b_card hHN hb hb' hs hs'

theorem three_le_blockDim_PSL
    [Finite X]
    {ψ : (ggU .PSL (m + 1) f).K →* X} (h : GGTCHyp .PSL (m + 1) f ψ p G₀ B D J L x)
    {σ : X → GL (Fin (m + 1)) 𝔽}
    (hσ : ∀ b ∈ B, IsGLLift Matrix.SpecialLinearGroup.toGL ψ (σ b) b)
    (hcomm : ∀ b ∈ B, ∀ b' ∈ B, Commute (σ b) (σ b')) (hodd : ∀ b ∈ B, Odd (orderOf (σ b)))
    {J' : Subgroup SLm} {e : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽}
    (he : IsPrimIdemIn (Algebra.adjoin 𝔽 (Units.val '' (σ '' (D : Set X)))) e)
    (hJe : IsComponentOf J' ⁅glBlockCentralizer Matrix.SpecialLinearGroup.toGL (σ '' (D : Set X)) e,
      glBlockCentralizer Matrix.SpecialLinearGroup.toGL (σ '' (D : Set X)) e⁆)
    (hJ : J'.map ψ = J) :
    3 * blockDegree (Algebra.adjoin 𝔽 (Units.val '' (σ '' (D : Set X)))) e ≤ e.rank := by
  classical
  have hf : f ≠ 0 := by have := h.adm.2.1; omega
  have hψ : ψ.ker ≤ Subgroup.center SLm := h.ker
  have hDB : D ≤ B := h.d_le
  have hS : ∀ s ∈ σ '' (D : Set X), ∀ s' ∈ σ '' (D : Set X), Commute s s' := by
    rintro _ ⟨d, hd, rfl⟩ _ ⟨d', hd', rfl⟩
    exact hcomm d (hDB hd) d' (hDB hd')
  have hSodd : ∀ s ∈ σ '' (D : Set X), Odd (orderOf s) := by
    rintro _ ⟨d, hd, rfl⟩
    exact hodd d (hDB hd)
  have : Finite (ggU StatedLieTag.PSL (m + 1) f).K := (inferInstance : Finite SLm)
  let QL : Subgroup (GL (Fin (m + 1)) 𝔽) :=
    liftGroup (Matrix.SpecialLinearGroup.toGL_injective) ψ ⊤ B
  have hmemQ : ∀ t : GL (Fin (m + 1)) 𝔽, t ∈ QL ↔
      ∃ b ∈ B, IsGLLift Matrix.SpecialLinearGroup.toGL ψ t b :=
    fun t => ⟨fun ht => (mem_liftGroup.mp ht).2,
      fun hb => mem_liftGroup.mpr ⟨Subgroup.mem_top _, hb⟩⟩
  have hΓA : ∀ γ : ↥QL, ∀ a ∈ Algebra.adjoin 𝔽 (Units.val '' (σ '' (D : Set X))),
      ((QL.subtype γ : GL (Fin (m + 1)) 𝔽) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) * a =
        a * ((QL.subtype γ : GL (Fin (m + 1)) 𝔽) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) := by
    intro γ a ha
    obtain ⟨b, hb, hγb⟩ := (hmemQ γ.1).mp γ.2
    refine tcPSL_commute_of_mem_adjoin_set' ?_ ha
    rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
    have h1 := congrArg Units.val (commute_of_lifts_PSL h hb (hDB hd) hγb (hσ d (hDB hd))).eq
    rwa [Units.val_mul, Units.val_mul] at h1
  have hΓc : ∀ γ γ' : ↥QL, QL.subtype γ * QL.subtype γ' = QL.subtype γ' * QL.subtype γ := by
    intro γ γ'
    obtain ⟨b, hb, hγb⟩ := (hmemQ γ.1).mp γ.2
    obtain ⟨b', hb', hγb'⟩ := (hmemQ γ'.1).mp γ'.2
    exact (commute_of_lifts_PSL h hb hb' hγb hγb').eq
  have hp0 : (p : 𝔽) ≠ 0 := by
    intro h0
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff 𝔽 2 p).mp h0
    rcases Nat.Prime.eq_one_or_self_of_dvd h.prime 2 h2 with h3 | h3
    · omega
    · exact h.ne_two h3.symm
  have hΓp : ∀ γ : ↥QL, ∃ c : 𝔽,
      ((QL.subtype γ : GL (Fin (m + 1)) 𝔽) : Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) ^ p =
        Matrix.scalar (Fin (m + 1)) c := by
    intro γ
    obtain ⟨b, hb, hγb⟩ := (hmemQ γ.1).mp γ.2
    obtain ⟨u, hu⟩ := lift_pow_scalar_PSL m f p ψ hψ hγb (h.b_elem.2 b hb)
    refine ⟨(u : 𝔽), ?_⟩
    have h1 := congrArg Units.val hu
    rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar] at h1
    exact h1
  obtain ⟨Γ₀, hΓ₀sc, hΓ₀blk, hΓ₀idx⟩ :=
    exists_subgroup_index_le_blockBound (F := 𝔽) QL.subtype hS hSodd he hΓA hΓc hp0 hΓp
  have hBfaith : B ⊓ Subgroup.centralizer (ψ.range : Set X) = ⊥ := by
    rw [h.range]
    exact h.b_faithful
  have hBc : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b := fun b hb b' hb' =>
    congrArg Subtype.val (h.b_elem.1.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩)
  let φ : ↥QL →* ↥B := liftHom (hj := Matrix.SpecialLinearGroup.toGL_injective) (ψ := ψ)
    (Q := ⊤) hBfaith hBc
  have hφsurj : Function.Surjective φ :=
    liftHom_surjective (hj := Matrix.SpecialLinearGroup.toGL_injective) (ψ := ψ) (Q := ⊤)
      hBfaith hBc (fun b hb => ⟨σ b, Subgroup.mem_top _, hσ b hb⟩)
  have hφlift : ∀ γ : ↥QL, IsGLLift Matrix.SpecialLinearGroup.toGL ψ
      (γ : GL (Fin (m + 1)) 𝔽) (φ γ : X) :=
    fun γ => isGLLift_liftHom (hj := Matrix.SpecialLinearGroup.toGL_injective) (ψ := ψ) (Q := ⊤)
      hBfaith hBc γ
  have hker : φ.ker ≤ Γ₀ := by
    intro γ hγ
    have h1 : φ γ = 1 := hγ
    have h2 : IsGLLift Matrix.SpecialLinearGroup.toGL ψ (γ : GL (Fin (m + 1)) 𝔽) 1 :=
      (liftHom_eq_one_iff (hj := Matrix.SpecialLinearGroup.toGL_injective) (ψ := ψ) (Q := ⊤)
        hBfaith hBc γ).mp h1
    obtain ⟨c, hc⟩ := isGLLift_unique_PSL m 𝔽 ψ hψ h2 isGLLift_one
    refine hΓ₀sc γ c ?_
    simpa using hc
  have himg : Γ₀.map φ ≤ D.subgroupOf B := by
    rintro _ ⟨γ, hγ, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨a, ha, hae⟩ := hΓ₀blk γ hγ
    have hcent : (φ γ : X) ∈ Subgroup.centralizer (J : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      rw [← hJ] at hj
      obtain ⟨u₀, hu₀, rfl⟩ := Subgroup.mem_map.mp hj
      have hu₀G := tcPSL_commutator_self_le _ (hJe.1 hu₀)
      have hu₀c : Matrix.SpecialLinearGroup.toGL u₀ ∈
          Subgroup.centralizer (σ '' (D : Set X)) := hu₀G.1
      have hu₀A : ∀ b ∈ Algebra.adjoin 𝔽 (Units.val '' (σ '' (D : Set X))),
          ((Matrix.SpecialLinearGroup.toGL u₀ : GL (Fin (m + 1)) 𝔽) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) * b =
          b * ((Matrix.SpecialLinearGroup.toGL u₀ : GL (Fin (m + 1)) 𝔽) :
            Matrix (Fin (m + 1)) (Fin (m + 1)) 𝔽) := by
        intro b hb
        refine tcPSL_commute_of_mem_adjoin_set' ?_ hb
        rintro _ ⟨_, ⟨d, hd, rfl⟩, rfl⟩
        have h1 := Subgroup.mem_centralizer_iff.mp hu₀c (σ d) ⟨d, hd, rfl⟩
        have h2 := congrArg Units.val h1
        rw [Units.val_mul, Units.val_mul] at h2
        exact h2.symm
      have hcomm_t : (γ : GL (Fin (m + 1)) 𝔽) * Matrix.SpecialLinearGroup.toGL u₀ =
          Matrix.SpecialLinearGroup.toGL u₀ * (γ : GL (Fin (m + 1)) 𝔽) :=
        commute_of_blockScalar (he.1) ha (hΓA γ) hu₀A hu₀G.2 hae
      obtain ⟨u', hu'1, hu'2⟩ := hφlift γ u₀
      have hu'eq : u' = u₀ := by
        apply Matrix.SpecialLinearGroup.toGL_injective
        rw [hu'1]
        exact mul_inv_eq_iff_eq_mul.mpr hcomm_t
      rw [hu'eq] at hu'2
      calc ψ u₀ * (φ γ : X) = (φ γ : X) * ((φ γ : X)⁻¹ * ψ u₀ * (φ γ : X)) := by group
        _ = (φ γ : X) * ψ u₀ := congrArg (fun y => (φ γ : X) * y) hu'2
    have hD : (φ γ : X) ∈ B ⊓ Subgroup.centralizer (J : Set X) := ⟨(φ γ).2, hcent⟩
    rw [h.j_cent] at hD
    exact hD
  have hcount := card_le_mul_of_surjective_of_index_le φ hφsurj hker himg hΓ₀idx
  have hDcard : Nat.card (D.subgroupOf B) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDB).toEquiv]
    exact h.d_card
  rw [hDcard] at hcount
  have h4 : p ^ 4 ≤ p ^ 2 * p ^ (e.rank / blockDegree
      (Algebra.adjoin 𝔽 (Units.val '' (σ '' (D : Set X)))) e - 1) := h.b_card.trans hcount
  rw [← pow_add] at h4
  have h5 := (Nat.pow_le_pow_iff_right h.prime.one_lt).mp h4
  obtain ⟨hdpos, k', hk'⟩ := exists_blockDegree_mul_eq_rank hS hSodd he
  have hdiv : e.rank / blockDegree (Algebra.adjoin 𝔽 (Units.val '' (σ '' (D : Set X)))) e = k' := by
    rw [← hk', Nat.mul_div_cancel_left _ hdpos]
  rw [hdiv] at h5
  calc 3 * blockDegree (Algebra.adjoin 𝔽 (Units.val '' (σ '' (D : Set X)))) e
      ≤ k' * blockDegree (Algebra.adjoin 𝔽 (Units.val '' (σ '' (D : Set X)))) e :=
        Nat.mul_le_mul_right _ (by omega)
    _ = e.rank := by rw [← hk', mul_comm]

end Item4

end Item4

end CFSG.StandardType.TableCRes
