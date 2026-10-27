module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinStatements
import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksBasic
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksGroup

public section

namespace CFSG.StandardType.GGQ2Frame.LinBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.ClassicalPosition
  CFSG.StandardType.SpJoin Matrix
open CFSG.Open (StatedSp)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K]

private theorem tau_mul_planeIdem_comm (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
    (t : ℕ) (ε : Fin 2) (u : PlaneRaw.V t) (S : Finset (Fin t)) (fix : Bool) :
    ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) *
        planeIdem t ε S fix =
      planeIdem t ε S fix * ((tau ζ t ε u : GL (LinIdx t ε) K) :
        Matrix (LinIdx t ε) (LinIdx t ε) K) := by
  rw [coe_tau_eq_fromBlocks_spTau, planeIdem_eq_fromBlocks, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.mul_one, Matrix.one_mul]
  rw [SpBlocks.tau_mul_planeIdem_comm]

private theorem tau_mul_planeIdem_eq (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
    (t : ℕ) (ε : Fin 2) {v w : PlaneRaw.V t} {S : Finset (Fin t)} (h : ∀ j ∈ S, v j = w j)
    (fix : Bool) :
    ((tau ζ t ε v : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) *
        planeIdem t ε S fix =
      ((tau ζ t ε w : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) *
        planeIdem t ε S fix := by
  rw [coe_tau_eq_fromBlocks_spTau, coe_tau_eq_fromBlocks_spTau, planeIdem_eq_fromBlocks,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add, Matrix.one_mul]
  rw [SpBlocks.tau_mul_planeIdem_eq ζ t h]

private theorem tau_zero (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ)
    (ε : Fin 2) : tau ζ t ε (0 : PlaneRaw.V t) = 1 := by
  have h : (fun i => Multiplicative.ofAdd ((0 : PlaneRaw.V t) i)) = 1 := by
    funext i
    rfl
  rw [tau, h, map_one]

private theorem tau_nsmul (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ)
    (ε : Fin 2) (n : ℕ) (v : PlaneRaw.V t) : tau ζ t ε (n • v) = tau ζ t ε v ^ n := by
  have h : (fun i => Multiplicative.ofAdd ((n • v) i)) =
      (fun i => Multiplicative.ofAdd (v i)) ^ n := by
    funext i
    rw [Pi.pow_apply, Pi.smul_apply, ofAdd_nsmul]
  rw [tau, tau, h, map_pow]

private theorem commute_of_mem_adjoin {R : Type} [CommRing R] {ι : Type} [Fintype ι]
    [DecidableEq ι] {S : Set (GL ι R)} {g : GL ι R} (hg : g ∈ Subgroup.centralizer S)
    {a : Matrix ι ι R} (ha : a ∈ Algebra.adjoin R (Units.val '' S)) :
    (g : Matrix ι ι R) * a = a * (g : Matrix ι ι R) := by
  refine Algebra.adjoin_induction (p := fun x _ =>
    (g : Matrix ι ι R) * x = x * (g : Matrix ι ι R)) ?_ ?_ ?_ ?_ ha
  · rintro x ⟨s, hs, rfl⟩
    have h := Subgroup.mem_centralizer_iff.mp hg s hs
    rw [← Units.val_mul, ← Units.val_mul, h]
  · intro r
    exact (Algebra.commutes r _).symm
  · intro x y _ _ hx hy
    rw [Matrix.mul_add, Matrix.add_mul, hx, hy]
  · intro x y _ _ hx hy
    rw [← Matrix.mul_assoc, hx, Matrix.mul_assoc, hy, Matrix.mul_assoc]

private theorem one_sub_mul_of_commute {R : Type} [Ring R] {ι : Type} [Fintype ι]
    [DecidableEq ι] {P g : Matrix ι ι R} (hg : g * P = P * g) (hfix : g * (1 - P) = 1 - P) :
    (1 - P) * g = 1 - P := by
  calc (1 - P) * g = 1 * g - P * g := sub_mul 1 P g
    _ = g - g * P := by rw [one_mul, ← hg]
    _ = g * 1 - g * P := by rw [mul_one]
    _ = g * (1 - P) := by rw [mul_sub, mul_one]
    _ = 1 - P := hfix

private theorem keyIdem_commute_of_mem_centralizer (h : LinIsPrimIdemInKeyIdem)
    [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) {t : ℕ} {ε : Fin 2} {U : Submodule (ZMod 3) (PlaneRaw.V t)}
    {c : PlaneRaw.Code t} (hc : PlaneRaw.occurs U c) (hne : 0 < keyDim ε c)
    {g : GL (LinIdx t ε) K} (hg : g ∈ Subgroup.centralizer (torusSet ζ t ε U)) :
    (g : Matrix (LinIdx t ε) (LinIdx t ε) K) * keyIdem t ε c =
      keyIdem t ε c * (g : Matrix (LinIdx t ε) (LinIdx t ε) K) :=
  commute_of_mem_adjoin hg (h ζ t ε hK hζ U c hc hne).1

private theorem blockGroup_le_centralizer
    (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (t : ℕ) (ε : Fin 2)
    (U : Submodule (ZMod 3) (PlaneRaw.V t)) {c : PlaneRaw.Code t}
    (hc : PlaneRaw.occurs U c) :
    blockGroup ζ t ε c ≤ Subgroup.centralizer (torusSet ζ t ε U) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  rintro s ⟨u, hu, rfl⟩
  apply Units.ext
  rw [Units.val_mul, Units.val_mul]
  cases c with
  | zero S =>
    obtain ⟨hfix, hfix'⟩ := hg
    have hσ : (1 : Matrix (LinIdx t ε) (LinIdx t ε) K) * planeIdem t ε S true =
        ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) *
          planeIdem t ε S true := by
      have h0 : ((tau ζ t ε (0 : PlaneRaw.V t) : GL (LinIdx t ε) K) :
          Matrix (LinIdx t ε) (LinIdx t ε) K) = 1 := by
        rw [tau_zero]
        rfl
      have h := tau_mul_planeIdem_eq ζ t ε (v := (0 : PlaneRaw.V t)) (w := u) (S := S)
        (fun j hj => ((hc j).1 hj ⟨u, hu⟩).symm) true
      rwa [h0] at h
    exact (SpBlocks.commute_of_block hfix hfix' (tau_mul_planeIdem_comm ζ t ε u S true) hσ
      (by rw [mul_one, one_mul])).symm
  | extension e =>
    have hLE : g ∈ levi (planeIdem t ε (PlaneRaw.Code.extSupport e) false) ⊓
        Subgroup.centralizer {tau ζ t ε e} := hg
    obtain ⟨hfix, hfix'⟩ := (Subgroup.mem_inf.mp hLE).1
    have hcomm : g * tau ζ t ε e = tau ζ t ε e * g :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hLE).2
    obtain ⟨-, χ, hχ, hsupp, -⟩ := hc
    have hej : ∀ j ∈ PlaneRaw.Code.extSupport e, e j ≠ 0 := fun j hj =>
      (Finset.mem_filter.mp hj).2
    have hT : ∀ j ∈ PlaneRaw.Code.extSupport e, ((χ ⟨u, hu⟩).val • e) j = u j := by
      intro j hj
      calc ((χ ⟨u, hu⟩).val • e) j = χ ⟨u, hu⟩ * e j := by
            rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val]
        _ = u j := by
            change χ ⟨u, hu⟩ * e j = PlaneRaw.evalRestr U j ⟨u, hu⟩
            rw [hsupp j (hej j hj), LinearMap.smul_apply, smul_eq_mul, mul_comm]
    have hσ := tau_mul_planeIdem_eq ζ t ε (v := (χ ⟨u, hu⟩).val • e) (w := u)
      (S := PlaneRaw.Code.extSupport e) hT false
    have hpow : (g : Matrix (LinIdx t ε) (LinIdx t ε) K) *
        ((tau ζ t ε ((χ ⟨u, hu⟩).val • e) : GL (LinIdx t ε) K) :
          Matrix (LinIdx t ε) (LinIdx t ε) K) =
        ((tau ζ t ε ((χ ⟨u, hu⟩).val • e) : GL (LinIdx t ε) K) :
          Matrix (LinIdx t ε) (LinIdx t ε) K) *
          (g : Matrix (LinIdx t ε) (LinIdx t ε) K) := by
      have hp : (g : GL (LinIdx t ε) K) * tau ζ t ε ((χ ⟨u, hu⟩).val • e) =
          tau ζ t ε ((χ ⟨u, hu⟩).val • e) * (g : GL (LinIdx t ε) K) := by
        rw [tau_nsmul]
        exact Commute.pow_right hcomm _
      simpa only [Units.val_mul] using congrArg Units.val hp
    exact (SpBlocks.commute_of_block hfix hfix'
      (tau_mul_planeIdem_comm ζ t ε u (PlaneRaw.Code.extSupport e) false) hσ hpow).symm

theorem linGlBlockCentralizerKeyIdem_of (h : LinIsPrimIdemInKeyIdem) :
    LinGlBlockCentralizerKeyIdem := by
  intro K _ _ _ ζ t ε hK hζ U c hc hne
  have hBC := blockGroup_le_centralizer ζ t ε U hc
  ext g
  rw [glBlockCentralizer, Subgroup.comap_id]
  cases c with
  | zero S =>
    show (g ∈ Subgroup.centralizer (torusSet ζ t ε U) ⊓
        glFixing (1 - planeIdem t ε S true)) ↔ g ∈ levi (planeIdem t ε S true)
    rw [Subgroup.mem_inf]
    constructor
    · rintro ⟨hcent, hfix⟩
      have hP : (g : Matrix (LinIdx t ε) (LinIdx t ε) K) * planeIdem t ε S true =
          planeIdem t ε S true * (g : Matrix (LinIdx t ε) (LinIdx t ε) K) :=
        keyIdem_commute_of_mem_centralizer h hK hζ hc hne hcent
      exact ⟨hfix, one_sub_mul_of_commute hP hfix⟩
    · rintro ⟨hfix, hfix'⟩
      exact ⟨hBC ⟨hfix, hfix'⟩, hfix⟩
  | extension e =>
    show (g ∈ Subgroup.centralizer (torusSet ζ t ε U) ⊓
        glFixing (1 - planeIdem t ε (PlaneRaw.Code.extSupport e) false)) ↔
      g ∈ levi (planeIdem t ε (PlaneRaw.Code.extSupport e) false) ⊓
        Subgroup.centralizer {tau ζ t ε e}
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hcent, hfix⟩
      have hP : (g : Matrix (LinIdx t ε) (LinIdx t ε) K) *
          planeIdem t ε (PlaneRaw.Code.extSupport e) false =
          planeIdem t ε (PlaneRaw.Code.extSupport e) false *
            (g : Matrix (LinIdx t ε) (LinIdx t ε) K) :=
        keyIdem_commute_of_mem_centralizer h hK hζ hc hne hcent
      have hfix' := one_sub_mul_of_commute hP hfix
      refine ⟨⟨hfix, hfix'⟩, ?_⟩
      obtain ⟨-, χ, hχ, hsupp, -⟩ := hc
      have hej : ∀ j ∈ PlaneRaw.Code.extSupport e, e j ≠ 0 := fun j hj =>
        (Finset.mem_filter.mp hj).2
      obtain ⟨u₁, hu₁⟩ : ∃ u : ↥U, χ u ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hχ (LinearMap.ext hcon)
      set u₀ : ↥U := (χ u₁)⁻¹ • u₁ with hu₀
      have hχ₀ : χ u₀ = 1 := by
        rw [hu₀, map_smul, smul_eq_mul, inv_mul_cancel₀ hu₁]
      have h₀T : ∀ j ∈ PlaneRaw.Code.extSupport e, (u₀ : PlaneRaw.V t) j = e j := by
        intro j hj
        change PlaneRaw.evalRestr U j u₀ = e j
        rw [hsupp j (hej j hj), LinearMap.smul_apply, hχ₀, smul_eq_mul, mul_one]
      have hgσ := Subgroup.mem_centralizer_iff.mp hcent
        (tau ζ t ε (u₀ : PlaneRaw.V t)) ⟨u₀, u₀.2, rfl⟩
      have hgσ' := congrArg Units.val hgσ
      rw [Units.val_mul, Units.val_mul] at hgσ'
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      exact SpBlocks.commute_of_block hfix hfix' (tau_mul_planeIdem_comm ζ t ε e _ false)
        (tau_mul_planeIdem_eq ζ t ε (v := (u₀ : PlaneRaw.V t)) (w := e)
          (S := PlaneRaw.Code.extSupport e) h₀T false) hgσ'.symm
    · rintro ⟨⟨hfix, hfix'⟩, hcomm⟩
      refine ⟨hBC ⟨⟨hfix, hfix'⟩,
        Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩, hfix⟩

theorem linYcodeLeCentralizer_holds : LinYcodeLeCentralizer := by
  intro K _ _ _ ζ t ε _ _ U c hc _
  exact (Subgroup.commutator_le_of_le le_rfl le_rfl).trans
    (blockGroup_le_centralizer ζ t ε U hc)

theorem linNormalYcode_of (h : LinIsPrimIdemInKeyIdem) : LinNormalYcode := by
  intro K _ _ _ ζ t ε hK hζ U c hc hne
  have hBC := blockGroup_le_centralizer ζ t ε U hc
  rw [Subgroup.normal_subgroupOf_iff (linYcodeLeCentralizer_holds ζ t ε hK hζ U c hc hne)]
  intro x k hx hk
  have hkP : (k : Matrix (LinIdx t ε) (LinIdx t ε) K) * keyIdem t ε c =
      keyIdem t ε c * (k : Matrix (LinIdx t ε) (LinIdx t ε) K) :=
    keyIdem_commute_of_mem_centralizer h hK hζ hc hne hk
  have hkiP := keyIdem_commute_of_mem_centralizer h hK hζ hc hne (Subgroup.inv_mem _ hk)
  have hkQ : (k : Matrix (LinIdx t ε) (LinIdx t ε) K) * (1 - keyIdem t ε c) =
      (1 - keyIdem t ε c) * (k : Matrix (LinIdx t ε) (LinIdx t ε) K) :=
    (Commute.sub_right (Commute.one_right _) hkP).eq
  have hkiQ : ((k⁻¹ : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) *
      (1 - keyIdem t ε c) = (1 - keyIdem t ε c) *
        ((k⁻¹ : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) :=
    (Commute.sub_right (Commute.one_right _) hkiP).eq
  have hkk : (k : Matrix (LinIdx t ε) (LinIdx t ε) K) *
      ((k⁻¹ : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) = 1 := by
    have h' := congrArg (fun u : GL (LinIdx t ε) K =>
      (u : Matrix (LinIdx t ε) (LinIdx t ε) K)) (mul_inv_cancel k)
    simpa only [Units.val_mul, Units.val_one] using h'
  have hB : (blockGroup ζ t ε c).map (MulAut.conj k).toMonoidHom ≤ blockGroup ζ t ε c := by
    rintro _ ⟨b, hb, rfl⟩
    have hbFix : (b : Matrix (LinIdx t ε) (LinIdx t ε) K) * (1 - keyIdem t ε c) =
        1 - keyIdem t ε c := by
      have hb' : b ∈ glBlockCentralizer (MonoidHom.id (GL (LinIdx t ε) K))
          (torusSet ζ t ε U) (keyIdem t ε c) := by
        rw [linGlBlockCentralizerKeyIdem_of h ζ t ε hK hζ U c hc hne]
        exact hb
      rw [glBlockCentralizer, Subgroup.comap_id] at hb'
      exact (Subgroup.mem_inf.mp hb').2
    rw [← linGlBlockCentralizerKeyIdem_of h ζ t ε hK hζ U c hc hne]
    rw [glBlockCentralizer, Subgroup.comap_id]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hk (hBC hb)) (Subgroup.inv_mem _ hk), ?_⟩
    show ((k * b * k⁻¹ : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) *
        (1 - keyIdem t ε c) = 1 - keyIdem t ε c
    rw [Units.val_mul, Units.val_mul]
    calc (k : Matrix (LinIdx t ε) (LinIdx t ε) K) * (b : Matrix (LinIdx t ε) (LinIdx t ε) K) *
          ((k⁻¹ : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) *
            (1 - keyIdem t ε c) =
        (k : Matrix (LinIdx t ε) (LinIdx t ε) K) *
          ((b : Matrix (LinIdx t ε) (LinIdx t ε) K) * (1 - keyIdem t ε c)) *
            ((k⁻¹ : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) := by
          simp only [Matrix.mul_assoc]
          rw [hkiQ]
      _ = (1 - keyIdem t ε c) * ((k : Matrix (LinIdx t ε) (LinIdx t ε) K) *
            ((k⁻¹ : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K)) := by
          rw [hbFix, hkQ, Matrix.mul_assoc]
      _ = 1 - keyIdem t ε c := by rw [hkk, Matrix.mul_one]
  have hmem := Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom hx
  rw [Ycode, Subgroup.map_commutator] at hmem
  have hmem' := Subgroup.commutator_mono hB hB hmem
  rw [Ycode]
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem'

end CFSG.StandardType.GGQ2Frame.LinBlocks

end
