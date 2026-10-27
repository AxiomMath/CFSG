module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpStatements
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksIdem
import CFSG.LocalAnalysis.StandardType.ClassicalPosition.GeoAdj
import CFSG.Open.StatedAPI

public section

namespace CFSG.StandardType.GGQ2Frame.SpBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition Matrix
open CFSG.Open (StatedSp)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K]

theorem commute_of_block {R : Type} [Ring R] {g τ σ ε : R} (hg : g * (1 - ε) = 1 - ε)
    (hg' : (1 - ε) * g = 1 - ε) (hτε : τ * ε = ε * τ) (hσ : σ * ε = τ * ε)
    (hgσ : g * σ = σ * g) : g * τ = τ * g := by
  have h1 : g * ε = g - (1 - ε) := by rw [← hg, mul_sub, mul_one, sub_sub_cancel]
  have h2 : ε * g = g - (1 - ε) := by rw [← hg', sub_mul, one_mul, sub_sub_cancel]
  have h3 : g * ε = ε * g := h1.trans h2.symm
  have haτ : (1 - ε) * τ = τ * (1 - ε) := by rw [sub_mul, mul_sub, one_mul, mul_one, hτε]
  have L : g * τ = (1 - ε) * τ + σ * (g * ε) := by
    calc g * τ = g * ((1 - ε) * τ) + g * (ε * τ) := by
          rw [← mul_add, sub_mul, one_mul, sub_add_cancel]
      _ = (1 - ε) * τ + σ * (g * ε) := by
          rw [← mul_assoc g (1 - ε) τ, hg, ← hτε, ← hσ, ← mul_assoc g σ ε, hgσ, mul_assoc σ g ε]
  have R' : τ * g = τ * (1 - ε) + σ * (g * ε) := by
    calc τ * g = τ * ((1 - ε) * g) + τ * (ε * g) := by
          rw [← mul_add, sub_mul, one_mul, sub_add_cancel]
      _ = τ * (1 - ε) + σ * (g * ε) := by
          rw [hg', ← mul_assoc τ ε g, ← hσ, mul_assoc σ ε g, ← h3]
  rw [L, R', haτ]

theorem one_sub_planeIdem_mul_of_mem {m : ℕ} {S : Finset (Fin m)} {g : GL (Fin m ⊕ Fin m) K}
    (hg : g ∈ StatedSp m K)
    (hfix : (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * (1 - planeIdem m S) =
      1 - planeIdem m S) :
    (1 - planeIdem m S) * (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 1 - planeIdem m S := by
  have hJdet : IsUnit (fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).det :=
    Matrix.isUnit_det_of_left_inverse (B := -fromBlocks 0 1 (-1) 0)
      (by rw [neg_mul, symJ_mul_self, neg_neg])
  have hadj : formAdj (RingHom.id K)
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
      (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
        ((g⁻¹ : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
    refine Geo.formAdj_eq_inv_of_isometry (RingHom.id K) hJdet g ?_
    have hmap : (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).map (RingHom.id K) = g := by
      ext a b
      rfl
    rw [hmap]
    exact CFSG.Open.StatedAPI.mem_statedSp_iff.mp hg
  have hP : formAdj (RingHom.id K)
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) (1 - planeIdem m S) =
        1 - planeIdem m S := by
    have h := Geo.formAdj_add (RingHom.id K)
      (fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
      (1 - planeIdem m S) (planeIdem m S)
    rw [sub_add_cancel, Geo.formAdj_one (RingHom.id K) hJdet, formAdj_planeIdem] at h
    exact eq_sub_iff_add_eq.mpr h.symm
  have h1 := congrArg (formAdj (RingHom.id K)
    (fromBlocks 0 1 (-1) 0 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) hfix
  rw [Geo.formAdj_mul (RingHom.id K) hJdet, hadj, hP] at h1
  calc (1 - planeIdem m S) * (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
        (1 - planeIdem m S) * ((g⁻¹ : GL (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
            (g : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by rw [h1]
    _ = 1 - planeIdem m S := by
        rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

theorem coe_mul_comm_of_mul_comm {m : ℕ} {a b : ↥(StatedSp m K)} (h : a * b = b * a) :
    ((a : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        ((b : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      ((b : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        ((a : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
  have h' := congrArg (fun x : ↥(StatedSp m K) =>
    ((x : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) h
  simpa only [Subgroup.coe_mul, Units.val_mul] using h'

theorem tau_zero (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m : ℕ) :
    tau ζ m (0 : PlaneRaw.V m) = 1 := by
  have h : (fun i => Multiplicative.ofAdd ((0 : PlaneRaw.V m) i)) = 1 := by
    funext i
    rfl
  rw [tau, h, map_one]

theorem tau_nsmul (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) (m n : ℕ)
    (v : PlaneRaw.V m) : tau ζ m (n • v) = tau ζ m v ^ n := by
  have h : (fun i => Multiplicative.ofAdd ((n • v) i)) =
      (fun i => Multiplicative.ofAdd (v i)) ^ n := by
    funext i
    rw [Pi.pow_apply, Pi.smul_apply, ofAdd_nsmul]
  rw [tau, tau, h, map_pow]

theorem tau_mul_planeIdem_comm (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
    (m : ℕ) (v : PlaneRaw.V m) (S : Finset (Fin m)) :
    (((tau ζ m v : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * planeIdem m S =
      planeIdem m S * (((tau ζ m v : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
  rw [coe_tau, planeIdem_eq_planeMat, WitSpNs.planeMat_mul, WitSpNs.planeMat_mul]
  congr 1
  funext j
  split_ifs <;> simp

theorem tau_mul_planeIdem_eq (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
    (m : ℕ) {v w : PlaneRaw.V m} {S : Finset (Fin m)} (h : ∀ j ∈ S, v j = w j) :
    (((tau ζ m v : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * planeIdem m S =
      (((tau ζ m w : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * planeIdem m S := by
  rw [coe_tau, coe_tau, planeIdem_eq_planeMat, WitSpNs.planeMat_mul, WitSpNs.planeMat_mul]
  congr 1
  funext j
  split_ifs with hj
  · rw [h j hj]
  · simp

theorem spGlBlockCentralizerPlaneIdem_holds : SpGlBlockCentralizerPlaneIdem := by
  intro K _ _ _ ζ m hK hζ U c hc hne
  ext g
  have hgSp : (g : GL (Fin m ⊕ Fin m) K) ∈ StatedSp m K := g.2
  change ((g : GL (Fin m ⊕ Fin m) K) ∈ Subgroup.centralizer (torusSet ζ m U) ∧
      ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        (1 - planeIdem m c.support) = 1 - planeIdem m c.support) ↔ g ∈ blockGroup ζ m c
  cases c with
  | zero S =>
    change _ ↔ ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        (1 - planeIdem m S) = 1 - planeIdem m S
    refine ⟨fun h => h.2, fun hfix => ⟨?_, hfix⟩⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro t ⟨u, hu, rfl⟩
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    have h0 : (((tau ζ m 0 : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 1 := by
      rw [tau_zero]
      rfl
    have hσ := tau_mul_planeIdem_eq ζ m (v := 0) (w := u) (S := S)
      fun j hj => ((hc j).1 hj ⟨u, hu⟩).symm
    rw [h0] at hσ
    exact (commute_of_block hfix (one_sub_planeIdem_mul_of_mem hgSp hfix)
      (tau_mul_planeIdem_comm ζ m u S) hσ (by rw [mul_one, one_mul])).symm
  | extension e =>
    change _ ↔ ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        (1 - planeIdem m (PlaneRaw.Code.extSupport e)) =
          1 - planeIdem m (PlaneRaw.Code.extSupport e) ∧
        g ∈ Subgroup.centralizer ({tau ζ m e} : Set ↥(StatedSp m K))
    obtain ⟨-, χ, hχ, hsupp, -⟩ := hc
    have hej : ∀ j ∈ PlaneRaw.Code.extSupport e, e j ≠ 0 := fun j hj =>
      (Finset.mem_filter.mp hj).2
    have hT : ∀ (u : PlaneRaw.V m) (hu : u ∈ U), ∀ j ∈ PlaneRaw.Code.extSupport e,
        ((χ ⟨u, hu⟩).val • e) j = u j := by
      intro u hu j hj
      calc ((χ ⟨u, hu⟩).val • e) j = χ ⟨u, hu⟩ * e j := by
            rw [Pi.smul_apply, nsmul_eq_mul, ZMod.natCast_zmod_val]
        _ = u j := by
            change χ ⟨u, hu⟩ * e j = PlaneRaw.evalRestr U j ⟨u, hu⟩
            rw [hsupp j (hej j hj), LinearMap.smul_apply, smul_eq_mul, mul_comm]
    obtain ⟨u₁, hu₁⟩ : ∃ u, χ u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hχ (LinearMap.ext hcon)
    set u₀ : ↥U := (χ u₁)⁻¹ • u₁ with hu₀
    have hχ₀ : χ u₀ = 1 := by
      rw [hu₀, map_smul, smul_eq_mul, inv_mul_cancel₀ hu₁]
    have h₀T : ∀ j ∈ PlaneRaw.Code.extSupport e, (u₀ : PlaneRaw.V m) j = e j := by
      intro j hj
      change PlaneRaw.evalRestr U j u₀ = e j
      rw [hsupp j (hej j hj), LinearMap.smul_apply, hχ₀, smul_eq_mul, mul_one]
    constructor
    · rintro ⟨hcent, hfix⟩
      refine ⟨hfix, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul]
      have hgσ := Subgroup.mem_centralizer_iff.mp hcent
        ((tau ζ m (u₀ : PlaneRaw.V m) : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K)
        ⟨u₀, u₀.2, rfl⟩
      have hgσ' := congrArg Units.val hgσ
      rw [Units.val_mul, Units.val_mul] at hgσ'
      exact commute_of_block hfix (one_sub_planeIdem_mul_of_mem hgSp hfix)
        (tau_mul_planeIdem_comm ζ m e _) (tau_mul_planeIdem_eq ζ m h₀T) hgσ'.symm
    · rintro ⟨hfix, hcomm⟩
      refine ⟨?_, hfix⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hcomm
      rw [Subgroup.mem_centralizer_iff]
      rintro t ⟨u, hu, rfl⟩
      apply Units.ext
      rw [Units.val_mul, Units.val_mul]
      have hpow : g * tau ζ m ((χ ⟨u, hu⟩).val • e) = tau ζ m ((χ ⟨u, hu⟩).val • e) * g := by
        rw [tau_nsmul]
        exact Commute.pow_right hcomm _
      exact (commute_of_block hfix (one_sub_planeIdem_mul_of_mem hgSp hfix)
        (tau_mul_planeIdem_comm ζ m u _) (tau_mul_planeIdem_eq ζ m (hT u hu))
        (coe_mul_comm_of_mul_comm hpow)).symm

theorem blockGroup_le_centralizer [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} (U : Submodule (ZMod 3) (PlaneRaw.V m)) {c : PlaneRaw.Code m}
    (hc : PlaneRaw.occurs U c) (hne : c.support.Nonempty) :
    blockGroup ζ m c ≤ (Subgroup.centralizer (torusSet ζ m U)).comap (StatedSp m K).subtype := by
  rw [← spGlBlockCentralizerPlaneIdem_holds ζ m hK hζ U c hc hne]
  exact Subgroup.comap_mono inf_le_left

theorem spYcodeLeCentralizer_holds : SpYcodeLeCentralizer := by
  intro K _ _ _ ζ m hK hζ U c hc hne
  exact (Subgroup.commutator_le_of_le le_rfl le_rfl).trans
    (blockGroup_le_centralizer hK hζ U hc hne)

theorem map_conj_blockGroup_le [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} (U : Submodule (ZMod 3) (PlaneRaw.V m)) {c : PlaneRaw.Code m}
    (hc : PlaneRaw.occurs U c) (hne : c.support.Nonempty) {k : ↥(StatedSp m K)}
    (hk : k ∈ (Subgroup.centralizer (torusSet ζ m U)).comap (StatedSp m K).subtype) :
    (blockGroup ζ m c).map (MulAut.conj k).toMonoidHom ≤ blockGroup ζ m c := by
  have hBC := blockGroup_le_centralizer hK hζ U hc hne
  have hkε := commute_planeIdem_of_mem_centralizer hK hζ U hc
    (g := (k : GL (Fin m ⊕ Fin m) K)) hk
  have hk' : k⁻¹ ∈ (Subgroup.centralizer (torusSet ζ m U)).comap (StatedSp m K).subtype :=
    Subgroup.inv_mem _ hk
  have hkiε := commute_planeIdem_of_mem_centralizer hK hζ U hc
    (g := ((k⁻¹ : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K)) hk'
  have hone : ∀ {x : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K},
      x * planeIdem m c.support = planeIdem m c.support * x →
        x * (1 - planeIdem m c.support) = (1 - planeIdem m c.support) * x := by
    intro x hx
    rw [mul_sub, sub_mul, mul_one, one_mul, hx]
  have hkk : ((k : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      (((k⁻¹ : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) = 1 := by
    have h' := congrArg (fun x : ↥(StatedSp m K) =>
      ((x : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K))
      (mul_inv_cancel k)
    simpa only [Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one] using h'
  rintro _ ⟨b, hb, rfl⟩
  have hbG : b ∈ glBlockCentralizer (StatedSp m K).subtype (torusSet ζ m U)
      (planeIdem m c.support) := by
    rw [spGlBlockCentralizerPlaneIdem_holds ζ m hK hζ U c hc hne]
    exact hb
  have hbF : ((b : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
      (1 - planeIdem m c.support) = 1 - planeIdem m c.support := hbG.2
  rw [← spGlBlockCentralizerPlaneIdem_holds ζ m hK hζ U c hc hne]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hk (hBC hb)) hk', ?_⟩
  change (((k * b * k⁻¹ : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * (1 - planeIdem m c.support) =
      1 - planeIdem m c.support
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul]
  calc ((k : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        ((b : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        (((k⁻¹ : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * (1 - planeIdem m c.support) =
        ((k : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
          (((b : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
            (1 - planeIdem m c.support)) *
          (((k⁻¹ : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
            Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
        rw [Matrix.mul_assoc _ _ (1 - planeIdem m c.support), hone hkiε]
        simp only [Matrix.mul_assoc]
    _ = (1 - planeIdem m c.support) *
          (((k : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
            (((k⁻¹ : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
              Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) := by
        rw [hbF, hone hkε, Matrix.mul_assoc]
    _ = 1 - planeIdem m c.support := by rw [hkk, Matrix.mul_one]

theorem spNormalYcode_holds : SpNormalYcode := by
  intro K _ _ _ ζ m hK hζ U c hc hne
  rw [Subgroup.normal_subgroupOf_iff (spYcodeLeCentralizer_holds ζ m hK hζ U c hc hne)]
  intro h k hh hk
  have hB := map_conj_blockGroup_le hK hζ U hc hne hk
  have hmem := Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom hh
  rw [Ycode, Subgroup.map_commutator] at hmem
  have hmem' := Subgroup.commutator_mono hB hB hmem
  rw [Ycode]
  simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem'

end CFSG.StandardType.GGQ2Frame.SpBlocks
