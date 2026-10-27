module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXDetDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoLDatumWeyl
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDatumDet
public import CFSG.LocalAnalysis.StandardType.GGQTwoCor123
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrLineStab
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private lemma ggQ2xd_model_nsmul {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {Bs L : Subgroup G} {x : G} (M : GGQ2LDatum p Bs L x) (n : ℕ) (b : ↥Bs) :
    M.model (n • Additive.ofMul b) = n • M.model (Additive.ofMul b) :=
  (M.model.toAddMonoidHom).map_nsmul n (Additive.ofMul b)

theorem ggQ2xd_gammaX_of_datumPM (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) (hp : p = 3)
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) (M : GGQ2LDatum p Bs L x)
    (hpm : ∀ u₀ : M.toWDatum.V, u₀ ≠ 0 →
      (∀ v : M.toWDatum.V, (∀ g ∈ M.toWDatum.weyl, g v = v) ↔
        v ∈ Submodule.span (ZMod p) {u₀}) →
      Module.finrank (ZMod p) M.toWDatum.V ≤ Fintype.card M.toWDatum.Λ + 1 →
      4 ≤ Module.finrank (ZMod p) M.toWDatum.V → TransvectionFree M.toWDatum.weyl →
      ∀ T : M.toWDatum.V ≃ₗ[ZMod p] M.toWDatum.V,
        T ∈ Subgroup.normalizer (M.toWDatum.weyl : Set (M.toWDatum.V ≃ₗ[ZMod p] M.toWDatum.V)) →
        ∃ w ∈ M.toWDatum.weyl, ∃ ε : ZMod p, (ε = 1 ∨ ε = -1) ∧
          ∀ v : M.toWDatum.V, T (w v) - ε • v ∈ Submodule.span (ZMod p) {u₀}) :
    GGQ2GammaX p B Bs x L D J := by
  subst hp
  classical
  obtain ⟨hcfg, -, -, -, -⟩ := hS.1
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hSstar : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hSstar.2.2.1
  have hx_D : x ∈ D := hStdSub.1.2.2.2.1
  have hDBs : D ≤ Bs := hStdSub.1.1.trans hBstar.1
  have hAJ : ggAutomizer J Bs ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hCav
    norm_num at hCav
  have hcard_bs : Nat.card ↥Bs = 3 ^ Module.finrank (ZMod 3) M.V := by
    have : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := rfl
      _ = Nat.card M.V := Nat.card_congr M.model.toEquiv
      _ = 3 ^ Module.finrank (ZMod 3) M.V := (FiniteField.pow_finrank_eq_natCard 3 M.V).symm
  have h4 : 4 ≤ Module.finrank (ZMod 3) M.V := by
    have hp4 : 3 ^ 4 ≤ Nat.card ↥Bs := (hS.1.1.tableB_facts).2.2.2.2
    rw [hcard_bs] at hp4
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hp4
  let D' : GGQ2WDatum 3 :=
    { Λ := M.Λ
      coxeter := M.coxeter
      cartan := M.cartan
      V := M.V
      coroot := M.coroot
      root := M.root
      isWeyl := M.isWeyl
      isCartan := M.isCartan
      pairing := M.pairing }
  have hpm' : ∀ u₀ : D'.V, u₀ ≠ 0 →
      (∀ v : D'.V, (∀ g ∈ D'.weyl, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {u₀}) →
      Module.finrank (ZMod 3) D'.V ≤ Fintype.card D'.Λ + 1 →
      4 ≤ Module.finrank (ZMod 3) D'.V → TransvectionFree D'.weyl →
      ∀ T : D'.V ≃ₗ[ZMod 3] D'.V,
        T ∈ Subgroup.normalizer (D'.weyl : Set (D'.V ≃ₗ[ZMod 3] D'.V)) →
        ∃ w ∈ D'.weyl, ∃ ε : ZMod 3, (ε = 1 ∨ ε = -1) ∧
          ∀ v : D'.V, T (w v) - ε • v ∈ Submodule.span (ZMod 3) {u₀} := hpm
  have hweyl : D'.weyl = (ggAutomizer L Bs).map (ggLin (p := 3) M.model) :=
    GGQ2LDatum.weyl_eq_map M
  have hxV0 : M.xV ≠ 0 := by
    intro h0
    have h1 : Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) = 0 :=
      M.model.injective (by rw [map_zero]; exact h0)
    have h2 : (⟨x, M.hx⟩ : ↥Bs) = 1 := Additive.ofMul.injective (by simpa using h1)
    exact hx1 (Subtype.ext_iff.mp h2)
  intro g hg hgx
  let φ : MulAut ↥Bs := ggConjAut Bs hg
  have hφ : φ ∈ ggAutomizer ⊤ Bs := ggConjAut_mem_ggAutomizer (Subgroup.mem_top g) hg
  have hφg : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹ := by
    intro b
    exact ggConjAut_apply Bs hg b
  have hφx : φ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hgx
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    apply Subtype.ext
    rw [Subgroup.coe_zpow, ggConjAut_apply]
    exact hk
  have hφN : φ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) :=
    ggQ2_lineStab_normalizes_L hLB hP hS.1 hAJ M.hx hφ hφx
  let T : D'.V ≃ₗ[ZMod 3] D'.V := ggLin (p := 3) M.model φ
  have hTnorm : T ∈ Subgroup.normalizer
      (D'.weyl : Set (D'.V ≃ₗ[ZMod 3] D'.V)) := by
    rw [hweyl]
    exact Subgroup.le_normalizer_map (ggLin (p := 3) M.model)
      (Subgroup.mem_map.mpr ⟨φ, hφN, rfl⟩)
  have hfix2 : ∀ v : D'.V,
      (∀ g ∈ D'.weyl, g v = v) ↔ v ∈ Submodule.span (ZMod 3) {M.xV} := by
    intro v
    rw [hweyl]
    have hmapfix : (∀ g ∈ (ggAutomizer L Bs).map (ggLin (p := 3) M.model), g v = v) ↔
        v ∈ ggFixedSubmodule (p := 3) M.model (ggAutomizer L Bs) := by
      simp only [mem_ggFixedSubmodule_iff]
      constructor
      · intro h ψ hψ
        exact h (ggLin (p := 3) M.model ψ) (Subgroup.mem_map.mpr ⟨ψ, hψ, rfl⟩)
      · rintro h g hg
        obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hg
        exact h ψ hψ
    rw [hmapfix, M.fixed_x]
    rfl
  have hdim : Module.finrank (ZMod 3) D'.V ≤ Fintype.card D'.Λ + 1 :=
    GGQ2WDatum.finrank_le_card_add_one_of_fix D' M.xV hfix2
  have hTF : TransvectionFree D'.weyl := by
    intro g' hg' htr
    rw [hweyl] at hg'
    obtain ⟨ψ, hψL, hψg⟩ := Subgroup.mem_map.mp hg'
    obtain ⟨w0, χ, hw0, hχ, hχw0, hgv⟩ := htr
    have hψtop : ψ ∈ ggInduced ⊤ Bs := by
      have h1 : ψ ∈ ggAutomizer ⊤ Bs := ggAutomizer_mono Bs le_top hψL
      rwa [ggAutomizer_eq] at h1
    exact hS.1.2.2.2.1 ψ hψtop (ggIsTransvection_of_apply M.model hw0 hχ hχw0 (fun v => by
      exact hψg ▸ hgv v))
  obtain ⟨w, hw, ε, hε, hwε⟩ := hpm' M.xV hxV0 hfix2 hdim h4 hTF T hTnorm
  have hw' : T * w * T⁻¹ ∈ D'.weyl :=
    (Subgroup.mem_normalizer_iff.mp hTnorm w).mp hw
  rw [hweyl] at hw'
  obtain ⟨ψ, hψL, hψw⟩ := Subgroup.mem_map.mp hw'
  have hD : ∀ b : ↥Bs, (b : G) ∈ D → (((ψ * φ) b : ↥Bs) : G) ∈ D := by
    intro b hbD
    obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp (hwε (M.model (Additive.ofMul b)))
    have hs' : s • M.xV = s.val • M.xV := by
      conv_lhs => rw [← ZMod.natCast_zmod_val s]
      rw [Nat.cast_smul_eq_nsmul]
    have hmodel_pow : M.model (Additive.ofMul ((⟨x, M.hx⟩ : ↥Bs) ^ s.val)) =
        s.val • M.xV := by
      rw [ofMul_pow, ggQ2xd_model_nsmul]
      rfl
    have heq : M.model (Additive.ofMul ((ψ * φ) b)) =
        (T * w * T⁻¹) (ggLin (p := 3) M.model φ (M.model (Additive.ofMul b))) := by
      rw [← ggLin_apply_ofMul (p := 3) M.model (ψ * φ) b, map_mul,
        LinearEquiv.mul_apply, hψw]
    have hTv : (T * w * T⁻¹) (T (M.model (Additive.ofMul b))) =
        T (w (M.model (Additive.ofMul b))) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
      congr 2
      exact T.symm_apply_apply _
    have hs1 : T (w (M.model (Additive.ofMul b))) =
        ε • M.model (Additive.ofMul b) + s • M.xV := by
      rw [hs]
      abel
    rcases hε with hε1 | hεm1
    · have key : M.model (Additive.ofMul ((ψ * φ) b)) =
          M.model (Additive.ofMul (b * (⟨x, M.hx⟩ : ↥Bs) ^ s.val)) := by
        rw [heq, hTv, hs1, hε1, one_smul, hs', ofMul_mul, map_add, hmodel_pow]
      have hd_eq : (ψ * φ) b = b * (⟨x, M.hx⟩ : ↥Bs) ^ s.val :=
        Additive.ofMul.injective (M.model.injective key)
      have hdmem : (((b * (⟨x, M.hx⟩ : ↥Bs) ^ s.val) : ↥Bs) : G) ∈ D := by
        have h1 : (((⟨x, M.hx⟩ : ↥Bs) ^ s.val : ↥Bs) : G) = x ^ s.val := by
          rw [Subgroup.coe_pow]
        rw [Subgroup.coe_mul, h1]
        exact D.mul_mem hbD (pow_mem hx_D s.val)
      rw [hd_eq]
      exact hdmem
    · have key : M.model (Additive.ofMul ((ψ * φ) b)) =
          M.model (Additive.ofMul (b⁻¹ * (⟨x, M.hx⟩ : ↥Bs) ^ s.val)) := by
        rw [heq, hTv, hs1, hεm1, hs', ofMul_mul, map_add, hmodel_pow]
        rw [show (-1 : ZMod 3) • M.model (Additive.ofMul b) = -M.model (Additive.ofMul b)
          from neg_one_smul (ZMod 3) _]
        rw [show M.model (Additive.ofMul b⁻¹) = -M.model (Additive.ofMul b) by
          rw [ofMul_inv, map_neg]]
      have hd_eq : (ψ * φ) b = b⁻¹ * (⟨x, M.hx⟩ : ↥Bs) ^ s.val :=
        Additive.ofMul.injective (M.model.injective key)
      have hdmem : (((b⁻¹ * (⟨x, M.hx⟩ : ↥Bs) ^ s.val) : ↥Bs) : G) ∈ D := by
        have h1 : (((⟨x, M.hx⟩ : ↥Bs) ^ s.val : ↥Bs) : G) = x ^ s.val := by
          rw [Subgroup.coe_pow]
        rw [Subgroup.coe_mul, Subgroup.coe_inv, h1]
        exact D.mul_mem (D.inv_mem hbD) (pow_mem hx_D s.val)
      rw [hd_eq]
      exact hdmem
  obtain ⟨k, hkL, hkN, hψk⟩ := mem_ggAutomizer_iff.mp hψL
  have hψφg : ∀ b : ↥Bs, (((ψ * φ) b : ↥Bs) : G) = (k * g) * b * (k * g)⁻¹ := by
    intro b
    rw [MulAut.mul_apply, hψk (φ b), hφg b]
    group
  have hmBs : k * g ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.mul_mem _ hkN hg
  have hmD : k * g ∈ Subgroup.normalizer (D : Set G) :=
    Subgroup.mem_normalizer_fintype (S := (D : Set G)) (fun n hn => by
      have hb := hD ⟨n, hDBs hn⟩ hn
      rwa [hψφg ⟨n, hDBs hn⟩] at hb)
  have hmG0 : k * g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
    ggQ2n_normalizer_inf_le hLB hP hS.1 rfl hCav (Subgroup.mem_inf.mpr ⟨hmBs, hmD⟩)
  have hkG0 : k ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
    Subgroup.le_normalizer (le_ggG0_left 3 B x L D J hkL)
  have hgG0 : g ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) := by
    have h : k⁻¹ * (k * g) ∈ Subgroup.normalizer (ggG0 3 B x L D J : Set G) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ hkG0) hmG0
    simpa using h
  exact hgG0

theorem ggQ2_gammaX_of_detLabel (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hCav : 4 ∣ Nat.card (ggAutomizer J Bs))
    (M : GGQ2LDatum 3 Bs L x) {lab : LargeEvenLabel} (hLW : GGQ2LabelWeyl lab M.coxeter)
    (hshape : M.Shape) (hdetlab : GGQ2DetLabel lab) (hnB : ¬ M.ShapeB) :
    GGQ2GammaX 3 B Bs x L D J := by
  classical
  have hdet0 : ((M.cartan.det : ℤ) : ZMod 3) = 0 := by
    rcases hdetlab with ⟨htag, hdvd⟩ | htag
    · have hLW' : ∃ e : Fin lab.rank ≃ M.Λ,
          M.coxeter = (CoxeterMatrix.A lab.rank).reindex e := by
        simpa only [GGQ2LabelWeyl, htag] using hLW
      obtain ⟨e, he⟩ := hLW'
      have hC : GGIntCartan ((CoxeterMatrix.A lab.rank).reindex e) M.cartan := by
        rw [← he]; exact M.isCartan
      have hC0 : GGIntCartan ((CoxeterMatrix.A lab.rank).reindex e)
          (Matrix.reindex e e (CartanMatrix.A lab.rank)) := (ggIntCartan_A lab.rank).reindex e
      have hone : GGAtMostOneMultipleEdge ((CoxeterMatrix.A lab.rank).reindex e) :=
        (ggAtMostOneMultipleEdge_A lab.rank).reindex e
      have hdet : M.cartan.det = (CartanMatrix.A lab.rank).det := by
        rcases hC.eq_or_eq_transpose hC0 hone with h | h
        · rw [h, Matrix.det_reindex_self e (CartanMatrix.A lab.rank)]
        · rw [h, Matrix.det_transpose, Matrix.det_reindex_self e (CartanMatrix.A lab.rank)]
      rw [hdet, CartanMatrix.A_det, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact_mod_cast hdvd
    · have hLW' : ∃ e : Fin 6 ≃ M.Λ, M.coxeter = CoxeterMatrix.E₆.reindex e := by
        simpa only [GGQ2LabelWeyl, htag] using hLW
      obtain ⟨e, he⟩ := hLW'
      have hC : GGIntCartan (CoxeterMatrix.E₆.reindex e) M.cartan := by
        rw [← he]; exact M.isCartan
      have hC0 : GGIntCartan (CoxeterMatrix.E₆.reindex e)
          (Matrix.reindex e e (CartanMatrix.E 6)) := ggIntCartan_E₆.reindex e
      have hone : GGAtMostOneMultipleEdge (CoxeterMatrix.E₆.reindex e) :=
        ggAtMostOneMultipleEdge_E₆.reindex e
      have hdet : M.cartan.det = (CartanMatrix.E 6).det := by
        rcases hC.eq_or_eq_transpose hC0 hone with h | h
        · rw [h, Matrix.det_reindex_self e (CartanMatrix.E 6)]
        · rw [h, Matrix.det_transpose, Matrix.det_reindex_self e (CartanMatrix.E 6)]
      rw [hdet, CartanMatrix.E₆_det, ZMod.intCast_zmod_eq_zero_iff_dvd]
      norm_num
  have hker : ∃ κ : M.Λ → ZMod 3, κ ≠ 0 ∧
      ∀ i : M.Λ, ∑ j : M.Λ, (M.cartan i j : ZMod 3) * κ j = 0 := by
    have hdet' : ((Int.castRingHom (ZMod 3)).mapMatrix M.cartan).det = 0 := by
      rw [← RingHom.map_det]
      exact hdet0
    obtain ⟨κ, hκ0, hκ⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet'
    refine ⟨κ, hκ0, fun i => ?_⟩
    simpa [Matrix.mulVec, dotProduct] using congrFun hκ i
  have hpos : LinearIndependent (ZMod 3) M.coroot ∨
      Module.finrank (ZMod 3) M.V = Fintype.card M.Λ + 1 := by
    rcases hshape with hF | hA | hB | hC | hD
    · exact Or.inl hF.2.1
    · exact Or.inl hA.2.1
    · exact absurd hB hnB
    · exact Or.inr hC.2.2.2.1
    · exact Or.inl hD.2.1
  exact ggQ2xd_gammaX_of_datumPM hLB hP hS rfl hCav M
    (fun u₀ hu₀ hfix hdim h4 hTF T hTnorm =>
      GGQ2WDatum.pmW_of_ker M.toWDatum u₀ hu₀ hfix hker hdim h4 hTF hpos T hTnorm)

end CFSG.StandardType

end
