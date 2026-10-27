module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112Lin
public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLDatum
public import CFSG.LocalAnalysis.StandardType.GGQTwoAjSetting
public import CFSG.LocalAnalysis.StandardType.GGQTwoK1Model
public import CFSG.LocalAnalysis.StandardType.GGQTwoCor81
public import CFSG.LocalAnalysis.StandardType.GGLineStabNormalizes

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggQ2xXL_gamma_of_normalizer_le {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (u : ↥Bs)
    (h : Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (ggG0 p B x L D J : Set G)) :
    GGGammaAt p B Bs x L D J u := by
  intro φ hφ _
  rw [mem_ggAutomizer_iff] at hφ ⊢
  obtain ⟨g, -, hgN, hg⟩ := hφ
  exact ⟨g, h hgN, hgN, hg⟩

private lemma ggQ2xXLg2_zsmul_model {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (n : ℤ) (b : ↥Bs) :
    M.model (n • Additive.ofMul b) = n • M.model (Additive.ofMul b) :=
  (M.model.toAddMonoidHom).map_zsmul n (Additive.ofMul b)

private lemma ggQ2xXLg2_nsmul_model {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (n : ℕ) (b : ↥Bs) :
    M.model (n • Additive.ofMul b) = n • M.model (Additive.ofMul b) :=
  (M.model.toAddMonoidHom).map_nsmul n (Additive.ofMul b)

private lemma ggQ2xXLg2_model_mem_span {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (c d : ↥Bs) (h : c ∈ Subgroup.zpowers d) :
    M.model (Additive.ofMul c) ∈ Submodule.span (ZMod p) {M.model (Additive.ofMul d)} := by
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp h
  rw [← hm, ofMul_zpow, ggQ2xXLg2_zsmul_model M m d]
  rw [← Int.cast_smul_eq_zsmul (R := ZMod p)]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

private theorem ggQ2xXLg2_ggLin_simple {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (k : M.ι) : ggLin (p := p) M.model (M.simple k) = M.toLin.simpleRefl k := by
  refine LinearEquiv.ext fun v => ?_
  rw [M.simple_apply]
  exact (Module.reflection_apply v (M.toLin.root_coroot_self k)).symm

private theorem ggQ2xXLg2_image_eq {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (S : Set M.ι) :
    ggLin (p := p) M.model '' (M.simple '' S) = M.toLin.simpleRefl '' S := by
  ext t
  constructor
  · rintro ⟨φ, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨k, hk, (ggQ2xXLg2_ggLin_simple M k).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨M.simple k, ⟨k, hk, rfl⟩, ggQ2xXLg2_ggLin_simple M k⟩

private theorem ggQ2xXLg2_parabL_eq {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (S : Set M.ι) :
    M.parabL S = (Subgroup.closure (M.simple '' S)).map (ggLin (p := p) M.model) := by
  rw [show M.parabL S = Subgroup.closure (M.toLin.simpleRefl '' S) from rfl,
    MonoidHom.map_closure, ggQ2xXLg2_image_eq]
  rfl

private theorem ggQ2xXLg2_parabL_L {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) :
    M.parabL {k | k ≠ M.a} = (ggAutomizer L Bs).map (ggLin (p := p) M.model) := by
  rw [ggQ2xXLg2_parabL_eq, ← M.automizer_L]

private lemma ggQ2xXLg2_pow_scalar_one {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (b : ↥Bs) :
    (1 : ZMod p) • M.model (Additive.ofMul b) =
      M.model (Additive.ofMul (b ^ (1 : ℤ))) := by
  rw [zpow_one, one_smul]

private lemma ggQ2xXLg2_pow_scalar_neg {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (b : ↥Bs) :
    (-1 : ZMod p) • M.model (Additive.ofMul b) =
      M.model (Additive.ofMul (b ^ (-1 : ℤ))) := by
  rw [zpow_neg_one, ofMul_inv, map_neg]
  exact neg_one_smul (ZMod p) (M.model (Additive.ofMul b))

private lemma ggQ2xXLg2_xV_pow {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (c : ZMod p) :
    c • M.xV = M.model (Additive.ofMul ((⟨x, M.hx⟩ : ↥Bs) ^ (c.val : ℤ))) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [GGQTwoModel.xV]
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [Nat.cast_smul_eq_nsmul, ← ggQ2xXLg2_nsmul_model M c.val ⟨x, M.hx⟩, ← ofMul_pow,
    zpow_natCast]

private lemma ggQ2xXLg2_T_w {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs : Subgroup G}
    {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K) (φ ψ : MulAut ↥Bs)
    (T : M.V ≃ₗ[ZMod p] M.V) (hT : T = ggLin (p := p) M.model φ)
    (w : M.V ≃ₗ[ZMod p] M.V) (hψw : ggLin (p := p) M.model ψ = w) (b : ↥Bs) :
    T (w (M.model (Additive.ofMul b))) = M.model (Additive.ofMul ((φ * ψ) b)) := by
  rw [hT, ← hψw, ggLin_apply_ofMul, ggLin_apply_ofMul, MulAut.mul_apply]

private lemma ggQ2xXLg2_scalar_step {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G} (M : GGQTwoModel p Bs x y D L J K)
    (φ ψ : MulAut ↥Bs) (T : M.V ≃ₗ[ZMod p] M.V) (hT : T = ggLin (p := p) M.model φ)
    (w : M.V ≃ₗ[ZMod p] M.V) (hψw : ggLin (p := p) M.model ψ = w) (ε : ZMod p)
    (ε' : ℤ)
    (hεpow : ∀ b : ↥Bs, ε • M.model (Additive.ofMul b) =
      M.model (Additive.ofMul (b ^ ε')))
    (hwε : ∀ v : M.V, T (w v) - ε • v ∈ Submodule.span (ZMod p) {M.xV}) (b : ↥Bs) :
    ∃ n : ℤ, ((φ * ψ) b : ↥Bs) = b ^ ε' * (⟨x, M.hx⟩ : ↥Bs) ^ n := by
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hwε (M.model (Additive.ofMul b)))
  refine ⟨(c.val : ℤ), ?_⟩
  have hTb := ggQ2xXLg2_T_w M φ ψ T hT w hψw b
  have hmain : M.model (Additive.ofMul ((φ * ψ) b)) =
      ε • M.model (Additive.ofMul b) + c • M.xV := by
    have h := eq_add_of_sub_eq hc.symm
    rw [← hTb]
    exact h.trans (add_comm _ _)
  have hpw := hεpow b
  have hxw := ggQ2xXLg2_xV_pow M c
  have hfin : M.model (Additive.ofMul ((φ * ψ) b)) =
      M.model (Additive.ofMul (b ^ ε' * (⟨x, M.hx⟩ : ↥Bs) ^ (c.val : ℤ))) := by
    rw [hmain, hpw, hxw, ← map_add, ← ofMul_mul]
  exact Additive.ofMul.injective (M.model.injective hfin)

private theorem ggQ2xXL_scalar_mod_x {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p = 3) {Bs : Subgroup G} {x y : G} {D L J K : Subgroup G}
    (M : GGQTwoModel p Bs x y D L J K) (hx0 : M.xV ≠ 0)
    (hind : LinearIndependent (ZMod p) (fun i : {k // k ≠ M.a} => M.coroot i))
    (hspan : M.xV ∈ Submodule.span (ZMod p) (Set.range fun i : {k // k ≠ M.a} => M.coroot i))
    (hdim : Module.finrank (ZMod p) M.V ≤ Fintype.card {k // k ≠ M.a} + 1)
    (h4 : 4 ≤ Module.finrank (ZMod p) M.V) (hTF : TransvectionFree M.linGroup)
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hφN : φ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)))
    (hφx : φ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs)) :
    ∃ ψ ∈ ggAutomizer L Bs, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∀ b : ↥Bs, ∃ n : ℤ, ((φ * ψ) b : ↥Bs) = b ^ ε * (⟨x, M.hx⟩ : ↥Bs) ^ n := by
  let T : M.V ≃ₗ[ZMod p] M.V := ggLin (p := p) M.model φ
  have hT : T = ggLin (p := p) M.model φ := rfl
  have hTnorm : T ∈ Subgroup.normalizer
      (M.parabL {k | k ≠ M.a} : Set (M.V ≃ₗ[ZMod p] M.V)) := by
    rw [ggQ2xXLg2_parabL_L M]
    exact Subgroup.le_normalizer_map (ggLin (p := p) M.model)
      (Subgroup.mem_map.mpr ⟨φ, hφN, rfl⟩)
  have hTx : T M.xV ∈ Submodule.span (ZMod p) {M.xV} := by
    have h1 : T M.xV = M.model (Additive.ofMul (φ ⟨x, M.hx⟩)) := by
      rw [hT, GGQTwoModel.xV, ggLin_apply_ofMul]
    rw [h1]
    exact ggQ2xXLg2_model_mem_span M (φ ⟨x, M.hx⟩) ⟨x, M.hx⟩ hφx
  have hfix : ∀ v : M.V, (∀ g ∈ M.parabL {k | k ≠ M.a}, g v = v) ↔
      v ∈ Submodule.span (ZMod p) {M.xV} := (ggQ2_fixed_lin M).1
  have hTFW : TransvectionFree (M.parabL {k | k ≠ M.a}) := by
    intro g hg htr
    exact hTF g (by
      change g ∈ (ggAutomizer ⊤ Bs).map (ggLin (p := p) M.model)
      rw [ggQ2xXLg2_parabL_L M] at hg
      exact Subgroup.map_mono (ggAutomizer_mono Bs le_top) hg) htr
  obtain ⟨w, hwW, ε, hε, hwε⟩ :=
    GGQ2Lin.pmW_of_span hp M.toLin M.xV hx0 hind hspan hdim h4 hTFW hfix T hTnorm hTx
  have hwW' : w ∈ M.parabL {k | k ≠ M.a} := hwW
  rw [ggQ2xXLg2_parabL_L M] at hwW'
  obtain ⟨ψ, hψ, hψw⟩ := Subgroup.mem_map.mp hwW'
  refine ⟨ψ, hψ, ?_⟩
  rcases hε with hε1 | hεneg
  · refine ⟨1, Or.inl rfl, fun b => ?_⟩
    have hεpow : ∀ b : ↥Bs, ε • M.model (Additive.ofMul b) =
        M.model (Additive.ofMul (b ^ (1 : ℤ))) := by
      intro b
      rw [hε1]
      exact ggQ2xXLg2_pow_scalar_one M b
    exact ggQ2xXLg2_scalar_step M φ ψ T hT w hψw ε 1 hεpow hwε b
  · refine ⟨-1, Or.inr rfl, fun b => ?_⟩
    have hεpow : ∀ b : ↥Bs, ε • M.model (Additive.ofMul b) =
        M.model (Additive.ofMul (b ^ (-1 : ℤ))) := by
      intro b
      rw [hεneg]
      exact ggQ2xXLg2_pow_scalar_neg M b
    exact ggQ2xXLg2_scalar_step M φ ψ T hT w hψw ε (-1) hεpow hwε b

private theorem ggQ2xXL_finish {G : Type} [Group G] [Finite G] {p : ℕ} (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hAJ : ggAutomizer J Bs ≠ ⊥)
    (hK1 : GGQTwoK1 p B Bs x D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hx : x ∈ Bs) (hy : y ∈ Bs) {φ ψ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer ⊤ Bs)
    (hψ : ψ ∈ ggAutomizer L Bs) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hscal : ∀ b : ↥Bs, ∃ n : ℤ, ((φ * ψ) b : ↥Bs) = b ^ ε * (⟨x, hx⟩ : ↥Bs) ^ n) :
    φ ∈ ggAutomizer (Subgroup.normalizer (ggG0 p B x L D J : Set G)) Bs := by
  obtain ⟨g, -, hgBs, hφg⟩ := mem_ggAutomizer_iff.mp hφ
  obtain ⟨k, hkL, hkBs, hψk⟩ := mem_ggAutomizer_iff.mp hψ
  have hφψg : ∀ b : ↥Bs, (((φ * ψ) b : ↥Bs) : G) = (g * k) * b * (g * k)⁻¹ := by
    intro b
    rw [MulAut.mul_apply, hφg (ψ b), hψk b]
    group
  have hxmem : x ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (Set.mem_insert x {y})
  have hymem : y ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  have hconj_x : (g * k) * x * (g * k)⁻¹ ∈ D := by
    obtain ⟨n, hn⟩ := hscal ⟨x, hx⟩
    have hval : (g * k) * x * (g * k)⁻¹ = x ^ ε * x ^ n := by
      have h1 := congrArg (fun b : ↥Bs => (b : G)) hn
      rw [hφψg ⟨x, hx⟩] at h1
      simpa using h1
    rw [hval]
    exact D.mul_mem (Subgroup.zpow_mem D hxmem ε) (Subgroup.zpow_mem D hxmem n)
  have hconj_y : (g * k) * y * (g * k)⁻¹ ∈ D := by
    obtain ⟨n, hn⟩ := hscal ⟨y, hy⟩
    have hval : (g * k) * y * (g * k)⁻¹ = y ^ ε * x ^ n := by
      have h1 := congrArg (fun b : ↥Bs => (b : G)) hn
      rw [hφψg ⟨y, hy⟩] at h1
      simpa using h1
    rw [hval]
    exact D.mul_mem (Subgroup.zpow_mem D hymem ε) (Subgroup.zpow_mem D hxmem n)
  let E : Subgroup G :=
    { carrier := {d : G | (g * k) * d * (g * k)⁻¹ ∈ D}
      one_mem' := by simpa using D.one_mem
      mul_mem' := by
        intro a b ha hb
        change (g * k) * (a * b) * (g * k)⁻¹ ∈ D
        have h : (g * k) * (a * b) * (g * k)⁻¹ =
            ((g * k) * a * (g * k)⁻¹) * ((g * k) * b * (g * k)⁻¹) := by group
        rw [h]
        exact D.mul_mem ha hb
      inv_mem' := by
        intro a ha
        change (g * k) * a⁻¹ * (g * k)⁻¹ ∈ D
        have h : (g * k) * a⁻¹ * (g * k)⁻¹ = ((g * k) * a * (g * k)⁻¹)⁻¹ := by group
        rw [h]
        exact D.inv_mem ha }
  have hDleE : D ≤ E := by
    rw [hnb.2.1]
    refine (Subgroup.closure_le E).mpr ?_
    intro d hd
    rw [Set.mem_insert_iff] at hd
    rcases hd with hd_eq | hd_mem
    · rw [hd_eq]
      exact hconj_x
    · rw [Set.mem_singleton_iff] at hd_mem
      rw [hd_mem]
      exact hconj_y
  have hmN : (g * k) ∈ Subgroup.normalizer (Bs : Set G) := Subgroup.mul_mem _ hgBs hkBs
  have hmD : (g * k) ∈ Subgroup.normalizer (D : Set G) :=
    Subgroup.mem_normalizer_fintype (S := (D : Set G))
      (fun n hn => show (g * k) * n * (g * k)⁻¹ ∈ D from hDleE hn)
  have hmG0 : (g * k) ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
    ggQ2_normalizer_inf_le hLB hP hS.1 hAJ hK1 (Subgroup.mem_inf.mpr ⟨hmN, hmD⟩)
  have hkG0 : k ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
    Subgroup.le_normalizer (le_ggG0_left p B x L D J hkL)
  have hgG0 : g ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) := by
    have h : (g * k) * k⁻¹ ∈ Subgroup.normalizer (ggG0 p B x L D J : Set G) :=
      Subgroup.mul_mem _ hmG0 (Subgroup.inv_mem _ hkG0)
    simpa using h
  exact mem_ggAutomizer_iff.mpr ⟨g, hgG0, hgBs, hφg⟩

private theorem ggQ2xXLg1_stable {G : Type} [Group G] {Bs : Subgroup G} {x : G} (hx : x ∈ Bs)
    {u : ↥Bs} (hu : Subgroup.zpowers (u : G) = Subgroup.zpowers x) {φ : MulAut ↥Bs}
    (hφu : φ u ∈ Subgroup.zpowers u) :
    φ ⟨x, hx⟩ ∈ Subgroup.zpowers (⟨x, hx⟩ : ↥Bs) := by
  obtain ⟨r, hr⟩ := Subgroup.mem_zpowers_iff.mp hφu
  have hxmem : x ∈ Subgroup.zpowers (u : G) := by
    rw [hu]
    exact Subgroup.mem_zpowers x
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxmem
  have hux : (⟨x, hx⟩ : ↥Bs) = u ^ k := by
    apply Subtype.ext
    rw [Subgroup.coe_zpow, hk]
  rw [Subgroup.mem_zpowers_iff]
  refine ⟨r, ?_⟩
  calc (⟨x, hx⟩ : ↥Bs) ^ r = (u ^ k) ^ r := by rw [hux]
    _ = u ^ (k * r) := (zpow_mul u k r).symm
    _ = u ^ (r * k) := by rw [mul_comm]
    _ = (u ^ r) ^ k := zpow_mul u r k
    _ = (φ u) ^ k := by rw [hr]
    _ = φ (u ^ k) := (map_zpow φ u k).symm
    _ = φ ⟨x, hx⟩ := by rw [← hux]

private theorem ggQ2xXL_model_case {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp : p = 3) (hLN : GGLNoncyclicInput) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (h8 : GGQTwoXInLDatum) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) (hxL : x ∈ L) (hAJ : ggAutomizer J Bs ≠ ⊥)
    (hK1 : GGQTwoK1 p B Bs x D J) {y : G} {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (M : GGQTwoModel p Bs x y D L J K) {u : ↥Bs}
    (hu : Subgroup.zpowers (u : G) = Subgroup.zpowers x) :
    GGGammaAt p B Bs x L D J u := by
  obtain ⟨hind, hspan, hdim⟩ := h8 G p B Bs x L D J hS hxL y K hnb M
  intro φ hφ hφu
  have hφx : φ ⟨x, M.hx⟩ ∈ Subgroup.zpowers (⟨x, M.hx⟩ : ↥Bs) :=
    ggQ2xXLg1_stable M.hx hu hφu
  have hφN : φ ∈ Subgroup.normalizer (ggAutomizer L Bs : Set (MulAut ↥Bs)) :=
    ggLineStabNormalizesInput_of_noncyclic hLN G p B Bs x L D J hS.1 M.hx φ hφ hφx
  have hxne : x ≠ 1 := hS.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hx0 : M.xV ≠ 0 := by
    intro h
    have h0 : Additive.ofMul (⟨x, M.hx⟩ : ↥Bs) = 0 :=
      M.model.injective (by rw [map_zero]; exact h)
    have h1 : (⟨x, M.hx⟩ : ↥Bs) = 1 :=
      Additive.ofMul.injective (by simpa using h0)
    exact hxne (Subtype.ext_iff.mp h1)
  have hTF : TransvectionFree M.linGroup := ggQ2_transvectionFree M hS.1.2.2.2.1
  haveI : Finite M.V := Finite.of_equiv (Additive ↥Bs) M.model.toEquiv
  have hcard : Nat.card ↥Bs = p ^ Module.finrank (ZMod p) M.V := by
    calc Nat.card ↥Bs = Nat.card (Additive ↥Bs) := rfl
      _ = Nat.card M.V := Nat.card_congr M.model.toEquiv
      _ = p ^ Module.finrank (ZMod p) M.V :=
        (FiniteField.pow_finrank_eq_natCard p M.V).symm
  have h4 : 4 ≤ Module.finrank (ZMod p) M.V := by
    have hp4 : p ^ 4 ≤ Nat.card ↥Bs := (hS.1.1.tableB_facts).2.2.2.2
    have hp1 : 1 < p := (hS.1.1.tableB_facts).1.one_lt
    rw [hcard] at hp4
    exact (Nat.pow_le_pow_iff_right hp1).mp hp4
  obtain ⟨ψ, hψ, ε, hε, hscal⟩ :=
    ggQ2xXL_scalar_mod_x hp M hx0 hind hspan hdim h4 hTF hφ hφN hφx
  exact ggQ2xXL_finish hLB hP hS hAJ hK1 hnb M.hx M.hy hφ hψ hε hscal

theorem ggQ2_gammaXInL_holds (hLN : GGLNoncyclicInput) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) (h1 : GGQTwoModelInput) (h1b : GGQTwoNoTwoNodeIndInput)
    (h1x : GGQTwoXInLNbrModelInput) (h5 : GGQTwoCentralizerInput) (h8 : GGQTwoXInLDatum)
    (hnode : GGQ2TwoNodeInput) : GGQ2GammaXInLInput := by
  intro G _ _ p B Bs x L D J hS hp hI1 hxL u hu
  haveI : Fact p.Prime := ⟨hS.1.1.tableB_facts.1⟩
  by_cases hrow : ∃ (y : G) (K : Subgroup G),
      GGNbr p B x D J y K ∧ GGQTwoTwoNodeRowAt p K J ∧ y ∉ K
  · obtain ⟨y, K, hnb, hKrow, hy⟩ := hrow
    exact ggQ2xXL_gamma_of_normalizer_le u (hnode hp hS hI1 hnb (Or.inr ⟨hKrow, hy⟩))
  · have hAJ : ggAutomizer J Bs ≠ ⊥ := ggQ2_ajOfSetting hP h5 hS
    have hH := hS.1
    have hRG : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
        GGReflGenerated p (ggAutomizer K Bs) := by
      intro y K hnb
      rcases h1 G p B Bs x L D J hS hI1 y K hnb with h | h | hM | ⟨-, hrg⟩
      · exact absurd hxL ((h1b G p B Bs x L D J hS hI1 y K hnb).1 h)
      · exact absurd ⟨y, K, hnb, h, (h1b G p B Bs x L D J hS hI1 y K hnb).2 h⟩ hrow
      · obtain ⟨M⟩ := hM
        exact ggQ2_reflGenerated_of_model M
      · exact hrg
    have hK1 : GGQTwoK1 p B Bs x D J := ggQ2_K1_of_I1 hLB hP hH hI1
    obtain ⟨y, K, hnb, ⟨M⟩⟩ := h1x G p B Bs x L D J hS hI1 hxL
    exact ggQ2xXL_model_case hp hLN hLB hP h8 hS hxL hAJ hK1 hnb M hu

end CFSG.StandardType

end
