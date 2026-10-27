module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7CentDecomp
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameSeven
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameA5
public import CFSG.LocalAnalysis.StandardType.FS81.TransferTwD7
import CFSG.LocalAnalysis.StandardType.FS81.TwD7BetaNormElements
import CFSG.LocalAnalysis.StandardType.FS81.TwD7BetaOuter
import CFSG.LocalAnalysis.SeitzReduction.E8PilotAutD
import CFSG.LocalAnalysis.SeitzReduction.F4PilotHR4Basic
import CFSG.GroupTheory.InnerCentralizerProjection

public section

namespace CFSG.StandardType.FrameRoute.FS81.E7Frame

open CFSG.Open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem orderOf_inv_mul_twD7 {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G (Row.twD7.n + 1)}
    (hB : Adapted B b₀ K E) : orderOf (b₀⁻¹ * B.b 1) = 3 := by
  obtain ⟨-, hHyp, -⟩ := id hstd
  obtain ⟨hA, -, -, -, -, -⟩ := hHyp
  obtain ⟨hb₀, hKC, -, hcenter, -, -, -, -⟩ := hA
  have hb₁K : B.b 1 ∈ K := hB.2.2 1 (by decide)
  have hb₀3 : b₀ ^ 3 = 1 := by rw [← hb₀]; exact pow_orderOf_eq_one b₀
  have hb₁3 : B.b 1 ^ 3 = 1 := by rw [← B.ord 1]; exact pow_orderOf_eq_one _
  have hcb : Commute b₀ (B.b 1) := (Subgroup.mem_centralizer_singleton_iff.mp (hKC hb₁K)).symm
  refine orderOf_eq_prime ?_ fun h => ?_
  · rw [hcb.inv_left.mul_pow, inv_pow, hb₀3, hb₁3, inv_one, one_mul]
  · have h' : b₀ = B.b 1 := inv_mul_eq_one.mp h
    have h1 : b₀ = 1 :=
      Subgroup.disjoint_def.mp (disjoint_zpowers_of_center hKC hcenter) (Subgroup.mem_zpowers b₀)
        (by rw [h']; exact hb₁K)
    rw [h1, orderOf_one] at hb₀
    exact absurd hb₀ (by decide)

theorem orderOf_mul_twD7 {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G (Row.twD7.n + 1)}
    (hB : Adapted B b₀ K E) : orderOf (b₀ * B.b 1) = 3 := by
  obtain ⟨-, hHyp, -⟩ := id hstd
  obtain ⟨hA, -, -, -, -, -⟩ := hHyp
  obtain ⟨hb₀, hKC, -, hcenter, -, -, -, -⟩ := hA
  have hb₁K : B.b 1 ∈ K := hB.2.2 1 (by decide)
  have hb₀3 : b₀ ^ 3 = 1 := by rw [← hb₀]; exact pow_orderOf_eq_one b₀
  have hb₁3 : B.b 1 ^ 3 = 1 := by rw [← B.ord 1]; exact pow_orderOf_eq_one _
  have hcb : Commute b₀ (B.b 1) := (Subgroup.mem_centralizer_singleton_iff.mp (hKC hb₁K)).symm
  refine orderOf_eq_prime ?_ fun h => ?_
  · rw [hcb.mul_pow, hb₀3, hb₁3, one_mul]
  · have h' : b₀ = (B.b 1)⁻¹ := eq_inv_of_mul_eq_one_left h
    have h1 : b₀ = 1 :=
      Subgroup.disjoint_def.mp (disjoint_zpowers_of_center hKC hcenter) (Subgroup.mem_zpowers b₀)
        (by rw [h']; exact K.inv_mem hb₁K)
    rw [h1, orderOf_one] at hb₀
    exact absurd hb₀ (by decide)

theorem tr_m0_eq_commutator_twD7 {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G (Row.twD7.n + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀) {R : Subgroup G}
    (hRK : R ≤ Subgroup.centralizer (K : Set G))
    (hC : Subgroup.centralizer ({b₀} : Set G) = R ⊔ (Subgroup.zpowers b₀ ⊔ K))
    {J : Subgroup G} (ψ : ↥L7 ≃* ↥J) (hCent : E7NatCent)
    (hJC : J ≤ Subgroup.centralizer ({b₀ * B.b 1} : Set G))
    (hMJ : ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ ≤ J)
    {z : ↥L7} (hz : (z : ModGL .E7 (ZMod 2)) ∈ Jn 0) (hψz : ((ψ z : ↥J) : G) = b₀⁻¹ * B.b 1) :
    tr ψ M0 = ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ := by
  obtain ⟨-, hHyp, -⟩ := id hstd
  obtain ⟨hA, -, -, -, -, -⟩ := hHyp
  obtain ⟨hb₀, hKC, -, -, -, -, -, -⟩ := hA
  have hrec' : RecOutTwD7 B b₀ := hrec
  have hb₁K : B.b 1 ∈ K := hB.2.2 1 (by decide)
  have hb₀3 : b₀ ^ 3 = 1 := by rw [← hb₀]; exact pow_orderOf_eq_one b₀
  have hβ₁o := orderOf_inv_mul_twD7 hstd hB
  have hz3 : orderOf (z : ModGL .E7 (ZMod 2)) = 3 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq ψ, ← Subgroup.orderOf_coe, hψz, hβ₁o]
  obtain ⟨-, hperf, -⟩ := centralizer_inf_eq_zpowers_sup_commutator_twD7 hstd hB hrec
  have hM₀K : ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ ≤ Subgroup.centralizer ({B.b 1} : Set G) ⊓ K :=
    Subgroup.commutator_le_self _
  have hMβ₁ : ∀ m ∈ ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆, m * ((ψ z : ↥J) : G) = ((ψ z : ↥J) : G) * m := by
    intro m hm
    have hm1 : Commute m (B.b 1) := Subgroup.mem_centralizer_singleton_iff.mp (hM₀K hm).1
    have hm0 : Commute m b₀ := Subgroup.mem_centralizer_singleton_iff.mp (hKC (hM₀K hm).2)
    rw [hψz]
    exact (hm0.inv_right.mul_right hm1).eq
  have hcz : ∀ t ∈ tr ψ M0, Commute ((ψ z : ↥J) : G) t := fun t ht =>
    (Subgroup.mem_centralizer_singleton_iff.mp (tr_M0_le_centralizer ψ hz ht)).symm
  have hge : ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ ≤ tr ψ M0 := by
    rw [← Subgroup.isPerfect_iff.mp hperf, Subgroup.commutator_le]
    intro m hm m' hm'
    obtain ⟨i, t, ht, rfl⟩ := exists_zpow_mul_of_commute hCent ψ hz hz3 (hMJ hm) (hMβ₁ m hm)
    obtain ⟨j, t', ht', rfl⟩ := exists_zpow_mul_of_commute hCent ψ hz hz3 (hMJ hm') (hMβ₁ m' hm')
    rw [commutatorElement_mul_mul_of_commute ((hcz t ht).zpow_left i) ((hcz t' ht').zpow_left i)
      ((hcz t ht).zpow_left j) ((hcz t' ht').zpow_left j) ((Commute.refl _).zpow_zpow i j),
      commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ht ht') (inv_mem ht)) (inv_mem ht')
  have hXP : tr ψ M0 ≤ Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.centralizer ({B.b 1} : Set G) := by
    rw [← centralizer_mul_inf_centralizer_inv_mul hb₀3]
    refine le_inf ((tr_le_K ψ M0).trans hJC) ?_
    have h := tr_M0_le_centralizer ψ hz
    rwa [hψz] at h
  rw [centralizer_inf_centralizer_eq_twD7 hstd hB hrec hRK hC] at hXP
  have hCM : ∀ {S : Subgroup G}, S ≤ Subgroup.centralizer ((⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G) →
      S ≤ Subgroup.normalizer ((⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G) :=
    fun h => h.trans (Subgroup.centralizer_le_normalizer _)
  have hMK : ((⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G) ⊆ K :=
    fun m hm => (hM₀K hm).2
  have hN : R ⊔ (Subgroup.zpowers b₀ ⊔ (Subgroup.zpowers (B.b 1) ⊔
      ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K, Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆)) ≤
      Subgroup.normalizer ((⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G) := by
    refine sup_le (hCM (hRK.trans (Subgroup.centralizer_le hMK)))
      (sup_le (hCM (Subgroup.zpowers_le.mpr ?_)) (sup_le (hCM (Subgroup.zpowers_le.mpr ?_))
        Subgroup.le_normalizer))
    · rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact Subgroup.mem_centralizer_singleton_iff.mp (hKC (hM₀K hm).2)
    · rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact Subgroup.mem_centralizer_singleton_iff.mp (hM₀K hm).1
  have hsimple : IsSimpleGroup ↥(tr ψ M0) := by
    have : IsSimpleGroup ↥M0 := hCent.2.2.1
    let e2 : ↥(M0.subgroupOf L7) ≃* ↥(tr ψ M0) :=
      (M0.subgroupOf L7).equivMapOfInjective (J.subtype.comp ψ.toMonoidHom)
        (J.subtype_injective.comp ψ.injective)
    let e3 : ↥(M0.subgroupOf L7) ≃* ↥M0 := Subgroup.subgroupOfEquivOfLe inf_le_left
    exact MulEquiv.isSimpleGroup (e2.symm.trans e3)
  have hb₂ : B.b 2 ∈ ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ :=
    tail_mem_commutator_centralizer_of_std_twD7 hstd B hB hrec' 0
  have hb₂1 : B.b 2 ≠ 1 := by
    intro h
    have h3 := B.ord 2
    rw [h, orderOf_one] at h3
    exact absurd h3 (by decide)
  have hnorm := Subgroup.normal_subgroupOf_of_le_normalizer (hXP.trans hN)
  refine le_antisymm ?_ hge
  have := hsimple
  have := hnorm
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆).subgroupOf (tr ψ M0)) with h | h
  · exfalso
    have hmem : (⟨B.b 2, hge hb₂⟩ : ↥(tr ψ M0)) ∈
        (⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
          Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆).subgroupOf (tr ψ M0) := by
      rw [Subgroup.mem_subgroupOf]
      exact hb₂
    rw [h, Subgroup.mem_bot] at hmem
    exact hb₂1 (congrArg Subtype.val hmem)
  · exact Subgroup.subgroupOf_eq_top.mp h

theorem not_isInnerAut_conjAut_of_tr_m0_eq {G : Type} [Group G] {J M : Subgroup G}
    (ψ : ↥L7 ≃* ↥J) (hM : tr ψ M0 = M) {σ : G}
    (hσM : (tr ψ M0).map (MulAut.conj σ).toMonoidHom = tr ψ M0)
    (hout : ¬ ∃ m ∈ M, ∀ x ∈ M, σ * x * σ⁻¹ = m * x * m⁻¹) :
    ¬ IsInnerAut (conjAut ψ (inf_le_left : M0 ≤ L7) σ hσM) := by
  rintro ⟨m₀, hm₀⟩
  refine hout ⟨((ψ ⟨m₀, m₀.2.1⟩ : ↥J) : G), hM ▸ (coe_mem_tr_iff ψ _).mpr m₀.2,
    fun x hx => ?_⟩
  rw [← hM] at hx
  obtain ⟨y, hy, rfl⟩ := mem_tr.mp hx
  have h := trEquiv_conjAut ψ (inf_le_left : M0 ≤ L7) σ hσM ⟨y, hy⟩
  rw [hm₀, coe_trEquiv, coe_trEquiv] at h
  have h' : ((ψ ⟨((MulAut.conj m₀ ⟨(y : ModGL .E7 (ZMod 2)), hy⟩ : ↥M0) : ModGL .E7 (ZMod 2)),
      (MulAut.conj m₀ ⟨(y : ModGL .E7 (ZMod 2)), hy⟩).2.1⟩ : ↥J) : G) =
        ((ψ ⟨m₀, m₀.2.1⟩ : ↥J) : G) * ((ψ y : ↥J) : G) * ((ψ ⟨m₀, m₀.2.1⟩ : ↥J) : G)⁻¹ := by
    have he : (⟨((MulAut.conj m₀ ⟨(y : ModGL .E7 (ZMod 2)), hy⟩ : ↥M0) : ModGL .E7 (ZMod 2)),
        (MulAut.conj m₀ ⟨(y : ModGL .E7 (ZMod 2)), hy⟩).2.1⟩ : ↥L7) =
          ⟨m₀, m₀.2.1⟩ * y * (⟨m₀, m₀.2.1⟩ : ↥L7)⁻¹ := Subtype.ext rfl
    rw [he, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [h'] at h
  have hyy : (⟨(y : ModGL .E7 (ZMod 2)), (inf_le_left : M0 ≤ L7) hy⟩ : ↥L7) = y := rfl
  rw [hyy] at h
  exact h.symm

private theorem exists_R_twD7 {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G (Row.twD7.n + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀) :
    ∃ R : Subgroup G, R ≤ Subgroup.centralizer (K : Set G) ∧
      Subgroup.centralizer ({b₀} : Set G) = R ⊔ (Subgroup.zpowers b₀ ⊔ K) := by
  obtain ⟨-, hHyp, hCanon⟩ := id hstd
  obtain ⟨hA, -, -, -, -, -⟩ := hHyp
  obtain ⟨-, hKC, -, hKz, -, -, -, -⟩ := hA
  obtain ⟨hKs, -⟩ := isSimpleGroup_and_mulEquiv_of_isRow_twD7 hCanon.1 hKz
  obtain ⟨R₀, -, -, -, hCeq, -, -, -, hker⟩ := exists_threePrime_core_twD7 hstd hB hrec
  have hb₁1 : B.b 1 ≠ 1 := by
    intro h
    have h3 := B.ord 1
    rw [h, orderOf_one] at h3
    exact absurd h3 (by decide)
  exact ⟨R₀, hker K hKs (hKC.trans le_sup_left) ⟨B.b 1, hB.2.2 1 (by decide),
    hB.1 ▸ B.b_mem_span 1, hb₁1⟩, hCeq⟩

theorem not_exists_conj_eq_mul {G : Type} [Group G] {M : Subgroup G} {n m : G} (hm : m ∈ M)
    (hn : ¬ ∃ a ∈ M, ∀ x ∈ M, n * x * n⁻¹ = a * x * a⁻¹) :
    ¬ ∃ a ∈ M, ∀ x ∈ M, n * m * x * (n * m)⁻¹ = a * x * a⁻¹ := by
  rintro ⟨a, ha, h⟩
  refine hn ⟨a * m⁻¹, M.mul_mem ha (M.inv_mem hm), fun x hx => ?_⟩
  have h' := h (m⁻¹ * x * m) (M.mul_mem (M.mul_mem (M.inv_mem hm) hx) hm)
  calc n * x * n⁻¹ = n * m * (m⁻¹ * x * m) * (n * m)⁻¹ := by group
    _ = a * (m⁻¹ * x * m) * a⁻¹ := h'
    _ = a * m⁻¹ * x * (a * m⁻¹)⁻¹ := by group

theorem not_mem_of_le_centralizer_psi (hF : E7NatFrame) (hC : E7NatCent) {G : Type} [Group G]
    {J : Subgroup G} (ψ : ↥L7 ≃* ↥J) {g : G}
    (hJg : J ≤ Subgroup.centralizer ({g} : Set G)) (hg : g ≠ 1) : g ∉ J := by
  intro hgJ
  have hgc : ∀ x ∈ J, g * x = x * g := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hJg hx)).symm
  have hgM : g ∈ Subgroup.centralizer (tr ψ M0 : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun m hm => (hgc m (tr_le_K ψ M0 hm)).symm
  exact hg (tr_jn0_eq_one_of_central hF ψ (inf_centralizer_le_tr_jn0 hC ψ ⟨hgJ, hgM⟩)
    fun v hv => hgc v (tr_le_K ψ _ hv))

theorem swap_mul_inverter_twD7 (hF : E7NatFrame) (hC : E7NatCent) {G : Type} [Group G]
    [Finite G] {b₀ : G} {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G (Row.twD7.n + 1)} (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀)
    {J' : Subgroup G} (ψ : ↥L7 ≃* ↥J')
    (hJC : J' ≤ Subgroup.centralizer ({b₀ * B.b 1} : Set G))
    (hJgen : J' ≤ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G))
    (hMJ : ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ ≤ J')
    {z : ↥L7} (hz : (z : ModGL .E7 (ZMod 2)) ∈ Jn 0) (hψz : ((ψ z : ↥J') : G) = b₀⁻¹ * B.b 1)
    (hNJ : (Subgroup.normalizer (Subgroup.zpowers (b₀ * B.b 1) : Set G) ⊓
        Subgroup.normalizer (E : Set G)) ⊓
      Subgroup.normalizer ((⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G) ≤
      Subgroup.normalizer (J' : Set G))
    {g : G} (hgK : g ∈ K) (hgE : g ∈ Subgroup.normalizer (E : Set G))
    (hgM : g ∈ Subgroup.normalizer ((⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G))
    (hg0 : g * (b₀ * B.b 1) * g⁻¹ = (b₀⁻¹ * B.b 1)⁻¹)
    (hg1 : g * (b₀⁻¹ * B.b 1) * g⁻¹ = (b₀ * B.b 1)⁻¹)
    (hgout : ¬ ∃ m ∈ ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆,
      ∀ x ∈ ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆, g * x * g⁻¹ = m * x * m⁻¹)
    {i : G} (hi : i ∈ tr ψ (Jn 0)) (hiβ : i * (b₀⁻¹ * B.b 1) * i⁻¹ = (b₀⁻¹ * B.b 1)⁻¹)
    (hiE : i ∈ Subgroup.normalizer (E : Set G)) :
    g * i ∈ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G) ∧
      g * i ∈ Subgroup.normalizer ((⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G) ∧
      (¬ ∃ m ∈ ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
          Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆,
        ∀ x ∈ ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
          Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆,
          g * i * x * (g * i)⁻¹ = m * x * m⁻¹) ∧
      g * i * (b₀⁻¹ * B.b 1) * (g * i)⁻¹ = b₀ * B.b 1 ∧
      (tr ψ (Jn 0)).map (MulAut.conj (g * i)).toMonoidHom ≤ Subgroup.normalizer (J' : Set G) ∧
      g * i * (g * i) ∈ Subgroup.normalizer (J' : Set G) := by
  obtain ⟨R, hRK, hCR⟩ := exists_R_twD7 hstd hB hrec
  obtain ⟨-, hHyp, -⟩ := id hstd
  obtain ⟨hA, -, -, -, -, -⟩ := hHyp
  obtain ⟨-, hKC, -, -, -, -, -, -⟩ := hA
  have hM := tr_m0_eq_commutator_twD7 hstd hB hrec hRK hCR ψ hC hJC hMJ hz hψz
  have hβ₁o := orderOf_inv_mul_twD7 hstd hB
  have hz3 : orderOf (z : ModGL .E7 (ZMod 2)) = 3 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq ψ, ← Subgroup.orderOf_coe, hψz, hβ₁o]
  have hJ0M : ∀ j ∈ tr ψ (Jn 0), j ∈ Subgroup.centralizer
      ((⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G) := fun j hj => by
    rw [← hM]
    exact tr_jn0_le_centralizer ψ hj
  have hJ0N : ∀ j ∈ tr ψ (Jn 0), j ∈ Subgroup.normalizer
      ((⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G) := fun j hj =>
    mem_normalizer_of_forall_commute fun x hx =>
      (Subgroup.mem_centralizer_iff.mp (hJ0M j hj) x hx).symm
  have hiJ : i ∈ J' := tr_le_K ψ _ hi
  have hiβc : i * (b₀ * B.b 1) = b₀ * B.b 1 * i :=
    Subgroup.mem_centralizer_singleton_iff.mp (hJC hiJ)
  have hJ0E : tr ψ (Jn 0) ≤ Subgroup.normalizer (E : Set G) := by
    have hb₀E : b₀ ∈ E := hB.1 ▸ hB.2.1 ▸ B.b_mem_span 0
    have hb₁E : B.b 1 ∈ E := hB.1 ▸ B.b_mem_span 1
    have hzE : ((ψ z : ↥J') : G) ∈ Subgroup.normalizer (E : Set G) := by
      rw [hψz]
      exact Subgroup.le_normalizer (E.mul_mem (E.inv_mem hb₀E) hb₁E)
    obtain ⟨t, ht, rfl⟩ := mem_tr.mp hi
    have htz : (t : ModGL .E7 (ZMod 2)) * z * (t : ModGL .E7 (ZMod 2))⁻¹ =
        (z : ModGL .E7 (ZMod 2))⁻¹ := by
      have h1 : ψ (t * z * t⁻¹) = ψ z⁻¹ := Subtype.ext (by
        simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hψz]
        exact hiβ)
      exact congrArg Subtype.val (ψ.injective h1)
    intro j hj
    obtain ⟨y, hy, rfl⟩ := mem_tr.mp hj
    have key : y = 1 ∨ y = z ∨ y = z⁻¹ ∨ y = t ∨ y = t * z ∨ y = t * z⁻¹ := by
      rcases jn0_eq_of_inv hF hz hz3 ht htz hy with h | h | h | h | h | h
      · exact Or.inl (Subtype.ext h)
      · exact Or.inr (Or.inl (Subtype.ext h))
      · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext h)))))
    rcases key with rfl | rfl | rfl | rfl | rfl | rfl
    · simp only [map_one, Subgroup.coe_one]
      exact Subgroup.one_mem _
    · exact hzE
    · simp only [map_inv, Subgroup.coe_inv]
      exact Subgroup.inv_mem _ hzE
    · exact hiE
    · simp only [map_mul, Subgroup.coe_mul]
      exact Subgroup.mul_mem _ hiE hzE
    · simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      exact Subgroup.mul_mem _ hiE (Subgroup.inv_mem _ hzE)
  have hnE : g * i ∈ Subgroup.normalizer (E : Set G) := Subgroup.mul_mem _ hgE hiE
  have hnN : g * i ∈ Subgroup.normalizer ((⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G) :=
    Subgroup.mul_mem _ hgM (hJ0N i hi)
  have hn1 : g * i * (b₀⁻¹ * B.b 1) * (g * i)⁻¹ = b₀ * B.b 1 := by
    calc g * i * (b₀⁻¹ * B.b 1) * (g * i)⁻¹ = g * (i * (b₀⁻¹ * B.b 1) * i⁻¹) * g⁻¹ := by group
      _ = (g * (b₀⁻¹ * B.b 1) * g⁻¹)⁻¹ := by rw [hiβ]; group
      _ = b₀ * B.b 1 := by rw [hg1, inv_inv]
  have hnβ : g * i * (b₀ * B.b 1) * (g * i)⁻¹ = (b₀⁻¹ * B.b 1)⁻¹ := by
    calc g * i * (b₀ * B.b 1) * (g * i)⁻¹ = g * (i * (b₀ * B.b 1)) * i⁻¹ * g⁻¹ := by group
      _ = g * (b₀ * B.b 1 * i) * i⁻¹ * g⁻¹ := by rw [hiβc]
      _ = g * (b₀ * B.b 1) * g⁻¹ := by group
      _ = (b₀⁻¹ * B.b 1)⁻¹ := hg0
  refine ⟨Subgroup.mul_mem _ ((le_sup_left : Subgroup.centralizer ({b₀} : Set G) ≤ _)
    (hKC hgK)) (hJgen hiJ), hnN, ?_, hn1, ?_, ?_⟩
  · rintro ⟨m, hm, h⟩
    refine hgout ⟨m, hm, fun x hx => ?_⟩
    have hix : i * x = x * i := (Subgroup.mem_centralizer_iff.mp (hJ0M i hi) x hx).symm
    rw [← h x hx]
    calc g * x * g⁻¹ = g * (i * x) * i⁻¹ * g⁻¹ := by rw [hix]; group
      _ = g * i * x * (g * i)⁻¹ := by group
  · have h1β : (Subgroup.zpowers (b₀⁻¹ * B.b 1)).map (MulAut.conj (g * i)).toMonoidHom =
        Subgroup.zpowers (b₀ * B.b 1) := by
      rw [zpowers_map_conj, hn1]
    rintro _ ⟨j, hj, rfl⟩
    refine hNJ ⟨⟨?_, ?_⟩, ?_⟩
    · have hjβ₁ := tr_jn0_le_normalizer_zpowers hF ψ hz hz3 hj
      rw [hψz] at hjβ₁
      exact conj_mem_normalizer_of_map h1β hjβ₁
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnE (hJ0E hj)) (Subgroup.inv_mem _ hnE)
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hnN (hJ0N j hj)) (Subgroup.inv_mem _ hnN)
  · refine hNJ ⟨⟨?_, Subgroup.mul_mem _ hnE hnE⟩, Subgroup.mul_mem _ hnN hnN⟩
    have h2 : g * i * (g * i) * (b₀ * B.b 1) * (g * i * (g * i))⁻¹ = (b₀ * B.b 1)⁻¹ := by
      calc g * i * (g * i) * (b₀ * B.b 1) * (g * i * (g * i))⁻¹ =
            g * i * (g * i * (b₀ * B.b 1) * (g * i)⁻¹) * (g * i)⁻¹ := by group
        _ = g * i * (b₀⁻¹ * B.b 1)⁻¹ * (g * i)⁻¹ := by rw [hnβ]
        _ = (g * i * (b₀⁻¹ * B.b 1) * (g * i)⁻¹)⁻¹ := by group
        _ = (b₀ * B.b 1)⁻¹ := by rw [hn1]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      ((zpowers_map_conj (b₀ * B.b 1) (g * i * (g * i))).trans
        (by rw [h2, Subgroup.zpowers_inv]))

section Seven

theorem normalizer_le_sup_centralizer_of_psi {G : Type} [Group G] {J : Subgroup G}
    (ψ : ↥L7 ≃* ↥J) :
    Subgroup.normalizer (J : Set G) ≤ J ⊔ Subgroup.centralizer (J : Set G) := by
  refine CFSG.le_sup_centralizer_of_forall_mem_range_conj le_rfl fun r hr => ?_
  refine (CFSG.SeitzReduction.F4Pilot.conj_mem_range_conj_iff ψ.symm
    (J.normalizerMonoidHom ⟨r, hr⟩)).1 ?_
  obtain ⟨g, hg⟩ := CFSG.SeitzReduction.E8Pilot.exists_eq_conj_of_forall_eq_zero_or_eq_one
    (Or.inl rfl) (by decide) ((ψ.symm.symm.trans (J.normalizerMonoidHom ⟨r, hr⟩)).trans ψ.symm)
  exact ⟨g, hg.symm⟩

theorem h77_twD7 (hF : E7NatFrame) (hC : E7NatCent) (hT : E7NatTau) (hA5 : E7NatA5)
    (hW : E7NatWeyl) {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G (Row.twD7.n + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀) {J' : Subgroup G} (hJs : IsSimpleGroup ↥J')
    (ψ : ↥L7 ≃* ↥J') (hJC : J' ≤ Subgroup.centralizer ({b₀ * B.b 1} : Set G))
    (hJgen : J' ≤ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G))
    (hMJ : ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ ≤ J')
    {z : ↥L7} (hz : (z : ModGL .E7 (ZMod 2)) ∈ Jn 0) (hψz : ((ψ z : ↥J') : G) = b₀⁻¹ * B.b 1)
    {σ : G} (hσgen : σ ∈ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G))
    (hσN : σ ∈ Subgroup.normalizer ((⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G))
    (hσout : ¬ ∃ m ∈ ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆,
      ∀ x ∈ ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆, σ * x * σ⁻¹ = m * x * m⁻¹)
    {K₀ : Subgroup G} (hK₀ : K₀ ≤ Subgroup.centralizer (J' : Set G)) (hβK₀ : b₀ * B.b 1 ∈ K₀)
    (h0 : (tr ψ (Jn 0)).map (MulAut.conj σ).toMonoidHom = K₀)
    (h0' : K₀.map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 0))
    (h1 : (tr ψ (Jn 1)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 6))
    (h3 : (tr ψ (Jn 3)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 5))
    (h5 : (tr ψ (Jn 5)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 3))
    (h6 : (tr ψ (Jn 6)).map (MulAut.conj σ).toMonoidHom = tr ψ (J mu))
    (hlam : (tr ψ (J lam)).map (MulAut.conj σ).toMonoidHom = tr ψ (Jn 1)) :
    ∀ u ∈ (tr ψ (J theta)).map (MulAut.conj σ⁻¹).toMonoidHom, ∀ w ∈ tr ψ (Jn 2),
      u * w = w * u := by
  obtain ⟨R, hRK, hCR'⟩ := exists_R_twD7 hstd hB hrec
  have hβ₁o := orderOf_inv_mul_twD7 hstd hB
  have hz3 : orderOf (z : ModGL .E7 (ZMod 2)) = 3 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq ψ, ← Subgroup.orderOf_coe, hψz, hβ₁o]
  have hβ3 := orderOf_mul_twD7 hstd hB
  have hβ₁tr : b₀⁻¹ * B.b 1 ∈ tr ψ (Jn 0) := mem_tr.mpr ⟨z, hz, hψz⟩
  have hinv : ∃ t ∈ J', t * (b₀⁻¹ * B.b 1) * t⁻¹ = (b₀⁻¹ * B.b 1)⁻¹ := by
    obtain ⟨t, htJ, ht⟩ := jn0_exists_inv hF hz hz3
    obtain ⟨t', rfl⟩ : ∃ t' : ↥L7, (t' : ModGL .E7 (ZMod 2)) = t := ⟨⟨t, hF.1 0 htJ⟩, rfl⟩
    have hty : t' * z * t'⁻¹ = z⁻¹ := Subtype.ext ht
    have hψt := congrArg (fun v : ↥L7 => ((ψ v : ↥J') : G)) hty
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, hψz] at hψt
    exact ⟨((ψ t' : ↥J') : G), (ψ t').2, hψt⟩
  obtain ⟨R₀, hRβ, hR3, hRJ, hRσ, hRN⟩ := exists_threePrime_core_beta_twD7 hstd hB hrec hJs hJC
    hJgen (hψz ▸ (ψ z).2) hMJ hinv
  have hM := tr_m0_eq_commutator_twD7 hstd hB hrec hRK hCR' ψ hC hJC hMJ hz hψz
  have hσM : (tr ψ M0).map (MulAut.conj σ).toMonoidHom = tr ψ M0 := by
    rw [hM]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hσN
  exact h77_of_sigma hF hC hT hA5 hW ψ σ hK₀ hβK₀ hβ3 hRβ hR3 hRJ
    (hCR_of_conj_mem_zpowers hF ψ hJC exists_conj_mu_jn0 hβ₁tr hβ₁o hRN) (hRσ σ hσgen) hσM
    (not_isInnerAut_conjAut_of_tr_m0_eq ψ hM hσM hσout) h0 h0' h1 h3 h5 h6 hlam

end Seven

section Frame

open CFSG.ClassicalInvolution.WeakCT CFSG.Timmesfeld

theorem e7Frame_twD7 (hF : E7NatFrame) (hH : E7NatHigh) (hC : E7NatCent) (hP : E7NatPsi)
    (hT : E7NatTau) (hA5 : E7NatA5) (hW : E7NatWeyl) {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G (Row.twD7.n + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀) {J' : Subgroup G}
    (hJs : IsSimpleGroup ↥J') (ψ : ↥L7 ≃* ↥J')
    (hJC : J' ≤ Subgroup.centralizer ({b₀ * B.b 1} : Set G))
    (hJgen : J' ≤ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G))
    (hMJ : ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ ≤ J')
    {z : ↥L7} (hz : (z : ModGL .E7 (ZMod 2)) ∈ Jn 0) (hψz : ((ψ z : ↥J') : G) = b₀⁻¹ * B.b 1)
    {n : G} (hngen : n ∈ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G))
    (hnN : n ∈ Subgroup.normalizer ((⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G))
    (hnout : ¬ ∃ m ∈ ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆,
      ∀ x ∈ ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆, n * x * n⁻¹ = m * x * m⁻¹)
    (hn1 : n * (b₀⁻¹ * B.b 1) * n⁻¹ = b₀ * B.b 1)
    (hK₀N : (tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom ≤ Subgroup.normalizer (J' : Set G))
    (hnnJ : n * n ∈ Subgroup.normalizer (J' : Set G)) :
    ∃ (U : Fin 8 → Subgroup G) (g : G),
      g ∈ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G) ∧
      g ∈ J' ⊔ Subgroup.zpowers n ∧
      (∀ i j : Fin 8, i ≠ j → ¬ edgeE 8 i j → ¬ edgeE 8 j i →
        ∀ a ∈ U i, ∀ c ∈ U j, a * c = c * a) ∧
      (∀ i j : Fin 8, edgeE 8 i j → ∃ W, LinearBlockStandardPair (ZMod 2) W (U i) (U j)) ∧
      J' ≤ ⨆ k, U k ∧ b₀ * B.b 1 ∈ ⨆ k, U k ∧ g * (b₀ * B.b 1) * g⁻¹ ∈ J' ∧
      (∃ (ψ : ↥(adjointGroup .E7 (ZMod 2)) ≃* ↥J') (r : ↥(adjointGroup .E7 (ZMod 2))),
        (r : ModGL .E7 (ZMod 2)) ∈ CFSG.SeitzReduction.EPilot.highRootSL2 .E7 (ZMod 2) ∧
          ((ψ r : ↥J') : G) = g⁻¹ * (b₀ * B.b 1) * g) ∧
      ∀ k, U k ≤ J' ∨ U k ≤ J'.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨R, hRK, hCR⟩ := exists_R_twD7 hstd hB hrec
  obtain ⟨-, hHyp, -⟩ := id hstd
  obtain ⟨hA, -, -, -, -, -⟩ := hHyp
  obtain ⟨-, hKC, -, -, -, -, -, -⟩ := hA
  have hM := tr_m0_eq_commutator_twD7 hstd hB hrec hRK hCR ψ hC hJC hMJ hz hψz
  have hnM : (tr ψ M0).map (MulAut.conj n).toMonoidHom = tr ψ M0 := by
    rw [hM]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hnN
  have hβ₁o := orderOf_inv_mul_twD7 hstd hB
  have hz3 : orderOf (z : ModGL .E7 (ZMod 2)) = 3 := by
    rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq ψ, ← Subgroup.orderOf_coe, hψz, hβ₁o]
  have hβ3 := orderOf_mul_twD7 hstd hB
  have hK₀M : (tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom ≤
      Subgroup.centralizer (tr ψ M0 : Set G) := by
    rintro _ ⟨j, hj, rfl⟩
    exact conj_mem_centralizer_of_map hnM (tr_jn0_le_centralizer ψ hj)
  have hn2 := map_conj_map_conj_tr_jn0 hC ψ hnnJ hnM
  have hβJ : n * ((ψ z : ↥J') : G) * n⁻¹ ∉ J' := by
    rw [hψz, hn1]
    refine not_mem_of_le_centralizer_psi hF hC ψ hJC fun h => ?_
    rw [h, orderOf_one] at hβ3
    exact absurd hβ3 (by decide)
  have hK₀ := le_centralizer_of_commute_tr_jn0 hF hC ψ (normalizer_le_sup_centralizer_of_psi ψ)
    hK₀N hK₀M (commute_tr_jn0_of_conj hF hC ψ hz hz3 hK₀N hK₀M hn2 hβJ)
  have hβK₀ : b₀ * B.b 1 ∈ (tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom := by
    refine ⟨((ψ z : ↥J') : G), mem_tr.mpr ⟨z, hz, rfl⟩, ?_⟩
    show n * ((ψ z : ↥J') : G) * n⁻¹ = _
    rw [hψz, hn1]
  obtain ⟨m, hm, hσM, -, h0, h0', h1, h3, h4, h5, h6, -, hlam⟩ :=
    exists_sigma_mul_of_conj hH hC hP ψ hnM
      (not_isInnerAut_conjAut_of_tr_m0_eq ψ hM hnM hnout) hK₀ hn2
  have hm₀ : m ∈ ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ := hM ▸ hm
  have hσgen : n * m ∈ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G) :=
    Subgroup.mul_mem _ hngen ((le_sup_left : Subgroup.centralizer ({b₀} : Set G) ≤ _)
      (hKC (Subgroup.commutator_le_self _ hm₀).2))
  have hσN : n * m ∈ Subgroup.normalizer ((⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G) := by
    refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
    rw [← hM]
    exact hσM
  obtain ⟨U, hU⟩ := e7Frame_inv_of_sigma ψ (n * m) hK₀ hβK₀ h0 h0' hσM h1 h3 h4 h5 h6
    (h77_twD7 hF hC hT hA5 hW hstd hB hrec hJs ψ hJC hJgen hMJ hz hψz hσgen hσN
      (not_exists_conj_eq_mul hm₀ hnout) hK₀ hβK₀ h0 h0' h1 h3 h5 h6 hlam)
  exact ⟨U, (n * m)⁻¹, Subgroup.inv_mem _ hσgen, Subgroup.inv_mem _
    (Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers n))
      (Subgroup.mem_sup_left (hMJ hm₀))), hU⟩

section Y

theorem exists_Y_twD7 (hF : E7NatFrame) (hH : E7NatHigh) (hC : E7NatCent) (hP : E7NatPsi)
    (hT : E7NatTau) (hA5 : E7NatA5) (hW : E7NatWeyl) {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G (Row.twD7.n + 1)}
    (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀) {J' : Subgroup G}
    (hJs : IsSimpleGroup ↥J') (ψ : ↥L7 ≃* ↥J')
    (hJC : J' ≤ Subgroup.centralizer ({b₀ * B.b 1} : Set G))
    (hJgen : J' ≤ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G))
    (hMJ : ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ ≤ J')
    (hEJ : E ≤ Subgroup.zpowers (b₀ * B.b 1) ⊔ J')
    {z : ↥L7} (hz : (z : ModGL .E7 (ZMod 2)) ∈ Jn 0) (hψz : ((ψ z : ↥J') : G) = b₀⁻¹ * B.b 1)
    {n : G} (hngen : n ∈ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G))
    (hnN : n ∈ Subgroup.normalizer ((⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G))
    (hnout : ¬ ∃ m ∈ ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆,
      ∀ x ∈ ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆, n * x * n⁻¹ = m * x * m⁻¹)
    (hn1 : n * (b₀⁻¹ * B.b 1) * n⁻¹ = b₀ * B.b 1)
    (hK₀N : (tr ψ (Jn 0)).map (MulAut.conj n).toMonoidHom ≤ Subgroup.normalizer (J' : Set G))
    (hnnJ : n * n ∈ Subgroup.normalizer (J' : Set G)) :
    ∃ Y : Subgroup G, IsEm 8 Y ∧ E ≤ Y ∧ Subgroup.centralizer ({B.b 1} : Set G) ⊓ K ≤ Y ∧
      Y ≤ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G) ∧
      Y ≤ J' ⊔ Subgroup.zpowers n := by
  obtain ⟨U, g, hg, hgJ, hcomm, hpair, hJU, hβU, -, -, hcover⟩ :=
    e7Frame_twD7 hF hH hC hP hT hA5 hW hstd hB hrec hJs ψ hJC hJgen hMJ hz hψz hngen hnN hnout
      hn1 hK₀N hnnJ
  obtain ⟨hEY, hCKY, hYgen⟩ :=
    le_sup_normalizer_of_frame hstd hB hrec U g hJU hβU hcover hEJ hMJ hJgen hg
  exact ⟨⨆ k, U k, (isEm_eight_of_frame U hcomm hpair).1, hEY, hCKY, hYgen,
    iSup_le_sup_normalizer_of_frame hcover hgJ⟩

theorem exists_Y_twD7_of_inverter (hF : E7NatFrame) (hH : E7NatHigh) (hC : E7NatCent)
    (hP : E7NatPsi) (hT : E7NatTau) (hA5 : E7NatA5) (hW : E7NatWeyl) {G : Type} [Group G]
    [Finite G] {b₀ : G} {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7)
    {B : Basis3 G (Row.twD7.n + 1)} (hB : Adapted B b₀ K E) (hrec : RecOut Row.twD7 B b₀)
    {J' : Subgroup G} (hJs : IsSimpleGroup ↥J') (ψ : ↥L7 ≃* ↥J')
    (hJC : J' ≤ Subgroup.centralizer ({b₀ * B.b 1} : Set G))
    (hJgen : J' ≤ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G))
    (hMJ : ⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
      Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ ≤ J')
    (hEJ : E ≤ Subgroup.zpowers (b₀ * B.b 1) ⊔ J')
    {z : ↥L7} (hz : (z : ModGL .E7 (ZMod 2)) ∈ Jn 0) (hψz : ((ψ z : ↥J') : G) = b₀⁻¹ * B.b 1)
    (hNJ : (Subgroup.normalizer (Subgroup.zpowers (b₀ * B.b 1) : Set G) ⊓
        Subgroup.normalizer (E : Set G)) ⊓
      Subgroup.normalizer ((⁅Subgroup.centralizer ({B.b 1} : Set G) ⊓ K,
        Subgroup.centralizer ({B.b 1} : Set G) ⊓ K⁆ : Subgroup G) : Set G) ≤
      Subgroup.normalizer (J' : Set G))
    {i : G} (hi : i ∈ tr ψ (Jn 0)) (hiβ : i * (b₀⁻¹ * B.b 1) * i⁻¹ = (b₀⁻¹ * B.b 1)⁻¹)
    (hiE : i ∈ Subgroup.normalizer (E : Set G)) :
    ∃ Y : Subgroup G, IsEm 8 Y ∧ E ≤ Y ∧ Subgroup.centralizer ({B.b 1} : Set G) ⊓ K ≤ Y ∧
      Y ≤ Subgroup.centralizer ({b₀} : Set G) ⊔ Subgroup.normalizer (E : Set G) ∧
      Y ≤ J' ⊔ K := by
  obtain ⟨g, hgK, hgE, hgM, hg0, hg1, -, hgout⟩ :=
    exists_beta_line_swap_outer_of_std_twD7 hstd B hB hrec
  obtain ⟨hngen, hnN, hnout, hn1, hK₀N, hnnJ⟩ := swap_mul_inverter_twD7 hF hC hstd hB hrec ψ hJC
    hJgen hMJ hz hψz hNJ hgK hgE hgM hg0 hg1 hgout hi hiβ hiE
  obtain ⟨Y, hY, hEY, hCKY, hYgen, hYn⟩ := exists_Y_twD7 hF hH hC hP hT hA5 hW hstd hB hrec hJs
    ψ hJC hJgen hMJ hEJ hz hψz hngen hnN hnout hn1 hK₀N hnnJ
  refine ⟨Y, hY, hEY, hCKY, hYgen, hYn.trans (sup_le le_sup_left ?_)⟩
  rw [Subgroup.zpowers_le]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hgK) (Subgroup.mem_sup_left (tr_le_K ψ _ hi))

end Y

end Frame

end CFSG.StandardType.FrameRoute.FS81.E7Frame
