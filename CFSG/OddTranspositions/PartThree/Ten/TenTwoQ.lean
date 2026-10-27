module

public import CFSG.OddTranspositions.PartThree.Ten.Steps
import CFSG.OddTranspositions.PartThree.Ten.TenTwo
public import CFSG.OddTranspositions.PartThree.Ten.TenTwoCover
import CFSG.OddTranspositions.PartThree.Ten.SetupPerfect
public import CFSG.OddTranspositions.PartThree.Ten.SwapImage
import CFSG.OddTranspositions.PartThree.Ten.DalphaBlocks
import CFSG.OddTranspositions.PartThree.EightSeven
import CFSG.OddTranspositions.PartThree.HalphaCentralizer
import CFSG.OddTranspositions.BlockGraph
import CFSG.OddTranspositions.SixEight
import CFSG.OddTranspositions.TheoremTwo.AalphaNonempty
public import CFSG.OddTranspositions.HalphaQuotient
import CFSG.Timmesfeld.Bridge.Asc72ZQuot
import CFSG.GroupTheory.PCore.SolvableRadical

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Connectivity CFSG.OddTranspositions.QZ

open scoped Pointwise commutatorElement

namespace TenTwoQ

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem mem_blockClass_trans {α β γ : Set G} (hβ : β ∈ blockClass α) (hγ : γ ∈ blockClass β) :
    γ ∈ blockClass α := by
  obtain ⟨g, rfl⟩ := mem_blockClass_iff'.mp hβ
  obtain ⟨k, rfl⟩ := mem_blockClass_iff'.mp hγ
  exact ⟨k * g, (mul_smul k g α).symm⟩

omit [Finite G] in
theorem DalphaStar_conj_image (hN : IsNormalSet D) {α : Set G} (g : G) :
    (fun x => g * x * g⁻¹) '' DalphaStar D α =
      DalphaStar D ((fun x => g * x * g⁻¹) '' α) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact DalphaStar.conj hN hx g
  · intro hy
    have h := DalphaStar.conj hN hy g⁻¹
    have himg : (fun x => g⁻¹ * x * g⁻¹⁻¹) '' ((fun x => g * x * g⁻¹) '' α) = α := by
      rw [Set.image_image]
      have hfun : (fun x => g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹) = id := by
        funext x
        show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
        group
      rw [hfun, Set.image_id]
    rw [himg] at h
    refine ⟨g⁻¹ * y * g⁻¹⁻¹, h, ?_⟩
    show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y
    group

omit [Finite G] in
theorem Halpha_conj (hN : IsNormalSet D) {α β : Set G} {g : G}
    (h : (fun x => g * x * g⁻¹) '' α = β) :
    Halpha D β = (Halpha D α).map (MulAut.conj g).toMonoidHom := by
  rw [Halpha, Halpha, MonoidHom.map_closure, ← h, ← DalphaStar_conj_image hN g]
  rfl

theorem exists_Dalpha_not_perp (hC : HypothesisC D) :
    ∃ β ∈ Dalpha D hC.alpha, ∃ δ ∈ Dalpha D β, δ ∉ perp D hC.alpha := by
  classical
  by_contra hcon
  push Not at hcon
  have hN := hC.setup.normal
  have hα := hC.isBlock_alpha
  have hconn := blockGraph_connected_of_connected hC.setup hα hC.conn
  obtain ⟨γ, hγc, hγ⟩ := Aalpha_nonempty hC.setup hα
  have hreach : (blockGraph D hC.alpha).Reachable ⟨hC.alpha, mem_blockClass_self _⟩ ⟨γ, hγc⟩ :=
    hconn.preconnected _ _
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  have key : ∀ δ : blockClass hC.alpha,
      Relation.ReflTransGen (blockGraph D hC.alpha).Adj ⟨hC.alpha, mem_blockClass_self _⟩ δ →
        (δ : Set G) ∈ perp D hC.alpha := by
    intro δ h
    induction h with
    | refl => exact Or.inr rfl
    | @tail x y _ hadj ih =>
      have hy : (y : Set G) ∈ Dalpha D (x : Set G) := (blockGraph_adj_iff hN hα).1 hadj.symm
      rcases ih with hx | hx
      · exact hcon _ hx _ hy
      · rw [hx] at hy
        exact Or.inl hy
  exact hγ (key _ hreach)

theorem exists_swap (hC : HypothesisC D) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    ∃ g : G, (fun x => g * x * g⁻¹) '' hC.alpha = β ∧
      (fun x => g * x * g⁻¹) '' β = hC.alpha := by
  have hN := hC.setup.normal
  obtain ⟨g₁, hg₁⟩ := mem_blockClass_iff.mp hβ.1
  have hαDβ : hC.alpha ∈ Dalpha D β :=
    ⟨mem_blockClass_of_mem_blockClass hβ.1 (mem_blockClass_self _), hC.isBlock_alpha.subset,
      hβ.2.2.1.symm, fun a ha b hb => (hβ.2.2.2 b hb a ha).symm⟩
  have h1 := Dalpha.conj hN hαDβ g₁⁻¹
  have hβα : (fun x => g₁⁻¹ * x * g₁⁻¹⁻¹) '' β = hC.alpha := by
    rw [hg₁, Set.image_image]
    have hfun : (fun x => g₁⁻¹ * (g₁ * x * g₁⁻¹) * g₁⁻¹⁻¹) = id := by
      funext x
      show g₁⁻¹ * (g₁ * x * g₁⁻¹) * g₁⁻¹⁻¹ = x
      group
    rw [hfun, Set.image_id]
  rw [hβα] at h1
  obtain ⟨n, hn, hnβ⟩ := hC.normalizer_transitive β hβ _ h1
  refine ⟨g₁ * n, ?_, ?_⟩
  · have hnα : (fun x => n * x * n⁻¹) '' hC.alpha = hC.alpha :=
      Subgroup.mem_normalizer_iff_conj_image_eq.mp hn
    rw [hg₁]
    calc (fun x => g₁ * n * x * (g₁ * n)⁻¹) '' hC.alpha
        = (fun x => g₁ * x * g₁⁻¹) '' ((fun x => n * x * n⁻¹) '' hC.alpha) := by
          rw [Set.image_image]
          congr 1
          funext x
          group
      _ = (fun x => g₁ * x * g₁⁻¹) '' hC.alpha := by rw [hnα]
  · calc (fun x => g₁ * n * x * (g₁ * n)⁻¹) '' β
        = (fun x => g₁ * x * g₁⁻¹) '' ((fun x => n * x * n⁻¹) '' β) := by
          rw [Set.image_image]
          congr 1
          funext x
          group
      _ = (fun x => g₁ * x * g₁⁻¹) '' ((fun x => g₁⁻¹ * x * g₁⁻¹⁻¹) '' hC.alpha) := by rw [hnβ]
      _ = hC.alpha := by
          rw [Set.image_image]
          have hfun : (fun x => g₁ * (g₁⁻¹ * x * g₁⁻¹⁻¹) * g₁⁻¹) = id := by
            funext x
            show g₁ * (g₁⁻¹ * x * g₁⁻¹⁻¹) * g₁⁻¹ = x
            group
          rw [hfun, Set.image_id]

theorem centralizer_inter_D_subset (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) {z : G} (hz1 : z ≠ 1)
    (hzH : z ∈ Halpha D hC.alpha) (hzc : ∀ h ∈ Halpha D hC.alpha, Commute z h) :
    ∀ y ∈ D, Commute y z → y ∈ hC.alpha ∨ y ∈ DalphaStar D hC.alpha := by
  classical
  set X : Subgroup G := Subgroup.closure {y | y ∈ D ∧ Commute y z} with hXdef
  have hXle : X ≤ Subgroup.centralizer {z} := by
    rw [hXdef, Subgroup.closure_le]
    rintro y ⟨-, hy⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 hy.eq
  have hXD : (X : Set G) ∩ D = {y | y ∈ D ∧ Commute y z} := by
    ext y
    constructor
    · rintro ⟨hyX, hyD⟩
      exact ⟨hyD, Subgroup.mem_centralizer_singleton_iff.1 (hXle hyX)⟩
    · rintro ⟨hyD, hyz⟩
      exact ⟨Subgroup.subset_closure ⟨hyD, hyz⟩, hyD⟩
  have hX : X = Subgroup.closure ((X : Set G) ∩ D) := by rw [hXD]
  have hdX : hC.d ∈ X :=
    Subgroup.subset_closure ⟨hC.hd, (Subgroup.mem_centralizer_singleton_iff.1
      (Halpha_le_centralizer_d hC hzH) : Commute z hC.d).symm⟩
  have hEX : hC.E ⊆ (X : Set G) := by
    intro x hx
    rw [← hC.DalphaStar_alpha] at hx
    exact Subgroup.subset_closure ⟨DalphaStar_subset hC.isBlock_alpha hx,
      (hzc x (Subgroup.subset_closure hx)).symm⟩
  have hproper : X ≠ ⊤ := by
    intro htop
    have hzcen : z ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subgroup.mem_centralizer_singleton_iff.1 (hXle (htop ▸ Subgroup.mem_top g))
    have hbot := hrad (Subgroup.center G) inferInstance inferInstance
    rw [hbot, Subgroup.mem_bot] at hzcen
    exact hz1 hzcen
  have h68 := inter_D_subset_perp hC hX hdX hEX hproper
  intro y hyD hyz
  exact h68 ⟨Subgroup.subset_closure ⟨hyD, hyz⟩, hyD⟩

theorem exists_central_generator {hC : HypothesisC D} {f n : ℕ} (hT : TenHyp hC f n)
    (hcard : Nat.card (CFSG.pCore 2 (Halpha D hC.alpha)) = 2) :
    ∃ z : Halpha D hC.alpha, z ≠ 1 ∧ z * z = 1 ∧ z ∈ Subgroup.center (Halpha D hC.alpha) ∧
      ∀ m : Halpha D hC.alpha, m ∈ Subgroup.center (Halpha D hC.alpha) → m * m = 1 →
        m = 1 ∨ m = z := by
  set H := Halpha D hC.alpha
  set Q := CFSG.pCore 2 H with hQ
  obtain ⟨z, hz1, huniq⟩ := (Nat.card_eq_two_iff' (1 : Q)).1 hcard
  have hQc : Q ≤ Subgroup.center H := (CFSG.pCore_le_solvableRadical 2 H).trans hT.radH.le
  have hzz : (z : H) * z = 1 := by
    have h := pow_card_eq_one' (G := Q) (x := z)
    rw [hcard, pow_two] at h
    exact congrArg Subtype.val h
  refine ⟨z, fun h => hz1 (Subtype.ext h), hzz, hQc z.2, ?_⟩
  intro m hm hmm
  by_cases hm1 : m = 1
  · exact Or.inl hm1
  · right
    have hnorm : (Subgroup.zpowers m).Normal :=
      Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hm)
    have hdd : m ^ 2 ^ 1 = 1 := by simpa [pow_two] using hmm
    have hp : IsPGroup 2 (Subgroup.zpowers m) := CentralQuot.isPGroup_zpowers_of_pow hdd
    have hle : Subgroup.zpowers m ≤ Q := le_sSup ⟨hnorm, hp⟩
    have hmQ : m ∈ Q := hle (Subgroup.mem_zpowers m)
    have h1 : (⟨m, hmQ⟩ : Q) ≠ 1 := fun h => hm1 (congrArg Subtype.val h)
    exact congrArg Subtype.val (huniq _ h1)

omit [Finite G] in
theorem commute_coe_iff {H : Subgroup G} {x y : H} : Commute x y ↔ Commute (x : G) (y : G) :=
  ⟨fun h => congrArg Subtype.val h.eq, fun h => Subtype.ext h.eq⟩

theorem mem_Dalpha_of_commute_of_notMem (hC : HypothesisC D) {β : Set G}
    (hβ : β ∈ blockClass hC.alpha) {y u : G} (hyD : y ∈ D) (hyβ : y ∉ β) (hu : u ∈ β)
    (huy : Commute u y) : ∃ γ ∈ Dalpha D β, y ∈ γ := by
  obtain ⟨γ, hγ, hyγ⟩ := exists_mem_blockClass_of_mem hC.setup.isClass hC.isBlock_alpha hyD
  have hne : β ≠ γ := fun h => hyβ (h ▸ hyγ)
  exact ⟨γ, mem_Dalpha_of_commute_mem hC.setup.normal hC.setup.oddT hC.isBlock_alpha hβ hγ hne
    hu hyγ huy, hyγ⟩

omit [Finite G] in
theorem commute_of_mem_Halpha_block {β : Set G} {a y : G} (ha : a ∈ β)
    (hy : y ∈ Halpha D β) : Commute a y := by
  have hle : Halpha D β ≤ Subgroup.centralizer {a} := by
    rw [Halpha, Subgroup.closure_le]
    rintro x ⟨γ, hγ, hxγ⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hγ.2.2.2 a ha x hxγ).symm.eq
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm

theorem hP_of_block (hC : HypothesisC D) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) :
    ∀ y ∈ DstarH hC, y ∉ {x : Halpha D hC.alpha | (x : G) ∈ β} →
      ∀ u ∈ {x : Halpha D hC.alpha | (x : G) ∈ β}, Commute y u →
        ∀ u' ∈ {x : Halpha D hC.alpha | (x : G) ∈ β}, Commute y u' := by
  intro y hy hyβ u hu huy u' hu'
  obtain ⟨γ, hγ, hyγ⟩ := mem_Dalpha_of_commute_of_notMem hC hβ.1
    (DalphaStar_subset hC.isBlock_alpha hy) hyβ hu (commute_coe_iff.1 huy).symm
  exact commute_coe_iff.2 (hγ.2.2.2 (u' : G) hu' (y : G) hyγ).symm

theorem hB_of_block (hC : HypothesisC D) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    {v : Halpha D hC.alpha} (hv : (v : G) ∈ β) :
    ∀ h : Halpha D hC.alpha, Commute h v → ∀ y : Halpha D hC.alpha,
      h * y * h⁻¹ ∈ {x : Halpha D hC.alpha | (x : G) ∈ β} ↔
        y ∈ {x : Halpha D hC.alpha | (x : G) ∈ β} := by
  intro h hhv y
  have hhv' : (h : G) * (v : G) * (h : G)⁻¹ = (v : G) := by
    rw [(commute_coe_iff.1 hhv).eq, mul_inv_cancel_right]
  have himg := conj_image_eq_of_mem hC h.2 hβ hv (by rw [hhv']; exact hv)
  exact conj_mem_iff_of_conj_image_eq himg (y : G)

omit [Finite G] in
theorem sign_right_eq_one_of_mem_commutator {H : Subgroup G} {f n : ℕ} (q : H →* L2Wreath f n)
    {c : G} (hcH : c ∈ H) (hc : c ∈ ⁅H, H⁆) :
    Equiv.Perm.sign (q ⟨c, hcH⟩).right = 1 := by
  obtain ⟨ψ, hψ⟩ : ∃ ψ : H →* ℤˣ, ∀ x, ψ x = Equiv.Perm.sign (q x).right :=
    ⟨Equiv.Perm.sign.comp (SemidirectProduct.rightHom.comp q), fun x => rfl⟩
  have hle : ⁅H, H⁆ ≤ ψ.ker.map H.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : H), ⟨b, hb⟩⁆, MonoidHom.mem_ker.2 ?_, rfl⟩
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.2 (Commute.all _ _)
  obtain ⟨c'', hc'', hcc⟩ := hle hc
  have h1 : c'' = ⟨c, hcH⟩ := Subtype.ext hcc
  rw [h1] at hc''
  have h2 : ψ ⟨c, hcH⟩ = 1 := MonoidHom.mem_ker.1 hc''
  rwa [hψ] at h2

theorem wreathCover_tenHom (hC : HypothesisC D) {f n : ℕ} (hT : TenHyp hC f n)
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n) :
    WreathCover (Halpha D hC.alpha) f n (DstarH hC) (tenHom hC e) :=
  { two_le := hT.two_le
    five_le := hT.five_le
    surj := tenHom_surjective hC e
    ker_eq := tenHom_ker hC e
    isClass := ⟨DstarH_isClass hC, DstarH_isOddTransp hC, DstarH_closure_eq_top hC⟩
    image := tenHom_image_DstarH hC hT.two_le hT.five_le e }

theorem exists_not_mem_block (hC : HypothesisC D) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    {δ : Set G} (hδ : δ ∈ Dalpha D β) (hδperp : δ ∉ perp D hC.alpha) :
    ∃ y ∈ DstarH hC, y ∉ {x : Halpha D hC.alpha | (x : G) ∈ β} := by
  by_contra hcon
  push Not at hcon
  have hα := hC.isBlock_alpha
  have hDα : Dalpha D hC.alpha = {β} := by
    refine Set.eq_singleton_iff_unique_mem.2 ⟨hβ, fun γ hγ => ?_⟩
    obtain ⟨x, hx⟩ := nonempty_of_mem_blockClass hα.nonempty hγ.1
    have hxE : x ∈ DalphaStar D hC.alpha := subset_DalphaStar hγ hx
    have hxβ : x ∈ β := hcon ⟨x, Subgroup.subset_closure hxE⟩ hxE
    exact eq_of_mem_of_mem_blockClass hα hγ.1 hβ.1 ⟨x, hx, hxβ⟩
  have hDβ := Dalpha_eq_singleton_of_Dalpha_eq_singleton hC.setup.normal hα.subset hβ hDα
  rw [hDβ, Set.mem_singleton_iff] at hδ
  exact hδperp (mem_perp_iff.2 (Or.inr hδ))

theorem center_le_commutator_Halpha (hC : HypothesisC D) {f n : ℕ} (hT : TenHyp hC f n)
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n)
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {v : G} (hv : v ∈ β)
    (hne : ∃ y ∈ DstarH hC, y ∉ {x : Halpha D hC.alpha | (x : G) ∈ β}) :
    ∀ m ∈ Subgroup.center (Halpha D hC.alpha), (m : G) ∈ ⁅Halpha D β, Halpha D β⁆ := by
  intro m hm
  have hvE : v ∈ DalphaStar D hC.alpha := subset_DalphaStar hβ hv
  have hvH : v ∈ Halpha D hC.alpha := Subgroup.subset_closure hvE
  have h1 := (wreathCover_tenHom hC hT e).center_le_commutator (hP_of_block hC hβ)
    (v := (⟨v, hvH⟩ : Halpha D hC.alpha)) hv hvE (hB_of_block hC hβ hv) hne hm
  have hY : Subgroup.closure {y | y ∈ DstarH hC ∧
      y ∉ {x : Halpha D hC.alpha | (x : G) ∈ β} ∧ Commute y (⟨v, hvH⟩ : Halpha D hC.alpha)} ≤
      (Halpha D β).comap (Halpha D hC.alpha).subtype := by
    rw [Subgroup.closure_le]
    rintro y ⟨hyE, hyβ, hyv⟩
    obtain ⟨γ, hγ, hyγ⟩ := mem_Dalpha_of_commute_of_notMem hC hβ.1
      (DalphaStar_subset hC.isBlock_alpha hyE) hyβ hv (commute_coe_iff.1 hyv).symm
    exact Subgroup.subset_closure ⟨γ, hγ, hyγ⟩
  have hYle := Subgroup.map_le_iff_le_comap.2 hY
  have hmem : (m : G) ∈ (⁅_, _⁆ : Subgroup (Halpha D hC.alpha)).map
      (Halpha D hC.alpha).subtype := ⟨m, h1, rfl⟩
  rw [Subgroup.map_commutator] at hmem
  exact Subgroup.commutator_mono hYle hYle hmem

omit [Finite G] in
theorem conj_facts (hC : HypothesisC D) {β : Set G} {g : G}
    (hgα : (fun x => g * x * g⁻¹) '' hC.alpha = β)
    (hgβ : (fun x => g * x * g⁻¹) '' β = hC.alpha) {z : G} (hzH : z ∈ Halpha D hC.alpha)
    (hzc : ∀ h ∈ Halpha D hC.alpha, Commute z h) (hzcomm : z ∈ ⁅Halpha D β, Halpha D β⁆) :
    g * z * g⁻¹ ∈ Halpha D β ∧ g * z * g⁻¹ ∈ Halpha D hC.alpha ∧
      g * z * g⁻¹ ∈ ⁅Halpha D hC.alpha, Halpha D hC.alpha⁆ ∧
      ∀ y ∈ Halpha D β, Commute (g * z * g⁻¹) y := by
  have hN := hC.setup.normal
  have hHβ : Halpha D β = (Halpha D hC.alpha).map (MulAut.conj g).toMonoidHom :=
    Halpha_conj hN hgα
  have hHα : Halpha D hC.alpha = (Halpha D β).map (MulAut.conj g).toMonoidHom :=
    Halpha_conj hN hgβ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hHβ]
    exact ⟨z, hzH, rfl⟩
  · have : g * z * g⁻¹ ∈ (Halpha D β).map (MulAut.conj g).toMonoidHom :=
      ⟨z, Subgroup.commutator_le_self _ hzcomm, rfl⟩
    rwa [← hHα] at this
  · have hcomm_eq : ⁅Halpha D hC.alpha, Halpha D hC.alpha⁆ =
        (⁅Halpha D β, Halpha D β⁆).map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.map_commutator, ← hHα]
    rw [hcomm_eq]
    exact ⟨z, hzcomm, rfl⟩
  · intro y hy
    rw [hHβ] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact (Commute.conj_iff g).2 (hzc x hx)

theorem commute_Halpha_of_mem_commutator (hC : HypothesisC D) {f n : ℕ} (hT : TenHyp hC f n)
    (e : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* L2Wreath f n)
    {z' : Halpha D hC.alpha} (hz'1 : z' ≠ 1) (hz'z : z' * z' = 1)
    (hz'c : z' ∈ Subgroup.center (Halpha D hC.alpha))
    (hz'm : ∀ m : Halpha D hC.alpha, m ∈ Subgroup.center (Halpha D hC.alpha) → m * m = 1 →
      m = 1 ∨ m = z')
    {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {v : G} (hv : v ∈ β) {g : G}
    (hgα : (fun x => g * x * g⁻¹) '' hC.alpha = β) (hgβ : (fun x => g * x * g⁻¹) '' β = hC.alpha)
    (hzcomm : (z' : G) ∈ ⁅Halpha D β, Halpha D β⁆) :
    ∀ y ∈ Halpha D β, Commute (z' : G) y := by
  have hvE : v ∈ DalphaStar D hC.alpha := subset_DalphaStar hβ hv
  have hvH : v ∈ Halpha D hC.alpha := Subgroup.subset_closure hvE
  have hzz : (z' : G) * (z' : G) = 1 := congrArg Subtype.val hz'z
  have hz1 : (z' : G) ≠ 1 := fun h => hz'1 (Subtype.ext h)
  have hzc : ∀ h ∈ Halpha D hC.alpha, Commute (z' : G) h := fun h hh =>
    commute_coe_iff.1 (Subgroup.mem_center_iff.1 hz'c ⟨h, hh⟩).symm
  obtain ⟨hcHβ, hcH, hccomm, hcentral⟩ := conj_facts hC hgα hgβ z'.2 hzc hzcomm
  have hcc : g * (z' : G) * g⁻¹ * (g * (z' : G) * g⁻¹) = 1 := by
    calc g * (z' : G) * g⁻¹ * (g * (z' : G) * g⁻¹) = g * ((z' : G) * (z' : G)) * g⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  have hc1 : g * (z' : G) * g⁻¹ ≠ 1 := fun h => hz1 (by
    calc (z' : G) = g⁻¹ * (g * (z' : G) * g⁻¹) * g := by group
      _ = g⁻¹ * 1 * g := by rw [h]
      _ = 1 := by group)
  have hcomm_c : ∀ x ∈ DstarH hC, Commute x (⟨v, hvH⟩ : Halpha D hC.alpha) →
      Commute (⟨g * (z' : G) * g⁻¹, hcH⟩ : Halpha D hC.alpha) x := by
    intro x hx hxv
    by_cases hxβ : (x : G) ∈ β
    · exact commute_coe_iff.2 (commute_of_mem_Halpha_block hxβ hcHβ).symm
    · obtain ⟨γ, hγ, hxγ⟩ := mem_Dalpha_of_commute_of_notMem hC hβ.1
        (DalphaStar_subset hC.isBlock_alpha hx) hxβ hv (commute_coe_iff.1 hxv).symm
      exact commute_coe_iff.2 (hcentral (x : G) (Subgroup.subset_closure ⟨γ, hγ, hxγ⟩))
  have hq1 := (wreathCover_tenHom hC hT e).q_eq_one_of_commute
    (v := (⟨v, hvH⟩ : Halpha D hC.alpha)) hvE
    (sign_right_eq_one_of_mem_commutator (tenHom hC e) hcH hccomm) hcomm_c
  have hc'cen : (⟨g * (z' : G) * g⁻¹, hcH⟩ : Halpha D hC.alpha) ∈
      Subgroup.center (Halpha D hC.alpha) := by
    rw [← tenHom_ker hC e]
    exact MonoidHom.mem_ker.2 hq1
  have hc'z := (hz'm _ hc'cen (Subtype.ext hcc)).resolve_left
    (fun h => hc1 (congrArg Subtype.val h))
  have hcz : g * (z' : G) * g⁻¹ = (z' : G) := congrArg Subtype.val hc'z
  intro y hy
  rw [← hcz]
  exact hcentral y hy

theorem false_of_card_two (hC : HypothesisC D) {f n : ℕ} (hT : TenHyp hC f n)
    (hcard : Nat.card (CFSG.pCore 2 (Halpha D hC.alpha)) = 2) : False := by
  obtain ⟨e⟩ := hT.iso
  have hα := hC.isBlock_alpha
  obtain ⟨z', hz'1, hz'z, hz'c, hz'm⟩ := exists_central_generator hT hcard
  have hz1 : (z' : G) ≠ 1 := fun h => hz'1 (Subtype.ext h)
  have hzc : ∀ h ∈ Halpha D hC.alpha, Commute (z' : G) h := fun h hh =>
    commute_coe_iff.1 (Subgroup.mem_center_iff.1 hz'c ⟨h, hh⟩).symm
  have h68 := centralizer_inter_D_subset hC hT.rad hz1 z'.2 hzc
  obtain ⟨β, hβ, δ, hδ, hδperp⟩ := exists_Dalpha_not_perp hC
  obtain ⟨g, hgα, hgβ⟩ := exists_swap hC hβ
  obtain ⟨v, hv⟩ := nonempty_of_mem_blockClass hα.nonempty hβ.1
  have hzcomm := center_le_commutator_Halpha hC hT e hβ hv
    (exists_not_mem_block hC hβ hδ hδperp) z' hz'c
  have hcent := commute_Halpha_of_mem_commutator hC hT e hz'1 hz'z hz'c hz'm hβ hv hgα hgβ hzcomm
  have hδα : δ ∈ blockClass hC.alpha := mem_blockClass_trans hβ.1 hδ.1
  obtain ⟨y, hyδ⟩ := nonempty_of_mem_blockClass hα.nonempty hδα
  have hzy : Commute y (z' : G) :=
    (hcent y (Subgroup.subset_closure ⟨δ, hδ, hyδ⟩)).symm
  rcases h68 y (hδ.2.1 hyδ) hzy with hyα | hyE
  · exact hδperp (mem_perp_iff.2 (Or.inr
      (eq_of_mem_of_mem_blockClass hα hδα (mem_blockClass_self _) ⟨y, hyδ, hyα⟩)))
  · obtain ⟨γ, hγ, hyγ⟩ := hyE
    exact hδperp (mem_perp_iff.2 (Or.inl
      ((eq_of_mem_of_mem_blockClass hα hδα hγ.1 ⟨y, hyδ, hyγ⟩) ▸ hγ)))

end TenTwoQ

theorem pCore_eq_bot_of_tenHyp :
    ∀ (G : Type) [Group G] [Finite G] (D : Set G) (hC : HypothesisC D) (f n : ℕ),
      TenHyp hC f n → CFSG.pCore 2 (Halpha D hC.alpha) = ⊥ := by
  intro G _ _ D hC f n hT
  rcases tenSetupQ_holds G D hC f n hT with h | ⟨-, hcard⟩
  · exact h
  · exact (TenTwoQ.false_of_card_two hC hT hcard).elim

theorem tenTwo_holds : TenTwo :=
  tenTwo_of_pCore_eq_bot pCore_eq_bot_of_tenHyp

end CFSG.OddTranspositions.PartThree

end
