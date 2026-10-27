module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec55
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec56Defs
import CFSG.RankThree.PartTwo.Sec21.FF79Lemma41
import CFSG.RankThree.PartTwo.Sec21.FF81Sec36Z
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.FF81Sec53
import CFSG.RankThree.PartTwo.Sec21.FF81Sec54
import CFSG.RankThree.PartTwo.Sec21.FF84S36Ab
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
import CFSG.Quasithin.Background.A1cRank
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LinearAlgebra.LinearGroups.LinearTwo
import CFSG.LocalAnalysis.ComponentClassification.CatFC.L44CoverTrivial
import CFSG.LocalAnalysis.ComponentClassification.CatalogueUStatement
import CFSG.LocalAnalysis.ComponentClassification.GSLitType
import CFSG.LocalAnalysis.ComponentClassification.GSThmB7Basic
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog8L4
import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic
import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent
import CFSG.Sporadic.Th.F2Spec

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79
open P51 (V e)
open S36 (hypF hypU hypA dot)

variable {G : Type} [Group G] [Finite G]

namespace S56

theorem conj_mem_cenS {s₀ : G} {H : Subgroup G} (hH : ∀ g ∈ Cen s₀, ∀ x ∈ H, g * x * g⁻¹ ∈ H)
    {g x : G} (hg : g ∈ Cen s₀) (hx : x ∈ CenS H) : g * x * g⁻¹ ∈ CenS H := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro y hy
  have hy' := hH g⁻¹ ((Cen s₀).inv_mem hg) y hy
  rw [inv_inv] at hy'
  have := hx _ hy'
  calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
    _ = g * x * g⁻¹ * y := by group

theorem conj_mem_center {s₀ g z : G} (hg : g ∈ Cen s₀)
    (hz : z ∈ Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) :
    g * z * g⁻¹ ∈ Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀)) :=
  Subgroup.mem_inf.mpr ⟨op_two_conj hg hz.1,
    conj_mem_cenS (fun _ hg _ hx => op_two_conj hg hx) hg hz.2⟩

theorem conj_mem_K {s₀ g x : G} (hg : g ∈ Cen s₀)
    (hx : x ∈ CenS (Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀)))) :
    g * x * g⁻¹ ∈ CenS (Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) :=
  conj_mem_cenS (fun _ hg _ hz => conj_mem_center hg hz) hg hx

theorem S_le_K (s₀ : G) : Op 2 (Cen s₀) ≤ CenS (Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) :=
  fun x hx => Subgroup.mem_centralizer_iff.mpr fun z hz =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 x hx).symm

theorem s₀_mem_center {s₀ : G} (hs : orderOf s₀ = 2) :
    s₀ ∈ Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀)) :=
  Subgroup.mem_inf.mpr ⟨mem_op_two_self hs, Subgroup.mem_centralizer_iff.mpr fun _ hh =>
    Subgroup.mem_centralizer_singleton_iff.mp (op_two_le s₀ hh)⟩

theorem K_le_cen {s₀ : G} (hs : orderOf s₀ = 2) :
    CenS (Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) ≤ Cen s₀ := fun _ hx =>
  Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hx s₀ (s₀_mem_center hs)).symm

set_option maxRecDepth 100000 in
theorem eq_zero_of_hyp234 : ∀ x : Fin 3 → ZMod 3, dot (hypF 2) x = 0 → dot (hypF 3) x = 0 →
    dot (hypF 4) x = 0 → x = 0 := by decide

set_option maxRecDepth 100000 in
theorem span_add : ∀ i : Fin 13, ∀ x z : Fin 3 → ZMod 3, dot (hypF i) x ≠ 0 →
    ∃ c : ZMod 3, dot (hypF i) (z - c • x) = 0 := by decide +kernel

set_option maxRecDepth 100000 in
theorem filter_u₃ :
    Finset.univ.filter (fun i : Fin 13 => dot (hypF i) ![0, 0, 1] = 0) = {0, 1, 3, 4} := by
  decide

end S56

variable {b : G} {L B : Subgroup G} {b₁ b₂ b₃ t₀ s₀ : G}

section Tools

variable (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀)
include h5

theorem FF81Sec5.mem_cenS_A₁_of_hyp {i : Fin 13} {x : Fin 3 → ZMod 3} (hx : dot (hypF i) x ≠ 0)
    {y : G} (hyi : y ∈ CenS (S55.hyp h5.εA i)) (hyx : y * h5.εA x = h5.εA x * y) :
    y ∈ CenS (A₁sub b b₁ b₂ b₃) := by
  refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
  obtain ⟨z, rfl⟩ := h5.coordA.surj a ha
  obtain ⟨c, hc⟩ := S56.span_add i x z hx
  have hz : z = c • x + (z - c • x) := by abel
  have h1 : Commute (h5.εA (z - c • x)) y :=
    Subgroup.mem_centralizer_iff.mp hyi _ ((h5.coordA.mem_hyp i _).2 hc)
  have h2 : Commute (h5.εA x) y := hyx.symm
  rw [hz, h5.coordA.add, h5.coordA.smul]
  exact ((h2.pow_left c.val).mul_left h1).eq

theorem FF81Sec5.mem_W_of_dot {i : Fin 13} {x : Fin 3 → ZMod 3} (hx : dot (hypF i) x = 0) {y : G}
    (hy : y ∈ h5.W i) : y ∈ Op 2 (Cen s₀) ⊓ Cen (h5.εA x) := by
  have hy' : y ∈ Op 2 (Cen s₀) ⊓ CenS (S55.hyp h5.εA i) := hy
  exact Subgroup.mem_inf.mpr ⟨hy'.1, Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hy'.2 _ ((h5.coordA.mem_hyp i _).2 hx)).symm⟩

theorem FF81Sec5.W_le_center (hbig : h5.Big) {i : Fin 13} (hi : i = 2 ∨ i = 3 ∨ i = 4) :
    h5.W i ≤ Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀)) := by
  rw [hbig.center_eq]
  rcases hi with rfl | rfl | rfl
  exacts [le_sup_left.trans le_sup_left, le_sup_right.trans le_sup_left, le_sup_right]

theorem FF81Sec5.b_cube : b ^ 3 = 1 := h5.εA_b ▸ h5.coordA.cube _

theorem FF81Sec5.orderOf_b : orderOf b = 3 := by
  rw [← h5.εA_b]; exact h5.coordA.orderOf (by decide)

theorem FF81Sec5.b_mem_A₁ : b ∈ A₁sub b b₁ b₂ b₃ := Subgroup.subset_closure (by simp)

theorem FF81Sec5.commute_of_dec {i : ℤ} {l : G} (hy : b ^ i * l ∈ Cen b) : Commute (b ^ i) l := by
  have hby : Commute b (b ^ i * l) := (Subgroup.mem_centralizer_singleton_iff.mp hy).symm
  have hl : l = b ^ (-i) * (b ^ i * l) := by group
  rw [hl]
  exact (Commute.zpow_zpow_self b i (-i)).mul_right (hby.zpow_left i)

theorem FF81Sec5.zpow_b_cube (i : ℤ) : (b ^ i) ^ 3 = 1 := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h5.b_cube, one_zpow]

theorem FF81Sec5.mem_L_of_coprime {k : G} (hkb : k ∈ Cen b) (hord : Nat.Coprime 3 (orderOf k)) :
    k ∈ L := by
  obtain ⟨i, l, hl, rfl⟩ := h5.basis.cen_dec' h5.opp_eq_bot hkb
  have hcomm := h5.commute_of_dec hkb
  rcases Nat.lt_or_ge 1 (orderOf (b ^ i * l)) with hn | hn
  · obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hord hn
    have h1 : b ^ i * l = (b ^ i * l) ^ (3 * m) := by
      rw [← pow_mod_orderOf, hm, pow_one]
    rw [h1, hcomm.mul_pow, pow_mul, h5.zpow_b_cube, one_pow, one_mul]
    exact L.pow_mem hl _
  · have : orderOf (b ^ i * l) = 1 := le_antisymm hn (orderOf_pos _)
    rw [orderOf_eq_one_iff] at this
    rw [this]; exact L.one_mem

end Tools

section ClaimA

variable (hKF : KF_Sp6Levi) (hKC : KF_Sp6ShortRootCen)
  (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) (hbig : h5.Big)

include hKF h5 hbig in
theorem FF81Sec5.card_W_eight :
    Nat.card (h5.W 2) = 8 ∧ Nat.card (h5.W 3) = 8 ∧ Nat.card (h5.W 4) = 8 := by
  obtain ⟨g, hgH, hg⟩ := h5.gens hKF
  have h2 : Nat.card (h5.W 2) = 8 := by rw [hbig.elemW2.2]; norm_num
  exact ⟨h2, by rw [h5.card_W hgH hg (r := 2) (w := [2]) (by decide), h2],
    by rw [h5.card_W hgH hg (r := 2) (w := [0, 2]) (by decide), h2]⟩

include hKF h5 hbig in
theorem FF81Sec5.eq_one_of_mem_A₁_K {a : G} (ha : a ∈ A₁sub b b₁ b₂ b₃)
    (haK : a ∈ CenS (Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀)))) : a = 1 := by
  obtain ⟨x, rfl⟩ := h5.coordA.surj a ha
  by_contra hne
  have hx0 : x ≠ 0 := fun h => hne (by rw [h, h5.coordA.zero])
  have key : ∀ i : Fin 13, (i = 2 ∨ i = 3 ∨ i = 4) → dot (hypF i) x ≠ 0 → False := by
    intro i hi hxi
    have hle : h5.W i ≤ Op 2 (Cen s₀) ⊓ CenS (A₁sub b b₁ b₂ b₃) := fun y hy => by
      have hy' : y ∈ Op 2 (Cen s₀) ⊓ CenS (S55.hyp h5.εA i) := hy
      exact Subgroup.mem_inf.mpr ⟨hy'.1, h5.mem_cenS_A₁_of_hyp hxi hy'.2
        (Subgroup.mem_centralizer_iff.mp haK y (h5.W_le_center hbig hi hy))⟩
    have := Subgroup.card_le_of_le hle
    rw [h5.card_S_cenS_A₁ hKF] at this
    have h8 : Nat.card (h5.W i) = 8 := by
      obtain ⟨c2, c3, c4⟩ := h5.card_W_eight hKF hbig
      rcases hi with rfl | rfl | rfl
      exacts [c2, c3, c4]
    omega
  by_cases h2 : dot (hypF 2) x = 0
  · by_cases h3 : dot (hypF 3) x = 0
    · by_cases h4 : dot (hypF 4) x = 0
      · exact hx0 (S56.eq_zero_of_hyp234 x h2 h3 h4)
      · exact key 4 (by simp) h4
    · exact key 3 (by simp) h3
  · exact key 2 (by simp) h2

include hKF hKC h5 hbig in
theorem FF81Sec5.coprime_K :
    Nat.Coprime (Nat.card ↥(CenS (Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))))) 3 := by
  set K := CenS (Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) with hK
  have hB := h5.basis
  have hC := hKC G L hB.hyp.model b₁ b₂ b₃ hB.hb₁ hB.hb₂ hB.hb₃ hB.elem hB.selfcen
    hB.monoL_stab s₀ h5.hs₀L h5.hs₀ h5.s₀_b₁ h5.s₀_u₃ h5.hs₀b
  rw [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbs : b ∈ Cen s₀ := h5.A₁_le_cen_s₀ h5.b_mem_A₁
  have hP : IsPGroup 3 (Subgroup.zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h5.orderOf_b, pow_one])
  have hPN : Subgroup.zpowers b ≤ Subgroup.normalizer (K : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_normalizer_fintype fun x hx => S56.conj_mem_K hbs hx)
  obtain ⟨y, hyK, hy3, hyb⟩ := CFSG.Quasithin.exists_orderOf_eq_of_isPGroup_normalizer hP hPN h3
  have hyb' : y * b = b * y :=
    (Subgroup.mem_centralizer_iff.mp hyb b (Subgroup.mem_zpowers b)).symm
  obtain ⟨i, l, hl, rfl⟩ := hB.cen_dec' h5.opp_eq_bot
    (Subgroup.mem_centralizer_singleton_iff.mpr hyb')
  have hcomm := h5.commute_of_dec (Subgroup.mem_centralizer_singleton_iff.mpr hyb')
  have hls : l ∈ Cen s₀ := by
    have := (Cen s₀).mul_mem ((Cen s₀).zpow_mem hbs (-i)) (S56.K_le_cen h5.hs₀ hyK)
    rwa [show b ^ (-i) * (b ^ i * l) = l by group] at this
  have hl3 : l ^ 3 = 1 := by
    have := pow_orderOf_eq_one (b ^ i * l)
    rw [hy3, hcomm.mul_pow, h5.zpow_b_cube, one_mul] at this
    exact this
  obtain ⟨c, hc, hcl⟩ := hC.1 l ⟨hl, hls⟩ hl3
  have hcb : Commute c (b ^ i) := Commute.zpow_right (h5.comm_b_of_mem_L hc.1) i
  have hcy : c * (b ^ i * l) * c⁻¹ = b ^ i * (c * l * c⁻¹) := by
    calc c * (b ^ i * l) * c⁻¹ = (c * b ^ i) * l * c⁻¹ := by group
      _ = (b ^ i * c) * l * c⁻¹ := by rw [hcb.eq]
      _ = b ^ i * (c * l * c⁻¹) := by group
  have hmemA : c * (b ^ i * l) * c⁻¹ ∈ A₁sub b b₁ b₂ b₃ := by
    rw [hcy]
    exact (A₁sub b b₁ b₂ b₃).mul_mem ((A₁sub b b₁ b₂ b₃).zpow_mem h5.b_mem_A₁ i)
      (Subgroup.closure_mono (Set.subset_insert _ _) hcl)
  have h1 := h5.eq_one_of_mem_A₁_K hKF hbig hmemA (S56.conj_mem_K hc.2 hyK)
  rw [conj_eq_one_iff] at h1
  rw [h1, orderOf_one] at hy3
  omega

include hKF hKC h5 hbig in
theorem FF81Sec5.K_inf_cen_le :
    CenS (Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) ⊓ Cen b ≤ Op 2 (Cen s₀) := by
  set K := CenS (Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) with hK
  have hB := h5.basis
  have hC := hKC G L hB.hyp.model b₁ b₂ b₃ hB.hb₁ hB.hb₂ hB.hb₃ hB.elem hB.selfcen
    hB.monoL_stab s₀ h5.hs₀L h5.hs₀ h5.s₀_b₁ h5.s₀_u₃ h5.hs₀b
  have hcop := h5.coprime_K hKF hKC hbig
  have hYL : K ⊓ Cen b ≤ L ⊓ Cen s₀ := fun k hk => by
    obtain ⟨hkK, hkb⟩ := Subgroup.mem_inf.mp hk
    refine Subgroup.mem_inf.mpr ⟨h5.mem_L_of_coprime hkb ?_, S56.K_le_cen h5.hs₀ hkK⟩
    have hd : orderOf k ∣ Nat.card K := by
      have := orderOf_dvd_natCard (⟨k, hkK⟩ : K)
      rwa [Subgroup.orderOf_mk] at this
    exact Nat.Coprime.coprime_dvd_right hd hcop.symm
  have hYn : L ⊓ Cen s₀ ≤ Nor (K ⊓ Cen b) := fun l hl =>
    Subgroup.mem_normalizer_fintype fun k hk => by
      obtain ⟨hkK, hkb⟩ := Subgroup.mem_inf.mp hk
      have hlb : l ∈ Cen b :=
        Subgroup.mem_centralizer_singleton_iff.mpr (h5.comm_b_of_mem_L (Subgroup.mem_inf.mp hl).1)
      exact Subgroup.mem_inf.mpr ⟨S56.conj_mem_K (Subgroup.mem_inf.mp hl).2 hkK,
        (Cen b).mul_mem ((Cen b).mul_mem hlb hkb) ((Cen b).inv_mem hlb)⟩
  have hYc : Nat.Coprime (Nat.card ↥(K ⊓ Cen b)) 3 :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le inf_le_left) hcop
  have h128 := hC.2.1 _ hYL hYn hYc
  have hRY : Op 2 (Cen s₀) ⊓ Cen b ≤ K ⊓ Cen b := inf_le_inf_right _ (S56.S_le_K s₀)
  have heq := Subgroup.eq_of_le_of_card_ge hRY (by rw [hbig.cardR]; exact h128)
  rw [← heq]
  exact inf_le_left

include hKF hKC h5 hbig in
theorem FF81Sec5.cenS_center (c2 : FF81Conc5_2 b b₁ b₂ b₃ s₀) :
    CenS (Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) = Op 2 (Cen s₀) := by
  set K := CenS (Op 2 (Cen s₀) ⊓ CenS (Op 2 (Cen s₀))) with hK
  refine le_antisymm ?_ (S56.S_le_K s₀)
  obtain ⟨-, -, -, -, hhyp⟩ := c2
  have hA₁ : CFSG.IsElementaryAbelian 3 (A₁sub b b₁ b₂ b₃) :=
    CFSG.IsElementaryAbelian.of_forall (fun x hx y hy => h5.A₁_comm hx hy) fun x hx => by
      obtain ⟨z, rfl⟩ := h5.coordA.surj x hx
      exact h5.coordA.cube z
  have hA₁' : CFSG.Open.IsElemAbelian 3 (A₁sub b b₁ b₂ b₃) :=
    CFSG.Open.isElemAbelian_of_isElementaryAbelian (h := hA₁)
  have hAX : A₁sub b b₁ b₂ b₃ ≤ Subgroup.normalizer (K : Set G) := fun a ha =>
    Subgroup.mem_normalizer_fintype fun x hx => S56.conj_mem_K (h5.A₁_le_cen_s₀ ha) hx
  have hiSup := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes Nat.prime_three
    hA₁' (by rw [h5.coordA.card]; norm_num) hAX (h5.coprime_K hKF hKC hbig).symm
  rw [← hiSup]
  refine iSup₂_le fun Γ hΓ => ?_
  obtain ⟨hΓA, hΓc⟩ := hΓ
  have hΓ9 : Nat.card Γ = 3 ^ 2 := by rw [h5.coordA.card] at hΓc; omega
  obtain ⟨h, hhH, hhb⟩ := hhyp Γ hΓA ⟨hA₁.of_le hΓA, hΓ9⟩
  have hhs : h ∈ Cen s₀ := Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hhH).1 s₀
      (Subgroup.subset_closure (by simp))).symm
  intro x hx
  obtain ⟨hxK, hxΓ⟩ := Subgroup.mem_inf.mp hx
  have hx'K : h⁻¹ * x * h ∈ K := by
    have := S56.conj_mem_K ((Cen s₀).inv_mem hhs) hxK
    rwa [inv_inv] at this
  have hxb : h * b * h⁻¹ * x = x * (h * b * h⁻¹) := Subgroup.mem_centralizer_iff.mp hxΓ _ hhb
  have hx'b : h⁻¹ * x * h ∈ Cen b := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc h⁻¹ * x * h * b = h⁻¹ * (x * (h * b * h⁻¹)) * h := by group
      _ = h⁻¹ * (h * b * h⁻¹ * x) * h := by rw [hxb]
      _ = b * (h⁻¹ * x * h) := by group
  have hx'S := h5.K_inf_cen_le hKF hKC hbig (Subgroup.mem_inf.mpr ⟨hx'K, hx'b⟩)
  have := op_two_conj hhs hx'S
  rwa [show h * (h⁻¹ * x * h) * h⁻¹ = x by group] at this

end ClaimA

section ClaimB

variable (hKF : KF_Sp6Levi)
  (h5 : FF81Sec5 b L B b₁ b₂ b₃ t₀ s₀) (hbig : h5.Big)
include hKF h5 hbig

theorem FF81Sec5.cen_u₃ :
    Op 2 (Cen s₀) ⊓ Cen (b₂ * b₃) = h5.W 3 ⊔ h5.W 4 ∧ IsElemAb 2 5 (Op 2 (Cen s₀) ⊓ Cen (b₂ * b₃)) := by
  obtain ⟨g, hgH, hg⟩ := h5.gens hKF
  obtain ⟨hc, hs⟩ := S36.coprime_solvable_of_two (op_two_isPGroup s₀)
  obtain ⟨-, c3, c4⟩ := h5.card_W_eight hKF hbig
  have c1 := hbig.cardW1
  have c0 : Nat.card (h5.W 0) = 2 := by
    rw [h5.card_W hgH hg (r := 1) (w := [1]) (by decide), c1]
  have hcu : Nat.card ↥(Op 2 (Cen s₀) ⊓ Cen (b₂ * b₃)) = 32 := by
    have hw := S55.card_cen_mul_pow_three h5.coordA h5.A₁_le_nor_S hc hs (x := ![0, 0, 1])
      (by decide)
    rw [S56.filter_u₃, h5.εA_u₃, h5.card_S_cenS_A₁ hKF] at hw
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.reduceEq, or_self, not_false_eq_true,
      Finset.prod_insert, Finset.prod_singleton] at hw
    change Nat.card ↥(Op 2 (Cen s₀) ⊓ Cen (b₂ * b₃)) * 2 ^ 3 = Nat.card (h5.W 0) *
      (Nat.card (h5.W 1) * (Nat.card (h5.W 3) * Nat.card (h5.W 4))) at hw
    rw [c0, c1, c3, c4] at hw
    omega
  have hWu : ∀ i : Fin 13, dot (hypF i) ![0, 0, 1] = 0 →
      h5.W i ≤ Op 2 (Cen s₀) ⊓ Cen (b₂ * b₃) := fun i hi y hy => by
    have := h5.mem_W_of_dot hi hy
    rwa [h5.εA_u₃] at this
  have hle : h5.W 3 ⊔ h5.W 4 ≤ Op 2 (Cen s₀) ⊓ Cen (b₂ * b₃) :=
    sup_le (hWu 3 (by decide)) (hWu 4 (by decide))
  have hZ3 : h5.W 3 ≤ h5.W 2 ⊔ h5.W 3 ⊔ h5.W 4 := le_sup_right.trans le_sup_left
  have hZ4 : h5.W 4 ≤ h5.W 2 ⊔ h5.W 3 ⊔ h5.W 4 := le_sup_right
  have hZ34 : h5.W 3 ⊔ h5.W 4 ≤ h5.W 2 ⊔ h5.W 3 ⊔ h5.W 4 := sup_le hZ3 hZ4
  have hint : ∀ y ∈ h5.W 3 ⊓ h5.W 4, y = 1 ∨ y = s₀ := by
    intro y hy
    obtain ⟨hy3, hy4⟩ := Subgroup.mem_inf.mp hy
    have hy3' : y ∈ Op 2 (Cen s₀) ⊓ CenS (S55.hyp h5.εA 3) := hy3
    have hyx := h5.mem_W_of_dot (i := 4) (x := ![1, 1, 0]) (by decide) hy4
    refine h5.mem_S_cenS_A₁ hKF (Subgroup.mem_inf.mpr ⟨hy3'.1,
      h5.mem_cenS_A₁_of_hyp (i := 3) (x := ![1, 1, 0]) (by decide) hy3'.2 ?_⟩)
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hyx).2
  have hc34 : Nat.card ↥(h5.W 3 ⊓ h5.W 4) = 2 :=
    card_eq_two_of_le h5.hs₀ (Subgroup.mem_inf.mpr ⟨h5.s₀_mem_W 3, h5.s₀_mem_W 4⟩) hint
  have hsup : Nat.card ↥(h5.W 3 ⊔ h5.W 4) = 32 := by
    have := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute (h5.W 3) (h5.W 4)
      fun x hx y hy => hbig.Zcomm x (hZ3 hx) y (hZ4 hy)).1
    rw [hc34, c3, c4] at this
    omega
  have heq : h5.W 3 ⊔ h5.W 4 = Op 2 (Cen s₀) ⊓ Cen (b₂ * b₃) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcu, hsup])
  refine ⟨heq.symm, ⟨?_, by rw [hcu]; norm_num⟩⟩
  rw [← heq]
  exact CFSG.IsElementaryAbelian.two_of_forall_mul_self
    (fun x hx y hy => hbig.Zcomm x (hZ34 hx) y (hZ34 hy)) fun x hx => hbig.Zsq x (hZ34 hx)

end ClaimB

end CFSG.RankThree.PartTwo.Sec21.FF81
