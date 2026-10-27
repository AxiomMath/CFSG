module

public import CFSG.OddTranspositions.Blocks
public import CFSG.OddTranspositions.HypothesisC
public import CFSG.OddTranspositions.FaithfulBlocks
public import CFSG.OddTranspositions.PartThree.Statements
import CFSG.OddTranspositions.PartThree.EightNine.Tools
public import CFSG.OddTranspositions.SixNineUnconditional
import CFSG.OddTranspositions.SixEight
import CFSG.OddTranspositions.PartThree.Nine.ThreeBlocks
import CFSG.OddTranspositions.PartThree.Ten.DalphaBlocks
import CFSG.OddTranspositions.PartThree.HalphaCentralizer
import CFSG.OddTranspositions.PartFour.LineTransport
import CFSG.Timmesfeld.Bridge.Asc72Minimal
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ CFSG.OddTranspositions.PartFour

variable {G : Type} [Group G] [Finite G] {D : Set G}

theorem exists_conj_alpha_eq_and_d_eq (hC : HypothesisC D) {ρ : Set G}
    (hρ : ρ ∈ blockClass hC.alpha) {r : G} (hr : r ∈ ρ) :
    ∃ g : G, (hC.conj g).alpha = ρ ∧ (hC.conj g).d = r := by
  obtain ⟨g₀, rfl⟩ := mem_blockClass_iff.mp hρ
  have hdρ : g₀ * hC.d * g₀⁻¹ ∈ (fun x => g₀ * x * g₀⁻¹) '' hC.alpha :=
    ⟨hC.d, hC.d_mem_alpha, rfl⟩
  have hdD : g₀ * hC.d * g₀⁻¹ ∈ D := hC.setup.conj_mem g₀ hC.hd
  have hrD : r ∈ D := by
    obtain ⟨a, ha, rfl⟩ := hr
    exact hC.setup.conj_mem g₀ (hC.isBlock_alpha.subset ha)
  obtain ⟨c, hc⟩ := isConj_iff.mp (hC.setup.isConj hdD hrD)
  have hcN : c ∈ Subgroup.normalizer ((fun x => g₀ * x * g₀⁻¹) '' hC.alpha) :=
    Nine.mem_normalizer_block_of_conj_mem hC (mem_blockClass_iff.mpr ⟨g₀, rfl⟩) hdρ (hc ▸ hr)
  refine ⟨c * g₀, ?_, ?_⟩
  · rw [HypothesisC.conj_alpha]
    have hcomp : cimg (c * g₀) hC.alpha = cimg c (cimg g₀ hC.alpha) := by
      unfold cimg
      rw [Set.image_image]
      congr 1
      funext y
      group
    rw [hcomp]
    exact Nine.conj_image_block_eq hcN
  · rw [HypothesisC.conj_d]
    calc (c * g₀) * hC.d * (c * g₀)⁻¹ = c * (g₀ * hC.d * g₀⁻¹) * c⁻¹ := by group
      _ = r := hc

theorem eq_one_of_commute_DalphaStar_of_perp (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha) {t : G}
    (ht : ∀ y ∈ DalphaStar D β, Commute t y)
    (hperp : ∀ γ ∈ perp D hC.alpha, (fun y => t * y * t⁻¹) '' γ = γ) : t = 1 :=
  hF t (actsTriviallyOnBlocks_of_perp_of_theorem8_7 h87 hC hrad hO4 hβ ht
    (hperp β (mem_perp_iff.mpr (Or.inl hβ))) hperp)

theorem commute_DalphaStar_of_conj_image_eq (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha) {k : G} (hk : k ∈ Halpha D hC.alpha)
    (hfix : ∀ β ∈ Dalpha D hC.alpha, (fun y => k * y * k⁻¹) '' β = β) :
    ∀ b ∈ DalphaStar D hC.alpha, Commute k b := by
  intro b hb
  obtain ⟨β, hβ, hbβ⟩ := hb
  let t : G := b * (k * b * k⁻¹)
  have hbStar : b ∈ DalphaStar D hC.alpha := ⟨β, hβ, hbβ⟩
  have hbH : b ∈ Halpha D hC.alpha := Subgroup.subset_closure hbStar
  have hb2 : b * b = 1 := hC.setup.oddT.mul_self_eq_one (hβ.2.1 hbβ)
  have hbβ' : k * b * k⁻¹ ∈ β := by
    rw [← hfix β hβ]
    exact ⟨b, hbβ, rfl⟩
  have hb'H : k * b * k⁻¹ ∈ Halpha D hC.alpha :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hbH) (Subgroup.inv_mem _ hk)
  have htH : t ∈ Halpha D hC.alpha := Subgroup.mul_mem _ hbH hb'H
  have htStar : ∀ y ∈ DalphaStar D β, Commute t y := by
    intro y hy
    obtain ⟨γ, hγ, hyγ⟩ := hy
    have hβγ := (mem_Dalpha_iff.mp hγ).2.2.2
    exact (hβγ b hbβ y hyγ).mul_left (hβγ (k * b * k⁻¹) hbβ' y hyγ)
  have htperp : ∀ γ ∈ perp D hC.alpha, (fun y => t * y * t⁻¹) '' γ = γ := by
    intro γ hγ
    rcases mem_perp_iff.mp hγ with hγD | rfl
    · have hbγ : cimg b γ ∈ Dalpha D hC.alpha :=
        smul_mem_Dalpha_of_mem_Halpha hC hbH hγD
      have hkγ : cimg k γ = γ := hfix γ hγD
      have hkδ : cimg k (cimg b γ) = cimg b γ := hfix _ hbγ
      have hkγ' : cimg k⁻¹ γ = γ := by
        calc cimg k⁻¹ γ = cimg k⁻¹ (cimg k γ) := by rw [hkγ]
          _ = γ := cimg_inv_cimg k γ
      have hbk : cimg (k * b * k⁻¹) γ = cimg b γ := by
        rw [cimg_mul, cimg_mul, hkγ', hkδ]
      change cimg t γ = γ
      calc cimg t γ = cimg b (cimg (k * b * k⁻¹) γ) := cimg_mul b (k * b * k⁻¹) γ
        _ = cimg b (cimg b γ) := by rw [hbk]
        _ = cimg (b * b) γ := (cimg_mul b b γ).symm
        _ = cimg 1 γ := by rw [hb2]
        _ = γ := cimg_one γ
    · have hcent := Halpha_le_centralizer D hC.alpha htH
      have hpt : ∀ y ∈ hC.alpha, t * y * t⁻¹ = y := by
        intro y hy
        have hyt : y * t = t * y := Subgroup.mem_centralizer_iff.mp hcent y hy
        rw [← hyt]
        group
      change cimg t hC.alpha = hC.alpha
      calc cimg t hC.alpha = (fun y => y) '' hC.alpha := Set.image_congr hpt
        _ = hC.alpha := Set.image_id' hC.alpha
  have ht1 : t = 1 :=
    eq_one_of_commute_DalphaStar_of_perp h87 hC hrad hO4 hF hβ htStar htperp
  have hkb : k * b * k⁻¹ = b := by
    have hc : k * b * k⁻¹ = b⁻¹ := eq_inv_of_mul_eq_one_right (by simpa [t] using ht1)
    rwa [inv_eq_of_mul_eq_one_right hb2] at hc
  have hcomm : Commute k b := by
    show k * b = b * k
    calc k * b = k * b * k⁻¹ * k := by group
      _ = b * k := by rw [hkb]
  exact hcomm

theorem forall_conj_image_eq_iff_commute (h87 : Theorem8_7) (hC : HypothesisC D)
    (hrad : ∀ N : Subgroup G, N.Normal → Group.IsSolvable N → N = ⊥) (hO4 : ¬ O4PairData G D)
    (hF : FaithfulOnBlocks hC.alpha) {k : G} (hk : k ∈ Halpha D hC.alpha) :
    (∀ β ∈ Dalpha D hC.alpha, (fun y => k * y * k⁻¹) '' β = β) ↔
      ∀ h ∈ Halpha D hC.alpha, Commute k h := by
  constructor
  · intro hfix
    have hcommStar := commute_DalphaStar_of_conj_image_eq h87 hC hrad hO4 hF hk hfix
    have hle : Halpha D hC.alpha ≤ Subgroup.centralizer ({k} : Set G) := by
      rw [Halpha, Subgroup.closure_le]
      intro b hb
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcommStar b hb).symm.eq
    intro h hh
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hh)).symm
  · intro hcomm β hβ
    have hpt : ∀ y ∈ β, k * y * k⁻¹ = y := fun y hy => by
      rw [(hcomm y (Subgroup.subset_closure (subset_DalphaStar hβ hy))).eq, mul_inv_cancel_right]
    calc (fun y => k * y * k⁻¹) '' β = (fun y => y) '' β := Set.image_congr hpt
      _ = β := Set.image_id' β

omit [Finite G] in
theorem closure_inter_normalizer_ne_top (hC : HypothesisC D) (hZ : Subgroup.center G = ⊥)
    {r : G} (hrD : r ∈ D) {K : Subgroup G} (hK : K ≠ ⊥)
    (hKr : ∀ k ∈ K, Commute k r) :
    Subgroup.closure ((D : Set G) ∩ (Subgroup.normalizer (K : Set G) : Set G)) ≠ ⊤ := by
  intro htop
  have hNtop : Subgroup.normalizer (K : Set G) = ⊤ := by
    rw [eq_top_iff]
    calc (⊤ : Subgroup G) = Subgroup.closure ((D : Set G) ∩
          (Subgroup.normalizer (K : Set G) : Set G)) := htop.symm
      _ ≤ Subgroup.normalizer (K : Set G) := by
          rw [Subgroup.closure_le]
          exact Set.inter_subset_right
  have hKnormal : K.Normal := Subgroup.normalizer_eq_top_iff.mp hNtop
  have hKcenter : K ≤ Subgroup.center G :=
    hC.setup.le_center_of_mem_centralizer hrD
      (Subgroup.mem_centralizer_iff.mpr fun k hk => (hKr k hk).eq)
  rw [hZ] at hKcenter
  exact hK (le_bot_iff.mp hKcenter)

theorem inter_normalizer_subset_perp (hC : HypothesisC D) (hZ : Subgroup.center G = ⊥)
    {ρ : Set G} (hρ : ρ ∈ blockClass hC.alpha) {r : G} (hr : r ∈ ρ) {K : Subgroup G}
    (hK : K ≠ ⊥) (hKr : ∀ k ∈ K, Commute k r)
    (hHK : Halpha D ρ ≤ Subgroup.normalizer (K : Set G)) :
    D ∩ (Subgroup.normalizer (K : Set G) : Set G) ⊆ ρ ∪ DalphaStar D ρ := by
  obtain ⟨g, hgα, hgd⟩ := exists_conj_alpha_eq_and_d_eq hC hρ hr
  let hC' : HypothesisC D := hC.conj g
  have hC'α : hC'.alpha = ρ := hgα
  have hC'd : hC'.d = r := hgd
  have hρblock : IsBlock D ρ := isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hρ
  have hrD : r ∈ D := hρblock.subset hr
  have hrN : r ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.centralizer_le_normalizer (K : Set G)
      (Subgroup.mem_centralizer_iff.mpr fun k hk => (hKr k hk).eq)
  set X : Subgroup G :=
    Subgroup.closure ((D : Set G) ∩ (Subgroup.normalizer (K : Set G) : Set G)) with hXdef
  have hXN : X ≤ Subgroup.normalizer (K : Set G) := by
    rw [hXdef, Subgroup.closure_le]
    exact Set.inter_subset_right
  have hXD : X = Subgroup.closure ((X : Set G) ∩ D) := by
    apply le_antisymm
    · rw [hXdef, Subgroup.closure_le]
      intro x hx
      exact Subgroup.subset_closure ⟨Subgroup.subset_closure hx, hx.1⟩
    · rw [Subgroup.closure_le]
      exact Set.inter_subset_left
  have hdX : hC'.d ∈ X := by
    rw [hC'd]
    exact Subgroup.subset_closure ⟨hrD, hrN⟩
  have hEX : hC'.E ⊆ (X : Set G) := by
    rw [← hC'.DalphaStar_alpha, hC'α]
    intro x hx
    refine Subgroup.subset_closure ⟨DalphaStar_subset hρblock hx, hHK ?_⟩
    exact Subgroup.subset_closure hx
  have hproper : X ≠ ⊤ := by
    rw [hXdef]
    exact closure_inter_normalizer_ne_top hC hZ hrD hK hKr
  have hmain := inter_D_subset_perp hC' hXD hdX hEX hproper
  rw [hC'α] at hmain
  intro x hx
  exact hmain ⟨Subgroup.subset_closure hx, hx.1⟩

theorem commute_subset_perp_of_commute_Halpha (hC : HypothesisC D)
    (hZ : Subgroup.center G = ⊥) {ρ : Set G} (hρ : ρ ∈ blockClass hC.alpha) {r t : G}
    (hr : r ∈ ρ) (ht : t ≠ 1) (htr : Commute t r) (htH : ∀ h ∈ Halpha D ρ, Commute t h) :
    {x | x ∈ D ∧ Commute x t} ⊆ ρ ∪ DalphaStar D ρ := by
  let K : Subgroup G := Subgroup.zpowers t
  have hK : K ≠ ⊥ := by
    intro hbot
    apply ht
    have hmem : t ∈ K := Subgroup.mem_zpowers t
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hKr : ∀ k ∈ K, Commute k r := by
    intro k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact htr.zpow_left n
  have hHK : Halpha D ρ ≤ Subgroup.normalizer (K : Set G) := by
    have hle : Halpha D ρ ≤ Subgroup.centralizer (K : Set G) := by
      rw [Halpha, Subgroup.closure_le]
      intro h hh
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro k hk
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
      exact ((htH h (Subgroup.subset_closure hh)).zpow_left n).eq
    exact hle.trans (Subgroup.centralizer_le_normalizer (K : Set G))
  intro x hx
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := by
    apply Subgroup.centralizer_le_normalizer (K : Set G)
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro k hk
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
    exact (hx.2.zpow_right n).symm.eq
  exact inter_normalizer_subset_perp hC hZ hρ hr hK hKr hHK ⟨hx.1, hxN⟩

end CFSG.OddTranspositions.PartThree.EightEight
