module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7CoreLift
public import CFSG.LocalAnalysis.StandardType.FS81.BasisCoprimeCore
public import CFSG.LocalAnalysis.StandardType.FS81.TransferTwD7

public noncomputable section

namespace CFSG.StandardType.FrameRoute.FS81

open Subgroup CFSG.Blueprint.Chevalley


theorem exists_attached_e7_of_std_twD7_projection
    {G : Type} [Group G] [Finite G] (b₀ : G) (K E : Subgroup G)
    (hstd : StdAssumptions b₀ K E Row.twD7) (B : Basis3 G 8)
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀)
    (H : Subgroup G) (hEH : E ≤ H)
    (hCH : centralizer ({B.b 1} : Set G) ⊓ K ≤ H)
    (hHβ : H ≤ centralizer ({b₀ * B.b 1} : Set G))
    (hHH₀ : H ≤ centralizer ({b₀} : Set G) ⊔ normalizer (E : Set G))
    (π : H →* adjointGroup .E7 (ZMod 2)) (hπ : Function.Surjective π)
    (hker : ∃ R₁ : Subgroup G, R₁ ≤ centralizer ({b₀} : Set G) ∧
      (R₁.subgroupOf (centralizer ({b₀} : Set G))).Normal ∧ ¬ 3 ∣ Nat.card R₁ ∧
      π.ker ≤ R₁.subgroupOf H ⊔ (zpowers (b₀ * B.b 1)).subgroupOf H)
    (τ : H) (hτ0 : (τ : G) * B.b 0 * (τ : G)⁻¹ = B.b 1) :
    ∃ J : Subgroup G, J ≤ H ∧
      J ≤ centralizer ({b₀} : Set G) ⊔ normalizer (E : Set G) ∧
      J ≤ centralizer ({b₀ * B.b 1} : Set G) ∧
      Nonempty (J ≃* adjointGroup .E7 (ZMod 2)) ∧
      Adapted B.twD7Beta (b₀ * B.b 1) J E ∧
      ⁅centralizer ({B.b 1} : Set G) ⊓ K, centralizer ({B.b 1} : Set G) ⊓ K⁆ ≤ J ∧
      (∀ R₁ : Subgroup G, R₁ ≤ centralizer ({b₀} : Set G) →
        (R₁.subgroupOf (centralizer ({b₀} : Set G))).Normal → ¬ 3 ∣ Nat.card R₁ →
        R₁ ≤ centralizer (J : Set G)) ∧
      normalizer (H : Set G) ⊓ normalizer (E : Set G) ≤ normalizer (J : Set G) ∧
      IsSimpleGroup J ∧
      ∃ η : J ≃* adjointGroup .E7 (ZMod 2),
        ∀ j : J, ∀ hj : (j : G) ∈ H, η j = π ⟨(j : G), hj⟩ := by
  obtain ⟨R₀, hR₀C, hR₀n, hR₀3, -, hR₀E, hNER₀, hRR₀, hXR₀⟩ :=
    exists_threePrime_core_twD7 hstd hB hrec
  have hCR₀ : centralizer ({b₀} : Set G) ≤ normalizer (R₀ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hR₀C).mp hR₀n
  have hHR₀ : H ≤ normalizer (R₀ : Set G) := hHH₀.trans (sup_le hCR₀ hNER₀)
  let R : Subgroup H := R₀.subgroupOf H
  let : R.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHR₀
  have hRmap : R.map H.subtype ≤ R₀ := by
    rw [Subgroup.subgroupOf_map_subtype]
    exact inf_le_left
  have hRE : R.map H.subtype ≤ centralizer (E : Set G) := hRmap.trans hR₀E
  obtain ⟨-, hHyp, hCanon⟩ := id hstd
  obtain ⟨hA, -, -, -, -, -⟩ := hHyp
  obtain ⟨-, hKC, -, hKz, -, -, -, -⟩ := hA
  obtain ⟨hKs, -⟩ := isSimpleGroup_and_mulEquiv_of_isRow_twD7 hCanon.1 hKz
  have hb₁E : B.b 1 ∈ E := hB.1 ▸ B.b_mem_span 1
  have hb₁1 : B.b 1 ≠ 1 := by
    intro he
    have ho := B.ord 1
    rw [he, orderOf_one] at ho
    norm_num at ho
  have hR₀K : R₀ ≤ centralizer (K : Set G) :=
    hXR₀ K hKs (hKC.trans le_sup_left)
      ⟨B.b 1, hB.2.2 1 (by decide), hb₁E, hb₁1⟩
  have hRK : R.map H.subtype ≤ centralizer (K : Set G) := hRmap.trans hR₀K
  have hkerR : π.ker ≤ R ⊔ (zpowers (b₀ * B.b 1)).subgroupOf H := by
    obtain ⟨R₁, hR₁C, hR₁n, hR₁3, hker₁⟩ := hker
    have hR₁R₀ : R₁ ≤ R₀ := hRR₀ R₁ hR₁C hR₁n hR₁3
    exact hker₁.trans (sup_le_sup (fun r hr => hR₁R₀ hr) le_rfl)
  let B' := B.twD7Beta
  have hB'E : B'.span = E := B.twD7Beta_span.trans hB.1
  have haE : B'.b 1 ∈ E := hB'E ▸ B'.b_mem_span 1
  let a : H := ⟨B'.b 1, hEH haE⟩
  have haC : a ∈ centralizer (R : Set H) := by
    rw [mem_centralizer_iff]
    intro r hr
    apply Subtype.ext
    have hr₀ : (r : G) ∈ R₀ := hRmap (Subgroup.mem_map_of_mem _ hr)
    exact (mem_centralizer_iff.mp (hR₀E hr₀) (B'.b 1) haE).symm
  have hβH : zpowers (b₀ * B.b 1) ≤ H := by
    refine zpowers_le.mpr (hEH (E.mul_mem ?_ hb₁E))
    exact hstd.2.1.2.2.1
  have haπ : π a ≠ 1 := by
    intro h1
    have hcap : a ∈ R ⊔ (zpowers (b₀ * B.b 1)).subgroupOf H :=
      hkerR (MonoidHom.mem_ker.mpr h1)
    have hmap : (R ⊔ (zpowers (b₀ * B.b 1)).subgroupOf H).map H.subtype ≤
        R₀ ⊔ zpowers (b₀ * B.b 1) := by
      rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hβH]
      exact sup_le (hRmap.trans le_sup_left) le_sup_right
    have hR₀B' : R₀ ≤ centralizer (B'.span : Set G) := by rw [hB'E]; exact hR₀E
    have hno := B'.not_mem_sup_zpowers_of_not_dvd_card R₀ hR₀3 hR₀B'
      (i := 1) (j := 0) (by decide)
    have hβ0 : B'.b 0 = b₀ * B.b 1 := by
      simp only [B', B.twD7Beta_b_zero, hB.2.1]
    rw [hβ0] at hno
    exact hno (hmap (Subgroup.mem_map_of_mem _ hcap))
  obtain ⟨J, hJH, ⟨eJ⟩, hB', hMJ, hJderived, hGraph⟩ :=
    exists_attached_e7_of_core_quotient b₀ K E hstd B hB hrec H hEH hCH hHβ
      R hRE hRK π hπ hkerR a haC haπ τ hτ0
  let S := adjointGroup .E7 (ZMod 2)
  have hSQ := CFSG.LieType.Simplicity.isQuasisimple_adjointGroup_e7 (ZMod 2)
  have hZS : center S = ⊥ := CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let eS : S ⧸ center S ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hZS).trans QuotientGroup.quotientBot
  let : IsSimpleGroup (S ⧸ center S) := hSQ.2.1
  let : IsSimpleGroup S := eS.symm.isSimpleGroup
  have hJs : IsSimpleGroup J := eJ.isSimpleGroup
  have hβ₁J : B'.b 1 ∈ J := hB'.2.2 1 (by decide)
  have hβ₁1 : B'.b 1 ≠ 1 := by
    intro he
    have ho := B'.ord 1
    rw [he, orderOf_one] at ho
    norm_num at ho
  have hR₀J : R₀ ≤ centralizer (J : Set G) :=
    hXR₀ J hJs (hJH.trans hHH₀) ⟨B'.b 1, hβ₁J, haE, hβ₁1⟩
  have hNJ : normalizer (H : Set G) ⊓ normalizer (E : Set G) ≤
      normalizer (J : Set G) := by
    intro g hg
    have hRg : g ∈ normalizer (R.map H.subtype : Set G) := by
      change g ∈ normalizer ((R₀.subgroupOf H).map H.subtype : Set G)
      rw [Subgroup.subgroupOf_map_subtype]
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hNER₀ hg.2, hg.1⟩
    have hCnorm : normalizer (R.map H.subtype : Set G) ≤
        normalizer (centralizer (R.map H.subtype : Set G) : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _)
    have hgC : g ∈ normalizer ((H ⊓ centralizer (R.map H.subtype : Set G) :
        Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hg.1, hCnorm hRg⟩
    rw [hJderived, Subgroup.mem_normalizer_iff_map_conj_eq,
      Subgroup.map_commutator, Subgroup.mem_normalizer_iff_map_conj_eq.mp hgC]
  exact ⟨J, hJH, hJH.trans hHH₀, hJH.trans hHβ, ⟨eJ⟩, hB', hMJ,
    (fun R₁ hR₁C hR₁n hR₁3 => (hRR₀ R₁ hR₁C hR₁n hR₁3).trans hR₀J), hNJ, hJs, hGraph⟩

end CFSG.StandardType.FrameRoute.FS81
