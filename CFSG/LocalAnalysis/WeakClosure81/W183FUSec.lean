module

public import CFSG.LocalAnalysis.WeakClosure81.W183FUBorel
public import CFSG.LocalAnalysis.WeakClosure81.W183Cited
import CFSG.LocalAnalysis.WeakClosure81.W183Br1Comp2
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
import CFSG.Holt.PointHullTwoGroupBasic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsU3)

variable {G : Type} [Group G] [Finite G]

private theorem w183fu_inf_eq_bot_of_commute {Y : Type} [Group Y] {A₁ A₂ : Subgroup Y}
    [IsSimpleGroup ↥A₁] (hnab : ∃ a b : ↥A₁, a * b ≠ b * a)
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) : A₁ ⊓ A₂ = ⊥ := by
  let N : Subgroup ↥A₁ := (A₁ ⊓ A₂).subgroupOf A₁
  have hNnormal : N.Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
    refine ⟨?_, ?_⟩
    · exact A₁.mul_mem (A₁.mul_mem g.2 hn.1) (A₁.inv_mem g.2)
    · have hgn : (g : Y) * (n : Y) = (n : Y) * (g : Y) := hcomm g g.2 n hn.2
      have he : ((g * n * g⁻¹ : ↥A₁) : Y) = (n : Y) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hgn]; group
      rw [he]; exact hn.2⟩
  haveI := hNnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxN : (⟨x, hx.1⟩ : ↥A₁) ∈ N := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]; exact hx
    rw [hbot, Subgroup.mem_bot] at hxN
    exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hxN)
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have haN : a ∈ N := by rw [htop]; trivial
    have hbN : b ∈ N := by rw [htop]; trivial
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at haN hbN
    exact hab (Subtype.ext (hcomm (a : Y) a.2 (b : Y) hbN.2))

private theorem w183fu_isU3_image_quotient {K H L : Subgroup G}
    (hKn : (K.subgroupOf H).Normal) (hLH : L ≤ H)
    (hQ : HasQuotShape L (K : Set G) (fun X _ => IsU3 X 2)) :
    IsU3 ↥((L.subgroupOf H).map (QuotientGroup.mk' (K.subgroupOf H))) 2 := by
  classical
  haveI := hKn
  obtain ⟨X, hX, φ, hφs, hφk, hXU⟩ := hQ
  letI : Group X := hX
  let q := QuotientGroup.mk' (K.subgroupOf H)
  let A : Subgroup (↥H ⧸ (K.subgroupOf H)) := (L.subgroupOf H).map q
  let eL : ↥(L.subgroupOf H) ≃* ↥L := Subgroup.subgroupOfEquivOfLe hLH
  let φ' : ↥(L.subgroupOf H) →* X := φ.comp eL.toMonoidHom
  have hφ's : Function.Surjective φ' := hφs.comp eL.surjective
  let ψ : ↥(L.subgroupOf H) →* A := q.subgroupMap (L.subgroupOf H)
  have hψs : Function.Surjective ψ := q.subgroupMap_surjective (L.subgroupOf H)
  have hker : φ'.ker = ψ.ker := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    have h1 : φ' k = 1 ↔ (k : G) ∈ K := by
      show φ (eL k) = 1 ↔ (k : G) ∈ K
      rw [hφk (eL k)]
      rfl
    have h2 : ψ k = 1 ↔ (k : G) ∈ K := by
      constructor
      · intro hk
        have hq1 : q k = 1 := congrArg Subtype.val hk
        rw [show q = QuotientGroup.mk' (K.subgroupOf H) from rfl, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hq1
        exact hq1
      · intro hk
        apply Subtype.ext
        show q k = 1
        rw [show q = QuotientGroup.mk' (K.subgroupOf H) from rfl, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hk
    exact h1.trans h2.symm
  let e : X ≃* A :=
    (QuotientGroup.quotientKerEquivOfSurjective φ' hφ's).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψs))
  exact CFSG.Blueprint.LieModel.of_mulEquiv e hXU

theorem w183fu_prod_layer_rank {S : Type} [Group S] [Finite S] {A₁ A₂ : Subgroup S}
    (h₁ : IsU3 ↥A₁ 2) (h₂ : IsU3 ↥A₂ 2) (hn₁ : A₁.Normal) (hn₂ : A₂.Normal)
    (hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a) (hgen : A₁ ⊔ A₂ = ⊤) :
    CFSG.layer S = ⊤ ∧ 4 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup S) := by
  haveI hsimple₁ : IsSimpleGroup ↥A₁ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_PSU3 h₁
  haveI hsimple₂ : IsSimpleGroup ↥A₂ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_PSU3 h₂
  have hnab₁ : ∃ a b : ↥A₁, a * b ≠ b * a :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_PSU3 h₁
  have hnab₂ : ∃ a b : ↥A₂, a * b ≠ b * a :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_PSU3 h₂
  have hinf : A₁ ⊓ A₂ = ⊥ := w183fu_inf_eq_bot_of_commute hnab₁ hcomm
  have hcomp₁ : CFSG.IsComponent A₁ :=
    CFSG.Quasithin.A3.isComponentOf_top_iff.mp
      ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib hn₁.isSubnormal,
        CFSG.Holt.PointHull.isQuasisimple_of_isSimpleGroup hnab₁⟩
  have hcomp₂ : CFSG.IsComponent A₂ :=
    CFSG.Quasithin.A3.isComponentOf_top_iff.mp
      ⟨le_top, CFSG.Open.IsSubnormal.of_mathlib hn₂.isSubnormal,
        CFSG.Holt.PointHull.isQuasisimple_of_isSimpleGroup hnab₂⟩
  have hle₁ : A₁ ≤ CFSG.layer S := by
    rw [CFSG.layer.eq_sSup S]
    exact le_sSup hcomp₁
  have hle₂ : A₂ ≤ CFSG.layer S := by
    rw [CFSG.layer.eq_sSup S]
    exact le_sSup hcomp₂
  have hlayer : CFSG.layer S = ⊤ :=
    le_antisymm le_top (by rw [← hgen]; exact sup_le hle₁ hle₂)
  have hrank₁ : 2 ≤ CFSG.Open.pRank 5 A₁ := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup A₁]
    exact w183fu_two_le_pRank_five h₁
  have hrank₂ : 2 ≤ CFSG.Open.pRank 5 A₂ := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup A₂]
    exact w183fu_two_le_pRank_five h₂
  obtain ⟨E₁, hE₁A₁, hE₁, hcard₁⟩ :=
    CFSG.SectionRank.exists_pRank (p := 5) (H := A₁) (by norm_num)
  obtain ⟨E₂, hE₂A₂, hE₂, hcard₂⟩ :=
    CFSG.SectionRank.exists_pRank (p := 5) (H := A₂) (by norm_num)
  have hcommE : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a :=
    fun a ha b hb => hcomm a (hE₁A₁ ha) b (hE₂A₂ hb)
  let f : (↥E₁) × (↥E₂) →* S :=
    { toFun := fun x => (x.1 : S) * (x.2 : S)
      map_one' := by simp
      map_mul' := by
        intro x y
        have hc : (y.1 : S) * (x.2 : S) = (x.2 : S) * (y.1 : S) :=
          hcommE (y.1 : S) y.1.2 (x.2 : S) x.2.2
        calc ((x.1 : S) * (y.1 : S)) * ((x.2 : S) * (y.2 : S))
            = (x.1 : S) * ((y.1 : S) * (x.2 : S)) * (y.2 : S) := by group
          _ = (x.1 : S) * ((x.2 : S) * (y.1 : S)) * (y.2 : S) := by rw [hc]
          _ = ((x.1 : S) * (x.2 : S)) * ((y.1 : S) * (y.2 : S)) := by group }
  have hf : Function.Injective f := by
    intro x y hxy
    have hxyeq : (x.1 : S) * (x.2 : S) = (y.1 : S) * (y.2 : S) := hxy
    have h : (y.1 : S)⁻¹ * (x.1 : S) = (y.2 : S) * (x.2 : S)⁻¹ := by
      calc (y.1 : S)⁻¹ * (x.1 : S)
          = (y.1 : S)⁻¹ * ((x.1 : S) * (x.2 : S)) * (x.2 : S)⁻¹ := by group
        _ = (y.1 : S)⁻¹ * ((y.1 : S) * (y.2 : S)) * (x.2 : S)⁻¹ := by rw [hxyeq]
        _ = (y.2 : S) * (x.2 : S)⁻¹ := by group
    have hmem : (y.1 : S)⁻¹ * (x.1 : S) ∈ A₁ ⊓ A₂ := by
      refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
      · exact A₁.mul_mem (A₁.inv_mem (hE₁A₁ y.1.2)) (hE₁A₁ x.1.2)
      · rw [h]
        exact A₂.mul_mem (hE₂A₂ y.2.2) (A₂.inv_mem (hE₂A₂ x.2.2))
    rw [hinf, Subgroup.mem_bot] at hmem
    have hyx : (y.1 : S) = (x.1 : S) := inv_mul_eq_one.mp hmem
    have hx₁ : x.1 = y.1 := Subtype.ext hyx.symm
    have hx₂ : x.2 = y.2 := by
      apply Subtype.ext
      have h2 : (y.2 : S) * (x.2 : S)⁻¹ = 1 := by
        rw [← h]
        exact hmem
      exact (mul_inv_eq_one.mp h2).symm
    exact Prod.ext hx₁ hx₂
  have hcard : Nat.card ((↥E₁) × (↥E₂)) =
      5 ^ (CFSG.Open.pRank 5 A₁ + CFSG.Open.pRank 5 A₂) := by
    rw [Nat.card_prod, hcard₁, hcard₂, ← pow_add]
  have hcomm' : ∀ a b : (↥E₁) × (↥E₂), a * b = b * a := by
    intro a b
    apply Prod.ext
    · exact hE₁.1.is_comm.comm a.1 b.1
    · exact hE₂.1.is_comm.comm a.2 b.2
  have hpow' : ∀ a : (↥E₁) × (↥E₂), a ^ 5 = 1 := by
    intro a
    apply Prod.ext
    · exact Subtype.ext (by simpa using hE₁.2 (a.1 : S) a.1.2)
    · exact Subtype.ext (by simpa using hE₂.2 (a.2 : S) a.2.2)
  have hle : CFSG.Open.pRank 5 A₁ + CFSG.Open.pRank 5 A₂ ≤
      CFSG.Open.pRank 5 (⊤ : Subgroup S) :=
    CFSG.SectionRank.le_pRank_of_injective (p := 5) (A := (↥E₁) × (↥E₂)) (H := ⊤)
      (by norm_num) hcomm' hpow' hcard f hf le_top
  exact ⟨hlayer, by omega⟩

theorem w183fu_normal_subgroupOf {K H M : Subgroup G} (hK : (K.subgroupOf H).Normal)
    (hKM : K ≤ M) (hMH : M ≤ H) : (K.subgroupOf M).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKM]
  exact hMH.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (hKM.trans hMH)).mp hK)

theorem w183fu_section {K L₁ L₂ H : Subgroup G} (h₁ : IsComponentModN K H L₁)
    (h₂ : IsComponentModN K H L₂) (hne : L₁ ≠ L₂)
    (hQ₁ : HasQuotShape L₁ (K : Set G) (fun X _ => IsU3 X 2))
    (hQ₂ : HasQuotShape L₂ (K : Set G) (fun X _ => IsU3 X 2))
    [hN : (K.subgroupOf (L₁ ⊔ L₂)).Normal] :
    CFSG.layer (↥(L₁ ⊔ L₂) ⧸ K.subgroupOf (L₁ ⊔ L₂)) = ⊤ ∧
      4 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (↥(L₁ ⊔ L₂) ⧸ K.subgroupOf (L₁ ⊔ L₂))) := by
  classical
  have hL₁M : L₁ ≤ L₁ ⊔ L₂ := le_sup_left
  have hL₂M : L₂ ≤ L₁ ⊔ L₂ := le_sup_right
  let q : ↥(L₁ ⊔ L₂) →* (↥(L₁ ⊔ L₂) ⧸ K.subgroupOf (L₁ ⊔ L₂)) :=
    QuotientGroup.mk' (K.subgroupOf (L₁ ⊔ L₂))
  let A₁ : Subgroup (↥(L₁ ⊔ L₂) ⧸ K.subgroupOf (L₁ ⊔ L₂)) :=
    (L₁.subgroupOf (L₁ ⊔ L₂)).map q
  let A₂ : Subgroup (↥(L₁ ⊔ L₂) ⧸ K.subgroupOf (L₁ ⊔ L₂)) :=
    (L₂.subgroupOf (L₁ ⊔ L₂)).map q
  have hU₁ : IsU3 ↥A₁ 2 := w183fu_isU3_image_quotient hN hL₁M hQ₁
  have hU₂ : IsU3 ↥A₂ 2 := w183fu_isU3_image_quotient hN hL₂M hQ₂
  have hgen : A₁ ⊔ A₂ = ⊤ := by
    have hsup : (L₁.subgroupOf (L₁ ⊔ L₂)) ⊔ (L₂.subgroupOf (L₁ ⊔ L₂)) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup hL₁M hL₂M, Subgroup.subgroupOf_self]
    rw [← Subgroup.map_sup, hsup,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective (K.subgroupOf (L₁ ⊔ L₂)))]
  have hcomm : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.1 hb
    have ha'L : (a' : G) ∈ L₁ := Subgroup.mem_subgroupOf.mp ha'
    have hb'L : (b' : G) ∈ L₂ := Subgroup.mem_subgroupOf.mp hb'
    have hmemK : ((a' * b' * a'⁻¹ * b'⁻¹ : ↥(L₁ ⊔ L₂)) : G) ∈ K := by
      simpa using w183_components_commute h₁ h₂ hne (a' : G) ha'L (b' : G) hb'L
    have hq1 : q (a' * b' * a'⁻¹ * b'⁻¹) = 1 := by
      rw [show q = QuotientGroup.mk' (K.subgroupOf (L₁ ⊔ L₂)) from rfl,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr hmemK
    rw [← commutatorElement_eq_one_iff_mul_comm, commutatorElement_def]
    simpa only [map_mul, map_inv] using hq1
  have hAn₁ : A₁.Normal := by
    have hcent : A₂ ≤ Subgroup.centralizer (A₁ : Set _) := by
      intro b hb
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact hcomm a ha b hb
    have hle : A₁ ⊔ A₂ ≤ Subgroup.normalizer (A₁ : Set _) :=
      sup_le Subgroup.le_normalizer (hcent.trans (Subgroup.centralizer_le_normalizer _))
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (hgen ▸ hle))
  have hAn₂ : A₂.Normal := by
    have hcent : A₁ ≤ Subgroup.centralizer (A₂ : Set _) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hcomm a ha b hb).symm
    have hle : A₁ ⊔ A₂ ≤ Subgroup.normalizer (A₂ : Set _) :=
      sup_le (hcent.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
    exact Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp (hgen ▸ hle))
  exact w183fu_prod_layer_rank hU₁ hU₂ hAn₁ hAn₂ hcomm hgen

theorem w183fu_pRank_five_gt (h22 : Asch2_2One) {K L₁ L₂ H : Subgroup G}
    (hH : CFSG.Open.IsKGroup ↥H) (h₁ : IsComponentModN K H L₁) (h₂ : IsComponentModN K H L₂)
    (hne : L₁ ≠ L₂) (hQ₁ : HasQuotShape L₁ (K : Set G) (fun X _ => IsU3 X 2))
    (hQ₂ : HasQuotShape L₂ (K : Set G) (fun X _ => IsU3 X 2)) :
    3 < CFSG.Open.pRank 5 H := by
  by_contra hle
  have hKM : K ≤ L₁ ⊔ L₂ := h₁.2.1.trans le_sup_left
  have hMH : L₁ ⊔ L₂ ≤ H := sup_le h₁.2.2.1 h₂.2.2.1
  haveI hN : (K.subgroupOf (L₁ ⊔ L₂)).Normal := w183fu_normal_subgroupOf h₁.1 hKM hMH
  obtain ⟨hlayer, hrank⟩ := w183fu_section h₁ h₂ hne hQ₁ hQ₂
  have h3 := h22 G H 5 Nat.prime_five (by norm_num) hH (not_lt.mp hle) (L₁ ⊔ L₂) K hKM hMH
    hlayer
  omega

end CFSG.LocalAnalysis.WeakClosure81

end
