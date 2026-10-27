module

public import CFSG.LocalAnalysis.StandardType.FS81.TwD7QSplit
public import CFSG.LocalAnalysis.StandardType.FS81.D6RootFusion
public import CFSG.LocalAnalysis.StandardType.FS81.D6Frame
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameMatch
public import CFSG.LocalAnalysis.StandardType.FS81.E7FrameNativeRoots
public import CFSG.Mathlib.GroupTheory.ProjOfCommute

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.FrameRoute.FS81

open Subgroup TwD7Q CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open E7Frame


theorem exists_twD7BetaHost_projection_of_quot {G : Type} [Group G] [Finite G] {b₀ : G}
    {K E : Subgroup G} (hstd : StdAssumptions b₀ K E Row.twD7) {B : Basis3 G 8}
    (hB : Adapted B b₀ K E) (hrec : RecOutTwD7 B b₀)
    (hQstd : StdLoc (B.twD7Quot.b 0) (img (B.b 0 * B.b 1) (twD7M0 K B)) B.twD7Quot.span
      Row.D6)
    (hQB : Adapted B.twD7Quot (B.twD7Quot.b 0) (img (B.b 0 * B.b 1) (twD7M0 K B))
      B.twD7Quot.span)
    (hQrec : RecOutD6 B.twD7Quot (B.twD7Quot.b 0))
    (horb : ∀ n ∈ normalizer (B.twD7Quot.span : Set (Q (B.b 0 * B.b 1))), ∀ e : Coords 7,
      n * B.twD7Quot.b 0 * n⁻¹ = B.twD7Quot.vec e → IsD6Root e)
    (hn1 : ∀ {x : ModGL .E7 (ZMod 2)}, x ∈ L7 → (∀ a ∈ Jn 1, x * a = a * x) →
      (∀ a ∈ Jn 2, x * a = a * x) → (∀ a ∈ Jn 5, x * a = a * x) →
      (∀ a ∈ Jn 6, x * a = a * x) → ∃ n ∈ L7, n * x * n⁻¹ ∈ Jn 0) :
    ∃ π : twD7BetaHost b₀ K E B →* adjointGroup .E7 (ZMod 2),
      Function.Surjective π ∧
      (∃ R₁ : Subgroup G, R₁ ≤ centralizer ({b₀} : Set G) ∧
        (R₁.subgroupOf (centralizer ({b₀} : Set G))).Normal ∧ ¬ 3 ∣ Nat.card R₁ ∧
        π.ker ≤ R₁.subgroupOf (twD7BetaHost b₀ K E B) ⊔
          (zpowers (b₀ * B.b 1)).subgroupOf (twD7BetaHost b₀ K E B)) ∧
      (∀ ha : b₀⁻¹ * B.b 1 ∈ twD7BetaHost b₀ K E B,
        ((π ⟨b₀⁻¹ * B.b 1, ha⟩ : adjointGroup .E7 (ZMod 2)) : ModGL .E7 (ZMod 2)) ∈ Jn 0) := by
  classical
  have hb0 : B.b 0 = b₀ := hB.2.1
  subst hb0
  obtain ⟨U, g, h₁, h₂, h₃, h₄, -, -, h₇, h₈, h₉, h₁₀, h₁₁⟩ := exists_d6Frame hQstd hQB hQrec
  set Y : Subgroup (Q (B.b 0 * B.b 1)) := ⨆ k, U k with hY
  have hUY : ∀ k, U k ≤ Y := fun k => le_iSup U k
  have hZY : centralizer (Y : Set (Q (B.b 0 * B.b 1))) ⊓ Y = ⊥ :=
    (isEm_seven_of_frame U h₁ h₂).2
  have hR : evenFix0 6 ⊆ B.twD7Quot.realized (img (B.b 0 * B.b 1) (twD7M0 K B)) :=
    (realized_centralizer_eq_realized_D6 hQstd hQB hQrec).2.symm.subset
  have hYle : Y ≤ img (B.b 0 * B.b 1) (twD7M0 K B) ⊔
      (img (B.b 0 * B.b 1) (twD7M0 K B)).map (MulAut.conj g).toMonoidHom :=
    iSup_le fun k => (h₈ k).elim (fun h => h.trans le_sup_left) (fun h => h.trans le_sup_right)
  obtain ⟨R, hRC, hRn, hR3, -, hYH, hHYR, hcomm, hYR⟩ :=
    exists_split_twD7Quot hstd hB hrec h₃ h₄ h₇ hYle hZY horb
      (fun e he => exists_mem_conj_b_zero_eq_vec_of_isD6Root hR h₃ h₉ h₁₀ he)
  obtain ⟨p, hp_surj, hp_ker, hp_id⟩ :=
    CFSG.GroupTheory.exists_proj_of_le_sup_of_commute hYH hHYR hcomm hYR
  have hHcen : twD7BetaHost (B.b 0) K E B ≤ cen (B.b 0 * B.b 1) := (twD7BetaHost_le_of_std hstd).1
  let prH : ↥(twD7BetaHost (B.b 0) K E B) →*
      ↥(img (B.b 0 * B.b 1) (twD7BetaHost (B.b 0) K E B)) :=
    ((pr _).comp (Subgroup.inclusion hHcen)).codRestrict _ fun h => pr_mem_img h.2
  have hprH : Function.Surjective prH := by
    rintro ⟨q, hq⟩
    obtain ⟨x, hx, rfl⟩ := mem_img_iff.mp hq
    exact ⟨⟨x, hx⟩, rfl⟩
  have hgen : ⨆ k, (U k).subgroupOf Y = ⊤ := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_iSup, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    simp_rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left (hUY _)]
    exact hY.symm
  have hZc : center ↥Y = ⊥ := by
    have h := CFSG.GroupTheory.inf_centralizer_eq_map_center Y
    rw [inf_comm, hZY] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).mp h.symm
  obtain ⟨φ, hφ⟩ := exists_mulEquiv_L7_frame e7NatFrame_holds (fun k => (U k).subgroupOf Y)
    hgen
    (fun i j hij hne1 hne2 a ha c hc => Subtype.ext (h₁ i j hij hne1 hne2 _
      (mem_subgroupOf.mp ha) _ (mem_subgroupOf.mp hc)))
    (fun i j hij => by
      obtain ⟨W, hW⟩ := h₂ i j hij
      exact ⟨_, linearBlockStandardPair_subgroupOf (hUY i) (hUY j) hW⟩)
    hZc
  have hM0C : img (B.b 0 * B.b 1) (twD7M0 K B) ≤
      centralizer ({B.twD7Quot.b 0} : Set (Q (B.b 0 * B.b 1))) := hQstd.2.1.1.2.1
  have hx₀c : ∀ k : Fin 7, k ≠ 0 → ∀ a ∈ Jn k,
      ((φ ⟨B.twD7Quot.b 0, h₄⟩ : ↥L7) : ModGL .E7 (ZMod 2)) * a =
        a * (φ ⟨B.twD7Quot.b 0, h₄⟩ : ↥L7) := by
    intro k hk a ha
    have haL : a ∈ L7 := jn_le_l7 k ha
    have ha' : (⟨a, haL⟩ : ↥L7) ∈ ((U k).subgroupOf Y).map φ.toMonoidHom := by
      rw [hφ k]
      exact ha
    obtain ⟨u, hu, hua⟩ := Subgroup.mem_map.mp ha'
    have hcomm' : (u : Q (B.b 0 * B.b 1)) * B.twD7Quot.b 0 = B.twD7Quot.b 0 * u :=
      mem_centralizer_singleton_iff.mp (hM0C (h₁₁ k hk (mem_subgroupOf.mp hu)))
    have huy : u * ⟨B.twD7Quot.b 0, h₄⟩ = ⟨B.twD7Quot.b 0, h₄⟩ * u := Subtype.ext hcomm'
    have h := congrArg (fun z => ((φ z : ↥L7) : ModGL .E7 (ZMod 2))) huy
    simp only [map_mul, Subgroup.coe_mul] at h
    have hφu : ((φ u : ↥L7) : ModGL .E7 (ZMod 2)) = a := congrArg Subtype.val hua
    rw [hφu] at h
    exact h.symm
  obtain ⟨n, hnL, hn⟩ := hn1 (φ ⟨B.twD7Quot.b 0, h₄⟩).2 (hx₀c 1 (by decide))
    (hx₀c 2 (by decide)) (hx₀c 5 (by decide)) (hx₀c 6 (by decide))
  let c : ↥L7 ≃* ↥L7 := MulAut.conj (⟨n, hnL⟩ : ↥L7)
  refine ⟨(c.toMonoidHom.comp φ.toMonoidHom).comp (p.comp prH), ?_, ⟨R, hRC, hRn, hR3, ?_⟩, ?_⟩
  · intro y
    obtain ⟨y₁, rfl⟩ := c.surjective y
    obtain ⟨y₂, rfl⟩ := φ.surjective y₁
    obtain ⟨y₃, rfl⟩ := hp_surj y₂
    obtain ⟨y₄, rfl⟩ := hprH y₃
    exact ⟨y₄, rfl⟩
  · intro h hh
    have hh' : c (φ (p (prH h))) = 1 := hh
    have h1 : φ (p (prH h)) = 1 := c.injective (hh'.trans (map_one c).symm)
    have h2 : p (prH h) = 1 := φ.injective (h1.trans (map_one φ).symm)
    have h3 : prH h ∈ (img (B.b 0 * B.b 1) R).subgroupOf _ := by
      rw [← hp_ker]
      exact h2
    obtain ⟨r, hrR, hr⟩ := mem_img_iff.mp (mem_subgroupOf.mp h3)
    have h4 : (r : G)⁻¹ * h ∈ zpowers (B.b 0 * B.b 1) := (pr_eq_pr_iff r _).mp hr
    have hβE : B.b 0 * B.b 1 ∈ E :=
      E.mul_mem (hB.1 ▸ B.b_mem_span 0) (hB.1 ▸ B.b_mem_span 1)
    have hβH : B.b 0 * B.b 1 ∈ twD7BetaHost (B.b 0) K E B := le_twD7BetaHost_of_std hstd hB hβE
    have hzH : (r : G)⁻¹ * h ∈ twD7BetaHost (B.b 0) K E B := zpowers_le.mpr hβH h4
    have hrH : (r : G) ∈ twD7BetaHost (B.b 0) K E B := by
      have : (r : G) = h * ((r : G)⁻¹ * h)⁻¹ := by group
      rw [this]
      exact mul_mem h.2 (inv_mem hzH)
    have hdec : h = ⟨r, hrH⟩ * ⟨(r : G)⁻¹ * h, hzH⟩ := Subtype.ext (by simp)
    rw [hdec]
    exact mul_mem (mem_sup_left (mem_subgroupOf.mpr hrR)) (mem_sup_right (mem_subgroupOf.mpr h4))
  · intro ha
    have hpr : prH ⟨(B.b 0)⁻¹ * B.b 1, ha⟩ = ⟨B.twD7Quot.b 0, hYH h₄⟩ := by
      apply Subtype.ext
      change pr _ ⟨(B.b 0)⁻¹ * B.b 1, hHcen ha⟩ = B.twD7Quot.b 0
      have e1 : (⟨(B.b 0)⁻¹ * B.b 1, hHcen ha⟩ : ↥(cen (B.b 0 * B.b 1))) =
          (⟨B.b 0, B.b_mem_cen_twD7 0⟩ : ↥(cen (B.b 0 * B.b 1)))⁻¹ *
            ⟨B.b 1, B.b_mem_cen_twD7 1⟩ := rfl
      rw [e1, map_mul, map_inv, B.pr_b_zero_twD7Quot, B.pr_b_one_twD7Quot]
      have h3 : B.twD7Quot.b 0 ^ 3 = 1 := by
        rw [← B.twD7Quot.ord 0]
        exact pow_orderOf_eq_one _
      calc (B.twD7Quot.b 0)⁻¹ * (B.twD7Quot.b 0)⁻¹ =
          B.twD7Quot.b 0 ^ 3 * (B.twD7Quot.b 0)⁻¹ * (B.twD7Quot.b 0)⁻¹ := by rw [h3, one_mul]
        _ = B.twD7Quot.b 0 := by group
    have hpy : p ⟨B.twD7Quot.b 0, hYH h₄⟩ = ⟨B.twD7Quot.b 0, h₄⟩ := Subtype.ext (hp_id _ h₄)
    change ((c (φ (p (prH ⟨(B.b 0)⁻¹ * B.b 1, ha⟩))) : ↥L7) : ModGL .E7 (ZMod 2)) ∈ Jn 0
    rw [hpr, hpy]
    exact hn

end CFSG.StandardType.FrameRoute.FS81
