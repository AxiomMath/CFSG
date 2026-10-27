module

public import CFSG.RankThree.GF2n.Stroth80.Sec4Bar

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Abstract

theorem isComponent_of_normal_normal {Γ : Type} [Group Γ] {N X : Subgroup Γ} (hN : N.Normal)
    (hXN : X ≤ N) (hX : (X.subgroupOf N).Normal) (hq : CFSG.IsQuasisimple ↥X) :
    IsComponent X :=
  ⟨hq, Subgroup.IsSubnormal.step X N hXN hN.isSubnormal hX⟩

theorem conj_mem_of_subgroupOf_normal {Γ : Type} [Group Γ] {N X : Subgroup Γ} (hXN : X ≤ N)
    (hX : (X.subgroupOf N).Normal) {r : Γ} (hr : r ∈ N) {x : Γ} (hx : x ∈ X) :
    r * x * r⁻¹ ∈ X := by
  have := hX.conj_mem ⟨x, hXN hx⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨r, hr⟩
  exact Subgroup.mem_subgroupOf.mp this

end Abstract

section

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.bar_Rt_le_bar_Lgen (t : G) :
    bar M Q (Rt M (LB M Q B) t) ≤ bar M Q (Lgen M (LB M Q B)) :=
  Subgroup.map_mono fun _ hx => Rt_le_Lgen' M (LB M Q B) t hx

theorem Ctx.bar_CN_le_bar_Rt (hc : Ctx M Q Z B) (t : G) :
    bar M Q (hc.CN t) ≤ bar M Q (Rt M (LB M Q B) t) :=
  Subgroup.map_mono fun _ hx => (Ctx.mem_CN (hc := hc)).mp hx |>.1

theorem Ctx.comm_of_normal_Rt (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B)
    {X : Subgroup (Mbar M Q)} (hXR : X ≤ bar M Q (Rt M (LB M Q B) t))
    (hXn : ∀ r ∈ bar M Q (Rt M (LB M Q B) t), ∀ x ∈ X, r * x * r⁻¹ ∈ X)
    (hXN : X ⊓ bar M Q (hc.CN t) = ⊥) :
    ∀ x ∈ X, ∀ ν ∈ bar M Q (hc.CN t), x * ν = ν * x := by
  intro x hx ν hν
  have hνR : ν ∈ bar M Q (Rt M (LB M Q B) t) := hc.bar_CN_le_bar_Rt t hν
  have h1 : x * ν * x⁻¹ ∈ bar M Q (hc.CN t) := hc.bar_CN_conj_mem ht (hXR hx) hν
  have h2 : ν * x⁻¹ * ν⁻¹ ∈ X := hXn ν hνR x⁻¹ (X.inv_mem hx)
  have h3 : x * ν * x⁻¹ * ν⁻¹ ∈ X ⊓ bar M Q (hc.CN t) := by
    refine ⟨?_, (bar M Q (hc.CN t)).mul_mem h1 ((bar M Q (hc.CN t)).inv_mem hν)⟩
    have e : x * ν * x⁻¹ * ν⁻¹ = x * (ν * x⁻¹ * ν⁻¹) := by group
    rw [e]
    exact X.mul_mem hx h2
  rw [hXN, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
  exact h3

theorem Ctx.normal_simple_embed (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hCQ : ClassicalQuasisimpleStatement) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hcs : CompSimple (Mbar M Q)) {t : G} (ht : t ∈ LB M Q B) (htQ : t ∉ Q)
    {X : Subgroup (Mbar M Q)} (hX : IsComponent X) (hXR : X ≤ bar M Q (Rt M (LB M Q B) t))
    (hXn : ∀ r ∈ bar M Q (Rt M (LB M Q B) t), ∀ x ∈ X, r * x * r⁻¹ ∈ X)
    (hXSL : ¬ IsSLModel 2 (Nat.card Z) ↥X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (Gc : Type) (_ : Group Gc)
      (π : ↥(bar M Q (Rt M (LB M Q B) t)) →* Gc), Nat.card K = Nat.card Z ∧
        Function.Surjective π ∧
        (∀ x : ↥(bar M Q (Rt M (LB M Q B) t)),
          π x = 1 ↔ (x : Mbar M Q) ∈ bar M Q (hc.CN t)) ∧ IsClassicalOver K Gc ∧
        CFSG.IsQuasisimple Gc ∧ (∀ g : Gc, ∃ x : ↥X, π ⟨(x : Mbar M Q), hXR x.2⟩ = g) := by
  classical
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  have hSL2 : ∀ (K : Type) [Field K] [Finite K], Nat.card K = Nat.card Z →
      CFSG.IsQuasisimple ↥(StatedSL 2 K) := by
    intro K _ _ hK
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans hZ2)
    exact (hCQ K (by rw [hK]; exact hq4)).1 2 le_rfl
  have hΛ := hc.swapHyp hw hn hno
  haveI := isSimpleGroup_of_center_eq_bot hX (hcs X hX)
  have hXN : X ⊓ bar M Q (hc.CN t) = ⊥ :=
    hc.component_inf_CN_eq_bot h34 hw hn hno hgen hcs ht hX hXR
  have hRne : Rt M (LB M Q B) t ≠ LB M Q B := by
    intro hRL
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_isComponent hX
    have hXΛ : X ≤ bar M Q (LB M Q B) := by
      have := hXR
      rwa [hRL] at this
    exact hab (Subtype.ext (hΛ.comm _ (hXΛ a.2) _ (hXΛ b.2)))
  obtain ⟨K, hF, hFin, hK2, Gc, hGc, π, hK, hπs, hπk, hcl⟩ :=
    hc.classical_quotient h310 hw hn hno hgen ht htQ hRne
  have hshape := hcl.shape hCQ (by rw [hK]; exact hq4)
  have hinj : ∀ x : ↥X, π ⟨(x : Mbar M Q), hXR x.2⟩ = 1 → x = 1 := by
    intro x hx
    have h1 := (hπk ⟨(x : Mbar M Q), hXR x.2⟩).mp hx
    have h2 : (x : Mbar M Q) ∈ X ⊓ bar M Q (hc.CN t) := ⟨x.2, h1⟩
    rw [hXN, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hns : ¬ Group.IsSolvable ↥X := fun hs => not_isSolvable_of_isQuasisimple hX.1 hs
  haveI : CharP K 2 := hK2
  rcases normal_embedding_cases (hSL2 K hK) (R := bar M Q (Rt M (LB M Q B) t)) (X := X)
    π hπs hshape hXR hXn hinj hns with ⟨hq, ⟨e⟩⟩ | he | he
  · refine ⟨K, hF, hFin, hK2, Gc, hGc, π, hK, hπs, hπk, hcl, hq, ?_⟩
    let φ : ↥X →* Gc := π.comp (Subgroup.inclusion hXR)
    have hφinj : Function.Injective φ := (injective_iff_map_eq_one φ).mpr hinj
    haveI : Finite Gc := Finite.of_equiv _ e.toEquiv
    have hbij : Function.Bijective φ :=
      hφinj.bijective_of_nat_card_le (Nat.card_congr e.toEquiv).symm.le
    intro g
    obtain ⟨x, hx⟩ := hbij.2 g
    exact ⟨x, hx⟩
  · exact (hXSL ⟨K, hF, hFin, hK, he⟩).elim
  · obtain ⟨e⟩ := he
    exact (not_isSimpleGroup_of_prod (hSL2 K hK) e).elim

theorem Ctx.Rt_eq_CN_sup (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hCQ : ClassicalQuasisimpleStatement) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hcs : CompSimple (Mbar M Q)) {t : G} (ht : t ∈ LB M Q B) (htQ : t ∉ Q)
    {X : Subgroup (Mbar M Q)} (hX : IsComponent X) (hXR : X ≤ bar M Q (Rt M (LB M Q B) t))
    (hXn : ∀ r ∈ bar M Q (Rt M (LB M Q B) t), ∀ x ∈ X, r * x * r⁻¹ ∈ X)
    (hXSL : ¬ IsSLModel 2 (Nat.card Z) ↥X) :
    bar M Q (Rt M (LB M Q B) t) = bar M Q (hc.CN t) ⊔ X := by
  obtain ⟨K, hF, hFin, hK2, Gc, hGc, π, hK, hπs, hπk, hcl, hq, hXπ⟩ :=
    hc.normal_simple_embed h34 h310 hCQ hw hn hno hgen hcs ht htQ hX hXR hXn hXSL
  refine le_antisymm ?_ (sup_le (hc.bar_CN_le_bar_Rt t) hXR)
  intro r hr
  obtain ⟨x, hx⟩ := hXπ (π ⟨r, hr⟩)
  have h1 : π ⟨r * (x : Mbar M Q)⁻¹, (bar M Q (Rt M (LB M Q B) t)).mul_mem hr
      ((bar M Q (Rt M (LB M Q B) t)).inv_mem (hXR x.2))⟩ = 1 := by
    have e : (⟨r * (x : Mbar M Q)⁻¹, (bar M Q (Rt M (LB M Q B) t)).mul_mem hr
        ((bar M Q (Rt M (LB M Q B) t)).inv_mem (hXR x.2))⟩ : ↥(bar M Q (Rt M (LB M Q B) t))) =
        ⟨r, hr⟩ * (⟨(x : Mbar M Q), hXR x.2⟩)⁻¹ := rfl
    rw [e, map_mul, map_inv, hx, mul_inv_cancel]
  have h2 := (hπk _).mp h1
  have e : r = r * (x : Mbar M Q)⁻¹ * (x : Mbar M Q) := by group
  rw [e]
  exact Subgroup.mul_mem_sup h2 x.2

theorem Ctx.inf_CN_inf_CN_eq_bot (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hCQ : ClassicalQuasisimpleStatement) (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    (hn : 2 < n) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hcs : CompSimple (Mbar M Q)) {X₁ X₂ : Subgroup (Mbar M Q)}
    (h₁ : IsQSNormalIn X₁ (bar M Q (Lgen M (LB M Q B))))
    (h₂ : IsQSNormalIn X₂ (bar M Q (Lgen M (LB M Q B)))) (hX : X₁ ⊓ X₂ = ⊥)
    (hSL₁ : ¬ IsSLModel 2 (Nat.card Z) ↥X₁) {t τ : G}
    (hcomm₂ : ∀ x ∈ X₂, ∀ ν ∈ bar M Q (hc.CN t), x * ν = ν * x)
    (hcomm₁ : ∀ x ∈ X₁, ∀ ν ∈ bar M Q (hc.CN τ), x * ν = ν * x) :
    bar M Q (LB M Q B) ⊓ bar M Q (hc.CN t) ⊓ bar M Q (hc.CN τ) = ⊥ := by
  classical
  by_contra hne
  obtain ⟨cb, hcb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hcbΛ : (cb : Mbar M Q) ∈ bar M Q (LB M Q B) := cb.2.1.1
  have hcbt : (cb : Mbar M Q) ∈ bar M Q (hc.CN t) := cb.2.1.2
  have hcbτ : (cb : Mbar M Q) ∈ bar M Q (hc.CN τ) := cb.2.2
  have hcb1' : (cb : Mbar M Q) ≠ 1 := fun h => hcb1 (Subtype.ext h)
  obtain ⟨c, hcLB, hcQ, hcmk⟩ := hc.exists_lift_ne_one hcbΛ hcb1'
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  have hSL2 : ∀ (K : Type) [Field K] [Finite K], Nat.card K = Nat.card Z →
      CFSG.IsQuasisimple ↥(StatedSL 2 K) := by
    intro K _ _ hK
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans hZ2)
    exact (hCQ K (by rw [hK]; exact hq4)).1 2 le_rfl
  have hΛ := hc.swapHyp hw hn hno
  have hNorm := hc.normal_bar_Lgen
  have hX₁c : IsComponent X₁ := isComponent_of_normal_normal hNorm h₁.1 h₁.2.1 h₁.2.2
  have hX₂c : IsComponent X₂ := isComponent_of_normal_normal hNorm h₂.1 h₂.2.1 h₂.2.2
  have hR₁ : X₁ ≤ bar M Q (Rt M (LB M Q B) (c : G)) := by
    refine hc.component_le_bar_Rt h34 hw hn hno hgen hcs hX₁c hcLB fun x hx => ?_
    rw [hcmk]
    exact hcomm₁ x hx _ hcbτ
  have hR₂ : X₂ ≤ bar M Q (Rt M (LB M Q B) (c : G)) := by
    refine hc.component_le_bar_Rt h34 hw hn hno hgen hcs hX₂c hcLB fun x hx => ?_
    rw [hcmk]
    exact hcomm₂ x hx _ hcbt
  have hRM : bar M Q (Rt M (LB M Q B) (c : G)) ≤ bar M Q (Lgen M (LB M Q B)) :=
    Ctx.bar_Rt_le_bar_Lgen (c : G)
  have hn₁ : ∀ r ∈ bar M Q (Rt M (LB M Q B) (c : G)), ∀ x ∈ X₁, r * x * r⁻¹ ∈ X₁ :=
    fun r hr x hx => conj_mem_of_subgroupOf_normal h₁.1 h₁.2.1 (hRM hr) hx
  haveI := isSimpleGroup_of_center_eq_bot hX₁c (hcs X₁ hX₁c)
  have hXN₁ : X₁ ⊓ bar M Q (hc.CN (c : G)) = ⊥ :=
    hc.component_inf_CN_eq_bot h34 hw hn hno hgen hcs hcLB hX₁c hR₁
  have hSup : (X₁ ⊔ X₂) ⊓ bar M Q (hc.CN (c : G)) = ⊥ := by
    have := hc.sSup_inf_CN_eq_bot h34 hw hn hno hgen hcs hcLB {X₁, X₂} (by
      intro C hC
      rcases hC with rfl | hC
      · exact ⟨hX₁c, hR₁⟩
      · have hC' : C = X₂ := hC
        subst hC'
        exact ⟨hX₂c, hR₂⟩)
    rwa [sSup_pair] at this
  have hRne : Rt M (LB M Q B) (c : G) ≠ LB M Q B := by
    intro hRL
    obtain ⟨a, b, hab⟩ := exists_noncomm_of_isComponent hX₁c
    have hXΛ : X₁ ≤ bar M Q (LB M Q B) := by
      have := hR₁
      rwa [hRL] at this
    exact hab (Subtype.ext (hΛ.comm _ (hXΛ a.2) _ (hXΛ b.2)))
  obtain ⟨K, hF, hFin, hK2, Gc, hGc, π, hK, hπs, hπk, hcl⟩ :=
    hc.classical_quotient h310 hw hn hno hgen hcLB hcQ hRne
  have hshape := hcl.shape hCQ (by rw [hK]; exact hq4)
  have hinj : ∀ x : ↥X₁, π ⟨(x : Mbar M Q), hR₁ x.2⟩ = 1 → x = 1 := by
    intro x hx
    have h1 := (hπk ⟨(x : Mbar M Q), hR₁ x.2⟩).mp hx
    have h2 : (x : Mbar M Q) ∈ X₁ ⊓ bar M Q (hc.CN (c : G)) := ⟨x.2, h1⟩
    rw [hXN₁, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hns : ¬ Group.IsSolvable ↥X₁ := fun hs => not_isSolvable_of_isQuasisimple hX₁c.1 hs
  haveI : CharP K 2 := hK2
  rcases normal_embedding_cases (hSL2 K hK) (R := bar M Q (Rt M (LB M Q B) (c : G))) (X := X₁)
    π hπs hshape hR₁ hn₁ hinj hns with ⟨hq, ⟨e⟩⟩ | he | he
  ·
    let φ : ↥X₁ →* Gc := π.comp (Subgroup.inclusion hR₁)
    have hφinj : Function.Injective φ := (injective_iff_map_eq_one φ).mpr hinj
    haveI : Finite Gc := Finite.of_equiv _ e.toEquiv
    have hbij : Function.Bijective φ :=
      hφinj.bijective_of_nat_card_le (Nat.card_congr e.toEquiv).symm.le
    apply ne_bot_of_isComponent hX₂c
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, hx⟩ := hbij.2 (π ⟨y, hR₂ hy⟩)
    have hx' : π ⟨(x : Mbar M Q), hR₁ x.2⟩ = π ⟨y, hR₂ hy⟩ := hx
    have h1 : π ⟨(x : Mbar M Q)⁻¹ * y, (bar M Q (Rt M (LB M Q B) (c : G))).mul_mem
        ((bar M Q (Rt M (LB M Q B) (c : G))).inv_mem (hR₁ x.2)) (hR₂ hy)⟩ = 1 := by
      have e' : (⟨(x : Mbar M Q)⁻¹ * y, (bar M Q (Rt M (LB M Q B) (c : G))).mul_mem
          ((bar M Q (Rt M (LB M Q B) (c : G))).inv_mem (hR₁ x.2)) (hR₂ hy)⟩ :
          ↥(bar M Q (Rt M (LB M Q B) (c : G)))) =
          (⟨(x : Mbar M Q), hR₁ x.2⟩)⁻¹ * ⟨y, hR₂ hy⟩ := rfl
      rw [e', map_mul, map_inv, hx', inv_mul_cancel]
    have h2 := (hπk _).mp h1
    have h3 : (x : Mbar M Q)⁻¹ * y ∈ (X₁ ⊔ X₂) ⊓ bar M Q (hc.CN (c : G)) :=
      ⟨(X₁ ⊔ X₂).mul_mem ((X₁ ⊔ X₂).inv_mem ((le_sup_left : X₁ ≤ X₁ ⊔ X₂) x.2))
        ((le_sup_right : X₂ ≤ X₁ ⊔ X₂) hy), h2⟩
    rw [hSup, Subgroup.mem_bot, inv_mul_eq_one] at h3
    have h4 : y ∈ X₁ ⊓ X₂ := ⟨h3 ▸ x.2, hy⟩
    rw [hX] at h4
    exact h4
  · exact hSL₁ ⟨K, hF, hFin, hK, he⟩
  · obtain ⟨e⟩ := he
    exact not_isSimpleGroup_of_prod (hSL2 K hK) e

end

section

@[expose] def Stroth41iiTensorStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) (n : ℕ), Width Q Z n → 2 < n → NoA2 Q Z (LB M Q B) → GenByB M Q B →
    ∀ (X₁ X₂ : Subgroup (Mbar M Q)), IsQSNormalIn X₁ (bar M Q (Lgen M (LB M Q B))) →
      IsQSNormalIn X₂ (bar M Q (Lgen M (LB M Q B))) → X₁ ⊓ X₂ = ⊥ →
      ¬ IsSLModel 2 (Nat.card Z) ↥X₁ → ¬ IsSLModel 2 (Nat.card Z) ↥X₂ →
      ∀ (t τ : ↥M), (t : G) ∈ LB M Q B → (τ : G) ∈ LB M Q B →
        (QuotientGroup.mk t : Mbar M Q) ∈ X₁ → (QuotientGroup.mk t : Mbar M Q) ≠ 1 →
        (QuotientGroup.mk τ : Mbar M Q) ∈ X₂ → (QuotientGroup.mk τ : Mbar M Q) ≠ 1 →
        bar M Q (LB M Q B) ⊓ bar M Q (hc.CN (t : G)) ⊓ bar M Q (hc.CN (τ : G)) = ⊥ → False

theorem stroth41ii_of_tensor (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (h44 : Stroth44Statement) (hCQ : ClassicalQuasisimpleStatement)
    (hT : Stroth41iiTensorStatement) : Stroth41iiStatement := by
  intro G _ _ M Q Z B hN hc n hw hn hno hgen hSL X₁ X₂ h₁ h₂
  classical
  by_contra hne
  have hcs := hc.compSimple h34 h44 hw hn hno hgen
  have hNorm := hc.normal_bar_Lgen
  have hX₁c : IsComponent X₁ := isComponent_of_normal_normal hNorm h₁.1 h₁.2.1 h₁.2.2
  have hX₂c : IsComponent X₂ := isComponent_of_normal_normal hNorm h₂.1 h₂.2.1 h₂.2.2
  have hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x := comm_of_ne_component hX₁c hX₂c hne
  have hXY : X₁ ⊓ X₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    exact Subgroup.mem_bot.mpr (hcs.eq_one_of_commutes hX₁c hx1 fun y hy => hcomm y hy x hx2)
  have hSL₁ : ¬ IsSLModel 2 (Nat.card Z) ↥X₁ := fun h => hSL ⟨X₁, h₁.1, h₁.2.1, h⟩
  have hSL₂ : ¬ IsSLModel 2 (Nat.card Z) ↥X₂ := fun h => hSL ⟨X₂, h₂.1, h₂.2.1, h⟩
  have hne₁ : bar M Q (LB M Q B) ⊓ X₁ ≠ ⊥ :=
    hc.inter_bar_LB_ne_bot h34 hw hn hno hgen h₁.2.2 (hc.bar_LB_le_normalizer_of_normal h₁.1 h₁.2.1)
  have hne₂ : bar M Q (LB M Q B) ⊓ X₂ ≠ ⊥ :=
    hc.inter_bar_LB_ne_bot h34 hw hn hno hgen h₂.2.2 (hc.bar_LB_le_normalizer_of_normal h₂.1 h₂.2.1)
  obtain ⟨tb, htb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne₁
  obtain ⟨τb, hτb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne₂
  have htb1' : (tb : Mbar M Q) ≠ 1 := fun h => htb1 (Subtype.ext h)
  have hτb1' : (τb : Mbar M Q) ≠ 1 := fun h => hτb1 (Subtype.ext h)
  obtain ⟨t, htLB, htQ, htmk⟩ := hc.exists_lift_ne_one tb.2.1 htb1'
  obtain ⟨τ, hτLB, hτQ, hτmk⟩ := hc.exists_lift_ne_one τb.2.1 hτb1'
  have hR₂ : X₂ ≤ bar M Q (Rt M (LB M Q B) (t : G)) := by
    refine hc.component_le_bar_Rt h34 hw hn hno hgen hcs hX₂c htLB fun x hx => ?_
    rw [htmk]
    exact (hcomm _ tb.2.2 x hx).symm
  have hR₁ : X₁ ≤ bar M Q (Rt M (LB M Q B) (τ : G)) := by
    refine hc.component_le_bar_Rt h34 hw hn hno hgen hcs hX₁c hτLB fun x hx => ?_
    rw [hτmk]
    exact hcomm x hx _ τb.2.2
  have hn₂ : ∀ r ∈ bar M Q (Rt M (LB M Q B) (t : G)), ∀ x ∈ X₂, r * x * r⁻¹ ∈ X₂ :=
    fun r hr x hx => conj_mem_of_subgroupOf_normal h₂.1 h₂.2.1
      (Ctx.bar_Rt_le_bar_Lgen (t : G) hr) hx
  have hn₁ : ∀ r ∈ bar M Q (Rt M (LB M Q B) (τ : G)), ∀ x ∈ X₁, r * x * r⁻¹ ∈ X₁ :=
    fun r hr x hx => conj_mem_of_subgroupOf_normal h₁.1 h₁.2.1
      (Ctx.bar_Rt_le_bar_Lgen (τ : G) hr) hx
  have hcomm₂ := hc.comm_of_normal_Rt htLB hR₂ hn₂
    (hc.component_inf_CN_eq_bot h34 hw hn hno hgen hcs htLB hX₂c hR₂)
  have hcomm₁ := hc.comm_of_normal_Rt hτLB hR₁ hn₁
    (hc.component_inf_CN_eq_bot h34 hw hn hno hgen hcs hτLB hX₁c hR₁)
  have hC := hc.inf_CN_inf_CN_eq_bot h34 h310 hCQ hw hn hno hgen hcs h₁ h₂ hXY hSL₁ hcomm₂ hcomm₁
  exact hT G M Q Z B hc n hw hn hno hgen X₁ X₂ h₁ h₂ hXY hSL₁ hSL₂ t τ htLB hτLB
    (htmk ▸ tb.2.2) (htmk ▸ htb1') (hτmk ▸ τb.2.2) (hτmk ▸ hτb1') hC

end

end CFSG.RankThree.GF2n.Stroth80
