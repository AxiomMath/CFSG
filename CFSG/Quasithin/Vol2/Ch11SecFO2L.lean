module

public import CFSG.Quasithin.Vol2.Ch11SecA11Comp
public import CFSG.Quasithin.Vol2.Ch11SecFFacts3
public import CFSG.Quasithin.Vol2.Ch11SecFQ1

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.QuasithinUnique.C5 (conjSubgroup_normalizer conjSubgroup_eq_self)
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_normalizer_commSub {A D : Subgroup G} {x : G}
    (hxA : x ∈ Subgroup.normalizer (A : Set G)) (hxD : x ∈ Subgroup.normalizer (D : Set G)) :
    x ∈ Subgroup.normalizer (commSub A D : Set G) := by
  have key : ∀ x : G, x ∈ Subgroup.normalizer (A : Set G) →
      x ∈ Subgroup.normalizer (D : Set G) → ∀ z ∈ commSub A D, x * z * x⁻¹ ∈ commSub A D := by
    intro x hxA hxD z hz
    refine mem_commSub.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hxD (mem_commSub.mp hz).1)
      (Subgroup.inv_mem _ hxD), fun a ha => ?_⟩
    have ha' : x⁻¹ * a * x ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxA) a).mp ha
      simpa using this
    have h1 := (mem_commSub.mp hz).2 _ ha'
    have heq : ⁅a, x * z * x⁻¹⁆ = x * ⁅x⁻¹ * a * x, z⁆ * x⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp hxD _).mp h1
  refine SecD.mem_normalizer_of_conj (key x hxA hxD) fun z hz => ?_
  have h := key x⁻¹ (Subgroup.inv_mem _ hxA) (Subgroup.inv_mem _ hxD) z hz
  simpa using h

theorem le_of_le_sup_of_perfect [Finite G] {B K S : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hS : IsPGroup 2 S) (hSB : S ≤ Subgroup.normalizer (B : Set G)) (hKS : K ≤ B ⊔ S) :
    K ≤ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBN : (B.subgroupOf (B ⊔ S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hSB)
  set φ := QuotientGroup.mk' (B.subgroupOf (B ⊔ S)) with hφ
  have hS' : IsPGroup 2 ↥(S.subgroupOf (B ⊔ S)) :=
    hS.of_equiv (Subgroup.subgroupOfEquivOfLe le_sup_right).symm
  have hrange : (S.subgroupOf (B ⊔ S)).map φ = ⊤ := by
    have h1 : B.subgroupOf (B ⊔ S) ⊔ S.subgroupOf (B ⊔ S) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
      exact Subgroup.subgroupOf_self _
    have h2 : (B.subgroupOf (B ⊔ S)).map φ = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, hφ, QuotientGroup.ker_mk']
    rw [← Subgroup.map_top_of_surjective φ (QuotientGroup.mk'_surjective _), ← h1,
      Subgroup.map_sup, h2, bot_sup_eq]
  have hQ : IsPGroup 2 (↥(B ⊔ S) ⧸ B.subgroupOf (B ⊔ S)) := by
    have h3 : IsPGroup 2 ↥((S.subgroupOf (B ⊔ S)).map φ) := hS'.map φ
    rw [hrange] at h3
    exact h3.of_equiv Subgroup.topEquiv
  have := hQ.isNilpotent
  have hK' : ⁅K.subgroupOf (B ⊔ S), K.subgroupOf (B ⊔ S)⁆ = K.subgroupOf (B ⊔ S) := by
    apply Subgroup.map_injective (B ⊔ S).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKS, hK]
  have hKφ : ⁅(K.subgroupOf (B ⊔ S)).map φ, (K.subgroupOf (B ⊔ S)).map φ⁆ =
      (K.subgroupOf (B ⊔ S)).map φ := by
    rw [← Subgroup.map_commutator, hK']
  have hbot := SecA.eq_bot_of_perfect_of_le_solvable
    (le_top (a := (K.subgroupOf (B ⊔ S)).map φ)) hKφ
  intro k hk
  have hkN : k ∈ B ⊔ S := hKS hk
  have h1 : φ ⟨k, hkN⟩ ∈ (K.subgroupOf (B ⊔ S)).map φ := ⟨⟨k, hkN⟩, hk, rfl⟩
  rw [hbot, Subgroup.mem_bot, hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

variable [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ V₂ V₃ : Subgroup G}

theorem gen_wH (hF : Sp4Facts) (hGen : FactSp4Gen) (hN : SecA.NatFacts) (h1102 : Stmt11_0_2)
    (h1103 : Stmt11_0_3) (h1113 : Stmt11_1_3) (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3)
    (h1154 : Stmt11_5_4) (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁)
    (hV₂ : IsVi T L I n 2 V₂) (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n)
    (hW : ¬ IsMulCommutative ↥(wH T I V₁)) {X : Subgroup G} (hX : IsCartanX T L X) {y : G}
    (hy : y ∈ L) (hopp : conjSubgroup V₁ y ⊓ V₃ = ⊥) :
    L ≤ (LOf L V₁ ⊔ conjSubgroup (wH T I V₁) y) ⊔ pCoreOf 2 (L ⊔ T) ∧
      L ≤ conjClosure (conjSubgroup (wH T I V₁) y) L ⊔ pCoreOf 2 (L ⊔ T) := by
  have hQ := fsuV_le_pCoreOf_normalizer hF h1102 h1103 h1141 h1143 h1154 h1156 h hV₁ hk
  have hC₃ := conjClosure_le_centralizer_V₃ hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁
    hV₂ hV₃ hk
  have hXW : X ≤ Subgroup.normalizer ((wH T I V₁ : Subgroup G) : Set G) :=
    (SecD.cartan_le_normalizer_V₁ hN h1102 h hV₁ hX).trans (le_normalizer_conjClosure _ _)
  exact hGen G T L I n V₁ V₃ X (SecD.natSetting11_of h1102 h1141 h hV₁) hk hV₁ hV₃ hX
    (wH T I V₁) ((conjClosure_le_pCoreOf hQ).trans (pCoreOf_normalizer_V₁_le_ROf h hV₁))
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hC₃))
    (commutator_fsuV_conjClosure_ne_bot hW) hXW y hy hopp

theorem pCoreOf_L_le (hF : Sp4Facts) (hGen : FactSp4Gen) (h13 : ASInputs.AS_I_1_3_Sp4)
    (hN : SecA.NatFacts) (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1113 : Stmt11_1_3)
    (h1141 : Stmt11_4_1) (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4) (h1156 : Stmt11_5_6)
    (h : Hyp11 G T L I n) (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂)
    (hV₃ : IsVi T L I n 3 V₃) (hk : KindSp4 L (fsuV T I) n) (hW : ¬ IsMulCommutative ↥(wH T I V₁))
    {X : Subgroup G} (hX : IsCartanX T L X) {y : G} (hy : y ∈ L)
    (hopp : conjSubgroup V₁ y ⊓ V₃ = ⊥)
    (hQ₁ : qOf T I V₁ y ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))) :
    pCoreOf 2 L ≤ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hset := SecD.natSetting11_of h1102 h1141 h hV₁
  have hQ := fsuV_le_pCoreOf_normalizer hF h1102 h1103 h1141 h1143 h1154 h1156 h hV₁ hk
  have hWQ₁ := conjClosure_le_pCoreOf hQ
  have hWT : wH T I V₁ ≤ T := hWQ₁.trans (pCoreOf_normalizer_V₁_le_T h hV₁)
  have hPC : pCoreOf 2 L ≤ Subgroup.centralizer (fsuV T I : Set G) := by
    rw [← SecA.centralizer_eq_pCoreOf h1102 h]
    exact inf_le_right
  have hLP : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
  have hTP : T ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    h.normal.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have hG₁Q₁ : Subgroup.normalizer (V₁ : Set G) ≤
      Subgroup.normalizer (pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hTQ₁ := (SecA.IsVi.le_normalizer hV₁).trans hG₁Q₁
  have hWyP : conjSubgroup (wH T I V₁) y ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := by
    intro w hw
    have hw' : y * w * y⁻¹ ∈ wH T I V₁ := mem_conjSubgroup_iff.mp hw
    have heq : w = y⁻¹ * (y * w * y⁻¹) * y := by group
    rw [heq]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hLP hy)) (hTP (hWT hw')))
      (hLP hy)
  have hPWy : pCoreOf 2 L ≤ Subgroup.normalizer ((conjSubgroup (wH T I V₁) y : Subgroup G) :
      Set G) := hPC.trans (centralizer_le_normalizer_conj_wH h hV₁ hy)
  have hPWyD : ⁅pCoreOf 2 L, conjSubgroup (wH T I V₁) y⁆ ≤
      pCoreOf 2 L ⊓ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) := by
    refine (commutator_le_inf_of_le_normalizer hPWy hWyP).trans (le_inf inf_le_left ?_)
    intro z hz
    exact hQ₁ (Subgroup.mem_sup_right ⟨hz.2, hPC hz.1⟩)
  have hD₁ : LOf L V₁ ≤ Subgroup.normalizer
      ((pCoreOf 2 L ⊓ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) : Subgroup G) : Set G) :=
    fun l hl => SecD.mem_normalizer_inf (hLP (((perfectCore_le _).trans inf_le_left) hl))
      (hG₁Q₁ (SecD.lOf_le_normalizer L V₁ hl))
  have hD₂ : conjSubgroup (wH T I V₁) y ≤ Subgroup.normalizer
      ((pCoreOf 2 L ⊓ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr
      ((Subgroup.commutator_mono inf_le_left le_rfl).trans hPWyD)
  have hD₃ : T ≤ Subgroup.normalizer
      ((pCoreOf 2 L ⊓ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) : Subgroup G) : Set G) :=
    fun t ht => SecD.mem_normalizer_inf (hTP ht) (hTQ₁ ht)
  have hOT : pCoreOf 2 (L ⊔ T) ≤ T := pCoreOf_le_of_sylow h.fsu.sylow le_sup_right
  obtain ⟨hGen₁, hGen₂⟩ := gen_wH hF hGen hN h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂
    hV₃ hk hW hX hy hopp
  have hLD := hGen₁.trans (sup_le (sup_le hD₁ hD₂) (hOT.trans hD₃))
  have hWyC : conjSubgroup (wH T I V₁) y ≤
      commSub (pCoreOf 2 L) (pCoreOf 2 L ⊓ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))) :=
    fun w hw => mem_commSub.mpr
      ⟨hD₂ hw, fun a ha => hPWyD (Subgroup.commutator_mem_commutator ha hw)⟩
  have hLC : L ≤ Subgroup.normalizer ((commSub (pCoreOf 2 L)
      (pCoreOf 2 L ⊓ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))) : Subgroup G) : Set G) :=
    fun l hl => mem_normalizer_commSub (hLP hl) (hLD hl)
  have hTC : T ≤ Subgroup.normalizer ((commSub (pCoreOf 2 L)
      (pCoreOf 2 L ⊓ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))) : Subgroup G) : Set G) :=
    fun t ht => mem_normalizer_commSub (hTP ht) (hD₃ ht)
  have hcl : conjClosure (conjSubgroup (wH T I V₁) y) L ≤
      commSub (pCoreOf 2 L) (pCoreOf 2 L ⊓ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G))) :=
    conjClosure_le fun g hg w hw => (Subgroup.mem_normalizer_iff.mp (hLC hg) w).mp (hWyC hw)
  have hLC' := le_of_le_sup_of_perfect (SecD.perfect_of_hyp11 h)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) (hOT.trans hTC)
    (hGen₂.trans (sup_le_sup_right hcl _))
  have hPL : ⁅pCoreOf 2 L, L⁆ ≤ pCoreOf 2 L ⊓ pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) := by
    rw [Subgroup.commutator_le]
    intro a ha l hl
    exact (mem_commSub.mp (hLC' hl)).2 a ha
  exact (le_of_eq (pCoreOf_eq_commutator h13 hset hk)).trans (hPL.trans inf_le_right)

end CFSG.Quasithin.Vol2.Ch11.SecF
