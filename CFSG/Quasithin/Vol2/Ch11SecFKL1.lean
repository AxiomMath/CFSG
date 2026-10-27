module

public import CFSG.Quasithin.Vol2.Ch11SecFFacts2
public import CFSG.Quasithin.Vol2.Ch11SecFW

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecF

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G]

theorem commutator_le_of_perfect {V V₃ A : Subgroup G} (hV : IsMulCommutative ↥V)
    (hA : ⁅A, A⁆ = A) (hVA : ⁅V, A⁆ ≤ V₃) {w : G}
    (hw : ∀ a ∈ A, ⁅w, a⁆ ∈ V) : ∀ a ∈ A, ⁅w, a⁆ ∈ V₃ := by
  have hc : ∀ x y : ↥V, x * y = y * x := fun x y => hV.is_comm.comm x y
  set N : Subgroup ↥V := V₃.subgroupOf V with hNdef
  have hN : N.Normal := ⟨fun x hx g => by rwa [hc g x, mul_inv_cancel_right]⟩
  let f : ↥A →* ↥V ⧸ N :=
    { toFun := fun a => QuotientGroup.mk ⟨⁅w, (a : G)⁆, hw a a.2⟩
      map_one' := by
        rw [← QuotientGroup.mk_one]
        congr 1
        ext
        simp [commutatorElement_def]
      map_mul' := by
        intro a b
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, hNdef, Subgroup.mem_subgroupOf]
        have h1 : ⁅(a : G), ((⁅w, (b : G)⁆ : G))⁻¹⁆ ∈ V₃ := by
          refine hVA ?_
          rw [Subgroup.commutator_comm]
          exact Subgroup.commutator_mem_commutator a.2 (V.inv_mem (hw b b.2))
        convert h1 using 1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group }
  have hab : ∀ p q : ↥V ⧸ N, p * q = q * p := by
    intro p q
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective p
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hc]
  have hcA : commutator ↥A = ⊤ := by
    apply Subgroup.map_injective A.subtype_injective
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      hA]
  have hker : commutator ↥A ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hab _ _
  intro a ha
  have h1 : f ⟨a, ha⟩ = 1 := by
    rw [← MonoidHom.mem_ker]
    exact hker (hcA ▸ Subgroup.mem_top _)
  have h2 := (QuotientGroup.eq_one_iff _).mp h1
  rw [hNdef, Subgroup.mem_subgroupOf] at h2
  exact h2

variable [Finite G] {T L I : Subgroup G} {n : ℕ} {V₁ V₂ V₃ : Subgroup G}

theorem commutator_conjClosure_lOf_le (hF : Sp4Facts) (hZC : FactSp4ZCent) (hVL1 : FactSp4VL1)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1113 : Stmt11_1_3) (h1141 : Stmt11_4_1)
    (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4) (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂) (hV₃ : IsVi T L I n 3 V₃)
    (hk : KindSp4 L (fsuV T I) n) (hO : pCoreOf 2 L = fsuV T I) :
    ⁅conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)), LOf L V₁⁆ ≤ V₃ := by
  have hset := SecD.natSetting11_of h1102 h1141 h hV₁
  have hQ := fsuV_le_pCoreOf_normalizer hF h1102 h1103 h1141 h1143 h1154 h1156 h hV₁ hk
  set W := conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) with hWdef
  have hWT : W ≤ T := (conjClosure_le_pCoreOf hQ).trans (pCoreOf_normalizer_V₁_le_T h hV₁)
  have hWR : W ≤ ROf T L V₁ :=
    (conjClosure_le_pCoreOf hQ).trans (pCoreOf_normalizer_V₁_le_ROf h hV₁)
  have hV₃W : ⁅V₃, W⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, ← Subgroup.le_centralizer_iff]
    exact conjClosure_le_centralizer_V₃ hF h1102 h1103 h1113 h1141 h1143 h1154 h1156 h hV₁ hV₂
      hV₃ hk
  have hL₁L : LOf L V₁ ≤ L := (perfectCore_le _).trans inf_le_left
  have hWL₁ : W ≤ Subgroup.normalizer (LOf L V₁ : Set G) := fun w hw =>
    SecD.mem_normalizer_lOf (h.normal (hWT hw)) (SecA.IsVi.le_normalizer hV₁ (hWT hw))
  have hL₁W : LOf L V₁ ≤ Subgroup.normalizer (W : Set G) :=
    (SecD.lOf_le_normalizer L V₁).trans (le_normalizer_conjClosure _ _)
  have hWV : ⁅W, LOf L V₁⁆ ≤ fsuV T I := by
    rw [← hO, ← SecA.centralizer_eq_pCoreOf h1102 h]
    exact le_inf ((commutator_le_inf_of_le_normalizer hWL₁ hL₁W).trans (inf_le_right.trans hL₁L))
      (hZC G T L I n V₁ V₃ hset hk hV₁ hV₃ W hWR hV₃W)
  rw [Subgroup.commutator_le]
  intro w hw a ha
  exact commutator_le_of_perfect (SecA.isElemAbelian_fsuV h).1 (perfectCore_perfect _)
    (hVL1 G T L I n V₁ V₃ hset hk hV₁ hV₃)
    (fun b hb => hWV (Subgroup.commutator_mem_commutator hw hb)) a ha

theorem commutator_conjClosure_kOf_le (hF : Sp4Facts) (hZC : FactSp4ZCent) (hVL1 : FactSp4VL1)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (h1113 : Stmt11_1_3) (h1141 : Stmt11_4_1)
    (h1143 : Stmt11_4_3) (h1154 : Stmt11_5_4) (h1156 : Stmt11_5_6) (h : Hyp11 G T L I n)
    (hV₁ : IsVi T L I n 1 V₁) (hV₂ : IsVi T L I n 2 V₂) (hV₃ : IsVi T L I n 3 V₃)
    (hk : KindSp4 L (fsuV T I) n) (hO : pCoreOf 2 L = fsuV T I) :
    ⁅conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)), KOf L V₁ V₁⁆ ≤
      conjClosure V₃ (Subgroup.normalizer (V₁ : Set G)) := by
  have h1 := commutator_conjClosure_lOf_le hF hZC hVL1 h1102 h1103 h1113 h1141 h1143 h1154 h1156
    h hV₁ hV₂ hV₃ hk hO
  set W := conjClosure (fsuV T I) (Subgroup.normalizer (V₁ : Set G)) with hWdef
  set U := conjClosure V₃ (Subgroup.normalizer (V₁ : Set G)) with hUdef
  have hG₁U : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_conjClosure _ _
  have hG₁W : Subgroup.normalizer (V₁ : Set G) ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_conjClosure _ _
  have hK : KOf L V₁ V₁ ≤ commSub W U := by
    refine conjClosure_le fun g hg l hl => mem_commSub.mpr ⟨hG₁U (Subgroup.mul_mem _
      (Subgroup.mul_mem _ hg (SecD.lOf_le_normalizer L V₁ hl)) (Subgroup.inv_mem _ hg)),
      fun w hw => ?_⟩
    have hw' : g⁻¹ * w * g ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp (hG₁W (Subgroup.inv_mem _ hg)) w).mp hw
      simpa using this
    have hc : ⁅g⁻¹ * w * g, l⁆ ∈ V₃ := h1 (Subgroup.commutator_mem_commutator hw' hl)
    have heq : ⁅w, g * l * g⁻¹⁆ = g * ⁅g⁻¹ * w * g, l⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [heq]
    exact mem_conjClosure hg hc
  rw [Subgroup.commutator_le]
  intro w hw k hk
  exact (mem_commSub.mp (hK hk)).2 w hw

end CFSG.Quasithin.Vol2.Ch11.SecF
