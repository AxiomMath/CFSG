module

public import CFSG.Quasithin.H13.L32AC43b

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped IsMulCommutative Pointwise

theorem mem_stabSub_of_inv' {X : Type*} [CommGroup X] {U : Subgroup X} {g : MulAut X}
    (h1 : ∀ u ∈ U, g u ∈ U) (h2 : ∀ u ∈ U, g⁻¹ u ∈ U) : g ∈ stabSub U := by
  intro u
  refine ⟨fun hu => ?_, fun hu => h1 u hu⟩
  have := h2 _ hu
  simpa using this

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace Top43

variable {W K : Subgroup G} (C : Top43 T L V H W K) [IsMulCommutative ↥(conjClosure V H)]
include C

theorem hexp (v : Hat V H W) : v ^ 2 = 1 := C.toTopW.hexp v

theorem autT_le_normalizer :
    C.autT ≤ Subgroup.normalizer (C.autK : Set (MulAut (Hat V H W))) :=
  C.toTopW.autOf_T_le_normalizer C.hKH C.hKn

theorem isPGroup_autT : IsPGroup 2 ↥C.autT := C.toTopW.isPGroup_autOf

theorem pCoreOf_autK (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    pCoreOf 2 C.autK = ⊥ :=
  C.toTopW.pCoreOf_autOf C.hKH C.hKn (C.pCoreOf_range h1222 h1332 h1334)

theorem commV_autK_ne_bot (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    commV C.autK ≠ ⊥ :=
  C.toTopW.commV_autOf_ne_bot (C.autK_ne_bot h1222 h1332 h1334)

theorem orbSup_eq_top {Vs : Subgroup (Hat V H W)} (hVs : Vs ∈ IrrPlus C.autK ⊤) :
    orbSup C.autT Vs = ⊤ := by
  obtain ⟨hinv, -, hlt, -⟩ := mem_irrPlus_top_iff.mp hVs
  set J := orbSup C.autT Vs with hJ
  have hT : C.autT ≤ stabSub J := le_stabSub_orbSup C.autT Vs
  have hKs : C.autK ≤ stabSub J := by
    have key : ∀ l ∈ C.autK, ∀ y ∈ J, l y ∈ J := by
      intro l hl y hy
      have hle : J.map l.toMonoidHom ≤ J := by
        rw [hJ, orbSup, Subgroup.map_iSup]
        refine iSup_le fun t => ?_
        rw [Subgroup.map_iSup]
        refine iSup_le fun ht => ?_
        rw [Subgroup.map_map]
        refine le_iSup₂_of_le t ht ?_
        rintro _ ⟨v, hv, rfl⟩
        refine ⟨(t⁻¹ * l * t) v, ?_, ?_⟩
        · have h1 : t⁻¹ * l * t ∈ C.autK := by
            have := (Subgroup.mem_normalizer_iff.mp
              (C.autT_le_normalizer (C.autT.inv_mem ht)) l).mp hl
            simpa using this
          exact hinv _ h1 v hv
        · show t ((t⁻¹ * l * t) v) = l (t v)
          simp [MulAut.mul_apply]
      exact hle ⟨y, hy, rfl⟩
    intro l hl
    exact mem_stabSub_of_inv' (key l hl) (key l⁻¹ (C.autK.inv_mem hl))
  have hR : C.act.range ≤ stabSub J := by
    rw [C.range_eq_sup]
    exact sup_le hKs hT
  have hH : ∀ h : ↥H, ∀ y ∈ J, C.act h y ∈ J := fun h y hy => (hR ⟨h, rfl⟩ y).mpr hy
  rcases C.irr J hH with h0 | h1
  · exfalso
    have hVJ : Vs ≤ J := fun v hv =>
      Subgroup.mem_iSup_of_mem 1 (Subgroup.mem_iSup_of_mem C.autT.one_mem ⟨v, hv, rfl⟩)
    rw [h0, le_bot_iff] at hVJ
    rw [hVJ] at hlt
    exact (lt_irrefl _ (lt_of_le_of_lt bot_le hlt)).elim
  · exact h1

theorem mem_pCoreOf_of_comm_act (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {B : Subgroup G} (hBT : B ≤ T) (b : ↥H) (hb : (b : G) ∈ B)
    (hc : ∀ k : ↥H, (k : G) ∈ K → C.act b * C.act k = C.act k * C.act b) :
    (b : G) ∈ pCoreOf 2 H :=
  C.mem_pCoreOf_of_commute h1222 h1332 h1334 (hBT hb) fun k hk => hc ⟨k, C.hKH hk⟩ hk

theorem qOff (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B) (hBT : B ≤ T) {Vs : Subgroup (Hat V H W)}
    (hVs : Vs ∈ IrrPlus C.autK ⊤) : QOff C.autK C.autT (C.autE B) (orbSup C.autT Vs) := by
  refine C.toTopW.qOff hB hBT (fun _ hf h => (C.mem_pCoreOf_iff_comm h1222 h1332 h1334
    (hBT hf)).mpr h) (C.mem_pCoreOf_of_comm_act h1222 h1332 h1334 hBT) ?_
  show C.autE B ⊓ centSub (orbSup C.autT Vs) = ⊥
  rw [C.orbSup_eq_top hVs, eq_bot_iff]
  intro a ha
  exact Subgroup.mem_bot.mpr (MulEquiv.ext fun v => ha.2 v (Subgroup.mem_top v))

theorem irr_or_d310Two (h310 : D310) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {B : Subgroup G} (hB : QCrit (fsuV1 T V) V H B) (hBT : B ≤ T) :
    (∀ J : Subgroup (Hat V H W), (∀ l ∈ C.autK, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤) ∨
      ∃ Vs : Subgroup (Hat V H W), D310Two C.autT C.autK Vs := by
  obtain ⟨Vs, hVs, hst | h2⟩ := C.toTopW.d310 h310 C.hK C.hKn C.hq
    (C.autK_ne_bot h1222 h1332 h1334) (C.pCoreOf_range h1222 h1332 h1334) hB hBT
    (fun _ hf h => (C.mem_pCoreOf_iff_comm h1222 h1332 h1334 (hBT hf)).mpr h)
    (C.mem_pCoreOf_of_comm_act h1222 h1332 h1334 hBT) fun Vs hVs =>
      (C.qOff h1222 h1332 h1334 hB hBT ⟨le_top, hVs.1.2⟩).faithVT
  · left
    have hVs1 : Vs ∈ IrrPlus C.autK ⊤ := ⟨le_top, hVs.1.2⟩
    obtain ⟨hinv, -, hlt, hirr⟩ := mem_irrPlus_top_iff.mp hVs1
    have hKs : C.autK ≤ stabSub Vs := fun l hl =>
      mem_stabSub_of_inv' (hinv l hl) (hinv l⁻¹ (C.autK.inv_mem hl))
    have hR : C.act.range ≤ stabSub Vs := by
      rw [C.range_eq_sup]
      exact sup_le hKs hst
    have hVtop : Vs = ⊤ := by
      rcases C.irr Vs (fun h y hy => (hR ⟨h, rfl⟩ y).mpr hy) with h0 | h1
      · exfalso
        rw [h0] at hlt
        exact (lt_irrefl _ (lt_of_le_of_lt bot_le hlt)).elim
      · exact h1
    have hfix : fixV C.autK = ⊥ := by
      have hH : ∀ h : ↥H, ∀ y ∈ fixV C.autK, C.act h y ∈ fixV C.autK := by
        intro h y hy l hl
        have hl' : (C.act h)⁻¹ * l * C.act h ∈ C.autK := by
          have := (Subgroup.mem_normalizer_iff.mp (C.range_le_normalizer
            (C.act.range.inv_mem ⟨h, rfl⟩)) l).mp hl
          simpa using this
        have := hy _ hl'
        calc l (C.act h y) = C.act h (((C.act h)⁻¹ * l * C.act h) y) := by
              simp [MulAut.mul_apply]
          _ = C.act h y := by rw [this]
      rcases C.irr _ hH with h0 | h1
      · exact h0
      · exfalso
        apply C.commV_autK_ne_bot h1222 h1332 h1334
        rw [eq_bot_iff]
        refine (Subgroup.closure_le _).mpr ?_
        rintro _ ⟨l, hl, v, rfl⟩
        have hv : v ∈ fixV C.autK := by rw [h1]; exact Subgroup.mem_top v
        rw [SetLike.mem_coe, hv l hl, mul_inv_cancel]
        exact Subgroup.one_mem _
    intro J hJ
    rw [hVtop, hfix, top_inf_eq] at hirr
    exact hirr J hJ bot_le le_top
  · exact Or.inr ⟨Vs, h2⟩

end Top43

end CFSG.Quasithin.H13.L32A.C
