module

public import CFSG.Quasithin.Background.SzG11SStmts
public import CFSG.Quasithin.Background.SzG11STensor
public import CFSG.Quasithin.Background.G118F4
public import CFSG.Quasithin.Background.G118Glue
public import CFSG.Quasithin.Background.G118Scan
public import CFSG.Quasithin.Background.G118Data
public import CFSG.Quasithin.Background.G117NoE9
public import CFSG.Quasithin.Background.G118Apply
public import CFSG.Quasithin.Background.G118Concl9
public import CFSG.Quasithin.Background.G118Dim
public import CFSG.Quasithin.Background.G118Hyp
public import CFSG.Quasithin.Background.G93ApplyStmt

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

namespace SzG11S

open CFSG.Quasithin.G11.G118

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

namespace G118

section Dim

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem not_fixedSpace_imp (hs : G11Setup B Γ v₁ W X X₀ L) (hI : G116Props B Γ v₁ X L I)
    (hItop : I ≠ ⊤) (hB : fixedSpace X ≠ Submodule.span (ZMod 2) {v₁}) :
    Module.finrank (ZMod 2) V = 2 * Module.finrank (ZMod 2) I ∧
      EndTrivial (normalClosure Γ L) I := by
  have h108 := hs.h108
  have hthree := hs.cx.hyp.three
  rcases hthree with hleft | ⟨a, haX, hrank, hv₁a⟩
  · exfalso
    apply hB
    refine le_antisymm (fun v hv => ?_) (Submodule.span_le.2 ?_)
    · rcases hleft v hv with h0 | h1
      · rw [h0]
        exact Submodule.zero_mem _
      · rw [h1]
        exact Submodule.subset_span rfl
    · intro v hv
      rw [Set.mem_singleton_iff] at hv
      rw [hv]
      exact h108.toG101Hyp.X_fixes
  · have ha1 : a ≠ 1 := by
      rintro rfl
      have : (v₁ : V) ∈ LinearMap.range ((1 : GLV V).toLinearMap - LinearMap.id) := hv₁a
      obtain ⟨u, hu⟩ := this
      apply h108.toG101Hyp.point
      rw [← hu]
      simp
    have hcomm := h108.exists_noncomm ha1 hrank
    have hfaith : ∀ J, IsIrr (normalClosure Γ L) J → FaithfulOn (normalClosure Γ L) J :=
      fun J hJ => faithful_all h108 hI hJ
    have ha' : ∀ h ∈ normalClosure Γ L, a⁻¹ * h * a ∈ normalClosure Γ L := by
      intro h hh
      have := normalClosure_normal Γ L a⁻¹ (Γ.inv_mem (h108.X_le haX)) h hh
      simpa using this
    rcases h108.irr_or_two haX hrank hcomm hfaith with
      hirr | ⟨J₁, J₂, hc, hJ₁, hJ₂, haJ₁, haJ₂, hr₁, hr₂⟩
    · exfalso
      rcases hirr.eq_bot_or_eq hI.irrPlus.1 le_top with h0 | h1
      · exact (isIrr_I h108 hI).ne_bot h0
      · exact hItop h1
    · have h1 := finrank_eq_of_isIrr h108 hI hJ₁
      have h2 := finrank_eq_of_isIrr h108 hI hJ₂
      have h3 := Submodule.finrank_add_eq_of_isCompl hc
      refine ⟨by omega, ?_⟩
      have hNT := endTrivial_of_finrank_raU_eq_one hJ₁ (by
        have := h108.two_lt_finrank hJ₁
        omega) haJ₁ ha' hr₁
      exact endTrivial_of_hIso hI.irrPlus.1
        (hI.homogeneous J₁ I (hJ₁.irrPlus h108.fixedSpace_H) hI.irrPlus) hNT

end Dim

end G118

end SzG11S

end G11

end CFSG.Quasithin

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

namespace SzG11S

open CFSG.Quasithin.G11.G118

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

namespace G118

section K2

variable [Finite V] {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem exists_mem_W_not_mem_I (hs : G11Setup B Γ v₁ W X X₀ L) (hI : G116Props B Γ v₁ X L I)
    (D : E11Data (normalClosure Γ L) I)
    (hd : Module.finrank (ZMod 2) V = 2 * Module.finrank (ZMod 2) I)
    (hnonE : ¬ EndTrivial (normalClosure Γ L) I) {y₀ : GLV V}
    (hy₀ : y₀ ∈ centralizerIn X (normalClosure Γ L)) (hy₀1 : y₀ ≠ 1) :
    ∃ w ∈ W, w ∉ I := by
  by_contra hWI
  push Not at hWI
  have h108 := hs.h108
  have hG := h108.toG101Hyp
  obtain ⟨hy₀X, hy₀c⟩ := mem_centralizerIn_iff.1 hy₀
  have hy₀I := fixes_of_mem_centralizerIn h108 hI hy₀
  have hy₀2 : y₀ * y₀ = 1 := h108.X_sq y₀ hy₀X
  have hI0 : 0 < Module.finrank (ZMod 2) I := by
    obtain ⟨i, hi, hi0⟩ := (Submodule.ne_bot_iff I).1 (isIrr_I h108 hI).ne_bot
    exact Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨i, hi⟩, fun h => hi0 (congrArg Subtype.val h)⟩
  have hker := ker_sub_one_eq_of_mem D hd hI0 hy₀c hy₀I hy₀1
  have hrange := range_sub_one_eq_of_mem D hd hI0 hy₀2 hy₀c hy₀I hy₀1
  obtain ⟨x, hxX, l, hl, hxl⟩ := h108.noncomm
  have hxI : ∃ i ∈ I, x i ≠ i := by
    by_contra hall
    push Not at hall
    apply hxl
    exact (centralizerIn_iff h108 hI hxX).2 hall l (le_normalClosure Γ L hl)
  obtain ⟨v₀, hv₀⟩ : ∃ v₀ : V, B v₁ v₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hG.point (hG.nondegenerate v₁ hall)
  have hv₀1 : B v₁ v₀ = 1 := by
    rcases zmod2_eq_zero_or_one (B v₁ v₀) with h | h
    · exact absurd h hv₀
    · exact h
  have hxy : x * y₀ = y₀ * x := hG.X_comm x hxX y₀ hy₀X
  set r₀ : V := y₀ (x v₀ - v₀) - (x v₀ - v₀) with hr₀
  have hR : raU x I ≤ Submodule.span (ZMod 2) {r₀} := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := mem_raU.1 hw
    have hi' : i ∈ LinearMap.range (y₀.toLinearMap - LinearMap.id) := by
      rw [hrange]
      exact hi
    obtain ⟨u, rfl⟩ := hi'
    set ε : ZMod 2 := B v₁ u with hε
    have hPmem : B v₁ (u + ε • v₀) = 0 := by
      rw [map_add, map_smul, hv₀1, smul_eq_mul, mul_one]
      have : ∀ a : ZMod 2, a + a = 0 := by decide
      exact this ε
    have hW1 : x (u + ε • v₀) - (u + ε • v₀) ∈ W := hG.commutator_le x hxX _ hPmem
    have he : x (u + ε • v₀) - (u + ε • v₀) ∈ I := hWI _ hW1
    have hy1 : (y₀ : GLV V) (x (u + ε • v₀) - (u + ε • v₀)) = x (u + ε • v₀) - (u + ε • v₀) :=
      (hker _).2 he
    have hcomm : ∀ z : V, x (y₀ z) = y₀ (x z) := fun z => congrArg (fun g : GLV V => g z) hxy
    have e1 : x (y₀ u - u) - (y₀ u - u) = y₀ (x u - u) - (x u - u) := by
      simp only [map_sub, hcomm]
      abel
    have e2 : x (u + ε • v₀) - (u + ε • v₀) = (x u - u) + ε • (x v₀ - v₀) := by
      rw [map_add, map_smul]
      module
    have hexp : x (y₀ u - u) - (y₀ u - u) = -(ε • r₀) := by
      rw [e2] at hy1
      rw [map_add, map_smul] at hy1
      have h3 : y₀ (x u - u) = (x u - u) + ε • (x v₀ - v₀) - ε • y₀ (x v₀ - v₀) := by
        rw [eq_sub_iff_add_eq]
        exact hy1
      rw [e1, h3, hr₀]
      module
    show x (y₀ u - u) - (y₀ u - u) ∈ _
    rw [hexp]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span rfl))
  have hrk1 : Module.finrank (ZMod 2) ↥(raU x I) ≤ 1 := by
    have h1 := Submodule.finrank_mono hR
    have h2 : Module.finrank (ZMod 2) ↥(Submodule.span (ZMod 2) {r₀}) ≤ 1 := by
      have := finrank_span_le_card (R := ZMod 2) ({r₀} : Set V)
      simpa using this
    omega
  have hne : raU x I ≠ ⊥ := by
    intro hbot
    obtain ⟨i, hi, hxi⟩ := hxI
    exact hxi ((raU_eq_bot_iff.1 hbot) i hi)
  have hrk : Module.finrank (ZMod 2) ↥(raU x I) = 1 := by
    have := Submodule.one_le_finrank_iff.2 hne
    omega
  have ha' : ∀ h ∈ normalClosure Γ L, x⁻¹ * h * x ∈ normalClosure Γ L := by
    intro h hh
    have := normalClosure_normal Γ L x⁻¹ (Γ.inv_mem (h108.X_le hxX)) h hh
    simpa using this
  exact hnonE (endTrivial_of_finrank_raU_eq_one (isIrr_I h108 hI)
    (h108.two_lt_finrank (isIrr_I h108 hI)) (hI.invariant_X.conjSub_eq hxX) ha' hrk)

theorem card_centralizerIn_eq_two_of_not_endTrivial (hs : G11Setup B Γ v₁ W X X₀ L)
    (hI : G116Props B Γ v₁ X L I) (hnf : ¬ FaithfulOn X I) (D : E11Data (normalClosure Γ L) I)
    (hd : Module.finrank (ZMod 2) V = 2 * Module.finrank (ZMod 2) I)
    (hnonE : ¬ EndTrivial (normalClosure Γ L) I) :
    Nat.card ↥(centralizerIn X (normalClosure Γ L)) = 2 := by
  have h108 := hs.h108
  have hG := h108.toG101Hyp
  obtain ⟨y₀, hy₀, hy₀1⟩ := exists_mem_centralizerIn_ne_one h108 hI hnf
  obtain ⟨w, hwW, hwI⟩ := exists_mem_W_not_mem_I hs hI D hd hnonE hy₀ hy₀1
  have hker := fun {y : GLV V} (hy : y ∈ centralizerIn X (normalClosure Γ L)) (hy1 : y ≠ 1) =>
    ker_eq_of_mem_centralizerIn h108 hI D hd hy hy1
  have hyw : ∀ y ∈ centralizerIn X (normalClosure Γ L), y ≠ 1 → y w = w + v₁ := by
    intro y hy hy1
    obtain ⟨f, hf0, hf⟩ := hG.transvection y (mem_centralizerIn_iff.1 hy).1
    have hyw := hf ⟨w, hwW⟩
    rcases zmod2_eq_zero_or_one (f ⟨w, hwW⟩) with h0 | h1
    · exfalso
      rw [h0, zero_smul, add_zero] at hyw
      exact hwI ((hker hy hy1 w).1 hyw)
    · rw [h1, one_smul] at hyw
      exact hyw
  have huniq : ∀ y ∈ centralizerIn X (normalClosure Γ L), y ≠ 1 → y = y₀ := by
    intro y hy hy1
    by_contra hne
    have hyy : y * y₀ ∈ centralizerIn X (normalClosure Γ L) :=
      Subgroup.mul_mem _ hy hy₀
    have hyy1 : y * y₀ ≠ 1 := by
      intro h1
      apply hne
      have h2 : y₀ * y₀ = 1 := h108.X_sq y₀ (mem_centralizerIn_iff.1 hy₀).1
      calc y = y * (y₀ * y₀) := by rw [h2, mul_one]
        _ = (y * y₀) * y₀ := by rw [mul_assoc]
        _ = y₀ := by rw [h1, one_mul]
    have hfix : (y * y₀) w = w := by
      show y (y₀ w) = w
      rw [hyw y₀ hy₀ hy₀1, map_add, hyw y hy hy1, hG.X_fixes y (mem_centralizerIn_iff.1 hy).1]
      have : ∀ a : V, a + v₁ + v₁ = a := fun a => by
        rw [add_assoc, ← two_smul (ZMod 2) v₁]
        have h2 : (2 : ZMod 2) = 0 := by decide
        rw [h2, zero_smul, add_zero]
      exact this w
    exact hwI ((hker hyy hyy1 w).1 hfix)
  rw [Nat.card_eq_two_iff' (1 : ↥(centralizerIn X (normalClosure Γ L)))]
  refine ⟨⟨y₀, hy₀⟩, fun h => hy₀1 (congrArg Subtype.val h), ?_⟩
  intro z hz
  have hz1 : (z : GLV V) ≠ 1 := fun h => hz (Subtype.ext h)
  exact Subtype.ext (huniq z z.2 hz1)

end K2

end G118

end SzG11S

end G11

end CFSG.Quasithin

namespace CFSG.Quasithin

open CFSG.Open
open scoped Pointwise

namespace G11

namespace SzG11S

open CFSG.Quasithin.G11.G118

namespace G118

variable {G : Type*} [Group G]

section Apply

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem g118_apply (hs : G11Setup B Γ v₁ W X X₀ L) (hI : G116Props B Γ v₁ X L I)
    (hA : G93ApplyStmt) (hY2 : Nat.card ↥(centralizerIn X (normalClosure Γ L)) = 2)
    (hd : Module.finrank (ZMod 2) V = 2 * Module.finrank (ZMod 2) I) :
    ∃ (m : ℕ) (hKI : Invariant (normalClosure Γ L ⊔ X) I)
      (hHI : Invariant (normalClosure Γ L) I),
      Nat.card X = 2 ^ (m + 1) ∧ Module.finrank (ZMod 2) I ≤ m + 2 ∧
      G93ConclDimensionOnly (restrictRange (normalClosure Γ L ⊔ X) I hKI)
        (restrictRange (normalClosure Γ L) I hHI) m ∧
      ∃ A : Subgroup (GLV V), A ≤ X ∧ A ⊔ centralizerIn X (normalClosure Γ L) = X ∧
        FaithfulOn A I ∧ Nat.card A = 2 ^ m := by
  have h108 := hs.h108
  have hG := h108.toG101Hyp
  set H := normalClosure Γ L with hH
  set Y := centralizerIn X H with hYdef
  have hYX : Y ≤ X := inf_le_left
  obtain ⟨A, hAX, hAY, hAsup⟩ :=
    exists_complement_of_isElemTwo (E := X) (F := Y) hG.X_comm hG.X_sq hYX
  have hAcomm : ∀ a ∈ A, ∀ y ∈ Y, a * y = y * a := fun a ha y hy =>
    hG.X_comm a (hAX ha) y (hYX hy)
  have hA2 : IsPGroup 2 A := fun g => ⟨1, by
    have := hG.X_sq g (hAX g.2)
    rw [pow_one, pow_two]
    exact Subtype.ext this⟩
  obtain ⟨m, hm⟩ := hA2.exists_card_eq
  have hXcard : Nat.card X = 2 ^ (m + 1) := by
    have hdisj : Disjoint (A.subgroupOf X) (Y.subgroupOf X) := by
      rw [disjoint_iff]
      have : A.subgroupOf X ⊓ Y.subgroupOf X = (A ⊓ Y).subgroupOf X :=
        (Subgroup.comap_inf A Y X.subtype).symm
      rw [this, hAY, Subgroup.bot_subgroupOf]
    have hmul : ((A.subgroupOf X : Subgroup ↥X) : Set ↥X) *
        ((Y.subgroupOf X : Subgroup ↥X) : Set ↥X) = Set.univ := by
      refine Set.eq_univ_of_forall fun g => ?_
      have hg : (g : GLV V) ∈ A ⊔ Y := by
        rw [hAsup]
        exact g.2
      obtain ⟨a, ha, y, hy, hgay⟩ := mem_sup_of_commute' hAcomm hg
      refine ⟨⟨a, hAX ha⟩, ha, ⟨y, hYX hy⟩, hy, ?_⟩
      exact Subtype.ext hgay.symm
    have hcompl := Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisj hmul
    have hcard := hcompl.card_mul_card
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX).toEquiv, hm, hY2] at hcard
    rw [← hcard, pow_succ]
  have hAfaith : FaithfulOn A I := by
    refine faithfulOn_iff.2 fun a haA haI => ?_
    have haY : a ∈ Y := mem_centralizerIn_of_fixes h108 hI (hAX haA) haI
    have : a ∈ A ⊓ Y := ⟨haA, haY⟩
    rw [hAY, Subgroup.mem_bot] at this
    exact this
  refine ⟨m, hI.irrPlus.1.sup_subgroup hI.invariant_X, hI.irrPlus.1, hXcard, ?_, ?_,
    A, hAX, hAsup, hAfaith, hm⟩
  · have := dim_le_of_card_X h108 hXcard
    omega
  · have hKΓ : H ⊔ X ≤ Γ := sup_le h108.H_le h108.X_le
    refine hA V Γ (H ⊔ X) H L A I m (hI.irrPlus.1.sup_subgroup hI.invariant_X) hI.irrPlus.1
      hs.cx.sqtk hKΓ le_sup_left (fun k hk h hh => normalClosure_normal Γ L k (hKΓ hk) h hh)
      (isIrr_I h108 hI) hI.faithful (hAX.trans le_sup_right) ?_ hm ?_ ?_ h108.component
      (le_normalClosure Γ L) ?_ (g118_hEq h108.component hs.numConj h108.fixedSpace_H
        hI.homogeneous hI.irrPlus hI.faithful)
    · exact ⟨⟨⟨fun a b => Subtype.ext (hG.X_comm a (hAX a.2) b (hAX b.2))⟩⟩, fun x hx => by
        rw [pow_two]
        exact hG.X_sq x (hAX hx)⟩
    · exact hAfaith
    · have := dim_le_of_card_X h108 hXcard
      omega
    · obtain ⟨x, hxX, l, hl, hxl⟩ := h108.noncomm
      have hx : x ∈ A ⊔ Y := by
        rw [hAsup]
        exact hxX
      obtain ⟨a, ha, y, hy, rfl⟩ := mem_sup_of_commute' hAcomm hx
      refine ⟨a, ha, l, hl, fun hal => hxl ?_⟩
      have hyl : y * l = l * y := ((mem_centralizerIn_iff.1 hy).2 l (le_normalClosure Γ L hl))
      calc a * y * l = a * (y * l) := by rw [mul_assoc]
        _ = a * (l * y) := by rw [hyl]
        _ = (a * l) * y := by rw [mul_assoc]
        _ = (l * a) * y := by rw [hal]
        _ = l * (a * y) := by rw [mul_assoc]

end Apply

end G118

end SzG11S

end G11

end CFSG.Quasithin

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

namespace SzG11S

open CFSG.Quasithin.G11.G118

namespace G118

section NoNormal

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)}

theorem centΓ_noNormalTwo (hs : G11Setup B Γ v₁ W X X₀ L) :
    ∀ N : Subgroup ↥(centΓ Γ (normalClosure Γ L)), N.Normal → IsPGroup 2 N → N = ⊥ := by
  have h108 := hs.h108
  have hN := normalClosure_normal Γ L
  set C := centΓ Γ (normalClosure Γ L) with hC
  have hCΓ : C ≤ Γ := inf_le_left
  have hO2Γ : pCoreOf 2 Γ = ⊥ := pCoreOf_eq_bot_of_isIrr_top h108.irreducible
  have hO2C : pCoreOf 2 C = ⊥ :=
    eq_bot_iff.2 ((pCoreOf_two_le_of_normalizer hCΓ (le_normalizer_centΓ hN)).trans hO2Γ.le)
  intro N hNn hNp
  have h1 : N ≤ CFSG.Open.pCore 2 ↥C := CFSG.LieType.BorelTits.le_pCore 2 hNn hNp
  have h2 : N.map C.subtype ≤ pCoreOf 2 C := Subgroup.map_mono h1
  rw [hO2C] at h2
  rw [eq_bot_iff]
  intro n hn
  have h3 : (n : GLV V) ∈ N.map C.subtype := ⟨n, hn, rfl⟩
  have h4 := h2 h3
  rw [Subgroup.mem_bot] at h4 ⊢
  exact Subtype.ext h4

end NoNormal

section F2

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem f2_S3 (hs : G11Setup B Γ v₁ W X X₀ L) (hI : G116Props B Γ v₁ X L I)
    (hnf : ¬ FaithfulOn X I) (D : E11Data (normalClosure Γ L) I)
    (hk : Module.finrank D.F D.U = 2) (hF : Nat.card D.F = 2) :
    Nonempty (↥(centΓ Γ (normalClosure Γ L)) ≃* Equiv.Perm (Fin 3)) ∧
      ∃ c y : GLV V, c ∈ centΓ Γ (normalClosure Γ L) ∧ y ∈ centΓ Γ (normalClosure Γ L) ∧
        y * y = 1 ∧ y ≠ 1 ∧ c ^ 3 = 1 ∧ c ≠ 1 ∧ y * c * y⁻¹ = c⁻¹ := by
  have h108 := hs.h108
  have hN := normalClosure_normal Γ L
  set C := centΓ Γ (normalClosure Γ L) with hC
  have hCΓ : C ≤ Γ := inf_le_left
  obtain ⟨y₀, hy₀, hy₀1⟩ := exists_mem_centralizerIn_ne_one h108 hI hnf
  have hy₀X := (mem_centralizerIn_iff.1 hy₀).1
  have hy₀C : y₀ ∈ C := mem_centΓ_iff.2 ⟨h108.X_le hy₀X, fun h hh =>
    ((mem_centralizerIn_iff.1 hy₀).2 h hh).symm⟩
  have hy₀2 : y₀ * y₀ = 1 := h108.X_sq y₀ hy₀X
  have hC6dvd : Nat.card C ∣ 6 := by
    have h1 : C ≤ Subgroup.centralizer (normalClosure Γ L : Set (GLV V)) := inf_le_right
    have := Subgroup.card_dvd_of_le h1
    rwa [card_centralizer_eq_six D hk hF] at this
  have hO2Γ : pCoreOf 2 Γ = ⊥ := pCoreOf_eq_bot_of_isIrr_top h108.irreducible
  have hO2C : pCoreOf 2 C = ⊥ :=
    eq_bot_iff.2 ((pCoreOf_two_le_of_normalizer hCΓ (le_normalizer_centΓ hN)).trans hO2Γ.le)
  have hC2 : ¬ IsPGroup 2 ↥C := by
    intro hp
    have hnorm : (C.subgroupOf C).Normal := by
      rw [Subgroup.subgroupOf_self]
      exact Subgroup.normal_top
    have hle : C ≤ pCoreOf 2 C := CFSG.LieType.BorelTits.le_pCoreOf 2 le_rfl hnorm hp
    rw [hO2C] at hle
    exact hy₀1 (by have := hle hy₀C; rwa [Subgroup.mem_bot] at this)
  have hy₀ord : orderOf y₀ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy₀2) hy₀1
  have h2dvd : 2 ∣ Nat.card C := by
    have := Subgroup.orderOf_dvd_natCard C hy₀C
    rwa [hy₀ord] at this
  have hC6 : Nat.card C = 6 := by
    have hmem : Nat.card C ∈ Nat.divisors 6 := by simp [hC6dvd]
    have hdiv : Nat.divisors 6 = {1, 2, 3, 6} := by decide
    rw [hdiv] at hmem
    simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
    rcases hmem with h1 | h2 | h3 | h6
    · exfalso
      have : C = ⊥ := Subgroup.card_eq_one.1 h1
      rw [this] at hy₀C
      exact hy₀1 (Subgroup.mem_bot.1 hy₀C)
    · exfalso
      exact hC2 (IsPGroup.of_card (n := 1) (by rw [h2]; norm_num))
    · exfalso
      rw [h3] at h2dvd
      omega
    · exact h6
  have hno := centΓ_noNormalTwo hs
  have hy2 : (⟨y₀, hy₀C⟩ : ↥C) * ⟨y₀, hy₀C⟩ = 1 := Subtype.ext hy₀2
  have hy1 : (⟨y₀, hy₀C⟩ : ↥C) ≠ 1 := fun h => hy₀1 (congrArg Subtype.val h)
  obtain ⟨c, hc3, hc1, hyc⟩ := g118_exists_inverting hC6 hy2 hy1 hno
  obtain ⟨e⟩ := g118_mulEquiv_perm_three hC6 hy2 hy1 hc3 hc1 hyc
  refine ⟨⟨e⟩, (c : GLV V), y₀, c.2, hy₀C, hy₀2, hy₀1, ?_, ?_, ?_⟩
  · exact congrArg Subtype.val hc3
  · exact fun h => hc1 (Subtype.ext h)
  · exact congrArg Subtype.val hyc

theorem f2_false_big (hs : G11Setup B Γ v₁ W X X₀ L) (hI : G116Props B Γ v₁ X L I)
    (hnf : ¬ FaithfulOn X I) (D : E11Data (normalClosure Γ L) I)
    (hk : Module.finrank D.F D.U = 2) (hF : Nat.card D.F = 2) {n : ℕ} (hn : n = 6 ∨ n = 8)
    (φ : ↥(normalClosure Γ L) ≃* ↥(alternatingGroup (Fin n))) : False := by
  have h108 := hs.h108
  obtain ⟨-, c, y, hcC, hyC, hy2, hy1, hc3, hc1, hyc⟩ := f2_S3 hs hI hnf D hk hF
  obtain ⟨a, b, hab, ha3, hb3, ha1, hb1, hba, hba2⟩ := g118_exists_E9_alt hn
  set a' : ↥(normalClosure Γ L) := φ.symm a with ha'
  set b' : ↥(normalClosure Γ L) := φ.symm b with hb'
  have hab' : a' * b' = b' * a' := by rw [ha', hb', ← map_mul, ← map_mul, hab]
  have ha3' : a' ^ 3 = 1 := by rw [ha', ← map_pow, ha3, map_one]
  have hb3' : b' ^ 3 = 1 := by rw [hb', ← map_pow, hb3, map_one]
  have ha1' : a' ≠ 1 := fun h => ha1 (φ.symm.injective (by rw [← ha', h, map_one]))
  have hb1' : b' ≠ 1 := fun h => hb1 (φ.symm.injective (by rw [← hb', h, map_one]))
  have hba' : b' ≠ a' := fun h => hba (φ.symm.injective h)
  have hba2' : b' ≠ a' ^ 2 := fun h => hba2 (φ.symm.injective (by rw [← hb', h, ha', map_pow]))
  obtain ⟨E, hE, haE, hbE, hcomm, hexp, hnc⟩ := exists_noncyclic_exp3
    (a := (a' : GLV V)) (b := (b' : GLV V)) (congrArg Subtype.val hab')
    (by simpa using congrArg Subtype.val ha3') (by simpa using congrArg Subtype.val hb3')
    (fun h => ha1' (Subtype.ext h)) (fun h => hb1' (Subtype.ext h))
    (fun h => hba' (Subtype.ext h))
    (fun h => hba2' (Subtype.ext (by simpa using h)))
  have hEH : E ≤ normalClosure Γ L := by
    rw [hE]
    refine (Subgroup.closure_le _).2 ?_
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact a'.2
    · exact b'.2
  have hyc' := (mem_centΓ_iff.1 hyC)
  have hcc' := (mem_centΓ_iff.1 hcC)
  exact G117.no_S3_noncyclic hs.cx.sqtk hyc'.1 hcc'.1 (hEH.trans h108.H_le) hy2 hy1 hc3 hc1 hyc
    hcomm hexp hnc (fun e he => hyc'.2 e (hEH he)) (fun e he => hcc'.2 e (hEH he))

theorem f2_false_A5 (hs : G11Setup B Γ v₁ W X X₀ L) (hI : G116Props B Γ v₁ X L I)
    (hnf : ¬ FaithfulOn X I) (D : E11Data (normalClosure Γ L) I)
    (hk : Module.finrank D.F D.U = 2) (hF : Nat.card D.F = 2)
    (hd : Module.finrank (ZMod 2) V = 8)
    (φ : ↥(normalClosure Γ L) ≃* ↥(alternatingGroup (Fin 5))) (hAut : AutA5Input) : False := by
  have h108 := hs.h108
  obtain ⟨⟨e⟩, -⟩ := f2_S3 hs hI hnf D hk hF
  have h9 := g118_concl9_of_S3 (G := GLV V) h108.H_le (normalClosure_normal Γ L) φ e hAut
  have h9' : G112Concl9 Γ := ⟨hd, by
    rcases h9 with h | h
    · exact Or.inl h
    · exact Or.inr h⟩
  apply hs.cx.notConcl
  refine Or.inl ?_
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9'))))))))

end F2

end G118

end SzG11S

end G11

end CFSG.Quasithin

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

namespace G11

namespace SzG11S

open CFSG.Quasithin.G11.G118

namespace G118

section F4Basic

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem exists_not_comm_kappa (hs : G11Setup B Γ v₁ W X X₀ L) (D : E11Data (normalClosure Γ L) I)
    (hF : Nat.card D.F = 4) (hB : fixedSpace X = Submodule.span (ZMod 2) {v₁}) :
    ∃ x ∈ X, ¬ ∀ f : D.F, (x : Module.End (ZMod 2) V) * D.κ f =
      D.κ f * (x : Module.End (ZMod 2) V) := by
  by_contra hcon
  have hall : ∀ y ∈ X, ∀ f : D.F, (y : Module.End (ZMod 2) V) * D.κ f =
      D.κ f * (y : Module.End (ZMod 2) V) := by
    intro y hy f
    by_contra hne
    exact hcon ⟨y, hy, fun h => hne (h f)⟩
  have hdvd := D.finrank_dvd_fixedSpace X hall
  rw [hB, finrank_span_singleton hs.h108.toG101Hyp.point,
    finrank_eq_two_of_card_four D hF] at hdvd
  omega

section Dichotomy

theorem f4_dichotomy (hs : G11Setup B Γ v₁ W X X₀ L) (hI : G116Props B Γ v₁ X L I)
    (hnf : ¬ FaithfulOn X I) (D : E11Data (normalClosure Γ L) I)
    (hk : Module.finrank D.F D.U = 2) (hF : Nat.card D.F = 4)
    (hB : fixedSpace X = Submodule.span (ZMod 2) {v₁}) (hD4 : GL24SubInput) :
    Nonempty (↥(centΓ Γ (normalClosure Γ L)) ≃* Equiv.Perm (Fin 3)) ∨
    Nonempty (↥(centΓ Γ (normalClosure Γ L)) ≃* ↥(alternatingGroup (Fin 5))) ∨
    ∃ a b : GLV V, a ∈ centΓ Γ (normalClosure Γ L) ∧ b ∈ centΓ Γ (normalClosure Γ L) ∧
      a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ a ≠ 1 ∧ b ≠ 1 ∧ b ≠ a ∧ b ≠ a ^ 2 ∧ a * b = b * a := by
  have h108 := hs.h108
  have hHI : Invariant (normalClosure Γ L) I := hI.irrPlus.1
  have hN := normalClosure_normal Γ L
  obtain ⟨x₀, hx₀X, hx₀nc⟩ := exists_not_comm_kappa hs D hF hB
  have hx₀Γ : x₀ ∈ Γ := h108.X_le hx₀X
  have hx₀N := mem_normalizer_of_normal hN hx₀Γ
  have hx₀I : conjSub x₀ I = I := hI.invariant_X.conjSub_eq hx₀X
  obtain ⟨τ, σ, hσ, hτ, hact, hcompat⟩ := exists_semilinear_field_type D hHI hx₀N hx₀I hx₀nc
  have hx₀2 : x₀ * x₀ = 1 := h108.X_sq x₀ hx₀X
  obtain ⟨y₀, hy₀, hy₀1⟩ := exists_mem_centralizerIn_ne_one h108 hI hnf
  have hy₀X := (mem_centralizerIn_iff.1 hy₀).1
  have hy₀C : y₀ ∈ centΓ Γ (normalClosure Γ L) := mem_centΓ_iff.2 ⟨h108.X_le hy₀X,
    fun h hh => ((mem_centralizerIn_iff.1 hy₀).2 h hh).symm⟩
  have hy₀2 : y₀ * y₀ = 1 := h108.X_sq y₀ hy₀X
  have key := hD4 D.F D.U hF hk (centHat D Γ) τ σ hσ hτ (map_semilinear_sq D hx₀2 hσ hact)
    (by
      intro c hc
      obtain ⟨ĉ, hĉC, rfl⟩ := (mem_centHat_iff D).1 hc
      have hmem := centΓ_conj hN x₀ hx₀Γ (ĉ : GLV V) hĉC
      refine ⟨D.θ ⟨x₀ * (ĉ : GLV V) * x₀⁻¹, centΓ_le_centralizer hmem⟩,
        (mem_centHat_iff D).2 ⟨_, hmem, rfl⟩, fun u => ?_⟩
      refine hcompat ĉ ⟨x₀ * (ĉ : GLV V) * x₀⁻¹, centΓ_le_centralizer hmem⟩ ?_ u
      show x₀ * (ĉ : GLV V) * x₀⁻¹ * x₀ = x₀ * (ĉ : GLV V)
      group)
    (noNormalTwo_of_mulEquiv (centHatEquiv D Γ) (centΓ_noNormalTwo hs))
    (by
      have hŷ2 : (⟨y₀, centΓ_le_centralizer hy₀C⟩ : ↥(Subgroup.centralizer
          ((normalClosure Γ L : Subgroup (GLV V)) : Set (GLV V)))) *
          ⟨y₀, centΓ_le_centralizer hy₀C⟩ = 1 := Subtype.ext hy₀2
      refine ⟨D.θ ⟨y₀, centΓ_le_centralizer hy₀C⟩, (mem_centHat_iff D).2 ⟨_, hy₀C, rfl⟩, ?_, ?_⟩
      · intro h
        apply hy₀1
        have := D.θ.injective (h.trans (map_one D.θ).symm)
        exact congrArg Subtype.val this
      · rw [← map_mul, hŷ2, map_one])
  rcases key with ⟨-, hS3 | hA5⟩ | ⟨ζ, hζ, hζ1, hζs, c, hc, hc3, hcs⟩
  · exact Or.inl (hS3.map fun e => (centHatEquiv D Γ).symm.trans e)
  · exact Or.inr (Or.inl (hA5.map fun e => (centHatEquiv D Γ).symm.trans e))
  · obtain ⟨ca, haC, hθa⟩ := (mem_centHat_iff D).1 hζ
    obtain ⟨cb, hbC, hθb⟩ := (mem_centHat_iff D).1 hc
    have hnt : Nontrivial D.U := Module.nontrivial_of_finrank_pos (R := D.F) (by omega)
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := scalar_case hF hζs hc3 hcs
    refine Or.inr (Or.inr ⟨(ca : GLV V), (cb : GLV V), haC, hbC, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩)
    · have : ca ^ 3 = 1 := D.θ.injective (by rw [map_pow, hθa, map_one]; exact h1)
      simpa using congrArg Subtype.val this
    · have : cb ^ 3 = 1 := D.θ.injective (by rw [map_pow, hθb, map_one]; exact h2)
      simpa using congrArg Subtype.val this
    · intro h
      apply hζ1
      rw [← hθa, show ca = 1 from Subtype.ext h, map_one]
    · intro h
      apply h3
      rw [← hθb, show cb = 1 from Subtype.ext h, map_one]
    · intro h
      apply h4
      rw [← hθb, ← hθa, show cb = ca from Subtype.ext h]
    · intro h
      apply h5
      rw [← hθb, show cb = ca ^ 2 from Subtype.ext (by simpa using h), map_pow, hθa]
    · have : ca * cb = cb * ca := D.θ.injective (by rw [map_mul, map_mul, hθa, hθb]; exact h6)
      exact congrArg Subtype.val this

end Dichotomy

section SL

theorem f4_false_SL (hT : Om4PlusTensor) (hs : G11Setup B Γ v₁ W X X₀ L)
    (hI : G116Props B Γ v₁ X L I) (hnf : ¬ FaithfulOn X I) (D : E11Data (normalClosure Γ L) I)
    (hk : Module.finrank D.F D.U = 2) (hF : Nat.card D.F = 4)
    (hd : Module.finrank (ZMod 2) V = 8) (hB : fixedSpace X = Submodule.span (ZMod 2) {v₁})
    (φ : ↥(normalClosure Γ L) ≃* ↥(alternatingGroup (Fin 5)))
    (hAut : AutA5Input) (hD1 : SL24IsoA5) (hD4 : GL24SubInput) : False := by
  have h108 := hs.h108
  have hN := normalClosure_normal Γ L
  rcases f4_dichotomy hs hI hnf D hk hF hB hD4 with hS | hA |
    ⟨a, b, haC, hbC, ha3, hb3, ha1, hb1, hba, hba2, hab⟩
  ·
    obtain ⟨eS⟩ := hS
    have h9 := g118_concl9_of_S3 (G := GLV V) h108.H_le hN φ eS hAut
    have h9' : G112Concl9 Γ := ⟨hd, by
      rcases h9 with h | h
      · exact Or.inl h
      · exact Or.inr h⟩
    apply hs.cx.notConcl
    refine Or.inl ?_
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h9'))))))))
  ·
    obtain ⟨eA⟩ := hA
    obtain ⟨eD⟩ := hD1
    have hmap := fstar_map_eq_of_alt_five h108.H_le hN φ eA
    have hcomm : ∀ h ∈ normalClosure Γ L, ∀ c ∈ centΓ Γ (normalClosure Γ L), h * c = c * h :=
      fun h hh c hc => ((mem_centΓ_iff.1 hc).2 h hh)
    apply hs.cx.notConcl
    refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨⟨hd, ?_, ?_⟩, ?_⟩)))))))
    · have hdis : normalClosure Γ L ⊓ centΓ Γ (normalClosure Γ L) = ⊥ := by
        rw [eq_bot_iff]
        rintro h ⟨hh, hhC⟩
        have hz : (⟨h, hh⟩ : ↥(normalClosure Γ L)) ∈ Subgroup.center ↥(normalClosure Γ L) := by
          rw [Subgroup.mem_center_iff]
          intro y
          exact Subtype.ext (((mem_centΓ_iff.1 hhC).2 y y.2))
        rw [center_eq_bot_of_mulEquiv_alt_five φ, Subgroup.mem_bot] at hz
        have h1 : ((⟨h, hh⟩ : ↥(normalClosure Γ L)) : GLV V) = 1 := congrArg Subtype.val hz
        exact h1
      obtain ⟨eP⟩ := exists_mulEquiv_prod
        (A := normalClosure Γ L ⊔ centΓ Γ (normalClosure Γ L)) (C := normalClosure Γ L)
        (D := centΓ Γ (normalClosure Γ L)) le_sup_left le_sup_right hcomm hdis
        (fun a ha => mem_sup_of_commute' hcomm ha)
      let e1 : ↥(genFittingFStar ↥Γ) ≃* ↥(normalClosure Γ L ⊔ centΓ Γ (normalClosure Γ L)) :=
        (Subgroup.equivMapOfInjective _ Γ.subtype Γ.subtype_injective).trans
          (MulEquiv.subgroupCongr hmap)
      let eSL : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2) ≃*
          ↥(alternatingGroup (Fin 5)) :=
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (GaloisField 2 2)).trans eD
      exact ⟨e1.trans (eP.trans ((φ.prodCongr eA).trans (eSL.prodCongr eSL).symm))⟩
    · rw [hmap]
      intro hXle
      obtain ⟨x₀, hx₀X, hx₀nc⟩ := exists_not_comm_kappa hs D hF hB
      obtain ⟨h, hh, c, hc, hx₀hc⟩ := mem_sup_of_commute' hcomm (hXle hx₀X)
      apply hx₀nc
      intro f
      have hcc := centralizer_comm_kappa D (centΓ_le_centralizer hc) f
      have hhk := D.κ_comm f h hh
      have e1 : ((h * c : GLV V) : Module.End (ZMod 2) V) =
          (h : Module.End (ZMod 2) V) * (c : Module.End (ZMod 2) V) := rfl
      rw [hx₀hc, e1, mul_assoc, hcc, ← mul_assoc, ← hhk, mul_assoc]
    · rw [hmap]
      exact hT V (normalClosure Γ L) (centΓ Γ (normalClosure Γ L)) I hI.homogeneous hI.irrPlus
        h108.fixedSpace_H h108.sSup_isIrr ((Nat.card_congr D.endEquiv.toEquiv).trans hF) hd
        hI.faithful ⟨φ⟩ (fun c hc => centΓ_le_centralizer hc) ⟨eA⟩
  ·
    obtain ⟨E, hE, haE, hbE, hcomm, hexp, hnc⟩ :=
      exists_noncyclic_exp3 hab ha3 hb3 ha1 hb1 hba hba2
    obtain ⟨s, t, ht2, ht1, hs3, hs1, hts⟩ := g118_exists_S3_alt_five
    have hEC : E ≤ centΓ Γ (normalClosure Γ L) := by
      rw [hE]
      refine (Subgroup.closure_le _).2 ?_
      intro x hx
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact haC
      · exact hbC
    have hEΓ : E ≤ Γ := hEC.trans inf_le_left
    set s' : ↥(normalClosure Γ L) := φ.symm s with hs'
    set t' : ↥(normalClosure Γ L) := φ.symm t with ht'
    have ht2' : t' * t' = 1 := by rw [ht', ← map_mul, ht2, map_one]
    have ht1' : t' ≠ 1 := fun h => ht1 (φ.symm.injective (by rw [← ht', h, map_one]))
    have hs3' : s' ^ 3 = 1 := by rw [hs', ← map_pow, hs3, map_one]
    have hs1' : s' ≠ 1 := fun h => hs1 (φ.symm.injective (by rw [← hs', h, map_one]))
    have hts' : t' * s' * t'⁻¹ = s'⁻¹ := by
      rw [hs', ht', ← map_inv, ← map_mul, ← map_mul, hts, map_inv]
    exact G117.no_S3_noncyclic hs.cx.sqtk (h108.H_le t'.2) (h108.H_le s'.2) hEΓ
      (by simpa using congrArg Subtype.val ht2') (fun h => ht1' (Subtype.ext h))
      (by simpa using congrArg Subtype.val hs3') (fun h => hs1' (Subtype.ext h))
      (by simpa using congrArg Subtype.val hts') hcomm hexp hnc
      (fun e he => ((mem_centΓ_iff.1 (hEC he)).2 t' t'.2).symm)
      (fun e he => ((mem_centΓ_iff.1 (hEC he)).2 s' s'.2).symm)

end SL

section Sp

theorem f4_false_Sp (hs : G11Setup B Γ v₁ W X X₀ L) (hI : G116Props B Γ v₁ X L I)
    (D : E11Data (normalClosure Γ L) I) (hF : Nat.card D.F = 4)
    (hB : fixedSpace X = Submodule.span (ZMod 2) {v₁})
    (hHI : Invariant (normalClosure Γ L) I)
    {A : Subgroup (GLV V)} (hAX : A ≤ X) (hAsup : A ⊔ centralizerIn X (normalClosure Γ L) = X)
    (hAfaith : FaithfulOn A I) {m : ℕ} (hAcard : Nat.card A = 2 ^ m) (hm : m = 6)
    (hnat : IsNaturalMatrixModule (restrictRange (normalClosure Γ L) I hHI)
      ⁅StatedSp 2 (GaloisField 2 2), StatedSp 2 (GaloisField 2 2)⁆)
    (hD3 : Sp44RankInput) : False := by
  have h108 := hs.h108
  have hG := h108.toG101Hyp
  have hN := normalClosure_normal Γ L
  have hAinv : Invariant A I := fun k hk i hi => hI.invariant_X k (hAX hk) i hi
  obtain ⟨x₀, hx₀X, hx₀nc⟩ := exists_not_comm_kappa hs D hF hB
  have hx₀N := mem_normalizer_of_normal hN (h108.X_le hx₀X)
  have hx₀I : conjSub x₀ I = I := hI.invariant_X.conjSub_eq hx₀X
  have hcomm : ∀ a ∈ A, ∀ y ∈ centralizerIn X (normalClosure Γ L), a * y = y * a :=
    fun a ha y hy => hG.X_comm a (hAX ha) y (mem_centralizerIn_iff.1 hy).1
  obtain ⟨a, haA, y, hyY, hx₀ay⟩ := mem_sup_of_commute' hcomm (hAsup ▸ hx₀X)
  have hai : ∀ i ∈ I, a i = x₀ i := by
    intro i hi
    rw [hx₀ay]
    show a i = a (y i)
    rw [fixes_of_mem_centralizerIn h108 hI hyY i hi]
  have hxnc := (not_congr (D.comm_kappa_iff hHI hx₀N hx₀I)).1 hx₀nc
  push Not at hxnc
  obtain ⟨f, i, j, hij, hne⟩ := hxnc
  have hElem : IsElemAbelian 2 A :=
    ⟨⟨⟨fun a b => Subtype.ext (hG.X_comm a (hAX a.2) b (hAX b.2))⟩⟩, fun x hx => by
      rw [pow_two]
      exact hG.X_sq x (hAX hx)⟩
  have hcard : Nat.card ↥(restrictRange A I hAinv) ≤ 2 ^ 4 := by
    refine hD3 ↥I (restrictRange (normalClosure Γ L) I hHI) hnat (restrictRange A I hAinv)
      (isElemAbelian_restrictRange hAinv hElem) ?_ ?_
    · intro g hg h' hh'
      obtain ⟨a₁, ha₁A, hga⟩ := (mem_restrictRange_iff hAinv).1 hg
      obtain ⟨h₁, hh₁H, hhh⟩ := (mem_restrictRange_iff hHI).1 hh'
      refine (mem_restrictRange_iff hHI).2 ⟨a₁ * h₁ * a₁⁻¹,
        hN a₁ (h108.X_le (hAX ha₁A)) h₁ hh₁H, fun i₁ => ?_⟩
      set i₀ : ↥I := g⁻¹ i₁ with hi₀
      have hgi₀ : g i₀ = i₁ := by rw [hi₀]; exact g.apply_symm_apply i₁
      have h1 : a₁ (i₀ : V) = (i₁ : V) := by rw [← hga i₀, hgi₀]
      have h2 : a₁⁻¹ (i₁ : V) = (i₀ : V) := by
        rw [← h1]
        exact a₁.symm_apply_apply _
      show (((g * h' * g⁻¹) i₁ : ↥I) : V) = a₁ (h₁ (a₁⁻¹ (i₁ : V)))
      rw [h2]
      show ((g (h' i₀) : ↥I) : V) = a₁ (h₁ (i₀ : V))
      rw [hga, hhh]
    · have hconj : conjSub a I = I := hAinv.conjSub_eq haA
      have hmemE : f.1 ∈ endCommutant (restrictRange (normalClosure Γ L) I hHI) := by
        rw [← endOn_eq_endCommutant hHI]
        exact f.2
      refine ⟨restrictEquiv a I hconj, restrictEquiv_mem_restrictRange hAinv haA, f.1, hmemE, ?_⟩
      intro h
      have h1 := congrArg (fun T : Module.End (ZMod 2) ↥I => ((T i : ↥I) : V)) h
      have h2 : a ((f.1 i : ↥I) : V) = ((f.1 (restrictEquiv a I hconj i) : ↥I) : V) := h1
      have h3 : restrictEquiv a I hconj i = j := by
        apply Subtype.ext
        rw [coe_restrictEquiv, hai i i.2, hij]
      rw [h3, hai _ (f.1 i).2] at h2
      exact hne h2
  rw [natCard_restrictRange hAinv hAfaith, hAcard, hm] at hcard
  norm_num at hcard

end Sp

end F4Basic

end G118

end SzG11S

end G11

end CFSG.Quasithin

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

namespace G11

namespace SzG11S

open CFSG.Quasithin.G11.G118

namespace G118

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

theorem k2_false (hT : Om4PlusTensor) (hs : G11Setup B Γ v₁ W X X₀ L)
    (hI : G116Props B Γ v₁ X L I)
    (hnf : ¬ FaithfulOn X I) (hItop : I ≠ ⊤)
    (hd : Module.finrank (ZMod 2) V = 2 * Module.finrank (ZMod 2) I)
    (hE11 : E11Stmt) (hApply : G93ApplyStmt) (hAut : AutA5Input) (hD1 : SL24IsoA5)
    (hD3 : Sp44RankInput) (hD4 : GL24SubInput) : False := by
  have h108 := hs.h108
  have hI0 : I ≠ ⊥ := (isIrr_I h108 hI).ne_bot
  have h3 : 2 < Module.finrank (ZMod 2) I := h108.two_lt_finrank (isIrr_I h108 hI)
  obtain ⟨D⟩ := hE11 V (normalClosure Γ L) I hI.homogeneous hI.irrPlus h108.fixedSpace_H
    h108.sSup_isIrr
  have hk : Module.finrank D.F D.U = 2 := by
    have h := D.finrank_mul
    rw [hd] at h
    have h' : Module.finrank D.F D.U * Module.finrank (ZMod 2) I = 2 * Module.finrank (ZMod 2) I :=
      h
    exact Nat.eq_of_mul_eq_mul_right (by omega) h'
  have hY1 : 2 ≤ Nat.card ↥(centralizerIn X (normalClosure Γ L)) := by
    obtain ⟨y, hy, hy1⟩ := exists_mem_centralizerIn_ne_one h108 hI hnf
    have : (2 : ℕ) ≤ Nat.card ↥(centralizerIn X (normalClosure Γ L)) := by
      by_contra hlt
      push Not at hlt
      have hcard1 : Nat.card ↥(centralizerIn X (normalClosure Γ L)) = 1 := by
        have : 0 < Nat.card ↥(centralizerIn X (normalClosure Γ L)) := Nat.card_pos
        omega
      have := Subgroup.card_eq_one.1 hcard1
      rw [this] at hy
      exact hy1 (Subgroup.mem_bot.1 hy)
    exact this
  have hY2 : Nat.card ↥(centralizerIn X (normalClosure Γ L)) = 2 := by
    by_cases hq : Nat.card D.F = 2
    · have := card_centralizerIn_le_two_of_card_two h108 D hk hq
      omega
    · exact card_centralizerIn_eq_two_of_not_endTrivial hs hI hnf D hd
        (fun h => hq ((endTrivial_iff_card_two D hI0).1 h))
  obtain ⟨m, hKI, hHI, hXcard, hdI, hconc, A, hAX, hAsup, hAfaith, hAcard⟩ :=
    g118_apply hs hI hApply hY2 hd
  have hsd := selfDual_restrictRange_top hHI hI.selfDual
  have hscan := g118_scan hconc hsd hdI h3
  have hfix : Nat.card D.F ≠ 2 → fixedSpace X = Submodule.span (ZMod 2) {v₁} := by
    intro hq
    by_contra hB
    obtain ⟨-, hET⟩ := not_fixedSpace_imp hs hI hItop hB
    exact hq ((endTrivial_iff_card_two D hI0).1 hET)
  rcases hscan with ⟨hd4, hm2, hnat, hend⟩ | ⟨hd4, hm2, hiso, hend⟩ | ⟨hd4, hperm, hend⟩ |
      ⟨hd8, hm6, hnat, hend⟩ | ⟨hd6, hm4, hperm, hend⟩
  ·
    have hF4 : Nat.card D.F = 4 := by
      have := natCard_F_of_endIsField D hHI (by norm_num) hend
      simpa using this
    obtain ⟨φ', -, -⟩ := hnat
    obtain ⟨eD1⟩ := id hD1
    exact f4_false_SL hT hs hI hnf D hk hF4 (by omega) (hfix (by omega))
      ((restrictRangeEquiv hHI hI.faithful).trans (φ'.trans eD1)) hAut hD1 hD4
  ·
    have hF2 : Nat.card D.F = 2 := by
      have := natCard_F_of_endIsField D hHI (by norm_num) hend
      simpa using this
    obtain ⟨φ'⟩ := hiso
    obtain ⟨eD1⟩ := hD1
    exact f2_false_A5 hs hI hnf D hk hF2 (by omega)
      ((restrictRangeEquiv hHI hI.faithful).trans (φ'.trans eD1)) hAut
  ·
    have hF2 : Nat.card D.F = 2 := by
      have := natCard_F_of_endIsField D hHI (by norm_num) hend
      simpa using this
    obtain ⟨φ', -⟩ := hperm
    exact f2_false_big hs hI hnf D hk hF2 (n := 6) (Or.inl rfl)
      ((restrictRangeEquiv hHI hI.faithful).trans φ')
  ·
    have hF4 : Nat.card D.F = 4 := by
      have := natCard_F_of_endIsField D hHI (by norm_num) hend
      simpa using this
    exact f4_false_Sp hs hI D hF4 (hfix (by omega)) hHI hAX hAsup hAfaith hAcard hm6 hnat hD3
  ·
    have hF2 : Nat.card D.F = 2 := by
      have := natCard_F_of_endIsField D hHI (by norm_num) hend
      simpa using this
    obtain ⟨φ', -⟩ := hperm
    exact f2_false_big hs hI hnf D hk hF2 (n := 8) (Or.inr rfl)
      ((restrictRangeEquiv hHI hI.faithful).trans φ')

end G118

end SzG11S

end G11

end CFSG.Quasithin

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

namespace G11

namespace SzG11S

open CFSG.Quasithin.G11.G118

theorem g11_8 (hT : Om4PlusTensor) (h7 : G117Stmt) (hE11 : E11Stmt)
    (hApply : G93ApplyStmt) (hD3 : G118.Sp44RankInput) (hD4 : G118.GL24SubInput) : G118Stmt := by
  intro V _ _ _ B Γ v₁ W X X₀ L hs I hI
  have h108 := hs.h108
  obtain ⟨hnf, hItop⟩ := h7 V B Γ v₁ W X X₀ L hs I hI
  have hge := G118.two_mul_finrank_le h108 hI hItop
  have h3 : ∀ x ∈ centralizerIn X (normalClosure Γ L), ∀ i ∈ I, x i = i := fun x hx =>
    G118.fixes_of_mem_centralizerIn h108 hI hx
  by_cases hlt : 2 * Module.finrank (ZMod 2) I < Module.finrank (ZMod 2) V
  · refine ⟨hlt, ?_, h3⟩
    by_contra hB
    have := (G118.not_fixedSpace_imp hs hI hItop hB).1
    omega
  · exfalso
    have hd : Module.finrank (ZMod 2) V = 2 * Module.finrank (ZMod 2) I := by omega
    exact G118.k2_false hT hs hI hnf hItop hd hE11 hApply G118.autA5Input G118.sl24IsoA5 hD3 hD4

end SzG11S

end G11

end CFSG.Quasithin

