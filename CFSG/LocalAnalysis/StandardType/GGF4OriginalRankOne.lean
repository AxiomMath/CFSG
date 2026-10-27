module

public import CFSG.LocalAnalysis.StandardType.GGOriginalRankOne
public import CFSG.LocalAnalysis.StandardType.GGF4QGeFourOrb
import CFSG.LocalAnalysis.StandardType.GGF4QGeFourRk2Cross
import CFSG.LocalAnalysis.StandardType.GGKGPosSpStd
import CFSG.LocalAnalysis.StandardType.GGInnerDiagMpStdAssembly
import Mathlib.Tactic.Group

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.Universal CFSG.LieType.RootSystem

variable {G : Type} [Group G]

@[expose] def GGOriginalRankOneFamily (p : ℕ) (L H Bs : Subgroup G)
    (R : Set (MulAut ↥Bs)) : Prop :=
  (∀ r ∈ R, ggRankOneFrom p L H Bs r ≤ H ∧
    IsComponentOf (ggRankOneFrom p L H Bs r)
      (Subgroup.centralizer (ggHyperplane Bs r : Set G)) ∧
    Bs ≤ Subgroup.normalizer (ggRankOneFrom p L H Bs r : Set G) ∧
    r ∈ ggAutomizer (ggRankOneFrom p L H Bs r) Bs ∧
    GGOriginalRankOneConjugate p L H Bs r (ggRankOneFrom p L H Bs r)) ∧
  (∀ r ∈ ggAutomizer L Bs, GGIsReflection p r →
    ggRankOneFrom p L H Bs r = ggRankOneIn L Bs r) ∧
  ∀ m ∈ H, ∀ (_ : m ∈ Subgroup.normalizer (Bs : Set G)), ∀ a : MulAut ↥Bs,
    (∀ b : ↥Bs, ((a b : ↥Bs) : G) = m * b * m⁻¹) → ∀ r : MulAut ↥Bs,
      (ggRankOneFrom p L H Bs r).map (MulAut.conj m).toMonoidHom =
        ggRankOneFrom p L H Bs (a * r * a⁻¹)

theorem GGOriginalRankOneFamily.exists_reflection_lift {p : ℕ} {L H Bs : Subgroup G}
    {R : Set (MulAut ↥Bs)} (h : GGOriginalRankOneFamily p L H Bs R)
    {r : MulAut ↥Bs} (hr : r ∈ R) :
    ∃ n ∈ H, n ∈ Subgroup.normalizer (Bs : Set G) ∧
      (∀ b : ↥Bs, ((r b : ↥Bs) : G) = n * b * n⁻¹) ∧ n ∈ ggRankOneFrom p L H Bs r := by
  obtain ⟨hSH, -, -, hrS, -⟩ := h.1 r hr
  obtain ⟨n, hnS, hnN, hn⟩ := mem_ggAutomizer_iff.mp hrS
  exact ⟨n, hSH hnS, hnN, hn, hnS⟩

theorem GGOriginalRankOneFamily.exists_centralizing_reflection_lift {p : ℕ}
    {L H Bs : Subgroup G} {R : Set (MulAut ↥Bs)} (h : GGOriginalRankOneFamily p L H Bs R)
    {u r : MulAut ↥Bs} (huL : u ∈ ggAutomizer L Bs) (hu : GGIsReflection p u) (hr : r ∈ R)
    (hcomm : ∀ s ∈ ggRankOneFrom p L H Bs u, ∀ t ∈ ggRankOneFrom p L H Bs r, s * t = t * s) :
    ∃ n ∈ H, n ∈ Subgroup.normalizer (Bs : Set G) ∧
      (∀ b : ↥Bs, ((r b : ↥Bs) : G) = n * b * n⁻¹) ∧
      n ∈ Subgroup.centralizer (ggRankOneIn L Bs u : Set G) := by
  obtain ⟨n, hnH, hnN, hn, hnS⟩ := h.exists_reflection_lift hr
  refine ⟨n, hnH, hnN, hn, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hsS : s ∈ ggRankOneFrom p L H Bs u := by
    rw [h.2.1 u huL hu]
    exact hs
  exact hcomm s hsS n hnS

section Coverage

variable [Finite G]

private theorem simple_first_eq_conj_middle {ι : Type} (M : CoxeterMatrix ι)
    (σ : Fin 3 ≃ ι) (h10 : M (σ 1) (σ 0) = 3) :
    ∃ w : M.Group, M.simple (σ 0) = w * M.simple (σ 1) * w⁻¹ := by
  let x := M.simple (σ 0)
  let y := M.simple (σ 1)
  have hx : x * x = 1 := by
    simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
      M.toCoxeterSystem.simple_mul_simple_self (σ 0)
  have hy : y * y = 1 := by
    simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
      M.toCoxeterSystem.simple_mul_simple_self (σ 1)
  have hpow : (y * x) ^ 3 = 1 := by
    simpa only [CoxeterMatrix.toCoxeterSystem_simple, h10] using
      M.toCoxeterSystem.simple_mul_simple_pow (σ 1) (σ 0)
  have hthree : (y * x) * (y * x) * (y * x) = 1 := by
    simpa only [pow_succ, pow_zero, one_mul] using hpow
  have hfive : y * x * y * x * y = x := by
    have h := congrArg (fun z : M.Group => z * x) hthree
    simpa only [mul_assoc, hx, mul_one, one_mul] using h
  refine ⟨y * x, ?_⟩
  rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hx, inv_eq_of_mul_eq_one_right hy]
  simpa only [mul_assoc] using hfive.symm

theorem isQuasisimple_ggRankOneIn_of_three_coxRefl {Bs L : Subgroup G}
    {ι : Type} {M : CoxeterMatrix ι} (ε : M.Group ≃* ↥(ggAutomizer L Bs))
    (σ : Fin 3 ≃ ι) (h10 : M (σ 1) (σ 0) = 3)
    (hq₁ : CFSG.Assembly.IsQuasisimple
      ↥(ggRankOneIn L Bs ((ε (M.simple (σ 1)) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)))
    (hq₂ : CFSG.Assembly.IsQuasisimple
      ↥(ggRankOneIn L Bs ((ε (M.simple (σ 2)) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)))
    {r : MulAut ↥Bs} (hr : r ∈ ggCoxRefl M ε) :
    CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs r) := by
  have hconj {a t : MulAut ↥Bs} (ha : a ∈ ggAutomizer L Bs)
      (hq : CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs t)) :
      CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs (a * t * a⁻¹)) := by
    obtain ⟨g, -, -, hS⟩ := exists_ggRankOneIn_conj_of_mem_ggAutomizer ha t
    rw [← hS]
    exact CFSG.Assembly.IsQuasisimple.of_mulEquiv
      ((ggRankOneIn L Bs t).equivMapOfInjective (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm hq
  have hsimple : ∀ i : Fin 3, CFSG.Assembly.IsQuasisimple
      ↥(ggRankOneIn L Bs ((ε (M.simple (σ i)) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)) := by
    intro i
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl
    · obtain ⟨w, hw⟩ := simple_first_eq_conj_middle M σ h10
      have h : ((ε (M.simple (σ 0)) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) =
          ((ε w : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) *
            ((ε (M.simple (σ 1)) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) *
            ((ε w : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)⁻¹ := by
        rw [hw]
        simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [h]
      exact hconj (ε w).2 hq₁
    · exact hq₁
    · exact hq₂
  obtain ⟨w, i, rfl⟩ := hr
  obtain ⟨k, rfl⟩ := σ.surjective i
  have h : ((ε (w * M.simple (σ k) * w⁻¹) : ↥(ggAutomizer L Bs)) :
      MulAut ↥Bs) = ((ε w : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) *
        ((ε (M.simple (σ k)) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs) *
        ((ε w : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)⁻¹ := by
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [h]
  exact hconj (ε w).2 (hsimple k)

theorem isQuasisimple_ggRankOneIn_of_b3 {p : ℕ} {Bs L : Subgroup G}
    (hpp : p.Prime) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {ι : Type} {M : CoxeterMatrix ι} (ε : M.Group ≃* ↥(ggAutomizer L Bs))
    (σ : Fin 3 ≃ ι) (hM : ∀ k l, M (σ k) (σ l) = CoxeterMatrix.B 3 k l)
    (hε : ∀ i, GGIsReflection p
      ((ε (M.simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
    (hq₁ : CFSG.Assembly.IsQuasisimple
      ↥(ggRankOneIn L Bs ((ε (M.simple (σ 1)) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)))
    (hq₂ : CFSG.Assembly.IsQuasisimple
      ↥(ggRankOneIn L Bs ((ε (M.simple (σ 2)) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)))
    {r : MulAut ↥Bs} (hrL : r ∈ ggAutomizer L Bs) (hr : GGIsReflection p r) :
    CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs r) := by
  have hMe : M = (CoxeterMatrix.B 3).reindex σ := by
    ext i j
    change M i j = CoxeterMatrix.B 3 (σ.symm i) (σ.symm j)
    simpa only [Equiv.apply_symm_apply] using hM (σ.symm i) (σ.symm j)
  have hW : GGIsWeylMatrix M :=
    Or.inl ⟨3, σ, by decide, Or.inr (Or.inl ⟨by decide, hMe⟩)⟩
  have hG2 : ¬ ∃ e : Fin 2 ≃ ι, M = CoxeterMatrix.G₂.reindex e := by
    rintro ⟨e, -⟩
    have h := Fintype.card_congr (e.trans σ.symm)
    simp at h
  have hAind : ggAutomizer L Bs ≤ ggInduced ⊤ Bs := by
    intro a ha
    have h := ggAutomizer_mono Bs le_top ha
    rw [ggAutomizer_eq] at h
    exact h
  obtain ⟨i, w, hw⟩ := SecFiveRootRefl.ggSecFiveRootReflInput_holds G p Bs hpp hp2 hBs hNT
    (ggAutomizer L Bs) hAind ι M hW hG2 ε hε ⟨r, hrL⟩ hr
  have h10 : M (σ 1) (σ 0) = 3 := by rw [hM]; decide
  exact isQuasisimple_ggRankOneIn_of_three_coxRefl ε σ h10 hq₁ hq₂
    ⟨w, i, congrArg Subtype.val hw⟩

theorem exists_originalRankOneConjugate_of_b3 {p : ℕ} {Bs L H : Subgroup G}
    (hpp : p.Prime) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    {A : Subgroup (MulAut ↥Bs)} (hAH : A ≤ ggAutomizer H Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    (hLA : ggAutomizer L Bs ≤ A) {ι : Type} {M : CoxeterMatrix ι}
    (ε : M.Group ≃* ↥(ggAutomizer L Bs))
    (hε : ∀ i, GGIsReflection p ((ε (M.simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
    (σ : Fin 3 ≃ ι) (hM : ∀ k l, M (σ k) (σ l) = CoxeterMatrix.B 3 k l)
    {r : MulAut ↥Bs} (hr : r ∈ ggCoxRefl CoxeterMatrix.F₄ e) :
    ∃ S, GGOriginalRankOneConjugate p L H Bs r S := by
  have hAind : A ≤ ggInduced ⊤ Bs := by
    intro a ha
    have h := ggAutomizer_mono Bs le_top (hAH ha)
    rw [ggAutomizer_eq] at h
    exact h
  obtain ⟨a, ha, ha01, ha12, ha02, haL⟩ :=
    exists_f4Triple_of_weyl hpp hp2 hBs hNT hAind hpres hLA ε hε σ hM
  obtain ⟨R, hRs⟩ := F4Model.exists_f4Rep CoxeterMatrix.F₄.toCoxeterSystem
  have hs : ∀ i, R.s i = CoxeterMatrix.F₄.simple i := fun i => by
    simpa only [CoxeterMatrix.toCoxeterSystem_simple] using hRs i
  obtain ⟨g, hg⟩ := R.classify
    ((F4Model.F4Rep.isRefl_iff hRs).mpr (ha 0))
    ((F4Model.F4Rep.isRefl_iff hRs).mpr (ha 1))
    ((F4Model.F4Rep.isRefl_iff hRs).mpr (ha 2)) ha01 ha12 ha02
  obtain ⟨w, i, rfl⟩ := hr
  have hcover : ∃ v : CoxeterMatrix.F₄.Group,
      v * R.s i * v⁻¹ ∈ Subgroup.closure (Set.range a) := by
    rcases hg with hg | hg
    · obtain ⟨v, hv, -⟩ := R.exists_conj_of_B hg (i := i) (j := i) (by omega)
      exact ⟨v, hv⟩
    · obtain ⟨v, hv, -⟩ := R.exists_conj_of_C hg (i := i) (j := i) (by omega)
      exact ⟨v, hv⟩
  obtain ⟨v, hv⟩ := hcover
  let t : MulAut ↥Bs := ((e (v * CoxeterMatrix.F₄.simple i * v⁻¹) : ↥A) : MulAut ↥Bs)
  have htL : t ∈ ggAutomizer L Bs := (haL _).mp (by simpa only [hs] using hv)
  have htr : GGIsReflection p t := ggCoxRefl_isReflection hpres.2 ⟨v, i, rfl⟩
  let b : MulAut ↥Bs := ((e (w * v⁻¹) : ↥A) : MulAut ↥Bs)
  obtain ⟨n, hn, hnN, hnb⟩ := mem_ggAutomizer_iff.mp (hAH (e (w * v⁻¹)).2)
  refine ⟨(ggRankOneIn L Bs t).map (MulAut.conj n).toMonoidHom,
    t, htL, htr, n, hn, hnN, b, hnb, ?_, rfl⟩
  let ιe : CoxeterMatrix.F₄.Group →* MulAut ↥Bs := A.subtype.comp e.toMonoidHom
  change ιe (w * CoxeterMatrix.F₄.simple i * w⁻¹) =
    ιe (w * v⁻¹) * ιe (v * CoxeterMatrix.F₄.simple i * v⁻¹) * (ιe (w * v⁻¹))⁻¹
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  group

theorem ggOriginalRankOneFamily_of_b3 {p : ℕ} {Bs L H : Subgroup G} {x : G}
    (hpp : p.Prime) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    (hx : x ∈ Bs) (hL : IsSubnormal L (Subgroup.centralizer ({x} : Set G)))
    (hBL : Bs ≤ Subgroup.normalizer (L : Set G)) (hLH : L ≤ H)
    {A : Subgroup (MulAut ↥Bs)} (hAH : A ≤ ggAutomizer H Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    (hLA : ggAutomizer L Bs ≤ A) {ι : Type} {M : CoxeterMatrix ι}
    (ε : M.Group ≃* ↥(ggAutomizer L Bs))
    (hε : ∀ i, GGIsReflection p ((ε (M.simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
    (σ : Fin 3 ≃ ι) (hM : ∀ k l, M (σ k) (σ l) = CoxeterMatrix.B 3 k l)
    (hqs : ∀ t ∈ ggAutomizer L Bs, GGIsReflection p t →
      CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs t)) :
    GGOriginalRankOneFamily p L H Bs (ggCoxRefl CoxeterMatrix.F₄ e) := by
  have hp : Odd p := hpp.odd_of_ne_two hp2
  refine ⟨?_, ?_, fun m hm hmN a ha r => ggRankOneFrom_map_conj hm hmN ha r⟩
  · intro r hr
    have hsource := exists_originalRankOneConjugate_of_b3 hpp hp2 hBs hNT hAH hpres hLA
      ε hε σ hM hr
    obtain ⟨hC, hN, hA⟩ := ggRankOneFrom_component_data hpp hp hBs hx hL hBL hqs hsource
    obtain ⟨S, hS⟩ := hsource
    have hEq := ggRankOneFrom_eq_of_conjugate hpp hp hBs hx hL hBL hqs hS
    refine ⟨ggRankOneFrom_le hLH r, hC, hN, hA, ?_⟩
    rw [hEq]
    exact hS
  · intro r hrL hr
    exact ggRankOneFrom_eq_original hpp hp hBs hx hL hBL hqs hrL hr

theorem ggOriginalRankOneFamily_of_b3_two {p : ℕ} {Bs L H : Subgroup G} {x : G}
    (hpp : p.Prime) (hp2 : p ≠ 2) (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs)
    (hx : x ∈ Bs) (hL : IsSubnormal L (Subgroup.centralizer ({x} : Set G)))
    (hBL : Bs ≤ Subgroup.normalizer (L : Set G)) (hLH : L ≤ H)
    {A : Subgroup (MulAut ↥Bs)} (hAH : A ≤ ggAutomizer H Bs)
    {e : CoxeterMatrix.F₄.Group ≃* ↥A} (hpres : GGCoxeterPres p A CoxeterMatrix.F₄ e)
    (hLA : ggAutomizer L Bs ≤ A)
    {ι : Type} {M : CoxeterMatrix ι} (ε : M.Group ≃* ↥(ggAutomizer L Bs))
    (σ : Fin 3 ≃ ι) (hM : ∀ k l, M (σ k) (σ l) = CoxeterMatrix.B 3 k l)
    (hε : ∀ i, GGIsReflection p
      ((ε (M.simple i) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))
    (hq₁ : CFSG.Assembly.IsQuasisimple
      ↥(ggRankOneIn L Bs ((ε (M.simple (σ 1)) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs)))
    (hq₂ : CFSG.Assembly.IsQuasisimple
      ↥(ggRankOneIn L Bs ((ε (M.simple (σ 2)) : ↥(ggAutomizer L Bs)) : MulAut ↥Bs))) :
    GGOriginalRankOneFamily p L H Bs (ggCoxRefl CoxeterMatrix.F₄ e) := by
  exact ggOriginalRankOneFamily_of_b3 hpp hp2 hBs hNT hx hL hBL hLH hAH hpres hLA ε hε
    σ hM (fun _ hrL hr => isQuasisimple_ggRankOneIn_of_b3 hpp hp2 hBs hNT ε σ hM hε
      hq₁ hq₂ hrL hr)

end Coverage

section Native

theorem ggF4OriginalRankOneFamily_of_tableBPosImage {G : Type} [Group G] [Finite G] {p : ℕ}
    {Bs L K : Subgroup G} {x : G} (hpp : p.Prime) (hp2 : p ≠ 2)
    (hBs : IsElemAbelian p Bs) (hNT : GGNoTransvection p Bs) (hx : x ∈ Bs)
    (hL : IsSubnormal L (Subgroup.centralizer ({x} : Set G)))
    (hBL : Bs ≤ Subgroup.normalizer (L : Set G))
    {e : CoxeterMatrix.F₄.Group ≃* ↥(ggAutomizer L Bs ⊔ ggAutomizer K Bs)}
    (hpres : GGCoxeterPres p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) CoxeterMatrix.F₄ e)
    {f : ℕ} (hf : 2 ≤ f)
    (hpos : GGTableBPosImage p Bs .PSp 3 f L ∨ GGTableBPosImage p Bs .POmegaMinus 4 f L) :
    GGOriginalRankOneFamily p L (L ⊔ K) Bs (ggCoxRefl CoxeterMatrix.F₄ e) := by
  have hAH : ggAutomizer L Bs ⊔ ggAutomizer K Bs ≤ ggAutomizer (L ⊔ K) Bs :=
    sup_le (ggAutomizer_mono Bs le_sup_left) (ggAutomizer_mono Bs le_sup_right)
  rcases hpos with hpos | hpos
  · have hqs : ∀ t ∈ ggAutomizer L Bs, GGIsReflection p t →
        CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs t) := fun t ht htr =>
      isQuasisimple_ggRankOneIn_of_tableBPosImage_PSp hpp hp2 hBs hNT hf hpos ht htr
    obtain ⟨ψ, -, -, ε, hε, -, -⟩ := hpos
    have hM : ∀ k l : Fin 3, (coxeterMatrix (ggU .PSp 3 f).D.isFiniteType)
        ((Equiv.refl (Fin 3)) k) ((Equiv.refl (Fin 3)) l) = CoxeterMatrix.B 3 k l := by
      intro k l
      rw [coxeterMatrix_PSp_three]
      rfl
    exact ggOriginalRankOneFamily_of_b3_two hpp hp2 hBs hNT hx hL hBL le_sup_left hAH hpres
      le_sup_left ε (Equiv.refl _) hM hε (hqs _ (ε _).2 (hε ((Equiv.refl (Fin 3)) 1)))
        (hqs _ (ε _).2 (hε ((Equiv.refl (Fin 3)) 2)))
  · have hqs : ∀ t ∈ ggAutomizer L Bs, GGIsReflection p t →
        CFSG.Assembly.IsQuasisimple ↥(ggRankOneIn L Bs t) := fun t ht htr =>
      isQuasisimple_ggRankOneIn_of_tableBPosImage_S2 hpp hp2 hBs hNT hf (Or.inl hpos) ht htr
    obtain ⟨ψ, -, -, ε, hε, -, -⟩ := hpos
    have hM : ∀ k l : Fin 3, (coxeterMatrix (ggU .POmegaMinus 4 f).D.isFiniteType)
        ((Equiv.refl (Fin 3)) k) ((Equiv.refl (Fin 3)) l) = CoxeterMatrix.B 3 k l := by
      intro k l
      rw [coxeterMatrix_POmegaMinus_four]
      rfl
    exact ggOriginalRankOneFamily_of_b3_two hpp hp2 hBs hNT hx hL hBL le_sup_left hAH hpres
      le_sup_left ε (Equiv.refl _) hM hε (hqs _ (ε _).2 (hε ((Equiv.refl (Fin 3)) 1)))
        (hqs _ (ε _).2 (hε ((Equiv.refl (Fin 3)) 2)))

end Native

end CFSG.StandardType

end
