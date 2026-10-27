module

public import CFSG.LocalAnalysis.StandardType.ZS.TableDefs
import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneFour
public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneSixTen
import CFSG.LocalAnalysis.StandardType.ZS.InitialPair
import CFSG.LocalAnalysis.StandardType.ZS.Conjugate
import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneTwo
import CFSG.LocalAnalysis.StandardType.ZS.Subquotient
import CFSG.LocalAnalysis.StandardType.ZS.ThroughRefl
import CFSG.LocalAnalysis.StandardType.ZS.PropOneEightSteps
import CFSG.LocalAnalysis.StandardType.ZS.MovedAction
import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem two_le_of_splitSupport_dLarge (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (hHs : SplitSupport H l)
    (htv : QTwoLin.TransvectionFree H)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) : 2 ≤ l := by
  by_contra h
  replace h : l < 2 := not_le.mp h
  obtain ⟨x, hxH, y, hyH, hx, hy, hord⟩ := hd
  have hmovx : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace x) = 1 := by
    rw [HardMathSupport.Kantor79.movedSpace]; exact hx.2
  have hmovy : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace y) = 1 := by
    rw [HardMathSupport.Kantor79.movedSpace]; exact hy.2
  rcases l with _ | _ | l
  · have hbot : HardMathSupport.Kantor79.commutatorSpace H = ⊥ :=
      (Submodule.finrank_eq_zero).mp hHs.2.1
    have hle := HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hxH
    rw [hbot] at hle
    have h0 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace x) = 0 := by
      rw [le_bot_iff.mp hle, finrank_bot]
    rw [hmovx] at h0
    exact Nat.zero_ne_one h0.symm
  · have hxle := HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hxH
    have hyle := HardMathSupport.Kantor79.movedSpace_le_commutatorSpace hyH
    have hxeq : HardMathSupport.Kantor79.movedSpace x =
        HardMathSupport.Kantor79.commutatorSpace H :=
      Submodule.eq_of_le_of_finrank_eq hxle (by rw [hmovx, hHs.2.1])
    have hyeq : HardMathSupport.Kantor79.movedSpace y =
        HardMathSupport.Kantor79.commutatorSpace H :=
      Submodule.eq_of_le_of_finrank_eq hyle (by rw [hmovy, hHs.2.1])
    have hmov : HardMathSupport.Kantor79.movedSpace x =
        HardMathSupport.Kantor79.movedSpace y := by rw [hxeq, hyeq]
    have hxy : x = y := eq_of_movedSpace_eq hp htv hxH hyH hx hy hmov
    subst hxy
    rw [hx.1] at hord
    simp at hord
  · omega

private theorem reflGen_closure_insert {A B : Subgroup (U ≃ₗ[ZMod p] U)}
    {a : U ≃ₗ[ZMod p] U} (hA : ReflGen p A) (ha : IsRefl p a)
    (hB : B = Subgroup.closure (insert a (A : Set (U ≃ₗ[ZMod p] U)))) : ReflGen p B := by
  rw [hB]
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    intro t ht
    rw [Set.mem_insert_iff] at ht
    rcases ht with rfl | ht
    · exact Subgroup.subset_closure ⟨Subgroup.subset_closure (by simp), ha⟩
    · rw [hA] at ht
      let RA : Set (U ≃ₗ[ZMod p] U) := {u : U ≃ₗ[ZMod p] U | u ∈ A ∧ IsRefl p u}
      let RB : Set (U ≃ₗ[ZMod p] U) :=
        {u : U ≃ₗ[ZMod p] U | u ∈ Subgroup.closure (insert a (A : Set (U ≃ₗ[ZMod p] U))) ∧
          IsRefl p u}
      have hsub : RA ⊆ RB := by
        intro u hu
        exact ⟨Subgroup.closure_mono (Set.subset_insert a _) (Subgroup.subset_closure hu.1),
          hu.2⟩
      exact Subgroup.closure_mono hsub ht
  · exact (Subgroup.closure_le _).mpr (fun u hu => hu.1)

private theorem exists_maximal_splitSupport [Module.Finite (ZMod p) U]
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (hHG : H ≤ G) (hH : ReflGen p H)
    (hHs : SplitSupport H l) :
    ∃ H' : Subgroup (U ≃ₗ[ZMod p] U), H ≤ H' ∧ H' ≤ G ∧ ReflGen p H' ∧ SplitSupport H' l ∧
      ∀ K : Subgroup (U ≃ₗ[ZMod p] U), H' ≤ K → K ≤ G → ReflGen p K →
        SplitSupport K l → K = H' := by
  classical
  let : Finite U := Module.finite_of_finite (ZMod p)
  let : Fintype U := Fintype.ofFinite U
  let : DecidableEq U := Classical.decEq U
  let : Fintype (U ≃ₗ[ZMod p] U) :=
    Fintype.ofInjective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun e f h => LinearEquiv.ext fun v => congrArg (fun g : U → U => g v) h)
  let : Fintype (Set (U ≃ₗ[ZMod p] U)) := Set.fintype
  let : Fintype (Subgroup (U ≃ₗ[ZMod p] U)) :=
    Fintype.ofInjective (fun K : Subgroup (U ≃ₗ[ZMod p] U) => (K : Set (U ≃ₗ[ZMod p] U)))
      (fun K L h => SetLike.ext (Set.ext_iff.mp h))
  let S : Set (Subgroup (U ≃ₗ[ZMod p] U)) :=
    {K | H ≤ K ∧ K ≤ G ∧ ReflGen p K ∧ SplitSupport K l}
  obtain ⟨H', hHH', hmax⟩ :=
    (Set.toFinite S).exists_le_maximal (a := H) ⟨le_rfl, hHG, hH, hHs⟩
  obtain ⟨hH'H, hH'G, hH'refl, hH'split⟩ := hmax.1
  refine ⟨H', hH'H, hH'G, hH'refl, hH'split, ?_⟩
  intro K hH'K hKG hKr hKs
  exact le_antisymm (hmax.2 ⟨hHH'.trans hH'K, hKG, hKr, hKs⟩ hH'K) hH'K

private def EnlGoal (G H : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  ∃ K : Subgroup (U ≃ₗ[ZMod p] U), H ≤ K ∧ K ≤ G ∧ ReflGen p K ∧
    (SplitSupport K (Module.finrank (ZMod p) U - 2) ∨
      SplitSupport K (Module.finrank (ZMod p) U - 1))

private structure EnlSetup (G H : Subgroup (U ≃ₗ[ZMod p] U)) (l : ℕ) where
  H' : Subgroup (U ≃ₗ[ZMod p] U)
  a : U ≃ₗ[ZMod p] U
  hHH' : H ≤ H'
  hH'G : H' ≤ G
  hH'refl : ReflGen p H'
  hH'split : SplitSupport H' l
  hmaxF : ∀ K : Subgroup (U ≃ₗ[ZMod p] U),
    K ≤ Subgroup.closure (insert a (H' : Set (U ≃ₗ[ZMod p] U))) → H' ≤ K → ReflGen p K →
      SplitSupport K l → K = H'
  hdH' : ∃ x ∈ H', ∃ y ∈ H', IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)
  haRefl : IsRefl p a
  hFG : Subgroup.closure (insert a (H' : Set (U ≃ₗ[ZMod p] U))) ≤ G
  hFrefl : ReflGen p (Subgroup.closure (insert a (H' : Set (U ≃ₗ[ZMod p] U))))
  hdF : ∃ x ∈ Subgroup.closure (insert a (H' : Set (U ≃ₗ[ZMod p] U))),
    ∃ y ∈ Subgroup.closure (insert a (H' : Set (U ≃ₗ[ZMod p] U))),
      IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)
  hFfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace
    (Subgroup.closure (insert a (H' : Set (U ≃ₗ[ZMod p] U))))) = l + 1
  hdisj : SplitSupport (Subgroup.closure (insert a (H' : Set (U ≃ₗ[ZMod p] U)))) (l + 1) ∨
    IsDegenerate (Subgroup.closure (insert a (H' : Set (U ≃ₗ[ZMod p] U)))) H'
  hln2 : l + 2 < Module.finrank (ZMod p) U

private def EnlIH (N : ℕ) (G : Subgroup (U ≃ₗ[ZMod p] U)) : Prop :=
  ∀ m : ℕ, m < N → ∀ (H : Subgroup (U ≃ₗ[ZMod p] U)) (l : ℕ),
    Module.finrank (ZMod p) U - l = m → l < Module.finrank (ZMod p) U → H ≤ G →
      ReflGen p H → SplitSupport H l →
      (∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) → EnlGoal G H

private theorem splitSupport_nontrivial [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (hHs : SplitSupport H l)
    (hln : l < Module.finrank (ZMod p) U) (hl : 1 ≤ l) :
    (HardMathSupport.Kantor79.commutatorSpace H ≠ ⊥) ∧
    (HardMathSupport.Kantor79.commutatorSpace H ≠ ⊤) ∧
    (centralizerSpace H ≠ ⊥) ∧ (centralizerSpace H ≠ ⊤) := by
  have hfl : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) = l := hHs.2.1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hbot
    rw [hbot, finrank_bot] at hfl
    omega
  · intro htop
    rw [htop, finrank_top] at hfl
    omega
  · intro hbot
    have htop : HardMathSupport.Kantor79.commutatorSpace H = ⊤ := by
      have h := hHs.1.sup_eq_top
      rw [hbot, sup_bot_eq] at h
      exact h
    rw [htop, finrank_top] at hfl
    omega
  · intro htop
    have hbot : HardMathSupport.Kantor79.commutatorSpace H = ⊥ :=
      hHs.1.disjoint.eq_bot_of_le (by rw [htop]; exact le_top)
    rw [hbot, finrank_bot] at hfl
    omega

private theorem closure_insert_le' {G F H' B : Subgroup (U ≃ₗ[ZMod p] U)}
    {g : U ≃ₗ[ZMod p] U}
    (hB : B = Subgroup.closure (insert g ((⁅H', kerSection F⁆ ⊔ H' : Subgroup (U ≃ₗ[ZMod p] U)) :
      Set _))) (hFG : F ≤ G) (hgG : g ∈ G) (hH'F : H' ≤ F) : B ≤ G ∧ H' ≤ B := by
  have hTF : kerSection F ≤ F := kerSection_le
  have hSsubF : ⁅H', kerSection F⁆ ≤ F := Subgroup.commutator_le_of_le hH'F hTF
  have hsupF : ⁅H', kerSection F⁆ ⊔ H' ≤ F := sup_le hSsubF hH'F
  refine ⟨?_, ?_⟩
  · rw [hB]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (rfl | hx)
    · exact hgG
    · exact hsupF.trans hFG hx
  · rw [hB]
    exact fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem g (Subgroup.mem_sup_right hx))

private theorem W_V0_trivial (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U} {l : ℕ}
    (hS : LemmaOneSixSetting F H a l) (hn : 2 ≤ Module.finrank (ZMod p) U) :
    (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F ≠ ⊥) ∧
    (HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F ≠ ⊤) ∧
    (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F ≠ ⊥) ∧
    (HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F ≠ ⊤) := by
  have hWfin : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 1 := hS.degenerate.1
  have hV0fin : Module.finrank (ZMod p)
      ↥(HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) =
        Module.finrank (ZMod p) U - 1 := hS.finrank_sup_eq hp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hbot
    have h0 : Module.finrank (ZMod p)
        ↥(HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) = 0 := by
      rw [hbot, finrank_bot]
    omega
  · intro htop
    have hfin := hWfin
    rw [htop, finrank_top] at hfin
    omega
  · intro hbot
    have h0 : Module.finrank (ZMod p)
        ↥(HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F) = 0 := by
      rw [hbot, finrank_bot]
    omega
  · intro htop
    have hfin := hV0fin
    rw [htop, finrank_top] at hfin
    omega

private theorem not_mem_of_moves {H : Subgroup (U ≃ₗ[ZMod p] U)} {c : U ≃ₗ[ZMod p] U}
    (hmov : ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace H,
      c v ∉ HardMathSupport.Kantor79.commutatorSpace H) :
    c ∉ H ∧ c ∉ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)) := by
  have hcH : c ∉ H := by
    intro hc
    obtain ⟨v, hv, hvne⟩ := hmov
    exact hvne (apply_mem_commutatorSpace hc hv)
  refine ⟨hcH, ?_⟩
  intro hc
  obtain ⟨v, hv, hvne⟩ := hmov
  have hmap : (HardMathSupport.Kantor79.commutatorSpace H).map (c : U →ₗ[ZMod p] U) ≤
      HardMathSupport.Kantor79.commutatorSpace H := by
    rw [HardMathSupport.Kantor79.commutatorSpace, Submodule.map_span, Submodule.span_le]
    rintro w ⟨s, hs, rfl⟩
    obtain ⟨h, hh, u, rfl⟩ := hs
    have hcomm : Commute c h := ((Subgroup.mem_centralizer_iff.mp hc) h hh).symm
    have h1 : (c : U →ₗ[ZMod p] U) ((h : U ≃ₗ[ZMod p] U) u) =
        (h : U ≃ₗ[ZMod p] U) ((c : U →ₗ[ZMod p] U) u) := by
      have := congrArg (fun e : U ≃ₗ[ZMod p] U => e u) hcomm.eq
      simpa [LinearEquiv.mul_apply] using this
    rw [map_sub, h1]
    exact Submodule.subset_span ⟨h, hh, (c : U →ₗ[ZMod p] U) u, rfl⟩
  exact hvne (hmap (Submodule.mem_map_of_mem (f := (c : U →ₗ[ZMod p] U)) hv))

private theorem conj_moves_of_fixes {W V0 : Submodule (ZMod p) U} {a b : U ≃ₗ[ZMod p] U}
    (haa : a * a = 1) (hafixW : ∀ w ∈ W, a w = w) (haV0 : ∀ u ∈ V0, a u ∈ V0)
    (hbW : ∃ w ∈ W, b w ∉ W) (hbV : ∃ v ∈ V0, b v ∉ V0) :
    (∃ w ∈ W, (a * b * a) w ∉ W) ∧ ∃ v ∈ V0, (a * b * a) v ∉ V0 := by
  have hback : ∀ x : U, a (a x) = x := fun x => by
    have := congrArg (fun e : U ≃ₗ[ZMod p] U => e x) haa
    simpa [LinearEquiv.mul_apply] using this
  refine ⟨?_, ?_⟩
  · obtain ⟨w, hw, hwne⟩ := hbW
    refine ⟨w, hw, ?_⟩
    have hval : (a * b * a) w = a (b w) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hafixW w hw]
    rw [hval]
    intro hmem
    have hfix := hafixW (a (b w)) hmem
    rw [hback (b w)] at hfix
    exact hwne (hfix.symm ▸ hmem)
  · obtain ⟨v, hv, hvne⟩ := hbV
    refine ⟨a v, haV0 v hv, ?_⟩
    have hval : (a * b * a) (a v) = a (b v) := by
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hback v]
    rw [hval]
    intro hmem
    exact hvne (hback (b v) ▸ haV0 (a (b v)) hmem)

private theorem isRefl_mul_conj {u t : U ≃ₗ[ZMod p] U} (hu : u * u = 1) (ht : IsRefl p t) :
    IsRefl p (u * t * u) := by
  have hu' : u⁻¹ = u := (eq_inv_of_mul_eq_one_right hu).symm
  simpa [hu'] using IsRefl.conj ht u

private theorem moving_refl_conj (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hn : 4 ≤ Module.finrank (ZMod p) U)
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : IsRGroup p G)
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} {a b0 : U ≃ₗ[ZMod p] U}
    (hS : LemmaOneSixSetting F H a (Module.finrank (ZMod p) U - 2)) (hFG : F ≤ G)
    (haV : ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace H,
      a v ∉ HardMathSupport.Kantor79.commutatorSpace H)
    (hb0G : b0 ∈ G) (hb0Refl : IsRefl p b0)
    (hb0W : ∃ w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F,
      b0 w ∉ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
    (hb0V : ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F,
      b0 v ∉ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F)
    (hb0C : b0 ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)))
    (hnotH : ∀ {c : U ≃ₗ[ZMod p] U},
      (∃ w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F, c w ∉
        HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) → c ∉ H) :
    ∃ b ∈ G, IsRefl p b ∧ b ∉ H ∧
      b ∉ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)) ∧
      (∃ w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F,
        b w ∉ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) ∧
      ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F,
        b v ∉ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F := by 
  have haF : a ∈ F := by
    rw [hS.eq_closure]
    exact Subgroup.subset_closure (by simp)
  have hafixW : ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F,
      a w = w := fun w hw => (mem_centralizerSpace.mp hw.2) a haF
  have hV0inv : ∀ f ∈ F, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔
      centralizerSpace F, f v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔
        centralizerSpace F := by
    intro f hf v hv
    rcases Submodule.mem_sup.mp hv with ⟨x, hx, y, hy, rfl⟩
    rw [map_add]
    exact Submodule.add_mem_sup (apply_mem_commutatorSpace hf hx)
      (by rw [(mem_centralizerSpace.mp hy) f hf]; exact hy)
  have haV0 : ∀ u ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F,
      a u ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F := by
    intro u hu
    have hmap := map_eq_self_of_invariant hV0inv haF
    have := Submodule.mem_map_of_mem (f := (a : U →ₗ[ZMod p] U)) hu
    rwa [hmap] at this
  have haa : a * a = 1 := hS.isRefl.1
  obtain ⟨hWmove, hVmove⟩ := conj_moves_of_fixes haa hafixW haV0 hb0W hb0V
  have hconj := hS.conj_not_mem_centralizer hp (by omega) haV hG.2 hFG hb0G hb0Refl hb0W hb0C
  exact ⟨a * b0 * a, G.mul_mem (G.mul_mem (hFG haF) hb0G) (hFG haF),
    isRefl_mul_conj haa hb0Refl, hnotH hWmove, hconj, hWmove, hVmove⟩

theorem exists_splitSupport_enlargement_of_le (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (htab : ∀ m, m < Module.finrank (ZMod p) U → TFNegOrGen p m)
    {G F H' H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hG : IsRGroup p G)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV G) {a : U ≃ₗ[ZMod p] U} {l α : ℕ}
    (hFG : F ≤ G) (hS : LemmaOneSixSetting F H' a l)
    (hn : 2 ≤ Module.finrank (ZMod p) U)
    (hH₁H' : H₁ ≤ H') (hH₁ : ReflGen p H₁) (hH₁s : SplitSupport H₁ α)
    (hdH₁ : ∃ x ∈ H₁, ∃ y ∈ H₁, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    ∃ B : Subgroup (U ≃ₗ[ZMod p] U), B ≤ G ∧ H₁ ≤ B ∧ ⁅H₁, kerSection F⁆ ≤ B ∧
      ReflGen p B ∧ SplitSupport B (α + 2) ∧
      (∃ x ∈ B, ∃ y ∈ B, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) := by
  have hH₁F : H₁ ≤ F := hH₁H'.trans (by
    rw [hS.eq_closure]
    exact fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem a hx))
  have hH₁ne : H₁ ≠ ⊥ := by
    intro hbot
    obtain ⟨x, hx, _, _, hxr, _⟩ := hdH₁
    exact IsRefl.ne_one hxr (Subgroup.mem_bot.mp (by rwa [hbot] at hx))
  have hc : HardMathSupport.Kantor79.commutatorSpace H₁ ⊓ centralizerSpace H₁ = ⊥ :=
    hH₁s.1.disjoint.eq_bot
  obtain ⟨hW_ne_bot, hW_ne_top, hV0_ne_bot, hV0_ne_top⟩ := W_V0_trivial hp hS hn
  obtain ⟨b, hbG, hbRefl, hbW, hbV⟩ :=
    exists_isRefl_moves_two hG.1 hirr hprim hW_ne_bot hW_ne_top hV0_ne_bot hV0_ne_top
  let B : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure
    (insert b ((⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup (U ≃ₗ[ZMod p] U)) : Set _))
  have hB : B = Subgroup.closure
      (insert b ((⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup (U ≃ₗ[ZMod p] U)) : Set _)) := rfl
  obtain ⟨hBrefl, hBirr, hBfin, _⟩ :=
    hS.irredOnSection_closure_insert hp hH₁H' hH₁ hH₁ne hc hbRefl hbW hbV hB
  obtain ⟨hBG, hH₁B⟩ := closure_insert_le' hB hFG hbG hH₁F
  have hT'B : ⁅H₁, kerSection F⁆ ≤ B := by
    rw [hB]
    intro s hs
    exact Subgroup.subset_closure (Set.mem_insert_of_mem b (Subgroup.mem_sup_left hs))
  have hdB : ∃ x ∈ B, ∃ y ∈ B, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
    obtain ⟨x, hx, y, hy, hxr, hyr, hord⟩ := hdH₁
    exact ⟨x, hH₁B hx, y, hH₁B hy, hxr, hyr, hord⟩
  have hSB : SplitSupport B (α + 2) := by
    refine splitSupport_of_irredOnSection hp (l := α + 2) (fun hlt => htab (α + 2) hlt)
      ⟨hBrefl, fun g hg => hG.2 g (hBG hg)⟩ hBirr ?_ hdB
    rw [hBfin, hH₁s.2.1]
  exact ⟨B, hBG, hH₁B, hT'B, hBrefl, hSB, hdB⟩

private noncomputable def enlargement_setup (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (htab : ∀ m, m < Module.finrank (ZMod p) U → TFNegOrGen p m)
    (hcop : ∀ m, m < Module.finrank (ZMod p) U → TFCoprimeWitness p m)
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} (hG : IsRGroup p G)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV G) {l : ℕ}
    (hle : ¬ Module.finrank (ZMod p) U - 2 ≤ l) (hln : l < Module.finrank (ZMod p) U)
    (hHG : H ≤ G) (hH : ReflGen p H) (hHs : SplitSupport H l)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    EnlSetup G H l := by
  replace hle : l < Module.finrank (ZMod p) U - 2 := not_le.mp hle
  have hl2 : 2 ≤ l := two_le_of_splitSupport_dLarge hp hHs (fun g hg => hG.2 g (hHG hg)) hd
  have hln1 : l + 1 < Module.finrank (ZMod p) U := by omega
  have hln2 : l + 2 < Module.finrank (ZMod p) U := by omega
  have hexH := exists_maximal_splitSupport hHG hH hHs
  let H' : Subgroup (U ≃ₗ[ZMod p] U) := Classical.choose hexH
  obtain ⟨hHH', hH'G, hH'refl, hH'split, hmax⟩ := Classical.choose_spec hexH
  have hdH' : ∃ x ∈ H', ∃ y ∈ H', IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
    obtain ⟨x, hx, y, hy, hxr, hyr, hord⟩ := hd
    exact ⟨x, hHH' hx, y, hHH' hy, hxr, hyr, hord⟩
  obtain ⟨hV_ne_bot, hV_ne_top, hC_ne_bot, hC_ne_top⟩ :=
    splitSupport_nontrivial hH'split (by omega) (by omega)
  have hexA := exists_isRefl_moves_two hG.1 hirr hprim hV_ne_bot hV_ne_top hC_ne_bot hC_ne_top
  let a : U ≃ₗ[ZMod p] U := Classical.choose hexA
  obtain ⟨haG, haRefl, haV, _⟩ := Classical.choose_spec hexA
  have hnm := not_mem_of_moves haV
  let F : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure (insert a (H' : Set (U ≃ₗ[ZMod p] U)))
  have hF : F = Subgroup.closure (insert a (H' : Set (U ≃ₗ[ZMod p] U))) := rfl
  have hH'F : H' ≤ F := by
    rw [hF]
    exact fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem a hx)
  have hFG : F ≤ G := by
    rw [hF]
    exact (Subgroup.closure_le _).mpr (Set.insert_subset haG hH'G)
  have hFrefl : ReflGen p F := reflGen_closure_insert hH'refl haRefl hF
  have hdF : ∃ x ∈ F, ∃ y ∈ F, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
    obtain ⟨x, hx, y, hy, hxr, hyr, hord⟩ := hdH'
    exact ⟨x, hH'F hx, y, hH'F hy, hxr, hyr, hord⟩
  have hmax' : ∀ K : Subgroup (U ≃ₗ[ZMod p] U), K ≤ F → H' ≤ K → ReflGen p K →
      SplitSupport K l → K = H' :=
    fun K hKF hH'K hKr hKs => hmax K hH'K (hKF.trans hFG) hKr hKs
  obtain ⟨hFfin, hFdisj⟩ := splitSupport_succ_or_degenerate hp (htab l hln)
    (fun hlt => htab (l + 1) hlt) (hcop l hln) hF
    (fun g hg => hG.2 g (hFG hg)) haRefl hH'refl hH'split hmax' hdH' hnm.1 hnm.2
  exact (⟨H', a, hHH', hH'G, hH'refl, hH'split, hmax', hdH', haRefl, hFG, hFrefl,
    hdF, hFfin, hFdisj, hln2⟩ : EnlSetup G H l)

private theorem enlargement_split [Module.Finite (ZMod p) U]
    {G : Subgroup (U ≃ₗ[ZMod p] U)} {N : ℕ} (ih : EnlIH N G)
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (S : EnlSetup G H l)
    (hN : Module.finrank (ZMod p) U - l = N)
    (hFs : SplitSupport (Subgroup.closure (insert S.a (S.H' : Set (U ≃ₗ[ZMod p] U)))) (l + 1)) :
    EnlGoal G H := by
  let F : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure (insert S.a (S.H' : Set (U ≃ₗ[ZMod p] U)))
  have hH'F : S.H' ≤ F := by
    change S.H' ≤ Subgroup.closure (insert S.a (S.H' : Set (U ≃ₗ[ZMod p] U)))
    exact fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem S.a hx)
  have hln2' : l + 2 < Module.finrank (ZMod p) U := S.hln2
  have hlt : Module.finrank (ZMod p) U - (l + 1) < N := by rw [← hN]; omega
  have hln1 : l + 1 < Module.finrank (ZMod p) U := by omega
  obtain ⟨K, hFK, hKG, hKr, hKs⟩ := ih (Module.finrank (ZMod p) U - (l + 1)) hlt F (l + 1)
    rfl hln1 S.hFG S.hFrefl hFs S.hdF
  exact ⟨K, S.hHH'.trans (hH'F.trans hFK), hKG, hKr, hKs⟩

private theorem enlargement_degenerate (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (htab : ∀ m, m < Module.finrank (ZMod p) U → TFNegOrGen p m)
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : IsRGroup p G)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV G) {N : ℕ} (ih : EnlIH N G)
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {l : ℕ} (S : EnlSetup G H l)
    (hN : Module.finrank (ZMod p) U - l = N)
    (hFdeg : IsDegenerate (Subgroup.closure (insert S.a (S.H' : Set (U ≃ₗ[ZMod p] U)))) S.H') :
    EnlGoal G H := by
  let F : Subgroup (U ≃ₗ[ZMod p] U) := Subgroup.closure (insert S.a (S.H' : Set (U ≃ₗ[ZMod p] U)))
  have hF : F = Subgroup.closure (insert S.a (S.H' : Set (U ≃ₗ[ZMod p] U))) := rfl
  have hS : LemmaOneSixSetting F S.H' S.a l :=
    { eq_closure := hF
      transvectionFree := fun g hg => hG.2 g (S.hFG hg)
      isRefl := S.haRefl
      reflGen := S.hH'refl
      splitSupport := S.hH'split
      maximal := S.hmaxF
      dLarge := S.hdH'
      finrank_eq := S.hFfin
      degenerate := hFdeg }
  have hn : 2 ≤ Module.finrank (ZMod p) U := by
    have h := S.hln2
    omega
  obtain ⟨B, hBG, hH'B, -, hBrefl, hSB, hdB⟩ :=
    exists_splitSupport_enlargement_of_le hp htab hG hirr hprim S.hFG hS hn
      le_rfl S.hH'refl S.hH'split S.hdH'
  have hln2' : l + 2 < Module.finrank (ZMod p) U := S.hln2
  have hlt : Module.finrank (ZMod p) U - (l + 2) < N := by rw [← hN]; omega
  obtain ⟨K, hBK, hKG, hKr, hKs⟩ := ih (Module.finrank (ZMod p) U - (l + 2)) hlt B (l + 2)
    rfl S.hln2 hBG hBrefl hSB hdB
  exact ⟨K, S.hHH'.trans (hH'B.trans hBK), hKG, hKr, hKs⟩

private theorem enlargement_aux (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (htab : ∀ m, m < Module.finrank (ZMod p) U → TFNegOrGen p m)
    (hcop : ∀ m, m < Module.finrank (ZMod p) U → TFCoprimeWitness p m)
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : IsRGroup p G)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV G) :
    ∀ N : ℕ, ∀ (H : Subgroup (U ≃ₗ[ZMod p] U)) (l : ℕ),
      Module.finrank (ZMod p) U - l = N → l < Module.finrank (ZMod p) U → H ≤ G →
        ReflGen p H → SplitSupport H l →
        (∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) →
        ∃ K : Subgroup (U ≃ₗ[ZMod p] U), H ≤ K ∧ K ≤ G ∧ ReflGen p K ∧
          (SplitSupport K (Module.finrank (ZMod p) U - 2) ∨
            SplitSupport K (Module.finrank (ZMod p) U - 1)) := by
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro H l hN hln hHG hH hHs hd
    by_cases hle : Module.finrank (ZMod p) U - 2 ≤ l
    · refine ⟨H, le_rfl, hHG, hH, ?_⟩
      have hl : l = Module.finrank (ZMod p) U - 1 ∨
          l = Module.finrank (ZMod p) U - 2 := by omega
      rcases hl with hl | hl
      · exact Or.inr (hl ▸ hHs)
      · exact Or.inl (hl ▸ hHs)
    · let S := enlargement_setup hp htab hcop hG hirr hprim hle hln hHG hH hHs hd
      rcases S.hdisj with hFs | hFdeg
      · exact enlargement_split ih S hN hFs
      · exact enlargement_degenerate hp htab hG hirr hprim ih S hN hFdeg

theorem exists_splitSupport_enlargement (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (htab : ∀ m, m < Module.finrank (ZMod p) U → TFNegOrGen p m)
    (hcop : ∀ m, m < Module.finrank (ZMod p) U → TFCoprimeWitness p m)
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : IsRGroup p G)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV G) {H : Subgroup (U ≃ₗ[ZMod p] U)}
    (hHG : H ≤ G) (hH : ReflGen p H) {l : ℕ} (hln : l < Module.finrank (ZMod p) U)
    (hHs : SplitSupport H l)
    (hd : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y)) :
    ∃ K : Subgroup (U ≃ₗ[ZMod p] U), H ≤ K ∧ K ≤ G ∧ ReflGen p K ∧
      (SplitSupport K (Module.finrank (ZMod p) U - 2) ∨
        SplitSupport K (Module.finrank (ZMod p) U - 1)) :=
  enlargement_aux hp htab hcop hG hirr hprim
    (Module.finrank (ZMod p) U - l) H l rfl hln hHG hH hHs hd

private theorem exists_maximal_dMax_group [Module.Finite (ZMod p) U]
    {G L : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ} (hLG : L ≤ G) (hLrefl : ReflGen p L)
    (hLs : SplitSupport L (Module.finrank (ZMod p) U - 2)) (hLd : DMax p L d) :
    ∃ H : Subgroup (U ≃ₗ[ZMod p] U), L ≤ H ∧ H ≤ G ∧ ReflGen p H ∧
      SplitSupport H (Module.finrank (ZMod p) U - 2) ∧ DMax p H d ∧
      ∀ K : Subgroup (U ≃ₗ[ZMod p] U), H ≤ K → K ≤ G → ReflGen p K →
        SplitSupport K (Module.finrank (ZMod p) U - 2) → DMax p K d → K = H := by
  classical
  let : Finite U := Module.finite_of_finite (ZMod p)
  let : Fintype U := Fintype.ofFinite U
  let : DecidableEq U := Classical.decEq U
  let : Fintype (U ≃ₗ[ZMod p] U) :=
    Fintype.ofInjective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun e f h => LinearEquiv.ext fun v => congrArg (fun g : U → U => g v) h)
  let : Fintype (Set (U ≃ₗ[ZMod p] U)) := Set.fintype
  let : Fintype (Subgroup (U ≃ₗ[ZMod p] U)) :=
    Fintype.ofInjective (fun K : Subgroup (U ≃ₗ[ZMod p] U) => (K : Set (U ≃ₗ[ZMod p] U)))
      (fun K L h => SetLike.ext (Set.ext_iff.mp h))
  let S : Set (Subgroup (U ≃ₗ[ZMod p] U)) :=
    {K | L ≤ K ∧ K ≤ G ∧ ReflGen p K ∧ SplitSupport K (Module.finrank (ZMod p) U - 2) ∧
      DMax p K d}
  obtain ⟨H, hLH, hmax⟩ :=
    (Set.toFinite S).exists_le_maximal (a := L) ⟨le_rfl, hLG, hLrefl, hLs, hLd⟩
  obtain ⟨hLH', hHG, hHrefl, hHs, hHd⟩ := hmax.1
  refine ⟨H, hLH', hHG, hHrefl, hHs, hHd, ?_⟩
  intro K hHK hKG hKr hKs hKd
  exact le_antisymm (hmax.2 ⟨hLH'.trans hHK, hKG, hKr, hKs, hKd⟩ hHK) hHK

private theorem dMax_of_le {G K : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ} (hKG : K ≤ G)
    (hGd : DMax p G d) {x y : U ≃ₗ[ZMod p] U} (hxK : x ∈ K) (hyK : y ∈ K) (hx : IsRefl p x)
    (hy : IsRefl p y) (hord : orderOf (x * y) = d) : DMax p K d :=
  ⟨fun x' hx' y' hy' hxr hyr => hGd.1 x' (hKG hx') y' (hKG hy') hxr hyr,
    ⟨x, hxK, y, hyK, hx, hy, hord⟩⟩

private theorem succ_or_setting (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hn : 4 ≤ Module.finrank (ZMod p) U)
    (htab : ∀ m, m < Module.finrank (ZMod p) U → TFNegOrGen p m)
    (hcop : ∀ m, m < Module.finrank (ZMod p) U → TFCoprimeWitness p m)
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : IsRGroup p G) {d : ℕ} (hd : DMax p G d) (hd3 : 3 < d)
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (hHG : H ≤ G) (hHrefl : ReflGen p H)
    (hHs : SplitSupport H (Module.finrank (ZMod p) U - 2)) (hHd : DMax p H d)
    (hmax : ∀ K : Subgroup (U ≃ₗ[ZMod p] U), H ≤ K → K ≤ G → ReflGen p K →
      SplitSupport K (Module.finrank (ZMod p) U - 2) → DMax p K d → K = H)
    {c : U ≃ₗ[ZMod p] U} (hcG : c ∈ G) (hc : IsRefl p c) (hcH : c ∉ H)
    (hcC : c ∉ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U))) :
    SplitSupport (Subgroup.closure (insert c (H : Set (U ≃ₗ[ZMod p] U))))
        (Module.finrank (ZMod p) U - 1) ∨
      LemmaOneSixSetting (Subgroup.closure (insert c (H : Set (U ≃ₗ[ZMod p] U)))) H c
        (Module.finrank (ZMod p) U - 2) := by
  let Fc : Subgroup (U ≃ₗ[ZMod p] U) :=
    Subgroup.closure (insert c (H : Set (U ≃ₗ[ZMod p] U)))
  have hFcG : Fc ≤ G := by
    change Subgroup.closure (insert c (H : Set (U ≃ₗ[ZMod p] U))) ≤ G
    exact (Subgroup.closure_le _).mpr (Set.insert_subset hcG hHG)
  have hmax' : ∀ K : Subgroup (U ≃ₗ[ZMod p] U), K ≤ Fc → H ≤ K → ReflGen p K →
      SplitSupport K (Module.finrank (ZMod p) U - 2) → K = H := by
    intro K hKF hHK hKr hKs
    obtain ⟨x, hx, y, hy, hxr, hyr, hord⟩ := hHd.2
    exact hmax K hHK (hKF.trans hFcG) hKr hKs
      (dMax_of_le (hKF.trans hFcG) hd (hHK hx) (hHK hy) hxr hyr hord)
  have hdH : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := by
    obtain ⟨x, hx, y, hy, hxr, hyr, hord⟩ := hHd.2
    exact ⟨x, hx, y, hy, hxr, hyr, by rw [hord]; exact hd3⟩
  have h21 : Module.finrank (ZMod p) U - 2 + 1 = Module.finrank (ZMod p) U - 1 := by omega
  obtain ⟨hfin, hdisj⟩ := splitSupport_succ_or_degenerate hp
    (htab (Module.finrank (ZMod p) U - 2) (by omega))
    (fun _ => by rw [h21]; exact htab (Module.finrank (ZMod p) U - 1) (by omega))
    (hcop (Module.finrank (ZMod p) U - 2) (by omega))
    (F := Fc) (H := H) (a := c) rfl (fun g hg => hG.2 g (hFcG hg)) hc hHrefl hHs hmax' hdH
    hcH hcC
  rcases hdisj with hsplit | hdeg
  · exact Or.inl (by rwa [h21] at hsplit)
  · exact Or.inr
      { eq_closure := rfl
        transvectionFree := fun g hg => hG.2 g (hFcG hg)
        isRefl := hc
        reflGen := hHrefl
        splitSupport := hHs
        maximal := hmax'
        dLarge := hdH
        finrank_eq := hfin
        degenerate := hdeg }

private theorem exists_moving_refl (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hn : 4 ≤ Module.finrank (ZMod p) U)
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : IsRGroup p G)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV G)
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U}
    (hS : LemmaOneSixSetting F H a (Module.finrank (ZMod p) U - 2)) (hFG : F ≤ G)
    (haV : ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace H,
      a v ∉ HardMathSupport.Kantor79.commutatorSpace H) :
    ∃ b ∈ G, IsRefl p b ∧ b ∉ H ∧
      b ∉ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)) ∧
      (∃ w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F,
        b w ∉ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) ∧
      ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F,
        b v ∉ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F := by
  obtain ⟨hW_ne_bot, hW_ne_top, hV0_ne_bot, hV0_ne_top⟩ := W_V0_trivial hp hS (by omega)
  obtain ⟨b0, hb0G, hb0Refl, hb0W, hb0V⟩ :=
    exists_isRefl_moves_two hG.1 hirr hprim hW_ne_bot hW_ne_top hV0_ne_bot hV0_ne_top
  have hHF : H ≤ F := by
    rw [hS.eq_closure]
    exact fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem a hx)
  have hnotH : ∀ {c : U ≃ₗ[ZMod p] U},
      (∃ w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F, c w ∉
        HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F) → c ∉ H := by
    intro c hcW hcH
    obtain ⟨w, hw, hwne⟩ := hcW
    have hwH : w ∈ centralizerSpace H := fun h hh => (mem_centralizerSpace.mp hw.2) h (hHF hh)
    exact hwne ((((mem_centralizerSpace.mp hwH) c hcH).symm) ▸ hw)
  by_cases hb0C : b0 ∈ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U))
  · exact moving_refl_conj hp hn hG hS hFG haV hb0G hb0Refl hb0W hb0V hb0C hnotH

  · exact ⟨b0, hb0G, hb0Refl, hnotH hb0W, hb0C, hb0W, hb0V⟩

private theorem exists_far_refl (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {G : Subgroup (U ≃ₗ[ZMod p] U)} {d : ℕ} (hd : DMax p G d)
    {Fb H : Subgroup (U ≃ₗ[ZMod p] U)} {b : U ≃ₗ[ZMod p] U}
    (hSb : LemmaOneSixSetting Fb H b (Module.finrank (ZMod p) U - 2)) (hFbG : Fb ≤ G)
    {W V0 : Submodule (ZMod p) U} (hWin : ∀ h ∈ H, ∀ w ∈ W, h w ∈ W)
    (hV0in : ∀ h ∈ H, ∀ v ∈ V0, h v ∈ V0)
    (hbW : ∃ w ∈ W, b w ∉ W) (hbV : ∃ v ∈ V0, b v ∉ V0)
    {h₁ h : U ≃ₗ[ZMod p] U} (hh₁H : h₁ ∈ H) (hhH : h ∈ H) (hh₁ : IsRefl p h₁)
    (hh : IsRefl p h) (hord : orderOf (h₁ * h) = d) :
    ∃ g ∈ G, IsRefl p g ∧ g ∉ H ∧ (∃ w ∈ W, g w ∉ W) ∧ (∃ v ∈ V0, g v ∉ V0) ∧
      orderOf (g * h) = d := by
  have hHFb : H ≤ Fb := by
    rw [hSb.eq_closure]
    exact fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem b hx)
  obtain ⟨t, htT, htnotcomm⟩ := hSb.exists_not_commute_kerSection hp hh₁H (IsRefl.ne_one hh₁)
  have htFb : t ∈ Fb := kerSection_le htT
  let g : U ≃ₗ[ZMod p] U := t * h₁ * t⁻¹
  have hgFb : g ∈ Fb := Fb.mul_mem (Fb.mul_mem htFb (hHFb hh₁H)) (Fb.inv_mem htFb)
  have hg : IsRefl p g := IsRefl.conj hh₁ t
  have hgH : g ∉ H := by
    intro hgH
    have hcomm : Commute t h₁ := hSb.commute_of_conj_mem htT hh₁H (by simpa [g] using hgH)
    exact htnotcomm hcomm.symm
  have hgW : ∃ w ∈ W, g w ∉ W :=
    hSb.exists_not_mem_of_not_mem hp hWin hbW hgFb hg hgH
  have hgV : ∃ v ∈ V0, g v ∉ V0 :=
    hSb.exists_not_mem_of_not_mem hp hV0in hbV hgFb hg hgH
  let : Finite (U ≃ₗ[ZMod p] U) := by
    let : Finite U := Module.finite_of_finite (ZMod p)
    exact Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun e f h => LinearEquiv.ext fun v => congrArg (fun g : U → U => g v) h)
  have hdv : d ∣ orderOf (g * h) := by
    have h := hSb.orderOf_mul_dvd_orderOf_conj_mul (x := h₁) (y := h) htT hh₁H hhH
    rw [hord] at h
    exact h
  have hle : orderOf (g * h) ≤ d := hd.1 g (hFbG hgFb) h (hHFb.trans hFbG hhH) hg hh
  have hdd : d ≤ orderOf (g * h) := Nat.le_of_dvd (orderOf_pos (g * h)) hdv
  exact ⟨g, hFbG hgFb, hg, hgH, hgW, hgV, le_antisymm hle hdd⟩

private theorem closure_insert_le_mem {G F H H₁ B : Subgroup (U ≃ₗ[ZMod p] U)}
    {g h : U ≃ₗ[ZMod p] U}
    (hB : B = Subgroup.closure (insert g ((⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup (U ≃ₗ[ZMod p] U)) :
      Set _))) (hFG : F ≤ G) (hgG : g ∈ G) (hH₁H : H₁ ≤ H) (hHF : H ≤ F)
    (hhH₁ : h ∈ H₁) : B ≤ G ∧ g ∈ B ∧ h ∈ B := by
  have hTF : kerSection F ≤ F := kerSection_le
  have hSsubF : ⁅H₁, kerSection F⁆ ≤ F := Subgroup.commutator_le_of_le (hH₁H.trans hHF) hTF
  have hsupF : ⁅H₁, kerSection F⁆ ⊔ H₁ ≤ F := sup_le hSsubF (hH₁H.trans hHF)
  have hBG : B ≤ G := by
    rw [hB]
    refine (Subgroup.closure_le _).mpr ?_
    rintro x (rfl | hx)
    · exact hgG
    · exact hsupF.trans hFG hx
  refine ⟨hBG, ?_, ?_⟩
  · rw [hB]
    exact Subgroup.subset_closure (by simp)
  · rw [hB]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem g (Subgroup.mem_sup_right hhH₁))

private theorem far_subgroup_of_H₁ (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hn : 4 ≤ Module.finrank (ZMod p) U)
    (htab : ∀ m, m < Module.finrank (ZMod p) U → TFNegOrGen p m)
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : IsRGroup p G) {d : ℕ} (hd : DMax p G d) (hd3 : 3 < d)
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U}
    (hS : LemmaOneSixSetting F H a (Module.finrank (ZMod p) U - 2)) (hFG : F ≤ G)
    {H₁ : Subgroup (U ≃ₗ[ZMod p] U)} (hH₁H : H₁ ≤ H) (hH₁refl : ReflGen p H₁)
    (hH₁split : SplitSupport H₁ (Module.finrank (ZMod p) U - 3))
    {g h : U ≃ₗ[ZMod p] U} (hgG : g ∈ G) (hg : IsRefl p g)
    (hgW : ∃ w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F,
      g w ∉ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
    (hgV : ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F,
      g v ∉ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F)
    (hhH₁ : h ∈ H₁) (hh : IsRefl p h) (hord : orderOf (g * h) = d) :
    ∃ N : Subgroup (U ≃ₗ[ZMod p] U), N ≤ G ∧ ReflGen p N ∧
      SplitSupport N (Module.finrank (ZMod p) U - 1) ∧ DMax p N d := by
  have hHF : H ≤ F := by
    rw [hS.eq_closure]
    exact fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem a hx)
  have hc : HardMathSupport.Kantor79.commutatorSpace H₁ ⊓ centralizerSpace H₁ = ⊥ :=
    hH₁split.1.disjoint.eq_bot
  have hH₁ne : H₁ ≠ ⊥ := by
    intro hbot
    exact IsRefl.ne_one hh (Subgroup.mem_bot.mp (by rwa [hbot] at hhH₁))
  let B : Subgroup (U ≃ₗ[ZMod p] U) :=
    Subgroup.closure (insert g ((⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup (U ≃ₗ[ZMod p] U)) : Set _))
  have hB : B = Subgroup.closure
      (insert g ((⁅H₁, kerSection F⁆ ⊔ H₁ : Subgroup (U ≃ₗ[ZMod p] U)) : Set _)) := rfl
  obtain ⟨hBrefl, hBirr, hBfin, _⟩ :=
    hS.irredOnSection_closure_insert hp hH₁H hH₁refl hH₁ne hc hg hgW hgV hB
  obtain ⟨hBG, hgB, hhB⟩ := closure_insert_le_mem hB hFG hgG hH₁H hHF hhH₁
  have hBfin' : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace B) =
      Module.finrank (ZMod p) U - 1 := by
    rw [hBfin, hH₁split.2.1]
    omega
  have hBd : ∃ x ∈ B, ∃ y ∈ B, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) :=
    ⟨g, hgB, h, hhB, hg, hh, by rw [hord]; exact hd3⟩
  have hBS : SplitSupport B (Module.finrank (ZMod p) U - 1) :=
    splitSupport_of_irredOnSection hp (l := Module.finrank (ZMod p) U - 1)
      (fun hlt => htab (Module.finrank (ZMod p) U - 1) hlt)
      ⟨hBrefl, fun x hx => hG.2 x (hBG hx)⟩ hBirr hBfin' hBd
  exact ⟨B, hBG, hBrefl, hBS, dMax_of_le hBG hd hgB hhB hg hh hord⟩

private theorem exists_far_subgroup (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hn : 4 ≤ Module.finrank (ZMod p) U)
    (htab : ∀ m, m < Module.finrank (ZMod p) U → TFNegOrGen p m)
    (hthr : TFThroughRefl p (Module.finrank (ZMod p) U - 2))
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : IsRGroup p G) {d : ℕ} (hd : DMax p G d) (hd3 : 3 < d)
    {F H : Subgroup (U ≃ₗ[ZMod p] U)} {a : U ≃ₗ[ZMod p] U}
    (hS : LemmaOneSixSetting F H a (Module.finrank (ZMod p) U - 2)) (hFG : F ≤ G)
    {g h : U ≃ₗ[ZMod p] U} (hgG : g ∈ G) (hg : IsRefl p g)
    (hgW : ∃ w ∈ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F,
      g w ∉ HardMathSupport.Kantor79.commutatorSpace F ⊓ centralizerSpace F)
    (hgV : ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F,
      g v ∉ HardMathSupport.Kantor79.commutatorSpace F ⊔ centralizerSpace F)
    (hhH : h ∈ H) (hh : IsRefl p h) (hord : orderOf (g * h) = d) :
    ∃ N : Subgroup (U ≃ₗ[ZMod p] U), N ≤ G ∧ ReflGen p N ∧
      SplitSupport N (Module.finrank (ZMod p) U - 1) ∧ DMax p N d := by
  have hHF : H ≤ F := by
    rw [hS.eq_closure]
    exact fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem a hx)
  have hH : IsRGroup p H := ⟨hS.reflGen, fun x hx => hG.2 x (hHF.trans hFG hx)⟩
  have hdH : ∃ x ∈ H, ∃ y ∈ H, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) := hS.dLarge
  obtain ⟨H₁, hH₁H, hhH₁, hH₁refl, hH₁split⟩ :=
    exists_splitSupport_pred_of_isRefl hthr hH hS.splitSupport hdH hhH hh
  have hpred : Module.finrank (ZMod p) U - 2 - 1 = Module.finrank (ZMod p) U - 3 := by omega
  have hH₁split' : SplitSupport H₁ (Module.finrank (ZMod p) U - 3) := by
    rwa [hpred] at hH₁split
  have hpred : Module.finrank (ZMod p) U - 2 - 1 = Module.finrank (ZMod p) U - 3 := by omega
  have hH₁split' : SplitSupport H₁ (Module.finrank (ZMod p) U - 3) := by
    rwa [hpred] at hH₁split
  exact far_subgroup_of_H₁ hp hn htab hG hd hd3 hS hFG hH₁H hH₁refl hH₁split' hgG hg hgW hgV
    hhH₁ hh hord

private theorem exists_moving_refl_of_split [Module.Finite (ZMod p) U]
    (hn : 4 ≤ Module.finrank (ZMod p) U)
    {G H : Subgroup (U ≃ₗ[ZMod p] U)} (hG : IsRGroup p G)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV G)
    (hHs : SplitSupport H (Module.finrank (ZMod p) U - 2)) :
    ∃ a ∈ G, IsRefl p a ∧ a ∉ H ∧
      a ∉ Subgroup.centralizer (H : Set (U ≃ₗ[ZMod p] U)) ∧
      ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace H,
        a v ∉ HardMathSupport.Kantor79.commutatorSpace H := by
  have hV_ne_bot : HardMathSupport.Kantor79.commutatorSpace H ≠ ⊥ := by
    intro hbot
    have h0 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) = 0 := by
      rw [hbot, finrank_bot]
    have := hHs.2.1
    omega
  have hV_ne_top : HardMathSupport.Kantor79.commutatorSpace H ≠ ⊤ := by
    intro htop
    have hfin := hHs.2.1
    rw [htop, finrank_top] at hfin
    omega
  have hC_ne_bot : centralizerSpace H ≠ ⊥ := by
    intro hbot
    have htop : HardMathSupport.Kantor79.commutatorSpace H = ⊤ := by
      have h := hHs.1.sup_eq_top
      rw [hbot, sup_bot_eq] at h
      exact h
    have hfin := hHs.2.1
    rw [htop, finrank_top] at hfin
    omega
  have hC_ne_top : centralizerSpace H ≠ ⊤ := by
    intro htop
    have hbot : HardMathSupport.Kantor79.commutatorSpace H = ⊥ :=
      hHs.1.disjoint.eq_bot_of_le (by rw [htop]; exact le_top)
    have h0 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace H) = 0 := by
      rw [hbot, finrank_bot]
    have := hHs.2.1
    omega
  obtain ⟨a, haG, haRefl, haV, _⟩ :=
    exists_isRefl_moves_two hG.1 hirr hprim hV_ne_bot hV_ne_top hC_ne_bot hC_ne_top
  have hnm := not_mem_of_moves haV
  exact ⟨a, haG, haRefl, hnm.1, hnm.2, haV⟩

private theorem dMax_of_far (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hn : 4 ≤ Module.finrank (ZMod p) U)
    (htab : ∀ m, m < Module.finrank (ZMod p) U → TFNegOrGen p m)
    (hthr : TFThroughRefl p (Module.finrank (ZMod p) U - 2))
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : IsRGroup p G) {d : ℕ} (hd : DMax p G d) (hd3 : 3 < d)
    {H : Subgroup (U ≃ₗ[ZMod p] U)} (hHd : DMax p H d)
    {a b : U ≃ₗ[ZMod p] U} {Fa Fb : Subgroup (U ≃ₗ[ZMod p] U)}
    (hSa : LemmaOneSixSetting Fa H a (Module.finrank (ZMod p) U - 2))
    (hSb : LemmaOneSixSetting Fb H b (Module.finrank (ZMod p) U - 2))
    (hFaG : Fa ≤ G) (hFbG : Fb ≤ G)
    (hbW : ∃ w ∈ HardMathSupport.Kantor79.commutatorSpace Fa ⊓ centralizerSpace Fa,
      b w ∉ HardMathSupport.Kantor79.commutatorSpace Fa ⊓ centralizerSpace Fa)
    (hbV : ∃ v ∈ HardMathSupport.Kantor79.commutatorSpace Fa ⊔ centralizerSpace Fa,
      b v ∉ HardMathSupport.Kantor79.commutatorSpace Fa ⊔ centralizerSpace Fa) :
    ∃ N : Subgroup (U ≃ₗ[ZMod p] U), N ≤ G ∧ ReflGen p N ∧
      SplitSupport N (Module.finrank (ZMod p) U - 1) ∧ DMax p N d := by
  have hHFa : H ≤ Fa := by
    rw [hSa.eq_closure]
    exact fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem a hx)
  have hWinv : ∀ h ∈ H, ∀ w ∈ HardMathSupport.Kantor79.commutatorSpace Fa ⊓
      centralizerSpace Fa, h w ∈ HardMathSupport.Kantor79.commutatorSpace Fa ⊓
        centralizerSpace Fa := by
    intro h hh w hw
    exact ⟨apply_mem_commutatorSpace (hHFa hh) hw.1,
      by rw [(mem_centralizerSpace.mp hw.2) h (hHFa hh)]; exact hw.2⟩
  have hV0inv : ∀ h ∈ H, ∀ v ∈ HardMathSupport.Kantor79.commutatorSpace Fa ⊔
      centralizerSpace Fa, h v ∈ HardMathSupport.Kantor79.commutatorSpace Fa ⊔
        centralizerSpace Fa := by
    intro h hh v hv
    rcases Submodule.mem_sup.mp hv with ⟨x, hx, y, hy, rfl⟩
    rw [map_add]
    exact Submodule.add_mem_sup (apply_mem_commutatorSpace (hHFa hh) hx)
      (by rw [(mem_centralizerSpace.mp hy) h (hHFa hh)]; exact hy)
  obtain ⟨h₁, hh₁H, h, hhH, hh₁, hh, hord₁⟩ := hHd.2
  obtain ⟨g, hgG, hgRefl, hgH, hgW, hgV, hordg⟩ :=
    exists_far_refl hp hd hSb hFbG hWinv hV0inv hbW hbV hh₁H hhH hh₁ hh hord₁
  exact exists_far_subgroup hp hn htab hthr hG hd hd3 hSa hFaG hgG hgRefl hgW hgV
    hhH hh hordg

private theorem dMax_of_splitSupport_pred (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hn : 4 ≤ Module.finrank (ZMod p) U)
    (htab : ∀ m, m < Module.finrank (ZMod p) U → TFNegOrGen p m)
    (hcop : ∀ m, m < Module.finrank (ZMod p) U → TFCoprimeWitness p m)
    (hthr : TFThroughRefl p (Module.finrank (ZMod p) U - 2))
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : IsRGroup p G)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV G) {d : ℕ} (hd : DMax p G d) (hd3 : 3 < d)
    {L : Subgroup (U ≃ₗ[ZMod p] U)} (hLG : L ≤ G) (hLrefl : ReflGen p L)
    (hLs : SplitSupport L (Module.finrank (ZMod p) U - 2)) (hLd : DMax p L d) :
    ∃ N : Subgroup (U ≃ₗ[ZMod p] U), N ≤ G ∧ ReflGen p N ∧
      SplitSupport N (Module.finrank (ZMod p) U - 1) ∧ DMax p N d := by
  obtain ⟨H, hLH, hHG, hHrefl, hHs, hHd, hmax⟩ :=
    exists_maximal_dMax_group hLG hLrefl hLs hLd
  obtain ⟨a, haG, haRefl, haH, haC, haV⟩ :=
    exists_moving_refl_of_split hn hG hirr hprim hHs
  let Fa : Subgroup (U ≃ₗ[ZMod p] U) :=
    Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U)))
  have hFaG : Fa ≤ G := by
    change Subgroup.closure (insert a (H : Set (U ≃ₗ[ZMod p] U))) ≤ G
    exact (Subgroup.closure_le _).mpr (Set.insert_subset haG hHG)
  have hHFa : H ≤ Fa := fun x hx =>
    Subgroup.subset_closure (Set.mem_insert_of_mem a hx)
  rcases succ_or_setting hp hn htab hcop hG hd hd3 hHG hHrefl hHs hHd hmax
      haG haRefl haH haC with hFasplit | hSa
  · have hFarefl : ReflGen p Fa := reflGen_closure_insert hHrefl haRefl rfl
    obtain ⟨x, hx, y, hy, hxr, hyr, hord⟩ := hHd.2
    exact ⟨Fa, hFaG, hFarefl, hFasplit,
      dMax_of_le hFaG hd (hHFa hx) (hHFa hy) hxr hyr hord⟩
  · obtain ⟨b, hbG, hbRefl, hbH, hbC, hbW, hbV⟩ :=
      exists_moving_refl hp hn hG hirr hprim hSa hFaG haV
    let Fb : Subgroup (U ≃ₗ[ZMod p] U) :=
      Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U)))
    have hFbG : Fb ≤ G := by
      change Subgroup.closure (insert b (H : Set (U ≃ₗ[ZMod p] U))) ≤ G
      exact (Subgroup.closure_le _).mpr (Set.insert_subset hbG hHG)
    rcases succ_or_setting hp hn htab hcop hG hd hd3 hHG hHrefl hHs hHd hmax
        hbG hbRefl hbH hbC with hFbsplit | hSb
    · have hHFb : H ≤ Fb := fun x hx =>
        Subgroup.subset_closure (Set.mem_insert_of_mem b hx)
      have hFbrefl : ReflGen p Fb := reflGen_closure_insert hHrefl hbRefl rfl
      obtain ⟨x, hx, y, hy, hxr, hyr, hord⟩ := hHd.2
      exact ⟨Fb, hFbG, hFbrefl, hFbsplit,
        dMax_of_le hFbG hd (hHFb hx) (hHFb hy) hxr hyr hord⟩
    · exact dMax_of_far hp hn htab hthr hG hd hd3 hHd hSa hSb hFaG hFbG hbW hbV

theorem exists_splitSupport_dMax (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    (hn : 4 ≤ Module.finrank (ZMod p) U)
    (htab : ∀ m, m < Module.finrank (ZMod p) U → TFNegOrGen p m)
    (hcop : ∀ m, m < Module.finrank (ZMod p) U → TFCoprimeWitness p m)
    (hthr : TFThroughRefl p (Module.finrank (ZMod p) U - 2))
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : IsRGroup p G)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ g ∈ G, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV G) {d : ℕ} (hd : DMax p G d) (hd3 : 3 < d) :
    ∃ N : Subgroup (U ≃ₗ[ZMod p] U), N ≤ G ∧ ReflGen p N ∧
      SplitSupport N (Module.finrank (ZMod p) U - 1) ∧ DMax p N d := by
  obtain ⟨r₁, hr₁G, r₂, hr₂G, hr₁, hr₂, hordd⟩ := hd.2
  have hpair : 3 < orderOf (r₁ * r₂) := by rw [hordd]; exact hd3
  obtain ⟨K, hr₁K, hr₂K, hKG, hKrefl, hKs⟩ :=
    exists_splitSupport_two_or_three hp hG hirr hprim hr₁G hr₂G hr₁ hr₂ hpair
  have hdK : ∃ x ∈ K, ∃ y ∈ K, IsRefl p x ∧ IsRefl p y ∧ 3 < orderOf (x * y) :=
    ⟨r₁, hr₁K, r₂, hr₂K, hr₁, hr₂, hpair⟩
  have hL : ∃ L : Subgroup (U ≃ₗ[ZMod p] U), K ≤ L ∧ L ≤ G ∧ ReflGen p L ∧
      (SplitSupport L (Module.finrank (ZMod p) U - 2) ∨
        SplitSupport L (Module.finrank (ZMod p) U - 1)) := by
    rcases hKs with hKs | hKs
    · exact exists_splitSupport_enlargement hp htab hcop hG hirr hprim hKG hKrefl
        (l := 2) (by omega) hKs hdK
    · exact exists_splitSupport_enlargement hp htab hcop hG hirr hprim hKG hKrefl
        (l := 3) (by omega) hKs hdK
  obtain ⟨L, hKL, hLG, hLrefl, hLdisj⟩ := hL
  have hLd : DMax p L d := dMax_of_le hLG hd (hKL hr₁K) (hKL hr₂K) hr₁ hr₂ hordd
  rcases hLdisj with hLs | hLs
  · exact dMax_of_splitSupport_pred hp hn htab hcop hthr hG hirr hprim hd hd3 hLG hLrefl hLs hLd
  · exact ⟨L, hLG, hLrefl, hLs, hLd⟩

end CFSG.StandardType.ZS
