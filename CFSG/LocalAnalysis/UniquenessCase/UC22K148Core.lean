module

public import CFSG.LocalAnalysis.UniquenessCase.UCFrontExt
public import CFSG.LocalAnalysis.UniquenessCase.UC22K148Strip
import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.CommLemmas
import CFSG.RankThree.FFModules.FixSubConj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K148

open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem commOn_le_fixSub_of_commute {X Y : Subgroup G} (U : Submodule (ZMod 2) V)
    (hc : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) (hY : ∀ y ∈ Y, ∀ n ∈ commOn ρ X ⊤, ρ y n = n) :
    commOn ρ Y U ≤ fixSub ρ X := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨y, hy, w, -, rfl⟩
  refine SetLike.mem_coe.2 (mem_fixSub.2 fun x hx => ?_)
  have h1 : ρ x (ρ y w) = ρ y (ρ x w) := by
    rw [← Module.End.mul_apply, ← map_mul, hc x hx y hy, map_mul, Module.End.mul_apply]
  have h2 : ρ y (ρ x w - w) = ρ x w - w := hY y hy _ (sub_mem_commOn hx Submodule.mem_top)
  rw [map_sub, sub_eq_iff_eq_add] at h2
  rw [map_sub, h1, h2]
  abel

theorem mem_iSup_of_forall_apply_eq {m : ℕ} {Hs : Fin m → Subgroup G}
    (hD : IsInternalDirect ⊤ Hs) {N : Fin m → Submodule (ZMod 2) V} {J : Finset (Fin m)}
    (hF0 : ∀ k ∈ J, ∀ i, i ≠ k → ∀ h ∈ Hs i, ∀ n ∈ N k, ρ h n = n)
    (hfaith : ∀ k ∈ J, ∀ h ∈ Hs k, (∀ n ∈ N k, ρ h n = n) → h = 1) {g : G}
    (hg : ∀ k ∈ J, ∀ n ∈ N k, ρ g n = n) : g ∈ ⨆ (i : Fin m) (_ : i ∉ J), Hs i := by
  classical
  have hcomm : Pairwise fun i j : Fin m => ∀ x y : G, x ∈ Hs i → y ∈ Hs j → Commute x y :=
    fun i j hij x y hx hy => hD.2.1 i j hij x hx y hy
  obtain ⟨x, rfl⟩ : g ∈ (Subgroup.noncommPiCoprod hcomm).range := by
    rw [Subgroup.noncommPiCoprod_range, hD.1]
    exact Subgroup.mem_top g
  have hx1 : ∀ k ∈ J, x k = 1 := fun k hk => by
    have hsplit : x = Pi.mulSingle k (x k) * Function.update x k 1 := by
      funext i
      by_cases hik : i = k
      · subst hik
        rw [Pi.mul_apply, Pi.mulSingle_eq_same, Function.update_self, mul_one]
      · rw [Pi.mul_apply, Pi.mulSingle_eq_of_ne hik, Function.update_of_ne hik, one_mul]
    have hy : Subgroup.noncommPiCoprod hcomm (Function.update x k 1) ∈ cenOn ρ ⊤ (N k) := by
      rw [Subgroup.noncommPiCoprod_apply]
      refine Subgroup.noncommProd_mem _ _ fun i _ => ?_
      by_cases hik : i = k
      · subst hik
        rw [Function.update_self, OneMemClass.coe_one]
        exact (cenOn ρ ⊤ (N i)).one_mem
      · rw [Function.update_of_ne hik]
        exact mem_cenOn.2 ⟨Subgroup.mem_top _, hF0 k hk i hik _ (x i).2⟩
    have hxk : ∀ n ∈ N k, ρ (x k : G) n = n := fun n hn => by
      have h := hg k hk n hn
      rw [hsplit, map_mul, Subgroup.noncommPiCoprod_mulSingle, map_mul, Module.End.mul_apply,
        (mem_cenOn.1 hy).2 n hn] at h
      exact h
    exact Subtype.ext (hfaith k hk _ (x k).2 hxk)
  rw [Subgroup.noncommPiCoprod_apply]
  refine Subgroup.noncommProd_mem _ _ fun i _ => ?_
  by_cases hi : i ∈ J
  · rw [hx1 i hi, OneMemClass.coe_one]
    exact Subgroup.one_mem _
  · exact Subgroup.mem_iSup_of_mem i (Subgroup.mem_iSup_of_mem hi (x i).2)

theorem commOn_zpowers_le_fixSub_top [Finite G] [Finite V] (hH : hP ρ = ⊤) {m : ℕ}
    {Hs : Fin m → Subgroup G} (hD : IsInternalDirect ⊤ Hs) {O : Fin m → Subgroup G}
    {J : Finset (Fin m)} (hOH : ∀ k ∈ J, O k ≤ Hs k) (hperf : ∀ i ∉ J, O i = Hs i)
    (hON : ∀ k ∈ J, (O k).Normal)
    (hF0 : ∀ i j, i ≠ j → ∀ h ∈ Hs j, ∀ n ∈ commOn ρ (O i) ⊤, ρ h n = n)
    (hfaith : ∀ k ∈ J, ∀ h ∈ Hs k, (∀ n ∈ commOn ρ (O k) ⊤, ρ h n = n) → h = 1)
    (hcompl : ∀ k ∈ J, IsCompl (commOn ρ (O k) ⊤) (fixSub ρ (O k)))
    (hNE : ∀ k ∈ J, ∀ X : Subgroup G, CFSG.Open.IsElemAbelian 2 X →
      NoExcess ρ X (commOn ρ (O k) ⊤))
    {j : Fin m} (hj : j ∈ J) {u : G} (hu : u ∈ Hs j) :
    commOn ρ (Subgroup.zpowers u) (fixSub ρ (O j)) ≤ fixSub ρ ⊤ := by
  set T := commOn ρ (Subgroup.zpowers u) (fixSub ρ (O j)) with hTdef
  have hYj : Subgroup.zpowers u ≤ Hs j := Subgroup.zpowers_le.2 hu
  have hF1 : ∀ i, i ≠ j → ∀ X ≤ Hs i, (∀ y ∈ Hs j, ∀ n ∈ commOn ρ X ⊤, ρ y n = n) →
      T ≤ fixSub ρ X := fun i hij X hX hYX =>
    commOn_le_fixSub_of_commute _ (fun x hx y hy => hD.2.1 i j hij x (hX hx) y (hYj hy))
      fun y hy n hn => hYX y (hYj hy) n hn
  have hTW : ∀ k ∈ J, T ≤ fixSub ρ (O k) := fun k hk => by
    by_cases hkj : k = j
    · subst hkj
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, -, w, hw, rfl⟩
      exact sub_mem (rep_apply_mem_fixSub_of_normal ρ (hON k hk) y hw) hw
    · exact hF1 k hkj (O k) (hOH k hk) (hF0 k j hkj)
  have hTH : ∀ i ∉ J, T ≤ fixSub ρ (Hs i) := fun i hi => by
    have hij : i ≠ j := fun h => hi (h ▸ hj)
    refine hF1 i hij (Hs i) le_rfl ?_
    rw [← hperf i hi]
    exact hF0 i j hij
  have hdet : ∀ b : G, (∀ k ∈ J, ∀ n ∈ commOn ρ (O k) ⊤, ρ b n = n) → ∀ t ∈ T, ρ b t = t := by
    intro b hb t ht
    have hmem := mem_iSup_of_forall_apply_eq hD
      (fun k _ i hik h hh n hn => hF0 k i (Ne.symm hik) h hh n hn) hfaith hb
    have hle : (⨆ (i : Fin m) (_ : i ∉ J), Hs i) ≤ cenOn ρ ⊤ T := iSup₂_le fun i hi x hx =>
      mem_cenOn.2 ⟨Subgroup.mem_top x, fun t ht => mem_fixSub.1 (hTH i hi ht) x hx⟩
    exact (mem_cenOn.1 (hle hmem)).2 t ht
  have hinv : ∀ k ∈ J, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ ⊤ (commOn ρ (O k) ⊤) ∧ CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ ⊤ (fixSub ρ (O k)) :=
    fun k hk => by
      have hNk : (⊤ : Subgroup G) ≤ Subgroup.normalizer (O k : Set G) := by
        rw [Subgroup.normalizer_eq_top_iff.2 (hON k hk)]
      exact ⟨(invariant_commOn_top hNk).2,
        fun a _ w hw => rep_apply_mem_fixSub_of_normal ρ (hON k hk) a hw⟩
  have hTA : ∀ A ∈ calP ρ, T ≤ fixSub ρ A := fun A hA => by
    have hA' : A ≠ ⊥ ∧ CFSG.Open.IsElemAbelian 2 A ∧ IsBestOffender ρ A := hA
    refine le_fixSub_of_strip (fun k => commOn ρ (O k) ⊤) (fun k => fixSub ρ (O k)) J hA'.2.2
      (fun k hk => ⟨hcompl k hk, fun a _ => (hinv k hk).1 a (Subgroup.mem_top a),
        fun a _ => (hinv k hk).2 a (Subgroup.mem_top a), hTW k hk,
        fun X hX => hNE k hk X (hA'.2.1.mono hX)⟩) fun b _ hb => hdet b hb
  have hle : hP ρ ≤ cenOn ρ ⊤ T := iSup₂_le fun A hA x hx =>
    mem_cenOn.2 ⟨Subgroup.mem_top x, fun t ht => mem_fixSub.1 (hTA A hA ht) x hx⟩
  intro t ht
  refine mem_fixSub.2 fun x _ => ?_
  have hx : x ∈ hP ρ := by
    rw [hH]
    exact Subgroup.mem_top x
  exact (mem_cenOn.1 (hle hx)).2 t ht

end CFSG.LocalAnalysis.UniquenessCase.UC22.K148
