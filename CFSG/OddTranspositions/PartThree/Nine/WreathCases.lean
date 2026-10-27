module

public import CFSG.OddTranspositions.HypothesisC
import CFSG.Timmesfeld.Bridge.Asc72WreathConn
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.LocalAnalysis.WeakClosure81.EightFiveGapFivePermA
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Bridge.Asc72Triangle
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72
open CFSG.Timmesfeld.Connectivity CFSG.BenderSuzuki Equiv SemidirectProduct

variable {G : Type} [Group G] [Finite G] {D : Set G}

private theorem apply_mem_of_commute_swap {α : Type} [DecidableEq α] {σ : Perm α} {i j : α}
    (hij : i ≠ j) (h : Commute σ (swap i j)) : σ i = i ∨ σ i = j := by
  rcases (CFSG.LocalAnalysis.WeakClosure81.w85g_mul_swap_commute_iff hij).mp h.eq with
    ⟨h1, -⟩ | ⟨h1, -⟩
  · exact Or.inl h1
  · exact Or.inr h1

private theorem swap_commute_cases {α : Type} [DecidableEq α] {i j k l : α} (hij : i ≠ j)
    (hkl : k ≠ l) (h : Commute (swap i j) (swap k l)) :
    (i = k ∧ j = l) ∨ (i = l ∧ j = k) ∨ (i ≠ k ∧ i ≠ l ∧ j ≠ k ∧ j ≠ l) := by
  rcases (CFSG.LocalAnalysis.WeakClosure81.w85g_mul_swap_commute_iff hij).mp h.symm.eq with
    ⟨hi, hj⟩ | ⟨hi, -⟩
  · refine Or.inr (Or.inr ⟨fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩)
    · rw [← h, swap_apply_left] at hi
      exact hkl (h.symm.trans hi.symm)
    · rw [← h, swap_apply_right] at hi
      exact hkl (hi.trans h)
    · rw [← h, swap_apply_left] at hj
      exact hkl (h.symm.trans hj.symm)
    · rw [← h, swap_apply_right] at hj
      exact hkl (hj.trans h)
  · by_cases hik : i = k
    · rw [← hik, swap_apply_left] at hi
      exact Or.inl ⟨hik, hi.symm⟩
    · by_cases hil : i = l
      · rw [← hil, swap_apply_right] at hi
        exact Or.inr (Or.inl ⟨hil, hi.symm⟩)
      · rw [swap_apply_of_ne_of_ne hik hil] at hi
        exact absurd hi hij

private theorem commute_right {f n : ℕ} {x y : L2Wreath f n} (h : Commute x y) :
    Commute x.right y.right := by
  show x.right * y.right = y.right * x.right
  rw [← mul_right, h.eq, mul_right]

private theorem left_of_isConj_of_right {f n : ℕ} {a b p q : Fin n} (hab : a ≠ b) (hpq : p ≠ q)
    {w : L2Wreath f n} (hw : IsConj (inr (swap a b)) w) (hr : w.right = swap p q) :
    (∀ k, k ≠ p → k ≠ q → w.left k = 1) ∧ w.left q = (w.left p)⁻¹ := by
  obtain ⟨i, j, hij, hwr, hl, hj⟩ := (WreathConn.isConj_inr_swap_iff hab w).mp hw
  have hc : Commute (swap i j) (swap p q) := by
    rw [← hwr, ← hr]
  rcases swap_commute_cases hij hpq hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨hip, hiq, -, -⟩
  · exact ⟨hl, hj⟩
  · refine ⟨fun k hk1 hk2 => hl k hk2 hk1, ?_⟩
    rw [hj, inv_inv]
  · have h := congrArg (fun σ : Perm (Fin n) => σ i) (hwr.symm.trans hr)
    simp only [swap_apply_left, swap_apply_of_ne_of_ne hip hiq] at h
    exact absurd h.symm hij

omit [Finite G] in
theorem disconnected_of_wreath_le_four {f n : ℕ} (h3 : 3 ≤ n) (h4 : n ≤ 4) {a b : Fin n}
    (hab : a ≠ b) (Ψ : G ≃* L2Wreath f n)
    (hΨD : ∀ x, x ∈ D ↔ IsConj (inr (swap a b) : L2Wreath f n) (Ψ x)) :
    Disconnected D := by
  classical
  have hmemD : ∀ w : L2Wreath f n, IsConj (inr (swap a b)) w → Ψ.symm w ∈ D := fun w hw =>
    (hΨD _).mpr (by rwa [MulEquiv.apply_symm_apply])
  obtain ⟨c, hc⟩ : (({a, b} : Finset (Fin n))ᶜ).Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_two (a := a) (b := b)
    omega
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
  obtain ⟨hca, hcb⟩ := hc
  set S : Set G := {x | x ∈ D ∧ Commute (Ψ x).right (swap a b)} with hSdef
  have hclosed : ∀ x ∈ S, ∀ y ∈ D, Commute x y → y ∈ S := by
    rintro x ⟨hx, hxc⟩ y hy hxy
    refine ⟨hy, ?_⟩
    obtain ⟨k, l, hkl, hxr, -, -⟩ := (WreathConn.isConj_inr_swap_iff hab _).mp ((hΨD x).mp hx)
    obtain ⟨k', l', hkl', hyr, -, -⟩ :=
      (WreathConn.isConj_inr_swap_iff hab _).mp ((hΨD y).mp hy)
    have hxy' := commute_right (hxy.map Ψ)
    rw [hxr, hyr] at hxy'
    rw [hxr] at hxc
    rw [hyr]
    rcases swap_commute_cases hkl hab hxc with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨hka, hkb, hla, hlb⟩
    · rw [h1, h2] at hxy'
      exact hxy'.symm
    · rw [h1, h2, swap_comm b a] at hxy'
      exact hxy'.symm
    · rcases swap_commute_cases hkl hkl' hxy' with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, h3, h4⟩
      · rw [← h1, ← h2]
        exact hxc
      · rw [← h1, ← h2, swap_comm l k]
        exact hxc
      ·
        have hk' : k' = a ∨ k' = b := by
          have := a.isLt; have := b.isLt; have := k.isLt; have := l.isLt; have := k'.isLt
          simp only [Fin.ext_iff, ne_eq] at hab hkl hka hkb hla hlb h1 h3 ⊢
          omega
        have hl' : l' = a ∨ l' = b := by
          have := a.isLt; have := b.isLt; have := k.isLt; have := l.isLt; have := l'.isLt
          simp only [Fin.ext_iff, ne_eq] at hab hkl hka hkb hla hlb h2 h4 ⊢
          omega
        rcases hk' with rfl | rfl <;> rcases hl' with rfl | rfl
        · exact absurd rfl hkl'
        · exact Commute.refl _
        · rw [swap_comm]
        · exact absurd rfl hkl'
  have hxS : Ψ.symm (inr (swap a b)) ∈ S :=
    ⟨hmemD _ (IsConj.refl _), by rw [MulEquiv.apply_symm_apply, right_inr]⟩
  refine ⟨_, hxS.1, Ψ.symm (inr (swap a c)),
    hmemD _ (MonoidHom.map_isConj inr (Perm.isConj_swap hab (Ne.symm hca))), fun hreach => ?_⟩
  have h := (mem_of_reach hclosed hxS hreach).2
  rw [MulEquiv.apply_symm_apply, right_inr] at h
  rcases swap_commute_cases (Ne.symm hca) hab h with ⟨-, h1⟩ | ⟨h1, -⟩ | ⟨h1, -⟩
  · exact hcb h1
  · exact hab h1
  · exact h1 rfl

theorem false_of_wreath_five_le (hC : HypothesisC D)
    (hB : IsBenderGroup (Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha))) {f n : ℕ}
    (hn : 5 ≤ n) {a b : Fin n} (hab : a ≠ b) (Ψ : G ≃* L2Wreath f n)
    (hΨu : Ψ hC.d = inr (swap a b))
    (hΨD : ∀ x, x ∈ D ↔ IsConj (inr (swap a b) : L2Wreath f n) (Ψ x)) : False := by
  classical
  have hS := hC.setup
  have hτu : Ψ.symm (inr (swap a b)) = hC.d := by rw [← hΨu, MulEquiv.symm_apply_apply]
  have hmemD : ∀ w : L2Wreath f n, IsConj (inr (swap a b)) w → Ψ.symm w ∈ D := fun w hw =>
    (hΨD _).mpr (by rwa [MulEquiv.apply_symm_apply])
  have hur : (Ψ hC.d).right = swap a b := by rw [hΨu, right_inr]
  have hdisj : ∀ (w : L2Wreath f n) (i j : Fin n), i ≠ j → IsConj (inr (swap a b)) w →
      w.right = swap i j → (∀ k, k ≠ i → k ≠ j → w.left k = 1) → i ≠ a → i ≠ b → j ≠ a →
      j ≠ b → Ψ.symm w ∈ commSet D hC.d := by
    intro w i j hij hw hr hl hia hib hja hjb
    refine ⟨hmemD w hw, ?_, fun h => ?_⟩
    · rw [← hτu]
      exact (WreathConn.commute_of_disjoint (y := inr (swap a b)) hr hl rfl (fun _ _ _ => rfl)
        hia hib hja hjb).map Ψ.symm
    · have h1 : swap i j = swap a b := by
        rw [← hr, ← hur, ← h, MulEquiv.apply_symm_apply]
      have h2 := congrArg (fun σ : Perm (Fin n) => σ i) h1
      simp only [swap_apply_left, swap_apply_of_ne_of_ne hia hib] at h2
      exact hij h2.symm
  have hσ : ∀ g ∈ Subgroup.closure (commSet D hC.d), Commute (Ψ g).right (swap a b) := by
    intro g hg
    have h := commute_right ((OddLocal.commute_of_mem_closure_commSet hg).map Ψ)
    rwa [hur] at h
  obtain ⟨e₀, he₀, hEeq, hmax⟩ := hC.hE
  have he₀E : e₀ ∈ hC.E := by
    rw [hEeq]
    exact OddLocal.self_mem_orbitIn hC.d e₀
  obtain ⟨c₂, hc₂, c₃, hc₃, c₄, hc₄, h23, h24, h34⟩ :
      ∃ c₂ ∈ ({a, b} : Finset (Fin n))ᶜ, ∃ c₃ ∈ ({a, b} : Finset (Fin n))ᶜ,
        ∃ c₄ ∈ ({a, b} : Finset (Fin n))ᶜ, c₂ ≠ c₃ ∧ c₂ ≠ c₄ ∧ c₃ ≠ c₄ := by
    rw [← Finset.two_lt_card, Finset.card_compl, Fintype.card_fin]
    have := Finset.card_le_two (a := a) (b := b)
    omega
  simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hc₂ hc₃ hc₄
  have hA : (Ψ e₀).right ≠ swap a b := by
    intro he₀r
    set P : Set G := {x | x ∈ D ∧ (Ψ x).right = swap a b} with hP
    have hEP : hC.E ⊆ P \ {hC.d} := by
      rw [hEeq]
      rintro _ ⟨g, hg, rfl⟩
      refine ⟨⟨hS.conj_mem g he₀.1, ?_⟩,
        (OddLocal.orbitIn_subset_commSet hS.normal he₀ ⟨g, hg, rfl⟩).2.2⟩
      rw [map_mul, map_mul, map_inv, mul_right, mul_right, inv_right, he₀r, (hσ g hg).eq,
        mul_inv_cancel_right]
    have huP : hC.d ∈ P := ⟨hC.hd, hur⟩
    have hPL : P.ncard ≤ Nat.card (PSL2Model f) := by
      rw [← Set.ncard_univ]
      refine Set.ncard_le_ncard_of_injOn (fun x => (Ψ x).left a) (fun _ _ => Set.mem_univ _)
        (fun x hx x' hx' hxx' => Ψ.injective ?_)
      have hxx'' : (Ψ x).left a = (Ψ x').left a := hxx'
      obtain ⟨h1, h1'⟩ := left_of_isConj_of_right hab hab ((hΨD x).mp hx.1) hx.2
      obtain ⟨h2, h2'⟩ := left_of_isConj_of_right hab hab ((hΨD x').mp hx'.1) hx'.2
      refine SemidirectProduct.ext (funext fun k => ?_) (hx.2.trans hx'.2.symm)
      by_cases hka : k = a
      · rw [hka, hxx'']
      by_cases hkb : k = b
      · rw [hkb, h1', h2', hxx'']
      · rw [h1 k hka hkb, h2 k hka hkb]
    set y : G := Ψ.symm (inr (swap c₂ c₃)) with hy
    have hyD : y ∈ commSet D hC.d :=
      hdisj _ c₂ c₃ h23 (MonoidHom.map_isConj inr (Perm.isConj_swap hab h23)) rfl
        (fun _ _ _ => rfl) hc₂.1 hc₂.2 hc₃.1 hc₃.2
    set Z : PSL2Model f → L2Wreath f n :=
      fun d => ⟨Pi.mulSingle c₃ d * Pi.mulSingle c₄ d⁻¹, swap c₃ c₄⟩ with hZdef
    have hZl : ∀ d, ∀ k, k ≠ c₃ → k ≠ c₄ → (Z d).left k = 1 := fun d k h3 h4 => by
      simp only [hZdef, Pi.mul_apply, Pi.mulSingle_eq_of_ne h3, Pi.mulSingle_eq_of_ne h4,
        mul_one]
    have hZ : ∀ d, Ψ.symm (Z d) ∈ commSet D hC.d := by
      intro d
      refine hdisj (Z d) c₃ c₄ h34 ((WreathConn.isConj_inr_swap_iff hab _).mpr
        ⟨c₃, c₄, h34, rfl, hZl d, ?_⟩) rfl (hZl d) hc₃.1 hc₃.2 hc₄.1 hc₄.2
      simp only [hZdef, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne h34,
        Pi.mulSingle_eq_of_ne h34.symm, one_mul, mul_one]
    set F : PSL2Model f → G := fun d => Ψ.symm (Z d) * y * (Ψ.symm (Z d))⁻¹ with hFdef
    have hF : ∀ d, F d ∈ orbitIn D hC.d y := fun d =>
      ⟨_, Subgroup.subset_closure (hZ d), rfl⟩
    have hFl : ∀ d, (Ψ (F d)).left c₂ = d := by
      intro d
      have hΨF : Ψ (F d) = Z d * inr (swap c₂ c₃) * (Z d)⁻¹ := by
        simp only [hFdef, hy, map_mul, map_inv, MulEquiv.apply_symm_apply]
      have hr : (Z d).right * swap c₂ c₃ * (Z d).right⁻¹ = swap c₄ c₂ := by
        show swap c₃ c₄ * swap c₂ c₃ * (swap c₃ c₄)⁻¹ = swap c₄ c₂
        rw [swap_inv, swap_mul_swap_mul_swap h23 h24]
      rw [hΨF, WreathConn.conj_inr_left, hr, swap_inv, swap_apply_right]
      simp only [hZdef, Pi.mul_apply, Pi.mulSingle_eq_of_ne h23, Pi.mulSingle_eq_of_ne h24,
        Pi.mulSingle_eq_of_ne h34.symm, Pi.mulSingle_eq_same, one_mul, inv_inv]
    have hLO : Nat.card (PSL2Model f) ≤ (orbitIn D hC.d y).ncard := by
      rw [← Set.ncard_univ]
      refine Set.ncard_le_ncard_of_injOn F (fun d _ => hF d) (fun d _ d' _ h => ?_)
      rw [← hFl d, ← hFl d', h]
    have h1 := Set.ncard_le_ncard hEP
    have h2 := Set.ncard_sdiff_singleton_lt_of_mem huP
    have h3 := hmax y hyD
    omega
  obtain ⟨k, l, hkl, hr₀, -, -⟩ :=
    (WreathConn.isConj_inr_swap_iff hab _).mp ((hΨD e₀).mp he₀.1)
  have hc₀ : Commute (swap k l) (swap a b) := by
    have h := commute_right (he₀.2.1.map Ψ)
    rwa [hr₀, hur] at h
  obtain ⟨hka, hkb, hla, hlb⟩ : k ≠ a ∧ k ≠ b ∧ l ≠ a ∧ l ≠ b := by
    rcases swap_commute_cases hkl hab hc₀ with ⟨h1, h2⟩ | ⟨h1, h2⟩ | h
    · rw [h1, h2] at hr₀
      exact absurd hr₀ hA
    · rw [h1, h2, swap_comm b a] at hr₀
      exact absurd hr₀ hA
    · exact h
  have hHE : ∀ x ∈ hC.E, x ∈ Halpha D hC.alpha := fun x hx =>
    Subgroup.subset_closure (hC.DalphaStar_alpha.symm ▸ hx)
  have hEfix : ∀ x ∈ hC.E, (Ψ x).right a = a ∧ (Ψ x).right b = b := by
    intro x hx
    rw [hEeq] at hx
    obtain ⟨g, hg, rfl⟩ := hx
    have hg' := (hσ g hg).inv_left
    have hfix : ∀ p, p = a ∨ p = b → swap k l p = p := by
      rintro p (rfl | rfl)
      · exact swap_apply_of_ne_of_ne (Ne.symm hka) (Ne.symm hla)
      · exact swap_apply_of_ne_of_ne (Ne.symm hkb) (Ne.symm hlb)
    have hg'' : Commute (Ψ g).right⁻¹ (swap b a) := by
      rw [swap_comm]
      exact hg'
    have ha' := apply_mem_of_commute_swap hab hg'
    have hb' := apply_mem_of_commute_swap (Ne.symm hab) hg''
    simp only [map_mul, map_inv, mul_right, inv_right, hr₀, Perm.mul_apply]
    exact ⟨by rw [hfix _ ha']; simp, by rw [hfix _ hb'.symm]; simp⟩
  have hHfix : ∀ h ∈ Halpha D hC.alpha, (Ψ h).right a = a ∧ (Ψ h).right b = b := by
    intro h (hh : h ∈ Subgroup.closure (DalphaStar D hC.alpha))
    induction hh using Subgroup.closure_induction with
    | mem x hx => exact hEfix x (hC.DalphaStar_alpha ▸ hx)
    | one => simp
    | mul x y _ _ hx hy =>
      simp only [map_mul, mul_right, Perm.mul_apply, hy.1, hy.2, hx.1, hx.2, and_self]
    | inv x _ hx =>
      rw [map_inv, inv_right]
      exact ⟨Perm.inv_eq_iff_eq.mpr hx.1.symm, Perm.inv_eq_iff_eq.mpr hx.2.symm⟩
  have hcenter : ∀ z ∈ Subgroup.center (Halpha D hC.alpha), (Ψ (z : G)).right = 1 := by
    intro z hz
    have hcz : ∀ x ∈ hC.E, Commute (Ψ (z : G)).right (Ψ x).right := by
      intro x hx
      have h1 := Subgroup.mem_center_iff.mp hz ⟨x, hHE x hx⟩
      have h2 : Commute (z : G) x := (congrArg Subtype.val h1).symm
      exact commute_right (h2.map Ψ)
    have hconj : ∀ i j : Fin n, i ≠ j → i ≠ a → i ≠ b → j ≠ a → j ≠ b →
        Commute (Ψ (z : G)).right (swap i j * swap k l * swap i j) := by
      intro i j hij hia hib hja hjb
      have hw := hdisj (inr (swap i j)) i j hij (MonoidHom.map_isConj inr
        (Perm.isConj_swap hab hij)) rfl (fun _ _ _ => rfl) hia hib hja hjb
      have hx : Ψ.symm (inr (swap i j)) * e₀ * (Ψ.symm (inr (swap i j)))⁻¹ ∈ hC.E := by
        rw [hEeq]
        exact ⟨_, Subgroup.subset_closure hw, rfl⟩
      have h := hcz _ hx
      rwa [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, mul_right, mul_right,
        inv_right, right_inr, hr₀, swap_inv] at h
    have hk : Commute (Ψ (z : G)).right (swap k l) := by
      rw [← hr₀]
      exact hcz e₀ he₀E
    have hzH := hHfix z z.2
    obtain ⟨m, hm⟩ : (({a, b, k, l} : Finset (Fin n))ᶜ).Nonempty := by
      rw [← Finset.card_pos, Finset.card_compl, Fintype.card_fin]
      have := Finset.card_le_four (a := a) (b := b) (c := k) (d := l)
      omega
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    obtain ⟨hma, hmb, hmk, hml⟩ := hm
    refine Perm.ext fun p => ?_
    rw [Perm.one_apply]
    by_cases hpa : p = a
    · rw [hpa]
      exact hzH.1
    by_cases hpb : p = b
    · rw [hpb]
      exact hzH.2
    by_cases hpk : p = k
    · rw [hpk]
      have h1 := apply_mem_of_commute_swap hkl hk
      have h2 := hconj l m (Ne.symm hml) hla hlb hma hmb
      rw [swap_mul_swap_mul_swap hkl (Ne.symm hmk), swap_comm m k] at h2
      rcases h1 with h1 | h1
      · exact h1
      rcases apply_mem_of_commute_swap (Ne.symm hmk) h2 with h3 | h3
      · exact h3
      · exact absurd (h1.symm.trans h3) (Ne.symm hml)
    by_cases hpl : p = l
    · rw [hpl]
      have hk' : Commute (Ψ (z : G)).right (swap l k) := by
        rw [swap_comm]
        exact hk
      have h1 := apply_mem_of_commute_swap (Ne.symm hkl) hk'
      have h2 := hconj k m (Ne.symm hmk) hka hkb hma hmb
      rw [swap_comm k l, swap_mul_swap_mul_swap (Ne.symm hkl) (Ne.symm hml), swap_comm m l]
        at h2
      rcases h1 with h1 | h1
      · exact h1
      rcases apply_mem_of_commute_swap (Ne.symm hml) h2 with h3 | h3
      · exact h3
      · exact absurd (h1.symm.trans h3) (Ne.symm hmk)
    · have h1 := hconj l p (Ne.symm hpl) hla hlb hpa hpb
      rw [swap_mul_swap_mul_swap hkl (Ne.symm hpk)] at h1
      have h2 := hconj k p (Ne.symm hpk) hka hkb hpa hpb
      rw [swap_comm k l, swap_mul_swap_mul_swap (Ne.symm hkl) (Ne.symm hpl)] at h2
      rcases apply_mem_of_commute_swap hpk h1 with h3 | h3
      · exact h3
      rcases apply_mem_of_commute_swap hpl h2 with h4 | h4
      · exact h4
      · exact absurd (h3.symm.trans h4) hkl
  have := IsBenderGroup.isSimpleGroup hB
  obtain ⟨q₁, q₂, hq⟩ := IsBenderGroup.exists_not_commute hB
  let φ : Halpha D hC.alpha →* ℤˣ :=
    Perm.sign.comp (rightHom.comp (Ψ.toMonoidHom.comp (Halpha D hC.alpha).subtype))
  have hφZ : Subgroup.center (Halpha D hC.alpha) ≤ φ.ker := fun z hz => by
    rw [MonoidHom.mem_ker]
    show Perm.sign (Ψ (z : G)).right = 1
    rw [hcenter z hz, map_one]
  let ψ := QuotientGroup.lift (Subgroup.center (Halpha D hC.alpha)) φ hφZ
  have hψ : ψ (⟨e₀, hHE e₀ he₀E⟩ : Halpha D hC.alpha) = -1 := by
    rw [QuotientGroup.lift_mk]
    show Perm.sign (Ψ e₀).right = -1
    rw [hr₀, Perm.sign_swap hkl]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
  · exact hq (((MonoidHom.ker_eq_bot_iff ψ).mp h) (by rw [map_mul, map_mul, mul_comm]))
  · have hmem : ((⟨e₀, hHE e₀ he₀E⟩ : Halpha D hC.alpha) :
        Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha)) ∈ ψ.ker :=
      h ▸ Subgroup.mem_top _
    rw [MonoidHom.mem_ker, hψ] at hmem
    exact absurd hmem (by decide)

end CFSG.OddTranspositions.PartThree.Nine
