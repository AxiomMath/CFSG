module

public import CFSG.YGroups.Exact.Model
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.GroupTheory.SemidirectProduct

public section

namespace CFSG.YGroups.Y442Tw

open CFSG.YGroups CFSG.Certificates.CosetEnumeration

@[expose] def swap442 : ℕ → ℕ
  | 1 => 5
  | 2 => 6
  | 3 => 7
  | 4 => 8
  | 5 => 1
  | 6 => 2
  | 7 => 3
  | 8 => 4
  | c => c

@[expose] def th432 : ℕ → ℕ
  | 1 => 5
  | 2 => 6
  | 3 => 7
  | 5 => 1
  | 6 => 2
  | 7 => 3
  | c => c

theorem swap442_swap442 (c : ℕ) : swap442 (swap442 c) = c := by
  match c with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl
  | c + 9 => rfl

theorem swap442_lt : ∀ c < 11, swap442 c < 11 := by decide

@[expose] def swSpider442 : List ℕ := (List.replicate 10 [0, 5, 6, 0, 1, 2, 0, 9, 10]).flatten

@[expose] def swSp432 : List ℕ := (List.replicate 10 [0, 5, 6, 0, 1, 2, 0, 8, 9]).flatten

theorem swap442_rels : ∀ w ∈ yRels 4 4 2, w.map swap442 ∈ yRels 4 4 2 ∨
    (w.map swap442).reverse ∈ yRels 4 4 2 ∨ w.map swap442 = swSpider442 := by
  decide

theorem swSp432_map : swSp432.map (shiftAt 7) = swSpider442 := by decide

theorem swSp432_lt : ∀ c ∈ swSp432, c < 10 := by decide

theorem swap442_shift : ∀ c < 10, c ≠ 4 → swap442 (shiftAt 7 c) = shiftAt 7 (th432 c) := by
  decide

theorem th432_lt : ∀ c < 10, th432 c < 10 := by decide

theorem rels_y432_y442 : ∀ w ∈ yRels 4 3 2, w.map (shiftAt 7) ∈ yRels 4 4 2 := by decide

@[expose] noncomputable def psi442 : YGroup 4 3 2 →* YGroup 4 4 2 := yHom (shiftAt 7) rels_y432_y442

theorem psi442_yGen {c : ℕ} (hc : c < 10) : psi442 (yGen 4 3 2 c) = yGen 4 4 2 (shiftAt 7 c) :=
  yHom_yGen _ _ (by simp only [ngen]; omega)

theorem evalWord_reverse {G : Type*} [Group G] {g : ℕ → G} (hg : ∀ c, g c * g c = 1)
    (w : List ℕ) : evalWord g w.reverse = (evalWord g w)⁻¹ := by
  induction w with
  | nil => simp [evalWord]
  | cons c w ih =>
    rw [List.reverse_cons, evalWord, List.map_append, List.prod_append, ← evalWord, ih,
      evalWord_cons, mul_inv_rev]
    simp [inv_eq_of_mul_eq_one_right (hg c)]

theorem evalWord_map_hom {G K : Type*} [Group G] [Group K] (f : G →* K) (g : ℕ → G)
    (w : List ℕ) : f (evalWord g w) = evalWord (fun c => f (g c)) w := by
  induction w with
  | nil => simp
  | cons c w ih => rw [evalWord_cons, map_mul, ih, evalWord_cons]

theorem evalWord_comp {G : Type*} [Group G] (g : ℕ → G) (f : ℕ → ℕ) (w : List ℕ) :
    evalWord (fun c => g (f c)) w = evalWord g (w.map f) := by
  induction w with
  | nil => rfl
  | cons c w ih => rw [evalWord_cons, List.map_cons, evalWord_cons, ih]

section
variable (hsw : evalWord (yGen 4 3 2) swSp432 = 1)
include hsw

theorem swSpider442_eq_one : evalWord (yGen 4 4 2) swSpider442 = 1 := by
  rw [← swSp432_map, ← evalWord_comp]
  have h := congrArg psi442 hsw
  rw [map_one, evalWord_map_hom] at h
  rw [← h]
  exact evalWord_congr fun c hc => (psi442_yGen (swSp432_lt c hc)).symm

theorem swGen_rels : ∀ w ∈ yRels 4 4 2, evalWord (fun c => yGen 4 4 2 (swap442 c)) w = 1 := by
  intro w hw
  rw [evalWord_comp]
  rcases swap442_rels w hw with h | h | h
  · exact evalWord_yGen_of_mem h
  · rw [← List.reverse_reverse (w.map swap442), evalWord_reverse (yGen_mul_self 4 4 2),
      evalWord_yGen_of_mem h, inv_one]
  · rw [h]
    exact swSpider442_eq_one hsw

@[expose] noncomputable def sigmaHom : YGroup 4 4 2 →* YGroup 4 4 2 :=
  yModelHom (fun c => yGen 4 4 2 (swap442 c)) (swGen_rels hsw)

theorem sigmaHom_yGen {c : ℕ} (hc : c < 11) :
    sigmaHom hsw (yGen 4 4 2 c) = yGen 4 4 2 (swap442 c) :=
  yModelHom_yGen (by simp only [ngen]; omega)

theorem sigmaHom_sigmaHom (b : YGroup 4 4 2) : sigmaHom hsw (sigmaHom hsw b) = b := by
  have h : (sigmaHom hsw).comp (sigmaHom hsw) = MonoidHom.id _ := by
    refine PresentedGroup.ext fun c => ?_
    have hc : (c : ℕ) < 11 := c.2
    change sigmaHom hsw (sigmaHom hsw (PresentedGroup.of c)) = PresentedGroup.of c
    rw [← yGen_of_lt c.2, sigmaHom_yGen hsw hc, sigmaHom_yGen hsw (swap442_lt c hc),
      swap442_swap442]
  exact DFunLike.congr_fun h b

@[expose] noncomputable def sigma : MulAut (YGroup 4 4 2) :=
  MulEquiv.mk' (Function.Involutive.toPerm _ (sigmaHom_sigmaHom hsw)) (map_mul (sigmaHom hsw))

theorem sigma_apply (b : YGroup 4 4 2) : sigma hsw b = sigmaHom hsw b := rfl

theorem sigma_mul_self : sigma hsw * sigma hsw = 1 := by
  ext b
  exact sigmaHom_sigmaHom hsw b

theorem sigma_psi {c : ℕ} (hc : c < 10) (h4 : c ≠ 4) :
    sigma hsw (psi442 (yGen 4 3 2 c)) = psi442 (yGen 4 3 2 (th432 c)) := by
  rw [sigma_apply, psi442_yGen hc, sigmaHom_yGen hsw (by unfold shiftAt; split_ifs <;> omega),
    swap442_shift c hc h4, psi442_yGen (th432_lt c hc)]

theorem sigma_psi4 : sigma hsw (psi442 (yGen 4 3 2 4)) = yGen 4 4 2 8 := by
  rw [sigma_apply, psi442_yGen (by norm_num), sigmaHom_yGen hsw (by decide)]
  rfl

@[expose] noncomputable def act : Multiplicative (ZMod 2) →* MulAut (YGroup 4 4 2) where
  toFun z := if Multiplicative.toAdd z = 0 then 1 else sigma hsw
  map_one' := by simp
  map_mul' a b := by
    have key : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    have h2 : (1 : ZMod 2) + 1 = 0 := by decide
    rcases key (Multiplicative.toAdd a) with ha | ha <;>
      rcases key (Multiplicative.toAdd b) with hb | hb <;>
      simp [ha, hb, h2, sigma_mul_self hsw]

abbrev Ghat : Type := YGroup 4 4 2 ⋊[act hsw] Multiplicative (ZMod 2)

@[expose] noncomputable def u : Ghat hsw := SemidirectProduct.inr (Multiplicative.ofAdd 1)

@[expose] noncomputable def psiG : YGroup 4 3 2 →* Ghat hsw := SemidirectProduct.inl.comp psi442

theorem u_mul_self : u hsw * u hsw = 1 := by
  rw [u, ← map_mul, ← ofAdd_add]
  have : (1 + 1 : ZMod 2) = 0 := by decide
  rw [this, ofAdd_zero, map_one]

theorem u_inv : (u hsw)⁻¹ = u hsw := inv_eq_of_mul_eq_one_right (u_mul_self hsw)

theorem u_conj_inl (b : YGroup 4 4 2) :
    u hsw * SemidirectProduct.inl b * u hsw = SemidirectProduct.inl (sigma hsw b) := by
  have h := SemidirectProduct.inl_aut (φ := act hsw) (Multiplicative.ofAdd 1) b
  have h1 : act hsw (Multiplicative.ofAdd 1) = sigma hsw := by
    simp [act]
  rw [h1, map_inv] at h
  rw [h]
  change u hsw * _ * u hsw = u hsw * _ * (u hsw)⁻¹
  rw [u_inv]

theorem u_conj {c : ℕ} (hc : c < 10) (h4 : c ≠ 4) :
    u hsw * psiG hsw (yGen 4 3 2 c) * u hsw = psiG hsw (yGen 4 3 2 (th432 c)) := by
  rw [psiG, MonoidHom.comp_apply, u_conj_inl, sigma_psi hsw hc h4, MonoidHom.comp_apply]

theorem commute_48 : Commute (yGen 4 4 2 4) (yGen 4 4 2 8) := by
  have h : [4, 8, 4, 8] ∈ yRels 4 4 2 := by decide
  have h1 := evalWord_yGen_of_mem h
  simp only [evalWord_cons, evalWord_nil, mul_one] at h1
  have e : yGen 4 4 2 4 * yGen 4 4 2 8 = (yGen 4 4 2 4 * yGen 4 4 2 8)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]
    simpa only [mul_assoc] using h1
  unfold Commute SemiconjBy
  rw [e, mul_inv_rev, yGen_inv, yGen_inv]

theorem rel4 : (psiG hsw (yGen 4 3 2 4) * u hsw) ^ 4 = 1 := by
  set e1 : Ghat hsw := psiG hsw (yGen 4 3 2 4)
  set e2 : Ghat hsw := SemidirectProduct.inl (yGen 4 4 2 8)
  have ht : u hsw * e1 * u hsw = e2 := by
    simp only [e1, e2, psiG, MonoidHom.comp_apply, u_conj_inl, sigma_psi4]
  have he1 : e1 = SemidirectProduct.inl (yGen 4 4 2 4) := by
    simp only [e1, psiG, MonoidHom.comp_apply, psi442_yGen (show 4 < 10 by norm_num)]
    rfl
  have hc : e1 * e2 = e2 * e1 := by
    rw [he1, ← map_mul, ← map_mul, Commute.eq (commute_48 hsw)]
  have h1sq : e1 * e1 = 1 := by rw [he1, ← map_mul, yGen_mul_self, map_one]
  have h2sq : e2 * e2 = 1 := by rw [← map_mul, yGen_mul_self, map_one]
  calc (e1 * u hsw) ^ 4 = e1 * (u hsw * e1 * u hsw) * e1 * (u hsw * e1 * u hsw) := by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = e1 * (e2 * e1) * e2 := by rw [ht]; group
    _ = e1 * (e1 * e2) * e2 := by rw [hc]
    _ = (e1 * e1) * (e2 * e2) := by group
    _ = 1 := by rw [h1sq, h2sq, one_mul]

theorem closure_H_u :
    Subgroup.closure (((psiG hsw).range : Set (Ghat hsw)) ∪ {u hsw}) = ⊤ := by
  set K := Subgroup.closure (((psiG hsw).range : Set (Ghat hsw)) ∪ {u hsw})
  have hH : ∀ y, psiG hsw y ∈ K := fun y => Subgroup.subset_closure (Or.inl ⟨y, rfl⟩)
  have hu : u hsw ∈ K := Subgroup.subset_closure (Or.inr rfl)
  have hlet : ∀ c < 11, (SemidirectProduct.inl (yGen 4 4 2 c) : Ghat hsw) ∈ K := by
    intro c hc
    by_cases h8 : c = 8
    · subst h8
      rw [← sigma_psi4 hsw, ← u_conj_inl]
      exact K.mul_mem (K.mul_mem hu (hH _)) hu
    · have hc' : ∃ d < 10, shiftAt 7 d = c := by
        refine ⟨if c ≤ 7 then c else c - 1, by split_ifs <;> omega, ?_⟩
        unfold shiftAt
        split_ifs <;> omega
      obtain ⟨d, hd, rfl⟩ := hc'
      rw [← psi442_yGen hd]
      exact hH _
  have hinl : ∀ b : YGroup 4 4 2, (SemidirectProduct.inl b : Ghat hsw) ∈ K := by
    intro b
    have hb : b ∈ Subgroup.closure (yGen 4 4 2 '' Set.Iio (ngen 4 4 2)) := by
      rw [closure_yGen]
      exact Subgroup.mem_top b
    induction hb using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      exact hlet c (by simpa [ngen] using hc)
    | one => rw [map_one]; exact K.one_mem
    | mul x y _ _ hx hy => rw [map_mul]; exact K.mul_mem hx hy
    | inv x _ hx => rw [map_inv]; exact K.inv_mem hx
  have hinr : ∀ z : Multiplicative (ZMod 2), (SemidirectProduct.inr z : Ghat hsw) ∈ K := by
    intro z
    have key : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
    rcases key (Multiplicative.toAdd z) with h | h
    · have : z = 1 := h
      rw [this, map_one]
      exact K.one_mem
    · have : z = Multiplicative.ofAdd 1 := h
      rw [this]
      exact hu
  rw [eq_top_iff]
  intro g _
  rw [← SemidirectProduct.inl_left_mul_inr_right g]
  exact K.mul_mem (hinl _) (hinr _)

theorem card_Ghat : Nat.card (Ghat hsw) = Nat.card (YGroup 4 4 2) * 2 := by
  rw [Nat.card_congr SemidirectProduct.equivProd, Nat.card_prod,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod 2) ≃ ZMod 2), Nat.card_zmod]

theorem card_range_psiG : Nat.card (psiG hsw).range = Nat.card psi442.range := by
  rw [psiG, MonoidHom.range_comp]
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective _ _ SemidirectProduct.inl_injective).symm.toEquiv

end

end CFSG.YGroups.Y442Tw

end
