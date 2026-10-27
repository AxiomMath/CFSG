module

public import CFSG.Quasithin.Background.C116Two.ModAdapters
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.Quasithin.C116Two

open CFSG.QuasithinUnique CFSG.Open

theorem permAct_injective {m : ℕ} (hm : 3 ≤ m) : Function.Injective (permAct m) := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  intro σ hσ
  apply perm_eq_one_of_fixes_evenWeight hm σ
  intro x i
  have h1 : permAct m σ = 1 := hσ
  have := congrArg (fun φ => ((Multiplicative.toAdd (φ (Multiplicative.ofAdd x)) :
    evenWeight m) : Fin m → ZMod 2) i) h1
  simp only [permAct_apply, MulAut.one_apply, toAdd_ofAdd] at this
  exact this.symm

private theorem permAct_fixed_iff {m : ℕ} (σ : Equiv.Perm (Fin m)) (x : Multiplicative (evenWeight m)) :
    permAct m σ x = x ↔ ∀ i, ((Multiplicative.toAdd x : evenWeight m) : Fin m → ZMod 2) (σ⁻¹ i) =
      ((Multiplicative.toAdd x : evenWeight m) : Fin m → ZMod 2) i := by
  constructor
  · intro h i
    have h' := congrArg (fun z => ((Multiplicative.toAdd z : evenWeight m) : Fin m → ZMod 2) i) h
    simpa only [permAct_apply] using h'
  · intro h
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    rw [permAct_apply]
    exact h i

private theorem zmod2_add_self : ∀ c : ZMod 2, c + c = 0 := by decide

private theorem zmod2_cases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private theorem zmod2_ite_one_mul : ∀ c v : ZMod 2, (if c = 1 then v else 0) = c * v := by decide

private def pairW (m : ℕ) (i j : Fin m) : Fin m → ZMod 2 :=
  fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0)

private theorem pairW_apply {m : ℕ} (i j k : Fin m) :
    pairW m i j k = (if k = i then 1 else 0) + (if k = j then 1 else 0) := rfl

private theorem pairW_mem (m : ℕ) (i j : Fin m) : pairW m i j ∈ evenWeight m := by
  show ∑ k, pairW m i j k = 0
  unfold pairW
  rw [Finset.sum_add_distrib]
  simp
  decide

private theorem pairW_self {m : ℕ} (p : Fin m) : pairW m p p = 0 := by
  funext k
  rw [pairW_apply, Pi.zero_apply]
  exact zmod2_add_self _

private theorem exists_not_mem_four {m : ℕ} (h5 : 5 ≤ m) (a b c d : Fin m) :
    ∃ r : Fin m, r ≠ a ∧ r ≠ b ∧ r ≠ c ∧ r ≠ d := by
  obtain ⟨r, -, hr⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({a, b, c, d} : Finset (Fin m))) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin]; exact lt_of_le_of_lt Finset.card_le_four (by omega))
  refine ⟨r, ?_, ?_, ?_, ?_⟩ <;> intro h <;> apply hr <;> simp [h]

private theorem permAct_pairW_fixed {m : ℕ} (σ : Equiv.Perm (Fin m)) {i j : Fin m}
    (h : (σ i = i ∧ σ j = j) ∨ (σ i = j ∧ σ j = i)) (x : Multiplicative (evenWeight m))
    (hx : ((Multiplicative.toAdd x : evenWeight m) : Fin m → ZMod 2) = pairW m i j) :
    permAct m σ x = x := by
  rw [permAct_fixed_iff]
  intro k
  rw [hx]
  simp only [pairW_apply]
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [Equiv.Perm.inv_eq_iff_eq, h1, h2]
  · simp only [Equiv.Perm.inv_eq_iff_eq, h1, h2]
    exact add_comm _ _

private theorem altOdd_fix_pair {m : ℕ} (hm : Odd m) (h5 : 5 ≤ m)
    (g : MulAut (Multiplicative (evenWeight m)))
    (hg : ∀ τ : alternatingGroup (Fin m), g * altAct m τ = altAct m τ * g)
    {i j : Fin m} (hij : i ≠ j) :
    g (Multiplicative.ofAdd ⟨pairW m i j, pairW_mem m i j⟩) =
      Multiplicative.ofAdd ⟨pairW m i j, pairW_mem m i j⟩ := by
  set dy : Multiplicative (evenWeight m) := Multiplicative.ofAdd ⟨pairW m i j, pairW_mem m i j⟩ with hdy
  set e : Multiplicative (evenWeight m) := g dy with he
  have hfixT : ∀ σ : Equiv.Perm (Fin m), σ ∈ alternatingGroup (Fin m) →
      ((σ i = i ∧ σ j = j) ∨ (σ i = j ∧ σ j = i)) → permAct m σ e = e := by
    intro σ hσ hpres
    have hd : permAct m σ dy = dy := permAct_pairW_fixed σ hpres dy rfl
    have h2 := congrArg (fun φ : MulAut (Multiplicative (evenWeight m)) => φ dy) (hg ⟨σ, hσ⟩)
    simp only [MulAut.mul_apply] at h2
    change g (permAct m σ dy) = permAct m σ (g dy) at h2
    rw [hd] at h2
    exact h2.symm
  set f : Fin m → ZMod 2 := ((Multiplicative.toAdd e : evenWeight m) : Fin m → ZMod 2) with hf
  have hsum : ∑ k, f k = 0 := (Multiplicative.toAdd e).2
  have hpi : pairW m i j i = 1 := by rw [pairW_apply]; simp [hij]
  have hpj : pairW m i j j = 1 := by rw [pairW_apply]; simp [Ne.symm hij]
  have hF1 : ∀ p q : Fin m, p ≠ i → p ≠ j → q ≠ i → q ≠ j → p ≠ q → f p = f q := by
    intro p q hpi₁ hpj₁ hqi hqj hpq
    obtain ⟨r, hri, hrj, hrp, hrq⟩ := exists_not_mem_four h5 i j p q
    have hσalt : (Equiv.swap p q * Equiv.swap q r) ∈ alternatingGroup (Fin m) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hpq,
        Equiv.Perm.sign_swap (Ne.symm hrq)]
      rfl
    have hσi : (Equiv.swap p q * Equiv.swap q r) i = i := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hqi) (Ne.symm hri),
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hpi₁) (Ne.symm hqi)]
    have hσj : (Equiv.swap p q * Equiv.swap q r) j = j := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hqj) (Ne.symm hrj),
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hpj₁) (Ne.symm hqj)]
    have hσp : (Equiv.swap p q * Equiv.swap q r) p = q := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hpq (Ne.symm hrp),
        Equiv.swap_apply_left]
    have hfix := hfixT _ hσalt (Or.inl ⟨hσi, hσj⟩)
    have h := (permAct_fixed_iff _ e).1 hfix q
    have hinv : (Equiv.swap p q * Equiv.swap q r)⁻¹ q = p :=
      Equiv.Perm.inv_eq_iff_eq.mpr hσp.symm
    rw [hinv] at h
    exact h
  have hF2 : f i = f j := by
    obtain ⟨k, hki, hkj, -, -⟩ := exists_not_mem_four h5 i j i j
    obtain ⟨l, hli, hlj, hlk, -⟩ := exists_not_mem_four h5 i j k k
    have hσalt : (Equiv.swap i j * Equiv.swap k l) ∈ alternatingGroup (Fin m) := by
      rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij,
        Equiv.Perm.sign_swap (Ne.symm hlk)]
      rfl
    have hσi : (Equiv.swap i j * Equiv.swap k l) i = j := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hki) (Ne.symm hli),
        Equiv.swap_apply_left]
    have hσj : (Equiv.swap i j * Equiv.swap k l) j = i := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hkj) (Ne.symm hlj),
        Equiv.swap_apply_right]
    have hfix := hfixT _ hσalt (Or.inr ⟨hσi, hσj⟩)
    have h := (permAct_fixed_iff _ e).1 hfix i
    have hinv : (Equiv.swap i j * Equiv.swap k l)⁻¹ i = j :=
      Equiv.Perm.inv_eq_iff_eq.mpr hσj.symm
    rw [hinv] at h
    exact h.symm
  obtain ⟨r₀, hr₀i, hr₀j, -, -⟩ := exists_not_mem_four h5 i j i j
  have hconst : ∀ k, k ≠ i → k ≠ j → f k = f r₀ := by
    intro k hki hkj
    by_cases hk : k = r₀
    · rw [hk]
    · exact hF1 k r₀ hki hkj hr₀i hr₀j hk
  have hb : f r₀ = 0 := by
    have hsplit : ∑ k, (f k + f r₀) = (f i + f r₀) + (f j + f r₀) := by
      apply Fintype.sum_eq_add i j hij
      intro x hx
      rw [hconst x hx.1 hx.2, zmod2_add_self]
    have hsum2 : ∑ k, (f k + f r₀) = 0 := by
      rw [hsplit, ← hF2]
      exact zmod2_add_self _
    rw [Finset.sum_add_distrib, hsum, zero_add, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ZMod.natCast_eq_one_iff_odd.mpr hm, one_mul] at hsum2
    exact hsum2
  have hzero : ∀ k, k ≠ i → k ≠ j → f k = 0 := fun k hki hkj => (hconst k hki hkj).trans hb
  have hdy1 : dy ≠ 1 := by
    intro h
    have h0 : ((Multiplicative.toAdd dy : evenWeight m) : Fin m → ZMod 2) i = 0 := by
      simp [h]
    have h1 : ((Multiplicative.toAdd dy : evenWeight m) : Fin m → ZMod 2) i = 1 := hpi
    rw [h0] at h1
    exact zero_ne_one h1
  have hne1 : e ≠ 1 := by
    intro h1
    apply hdy1
    apply g.injective
    rw [map_one]
    exact h1
  rcases zmod2_cases (f i) with ha | ha
  · exfalso
    apply hne1
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext k
    have hfk : f k = 0 := by
      by_cases hki : k = i
      · rw [hki]; exact ha
      · by_cases hkj : k = j
        · rw [hkj, ← hF2]; exact ha
        · exact hzero k hki hkj
    exact hfk
  · have hfe : ∀ k, f k = pairW m i j k := by
      intro k
      by_cases hki : k = i
      · rw [hki, ha, hpi]
      · by_cases hkj : k = j
        · rw [hkj, ← hF2, ha, hpj]
        · rw [hzero k hki hkj]
          rw [pairW_apply]
          simp [hki, hkj]
    have he_dy : e = dy := by
      apply Multiplicative.toAdd.injective
      apply Subtype.ext
      funext k
      exact hfe k
    exact he_dy

theorem altOdd_centralizer_trivial {m : ℕ} (hm : Odd m) (h5 : 5 ≤ m)
    (g : MulAut (Multiplicative (evenWeight m)))
    (hg : ∀ τ : alternatingGroup (Fin m), g * altAct m τ = altAct m τ * g) : g = 1 := by
  have hpos : 0 < m := by omega
  set p₀ : Fin m := ⟨0, hpos⟩ with hp₀
  let ψ : evenWeight m →+ evenWeight m :=
    AddMonoidHom.mk' (fun x => Multiplicative.toAdd (g (Multiplicative.ofAdd x)))
      (fun a b => by simp only [ofAdd_add, map_mul, toAdd_mul])
  let w : Fin m → evenWeight m := fun k => ⟨pairW m p₀ k, pairW_mem m p₀ k⟩
  have hw0 : w p₀ = 0 := Subtype.ext (pairW_self p₀)
  have hpair : ∀ k, ψ (w k) = w k := by
    intro k
    by_cases hk : k = p₀
    · rw [hk, hw0, map_zero]
    · have hfix := altOdd_fix_pair hm h5 g hg (i := p₀) (j := k) (Ne.symm hk)
      show Multiplicative.toAdd (g (Multiplicative.ofAdd ⟨pairW m p₀ k, pairW_mem m p₀ k⟩)) =
        ⟨pairW m p₀ k, pairW_mem m p₀ k⟩
      rw [hfix, toAdd_ofAdd]
  have hfun : ∀ x : Fin m → ZMod 2, ∑ k, x k = 0 → ∀ l,
      ∑ k, (if x k = 1 then pairW m p₀ k l else 0) = x l := by
    intro x hx l
    have h1 : ∀ k, (if x k = 1 then pairW m p₀ k l else 0) =
        x k * (if l = p₀ then 1 else 0) + (if l = k then x k else 0) := by
      intro k
      rw [zmod2_ite_one_mul, pairW_apply]
      rw [mul_add]
      by_cases hl : l = k <;> simp [hl]
    simp only [h1]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hx, zero_mul, zero_add]
    simp
  have hcoord : ∀ (x : evenWeight m) (k l : Fin m),
      ((if (x : Fin m → ZMod 2) k = 1 then w k else 0 : evenWeight m) : Fin m → ZMod 2) l =
        if (x : Fin m → ZMod 2) k = 1 then pairW m p₀ k l else 0 := by
    intro x k l
    split_ifs <;> rfl
  have hcoe : ∀ (s : Finset (Fin m)) (f : Fin m → evenWeight m),
      ((∑ k ∈ s, f k : evenWeight m) : Fin m → ZMod 2) = ∑ k ∈ s, (f k : Fin m → ZMod 2) :=
    fun s f => map_sum (AddSubgroup.subtype (evenWeight m)) f s
  have hdecomp : ∀ x : evenWeight m,
      x = ∑ k, (if (x : Fin m → ZMod 2) k = 1 then w k else 0) := by
    intro x
    apply Subtype.ext
    rw [hcoe]
    funext l
    rw [Finset.sum_apply]
    simp only [hcoord]
    exact (hfun (x : Fin m → ZMod 2) x.2 l).symm
  have hψ : ∀ x : evenWeight m, ψ x = x := by
    intro x
    have hterm : ∀ k, ψ (if (x : Fin m → ZMod 2) k = 1 then w k else 0) =
        if (x : Fin m → ZMod 2) k = 1 then w k else 0 := by
      intro k
      split_ifs
      · exact hpair k
      · exact map_zero ψ
    calc ψ x = ψ (∑ k, (if (x : Fin m → ZMod 2) k = 1 then w k else 0)) := by rw [← hdecomp x]
      _ = ∑ k, ψ (if (x : Fin m → ZMod 2) k = 1 then w k else 0) := map_sum ψ _ _
      _ = ∑ k, (if (x : Fin m → ZMod 2) k = 1 then w k else 0) :=
          Finset.sum_congr rfl fun k _ => hterm k
      _ = x := (hdecomp x).symm
  refine MulEquiv.ext fun y => ?_
  rw [MulAut.one_apply]
  have h2 : Multiplicative.toAdd (g y) = Multiplicative.toAdd y := hψ (Multiplicative.toAdd y)
  exact Multiplicative.toAdd.injective h2

theorem altOdd_normalizer_perm {m : ℕ} (hm : Odd m) (h5 : 5 ≤ m)
    (g : MulAut (Multiplicative (evenWeight m)))
    (hg : ∀ l ∈ (altAct m).range, g * l * g⁻¹ ∈ (altAct m).range) :
    ∃ σ : Equiv.Perm (Fin m), g = permAct m σ := by
  have hm3 : 3 ≤ m := by omega
  have hm6 : m ≠ 6 := by
    obtain ⟨k, hk⟩ := hm
    omega
  have hinj : Function.Injective (altAct m) := by
    intro a b hab
    have hab' : permAct m (a : Equiv.Perm (Fin m)) = permAct m (b : Equiv.Perm (Fin m)) := hab
    exact Subtype.ext (permAct_injective hm3 hab')
  have hsub : ∀ τ : alternatingGroup (Fin m), ∃ τ' : alternatingGroup (Fin m),
      altAct m τ' = g * altAct m τ * g⁻¹ := fun τ =>
    MonoidHom.mem_range.mp (hg (altAct m τ) (MonoidHom.mem_range.mpr ⟨τ, rfl⟩))
  choose F hF using hsub
  have hFmul : ∀ a b, F (a * b) = F a * F b := by
    intro a b
    apply hinj
    simp only [hF, map_mul]
    group
  let Fh : alternatingGroup (Fin m) →* alternatingGroup (Fin m) := MonoidHom.mk' F hFmul
  have hFinj : Function.Injective Fh := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have ha' : F a = 1 := ha
    have h1 : altAct m (F a) = 1 := by rw [ha', map_one]
    rw [hF] at h1
    have h2 : altAct m a = 1 := by
      calc altAct m a = g⁻¹ * (g * altAct m a * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    exact hinj (h2.trans (map_one _).symm)
  have hFsurj : Function.Surjective Fh := Finite.injective_iff_surjective.mp hFinj
  let θ : alternatingGroup (Fin m) ≃* alternatingGroup (Fin m) :=
    MulEquiv.ofBijective Fh ⟨hFinj, hFsurj⟩
  obtain ⟨σ, hσ⟩ := (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj m h5 hm6).2 θ
  have hformula : ∀ τ : alternatingGroup (Fin m),
      ((F τ : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) = σ * τ * σ⁻¹ := by
    intro τ
    have h1 : (MulAut.conjNormal (H := alternatingGroup (Fin m)) σ) τ = F τ := by
      rw [hσ]
      rfl
    have h2 := MulAut.conjNormal_apply σ τ
    rw [h1] at h2
    exact h2
  have hP : ∀ τ : alternatingGroup (Fin m),
      g * altAct m τ * g⁻¹ = permAct m σ * altAct m τ * (permAct m σ)⁻¹ := by
    intro τ
    rw [← hF τ]
    show permAct m ((F τ : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) =
      permAct m σ * altAct m τ * (permAct m σ)⁻¹
    rw [hformula τ, map_mul, map_mul, map_inv]
    rfl
  have hcomm : ∀ τ : alternatingGroup (Fin m),
      (permAct m σ)⁻¹ * g * altAct m τ = altAct m τ * ((permAct m σ)⁻¹ * g) := by
    intro τ
    calc (permAct m σ)⁻¹ * g * altAct m τ
        = (permAct m σ)⁻¹ * (g * altAct m τ * g⁻¹) * g := by group
      _ = (permAct m σ)⁻¹ * (permAct m σ * altAct m τ * (permAct m σ)⁻¹) * g := by rw [hP τ]
      _ = altAct m τ * ((permAct m σ)⁻¹ * g) := by group
  have hc := altOdd_centralizer_trivial hm h5 ((permAct m σ)⁻¹ * g) hcomm
  refine ⟨σ, ?_⟩
  calc g = permAct m σ * ((permAct m σ)⁻¹ * g) := by group
    _ = permAct m σ * 1 := by rw [hc]
    _ = permAct m σ := mul_one _

private abbrev pmoR {X : Type} (B : Subgroup (Equiv.Perm X)) (i j : X) : Prop :=
  ∃ σ ∈ B, σ i = j

private theorem pmo_inv_apply_self {X : Type} (σ : Equiv.Perm X) (i : X) : σ⁻¹ (σ i) = i :=
  Equiv.symm_apply_apply σ i

private theorem pmoR_equivalence {X : Type} (B : Subgroup (Equiv.Perm X)) :
    Equivalence (pmoR B) where
  refl i := ⟨1, B.one_mem, rfl⟩
  symm := fun {i j} ⟨σ, hσ, h⟩ => ⟨σ⁻¹, B.inv_mem hσ, by rw [← h, pmo_inv_apply_self]⟩
  trans := fun {i j k} ⟨σ, hσ, h⟩ ⟨τ, hτ, h'⟩ =>
    ⟨τ * σ, B.mul_mem hτ hσ, by rw [Equiv.Perm.mul_apply, h, h']⟩

private abbrev pmoSetoid {X : Type} (B : Subgroup (Equiv.Perm X)) : Setoid X :=
  ⟨pmoR B, pmoR_equivalence B⟩

private noncomputable def pmoRep {X : Type} (B : Subgroup (Equiv.Perm X))
    (q : Quotient (pmoSetoid B)) : X :=
  Quotient.out q

private theorem pmoRep_spec {X : Type} (B : Subgroup (Equiv.Perm X))
    (q : Quotient (pmoSetoid B)) : Quotient.mk (pmoSetoid B) (pmoRep B q) = q :=
  Quotient.out_eq q

private abbrev pmoFiber {X : Type} (B : Subgroup (Equiv.Perm X)) (q : Quotient (pmoSetoid B)) : Type :=
  {i : X // Quotient.mk (pmoSetoid B) i = q}

private theorem pmo_exists_of_mk_eq {X : Type} {B : Subgroup (Equiv.Perm X)} {i j : X}
    (h : Quotient.mk (pmoSetoid B) i = Quotient.mk (pmoSetoid B) j) : pmoR B i j :=
  Quotient.exact h

private theorem pmo_fixed_const {X : Type} {B : Subgroup (Equiv.Perm X)} (x : X → ZMod 2)
    (hx : ∀ σ ∈ B, ∀ i, x (σ⁻¹ i) = x i) {i j : X} (h : pmoR B i j) : x i = x j := by
  obtain ⟨σ, hσ, rfl⟩ := h
  have h1 := hx σ hσ (σ i)
  rw [pmo_inv_apply_self σ i] at h1
  exact h1

private theorem pmo_comm {X : Type} {B : Subgroup (Equiv.Perm X)} (hB : IsElemAbelian 2 B)
    {b s : Equiv.Perm X} (hb : b ∈ B) (hs : s ∈ B) (i : X) : b (s i) = s (b i) := by
  have h : (⟨b, hb⟩ : ↥B) * ⟨s, hs⟩ = ⟨s, hs⟩ * ⟨b, hb⟩ := hB.1.is_comm.comm _ _
  have h2 : b * s = s * b := congrArg Subtype.val h
  exact congrArg (fun g : Equiv.Perm X => g i) h2

private theorem pmo_mk_perm_rep {X : Type} (B : Subgroup (Equiv.Perm X)) (b : ↥B)
    (q : Quotient (pmoSetoid B)) :
    Quotient.mk (pmoSetoid B) ((b : Equiv.Perm X) (pmoRep B q)) = q := by
  have hr : pmoR B (pmoRep B q) ((b : Equiv.Perm X) (pmoRep B q)) :=
    ⟨(b : Equiv.Perm X), b.2, rfl⟩
  have hq : Quotient.mk (pmoSetoid B) (pmoRep B q) =
      Quotient.mk (pmoSetoid B) ((b : Equiv.Perm X) (pmoRep B q)) := Quotient.sound hr
  exact hq.symm.trans (pmoRep_spec B q)

private noncomputable def pmoMap {X : Type} (B : Subgroup (Equiv.Perm X))
    (p : ↥B × {x : X → ZMod 2 // ∀ σ ∈ B, ∀ i, x (σ⁻¹ i) = x i}) :
    ∀ q : Quotient (pmoSetoid B), pmoFiber B q × ZMod 2 :=
  fun q => (⟨(p.1 : Equiv.Perm X) (pmoRep B q), pmo_mk_perm_rep B p.1 q⟩, p.2.1 (pmoRep B q))

private theorem pmoMap_injective {X : Type} (B : Subgroup (Equiv.Perm X))
    (hB : IsElemAbelian 2 B) : Function.Injective (pmoMap B) := by
  rintro ⟨b, x⟩ ⟨c, y⟩ h
  have h1 : ∀ q, (b : Equiv.Perm X) (pmoRep B q) = (c : Equiv.Perm X) (pmoRep B q) := fun q =>
    congrArg Subtype.val (congrArg Prod.fst (congrFun h q))
  have h2 : ∀ q, x.1 (pmoRep B q) = y.1 (pmoRep B q) := fun q =>
    congrArg Prod.snd (congrFun h q)
  have hbc : b = c := by
    apply Subtype.ext
    apply Equiv.ext
    intro i
    obtain ⟨s, hs, hsi⟩ := pmo_exists_of_mk_eq (pmoRep_spec B (Quotient.mk (pmoSetoid B) i))
    calc (b : Equiv.Perm X) i
        = (b : Equiv.Perm X) (s (pmoRep B (Quotient.mk (pmoSetoid B) i))) := by rw [hsi]
      _ = s ((b : Equiv.Perm X) (pmoRep B (Quotient.mk (pmoSetoid B) i))) :=
          pmo_comm hB b.2 hs _
      _ = s ((c : Equiv.Perm X) (pmoRep B (Quotient.mk (pmoSetoid B) i))) := by rw [h1]
      _ = (c : Equiv.Perm X) (s (pmoRep B (Quotient.mk (pmoSetoid B) i))) :=
          (pmo_comm hB c.2 hs _).symm
      _ = (c : Equiv.Perm X) i := by rw [hsi]
  have hxy : x = y := by
    apply Subtype.ext
    funext i
    obtain ⟨s, hs, hsi⟩ := pmo_exists_of_mk_eq (pmoRep_spec B (Quotient.mk (pmoSetoid B) i))
    rw [(pmo_fixed_const x.1 x.2 (⟨s, hs, hsi⟩ : pmoR B _ i)).symm,
      (pmo_fixed_const y.1 y.2 (⟨s, hs, hsi⟩ : pmoR B _ i)).symm]
    exact h2 _
  subst hbc
  subst hxy
  rfl

private theorem pmo_mul_two_le_two_pow (n : ℕ) : n * 2 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      norm_num
    · rw [pow_succ]
      omega

theorem perm_module_noOffender (X : Type) [Fintype X] [DecidableEq X]
    (B : Subgroup (Equiv.Perm X)) (hB : IsElemAbelian 2 B) :
    Nat.card B * Nat.card {x : X → ZMod 2 // ∀ σ ∈ B, ∀ i, x (σ⁻¹ i) = x i} ≤
      2 ^ Fintype.card X := by
  haveI : Fintype (Quotient (pmoSetoid B)) := Fintype.ofFinite _
  have hsum : ∑ q : Quotient (pmoSetoid B), Nat.card (pmoFiber B q) = Nat.card X := by
    rw [← Nat.card_sigma]
    exact Nat.card_congr (Equiv.sigmaFiberEquiv (Quotient.mk (pmoSetoid B)))
  calc Nat.card B * Nat.card {x : X → ZMod 2 // ∀ σ ∈ B, ∀ i, x (σ⁻¹ i) = x i}
      = Nat.card (↥B × {x : X → ZMod 2 // ∀ σ ∈ B, ∀ i, x (σ⁻¹ i) = x i}) :=
        (Nat.card_prod _ _).symm
    _ ≤ Nat.card (∀ q : Quotient (pmoSetoid B), pmoFiber B q × ZMod 2) :=
        Nat.card_le_card_of_injective (pmoMap B) (pmoMap_injective B hB)
    _ = ∏ q : Quotient (pmoSetoid B), Nat.card (pmoFiber B q) * 2 := by
        rw [Nat.card_pi]
        exact Finset.prod_congr rfl fun q _ => by rw [Nat.card_prod, Nat.card_zmod]
    _ ≤ ∏ q : Quotient (pmoSetoid B), 2 ^ Nat.card (pmoFiber B q) :=
        Finset.prod_le_prod fun q _ => pmo_mul_two_le_two_pow (Nat.card (pmoFiber B q))
    _ = 2 ^ ∑ q : Quotient (pmoSetoid B), Nat.card (pmoFiber B q) := by
        rw [Finset.prod_pow_eq_pow_sum]
    _ = 2 ^ Fintype.card X := by rw [hsum, Nat.card_eq_fintype_card]

theorem exists_fixedPoint_of_odd {m : ℕ} (hm : Odd m) (B : Subgroup (Equiv.Perm (Fin m)))
    (hB : IsElemAbelian 2 B) : ∃ i : Fin m, ∀ σ ∈ B, σ i = i := by
  have hG : IsPGroup 2 B := fun g => ⟨1, by
    rw [pow_one]
    apply Subtype.ext
    simpa using hB.2 (g : Equiv.Perm (Fin m)) g.2⟩
  have hnd : ¬ 2 ∣ Nat.card (Fin m) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    obtain ⟨k, hk⟩ := hm
    omega
  obtain ⟨i, hi⟩ := hG.nonempty_fixed_point_of_prime_not_dvd_card (Fin m) hnd
  exact ⟨i, fun σ hσ => by simpa using hi ⟨σ, hσ⟩⟩

theorem card_fixed_perm_two_mul {m : ℕ} (B : Subgroup (Equiv.Perm (Fin m))) {i₀ : Fin m}
    (h : ∀ σ ∈ B, σ i₀ = i₀) :
    Nat.card {x : Fin m → ZMod 2 // ∀ σ ∈ B, ∀ i, x (σ⁻¹ i) = x i} =
      2 * Nat.card {x : Fin m → ZMod 2 // (∀ σ ∈ B, ∀ i, x (σ⁻¹ i) = x i) ∧ ∑ i, x i = 0} := by
  have hfix1 : ∀ σ ∈ B, ∀ (c : ZMod 2) (i : Fin m),
      (Pi.single i₀ c : Fin m → ZMod 2) (σ⁻¹ i) = (Pi.single i₀ c : Fin m → ZMod 2) i := by
    intro σ hσ c i
    by_cases hi : i = i₀
    · subst hi
      have hσi : σ⁻¹ i = i := Equiv.Perm.inv_eq_iff_eq.mpr (h σ hσ).symm
      rw [hσi]
    · have hne : σ⁻¹ i ≠ i₀ := fun hc => hi (by
        rw [Equiv.Perm.inv_eq_iff_eq, h σ hσ] at hc
        exact hc)
      simp only [Pi.single_apply, if_neg hne, if_neg hi]
  have hsum1 : ∀ c : ZMod 2, ∑ i, (Pi.single i₀ c : Fin m → ZMod 2) i = c := by
    intro c
    simp [Pi.single_apply]
  have hc : ∀ c : ZMod 2, c + c = 0 := by decide
  have hdouble : ∀ f : Fin m → ZMod 2, f + f = 0 := fun f => funext fun i => hc (f i)
  have hsumfix : ∀ y : Fin m → ZMod 2,
      ∑ i, (y + Pi.single i₀ (∑ j, y j) : Fin m → ZMod 2) i = 0 := by
    intro y
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, hsum1]
    exact hc _
  have e : {x : Fin m → ZMod 2 // ∀ σ ∈ B, ∀ i, x (σ⁻¹ i) = x i} ≃
      {x : Fin m → ZMod 2 // (∀ σ ∈ B, ∀ i, x (σ⁻¹ i) = x i) ∧ ∑ i, x i = 0} × ZMod 2 :=
    { toFun := fun x => ⟨⟨x.1 + Pi.single i₀ (∑ j, x.1 j), fun σ hσ i => by
          simp only [Pi.add_apply]
          rw [x.2 σ hσ i, hfix1 σ hσ], hsumfix x.1⟩, ∑ j, x.1 j⟩
      invFun := fun p => ⟨p.1.1 + Pi.single i₀ p.2, fun σ hσ i => by
          simp only [Pi.add_apply]
          rw [p.1.2.1 σ hσ i, hfix1 σ hσ]⟩
      left_inv := fun x => Subtype.ext (by
          show (x.1 + Pi.single i₀ (∑ j, x.1 j)) + Pi.single i₀ (∑ j, x.1 j) = x.1
          rw [add_assoc, hdouble, add_zero])
      right_inv := fun p => by
        have hs : ∑ j, (p.1.1 + Pi.single i₀ p.2 : Fin m → ZMod 2) j = p.2 := by
          simp only [Pi.add_apply]
          rw [Finset.sum_add_distrib, p.1.2.2, hsum1, zero_add]
        apply Prod.ext
        · apply Subtype.ext
          show (p.1.1 + Pi.single i₀ p.2) + Pi.single i₀
            (∑ j, (p.1.1 + Pi.single i₀ p.2 : Fin m → ZMod 2) j) = p.1.1
          rw [hs, add_assoc, hdouble, add_zero]
        · exact hs }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_zmod, mul_comm]

theorem card_fixed_permMod_eq {m : ℕ} (B : Subgroup (Equiv.Perm (Fin m))) :
    Nat.card {x : Multiplicative (evenWeight m) // ∀ σ ∈ B, permAct m σ x = x} =
      Nat.card {x : Fin m → ZMod 2 // (∀ σ ∈ B, ∀ i, x (σ⁻¹ i) = x i) ∧ ∑ i, x i = 0} := by
  refine Nat.card_congr
    { toFun := fun x => ⟨((Multiplicative.toAdd x.1 : evenWeight m) : Fin m → ZMod 2),
        fun σ hσ i => (permAct_fixed_iff σ x.1).1 (x.2 σ hσ) i, (Multiplicative.toAdd x.1).2⟩
      invFun := fun y => ⟨Multiplicative.ofAdd ⟨y.1, y.2.2⟩, fun σ hσ =>
        (permAct_fixed_iff σ _).2 (fun i => y.2.1 σ hσ i)⟩
      left_inv := fun x => Subtype.ext rfl
      right_inv := fun y => Subtype.ext (by simp) }

theorem card_evenWeight {m : ℕ} (hm : 1 ≤ m) : Nat.card (evenWeight m) = 2 ^ (m - 1) := by
  set f : (Fin m → ZMod 2) →+ ZMod 2 :=
    AddMonoidHom.mk' (fun x : Fin m → ZMod 2 => ∑ i, x i) (fun _ _ => Finset.sum_add_distrib)
    with hf
  have hsurj : Function.Surjective f := by
    intro c
    refine ⟨Pi.single ⟨0, hm⟩ c, ?_⟩
    simp [hf]
  have h1 : Nat.card f.ker * Nat.card (ZMod 2) = Nat.card (Fin m → ZMod 2) :=
    AddSubgroup.card_ker_mul_card_of_surjective hsurj
  have h2 : Nat.card (Fin m → ZMod 2) = 2 ^ m := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h3 : 2 ^ m = 2 ^ (m - 1) * 2 := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h2, Nat.card_zmod, h3] at h1
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1

theorem card_fixed_altmod_le {m : ℕ} (hm : Odd m) (B : Subgroup (Equiv.Perm (Fin m)))
    (hB : IsElemAbelian 2 B) :
    Nat.card B * Nat.card {x : Multiplicative (evenWeight m) // ∀ σ ∈ B, permAct m σ x = x} ≤
      Nat.card (Multiplicative (evenWeight m)) := by
  obtain ⟨i₀, hi₀⟩ := exists_fixedPoint_of_odd hm B hB
  have hm1 : 1 ≤ m := hm.pos
  have h1 := perm_module_noOffender (Fin m) B hB
  rw [Fintype.card_fin, card_fixed_perm_two_mul B hi₀] at h1
  rw [card_fixed_permMod_eq B,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (evenWeight m) ≃ evenWeight m),
    card_evenWeight hm1]
  have hpow : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hpow] at h1
  have h2 : 2 * (Nat.card B * Nat.card {x : Fin m → ZMod 2 //
      (∀ σ ∈ B, ∀ i, x (σ⁻¹ i) = x i) ∧ ∑ i, x i = 0}) ≤ 2 * 2 ^ (m - 1) := by
    calc 2 * (Nat.card B * Nat.card {x : Fin m → ZMod 2 //
        (∀ σ ∈ B, ∀ i, x (σ⁻¹ i) = x i) ∧ ∑ i, x i = 0})
        = Nat.card B * (2 * Nat.card {x : Fin m → ZMod 2 //
        (∀ σ ∈ B, ∀ i, x (σ⁻¹ i) = x i) ∧ ∑ i, x i = 0}) := by ring
      _ ≤ 2 * 2 ^ (m - 1) := h1
  exact Nat.le_of_mul_le_mul_left h2 (by norm_num)

theorem natCountMod_altOdd {m : ℕ} (hm : Odd m) (h5 : 5 ≤ m) :
    NatCountMod (Multiplicative (evenWeight m)) (altAct m).range := by
  intro B hB hN
  have hm3 : 3 ≤ m := by omega
  have hinj := permAct_injective hm3
  have hperm : ∀ b ∈ B, ∃ σ : Equiv.Perm (Fin m), b = permAct m σ := fun b hb =>
    altOdd_normalizer_perm hm h5 b (hN b hb)
  have hBle : B ≤ (permAct m).range := fun b hb => by
    obtain ⟨σ, hσ⟩ := hperm b hb
    exact ⟨σ, hσ.symm⟩
  set B' : Subgroup (Equiv.Perm (Fin m)) := B.comap (permAct m) with hB'
  have hmap : B'.map (permAct m) = B := Subgroup.map_comap_eq_self hBle
  have hcard : Nat.card B' = Nat.card B := by
    have := Nat.card_congr (B'.equivMapOfInjective (permAct m) hinj).toEquiv
    rw [hmap] at this
    exact this
  have hBcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => by
    have := hB.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
    exact congrArg Subtype.val this
  have hB'e : IsElemAbelian 2 B' := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun σ hσ => ?_⟩
    · apply Subtype.ext
      apply hinj
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact hBcomm _ a.2 _ b.2
    · apply hinj
      have h2 := hB.2 (permAct m σ) hσ
      rw [map_pow, map_one]
      exact h2
  have hfix : Nat.card {x : Multiplicative (evenWeight m) // ∀ b ∈ B, b x = x} ≤
      Nat.card {x : Multiplicative (evenWeight m) // ∀ σ ∈ B', permAct m σ x = x} :=
    Nat.card_le_card_of_injective (fun x => ⟨x.1, fun σ hσ => x.2 _ hσ⟩) (by
      intro x y h; apply Subtype.ext; have h' := congrArg Subtype.val h; simpa using h')
  calc Nat.card B * Nat.card {x : Multiplicative (evenWeight m) // ∀ b ∈ B, b x = x}
      ≤ Nat.card B' * Nat.card {x : Multiplicative (evenWeight m) // ∀ σ ∈ B', permAct m σ x = x} := by
        rw [hcard]; exact Nat.mul_le_mul_left _ hfix
    _ ≤ Nat.card (Multiplicative (evenWeight m)) := card_fixed_altmod_le hm B' hB'e

end CFSG.Quasithin.C116Two
