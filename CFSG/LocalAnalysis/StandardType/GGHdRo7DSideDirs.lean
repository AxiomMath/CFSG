module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DLModelDefs
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelI

public section

namespace CFSG.StandardType.HdRo7D

open CFSG.Assembly CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

private lemma hdRo7DDSdRAux_dinv_succ_cons {p k : ℕ} (i j : Fin k)
    (hij : i ≠ j) (f : Fin (k + 1) → Multiplicative (ZMod p)) :
    NbrOrth.dinv i.succ j.succ f = Fin.cons (f 0) (NbrOrth.dinv i j (Fin.tail f)) := by
  have htail : Fin.tail (NbrOrth.dinv i.succ j.succ f) = NbrOrth.dinv i j (Fin.tail f) := by
    funext m
    simp only [NbrOrth.dinv, Fin.tail, Function.update_apply]
    by_cases hi : m = i
    · subst hi
      simp [hij, Fin.succ_inj]
    · by_cases hj : m = j
      · subst hj
        simp [hi, Fin.succ_inj]
      · simp [hi, hj, Fin.succ_inj]
  conv_lhs => rw [← Fin.cons_self_tail (NbrOrth.dinv i.succ j.succ f), htail]
  rw [show NbrOrth.dinv i.succ j.succ f 0 = f 0 from by
    rw [NbrOrth.dinv, Function.update_apply, if_neg (Ne.symm (Fin.succ_ne_zero i)),
      Function.update_apply, if_neg (Ne.symm (Fin.succ_ne_zero j))]]

private lemma hdRo7DDSdRAux_model_dinv {G : Type} [Group G] [Finite G] (p : ℕ)
    (B Bs : Subgroup G) (x : G) (L : Subgroup G) (k : ℕ)
    (τT : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ L))
    (hτT : Function.Bijective τT)
    (τC : Multiplicative (ZMod p) ≃* ↥(Bs ⊓ Subgroup.centralizer (L : Set G)))
    (Φ : ↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≃* ↥Bs)
    (hΦ : ∀ (t : ↥(Bs ⊓ L)) (c : ↥(Bs ⊓ Subgroup.centralizer (L : Set G))),
      (Φ (t, c) : G) = (t : G) * (c : G))
    (hC : ∀ m : Multiplicative (ZMod p), (τC m : G) = x ^ (Multiplicative.toAdd m).val)
    (hdinv : ∀ i j : Fin k, i ≠ j → ∃ w : ↥L, ∀ f,
      (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (NbrOrth.dinv i j f) : G))
    (hLx : ∀ g : ↥L, (g : G) * x * (g : G)⁻¹ = x)
    (i j : Fin k) (hij : i ≠ j) :
    ∃ a ∈ ggAutomizer L Bs,
      ∀ f : Fin (k + 1) → Multiplicative (ZMod p),
        (a (hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ f) : G) =
          (hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ
            (NbrOrth.dinv i.succ j.succ f) : G) := by
  obtain ⟨w, hw⟩ := hdinv i j hij
  let s : MulAut (Fin k → Multiplicative (ZMod p)) :=
    SpCoord.sgnAut i * SpCoord.sgnAut j
  have hs : ∀ f, s f = NbrOrth.dinv i j f := fun f => rfl
  have hw' : ∀ f, (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (s f) : G) := by
    intro f
    rw [hs f, hw f]
  have hwN := hdRo7CLCoordAux_conj_mem_normalizer p B Bs x L k τT hτT Φ hΦ w s hw'
  have hwp : ∀ n, (w : G) * x ^ n * (w : G)⁻¹ = x ^ n := by
    intro n
    calc (w : G) * x ^ n * (w : G)⁻¹ = (MulAut.conj (w : G)) (x ^ n) := by
          rw [MulAut.conj_apply]
      _ = ((MulAut.conj (w : G)) x) ^ n := map_pow _ _ _
      _ = x ^ n := by
          rw [show (MulAut.conj (w : G)) x = x from by
            rw [MulAut.conj_apply]; exact hLx w]
  refine ⟨ggConjAut Bs hwN, ggConjAut_mem_ggAutomizer w.2 hwN, fun f => ?_⟩
  rw [ggConjAut_apply]
  rw [show ((hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ f : ↥Bs) : G) =
      (τT (Fin.tail f) : G) * x ^ (Multiplicative.toAdd (f 0)).val from
    hdRo7CLCoordAux_tau_apply p B Bs x L k τT hτT τC Φ hΦ hC (f := f)]
  rw [hdRo7DDSdRAux_dinv_succ_cons i j hij f,
    hdRo7CLCoordAux_tau_apply p B Bs x L k τT hτT τC Φ hΦ hC
      (f := Fin.cons (f 0) (NbrOrth.dinv i j (Fin.tail f)))]
  rw [Fin.tail_cons, Fin.cons_zero]
  rw [show (w : G) * ((τT (Fin.tail f) : G) * x ^ (Multiplicative.toAdd (f 0)).val) *
        (w : G)⁻¹ =
      ((w : G) * (τT (Fin.tail f) : G) * (w : G)⁻¹) *
        ((w : G) * x ^ (Multiplicative.toAdd (f 0)).val * (w : G)⁻¹) from by group]
  rw [hw (Fin.tail f), hwp (Multiplicative.toAdd (f 0)).val]

private lemma hdRo7DDSdRAux_prod_two {p k : ℕ} (c : Fin (k + 1) → ZMod p)
    {i0 j0 : Fin (k + 1)} (hij : i0 ≠ j0) (hi0 : c i0 = -1) (hj0 : c j0 = -1)
    (hprod : ∏ i, c i = 1) :
    ∏ i, (if i = i0 ∨ i = j0 then -c i else c i) = 1 := by
  classical
  have hsplit : ∀ d : Fin (k + 1) → ZMod p,
      (∏ i, d i) = d i0 * (d j0 * ((Finset.univ.erase i0).erase j0).prod d) := by
    intro d
    rw [← Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i0)]
    rw [← Finset.mul_prod_erase (Finset.univ.erase i0) d
      (Finset.mem_erase.mpr ⟨Ne.symm hij, Finset.mem_univ j0⟩)]
  have hrest : (((Finset.univ.erase i0).erase j0).prod
        (fun i => if i = i0 ∨ i = j0 then -c i else c i)) =
      ((Finset.univ.erase i0).erase j0).prod c := by
    apply Finset.prod_congr rfl
    intro x hx
    rw [Finset.mem_erase, Finset.mem_erase] at hx
    have hx' : x ≠ i0 ∧ x ≠ j0 := ⟨hx.2.1, hx.1⟩
    have hne : ¬ (x = i0 ∨ x = j0) := by
      push Not
      exact hx'
    rw [if_neg hne]
  have hc'prod := hsplit (fun i => if i = i0 ∨ i = j0 then -c i else c i)
  rw [hrest] at hc'prod
  have hcprod := hsplit c
  have hii : (if i0 = i0 ∨ i0 = j0 then -c i0 else c i0) = 1 := by
    rw [if_pos (Or.inl rfl), hi0]; ring
  have hjj : (if j0 = i0 ∨ j0 = j0 then -c j0 else c j0) = 1 := by
    rw [if_pos (Or.inr rfl), hj0]; ring
  rw [hii, hjj] at hc'prod
  have hP : ((Finset.univ.erase i0).erase j0).prod c = 1 := by
    have h := hcprod
    rw [hprod, hi0, hj0] at h
    rw [show (-1 : ZMod p) * (-1 * ((Finset.univ.erase i0).erase j0).prod c) =
        ((Finset.univ.erase i0).erase j0).prod c from by ring] at h
    exact h.symm
  rw [hc'prod, hP]
  ring

private def hdRo7DDSdRAux_CoordPerm {G : Type} [Group G] (p : ℕ) (Bs : Subgroup G) (k : ℕ)
    (τ : (Fin (k + 1) → Multiplicative (ZMod p)) ≃* ↥Bs) (a : MulAut ↥Bs) : Prop :=
  ∃ (σ : Equiv.Perm (Fin (k + 1))) (c : Fin (k + 1) → ZMod p), σ 0 = 0 ∧ c 0 = 1 ∧
    (∀ i, c i = 1 ∨ c i = -1) ∧ ∏ i, c i = 1 ∧
    ∀ (f : Fin (k + 1) → Multiplicative (ZMod p)) (i : Fin (k + 1)),
      Multiplicative.toAdd (τ.symm (a (τ f)) (σ i)) = c i * Multiplicative.toAdd (f i)

private lemma hdRo7DDSdRAux_base {G : Type} [Group G] [Finite G] (p : ℕ)
    (B Bs : Subgroup G) (x : G) (L : Subgroup G) (k : ℕ)
    (τT : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ L))
    (hτT : Function.Bijective τT)
    (τC : Multiplicative (ZMod p) ≃* ↥(Bs ⊓ Subgroup.centralizer (L : Set G)))
    (Φ : ↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≃* ↥Bs)
    (hΦ : ∀ (t : ↥(Bs ⊓ L)) (c : ↥(Bs ⊓ Subgroup.centralizer (L : Set G))),
      (Φ (t, c) : G) = (t : G) * (c : G))
    (hC : ∀ m : Multiplicative (ZMod p), (τC m : G) = x ^ (Multiplicative.toAdd m).val)
    (hperm : ∀ σ : Equiv.Perm (Fin k), ∃ w : ↥L, ∀ f,
      (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (SpCoord.permAut σ f) : G))
    (hLx : ∀ g : ↥L, (g : G) * x * (g : G)⁻¹ = x) (hx : x ∈ Bs)
    (a : MulAut ↥Bs) (σ : Equiv.Perm (Fin (k + 1))) (c : Fin (k + 1) → ZMod p)
    (hσ0 : σ 0 = 0) (hc1 : ∀ i, c i = 1)
    (hrel : ∀ f i, Multiplicative.toAdd
      ((hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ).symm
        (a ((hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ) f)) (σ i)) =
      c i * Multiplicative.toAdd (f i)) :
    a ∈ ggAutomizer L Bs := by
  let τ : (Fin (k + 1) → Multiplicative (ZMod p)) ≃* ↥Bs :=
    hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ
  let π : Equiv.Perm (Fin k) := (Equiv.Perm.decomposeFin σ⁻¹).2
  have hσ0' : σ⁻¹ 0 = 0 := (Equiv.symm_apply_eq σ).mpr hσ0.symm
  have hdecomp : Equiv.Perm.decomposeFin.symm (0, π) = σ⁻¹ := by
    have h1 : (Equiv.Perm.decomposeFin σ⁻¹).1 = 0 := by
      have h := Equiv.Perm.decomposeFin_symm_apply_zero
        (Equiv.Perm.decomposeFin σ⁻¹).1 (Equiv.Perm.decomposeFin σ⁻¹).2
      have h' : (Equiv.Perm.decomposeFin.symm (Equiv.Perm.decomposeFin σ⁻¹)) 0 =
          (Equiv.Perm.decomposeFin σ⁻¹).1 := h
      rw [Equiv.Perm.decomposeFin.symm_apply_apply, hσ0'] at h'
      exact h'.symm
    have hpair : Equiv.Perm.decomposeFin σ⁻¹ = (0, π) := by
      apply Prod.ext
      · exact h1
      · rfl
    rw [← hpair, Equiv.Perm.decomposeFin.symm_apply_apply]
  obtain ⟨aπ, haπ, haπact⟩ :=
    hdRo7CLCoordAux_model_perm p B Bs x L k τT hτT τC Φ hΦ hC hperm hLx hx π
  have hact : ∀ f, a (τ f) = τ (fun j => f (σ.symm j)) := by
    intro f
    have hsymm : τ.symm (a (τ f)) = (fun j => f (σ.symm j)) := by
      funext j
      apply Multiplicative.toAdd.injective
      have h := hrel f (σ.symm j)
      rw [Equiv.apply_symm_apply, hc1 (σ.symm j), one_mul] at h
      exact h
    rw [← MulEquiv.apply_symm_apply τ (a (τ f)), hsymm]
  have haπact' : ∀ f, aπ (τ f) =
      τ (fun j => f (Equiv.Perm.decomposeFin.symm (0, π) j)) :=
    fun f => Subtype.ext (haπact f)
  have haeq : a = aπ := by
    apply MulEquiv.ext
    intro b
    have h1 : a b = τ (fun j => (τ.symm b) (σ.symm j)) := by
      conv_lhs => rw [← MulEquiv.apply_symm_apply τ b]
      exact hact (τ.symm b)
    have h2 : aπ b = τ (fun j => (τ.symm b) (σ.symm j)) := by
      conv_lhs => rw [← MulEquiv.apply_symm_apply τ b]
      rw [haπact' (τ.symm b)]
      congr 1
      funext j
      rw [hdecomp]
      rfl
    rw [h1, h2]
  rw [haeq]
  exact haπ

private theorem hdRo7DDSdRAux_backward_aux {G : Type} [Group G] [Finite G] (p : ℕ)
    (B Bs : Subgroup G) (x : G) (L : Subgroup G) (k : ℕ)
    (τT : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ L))
    (hτT : Function.Bijective τT)
    (τC : Multiplicative (ZMod p) ≃* ↥(Bs ⊓ Subgroup.centralizer (L : Set G)))
    (Φ : ↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≃* ↥Bs)
    (hΦ : ∀ (t : ↥(Bs ⊓ L)) (c : ↥(Bs ⊓ Subgroup.centralizer (L : Set G))),
      (Φ (t, c) : G) = (t : G) * (c : G))
    (hC : ∀ m : Multiplicative (ZMod p), (τC m : G) = x ^ (Multiplicative.toAdd m).val)
    (hdinv : ∀ i j : Fin k, i ≠ j → ∃ w : ↥L, ∀ f,
      (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (NbrOrth.dinv i j f) : G))
    (hperm : ∀ σ : Equiv.Perm (Fin k), ∃ w : ↥L, ∀ f,
      (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (SpCoord.permAut σ f) : G))
    (hLx : ∀ g : ↥L, (g : G) * x * (g : G)⁻¹ = x) (hx : x ∈ Bs) (n : ℕ) :
    ∀ (a : MulAut ↥Bs) (σ : Equiv.Perm (Fin (k + 1))) (c : Fin (k + 1) → ZMod p),
      σ 0 = 0 → c 0 = 1 → (∀ i, c i = 1 ∨ c i = -1) → ∏ i, c i = 1 →
      (Finset.univ.filter (fun i : Fin (k + 1) => c i ≠ 1)).card = n →
      (∀ f i, Multiplicative.toAdd
        ((hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ).symm
          (a ((hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ) f)) (σ i)) =
        c i * Multiplicative.toAdd (f i)) →
      a ∈ ggAutomizer L Bs := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a σ c hσ0 hc0 hc hcprod hcount hrel
    let τ : (Fin (k + 1) → Multiplicative (ZMod p)) ≃* ↥Bs :=
      hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ
    by_cases hn : n = 0
    · have hc1 : ∀ i, c i = 1 := by
        intro i
        by_contra hne
        have hmem : i ∈ Finset.univ.filter (fun i : Fin (k + 1) => c i ≠ 1) := by
          simp [hne]
        have hpos : 0 < (Finset.univ.filter (fun i : Fin (k + 1) => c i ≠ 1)).card :=
          Finset.card_pos.mpr ⟨i, hmem⟩
        rw [hcount, hn] at hpos
        exact Nat.lt_irrefl 0 hpos
      exact hdRo7DDSdRAux_base p B Bs x L k τT hτT τC Φ hΦ hC hperm hLx hx
        a σ c hσ0 hc1 hrel
    · have hpos : 0 < (Finset.univ.filter (fun i : Fin (k + 1) => c i ≠ 1)).card := by
        rw [hcount]; exact Nat.pos_of_ne_zero hn
      obtain ⟨i0, hi0mem⟩ := Finset.card_pos.mp hpos
      have hi0ne1 : c i0 ≠ 1 := (Finset.mem_filter.mp hi0mem).2
      have hi0 : c i0 = -1 := by
        rcases hc i0 with h | h
        · exact absurd h hi0ne1
        · exact h
      have hi0ne0 : i0 ≠ 0 := by
        intro h; rw [h, hc0] at hi0ne1; exact hi0ne1 rfl
      have hex : ∃ j0 : Fin (k + 1), j0 ≠ i0 ∧ c j0 ≠ 1 := by
        by_contra h
        have hall : ∀ j, j ≠ i0 → c j = 1 := by
          intro j hj
          by_contra hcj
          exact h ⟨j, hj, hcj⟩
        have hprod_eq : (∏ i, c i) = c i0 := by
          rw [← Finset.mul_prod_erase Finset.univ c (Finset.mem_univ i0)]
          rw [Finset.prod_eq_one (fun j hj => hall j (Finset.mem_erase.mp hj).1), mul_one]
        have h1 : c i0 = 1 := by rw [← hprod_eq]; exact hcprod
        exact hi0ne1 h1
      obtain ⟨j0, hj0ne, hj0ne1⟩ := hex
      have hj0 : c j0 = -1 := by
        rcases hc j0 with h | h
        · exact absurd h hj0ne1
        · exact h
      have hj0ne0 : j0 ≠ 0 := by
        intro h; rw [h, hc0] at hj0ne1; exact hj0ne1 rfl
      have hσi0ne : σ i0 ≠ 0 := fun h =>
        hi0ne0 (σ.injective (h.trans hσ0.symm))
      obtain ⟨ib, hib⟩ : ∃ ib : Fin k, ib.succ = σ i0 := Fin.exists_succ_eq.mpr hσi0ne
      have hσj0ne : σ j0 ≠ 0 := fun h =>
        hj0ne0 (σ.injective (h.trans hσ0.symm))
      obtain ⟨jb, hjb⟩ : ∃ jb : Fin k, jb.succ = σ j0 := Fin.exists_succ_eq.mpr hσj0ne
      have hibj : ib ≠ jb := by
        intro h
        have h' : i0 = j0 := σ.injective (by rw [← hib, ← hjb, h])
        exact hj0ne h'.symm
      obtain ⟨a_d, ha_d_mem, ha_d_act⟩ :=
        hdRo7DDSdRAux_model_dinv p B Bs x L k τT hτT τC Φ hΦ hC hdinv hLx ib jb hibj
      let c' : Fin (k + 1) → ZMod p := fun i => if i = i0 ∨ i = j0 then -c i else c i
      let a' : MulAut ↥Bs := a_d * a
      have hc'i0 : c' i0 = 1 := by
        simp [c', hi0]
      have hc'j0 : c' j0 = 1 := by
        simp [c', hj0]
      have hc0' : c' 0 = 1 := by
        simp only [c']
        have h0 : ¬ ((0 : Fin (k + 1)) = i0 ∨ (0 : Fin (k + 1)) = j0) := by
          push Not
          exact ⟨Ne.symm hi0ne0, Ne.symm hj0ne0⟩
        rw [if_neg h0]
        exact hc0
      have hc' : ∀ i, c' i = 1 ∨ c' i = -1 := by
        intro i
        by_cases h : i = i0 ∨ i = j0
        · rw [show c' i = 1 from by
            rcases h with rfl | rfl
            · exact hc'i0
            · exact hc'j0]
          exact Or.inl rfl
        · have h1 : c' i = c i := by simp only [c']; rw [if_neg h]
          rw [h1]; exact hc i
      have hprod' : ∏ i, c' i = 1 := by
        have h := hdRo7DDSdRAux_prod_two c (Ne.symm hj0ne) hi0 hj0 hcprod
        simpa [c'] using h
      have hrel' : ∀ f i, Multiplicative.toAdd (τ.symm (a' (τ f)) (σ i)) =
          c' i * Multiplicative.toAdd (f i) := by
        intro f i
        have ha_d_eq : ∀ g, a_d (τ g) = τ (NbrOrth.dinv ib.succ jb.succ g) :=
          fun g => Subtype.ext (ha_d_act g)
        have ha' : τ.symm (a' (τ f)) =
            NbrOrth.dinv ib.succ jb.succ (τ.symm (a (τ f))) := by
          have hinner : a' (τ f) = a_d (τ (τ.symm (a (τ f)))) := by
            show (a_d * a) (τ f) = a_d (τ (τ.symm (a (τ f))))
            rw [MulAut.mul_apply, MulEquiv.apply_symm_apply]
          rw [hinner, ha_d_eq (τ.symm (a (τ f))), MulEquiv.symm_apply_apply]
        rw [ha']
        by_cases hi' : i = i0
        · rw [hi']
          rw [NbrOrth.dinv, Function.update_apply, if_pos hib.symm, Function.update_apply,
            if_neg (fun h => hibj (Fin.succ_inj.mp h))]
          rw [hib, show Multiplicative.toAdd ((τ.symm (a (τ f)) (σ i0))⁻¹) =
            -Multiplicative.toAdd (τ.symm (a (τ f)) (σ i0)) from rfl, hrel f i0,
            hi0, hc'i0, one_mul]
          ring
        · by_cases hj' : i = j0
          · rw [hj']
            rw [NbrOrth.dinv, Function.update_apply,
              if_neg (fun h => hj0ne (σ.injective (h.trans hib))), Function.update_apply,
              if_pos hjb.symm]
            rw [hjb, show Multiplicative.toAdd ((τ.symm (a (τ f)) (σ j0))⁻¹) =
              -Multiplicative.toAdd (τ.symm (a (τ f)) (σ j0)) from rfl, hrel f j0,
              hj0, hc'j0, one_mul]
            ring
          · have hnei : ¬ (σ i = ib.succ) := fun h =>
              hi' (σ.injective (h.trans hib))
            have hnej : ¬ (σ i = jb.succ) := fun h =>
              hj' (σ.injective (h.trans hjb))
            rw [NbrOrth.dinv, Function.update_apply, if_neg hnei, Function.update_apply,
              if_neg hnej]
            have hci : c' i = c i := by
              simp only [c']
              rw [if_neg]
              push Not
              exact ⟨hi', hj'⟩
            rw [hrel f i, hci]
      have hcount_lt : (Finset.univ.filter (fun i : Fin (k + 1) => c' i ≠ 1)).card < n := by
        have hfilter : Finset.univ.filter (fun i : Fin (k + 1) => c' i ≠ 1) =
            ((Finset.univ.filter (fun i : Fin (k + 1) => c i ≠ 1)).erase i0).erase j0 := by
          ext i
          by_cases hii : i = i0
          · subst hii
            simp [hc'i0]
          · by_cases hjj : i = j0
            · subst hjj
              simp [hc'j0, hii]
            · have hci : c' i = c i := by
                simp only [c']
                rw [if_neg]
                push Not
                exact ⟨hii, hjj⟩
              simp [hii, hjj, hci]
        rw [hfilter, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hj0ne, by simp [hj0ne1]⟩),
          Finset.card_erase_of_mem hi0mem, hcount, Nat.sub_sub]
        exact Nat.sub_lt (Nat.pos_of_ne_zero hn) (by norm_num)
      have ha'_mem : a' ∈ ggAutomizer L Bs :=
        ih _ hcount_lt a' σ c' hσ0 hc0' hc' hprod' rfl hrel'
      have haeq : a = a_d⁻¹ * a' := by
        show a = a_d⁻¹ * (a_d * a)
        group
      rw [haeq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ha_d_mem) ha'_mem

private lemma hdRo7DDSdRAux_model_forward {G : Type} [Group G] [Finite G] (p : ℕ)
    (B Bs : Subgroup G) (x : G) (L : Subgroup G) (k : ℕ)
    (τT : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ L))
    (hτT : Function.Bijective τT)
    (τC : Multiplicative (ZMod p) ≃* ↥(Bs ⊓ Subgroup.centralizer (L : Set G)))
    (Φ : ↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≃* ↥Bs)
    (hΦ : ∀ (t : ↥(Bs ⊓ L)) (c : ↥(Bs ⊓ Subgroup.centralizer (L : Set G))),
      (Φ (t, c) : G) = (t : G) * (c : G))
    (hC : ∀ m : Multiplicative (ZMod p), (τC m : G) = x ^ (Multiplicative.toAdd m).val)
    (hnorm : ∀ g : ↥L, (∀ e : ↥(Bs ⊓ L), ∃ e' : ↥(Bs ⊓ L),
        (g : G) * (e : G) * (g : G)⁻¹ = (e' : G)) →
      ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p),
        (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∏ i, ε i = 1 ∧
        ∀ f f', (g : G) * (τT f : G) * (g : G)⁻¹ = (τT f' : G) →
          ∀ i, Multiplicative.toAdd (f' (π i)) = ε i * Multiplicative.toAdd (f i))
    (hLx : ∀ g : ↥L, (g : G) * x * (g : G)⁻¹ = x)
    (a : MulAut ↥Bs) (ha : a ∈ ggAutomizer L Bs) :
    hdRo7DDSdRAux_CoordPerm p Bs k
      (hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ) a := by
  obtain ⟨g, hgL, hgN, haconj⟩ := mem_ggAutomizer_iff.mp ha
  have hgE : ∀ e : ↥(Bs ⊓ L), ∃ e' : ↥(Bs ⊓ L),
      (g : G) * (e : G) * (g : G)⁻¹ = (e' : G) := by
    intro e
    exact ⟨⟨(g : G) * (e : G) * (g : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp hgN (e : G)).mp e.2.1,
      L.mul_mem (L.mul_mem hgL e.2.2) (L.inv_mem hgL)⟩, rfl⟩
  obtain ⟨π, ε, hε, hεprod, hrel⟩ := hnorm ⟨g, hgL⟩ hgE
  have hgxp : ∀ n, (g : G) * x ^ n * (g : G)⁻¹ = x ^ n := by
    intro n
    calc (g : G) * x ^ n * (g : G)⁻¹ = (MulAut.conj (g : G)) (x ^ n) := by
          rw [MulAut.conj_apply]
      _ = ((MulAut.conj (g : G)) x) ^ n := map_pow _ _ _
      _ = x ^ n := by
          rw [show (MulAut.conj (g : G)) x = x from by
            rw [MulAut.conj_apply]; exact hLx ⟨g, hgL⟩]
  let eT : (Fin k → Multiplicative (ZMod p)) ≃* ↥(Bs ⊓ L) :=
    MulEquiv.ofBijective τT hτT
  let τ : (Fin (k + 1) → Multiplicative (ZMod p)) ≃* ↥Bs :=
    hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ
  refine ⟨Equiv.Perm.decomposeFin.symm (0, π), Fin.cases 1 ε, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.decomposeFin_symm_apply_zero]
  · rfl
  · intro i
    cases i using Fin.cases with
    | zero => exact Or.inl rfl
    | succ j => exact hε j
  · rw [Fin.prod_univ_succ]
    simp [hεprod]
  · intro f i
    have hmem : (g : G) * (τT (Fin.tail f) : G) * (g : G)⁻¹ ∈ Bs ⊓ L :=
      ⟨(Subgroup.mem_normalizer_iff.mp hgN (τT (Fin.tail f) : G)).mp (τT (Fin.tail f)).2.1,
        L.mul_mem (L.mul_mem hgL (τT (Fin.tail f)).2.2) (L.inv_mem hgL)⟩
    let f' : Fin k → Multiplicative (ZMod p) := eT.symm ⟨_, hmem⟩
    have hf' : (τT f' : G) = (g : G) * (τT (Fin.tail f) : G) * (g : G)⁻¹ := by
      change ((eT f' : ↥(Bs ⊓ L)) : G) = _
      rw [show eT f' = ⟨_, hmem⟩ from MulEquiv.apply_symm_apply _ _]
    let h : Fin (k + 1) → Multiplicative (ZMod p) := Fin.cons (f 0) f'
    have hτh : τ h = a (τ f) := by
      apply Subtype.ext
      rw [show ((τ h : ↥Bs) : G) = (τT (Fin.tail h) : G) *
          x ^ (Multiplicative.toAdd (h 0)).val from
        hdRo7CLCoordAux_tau_apply p B Bs x L k τT hτT τC Φ hΦ hC (f := h)]
      rw [show Fin.tail h = f' from Fin.tail_cons _ _, show h 0 = f 0 from Fin.cons_zero _ _,
        hf']
      rw [show (a (τ f) : G) = (g : G) * ((τ f : ↥Bs) : G) * (g : G)⁻¹ from haconj (τ f)]
      rw [show ((τ f : ↥Bs) : G) = (τT (Fin.tail f) : G) *
          x ^ (Multiplicative.toAdd (f 0)).val from
        hdRo7CLCoordAux_tau_apply p B Bs x L k τT hτT τC Φ hΦ hC (f := f)]
      rw [show (g : G) * ((τT (Fin.tail f) : G) * x ^ (Multiplicative.toAdd (f 0)).val) *
            (g : G)⁻¹ =
          ((g : G) * (τT (Fin.tail f) : G) * (g : G)⁻¹) *
            ((g : G) * x ^ (Multiplicative.toAdd (f 0)).val * (g : G)⁻¹) from by group]
      rw [hgxp (Multiplicative.toAdd (f 0)).val]
    have hsymm : τ.symm (a (τ f)) = h := (MulEquiv.symm_apply_eq τ).mpr hτh.symm
    rw [hsymm]
    cases i using Fin.cases with
    | zero =>
        rw [Equiv.Perm.decomposeFin_symm_apply_zero]
        simp [h]
    | succ j =>
        rw [Equiv.Perm.decomposeFin_symm_apply_succ]
        have hrelj := hrel (Fin.tail f) f' (by rw [hf']) j
        simpa [h, Equiv.swap_self, Fin.tail] using hrelj

private theorem hdRo7DDSdRAux_model_backward {G : Type} [Group G] [Finite G] (p : ℕ)
    (B Bs : Subgroup G) (x : G) (L : Subgroup G) (k : ℕ)
    (τT : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ L))
    (hτT : Function.Bijective τT)
    (τC : Multiplicative (ZMod p) ≃* ↥(Bs ⊓ Subgroup.centralizer (L : Set G)))
    (Φ : ↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≃* ↥Bs)
    (hΦ : ∀ (t : ↥(Bs ⊓ L)) (c : ↥(Bs ⊓ Subgroup.centralizer (L : Set G))),
      (Φ (t, c) : G) = (t : G) * (c : G))
    (hC : ∀ m : Multiplicative (ZMod p), (τC m : G) = x ^ (Multiplicative.toAdd m).val)
    (hdinv : ∀ i j : Fin k, i ≠ j → ∃ w : ↥L, ∀ f,
      (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (NbrOrth.dinv i j f) : G))
    (hperm : ∀ σ : Equiv.Perm (Fin k), ∃ w : ↥L, ∀ f,
      (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (SpCoord.permAut σ f) : G))
    (hLx : ∀ g : ↥L, (g : G) * x * (g : G)⁻¹ = x) (hx : x ∈ Bs)
    (a : MulAut ↥Bs)
    (ha : hdRo7DDSdRAux_CoordPerm p Bs k
      (hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ) a) :
    a ∈ ggAutomizer L Bs := by
  obtain ⟨σ, c, hσ0, hc0, hc, hcprod, hrel⟩ := ha
  exact hdRo7DDSdRAux_backward_aux p B Bs x L k τT hτT τC Φ hΦ hC hdinv hperm hLx hx
    _ a σ c hσ0 hc0 hc hcprod rfl hrel

theorem d_dcoordModel_tau_of_dirs {G : Type} [Group G] [Finite G] (p : ℕ)
    (B Bs : Subgroup G) (x : G) (L : Subgroup G) (k : ℕ)
    (τT : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ L))
    (hτT : Function.Bijective τT)
    (τC : Multiplicative (ZMod p) ≃* ↥(Bs ⊓ Subgroup.centralizer (L : Set G)))
    (Φ : ↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≃* ↥Bs)
    (hΦ : ∀ (t : ↥(Bs ⊓ L)) (c : ↥(Bs ⊓ Subgroup.centralizer (L : Set G))),
      (Φ (t, c) : G) = (t : G) * (c : G))
    (hC : ∀ m : Multiplicative (ZMod p), (τC m : G) = x ^ (Multiplicative.toAdd m).val)
    (hdinv : ∀ i j : Fin k, i ≠ j → ∃ w : ↥L, ∀ f,
      (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (NbrOrth.dinv i j f) : G))
    (hperm : ∀ σ : Equiv.Perm (Fin k), ∃ w : ↥L, ∀ f,
      (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (SpCoord.permAut σ f) : G))
    (hnorm : ∀ g : ↥L, (∀ e : ↥(Bs ⊓ L), ∃ e' : ↥(Bs ⊓ L),
        (g : G) * (e : G) * (g : G)⁻¹ = (e' : G)) →
      ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p),
        (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∏ i, ε i = 1 ∧
        ∀ f f', (g : G) * (τT f : G) * (g : G)⁻¹ = (τT f' : G) →
          ∀ i, Multiplicative.toAdd (f' (π i)) = ε i * Multiplicative.toAdd (f i))
    (hLx : ∀ g : ↥L, (g : G) * x * (g : G)⁻¹ = x)
    (hxp : x ^ p = 1) (hxne : x ≠ 1) (hp : Nat.Prime p) (hx : x ∈ Bs) :
    DCoordModel p Bs L k (hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ) := by
  intro a
  exact ⟨hdRo7DDSdRAux_model_forward p B Bs x L k τT hτT τC Φ hΦ hC hnorm hLx a,
    hdRo7DDSdRAux_model_backward p B Bs x L k τT hτT τC Φ hΦ hC hdinv hperm hLx hx a⟩

end CFSG.StandardType.HdRo7D
