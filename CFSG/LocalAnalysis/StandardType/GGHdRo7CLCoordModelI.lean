module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CLCoordModelH

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG.StandardType CFSG.Open CFSG.Assembly SpCoord

def hdRo7CLCoordAux_CoordPerm {G : Type} [Group G] (p : ℕ) (Bs : Subgroup G) (k : ℕ)
    (τ : (Fin (k + 1) → Multiplicative (ZMod p)) ≃* ↥Bs) (a : MulAut ↥Bs) : Prop :=
  ∃ (σ : Equiv.Perm (Fin (k + 1))) (c : Fin (k + 1) → ZMod p), σ 0 = 0 ∧ c 0 = 1 ∧
    (∀ i, c i = 1 ∨ c i = -1) ∧
    ∀ f i, Multiplicative.toAdd (τ.symm (a (τ f)) (σ i)) = c i * Multiplicative.toAdd (f i)

theorem hdRo7CLCoordAux_model_forward {G : Type} [Group G] [Finite G] (p : ℕ)
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
        (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', (g : G) * (τT f : G) * (g : G)⁻¹ = (τT f' : G) →
          ∀ i, Multiplicative.toAdd (f' (π i)) = ε i * Multiplicative.toAdd (f i))
    (hLx : ∀ g : ↥L, (g : G) * x * (g : G)⁻¹ = x)
    (hxp : x ^ p = 1) (hxne : x ≠ 1) (hp : Nat.Prime p) (hx : x ∈ Bs) :
    ∀ a : MulAut ↥Bs, a ∈ ggAutomizer L Bs →
      hdRo7CLCoordAux_CoordPerm p Bs k
        (hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ) a := by
  intro a ha
  obtain ⟨g, hgL, hgN, haconj⟩ := mem_ggAutomizer_iff.mp ha
  have hgE : ∀ e : ↥(Bs ⊓ L), ∃ e' : ↥(Bs ⊓ L), (g : G) * (e : G) * (g : G)⁻¹ = (e' : G) := by
    intro e
    exact ⟨⟨(g : G) * (e : G) * (g : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp hgN (e : G)).mp e.2.1,
      L.mul_mem (L.mul_mem hgL e.2.2) (L.inv_mem hgL)⟩, rfl⟩
  obtain ⟨π, ε, hε, hrel⟩ := hnorm ⟨g, hgL⟩ hgE
  have hgxp : ∀ n, (g : G) * x ^ n * (g : G)⁻¹ = x ^ n := by
    intro n
    calc (g : G) * x ^ n * (g : G)⁻¹ = (MulAut.conj (g : G)) (x ^ n) := by
          rw [MulAut.conj_apply]
      _ = ((MulAut.conj (g : G)) x) ^ n := map_pow _ _ _
      _ = x ^ n := by
          rw [show (MulAut.conj (g : G)) x = x from by rw [MulAut.conj_apply]; exact hLx ⟨g, hgL⟩]
  let eT : (Fin k → Multiplicative (ZMod p)) ≃* ↥(Bs ⊓ L) :=
    MulEquiv.ofBijective τT hτT
  let τ : (Fin (k + 1) → Multiplicative (ZMod p)) ≃* ↥Bs :=
    hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ
  refine ⟨Equiv.Perm.decomposeFin.symm (0, π), Fin.cases 1 ε, ?_, ?_, ?_, ?_⟩
  · rw [Equiv.Perm.decomposeFin_symm_apply_zero]
  · rfl
  · intro i
    cases i using Fin.cases with
    | zero => exact Or.inl rfl
    | succ j => exact hε j
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


theorem hdRo7CLCoordAux_conj_mem_normalizer {G : Type} [Group G] [Finite G] (p : ℕ)
    (B Bs : Subgroup G) (x : G) (L : Subgroup G) (k : ℕ)
    (τT : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ L))
    (hτT : Function.Bijective τT)
    (Φ : ↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≃* ↥Bs)
    (hΦ : ∀ (t : ↥(Bs ⊓ L)) (c : ↥(Bs ⊓ Subgroup.centralizer (L : Set G))),
      (Φ (t, c) : G) = (t : G) * (c : G))
    (u : ↥L) (s : MulAut (Fin k → Multiplicative (ZMod p)))
    (hu : ∀ f, (u : G) * (τT f : G) * (u : G)⁻¹ = (τT (s f) : G)) :
    (u : G) ∈ Subgroup.normalizer (Bs : Set G) := by
  let eT : (Fin k → Multiplicative (ZMod p)) ≃* ↥(Bs ⊓ L) := MulEquiv.ofBijective τT hτT
  have hconj : ∀ (w : ↥L) (s' : MulAut (Fin k → Multiplicative (ZMod p))),
      (∀ f, (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (s' f) : G)) →
      ∀ b : ↥Bs, (w : G) * (b : G) * (w : G)⁻¹ ∈ Bs := by
    intro w s' hw b
    obtain ⟨⟨t, c⟩, rfl⟩ := Φ.surjective b
    rw [hΦ t c]
    have hc : (w : G) * (c : G) * (w : G)⁻¹ = (c : G) := by
      have := Subgroup.mem_centralizer_iff.mp c.2.2 (w : G) w.2
      rw [this]; group
    have ht : (w : G) * (t : G) * (w : G)⁻¹ ∈ Bs := by
      obtain ⟨f, rfl⟩ := eT.surjective t
      change (w : G) * (τT f : G) * (w : G)⁻¹ ∈ Bs
      rw [hw f]
      exact (τT (s' f)).2.1
    rw [show (w : G) * ((t : G) * (c : G)) * (w : G)⁻¹ =
        ((w : G) * (t : G) * (w : G)⁻¹) * ((w : G) * (c : G) * (w : G)⁻¹) from by group,
      hc]
    exact Bs.mul_mem ht c.2.1
  have hu' : ∀ f, ((u⁻¹ : ↥L) : G) * (τT f : G) * ((u⁻¹ : ↥L) : G)⁻¹ = (τT (s⁻¹ f) : G) := by
    intro f
    have h1 := hu (s⁻¹ f)
    rw [MulAut.apply_inv_self] at h1
    calc ((u⁻¹ : ↥L) : G) * (τT f : G) * ((u⁻¹ : ↥L) : G)⁻¹
        = ((u⁻¹ : ↥L) : G) * ((u : G) * (τT (s⁻¹ f) : G) * (u : G)⁻¹) *
            ((u⁻¹ : ↥L) : G)⁻¹ := by rw [h1]
      _ = (τT (s⁻¹ f) : G) := by simp only [Subgroup.coe_inv]; group
  rw [Subgroup.mem_normalizer_iff]
  intro b
  exact ⟨fun hb => hconj u s hu ⟨b, hb⟩, fun hb => by
    have h1 := hconj (u⁻¹) s⁻¹ hu' ⟨(u : G) * (b : G) * (u : G)⁻¹, hb⟩
    have h2 : (↑(u⁻¹ : ↥L) : G) * ((u : G) * b * (u : G)⁻¹) * ((↑(u⁻¹ : ↥L) : G))⁻¹ = b := by
      simp only [Subgroup.coe_inv]; group
    rw [← h2]
    exact h1⟩

theorem hdRo7CLCoordAux_model_sign {G : Type} [Group G] [Finite G] (p : ℕ)
    (B Bs : Subgroup G) (x : G) (L : Subgroup G) (k : ℕ)
    (τT : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ L))
    (hτT : Function.Bijective τT)
    (τC : Multiplicative (ZMod p) ≃* ↥(Bs ⊓ Subgroup.centralizer (L : Set G)))
    (Φ : ↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≃* ↥Bs)
    (hΦ : ∀ (t : ↥(Bs ⊓ L)) (c : ↥(Bs ⊓ Subgroup.centralizer (L : Set G))),
      (Φ (t, c) : G) = (t : G) * (c : G))
    (hC : ∀ m : Multiplicative (ZMod p), (τC m : G) = x ^ (Multiplicative.toAdd m).val)
    (hsgn : ∀ i : Fin k, ∃ w : ↥L, ∀ f,
      (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (SpCoord.sgnAut i f) : G))
    (hLx : ∀ g : ↥L, (g : G) * x * (g : G)⁻¹ = x) (hx : x ∈ Bs) :
    ∀ i : Fin k, ∃ a ∈ ggAutomizer L Bs,
      ∀ f : Fin (k + 1) → Multiplicative (ZMod p),
        (a (hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ f) : G) =
          (hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ
            (Function.update f i.succ (f i.succ)⁻¹) : G) := by
  intro i
  obtain ⟨w, hw⟩ := hsgn i
  have hwN := hdRo7CLCoordAux_conj_mem_normalizer p B Bs x L k τT hτT Φ hΦ w (SpCoord.sgnAut i) hw
  have hwp : ∀ n, (w : G) * x ^ n * (w : G)⁻¹ = x ^ n := by
    intro n
    calc (w : G) * x ^ n * (w : G)⁻¹ = (MulAut.conj (w : G)) (x ^ n) := by
          rw [MulAut.conj_apply]
      _ = ((MulAut.conj (w : G)) x) ^ n := map_pow _ _ _
      _ = x ^ n := by
          rw [show (MulAut.conj (w : G)) x = x from by rw [MulAut.conj_apply]; exact hLx w]
  refine ⟨ggConjAut Bs hwN, ggConjAut_mem_ggAutomizer w.2 hwN, fun f => ?_⟩
  have htail : Fin.tail (Function.update f i.succ (f i.succ)⁻¹) =
      SpCoord.sgnAut i (Fin.tail f) := by
    funext j
    unfold Fin.tail
    rw [SpCoord.sgnAut_apply, Function.update_apply, Function.update_apply]
    by_cases hj : j = i
    · rw [hj]
      rw [if_pos rfl, if_pos rfl]
    · have h : ¬ (j.succ = i.succ) := fun hh => hj (Fin.succ_inj.mp hh)
      rw [if_neg h, if_neg hj]
  have hzero : (Function.update f i.succ (f i.succ)⁻¹) 0 = f 0 :=
    Function.update_of_ne (Fin.succ_ne_zero i).symm (f i.succ)⁻¹ f
  rw [ggConjAut_apply]
  rw [show ((hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ f : ↥Bs) : G) =
      (τT (Fin.tail f) : G) * x ^ (Multiplicative.toAdd (f 0)).val from
    hdRo7CLCoordAux_tau_apply p B Bs x L k τT hτT τC Φ hΦ hC (f := f)]
  rw [show ((hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ
        (Function.update f i.succ (f i.succ)⁻¹) : ↥Bs) : G) =
      (τT (Fin.tail (Function.update f i.succ (f i.succ)⁻¹)) : G) *
        x ^ (Multiplicative.toAdd ((Function.update f i.succ (f i.succ)⁻¹) 0)).val from
    hdRo7CLCoordAux_tau_apply p B Bs x L k τT hτT τC Φ hΦ hC
      (f := Function.update f i.succ (f i.succ)⁻¹)]
  rw [htail, hzero]
  rw [show (w : G) * ((τT (Fin.tail f) : G) * x ^ (Multiplicative.toAdd (f 0)).val) *
        (w : G)⁻¹ =
      ((w : G) * (τT (Fin.tail f) : G) * (w : G)⁻¹) *
        ((w : G) * x ^ (Multiplicative.toAdd (f 0)).val * (w : G)⁻¹) from by group]
  rw [hw (Fin.tail f), hwp (Multiplicative.toAdd (f 0)).val]

theorem hdRo7CLCoordAux_model_perm {G : Type} [Group G] [Finite G] (p : ℕ)
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
    (hLx : ∀ g : ↥L, (g : G) * x * (g : G)⁻¹ = x) (hx : x ∈ Bs) :
    ∀ π : Equiv.Perm (Fin k), ∃ a ∈ ggAutomizer L Bs,
      ∀ f : Fin (k + 1) → Multiplicative (ZMod p),
        (a (hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ f) : G) =
          (hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ
            (fun j => f (Equiv.Perm.decomposeFin.symm (0, π) j)) : G) := by
  intro π
  let σ : Equiv.Perm (Fin (k + 1)) := Equiv.Perm.decomposeFin.symm (0, π)
  obtain ⟨w, hw⟩ := hperm π⁻¹
  have hwN := hdRo7CLCoordAux_conj_mem_normalizer p B Bs x L k τT hτT Φ hΦ w
    (SpCoord.permAut π⁻¹) hw
  have hwp : ∀ n, (w : G) * x ^ n * (w : G)⁻¹ = x ^ n := by
    intro n
    calc (w : G) * x ^ n * (w : G)⁻¹ = (MulAut.conj (w : G)) (x ^ n) := by
          rw [MulAut.conj_apply]
      _ = ((MulAut.conj (w : G)) x) ^ n := map_pow _ _ _
      _ = x ^ n := by
          rw [show (MulAut.conj (w : G)) x = x from by rw [MulAut.conj_apply]; exact hLx w]
  have hσ : ∀ j : Fin k, σ j.succ = (π j).succ := by
    intro j
    simp [σ, Equiv.Perm.decomposeFin_symm_apply_succ]
  have hσ0 : σ 0 = 0 := by
    simp [σ, Equiv.Perm.decomposeFin_symm_apply_zero]
  refine ⟨ggConjAut Bs hwN, ggConjAut_mem_ggAutomizer w.2 hwN, fun f => ?_⟩
  let F : Fin (k + 1) → Multiplicative (ZMod p) := fun j => f (σ j)
  change (ggConjAut Bs hwN (hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ f) : G) =
    (hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ F : G)
  have htail : Fin.tail F = SpCoord.permAut π⁻¹ (Fin.tail f) := by
    funext j
    change f (σ j.succ) = f ((π j).succ)
    rw [hσ j]
  have hzero : F 0 = f 0 := by
    change f (σ 0) = f 0
    rw [hσ0]
  rw [ggConjAut_apply]
  rw [show ((hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ f : ↥Bs) : G) =
      (τT (Fin.tail f) : G) * x ^ (Multiplicative.toAdd (f 0)).val from
    hdRo7CLCoordAux_tau_apply p B Bs x L k τT hτT τC Φ hΦ hC (f := f)]
  rw [show ((hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ F : ↥Bs) : G) =
      (τT (Fin.tail F) : G) * x ^ (Multiplicative.toAdd (F 0)).val from
    hdRo7CLCoordAux_tau_apply p B Bs x L k τT hτT τC Φ hΦ hC (f := F)]
  rw [htail, hzero]
  rw [show (w : G) * ((τT (Fin.tail f) : G) * x ^ (Multiplicative.toAdd (f 0)).val) *
        (w : G)⁻¹ =
      ((w : G) * (τT (Fin.tail f) : G) * (w : G)⁻¹) *
        ((w : G) * x ^ (Multiplicative.toAdd (f 0)).val * (w : G)⁻¹) from by group]
  rw [hw (Fin.tail f), hwp (Multiplicative.toAdd (f 0)).val]

private theorem hdRo7CLCoordAux_model_backward_aux {G : Type} [Group G] [Finite G] (p : ℕ)
    (B Bs : Subgroup G) (x : G) (L : Subgroup G) (k : ℕ)
    (τT : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ L))
    (hτT : Function.Bijective τT)
    (τC : Multiplicative (ZMod p) ≃* ↥(Bs ⊓ Subgroup.centralizer (L : Set G)))
    (Φ : ↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≃* ↥Bs)
    (hΦ : ∀ (t : ↥(Bs ⊓ L)) (c : ↥(Bs ⊓ Subgroup.centralizer (L : Set G))),
      (Φ (t, c) : G) = (t : G) * (c : G))
    (hC : ∀ m : Multiplicative (ZMod p), (τC m : G) = x ^ (Multiplicative.toAdd m).val)
    (hsgn : ∀ i : Fin k, ∃ w : ↥L, ∀ f,
      (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (SpCoord.sgnAut i f) : G))
    (hperm : ∀ σ : Equiv.Perm (Fin k), ∃ w : ↥L, ∀ f,
      (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (SpCoord.permAut σ f) : G))
    (hLx : ∀ g : ↥L, (g : G) * x * (g : G)⁻¹ = x) (hx : x ∈ Bs) (n : ℕ) :
    ∀ (a : MulAut ↥Bs) (σ : Equiv.Perm (Fin (k + 1))) (c : Fin (k + 1) → ZMod p),
      σ 0 = 0 → c 0 = 1 → (∀ i, c i = 1 ∨ c i = -1) →
      (Finset.univ.filter (fun i : Fin (k + 1) => c i ≠ 1)).card = n →
      (∀ f i, Multiplicative.toAdd
        ((hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ).symm
          (a ((hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ) f)) (σ i)) =
        c i * Multiplicative.toAdd (f i)) →
      a ∈ ggAutomizer L Bs := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a σ c hσ0 hc0 hc hcount hrel
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
    · have hpos : 0 < (Finset.univ.filter (fun i : Fin (k + 1) => c i ≠ 1)).card := by
        rw [hcount]; exact Nat.pos_of_ne_zero hn
      obtain ⟨i0, hi0mem⟩ := Finset.card_pos.mp hpos
      have hi0ne1 : c i0 ≠ 1 := (Finset.mem_filter.mp hi0mem).2
      have hi0 : c i0 = -1 := by
        rcases hc i0 with h | h
        · exact absurd h hi0ne1
        · exact h
      have hi0ne : i0 ≠ 0 := by intro h; rw [h, hc0] at hi0ne1; exact hi0ne1 rfl
      have hσi0ne : σ i0 ≠ 0 := fun h => hi0ne (σ.injective (h.trans hσ0.symm))
      obtain ⟨j, hj⟩ : ∃ j : Fin k, j.succ = σ i0 := Fin.exists_succ_eq.mpr hσi0ne
      obtain ⟨a_j, ha_j_mem, ha_j_act⟩ :=
        hdRo7CLCoordAux_model_sign p B Bs x L k τT hτT τC Φ hΦ hC hsgn hLx hx j
      let c' : Fin (k + 1) → ZMod p := fun i => if i = i0 then -c i else c i
      let a' : MulAut ↥Bs := a_j * a
      have hc0' : c' 0 = 1 := by simp only [c']; rw [if_neg (Ne.symm hi0ne), hc0]
      have hc' : ∀ i, c' i = 1 ∨ c' i = -1 := by
        intro i
        by_cases h : i = i0
        · have h1 : c' i = 1 := by
            rw [h]
            simp [c', hi0]
          rw [h1]; exact Or.inl rfl
        · have hci : c' i = c i := by simp only [c']; rw [if_neg h]
          rw [hci]; exact hc i
      have hrel' : ∀ f i, Multiplicative.toAdd (τ.symm (a' (τ f)) (σ i)) =
          c' i * Multiplicative.toAdd (f i) := by
        intro f i
        have ha_j_eq : ∀ g, a_j (τ g) = τ (Function.update g j.succ (g j.succ)⁻¹) :=
          fun g => Subtype.ext (ha_j_act g)
        have ha' : τ.symm (a' (τ f)) =
            Function.update (τ.symm (a (τ f))) j.succ
              ((τ.symm (a (τ f))) j.succ)⁻¹ := by
          have hinner : a' (τ f) = a_j (τ (τ.symm (a (τ f)))) := by
            show (a_j * a) (τ f) = a_j (τ (τ.symm (a (τ f))))
            rw [MulAut.mul_apply, MulEquiv.apply_symm_apply]
          rw [hinner, ha_j_eq (τ.symm (a (τ f))), MulEquiv.symm_apply_apply]
        rw [ha']
        by_cases hi : i = i0
        · have hrelj := hrel f i0
          rw [← hj] at hrelj
          rw [hi, ← hj, Function.update_apply, if_pos rfl]
          rw [show Multiplicative.toAdd ((τ.symm (a (τ f)) j.succ)⁻¹) =
              -Multiplicative.toAdd (τ.symm (a (τ f)) j.succ) from rfl]
          rw [hrelj, hi0]
          have hc'i0 : c' i0 = 1 := by simp [c', hi0]
          rw [hc'i0, one_mul]
          ring
        · have hne : σ i ≠ j.succ := fun h => hi (σ.injective (h.trans hj))
          rw [Function.update_apply, if_neg hne]
          have hci : c' i = c i := by simp only [c']; rw [if_neg hi]
          rw [hrel f i, hci]
      have hfilter : Finset.univ.filter (fun i : Fin (k + 1) => c' i ≠ 1) =
          (Finset.univ.filter (fun i : Fin (k + 1) => c i ≠ 1)).erase i0 := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
        constructor
        · intro hi
          refine ⟨?_, ?_⟩
          · intro h
            have h1 : c' i0 = 1 := by simp [c', hi0]
            rw [← h] at h1
            exact hi h1
          · by_cases h : i = i0
            · rw [h]; exact hi0ne1
            · have hci : c' i = c i := by simp only [c']; rw [if_neg h]
              rwa [hci] at hi
        · rintro ⟨hne, hci⟩
          have h : i ≠ i0 := hne
          have hci' : c' i = c i := by simp only [c']; rw [if_neg h]
          rw [hci']
          exact hci
      have hcount_lt : (Finset.univ.filter (fun i : Fin (k + 1) => c' i ≠ 1)).card < n := by
        rw [hfilter, Finset.card_erase_of_mem hi0mem, hcount]; exact Nat.sub_lt (Nat.pos_of_ne_zero hn) (by norm_num)
      have ha'_mem : a' ∈ ggAutomizer L Bs :=
        ih _ hcount_lt a' σ c' hσ0 hc0' hc' rfl hrel'
      have haeq : a = a_j⁻¹ * a' := by rw [show a' = a_j * a from rfl]; group
      rw [haeq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ ha_j_mem) ha'_mem

theorem hdRo7CLCoordAux_model_backward {G : Type} [Group G] [Finite G] (p : ℕ)
    (B Bs : Subgroup G) (x : G) (L : Subgroup G) (k : ℕ)
    (τT : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ L))
    (hτT : Function.Bijective τT)
    (τC : Multiplicative (ZMod p) ≃* ↥(Bs ⊓ Subgroup.centralizer (L : Set G)))
    (Φ : ↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≃* ↥Bs)
    (hΦ : ∀ (t : ↥(Bs ⊓ L)) (c : ↥(Bs ⊓ Subgroup.centralizer (L : Set G))),
      (Φ (t, c) : G) = (t : G) * (c : G))
    (hC : ∀ m : Multiplicative (ZMod p), (τC m : G) = x ^ (Multiplicative.toAdd m).val)
    (hsgn : ∀ i : Fin k, ∃ w : ↥L, ∀ f,
      (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (SpCoord.sgnAut i f) : G))
    (hperm : ∀ σ : Equiv.Perm (Fin k), ∃ w : ↥L, ∀ f,
      (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (SpCoord.permAut σ f) : G))
    (hLx : ∀ g : ↥L, (g : G) * x * (g : G)⁻¹ = x)
    (hxp : x ^ p = 1) (hxne : x ≠ 1) (hp : Nat.Prime p) (hx : x ∈ Bs) :
    ∀ a : MulAut ↥Bs,
      hdRo7CLCoordAux_CoordPerm p Bs k
        (hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ) a →
      a ∈ ggAutomizer L Bs := by
  intro a ha
  obtain ⟨σ, c, hσ0, hc0, hc, hrel⟩ := ha
  exact hdRo7CLCoordAux_model_backward_aux p B Bs x L k τT hτT τC Φ hΦ hC hsgn hperm hLx hx
    (Finset.univ.filter (fun i : Fin (k + 1) => c i ≠ 1)).card a σ c hσ0 hc0 hc rfl hrel

theorem hdRo7CLCoordAux_coordModel_tau_of_dirs {G : Type} [Group G] [Finite G] (p : ℕ)
    (B Bs : Subgroup G) (x : G) (L : Subgroup G) (k : ℕ)
    (τT : (Fin k → Multiplicative (ZMod p)) →* ↥(Bs ⊓ L))
    (hτT : Function.Bijective τT)
    (τC : Multiplicative (ZMod p) ≃* ↥(Bs ⊓ Subgroup.centralizer (L : Set G)))
    (Φ : ↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≃* ↥Bs)
    (hΦ : ∀ (t : ↥(Bs ⊓ L)) (c : ↥(Bs ⊓ Subgroup.centralizer (L : Set G))),
      (Φ (t, c) : G) = (t : G) * (c : G))
    (hC : ∀ m : Multiplicative (ZMod p), (τC m : G) = x ^ (Multiplicative.toAdd m).val)
    (hsgn : ∀ i : Fin k, ∃ w : ↥L, ∀ f,
      (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (SpCoord.sgnAut i f) : G))
    (hperm : ∀ σ : Equiv.Perm (Fin k), ∃ w : ↥L, ∀ f,
      (w : G) * (τT f : G) * (w : G)⁻¹ = (τT (SpCoord.permAut σ f) : G))
    (hnorm : ∀ g : ↥L, (∀ e : ↥(Bs ⊓ L), ∃ e' : ↥(Bs ⊓ L),
        (g : G) * (e : G) * (g : G)⁻¹ = (e' : G)) →
      ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p),
        (∀ i, ε i = 1 ∨ ε i = -1) ∧
        ∀ f f', (g : G) * (τT f : G) * (g : G)⁻¹ = (τT f' : G) →
          ∀ i, Multiplicative.toAdd (f' (π i)) = ε i * Multiplicative.toAdd (f i))
    (hLx : ∀ g : ↥L, (g : G) * x * (g : G)⁻¹ = x)
    (hxp : x ^ p = 1) (hxne : x ≠ 1) (hp : Nat.Prime p) (hx : x ∈ Bs) :
    C2CoordModel p Bs L k (hdRo7CLCoordAux_tau p B Bs x L k τT hτT τC Φ) := by
  intro a
  exact ⟨hdRo7CLCoordAux_model_forward p B Bs x L k τT hτT τC Φ hΦ hC hnorm hLx hxp hxne hp hx a,
    hdRo7CLCoordAux_model_backward p B Bs x L k τT hτT τC Φ hΦ hC hsgn hperm hLx hxp hxne hp hx a⟩

end CFSG.StandardType.HdRo7C

end
