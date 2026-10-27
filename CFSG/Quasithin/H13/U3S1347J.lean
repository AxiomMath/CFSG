module

public import CFSG.Quasithin.H13.VolIH5
public import Mathlib.Order.CompletePartialOrder

public section

namespace CFSG.Quasithin.H13.U3

namespace L32Mod

open CFSG.Quasithin.H6

@[expose] def tb1 : Γ := ⟨!![1, 1, 0; 0, 1, 0; 0, 0, 1], by decide⟩

@[expose] def tb2 : Γ := ⟨!![1, 0, 0; 0, 1, 1; 0, 0, 1], by decide⟩

theorem borel_words : ∀ t : Γ, t ∈ H6.borel → t = 1 ∨ t = tb1 ∨ t = tb2 ∨ t = tb1 * tb2 ∨
    t = tb2 * tb1 ∨ t = tb1 * tb2 * tb1 ∨ t = tb2 * tb1 * tb2 ∨ t = tb1 * tb2 * tb1 * tb2 := by
  decide +kernel

theorem tb1_mem : tb1 ∈ H6.borel := by decide +kernel

theorem tb2_mem : tb2 ∈ H6.borel := by decide +kernel

@[expose] def o2 : Fin 8 → ZMod 2 := ![0, 0, 1, 1, 0, 0, 0, 0]

@[expose] def InKa (f : Fin 8 → ZMod 2) : Prop := f = 0 ∨ f = eF 0

@[expose] def InKb (f : Fin 8 → ZMod 2) : Prop := f = 0 ∨ f = eF 0 ∨ f = om ∨ f = om + eF 0

@[expose] def InKc (f : Fin 8 → ZMod 2) : Prop :=
  epsF f = 0 ∧ (f = 0 ∨ f = eF 0 ∨ ∃ k : Fin 7, actF (s7 k) f = bL ∨ actF (s7 k) f = bL + eF 0)

@[expose] def InKd (f : Fin 8 → ZMod 2) : Prop := epsF f = 0

instance : DecidablePred InKa := fun _ => by unfold InKa; infer_instance
instance : DecidablePred InKb := fun _ => by unfold InKb; infer_instance
instance : DecidablePred InKc := fun _ => by unfold InKc; infer_instance
instance : DecidablePred InKd := fun _ => by unfold InKd; infer_instance

theorem o2_fixed : ∀ t : Γ, t ∈ H6.borel → actF t o2 = o2 ∧ actF t bL = bL := by
  decide +kernel

theorem facts_a : ¬ InKa o2 ∧ ¬ InKa (o2 + eF 1) ∧ ¬ InKa bL ∧ ¬ InKa (bL + eF 1) ∧
    ¬ InKa (o2 + bL) ∧ ¬ InKa (o2 + bL + eF 1) := by
  decide +kernel

theorem facts_b : ¬ InKb o2 ∧ ¬ InKb (o2 + eF 1) := by
  decide +kernel

theorem facts_c : ¬ InKc o2 ∧ ¬ InKc (o2 + eF 1) ∧
    ∀ g : Γ, g ∈ Lp → InKc (actF g o2 + o2) ∧ InKc (actF g (o2 + eF 1) + (o2 + eF 1)) := by
  decide +kernel

theorem facts_d : ∀ f : Fin 8 → ZMod 2, InKd (actF tb1 f + f) → InKd (actF tb2 f + f) →
    InKd f ∨ InKd (f + eF 1) := by
  decide +kernel

theorem ker_cases (K : AddSubgroup (Fin 8 → ZMod 2)) (he0 : eF 0 ∈ K)
    (hinv : ∀ g : Γ, ∀ f ∈ K, actF g f ∈ K) (hε : ∀ f ∈ K, epsF f = 0) :
    (∀ f, f ∈ K ↔ InKa f) ∨ (∀ f, f ∈ K ↔ InKb f) ∨ (∀ f, f ∈ K ↔ InKc f) ∨
      (∀ f, f ∈ K ↔ InKd f) := by
  classical
  have hsmul : ∀ (c : ZMod 2) (f : Fin 8 → ZMod 2), f ∈ K → c • f ∈ K := by
    intro c f hf
    rcases zmod_two_cases c with rfl | rfl
    · rw [zero_smul]; exact K.zero_mem
    · rw [one_smul]; exact hf
  by_cases heL : eL ∈ K
  · right; right; right
    intro f
    refine ⟨hε f, fun hf => ?_⟩
    obtain ⟨c, rfl⟩ := ker_eps_span f hf
    refine K.add_mem (K.add_mem (K.add_mem (K.add_mem (hsmul _ _ he0) ?_) ?_) ?_) ?_ <;>
      exact hsmul _ _ (hinv _ _ heL)
  have hA : ∀ f ∈ K, ∀ k : Fin 7, actF (s7 k) f ≠ eL ∧ actF (s7 k) f ≠ eL + eF 0 := by
    intro f hf k
    refine ⟨fun h => heL (h ▸ hinv _ _ hf), fun h => heL ?_⟩
    have h1 : eL + eF 0 ∈ K := h ▸ hinv _ _ hf
    have h2 := K.add_mem h1 he0
    rwa [add_assoc, show eF 0 + eF 0 = (0 : Fin 8 → ZMod 2) by decide, add_zero] at h2
  have hmem_e0 : ∀ f, f + eF 0 ∈ K → f ∈ K := fun f h => by
    have := K.add_mem h he0
    rwa [add_assoc, show eF 0 + eF 0 = (0 : Fin 8 → ZMod 2) by decide, add_zero] at this
  by_cases hbL : bL ∈ K
  · right; right; left
    have hom : om ∉ K := fun h => heL (om_add_bL ▸ K.add_mem h hbL)
    intro f
    constructor
    · intro hf
      refine ⟨hε f hf, ?_⟩
      rcases ker_eps_cases f (hε f hf) with h | h | h | h | ⟨k, hk⟩ | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact absurd (h ▸ hf) hom
      · exact absurd (hmem_e0 _ (h ▸ hf)) hom
      · rcases hk with hk | hk
        · exact absurd hk (hA f hf k).1
        · exact absurd hk (hA f hf k).2
      · exact Or.inr (Or.inr h)
    · rintro ⟨-, h | h | ⟨k, hk | hk⟩⟩
      · exact h ▸ K.zero_mem
      · exact h ▸ he0
      · rw [← actF_inv_actF (s7 k) f, hk]; exact hinv _ _ hbL
      · rw [← actF_inv_actF (s7 k) f, hk]; exact hinv _ _ (K.add_mem hbL he0)
  have hB : ∀ f ∈ K, ∀ k : Fin 7, actF (s7 k) f ≠ bL ∧ actF (s7 k) f ≠ bL + eF 0 := by
    intro f hf k
    refine ⟨fun h => hbL (h ▸ hinv _ _ hf), fun h => hbL (hmem_e0 _ (h ▸ hinv _ _ hf))⟩
  have hsub : ∀ f ∈ K, f = 0 ∨ f = eF 0 ∨ f = om ∨ f = om + eF 0 := by
    intro f hf
    rcases ker_eps_cases f (hε f hf) with h | h | h | h | ⟨k, hk⟩ | ⟨k, hk⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · rcases hk with hk | hk
      · exact absurd hk (hA f hf k).1
      · exact absurd hk (hA f hf k).2
    · rcases hk with hk | hk
      · exact absurd hk (hB f hf k).1
      · exact absurd hk (hB f hf k).2
  by_cases hom : om ∈ K
  · right; left
    intro f
    refine ⟨hsub f, ?_⟩
    rintro (h | h | h | h)
    · exact h ▸ K.zero_mem
    · exact h ▸ he0
    · exact h ▸ hom
    · exact h ▸ K.add_mem hom he0
  · left
    intro f
    constructor
    · intro hf
      rcases hsub f hf with h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd (h ▸ hf) hom
      · exact absurd (hmem_e0 _ (h ▸ hf)) hom
    · rintro (h | h)
      · exact h ▸ K.zero_mem
      · exact h ▸ he0

theorem facts_core : (∀ f : Fin 8 → ZMod 2, f 0 = 0 → ∑ i, f i = 0 → InKb f → f = 0) ∧
    ∀ f : Fin 8 → ZMod 2, (f + f 0 • eF 0 + (∑ i, f i + f 0) • om) 0 = 0 ∧
      ∑ i, (f + f 0 • eF 0 + (∑ i, f i + f 0) • om) i = 0 ∧
      InKb (f + (f + f 0 • eF 0 + (∑ i, f i + f 0) • om)) := by
  decide +kernel

section Module

variable {M : Type} [AddCommGroup M] {ρ : Γ →* AddMonoid.End M}

theorem phi_e1 (h2 : ∀ m : M, m + m = 0) {x : M} (hx : ∀ g ∈ Lp, ρ g x = x) :
    phiHom ρ x h2 (eF 1) = x := by
  rw [phiHom_apply, phiF_eF, xpt_one hx]

theorem phi_act (h2 : ∀ m : M, m + m = 0) {x : M} (hx : ∀ g ∈ Lp, ρ g x = x) (g : Γ)
    (f : Fin 8 → ZMod 2) : phiHom ρ x h2 (actF g f) = ρ g (phiHom ρ x h2 f) :=
  phiF_actF hx g f

theorem phi_eq_iff (h2 : ∀ m : M, m + m = 0) {x : M} (f f' : Fin 8 → ZMod 2) :
    phiHom ρ x h2 f = phiHom ρ x h2 f' ↔ f + f' ∈ (phiHom ρ x h2).ker := by
  rw [AddMonoidHom.mem_ker, map_add]
  constructor
  · intro h
    rw [h, h2]
  · intro h
    have := congrArg (· + phiHom ρ x h2 f') h
    simpa [add_assoc, h2] using this

theorem add_mem_of_mem (h2 : ∀ m : M, m + m = 0) {x y a b : M} (ha : a = y ∨ a = x + y)
    (hb : b = y ∨ b = x + y) : a + b = 0 ∨ a + b = x := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> rw [ha, hb]
  · exact Or.inl (h2 y)
  · right
    rw [add_comm x y, ← add_assoc, h2, zero_add]
  · right
    rw [add_assoc, h2, add_zero]
  · exact Or.inl (h2 _)

theorem phi_mem_of_fixed (h2 : ∀ m : M, m + m = 0) {x y : M} (hx : ∀ g ∈ Lp, ρ g x = x)
    (hC : ∀ m : M, (∀ t ∈ H6.borel, ρ t m = m) → m = 0 ∨ m = x ∨ m = y ∨ m = x + y)
    {f : Fin 8 → ZMod 2} (hf : ∀ t ∈ H6.borel, actF t f + f ∈ (phiHom ρ x h2).ker)
    (hf0 : f ∉ (phiHom ρ x h2).ker) (hf1 : f + eF 1 ∉ (phiHom ρ x h2).ker) :
    phiHom ρ x h2 f = y ∨ phiHom ρ x h2 f = x + y := by
  have hfix : ∀ t ∈ H6.borel, ρ t (phiHom ρ x h2 f) = phiHom ρ x h2 f := fun t ht => by
    rw [← phi_act h2 hx, phi_eq_iff]
    exact hf t ht
  rcases hC _ hfix with h | h | h | h
  · exact absurd ((AddMonoidHom.mem_ker).2 h) hf0
  · exfalso
    apply hf1
    rw [AddMonoidHom.mem_ker, map_add, h, phi_e1 h2 hx, h2]
  · exact Or.inl h
  · exact Or.inr h

theorem pts_cases (h2 : ∀ m : M, m + m = 0) {x y : M} (hx : ∀ g ∈ Lp, ρ g x = x)
    (hnf : ∃ g : Γ, ρ g x ≠ x) (hy0 : y ≠ 0) (hyx : y ≠ x)
    (hC : ∀ m : M, (∀ t ∈ H6.borel, ρ t m = m) → m = 0 ∨ m = x ∨ m = y ∨ m = x + y) :
    (y ∈ (phiHom ρ x h2).range ∧ ∀ f, f ∈ (phiHom ρ x h2).ker ↔ InKb f) ∨
      (∀ g ∈ Lp, ρ g y = y) ∨ (∀ f, f ∈ (phiHom ρ x h2).ker ↔ InKd f) := by
  obtain ⟨he0, hinv, hε⟩ := ker_facts hx h2 hnf
  set φ := phiHom ρ x h2 with hφ
  have hfixK : ∀ (P : (Fin 8 → ZMod 2) → Prop), (∀ f, f ∈ φ.ker ↔ P f) →
      ∀ f, (∀ t ∈ H6.borel, actF t f = f) → ∀ t ∈ H6.borel, actF t f + f ∈ φ.ker := by
    intro P _ f hf t ht
    rw [hf t ht, AddMonoidHom.mem_ker, map_add, h2]
  have hx2 : x + y + x = y := by rw [add_comm x y, add_assoc, h2, add_zero]
  rcases ker_cases φ.ker he0 hinv hε with hK | hK | hK | hK
  ·
    exfalso
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := facts_a
    have hfo2 := hfixK _ hK o2 fun t ht => (o2_fixed t ht).1
    have hfbL := hfixK _ hK bL fun t ht => (o2_fixed t ht).2
    have hfs : ∀ t ∈ H6.borel, actF t (o2 + bL) + (o2 + bL) ∈ φ.ker := by
      refine hfixK _ hK (o2 + bL) fun t ht => ?_
      rw [actF_add, (o2_fixed t ht).1, (o2_fixed t ht).2]
    have h1 := phi_mem_of_fixed h2 hx hC hfo2 (fun h => a1 ((hK _).1 h))
      (fun h => a2 ((hK _).1 h))
    have h2' := phi_mem_of_fixed h2 hx hC hfbL (fun h => a3 ((hK _).1 h))
      (fun h => a4 ((hK _).1 h))
    have h3 := phi_mem_of_fixed h2 hx hC hfs (fun h => a5 ((hK _).1 h))
      (fun h => a6 ((hK _).1 h))
    rw [map_add] at h3
    rcases add_mem_of_mem h2 h1 h2' with h4 | h4 <;> rw [h4] at h3
    · rcases h3 with h3 | h3
      · exact hy0 h3.symm
      · exact hyx (by
          have := congrArg (· + x) h3
          simpa [add_comm x y, add_assoc, h2] using this.symm)
    · rcases h3 with h3 | h3
      · exact hyx h3.symm
      · exact hy0 (by
          have := congrArg (x + ·) h3
          simpa [← add_assoc, h2] using this.symm)
  ·
    left
    refine ⟨?_, hK⟩
    obtain ⟨b1, b2⟩ := facts_b
    have hfo2 := hfixK _ hK o2 fun t ht => (o2_fixed t ht).1
    rcases phi_mem_of_fixed h2 hx hC hfo2 (fun h => b1 ((hK _).1 h))
      (fun h => b2 ((hK _).1 h)) with h | h
    · exact ⟨o2, h⟩
    · refine ⟨o2 + eF 1, ?_⟩
      rw [map_add, h, phi_e1 h2 hx, hx2]
  ·
    right; left
    obtain ⟨c1, c2, c3⟩ := facts_c
    have hfo2 := hfixK _ hK o2 fun t ht => (o2_fixed t ht).1
    intro g hg
    rcases phi_mem_of_fixed h2 hx hC hfo2 (fun h => c1 ((hK _).1 h))
      (fun h => c2 ((hK _).1 h)) with h | h
    · rw [← h, ← phi_act h2 hx, phi_eq_iff]
      exact (hK _).2 (c3 g hg).1
    · have hy : y = φ (o2 + eF 1) := by rw [map_add, h, phi_e1 h2 hx, hx2]
      rw [hy, ← phi_act h2 hx, phi_eq_iff]
      exact (hK _).2 (c3 g hg).2
  · right; right
    exact hK

theorem v3_add_self : ∀ v : V3, v + v = 0 := by decide

theorem pts_d_fixed (h2 : ∀ m : M, m + m = 0) {x : M} (hx : ∀ g ∈ Lp, ρ g x = x)
    (hK : ∀ f, f ∈ (phiHom ρ x h2).ker ↔ InKd f) {m : M} (hm : m ∈ (phiHom ρ x h2).range)
    (hfix : ∀ t ∈ H6.borel, ρ t m = m) : m = 0 ∨ m = x := by
  obtain ⟨f, rfl⟩ := hm
  have h1 : ∀ t ∈ H6.borel, actF t f + f ∈ (phiHom ρ x h2).ker := fun t ht => by
    rw [← phi_eq_iff, phi_act h2 hx, hfix t ht]
  rcases facts_d f ((hK _).1 (h1 tb1 tb1_mem)) ((hK _).1 (h1 tb2 tb2_mem)) with h | h
  · exact Or.inl ((hK f).2 h)
  · exact Or.inr (((phi_eq_iff h2 f (eF 1)).2 ((hK _).2 h)).trans (phi_e1 h2 hx))

theorem pts_d_irred (h2 : ∀ m : M, m + m = 0) {x : M} (hx : ∀ g ∈ Lp, ρ g x = x)
    (hK : ∀ f, f ∈ (phiHom ρ x h2).ker ↔ InKd f) {m : M} (hm : m ∈ (phiHom ρ x h2).range)
    (hm0 : m ≠ 0) : ∃ g : Γ, ρ g m = x := by
  obtain ⟨f, rfl⟩ := hm
  have hε : epsF f ≠ 0 := fun h => hm0 ((AddMonoidHom.mem_ker).1 ((hK f).2 h))
  have hi : idxOf (epsF f) ≠ 0 := by
    intro h
    apply hε
    rw [← vecOf_idxOf (epsF f), h]
    decide
  obtain ⟨g, hg⟩ := exists_smul_e1 _ hi
  rw [vecOf_idxOf] at hg
  refine ⟨g⁻¹, ?_⟩
  have h1 : InKd (actF g⁻¹ f + eF 1) := by
    show epsF (actF g⁻¹ f + eF 1) = 0
    rw [epsF_add, epsF_actF, epsF_eF, ← hg, inv_smul_smul, v3_add_self]
  rw [← phi_act h2 hx]
  exact ((phi_eq_iff h2 _ (eF 1)).2 ((hK _).2 h1)).trans (phi_e1 h2 hx)

theorem pts_d_iso (h2 : ∀ m : M, m + m = 0) {x : M}
    (hK : ∀ f, f ∈ (phiHom ρ x h2).ker ↔ InKd f) :
    ∃ e : ↥(phiHom ρ x h2).range ≃+ V3, ∀ f, e ⟨phiHom ρ x h2 f, f, rfl⟩ = epsF f := by
  have hker : (phiHom ρ x h2).ker = epsHom.ker := by
    ext f
    rw [hK, AddMonoidHom.mem_ker]
    rfl
  have hsurj : Function.Surjective epsHom := fun v =>
    ⟨eF (idxOf v), by show epsF _ = v; rw [epsF_eF, vecOf_idxOf]⟩
  refine ⟨(QuotientAddGroup.quotientKerEquivRange (phiHom ρ x h2)).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq hker).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective epsHom hsurj)), fun f => ?_⟩
  have h1 : (QuotientAddGroup.quotientKerEquivRange (phiHom ρ x h2)).symm
      ⟨phiHom ρ x h2 f, f, rfl⟩ = (f : (Fin 8 → ZMod 2) ⧸ (phiHom ρ x h2).ker) := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  rw [AddEquiv.trans_apply, h1, AddEquiv.trans_apply]
  rfl

theorem pts_b_iso (h2 : ∀ m : M, m + m = 0) {x : M} (hx : ∀ g ∈ Lp, ρ g x = x)
    (hK : ∀ f, f ∈ (phiHom ρ x h2).ker ↔ InKb f) (htop : (phiHom ρ x h2).range = ⊤) :
    IsoMod ρ ρCore := by
  obtain ⟨hinj, hsurj⟩ := facts_core
  refine ⟨(phiHom ρ x h2).comp coreSub.subtype, ⟨fun c c' hcc => ?_, fun m => ?_⟩,
    fun g c => ?_⟩
  · have h1 : (c : Fin 8 → ZMod 2) + c' ∈ (phiHom ρ x h2).ker := (phi_eq_iff h2 _ _).1 hcc
    have h3 : ((c : Fin 8 → ZMod 2) + c') 0 = 0 ∧ ∑ i, ((c : Fin 8 → ZMod 2) + c') i = 0 := by
      have hc := mem_coreSub.1 c.2
      have hc' := mem_coreSub.1 c'.2
      refine ⟨by rw [Pi.add_apply, hc.1, hc'.1, add_zero], ?_⟩
      simp only [Pi.add_apply, Finset.sum_add_distrib, hc.2, hc'.2, add_zero]
    have h4 := hinj _ h3.1 h3.2 ((hK _).1 h1)
    apply Subtype.ext
    have := congrArg (· + (c' : Fin 8 → ZMod 2)) h4
    simpa [add_assoc, show ∀ f : Fin 8 → ZMod 2, f + f = 0 from fun f => by
      funext i; exact (by decide : ∀ a : ZMod 2, a + a = 0) _] using this
  · have hm : m ∈ (phiHom ρ x h2).range := htop ▸ AddSubgroup.mem_top m
    obtain ⟨f, rfl⟩ := hm
    obtain ⟨hc0, hcs, hcK⟩ := hsurj f
    refine ⟨⟨_, mem_coreSub.2 ⟨hc0, hcs⟩⟩, ?_⟩
    show phiHom ρ x h2 _ = phiHom ρ x h2 f
    rw [phi_eq_iff, add_comm]
    exact (hK _).2 hcK
  · show phiHom ρ x h2 (g • c).1 = ρ g (phiHom ρ x h2 c.1)
    rw [← phi_act h2 hx]
    rfl

theorem graph_graph (g : Γ) : graph (graph g) = g := graphFun_graphFun g

theorem graph_mem_Lp_iff (g : Γ) : graph g ∈ Lp ↔ g ∈ Ll := by
  have := graph_mem_Ll_iff (graph g)
  rw [graph_graph] at this
  exact this.symm

theorem borel_le_Lp : H6.borel ≤ Lp := inf_le_left

theorem l32_cases (h2 : ∀ m : M, m + m = 0) {x y : M} (hx : ∀ g ∈ Lp, ρ g x = x)
    (hy : ∀ g ∈ Ll, ρ g y = y) (hxl : ∃ g ∈ Ll, ρ g x ≠ x) (hyp : ∃ g ∈ Lp, ρ g y ≠ y)
    (hgen : ∀ N : AddSubgroup M, (∀ g, ρ g x ∈ N) → (∀ g, ρ g y ∈ N) → N = ⊤)
    (hC : ∀ m : M, (∀ t ∈ H6.borel, ρ t m = m) → m = 0 ∨ m = x ∨ m = y ∨ m = x + y) :
    IsoMod ρ ρCore ∨ IsoMod (ρ.comp graph.toMonoidHom) ρCore ∨
      ∃ U₁ U₂ : AddSubgroup M, U₁ ⊔ U₂ = ⊤ ∧ U₁ ⊓ U₂ = ⊥ ∧
        (∀ g, ∀ m ∈ U₁, ρ g m ∈ U₁) ∧ (∀ g, ∀ m ∈ U₂, ρ g m ∈ U₂) ∧
        (∃ e : ↥U₁ ≃+ V3, ∀ (g : Γ) (m : M) (hm : m ∈ U₁) (hgm : ρ g m ∈ U₁),
          e ⟨ρ g m, hgm⟩ = g • e ⟨m, hm⟩) ∧
        (∃ e : ↥U₂ ≃+ V3, ∀ (g : Γ) (m : M) (hm : m ∈ U₂) (hgm : ρ g m ∈ U₂),
          e ⟨ρ g m, hgm⟩ = graph g • e ⟨m, hm⟩) := by
  set ρ' := ρ.comp graph.toMonoidHom with hρ'
  have hρ'g : ∀ g m, ρ' g m = ρ (graph g) m := fun _ _ => rfl
  obtain ⟨gx, hgx, hgx'⟩ := hxl
  obtain ⟨gy, hgy, hgy'⟩ := hyp
  have hx0 : x ≠ 0 := fun h => hgx' (by rw [h, map_zero])
  have hy0 : y ≠ 0 := fun h => hgy' (by rw [h, map_zero])
  have hyx : y ≠ x := fun h => hgx' (h ▸ hy gx hgx)
  have hy' : ∀ g ∈ Lp, ρ' g y = y := fun g hg => hy _ ((graph_mem_Ll_iff g).2 hg)
  have hnfy : ∃ g, ρ' g y ≠ y := ⟨graph gy, by rw [hρ'g, graph_graph]; exact hgy'⟩
  have hC' : ∀ m : M, (∀ t ∈ H6.borel, ρ' t m = m) → m = 0 ∨ m = y ∨ m = x ∨ m = y + x := by
    intro m hm
    have hm' : ∀ t ∈ H6.borel, ρ t m = m := fun t ht => by
      have := hm (graph t) ((graph_mem_borel_iff t).2 ht)
      rwa [hρ'g, graph_graph] at this
    rcases hC m hm' with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (by rw [h, add_comm])))
  have hinvx : ∀ g, ∀ m ∈ (phiHom ρ x h2).range, ρ g m ∈ (phiHom ρ x h2).range := by
    rintro g _ ⟨f, rfl⟩
    exact ⟨actF g f, phi_act h2 hx g f⟩
  have hinvy : ∀ g, ∀ m ∈ (phiHom ρ' y h2).range, ρ g m ∈ (phiHom ρ' y h2).range := by
    rintro g _ ⟨f, rfl⟩
    refine ⟨actF (graph g) f, ?_⟩
    rw [phi_act h2 hy', hρ'g, graph_graph]
  have hxr : x ∈ (phiHom ρ x h2).range := ⟨eF 1, phi_e1 h2 hx⟩
  have hyr : y ∈ (phiHom ρ' y h2).range := ⟨eF 1, phi_e1 h2 hy'⟩
  have htop : ∀ N : AddSubgroup M, (∀ g, ∀ m ∈ N, ρ g m ∈ N) → x ∈ N → y ∈ N → N = ⊤ :=
    fun N hN hxN hyN => hgen N (fun g => hN g x hxN) (fun g => hN g y hyN)
  rcases pts_cases h2 hx ⟨gx, hgx'⟩ hy0 hyx hC with ⟨hyx', hK⟩ | hyLp | hKd
  · exact Or.inl (pts_b_iso h2 hx hK (htop _ hinvx hxr hyx'))
  · exact absurd (hyLp gy hgy) hgy'
  rcases pts_cases h2 hy' hnfy hx0 hyx.symm hC' with ⟨hxy', hK'⟩ | hxLp | hKd'
  · exact Or.inr (Or.inl (pts_b_iso h2 hy' hK' (htop _ hinvy hxy' hyr)))
  · exfalso
    apply hgx'
    have := hxLp (graph gx) ((graph_mem_Lp_iff gx).2 hgx)
    rwa [hρ'g, graph_graph] at this
  right; right
  obtain ⟨e₁, he₁⟩ := pts_d_iso h2 hKd
  obtain ⟨e₂, he₂⟩ := pts_d_iso h2 hKd'
  refine ⟨_, _, htop _ ?_ (AddSubgroup.mem_sup_left hxr) (AddSubgroup.mem_sup_right hyr), ?_,
    hinvx, hinvy, ⟨e₁, ?_⟩, ⟨e₂, ?_⟩⟩
  · intro g m hm
    obtain ⟨a, ha, b, hb, rfl⟩ := AddSubgroup.mem_sup.1 hm
    rw [map_add]
    exact AddSubgroup.add_mem_sup (hinvx g a ha) (hinvy g b hb)
  · rw [eq_bot_iff]
    intro m hm
    rw [AddSubgroup.mem_bot]
    by_contra hm0
    obtain ⟨g, hg⟩ := pts_d_irred h2 hx hKd (AddSubgroup.mem_inf.1 hm).1 hm0
    have hxU : x ∈ (phiHom ρ' y h2).range := hg ▸ hinvy g m (AddSubgroup.mem_inf.1 hm).2
    rcases pts_d_fixed h2 hy' hKd' hxU (fun t ht => by
      rw [hρ'g]
      exact hx _ (borel_le_Lp ((graph_mem_borel_iff t).2 ht))) with h | h
    · exact hx0 h
    · exact hyx h.symm
  · intro g m hm hgm
    obtain ⟨f, rfl⟩ := hm
    have h1 : (⟨ρ g (phiHom ρ x h2 f), hgm⟩ : ↥(phiHom ρ x h2).range) =
        ⟨phiHom ρ x h2 (actF g f), actF g f, rfl⟩ := Subtype.ext (phi_act h2 hx g f).symm
    rw [h1, he₁, he₁, epsF_actF]
  · intro g m hm hgm
    obtain ⟨f, rfl⟩ := hm
    have hv : ρ g (phiHom ρ' y h2 f) = phiHom ρ' y h2 (actF (graph g) f) := by
      rw [phi_act h2 hy', hρ'g, graph_graph]
    have h1 : (⟨ρ g (phiHom ρ' y h2 f), hgm⟩ : ↥(phiHom ρ' y h2).range) =
        ⟨phiHom ρ' y h2 (actF (graph g) f), actF (graph g) f, rfl⟩ := Subtype.ext hv
    rw [h1, he₂, he₂, epsF_actF]

end Module

end L32Mod

end CFSG.Quasithin.H13.U3
