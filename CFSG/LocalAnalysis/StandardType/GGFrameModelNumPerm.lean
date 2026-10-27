module

public import CFSG.LocalAnalysis.StandardType.GGFrameModelNum

public section

namespace CFSG.StandardType.FrameRoute

open CFSG

private def frameAP_isSwapSet (d : ℕ) : Set (Equiv.Perm (Fin d)) :=
  {σ | σ.IsSwap}

private noncomputable def frameAP_transpositions (d : ℕ) : Finset (Equiv.Perm (Fin d)) := by
  classical
  exact Finset.univ.filter (fun σ => σ.IsSwap)

private abbrev frameAP_P (d : ℕ) : Type := {x : Fin d × Fin d // x.1 < x.2}

private def frameAP_edge {d : ℕ} : Equiv.Perm (Fin d) → Equiv.Perm (Fin d) → Prop :=
  fun σ τ => σ.IsSwap ∧ τ.IsSwap ∧ σ * τ ≠ τ * σ

private def frameAP_pairFinset {d : ℕ} (a b : Fin d) : Finset (Fin d × Fin d) :=
  ({a, b} : Finset (Fin d)) ×ˢ ({a, b} : Finset (Fin d))ᶜ

private noncomputable def frameAP_noncommFinset {d : ℕ} (a b : Fin d) :
    Finset (Equiv.Perm (Fin d)) := by
  classical
  exact Finset.univ.filter
    (fun τ => τ.IsSwap ∧ Equiv.swap a b * τ ≠ τ * Equiv.swap a b)

private lemma frameAP_swap_lt_inj {d : ℕ} {a b c e : Fin d} (hab : a < b) (hce : c < e)
    (h : Equiv.swap a b = Equiv.swap c e) : a = c ∧ b = e := by
  have h1 : Equiv.swap c e a = b := by rw [← h, Equiv.swap_apply_left]
  rw [Equiv.swap_apply_def] at h1
  split_ifs at h1 with hac hae
  · exact ⟨hac, h1.symm⟩
  · exfalso
    have hlt₁ : a < c := by rwa [← h1] at hab
    have hlt₂ : c < a := by rwa [← hae] at hce
    exact lt_asymm hlt₁ hlt₂
  · exact absurd h1 hab.ne

private noncomputable def frameAP_equivP (d : ℕ) :
    frameAP_P d ≃ {σ : Equiv.Perm (Fin d) // σ.IsSwap} := by
  classical
  let f : frameAP_P d → {σ : Equiv.Perm (Fin d) // σ.IsSwap} :=
    fun x => ⟨Equiv.swap x.1.1 x.1.2, ⟨x.1.1, x.1.2, x.2.ne, rfl⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro x y h
    have hswap : Equiv.swap x.1.1 x.1.2 = Equiv.swap y.1.1 y.1.2 :=
      congrArg Subtype.val h
    obtain ⟨h1, h2⟩ := frameAP_swap_lt_inj x.2 y.2 hswap
    exact Subtype.ext (Prod.ext h1 h2)
  · intro σ
    obtain ⟨a, b, hab, hσ⟩ := σ.2
    rcases lt_or_gt_of_ne hab with hlt | hlt
    · refine ⟨⟨(a, b), hlt⟩, ?_⟩
      apply Subtype.ext
      simpa [f] using hσ.symm
    · refine ⟨⟨(b, a), hlt⟩, ?_⟩
      apply Subtype.ext
      change Equiv.swap b a = σ.1
      rw [Equiv.swap_comm]
      exact hσ.symm

private lemma frameAP_card_P (d : ℕ) : Fintype.card (frameAP_P d) = d.choose 2 := by
  classical
  change Fintype.card {x : Fin d × Fin d // x.1 < x.2} = d.choose 2
  rw [Fintype.card_subtype]
  simpa using (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin d))))

private lemma frameAP_card_transpositions (d : ℕ) :
    (frameAP_transpositions d).card = d.choose 2 := by
  classical
  have hcard : Fintype.card {σ : Equiv.Perm (Fin d) // σ.IsSwap}
      = (frameAP_transpositions d).card := by
    rw [← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (by
      intro σ
      simp [frameAP_transpositions]))
  rw [← hcard, ← Fintype.card_congr (frameAP_equivP d)]
  exact frameAP_card_P d

private lemma frameAP_swap_mul_swap_ne_comm {α : Type*} [DecidableEq α] {a b c : α}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    Equiv.swap a b * Equiv.swap a c ≠ Equiv.swap a c * Equiv.swap a b := by
  intro h
  have hc : b = a := by
    have h' := congrFun (congrArg (fun f : Equiv.Perm α => (f : α → α)) h) c
    rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm,
      Equiv.swap_apply_right] at h'
    exact h'
  exact hab hc.symm

private lemma frameAP_swap_mul_swap_comm_of_ne {α : Type*} [Fintype α] [DecidableEq α]
    {a b c e : α} (hac : a ≠ c) (hae : a ≠ e) (hbc : b ≠ c) (hbe : b ≠ e) :
    Equiv.swap a b * Equiv.swap c e = Equiv.swap c e * Equiv.swap a b := by
  have hd : Equiv.Perm.Disjoint (Equiv.swap a b) (Equiv.swap c e) := by
    rw [Equiv.Perm.disjoint_iff_disjoint_support]
    by_cases hab : a = b
    · subst b
      simp
    · by_cases hce : c = e
      · subst e
        simp
      · rw [Equiv.Perm.support_swap hab, Equiv.Perm.support_swap hce]
        simp [Finset.disjoint_left, hac, hae, hbc, hbe]
  exact (Equiv.Perm.Disjoint.commute hd).eq

private lemma frameAP_card_pairFinset {d : ℕ} {a b : Fin d} (hab : a ≠ b) :
    (frameAP_pairFinset a b).card = 2 * (d - 2) := by
  classical
  rw [frameAP_pairFinset, Finset.card_product, Finset.card_compl, Finset.card_pair hab]
  simp

private lemma frameAP_card_noncomm {d : ℕ} {a b : Fin d} (hab : a ≠ b) :
    (frameAP_noncommFinset a b).card = 2 * (d - 2) := by
  classical
  have hcard : (frameAP_pairFinset a b).card = (frameAP_noncommFinset a b).card := by
    refine Finset.card_bij (s := frameAP_pairFinset a b) (t := frameAP_noncommFinset a b)
      (fun x _ => Equiv.swap x.1 x.2) ?_ ?_ ?_
    · intro x hx
      rw [frameAP_pairFinset, Finset.mem_product, Finset.mem_compl] at hx
      obtain ⟨hx1, hx2⟩ := hx
      have hx1' : x.1 = a ∨ x.1 = b := by simpa using hx1
      have hx2' : x.2 ≠ a ∧ x.2 ≠ b := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hx2
      have hne : x.1 ≠ x.2 := by
        intro h12
        rcases hx1' with hxa | hxb
        · exact hx2'.1 (hxa.symm.trans h12).symm
        · exact hx2'.2 (hxb.symm.trans h12).symm
      simp only [frameAP_noncommFinset, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ⟨x.1, x.2, hne, rfl⟩, by
        rcases hx1' with hxa | hxb
        · rw [hxa]
          exact frameAP_swap_mul_swap_ne_comm hab (Ne.symm hx2'.1) (Ne.symm hx2'.2)
        · rw [hxb]
          have h := frameAP_swap_mul_swap_ne_comm (a := b) (b := a) (c := x.2)
            hab.symm (Ne.symm hx2'.2) (Ne.symm hx2'.1)
          simpa [Equiv.swap_comm b a] using h⟩
    · intro x hx y hy hxy
      rw [frameAP_pairFinset, Finset.mem_product, Finset.mem_compl] at hx hy
      obtain ⟨hx1, hx2⟩ := hx
      obtain ⟨hy1, hy2⟩ := hy
      have hx1' : x.1 = a ∨ x.1 = b := by simpa using hx1
      have hx2' : x.2 ≠ a ∧ x.2 ≠ b := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hx2
      have hy2' : y.2 ≠ a ∧ y.2 ≠ b := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hy2
      have h1 : Equiv.swap y.1 y.2 x.1 = x.2 := by
        have h := congrFun (congrArg (fun f : Equiv.Perm (Fin d) => (f : Fin d → Fin d))
          hxy) x.1
        rw [Equiv.swap_apply_left] at h
        exact h.symm
      rw [Equiv.swap_apply_def] at h1
      split_ifs at h1 with hyx hye
      · have hx1eq : x.1 = y.1 := hyx
        have hx2eq : x.2 = y.2 := h1.symm
        exact Prod.ext hx1eq hx2eq
      · exfalso
        rcases hx1' with hxa | hxb
        · exact hy2'.1 (hxa.symm.trans hye).symm
        · exact hy2'.2 (hxb.symm.trans hye).symm
      · exfalso
        rcases hx1' with hxa | hxb
        · exact hx2'.1 (hxa.symm.trans h1).symm
        · exact hx2'.2 (hxb.symm.trans h1).symm
    · intro τ hτ
      simp only [frameAP_noncommFinset, Finset.mem_filter] at hτ
      obtain ⟨-, hτswap, hτnc⟩ := hτ
      obtain ⟨c, e, hce, hτeq⟩ := hτswap
      by_cases hc : c ∈ ({a, b} : Finset (Fin d))
      · by_cases he : e ∈ ({a, b} : Finset (Fin d))
        · exfalso
          have hc' : c = a ∨ c = b := by simpa using hc
          have he' : e = a ∨ e = b := by simpa using he
          have hcomm : Equiv.swap c e = Equiv.swap a b := by
            rcases hc' with rfl | rfl <;> rcases he' with rfl | rfl
            · exact absurd rfl hce
            · rfl
            · rw [Equiv.swap_comm]
            · exact absurd rfl hce
          apply hτnc
          simp [hτeq, hcomm]
        · refine ⟨(c, e), ?_, hτeq.symm⟩
          rw [frameAP_pairFinset, Finset.mem_product, Finset.mem_compl]
          exact ⟨hc, he⟩
      · by_cases he : e ∈ ({a, b} : Finset (Fin d))
        · refine ⟨(e, c), ?_, ?_⟩
          · rw [frameAP_pairFinset, Finset.mem_product, Finset.mem_compl]
            exact ⟨he, hc⟩
          · rw [Equiv.swap_comm]
            exact hτeq.symm
        · exfalso
          have hc' : c ≠ a ∧ c ≠ b := by simpa using hc
          have he' : e ≠ a ∧ e ≠ b := by simpa using he
          have hcomm : Equiv.swap a b * Equiv.swap c e =
              Equiv.swap c e * Equiv.swap a b :=
            frameAP_swap_mul_swap_comm_of_ne (Ne.symm hc'.1) (Ne.symm he'.1)
              (Ne.symm hc'.2) (Ne.symm he'.2)
          apply hτnc
          simp [hτeq, hcomm]
  rw [← hcard, frameAP_card_pairFinset hab]

private lemma frameAP_edge_swap_share {d : ℕ} {a b c : Fin d} (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c) :
    frameAP_edge (Equiv.swap a b) (Equiv.swap a c) :=
  ⟨⟨a, b, hab, rfl⟩, ⟨a, c, hac, rfl⟩, frameAP_swap_mul_swap_ne_comm hab hac hbc⟩

private lemma frameAP_root_path {d : ℕ} (hd : 3 ≤ d) {a b : Fin d} (hab : a ≠ b) :
    Relation.ReflTransGen (frameAP_edge (d := d)) (Equiv.swap a b)
      (Equiv.swap ⟨0, by omega⟩ ⟨1, by omega⟩) := by
  let z : Fin d := ⟨0, by omega⟩
  let o : Fin d := ⟨1, by omega⟩
  change Relation.ReflTransGen (frameAP_edge (d := d)) (Equiv.swap a b) (Equiv.swap z o)
  have hzo : z ≠ o := by
    intro h
    exact absurd (congrArg Fin.val h) (by simp [z, o])
  by_cases haz : a = z
  · subst a
    by_cases hbo : b = o
    · subst b
      exact Relation.ReflTransGen.refl
    · refine Relation.ReflTransGen.single ?_
      exact frameAP_edge_swap_share (a := z) (b := b) (c := o) hab hzo hbo
  · by_cases hbz : b = z
    · subst b
      by_cases hao : a = o
      · subst a
        rw [Equiv.swap_comm o z]
      · refine Relation.ReflTransGen.single ?_
        have h := frameAP_edge_swap_share (a := z) (b := a) (c := o) (Ne.symm haz) hzo hao
        simpa [Equiv.swap_comm a z] using h
    · by_cases hao : a = o
      · subst a
        refine Relation.ReflTransGen.single ?_
        have h := frameAP_edge_swap_share (a := o) (b := b) (c := z) hab (Ne.symm hzo) hbz
        simpa [Equiv.swap_comm o z] using h
      · have e1 : frameAP_edge (Equiv.swap a b) (Equiv.swap z a) := by
          have h := frameAP_edge_swap_share (a := a) (b := b) (c := z) hab haz hbz
          simpa [Equiv.swap_comm a z] using h
        have e2 : frameAP_edge (Equiv.swap z a) (Equiv.swap z o) :=
          frameAP_edge_swap_share (a := z) (b := a) (c := o) (Ne.symm haz) hzo hao
        exact (Relation.ReflTransGen.single e1).trans (Relation.ReflTransGen.single e2)

private lemma frameAP_conn_transpositions {d : ℕ} (hd : 3 ≤ d) :
    ∀ σ : Equiv.Perm (Fin d), σ.IsSwap → ∀ τ : Equiv.Perm (Fin d), τ.IsSwap →
      Relation.ReflTransGen (frameAP_edge (d := d)) σ τ := by
  intro σ hσ τ hτ
  obtain ⟨a, b, hab, rfl⟩ := hσ
  obtain ⟨c, e, hce, rfl⟩ := hτ
  have h1 := frameAP_root_path hd hab
  have h2 := frameAP_root_path hd hce
  have hedge_symm : ∀ {x y : Equiv.Perm (Fin d)},
      frameAP_edge (d := d) x y → frameAP_edge y x := by
    rintro x y ⟨hx, hy, hne⟩
    exact ⟨hy, hx, hne.symm⟩
  have hsymm : ∀ {x y : Equiv.Perm (Fin d)},
      Relation.ReflTransGen (frameAP_edge (d := d)) x y →
      Relation.ReflTransGen (frameAP_edge (d := d)) y x := by
    intro x y h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | tail _ hbc ih => exact Relation.ReflTransGen.head (hedge_symm hbc) ih
  exact h1.trans (hsymm h2)

theorem modelNumIs_modelConn_of_perm {X : Type} [Group X] {d : ℕ} (hd : 3 ≤ d)
    (ρ : Equiv.Perm (Fin d) →* MulAut X) (hρ : Function.Injective ρ) {S : Set (MulAut X)}
    (hS : ∀ u, u ∈ modelReflSet S ↔ ∃ a b : Fin d, a ≠ b ∧ u = ρ (Equiv.swap a b)) :
    ModelNumIs S (d * (d - 1) / 2) (some (2 * (d - 2))) ∧ ModelConn S := by
  classical
  have hR : modelReflSet S = ρ '' frameAP_isSwapSet d := by
    ext u
    rw [hS u]
    constructor
    · rintro ⟨a, b, hab, rfl⟩
      exact ⟨Equiv.swap a b, ⟨a, b, hab, rfl⟩, rfl⟩
    · rintro ⟨σ, ⟨a, b, hab, hσ⟩, rfl⟩
      exact ⟨a, b, hab, by rw [hσ]⟩
  have hTcard : (frameAP_isSwapSet d).ncard = d * (d - 1) / 2 := by
    rw [← Set.fintypeCard_eq_ncard]
    have hcard : Fintype.card (frameAP_isSwapSet d) = (frameAP_transpositions d).card := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (by
        intro σ
        simp [frameAP_isSwapSet, frameAP_transpositions]))
    rw [hcard, frameAP_card_transpositions, Nat.choose_two_right]
  have hnoncomm : ∀ a b : Fin d, a ≠ b →
      ({τ : Equiv.Perm (Fin d) | τ.IsSwap ∧
        Equiv.swap a b * τ ≠ τ * Equiv.swap a b} : Set (Equiv.Perm (Fin d))).ncard =
        2 * (d - 2) := by
    intro a b hab
    rw [← Set.fintypeCard_eq_ncard]
    have hcard : Fintype.card ({τ : Equiv.Perm (Fin d) | τ.IsSwap ∧
        Equiv.swap a b * τ ≠ τ * Equiv.swap a b} : Set (Equiv.Perm (Fin d))) =
        (frameAP_noncommFinset a b).card := by
      rw [← Fintype.card_coe]
      exact Fintype.card_congr (Equiv.subtypeEquivRight (by
        intro τ
        simp [frameAP_noncommFinset]))
    rw [hcard, frameAP_card_noncomm hab]
  constructor
  · constructor
    · rw [hR, Set.ncard_image_of_injective _ hρ]
      exact hTcard
    · intro u hu
      rw [hR] at hu
      obtain ⟨σ, hσ, rfl⟩ := hu
      obtain ⟨a, b, hab, rfl⟩ := hσ
      rw [modelNonComm]
      have hset : {v : MulAut X | v ∈ modelReflSet S ∧
          ρ (Equiv.swap a b) * v ≠ v * ρ (Equiv.swap a b)} =
          ρ '' {τ : Equiv.Perm (Fin d) | τ.IsSwap ∧
            Equiv.swap a b * τ ≠ τ * Equiv.swap a b} := by
        ext v
        rw [hR]
        constructor
        · rintro ⟨⟨τ, hτ, rfl⟩, hnc⟩
          refine ⟨τ, ⟨hτ, ?_⟩, rfl⟩
          intro h
          apply hnc
          calc ρ (Equiv.swap a b) * ρ τ = ρ (Equiv.swap a b * τ) :=
                (map_mul ρ _ _).symm
            _ = ρ (τ * Equiv.swap a b) := by rw [h]
            _ = ρ τ * ρ (Equiv.swap a b) := map_mul ρ _ _
        · rintro ⟨τ, ⟨hτ, hnc⟩, rfl⟩
          refine ⟨⟨τ, hτ, rfl⟩, ?_⟩
          intro h
          apply hnc
          apply hρ
          calc ρ (Equiv.swap a b * τ) = ρ (Equiv.swap a b) * ρ τ := map_mul ρ _ _
            _ = ρ τ * ρ (Equiv.swap a b) := h
            _ = ρ (τ * Equiv.swap a b) := (map_mul ρ _ _).symm
      rw [hset, Set.ncard_image_of_injective _ hρ]
      exact hnoncomm a b hab
  · intro u hu v hv
    rw [hR] at hu hv
    obtain ⟨σ, hσ, rfl⟩ := hu
    obtain ⟨τ, hτ, rfl⟩ := hv
    let P : MulAut X → MulAut X → Prop :=
      fun u v => u ∈ modelReflSet S ∧ v ∈ modelReflSet S ∧ u * v ≠ v * u
    have hP : ∀ {x y : Equiv.Perm (Fin d)}, frameAP_edge (d := d) x y →
        P (ρ x) (ρ y) := by
      intro x y hxy
      refine ⟨?_, ?_, ?_⟩
      · rw [hR]
        exact ⟨x, hxy.1, rfl⟩
      · rw [hR]
        exact ⟨y, hxy.2.1, rfl⟩
      · intro h
        apply hxy.2.2
        apply hρ
        simpa [map_mul] using h
    have hpath : Relation.ReflTransGen (frameAP_edge (d := d)) σ τ :=
      frameAP_conn_transpositions hd σ hσ τ hτ
    have hlift : Relation.ReflTransGen P (ρ σ) (ρ τ) := by
      refine Relation.ReflTransGen.trans_induction_on
        (motive := fun {a b} (_ : Relation.ReflTransGen (frameAP_edge (d := d)) a b) =>
          Relation.ReflTransGen P (ρ a) (ρ b)) hpath ?_ ?_ ?_
      · intro a
        exact Relation.ReflTransGen.refl
      · intro a b hab
        exact Relation.ReflTransGen.single (hP hab)
      · intro a b c hab hbc ih_ab ih_bc
        exact ih_ab.trans ih_bc
    exact hlift

end CFSG.StandardType.FrameRoute

end
