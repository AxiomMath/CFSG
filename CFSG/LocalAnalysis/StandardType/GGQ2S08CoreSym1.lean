module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreSymType
public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreDefs
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Data.Fintype.Card

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ggQ2s08k7_swap_path {m ℓ : ℕ} (a : Fin (ℓ + 1) → Fin m)
    (H : Subgroup (Equiv.Perm (Fin m)))
    (hτ : ∀ i : Fin ℓ, Equiv.swap (a i.castSucc) (a i.succ) ∈ H) :
    ∀ i j : Fin (ℓ + 1), Equiv.swap (a i) (a j) ∈ H := by
  have hle : ∀ j : Fin (ℓ + 1), ∀ i : Fin (ℓ + 1), i ≤ j → Equiv.swap (a i) (a j) ∈ H := by
    intro j
    induction j using Fin.induction with
    | zero =>
        intro i hi
        have hi0 : i = 0 := Fin.eq_of_val_eq (Nat.eq_zero_of_le_zero (by simpa using hi))
        subst hi0
        rw [Equiv.swap_self]; exact H.one_mem
    | succ j ih =>
        intro i hi
        rcases lt_or_eq_of_le hi with hlt | heq
        · have hi' : i ≤ j.castSucc := Fin.le_castSucc_iff.mpr hlt
          exact SubmonoidClass.swap_mem_trans H (ih i hi') (hτ j)
        · subst heq
          rw [Equiv.swap_self]; exact H.one_mem
  intro i j
  rcases le_total i j with h | h
  · exact hle j i h
  · have := hle i j h
    simpa [Equiv.swap_comm] using this

private lemma ggQ2s08k7_ofSubtype_swap {α : Type} [DecidableEq α] (p : α → Prop) [DecidablePred p]
    (x y : Subtype p) :
    Equiv.Perm.ofSubtype (p := p) (Equiv.swap x y) = Equiv.swap (x : α) (y : α) := by
  ext z
  by_cases hz : p z
  · change (Equiv.Perm.ofSubtype (p := p) (Equiv.swap x y)) (↑(⟨z, hz⟩ : Subtype p)) =
      (Equiv.swap (x : α) (y : α)) (↑(⟨z, hz⟩ : Subtype p))
    rw [Equiv.Perm.ofSubtype_apply_coe]
    rcases eq_or_ne (⟨z, hz⟩ : Subtype p) x with hx | hx
    · rw [hx, Equiv.swap_apply_left, Equiv.swap_apply_left]
    · rcases eq_or_ne (⟨z, hz⟩ : Subtype p) y with hy | hy
      · rw [hy, Equiv.swap_apply_right, Equiv.swap_apply_right]
      · have hzx : z ≠ x := fun h => hx (Subtype.ext h)
        have hzy : z ≠ y := fun h => hy (Subtype.ext h)
        rw [Equiv.swap_apply_of_ne_of_ne hx hy, Equiv.swap_apply_of_ne_of_ne hzx hzy]
  · rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hz]
    rw [Equiv.swap_apply_of_ne_of_ne]
    · intro h; exact hz (by rw [h]; exact x.2)
    · intro h; exact hz (by rw [h]; exact y.2)

private lemma ggQ2s08k7_fixing_mem_closure {α : Type} [DecidableEq α] [Fintype α]
    {S : Set α} {H : Subgroup (Equiv.Perm α)}
    (hS : ∀ x y : α, x ∈ S → y ∈ S → x ≠ y → Equiv.swap x y ∈ H) :
    ∀ g : Equiv.Perm α, (∀ y : α, y ∉ S → g y = y) → g ∈ H := by
  classical
  intro g hg
  let p : α → Prop := fun x => x ∈ S
  let φ : Equiv.Perm (Subtype p) →* Equiv.Perm α := Equiv.Perm.ofSubtype
  have hφ : ∀ σ : Equiv.Perm (Subtype p), σ.IsSwap → φ σ ∈ H := by
    rintro σ ⟨x, y, hxy, rfl⟩
    rw [show φ (Equiv.swap x y) = Equiv.swap (x : α) (y : α) from
      ggQ2s08k7_ofSubtype_swap p x y]
    exact hS x y x.2 y.2 (fun h => hxy (Subtype.ext h))
  have hrange : φ.range ≤ H := by
    rw [← Subgroup.map_top φ, ← Equiv.Perm.closure_isSwap, MonoidHom.map_closure]
    exact (Subgroup.closure_le H).mpr (by rintro _ ⟨σ, hσ, rfl⟩; exact hφ σ hσ)
  have hperm : ∀ x : α, p (g x) ↔ p x := by
    intro x
    constructor
    · intro hx
      by_contra hxS
      have : g x = x := hg x hxS
      exact hxS (by simpa [p, this] using hx)
    · intro hx
      by_contra hgx
      have h1 : g (g x) = g x := hg (g x) hgx
      have h2 : g x = x := g.injective (by simpa using h1)
      exact hgx (by simpa [p, h2] using hx)
  obtain ⟨gS, hgS⟩ : ∃ gS : Equiv.Perm (Subtype p), φ gS = g := by
    refine ⟨g.subtypePerm hperm, ?_⟩
    ext z
    by_cases hz : p z
    · change (Equiv.Perm.ofSubtype (p := p) (g.subtypePerm hperm)) (↑(⟨z, hz⟩ : Subtype p)) =
        g (↑(⟨z, hz⟩ : Subtype p))
      rw [Equiv.Perm.ofSubtype_apply_coe, Equiv.Perm.subtypePerm_apply]
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hz, hg z hz]
  rw [← hgS]
  exact hrange (MonoidHom.mem_range.mpr ⟨gS, rfl⟩)

theorem ggQ2s08core_sym1 {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {ℓ : ℕ} (hℓ : 9 ≤ ℓ)
    (R W : Subgroup (V ≃ₗ[ZMod 3] V)) (hWR : W ≤ R) (e : R ≃* Equiv.Perm (Fin (ℓ + 2)))
    (he : ∀ r : R, GGLinRefl (r : V ≃ₗ[ZMod 3] V) → ∃ i j, i ≠ j ∧ e r = Equiv.swap i j)
    (s : Fin ℓ → (V ≃ₗ[ZMod 3] V)) (M : CoxeterMatrix (Fin ℓ))
    (hM : M = CoxeterMatrix.A ℓ ∨ M = CoxeterMatrix.B ℓ ∨ M = ggCoxeterMatrixD ℓ)
    (hsR : ∀ i, s i ∈ R) (hsrefl : ∀ i, GGLinRefl (s i))
    (hrel : ∀ i j, i ≠ j → (s i * s j) ^ M i j = 1) (hdist : ∀ i j, i ≠ j → s i ≠ s j)
    (hncomm : ∀ i j, i ≠ j → M i j ≠ 2 → s i * s j ≠ s j * s i)
    (hWs : W = Subgroup.closure (Set.range s))
    (r : V ≃ₗ[ZMod 3] V) (hrR : r ∈ R) (hr : GGLinRefl r) (hrW : r ∉ W) :
    Subgroup.closure ((W : Set (V ≃ₗ[ZMod 3] V)) ∪ {r}) = R := by
  classical
  let s' : Fin ℓ → R := fun i => ⟨s i, hsR i⟩
  let r' : R := ⟨r, hrR⟩
  let τ : Fin ℓ → Equiv.Perm (Fin (ℓ + 2)) := fun i => e (s' i)
  have hsw : ∀ i : Fin ℓ, (τ i).IsSwap := by
    intro i
    exact he (s' i) (hsrefl i)
  have hne : ∀ i j : Fin ℓ, i ≠ j → τ i ≠ τ j := by
    intro i j hij h
    apply hdist i j hij
    have h1 : s' i = s' j := e.injective (by simpa [τ] using h)
    simpa [s'] using congrArg (fun x : R => (x : V ≃ₗ[ZMod 3] V)) h1
  have hrelτ : ∀ i j : Fin ℓ, i ≠ j → (τ i * τ j) ^ M i j = 1 := by
    intro i j hij
    have h1 : ((s' i * s' j) ^ M i j : R) = 1 := by
      apply Subtype.ext
      simp [s', hrel i j hij]
    have h2 : e ((s' i * s' j) ^ M i j) = 1 := by rw [h1, map_one]
    have h3 : (τ i * τ j) ^ M i j = e ((s' i * s' j) ^ M i j) := by
      simp [τ, map_mul, map_pow]
    rw [h3, h2]
  have hncommτ : ∀ i j : Fin ℓ, i ≠ j → M i j ≠ 2 → τ i * τ j ≠ τ j * τ i := by
    intro i j hij hM2 h
    have h1 : s' i * s' j = s' j * s' i := by
      apply e.injective
      rw [map_mul, map_mul]
      simpa [τ] using h
    have h2 : s i * s j = s j * s i := by
      have hcoe := congrArg (fun x : R => (x : V ≃ₗ[ZMod 3] V)) h1
      simpa [s'] using hcoe
    exact hncomm i j hij hM2 h2
  obtain ⟨_, a, ha_inj, haτ⟩ :=
    ggQ2s08core_swap_coxeter hℓ τ hsw hne M hM hrelτ hncommτ
  let S : Set (Fin (ℓ + 2)) := Set.range a
  let H : Subgroup (Equiv.Perm (Fin (ℓ + 2))) := Subgroup.closure (Set.range τ)
  have hτH : ∀ i : Fin ℓ, Equiv.swap (a i.castSucc) (a i.succ) ∈ H := by
    intro i
    have h : τ i ∈ H := Subgroup.subset_closure ⟨i, rfl⟩
    rwa [haτ i] at h
  have hswap_path : ∀ i j : Fin (ℓ + 1), Equiv.swap (a i) (a j) ∈ H :=
    ggQ2s08k7_swap_path a H hτH
  have hS_swaps : ∀ x y : Fin (ℓ + 2), x ∈ S → y ∈ S → x ≠ y → Equiv.swap x y ∈ H := by
    intro x y hx hy _
    have hx' : x ∈ Set.range a := hx
    have hy' : y ∈ Set.range a := hy
    rw [Set.mem_range] at hx' hy'
    rcases hx' with ⟨i, rfl⟩
    rcases hy' with ⟨j, rfl⟩
    exact hswap_path i j
  have hfix : ∀ g : Equiv.Perm (Fin (ℓ + 2)), (∀ y : Fin (ℓ + 2), y ∉ S → g y = y) → g ∈ H :=
    ggQ2s08k7_fixing_mem_closure hS_swaps
  let W' : Subgroup R := W.subgroupOf R
  have hW' : W' = Subgroup.closure (Set.range s') := by
    refine Subgroup.map_injective (f := R.subtype) Subtype.coe_injective ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWR, hWs, MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨s' i, ⟨i, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨i, rfl⟩, hxy⟩
      exact ⟨i, hxy⟩
  have hHmap : Subgroup.map e.toMonoidHom W' = H := by
    rw [hW', MonoidHom.map_closure]
    congr 1
    ext y
    constructor
    · rintro ⟨x, ⟨i, rfl⟩, hxy⟩
      exact ⟨i, hxy⟩
    · rintro ⟨i, rfl⟩
      exact ⟨s' i, ⟨i, rfl⟩, rfl⟩
  have hr'W : r' ∉ W' := by
    intro h
    have hW : (r : V ≃ₗ[ZMod 3] V) ∈ W := by
      simpa [r'] using (Subgroup.mem_subgroupOf).mp h
    exact hrW hW
  have herH : e r' ∉ H := by
    intro h
    have h' : e r' ∈ Subgroup.map e.toMonoidHom W' := by
      rw [hHmap]; exact h
    rcases (Subgroup.mem_map).mp h' with ⟨x, hxW, hxe⟩
    have hxr : x = r' := e.injective hxe
    exact hr'W (hxr ▸ hxW)
  obtain ⟨c, d, hcd, her⟩ := he r' hr
  have hc_or_hd : c ∉ S ∨ d ∉ S := by
    by_contra h
    push Not at h
    have hcS : c ∈ S := h.1
    have hdS : d ∈ S := h.2
    have hfixer : e r' ∈ H := by
      apply hfix
      intro y hy
      rw [her]
      exact Equiv.swap_apply_of_ne_of_ne
        (by intro hcy; exact hy (by rw [hcy]; exact hcS))
        (by intro hdy; exact hy (by rw [hdy]; exact hdS))
    exact herH hfixer
  have hcardS : Fintype.card S = ℓ + 1 := by
    let ab : Fin (ℓ + 1) ↪ Fin (ℓ + 2) := ⟨a, ha_inj⟩
    have h := Fintype.card_range ab
    simpa [S, ab, Fintype.card_fin] using h
  have hcard_compl : Fintype.card {x : Fin (ℓ + 2) // x ∉ S} = 1 := by
    have h := Fintype.card_subtype_compl (α := Fin (ℓ + 2)) (fun x => x ∈ S)
    have hS' : Fintype.card {x : Fin (ℓ + 2) // x ∈ S} = ℓ + 1 := hcardS
    rw [h, Fintype.card_fin, hS']
    omega
  haveI : Subsingleton {x : Fin (ℓ + 2) // x ∉ S} :=
    ⟨fun a b => by
      have h : Fintype.card {x : Fin (ℓ + 2) // x ∉ S} ≤ 1 := by omega
      exact Fintype.card_le_one_iff.mp h a b⟩
  have hne_compl : Nonempty {x : Fin (ℓ + 2) // x ∉ S} := by
    rw [← Fintype.card_pos_iff]
    omega
  obtain ⟨⟨p, hpS⟩⟩ := hne_compl
  have hp_unique : ∀ y : Fin (ℓ + 2), y ∉ S → y = p := by
    intro y hy
    have h : (⟨y, hy⟩ : {x // x ∉ S}) = ⟨p, hpS⟩ := Subsingleton.elim _ _
    exact congrArg Subtype.val h
  obtain ⟨c', hc'S, her_p⟩ : ∃ c' : Fin (ℓ + 2), c' ∈ S ∧ e r' = Equiv.swap c' p := by
    rcases hc_or_hd with hc | hd
    · have hcp : c = p := hp_unique c hc
      refine ⟨d, ?_, ?_⟩
      · by_contra hdS
        have hdp : d = p := hp_unique d hdS
        exact hcd (by rw [hcp, hdp])
      · rw [her, Equiv.swap_comm, hcp]
    · have hdp : d = p := hp_unique d hd
      refine ⟨c, ?_, ?_⟩
      · by_contra hcS
        have hcp : c = p := hp_unique c hcS
        exact hcd (by rw [hcp, hdp])
      · rw [her, hdp]
  let K : Subgroup (Equiv.Perm (Fin (ℓ + 2))) := Subgroup.closure ((H : Set _) ∪ {e r'})
  have hswapK : ∀ x y : Fin (ℓ + 2), x ≠ y → Equiv.swap x y ∈ K := by
    intro x y hxy
    by_cases hxS : x ∈ S
    · by_cases hyS : y ∈ S
      · exact Subgroup.subset_closure (Or.inl (hS_swaps x y hxS hyS hxy))
      · have hyp : y = p := hp_unique y hyS
        have hxc' : Equiv.swap x c' ∈ K := by
          by_cases hxc : x = c'
          · rw [hxc, Equiv.swap_self]; exact K.one_mem
          · exact Subgroup.subset_closure (Or.inl (hS_swaps x c' hxS hc'S hxc))
        have hc'p : Equiv.swap c' p ∈ K := by
          rw [← her_p]; exact Subgroup.subset_closure (Or.inr rfl)
        have hxp : Equiv.swap x p ∈ K := SubmonoidClass.swap_mem_trans K hxc' hc'p
        rw [hyp]; exact hxp
    · by_cases hyS : y ∈ S
      · have hxp : x = p := hp_unique x hxS
        have hyc' : Equiv.swap y c' ∈ K := by
          by_cases hyc : y = c'
          · rw [hyc, Equiv.swap_self]; exact K.one_mem
          · exact Subgroup.subset_closure (Or.inl (hS_swaps y c' hyS hc'S hyc))
        have hc'p : Equiv.swap c' p ∈ K := by
          rw [← her_p]; exact Subgroup.subset_closure (Or.inr rfl)
        have hyp : Equiv.swap y p ∈ K := SubmonoidClass.swap_mem_trans K hyc' hc'p
        rw [hxp, Equiv.swap_comm]; exact hyp
      · exfalso
        exact hxy (by rw [hp_unique x hxS, hp_unique y hyS])
  have htopK : K = ⊤ := by
    have hall : {σ : Equiv.Perm (Fin (ℓ + 2)) | σ.IsSwap} ⊆ K := by
      intro σ hσ
      rcases hσ with ⟨x, y, hxy, rfl⟩
      exact hswapK x y hxy
    have hle : ⊤ ≤ K := by
      rw [← Equiv.Perm.closure_isSwap]
      exact (Subgroup.closure_le K).mpr hall
    exact top_le_iff.mp hle
  let M : Subgroup (V ≃ₗ[ZMod 3] V) := Subgroup.closure ((W : Set (V ≃ₗ[ZMod 3] V)) ∪ {r})
  have hMR : M ≤ R := by
    dsimp only [M]
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with hx | hx
    · exact hWR hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hrR
  have hM' : M.subgroupOf R = Subgroup.closure ((W' : Set R) ∪ {r'}) := by
    refine Subgroup.map_injective (f := R.subtype) Subtype.coe_injective ?_
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hMR, MonoidHom.map_closure]
    have hset : R.subtype '' ((W' : Set R) ∪ {r'}) =
        (W : Set (V ≃ₗ[ZMod 3] V)) ∪ {r} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases hx with hx | hx
        · left
          exact (Subgroup.mem_subgroupOf).mp hx
        · right
          rw [Set.mem_singleton_iff] at hx
          rw [hx]
          rfl
      · intro hy
        rcases hy with hy | hy
        · refine ⟨⟨y, hWR hy⟩, Or.inl ?_, rfl⟩
          change (⟨y, hWR hy⟩ : R) ∈ W.subgroupOf R
          rw [Subgroup.mem_subgroupOf]
          exact hy
        · rw [Set.mem_singleton_iff] at hy
          refine ⟨r', Or.inr rfl, ?_⟩
          rw [hy]
          rfl
    rw [hset]
  have hmapM : Subgroup.map e.toMonoidHom (M.subgroupOf R) = K := by
    rw [hM', MonoidHom.map_closure]
    have himage : e.toMonoidHom '' ((W' : Set R) ∪ {r'}) =
        (H : Set (Equiv.Perm (Fin (ℓ + 2)))) ∪ {e r'} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        rcases hx with hx | hx
        · left
          have hxH : e x ∈ Subgroup.map e.toMonoidHom W' := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
          rwa [hHmap] at hxH
        · right
          rw [Set.mem_singleton_iff] at hx
          rw [hx]
          exact Set.mem_singleton _
      · intro hy
        rcases hy with hy | hy
        · rw [← hHmap] at hy
          rcases (Subgroup.mem_map).mp hy with ⟨x, hxW, hxe⟩
          exact ⟨x, Or.inl hxW, hxe⟩
        · rw [Set.mem_singleton_iff] at hy
          exact ⟨r', Or.inr rfl, by rw [hy]; rfl⟩
    rw [himage]
  have hmap_top : Subgroup.map e.toMonoidHom (M.subgroupOf R) = Subgroup.map e.toMonoidHom ⊤ := by
    rw [hmapM, htopK, Subgroup.map_top, MonoidHom.range_eq_top.mpr e.surjective]
  have hMtop : M.subgroupOf R = ⊤ := Subgroup.map_injective e.injective hmap_top
  have hRM : R ≤ M := (Subgroup.subgroupOf_eq_top).mp hMtop
  change M = R
  exact le_antisymm hMR hRM

end CFSG.StandardType

end
