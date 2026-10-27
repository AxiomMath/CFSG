module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Module.Submodule.Equiv

public section

namespace CFSG.Quasithin.HM22

variable (K : Type*) [Field K]

@[expose] def flagSub (N n : ℕ) : Submodule K (Fin N → K) where
  carrier := {v | ∀ k : Fin N, n ≤ k.val → v k = 0}
  add_mem' := by
    intro u v hu hv k hk
    simp [hu k hk, hv k hk]
  zero_mem' := by intro k _; rfl
  smul_mem' := by
    intro c v hv k hk
    simp [hv k hk]

variable {K}

theorem mem_flagSub {N n : ℕ} {v : Fin N → K} :
    v ∈ flagSub K N n ↔ ∀ k : Fin N, n ≤ k.val → v k = 0 := Iff.rfl

theorem flagSub_zero (N : ℕ) : flagSub K N 0 = ⊥ := by
  rw [eq_bot_iff]
  intro v hv
  rw [Submodule.mem_bot]
  funext k
  exact hv k (Nat.zero_le _)

theorem flagSub_self (N : ℕ) : flagSub K N N = ⊤ := by
  rw [eq_top_iff]
  intro v _ k hk
  exact absurd k.isLt (by omega)

variable (K) in
@[expose] def resW (N n0 d : ℕ) : (Fin N → K) →ₗ[K] (Fin d → K) where
  toFun v := fun k => if h : n0 + k.val < N then v ⟨n0 + k.val, h⟩ else 0
  map_add' u v := by funext k; by_cases h : n0 + k.val < N <;> simp [h]
  map_smul' c v := by funext k; by_cases h : n0 + k.val < N <;> simp [h]

variable (K) in
@[expose] def embW (N n0 d : ℕ) : (Fin d → K) →ₗ[K] (Fin N → K) where
  toFun s := fun j => if h : n0 ≤ j.val ∧ j.val - n0 < d then s ⟨j.val - n0, h.2⟩ else 0
  map_add' u v := by funext j; by_cases h : n0 ≤ j.val ∧ j.val - n0 < d <;> simp [h]
  map_smul' c v := by funext j; by_cases h : n0 ≤ j.val ∧ j.val - n0 < d <;> simp [h]

theorem resW_apply {N n0 d : ℕ} (v : Fin N → K) (k : Fin d) :
    resW K N n0 d v k = if h : n0 + k.val < N then v ⟨n0 + k.val, h⟩ else 0 := rfl

theorem embW_apply {N n0 d : ℕ} (s : Fin d → K) (j : Fin N) :
    embW K N n0 d s j = if h : n0 ≤ j.val ∧ j.val - n0 < d then s ⟨j.val - n0, h.2⟩ else 0 :=
  rfl

theorem resW_embW {N n0 d : ℕ} (h : n0 + d ≤ N) (s : Fin d → K) :
    resW K N n0 d (embW K N n0 d s) = s := by
  funext k
  have h1 : n0 + k.val < N := by omega
  have h2 : n0 ≤ n0 + k.val ∧ n0 + k.val - n0 < d := ⟨by omega, by omega⟩
  rw [resW_apply, dite_eq_left h1, embW_apply, dite_eq_left h2]
  exact congrArg s (Fin.ext (by simp))

theorem embW_mem {N n0 d : ℕ} (s : Fin d → K) : embW K N n0 d s ∈ flagSub K N (n0 + d) := by
  intro k hk
  have h2 : ¬ (n0 ≤ k.val ∧ k.val - n0 < d) := by omega
  rw [embW_apply, dite_eq_right h2]

theorem resW_low {N n0 d : ℕ} {w : Fin N → K} (hw : w ∈ flagSub K N n0) :
    resW K N n0 d w = 0 := by
  funext k
  rw [resW_apply]
  split_ifs with h
  · exact hw _ (by simp)
  · rfl

theorem sub_embW_resW_mem {N n0 d : ℕ} (h : n0 + d ≤ N) {v : Fin N → K}
    (hv : v ∈ flagSub K N (n0 + d)) :
    v - embW K N n0 d (resW K N n0 d v) ∈ flagSub K N n0 := by
  intro k hk
  rw [Pi.sub_apply, embW_apply]
  by_cases h2 : n0 ≤ k.val ∧ k.val - n0 < d
  · have h3 : n0 + (k.val - n0) < N := by omega
    have h4 : (⟨n0 + (k.val - n0), h3⟩ : Fin N) = k := Fin.ext (by simp; omega)
    rw [dite_eq_left h2, resW_apply, dite_eq_left h3, h4, sub_self]
  · rw [dite_eq_right h2, sub_zero]
    exact hv k (by omega)

theorem mem_flagSub_of_resW_eq_zero {N n0 d : ℕ} (h : n0 + d ≤ N) {v : Fin N → K}
    (hv : v ∈ flagSub K N (n0 + d)) (h0 : resW K N n0 d v = 0) : v ∈ flagSub K N n0 := by
  have := sub_embW_resW_mem h hv
  rwa [h0, map_zero, sub_zero] at this

variable (K) in
@[expose] def blockW (N n0 d : ℕ) (X : (Fin N → K) →ₗ[K] (Fin N → K)) :
    (Fin d → K) →ₗ[K] (Fin d → K) :=
  (resW K N n0 d).comp (X.comp (embW K N n0 d))

theorem blockW_rel {N n0 d : ℕ} (h : n0 + d ≤ N) {X : (Fin N → K) →ₗ[K] (Fin N → K)}
    (hX : ∀ v ∈ flagSub K N n0, X v ∈ flagSub K N n0) {v : Fin N → K}
    (hv : v ∈ flagSub K N (n0 + d)) :
    resW K N n0 d (X v) = blockW K N n0 d X (resW K N n0 d v) := by
  have hlow := sub_embW_resW_mem h hv
  have e : v = (v - embW K N n0 d (resW K N n0 d v)) + embW K N n0 d (resW K N n0 d v) :=
    (sub_add_cancel v _).symm
  conv_lhs => rw [e]
  rw [map_add, map_add, resW_low (hX _ hlow), zero_add]
  rfl

section Fam

variable {ι M : Type*} [AddCommGroup M] [Module K M]

@[expose] def IsInvFam (g : ι → (M →ₗ[K] M)) (U : Submodule K M) : Prop :=
  ∀ i, ∀ u ∈ U, g i u ∈ U

@[expose] def IrredFam (g : ι → (M →ₗ[K] M)) : Prop :=
  ∀ U : Submodule K M, IsInvFam g U → U = ⊥ ∨ U = ⊤

end Fam

theorem ns_mono' {ns : ℕ → ℕ} {m : ℕ} (hmono : ∀ i < m, ns i < ns (i + 1)) :
    ∀ i j, i ≤ j → j ≤ m → ns i ≤ ns j := by
  intro i j hij
  induction j, hij using Nat.le_induction with
  | base => intro _; exact le_rfl
  | succ j hij ih =>
    intro hj
    exact le_trans (ih (by omega)) (hmono j (by omega)).le

theorem jordanHolder_step {ι : Type*} {N : ℕ} (ns : ℕ → ℕ) (m : ℕ) (hns0 : ns 0 = 0)
    (hnsN : ns m = N) (hmono : ∀ i < m, ns i < ns (i + 1))
    (g : ι → ((Fin N → K) →ₗ[K] (Fin N → K)))
    (hinv : ∀ j ≤ m, ∀ i, ∀ v ∈ flagSub K N (ns j), g i v ∈ flagSub K N (ns j))
    (hirr : ∀ j < m, IrredFam (fun i => blockW K N (ns j) (ns (j + 1) - ns j) (g i)))
    {W : Type*} [AddCommGroup W] [Module K W] (gW : ι → (W →ₗ[K] W)) (hW : IrredFam gW)
    (hWne : (⊤ : Submodule K W) ≠ ⊥) (φ : (Fin N → K) →ₗ[K] W) (hφ : Function.Surjective φ)
    (hφeq : ∀ i v, φ (g i v) = gW i (φ v)) :
    ∃ j < m, ∃ Ψ : (Fin (ns (j + 1) - ns j) → K) ≃ₗ[K] W,
      ∀ i s, Ψ (blockW K N (ns j) (ns (j + 1) - ns j) (g i) s) = gW i (Ψ s) := by
  classical
  let P : ℕ → Prop := fun j => Submodule.map φ (flagSub K N (ns j)) ≠ ⊥
  have hPN : P m := by
    show Submodule.map φ (flagSub K N (ns m)) ≠ ⊥
    rw [hnsN, flagSub_self, Submodule.map_top, LinearMap.range_eq_top.mpr hφ]
    exact hWne
  have hP0 : ¬ P 0 := by
    show ¬ (Submodule.map φ (flagSub K N (ns 0)) ≠ ⊥)
    rw [hns0, flagSub_zero, Submodule.map_bot]
    simp
  have hex : ∃ j, P j := ⟨m, hPN⟩
  have hj₀ : P (Nat.find hex) := Nat.find_spec hex
  have hj₀pos : Nat.find hex ≠ 0 := fun h => hP0 (h ▸ hj₀)
  obtain ⟨j, hj⟩ : ∃ j, Nat.find hex = j + 1 := ⟨Nat.find hex - 1, by omega⟩
  have hnP : ¬ P j := Nat.find_min hex (by omega)
  have hle : j + 1 ≤ m := hj ▸ Nat.find_min' hex hPN
  rw [hj] at hj₀
  have hn0lt : ns j < ns (j + 1) := hmono j (by omega)
  have hn1N : ns (j + 1) ≤ N := hnsN ▸ ns_mono' hmono (j + 1) m hle le_rfl
  refine ⟨j, by omega, ?_⟩
  have hirr' := hirr j (by omega)
  have hinv0 := hinv j (by omega)
  have hinv1 := hinv (j + 1) hle
  have hnP' : Submodule.map φ (flagSub K N (ns j)) = ⊥ := not_not.mp hnP
  have hj₀' : Submodule.map φ (flagSub K N (ns (j + 1))) ≠ ⊥ := hj₀
  clear hirr hinv hnP hj₀ hmono hex hj₀pos hj hle hPN hP0
  generalize ns j = n0 at hirr' hinv0 hnP' hn0lt ⊢
  generalize ns (j + 1) = n1 at hirr' hinv1 hj₀' hn1N hn0lt ⊢
  obtain ⟨d, rfl⟩ : ∃ d, n1 = n0 + d := ⟨n1 - n0, by omega⟩
  have hd : n0 + d - n0 = d := by omega
  rw [hd] at hirr' ⊢
  have hwin : n0 + d ≤ N := hn1N
  have hφlow : ∀ v ∈ flagSub K N n0, φ v = 0 := by
    intro v hv
    have : φ v ∈ Submodule.map φ (flagSub K N n0) := ⟨v, hv, rfl⟩
    rw [hnP'] at this
    exact this
  let Kr : Submodule K (Fin N → K) := LinearMap.ker φ ⊓ flagSub K N (n0 + d)
  let R : Submodule K (Fin d → K) := Kr.map (resW K N n0 d)
  have hRinv : IsInvFam (fun i => blockW K N n0 d (g i)) R := by
    intro i s hs
    obtain ⟨v, ⟨hvker, hvFl⟩, rfl⟩ := hs
    refine ⟨g i v, ⟨?_, hinv1 i v hvFl⟩, ?_⟩
    · show φ (g i v) = 0
      rw [hφeq, LinearMap.mem_ker.mp hvker, map_zero]
    · exact blockW_rel hwin (hinv0 i) hvFl
  have hKlow : R = ⊤ → False := by
    intro hR
    apply hj₀'
    rw [eq_bot_iff]
    rintro w ⟨u, hu, rfl⟩
    rw [Submodule.mem_bot]
    have hres : resW K N n0 d u ∈ R := by rw [hR]; trivial
    obtain ⟨v, ⟨hvker, hvFl⟩, hvres⟩ := hres
    have hdiff : u - v ∈ flagSub K N (n0 + d) := Submodule.sub_mem _ hu hvFl
    have hres0 : resW K N n0 d (u - v) = 0 := by
      rw [map_sub, hvres]; exact sub_self _
    have hlow : u - v ∈ flagSub K N n0 := mem_flagSub_of_resW_eq_zero hwin hdiff hres0
    have h1 := hφlow _ hlow
    have h2 : φ v = 0 := LinearMap.mem_ker.mp hvker
    rw [map_sub, h2, sub_zero] at h1
    exact h1
  have hR : R = ⊥ := (hirr' R hRinv).resolve_right hKlow
  have hKle : ∀ v ∈ Kr, v ∈ flagSub K N n0 := by
    intro v hv
    have : resW K N n0 d v ∈ R := ⟨v, hv, rfl⟩
    rw [hR, Submodule.mem_bot] at this
    exact mem_flagSub_of_resW_eq_zero hwin hv.2 this
  let Ψ : (Fin d → K) →ₗ[K] W := φ.comp (embW K N n0 d)
  have hinj : Function.Injective Ψ := by
    refine (injective_iff_map_eq_zero Ψ).mpr fun s hs => ?_
    have hs' : φ (embW K N n0 d s) = 0 := hs
    have hmem : embW K N n0 d s ∈ Kr := ⟨hs', embW_mem s⟩
    have := resW_low (d := d) (hKle _ hmem)
    rw [resW_embW hwin] at this
    exact this
  have himg_inv : IsInvFam gW (Submodule.map φ (flagSub K N (n0 + d))) := by
    intro i w hw
    obtain ⟨v, hv, rfl⟩ := hw
    exact ⟨g i v, hinv1 i v hv, hφeq i v⟩
  have himg_top : Submodule.map φ (flagSub K N (n0 + d)) = ⊤ :=
    (hW _ himg_inv).resolve_left hj₀'
  have hsurj : Function.Surjective Ψ := by
    intro w
    have : w ∈ Submodule.map φ (flagSub K N (n0 + d)) := by rw [himg_top]; trivial
    obtain ⟨v, hv, rfl⟩ := this
    refine ⟨resW K N n0 d v, ?_⟩
    have h1 := hφlow _ (sub_embW_resW_mem hwin hv)
    rw [map_sub, sub_eq_zero] at h1
    exact h1.symm
  refine ⟨LinearEquiv.ofBijective Ψ ⟨hinj, hsurj⟩, ?_⟩
  intro i s
  show φ (embW K N n0 d (blockW K N n0 d (g i) s)) = gW i (φ (embW K N n0 d s))
  rw [← hφeq]
  have hv : g i (embW K N n0 d s) ∈ flagSub K N (n0 + d) := hinv1 i _ (embW_mem s)
  have h1 := hφlow _ (sub_embW_resW_mem hwin hv)
  rw [map_sub, sub_eq_zero] at h1
  exact h1.symm

end CFSG.Quasithin.HM22
