module

public import CFSG.RankThree.PartOne.S12.Hyp

public section

namespace CFSG.RankThree.PartOne.Sec154

open Equiv

variable {G : Type} [Group G]

@[expose] def powHom (E : Subgroup G) (hE : ∀ a b : E, a * b = b * a) (k : ℤ) : E →* E where
  toFun e := e ^ k
  map_one' := one_zpow k
  map_mul' a b := Commute.mul_zpow (hE a b) k

theorem mem_autMoved (E : Subgroup G) (t : MulAut E) (e : E) : t e * e⁻¹ ∈ autMoved E t :=
  Subgroup.subset_closure ⟨e, rfl⟩

theorem map_autMoved (E : Subgroup G) (w t : MulAut E) :
    (autMoved E t).map w.toMonoidHom = autMoved E (w * t * w⁻¹) := by
  unfold autMoved
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨e, rfl⟩, rfl⟩
    refine ⟨w e, ?_⟩
    simp [MulAut.mul_apply]
  · rintro ⟨e, rfl⟩
    refine ⟨t (w⁻¹ e) * (w⁻¹ e)⁻¹, ⟨w⁻¹ e, rfl⟩, ?_⟩
    simp [MulAut.mul_apply]

theorem map_mem_autMoved (E : Subgroup G) {z t : MulAut E} (hz : z * t = t * z) {m : E}
    (hm : m ∈ autMoved E t) : z m ∈ autMoved E t := by
  refine Subgroup.closure_induction (p := fun m _ => z m ∈ autMoved E t) ?_ ?_ ?_ ?_ hm
  · rintro _ ⟨e, rfl⟩
    have h1 : z (t e) = t (z e) := by
      have := congrArg (fun m : MulAut E => m e) hz
      simpa [MulAut.mul_apply] using this
    have : z (t e * e⁻¹) = t (z e) * (z e)⁻¹ := by rw [map_mul, map_inv, h1]
    rw [this]
    exact mem_autMoved E t (z e)
  · simp
  · intro a b _ _ ha hb
    rw [map_mul]
    exact (autMoved E t).mul_mem ha hb
  · intro a _ ha
    rw [map_inv]
    exact (autMoved E t).inv_mem ha

theorem autMoved_eq_zpowers {p : ℕ} (hp : p.Prime) (E : Subgroup G) (t : MulAut E)
    (ht : Nat.card (autMoved E t) = p) {m : E} (hm : m ∈ autMoved E t) (hm1 : m ≠ 1) :
    ∀ m' ∈ autMoved E t, ∃ j : ℤ, m' = m ^ j := by
  have : Fact p.Prime := ⟨hp⟩
  have htop := zpowers_eq_top_of_prime_card (G := ↥(autMoved E t)) ht
    (g := ⟨m, hm⟩) (fun h => hm1 (congrArg Subtype.val h))
  intro m' hm'
  have : (⟨m', hm'⟩ : ↥(autMoved E t)) ∈ Subgroup.zpowers (⟨m, hm⟩ : ↥(autMoved E t)) := by
    rw [htop]; trivial
  obtain ⟨j, hj⟩ := this
  exact ⟨j, by simpa using (congrArg Subtype.val hj).symm⟩

theorem exists_ne_one_autMoved {p : ℕ} (hp : p.Prime) (E : Subgroup G) (t : MulAut E)
    (ht : Nat.card (autMoved E t) = p) : ∃ m ∈ autMoved E t, m ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have : Nat.card (autMoved E t) = 1 := by
    rw [Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨1⟩⟩
    rw [hcon a a.2, hcon b b.2]
  rw [ht] at this
  exact hp.one_lt.ne' this

theorem scalar_of_commuting {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : ∀ a b : E, a * b = b * a) {T : Set (MulAut E)}
    (hT : ∀ t ∈ T, Nat.card (autMoved E t) = p) (hne : T.Nonempty)
    (hcls : ∀ s ∈ T, ∀ t ∈ T, ∃ w ∈ Subgroup.closure T, w * s * w⁻¹ = t)
    (hspan : Subgroup.closure {m : E | ∃ t ∈ T, m ∈ autMoved E t} = ⊤)
    {z : MulAut E} (hz : ∀ t ∈ T, z * t = t * z) : ∃ k : ℤ, ∀ e : E, z e = e ^ k := by
  obtain ⟨t₀, ht₀⟩ := hne
  obtain ⟨m₀, hm₀, hm₀1⟩ := exists_ne_one_autMoved hp E t₀ (hT t₀ ht₀)
  have hpow₀ := autMoved_eq_zpowers hp E t₀ (hT t₀ ht₀) hm₀ hm₀1
  have hzc : ∀ w ∈ Subgroup.closure T, z * w = w * z := by
    have hle : Subgroup.closure T ≤ Subgroup.centralizer ({z} : Set (MulAut E)) := by
      rw [Subgroup.closure_le]
      intro t ht
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact hz t ht
    intro w hw
    exact Subgroup.mem_centralizer_iff.1 (hle hw) z (Set.mem_singleton z)
  obtain ⟨k, hk⟩ := hpow₀ (z m₀) (map_mem_autMoved E (hz t₀ ht₀) hm₀)
  refine ⟨k, fun e => ?_⟩
  have hroot : ∀ m : E, (∃ t ∈ T, m ∈ autMoved E t) → z m = m ^ k := by
    rintro m ⟨t, ht, hmt⟩
    obtain ⟨w, hw, hwt⟩ := hcls t₀ ht₀ t ht
    have hmap : m ∈ (autMoved E t₀).map w.toMonoidHom := by
      rw [map_autMoved E w t₀, hwt]; exact hmt
    obtain ⟨m', hm', rfl⟩ := hmap
    obtain ⟨j, rfl⟩ := hpow₀ m' hm'
    show z (w (m₀ ^ j)) = (w (m₀ ^ j)) ^ k
    have hzw' : z (w (m₀ ^ j)) = w (z (m₀ ^ j)) := by
      have := congrArg (fun m : MulAut E => m (m₀ ^ j)) (hzc w hw)
      simpa [MulAut.mul_apply] using this
    calc z (w (m₀ ^ j)) = w (z (m₀ ^ j)) := hzw'
      _ = w ((m₀ ^ k) ^ j) := by rw [map_zpow, hk]
      _ = w ((m₀ ^ j) ^ k) := by rw [← zpow_mul, ← zpow_mul, mul_comm]
      _ = (w (m₀ ^ j)) ^ k := by rw [map_zpow]
  have hle : Subgroup.closure {m : E | ∃ t ∈ T, m ∈ autMoved E t} ≤
      MonoidHom.eqLocus z.toMonoidHom (powHom E hE k) := by
    rw [Subgroup.closure_le]
    intro m hm
    exact hroot m hm
  have he : e ∈ Subgroup.closure {m : E | ∃ t ∈ T, m ∈ autMoved E t} := by
    rw [hspan]; trivial
  exact hle he

theorem span_root_groups {p : ℕ} (hp : p.Prime) {E : Subgroup G} {W : Subgroup (MulAut E)}
    {T : Set (MulAut E)} (hne : T.Nonempty) (hTconj : ∀ g ∈ W, ∀ t ∈ T, g * t * g⁻¹ ∈ T)
    (hT : ∀ t ∈ T, Nat.card (autMoved E t) = p)
    (hirr : ∀ B : Subgroup E, (∀ w ∈ W, ∀ b ∈ B, w b ∈ B) → B = ⊥ ∨ B = ⊤) :
    Subgroup.closure {m : E | ∃ t ∈ T, m ∈ autMoved E t} = ⊤ := by
  set B := Subgroup.closure {m : E | ∃ t ∈ T, m ∈ autMoved E t} with hB
  have hinv : ∀ w ∈ W, ∀ b ∈ B, w b ∈ B := by
    intro w hw b hb
    refine Subgroup.closure_induction (p := fun b _ => w b ∈ B) ?_ ?_ ?_ ?_ hb
    · rintro m ⟨t, ht, hmt⟩
      apply Subgroup.subset_closure
      refine ⟨w * t * w⁻¹, hTconj w hw t ht, ?_⟩
      rw [← map_autMoved E w t]
      exact ⟨m, hmt, rfl⟩
    · simp
    · intro a b' _ _ ha hb'
      rw [map_mul]
      exact B.mul_mem ha hb'
    · intro a _ ha
      rw [map_inv]
      exact B.inv_mem ha
  rcases hirr B hinv with h | h
  · exfalso
    obtain ⟨t, ht⟩ := hne
    obtain ⟨m, hm, hm1⟩ := exists_ne_one_autMoved hp E t (hT t ht)
    have : m ∈ B := Subgroup.subset_closure ⟨t, ht, hm⟩
    rw [h] at this
    exact hm1 ((Subgroup.mem_bot).1 this)
  · exact h

theorem range_eq_closure {n : ℕ} {E : Subgroup G} (φ : Perm (Fin n) →* MulAut E)
    {T : Set (MulAut E)} (hTφ : ∀ t, t ∈ T ↔ ∃ τ : Perm (Fin n), τ.IsSwap ∧ φ τ = t) :
    φ.range = Subgroup.closure T := by
  have hTeq : T = φ '' {σ : Perm (Fin n) | σ.IsSwap} := by
    ext t
    rw [hTφ]
    constructor
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨τ, hτ, rfl⟩
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨τ, hτ, rfl⟩
  rw [hTeq, ← MonoidHom.map_closure, Equiv.Perm.closure_isSwap, MonoidHom.range_eq_map]

theorem weyl_split {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hE : ∀ a b : E, a * b = b * a)
    {W : Subgroup (MulAut E)} {n : ℕ} (hn : 2 ≤ n) (φ : Perm (Fin n) →* MulAut E)
    (hφ : Function.Injective φ) {T : Set (MulAut E)}
    (hTφ : ∀ t, t ∈ T ↔ ∃ τ : Perm (Fin n), τ.IsSwap ∧ φ τ = t)
    (hTW : T ⊆ W) (hTconj : ∀ g ∈ W, ∀ t ∈ T, g * t * g⁻¹ ∈ T)
    (hT : ∀ t ∈ T, Nat.card (autMoved E t) = p)
    (hirr : ∀ B : Subgroup E, (∀ w ∈ W, ∀ b ∈ B, w b ∈ B) → B = ⊥ ∨ B = ⊤)
    (hcomplete : Function.Surjective (MulAut.conj : Perm (Fin n) →* MulAut (Perm (Fin n))))
    (hcenter : ∀ σ : Perm (Fin n), (∀ τ, σ * τ = τ * σ) → σ = 1) :
    W = (Subgroup.center W).map W.subtype ⊔ φ.range ∧
      (Subgroup.center W).map W.subtype ⊓ φ.range = ⊥ ∧
      ∀ z ∈ Subgroup.center W, ∃ k : ℤ, ∀ e : E, (z : MulAut E) e = e ^ k := by
  classical
  have hrange : φ.range = Subgroup.closure T := range_eq_closure φ hTφ
  have hne : T.Nonempty := by
    have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by
      intro h
      have := congrArg Fin.val h
      simp at this
    exact ⟨φ (swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩),
      (hTφ _).2 ⟨_, ⟨_, _, h01, rfl⟩, rfl⟩⟩
  have hcls : ∀ s ∈ T, ∀ t ∈ T, ∃ w ∈ Subgroup.closure T, w * s * w⁻¹ = t := by
    intro s hs t ht
    obtain ⟨σ, ⟨a, b, hab, rfl⟩, rfl⟩ := (hTφ s).1 hs
    obtain ⟨τ, ⟨c, d, hcd, rfl⟩, rfl⟩ := (hTφ t).1 ht
    obtain ⟨γ, hγ⟩ := isConj_iff.1 (Equiv.Perm.isConj_swap hab hcd)
    refine ⟨φ γ, ?_, ?_⟩
    · rw [← hrange]
      exact ⟨γ, rfl⟩
    · rw [← map_inv, ← map_mul, ← map_mul, hγ]
  have hspan := span_root_groups hp hne hTconj hT hirr
  have hscal : ∀ z : MulAut E, (∀ t ∈ T, z * t = t * z) → ∃ k : ℤ, ∀ e : E, z e = e ^ k :=
    fun z hz => scalar_of_commuting hp hE hT hne hcls hspan hz
  have hrangeW : φ.range ≤ W := by
    rw [hrange]
    exact (Subgroup.closure_le _).2 hTW
  have hconjmem : ∀ g ∈ W, ∀ σ : Perm (Fin n), ∃ τ : Perm (Fin n), φ τ = g * φ σ * g⁻¹ := by
    intro g hg σ
    have hσ : φ σ ∈ Subgroup.closure T := by
      rw [← hrange]
      exact ⟨σ, rfl⟩
    have hmemT : g * φ σ * g⁻¹ ∈ Subgroup.closure T := by
      refine Subgroup.closure_induction (p := fun x _ => g * x * g⁻¹ ∈ Subgroup.closure T)
        ?_ ?_ ?_ ?_ hσ
      · intro t ht
        exact Subgroup.subset_closure (hTconj g hg t ht)
      · simp
      · intro a b _ _ ha hb
        have : g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
        rw [this]
        exact Subgroup.mul_mem _ ha hb
      · intro a _ ha
        have : g * a⁻¹ * g⁻¹ = (g * a * g⁻¹)⁻¹ := by group
        rw [this]
        exact Subgroup.inv_mem _ ha
    have hmemR : g * φ σ * g⁻¹ ∈ φ.range := by
      rw [hrange]
      exact hmemT
    obtain ⟨τ, hτ⟩ := hmemR
    exact ⟨τ, hτ⟩
  have key : ∀ g ∈ W, ∃ σ₀ : Perm (Fin n), ∀ σ, g * φ σ * g⁻¹ = φ σ₀ * φ σ * (φ σ₀)⁻¹ := by
    intro g hg
    choose ψf hψf using hconjmem g hg
    have hmul : ∀ a b, ψf (a * b) = ψf a * ψf b := by
      intro a b
      apply hφ
      rw [map_mul, hψf, hψf, hψf, map_mul]
      group
    have hinj : Function.Injective ψf := by
      intro a b hab
      apply hφ
      have := congrArg φ hab
      rw [hψf, hψf] at this
      have h2 : φ a = φ b := by
        have := mul_left_cancel (a := g) (mul_right_cancel (b := g⁻¹) this)
        exact this
      exact h2
    have hsurj : Function.Surjective ψf := Finite.injective_iff_surjective.1 hinj
    let ψ : MulAut (Perm (Fin n)) :=
      MulEquiv.ofBijective (MonoidHom.mk' ψf hmul) ⟨hinj, hsurj⟩
    obtain ⟨σ₀, hσ₀⟩ := hcomplete ψ
    refine ⟨σ₀, fun σ => ?_⟩
    have h1 : ψf σ = σ₀ * σ * σ₀⁻¹ := by
      have := congrArg (fun f : MulAut (Perm (Fin n)) => f σ) hσ₀
      simp only [MulAut.conj_apply] at this
      exact this.symm
    rw [← hψf, ← map_inv, ← map_mul, ← map_mul, h1]
  have hscalar_center : ∀ z ∈ Subgroup.center W, ∃ k : ℤ, ∀ e : E, (z : MulAut E) e = e ^ k := by
    intro z hz
    refine hscal z fun t ht => ?_
    have := Subgroup.mem_center_iff.1 hz ⟨t, hTW ht⟩
    exact (congrArg Subtype.val this).symm
  refine ⟨?_, ?_, hscalar_center⟩
  · apply le_antisymm
    · intro g hg
      obtain ⟨σ₀, hσ₀⟩ := key g hg
      have hn₀W : φ σ₀ ∈ W := hrangeW ⟨σ₀, rfl⟩
      obtain ⟨c, hc⟩ : ∃ c : MulAut E, c = (φ σ₀)⁻¹ * g := ⟨_, rfl⟩
      have hcW : c ∈ W := by
        rw [hc]
        exact W.mul_mem (W.inv_mem hn₀W) hg
      have hcT : ∀ t ∈ T, c * t = t * c := by
        intro t ht
        obtain ⟨τ, -, rfl⟩ := (hTφ t).1 ht
        have h1 := hσ₀ τ
        rw [hc]
        calc (φ σ₀)⁻¹ * g * φ τ = (φ σ₀)⁻¹ * (g * φ τ * g⁻¹) * g := by group
          _ = (φ σ₀)⁻¹ * (φ σ₀ * φ τ * (φ σ₀)⁻¹) * g := by rw [h1]
          _ = φ τ * ((φ σ₀)⁻¹ * g) := by group
      obtain ⟨k, hk⟩ := hscal c hcT
      have hccen : (⟨c, hcW⟩ : ↥W) ∈ Subgroup.center W := by
        rw [Subgroup.mem_center_iff]
        intro w
        apply Subtype.ext
        show (w : MulAut E) * c = c * (w : MulAut E)
        apply MulEquiv.ext
        intro e
        rw [MulAut.mul_apply, MulAut.mul_apply, hk e, map_zpow, ← hk ((w : MulAut E) e)]
      have hcomm : φ σ₀ * c = c * φ σ₀ := by
        have := Subgroup.mem_center_iff.1 hccen ⟨φ σ₀, hn₀W⟩
        have h2 := congrArg Subtype.val this
        simpa using h2
      have hg_eq : g = c * φ σ₀ := by
        rw [← hcomm, hc]
        group
      rw [hg_eq]
      exact Subgroup.mul_mem_sup ⟨⟨c, hcW⟩, hccen, rfl⟩ ⟨σ₀, rfl⟩
    · exact sup_le (Subgroup.map_subtype_le _) hrangeW
  · rw [eq_bot_iff]
    rintro x ⟨⟨z, hz, rfl⟩, ⟨σ, hσ⟩⟩
    have hcomm : ∀ τ, σ * τ = τ * σ := by
      intro τ
      apply hφ
      have hτW : φ τ ∈ W := hrangeW ⟨τ, rfl⟩
      have := Subgroup.mem_center_iff.1 hz ⟨φ τ, hτW⟩
      have h2 : φ τ * (z : MulAut E) = (z : MulAut E) * φ τ := congrArg Subtype.val this
      have hσ' : φ σ = (z : MulAut E) := hσ
      rw [map_mul, map_mul, hσ']
      exact h2.symm
    have h1 := hcenter σ hcomm
    rw [Subgroup.mem_bot]
    have hσ' : φ σ = (z : MulAut E) := hσ
    show (z : MulAut E) = 1
    rw [← hσ', h1, map_one]

end CFSG.RankThree.PartOne.Sec154
