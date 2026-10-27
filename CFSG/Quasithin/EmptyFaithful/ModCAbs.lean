module

public import CFSG.Quasithin.EmptyFaithful.ModCBase

public section

namespace CFSG.Quasithin.ModC

open Equiv Equiv.Perm CFSG.Quasithin.G6

section Lift

variable {n : ℕ} {W : Type*} [CommGroup W]

@[expose] def liftAut (Φ : W ≃* ↥(coreMod n)) : Perm (Fin n) →* MulAut W :=
  (MulAut.congr Φ.symm).toMonoidHom.comp (coreAct n)

theorem liftAut_apply (Φ : W ≃* ↥(coreMod n)) (σ : Perm (Fin n)) (w : W) :
    Φ (liftAut Φ σ w) = coreAct n σ (Φ w) := by
  simp [liftAut]

theorem ev_pair_mem_core {i j : Fin n} (hij : i ≠ j) :
    (Multiplicative.ofAdd (fun k : Fin n => if k = i ∨ k = j then (1 : ZMod 2) else 0) : PermMod n) ∈
      coreMod n := by
  classical
  rw [mem_coreMod]
  simp only [toAdd_ofAdd]
  rw [Finset.sum_boole]
  have : (Finset.univ.filter fun k : Fin n => k = i ∨ k = j) = {i, j} := by
    ext k; simp
  rw [this, Finset.card_pair hij]
  decide

theorem coreAct_faithful (hn : 3 ≤ n) (σ : Perm (Fin n))
    (h : ∀ x : ↥(coreMod n), coreAct n σ x = x) : σ = 1 := by
  classical
  refine Equiv.ext fun i => ?_
  by_contra hi
  have hi' : σ i ≠ i := hi
  obtain ⟨j, hji, hjσ⟩ : ∃ j : Fin n, j ≠ i ∧ j ≠ σ i := by
    by_contra hcon
    push Not at hcon
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ {i, σ i} := by
      intro j _
      by_cases hj : j = i
      · simp [hj]
      · simp [hcon j hj]
    have h1 := Finset.card_le_card hsub
    have h2 : ({i, σ i} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    omega
  have hx := ev_pair_mem_core (Ne.symm hji)
  have h1 := congrArg (fun y : ↥(coreMod n) => Multiplicative.toAdd (y : PermMod n) (σ i))
    (h ⟨_, hx⟩)
  simp only [coreAct_coe, permAct_apply, toAdd_ofAdd] at h1
  simp [hi', hjσ.symm] at h1

theorem theta_injective (hn : 3 ≤ n) (Φ : W ≃* ↥(coreMod n)) {Θ : Perm (Fin n) →* MulAut W}
    (hΘ : ∀ σ w, Φ (Θ σ w) = coreAct n σ (Φ w)) : Function.Injective Θ := by
  rw [injective_iff_map_eq_one]
  intro σ hσ
  apply coreAct_faithful hn
  intro x
  obtain ⟨w, rfl⟩ := Φ.surjective x
  have := hΘ σ w
  rw [hσ] at this
  exact this.symm

end Lift

section Pigeon

variable {n : ℕ}

theorem pigeon (ρ : MulAut ↥(coreMod n))
    (hρ : ∀ σ : Perm (Fin n), sign σ = 1 → ∃ σ' : Perm (Fin n), sign σ' = 1 ∧
      ∀ x : ↥(coreMod n), ρ⁻¹ (coreAct n σ (ρ x)) = coreAct n σ' x)
    {y b : PermMod n} (hy : y ∈ coreMod n) (hb : b ∈ coreMod n) (hρy : ρ ⟨y, hy⟩ = ⟨b, hb⟩)
    (L : List (Perm (Fin n))) (hL8 : L.length = 8) (hLs : ∀ σ ∈ L, sign σ = 1)
    (hLn : (L.map (fun σ => permAct n σ b)).Nodup)
    (hcount : (Finset.univ.filter fun u : PermMod n =>
      (∑ i, Multiplicative.toAdd u i = 0) ∧ wt u = wt y).card ≤ 7) : False := by
  classical
  let f : Perm (Fin n) → PermMod n := fun σ =>
    ((ρ⁻¹ (coreAct n σ ⟨b, hb⟩) : ↥(coreMod n)) : PermMod n)
  have hnd : (L.map f).Nodup := by
    have h1 : (L.map (fun σ => coreAct n σ ⟨b, hb⟩)).Nodup := by
      have e : (L.map (fun σ => coreAct n σ ⟨b, hb⟩)).map (fun u : ↥(coreMod n) => (u : PermMod n)) =
          L.map (fun σ => permAct n σ b) := by
        rw [List.map_map]
        rfl
      rw [← e] at hLn
      exact List.Nodup.of_map _ hLn
    have h2 : L.map f = (L.map (fun σ => coreAct n σ ⟨b, hb⟩)).map
        (fun u => ((ρ⁻¹ u : ↥(coreMod n)) : PermMod n)) := by
      rw [List.map_map]
      rfl
    rw [h2]
    exact h1.map fun u v huv => ρ⁻¹.injective (Subtype.ext huv)
  have hmem : ∀ σ ∈ L, f σ ∈ Finset.univ.filter fun u : PermMod n =>
      (∑ i, Multiplicative.toAdd u i = 0) ∧ wt u = wt y := by
    intro σ hσ
    obtain ⟨σ', -, hσ'⟩ := hρ σ (hLs σ hσ)
    have e : ρ⁻¹ (coreAct n σ ⟨b, hb⟩) = coreAct n σ' ⟨y, hy⟩ := by
      have := hσ' ⟨y, hy⟩
      rwa [hρy] at this
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, f]
    rw [e]
    refine ⟨(coreAct n σ' ⟨y, hy⟩).2, ?_⟩
    rw [coreAct_coe, wt_permAct]
  have hcardF : (L.map f).toFinset.card = 8 := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map, hL8]
  have hsub : (L.map f).toFinset ⊆ Finset.univ.filter fun u : PermMod n =>
      (∑ i, Multiplicative.toAdd u i = 0) ∧ wt u = wt y := by
    intro u hu
    rw [List.mem_toFinset, List.mem_map] at hu
    obtain ⟨σ, hσ, rfl⟩ := hu
    exact hmem σ hσ
  have := Finset.card_le_card hsub
  omega

end Pigeon

section Join

variable {n : ℕ} {W : Type*} [CommGroup W]

@[expose] def join3 (V : Subgroup W) (g : MulAut W) : Subgroup W :=
  V ⊔ V.map g.toMonoidHom ⊔ V.map (g ^ 2).toMonoidHom

theorem mem_join3 {V : Subgroup W} {g : MulAut W} {x : W} :
    x ∈ join3 V g ↔ ∃ a ∈ V, ∃ b ∈ V, ∃ c ∈ V, a * g b * (g ^ 2) c = x := by
  unfold join3
  rw [Subgroup.mem_sup]
  constructor
  · rintro ⟨y, hy, c', hc', rfl⟩
    rw [Subgroup.mem_sup] at hy
    obtain ⟨a, ha, b', hb', rfl⟩ := hy
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hb'
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hc'
    exact ⟨a, ha, b, hb, c, hc, rfl⟩
  · rintro ⟨a, ha, b, hb, c, hc, rfl⟩
    refine ⟨a * g b, ?_, (g ^ 2) c, Subgroup.mem_map_of_mem _ hc, rfl⟩
    rw [Subgroup.mem_sup]
    exact ⟨a, ha, g b, Subgroup.mem_map_of_mem _ hb, rfl⟩

theorem image_join3 (Φ : W ≃* ↥(coreMod n)) {Θ : Perm (Fin n) →* MulAut W}
    (hΘ : ∀ σ w, Φ (Θ σ w) = coreAct n σ (Φ w)) {V : Subgroup W} {z v : W} (hzV : z ∈ V)
    (hvV : v ∈ V) (hV : ∀ a ∈ V, a = 1 ∨ a = z ∨ a = v ∨ a = z * v) (σ : Perm (Fin n)) :
    (fun w : W => ((Φ w : ↥(coreMod n)) : PermMod n)) '' (join3 V (Θ σ) : Set W) =
      ↑(join3F ((Φ z : ↥(coreMod n)) : PermMod n) ((Φ v : ↥(coreMod n)) : PermMod n) σ) := by
  classical
  let Ψ : W → PermMod n := fun w => ((Φ w : ↥(coreMod n)) : PermMod n)
  have hΨmul : ∀ a b : W, Ψ (a * b) = Ψ a * Ψ b := fun a b => by simp [Ψ]
  have hΨ1 : Ψ 1 = 1 := by simp [Ψ]
  have hΨΘ : ∀ (τ : Perm (Fin n)) (w : W), Ψ (Θ τ w) = permAct n τ (Ψ w) := fun τ w => by
    simp only [Ψ]
    rw [hΘ]
    rfl
  have hV4 : ∀ q : PermMod n, q ∈ V4 (Ψ z) (Ψ v) ↔ ∃ a ∈ V, Ψ a = q := by
    intro q
    simp only [V4, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl | rfl | rfl)
      · exact ⟨1, V.one_mem, hΨ1⟩
      · exact ⟨z, hzV, rfl⟩
      · exact ⟨v, hvV, rfl⟩
      · exact ⟨z * v, V.mul_mem hzV hvV, hΨmul z v⟩
    · rintro ⟨a, ha, rfl⟩
      rcases hV a ha with rfl | rfl | rfl | rfl
      · exact Or.inl hΨ1
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (hΨmul z v)))
  show Ψ '' (join3 V (Θ σ) : Set W) = ↑(join3F (Ψ z) (Ψ v) σ)
  ext p
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := mem_join3.mp hx
    rw [Finset.mem_coe, join3F, Finset.mem_image]
    refine ⟨(Ψ a, Ψ b, Ψ c), ?_, ?_⟩
    · simp only [Finset.mem_product]
      exact ⟨(hV4 _).2 ⟨a, ha, rfl⟩, (hV4 _).2 ⟨b, hb, rfl⟩, (hV4 _).2 ⟨c, hc, rfl⟩⟩
    · simp only [hΨmul]
      rw [hΨΘ σ b, ← map_pow, hΨΘ (σ ^ 2) c]
  · intro hp
    rw [Finset.mem_coe, join3F, Finset.mem_image] at hp
    obtain ⟨⟨q1, q2, q3⟩, hq, rfl⟩ := hp
    simp only [Finset.mem_product] at hq
    obtain ⟨a, ha, rfl⟩ := (hV4 _).1 hq.1
    obtain ⟨b, hb, rfl⟩ := (hV4 _).1 hq.2.1
    obtain ⟨c, hc, rfl⟩ := (hV4 _).1 hq.2.2
    refine ⟨a * Θ σ b * (Θ σ ^ 2) c, mem_join3.mpr ⟨a, ha, b, hb, c, hc, rfl⟩, ?_⟩
    simp only [hΨmul]
    rw [hΨΘ σ b, ← map_pow, hΨΘ (σ ^ 2) c]

theorem card_join3 (Φ : W ≃* ↥(coreMod n)) {Θ : Perm (Fin n) →* MulAut W}
    (hΘ : ∀ σ w, Φ (Θ σ w) = coreAct n σ (Φ w)) {V : Subgroup W} {z v : W} (hzV : z ∈ V)
    (hvV : v ∈ V) (hV : ∀ a ∈ V, a = 1 ∨ a = z ∨ a = v ∨ a = z * v) (σ : Perm (Fin n)) :
    Nat.card ↥(join3 V (Θ σ)) =
      (join3F ((Φ z : ↥(coreMod n)) : PermMod n) ((Φ v : ↥(coreMod n)) : PermMod n) σ).card := by
  classical
  have hΨinj : Function.Injective (fun w : W => ((Φ w : ↥(coreMod n)) : PermMod n)) :=
    fun a b h => Φ.injective (Subtype.ext h)
  calc Nat.card ↥(join3 V (Θ σ)) = (join3 V (Θ σ) : Set W).ncard := Nat.card_coe_set_eq _
    _ = ((fun w : W => ((Φ w : ↥(coreMod n)) : PermMod n)) '' (join3 V (Θ σ) : Set W)).ncard :=
        (Set.ncard_image_of_injective _ hΨinj).symm
    _ = (↑(join3F ((Φ z : ↥(coreMod n)) : PermMod n) ((Φ v : ↥(coreMod n)) : PermMod n) σ) :
          Set (PermMod n)).ncard := by rw [image_join3 Φ hΘ hzV hvV hV σ]
    _ = (join3F ((Φ z : ↥(coreMod n)) : PermMod n) ((Φ v : ↥(coreMod n)) : PermMod n) σ).card :=
        Set.ncard_coe_finset _

theorem mem_join3_of_coords (Φ : W ≃* ↥(coreMod n)) {Θ : Perm (Fin n) →* MulAut W}
    (hΘ : ∀ σ w, Φ (Θ σ w) = coreAct n σ (Φ w)) {V : Subgroup W} {z v : W} (hzV : z ∈ V)
    (hvV : v ∈ V) (hV : ∀ a ∈ V, a = 1 ∨ a = z ∨ a = v ∨ a = z * v) (σ : Perm (Fin n)) {w : W}
    (hw : ((Φ w : ↥(coreMod n)) : PermMod n) ∈
      join3F ((Φ z : ↥(coreMod n)) : PermMod n) ((Φ v : ↥(coreMod n)) : PermMod n) σ) :
    w ∈ join3 V (Θ σ) := by
  have h := image_join3 Φ hΘ hzV hvV hV σ
  have hw' : ((Φ w : ↥(coreMod n)) : PermMod n) ∈
      (fun w : W => ((Φ w : ↥(coreMod n)) : PermMod n)) '' (join3 V (Θ σ) : Set W) := by
    rw [h]
    exact hw
  obtain ⟨x, hx, hxw⟩ := hw'
  have : x = w := Φ.injective (Subtype.ext hxw)
  rw [← this]
  exact hx

theorem card_D {Θ : Perm (Fin n) →* MulAut W} (hΘ : Function.Injective Θ) {Bf : Subgroup (MulAut W)}
    (hB2 : IsPGroup 2 Bf) {o : ℕ} (ho : Odd o) (hcardA : Nat.card (alternatingGroup (Fin n)) = 8 * o)
    (h8 : 8 ≤ Nat.card ↥((alternatingGroup (Fin n)).map Θ ⊓ Bf)) :
    Nat.card ↥(Bf.comap Θ ⊓ alternatingGroup (Fin n)) = 8 := by
  classical
  set D : Subgroup (Perm (Fin n)) := Bf.comap Θ ⊓ alternatingGroup (Fin n) with hD
  have hmap : D.map Θ = (alternatingGroup (Fin n)).map Θ ⊓ Bf := by
    ext g
    simp only [Subgroup.mem_map, Subgroup.mem_inf, hD, Subgroup.mem_comap]
    constructor
    · rintro ⟨d, ⟨hdB, hdA⟩, rfl⟩
      exact ⟨⟨d, hdA, rfl⟩, hdB⟩
    · rintro ⟨⟨d, hdA, rfl⟩, hgB⟩
      exact ⟨d, ⟨hgB, hdA⟩, rfl⟩
  have hcard : Nat.card D = Nat.card ↥((alternatingGroup (Fin n)).map Θ ⊓ Bf) := by
    rw [← hmap]
    exact (Subgroup.card_map_of_injective hΘ).symm
  have hle8 : Nat.card D ≤ 8 := by
    have hDp : IsPGroup 2 ↥D := by
      have h1 : IsPGroup 2 ↥(D.map Θ) := by
        rw [hmap]
        exact hB2.to_le inf_le_right
      exact h1.of_equiv (Subgroup.equivMapOfInjective D Θ hΘ).symm
    obtain ⟨k, hk⟩ := hDp.exists_card_eq
    have hdvd : Nat.card D ∣ 8 * o := by
      rw [← hcardA]
      exact Subgroup.card_dvd_of_le (fun d hd => hd.2)
    rw [hk] at hdvd ⊢
    have hcop : Nat.Coprime (2 ^ k) o := Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr ho)
    have h8' : 2 ^ k ∣ 8 := hcop.dvd_of_dvd_mul_right hdvd
    exact Nat.le_of_dvd (by norm_num) h8'
  omega

end Join

section Main

variable {n : ℕ} {W : Type*} [CommGroup W]

theorem abstractOut (hn : 3 ≤ n) (hmodel : ModelOut n) {o : ℕ} (ho : Odd o)
    (hcardA : Nat.card (alternatingGroup (Fin n)) = 8 * o)
    (Φ : W ≃* ↥(coreMod n)) {Θ : Perm (Fin n) →* MulAut W}
    (hΘ : ∀ σ w, Φ (Θ σ w) = coreAct n σ (Φ w)) {Kb Bf : Subgroup (MulAut W)}
    (hKb : Kb = (alternatingGroup (Fin n)).map Θ)
    (hB2 : IsPGroup 2 Bf) (hnorm : ∀ τ ∈ Bf, ∀ k ∈ Kb, τ * k * τ⁻¹ ∈ Kb)
    (h8 : 8 ≤ Nat.card ↥(Kb ⊓ Bf))
    {z v : W} (hz1 : z ≠ 1) (hv1 : v ≠ 1) (hvz : v ≠ z) {V : Subgroup W} (hzV : z ∈ V) (hvV : v ∈ V)
    (hV : ∀ a ∈ V, a = 1 ∨ a = z ∨ a = v ∨ a = z * v)
    (hBz : ∀ τ ∈ Bf, τ z = z) (hBV : ∀ τ ∈ Bf, ∀ a ∈ V, τ a ∈ V)
    (hwt : ∃ k ∈ Kb, k z = v)
    {g : MulAut W} (hgK : g ∈ Kb) (hg3 : g ^ 3 = 1) (hgz : g z = z) (hgv1 : g v ≠ v)
    (hgv2 : g v ≠ z * v) (hne : Nat.card ↥(join3 V g) ≠ 8)
    {B₂ : Subgroup (MulAut W)} (hBB₂ : Bf ≤ B₂) (hgB₂ : g ∈ B₂) (h5 : ¬ 5 ∣ Nat.card ↥B₂) :
    ∃ x : W, x ∈ join3 V g ∧ x ≠ 1 ∧ (∀ τ ∈ Bf, τ x = x) ∧ (∃ j ∈ Kb, j x = x ∧ j z ≠ z) ∧
      (∃ j' ∈ Kb, j' x = x ∧ j' v ∉ V) := by
  classical
  have hΘinj : Function.Injective Θ := theta_injective hn Φ hΘ
  let Ψ : W → PermMod n := fun w => ((Φ w : ↥(coreMod n)) : PermMod n)
  have hΨinj : Function.Injective Ψ := fun a b h => Φ.injective (Subtype.ext h)
  have hΨmul : ∀ a b : W, Ψ (a * b) = Ψ a * Ψ b := fun a b => by simp [Ψ]
  have hΨ1 : Ψ 1 = 1 := by simp [Ψ]
  have hΨcore : ∀ w, ∑ i, Multiplicative.toAdd (Ψ w) i = 0 := fun w => mem_coreMod.mp (Φ w).2
  have hΨΘ : ∀ (τ : Perm (Fin n)) (w : W), Ψ (Θ τ w) = permAct n τ (Ψ w) := fun τ w => by
    simp only [Ψ]
    rw [hΘ]
    rfl
  have hKbmem : ∀ k ∈ Kb, ∃ σ ∈ alternatingGroup (Fin n), Θ σ = k := by
    intro k hk
    rw [hKb] at hk
    obtain ⟨σ, hσ, rfl⟩ := Subgroup.mem_map.mp hk
    exact ⟨σ, hσ, rfl⟩
  have hΘKb : ∀ σ ∈ alternatingGroup (Fin n), Θ σ ∈ Kb := fun σ hσ => by
    rw [hKb]
    exact Subgroup.mem_map_of_mem _ hσ
  have hsign : ∀ σ : Perm (Fin n), σ ∈ alternatingGroup (Fin n) ↔ sign σ = 1 :=
    fun σ => Perm.mem_alternatingGroup
  have hD8 : Nat.card ↥(Bf.comap Θ ⊓ alternatingGroup (Fin n)) = 8 :=
    card_D hΘinj hB2 ho hcardA (by rw [← hKb]; exact h8)
  have hDe : ∀ d ∈ Bf.comap Θ ⊓ alternatingGroup (Fin n), sign d = 1 := fun d hd => (hsign d).mp hd.2
  have hDB : ∀ d ∈ Bf.comap Θ ⊓ alternatingGroup (Fin n), Θ d ∈ Bf := fun d hd => hd.1
  have hz1' : Ψ z ≠ 1 := fun h => hz1 (hΨinj (h.trans hΨ1.symm))
  have hv1' : Ψ v ≠ 1 := fun h => hv1 (hΨinj (h.trans hΨ1.symm))
  have hvz' : Ψ v ≠ Ψ z := fun h => hvz (hΨinj h)
  have hDV : ∀ d ∈ Bf.comap Θ ⊓ alternatingGroup (Fin n),
      permAct n d (Ψ z) = Ψ z ∧ (permAct n d (Ψ v) = Ψ v ∨ permAct n d (Ψ v) = Ψ z * Ψ v) := by
    intro d hd
    have hτ := hDB d hd
    have h1 : Θ d z = z := hBz _ hτ
    have h2 : Θ d v ∈ V := hBV _ hτ v hvV
    refine ⟨by rw [← hΨΘ, h1], ?_⟩
    rcases hV _ h2 with h | h | h | h
    · exact absurd ((Θ d).injective (h.trans (map_one (Θ d)).symm)) hv1
    · exact absurd ((Θ d).injective (h.trans h1.symm)) hvz
    · left
      rw [← hΨΘ, h]
    · right
      rw [← hΨΘ, h, hΨmul]
  have hwt' : wt (Ψ v) = wt (Ψ z) ∨ wt (Ψ z * Ψ v) = wt (Ψ z) := by
    left
    obtain ⟨k, hk, hkz⟩ := hwt
    obtain ⟨σ, -, rfl⟩ := hKbmem k hk
    have : Ψ v = permAct n σ (Ψ z) := by rw [← hkz, hΨΘ]
    rw [this, wt_permAct]
  obtain ⟨σg, -, hσgΘ⟩ := hKbmem g hgK
  have hσg3 : σg ^ 3 = 1 := by
    apply hΘinj
    rw [map_pow, hσgΘ, hg3, map_one]
  have hgz' : permAct n σg (Ψ z) = Ψ z := by rw [← hΨΘ, hσgΘ, hgz]
  have hgv1' : permAct n σg (Ψ v) ≠ Ψ v := by
    intro h
    apply hgv1
    apply hΨinj
    rw [← hσgΘ, hΨΘ]
    exact h
  have hgv2' : permAct n σg (Ψ v) ≠ Ψ z * Ψ v := by
    intro h
    apply hgv2
    apply hΨinj
    rw [hΨmul, ← hσgΘ, hΨΘ]
    exact h
  have hne' : (join3F (Ψ z) (Ψ v) σg).card ≠ 8 := by
    have h := card_join3 Φ hΘ hzV hvV hV σg
    rw [hσgΘ] at h
    exact fun h8' => hne (h.trans h8')
  have h5' : ¬ 5 ∣ Nat.card ↥(Subgroup.closure
      (((Bf.comap Θ ⊓ alternatingGroup (Fin n) : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) ∪ {σg})) := by
    intro h5d
    apply h5
    set C := Subgroup.closure
      (((Bf.comap Θ ⊓ alternatingGroup (Fin n) : Subgroup (Perm (Fin n))) : Set (Perm (Fin n))) ∪ {σg})
      with hC
    have hCle : C.map Θ ≤ B₂ := by
      rw [Subgroup.map_le_iff_le_comap, hC, Subgroup.closure_le]
      rintro s (hs | hs)
      · exact hBB₂ (hDB s hs)
      · rw [Set.mem_singleton_iff.mp hs]
        show Θ σg ∈ B₂
        rw [hσgΘ]
        exact hgB₂
    have h1 : Nat.card ↥(C.map Θ) = Nat.card ↥C := Subgroup.card_map_of_injective hΘinj
    rw [← h1] at h5d
    exact h5d.trans (Subgroup.card_dvd_of_le hCle)
  obtain ⟨y, hyjoin, hysum, hy1, hyz, hyD, hDfix, ⟨j, hjs, hjy, hjz⟩, ⟨j', hj's, hj'y, hj'v1, hj'v2, hj'v3⟩,
    ⟨L, hL8, hLs, hLn⟩, hcount⟩ :=
    hmodel _ hDe hD8 (Ψ z) (Ψ v) (hΨcore z) hz1' (hΨcore v) hv1' hvz' hDV hwt' σg hσg3 hgz' hgv1'
      hgv2' hne' h5'
  have hyc : y ∈ coreMod n := mem_coreMod.mpr hysum
  let x : W := Φ.symm ⟨y, hyc⟩
  have hΨx : Ψ x = y := by simp [Ψ, x]
  have hxjoin : x ∈ join3 V g := by
    rw [← hσgΘ]
    exact mem_join3_of_coords Φ hΘ hzV hvV hV σg (by rw [show ((Φ x : ↥(coreMod n)) : PermMod n) = y from hΨx]; exact hyjoin)
  have hx1 : x ≠ 1 := fun h => hy1 (by rw [← hΨx, h, hΨ1])
  have hΘsymm : ∀ (σ : Perm (Fin n)) (u : W), Φ.symm (coreAct n σ (Φ u)) = Θ σ u := fun σ u => by
    rw [← hΘ]
    simp
  have hxfix : ∀ τ ∈ Bf, τ x = x := by
    intro τ hτ
    have hτinv : τ⁻¹ ∈ Bf := Bf.inv_mem hτ
    have hconj : ∀ s : Perm (Fin n), s ∈ alternatingGroup (Fin n) → Θ s ∈ Bf →
        ∃ s' ∈ Bf.comap Θ ⊓ alternatingGroup (Fin n), Θ s' = τ⁻¹ * Θ s * τ := by
      intro s hs hsB
      have h1 : τ⁻¹ * Θ s * τ ∈ Kb := by
        have := hnorm τ⁻¹ hτinv (Θ s) (hΘKb s hs)
        simpa using this
      obtain ⟨s', hs'A, hs'⟩ := hKbmem _ h1
      refine ⟨s', ⟨?_, hs'A⟩, hs'⟩
      show Θ s' ∈ Bf
      rw [hs']
      exact Bf.mul_mem (Bf.mul_mem hτinv hsB) hτ
    have hDτ : ∀ d ∈ Bf.comap Θ ⊓ alternatingGroup (Fin n), Θ d (τ x) = τ x := by
      intro d hd
      obtain ⟨d', hd'D, hd'⟩ := hconj d hd.2 hd.1
      have h1 : permAct n d' y = y := hyD d' hd'D
      have h2 : Θ d' x = x := by
        apply hΨinj
        rw [hΨΘ, hΨx, h1]
      rw [hd'] at h2
      have h3 : τ⁻¹ (Θ d (τ x)) = x := h2
      calc Θ d (τ x) = τ (τ⁻¹ (Θ d (τ x))) := by simp
        _ = τ x := by rw [h3]
    have hΨτx_fix : ∀ d ∈ Bf.comap Θ ⊓ alternatingGroup (Fin n),
        permAct n d (Ψ (τ x)) = Ψ (τ x) := by
      intro d hd
      rw [← hΨΘ, hDτ d hd]
    rcases hDfix (Ψ (τ x)) (hΨcore _) hΨτx_fix with h | h | h | h
    · exfalso
      apply hx1
      have : τ x = 1 := hΨinj (h.trans hΨ1.symm)
      exact τ.injective (this.trans (map_one τ).symm)
    · exfalso
      have : τ x = z := hΨinj h
      have h2 : x = z := τ.injective (this.trans (hBz τ hτ).symm)
      apply hyz
      rw [← hΨx, h2]
    · exact hΨinj (h.trans hΨx.symm)
    · exfalso
      have hb : Ψ z * y ∈ coreMod n := (coreMod n).mul_mem (Φ z).2 hyc
      let ρ : MulAut ↥(coreMod n) := MulAut.congr Φ τ
      have hρapp : ∀ u, ρ u = Φ (τ (Φ.symm u)) := fun u => rfl
      have hρinv : ∀ u, ρ⁻¹ u = Φ (τ⁻¹ (Φ.symm u)) := by
        intro u
        have : ρ⁻¹ = MulAut.congr Φ τ⁻¹ := (map_inv (MulAut.congr Φ) τ).symm
        rw [this]
        rfl
      have hρy : ρ ⟨y, hyc⟩ = ⟨Ψ z * y, hb⟩ := by
        apply Subtype.ext
        rw [hρapp]
        exact h
      have hρ : ∀ σ : Perm (Fin n), sign σ = 1 → ∃ σ' : Perm (Fin n), sign σ' = 1 ∧
          ∀ X : ↥(coreMod n), ρ⁻¹ (coreAct n σ (ρ X)) = coreAct n σ' X := by
        intro σ hσ
        have hσA : σ ∈ alternatingGroup (Fin n) := (hsign σ).2 hσ
        have h1 : τ⁻¹ * Θ σ * τ ∈ Kb := by
          have := hnorm τ⁻¹ hτinv (Θ σ) (hΘKb σ hσA)
          simpa using this
        obtain ⟨σ', hσ'A, hσ'⟩ := hKbmem _ h1
        refine ⟨σ', (hsign σ').1 hσ'A, fun X => ?_⟩
        obtain ⟨w, rfl⟩ := Φ.surjective X
        rw [hρapp, hρinv]
        simp only [MulEquiv.symm_apply_apply]
        rw [hΘsymm, ← hΘ σ' w, hσ']
        rfl
      exact pigeon ρ hρ hyc hb hρy L hL8 hLs hLn hcount
  refine ⟨x, hxjoin, hx1, hxfix, ?_, ?_⟩
  · refine ⟨Θ j, hΘKb j ((hsign j).2 hjs), ?_, ?_⟩
    · apply hΨinj
      rw [hΨΘ, hΨx, hjy]
    · intro h
      apply hjz
      rw [← hΨΘ, h]
  · refine ⟨Θ j', hΘKb j' ((hsign j').2 hj's), ?_, ?_⟩
    · apply hΨinj
      rw [hΨΘ, hΨx, hj'y]
    · intro hmem
      rcases hV _ hmem with h | h | h | h
      · exact hv1 ((Θ j').injective (h.trans (map_one (Θ j')).symm))
      · apply hj'v3
        rw [← hΨΘ, h]
      · apply hj'v1
        rw [← hΨΘ, h]
      · apply hj'v2
        rw [← hΨΘ, h, hΨmul]

end Main

end CFSG.Quasithin.ModC
