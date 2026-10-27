module

public import CFSG.Quasithin.Background.G11Defs

public section

namespace CFSG.Quasithin

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem mem_conjSub {g : GLV V} {U : Submodule (ZMod 2) V} {v : V} :
    v ∈ conjSub g U ↔ g.symm v ∈ U := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu
  · intro h
    exact ⟨g.symm v, h, by simp⟩

theorem apply_mem_conjSub {g : GLV V} {U : Submodule (ZMod 2) V} {u : V} (hu : u ∈ U) :
    g u ∈ conjSub g U := ⟨u, hu, rfl⟩

@[simp] theorem conjSub_one (U : Submodule (ZMod 2) V) : conjSub (1 : GLV V) U = U := by
  show Submodule.map ((1 : GLV V) : V →ₗ[ZMod 2] V) U = U
  exact Submodule.map_id U

theorem conjSub_mul (g h : GLV V) (U : Submodule (ZMod 2) V) :
    conjSub (g * h) U = conjSub g (conjSub h U) := by
  ext v
  simp only [mem_conjSub]
  rfl

theorem conjSub_inv_conjSub (g : GLV V) (U : Submodule (ZMod 2) V) :
    conjSub g⁻¹ (conjSub g U) = U := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem conjSub_conjSub_inv (g : GLV V) (U : Submodule (ZMod 2) V) :
    conjSub g (conjSub g⁻¹ U) = U := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem conjSub_mono (g : GLV V) {U U' : Submodule (ZMod 2) V} (h : U ≤ U') :
    conjSub g U ≤ conjSub g U' := Submodule.map_mono h

theorem conjSub_le_iff (g : GLV V) {U U' : Submodule (ZMod 2) V} :
    conjSub g U ≤ conjSub g U' ↔ U ≤ U' := by
  refine ⟨fun h => ?_, conjSub_mono g⟩
  have := conjSub_mono g⁻¹ h
  rwa [conjSub_inv_conjSub, conjSub_inv_conjSub] at this

theorem conjSub_inj (g : GLV V) {U U' : Submodule (ZMod 2) V} :
    conjSub g U = conjSub g U' ↔ U = U' := by
  simp only [le_antisymm_iff, conjSub_le_iff]

theorem conjSub_inf (g : GLV V) (U U' : Submodule (ZMod 2) V) :
    conjSub g (U ⊓ U') = conjSub g U ⊓ conjSub g U' := by
  ext v
  simp [mem_conjSub]

theorem conjSub_sup (g : GLV V) (U U' : Submodule (ZMod 2) V) :
    conjSub g (U ⊔ U') = conjSub g U ⊔ conjSub g U' :=
  Submodule.map_sup _ _ _

@[simp] theorem conjSub_bot (g : GLV V) : conjSub g (⊥ : Submodule (ZMod 2) V) = ⊥ :=
  Submodule.map_bot _

@[simp] theorem conjSub_top (g : GLV V) : conjSub g (⊤ : Submodule (ZMod 2) V) = ⊤ := by
  ext v
  simp [mem_conjSub]

theorem conjSub_eq_bot_iff (g : GLV V) {U : Submodule (ZMod 2) V} :
    conjSub g U = ⊥ ↔ U = ⊥ := by
  constructor
  · intro h
    have := congrArg (conjSub g⁻¹) h
    rwa [conjSub_inv_conjSub, conjSub_bot] at this
  · rintro rfl
    exact conjSub_bot g

theorem finrank_conjSub (g : GLV V) (U : Submodule (ZMod 2) V) :
    Module.finrank (ZMod 2) (conjSub g U) = Module.finrank (ZMod 2) U :=
  LinearEquiv.finrank_eq (Submodule.equivMapOfInjective (g : V →ₗ[ZMod 2] V) g.injective U).symm


theorem Invariant.conjSub_le {K : Subgroup (GLV V)} {U : Submodule (ZMod 2) V} (h : Invariant K U)
    {k : GLV V} (hk : k ∈ K) : conjSub k U ≤ U := by
  rintro _ ⟨u, hu, rfl⟩
  exact h k hk u hu

theorem Invariant.conjSub_eq {K : Subgroup (GLV V)} {U : Submodule (ZMod 2) V} (h : Invariant K U)
    {k : GLV V} (hk : k ∈ K) : conjSub k U = U := by
  refine le_antisymm (h.conjSub_le hk) ?_
  have := conjSub_mono k (h.conjSub_le (K.inv_mem hk))
  rwa [conjSub_conjSub_inv] at this

theorem invariant_iff_conjSub_le {K : Subgroup (GLV V)} {U : Submodule (ZMod 2) V} :
    Invariant K U ↔ ∀ k ∈ K, conjSub k U ≤ U := by
  refine ⟨fun h k hk => h.conjSub_le hk, fun h k hk u hu => ?_⟩
  exact h k hk (apply_mem_conjSub hu)

theorem Invariant.mono {K K' : Subgroup (GLV V)} (hK : K ≤ K') {U : Submodule (ZMod 2) V}
    (h : Invariant K' U) : Invariant K U := fun k hk => h k (hK hk)

theorem Invariant.sup_subgroup {K K' : Subgroup (GLV V)} {U : Submodule (ZMod 2) V}
    (h : Invariant K U) (h' : Invariant K' U) : Invariant (K ⊔ K') U := by
  have hle : K ⊔ K' ≤ stabilizerOf ⊤ U :=
    sup_le (fun k hk => ⟨Subgroup.mem_top _, h.conjSub_eq hk⟩)
      (fun k hk => ⟨Subgroup.mem_top _, h'.conjSub_eq hk⟩)
  intro k hk u hu
  have := (hle hk).2
  rw [← this]
  exact apply_mem_conjSub hu

theorem invariant_bot (K : Subgroup (GLV V)) : Invariant K (⊥ : Submodule (ZMod 2) V) := by
  intro k _ u hu
  rw [Submodule.mem_bot] at hu ⊢
  rw [hu, map_zero]

theorem invariant_top (K : Subgroup (GLV V)) : Invariant K (⊤ : Submodule (ZMod 2) V) :=
  fun _ _ _ _ => Submodule.mem_top

theorem Invariant.inf {K : Subgroup (GLV V)} {U U' : Submodule (ZMod 2) V} (h : Invariant K U)
    (h' : Invariant K U') : Invariant K (U ⊓ U') :=
  fun k hk u hu => ⟨h k hk u hu.1, h' k hk u hu.2⟩

theorem Invariant.sup {K : Subgroup (GLV V)} {U U' : Submodule (ZMod 2) V} (h : Invariant K U)
    (h' : Invariant K U') : Invariant K (U ⊔ U') := by
  rw [invariant_iff_conjSub_le] at *
  intro k hk
  rw [conjSub_sup]
  exact sup_le_sup (h k hk) (h' k hk)

theorem invariant_iSup {K : Subgroup (GLV V)} {ι : Sort*} {U : ι → Submodule (ZMod 2) V}
    (h : ∀ i, Invariant K (U i)) : Invariant K (⨆ i, U i) := by
  rw [invariant_iff_conjSub_le]
  intro k hk
  rw [conjSub, Submodule.map_iSup]
  exact iSup_mono fun i => (invariant_iff_conjSub_le.1 (h i)) k hk

theorem invariant_sSup {K : Subgroup (GLV V)} {S : Set (Submodule (ZMod 2) V)}
    (h : ∀ U ∈ S, Invariant K U) : Invariant K (sSup S) := by
  rw [sSup_eq_iSup]
  exact invariant_iSup fun U => invariant_iSup fun hU => h U hU

theorem Invariant.conj_of_normal {N Γ : Subgroup (GLV V)}
    (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) {U : Submodule (ZMod 2) V} (hU : Invariant N U)
    {γ : GLV V} (hγ : γ ∈ Γ) : Invariant N (conjSub γ U) := by
  rintro n hn _ ⟨u, hu, rfl⟩
  have h1 : γ⁻¹ * n * γ⁻¹⁻¹ ∈ N := hN γ⁻¹ (Γ.inv_mem hγ) n hn
  have h2 : (γ⁻¹ * n * γ) u ∈ U := by
    simpa using hU _ h1 u hu
  refine ⟨_, h2, ?_⟩
  simp [mul_assoc]

theorem IsIrr.ne_bot {K : Subgroup (GLV V)} {U : Submodule (ZMod 2) V} (h : IsIrr K U) : U ≠ ⊥ :=
  (bot_lt_iff_ne_bot.1 h.2.1)

theorem IsIrr.eq_bot_or_eq {K : Subgroup (GLV V)} {U : Submodule (ZMod 2) V} (h : IsIrr K U)
    {J : Submodule (ZMod 2) V} (hJ : Invariant K J) (hJU : J ≤ U) : J = ⊥ ∨ J = U :=
  h.2.2 J hJ bot_le hJU

theorem IsIrr.conj_of_normal {N Γ : Subgroup (GLV V)}
    (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) {U : Submodule (ZMod 2) V} (hU : IsIrr N U)
    {γ : GLV V} (hγ : γ ∈ Γ) : IsIrr N (conjSub γ U) := by
  refine ⟨hU.1.conj_of_normal hN hγ, bot_lt_iff_ne_bot.2 ?_, fun J hJ _ hJU => ?_⟩
  · rw [Ne, conjSub_eq_bot_iff]
    exact hU.ne_bot
  · have hJ' : Invariant N (conjSub γ⁻¹ J) := hJ.conj_of_normal hN (Γ.inv_mem hγ)
    have hle : conjSub γ⁻¹ J ≤ U := by
      have := conjSub_mono γ⁻¹ hJU
      rwa [conjSub_inv_conjSub] at this
    rcases hU.eq_bot_or_eq hJ' hle with h | h
    · left
      have := congrArg (conjSub γ) h
      rwa [conjSub_conjSub_inv, conjSub_bot] at this
    · right
      have := congrArg (conjSub γ) h
      rwa [conjSub_conjSub_inv] at this

theorem IsIrr.conj_eq_or_inf_eq_bot [Finite V] {N Γ : Subgroup (GLV V)}
    (hN : ∀ γ ∈ Γ, ∀ n ∈ N, γ * n * γ⁻¹ ∈ N) {I : Submodule (ZMod 2) V} (hI : IsIrr N I)
    {γ : GLV V} (hγ : γ ∈ Γ) : conjSub γ I = I ∨ conjSub γ I ⊓ I = ⊥ := by
  have hinv : Invariant N (conjSub γ I ⊓ I) := (hI.1.conj_of_normal hN hγ).inf hI.1
  rcases hI.eq_bot_or_eq hinv inf_le_right with h | h
  · exact Or.inr h
  · left
    have hle : I ≤ conjSub γ I := by
      have := (inf_le_left : conjSub γ I ⊓ I ≤ conjSub γ I)
      rwa [h] at this
    exact (Submodule.eq_of_le_of_finrank_eq hle (finrank_conjSub γ I).symm).symm

theorem mem_fixedSpace_iff {K : Subgroup (GLV V)} {v : V} :
    v ∈ fixedSpace K ↔ ∀ k ∈ K, k v = v := Iff.rfl

theorem fixedSpace_anti {K K' : Subgroup (GLV V)} (h : K ≤ K') : fixedSpace K' ≤ fixedSpace K :=
  fun _ hv k hk => hv k (h hk)

theorem fixedSpace_eq_top_iff {K : Subgroup (GLV V)} : fixedSpace K = ⊤ ↔ ∀ k ∈ K, k = 1 := by
  constructor
  · intro h k hk
    ext v
    exact (mem_fixedSpace_iff.1 (h ▸ Submodule.mem_top : v ∈ fixedSpace K)) k hk
  · intro h
    rw [eq_top_iff]
    intro v _ k hk
    rw [h k hk]
    rfl

theorem invariant_fixedSpace {K K' : Subgroup (GLV V)}
    (hn : ∀ k' ∈ K', ∀ k ∈ K, k' * k * k'⁻¹ ∈ K) : Invariant K' (fixedSpace K) := by
  intro k' hk' v hv k hk
  have h1 : k'⁻¹ * k * k'⁻¹⁻¹ ∈ K := hn k'⁻¹ (K'.inv_mem hk') k hk
  have h2 := hv _ h1
  have : k (k' v) = k' ((k'⁻¹ * k * k') v) := by simp [mul_assoc]
  rw [this]
  simp only [inv_inv] at h1 h2
  rw [h2]

theorem sub_mem_commSpace {K : Subgroup (GLV V)} {U : Submodule (ZMod 2) V} {k : GLV V}
    (hk : k ∈ K) {u : V} (hu : u ∈ U) : k u - u ∈ commSpace K U :=
  Submodule.subset_span ⟨k, hk, u, hu, rfl⟩

theorem commSpace_le_iff {K : Subgroup (GLV V)} {U U' : Submodule (ZMod 2) V} :
    commSpace K U ≤ U' ↔ ∀ k ∈ K, ∀ u ∈ U, k u - u ∈ U' := by
  constructor
  · intro h k hk u hu
    exact h (sub_mem_commSpace hk hu)
  · intro h
    refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, u, hu, rfl⟩
    exact h k hk u hu

theorem commSpace_le_of_invariant {K : Subgroup (GLV V)} {U : Submodule (ZMod 2) V}
    (h : Invariant K U) : commSpace K U ≤ U :=
  commSpace_le_iff.2 fun k hk u hu => U.sub_mem (h k hk u hu) hu

theorem commSpace_mono {K K' : Subgroup (GLV V)} {U U' : Submodule (ZMod 2) V} (hK : K ≤ K')
    (hU : U ≤ U') : commSpace K U ≤ commSpace K' U' :=
  commSpace_le_iff.2 fun _ hk _ hu => sub_mem_commSpace (hK hk) (hU hu)

theorem commSpace_eq_bot_iff {K : Subgroup (GLV V)} {U : Submodule (ZMod 2) V} :
    commSpace K U = ⊥ ↔ ∀ k ∈ K, ∀ u ∈ U, k u = u := by
  rw [← le_bot_iff, commSpace_le_iff]
  simp [sub_eq_zero]

theorem invariant_commSpace {K K' : Subgroup (GLV V)}
    (hn : ∀ k' ∈ K', ∀ k ∈ K, k' * k * k'⁻¹ ∈ K) {U : Submodule (ZMod 2) V}
    (hU : Invariant K' U) : Invariant K' (commSpace K U) := by
  intro k' hk' w hw
  have : commSpace K U ≤ (commSpace K U).comap (k' : V →ₗ[ZMod 2] V) := by
    refine commSpace_le_iff.2 fun k hk u hu => ?_
    show k' (k u - u) ∈ commSpace K U
    have e : k' (k u - u) = (k' * k * k'⁻¹) (k' u) - k' u := by simp [mul_assoc]
    rw [e]
    exact sub_mem_commSpace (hn k' hk' k hk) (hU k' hk' u hu)
  exact this hw


theorem mem_centralizerOn {K : Subgroup (GLV V)} {I : Submodule (ZMod 2) V} {k : GLV V} :
    k ∈ centralizerOn K I ↔ k ∈ K ∧ ∀ u ∈ I, k u = u := Iff.rfl

theorem faithfulOn_iff {K : Subgroup (GLV V)} {I : Submodule (ZMod 2) V} :
    FaithfulOn K I ↔ ∀ k ∈ K, (∀ u ∈ I, k u = u) → k = 1 := by
  rw [FaithfulOn, Subgroup.eq_bot_iff_forall]
  exact ⟨fun h k hk hku => h k ⟨hk, hku⟩, fun h k hk => h k hk.1 hk.2⟩

@[expose] noncomputable def restrictEquiv (k : GLV V) (I : Submodule (ZMod 2) V)
    (h : conjSub k I = I) : I ≃ₗ[ZMod 2] I :=
  LinearEquiv.ofSubmodules k I I h

@[simp] theorem coe_restrictEquiv (k : GLV V) (I : Submodule (ZMod 2) V) (h : conjSub k I = I)
    (i : I) : ((restrictEquiv k I h i : I) : V) = k (i : V) := rfl

@[expose] noncomputable def restrictHom (K : Subgroup (GLV V)) (I : Submodule (ZMod 2) V)
    (hI : Invariant K I) : K →* (I ≃ₗ[ZMod 2] I) where
  toFun k := restrictEquiv k I (hI.conjSub_eq k.2)
  map_one' := by
    ext i
    rfl
  map_mul' a b := by
    ext i
    rfl

@[simp] theorem coe_restrictHom {K : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}
    {hI : Invariant K I} (k : K) (i : I) :
    ((restrictHom K I hI k i : I) : V) = (k : GLV V) (i : V) := rfl

theorem restrictHom_eq_one_iff {K : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}
    {hI : Invariant K I} {k : K} :
    restrictHom K I hI k = 1 ↔ ∀ i ∈ I, (k : GLV V) i = i := by
  constructor
  · intro h i hi
    have := congrArg (fun e : I ≃ₗ[ZMod 2] I => ((e ⟨i, hi⟩ : I) : V)) h
    simpa using this
  · intro h
    ext i
    exact h i i.2

@[expose] def linToPerm (I : Type*) [AddCommGroup I] [Module (ZMod 2) I] :
    (I ≃ₗ[ZMod 2] I) →* Equiv.Perm I where
  toFun e := e.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem linToPerm_injective (I : Type*) [AddCommGroup I] [Module (ZMod 2) I] :
    Function.Injective (linToPerm I) := fun _ _ h => LinearEquiv.toEquiv_injective h

theorem isSolvable_linearEquiv_of_finrank_le_two [Finite V] (I : Submodule (ZMod 2) V)
    (h : Module.finrank (ZMod 2) I ≤ 2) : Group.IsSolvable (I ≃ₗ[ZMod 2] I) := by
  have hcard : Nat.card I ≤ 4 := by
    let _ : Fintype I := Fintype.ofFinite I
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := I)]
    calc Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) I ≤ 2 ^ 2 := by
          rw [ZMod.card]
          exact Nat.pow_le_pow_right (by norm_num) h
      _ = 4 := by norm_num
  have := Equiv.Perm.isSolvable (α := I) hcard
  exact Group.isSolvable_of_isSolvable_injective (linToPerm_injective I)

theorem le_normalClosure (Γ L : Subgroup (GLV V)) : L ≤ normalClosure Γ L := by
  intro l hl
  apply Subgroup.subset_closure
  exact ⟨1, Γ.one_mem, l, hl, by simp⟩

theorem normalClosure_le {Γ L : Subgroup (GLV V)} (hL : L ≤ Γ) : normalClosure Γ L ≤ Γ := by
  rw [normalClosure, Subgroup.closure_le]
  rintro _ ⟨γ, hγ, l, hl, rfl⟩
  exact Γ.mul_mem (Γ.mul_mem hγ (hL hl)) (Γ.inv_mem hγ)

theorem normalClosure_conj {Γ L : Subgroup (GLV V)} {γ : GLV V} (hγ : γ ∈ Γ) {h : GLV V}
    (hh : h ∈ normalClosure Γ L) : γ * h * γ⁻¹ ∈ normalClosure Γ L := by
  induction hh using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨δ, hδ, l, hl, rfl⟩ := hx
    apply Subgroup.subset_closure
    exact ⟨γ * δ, Γ.mul_mem hγ hδ, l, hl, by group⟩
  | one => simp
  | mul x y _ _ hx hy =>
    have := (normalClosure Γ L).mul_mem hx hy
    convert this using 1
    group
  | inv x _ hx =>
    have := (normalClosure Γ L).inv_mem hx
    convert this using 1
    group


theorem normalClosure_normal (Γ L : Subgroup (GLV V)) :
    ∀ γ ∈ Γ, ∀ h ∈ normalClosure Γ L, γ * h * γ⁻¹ ∈ normalClosure Γ L :=
  fun _ hγ _ hh => normalClosure_conj hγ hh

theorem IsIrr.irrPlus {H : Subgroup (GLV V)} {J : Submodule (ZMod 2) V}
    (hH : fixedSpace H = ⊥) (hJ : IsIrr H J) : IrrPlus H J := by
  have hinv : Invariant H (commSpace H J) :=
    invariant_commSpace (fun k' hk' k hk => H.mul_mem (H.mul_mem hk' hk) (H.inv_mem hk')) hJ.1
  refine ⟨hJ.1, ?_, ?_⟩
  · rcases hJ.eq_bot_or_eq hinv (commSpace_le_of_invariant hJ.1) with h | h
    · exfalso
      refine hJ.ne_bot ?_
      rw [commSpace_eq_bot_iff] at h
      rw [eq_bot_iff, ← hH]
      exact fun u hu k hk => h k hk u hu
    · exact h
  · rw [hH, bot_inf_eq]
    exact hJ.2

theorem IrrPlus.isIrr {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}
    (hH : fixedSpace H = ⊥) (hI : IrrPlus H I) : IsIrr H I := by
  refine ⟨hI.1, ?_⟩
  have := hI.2.2
  rwa [hH, bot_inf_eq] at this

theorem exists_isIrr_le [Finite V] {H : Subgroup (GLV V)} {U : Submodule (ZMod 2) V}
    (hU : Invariant H U) (hne : U ≠ ⊥) : ∃ J : Submodule (ZMod 2) V, J ≤ U ∧ IsIrr H J := by
  classical
  let S : Set ℕ := {n | ∃ J : Submodule (ZMod 2) V, J ≤ U ∧ Invariant H J ∧ J ≠ ⊥ ∧
    Module.finrank (ZMod 2) J = n}
  have hS : S.Nonempty := ⟨_, U, le_rfl, hU, hne, rfl⟩
  obtain ⟨J, hJU, hJinv, hJne, hJn⟩ := Nat.sInf_mem hS
  refine ⟨J, hJU, hJinv, bot_lt_iff_ne_bot.2 hJne, fun J' hJ' _ hJ'J => ?_⟩
  by_contra hcon
  have hne' : J' ≠ ⊥ := fun h => hcon (Or.inl h)
  have hne'' : J' ≠ J := fun h => hcon (Or.inr h)
  have hlt : Module.finrank (ZMod 2) J' < Module.finrank (ZMod 2) J :=
    Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hJ'J hne'')
  have : sInf S ≤ Module.finrank (ZMod 2) J' := Nat.sInf_le ⟨J', hJ'J.trans hJU, hJ', hne', rfl⟩
  omega

theorem exists_invariant_compl [Finite V] {H : Subgroup (GLV V)}
    (hV : sSup {J : Submodule (ZMod 2) V | IsIrr H J} = ⊤) {U : Submodule (ZMod 2) V}
    (hU : Invariant H U) : ∃ U' : Submodule (ZMod 2) V, Invariant H U' ∧ IsCompl U U' := by
  classical
  let S : Set ℕ := {n | ∃ W : Submodule (ZMod 2) V, Invariant H W ∧ Disjoint U W ∧
    Module.finrank (ZMod 2) W = n}
  have hS : S.Nonempty := ⟨0, ⊥, invariant_bot H, disjoint_bot_right, by simp⟩
  have hbdd : BddAbove S :=
    ⟨Module.finrank (ZMod 2) V, by rintro n ⟨W, -, -, rfl⟩; exact Submodule.finrank_le W⟩
  obtain ⟨W, hWinv, hWdisj, hWn⟩ := Nat.sSup_mem hS hbdd
  refine ⟨W, hWinv, hWdisj, ?_⟩
  rw [codisjoint_iff]
  by_contra hne
  have hex : ∃ J : Submodule (ZMod 2) V, IsIrr H J ∧ ¬ J ≤ U ⊔ W := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [eq_top_iff, ← hV]
    exact sSup_le fun J hJ => hcon J hJ
  obtain ⟨J, hJ, hJn⟩ := hex
  have hinf : J ⊓ (U ⊔ W) = ⊥ := by
    rcases hJ.eq_bot_or_eq (hJ.1.inf (hU.sup hWinv)) inf_le_left with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hJn
  have hdisj : Disjoint U (W ⊔ J) := by
    rw [Submodule.disjoint_def]
    intro x hxU hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    have hz' : z ∈ J ⊓ (U ⊔ W) := ⟨hz, by
      have : z = (y + z) - y := by abel
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left hxU) (Submodule.mem_sup_right hy)⟩
    rw [hinf, Submodule.mem_bot] at hz'
    rw [hz', add_zero] at hxU ⊢
    exact Submodule.disjoint_def.1 hWdisj y hxU hy
  have hlt : W < W ⊔ J := by
    refine lt_of_le_of_ne le_sup_left ?_
    intro h
    apply hJn
    calc J ≤ W ⊔ J := le_sup_right
      _ = W := h.symm
      _ ≤ U ⊔ W := le_sup_right
  have h1 : Module.finrank (ZMod 2) W < Module.finrank (ZMod 2) ↥(W ⊔ J) :=
    Submodule.finrank_lt_finrank_of_lt hlt
  have h2 : Module.finrank (ZMod 2) ↥(W ⊔ J) ≤ sSup S :=
    le_csSup hbdd ⟨W ⊔ J, hWinv.sup hJ.1, hdisj, rfl⟩
  omega

theorem iSup_conjSub_eq_top {Γ : Subgroup (GLV V)} (hΓ : IsIrr Γ ⊤) {I : Submodule (ZMod 2) V}
    (hne : I ≠ ⊥) : (⨆ γ : Γ, conjSub (γ : GLV V) I) = ⊤ := by
  have hinv : Invariant Γ (⨆ γ : Γ, conjSub (γ : GLV V) I) := by
    rw [invariant_iff_conjSub_le]
    intro δ hδ
    rw [conjSub, Submodule.map_iSup]
    refine iSup_le fun γ => ?_
    have : conjSub δ (conjSub (γ : GLV V) I) = conjSub ((⟨δ, hδ⟩ * γ : Γ) : GLV V) I :=
      (conjSub_mul δ γ I).symm
    exact (le_of_eq this).trans (le_iSup (fun γ : Γ => conjSub (γ : GLV V) I) _)
  rcases hΓ.eq_bot_or_eq hinv le_top with h | h
  · exfalso
    apply hne
    have : conjSub ((1 : Γ) : GLV V) I ≤ ⨆ γ : Γ, conjSub (γ : GLV V) I :=
      le_iSup (fun γ : Γ => conjSub (γ : GLV V) I) 1
    rw [h] at this
    simpa using this
  · exact h

theorem Invariant.orthogonal {B : LinearMap.BilinForm (ZMod 2) V} {K : Subgroup (GLV V)}
    (hB : ∀ k ∈ K, ∀ v w, B (k v) (k w) = B v w) {U : Submodule (ZMod 2) V}
    (hU : Invariant K U) : Invariant K (B.orthogonal U) := by
  intro k hk m hm
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hm ⊢
  intro n hn
  have hn' : k⁻¹ n ∈ U := hU k⁻¹ (K.inv_mem hk) n hn
  have := hm _ hn'
  rw [← hB k hk (k⁻¹ n) m] at this
  simpa using this

end G11

end CFSG.Quasithin
