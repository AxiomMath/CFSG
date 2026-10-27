module

public import CFSG.LieType.SeitzGeneration.ExcTorusSylow
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylFrameGen
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMonomialIrred

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open CFSG.LieType.SeitzGeneration

section FrameSubgroup

variable {p N : ℕ} [Fact p.Prime]

theorem frameTorus_single_pow (i : Fin N) (a : ZMod p) (k : ℕ) :
    (Multiplicative.ofAdd (Pi.single i a : Fin N → ZMod p)) ^ k =
      Multiplicative.ofAdd (Pi.single i ((k : ZMod p) * a) : Fin N → ZMod p) := by
  rw [← ofAdd_nsmul]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    simp [nsmul_eq_mul]
  · simp [Pi.single_eq_of_ne hj]

theorem frameTorus_div_update (u : ZMod p) (i : Fin N) (v : Fin N → ZMod p) :
    Multiplicative.ofAdd v * (Multiplicative.ofAdd (Function.update v i (u * v i)))⁻¹ =
      Multiplicative.ofAdd (Pi.single i ((1 - u) * v i) : Fin N → ZMod p) := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, toAdd_ofAdd]
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [Pi.add_apply, Pi.neg_apply, Function.update_self, Pi.single_eq_same]
    ring
  · simp [Function.update_of_ne hj, Pi.single_eq_of_ne hj]

theorem frameTorus_single_mem_of_scaling (u : ZMod p) (hu : u ≠ 1)
    (T : Subgroup (Multiplicative (Fin N → ZMod p)))
    (hT : ∀ (i : Fin N) (w : Multiplicative (Fin N → ZMod p)), w ∈ T →
      Multiplicative.ofAdd (Function.update (Multiplicative.toAdd w) i
        (u * Multiplicative.toAdd w i)) ∈ T)
    {w : Multiplicative (Fin N → ZMod p)} (hw : w ∈ T) {i : Fin N}
    (hi : Multiplicative.toAdd w i ≠ 0) :
    Multiplicative.ofAdd (Pi.single i (1 : ZMod p)) ∈ T := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hq := T.mul_mem hw (T.inv_mem (hT i w hw))
  have hqe := frameTorus_div_update u i (Multiplicative.toAdd w)
  rw [ofAdd_toAdd] at hqe
  rw [hqe] at hq
  have hc0 : (1 - u) * Multiplicative.toAdd w i ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr (Ne.symm hu)) hi
  have hpow : Multiplicative.ofAdd (Pi.single i (1 : ZMod p) : Fin N → ZMod p) =
      (Multiplicative.ofAdd
        (Pi.single i ((1 - u) * Multiplicative.toAdd w i) : Fin N → ZMod p)) ^
        (((1 - u) * Multiplicative.toAdd w i)⁻¹).val := by
    rw [frameTorus_single_pow, ZMod.natCast_zmod_val, inv_mul_cancel₀ hc0]
  rw [hpow]
  exact T.pow_mem hq _

theorem frameTorus_eq_top_of_single_mem (T : Subgroup (Multiplicative (Fin N → ZMod p)))
    (h : ∀ i, Multiplicative.ofAdd (Pi.single i (1 : ZMod p)) ∈ T) : T = ⊤ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  refine eq_top_iff.mpr fun w _ => ?_
  have hw : w = ∏ i, Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd w i) :
      Fin N → ZMod p) := by
    rw [← ofAdd_sum, Finset.univ_sum_single, ofAdd_toAdd]
  rw [hw]
  refine T.prod_mem fun i _ => ?_
  have : Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd w i) : Fin N → ZMod p) =
      (Multiplicative.ofAdd (Pi.single i (1 : ZMod p) : Fin N → ZMod p)) ^
        (Multiplicative.toAdd w i).val := by
    rw [frameTorus_single_pow, ZMod.natCast_zmod_val, mul_one]
  rw [this]
  exact T.pow_mem (h i) _

theorem frameTorus_eq_bot_or_top (u : ZMod p) (hu : u ≠ 1)
    (T : Subgroup (Multiplicative (Fin N → ZMod p)))
    (hT : ∀ (i : Fin N) (w : Multiplicative (Fin N → ZMod p)), w ∈ T →
      Multiplicative.ofAdd (Function.update (Multiplicative.toAdd w) i
        (u * Multiplicative.toAdd w i)) ∈ T)
    (hS : (∃ i, Multiplicative.ofAdd (Pi.single i (1 : ZMod p)) ∈ T) →
      ∀ i, Multiplicative.ofAdd (Pi.single i (1 : ZMod p)) ∈ T) :
    T = ⊥ ∨ T = ⊤ := by
  by_cases hbot : T = ⊥
  · exact Or.inl hbot
  refine Or.inr (frameTorus_eq_top_of_single_mem T (hS ?_))
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  obtain ⟨i, hi⟩ : ∃ i, Multiplicative.toAdd w i ≠ 0 := by
    by_contra h
    push Not at h
    exact hw1 (Subtype.ext (Multiplicative.toAdd.injective (funext h)))
  exact ⟨i, frameTorus_single_mem_of_scaling u hu T hT hw hi⟩

end FrameSubgroup

section FrameRange

variable {p N : ℕ} [Fact p.Prime] {R : Type} [Group R]

theorem ggWeylIrred_range_of_frame (ι : Multiplicative (Fin N → ZMod p) →* R) (u : ZMod p)
    (hu : u ≠ 1)
    (hscale : ∀ i : Fin N, ∃ m ∈ Subgroup.normalizer (ι.range : Set R),
      ∀ v : Fin N → ZMod p, m * ι (Multiplicative.ofAdd v) * m⁻¹ =
        ι (Multiplicative.ofAdd (Function.update v i (u * v i))))
    (hS : ∀ T : Subgroup (Multiplicative (Fin N → ZMod p)),
      (∀ n ∈ Subgroup.normalizer (ι.range : Set R), ∀ w ∈ T, ∀ w',
        n * ι w * n⁻¹ = ι w' → w' ∈ T) →
      (∀ (i : Fin N) (w : Multiplicative (Fin N → ZMod p)), w ∈ T →
        Multiplicative.ofAdd (Function.update (Multiplicative.toAdd w) i
          (u * Multiplicative.toAdd w i)) ∈ T) →
      (∃ i, Multiplicative.ofAdd (Pi.single i (1 : ZMod p)) ∈ T) →
        ∀ i, Multiplicative.ofAdd (Pi.single i (1 : ZMod p)) ∈ T) :
    GGWeylIrred ι.range := by
  intro E' hE' hinv
  set T : Subgroup (Multiplicative (Fin N → ZMod p)) := E'.comap ι with hTdef
  have hTinv : ∀ n ∈ Subgroup.normalizer (ι.range : Set R), ∀ w ∈ T, ∀ w',
      n * ι w * n⁻¹ = ι w' → w' ∈ T := by
    intro n hn w hw w' hww'
    have h1 := hinv n hn (ι w) hw
    rw [hww'] at h1
    exact h1
  have hscT : ∀ (i : Fin N) (w : Multiplicative (Fin N → ZMod p)), w ∈ T →
      Multiplicative.ofAdd (Function.update (Multiplicative.toAdd w) i
        (u * Multiplicative.toAdd w i)) ∈ T := by
    intro i w hw
    obtain ⟨m, hm, hmv⟩ := hscale i
    refine hTinv m hm w hw _ ?_
    have h1 := hmv (Multiplicative.toAdd w)
    rwa [ofAdd_toAdd] at h1
  rcases frameTorus_eq_bot_or_top u hu T hscT (hS T hTinv hscT) with hbot | htop
  · left
    rw [eq_bot_iff]
    intro e he
    obtain ⟨w, hw⟩ := hE' he
    have hwT : w ∈ T := by
      show ι w ∈ E'
      rw [hw]
      exact he
    rw [hbot, Subgroup.mem_bot] at hwT
    rw [Subgroup.mem_bot, ← hw, hwT, map_one]
  · right
    refine le_antisymm hE' fun e he => ?_
    obtain ⟨w, hw⟩ := he
    have hwT : w ∈ T := by
      rw [htop]
      exact Subgroup.mem_top w
    rw [← hw]
    exact hwT

end FrameRange

theorem fin_three_connected : ∀ f : Fin 3 → Fin 3, (∀ i, f i ≠ i) →
    ∀ S : Finset (Fin 3), S.Nonempty → (∀ i, i ∈ S ↔ f i ∈ S) → S = Finset.univ := by
  decide +kernel


theorem ggSCWeylIrred_of_sylowTorus_frameGen {G₀ : Type} [Group G₀] {p N : ℕ} (hp : p.Prime)
    (u : ZMod p) (hu : u ≠ 1) (s n : G₀) (hs : orderOf s = p)
    (hn : n * s * n⁻¹ = s ^ u.val) (hZ : Disjoint (Subgroup.zpowers s) (Subgroup.center G₀))
    {R : Type} [Group R] [Finite R] (hT : SylowTorus R p N) (ρ : Fin N → G₀ →* R)
    (hρ : ∀ i, Function.Injective (ρ i))
    (hc : ∀ i j, i ≠ j → ∀ A B, Commute (ρ i A) (ρ j B))
    (hmove : ∀ i : Fin N, ∃ j : Fin N, j ≠ i ∧ ∃ (g : R) (t : ZMod p), t ≠ 0 ∧
      g * ρ i s * g⁻¹ = ρ j (s ^ t.val))
    (hconn : ∀ f : Fin N → Fin N, (∀ i, f i ≠ i) → ∀ S : Finset (Fin N), S.Nonempty →
      (∀ i, i ∈ S ↔ f i ∈ S) → S = Finset.univ)
    (r : ℕ) : GGSCWeylIrred p r R := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨e, m, he_inj, he_single, hm_conj⟩ :=
    exists_frameTorus_of_commutingFrames hp u s n hs hn hZ ρ hρ hc
  let E : Subgroup R := e.range
  have hE : IsElemAbelian p E := by
    change IsElemAbelian p e.range
    refine ⟨IsMulCommutative.of_comm fun a b => Subtype.ext ?_, fun x hx => ?_⟩
    · obtain ⟨v, hv⟩ := a.2
      obtain ⟨w, hw⟩ := b.2
      show (a : R) * (b : R) = (b : R) * (a : R)
      rw [← hv, ← hw, ← map_mul, ← map_mul]
      congr 1
      exact mul_comm v w
    · obtain ⟨v, hv⟩ := hx
      rw [← hv, ← map_pow, ← ofAdd_toAdd v, ← ofAdd_nsmul,
        ZModModule.char_nsmul_eq_zero, ofAdd_zero, map_one]
  have hcardE : Nat.card E = p ^ N := by
    change Nat.card e.range = p ^ N
    rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective he_inj, Subgroup.card_top,
      Nat.card_eq_fintype_card, Fintype.card_multiplicative, Fintype.card_fun, ZMod.card,
      Fintype.card_fin]
  have hmN : ∀ i, m i ∈ Subgroup.normalizer (E : Set R) := fun i =>
    frameScale_mem_normalizer_range u e m hm_conj i
  have hfus : ∀ i : Fin N, ∃ j : Fin N, j ≠ i ∧ ∃ t : ZMod p, t ≠ 0 ∧
      ∃ n' ∈ Subgroup.normalizer (E : Set R),
        n' * e (Multiplicative.ofAdd (Pi.single i (1 : ZMod p))) * n'⁻¹ =
          e (Multiplicative.ofAdd (Pi.single j t)) := by
    intro i
    obtain ⟨j, hji, g, t, ht, hgt⟩ := hmove i
    obtain ⟨P, hEP, hPcomm, hPΩ⟩ := exists_sylow_of_sylowTorus_elemAbelian hp hT hE hcardE
    have hx : e (Multiplicative.ofAdd (Pi.single i (1 : ZMod p))) ∈ (P : Subgroup R) :=
      hEP ⟨_, rfl⟩
    have hy : e (Multiplicative.ofAdd (Pi.single j t)) ∈ (P : Subgroup R) := hEP ⟨_, rfl⟩
    have hg : g * e (Multiplicative.ofAdd (Pi.single i (1 : ZMod p))) * g⁻¹ =
        e (Multiplicative.ofAdd (Pi.single j t)) := by
      rw [he_single, he_single, ZMod.val_one, pow_one]
      exact hgt
    obtain ⟨n', hnP, hnconj⟩ :=
      exists_mem_normalizer_conj_of_commutative_sylow P hPcomm hx hy hg
    exact ⟨j, hji, t, ht, n', ggFrame_mem_normalizer_of_le_and_pow_eq_one hEP hE.2 hPΩ hnP,
      hnconj⟩
  have hirr : GGWeylIrred E := by
    refine ggWeylIrred_range_of_frame e u hu (fun i => ⟨m i, hmN i, hm_conj i⟩) ?_
    intro T hTinv hscT ⟨i₀, hi₀⟩
    choose f hf t ht n' hn' hn'eq using hfus
    have hiff : ∀ i, Multiplicative.ofAdd (Pi.single i (1 : ZMod p)) ∈ T ↔
        Multiplicative.ofAdd (Pi.single (f i) (1 : ZMod p)) ∈ T := by
      intro i
      constructor
      · intro hi
        have h1 := hTinv (n' i) (hn' i) _ hi _ (hn'eq i)
        exact frameTorus_single_mem_of_scaling u hu T hscT h1
          (by simpa using ht i)
      · intro hi
        have h1 : Multiplicative.ofAdd (Pi.single (f i) (t i)) ∈ T := by
          have := T.pow_mem hi (t i).val
          rwa [frameTorus_single_pow, ZMod.natCast_zmod_val, mul_one] at this
        refine hTinv (n' i)⁻¹ (Subgroup.inv_mem _ (hn' i)) _ h1 _ ?_
        rw [← hn'eq i]
        group
    have hS := hconn f hf (Finset.univ.filter fun i =>
      Multiplicative.ofAdd (Pi.single i (1 : ZMod p)) ∈ T) ⟨i₀, by simpa using hi₀⟩
      (fun i => by simpa using hiff i)
    intro i
    have hmem : i ∈ Finset.univ.filter fun i =>
        Multiplicative.ofAdd (Pi.single i (1 : ZMod p)) ∈ T := by
      rw [hS]
      exact Finset.mem_univ i
    exact (Finset.mem_filter.mp hmem).2
  intro E₁ hE₁ _ _ hsc
  obtain ⟨c, hcE⟩ := exists_conj_eq_of_selfCentralizing_of_sylowTorus hp hT hE hcardE hE₁ hsc
  rw [hcE]
  exact ggWeylIrred_map (MulAut.conj c) hirr

end CFSG.StandardType

end
