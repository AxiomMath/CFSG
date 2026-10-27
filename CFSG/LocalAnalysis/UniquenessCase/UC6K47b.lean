module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K47a
public import CFSG.LocalAnalysis.PreuniquenessRankFour.HyperplaneGeneration

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup

section Core

variable {E : Type} [CommGroup E] [Finite E] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def Wsp (σ : E →* Module.End (ZMod 2) V) (K : Subgroup E) : Submodule (ZMod 2) V where
  carrier := {v | nrmAll σ v = 0 ∧ ∀ s ∈ K, σ s v = v}
  add_mem' {a b} ha hb := ⟨by rw [map_add, ha.1, hb.1, add_zero],
    fun s hs => by rw [map_add, ha.2 s hs, hb.2 s hs]⟩
  zero_mem' := ⟨map_zero _, fun s _ => map_zero _⟩
  smul_mem' c v hv := ⟨by rw [map_smul, hv.1, smul_zero], fun s hs => by rw [map_smul, hv.2 s hs]⟩

theorem nrmAll_eq_nrmOp_top_uc6 (σ : E →* Module.End (ZMod 2) V) :
    nrmAll σ = nrmOp σ ⊤ := by
  haveI : Fintype E := Fintype.ofFinite E
  haveI : Fintype ↥(⊤ : Subgroup E) := Fintype.ofFinite _
  rw [nrmAll_eq_sum_uc6, nrmOp_eq_sum_uc6]
  exact (Fintype.sum_equiv (Subgroup.topEquiv (G := E)).toEquiv (fun s : ↥(⊤ : Subgroup E) => σ (s : E))
    (fun e : E => σ e) (fun s => rfl)).symm

theorem σ_mul_nrmAll_uc6 (σ : E →* Module.End (ZMod 2) V) (g : E) :
    σ g * nrmAll σ = nrmAll σ := by
  rw [nrmAll_eq_nrmOp_top_uc6]
  exact σ_mul_nrmOp_uc6 σ ⊤ (Subgroup.mem_top g)

theorem nrmAll_mul_σ_uc6 (σ : E →* Module.End (ZMod 2) V) (g : E) :
    nrmAll σ * σ g = nrmAll σ := by
  rw [nrmAll_eq_nrmOp_top_uc6]
  exact nrmOp_mul_σ_uc6 σ ⊤ (Subgroup.mem_top g)

theorem nrmAll_mul_nrmAll_uc6 (σ : E →* Module.End (ZMod 2) V) (hE : Odd (Nat.card E)) :
    nrmAll σ * nrmAll σ = nrmAll σ := by
  rw [nrmAll_eq_nrmOp_top_uc6]
  exact nrmOp_mul_nrmOp_uc6 σ ⊤ (by rwa [Subgroup.card_top])

theorem nrmAll_fixed_uc6 (σ : E →* Module.End (ZMod 2) V) (hE : Odd (Nat.card E)) {v : V}
    (hv : ∀ s, σ s v = v) : nrmAll σ v = v := by
  rw [nrmAll_eq_nrmOp_top_uc6]
  exact nrmOp_fixed_uc6 σ ⊤ (by rwa [Subgroup.card_top]) (fun s _ => hv s)

theorem σ_comm_nrmAll_uc6 (σ : E →* Module.End (ZMod 2) V) (g : E) (v : V) :
    nrmAll σ (σ g v) = σ g (nrmAll σ v) := by
  have h1 := congrArg (fun f : Module.End (ZMod 2) V => f v) (nrmAll_mul_σ_uc6 σ g)
  have h2 := congrArg (fun f : Module.End (ZMod 2) V => f v) (σ_mul_nrmAll_uc6 σ g)
  simp only [Module.End.mul_apply] at h1 h2
  rw [h1, h2]

theorem T_comm_nrmAll_uc6 (σ : E →* Module.End (ZMod 2) V) (T : Module.End (ZMod 2) V)
    (α : MulAut E) (hTα : ∀ e, T * σ e = σ (α e) * T) (v : V) :
    nrmAll σ (T v) = T (nrmAll σ v) := by
  haveI : Fintype E := Fintype.ofFinite E
  rw [nrmAll_eq_sum_uc6]
  simp only [LinearMap.sum_apply]
  have h : ∀ e : E, σ (α e) (T v) = T (σ e v) := fun e => by
    have := congrArg (fun f : Module.End (ZMod 2) V => f v) (hTα e)
    simpa using this.symm
  have h2 : ∑ e : E, σ e (T v) = ∑ e : E, σ (α e) (T v) :=
    (Fintype.sum_equiv α.toEquiv (fun e => σ (α e) (T v)) (fun e => σ e (T v)) (fun e => rfl)).symm
  rw [h2, map_sum]
  exact Finset.sum_congr rfl fun e _ => h e

theorem decomposition_uc6 (σ : E →* Module.End (ZMod 2) V) {q : ℕ} (hq : q.Prime)
    (hexp : ∀ e : E, e ^ q = 1) (hE : Odd (Nat.card E)) {v : V} (hv : nrmAll σ v = 0) :
    v ∈ ⨆ K : {K : Subgroup E // K.index = q}, Wsp σ K.1 := by
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero (Nat.card E : ZMod 2) := ⟨by
    intro h
    have := (ZMod.natCast_eq_zero_iff (Nat.card E) 2).1 h
    exact (Nat.not_even_iff_odd.2 hE) (even_iff_two_dvd.2 this)⟩
  have hsum := CFSG.PreuniquenessRankFour.Helpers.coprime_abelian_representation_prime_fixedSpaces
    (coefficient := ZMod 2) (space := V) (acting := E) q σ hexp
  let P : Module.End (ZMod 2) V := 1 - nrmAll σ
  have hPv : P v = v := by simp [P, hv]
  have hPmem : ∀ w, nrmAll σ (P w) = 0 := fun w => by
    simp only [P, LinearMap.sub_apply, Module.End.one_apply, map_sub]
    have := congrArg (fun f : Module.End (ZMod 2) V => f w) (nrmAll_mul_nrmAll_uc6 σ hE)
    simp only [Module.End.mul_apply] at this
    rw [this, sub_self]
  have hle : Submodule.map P ⊤ ≤ ⨆ K : {K : Subgroup E // K.index = q}, Wsp σ K.1 := by
    rw [← hsum, sSup_eq_iSup', Submodule.map_iSup]
    refine iSup_le fun W => ?_
    obtain ⟨K, hKidx, hKfix⟩ := W.2
    rintro _ ⟨w, hw, rfl⟩
    rcases hKidx with h1 | h1
    · have hKtop : K = ⊤ := Subgroup.index_eq_one.1 h1
      have hall : ∀ s, σ s w = w := fun s => hKfix s (hKtop ▸ Subgroup.mem_top s) w hw
      have : P w = 0 := by simp [P, nrmAll_fixed_uc6 σ hE hall]
      rw [this]
      exact Submodule.zero_mem _
    · refine Submodule.mem_iSup_of_mem (⟨K, h1⟩ : {K : Subgroup E // K.index = q}) ?_
      refine ⟨hPmem w, fun s hs => ?_⟩
      have h3 : σ s (nrmAll σ w) = nrmAll σ w := by
        have := congrArg (fun f : Module.End (ZMod 2) V => f w) (σ_mul_nrmAll_uc6 σ s)
        simpa using this
      simp only [P, LinearMap.sub_apply, Module.End.one_apply, map_sub]
      rw [hKfix s hs w hw, h3]
  have := hle (Submodule.mem_map_of_mem (f := P) (Submodule.mem_top (x := v)))
  rwa [hPv] at this

theorem odd_card_hyp_uc6 {q : ℕ} (hE : Odd (Nat.card E)) {K : Subgroup E} (hK : K.index = q) :
    Odd (Nat.card K) := by
  have h := Subgroup.card_mul_index K
  rw [hK] at h
  rw [← h] at hE
  exact (Nat.odd_mul.1 hE).1

theorem exists_second_uc6 (σ : E →* Module.End (ZMod 2) V) (hE : Odd (Nat.card E))
    {K : Subgroup E} {u : V} (hu : u ∈ Wsp σ K) (hu0 : u ≠ 0) :
    ∃ u' ∈ Wsp σ K, u' ≠ 0 ∧ u' ≠ u := by
  obtain ⟨hu1, hu2⟩ := hu
  have hex : ∃ e : E, σ e u ≠ u := by
    by_contra hcon
    push Not at hcon
    have := nrmAll_fixed_uc6 σ hE hcon
    rw [hu1] at this
    exact hu0 this.symm
  obtain ⟨e, he⟩ := hex
  refine ⟨σ e u, ⟨?_, fun s hs => ?_⟩, ?_, he⟩
  · rw [σ_comm_nrmAll_uc6, hu1, map_zero]
  · have : σ s (σ e u) = σ e (σ s u) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
    rw [this, hu2 s hs]
  · intro h0
    apply hu0
    have : σ e⁻¹ (σ e u) = u := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    rw [← this, h0, map_zero]

theorem exists_pow_pow_eq_uc6 (α : MulAut E) {r : ℕ} (hr : r.Prime) (hαr : α ^ r = 1) {i : ℕ}
    (hi0 : 0 < i) (hir : i < r) : ∃ j : ℕ, (α ^ i) ^ j = α := by
  have hcop : Nat.Coprime i r :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hr).2 (Nat.not_dvd_of_pos_of_lt hi0 hir))
  obtain ⟨j, hj⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr.one_lt
  refine ⟨j, ?_⟩
  rw [← pow_mul, pow_eq_pow_mod (i * j) hαr, hj.2, pow_one]

theorem exists_not_mem_pow_uc6 (α : MulAut E) {r : ℕ} (hr : r.Prime) (hαr : α ^ r = 1)
    {K : Subgroup E} (hK : ∃ k ∈ K, α k ∉ K) {i : ℕ} (hi0 : 0 < i) (hir : i < r) :
    ∃ k ∈ K, (α ^ i) k ∉ K := by
  by_contra hcon
  push Not at hcon
  have hj : ∀ j : ℕ, ∀ k ∈ K, ((α ^ i) ^ j) k ∈ K := by
    intro j
    induction j with
    | zero => intro k hk; simpa using hk
    | succ j ih =>
      intro k hk
      rw [pow_succ', MulAut.mul_apply]
      exact hcon _ (ih k hk)
  obtain ⟨j, hαj⟩ := exists_pow_pow_eq_uc6 α hr hαr hi0 hir
  obtain ⟨k, hkK, hk⟩ := hK
  exact hk (hαj ▸ hj j k hkK)

theorem regular_case_uc6 (σ : E →* Module.End (ZMod 2) V) (hE : Odd (Nat.card E)) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hexp : ∀ e : E, e ^ q = 1) (T : Module.End (ZMod 2) V) {r : ℕ}
    (hr : r.Prime) (α : MulAut E) (hαr : α ^ r = 1) (hTα : ∀ e, T * σ e = σ (α e) * T)
    {K : Subgroup E} (hK : K.index = q) (hKns : ∃ k ∈ K, α k ∉ K) {v : V} (hv : v ∈ Wsp σ K)
    (hv0 : v ≠ 0) : (∑ i ∈ Finset.range r, T ^ i) v ≠ 0 := by
  haveI : Fintype E := Fintype.ofFinite E
  have hKodd : Odd (Nat.card K) := odd_card_hyp_uc6 hE hK
  have hTi : ∀ j : ℕ, nrmAll σ ((T ^ j) v) = 0 := by
    intro j
    induction j with
    | zero => simpa using hv.1
    | succ j ih =>
      rw [pow_succ', Module.End.mul_apply, T_comm_nrmAll_uc6 σ T α hTα, ih, map_zero]
  have hnrm : nrmOp σ K ((∑ i ∈ Finset.range r, T ^ i) v) = v := by
    rw [LinearMap.sum_apply, map_sum, Finset.sum_eq_single 0]
    · simpa using nrmOp_fixed_uc6 σ K hKodd hv.2
    · intro i hi hi0
      obtain ⟨k, hkK, hk⟩ := exists_not_mem_pow_uc6 α hr hαr hKns (Nat.pos_of_ne_zero hi0)
        (Finset.mem_range.1 hi)
      refine nrmOp_eq_zero_of_fixed_uc6 σ hq hq2 hexp K hK hk (u := (T ^ i) v) ?_ (hTi i)
      have := congrArg (fun f : Module.End (ZMod 2) V => f v) (pow_mul_σ_uc6 σ T α hTα i k)
      simp only [Module.End.mul_apply] at this
      rw [← this, hv.2 k hkK]
    · intro h0
      exact absurd (Finset.mem_range.2 hr.pos) h0
  intro h0
  rw [h0, map_zero] at hnrm
  exact hv0 hnrm.symm

theorem fixed_case_uc6 (σ : E →* Module.End (ZMod 2) V) (hE : Odd (Nat.card E))
    (T : Module.End (ZMod 2) V) {r : ℕ} (hr : r.Prime) (hTr : T ^ r = 1) (α : MulAut E)
    (hTα : ∀ e, T * σ e = σ (α e) * T)
    (hfix : ∀ i, 0 < i → i < r → ∀ y, (α ^ i) y = y → y = 1)
    {K : Subgroup E} (hKst : ∀ k ∈ K, α k ∈ K) (hne : Wsp σ K ≠ ⊥) :
    ∃ a ∈ Wsp σ K, a ≠ 0 ∧ T a = a := by
  haveI : Fintype E := Fintype.ofFinite E
  have hsurj : ∀ s ∈ K, ∃ e ∈ K, α e = s := by
    let f : ↥K → ↥K := fun k => ⟨α k, hKst k k.2⟩
    have hinj : Function.Injective f := fun a b h =>
      Subtype.ext (α.injective (congrArg Subtype.val h))
    intro s hs
    obtain ⟨e, he⟩ := Finite.injective_iff_surjective.1 hinj ⟨s, hs⟩
    exact ⟨e, e.2, congrArg Subtype.val he⟩
  refine exists_fixed_vector_uc6 σ hE T α r hr.pos hTr hTα hfix (Wsp σ K) ?_ ?_
    (fun w hw => hw.1) hne
  · intro e w hw
    refine ⟨by rw [σ_comm_nrmAll_uc6, hw.1, map_zero], fun s hs => ?_⟩
    have : σ s (σ e w) = σ e (σ s w) := by
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, mul_comm]
    rw [this, hw.2 s hs]
  · intro w hw
    refine ⟨by rw [T_comm_nrmAll_uc6 σ T α hTα, hw.1, map_zero], fun s hs => ?_⟩
    obtain ⟨e, heK, rfl⟩ := hsurj s hs
    have := congrArg (fun f : Module.End (ZMod 2) V => f w) (hTα e)
    simp only [Module.End.mul_apply] at this
    rw [← this, hw.2 e heK]

theorem exists_mem_diff_uc6 {q : ℕ} (hq : q.Prime) {K₁ K₂ : Subgroup E} (h1 : K₁.index = q)
    (h2 : K₂.index = q) (hne : K₁ ≠ K₂) : ∃ y ∈ K₂, y ∉ K₁ := by
  by_contra hcon
  push Not at hcon
  apply hne
  have hc1 := Subgroup.card_mul_index K₁
  have hc2 := Subgroup.card_mul_index K₂
  rw [h1] at hc1
  rw [h2] at hc2
  have hcard : Nat.card K₁ = Nat.card K₂ :=
    Nat.eq_of_mul_eq_mul_right hq.pos (hc1.trans hc2.symm)
  exact (Subgroup.eq_of_le_of_card_ge (fun y hy => hcon y hy) (le_of_eq hcard)).symm

theorem exists_two_fixed_core_uc6 (σ : E →* Module.End (ZMod 2) V) (hσ : Function.Injective σ)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hexp : ∀ e : E, e ^ q = 1) (hE : Odd (Nat.card E))
    (hbig : q < Nat.card E) {r : ℕ} (hr : r.Prime) (T : Module.End (ZMod 2) V) (hTr : T ^ r = 1)
    (α : MulAut E) (hαr : α ^ r = 1) (hTα : ∀ e, T * σ e = σ (α e) * T)
    (hfix : ∀ e, α e = e → e = 1) :
    ∃ a b : V, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ T a = a ∧ T b = b := by
  by_contra hcon
  have hC : ∀ a b : V, a ≠ 0 → b ≠ 0 → a ≠ b → T a = a → T b = b → False :=
    fun a b h1 h2 h3 h4 h5 => hcon ⟨a, b, h1, h2, h3, h4, h5⟩
  have hfixi : ∀ i, 0 < i → i < r → ∀ y, (α ^ i) y = y → y = 1 := by
    intro i hi0 hir y hy
    apply hfix
    obtain ⟨j, hj⟩ := exists_pow_pow_eq_uc6 α hr hαr hi0 hir
    have hall : ∀ n : ℕ, ((α ^ i) ^ n) y = y := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ', MulAut.mul_apply, ih, hy]
    rw [← hj]
    exact hall j
  have hTND : ∀ w, T ((∑ i ∈ Finset.range r, T ^ i) w) = (∑ i ∈ Finset.range r, T ^ i) w := by
    intro w
    have := congrArg (fun f : Module.End (ZMod 2) V => f w) (T_mul_sum_uc6 T r hTr)
    simpa using this
  haveI : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (lt_trans hq.one_lt hbig)
  obtain ⟨e, he1⟩ : ∃ e : E, e ≠ 1 := exists_ne 1
  have hσe : σ e ≠ 1 := fun h => he1 (hσ (by rw [h, map_one]))
  obtain ⟨v, hv⟩ : ∃ v, σ e v ≠ v := by
    by_contra h
    push Not at h
    exact hσe (LinearMap.ext fun w => by simpa using h w)
  have hσN : ∀ g : E, ∀ w, σ g (nrmAll σ w) = nrmAll σ w := fun g w => by
    have := congrArg (fun f : Module.End (ZMod 2) V => f w) (σ_mul_nrmAll_uc6 σ g)
    simpa using this
  have hNN : ∀ w, nrmAll σ (nrmAll σ w) = nrmAll σ w := fun w => by
    have := congrArg (fun f : Module.End (ZMod 2) V => f w) (nrmAll_mul_nrmAll_uc6 σ hE)
    simpa using this
  have hproj : ∀ w, nrmAll σ (w - nrmAll σ w) = 0 := fun w => by
    rw [map_sub, hNN, sub_self]
  have hv'ne : v - nrmAll σ v ≠ 0 := by
    intro h0
    have h1 : v = nrmAll σ v := sub_eq_zero.1 h0
    apply hv
    calc σ e v = σ e (nrmAll σ v) := by rw [← h1]
      _ = nrmAll σ v := hσN e v
      _ = v := h1.symm
  have hv'mem := decomposition_uc6 σ hq hexp hE (hproj v)
  obtain ⟨K₀, hK₀⟩ : ∃ K : {K : Subgroup E // K.index = q}, Wsp σ K.1 ≠ ⊥ := by
    by_contra hcon'
    push Not at hcon'
    have : (⨆ K : {K : Subgroup E // K.index = q}, Wsp σ K.1) = ⊥ := iSup_eq_bot.2 hcon'
    rw [this] at hv'mem
    exact hv'ne ((Submodule.mem_bot _).1 hv'mem)
  have htwo : ∃ K₁ K₂ : {K : Subgroup E // K.index = q}, K₁ ≠ K₂ ∧ Wsp σ K₁.1 ≠ ⊥ ∧
      Wsp σ K₂.1 ≠ ⊥ := by
    by_contra h2
    push Not at h2
    have hbot : ∀ K : {K : Subgroup E // K.index = q}, K ≠ K₀ → Wsp σ K.1 = ⊥ :=
      fun K hK => h2 K₀ K (Ne.symm hK) hK₀
    have hsub : (⨆ K : {K : Subgroup E // K.index = q}, Wsp σ K.1) ≤ Wsp σ K₀.1 := by
      refine iSup_le fun K => ?_
      by_cases hKK : K = K₀
      · subst hKK
        exact le_rfl
      · rw [hbot K hKK]
        exact bot_le
    have hfixK : ∀ s ∈ K₀.1, ∀ w, nrmAll σ w = 0 → σ s w = w := fun s hs w hw =>
      (hsub (decomposition_uc6 σ hq hexp hE hw)).2 s hs
    have hone : ∀ s ∈ K₀.1, s = 1 := by
      intro s hs
      apply hσ
      rw [map_one]
      apply LinearMap.ext
      intro w
      have h2 : σ s (w - nrmAll σ w) = w - nrmAll σ w := hfixK s hs _ (hproj w)
      rw [map_sub, hσN] at h2
      simpa using sub_left_injective (b := nrmAll σ w) h2
    have hK0bot : K₀.1 = ⊥ := eq_bot_iff.2 fun s hs => Subgroup.mem_bot.2 (hone s hs)
    have hcardK := Subgroup.card_mul_index K₀.1
    rw [K₀.2, hK0bot, Subgroup.card_bot, one_mul] at hcardK
    omega
  have hreg : ∀ K : {K : Subgroup E // K.index = q}, Wsp σ K.1 ≠ ⊥ → ∀ k ∈ K.1, α k ∈ K.1 := by
    intro K hKne
    by_contra hns
    push Not at hns
    obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).1 hKne
    obtain ⟨u', hu', hu'0, hu'u⟩ := exists_second_uc6 σ hE hu hu0
    have hND : ∀ w ∈ Wsp σ K.1, w ≠ 0 → (∑ i ∈ Finset.range r, T ^ i) w ≠ 0 := fun w hw hw0 =>
      regular_case_uc6 σ hE hq hq2 hexp T hr α hαr hTα K.2 hns hw hw0
    refine hC _ _ (hND u hu hu0) (hND u' hu' hu'0) ?_ (hTND u) (hTND u')
    intro heq
    apply hND (u - u') ((Wsp σ K.1).sub_mem hu hu') (sub_ne_zero.2 (Ne.symm hu'u))
    rw [map_sub, heq, sub_self]
  obtain ⟨K₁, K₂, hne12, hK1, hK2⟩ := htwo
  obtain ⟨a₁, ha₁, ha₁0, hTa₁⟩ := fixed_case_uc6 σ hE T hr hTr α hTα hfixi (hreg K₁ hK1) hK1
  obtain ⟨a₂, ha₂, ha₂0, hTa₂⟩ := fixed_case_uc6 σ hE T hr hTr α hTα hfixi (hreg K₂ hK2) hK2
  refine hC a₁ a₂ ha₁0 ha₂0 ?_ hTa₁ hTa₂
  intro heq
  obtain ⟨y, hyK₂, hyK₁⟩ := exists_mem_diff_uc6 hq K₁.2 K₂.2 (fun h => hne12 (Subtype.ext h))
  haveI : Fintype E := Fintype.ofFinite E
  have h0 : nrmOp σ K₁.1 a₁ = 0 :=
    nrmOp_eq_zero_of_fixed_uc6 σ hq hq2 hexp K₁.1 K₁.2 hyK₁ (u := a₁)
      (by rw [heq]; exact ha₂.2 y hyK₂) ha₁.1
  have h1 : nrmOp σ K₁.1 a₁ = a₁ := nrmOp_fixed_uc6 σ K₁.1 (odd_card_hyp_uc6 hE K₁.2) ha₁.2
  exact ha₁0 (h1.symm.trans h0)

end Core

end CFSG.LocalAnalysis.UniquenessCase.UC6
