module

public import CFSG.Quasithin.Vol2.KGFactG2RuAbs
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin.H13.Ch4.G2Ru

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement IsMulCommutative

section Closure

variable {M : Type*} [Group M] {s : Set M}

theorem closure_comm (h : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) {x y : M}
    (hx : x ∈ Subgroup.closure s) (hy : y ∈ Subgroup.closure s) : x * y = y * x := by
  have h1 : ∀ z ∈ s, Subgroup.closure s ≤ Subgroup.centralizer {z} := fun z hz => by
    rw [Subgroup.closure_le]
    intro u hu
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact h z hz u hu
  have h2 : Subgroup.closure s ≤ Subgroup.centralizer {y} := by
    rw [Subgroup.closure_le]
    intro z hz
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    rw [ht]
    exact (Subgroup.mem_centralizer_iff.1 (h1 z hz hy) z rfl).symm
  exact (Subgroup.mem_centralizer_iff.1 (h2 hx) y rfl).symm

theorem closure_sq (h : ∀ x ∈ s, ∀ y ∈ s, x * y = y * x) (hsq : ∀ x ∈ s, x * x = 1) {x : M}
    (hx : x ∈ Subgroup.closure s) : x * x = 1 := by
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hsq y hy
  | one => simp
  | mul a b ha hb iha ihb =>
    calc a * b * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [closure_comm h hb ha]
      _ = (a * a) * (b * b) := by simp only [mul_assoc]
      _ = 1 := by rw [iha, ihb, one_mul]
  | inv a ha iha => rw [← mul_inv_rev, iha, inv_one]

end Closure

variable {Q : Type} [Group Q] [Finite Q] {P T W V : Subgroup Q} {x : Q} {ns : List Q}
  {a : ℕ → Q} {G : Type} [Group G] [Finite G] {K : Subgroup G} {ψ : ↥K →* Q}
  {B : Subgroup G}

omit [Finite G] in
theorem conjAct_apply_coe {W₀ : Subgroup G} (n : Subgroup.normalizer (W₀ : Set G)) (w : ↥W₀) :
    ((conjAct W₀ n w : ↥W₀) : G) = (n : G) * w * (n : G)⁻¹ := by
  simp [conjAct, Subgroup.normalizerMonoidHom_apply_apply_coe]

theorem ff_of_model (hM : G2RuModel P T W V x ns a) (hrange : ψ.range = P)
    (hker : ψ.ker = Subgroup.center ↥K) (hBK : B ≤ K) (hB : IsG2Block B) {W₀ : Subgroup G}
    (hWU : W₀ ≤ blockU B) (hWZ : W₀ ⊓ blockZ B = ⊥)
    (hBW : B ≤ Subgroup.normalizer (W₀ : Set G)) (hW : Nat.card W₀ = 64) :
    ∃ _ : IsMulCommutative ↥W₀,
      IsFFModule (V := ↥W₀) (autOn (K ⊓ Subgroup.normalizer (W₀ : Set G)) W₀) := by
  have hcW : IsMulCommutative ↥W₀ :=
    ⟨⟨fun u v => Subtype.ext (blockU_comm hB.1 (hWU u.2) (hWU v.2))⟩⟩
  refine ⟨hcW, ?_⟩
  obtain ⟨g, hgP, hgU, -, h64⟩ := exists_conj_model hM hrange hker hBK hB (S' := ⊥) bot_le
    IsPGroup.of_bot
  have hWK : W₀ ≤ K := hWU.trans ((blockU_le B).trans hBK)
  have hW0Z : W₀ ⊓ zK K = ⊥ := by
    rw [eq_bot_iff, ← hWZ]
    intro w hw
    exact ⟨hw.1, blockU_inf_zK_le hBK ⟨hWU hw.1, hw.2⟩⟩
  have himgW : img ψ W₀ = img ψ (blockU B) := Subgroup.eq_of_le_of_card_ge (img_mono ψ hWU)
    (by rw [h64, card_img_of_inf hker hWK hW0Z, hW])
  have hcomm := commutator_eq_of_inf hB hWU hBW hWZ hW
  let θ : ↥W₀ → Q := fun w => g * ψ ⟨w, hWK w.2⟩ * g⁻¹
  have hθW : ∀ w : ↥W₀, θ w ∈ W := by
    intro w
    rw [← hgU, mem_map_conj, ← himgW]
    simpa [θ, mul_assoc] using mem_img_of_mem ψ w.2 (hWK w.2)
  have hθinj : Function.Injective θ := by
    intro u v h
    have h1 : ψ ⟨u, hWK u.2⟩ = ψ ⟨v, hWK v.2⟩ := by
      have := congrArg (fun y => g⁻¹ * y * g) h
      simpa [θ, mul_assoc] using this
    exact Subtype.ext (eq_of_img_eq hker hW0Z u.2 v.2 (hWK u.2) (hWK v.2) h1)
  have hθsurj : ∀ y ∈ W, ∃ w : ↥W₀, θ w = y := by
    intro y hy
    rw [← hgU, mem_map_conj, ← himgW] at hy
    obtain ⟨w, hw, hwK, he⟩ := exists_of_mem_img ψ hy
    refine ⟨⟨w, hw⟩, ?_⟩
    simp only [θ, he]
    group
  have hlift : ∀ q ∈ P ⊓ Subgroup.normalizer (W : Set Q), ∀ k' : ↥K, ψ k' = g⁻¹ * q * g →
      (k' : G) ∈ Subgroup.normalizer (W₀ : Set G) := by
    intro q hq k' hk'
    obtain ⟨hk'B, hk'U⟩ := lift_model hM hrange hker hBK hB hgP hgU hq hk'
    exact lift_normalizer_W hker hBK hWU hBW hcomm hk'B (himgW ▸ hk'U)
  have hy : ∀ i : Fin 3, ∃ y : ↥K, ψ y = g⁻¹ * a i * g := fun i =>
    exists_preimage hrange (P.mul_mem (P.mul_mem (P.inv_mem hgP) (hM.a_mem i i.2).1) hgP)
  choose y hyψ using hy
  set N₀ := K ⊓ Subgroup.normalizer (W₀ : Set G) with hN₀
  have hyN : ∀ i : Fin 3, (y i : G) ∈ N₀ := fun i =>
    ⟨(y i).2, hlift _ (hM.a_mem i i.2) (y i) (hyψ i)⟩
  let ρ : ↥N₀ →* MulAut ↥W₀ := (conjAct W₀).comp (Subgroup.inclusion inf_le_right)
  let κ : ↥N₀ →* Q :=
    (MulAut.conj g).toMonoidHom.comp (ψ.comp (Subgroup.inclusion inf_le_left))
  have hκ : ∀ n : ↥N₀, κ n = g * ψ ⟨n, n.2.1⟩ * g⁻¹ := fun n => rfl
  have hρθ : ∀ (n : ↥N₀) (w : ↥W₀), θ (ρ n w) = κ n * θ w * (κ n)⁻¹ := by
    intro n w
    have hc : ((ρ n w : ↥W₀) : G) = (n : G) * w * (n : G)⁻¹ :=
      conjAct_apply_coe (Subgroup.inclusion inf_le_right n) w
    have hψ : ψ ⟨((ρ n w : ↥W₀) : G), hWK (ρ n w).2⟩ =
        ψ ⟨n, n.2.1⟩ * ψ ⟨w, hWK w.2⟩ * (ψ ⟨n, n.2.1⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      congr 1
    simp only [θ, hψ, hκ]
    group
  set n : ℕ → ↥N₀ := fun i => if hi : i < 3 then ⟨y ⟨i, hi⟩, hyN ⟨i, hi⟩⟩ else 1 with hn
  have hκn : ∀ i < 3, κ (n i) = a i := by
    intro i hi
    rw [hκ]
    simp only [hn, hi, dite_true]
    rw [hyψ ⟨i, hi⟩]
    group
  set α : ℕ → MulAut ↥W₀ := fun i => ρ (n i) with hα
  have hθpow : ∀ (m : ↥N₀) (w : ↥W₀), θ (ρ m w) = κ m * θ w * (κ m)⁻¹ := hρθ
  have hext : ∀ m m' : ↥N₀, (∀ w ∈ W, κ m * w * (κ m)⁻¹ = κ m' * w * (κ m')⁻¹) → ρ m = ρ m' := by
    intro m m' h
    refine MulEquiv.ext fun w => hθinj ?_
    rw [hρθ, hρθ, h _ (hθW w)]
  set A : Subgroup (MulAut ↥W₀) := Subgroup.closure {β | ∃ i < 3, α i = β} with hA
  have hgcomm : ∀ u ∈ {β | ∃ i < 3, α i = β}, ∀ v ∈ {β | ∃ i < 3, α i = β}, u * v = v * u := by
    rintro _ ⟨i, hi, rfl⟩ _ ⟨j, hj, rfl⟩
    simp only [hα]
    rw [← map_mul, ← map_mul]
    refine hext _ _ fun w hw => ?_
    rw [map_mul, map_mul, hκn i hi, hκn j hj]
    exact hM.a_comm i hi j hj w hw
  have hgsq : ∀ u ∈ {β | ∃ i < 3, α i = β}, u * u = 1 := by
    rintro _ ⟨i, hi, rfl⟩
    simp only [hα]
    rw [← map_mul, ← map_one ρ]
    refine hext _ _ fun w hw => ?_
    rw [map_mul, hκn i hi, map_one, one_mul, inv_one, mul_one]
    exact hM.a_sq i hi w hw
  have hαA : ∀ i < 3, α i ∈ A := fun i hi => Subgroup.subset_closure ⟨i, hi, rfl⟩
  have hAle : A ≤ autOn (K ⊓ Subgroup.normalizer (W₀ : Set G)) W₀ := by
    rw [hA, Subgroup.closure_le]
    rintro _ ⟨i, hi, rfl⟩
    exact ⟨Subgroup.inclusion inf_le_right (n i), Subgroup.mem_subgroupOf.2 (n i).2, rfl⟩
  set nE : ℕ → ↥N₀ := fun e => n 0 ^ (e % 2) * (n 1 ^ (e / 2 % 2) * n 2 ^ (e / 4 % 2)) with hnE
  have hκE : ∀ e, κ (nE e) = aE a e := by
    intro e
    simp only [hnE, map_mul, map_pow, hκn 0 (by norm_num), hκn 1 (by norm_num),
      hκn 2 (by norm_num), aE]
  have hρE : ∀ e, ρ (nE e) ∈ A := by
    intro e
    simp only [hnE, map_mul, map_pow]
    exact A.mul_mem (A.pow_mem (hαA 0 (by norm_num)) _) (A.mul_mem
      (A.pow_mem (hαA 1 (by norm_num)) _) (A.pow_mem (hαA 2 (by norm_num)) _))
  have hρinj : ∀ e < 8, ∀ e' < 8, ρ (nE e) = ρ (nE e') → e = e' := by
    intro e he e' he' h
    by_contra hne
    obtain ⟨w, hw, hne'⟩ := hM.a_ne e he e' he' hne
    obtain ⟨u, rfl⟩ := hθsurj w hw
    apply hne'
    rw [← hκE, ← hκE, ← hρθ, ← hρθ, h]
  have hcardA : 8 ≤ Nat.card A := by
    let f : Fin 8 → A := fun e => ⟨ρ (nE e), hρE e⟩
    have hf : Function.Injective f := fun e e' h =>
      Fin.ext (hρinj e e.2 e' e'.2 (congrArg Subtype.val h))
    simpa using Nat.card_le_card_of_injective f hf
  have hfix : ∀ w : ↥W₀, θ w ∈ V → w ∈ fixV A := by
    intro w hwV
    rw [mem_fixV]
    intro β hβ
    induction hβ using Subgroup.closure_induction with
    | mem u hu =>
      obtain ⟨i, hi, rfl⟩ := hu
      refine hθinj ?_
      simp only [hα]
      rw [hρθ, hκn i hi, hM.a_V i hi _ hwV, mul_inv_cancel_right]
    | one => rfl
    | mul u v _ _ ihu ihv =>
      rw [MulAut.mul_apply, ihv, ihu]
    | inv u _ ihu =>
      have h := congrArg (fun t => u⁻¹ t) ihu
      simpa using h.symm
  have hcardF : 8 ≤ Nat.card (fixV A) := by
    choose θi hθi using hθsurj
    let f : ↥V → ↥(fixV A) := fun v => ⟨θi v (hM.V_le v.2), hfix _ (by
      rw [hθi]
      exact v.2)⟩
    have hf : Function.Injective f := by
      intro u v h
      have h1 := congrArg (fun t : ↥(fixV A) => θ t) h
      simp only [f, hθi] at h1
      exact Subtype.ext h1
    have := Nat.card_le_card_of_injective f hf
    rwa [hM.card_V] at this
  refine ⟨A, hAle, ?_, ⟨fun u hu v hv => closure_comm hgcomm hu hv,
    fun u hu => by rw [sq]; exact closure_sq hgcomm hgsq hu⟩, ?_⟩
  · intro hbot
    have h1 := hρinj 1 (by norm_num) 0 (by norm_num) (by
      have hρ1 : ρ (nE 1) ∈ A := hρE 1
      have hρ0 : ρ (nE 0) = 1 := by simp [hnE]
      rw [hbot, Subgroup.mem_bot] at hρ1
      rw [hρ1, hρ0])
    norm_num at h1
  · rw [hW]
    calc 64 = 8 * 8 := by norm_num
      _ ≤ Nat.card A * Nat.card (fixV A) := Nat.mul_le_mul hcardA hcardF

end CFSG.Quasithin.H13.Ch4.G2Ru
