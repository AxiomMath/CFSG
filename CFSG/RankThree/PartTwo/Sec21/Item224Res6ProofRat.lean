module

public import CFSG.RankThree.Classical.SemilinearFixedBasis
public import CFSG.LieType.BorelTits.FormFlag

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof

open CFSG.LieType.BorelTits Module

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

theorem rational_form_props [Finite K] [CharP K 2] [FiniteDimensional K V] {e : ℕ} (he : 1 ≤ e)
    (hK : Nat.card K = 2 ^ e) (F : ReflForm K V) (hsymm : ∀ u v, F.β v u = F.σ (F.β u v))
    {φ : K ≃+* K} (hσφ : ∀ c, φ c = c → F.σ c = c) (ψ : V ≃+ V)
    (hψs : ∀ (c : K) (v : V), ψ (c • v) = φ c • ψ v)
    (hψβ : ∀ u v, F.β (ψ u) (ψ v) = φ (F.β u v)) (hψm : ∀ v, (⇑ψ)^[orderOf φ] v = v)
    (W : Submodule K V) (hW : ∀ w ∈ W, ψ w ∈ W) (hW' : ∀ w ∈ W, ψ.symm w ∈ W)
    (hW3 : 3 ≤ finrank K W) (hWnd : ∀ c ∈ W, (∀ w ∈ W, F.β w c = 0) → c = 0)
    (hiso : ∀ v ∈ W, ψ v = v → F.β v v = 0) :
    (∀ a ∈ {v | v ∈ W ∧ ψ v = v}, ∀ b ∈ {v | v ∈ W ∧ ψ v = v},
        a + b ∈ {v | v ∈ W ∧ ψ v = v}) ∧
      (∀ b ∈ {v | v ∈ W ∧ ψ v = v}, ∀ c ∈ {v | v ∈ W ∧ ψ v = v}, F.β b c ≠ 0 →
        ∃ l : K, l • b ∈ {v | v ∈ W ∧ ψ v = v} ∧ F.β (l • b) c = 1) ∧
      (∀ c ∈ {v | v ∈ W ∧ ψ v = v}, c ≠ 0 → ∃ b ∈ {v | v ∈ W ∧ ψ v = v}, F.β b c ≠ 0) ∧
      (∀ b ∈ {v | v ∈ W ∧ ψ v = v}, ∀ c ∈ {v | v ∈ W ∧ ψ v = v}, F.β b c = 1 →
        ∃ a ∈ {v | v ∈ W ∧ ψ v = v}, ∃ a' ∈ {v | v ∈ W ∧ ψ v = v}, F.β a b = 0 ∧
          F.β a c = 0 ∧ F.β a' b = 0 ∧ F.β a' c = 0 ∧ F.β a a' = 1) ∧
      (∃ b ∈ {v | v ∈ W ∧ ψ v = v}, ∃ c ∈ {v | v ∈ W ∧ ψ v = v}, F.β b c ≠ 0) ∧
      (∀ w : V, (∀ c ∈ {v | v ∈ W ∧ ψ v = v}, F.β c w = 0) → ∀ w' ∈ W, F.β w' w = 0) := by
  classical
  have : Finite (K ≃+* K) :=
    Finite.of_injective (fun φ : K ≃+* K => (φ : K → K)) fun a b hab => RingEquiv.ext
      (congrFun hab)
  have : Finite V := Module.finite_of_finite K
  set W₀ : Set V := {v | v ∈ W ∧ ψ v = v} with hW₀
  have hval : ∀ u ∈ W₀, ∀ v ∈ W₀, φ (F.β u v) = F.β u v := by
    rintro u ⟨-, hu⟩ v ⟨-, hv⟩
    rw [← hψβ, hu, hv]
  have hσval : ∀ u ∈ W₀, ∀ v ∈ W₀, F.σ (F.β u v) = F.β u v := fun u hu v hv =>
    hσφ _ (hval u hu v hv)
  have hadd : ∀ a ∈ W₀, ∀ b ∈ W₀, a + b ∈ W₀ := by
    rintro a ⟨haW, ha⟩ b ⟨hbW, hb⟩
    exact ⟨add_mem haW hbW, by rw [map_add, ha, hb]⟩
  have hsmul : ∀ c : K, φ c = c → ∀ a ∈ W₀, c • a ∈ W₀ := by
    rintro c hc a ⟨haW, ha⟩
    exact ⟨W.smul_mem c haW, by rw [hψs, hc, ha]⟩
  let ψW : W ≃+ W :=
    { toFun := fun w => ⟨ψ (w : V), hW _ w.2⟩
      invFun := fun w => ⟨ψ.symm (w : V), hW' _ w.2⟩
      left_inv := fun w => Subtype.ext (ψ.symm_apply_apply (w : V))
      right_inv := fun w => Subtype.ext (ψ.apply_symm_apply (w : V))
      map_add' := fun u v => Subtype.ext (map_add ψ (u : V) (v : V)) }
  have hψWs : ∀ (c : K) (w : W), ψW (c • w) = φ c • ψW w := fun c w =>
    Subtype.ext (hψs c (w : V))
  have hψWit : ∀ j (w : W), (((⇑ψW)^[j] w : W) : V) = (⇑ψ)^[j] (w : V) := by
    intro j
    induction j with
    | zero => intro w; rfl
    | succ j ih =>
      intro w
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ← ih]
      rfl
  have hψWm : ∀ w : W, (⇑ψW)^[orderOf φ] w = w := fun w =>
    Subtype.ext (by rw [hψWit, hψm])
  obtain ⟨-, k₀, hk₀, -, b, hb, C, hC, -, hCdim, -⟩ :=
    CFSG.RankThree.Classical.semilinear_fixed_basis Nat.prime_two he hK φ rfl
      (m := finrank K W) rfl ψW hψWs hψWm
  have hbW₀ : ∀ i, ((b i : W) : V) ∈ W₀ := fun i =>
    ⟨(b i).2, congrArg Subtype.val (hb i)⟩
  have hspan : ∀ w : V, (∀ c ∈ W₀, F.β c w = 0) → ∀ w' ∈ W, F.β w' w = 0 := by
    intro w hw w' hw'
    have hrepr := b.sum_repr ⟨w', hw'⟩
    have : w' = ∑ i, (b.repr ⟨w', hw'⟩ i) • ((b i : W) : V) := by
      have := congrArg Subtype.val hrepr
      rw [Submodule.coe_sum] at this
      simpa using this.symm
    rw [this]
    have key : ∀ s : Finset (Fin (finrank K W)),
        F.β (∑ i ∈ s, (b.repr ⟨w', hw'⟩ i) • ((b i : W) : V)) w = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty => rw [Finset.sum_empty, F.β_zero_left]
      | insert i s hi ih =>
        rw [Finset.sum_insert hi, F.add_left, ih, add_zero, F.smul_left, hw _ (hbW₀ i),
          mul_zero]
    exact key Finset.univ
  have hnd : ∀ c ∈ W₀, c ≠ 0 → ∃ b ∈ W₀, F.β b c ≠ 0 := by
    intro c hc hc0
    by_contra hall
    push Not at hall
    exact hc0 (hWnd c hc.1 (hspan c hall))
  have hscale : ∀ b ∈ W₀, ∀ c ∈ W₀, F.β b c ≠ 0 → ∃ l : K, l • b ∈ W₀ ∧ F.β (l • b) c = 1 := by
    intro b hb c hc hbc
    refine ⟨(F.β b c)⁻¹, hsmul _ (by rw [map_inv₀, hval b hb c hc]) b hb, ?_⟩
    rw [F.smul_left, map_inv₀, hσval b hb c hc, inv_mul_cancel₀ hbc]
  have hhyp : ∀ b ∈ W₀, ∀ c ∈ W₀, F.β b c = 1 → ∃ a ∈ W₀, ∃ a' ∈ W₀, F.β a b = 0 ∧
      F.β a c = 0 ∧ F.β a' b = 0 ∧ F.β a' c = 0 ∧ F.β a a' = 1 := by
    intro b hb c hc hbc
    have hmemC : ∀ w : W, w ∈ C ↔ ψ w = w := fun w => by
      rw [← SetLike.mem_coe, hC]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have hk₀mem : ∀ x : K, x ∈ k₀ ↔ φ x = x := fun x => by
      rw [← SetLike.mem_coe, hk₀]
      rfl
    have hCW₀ : ∀ w : C, ((w : W) : V) ∈ W₀ := fun w =>
      ⟨(w : W).2, (hmemC w).mp w.2⟩
    have : Module.Finite k₀ C := Module.Finite.of_finite
    let g : C →ₗ[k₀] k₀ × k₀ :=
      { toFun := fun w => (⟨F.β ((w : W) : V) b, (hk₀mem _).mpr (hval _ (hCW₀ w) b hb)⟩,
          ⟨F.β ((w : W) : V) c, (hk₀mem _).mpr (hval _ (hCW₀ w) c hc)⟩)
        map_add' := fun u v => by
          ext
          · exact F.add_left _ _ _
          · exact F.add_left _ _ _
        map_smul' := fun l w => by
          have hl : F.σ (l : K) = l := hσφ _ ((hk₀mem _).mp l.2)
          ext
          · change F.β ((l : K) • ((w : W) : V)) b = (l : K) * F.β ((w : W) : V) b
            rw [F.smul_left, hl]
          · change F.β ((l : K) • ((w : W) : V)) c = (l : K) * F.β ((w : W) : V) c
            rw [F.smul_left, hl] }
    have hrank := LinearMap.finrank_range_add_finrank_ker g
    have hrange : finrank k₀ (LinearMap.range g) ≤ 2 := by
      have := Submodule.finrank_le (LinearMap.range g)
      rwa [Module.finrank_prod, Module.finrank_self] at this
    have hker : LinearMap.ker g ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot, hCdim] at hrank
      omega
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
    have hab : F.β ((a : W) : V) b = 0 := congrArg (fun x => (x.1 : K)) ha
    have hac : F.β ((a : W) : V) c = 0 := congrArg (fun x => (x.2 : K)) ha
    have ha0' : ((a : W) : V) ≠ 0 := fun h => ha0 (Subtype.ext (Subtype.ext h))
    obtain ⟨y, hy, hya⟩ := hnd _ (hCW₀ a) ha0'
    have hay : F.β ((a : W) : V) y ≠ 0 := by
      rw [hsymm]
      exact fun h => hya ((map_eq_zero_iff F.σ F.σ.injective).mp h)
    obtain ⟨x, hl, hax⟩ : ∃ x ∈ W₀, F.β ((a : W) : V) x = 1 := by
      obtain ⟨l, hl, hlx⟩ := hscale y hy _ (hCW₀ a) hya
      exact ⟨l • y, hl, by rw [hsymm, hlx, map_one]⟩
    set a' := x + F.β x c • b + F.β x b • c with ha'
    have hxc := hval x hl c hc
    have hxb := hval x hl b hb
    have ha'W₀ : a' ∈ W₀ :=
      hadd _ (hadd _ hl _ (hsmul _ hxc b hb)) _ (hsmul _ hxb c hc)
    have hcb : F.β c b = 1 := by rw [hsymm, hbc, map_one]
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    refine ⟨(a : W), hCW₀ a, a', ha'W₀, hab, hac, ?_, ?_, ?_⟩
    · rw [ha', F.add_left, F.add_left, F.smul_left, F.smul_left, hiso b hb.1 hb.2,
        hσφ _ hxc, hσφ _ hxb, hcb]
      linear_combination F.β x b * h2
    · rw [ha', F.add_left, F.add_left, F.smul_left, F.smul_left, hiso c hc.1 hc.2,
        hσφ _ hxc, hσφ _ hxb, hbc]
      linear_combination F.β x c * h2
    · rw [ha', F.add_right, F.add_right, F.smul_right, F.smul_right, hax, hab, hac]
      ring
  have hpair : ∃ b ∈ W₀, ∃ c ∈ W₀, F.β b c ≠ 0 := by
    have hpos : 0 < finrank K W := by omega
    set i₀ : Fin (finrank K W) := ⟨0, hpos⟩
    have hb0 : ((b i₀ : W) : V) ≠ 0 := fun h => b.ne_zero i₀ (Subtype.ext h)
    obtain ⟨c, hc, hcb⟩ := hnd _ (hbW₀ i₀) hb0
    exact ⟨c, hc, _, hbW₀ i₀, hcb⟩
  exact ⟨hadd, hscale, hnd, hhyp, hpair, hspan⟩

end CFSG.RankThree.PartTwo.Sec21.Item224Res6Proof
