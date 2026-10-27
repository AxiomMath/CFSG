module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreOrth
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerRestCore
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord Multiplicative NbrOrth

@[expose] def GGTorusEvenSignedEltSC (p : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ 3 ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
    ∃ (k : ℕ) (τ : (Fin k → Multiplicative (ZMod p)) →* R), Function.Injective τ ∧
      τ.range = E ∧
      (∀ i j : Fin k, i ≠ j → ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (dinv i j f)) ∧
      ∀ j t u : Fin k, j ≠ t → j ≠ u → t ≠ u →
        ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (f ∘ ⇑(swapComm j t u)⁻¹)

namespace OrthNs

section Coord

variable {p m : ℕ}

theorem dinv_apply_eq (i k : Fin m) (f : Fin m → Multiplicative (ZMod p)) (j : Fin m) :
    dinv i k f j = if i = k then f j else if j = i ∨ j = k then (f j)⁻¹ else f j := by
  unfold dinv
  by_cases hik : i = k
  · subst hik
    by_cases hj : j = i
    · subst hj
      simp
    · simp [Function.update_of_ne hj]
  · by_cases hji : j = i
    · subst hji
      simp [hik]
    · by_cases hjk : j = k
      · subst hjk
        simp [hik, hji]
      · simp [hik, hji, hjk]

theorem dinv_pow (i k : Fin m) (f : Fin m → Multiplicative (ZMod p)) (c : ℕ) :
    dinv i k (f ^ c) = dinv i k f ^ c := by
  funext j
  rw [Pi.pow_apply, dinv_apply_eq, dinv_apply_eq, Pi.pow_apply]
  split_ifs <;> simp [inv_pow]

theorem comp_pow (σ : Equiv.Perm (Fin m)) (f : Fin m → Multiplicative (ZMod p)) (c : ℕ) :
    (f ^ c) ∘ ⇑σ = (f ∘ ⇑σ) ^ c := by
  funext j
  simp [Pi.pow_apply]

end Coord

section Transport

theorem ggTorusEvenSignedEltSC_of_mulEquiv {p : ℕ} {R R' : Type} [Group R] [Group R']
    (e : R ≃* R') (h : GGTorusEvenSignedEltSC p R') : GGTorusEvenSignedEltSC p R := by
  intro E hE h3 hsc
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    (Nat.card_congr (E.equivMapOfInjective _ e.injective).toEquiv).symm
  have hmem : ∀ x : R, e x ∈ E.map e.toMonoidHom ↔ x ∈ E := fun x =>
    ⟨fun ⟨y, hy, hyx⟩ => e.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hsc' : ∀ g : R', (∀ x ∈ E.map e.toMonoidHom, g * x = x * g) → g ^ p = 1 →
      g ∈ E.map e.toMonoidHom := by
    intro g hg hgp
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [hmem]
    refine hsc y (fun x hx => e.injective ?_) ?_
    · rw [map_mul, map_mul]
      exact hg _ ((hmem x).mpr hx)
    · apply e.injective
      rw [map_pow, hgp, map_one]
  obtain ⟨k, τ, hτinj, hτE, hdinv, hswap⟩ :=
    h (E.map e.toMonoidHom) (TableB.isElemAbelian_map hE _) (hcard ▸ h3) hsc'
  have hconj : ∀ (w : R') (f f' : Fin k → Multiplicative (ZMod p)),
      w * τ f * w⁻¹ = τ f' → e.symm w * e.symm (τ f) * (e.symm w)⁻¹ = e.symm (τ f') := by
    intro w f f' h
    rw [← map_inv, ← map_mul, ← map_mul, h]
  refine ⟨k, e.symm.toMonoidHom.comp τ, e.symm.injective.comp hτinj, ?_,
    fun i j hij => ?_, fun j t u hjt hju htu => ?_⟩
  · ext x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨f, rfl⟩
      have : τ f ∈ τ.range := ⟨f, rfl⟩
      rw [hτE] at this
      rw [← hmem]
      simpa using this
    · intro hx
      have : e x ∈ τ.range := hτE ▸ (hmem x).mpr hx
      obtain ⟨f, hf⟩ := this
      exact ⟨f, by simp [hf]⟩
  · obtain ⟨w, hw⟩ := hdinv i j hij
    exact ⟨e.symm w, fun f => hconj w f _ (hw f)⟩
  · obtain ⟨w, hw⟩ := hswap j t u hjt hju htu
    exact ⟨e.symm w, fun f => hconj w f _ (hw f)⟩

end Transport

section Model

variable {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem exists_evenSignedModelSC (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusEvenSignedEltSC p R) {L' : Type} [Group L']
    [Finite L'] {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) (h3 : p ^ 3 ≤ Nat.card A)
    (hsc : GGTorusSelfCent p A) :
    ∃ (k : ℕ) (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A), 3 ≤ k ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) ∧
      (∀ i j : Fin k, i ≠ j → ∃ n : L',
        MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) ∧
        ∀ f, MulAut.conj n * ((Θ f : ↥A) : MulAut L') * (MulAut.conj n)⁻¹ =
          ((Θ (dinv i j f) : ↥A) : MulAut L')) ∧
      ∀ j t u : Fin k, j ≠ t → j ≠ u → t ≠ u → ∃ n : L',
        MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) ∧
        ∀ f, MulAut.conj n * ((Θ f : ↥A) : MulAut L') * (MulAut.conj n)⁻¹ =
          ((Θ (f ∘ ⇑(swapComm j t u)⁻¹) : ↥A) : MulAut L') := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcpL := hcp L' ψ hψ hker hperf
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    obtain ⟨e, rfl⟩ := hI hφI
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨n, hn, hnp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL hgp
    have hfix : ∀ a ∈ A, a n = n := by
      intro a ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have heE : e ∈ E := show Λ e ∈ A from ha
      refine eq_of_lift_pow_eq_one hp hker hcpL ?_ ?_ hnp
      · rw [hΛmap, hn, ← hg e heE, mul_inv_cancel_right]
      · rw [← map_pow, hnp, map_one]
    have h1 := hsc n hfix hnp
    rw [← hΛn, hn] at h1
    exact h1
  obtain ⟨k, τ, hτinj, hτE, hdinv, hswap⟩ := h E hEab (hcardE ▸ h3) hscE
  have hτmem : ∀ f, Λ (τ f) ∈ A := fun f => by
    have : τ f ∈ E := hτE ▸ ⟨f, rfl⟩
    exact this
  set Θ₀ : (Fin k → Multiplicative (ZMod p)) →* ↥A := (Λ.comp τ).codRestrict A hτmem with hΘ₀
  have hΘ₀bij : Function.Bijective Θ₀ := by
    refine ⟨fun f g hfg => hτinj (hΛinj (congrArg Subtype.val hfg)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    have heE : e ∈ E := show Λ e ∈ A from he ▸ a.2
    rw [← hτE] at heE
    obtain ⟨f, rfl⟩ := heE
    exact ⟨f, Subtype.ext he⟩
  set Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A := MulEquiv.ofBijective Θ₀ hΘ₀bij with hΘ
  have hΘval : ∀ f, ((Θ f : ↥A) : MulAut L') = Λ (τ f) := fun f => rfl
  have hk : 3 ≤ k := by
    have hcV : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
      rw [Nat.card_fun, Nat.card_fin]
      congr 1
      exact Nat.card_zmod p
    have h1 : Nat.card (Fin k → Multiplicative (ZMod p)) = Nat.card A :=
      Nat.card_congr Θ.toEquiv
    rw [hcV] at h1
    rw [← h1] at h3
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp h3
  have hlift : ∀ (w : R)
      (α : (Fin k → Multiplicative (ZMod p)) → (Fin k → Multiplicative (ZMod p))),
      (∀ f, w * τ f * w⁻¹ = τ (α f)) → ∃ n : L',
        MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) ∧
        ∀ f, MulAut.conj n * ((Θ f : ↥A) : MulAut L') * (MulAut.conj n)⁻¹ =
          ((Θ (α f) : ↥A) : MulAut L') := by
    intro w α hw
    obtain ⟨n, rfl⟩ := hψ w
    have hconjΘ : ∀ f, MulAut.conj n * ((Θ f : ↥A) : MulAut L') * (MulAut.conj n)⁻¹ =
        ((Θ (α f) : ↥A) : MulAut L') := by
      intro f
      rw [hΘval, hΘval, ← hΛn n, ← map_inv, ← map_mul, ← map_mul, hw f]
    refine ⟨n, ?_, hconjΘ⟩
    have h1 : (MulAut.conj n)⁻¹ ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
      refine mem_normalizer_of_forall_conj_mem fun a ha => ?_
      obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha⟩
      have e : ((MulAut.conj n)⁻¹)⁻¹ * a * (MulAut.conj n)⁻¹ =
          ((Θ (α f) : ↥A) : MulAut L') := by
        rw [inv_inv, ← hconjΘ f, hf]
      rw [e]
      exact (Θ _).2
    simpa using Subgroup.inv_mem _ h1
  obtain ⟨σ, hσ⟩ := TableBSymp.exists_torus_section hψ hker (hp.odd_of_ne_two hp2) τ
    fun i j => by
      obtain ⟨m, hmi, hmj⟩ := TableBSymp.exists_ne_ne_of_three_le hk i j
      obtain ⟨w, hw⟩ := hdinv i m (Ne.symm hmi)
      refine ⟨w, ?_, fun hji => ?_⟩
      · rw [TableBSymp.torusBasis, hw, dinv_mulSingle_self (Ne.symm hmi), map_inv]
      · rw [TableBSymp.torusBasis, hw, dinv_mulSingle_of_ne hji (Ne.symm hmj)]
  have hψσ : ∀ f, ψ (σ f) = τ f := fun f => by rw [← MonoidHom.comp_apply, hσ]
  have hΘσ : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (σ f) := fun f =>
    (hΘval f).trans (hΛeq (hψσ f))
  have hσc : ∀ f g, σ f * σ g = σ g * σ f := fun f g => by
    rw [← map_mul, ← map_mul, mul_comm]
  have hNE : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∀ f, ∃ f', ψ n * τ f * (ψ n)⁻¹ = τ f' := by
    intro n hn f
    have h1 : Λ (ψ n * τ f * (ψ n)⁻¹) ∈ A := by
      rw [map_mul, map_mul, map_inv, hΛn]
      exact (Subgroup.mem_normalizer_iff.mp hn _).mp (hτmem f)
    have h2 : ψ n * τ f * (ψ n)⁻¹ ∈ τ.range := hτE ▸ h1
    obtain ⟨f', hf'⟩ := h2
    exact ⟨f', hf'.symm⟩
  refine ⟨k, Θ, hk, fun n hn => ?_, fun i j hij => ?_, fun j t u hjt hju htu => ?_⟩
  ·
    have hform : ∀ f, ∃ g, ∃ z ∈ ψ.ker, z ^ p = 1 ∧
        n * (MulAut.conj (σ f) n)⁻¹ = σ g * z := by
      intro f
      obtain ⟨f', hf'⟩ := hNE n hn f
      set z := (σ f')⁻¹ * (n * σ f * n⁻¹) with hz
      have hzk : z ∈ ψ.ker := by
        rw [MonoidHom.mem_ker, hz, map_mul, map_inv, map_mul, map_mul, map_inv, hψσ, hψσ, hf',
          inv_mul_cancel]
      have hzc := Subgroup.mem_center_iff.mp (hker hzk)
      have hzp : z ^ p = 1 := by
        have h1 : (n * σ f * n⁻¹) ^ p = 1 := by
          rw [conj_pow, ← map_pow, ReflInner.pow_eq_one_of_zmod, map_one, mul_one, mul_inv_cancel]
        have h2 : n * σ f * n⁻¹ = σ f' * z := by rw [hz, mul_inv_cancel_left]
        rw [h2, (show Commute (σ f') z from hzc (σ f')).mul_pow, ← map_pow,
          ReflInner.pow_eq_one_of_zmod, map_one, one_mul] at h1
        exact h1
      refine ⟨f' * f⁻¹, z, hzk, hzp, ?_⟩
      rw [MulAut.conj_apply, map_mul, map_inv, mul_assoc (σ f'), hzc (σ f)⁻¹, hz]
      group
    intro a ha
    obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha⟩
    have haσ : a = MulAut.conj (σ f) := by
      rw [← hΘσ, hf]
    obtain ⟨g, z, hzk, hzp, he⟩ := hform f
    have hzc := Subgroup.mem_center_iff.mp (hker hzk)
    rw [haσ, he]
    refine ⟨?_, fun a' ha' => ?_⟩
    · rw [(show Commute (σ g) z from hzc (σ g)).mul_pow, ← map_pow,
        ReflInner.pow_eq_one_of_zmod, map_one, one_mul, hzp]
    · obtain ⟨f'', hf''⟩ := Θ.surjective ⟨a', ha'⟩
      have ha'σ : a' = MulAut.conj (σ f'') := by
        rw [← hΘσ, hf'']
      rw [ha'σ, MulAut.conj_apply]
      calc σ f'' * (σ g * z) * (σ f'')⁻¹ = σ g * (σ f'' * z) * (σ f'')⁻¹ := by
            rw [← mul_assoc, hσc]; group
        _ = σ g * (z * σ f'') * (σ f'')⁻¹ := by rw [hzc]
        _ = σ g * z := by group
  · obtain ⟨w, hw⟩ := hdinv i j hij
    exact hlift w _ hw
  · obtain ⟨w, hw⟩ := hswap j t u hjt hju htu
    exact hlift w _ hw

end Model

section Transfer

variable {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem ggTorusIrredSC_of_evenSignedEltSC (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusEvenSignedEltSC p R) :
    CorFourTwoOpen.GGTorusIrredSC p R I := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc
  have := Fact.mk hp
  obtain ⟨k, Θ, hk, hW, hD, hS⟩ :=
    exists_evenSignedModelSC hp hp2 hI hZ hcp h hψ hker hperf hA hAI h3 hsc
  set W : Set L' := {n | MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))} with hWdef
  have hirr : ∀ A' : Subgroup (MulAut L'), A' ≤ A →
      (∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A') → A' = ⊥ ∨ A' = A := by
    intro A' hA'A hinv
    set F : Subgroup (Fin k → Multiplicative (ZMod p)) :=
      (A'.subgroupOf A).comap Θ.toMonoidHom with hF
    have hmemF : ∀ f, f ∈ F ↔ ((Θ f : ↥A) : MulAut L') ∈ A' := fun f => Iff.rfl
    have hstab : ∀ α : (Fin k → Multiplicative (ZMod p)) → (Fin k → Multiplicative (ZMod p)),
        (∃ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) ∧
          ∀ f, MulAut.conj n * ((Θ f : ↥A) : MulAut L') * (MulAut.conj n)⁻¹ =
            ((Θ (α f) : ↥A) : MulAut L')) → ∀ f ∈ F, α f ∈ F := by
      rintro α ⟨n, hn, hnα⟩ f hf
      rw [hmemF, ← hnα]
      exact hinv n hn _ ((hmemF f).mp hf)
    rcases eq_bot_or_eq_top_of_dinv hp hp2 hk F
        (fun i j hij f hf => hstab _ (hD i j hij) f hf)
        (fun j t u hjt hju htu f hf => hstab _ (hS j t u hjt hju htu) f hf) with hbot | htop
    · left
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨f, hf⟩ := Θ.surjective ⟨a, hA'A ha⟩
      have hfF : f ∈ F := by
        rw [hmemF, hf]
        exact ha
      rw [hbot, Subgroup.mem_bot] at hfF
      rw [hfF, map_one] at hf
      rw [Subgroup.mem_bot]
      exact (congrArg Subtype.val hf).symm
    · right
      refine le_antisymm hA'A fun a ha => ?_
      obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha⟩
      have hfF : f ∈ F := htop ▸ Subgroup.mem_top f
      rw [hmemF, hf] at hfF
      exact hfF
  set i₀ : Fin k := ⟨0, by omega⟩ with hi₀
  set i₁ : Fin k := ⟨1, by omega⟩ with hi₁
  set i₂ : Fin k := ⟨2, by omega⟩ with hi₂
  have h01 : i₀ ≠ i₁ := by simp [hi₀, hi₁, Fin.ext_iff]
  have h02 : i₀ ≠ i₂ := by simp [hi₀, hi₂, Fin.ext_iff]
  have h12 : i₁ ≠ i₂ := by simp [hi₁, hi₂, Fin.ext_iff]
  set δ : Fin k → Multiplicative (ZMod p) := Pi.mulSingle i₀ (ofAdd 1) with hδ
  have hδ1 : δ ≠ 1 := by
    intro h1
    have h2 := congrFun h1 i₀
    rw [hδ, Pi.mulSingle_eq_same, Pi.one_apply] at h2
    have h3 : (1 : ZMod p) = 0 := by simpa using congrArg toAdd h2
    exact one_ne_zero h3
  have hδinv : ∀ j, i₀ ≠ j → dinv i₀ j δ = δ⁻¹ := fun j hj => dinv_mulSingle_self hj _
  refine ⟨W, fun n hn => hW n hn, hirr, ?_, fun F hFA hFmul hFW => ?_⟩
  ·
    obtain ⟨n, hn, hnα⟩ := hD i₀ i₁ h01
    refine ⟨n, hn, Θ δ, (Θ δ).2, fun heq => ?_⟩
    rw [hnα, hδinv i₁ h01] at heq
    have h4 := congrFun (Θ.injective (Subtype.ext heq)) i₀
    rw [hδ, Pi.inv_apply, Pi.mulSingle_eq_same] at h4
    have h6 : (1 : ZMod p) = -1 := by
      have h7 := congrArg toAdd h4
      rw [toAdd_inv, toAdd_ofAdd] at h7
      exact h7.symm
    exact one_ne_zero (coord_eq_zero_of_eq_neg hp hp2 h6)
  ·
    have hF1 : F 1 = 1 := by
      have h1 := hFmul 1 A.one_mem 1 A.one_mem
      rw [mul_one] at h1
      exact mul_eq_left.mp h1.symm
    let Fc : (Fin k → Multiplicative (ZMod p)) →* (Fin k → Multiplicative (ZMod p)) :=
      { toFun := fun g => Θ.symm ⟨F (Θ g), hFA _ (Θ g).2⟩
        map_one' := by
          apply Θ.injective
          rw [MulEquiv.apply_symm_apply, map_one]
          exact Subtype.ext (by simpa using hF1)
        map_mul' := fun g g' => by
          apply Θ.injective
          rw [MulEquiv.apply_symm_apply, map_mul, map_mul, MulEquiv.apply_symm_apply,
            MulEquiv.apply_symm_apply]
          exact Subtype.ext (by simpa using hFmul _ (Θ g).2 _ (Θ g').2) }
    have hFc : ∀ g, ((Θ (Fc g) : ↥A) : MulAut L') = F (Θ g) := fun g => by
      show ((Θ (Θ.symm ⟨F (Θ g), hFA _ (Θ g).2⟩) : ↥A) : MulAut L') = F (Θ g)
      rw [MulEquiv.apply_symm_apply]
    have hcomm : ∀ α : (Fin k → Multiplicative (ZMod p)) → (Fin k → Multiplicative (ZMod p)),
        (∃ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) ∧
          ∀ f, MulAut.conj n * ((Θ f : ↥A) : MulAut L') * (MulAut.conj n)⁻¹ =
            ((Θ (α f) : ↥A) : MulAut L')) → ∀ g, Fc (α g) = α (Fc g) := by
      rintro α ⟨n, hn, hnα⟩ g
      apply Θ.injective
      apply Subtype.ext
      rw [hFc, ← hnα, ← hnα, hFc]
      exact hFW n hn _ (Θ g).2
    have hinvF : ∀ j, i₀ ≠ j → dinv i₀ j (Fc δ) = (Fc δ)⁻¹ := by
      intro j hj
      rw [← hcomm _ (hD i₀ j hj), hδinv j hj]
      exact map_inv Fc δ
    have hgsupp :=
      CorFourTwoMore.eq_mulSingle_of_dinv hp hp2 h12 (hinvF i₁ h01) (hinvF i₂ h02)
    set cc := (toAdd (Fc δ i₀)).val with hcc
    have hFδ : Fc δ = δ ^ cc := by
      rw [hgsupp, hδ, ← Pi.mulSingle_pow]
      congr 1
      rw [← ofAdd_nsmul, nsmul_eq_mul, mul_one, hcc, ZMod.natCast_zmod_val, ofAdd_toAdd]
    set G : Subgroup (Fin k → Multiplicative (ZMod p)) := Fc.eqLocus (powMonoidHom cc) with hG
    have hmemG : ∀ g, g ∈ G ↔ Fc g = g ^ cc := fun g => Iff.rfl
    have hGd : ∀ i j, i ≠ j → ∀ g ∈ G, dinv i j g ∈ G := by
      intro i j hij g hg
      rw [hmemG] at hg ⊢
      rw [hcomm _ (hD i j hij), hg, dinv_pow]
    have hGs : ∀ j t u : Fin k, j ≠ t → j ≠ u → t ≠ u → ∀ g ∈ G,
        g ∘ ⇑(swapComm j t u)⁻¹ ∈ G := by
      intro j t u hjt hju htu g hg
      rw [hmemG] at hg ⊢
      rw [hcomm _ (hS j t u hjt hju htu), hg, comp_pow]
    rcases eq_bot_or_eq_top_of_dinv hp hp2 hk G hGd hGs with hbot | htop
    · exfalso
      have : δ ∈ G := hFδ
      rw [hbot, Subgroup.mem_bot] at this
      exact hδ1 this
    · refine ⟨cc, fun a ha => ?_⟩
      obtain ⟨g, hg⟩ := Θ.surjective ⟨a, ha⟩
      have hgG : g ∈ G := htop ▸ Subgroup.mem_top g
      have h1 := hFc g
      rw [(hmemG g).mp hgG, map_pow, hg] at h1
      rw [← h1]
      rfl

theorem ggTorusNbrSC_of_evenSignedEltSC (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusEvenSignedEltSC p R) : GGTorusNbrSC p R I :=
  ggTorusNbrSC_of_ggTorusIrredSC hp (ggTorusIrredSC_of_evenSignedEltSC hp hp2 hI hZ hcp h)

end Transfer

end OrthNs

end CFSG.StandardType

end
