module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyU
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpModel

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord Multiplicative

@[expose] def GGTorusSignedEltSC (p : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ 3 ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
    ∃ (k : ℕ) (τ : (Fin k → Multiplicative (ZMod p)) →* R), Function.Injective τ ∧
      τ.range = E ∧
      (∀ i : Fin k, ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (sgnAut i f)) ∧
      (∀ σ : Equiv.Perm (Fin k), ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (permAut σ f)) ∧
      ∀ g : R, (∀ e ∈ E, g * e * g⁻¹ ∈ E) →
        ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)

section Model

variable {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem exists_signedModelSC_of_centerPrime (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (h : GGTorusSignedEltSC p R) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤)
    (hcpL : ¬ p ∣ Nat.card (Subgroup.center L'))
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) (h3 : p ^ 3 ≤ Nat.card A)
    (hsc : GGTorusSelfCent p A) :
    ∃ (k : ℕ) (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A), 3 ≤ k ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) ∧
      (∀ i : Fin k, ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ (sgnAut i)) ∧
      (∀ σ : Equiv.Perm (Fin k), ∃ (n : L')
        (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ (permAut σ)) ∧
      ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hn)) := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
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
  obtain ⟨k, τ, hτinj, hτE, hsgn, hperm, hnorm⟩ := h E hEab (hcardE ▸ h3) hscE
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
  have hlift : ∀ (w : R) (α : MulAut (Fin k → Multiplicative (ZMod p))),
      (∀ f, w * τ f * w⁻¹ = τ (α f)) → ∃ (n : L')
        (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ α := by
    intro w α hw
    obtain ⟨n, rfl⟩ := hψ w
    have hconjΘ : ∀ f, MulAut.conj n * ((Θ f : ↥A) : MulAut L') * (MulAut.conj n)⁻¹ =
        ((Θ (α f) : ↥A) : MulAut L') := by
      intro f
      rw [hΘval, hΘval, ← hΛn n, ← map_inv, ← map_mul, ← map_mul, hw f]
    have hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
      refine mem_normalizer_of_forall_conj_mem fun a ha => ?_
      obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha⟩
      have h1 := hconjΘ (α⁻¹ f)
      rw [MulAut.apply_inv_self, hf] at h1
      have h2 : a = MulAut.conj n * ((Θ (α⁻¹ f) : ↥A) : MulAut L') * (MulAut.conj n)⁻¹ := h1.symm
      have e : (MulAut.conj n)⁻¹ * a * MulAut.conj n = ((Θ (α⁻¹ f) : ↥A) : MulAut L') := by
        rw [h2]
        group
      rw [e]
      exact (Θ _).2
    refine ⟨n, hn, MulEquiv.ext fun a => Subtype.ext ?_⟩
    obtain ⟨f, rfl⟩ := Θ.surjective a
    rw [ggConjAut_apply, hconjΘ, MulAut.congr_apply]
    simp
  obtain ⟨σ, hσ⟩ := TableBSymp.exists_torus_section hψ hker (hp.odd_of_ne_two hp2) τ
    fun i j => by
      obtain ⟨w, hw⟩ := hsgn i
      refine ⟨w, ?_, fun hji => ?_⟩
      · rw [TableBSymp.torusBasis, hw, sgnAut_mulSingle_self, map_inv]
      · rw [TableBSymp.torusBasis, hw, sgnAut_mulSingle_of_ne hji]
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
  refine ⟨k, Θ, hk, fun n hn => ?_, fun i => ?_, fun σ' => ?_, fun n hn => ?_⟩
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
  · obtain ⟨w, hw⟩ := hsgn i
    exact hlift w _ hw
  · obtain ⟨w, hw⟩ := hperm σ'
    exact hlift w _ hw
  ·
    have hNE' : ∀ e ∈ E, ψ n * e * (ψ n)⁻¹ ∈ E := by
      intro e he
      rw [← hτE] at he ⊢
      obtain ⟨f, rfl⟩ := he
      obtain ⟨f', hf'⟩ := hNE n hn f
      exact ⟨f', hf'.symm⟩
    obtain ⟨π, ε, hε, hrel⟩ := hnorm (ψ n) hNE'
    refine ⟨π, ε, hε, fun f i => hrel f _ ?_ i⟩
    apply hΛinj
    set u := (MulAut.congr Θ).symm (ggConjAut A hn) with hu
    have hu' : MulAut.congr Θ u = ggConjAut A hn := MulEquiv.apply_symm_apply _ _
    have h1 : ((ggConjAut A hn (Θ f) : ↥A) : MulAut L') = ((Θ (u f) : ↥A) : MulAut L') := by
      rw [← hu', MulAut.congr_apply]
      simp
    rw [← hΘval, ← h1, ggConjAut_apply, hΘval, map_mul, map_mul, map_inv, hΛn]

theorem exists_signedModelSC (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusSignedEltSC p R) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) (h3 : p ^ 3 ≤ Nat.card A)
    (hsc : GGTorusSelfCent p A) :
    ∃ (k : ℕ) (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A), 3 ≤ k ∧
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) ∧
      (∀ i : Fin k, ∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ (sgnAut i)) ∧
      (∀ σ : Equiv.Perm (Fin k), ∃ (n : L')
        (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ (permAut σ)) ∧
      ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hn)) :=
  exists_signedModelSC_of_centerPrime (p := p) (R := R) (I := I)
    hp hp2 hI hZ h hψ hker hperf (hcp L' ψ hψ hker hperf) hA hAI h3 hsc

end Model


section Transfer

variable {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem ggTorusPseudoReflGenSC_of_signedEltSC (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusSignedEltSC p R) : GGTorusPseudoReflGenSC p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc v hv
  obtain ⟨k, Θ, -, hW, hS, hP, hN⟩ :=
    exists_signedModelSC hp hp2 hI hZ hcp h hψ hker hperf hA hAI h3 hsc
  obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hv
  have hv' : v = ggConjAut A hcN := MulEquiv.ext fun a => Subtype.ext (hvc a)
  set H : Subgroup (MulAut (Fin k → Multiplicative (ZMod p))) :=
    (Subgroup.closure (ggTorusPseudoReflSet p A)).comap (MulAut.congr Θ).toMonoidHom with hH
  have hgen : ∀ α : MulAut (Fin k → Multiplicative (ZMod p)), α ^ 2 = 1 →
      Nat.card {f // α f = f} * p = Nat.card (Fin k → Multiplicative (ZMod p)) →
      (∃ (m : L') (hm : MulAut.conj m ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hm = MulAut.congr Θ α) → α ∈ H := by
    rintro α hα2 hαfix ⟨m, hm, hmα⟩
    exact Subgroup.subset_closure ⟨m, hm, hW m hm, hmα.symm,
      ggIsPseudoReflection_congr Θ (pow_sub_one_eq_one_of_sq hp hp2 hα2) hαfix⟩
  have hsH : ∀ i, sgnAut i ∈ H := fun i =>
    hgen _ (sgnAut_sq i) (card_fix_sgnAut hp hp2 i) (hS i)
  have htH : ∀ a b : Fin k, a ≠ b → permAut (Equiv.swap a b) ∈ H := fun a b hab =>
    hgen _ (permAut_swap_sq a b) (card_fix_permAut_swap hp hp2 hab) (hP _)
  have hmem := mem_of_isSignedPerm hsH htH (hN n hcN)
  rw [hH, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at hmem
  rw [hv']
  exact hmem

theorem ggTorusSchurSC_of_signedEltSC (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusSignedEltSC p R) : GGTorusSchurSC p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc
  obtain ⟨k, Θ, hk, hW, hS, hP, -⟩ :=
    exists_signedModelSC hp hp2 hI hZ hcp h hψ hker hperf hA hAI h3 hsc
  refine ⟨{n | MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))}, fun n hn => hW n hn,
    fun F hFA hFmul hFW => ?_⟩
  have hF1 : F 1 = 1 := by
    have h1 := hFmul 1 A.one_mem 1 A.one_mem
    rw [mul_one] at h1
    exact (mul_eq_left.mp h1.symm)
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
  have hcomm : ∀ α : MulAut (Fin k → Multiplicative (ZMod p)),
      (∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ α) → ∀ g, Fc (α g) = α (Fc g) := by
    rintro α ⟨n, hn, hnα⟩ g
    apply Θ.injective
    apply Subtype.ext
    rw [hFc, ← coe_conj_of_ggConjAut_eq Θ hnα, ← coe_conj_of_ggConjAut_eq Θ hnα, hFc]
    exact hFW n hn _ (Θ g).2
  obtain ⟨c, hc⟩ := exists_pow_of_commute hp hp2 (by omega) Fc
    (fun i g => hcomm _ (hS i) g) (fun a b g => hcomm _ (hP _) g)
  refine ⟨c, fun a ha => ?_⟩
  obtain ⟨g, hg⟩ := Θ.surjective ⟨a, ha⟩
  have h1 := hFc g
  rw [hc, map_pow, hg] at h1
  rw [← h1]
  rfl

theorem exists_signedModelSC_normalizer (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusSignedEltSC p R)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l))
    (h3 : p ^ 3 ≤ Nat.card A) (hsc : GGTorusSelfCent p A) {φ : MulAut ↥A}
    (hφ : φ ∈ Subgroup.normalizer
      (ggAutomizer (MulAut.conj : L' →* MulAut L').range A : Set (MulAut ↥A))) :
    ∃ (k : ℕ) (Θ : (Fin k → Multiplicative (ZMod p)) ≃* ↥A) (w : MulAut ↥A),
      3 ≤ k ∧ w ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A ∧
        IsSignedPerm ⇑((MulAut.congr Θ).symm w) ∧ ∃ c : ℕ, ∀ a, φ a = (w a) ^ c := by
  obtain ⟨k, Θ, hk, -, hS, hP, hN⟩ :=
    exists_signedModelSC hp hp2 hI hZ hcp h hψ hker hperf hA hAI h3 hsc
  set W := ggAutomizer (MulAut.conj : L' →* MulAut L').range A with hWdef
  have hWin : ∀ α : MulAut (Fin k → Multiplicative (ZMod p)),
      (∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ α) → MulAut.congr Θ α ∈ W := by
    rintro α ⟨n, hn, hnα⟩
    rw [← hnα]
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
  have hW : ∀ v : MulAut ↥A, v ∈ W ↔ IsSignedPerm ⇑((MulAut.congr Θ).symm v) := by
    intro v
    constructor
    · intro hv
      obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hv
      have hv' : v = ggConjAut A hcN := MulEquiv.ext fun a => Subtype.ext (hvc a)
      rw [hv']
      exact hN n hcN
    · intro hv
      have hmem := mem_of_isSignedPerm (H := W.comap (MulAut.congr Θ).toMonoidHom)
        (fun i => hWin _ (hS i)) (fun a b _ => hWin _ (hP _)) hv
      rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply] at hmem
  have hcongr : ∀ u : MulAut (Fin k → Multiplicative (ZMod p)),
      IsSignedPerm ⇑u ↔ MulAut.congr Θ u ∈ W := fun u => by
    rw [hW, MulEquiv.symm_apply_apply]
  set φ' := (MulAut.congr Θ).symm φ with hφ'
  have hφφ' : φ = MulAut.congr Θ φ' := (MulEquiv.apply_symm_apply _ _).symm
  have h1 : ∀ u : MulAut (Fin k → Multiplicative (ZMod p)), IsSignedPerm ⇑u →
      IsSignedPerm ⇑(φ' * u * φ'⁻¹) := by
    intro u hu
    rw [hcongr, map_mul, map_mul, map_inv, ← hφφ']
    exact (Subgroup.mem_normalizer_iff.mp hφ _).mp ((hcongr u).mp hu)
  have h2 : ∀ u : MulAut (Fin k → Multiplicative (ZMod p)), IsSignedPerm ⇑u →
      IsSignedPerm ⇑(φ'⁻¹ * u * φ') := by
    intro u hu
    rw [hcongr, map_mul, map_mul, map_inv, ← hφφ']
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hφ) _).mp ((hcongr u).mp hu)
    rwa [inv_inv] at h
  obtain ⟨w, hw, c, hc⟩ := exists_isSignedPerm_pow hp hp2 hk h1 h2
  refine ⟨k, Θ, MulAut.congr Θ w, hk, (hcongr w).mp hw,
    by simpa only [MulEquiv.symm_apply_apply] using hw, c, fun a => ?_⟩
  obtain ⟨f, rfl⟩ := Θ.surjective a
  rw [hφφ', MulAut.congr_apply, MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hc, map_pow]

theorem ggTorusWeylNormInnerSC_of_signedEltSC (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime p R) (h : GGTorusSignedEltSC p R) : GGTorusWeylNormInnerSC p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc φ hφ
  obtain ⟨-, -, w, -, hw, -, c, hc⟩ :=
    exists_signedModelSC_normalizer hp hp2 hI hZ hcp h hψ hker hperf hA hAI h3 hsc hφ
  exact ⟨w, hw, fun v _ => conj_eq_of_forall_eq_pow hc v⟩

end Transfer


@[expose] def GGSpNonsplitTorusInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (m p : ℕ), 2 ≤ m → p.Prime →
    p ∣ Nat.card K + 1 →
      GGTorusSignedEltSC p (LargeEvenProj (LargeEvenSpGroup K m)) ∧
        GGCenterPrime p (LargeEvenProj (LargeEvenSpGroup K m))

@[expose] def GGSpNonsplitLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .B ∨ lab.tag = .C) ∧ p ∣ 2 ^ lab.n + 1

theorem recipeSymplectic_weylInputsSC (hin : GGSpNonsplitTorusInput) {l n p : ℕ} (hp : p.Prime)
    (hpn : p ∣ 2 ^ n + 1) (hn : 1 ≤ n) (hl : 2 ≤ l) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeSymplectic l (2 ^ n) false Q) :
    LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F => Q R I F ∧
      (GGTorusPseudoReflGenSC p R I ∧ GGTorusSchurSC p R I ∧ GGTorusWeylNormInnerSC p R I) := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  have := charP_two_of_card hK
  have : NeZero l := ⟨by omega⟩
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpn
  have hpK : p ∣ Nat.card K + 1 := by
    rw [hK]
    exact hpn
  obtain ⟨hT, hcp⟩ := hin K l p hl hp hpK
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    ggTorusPseudoReflGenSC_of_signedEltSC hp hp2 TableBSymp.sp_I_subset_inn
      TableBSymp.center_spProj_eq_bot hcp hT,
    ggTorusSchurSC_of_signedEltSC hp hp2 TableBSymp.sp_I_subset_inn
      TableBSymp.center_spProj_eq_bot hcp hT,
    ggTorusWeylNormInnerSC_of_signedEltSC hp hp2 TableBSymp.sp_I_subset_inn
      TableBSymp.center_spProj_eq_bot hcp hT⟩

theorem largeEvenLabelAll_weylInputsSC_spNonsplit (hin : GGSpNonsplitTorusInput) {p : ℕ}
    (hp : p.Prime) {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : GGSpNonsplitLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusPseudoReflGenSC p R I ∧ GGTorusSchurSC p R I ∧ GGTorusWeylNormInnerSC p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hpn⟩ := h
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases htag with h | h <;> dsimp only at h <;> subst h <;>
    exact recipeSymplectic_weylInputsSC hin hp hpn hn hlab.2.1 hQ

theorem ggCorFiveTwentyWeylInputsOn_spNonsplit_of_input (hin : GGSpNonsplitTorusInput) :
    GGWeylPseudoReflGenInputOn GGSpNonsplitLabel ∧
      GGWeylCentralizerScalarInputOn GGSpNonsplitLabel ∧
      GGCorFiveTwentyOuterInputOn GGSpNonsplitLabel :=
  ⟨ggWeylPseudoReflGenInputOn_of_labelsSC fun _ _ hp hlab h =>
      (largeEvenLabelAll_weylInputsSC_spNonsplit hin hp hlab h).mono fun _ _ _ _ hP => hP.1,
    ggWeylCentralizerScalarInputOn_of_labelsSC fun _ _ hp hlab h =>
      (largeEvenLabelAll_weylInputsSC_spNonsplit hin hp hlab h).mono fun _ _ _ _ hP => hP.2.1,
    ggCorFiveTwentyOuterInputOn_of_labelsSC fun _ _ hp hlab h =>
      (largeEvenLabelAll_weylInputsSC_spNonsplit hin hp hlab h).mono
        fun _ _ _ _ hP => ⟨hP.1, hP.2.2⟩⟩

@[expose] def GGCorFiveTwentyRestUSLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  GGCorFiveTwentyRestULabel p lab ∧ ¬ GGSpNonsplitLabel p lab

theorem ggCorFiveTwentyWeylInputsOn_restU_of_restUS (hin : GGSpNonsplitTorusInput)
    (hG : GGWeylPseudoReflGenInputOn GGCorFiveTwentyRestUSLabel)
    (hSc : GGWeylCentralizerScalarInputOn GGCorFiveTwentyRestUSLabel)
    (hO : GGCorFiveTwentyOuterInputOn GGCorFiveTwentyRestUSLabel) :
    GGWeylPseudoReflGenInputOn GGCorFiveTwentyRestULabel ∧
      GGWeylCentralizerScalarInputOn GGCorFiveTwentyRestULabel ∧
      GGCorFiveTwentyOuterInputOn GGCorFiveTwentyRestULabel := by
  have hsplit : ∀ p lab, GGCorFiveTwentyRestULabel p lab →
      GGSpNonsplitLabel p lab ∨ GGCorFiveTwentyRestUSLabel p lab := fun p lab h => by
    by_cases hs : GGSpNonsplitLabel p lab
    · exact Or.inl hs
    · exact Or.inr ⟨h, hs⟩
  obtain ⟨h₁, h₂, h₃⟩ := ggCorFiveTwentyWeylInputsOn_spNonsplit_of_input hin
  exact ⟨ggWeylPseudoReflGenInputOn_of_split hsplit h₁ hG,
    ggWeylCentralizerScalarInputOn_of_split hsplit h₂ hSc,
    ggCorFiveTwentyOuterInputOn_of_split hsplit h₃ hO⟩

theorem ggCorFiveTwentyInput_of_stab_restUS
    (ha₀ : GGLNoncyclicInput)
    (hRL : GGPseudoReflStabInput) (hRO : GGPseudoReflOrbitInput) (hin : GGSpNonsplitTorusInput)
    (hG : GGWeylPseudoReflGenInputOn GGCorFiveTwentyRestUSLabel)
    (hSc : GGWeylCentralizerScalarInputOn GGCorFiveTwentyRestUSLabel)
    (hO : GGCorFiveTwentyOuterInputOn GGCorFiveTwentyRestUSLabel) : GGCorFiveTwentyInput :=
  let h := ggCorFiveTwentyWeylInputsOn_restU_of_restUS hin hG hSc hO
  ggCorFiveTwentyInput_of_stab_restU ha₀ hRL hRO h.1 h.2.1 h.2.2

theorem ggCorFiveTwentyInput_of_reflRest_restUS
    (ha₀ : GGLNoncyclicInput)
    (hBL4 : GGNbrSStarInput) (hrest : GGPseudoReflStabModInputOn GGReflRestLabel)
    (hnrest : GGPseudoReflNbrStabModInputOn GGReflRestLabel) (hA : GGPseudoReflAwayInput)
    (hin : GGSpNonsplitTorusInput)
    (hG : GGWeylPseudoReflGenInputOn GGCorFiveTwentyRestUSLabel)
    (hSc : GGWeylCentralizerScalarInputOn GGCorFiveTwentyRestUSLabel)
    (hO : GGCorFiveTwentyOuterInputOn GGCorFiveTwentyRestUSLabel) : GGCorFiveTwentyInput :=
  let h := ggCorFiveTwentyWeylInputsOn_restU_of_restUS hin hG hSc hO
  ggCorFiveTwentyInput_of_reflRest_restU ha₀ hBL4 hrest hnrest hA h.1 h.2.1 h.2.2

end CFSG.StandardType

end
