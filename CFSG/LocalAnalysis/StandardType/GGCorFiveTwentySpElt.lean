module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestGen
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyReflInner

public section

namespace CFSG.StandardType

open CFSG.Assembly SpCoord Multiplicative

@[expose] def GGTorusSignedElt (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E → p ^ 3 ≤ Nat.card E →
    ∃ (k : ℕ) (τ : (Fin k → Multiplicative (ZMod p)) →* R), Function.Injective τ ∧
      τ.range = E ∧
      (∀ i : Fin k, ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (sgnAut i f)) ∧
      (∀ σ : Equiv.Perm (Fin k), ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (permAut σ f)) ∧
      ∀ g : R, (∀ e ∈ E, g * e * g⁻¹ ∈ E) →
        ∃ (π : Equiv.Perm (Fin k)) (ε : Fin k → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
          ∀ f f', g * τ f * g⁻¹ = τ f' → ∀ i, toAdd (f' (π i)) = ε i * toAdd (f i)

theorem ggTorusSignedElt_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : GGTorusSignedElt p r R') : GGTorusSignedElt p r R := by
  intro E hE hr h3
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    (Nat.card_congr (E.equivMapOfInjective _ e.injective).toEquiv).symm
  have hmem : ∀ x : R, e x ∈ E.map e.toMonoidHom ↔ x ∈ E := fun x =>
    ⟨fun ⟨y, hy, hyx⟩ => e.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  obtain ⟨k, τ, hτinj, hτE, hsgn, hperm, hnorm⟩ :=
    h (E.map e.toMonoidHom) (TableB.isElemAbelian_map hE _) (hcard ▸ hr) (hcard ▸ h3)
  have hconj : ∀ (w : R') (f f' : Fin k → Multiplicative (ZMod p)),
      w * τ f * w⁻¹ = τ f' → e.symm w * e.symm (τ f) * (e.symm w)⁻¹ = e.symm (τ f') := by
    intro w f f' h
    rw [← map_inv, ← map_mul, ← map_mul, h]
  refine ⟨k, e.symm.toMonoidHom.comp τ, e.symm.injective.comp hτinj, ?_, fun i => ?_,
    fun σ => ?_, fun g hg => ?_⟩
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
  · obtain ⟨w, hw⟩ := hsgn i
    exact ⟨e.symm w, fun f => hconj w f _ (hw f)⟩
  · obtain ⟨w, hw⟩ := hperm σ
    exact ⟨e.symm w, fun f => hconj w f _ (hw f)⟩
  · have hg' : ∀ x ∈ E.map e.toMonoidHom, e g * x * (e g)⁻¹ ∈ E.map e.toMonoidHom := by
      rintro _ ⟨y, hy, rfl⟩
      refine ⟨g * y * g⁻¹, hg y hy, ?_⟩
      simp
    obtain ⟨π, ε, hε, hrel⟩ := hnorm (e g) hg'
    refine ⟨π, ε, hε, fun f f' hff' => hrel f f' ?_⟩
    apply e.symm.injective
    rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
    exact hff'

section Model

variable {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem exists_signedModel (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (h : GGTorusSignedElt p r R) {L' : Type} [Group L'] [Finite L'] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l))
    (hr : p ^ r ≤ Nat.card A) (h3 : p ^ 3 ≤ Nat.card A) :
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
  obtain ⟨k, τ, hτinj, hτE, hsgn, hperm, hnorm⟩ := h E hEab (hcardE ▸ hr) (hcardE ▸ h3)
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

end Model

section Congr

theorem coe_conj_of_ggConjAut_eq {L' V : Type} [Group L'] [Group V] {A : Subgroup (MulAut L')}
    (Θ : V ≃* ↥A) {n : L'} {hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))}
    {α : MulAut V} (h : ggConjAut A hn = MulAut.congr Θ α) (f : V) :
    MulAut.conj n * ((Θ f : ↥A) : MulAut L') * (MulAut.conj n)⁻¹ =
      ((Θ (α f) : ↥A) : MulAut L') := by
  have h1 := congrArg (fun φ : MulAut ↥A => ((φ (Θ f) : ↥A) : MulAut L')) h
  simp only [ggConjAut_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h1
  exact h1

theorem ggIsPseudoReflection_congr {p : ℕ} {G : Type} [Group G] {A : Subgroup G} {V : Type}
    [Group V] (Θ : V ≃* ↥A) {s : MulAut V} (hs : s ^ (p - 1) = 1)
    (hfix : Nat.card {f : V // s f = f} * p = Nat.card V) :
    GGIsPseudoReflection p (MulAut.congr Θ s) := by
  refine ⟨by rw [← map_pow, hs, map_one], ?_⟩
  have h1 : Nat.card {a : ↥A // MulAut.congr Θ s a = a} = Nat.card {f : V // s f = f} := by
    refine Nat.card_congr (Equiv.subtypeEquiv Θ.symm.toEquiv fun a => ?_)
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.toEquiv_eq_coe,
      MulEquiv.coe_toEquiv]
    constructor
    · intro h
      have h' := congrArg Θ.symm h
      rwa [MulEquiv.symm_apply_apply] at h'
    · intro h
      rw [h, MulEquiv.apply_symm_apply]
  rw [h1, hfix]
  exact Nat.card_congr Θ.toEquiv

theorem conj_eq_of_forall_eq_pow {M : Type*} [Group M] {φ w : MulAut M} {c : ℕ}
    (h : ∀ a, φ a = (w a) ^ c) (v : MulAut M) : φ * v * φ⁻¹ = w * v * w⁻¹ := by
  refine MulEquiv.ext fun a => ?_
  obtain ⟨b, rfl⟩ := φ.surjective a
  simp only [MulAut.mul_apply, MulAut.inv_apply_self]
  rw [h (v b), h b]
  simp only [map_pow, MulAut.inv_apply_self]

end Congr

section Transfer

variable {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem ggTorusPseudoReflGen_of_signedElt (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (h : GGTorusSignedElt p r R) : GGTorusPseudoReflGen p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 v hv
  obtain ⟨k, Θ, -, hW, hS, hP, hN⟩ :=
    exists_signedModel hp hp2 hI hZ h hψ hker hperf hA hAI hr h3
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

theorem ggTorusIrred_of_signedElt (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (h : GGTorusSignedElt p r R) : GGTorusIrred p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3
  obtain ⟨k, Θ, hk, hW, hS, hP, -⟩ :=
    exists_signedModel hp hp2 hI hZ h hψ hker hperf hA hAI hr h3
  refine ⟨{n | MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))}, fun n hn => hW n hn,
    fun A' hA'A hinv => ?_, ?_, fun F hFA hFmul hFW => ?_⟩
  ·
    set F : Subgroup (Fin k → Multiplicative (ZMod p)) :=
      (A'.subgroupOf A).comap Θ.toMonoidHom with hF
    have hmemF : ∀ f, f ∈ F ↔ ((Θ f : ↥A) : MulAut L') ∈ A' := fun f => Iff.rfl
    have hstab : ∀ α : MulAut (Fin k → Multiplicative (ZMod p)),
        (∃ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
          ggConjAut A hn = MulAut.congr Θ α) → ∀ f ∈ F, α f ∈ F := by
      rintro α ⟨n, hn, hnα⟩ f hf
      rw [hmemF, ← coe_conj_of_ggConjAut_eq Θ hnα]
      exact hinv n hn _ ((hmemF f).mp hf)
    rcases NbrSp.eq_bot_or_eq_top_of_signed hp hp2 F (fun i f hf => hstab _ (hS i) f hf)
        (fun σ f hf => hstab _ (hP σ) f hf) with hbot | htop
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
  ·
    have hk0 : 0 < k := by omega
    obtain ⟨n, hn, hnα⟩ := hS ⟨0, hk0⟩
    refine ⟨n, hn, _, (Θ (Pi.mulSingle ⟨0, hk0⟩ (ofAdd 1))).2, fun heq => ?_⟩
    rw [coe_conj_of_ggConjAut_eq Θ hnα, sgnAut_mulSingle_self] at heq
    have h1 := congrArg (fun f : Fin k → Multiplicative (ZMod p) => toAdd (f ⟨0, hk0⟩))
      (Θ.injective (Subtype.ext heq))
    simp only [Pi.inv_apply, Pi.mulSingle_eq_same, toAdd_inv, toAdd_ofAdd] at h1
    exact coord_two_ne_zero hp hp2 (by linear_combination -h1)
  ·
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

theorem ggTorusWeylNormInner_of_signedElt (hp : p.Prime) (hp2 : p ≠ 2)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (h : GGTorusSignedElt p r R) : GGTorusWeylNormInner p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 φ hφ
  obtain ⟨k, Θ, hk, -, hS, hP, hN⟩ :=
    exists_signedModel hp hp2 hI hZ h hψ hker hperf hA hAI hr h3
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
  refine ⟨MulAut.congr Θ w, (hcongr w).mp hw, fun v _ => conj_eq_of_forall_eq_pow (c := c)
    (fun a => ?_) v⟩
  obtain ⟨f, rfl⟩ := Θ.surjective a
  rw [hφφ', MulAut.congr_apply, MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [hc, map_pow]

end Transfer

end CFSG.StandardType

end
