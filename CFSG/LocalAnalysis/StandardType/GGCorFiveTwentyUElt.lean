module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUCoord
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpElt
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs
public import CFSG.LocalAnalysis.StandardType.GGR4PumpDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly UCoord

section Lift

variable {L' R : Type} [Group L'] [Group R] {ψ : L' →* R} {p : ℕ}

theorem eq_one_of_mem_ker_of_pow [Finite L'] (hp : p.Prime) (hker : ψ.ker ≤ Subgroup.center L')
    (hcp : ¬ p ∣ Nat.card (Subgroup.center L')) {z : L'} (hz : z ∈ ψ.ker) (hzp : z ^ p = 1) :
    z = 1 := by
  have := Fact.mk hp
  by_contra hz1
  apply hcp
  have h1 : orderOf (⟨z, hker hz⟩ : Subgroup.center L') = p := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hzp hz1
  rw [← h1]
  exact orderOf_dvd_natCard _

theorem exists_lift_pow_eq_one [Finite L'] (hp : p.Prime) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hcp : ¬ p ∣ Nat.card (Subgroup.center L'))
    {g : R} (hg : g ^ p = 1) : ∃ n : L', ψ n = g ∧ n ^ p = 1 := by
  obtain ⟨n₀, rfl⟩ := hψ g
  set z := n₀ ^ p with hz
  have hzk : z ∈ ψ.ker := by rw [MonoidHom.mem_ker, hz, map_pow, hg]
  have hcop : p.Coprime (orderOf z) := by
    rw [Nat.Prime.coprime_iff_not_dvd hp]
    intro hdvd
    apply hcp
    have h1 : orderOf (⟨z, hker hzk⟩ : Subgroup.center L') = orderOf z := Subgroup.orderOf_mk _ _
    exact hdvd.trans (h1 ▸ orderOf_dvd_natCard _)
  obtain ⟨t, ht⟩ := exists_pow_eq_self_of_coprime hcop
  have hcomm : Commute n₀ (z ^ t)⁻¹ :=
    Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ (Subgroup.pow_mem _ (hker hzk) t)) n₀
  refine ⟨n₀ * (z ^ t)⁻¹, ?_, ?_⟩
  · rw [map_mul, map_inv, map_pow, MonoidHom.mem_ker.mp hzk, one_pow, inv_one, mul_one]
  · rw [hcomm.mul_pow, ← hz, inv_pow, ← pow_mul, mul_comm t p, pow_mul, ht, mul_inv_cancel]

theorem eq_of_lift_pow_eq_one [Finite L'] (hp : p.Prime) (hker : ψ.ker ≤ Subgroup.center L')
    (hcp : ¬ p ∣ Nat.card (Subgroup.center L')) {x y : L'} (hxy : ψ x = ψ y) (hx : x ^ p = 1)
    (hy : y ^ p = 1) : x = y := by
  set z := x⁻¹ * y with hz
  have hzk : z ∈ ψ.ker := by rw [MonoidHom.mem_ker, hz, map_mul, map_inv, hxy, inv_mul_cancel]
  have hyz : y = x * z := by rw [hz, mul_inv_cancel_left]
  have hcomm : Commute x z := Subgroup.mem_center_iff.mp (hker hzk) x
  have hzp : z ^ p = 1 := by
    have h1 := hy
    rw [hyz, hcomm.mul_pow, hx, one_mul] at h1
    exact h1
  rw [hyz, eq_one_of_mem_ker_of_pow hp hker hcp hzk hzp, mul_one]

theorem commute_of_lift_pow_eq_one [Finite L'] (hp : p.Prime) (hker : ψ.ker ≤ Subgroup.center L')
    (hcp : ¬ p ∣ Nat.card (Subgroup.center L')) {x y : L'} (hxy : ψ x * ψ y = ψ y * ψ x)
    (hy : y ^ p = 1) : x * y = y * x := by
  have h1 : x * y * x⁻¹ = y := by
    refine eq_of_lift_pow_eq_one hp hker hcp ?_ ?_ hy
    · rw [map_mul, map_mul, map_inv, hxy, mul_inv_cancel_right]
    · rw [conj_pow, hy, mul_one, mul_inv_cancel]
  calc x * y = x * y * x⁻¹ * x := by group
    _ = y * x := by rw [h1]

theorem exists_section_of_centerPrime [Finite L'] (hp : p.Prime) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hcp : ¬ p ∣ Nat.card (Subgroup.center L'))
    {V : Type*} [CommGroup V] (hV : ∀ v : V, v ^ p = 1) (τ : V →* R) :
    ∃ s : V →* L', (∀ v, ψ (s v) = τ v) ∧ ∀ v, s v ^ p = 1 := by
  choose s hs hsp using fun v => exists_lift_pow_eq_one hp hψ hker hcp (g := τ v)
    (by rw [← map_pow, hV, map_one])
  have hmul : ∀ v w, s (v * w) = s v * s w := by
    intro v w
    have hc : s v * s w = s w * s v := commute_of_lift_pow_eq_one hp hker hcp
      (by rw [hs, hs, ← map_mul, ← map_mul, mul_comm]) (hsp w)
    refine eq_of_lift_pow_eq_one hp hker hcp ?_ (hsp _) ?_
    · rw [map_mul ψ, hs, hs, hs, map_mul]
    · rw [(show Commute (s v) (s w) from hc).mul_pow, hsp, hsp, one_mul]
  exact ⟨MonoidHom.mk' s hmul, hs, hsp⟩

end Lift

@[expose] def GGTorusPermEltSC (p d : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ 3 ≤ Nat.card E →
    (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
    ∃ τ : ↥(sumZero d p) →* R, Function.Injective τ ∧ τ.range = E ∧
      (∀ σ : Equiv.Perm (Fin d), ∃ w : R, ∀ f, w * τ f * w⁻¹ = τ (permAutV σ f)) ∧
      ∀ g : R, (∀ e ∈ E, g * e * g⁻¹ ∈ E) →
        ∃ π : Equiv.Perm (Fin d), ∀ f, g * τ f * g⁻¹ = τ (permAutV π f)

section Model

variable {p d : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem exists_permModel (hp : p.Prime) (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (h : GGTorusPermEltSC p d R) {L' : Type} [Group L'] [Finite L']
    {ψ : L' →* R} (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) (h3 : p ^ 3 ≤ Nat.card A)
    (hsc : GGTorusSelfCent p A) :
    ∃ Θ : ↥(sumZero d p) ≃* ↥A,
      (∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
        GGTorusWeylElt p A n) ∧
      (∀ σ : Equiv.Perm (Fin d), ∃ (n : L')
        (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ggConjAut A hn = MulAut.congr Θ (permAutV σ)) ∧
      ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
        ∃ π : Equiv.Perm (Fin d), ggConjAut A hn = MulAut.congr Θ (permAutV π) := by
  classical
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
    have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
    have hφp : φ ^ p = 1 := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ r
      rw [hk, hA.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ := hIp φ hφI hφp
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
  obtain ⟨τ, hτinj, hτE, hperm, hnorm⟩ := h E hEab (hcardE ▸ h3) hscE
  have hτmem : ∀ f, Λ (τ f) ∈ A := fun f => by
    have : τ f ∈ E := hτE ▸ ⟨f, rfl⟩
    exact this
  set Θ₀ : ↥(sumZero d p) →* ↥A := (Λ.comp τ).codRestrict A hτmem with hΘ₀
  have hΘ₀bij : Function.Bijective Θ₀ := by
    refine ⟨fun f g hfg => hτinj (hΛinj (congrArg Subtype.val hfg)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    have heE : e ∈ E := show Λ e ∈ A from he ▸ a.2
    rw [← hτE] at heE
    obtain ⟨f, rfl⟩ := heE
    exact ⟨f, Subtype.ext he⟩
  set Θ : ↥(sumZero d p) ≃* ↥A := MulEquiv.ofBijective Θ₀ hΘ₀bij with hΘ
  have hΘval : ∀ f, ((Θ f : ↥A) : MulAut L') = Λ (τ f) := fun f => rfl
  obtain ⟨s, hs, hsp⟩ := exists_section_of_centerPrime hp hψ hker hcpL
    (V := ↥(sumZero d p)) pow_p_eq_one τ
  have hΘs : ∀ f, ((Θ f : ↥A) : MulAut L') = MulAut.conj (s f) := fun f =>
    (hΘval f).trans (hΛeq (hs f))
  have hlift : ∀ (n : L') (α : MulAut ↥(sumZero d p)),
      (∀ f, ψ n * τ f * (ψ n)⁻¹ = τ (α f)) →
        ∃ hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')),
          ggConjAut A hn = MulAut.congr Θ α := by
    intro n α hw
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
    refine ⟨hn, MulEquiv.ext fun a => Subtype.ext ?_⟩
    obtain ⟨f, rfl⟩ := Θ.surjective a
    rw [ggConjAut_apply, hconjΘ, MulAut.congr_apply]
    simp
  have hNE : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ∀ f, ∃ f', ψ n * τ f * (ψ n)⁻¹ = τ f' := by
    intro n hn f
    have h1 : Λ (ψ n * τ f * (ψ n)⁻¹) ∈ A := by
      rw [map_mul, map_mul, map_inv, hΛn]
      exact (Subgroup.mem_normalizer_iff.mp hn _).mp (hτmem f)
    have h2 : ψ n * τ f * (ψ n)⁻¹ ∈ τ.range := hτE ▸ h1
    obtain ⟨f', hf'⟩ := h2
    exact ⟨f', hf'.symm⟩
  refine ⟨Θ, fun n hn => ?_, fun σ => ?_, fun n hn => ?_⟩
  ·
    intro a ha
    obtain ⟨f, hf⟩ := Θ.surjective ⟨a, ha⟩
    have has : a = MulAut.conj (s f) := by rw [← hΘs, hf]
    obtain ⟨f', hf'⟩ := hNE n hn f
    have hconj : n * s f * n⁻¹ = s f' := by
      refine eq_of_lift_pow_eq_one hp hker hcpL ?_ ?_ (hsp f')
      · rw [map_mul, map_mul, map_inv, hs, hs, hf']
      · rw [conj_pow, hsp, mul_one, mul_inv_cancel]
    have he : n * (a n)⁻¹ = s (f' * f⁻¹) := by
      rw [has, MulAut.conj_apply, map_mul, map_inv, ← hconj]
      group
    rw [he]
    refine ⟨by rw [← map_pow, pow_p_eq_one, map_one], fun a' ha' => ?_⟩
    obtain ⟨f'', hf''⟩ := Θ.surjective ⟨a', ha'⟩
    have ha's : a' = MulAut.conj (s f'') := by rw [← hΘs, hf'']
    have hc : s f'' * s (f' * f⁻¹) = s (f' * f⁻¹) * s f'' := by
      rw [← map_mul, ← map_mul, mul_comm]
    rw [ha's, MulAut.conj_apply, hc, mul_inv_cancel_right]
  ·
    obtain ⟨w, hw⟩ := hperm σ
    obtain ⟨n, rfl⟩ := hψ w
    obtain ⟨hn, hnα⟩ := hlift n _ hw
    exact ⟨n, hn, hnα⟩
  ·
    have hNE' : ∀ e ∈ E, ψ n * e * (ψ n)⁻¹ ∈ E := by
      intro e he
      rw [← hτE] at he ⊢
      obtain ⟨f, rfl⟩ := he
      obtain ⟨f', hf'⟩ := hNE n hn f
      exact ⟨f', hf'.symm⟩
    obtain ⟨π, hπ⟩ := hnorm (ψ n) hNE'
    obtain ⟨hn', hnα⟩ := hlift n _ hπ
    exact ⟨π, hnα⟩

end Model

section AutCard

variable {p d : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

private theorem sumZero_pow_le_card (m p : ℕ) [NeZero p] :
    p ^ m ≤ Nat.card ↥(sumZero (m + 1) p) := by
  let G : (Fin m → ZMod p) → ↥(sumZero (m + 1) p) := fun v =>
    ⟨fun k => Multiplicative.ofAdd ((Fin.cons (-∑ i, v i) v : Fin (m + 1) → ZMod p) k), by
      show ∑ k, (Fin.cons (-∑ i, v i) v : Fin (m + 1) → ZMod p) k = 0
      rw [Fin.sum_univ_succ, Fin.cons_zero]
      simp only [Fin.cons_succ]
      exact neg_add_cancel _⟩
  have hG : Function.Injective G := by
    intro v w hvw
    funext i
    have h1 := congrFun (congrArg Subtype.val hvw) i.succ
    simp only [G, Fin.cons_succ] at h1
    exact Multiplicative.ofAdd.injective h1
  calc p ^ m = Nat.card (Fin m → ZMod p) := by
        rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
    _ ≤ Nat.card ↥(sumZero (m + 1) p) := Nat.card_le_card_of_injective G hG

theorem ggTorusAutCardSC_of_permEltSC (hp : p.Prime) (hp2 : p ≠ 2) (hd : 1 ≤ d)
    (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (hmodel : GGTorusPermEltSC p d R) :
    GGTorusAutCardSC p R I (d - 1) d.factorial := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc
  obtain ⟨Θ, -, hP, hN⟩ := exists_permModel hp hZ hIp hcp hmodel hψ hker hperf hA hAI h3 hsc
  refine ⟨?_, ?_⟩
  ·
    have : NeZero p := ⟨hp.ne_zero⟩
    have hcardA : Nat.card A = Nat.card ↥(sumZero d p) :=
      (Nat.card_congr Θ.toEquiv).symm
    rw [hcardA]
    obtain ⟨m, rfl⟩ : ∃ m, d = m + 1 := ⟨d - 1, by omega⟩
    simpa using sumZero_pow_le_card m p
  ·
    let ρ : Equiv.Perm (Fin d) →* MulAut ↥A :=
      (MulAut.congr Θ).toMonoidHom.comp (permAutVHom d p)
    have hρapply : ∀ σ, ρ σ = MulAut.congr Θ (permAutV σ) := fun σ => rfl
    have hρinj : Function.Injective ρ := by
      intro σ τ h
      apply permAutV_injective hp hp2
      exact (MulAut.congr Θ).injective h
    have hWmem : ∀ σ : Equiv.Perm (Fin d),
        MulAut.congr Θ (permAutV σ) ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A := by
      intro σ
      obtain ⟨n, hn, hnα⟩ := hP σ
      rw [← hnα]
      exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
    have hWperm : ∀ v ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A,
        ∃ σ : Equiv.Perm (Fin d), v = MulAut.congr Θ (permAutV σ) := by
      intro v hv
      obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hv
      have hv' : v = ggConjAut A hcN := MulEquiv.ext fun a => Subtype.ext (hvc a)
      obtain ⟨π, hπ⟩ := hN n hcN
      exact ⟨π, hv'.trans hπ⟩
    have hWρ : ggAutomizer (MulAut.conj : L' →* MulAut L').range A = ρ.range := by
      apply le_antisymm
      · intro v hv
        obtain ⟨σ, rfl⟩ := hWperm v hv
        exact ⟨σ, hρapply σ⟩
      · rintro _ ⟨σ, rfl⟩
        rw [hρapply]
        exact hWmem σ
    have hcard : Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A) = d.factorial := by
      rw [hWρ]
      have hrange : Nat.card ↥ρ.range = Nat.card (Equiv.Perm (Fin d)) :=
        (Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv).symm
      rw [hrange, Nat.card_perm, Nat.card_fin]
    exact hcard

end AutCard

section Transfer

variable {p d : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem ggTorusPseudoReflGenSC_of_permElt (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (h : GGTorusPermEltSC p d R) : GGTorusPseudoReflGenSC p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc v hv
  obtain ⟨Θ, hW, hP, hN⟩ := exists_permModel hp hZ hIp hcp h hψ hker hperf hA hAI h3 hsc
  obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hv
  have hv' : v = ggConjAut A hcN := MulEquiv.ext fun a => Subtype.ext (hvc a)
  obtain ⟨π, hπ⟩ := hN n hcN
  set H : Subgroup (MulAut ↥(sumZero d p)) :=
    (Subgroup.closure (ggTorusPseudoReflSet p A)).comap (MulAut.congr Θ).toMonoidHom with hH
  have hsw : ∀ i j : Fin d, i ≠ j → permAutV (Equiv.swap i j) ∈ H := by
    intro i j hij
    obtain ⟨m, hm, hmα⟩ := hP (Equiv.swap i j)
    obtain ⟨hpow, hfix⟩ := isPseudoReflection_permAutV_swap hp hp2 hij
    exact Subgroup.subset_closure ⟨m, hm, hW m hm, hmα.symm,
      ggIsPseudoReflection_congr Θ hpow hfix⟩
  have hmem := mem_closure_permAutV hsw π
  rw [hH, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom] at hmem
  rw [hv', hπ]
  exact hmem

theorem ggTorusSchurSC_of_permElt (hp : p.Prime) (hp2 : p ≠ 2) (hd : 2 ≤ d) (hpd : ¬ p ∣ d)
    (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (h : GGTorusPermEltSC p d R) : GGTorusSchurSC p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc
  obtain ⟨Θ, hW, hP, -⟩ := exists_permModel hp hZ hIp hcp h hψ hker hperf hA hAI h3 hsc
  refine ⟨{n | MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))}, fun n hn => hW n hn,
    fun F hFA hFmul hFW => ?_⟩
  have hF1 : F 1 = 1 := by
    have h1 := hFmul 1 A.one_mem 1 A.one_mem
    rw [mul_one] at h1
    exact (mul_eq_left.mp h1.symm)
  let Fc : ↥(sumZero d p) →* ↥(sumZero d p) :=
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
  have hcomm : ∀ (σ : Equiv.Perm (Fin d)) (g : ↥(sumZero d p)),
      Fc (permAutV σ g) = permAutV σ (Fc g) := by
    intro σ g
    obtain ⟨n, hn, hnα⟩ := hP σ
    apply Θ.injective
    apply Subtype.ext
    rw [hFc, ← coe_conj_of_ggConjAut_eq Θ hnα, ← coe_conj_of_ggConjAut_eq Θ hnα, hFc]
    exact hFW n hn _ (Θ g).2
  obtain ⟨c, hc⟩ := exists_pow_of_commute_permAutV hp hp2 hd hpd Fc hcomm
  refine ⟨c, fun a ha => ?_⟩
  obtain ⟨g, hg⟩ := Θ.surjective ⟨a, ha⟩
  have h1 := hFc g
  rw [hc, map_pow, hg] at h1
  rw [← h1]
  rfl

theorem ggTorusWeylNormInnerSC_of_permElt (hp : p.Prime) (hp2 : p ≠ 2) (hd : 4 ≤ d)
    (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (h : GGTorusPermEltSC p d R) : GGTorusWeylNormInnerSC p R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI h3 hsc φ hφ
  obtain ⟨Θ, -, hP, hN⟩ := exists_permModel hp hZ hIp hcp h hψ hker hperf hA hAI h3 hsc
  set W := ggAutomizer (MulAut.conj : L' →* MulAut L').range A with hWdef
  have hWin : ∀ σ : Equiv.Perm (Fin d), MulAut.congr Θ (permAutV σ) ∈ W := by
    intro σ
    obtain ⟨n, hn, hnα⟩ := hP σ
    rw [← hnα]
    exact ggConjAut_mem_ggAutomizer (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hn
  have hWperm : ∀ v ∈ W, ∃ σ : Equiv.Perm (Fin d), v = MulAut.congr Θ (permAutV σ) := by
    intro v hv
    obtain ⟨c, ⟨n, rfl⟩, hcN, hvc⟩ := mem_ggAutomizer_iff.mp hv
    have hv' : v = ggConjAut A hcN := MulEquiv.ext fun a => Subtype.ext (hvc a)
    obtain ⟨π, hπ⟩ := hN n hcN
    exact ⟨π, hv'.trans hπ⟩
  set φ' := (MulAut.congr Θ).symm φ with hφ'
  have hφφ' : φ = MulAut.congr Θ φ' := (MulEquiv.apply_symm_apply _ _).symm
  have hnorm : ∀ σ : Equiv.Perm (Fin d), ∃ τ, φ' * permAutV σ * φ'⁻¹ = permAutV τ := by
    intro σ
    have h1 : φ * MulAut.congr Θ (permAutV σ) * φ⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp hφ _).mp (hWin σ)
    obtain ⟨τ, hτ⟩ := hWperm _ h1
    refine ⟨τ, (MulAut.congr Θ).injective ?_⟩
    rw [map_mul, map_mul, map_inv, ← hφφ', hτ]
  obtain ⟨π₀, hπ₀⟩ := exists_eq_conj_of_normalizes hp hp2 hd hnorm
  refine ⟨MulAut.congr Θ (permAutV π₀), hWin π₀, fun v hv => ?_⟩
  obtain ⟨σ, rfl⟩ := hWperm v hv
  have key : φ' * permAutV σ * φ'⁻¹ = permAutV π₀ * permAutV σ * (permAutV π₀)⁻¹ := by
    rw [hπ₀ σ, permAutV_mul, permAutV_mul, ← permAutVHom_apply π₀⁻¹, map_inv,
      permAutVHom_apply]
  calc φ * MulAut.congr Θ (permAutV σ) * φ⁻¹
      = MulAut.congr Θ (φ' * permAutV σ * φ'⁻¹) := by rw [hφφ', map_mul, map_mul, map_inv]
    _ = MulAut.congr Θ (permAutV π₀ * permAutV σ * (permAutV π₀)⁻¹) := by rw [key]
    _ = _ := by rw [map_mul, map_mul, map_inv]

end Transfer

end CFSG.StandardType

end
