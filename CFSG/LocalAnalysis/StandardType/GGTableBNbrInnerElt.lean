module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerCore
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticCover

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB TableBSymp

@[expose] def GGTorusIrredElt (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E → p ^ 3 ≤ Nat.card E →
    ∃ (k : ℕ) (τ : (Fin k → Multiplicative (ZMod p)) →* R) (W : Set R), τ.range = E ∧
      (∀ i j : Fin k, ∃ w : R, w * torusBasis τ i * w⁻¹ = (torusBasis τ i)⁻¹ ∧
        (j ≠ i → w * torusBasis τ j * w⁻¹ = torusBasis τ j)) ∧
      (∀ w ∈ W, ∀ e ∈ E, w * e * w⁻¹ ∈ E) ∧
      ∀ E' : Subgroup R, E' ≤ E → (∀ w ∈ W, ∀ e ∈ E', w * e * w⁻¹ ∈ E') → E' = ⊥ ∨ E' = E

theorem ggTorusIrredElt_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : GGTorusIrredElt p r R') : GGTorusIrredElt p r R := by
  intro E hE hr h3
  have hcard : Nat.card (E.map e.toMonoidHom) = Nat.card E :=
    (Nat.card_congr (E.equivMapOfInjective _ e.injective).toEquiv).symm
  obtain ⟨k, τ, W, hτE, hinv, hWE, hirr⟩ :=
    h (E.map e.toMonoidHom) (isElemAbelian_map hE _) (hcard ▸ hr) (hcard ▸ h3)
  have hmem : ∀ x : R, e x ∈ E.map e.toMonoidHom ↔ x ∈ E := fun x =>
    ⟨fun ⟨y, hy, hyx⟩ => e.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  refine ⟨k, e.symm.toMonoidHom.comp τ, e.symm '' W, ?_, fun i j => ?_, ?_, fun E' hE' hinv' => ?_⟩
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
  · obtain ⟨w, hw1, hw2⟩ := hinv i j
    refine ⟨e.symm w, ?_, fun hji => ?_⟩
    · apply e.injective
      simpa [torusBasis] using hw1
    · apply e.injective
      simpa [torusBasis] using hw2 hji
  · rintro _ ⟨w, hw, rfl⟩ x hx
    rw [← hmem]
    simpa using hWE w hw (e x) ((hmem x).mpr hx)
  · have hle : E'.map e.toMonoidHom ≤ E.map e.toMonoidHom := Subgroup.map_mono hE'
    have hinv'' : ∀ w ∈ W, ∀ x ∈ E'.map e.toMonoidHom, w * x * w⁻¹ ∈ E'.map e.toMonoidHom := by
      rintro w hw _ ⟨y, hy, rfl⟩
      refine ⟨_, hinv' (e.symm w) ⟨w, hw, rfl⟩ y hy, ?_⟩
      simp
    rcases hirr _ hle hinv'' with h1 | h1
    · left
      rw [eq_bot_iff]
      intro x hx
      have : e x ∈ E'.map e.toMonoidHom := ⟨x, hx, rfl⟩
      rw [h1, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at this
      exact this ▸ Subgroup.one_mem _
    · right
      refine le_antisymm hE' fun x hx => ?_
      have : e x ∈ E'.map e.toMonoidHom := h1 ▸ (hmem x).mpr hx
      obtain ⟨y, hy, hyx⟩ := this
      exact e.injective hyx ▸ hy

@[expose] def GGTorusSecElt (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E → p ^ 3 ≤ Nat.card E →
    ∃ (k : ℕ) (τ : (Fin k → Multiplicative (ZMod p)) →* R) (W : Set R), τ.range = E ∧
      (∀ (L' : Type) [Group L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → ∃ σ : (Fin k → Multiplicative (ZMod p)) →* L', ψ.comp σ = τ) ∧
      (∀ w ∈ W, ∀ e ∈ E, w * e * w⁻¹ ∈ E) ∧
      ∀ E' : Subgroup R, E' ≤ E → (∀ w ∈ W, ∀ e ∈ E', w * e * w⁻¹ ∈ E') → E' = ⊥ ∨ E' = E

theorem ggTorusSecElt_of_irredElt {p r : ℕ} (hp : Odd p) {R : Type} [Group R]
    (h : GGTorusIrredElt p r R) : GGTorusSecElt p r R := by
  intro E hE hr h3
  obtain ⟨k, τ, W, hτE, hinv, hWE, hirr⟩ := h E hE hr h3
  exact ⟨k, τ, W, hτE, fun L' _ ψ hψ hker => exists_torus_section hψ hker hp τ hinv, hWE, hirr⟩

theorem ggTorusNbr_of_secElt {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (h : GGTorusSecElt p r R) : GGTorusNbr p r R I := by
  classical
  have := Fact.mk hp
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3
  have hex : ∀ a : A, ∃ t : R, ∀ l, ψ ((a : MulAut L') l) = t * ψ l * t⁻¹ := by
    intro a
    obtain ⟨φ, hφI, hφ⟩ := hAI a a.2
    obtain ⟨t, rfl⟩ := hI hφI
    exact ⟨t, fun l => (hφ l).symm⟩
  have huniq : ∀ (a : MulAut L') (t t' : R), (∀ l, ψ (a l) = t * ψ l * t⁻¹) →
      (∀ l, ψ (a l) = t' * ψ l * t'⁻¹) → t = t' := by
    intro a t t' ht ht'
    have hc : t'⁻¹ * t ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hψ g
      have e := (ht l).symm.trans (ht' l)
      calc ψ l * (t'⁻¹ * t) = t'⁻¹ * (t' * ψ l * t'⁻¹) * t := by group
        _ = t'⁻¹ * (t * ψ l * t⁻¹) * t := by rw [e]
        _ = (t'⁻¹ * t) * ψ l := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.mp hc).symm
  choose χf hχf using hex
  have hχmul : ∀ a b : A, χf (a * b) = χf a * χf b := by
    intro a b
    refine huniq ((a * b : A) : MulAut L') _ _ (hχf (a * b)) fun l => ?_
    rw [Subgroup.coe_mul, MulAut.mul_apply, hχf a, hχf b]
    group
  have hχone : χf 1 = 1 := huniq 1 _ _ (hχf 1) fun l => by simp
  let χ : A →* R := { toFun := χf, map_one' := hχone, map_mul' := hχmul }
  have hχ : ∀ a : A, ∀ l, ψ ((a : MulAut L') l) = χ a * ψ l * (χ a)⁻¹ := hχf
  have hinner : ∀ (a : A) (t' : L'), ψ t' = χ a → ∀ l, (a : MulAut L') l = t' * l * t'⁻¹ :=
    fun a t' ht' => eq_conj_of_induces hker hperf (a : MulAut L') t' (fun l => by rw [hχ, ht'])
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 := hinner a 1 (by rw [map_one]; exact ha.symm)
    apply Subtype.ext
    ext l
    rw [h1 l]
    simp
  have hEA : IsElemAbelian p χ.range := isElemAbelian_range
    (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
    (fun a => Subtype.ext (by simpa using hA.2 a a.2)) χ
  have hcard : Nat.card χ.range = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv).symm
  obtain ⟨k, τ, WR, hτE, hsec, hWE, hirr⟩ := h χ.range hEA (hcard ▸ hr) (hcard ▸ h3)
  obtain ⟨σ, hσ⟩ := hsec L' ψ hψ hker
  have hψσ : ∀ f, ψ (σ f) = τ f := fun f => DFunLike.congr_fun hσ f
  have hfp : ∀ f : Fin k → Multiplicative (ZMod p), f ^ p = 1 := by
    intro f
    funext i
    rw [Pi.pow_apply, Pi.one_apply, ← ofAdd_toAdd (f i), ← ofAdd_nsmul, nsmul_eq_mul,
      ZMod.natCast_self, zero_mul, ofAdd_zero]
  have hσp : ∀ f, σ f ^ p = 1 := fun f => by rw [← map_pow, hfp, map_one]
  have hσc : ∀ f g, σ f * σ g = σ g * σ f := fun f g => by
    rw [← map_mul, ← map_mul, mul_comm]
  have hzc : ∀ z ∈ ψ.ker, ∀ x : L', z * x = x * z := fun z hz x =>
    (Subgroup.mem_center_iff.mp (hker hz) x).symm
  have hsec : ∀ (a : MulAut L') (ha : a ∈ A), ∃ f, τ f = χ ⟨a, ha⟩ ∧
      ∀ l, a l = σ f * l * (σ f)⁻¹ := by
    intro a ha
    have hmem : χ ⟨a, ha⟩ ∈ τ.range := hτE ▸ ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨f, hf⟩ := hmem
    exact ⟨f, hf, hinner ⟨a, ha⟩ (σ f) (by rw [hψσ, hf])⟩
  have hform : ∀ n : L', ψ n ∈ WR → ∀ (a : MulAut L') (ha : a ∈ A), ∃ g, ∃ z ∈ ψ.ker,
      z ^ p = 1 ∧ n * (a n)⁻¹ = σ g * z := by
    intro n hn a ha
    obtain ⟨f, hf, ha'⟩ := hsec a ha
    have hu : ψ (n * σ f * n⁻¹) ∈ τ.range := by
      rw [hτE, map_mul, map_mul, map_inv, hψσ, hf]
      exact hWE _ hn _ ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨g, hg⟩ := hu
    set z := (σ g)⁻¹ * (n * σ f * n⁻¹) with hz
    have hzk : z ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, hz, map_mul, map_inv, hψσ, hg, inv_mul_cancel]
    have h2 : n * σ f * n⁻¹ = σ g * z := by rw [hz, mul_inv_cancel_left]
    have hzp : z ^ p = 1 := by
      have h1 : (n * σ f * n⁻¹) ^ p = 1 := by rw [conj_pow, hσp, mul_one, mul_inv_cancel]
      rw [h2, Commute.mul_pow (hzc z hzk (σ g)).symm, hσp, one_mul] at h1
      exact h1
    refine ⟨g * f⁻¹, z, hzk, hzp, ?_⟩
    rw [ha' n]
    calc n * (σ f * n * (σ f)⁻¹)⁻¹ = (n * σ f * n⁻¹) * (σ f)⁻¹ := by group
      _ = σ g * z * (σ f)⁻¹ := by rw [h2]
      _ = σ g * (σ f)⁻¹ * z := by rw [mul_assoc, hzc z hzk (σ f)⁻¹, ← mul_assoc]
      _ = σ (g * f⁻¹) * z := by rw [map_mul, ← map_inv σ f]; rfl
  refine ⟨ψ ⁻¹' WR, fun n hn a ha => ?_, fun Y hWA hWY hYA hYp => ?_⟩
  · obtain ⟨g, z, hzk, hzp, he⟩ := hform n hn a ha
    refine ⟨?_, fun a' ha' => ?_⟩
    · rw [he, Commute.mul_pow (hzc z hzk (σ g)).symm, hσp, hzp, one_mul]
    · obtain ⟨f', -, ha''⟩ := hsec a' ha'
      rw [he, ha'']
      calc σ f' * (σ g * z) * (σ f')⁻¹ = σ f' * σ g * z * (σ f')⁻¹ := by group
        _ = σ g * σ f' * z * (σ f')⁻¹ := by rw [hσc]
        _ = σ g * (z * σ f') * (σ f')⁻¹ := by rw [hzc z hzk (σ f')]; group
        _ = σ g * z := by group
  ·
    set A' : Subgroup (MulAut L') := A ⊓ Subgroup.centralizer (Y : Set (MulAut L')) with hA'
    have hA'inv : ∀ n ∈ ψ ⁻¹' WR, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A' := by
      intro n hn a ha
      refine ⟨hWA n hn a ha.1, Subgroup.mem_centralizer_iff.mpr fun φ hφ => ?_⟩
      have hχ' := inv_conj_mem_of_conj_mem (hWY n hn) hφ
      have hc := Subgroup.mem_centralizer_iff.mp ha.2 _ hχ'
      set c := MulAut.conj n
      calc φ * (c * a * c⁻¹) = c * ((c⁻¹ * φ * c) * a) * c⁻¹ := by group
        _ = c * (a * (c⁻¹ * φ * c)) * c⁻¹ := by rw [hc]
        _ = c * a * c⁻¹ * φ := by group
    have hχconj : ∀ (n : L') (a : MulAut L') (ha : a ∈ A)
        (hna : MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A),
        χ ⟨_, hna⟩ = ψ n * χ ⟨a, ha⟩ * (ψ n)⁻¹ := by
      intro n a ha hna
      refine huniq _ _ _ (hχ ⟨_, hna⟩) fun l => ?_
      simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
      rw [map_mul, map_mul, map_inv, hχ ⟨a, ha⟩]
      simp only [map_mul, map_inv]
      group
    set E' : Subgroup R := (A'.subgroupOf A).map χ with hE'
    have hE'E : E' ≤ χ.range := Subgroup.map_le_range _ _
    have hE'inv : ∀ w ∈ WR, ∀ e ∈ E', w * e * w⁻¹ ∈ E' := by
      rintro w hw _ ⟨⟨a, ha⟩, haA', rfl⟩
      obtain ⟨n, rfl⟩ := hψ w
      have hna := hA'inv n hw a (Subgroup.mem_subgroupOf.mp haA')
      exact ⟨⟨_, hna.1⟩, Subgroup.mem_subgroupOf.mpr hna, hχconj n a ha hna.1⟩
    rcases hirr E' hE'E hE'inv with hbot | htop
    · exfalso
      have hA1 : Nat.card A ≠ 1 := by
        intro h1
        rw [h1] at h3
        have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
        omega
      obtain ⟨a, ha, ha1, hac⟩ :=
        exists_ne_one_forall_comm_of_pGroup (isPGroup_of_isElemAbelian hA) hA1 hYA hYp
      have haA' : a ∈ A' := ⟨ha, Subgroup.mem_centralizer_iff.mpr hac⟩
      have hmem : χ ⟨a, ha⟩ ∈ E' := ⟨⟨a, ha⟩, Subgroup.mem_subgroupOf.mpr haA', rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact ha1 (congrArg Subtype.val (hχinj (hmem.trans (map_one χ).symm)))
    · intro φ hφ a ha
      have hmem : χ ⟨a, ha⟩ ∈ E' := by
        rw [htop]
        exact ⟨⟨a, ha⟩, rfl⟩
      obtain ⟨a', ha', he⟩ := hmem
      have he' : a' = ⟨a, ha⟩ := hχinj he
      rw [he'] at ha'
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp ha').2 φ hφ

theorem ggTorusNbr_of_irredElt {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type} [Group R]
    {I : Set (MulAut R)} (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (h : GGTorusIrredElt p r R) : GGTorusNbr p r R I :=
  ggTorusNbr_of_secElt hp hI hZ (ggTorusSecElt_of_irredElt (hp.odd_of_ne_two hp2) h)

end CFSG.StandardType

end
