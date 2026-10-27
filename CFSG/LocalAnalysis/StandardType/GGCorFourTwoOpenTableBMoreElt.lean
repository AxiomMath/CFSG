module

public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerF4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB TableBSymp

namespace CorFourTwoMore

@[expose] def GGTorusIrredSecElt (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ E : Subgroup R, IsElemAbelian p E → p ^ r ≤ Nat.card E → p ^ 3 ≤ Nat.card E →
    ∃ (k : ℕ) (τ : (Fin k → Multiplicative (ZMod p)) →* R) (W : Set R), τ.range = E ∧
      (∀ (L' : Type) [Group L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' →
          ∃ σ : (Fin k → Multiplicative (ZMod p)) →* L', ψ.comp σ = τ) ∧
      (∀ w ∈ W, ∀ e ∈ E, w * e * w⁻¹ ∈ E) ∧
      (∀ E' : Subgroup R, E' ≤ E → (∀ w ∈ W, ∀ e ∈ E', w * e * w⁻¹ ∈ E') → E' = ⊥ ∨ E' = E) ∧
      (∃ w ∈ W, ∃ e ∈ E, w * e * w⁻¹ ≠ e) ∧
      ∀ F : R → R, (∀ e ∈ E, F e ∈ E) → (∀ e ∈ E, ∀ e' ∈ E, F (e * e') = F e * F e') →
        (∀ w ∈ W, ∀ e ∈ E, F (w * e * w⁻¹) = w * F e * w⁻¹) → ∃ c : ℕ, ∀ e ∈ E, F e = e ^ c

section Congr

variable {p r : ℕ} {R R' : Type} [Group R] [Group R']

theorem ggTorusIrredSecElt_of_mulEquiv (φ : R ≃* R') (h : GGTorusIrredSecElt p r R') :
    GGTorusIrredSecElt p r R := by
  intro E hE hr h3
  have hcard : Nat.card (E.map φ.toMonoidHom) = Nat.card E :=
    (Nat.card_congr (E.equivMapOfInjective _ φ.injective).toEquiv).symm
  obtain ⟨k, τ, W, hτE, hsec, hWE, hirr, ⟨w₀, hw₀, e₀, he₀, hwe₀⟩, hschur⟩ :=
    h (E.map φ.toMonoidHom) (isElemAbelian_map hE _) (hcard ▸ hr) (hcard ▸ h3)
  have hmem : ∀ x : R, φ x ∈ E.map φ.toMonoidHom ↔ x ∈ E := fun x =>
    ⟨fun ⟨y, hy, hyx⟩ => φ.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  have hmem' : ∀ x : R', x ∈ E.map φ.toMonoidHom ↔ φ.symm x ∈ E := fun x => by
    rw [← hmem, MulEquiv.apply_symm_apply]
  refine ⟨k, φ.symm.toMonoidHom.comp τ, φ.symm '' W, ?_, fun L' _ ψ hψ hker => ?_, ?_,
    fun E' hE' hinv' => ?_, ?_, fun F hFE hFmul hFW => ?_⟩
  · ext x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨f, rfl⟩
      have : τ f ∈ τ.range := ⟨f, rfl⟩
      rw [hτE] at this
      rw [← hmem]
      simpa using this
    · intro hx
      have : φ x ∈ τ.range := hτE ▸ (hmem x).mpr hx
      obtain ⟨f, hf⟩ := this
      exact ⟨f, by simp [hf]⟩
  · obtain ⟨σ, hσ⟩ := hsec L' (φ.toMonoidHom.comp ψ) (φ.surjective.comp hψ) (fun l hl =>
      hker (by simpa [MonoidHom.mem_ker] using hl))
    refine ⟨σ, MonoidHom.ext fun f => ?_⟩
    have h1 := DFunLike.congr_fun hσ f
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h1 ⊢
    rw [← h1, MulEquiv.symm_apply_apply]
  · rintro _ ⟨w, hw, rfl⟩ x hx
    rw [← hmem]
    simpa using hWE w hw (φ x) ((hmem x).mpr hx)
  · have hle : E'.map φ.toMonoidHom ≤ E.map φ.toMonoidHom := Subgroup.map_mono hE'
    have hinv'' : ∀ w ∈ W, ∀ x ∈ E'.map φ.toMonoidHom, w * x * w⁻¹ ∈ E'.map φ.toMonoidHom := by
      rintro w hw _ ⟨y, hy, rfl⟩
      refine ⟨_, hinv' (φ.symm w) ⟨w, hw, rfl⟩ y hy, ?_⟩
      simp
    rcases hirr _ hle hinv'' with h1 | h1
    · left
      rw [eq_bot_iff]
      intro x hx
      have : φ x ∈ E'.map φ.toMonoidHom := ⟨x, hx, rfl⟩
      rw [h1, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at this
      exact this ▸ Subgroup.one_mem _
    · right
      refine le_antisymm hE' fun x hx => ?_
      have : φ x ∈ E'.map φ.toMonoidHom := h1 ▸ (hmem x).mpr hx
      obtain ⟨y, hy, hyx⟩ := this
      exact φ.injective hyx ▸ hy
  · refine ⟨φ.symm w₀, ⟨w₀, hw₀, rfl⟩, φ.symm e₀, (hmem' e₀).mp he₀, fun heq => hwe₀ ?_⟩
    have h1 := congrArg φ heq
    simpa using h1
  · obtain ⟨c, hc⟩ := hschur (fun y => φ (F (φ.symm y)))
      (fun y hy => (hmem _).mpr (by simpa using hFE _ ((hmem' y).mp hy)))
      (fun y hy y' hy' => by
        rw [map_mul, hFmul _ ((hmem' y).mp hy) _ ((hmem' y').mp hy'), map_mul])
      (fun w hw y hy => by
        have h1 := hFW (φ.symm w) ⟨w, hw, rfl⟩ (φ.symm y) ((hmem' y).mp hy)
        simp only [map_mul, map_inv] at h1 ⊢
        rw [h1]
        simp)
    refine ⟨c, fun x hx => ?_⟩
    have h1 := hc (φ x) ((hmem x).mpr hx)
    simp only [MulEquiv.symm_apply_apply] at h1
    apply φ.injective
    rw [h1, map_pow]

end Congr

section Transfer

variable {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}

theorem ggTorusIrred_of_irredSecElt (hp : p.Prime)
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (h : GGTorusIrredSecElt p r R) : GGTorusIrred p r R I := by
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
  obtain ⟨k, τ, WR, hτE, hsec, hWE, hirr, ⟨w₀, hw₀, e₀, he₀, hwe₀⟩, hschur⟩ :=
    h χ.range hEA (hcard ▸ hr) (hcard ▸ h3)
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
  have hsecA : ∀ (a : MulAut L') (ha : a ∈ A), ∃ f, τ f = χ ⟨a, ha⟩ ∧
      ∀ l, a l = σ f * l * (σ f)⁻¹ := by
    intro a ha
    have hmem : χ ⟨a, ha⟩ ∈ τ.range := hτE ▸ ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨f, hf⟩ := hmem
    exact ⟨f, hf, hinner ⟨a, ha⟩ (σ f) (by rw [hψσ, hf])⟩
  have hform : ∀ n : L', ψ n ∈ WR → ∀ (a : MulAut L') (ha : a ∈ A), ∃ g, ∃ z ∈ ψ.ker,
      z ^ p = 1 ∧ n * (a n)⁻¹ = σ g * z := by
    intro n hn a ha
    obtain ⟨f, hf, ha'⟩ := hsecA a ha
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
  have hconjA : ∀ n : L', ψ n ∈ WR → ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A := by
    intro n hn a ha
    obtain ⟨t, ht⟩ := hψ (χ ⟨a, ha⟩)
    have hat := hinner ⟨a, ha⟩ t ht
    obtain ⟨a', ha'⟩ : ψ n * χ ⟨a, ha⟩ * (ψ n)⁻¹ ∈ χ.range := hWE _ hn _ ⟨⟨a, ha⟩, rfl⟩
    have ha't := hinner a' (n * t * n⁻¹) (by rw [map_mul, map_mul, map_inv, ht, ha'])
    have he : MulAut.conj n * a * (MulAut.conj n)⁻¹ = (a' : MulAut L') := by
      ext l
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, hat,
        ha't]
      group
    rw [he]
    exact a'.2
  have hχconj : ∀ (n : L') (a : MulAut L') (ha : a ∈ A)
      (hna : MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A),
      χ ⟨_, hna⟩ = ψ n * χ ⟨a, ha⟩ * (ψ n)⁻¹ := by
    intro n a ha hna
    refine huniq _ _ _ (hχ ⟨_, hna⟩) fun l => ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
    rw [map_mul, map_mul, map_inv, hχ ⟨a, ha⟩]
    simp only [map_mul, map_inv]
    group
  refine ⟨ψ ⁻¹' WR, fun n hn a ha => ?_, fun A' hA'A hinv => ?_, ?_,
    fun f hfA hfmul hfW => ?_⟩
  ·
    obtain ⟨g, z, hzk, hzp, he⟩ := hform n hn a ha
    refine ⟨?_, fun a' ha' => ?_⟩
    · rw [he, Commute.mul_pow (hzc z hzk (σ g)).symm, hσp, hzp, one_mul]
    · obtain ⟨f', -, ha''⟩ := hsecA a' ha'
      rw [he, ha'']
      calc σ f' * (σ g * z) * (σ f')⁻¹ = σ f' * σ g * z * (σ f')⁻¹ := by group
        _ = σ g * σ f' * z * (σ f')⁻¹ := by rw [hσc]
        _ = σ g * (z * σ f') * (σ f')⁻¹ := by rw [hzc z hzk (σ f')]; group
        _ = σ g * z := by group
  ·
    set E' : Subgroup R := (A'.subgroupOf A).map χ with hE'
    have hE'E : E' ≤ χ.range := Subgroup.map_le_range _ _
    have hE'inv : ∀ w ∈ WR, ∀ e ∈ E', w * e * w⁻¹ ∈ E' := by
      rintro w hw _ ⟨⟨a, ha⟩, haA', rfl⟩
      obtain ⟨n, rfl⟩ := hψ w
      have hna := hinv n hw a (Subgroup.mem_subgroupOf.mp haA')
      exact ⟨⟨_, hA'A hna⟩, Subgroup.mem_subgroupOf.mpr hna, hχconj n a ha (hA'A hna)⟩
    rcases hirr E' hE'E hE'inv with hbot | htop
    · left
      rw [eq_bot_iff]
      intro a haA'
      have hmem : χ ⟨a, hA'A haA'⟩ ∈ E' :=
        ⟨⟨a, hA'A haA'⟩, Subgroup.mem_subgroupOf.mpr haA', rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      have h1 : (⟨a, hA'A haA'⟩ : A) = 1 := hχinj (hmem.trans (map_one χ).symm)
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val h1
    · right
      refine le_antisymm hA'A fun a ha => ?_
      have hmem : χ ⟨a, ha⟩ ∈ E' := by
        rw [htop]
        exact ⟨⟨a, ha⟩, rfl⟩
      obtain ⟨a', ha', he⟩ := hmem
      have he' : a' = ⟨a, ha⟩ := hχinj he
      rw [he'] at ha'
      exact Subgroup.mem_subgroupOf.mp ha'
  ·
    obtain ⟨n, rfl⟩ := hψ w₀
    obtain ⟨⟨a₀, ha₀⟩, rfl⟩ := he₀
    refine ⟨n, hw₀, a₀, ha₀, fun heq => hwe₀ ?_⟩
    rw [← hχconj n a₀ ha₀ (hconjA n hw₀ a₀ ha₀)]
    congr 1
    exact Subtype.ext heq
  ·
    let e' : A ≃* χ.range := MonoidHom.ofInjective hχinj
    let F : R → R := fun y => if hy : y ∈ χ.range then
      χ ⟨f ((e'.symm ⟨y, hy⟩ : A) : MulAut L'), hfA _ (e'.symm ⟨y, hy⟩).2⟩ else y
    have hF : ∀ (a : MulAut L') (ha : a ∈ A), F (χ ⟨a, ha⟩) = χ ⟨f a, hfA a ha⟩ := by
      intro a ha
      have hy : χ ⟨a, ha⟩ ∈ χ.range := ⟨⟨a, ha⟩, rfl⟩
      have hs : e'.symm ⟨χ ⟨a, ha⟩, hy⟩ = ⟨a, ha⟩ := by
        rw [show (⟨χ ⟨a, ha⟩, hy⟩ : χ.range) = e' ⟨a, ha⟩ from
          Subtype.ext (MonoidHom.ofInjective_apply hχinj (x := ⟨a, ha⟩)).symm,
          MulEquiv.symm_apply_apply]
      show (if hy : χ ⟨a, ha⟩ ∈ χ.range then _ else _) = _
      rw [dite_eq_left hy]
      congr 1
      apply Subtype.ext
      show f ((e'.symm ⟨χ ⟨a, ha⟩, hy⟩ : A) : MulAut L') = f a
      rw [hs]
    obtain ⟨c, hc⟩ := hschur F
      (by
        rintro _ ⟨⟨a, ha⟩, rfl⟩
        rw [hF a ha]
        exact ⟨_, rfl⟩)
      (by
        rintro _ ⟨⟨a, ha⟩, rfl⟩ _ ⟨⟨b, hb⟩, rfl⟩
        have e1 : χ ⟨a, ha⟩ * χ ⟨b, hb⟩ = χ ⟨a * b, A.mul_mem ha hb⟩ := by
          rw [← map_mul]
          rfl
        rw [e1, hF _ (A.mul_mem ha hb), hF a ha, hF b hb, ← map_mul]
        congr 1
        exact Subtype.ext (hfmul a ha b hb))
      (by
        rintro w hw _ ⟨⟨a, ha⟩, rfl⟩
        obtain ⟨n, rfl⟩ := hψ w
        have hna := hconjA n hw a ha
        have hnfa := hconjA n hw (f a) (hfA a ha)
        rw [← hχconj n a ha hna, hF _ hna, hF a ha, ← hχconj n (f a) (hfA a ha) hnfa]
        congr 1
        exact Subtype.ext (hfW n hw a ha))
    refine ⟨c, fun a ha => ?_⟩
    have h1 := hc (χ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩
    rw [hF a ha, ← map_pow] at h1
    have h2 := congrArg Subtype.val (hχinj h1)
    simpa using h2

theorem ggTorusIrred_of_pow (h : GGTorusIrred p r R {φ | φ ∈ I ∧ φ ^ p = 1}) :
    GGTorusIrred p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3
  refine h L' ψ hψ hker hperf A hA (fun a ha => ?_) hr h3
  obtain ⟨φ, hφ, hφa⟩ := hAI a ha
  refine ⟨φ, ⟨hφ, ?_⟩, hφa⟩
  have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
    intro k
    induction k with
    | zero => intro l; rfl
    | succ k ih =>
      intro l
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφa, ih]
  ext x
  obtain ⟨l, rfl⟩ := hψ x
  rw [hk p l, hA.2 a ha]
  rfl

end Transfer

section Refl

variable {p r : ℕ}

theorem ggTorusReflElt_of_mulEquiv {R R' : Type} [Group R] [Group R'] (φ : R ≃* R')
    (h : GGTorusReflElt p r R') : GGTorusReflElt p r R := by
  intro E hE hr h3
  have hcard : Nat.card (E.map φ.toMonoidHom) = Nat.card E :=
    (Nat.card_congr (E.equivMapOfInjective _ φ.injective).toEquiv).symm
  obtain ⟨d, e, c, n, heE, hc, hn, hirr⟩ :=
    h (E.map φ.toMonoidHom) (isElemAbelian_map hE _) (hcard ▸ hr) (hcard ▸ h3)
  have hmem : ∀ x : R, φ x ∈ E.map φ.toMonoidHom ↔ x ∈ E := fun x =>
    ⟨fun ⟨y, hy, hyx⟩ => φ.injective hyx ▸ hy, fun hx => ⟨x, hx, rfl⟩⟩
  refine ⟨d, φ.symm.toMonoidHom.comp e, c, fun i => φ.symm (n i), ?_, hc, fun i v => ?_,
    fun E' hE' hinv => ?_⟩
  · ext x
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨f, rfl⟩
      have : e f ∈ e.range := ⟨f, rfl⟩
      rw [heE] at this
      rw [← hmem]
      simpa using this
    · intro hx
      have : φ x ∈ e.range := heE ▸ (hmem x).mpr hx
      obtain ⟨f, hf⟩ := this
      exact ⟨f, by simp [hf]⟩
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    rw [← map_inv, ← map_mul, ← map_mul, hn]
  · have hle : E'.map φ.toMonoidHom ≤ E.map φ.toMonoidHom := Subgroup.map_mono hE'
    have hinv'' : ∀ i, ∀ x ∈ E'.map φ.toMonoidHom, n i * x * (n i)⁻¹ ∈
        E'.map φ.toMonoidHom := by
      rintro i _ ⟨y, hy, rfl⟩
      refine ⟨_, hinv i y hy, ?_⟩
      simp
    rcases hirr _ hle hinv'' with h1 | h1
    · left
      rw [eq_bot_iff]
      intro x hx
      have : φ x ∈ E'.map φ.toMonoidHom := ⟨x, hx, rfl⟩
      rw [h1, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at this
      exact this ▸ Subgroup.one_mem _
    · right
      refine le_antisymm hE' fun x hx => ?_
      have : φ x ∈ E'.map φ.toMonoidHom := h1 ▸ (hmem x).mpr hx
      obtain ⟨y, hy, hyx⟩ := this
      exact φ.injective hyx ▸ hy

theorem ggTorusIrredSecElt_of_reflElt (hp : p.Prime) (hp2 : p ≠ 2) {R : Type} [Group R]
    (h : GGTorusReflElt p r R) : GGTorusIrredSecElt p r R := by
  classical
  intro E hE hr h3
  obtain ⟨d, e, c, n, heE, hc, hn, hirr⟩ := h E hE hr h3
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have : NeZero p := ⟨hp.ne_zero⟩
  set τ := TableBF4.piTorus e with hτdef
  have hτE : τ.range = E := by rw [hτdef, TableBF4.range_piTorus, heE]
  set u : Fin d → R := fun i => e (.ofAdd (Pi.single i 1)) with hu
  have hEmem : ∀ x ∈ E, ∃ v, e (.ofAdd v) = x := fun x hx => by
    rw [← heE] at hx
    obtain ⟨y, rfl⟩ := hx
    exact ⟨Multiplicative.toAdd y, by rw [ofAdd_toAdd]⟩
  have heE' : ∀ v, e (.ofAdd v) ∈ E := fun v => heE ▸ ⟨_, rfl⟩
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    TableB.IsElemAbelian.comm hE hx hy
  have huE : ∀ i, u i ∈ E := fun i => heE' _
  have hact : ∀ i v, n i * e (.ofAdd v) * (n i)⁻¹ = e (.ofAdd v) * (u i ^ (c i v).val)⁻¹ := by
    intro i v
    rw [hn, sub_eq_add_neg, ofAdd_add, map_mul]
    congr 1
    rw [hu, ← map_pow, ← map_inv, ← ofAdd_nsmul, ← ofAdd_neg]
    congr 2
    rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
  have hnE : ∀ i, ∀ x ∈ E, n i * x * (n i)⁻¹ ∈ E := by
    intro i x hx
    obtain ⟨v, rfl⟩ := hEmem x hx
    rw [hn]
    exact heE' _
  have hinvu : ∀ i, n i * u i * (n i)⁻¹ = (u i)⁻¹ := by
    intro i
    rw [hu, hn, hc, ← map_inv, ← ofAdd_neg]
    congr 2
    rw [two_smul]
    abel
  have heig : ∀ i, ∀ x ∈ E, n i * x * (n i)⁻¹ = x⁻¹ → ∃ m : ℕ, x = u i ^ m := by
    intro i x hx hinv
    obtain ⟨v, rfl⟩ := hEmem x hx
    rw [hact] at hinv
    set y := e (.ofAdd v) with hy
    set m := (c i v).val with hm
    have h2 : y * y = u i ^ m := by
      have e1 : y * (y * (u i ^ m)⁻¹) * u i ^ m = y * y := by
        rw [← mul_assoc, inv_mul_cancel_right]
      rw [← e1, hinv, mul_inv_cancel, one_mul]
    have hyp : y ^ p = 1 := hE.2 y hx
    have hp1 : 2 * ((p + 1) / 2) = p + 1 :=
      Nat.two_mul_div_two_of_even (by rcases hodd with ⟨k, hk⟩; exact ⟨k + 1, by omega⟩)
    refine ⟨m * ((p + 1) / 2), ?_⟩
    calc y = y ^ (p + 1) := by rw [pow_succ, hyp, one_mul]
      _ = y ^ (2 * ((p + 1) / 2)) := by rw [hp1]
      _ = (y * y) ^ ((p + 1) / 2) := by rw [pow_mul, sq]
      _ = u i ^ (m * ((p + 1) / 2)) := by rw [h2, pow_mul]
  obtain ⟨i₀, hu1⟩ : ∃ i, u i ≠ 1 := by
    by_contra hall
    push Not at hall
    have hcen : ∀ i, ∀ x ∈ E, n i * x * (n i)⁻¹ = x := by
      intro i x hx
      obtain ⟨v, rfl⟩ := hEmem x hx
      rw [hact, hall i, one_pow, inv_one, mul_one]
    have hE1 : E ≠ ⊥ := by
      intro hb
      rw [hb, Subgroup.card_bot] at h3
      exact absurd h3 (not_le.mpr (Nat.one_lt_pow (by norm_num) hp.one_lt))
    obtain ⟨⟨x, hx⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hE1
    have hx1' : x ≠ 1 := fun h => hx1 (Subtype.ext h)
    rcases hirr (Subgroup.zpowers x) (Subgroup.zpowers_le.mpr hx) (fun i y hy => by
        rw [hcen i y (Subgroup.zpowers_le.mpr hx hy)]
        exact hy) with hb | htop
    · exact hx1' (Subgroup.zpowers_eq_bot.mp hb)
    · have hc1 : Nat.card E ≤ p := by
        rw [← htop, Nat.card_zpowers]
        exact orderOf_le_of_pow_eq_one hp.pos (hE.2 x hx)
      have : p < p ^ 3 := by
        calc p = p ^ 1 := (pow_one p).symm
          _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
      omega
  refine ⟨d, τ, Set.range n, hτE, fun L' _ ψ hψ hker => ?_, ?_,
    fun E' hE' hinv => hirr E' hE' fun i x hx => hinv (n i) ⟨i, rfl⟩ x hx, ?_,
    fun F hFE hFmul hFW => ?_⟩
  · have hcomm' : ∀ x ∈ τ.range.comap ψ, ∀ y ∈ τ.range.comap ψ, x * y = y * x := by
      rw [hτdef, TableBF4.range_piTorus]
      exact CFSG.RankThree.CentralCover.reflection_comap_comm hψ hker hp hp2 e c hc n hn
    have hinvb : ∀ i : Fin d, ∃ w : R,
        w * TableBSymp.torusBasis τ i * w⁻¹ = (TableBSymp.torusBasis τ i)⁻¹ := by
      intro i
      refine ⟨n i, ?_⟩
      rw [hτdef, TableBF4.torusBasis_piTorus, hn, hc, ← map_inv, ← ofAdd_neg]
      congr 2
      rw [two_smul]
      abel
    exact TableBF4.exists_torus_section_of_comm hψ hker hodd τ hcomm' hinvb
  · rintro _ ⟨i, rfl⟩ x hx
    exact hnE i x hx
  · refine ⟨n i₀, ⟨i₀, rfl⟩, u i₀, huE i₀, fun heq => hu1 ?_⟩
    rw [hinvu] at heq
    have h2 : u i₀ ^ 2 = 1 := by
      rw [sq]
      calc u i₀ * u i₀ = (u i₀)⁻¹ * u i₀ := by rw [heq]
        _ = 1 := inv_mul_cancel _
    have hpu : u i₀ ^ p = 1 := hE.2 _ (huE i₀)
    have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop
      (orderOf_dvd_of_pow_eq_one h2) (orderOf_dvd_of_pow_eq_one hpu))
  · have hF1 : F 1 = 1 := by
      have h1 := hFmul 1 E.one_mem 1 E.one_mem
      rw [mul_one] at h1
      exact mul_eq_left.mp h1.symm
    have hFinv : ∀ x ∈ E, F x⁻¹ = (F x)⁻¹ := by
      intro x hx
      have h1 := hFmul x hx x⁻¹ (E.inv_mem hx)
      rw [mul_inv_cancel, hF1] at h1
      exact eq_inv_of_mul_eq_one_right h1.symm
    obtain ⟨cc, hcc⟩ : ∃ cc : ℕ, F (u i₀) = u i₀ ^ cc := by
      refine heig i₀ (F (u i₀)) (hFE _ (huE i₀)) ?_
      rw [← hFW (n i₀) ⟨i₀, rfl⟩ (u i₀) (huE i₀), hinvu, hFinv _ (huE i₀)]
    refine ⟨cc, ?_⟩
    let E₁ : Subgroup R :=
      { carrier := {x | x ∈ E ∧ F x = x ^ cc}
        mul_mem' := fun {x y} hx hy => ⟨E.mul_mem hx.1 hy.1, by
          rw [hFmul x hx.1 y hy.1, hx.2, hy.2,
            (Commute.mul_pow (hcomm x hx.1 y hy.1 : Commute x y) cc)]⟩
        one_mem' := ⟨E.one_mem, by rw [hF1, one_pow]⟩
        inv_mem' := fun {x} hx => ⟨E.inv_mem hx.1, by rw [hFinv x hx.1, hx.2, inv_pow]⟩ }
    rcases hirr E₁ (fun x hx => hx.1) (fun i x hx => ⟨hnE i x hx.1, by
        rw [hFW (n i) ⟨i, rfl⟩ x hx.1, hx.2, conj_pow]⟩) with hb | htop
    · exfalso
      have : u i₀ ∈ E₁ := ⟨huE i₀, hcc⟩
      rw [hb, Subgroup.mem_bot] at this
      exact hu1 this
    · intro x hx
      have : x ∈ E₁ := htop ▸ hx
      exact this.2

end Refl

end CorFourTwoMore

end CFSG.StandardType

end
