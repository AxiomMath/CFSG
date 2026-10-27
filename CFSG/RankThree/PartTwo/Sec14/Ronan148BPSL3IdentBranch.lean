module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148BPSL3Ident
public import CFSG.RankThree.PartTwo.KFacts.KS12ClassOut
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofA6

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148B

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec13

theorem center_eq_bot_of_mulEquiv' {Y Z : Type} [Group Y] [Group Z] (φ : Y ≃* Z)
    (h : Subgroup.center Z = ⊥) : Subgroup.center Y = ⊥ := by
  rw [eq_bot_iff]
  intro y hy
  have hφ : φ y ∈ Subgroup.center Z := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 := congrArg φ (Subgroup.mem_center_iff.mp hy (φ.symm z))
    simpa using h1
  rw [h, Subgroup.mem_bot] at hφ
  rw [Subgroup.mem_bot]
  exact φ.injective (hφ.trans (map_one φ).symm)

theorem inn3_of_mulEquiv {Y Z : Type} [Group Y] [Group Z] (φ : Y ≃* Z)
    (h : ∀ β : MulAut Z, β ^ 3 = 1 → β ∈ (MulAut.conj : Z →* MulAut Z).range) :
    ∀ α : MulAut Y, α ^ 3 = 1 → α ∈ (MulAut.conj : Y →* MulAut Y).range := by
  intro α hα
  have hβ : (MulAut.congr φ α) ^ 3 = 1 := by rw [← map_pow, hα, map_one]
  obtain ⟨a, ha⟩ := h _ hβ
  refine ⟨φ.symm a, MulEquiv.ext fun y => ?_⟩
  have h1 := congrArg (fun β : MulAut Z => β (φ y)) ha
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h1
  rw [MulAut.conj_apply]
  apply φ.injective
  rw [← h1, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

section Inner

variable {X : Type} [Group X] [Finite X]

def resHom {P : Subgroup (MulAut X)} {K₀ : Subgroup X} (hPK : ∀ σ ∈ P, ∀ k ∈ K₀, σ k ∈ K₀) :
    ↥P →* MulAut ↥K₀ where
  toFun σ :=
    { toFun := fun z => ⟨(σ : MulAut X) z, hPK σ σ.2 z z.2⟩
      invFun := fun z => ⟨(σ : MulAut X)⁻¹ z, hPK _ (P.inv_mem σ.2) z z.2⟩
      left_inv := fun z => Subtype.ext (MulAut.inv_apply_self _ _ (z : X))
      right_inv := fun z => Subtype.ext (MulAut.apply_inv_self _ _ (z : X))
      map_mul' := fun x y => Subtype.ext (map_mul (σ : MulAut X) (x : X) (y : X)) }
  map_one' := MulEquiv.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := MulEquiv.ext fun _ => Subtype.ext rfl

theorem exists_inner_of_inn3 {P : Subgroup (MulAut X)} (hP3 : ∀ σ ∈ P, σ ^ 3 = 1)
    {K₀ : Subgroup X} (hPK : ∀ σ ∈ P, ∀ k ∈ K₀, σ k ∈ K₀)
    (hfaith : ∀ σ ∈ P, (∀ k ∈ K₀, σ k = k) → σ = 1) (hZ₀ : Subgroup.center ↥K₀ = ⊥)
    (hinn : ∀ α : MulAut ↥K₀, α ^ 3 = 1 → α ∈ (MulAut.conj : ↥K₀ →* MulAut ↥K₀).range) :
    ∃ E : Subgroup X, E ≤ K₀ ∧ Nat.card E = Nat.card P ∧
      ∀ σ ∈ P, ∃ e ∈ E, ∀ k ∈ K₀, σ k = e * k * e⁻¹ := by
  set ρ := resHom hPK with hρ
  have hρinj : Function.Injective ρ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro σ hσ
    have h1 : ρ σ = 1 := hσ
    have h2 : (σ : MulAut X) = 1 := hfaith σ σ.2 fun k hk =>
      congrArg (fun α : MulAut ↥K₀ => ((α ⟨k, hk⟩ : ↥K₀) : X)) h1
    exact (Subgroup.mem_bot).mpr (Subtype.ext h2)
  have hrange : ρ.range ≤ (MulAut.conj : ↥K₀ →* MulAut ↥K₀).range := by
    rintro _ ⟨σ, rfl⟩
    apply hinn
    have hσ3 : σ ^ 3 = 1 := Subtype.ext (by simpa using hP3 σ σ.2)
    rw [← map_pow, hσ3, map_one]
  have hinj₀ := PS.conj_injective hZ₀
  set E₀ : Subgroup ↥K₀ := ρ.range.comap MulAut.conj with hE₀
  refine ⟨E₀.map K₀.subtype, Subgroup.map_subtype_le E₀, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective K₀.subtype_injective,
      card_comap_of_le_range MulAut.conj hinj₀ hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv).symm
  · intro σ hσ
    obtain ⟨e', he'⟩ := hrange ⟨⟨σ, hσ⟩, rfl⟩
    refine ⟨e', ⟨e', ?_, rfl⟩, fun k hk => ?_⟩
    · change MulAut.conj e' ∈ ρ.range
      rw [he']
      exact ⟨_, rfl⟩
    · have h1 := congrArg (fun α : MulAut ↥K₀ => ((α ⟨k, hk⟩ : ↥K₀) : X)) he'
      exact h1.symm

theorem l3Ident148_of_alt7 (hZ : Subgroup.center X = ⊥) {P : Subgroup (MulAut X)}
    (hPe : CFSG.Assembly.IsElemAbelian 3 P) (hP9 : Nat.card P = 9) {K₀ : Subgroup X}
    {Q D : Subgroup (MulAut X)}
    (hh : SigGenHyp P (K₀.map (MulAut.conj : X →* MulAut X)) Q D)
    (φ : ↥K₀ ≃* alternatingGroup (Fin 7)) : L3Ident148 P K₀ := by
  have hI := InspIn148.of_mulEquiv φ A7.inspIn148_alt7
  obtain ⟨E, hEK, hE9, hPE⟩ := exists_inner_of_inn3 (fun σ hσ => hPe.2 σ hσ) (inv_of_hyp hZ hh)
    (fun σ hσ h => eq_one_of_trivial hh hσ h) hI.1 hI.2.1
  exact Or.inr (Or.inr (Or.inl ⟨⟨φ⟩, E, hEK, hE9.trans hP9, hPE⟩))

theorem isPGroup_inf_centralizer_of_alt6 {K₀ : Subgroup X} (φ : ↥K₀ ≃* alternatingGroup (Fin 6))
    {E : Subgroup X} (hEK : E ≤ K₀) (hE9 : Nat.card E = 9) {e : X} (he : e ∈ E) (he1 : e ≠ 1) :
    IsPGroup 3 ↥(K₀ ⊓ Subgroup.centralizer ({e} : Set X)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set E' := (E.subgroupOf K₀).map φ.toMonoidHom with hE'
  have hE'9 : Nat.card E' = 9 := by
    rw [hE', Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv, hE9]
  obtain ⟨g, hg⟩ := Sec4.Res423Two.exists_map_conj_eq_of_card_nine
    Sec4.Res423Two.factorization_card_alt6 hE'9 Sec4.Item434AltPerm.card_F06
  set ek : ↥K₀ := ⟨e, hEK he⟩ with hek
  set f := g * φ ek * g⁻¹ with hf
  have hfF : f ∈ Sec4.Item434AltPerm.F06 := by
    rw [← hg]
    exact ⟨φ ek, ⟨ek, Subgroup.mem_subgroupOf.mpr he, rfl⟩, rfl⟩
  have hf1 : f ≠ 1 := by
    intro h
    apply he1
    have h2 : φ ek = 1 := by
      calc φ ek = g⁻¹ * f * g := by rw [hf]; group
        _ = 1 := by rw [h]; group
    have h3 : ek = 1 := φ.injective (h2.trans (map_one φ).symm)
    exact congrArg Subtype.val h3
  have hC := Sec4.Item434AltPerm.centralizer_le_F06 hfF hf1
  have hF3 : IsPGroup 3 Sec4.Item434AltPerm.F06 :=
    IsPGroup.of_card (n := 2) (by rw [Sec4.Item434AltPerm.card_F06]; norm_num)
  set ψ₁ : ↥(K₀ ⊓ Subgroup.centralizer ({e} : Set X)) →* alternatingGroup (Fin 6) :=
    (MulAut.conj g).toMonoidHom.comp (φ.toMonoidHom.comp (Subgroup.inclusion inf_le_left))
    with hψ₁
  have hψ₁inj : Function.Injective ψ₁ :=
    (MulAut.conj g).injective.comp (φ.injective.comp (Subgroup.inclusion_injective _))
  have hmem : ∀ x, ψ₁ x ∈ Sec4.Item434AltPerm.F06 := by
    intro x
    apply hC
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hxe : (x : X) * e = e * x := Subgroup.mem_centralizer_singleton_iff.mp x.2.2
    have hk : Subgroup.inclusion inf_le_left x * ek = ek * Subgroup.inclusion inf_le_left x :=
      Subtype.ext hxe
    have hφk := congrArg φ hk
    rw [map_mul, map_mul] at hφk
    change g * φ (Subgroup.inclusion inf_le_left x) * g⁻¹ * f =
      f * (g * φ (Subgroup.inclusion inf_le_left x) * g⁻¹)
    rw [hf]
    calc g * φ (Subgroup.inclusion inf_le_left x) * g⁻¹ * (g * φ ek * g⁻¹)
        = g * (φ (Subgroup.inclusion inf_le_left x) * φ ek) * g⁻¹ := by group
      _ = g * (φ ek * φ (Subgroup.inclusion inf_le_left x)) * g⁻¹ := by rw [hφk]
      _ = g * φ ek * g⁻¹ * (g * φ (Subgroup.inclusion inf_le_left x) * g⁻¹) := by group
  exact hF3.of_injective (ψ₁.codRestrict _ hmem) fun a b hab =>
    hψ₁inj (congrArg Subtype.val hab)

theorem l3Ident148_of_alt6 (hZ : Subgroup.center X = ⊥) {P : Subgroup (MulAut X)}
    (hPe : CFSG.Assembly.IsElemAbelian 3 P) (hP9 : Nat.card P = 9) {K₀ : Subgroup X}
    {Q D : Subgroup (MulAut X)}
    (hh : SigGenHyp P (K₀.map (MulAut.conj : X →* MulAut X)) Q D)
    (φ : ↥K₀ ≃* alternatingGroup (Fin 6)) : L3Ident148 P K₀ := by
  have hZ₀ : Subgroup.center ↥K₀ = ⊥ :=
    center_eq_bot_of_mulEquiv' φ (alternatingGroup.center_eq_bot (by simp))
  have hinn := inn3_of_mulEquiv φ fun β hβ =>
    KFacts.mem_range_conj_alternatingGroup_six ⟨1, by rw [pow_one]; exact hβ⟩
  obtain ⟨E, hEK, hE9, hPE⟩ := exists_inner_of_inn3 (fun σ hσ => hPe.2 σ hσ) (inv_of_hyp hZ hh)
    (fun σ hσ h => eq_one_of_trivial hh hσ h) hZ₀ hinn
  exact Or.inr (Or.inr (Or.inr ⟨hZ₀, E, hEK, fun e he he1 =>
    isPGroup_inf_centralizer_of_alt6 φ hEK (hE9.trans hP9) he he1, hPE⟩))

end Inner

end CFSG.RankThree.PartTwo.Sec14.Ronan148B
