module

public import CFSG.Quasithin.Vol2.Ch11SecBK2G
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin

namespace BK2

variable {D : FFModel} {K M : Type} [Field K] [Finite K] [AddCommGroup M] [Module K M]
  {W : Type} [CommGroup W] {LM : KGNat.LinModel D K M} {H : Subgroup (MulAut W)}
  {Z : Subgroup W} {π : D.Gam →* ↥H} {f : W → M}

omit [Finite K] in
theorem exists_isSemiF (hf : KGNat.IsCoord LM H Z π f)
    (hcomm : ∀ T : M →+ M, (∀ (γ : D.Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ c : K, ∀ x, T x = c • x)
    {x₀ : M} (hx₀ : x₀ ≠ 0) {a : MulAut W} (haZ : ∀ z ∈ Z, a z ∈ Z)
    (haZ' : ∀ z ∈ Z, a⁻¹ z ∈ Z) (haH' : ∀ h ∈ H, a⁻¹ * h * a ∈ H) :
    ∃ σ : K →+* K, IsSemiF f σ a := by
  obtain ⟨σ, hσ⟩ := hf.exists_semilinear hcomm hx₀ a haZ haZ' haH'
  refine ⟨σ, fun c w w' h => ?_⟩
  rw [← hf.autMap_apply a haZ, ← hf.autMap_apply a haZ, h, hσ]

omit [Finite K] in
theorem IsSemiF.mul {σ τ : K →+* K} {a b : MulAut W} (ha : IsSemiF f σ a)
    (hb : IsSemiF f τ b) : IsSemiF f (σ.comp τ) (a * b) := fun c w w' h => by
  rw [MulAut.mul_apply, MulAut.mul_apply, RingHom.comp_apply]
  exact ha _ _ _ (hb c w w' h)

omit [Finite K] in
theorem IsSemiF.invol (hf : KGNat.IsCoord LM H Z π f) {x₀ : M} (hx₀ : x₀ ≠ 0)
    {σ : K →+* K} {a : MulAut W} (ha : IsSemiF f σ a) (ha2 : a * a = 1) :
    ∀ c, σ (σ c) = c := by
  intro c
  obtain ⟨w, hw⟩ := hf.surj x₀
  obtain ⟨w', hw'⟩ := hf.surj (c • x₀)
  have h1 := (ha.mul ha) c w w' (by rw [hw, hw'])
  rw [ha2, MulAut.one_apply, MulAut.one_apply, hw, hw', RingHom.comp_apply] at h1
  exact (smul_left_injective K hx₀ h1).symm

theorem isSemiF_id_mul {n : ℕ} (hK : Nat.card K = 2 ^ n) (hf : KGNat.IsCoord LM H Z π f)
    {x₀ : M} (hx₀ : x₀ ≠ 0) {σa σb : K →+* K} {a b : MulAut W} (ha : IsSemiF f σa a)
    (hb : IsSemiF f σb b) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (hna : ¬ IsSemiF f (RingHom.id K) a) (hnb : ¬ IsSemiF f (RingHom.id K) b) :
    IsSemiF f (RingHom.id K) (a * b) := by
  have hσa1 : ∃ c, σa c ≠ c := by
    by_contra h
    push Not at h
    exact hna fun c w w' hw => by rw [ha c w w' hw, h c, RingHom.id_apply]
  have hσb1 : ∃ c, σb c ≠ c := by
    by_contra h
    push Not at h
    exact hnb fun c w w' hw => by rw [hb c w w' hw, h c, RingHom.id_apply]
  have heq := ringHom_eq_of_involutive hK (ha.invol hf hx₀ ha2) (hb.invol hf hx₀ hb2) hσa1 hσb1
  intro c w w' h
  rw [(ha.mul hb) c w w' h, RingHom.comp_apply, ← heq, ha.invol hf hx₀ ha2, RingHom.id_apply]

theorem le_of_aSet_two {n : ℕ} (hK : Nat.card K = 2 ^ n) (hf : KGNat.IsCoord LM H Z π f)
    (hcomm : ∀ T : M →+ M, (∀ (γ : D.Gam) (x : M), T (LM.lin γ x) = LM.lin γ (T x)) →
      ∃ c : K, ∀ x, T x = c • x)
    {x₀ : M} (hx₀ : x₀ ≠ 0) {A : Subgroup (MulAut W)} (hAab : IsElemAbelian2 A)
    (hAfix : ∀ B ≤ A, E3.mQuot A B < 2 → fixV B = fixV A)
    (hAZ : ∀ a ∈ A, ∀ z ∈ Z, a z ∈ Z) (hAH : ∀ a ∈ A, ∀ h ∈ H, a * h * a⁻¹ ∈ H)
    (hlin : ∀ a ∈ A, IsSemiF f (RingHom.id K) a → a ∈ H)
    (hpt : ∀ B ≤ H, IsPGroup 2 ↥B →
      ∃ u₀ : M, u₀ ≠ 0 ∧ ∀ c : K, ∃ w, f w = c • u₀ ∧ ∀ b ∈ B, b w = w) :
    A ≤ H := by
  have ha2 : ∀ a ∈ A, a * a = 1 := fun a ha => by rw [← sq]; exact hAab.2 a ha
  have hainv : ∀ a ∈ A, a⁻¹ = a := fun a ha => inv_eq_of_mul_eq_one_right (ha2 a ha)
  have hsemi : ∀ a ∈ A, ∃ σ : K →+* K, IsSemiF f σ a := fun a ha =>
    exists_isSemiF hf hcomm hx₀ (hAZ a ha) (by rw [hainv a ha]; exact hAZ a ha) fun h hh => by
      rw [hainv a ha]
      have := hAH a ha h hh
      rwa [hainv a ha] at this
  let A₀ : Subgroup (MulAut W) :=
    { carrier := {a | a ∈ A ∧ IsSemiF f (RingHom.id K) a}
      mul_mem' := fun {a b} ha hb => ⟨A.mul_mem ha.1 hb.1, fun c w w' h => by
        rw [MulAut.mul_apply, MulAut.mul_apply]
        exact ha.2 _ _ _ (hb.2 c w w' h)⟩
      one_mem' := ⟨A.one_mem, fun c w w' h => by simpa using h⟩
      inv_mem' := fun {a} ha => by
        change a⁻¹ ∈ A ∧ IsSemiF f (RingHom.id K) a⁻¹
        rw [hainv a ha.1]
        exact ha }
  have hmem₀ : ∀ a, a ∈ A₀ ↔ a ∈ A ∧ IsSemiF f (RingHom.id K) a := fun a => Iff.rfl
  have hidx : E3.mQuot A A₀ < 2 := by
    unfold E3.mQuot
    by_cases hall : ∀ a ∈ A, IsSemiF f (RingHom.id K) a
    · rw [Subgroup.relIndex_eq_one.mpr fun a ha => (hmem₀ a).mpr ⟨ha, hall a ha⟩,
        padicValNat_one_right]
      norm_num
    · push Not at hall
      obtain ⟨a₁, ha₁, hna₁⟩ := hall
      have h2 : A₀.relIndex A = 2 := by
        rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
        refine ⟨⟨a₁, ha₁⟩, fun b => ?_⟩
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, hmem₀, hmem₀]
        by_cases hb : IsSemiF f (RingHom.id K) (b : MulAut W)
        · refine Or.inr ⟨⟨b.2, hb⟩, fun h => hna₁ ?_⟩
          have e : (b : MulAut W) * ((b : MulAut W) * a₁) = a₁ := by
            rw [← mul_assoc, ha2 _ b.2, one_mul]
          have h3 := hb.mul h.2
          rwa [e, RingHom.id_comp] at h3
        · exact Or.inl ⟨⟨A.mul_mem b.2 ha₁, isSemiF_id_mul hK hf hx₀ (hsemi _ b.2).choose_spec
            (hsemi _ ha₁).choose_spec (ha2 _ b.2) (ha2 _ ha₁) hb hna₁⟩, fun h => hb h.2⟩
      rw [h2, padicValNat_self]
      norm_num
  have hfix0 := hAfix A₀ (fun a ha => ((hmem₀ a).mp ha).1) hidx
  have hA₀H : A₀ ≤ H := fun a ha => hlin a ((hmem₀ a).mp ha).1 ((hmem₀ a).mp ha).2
  have hA₀2 : IsPGroup 2 ↥A₀ := fun b =>
    ⟨1, Subtype.ext (by simpa using hAab.2 _ ((hmem₀ _).mp b.2).1)⟩
  obtain ⟨u₀, hu₀, hline⟩ := hpt A₀ hA₀H hA₀2
  intro a ha
  obtain ⟨σ, hσ⟩ := hsemi a ha
  have hfixA : ∀ v, (∀ b ∈ A₀, b v = v) → a v = v := fun v hv => by
    have hv' : v ∈ fixV A₀ := hv
    rw [hfix0] at hv'
    exact hv' a ha
  have hσc : ∀ d, σ d = d := by
    intro d
    obtain ⟨w₁, hw₁, hf₁⟩ := hline 1
    obtain ⟨w₂, hw₂, hf₂⟩ := hline d
    have h1 := hσ d w₁ w₂ (by rw [hw₁, hw₂, one_smul])
    rw [hfixA w₁ hf₁, hfixA w₂ hf₂, hw₁, hw₂, one_smul] at h1
    exact (smul_left_injective K hu₀ h1).symm
  refine hlin a ha fun c w w' hw => ?_
  rw [hσ c w w' hw, hσc, RingHom.id_apply]

end BK2

end CFSG.Quasithin.Vol2.Ch11.SecB
