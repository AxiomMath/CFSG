module

public import CFSG.Quasithin.Background.SmithD37Real
public import CFSG.Quasithin.Background.SmithD37Dim2
public import CFSG.Quasithin.Background.SmithD37Core
import CFSG.Quasithin.Background.F918P1

public section

namespace CFSG.Quasithin.SmithD37

open CFSG.Assembly.LowTwoRank
open scoped Matrix

section SL

variable {F : Type} [Field F]

theorem statedScalars_subgroupOf_eq_bot [CharP F 2] :
    (StatedScalars (Fin 2) F).subgroupOf (StatedSL 2 F) = ⊥ :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot

end SL

section Six

theorem mul_comm_of_card_dvd_six {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (h : Nat.card X ∣ 6) (a b : X) : a * b = b * a := by
  have hcyc : IsCyclic X := by
    by_cases h3 : 3 ∣ Nat.card X
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := X) 3 h3
      have hH : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
      have hmi := (Subgroup.zpowers x).card_mul_index
      rw [hH] at hmi
      have hi : (Subgroup.zpowers x).index = 1 ∨ (Subgroup.zpowers x).index = 2 := by
        obtain ⟨k, hk⟩ := h
        have h32 : 3 * ((Subgroup.zpowers x).index * k) = 3 * 2 := by
          rw [← mul_assoc, hmi, ← hk]
        have := Nat.eq_of_mul_eq_mul_left (by norm_num) h32
        have := Nat.le_of_dvd (by norm_num) (Dvd.intro k this)
        have h0 : (Subgroup.zpowers x).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        omega
      have hn : (Subgroup.zpowers x).Normal := by
        rcases hi with hi | hi
        · rw [Subgroup.index_eq_one.mp hi]
          infer_instance
        · exact Subgroup.normal_of_index_eq_two hi
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with hb | ht
      · rw [hb, Subgroup.card_bot] at hH
        omega
      · exact isCyclic_iff_exists_zpowers_eq_top.mpr ⟨x, ht⟩
    · have h2 : Nat.card X ∣ 2 := by
        have : Nat.Coprime (Nat.card X) 3 :=
          (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3))
        exact this.dvd_of_dvd_mul_right (by simpa using h)
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
      · have : Subsingleton X := (Nat.card_eq_one_iff_unique.mp h1).1
        exact isCyclic_of_subsingleton
      · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact isCyclic_of_prime_card h1
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨i, rfl⟩ := hg a
  obtain ⟨j, rfl⟩ := hg b
  exact (Commute.zpow_zpow_self g i j).eq

end Six

section Model

variable {F : Type} [Field F] [Fintype F] [CharP F 2]

noncomputable def statedProjEquiv : StatedProj (StatedSL 2 F) ≃* ↥(StatedSL 2 F) :=
  (QuotientGroup.quotientMulEquivOfEq statedScalars_subgroupOf_eq_bot).trans
    QuotientGroup.quotientBot

theorem isPSL_of_mulEquiv {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (hF : Nat.card F = 2 ^ n) (e : X ≃* ↥(StatedSL 2 F)) : IsPSL 2 2 n X := by
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, F, inferInstance, inferInstance, hF,
    ⟨e.trans statedProjEquiv.symm⟩⟩
  · intro h
    have h2 : 2 ^ n = 2 := congrArg Prod.snd h
    omega
  · intro h
    have h2 : 2 ^ n = 3 := congrArg Prod.snd h
    omega

end Model

section Pair

variable {F : Type} [Field F] [Fintype F] [CharP F 2]
variable {U : Type} [CommGroup U]

theorem range_eq_statedSL {L : Subgroup (MulAut U)}
    (R : ↥L →* Matrix.GeneralLinearGroup (Fin 2) F) (hR : Function.Injective R)
    (hA : A38Types ↥L)
    (hirr : ∀ S : AddSubgroup (Fin 2 → F), (∀ l : ↥L, ∀ v ∈ S,
      ((R l : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ S) →
        S = ⊥ ∨ S = ⊤)
    (hend : ∀ φ : (Fin 2 → F) →+ (Fin 2 → F), (∀ (l : ↥L) v,
      φ (((R l : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        ((R l : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ φ v) →
      ∃ c : F, ∀ v, φ v = c • v) :
    R.range = StatedSL 2 F ∧ ∃ n, 2 ≤ n ∧ Nat.card F = 2 ^ n := by
  have hA' : A38Types ↥R.range := a38Types_congr (MonoidHom.ofInjective hR) hA
  have hirr' : ∀ S : AddSubgroup (Fin 2 → F), (∀ h ∈ R.range, ∀ v ∈ S,
      ((h : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v ∈ S) →
        S = ⊥ ∨ S = ⊤ := by
    intro S hS
    exact hirr S fun l v hv => hS _ ⟨l, rfl⟩ v hv
  have hend' : ∀ φ : (Fin 2 → F) →+ (Fin 2 → F), (∀ h ∈ R.range, ∀ v,
      φ (((h : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v) =
        ((h : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ φ v) →
      ∃ c : F, ∀ v, φ v = c • v := by
    intro φ hφ
    exact hend φ fun l v => hφ _ ⟨l, rfl⟩ v
  refine ⟨eq_statedSL_of_dim_two R.range hA' hirr' hend', ?_⟩
  obtain ⟨n, -, hn⟩ := FiniteField.card F 2
  refine ⟨n, ?_, Nat.card_eq_fintype_card.trans hn⟩
  by_contra hlt
  have hn1 : (n : ℕ) = 1 := by
    have := n.pos
    omega
  have : IsSimpleGroup ↥R.range :=
    CFSG.QuasithinUnique.Vol2Native.L122A.isSimpleGroup_of_a38Types hA'
  have hdvd : Nat.card ↥R.range ∣ 6 := by
    have h6 : Nat.card (Matrix.GeneralLinearGroup (Fin 2) F) = 6 := by
      rw [Matrix.card_GL_field, hn, hn1]
      simp [Fin.prod_univ_two]
    rw [← h6]
    exact Subgroup.card_subgroup_dvd_card _
  exact not_forall_mul_comm R.range hirr' hend' (mul_comm_of_card_dvd_six hdvd)

variable {L₁ L₂ : Subgroup (MulAut U)}

omit [Fintype F] [CharP F 2] in
theorem coe_symm_ofInjective {L : Subgroup (MulAut U)} {d : ℕ}
    {R : ↥L →* Matrix.GeneralLinearGroup (Fin d) F} (hR : Function.Injective R)
    {H : Subgroup (Matrix.GeneralLinearGroup (Fin d) F)} (h : R.range = H) (g : ↥H) :
    R (((MonoidHom.ofInjective hR).trans (MulEquiv.subgroupCongr h)).symm g) = g := by
  set e := (MonoidHom.ofInjective hR).trans (MulEquiv.subgroupCongr h)
  have : ((e (e.symm g) : ↥H) : Matrix.GeneralLinearGroup (Fin d) F) = R (e.symm g) := rfl
  rw [← this, MulEquiv.apply_symm_apply]

theorem omega4_of_dim_two (Mm : MatModel L₁ L₂ F 2)
    (hA₁ : A38Types ↥L₁) (hA₂ : A38Types ↥L₂) :
    ∃ n, IsPSL 2 2 n ↥L₁ ∧ Omega4PlusModule (L₁ ⊔ L₂) n := by
  obtain ⟨h₁, n, hn, hF⟩ := range_eq_statedSL Mm.R₁ Mm.inj₁ hA₁ Mm.irr₁ Mm.end₁
  obtain ⟨h₂, -⟩ := range_eq_statedSL Mm.R₂ Mm.inj₂ hA₂ Mm.irr₂ Mm.end₂
  set e₁ := (MonoidHom.ofInjective Mm.inj₁).trans (MulEquiv.subgroupCongr h₁)
  set e₂ := (MonoidHom.ofInjective Mm.inj₂).trans (MulEquiv.subgroupCongr h₂)
  have hrange : ∀ (L : Subgroup (MulAut U)) (e : ↥L ≃* ↥(StatedSL 2 F)),
      (L.subtype.comp e.symm.toMonoidHom).range = L := by
    intro L e
    ext x
    constructor
    · rintro ⟨g, rfl⟩
      exact (e.symm g).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp⟩
  refine ⟨n, isPSL_of_mulEquiv hn hF e₁, F, inferInstance, inferInstance, hF, ?_⟩
  refine tensorNat_realizes_of_pair L₁ L₂ Mm.β (L₁.subtype.comp e₁.symm.toMonoidHom)
    (L₂.subtype.comp e₂.symm.toMonoidHom) (hrange L₁ e₁) (hrange L₂ e₂) ?_ ?_
  · intro g u
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.coe_subtype]
    rw [Mm.act₁, coe_symm_ofInjective]
  · intro g u
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      Subgroup.coe_subtype]
    rw [Mm.act₂, coe_symm_ofInjective]

end Pair

end CFSG.Quasithin.SmithD37
