module

public import CFSG.Quasithin.Background.A3Structure313Mult
public import CFSG.Quasithin.Background.A3Structure313Irr
public import CFSG.Quasithin.Background.A3Structure312Quotient
public import CFSG.Quasithin.Background.A3Structure312Iso

public section

namespace CFSG.Quasithin.A313

open Matrix

variable {Λ : Type} [Group Λ] [Finite Λ]

@[expose] def imgOdd (B : Subgroup Λ) : Subgroup (Λ ⧸ CFSG.oddCore Λ) :=
  B.map (QuotientGroup.mk' (CFSG.oddCore Λ))

@[expose] noncomputable def rho (B : Subgroup Λ) : ↥B →* ↥(imgOdd B) :=
  ((QuotientGroup.mk' (CFSG.oddCore Λ)).comp B.subtype).codRestrict _ (fun b => ⟨b, b.2, rfl⟩)

omit [Finite Λ] in
theorem rho_surjective (B : Subgroup Λ) : Function.Surjective (rho B) := by
  rintro ⟨_, ⟨b, hb, rfl⟩⟩
  exact ⟨⟨b, hb⟩, rfl⟩

omit [Finite Λ] in
theorem mem_ker_rho {B : Subgroup Λ} {b : ↥B} :
    b ∈ (rho B).ker ↔ (b : Λ) ∈ CFSG.oddCore Λ := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)
  · intro h
    exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)

theorem odd_card_ker_rho (B : Subgroup Λ) : Odd (Nat.card ↥(rho B).ker) := by
  have hle : (rho B).ker.map B.subtype ≤ CFSG.oddCore Λ := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_ker_rho.mp hx
  have h1 : Nat.card ↥((rho B).ker.map B.subtype) = Nat.card ↥(rho B).ker :=
    Subgroup.card_map_of_injective B.subtype_injective
  rw [← h1]
  exact (A312.odd_card_oddCore Λ).of_dvd_nat (Subgroup.card_dvd_of_le hle)

theorem oddCore_map_eq {B : Subgroup Λ} {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hM : IsSL2 r ↥(imgOdd B)) :
    (CFSG.oddCore ↥B).map B.subtype = B ⊓ CFSG.oddCore Λ := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, ?_⟩
    have hKbot : (CFSG.oddCore ↥B).map (rho B) = ⊥ := by
      have : ((CFSG.oddCore ↥B).map (rho B)).Normal :=
        Subgroup.Normal.map inferInstance _ (rho_surjective B)
      refine IsSL2.eq_bot_of_odd hr hr5 hM ?_
      exact (A312.odd_card_oddCore ↥B).of_dvd_nat
        (Subgroup.card_map_dvd (CFSG.oddCore ↥B) (rho B))
    have hmem : rho B x ∈ (CFSG.oddCore ↥B).map (rho B) := ⟨x, hx, rfl⟩
    rw [hKbot, Subgroup.mem_bot] at hmem
    exact mem_ker_rho.mp (MonoidHom.mem_ker.mpr hmem)
  · rintro y ⟨hyB, hyO⟩
    have hker : (⟨y, hyB⟩ : ↥B) ∈ (rho B).ker := mem_ker_rho.mpr hyO
    have hle : (rho B).ker ≤ CFSG.oddCore ↥B := le_sSup ⟨inferInstance, odd_card_ker_rho B⟩
    exact ⟨⟨y, hyB⟩, hle hker, rfl⟩

omit [Finite Λ] in
theorem inf_ne_bot_of_not_quasisimple {B : Subgroup Λ} {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hM : IsSL2 r ↥(imgOdd B)) (hnq : ¬ CFSG.IsQuasisimple ↥B) :
    B ⊓ CFSG.oddCore Λ ≠ ⊥ := by
  intro hbot
  apply hnq
  have hinj : Function.Injective (rho B) := by
    rw [← MonoidHom.ker_eq_bot_iff, Subgroup.eq_bot_iff_forall]
    intro x hx
    have hx' : (x : Λ) ∈ B ⊓ CFSG.oddCore Λ := ⟨x.2, mem_ker_rho.mp hx⟩
    rw [hbot, Subgroup.mem_bot] at hx'
    exact Subtype.ext hx'
  let e : ↥B ≃* ↥(imgOdd B) := MulEquiv.ofBijective (rho B) ⟨hinj, rho_surjective B⟩
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm (IsSL2.isQuasisimple hr hr5 hM)

omit [Finite Λ] in
theorem eq_top_of_imgOdd_eq_top {B : Subgroup Λ} (htop : imgOdd B = ⊤)
    (hOB : CFSG.oddCore Λ ≤ B) : B = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have h1 : QuotientGroup.mk' (CFSG.oddCore Λ) x ∈ imgOdd B := by rw [htop]; trivial
  obtain ⟨b, hb, hbx⟩ := h1
  have h2 : b⁻¹ * x ∈ CFSG.oddCore Λ := (QuotientGroup.eq (s := CFSG.oddCore Λ)).mp hbx
  have : x = b * (b⁻¹ * x) := by group
  rw [this]
  exact B.mul_mem hb (hOB h2)

omit [Finite Λ] in
theorem isSL2_quotient_of_natural {p : ℕ} (hF : CFSG.fittingSubgroup Λ = CFSG.oddCore Λ)
    (hnat : NaturalSL2Action p Λ (CFSG.fittingSubgroup Λ)) :
    IsSL2 p (Λ ⧸ CFSG.oddCore Λ) := by
  obtain ⟨-, ψ, hψs, hψk, -⟩ := hnat
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (hF.symm.trans hψk.symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)⟩

omit [Finite Λ] in
theorem p_eq_five_of_case4 (hF : CFSG.fittingSubgroup Λ = CFSG.oddCore Λ) (h4 : A36Case4 Λ)
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hΛ : IsSL2 p₀ (Λ ⧸ CFSG.oddCore Λ)) : p₀ = 5 := by
  obtain ⟨-, -, h5, -⟩ := h4
  have e : Λ ⧸ CFSG.fittingSubgroup Λ ≃* Λ ⧸ CFSG.oddCore Λ :=
    QuotientGroup.quotientMulEquivOfEq hF
  exact IsSL2.eq_of_isSL2 hp₀ Nat.prime_five hΛ (IsSL2.of_mulEquiv e h5)

omit [Finite Λ] in
theorem inf_eq_bot_or_eq {B : Subgroup Λ} {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hM : IsSL2 r ↥(imgOdd B)) (hF : CFSG.fittingSubgroup Λ = CFSG.oddCore Λ) {p : ℕ}
    [Fact p.Prime] (hnat : NaturalSL2Action p Λ (CFSG.fittingSubgroup Λ)) :
    B ⊓ CFSG.oddCore Λ = ⊥ ∨ B ⊓ CFSG.oddCore Λ = CFSG.oddCore Λ := by
  obtain ⟨e, ψ, hψs, hψk, hact⟩ := hnat
  have hKF : B ⊓ CFSG.oddCore Λ ≤ CFSG.fittingSubgroup Λ := fun x hx => hF ▸ hx.2
  have hBK : B ≤ Subgroup.normalizer ((B ⊓ CFSG.oddCore Λ : Subgroup Λ) : Set Λ) := by
    intro b hb
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hb, ?_⟩
    have : Subgroup.normalizer (CFSG.oddCore Λ : Set Λ) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr inferInstance
    rw [this]
    trivial
  have hsolv : ¬ Group.IsSolvable ↥(B.map ψ) := by
    intro hs
    let σ : ↥B →* ↥(B.map ψ) :=
      (ψ.comp B.subtype).codRestrict (B.map ψ) (fun b => ⟨b, b.2, rfl⟩)
    have hσ : Function.Surjective σ := by
      rintro ⟨_, ⟨b, hb, rfl⟩⟩
      exact ⟨⟨b, hb⟩, rfl⟩
    have hkerEq : (rho B).ker = σ.ker := by
      ext b
      rw [mem_ker_rho, MonoidHom.mem_ker]
      constructor
      · intro h
        apply Subtype.ext
        have : (b : Λ) ∈ ψ.ker := by rw [hψk, hF]; exact h
        exact this
      · intro h
        have : (b : Λ) ∈ ψ.ker := congrArg Subtype.val h
        rw [hψk, hF] at this
        exact this
    let e' : ↥(imgOdd B) ≃* ↥(B.map ψ) :=
      (QuotientGroup.quotientKerEquivOfSurjective (rho B) (rho_surjective B)).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hkerEq).trans
          (QuotientGroup.quotientKerEquivOfSurjective σ hσ))
    have : Group.IsSolvable ↥(imgOdd B) :=
      Group.isSolvable_of_isSolvable_injective (f := e'.toMonoidHom) e'.injective
    exact IsSL2.not_isSolvable hr hr5 hM this
  have := eq_bot_or_eq_of_natural (CFSG.fittingSubgroup Λ) e ψ hact B (B ⊓ CFSG.oddCore Λ) hKF
    hBK hsolv
  rcases this with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans hF)

theorem core (hmult : L2MultiplierFact) (hcom : A36Common Λ) (hcase : A36Case3 Λ ∨ A36Case4 Λ)
    {p₀ : ℕ} (hp₀ : p₀.Prime) (hp₀3 : 3 < p₀) (hΛ : IsSL2 p₀ (Λ ⧸ CFSG.oddCore Λ))
    {B : Subgroup Λ} (hB : B ≠ ⊤) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hM : IsSL2 r ↥(imgOdd B))
    (hdich : (imgOdd B = ⊤ ∧ r = p₀) ∨ (imgOdd B ≠ ⊤ ∧ r = 5 ∧ p₀ ≠ 5)) :
    (CFSG.IsQuasisimple ↥B ∧ IsSL2 r ↥B) ∨
      (¬ CFSG.IsQuasisimple ↥B ∧
        ((imgOdd B = ⊤ ∧ (CFSG.oddCore ↥B).map B.subtype < CFSG.oddCore Λ ∧ r = 5 ∧ p₀ = 5) ∨
         (imgOdd B ≠ ⊤ ∧
          IsExt Λ (fun V _ => IsElemAbelianOfRank p₀ 2 V) (fun Y _ => IsSL2 p₀ Y) ∧
          5 < p₀ ∧ r = 5 ∧ (CFSG.oddCore ↥B).map B.subtype = CFSG.oddCore Λ))) := by
  have hF : CFSG.fittingSubgroup Λ = CFSG.oddCore Λ := hcom.1
  by_cases hBq : CFSG.IsQuasisimple ↥B
  · left
    refine ⟨hBq, ?_⟩
    have hker := ker_eq_bot_of_quasisimple hmult hr hr5 hM (rho B) (rho_surjective B) hBq
    let e : ↥B ≃* ↥(imgOdd B) :=
      MulEquiv.ofBijective (rho B) ⟨(MonoidHom.ker_eq_bot_iff _).mp hker, rho_surjective B⟩
    exact IsSL2.of_mulEquiv e.symm hM
  right
  refine ⟨hBq, ?_⟩
  have hK := inf_ne_bot_of_not_quasisimple hr hr5 hM hBq
  have hodd := oddCore_map_eq hr hr5 hM
  rcases hdich with ⟨htop, hrp⟩ | ⟨hntop, hr5', hp0⟩
  ·
    have hc4 : A36Case4 Λ := by
      rcases hcase with h3 | h4
      · exfalso
        obtain ⟨p, hp, hp3, -, -, hnat⟩ := h3
        have : Fact p.Prime := ⟨hp⟩
        rcases inf_eq_bot_or_eq hr hr5 hM hF hnat with h | h
        · exact hK h
        · exact hB (eq_top_of_imgOdd_eq_top htop (h ▸ inf_le_left))
      · exact h4
    have hp5 : p₀ = 5 := p_eq_five_of_case4 hF hc4 hp₀ hΛ
    refine Or.inl ⟨htop, ?_, by omega, hp5⟩
    rw [hodd]
    refine lt_of_le_of_ne inf_le_right (fun h => hB ?_)
    exact eq_top_of_imgOdd_eq_top htop (h ▸ inf_le_left)
  ·
    have hc3 : A36Case3 Λ := by
      rcases hcase with h3 | h4
      · exact h3
      · exact absurd (p_eq_five_of_case4 hF h4 hp₀ hΛ) hp0
    obtain ⟨p, hp, hp3, -, hE, hnat⟩ := hc3
    have : Fact p.Prime := ⟨hp⟩
    have hpp : p = p₀ := IsSL2.eq_of_isSL2 hp hp₀ (isSL2_quotient_of_natural hF hnat) hΛ
    rcases inf_eq_bot_or_eq hr hr5 hM hF hnat with h | h
    · exact absurd h hK
    · refine Or.inr ⟨hntop, ?_, ?_, hr5', by rw [hodd, h]⟩
      · refine ⟨CFSG.fittingSubgroup Λ, inferInstance, ?_, ?_⟩
        · rw [← hpp]
          exact hE
        · rw [← hpp]
          have : IsSL2 p (Λ ⧸ CFSG.fittingSubgroup Λ) := by
            obtain ⟨-, ψ, hψs, hψk, -⟩ := hnat
            exact ⟨(QuotientGroup.quotientMulEquivOfEq hψk.symm).trans
              (QuotientGroup.quotientKerEquivOfSurjective ψ hψs)⟩
          exact this
      · have h4 : p₀ ≠ 4 := by
          rintro rfl
          norm_num at hp₀
        omega

end CFSG.Quasithin.A313
