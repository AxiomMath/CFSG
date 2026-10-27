module

public import CFSG.RankThree.PartOne.U5K.Kf.Std
public import CFSG.RankThree.PartOne.U5K.Kf.Assist
public import CFSG.RankThree.PartOne.U5K.Kf.Inner
public import CFSG.RankThree.PartOne.U5K.Kf.Outer
public import CFSG.RankThree.PartOne.U5K.Kf.Atil

public section

namespace CFSG.RankThree.PartOne.U5K.Kf

open Matrix CFSG CFSG.RankThree.PartOne CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.RankThree.PartOne.KCUnitaryModel

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ} [Fact p.Prime]

theorem mem_normalizer_map_conj {G : Type*} [Group G] {Q : Subgroup G} {g : G} (γ : G)
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    γ * g * γ⁻¹ ∈ Subgroup.normalizer
      ((Q.map (MulAut.conj γ).toMonoidHom : Subgroup G) : Set G) := by
  have key : ∀ y, y ∈ Q.map (MulAut.conj γ).toMonoidHom ↔ γ⁻¹ * y * γ ∈ Q := by
    intro y
    rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  rw [key, key]
  have := hg (γ⁻¹ * x * γ)
  have e : γ⁻¹ * (γ * g * γ⁻¹ * x * (γ * g * γ⁻¹)⁻¹) * γ = g * (γ⁻¹ * x * γ) * g⁻¹ := by group
  rw [e]
  exact this

theorem ZetaData.false_of_distinguished (Z : ZetaData h p)
    {Ab : Subgroup (MulAut (primeFormP h (idGram K 5)))}
    (P : primeFormUnitary h (idGram K 5))
    (hD : Ab ≤ primeFormD h (idGram K 5))
    (hcardÃ : Nat.card (Z.Atil P Ab) = p ^ 4)
    (hG : ∀ i j : Fin 5, i ≠ j → ∃ a : Fin 5 → ZMod p,
      Multiplicative.ofAdd a ∈ Z.Atil P Ab ∧ a i ≠ a j)
    (S : Subgroup (MulAut (primeFormP h (idGram K 5)))) (hSne : S ≠ ⊥) (hS2 : IsPGroup 2 S)
    (hSn : Ab ≤ Subgroup.normalizer (S : Set _)) : False := by
  classical
  have hfinK := h.finite
  set Inn : Subgroup (MulAut (primeFormP h (idGram K 5))) :=
    (MulAut.conj : primeFormP h (idGram K 5) →* MulAut (primeFormP h (idGram K 5))).range
    with hInn
  have hInnN : Inn.Normal :=
    CFSG.ComponentClassification.OuterAutomorphisms.innerNormal (primeFormP h (idGram K 5))
  have hDN : (primeFormD h (idGram K 5)).Normal := primeFormD_normal (by norm_num) Z.three_lt
  set γ : MulAut (primeFormP h (idGram K 5)) := (primeFormConjHom h (idGram K 5) P)⁻¹ with hγ
  have hpar : ∀ a : Fin 5 → ZMod p, Multiplicative.ofAdd a ∈ Z.Atil P Ab → Z.par P a ∈ Ab :=
    fun a ha => (Z.mem_Atil P Ab a).1 ha
  have hρdg : ∀ a : Fin 5 → ZMod p, primeFormConjHom h (idGram K 5) (Z.dgU a) =
      γ * Z.par P a * γ⁻¹ := by
    intro a
    unfold ZetaData.par ZetaData.Y
    rw [hγ, map_mul, map_mul, map_inv]
    group
  by_cases hQ : S ⊓ Inn = ⊥
  · obtain ⟨s, hsS, hs1, hs2, -⟩ := exists_central_involution hS2 hSne
    have hsD : s ∉ primeFormD h (idGram K 5) := by
      intro hsD'
      have hsI : s ∈ Inn := two_mem_inn h hsD' (k := 1) (by simpa [pow_two] using hs2)
      have : s ∈ S ⊓ Inn := ⟨hsS, hsI⟩
      rw [hQ] at this
      exact hs1 (Subgroup.mem_bot.1 this)
    have hcentr : ∀ a : Fin 5 → ZMod p, Multiplicative.ofAdd a ∈ Z.Atil P Ab → ∀ x ∈ S,
        Z.par P a * x = x * Z.par P a := by
      intro a ha x hx
      set b := Z.par P a with hb
      have hbA : b ∈ Ab := hpar a ha
      have hbS : b ∈ Subgroup.normalizer (S : Set _) := hSn hbA
      have hc1 : b * x * b⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.1 hbS x).1 hx
      have hcS : b * x * b⁻¹ * x⁻¹ ∈ S := S.mul_mem hc1 (S.inv_mem hx)
      have hcD : b * x * b⁻¹ * x⁻¹ ∈ primeFormD h (idGram K 5) := by
        have : b * (x * b⁻¹ * x⁻¹) ∈ primeFormD h (idGram K 5) :=
          (primeFormD h (idGram K 5)).mul_mem (hD hbA)
            (hDN.conj_mem _ ((primeFormD h (idGram K 5)).inv_mem (hD hbA)) x)
        simpa [mul_assoc] using this
      obtain ⟨k, hk⟩ := hS2 ⟨_, hcS⟩
      have hk' : (b * x * b⁻¹ * x⁻¹) ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
      have hcInn := two_mem_inn h hcD hk'
      have : b * x * b⁻¹ * x⁻¹ ∈ S ⊓ Inn := ⟨hcS, hcInn⟩
      rw [hQ] at this
      have h1 : b * x * b⁻¹ * x⁻¹ = 1 := Subgroup.mem_bot.1 this
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
      exact h1
    have hs'2 : γ * s * γ⁻¹ * (γ * s * γ⁻¹) = 1 := by
      calc γ * s * γ⁻¹ * (γ * s * γ⁻¹) = γ * (s * s) * γ⁻¹ := by group
        _ = 1 := by rw [hs2]; group
    have hs'D : γ * s * γ⁻¹ ∉ primeFormD h (idGram K 5) := by
      intro hmem
      apply hsD
      have := hDN.conj_mem _ hmem γ⁻¹
      simpa [mul_assoc] using this
    refine Z.no_outer hG hcardÃ (γ * s * γ⁻¹) hs'2 hs'D (fun a ha => ?_)
    rw [hρdg a]
    calc γ * Z.par P a * γ⁻¹ * (γ * s * γ⁻¹) = γ * (Z.par P a * s) * γ⁻¹ := by group
      _ = γ * (s * Z.par P a) * γ⁻¹ := by rw [hcentr a ha s hsS]
      _ = γ * s * γ⁻¹ * (γ * Z.par P a * γ⁻¹) := by group
  · set Q : Subgroup (MulAut (primeFormP h (idGram K 5))) := S ⊓ Inn with hQdef
    have hQ2 : IsPGroup 2 Q := hS2.to_le inf_le_left
    set Q' : Subgroup (MulAut (primeFormP h (idGram K 5))) :=
      Q.map (MulAut.conj γ).toMonoidHom with hQ'
    have hQ'2 : IsPGroup 2 Q' := hQ2.map _
    have hQ'ne : Q' ≠ ⊥ := by
      intro h0
      apply hQ
      exact (Subgroup.map_eq_bot_iff_of_injective Q (f := (MulAut.conj γ).toMonoidHom)
        (MulAut.conj γ).injective).1 h0
    have hQ'inn : Q' ≤ Inn := by
      rintro _ ⟨x, hx, rfl⟩
      exact hInnN.conj_mem x hx.2 γ
    refine Z.no_inner_core hG Q' hQ'2 hQ'ne hQ'inn (fun a ha => ?_)
    rw [hρdg a]
    refine mem_normalizer_map_conj γ ?_
    set b := Z.par P a with hb
    have hbA : b ∈ Ab := hpar a ha
    have hbS : b ∈ Subgroup.normalizer (S : Set _) := hSn hbA
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxS, hxI⟩
      exact ⟨(Subgroup.mem_normalizer_iff.1 hbS x).1 hxS, hInnN.conj_mem x hxI b⟩
    · rintro ⟨hxS, hxI⟩
      refine ⟨(Subgroup.mem_normalizer_iff.1 hbS x).2 hxS, ?_⟩
      have := hInnN.conj_mem _ hxI b⁻¹
      simpa [mul_assoc] using this

theorem ZetaData.exists_T_of_coincident (Z : ZetaData h p)
    (hZ : Subgroup.center (primeFormP h (idGram K 5)) = ⊥) (P : primeFormUnitary h (idGram K 5))
    {H Ab : Subgroup (MulAut (primeFormP h (idGram K 5)))}
    (hH : (MulAut.conj : primeFormP h (idGram K 5) →*
      MulAut (primeFormP h (idGram K 5))).range ≤ H)
    (hD : Ab ≤ primeFormD h (idGram K 5)) (hel : IsElementaryAbelian p ↥Ab)
    (hcard : Nat.card Ab = p ^ 3)
    (hP : ∀ x : primeFormUnitary h (idGram K 5), primeFormConjHom h (idGram K 5) x ∈ Ab →
      (((P⁻¹ * x * P : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K).IsDiag)
    (i j : Fin 5) (hij : i ≠ j)
    (hcoin : ∀ a : Fin 5 → ZMod p, Multiplicative.ofAdd a ∈ Z.Atil P Ab → a i = a j) :
    ∃ T : Subgroup (MulAut (primeFormP h (idGram K 5))), IsSylowOf 2 T H ∧
      Ab ≤ Subgroup.centralizer (omegaOneCenterIn T : Set (MulAut (primeFormP h (idGram K 5)))) ∧
      ∃ B : Subgroup (MulAut (primeFormP h (idGram K 5))), B ≤ Ab ∧ Nat.card B = p ^ 2 ∧
        B ≤ Subgroup.normalizer (pushingUpS T : Set (MulAut (primeFormP h (idGram K 5)))) := by
  classical
  have hfinK := h.finite
  set Ã := Z.Atil P Ab with hÃ
  have hcardÃ : Nat.card Ã = p ^ 4 := by
    rw [hÃ, Z.card_Atil P hel hD hP, hcard]
    ring
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_zero_one hij
  set ι : HypIndex 2 1 ≃ Fin 5 := stdIdx.trans σ with hι
  have hι0 : ι (.inl 0) = i := by simp [hι, stdIdx, hσ0]
  have hι1 : ι (.inr (.inr 0)) = j := by simp [hι, stdIdx, hσ1]
  have hcov : ∀ t : Fin 5, t = i ∨ t = j ∨ t = σ 2 ∨ t = σ 3 ∨ t = σ 4 := by
    intro t
    obtain ⟨u, rfl⟩ := σ.surjective t
    fin_cases u <;> simp [hσ0, hσ1]
  have hι2 : ι (.inl 1) = σ 2 := by simp [hι, stdIdx]
  have hι3 : ι (.inr (.inr 1)) = σ 3 := by simp [hι, stdIdx]
  set St : Subgroup (VM p) := Ã ⊓ Hsub p (σ 2) (σ 3) with hSt
  have hp0 : 0 < p := (Fact.out : p.Prime).pos
  have hStcard : Nat.card St = p ^ 3 := by
    have hup : Nat.card (St : Set (VM p)) ≤ p ^ 3 := by
      refine card_le_pow_three (St : Set (VM p)) i j (σ 2) (σ 3) (σ 4) hcov ?_
      intro a ha
      exact ⟨hcoin (Multiplicative.toAdd a) ha.1, mem_Hsub.1 ha.2⟩
    have hup' : Nat.card St ≤ p ^ 3 := by simpa using hup
    have hlow := card_le_mul_inf_Hsub (p := p) (σ 2) (σ 3) Ã
    rw [inf_comm, ← hSt, hcardÃ] at hlow
    have hlow' : p ^ 3 ≤ Nat.card St :=
      Nat.le_of_mul_le_mul_left (by simpa [pow_succ'] using hlow) hp0
    exact le_antisymm hup' hlow'
  set B : Subgroup (MulAut (primeFormP h (idGram K 5))) := St.map (Z.parHom P) with hB
  have hBle : B ≤ Ab := by
    rw [hB, Subgroup.map_le_iff_le_comap]
    exact inf_le_left
  have hBcard : Nat.card B = p ^ 2 := by
    have h1 := Subgroup.relIndex_mul_card (H := (Z.parHom P).ker) (K := St)
    rw [Subgroup.relIndex_ker, Z.ker_parHom] at h1
    have hkerSt : constSub p ≤ St := by
      intro a ha
      refine ⟨?_, ?_⟩
      · have : Z.parHom P a = 1 := by
          rw [← MonoidHom.mem_ker, Z.ker_parHom]
          exact ha
        show Z.parHom P a ∈ Ab
        rw [this]
        exact Ab.one_mem
      · exact mem_Hsub.2 (ha _ _)
    rw [inf_eq_left.2 hkerSt, card_constSub, hStcard] at h1
    exact Nat.eq_of_mul_eq_mul_right hp0 (by rw [h1]; ring)
  have hAb' : ∀ ρ₀ ∈ Ab, ∃ (X : primeFormUnitary h (idGram K 5)) (μ : Fin 5 → K),
      primeFormConjHom h (idGram K 5) X = ρ₀ ∧
      (((P⁻¹ * X * P : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) = diagonal μ ∧ μ (ι (.inl 0)) = μ (ι (.inr (.inr 0))) := by
    intro ρ₀ hρ₀
    obtain ⟨a', ha'⟩ := Z.le_range_parHom P hel hD hP hρ₀
    have hρa : Z.par P (Multiplicative.toAdd a') = ρ₀ := ha'
    have hmem : Multiplicative.ofAdd (Multiplicative.toAdd a') ∈ Ã := by
      rw [hÃ, Z.mem_Atil, hρa]
      exact hρ₀
    refine ⟨Z.Y P (Multiplicative.toAdd a'), fun s => zp Z.ζ (Multiplicative.toAdd a' s), hρa,
      ?_, ?_⟩
    · have e : P⁻¹ * Z.Y P (Multiplicative.toAdd a') * P = Z.dgU (Multiplicative.toAdd a') := by
        unfold ZetaData.Y
        group
      rw [e]
      exact Z.dgU_val _
    · rw [hι0, hι1]
      exact congrArg (zp Z.ζ) (hcoin _ hmem)
  have hB' : ∀ ρ₀ ∈ B, ∃ (X : primeFormUnitary h (idGram K 5)) (μ : Fin 5 → K),
      primeFormConjHom h (idGram K 5) X = ρ₀ ∧
      (((P⁻¹ * X * P : primeFormUnitary h (idGram K 5)) : GL (Fin 5) K) :
        Matrix (Fin 5) (Fin 5) K) = diagonal μ ∧
      μ (ι (.inl 0)) = μ (ι (.inr (.inr 0))) ∧ μ (ι (.inl 1)) = μ (ι (.inr (.inr 1))) := by
    rintro ρ₀ ⟨a', ha'St, ha'⟩
    have hρa : Z.par P (Multiplicative.toAdd a') = ρ₀ := ha'
    refine ⟨Z.Y P (Multiplicative.toAdd a'), fun s => zp Z.ζ (Multiplicative.toAdd a' s), hρa,
      ?_, ?_, ?_⟩
    · have e : P⁻¹ * Z.Y P (Multiplicative.toAdd a') * P = Z.dgU (Multiplicative.toAdd a') := by
        unfold ZetaData.Y
        group
      rw [e]
      exact Z.dgU_val _
    · rw [hι0, hι1]
      exact congrArg (zp Z.ζ) (hcoin _ ha'St.1)
    · rw [hι2, hι3]
      exact congrArg (zp Z.ζ) (mem_Hsub.1 ha'St.2)
  obtain ⟨T, hT, hA, hBn⟩ := exists_T_std h Z.three_lt.le hZ P ι hH hAb' hB'
  exact ⟨T, hT, hA, B, hBle, hBcard, hBn⟩

theorem ZetaData.kf_identity (Z : ZetaData h p)
    (hZ : Subgroup.center (primeFormP h (idGram K 5)) = ⊥)
    {H Ab : Subgroup (MulAut (primeFormP h (idGram K 5)))}
    (hH : (MulAut.conj : primeFormP h (idGram K 5) →*
      MulAut (primeFormP h (idGram K 5))).range ≤ H)
    (hD : Ab ≤ primeFormD h (idGram K 5)) (hel : IsElementaryAbelian p ↥Ab)
    (hcard : Nat.card Ab = p ^ 3)
    (hS : ∃ S : Subgroup (MulAut (primeFormP h (idGram K 5))), S ≠ ⊥ ∧ IsPGroup 2 S ∧
      Ab ≤ Subgroup.normalizer (S : Set _)) :
    ∃ T : Subgroup (MulAut (primeFormP h (idGram K 5))), IsSylowOf 2 T H ∧
      Ab ≤ Subgroup.centralizer (omegaOneCenterIn T : Set (MulAut (primeFormP h (idGram K 5)))) ∧
      ∃ B : Subgroup (MulAut (primeFormP h (idGram K 5))), B ≤ Ab ∧ Nat.card B = p ^ 2 ∧
        B ≤ Subgroup.normalizer (pushingUpS T : Set (MulAut (primeFormP h (idGram K 5)))) := by
  classical
  have hfinK := h.finite
  obtain ⟨P, hP⟩ := Z.exists_diagonalizing hel hcard.ge hD
  have hcardÃ : Nat.card (Z.Atil P Ab) = p ^ 4 := by
    rw [Z.card_Atil P hel hD hP, hcard]
    ring
  by_cases hNG : ∃ i j : Fin 5, i ≠ j ∧
      ∀ a : Fin 5 → ZMod p, Multiplicative.ofAdd a ∈ Z.Atil P Ab → a i = a j
  · obtain ⟨i, j, hij, hcoin⟩ := hNG
    exact Z.exists_T_of_coincident hZ P hH hD hel hcard hP i j hij hcoin
  · exfalso
    push Not at hNG
    obtain ⟨S, hSne, hS2, hSn⟩ := hS
    exact Z.false_of_distinguished P hD hcardÃ hNG S hSne hS2 hSn

end CFSG.RankThree.PartOne.U5K.Kf
