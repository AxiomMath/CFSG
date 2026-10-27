module

public import CFSG.Quasithin.Vol2.Ch3Sec3FactAutL3Red
public import CFSG.GH74.KGroups.L3EpsLinSyl
public import CFSG.GH74.KGroups.L3EpsUniSyl
public import CFSG.CharacterTheory.Wreathed.BrauerWongSupport
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.L3Eps

open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Wreathed CFSG.Wreathed.BrauerWong
open CFSG.GH74.KGroups.L3Eps CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LieType.Steinberg

theorem isPGroup_mulAut_of_wreathGenerators {G : Type*} [Group G] [Finite G] {n : ℕ} (hn : 2 ≤ n)
    {P : Subgroup G} {S₁ S₂ T : G} (hW : WreathGenerators n P S₁ S₂ T) :
    IsPGroup 2 (MulAut ↥P) := by
  have hinj := presentationHom_injective hW.pow_left hW.pow_right hW.sq_swap hW.comm hW.conj
    (by omega) P hW.closure_eq hW.card_eq
  have hrange := (presentationHom_range hW.pow_left hW.pow_right hW.sq_swap hW.comm hW.conj
    (by omega)).trans hW.closure_eq
  let e : Wreath (2 ^ n) ≃* ↥P :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  exact (wreath_automorphism_isPGroup n hn).of_equiv (MulAut.congr e)

theorem two_le_factorization_of_mod_four {n : ℕ} (hn : n % 4 = 0) (hn0 : n ≠ 0) :
    2 ≤ n.factorization 2 := by
  rw [← Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn0]
  exact Nat.dvd_of_mod_eq_zero (by omega)

section Linear

variable {F : Type} [Field F] [Finite F]

theorem exists_sylow_projectiveSL_wreath (hF4 : Nat.card F % 4 = 1) :
    ∃ P : Sylow 2 (projectiveSL 3 F), IsPGroup 2 (MulAut ↥(P : Subgroup (projectiveSL 3 F))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set a := (Nat.card F - 1).factorization 2 with ha
  set r := 2 ^ a with hr
  have hF1 : 1 < Nat.card F := Finite.one_lt_card
  have hF2 : Nat.card F % 2 = 1 := by omega
  have ha2 : 2 ≤ a := two_le_factorization_of_mod_four (by omega) (by omega)
  have hrdvd : r ∣ Nat.card F - 1 := Nat.ordProj_dvd _ 2
  have hr3 : ¬ 3 ∣ r := by
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hmu : Nat.card (mu r F) = r := card_mu hrdvd
  obtain ⟨α, hα⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := mu r F)
  have hαr : α ^ r = 1 := by
    have h := pow_orderOf_eq_one α
    rwa [hα, hmu] at h
  have hpow : ∀ x : mu r F, ∃ i : ℕ, α ^ i = x := by
    intro x
    have htop : Subgroup.zpowers α = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hα])
    have hx : x ∈ Subgroup.zpowers α := by rw [htop]; trivial
    obtain ⟨k, hk⟩ := (mem_powers_iff_mem_zpowers.mpr hx)
    exact ⟨k, hk⟩
  set S₁ := thetaMu (F := F) r ((α, 1) : mu r F × mu r F) with hS₁
  set S₂ := thetaMu (F := F) r ((1, α) : mu r F × mu r F) with hS₂
  have hpow₁ : ((α, 1) : mu r F × mu r F) ^ r = 1 := Prod.ext hαr (one_pow r)
  have hpow₂ : ((1, α) : mu r F × mu r F) ^ r = 1 := Prod.ext (one_pow r) hαr
  have hW : WreathGenerators a (Pexp (F := F) r) S₁ S₂ tauBar :=
    { closure_eq := by
        apply le_antisymm
        · rw [Subgroup.closure_le]
          rintro x (rfl | rfl | rfl)
          · exact Jexp_le_Pexp r ⟨_, rfl⟩
          · exact Jexp_le_Pexp r ⟨_, rfl⟩
          · exact tauBar_mem_Pexp r
        · rintro x ⟨j, ⟨⟨y, z⟩, rfl⟩, hx⟩
          obtain ⟨i, rfl⟩ := hpow y
          obtain ⟨k, rfl⟩ := hpow z
          have hj : thetaMu (F := F) r ((α ^ i, α ^ k) : mu r F × mu r F) = S₁ ^ i * S₂ ^ k := by
            rw [hS₁, hS₂, ← map_pow, ← map_pow, ← map_mul]
            congr 1
            ext <;> simp
          have hjc : thetaMu (F := F) r ((α ^ i, α ^ k) : mu r F × mu r F) ∈
              Subgroup.closure {S₁, S₂, tauBar} := by
            rw [hj]
            exact mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
              (pow_mem (Subgroup.subset_closure (by simp)) _)
          rcases hx with rfl | rfl
          · exact hjc
          · exact mul_mem hjc (Subgroup.subset_closure (by simp))
      card_eq := by
        rw [card_Pexp, card_Jexp hr3 hmu, hr]
        ring
      pow_left := by rw [hS₁, ← map_pow, hpow₁, map_one]
      pow_right := by rw [hS₂, ← map_pow, hpow₂, map_one]
      sq_swap := tauBar_sq
      comm := Jexp_comm r _ ⟨_, rfl⟩ _ ⟨_, rfl⟩
      conj := by
        rw [hS₁, hS₂, tauBar_inv]
        have h := tauBar_conj_theta (F := F) r α 1
        rwa [tauBar_inv] at h }
  obtain ⟨hP2, hmax⟩ := Pexp_sylow hF2 hF4 hr
  exact ⟨⟨Pexp r, hP2, fun {Q} hQ hle => le_antisymm (hmax Q hQ hle) hle⟩,
    isPGroup_mulAut_of_wreathGenerators ha2 hW⟩

theorem exists_sylow_wreath_of_isPSL {W : Type} [Group W] {p : ℕ} (h1 : p % 4 = 1)
    (hX : IsPSL 3 p 1 W) : ∃ P : Sylow 2 W, IsPGroup 2 (MulAut ↥(P : Subgroup W)) := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := exists_projectiveSL_equiv hX
  exact exists_sylow_of_mulEquiv e
    (exists_sylow_projectiveSL_wreath (by rw [hF, pow_one]; exact h1))

end Linear

section Unitary

variable {K : Type} [Field K] {p : ℕ}

theorem exists_sylow_SUgram_wreath (hU : UnitaryFieldData p 1 K) (hp2 : p ≠ 2)
    (h3 : p ^ 1 % 4 = 3) :
    ∃ P : Sylow 2 (↥(SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K)) ⧸
        (StatedScalars (Fin 3) K).subgroupOf (SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K))),
      IsPGroup 2 (MulAut ↥P.toSubgroup) := by
  have := hU.finite
  have : Fact p.Prime := ⟨hU.prime⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K p := hU.charP
  have hdet : (1 : Matrix (Fin 3) (Fin 3) K).det ≠ 0 := by rw [Matrix.det_one]; exact one_ne_zero
  set D := (StatedScalars (Fin 3) K).subgroupOf (SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K))
    with hD
  have hmodels := odd_unitary_three_exact_coordinate_and_Sylow_models hU hp2 (G₀ := 1)
    (bar_one_apply' hU) hdet D le_rfl
  obtain ⟨⟨P, hP⟩, -, -, ⟨htwoS, -⟩, h3part, -⟩ := hmodels
  obtain ⟨⟨l, hl, hlo⟩, hall⟩ := h3part h3
  obtain ⟨u, v, τ, -, -, -, hvu, huv, hou, hov, hτ2, -, -, -, -, -, hWcard, hinj, hWbar2,
    hWbarcard⟩ := hall P hP l hl hlo
  set W := Subgroup.closure ({u, v, τ} : Set (SUgram hU.bar (1 : Matrix (Fin 3) (Fin 3) K)))
    with hW
  set a := (p ^ 1 + 1).factorization 2 with ha
  have ha2 : 2 ≤ a := two_le_factorization_of_mod_four (by omega) (by omega)
  have hr : ordProj[2] (p ^ 1 - 1) = 2 := ordProj_two_sub_one_of_mod_four_eq_three h3
  have hWG : WreathGenerators a W u v τ :=
    { closure_eq := rfl
      card_eq := by
        rw [hWcard, htwoS, hr]
        ring
      pow_left := by rw [← hou]; exact pow_orderOf_eq_one u
      pow_right := by rw [← hov]; exact pow_orderOf_eq_one v
      sq_swap := hτ2
      comm := huv.eq
      conj := hvu.symm }
  have hAut : IsPGroup 2 (MulAut ↥W) := isPGroup_mulAut_of_wreathGenerators ha2 hWG
  let e : ↥W ≃* ↥(W.map (QuotientGroup.mk' D)) := equivMapOfInjOn (QuotientGroup.mk' D) W hinj
  exact ⟨⟨W.map (QuotientGroup.mk' D), hWbar2, fun {Q} hQ hle =>
    le_antisymm (isMax_of_card hWbarcard Q hQ hle) hle⟩, hAut.of_equiv (MulAut.congr e)⟩

theorem exists_sylow_wreath_of_isPSU {W : Type} [Group W] (hp2 : p ≠ 2) (h3 : p % 4 = 3)
    (hX : IsPSU 3 p 1 W) : ∃ P : Sylow 2 W, IsPGroup 2 (MulAut ↥(P : Subgroup W)) := by
  obtain ⟨K, _, hU, ⟨ψ⟩⟩ := exists_unitary_quotient_equiv hX
  have := hU.finite
  exact exists_sylow_of_mulEquiv ψ (exists_sylow_SUgram_wreath hU hp2 (by rw [pow_one]; exact h3))

end Unitary

end CFSG.Quasithin.H13.L3Eps
