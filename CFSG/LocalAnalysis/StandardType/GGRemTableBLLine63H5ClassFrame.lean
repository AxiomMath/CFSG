module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5ClassPg
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5Torus

public section

namespace CFSG.StandardType.Line63.H5

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical2 CFSG.RankThree.Classical
  CFSG.StandardType.LineU CFSG.Assembly

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def torusFiveGen (ζ : Kˣ) (j : Fin 5) : Fin 6 → Kˣ :=
  (Pi.mulSingle (Fin.castSucc j) ζ : Fin 6 → Kˣ) * (Pi.mulSingle (Fin.last 5) ζ⁻¹ : Fin 6 → Kˣ)

theorem torusFiveGen_apply (ζ : Kˣ) (j : Fin 5) (i : Fin 6) :
    torusFiveGen ζ j i =
      (if i = Fin.castSucc j then ζ else 1) * (if i = Fin.last 5 then ζ⁻¹ else 1) := by
  simp only [torusFiveGen, Pi.mul_apply, Pi.mulSingle_apply]

theorem torusFiveGen_pow {ζ : Kˣ} {k : ℕ} (hζ : ζ ^ k = 1) (j : Fin 5) (i : Fin 6) :
    torusFiveGen ζ j i ^ k = 1 := by
  rw [torusFiveGen_apply, mul_pow]
  split_ifs <;> simp [hζ, inv_pow]

theorem prod_torusFiveGen (ζ : Kˣ) (j : Fin 5) : ∏ i, torusFiveGen ζ j i = 1 := by
  simp only [torusFiveGen, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
  exact mul_inv_cancel ζ

theorem torusFiveGen_self (ζ : Kˣ) (j : Fin 5) : torusFiveGen ζ j (Fin.castSucc j) = ζ := by
  have h : Fin.castSucc j ≠ Fin.last 5 := (Fin.castSucc_lt_last j).ne
  rw [torusFiveGen_apply, if_pos rfl, if_neg h, mul_one]

theorem torusFiveGen_other (ζ : Kˣ) {j j' : Fin 5} (hj : j' ≠ j) :
    torusFiveGen ζ j' (Fin.castSucc j) = 1 := by
  have h : Fin.castSucc j ≠ Fin.last 5 := (Fin.castSucc_lt_last j).ne
  have h' : Fin.castSucc j ≠ Fin.castSucc j' := fun e => hj (Fin.castSucc_injective _ e).symm
  rw [torusFiveGen_apply, if_neg h', if_neg h, mul_one]

theorem exists_torusFive [Finite K] (hKd : UnitaryFieldData 2 n K) (hpq : 3 ∣ 2 ^ n + 1) :
    ∃ T : Subgroup ↥(unitarySU 2 n K 6), CFSG.Open.IsElemAbelian 3 T ∧ Nat.card T = 3 ^ 5 ∧
      ∀ e ∈ T, ∃ t : Fin 6 → Kˣ, (e : GL (Fin 6) K) = diagHom 6 t := by
  classical
  have := Fact.mk Nat.prime_three
  have : NeZero 3 := ⟨by norm_num⟩
  obtain ⟨ζ, hζo, hζq⟩ := exists_orderOf_eq_norm_one hKd Nat.prime_three hpq
  have hζp : ζ ^ 3 = 1 := hζo ▸ pow_orderOf_eq_one ζ
  set c : Fin 5 → Fin 6 → Kˣ := fun j => torusFiveGen ζ j with hc
  have hcp : ∀ j i, c j i ^ 3 = 1 := fun j i => torusFiveGen_pow hζp j i
  have hcprod : ∀ j, ∏ i, c j i = 1 := fun j => prod_torusFiveGen ζ j
  have hcnorm : ∀ j i, c j i ^ (2 ^ n + 1) = 1 := fun j i => torusFiveGen_pow hζq j i
  have hmemH : ∀ a, diagHom 6 (expHom c hcp a) ∈ unitarySU 2 n K 6 := fun a =>
    diagHom_expHom_mem_unitarySU hKd c hcp hcprod hcnorm a
  have hpriv : ∀ j, ∃ i, (∀ j', j' ≠ j → c j' i = 1) ∧ orderOf (c j i) = 3 := by
    intro j
    exact ⟨Fin.castSucc j, fun j' hj' => torusFiveGen_other ζ hj', by
      rw [hc]
      dsimp only
      rw [torusFiveGen_self, hζo]⟩
  have hexpinj := expHom_injective c hcp hpriv
  set φ : Multiplicative (Fin 5 → ZMod 3) →* ↥(unitarySU 2 n K 6) :=
    ((diagHom 6).comp (expHom c hcp)).codRestrict _ hmemH with hφ
  have hφinj : Function.Injective φ := by
    intro a b hab
    have h1 : diagHom 6 (expHom c hcp a) = diagHom 6 (expHom c hcp b) := congrArg Subtype.val hab
    exact hexpinj (diagHom_injective 6 h1)
  have hapow : ∀ a : Multiplicative (Fin 5 → ZMod 3), a ^ 3 = 1 := by
    intro a
    rw [← toAdd_eq_zero, toAdd_pow]
    funext i
    have h3 : (3 : ZMod 3) = 0 := by exact_mod_cast ZMod.natCast_self 3
    simp [Pi.smul_apply, nsmul_eq_mul, h3]
  refine ⟨φ.range, ?_, ?_, ?_⟩
  · exact isElemAbelian_range (fun a b => mul_comm a b) hapow φ
  · rw [Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv.symm,
      Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
      Fintype.card_fin]
  · rintro _ ⟨a, rfl⟩
    exact ⟨expHom c hcp a, rfl⟩

section Frame

variable {G : Type} [Group G]

theorem false_of_frame [Finite K] [Finite G] (hKd : UnitaryFieldData 2 n K)
    (hpq : 3 ∣ 2 ^ n + 1) (φ : ↥(unitarySU 2 n K 6) →* G) (hφ : Function.Injective φ)
    {B : Subgroup G} (hBcard : Nat.card B = 3 ^ 4)
    (hSC : ∀ g ∈ Subgroup.centralizer (B : Set G), g ^ 3 = 1 → g ∈ B)
    (hact : ∀ b ∈ B, ∃ M, ActsAs φ b M) {P : GL (Fin 6) K}
    (hP : P ∈ CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.primeFormUnitary hKd
      (CFSG.RankThree.PartOne.KCUnitaryModel.idGram K 6))
    (hdiag : ∀ b ∈ B, ∀ M, ActsAs φ b M →
      ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag) : False := by
  classical
  obtain ⟨T, hTab, hTcard, hTdiag⟩ := exists_torusFive hKd hpq
  set c := TableBUE.conjSU hKd P hP with hc
  set Φ : ↥T →* G :=
    φ.comp ((c.symm : ↥(unitarySU 2 n K 6) ≃* ↥(unitarySU 2 n K 6)).toMonoidHom.comp
      T.subtype) with hΦ
  have hΦinj : Function.Injective Φ := hφ.comp (c.symm.injective.comp T.subtype_injective)
  have hΦB : ∀ e : T, Φ e ∈ B := by
    intro e
    have hΦe : Φ e = φ (c.symm (e : ↥(unitarySU 2 n K 6))) := rfl
    rw [hΦe]
    apply hSC
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨M, hM⟩ := hact b hb
      have hMd := hdiag b hb M hM
      obtain ⟨hMN, hMact⟩ := hM
      obtain ⟨σ, hσ⟩ := TableBUE.exists_diagHom_of_isDiag hMd
      obtain ⟨t, ht⟩ := hTdiag (e : ↥(unitarySU 2 n K 6)) e.2
      have hcs : conjN M hMN (c.symm (e : ↥(unitarySU 2 n K 6))) =
          c.symm (e : ↥(unitarySU 2 n K 6)) := by
        apply Subtype.ext
        rw [coe_conjN]
        show M * (P * ((e : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) * P⁻¹) * M⁻¹ =
          P * ((e : ↥(unitarySU 2 n K 6)) : GL (Fin 6) K) * P⁻¹
        have hM' : M = P * diagHom 6 σ * P⁻¹ := by rw [← hσ]; group
        have hcomm := (diagHom_commute σ t).eq
        rw [ht, hM']
        calc P * diagHom 6 σ * P⁻¹ * (P * diagHom 6 t * P⁻¹) * (P * diagHom 6 σ * P⁻¹)⁻¹
            = P * (diagHom 6 σ * diagHom 6 t * (diagHom 6 σ)⁻¹) * P⁻¹ := by group
          _ = P * diagHom 6 t * P⁻¹ := by rw [hcomm]; group
      have h1 := hMact (c.symm (e : ↥(unitarySU 2 n K 6)))
      rw [hcs] at h1
      calc b * φ (c.symm (e : ↥(unitarySU 2 n K 6)))
          = b * φ (c.symm (e : ↥(unitarySU 2 n K 6))) * b⁻¹ * b := by group
        _ = φ (c.symm (e : ↥(unitarySU 2 n K 6))) * b := by rw [h1]
    · rw [← map_pow, ← map_pow, hTab.2 (e : ↥(unitarySU 2 n K 6)) e.2, map_one, map_one]
  have hle : Nat.card T ≤ Nat.card B := by
    calc Nat.card T = Nat.card Φ.range := Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv
      _ ≤ Nat.card B := Subgroup.card_le_of_le (by rintro _ ⟨e, rfl⟩; exact hΦB e)
  rw [hTcard, hBcard] at hle
  norm_num at hle

end Frame

end CFSG.StandardType.Line63.H5

end
