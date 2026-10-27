module

public import CFSG.RankThree.PartOne.K159W.WeylPSL
public import CFSG.RankThree.PartOne.K159.CoverPSU

public section

namespace CFSG.RankThree.PartOne.K159W

open scoped commutatorElement
open Matrix CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover CFSG.RankThree.Classical
  CFSG.RankThree.Classical2 CFSG.RankThree.CentralCover CFSG.RankThree.PartOne.K159

section Package

variable {ℓ f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def uDelta (n m : ℕ) {p : ℕ} (E : Multiplicative (Fin m → ZMod p) →* (Fin n → Kˣ))
    (hES : ∀ a, diagHom n (E a) ∈ unitarySU ℓ f K n) :
    Multiplicative (Fin m → ZMod p) →* unitarySU ℓ f K n :=
  ((diagHom n).comp E).codRestrict (unitarySU ℓ f K n) hES

@[expose] noncomputable def uTheta (hK : UnitaryFieldData ℓ f K) (n m : ℕ) {p : ℕ}
    (E : Multiplicative (Fin m → ZMod p) →* (Fin n → Kˣ))
    (hES : ∀ a, diagHom n (E a) ∈ unitarySU ℓ f K n) :
    Multiplicative (Fin m → ZMod p) →* unitaryPSU hK n :=
  (unitaryProj hK n).comp (uDelta n m E hES)

theorem unitary_torus_package {Y : Type*} [Group Y] [Finite Y] (hK : UnitaryFieldData ℓ f K)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 1 ≤ n) (φ : Y →* unitaryPSU hK n)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y) {m : ℕ}
    (E : Multiplicative (Fin m → ZMod p) →* (Fin n → Kˣ))
    (hES : ∀ a, diagHom n (E a) ∈ unitarySU ℓ f K n) (hinj : Function.Injective E)
    (hswap : ∀ j k, j ≠ k → ∃ w ∈ unitarySU ℓ f K n,
      w * diagHom n (E (Multiplicative.ofAdd (Pi.single j 1))) * w⁻¹ =
          diagHom n (E (Multiplicative.ofAdd (Pi.single k 1))) ∧
        w * diagHom n (E (Multiplicative.ofAdd (Pi.single k 1))) * w⁻¹ =
          diagHom n (E (Multiplicative.ofAdd (Pi.single j 1)))) :
    (∀ x ∈ (uTheta hK n m E hES).range, x ^ p = 1) ∧
      (∀ x ∈ (uTheta hK n m E hES).range.comap φ, ∀ y ∈ (uTheta hK n m E hES).range.comap φ,
        x * y = y * x) ∧
      p ^ (m - if p ∣ n then 1 else 0) ≤ Nat.card (uTheta hK n m E hES).range := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite K := hK.finite
  set S := unitarySU ℓ f K n
  let δ : Multiplicative (Fin m → ZMod p) →* S := ((diagHom n).comp E).codRestrict S hES
  have hδ : ∀ a, (δ a : GL (Fin n) K) = diagHom n (E a) := fun a => rfl
  let θ : Multiplicative (Fin m → ZMod p) →* unitaryPSU hK n := (unitaryProj hK n).comp δ
  set D := θ.range with hDdef
  have hθsingle : ∀ j, (δ (Multiplicative.ofAdd (Pi.single j 1)) : GL (Fin n) K) =
      diagHom n (E (Multiplicative.ofAdd (Pi.single j 1))) := fun j => hδ _
  have hpow : ∀ a : Multiplicative (Fin m → ZMod p), a ^ p = 1 := by
    intro a
    change Multiplicative.ofAdd (p • Multiplicative.toAdd a) = 1
    have : p • Multiplicative.toAdd a = 0 := by
      funext i
      simp [nsmul_eq_mul]
    rw [this]
    rfl
  have hDp : ∀ x ∈ D, x ^ p = 1 := by
    rintro _ ⟨a, rfl⟩
    rw [← map_pow, hpow, map_one]
  have hgen : ∀ j k : Fin m, liftComm φ hφ (θ (Multiplicative.ofAdd (Pi.single j 1)))
      (θ (Multiplicative.ofAdd (Pi.single k 1))) = 1 := by
    intro j k
    rcases eq_or_ne j k with rfl | hjk
    · exact liftComm_self hφ _
    obtain ⟨w, hwS, hw1, hw2⟩ := hswap j k hjk
    have hcomm : Commute (θ (Multiplicative.ofAdd (Pi.single j 1)))
        (θ (Multiplicative.ofAdd (Pi.single k 1))) := (Commute.all _ _).map θ
    refine liftComm_eq_one_of_conj_swap hφ hker (hp.odd_of_ne_two hp2) hcomm
      (by rw [← map_pow, hpow, map_one]) (unitaryProj hK n ⟨w, hwS⟩) ?_ ?_
    · change unitaryProj hK n (⟨w, hwS⟩ * δ _ * ⟨w, hwS⟩⁻¹) = unitaryProj hK n (δ _)
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hθsingle, hθsingle, hw1]
    · change unitaryProj hK n (⟨w, hwS⟩ * δ _ * ⟨w, hwS⟩⁻¹) = unitaryProj hK n (δ _)
      congr 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hθsingle, hθsingle, hw2]
  have hall : ∀ s ∈ D, ∀ t ∈ D, liftComm φ hφ s t = 1 := by
    rintro _ ⟨a, rfl⟩ _ ⟨a', rfl⟩
    refine liftComm_eq_one_of_closure hφ hker θ closure_range_single_eq_top ?_ a a'
    rintro _ ⟨j, rfl⟩ _ ⟨k, rfl⟩
    exact hgen j k
  have hF : ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x := fun x hx y hy =>
    mul_comm_of_liftComm_eq_one hφ hker hall hx hy
  have hscalar : ∀ a, θ a = 1 → ∃ c : Kˣ, c ^ n = 1 ∧ c ^ p = 1 ∧
      diagHom n (E a) = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
    intro a ha
    have hmem : δ a ∈ unitaryScalars hK n := by
      rw [← ker_unitaryProj hK n]
      exact ha
    obtain ⟨c, -, hcn, hc⟩ := mem_unitaryScalars.mp hmem
    refine ⟨c, hcn, ?_, by rw [← hδ, hc]⟩
    have h1 : (δ (a ^ p) : GL (Fin n) K) = 1 := by rw [hpow, map_one]; rfl
    rw [map_pow, Subgroup.coe_pow, hc, ← map_pow] at h1
    have h2 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩
      ⟨0, by omega⟩) h1
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Units.val_one, Matrix.one_apply_eq] at h2
    exact Units.ext (by simpa using h2)
  have hkercard : Nat.card θ.ker ≤ p ^ (if p ∣ n then 1 else 0) := by
    split_ifs with hpn
    · rw [pow_one]
      let ev : θ.ker →* Kˣ := ((Pi.evalMonoidHom (fun _ : Fin n => Kˣ) ⟨0, by omega⟩).comp E).comp
        θ.ker.subtype
      have hev : Function.Injective ev := by
        refine (injective_iff_map_eq_one ev).mpr fun x hx => ?_
        obtain ⟨c, -, -, hc⟩ := hscalar x x.2
        have h0 : (c : K) = 1 := by
          have := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩
            ⟨0, by omega⟩) hc
          simp only [coe_diagHom, Matrix.diagonal_apply_eq, Matrix.GeneralLinearGroup.coe_scalar,
            Matrix.scalar_apply] at this
          rw [← this]
          exact congrArg Units.val hx
        have hc1 : c = 1 := Units.ext h0
        have h1 : E x = 1 := by
          apply diagHom_injective n
          rw [hc, hc1, map_one, map_one]
        exact Subtype.ext (hinj (h1.trans (map_one E).symm))
      have hrange : ev.range ≤ rootsOfUnity p K := by
        rintro _ ⟨x, rfl⟩
        have hx : x ^ p = 1 := Subtype.ext (by rw [Subgroup.coe_pow, hpow]; rfl)
        rw [mem_rootsOfUnity, ← map_pow, hx, map_one]
      calc Nat.card θ.ker = Nat.card ev.range :=
            Nat.card_congr (MonoidHom.ofInjective hev).toEquiv
        _ ≤ Nat.card (rootsOfUnity p K) := Subgroup.card_le_of_le hrange
        _ ≤ p := card_rootsOfUnity K p
    · rw [pow_zero]
      have hbot : θ.ker = ⊥ := by
        refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
        obtain ⟨c, hcn, hcp', hc⟩ := hscalar x hx
        have hc1 : c = 1 := by
          have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpn
          have : c ^ Nat.gcd p n = 1 := pow_gcd_eq_one.mpr ⟨hcp', hcn⟩
          rwa [hcop.gcd_eq_one, pow_one] at this
        have h1 : E x = 1 := by
          apply diagHom_injective n
          rw [hc, hc1, map_one, map_one]
        exact hinj (h1.trans (map_one E).symm)
      rw [hbot, Subgroup.card_bot]
  have hDcard : p ^ (m - if p ∣ n then 1 else 0) ≤ Nat.card D := by
    set ε := if p ∣ n then 1 else 0 with hεdef
    by_cases hε : ε ≤ m
    · have h1 : Nat.card θ.ker * Nat.card D = p ^ m := by
        rw [hDdef, ← Subgroup.index_ker, Subgroup.card_mul_index, Nat.card_congr
          Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card,
          Fintype.card_fin]
      have h2 : p ^ m ≤ Nat.card D * p ^ ε := by
        rw [← h1, mul_comm]
        exact Nat.mul_le_mul_left _ hkercard
      have h3 : p ^ m = p ^ (m - ε) * p ^ ε := by
        rw [← pow_add, Nat.sub_add_cancel hε]
      rw [h3] at h2
      exact Nat.le_of_mul_le_mul_right h2 (pow_pos hp.pos _)
    · rw [Nat.sub_eq_zero_of_le (by omega), pow_zero]
      exact Nat.card_pos
  exact ⟨hDp, hF, hDcard⟩

end Package

section Torus

variable {ℓ f : ℕ} {K : Type} [Field K]

@[expose] noncomputable def uE (ζ : Kˣ) (hζ : ζ ^ 5 = 1) :
    Multiplicative (Fin 4 → ZMod 5) →* (Fin 5 → Kˣ) where
  toFun a := torusEntries ζ hζ (Multiplicative.toAdd a)
  map_one' := torusEntries_zero ζ hζ
  map_mul' _ _ := torusEntries_add ζ hζ _ _

theorem uE_apply (ζ : Kˣ) (hζ : ζ ^ 5 = 1) (a : Multiplicative (Fin 4 → ZMod 5)) :
    uE ζ hζ a = torusEntries ζ hζ (Multiplicative.toAdd a) := rfl

theorem uE_mem (hK : UnitaryFieldData ℓ f K) (ζ : Kˣ) (hζ : ζ ^ 5 = 1)
    (hζN : ζ ^ (ℓ ^ f + 1) = 1) (a : Multiplicative (Fin 4 → ZMod 5)) :
    diagHom 5 (uE ζ hζ a) ∈ unitarySU ℓ f K 5 := by
  rw [mem_unitarySU_iff hK]
  refine ⟨?_, diagHom_unitary hK fun i => ?_⟩
  · rw [det_diagHom, ← Units.coe_prod]
    simp only [uE_apply]
    rw [prod_torusEntries, Units.val_one]
  · rw [← Units.val_pow_eq_pow_val, uE_apply]
    simp only [torusEntries, zmodPowHom_apply]
    rw [← pow_mul, mul_comm, pow_mul, hζN, one_pow, Units.val_one]

theorem uE_injective {ζ : Kˣ} (hζo : orderOf ζ = 5) (hζ : ζ ^ 5 = 1) :
    Function.Injective (uE ζ hζ) := by
  refine (injective_iff_map_eq_one _).2 fun a ha => ?_
  apply Multiplicative.toAdd.injective
  funext j
  have h := congrFun ha j.castSucc
  simp only [uE_apply, torusEntries, torusExp_castSucc, Pi.one_apply] at h
  have h2 := zmodPowHom_injective hζo hζ (h.trans (map_one (zmodPowHom ζ hζ)).symm)
  exact Multiplicative.ofAdd.injective h2

theorem torusEntries_neg (ζ : Kˣ) (hζ : ζ ^ 5 = 1) (a : Fin 4 → ZMod 5) :
    torusEntries ζ hζ (-a) = (torusEntries ζ hζ a)⁻¹ := by
  have h := torusEntries_add ζ hζ a (-a)
  rw [add_neg_cancel, torusEntries_zero] at h
  exact eq_inv_of_mul_eq_one_right h.symm

theorem signedSwap_mem (hK : UnitaryFieldData ℓ f K) {a b : Fin 5} (hab : a ≠ b) :
    permGL (Equiv.swap a b) * diagHom 5 (Function.update 1 (Fin.last 4) (-1)) ∈
      unitarySU ℓ f K 5 := by
  have hd₁norm : ∀ i, ((Function.update (1 : Fin 5 → Kˣ) (Fin.last 4) (-1) i : Kˣ) : K) ^
      (ℓ ^ f + 1) = 1 := by
    intro i
    by_cases hi : i = Fin.last 4
    · subst hi
      rw [Function.update_self, Units.val_neg, Units.val_one]
      exact neg_one_pow_norm hK
    · rw [Function.update_of_ne hi, Pi.one_apply, Units.val_one, one_pow]
  rw [mem_unitarySU_iff hK, Units.val_mul]
  refine ⟨?_, unitary_mul hK (permGL_unitary hK _) (diagHom_unitary hK hd₁norm)⟩
  rw [Matrix.det_mul, det_permGL, Equiv.Perm.sign_swap hab, det_diagHom, prod_update_neg_one]
  simp

theorem signedSwap_conj (σ : Equiv.Perm (Fin 5)) (e : Fin 5 → Kˣ) :
    (permGL σ * diagHom 5 (Function.update (1 : Fin 5 → Kˣ) (Fin.last 4) (-1))) * diagHom 5 e *
        (permGL σ * diagHom 5 (Function.update (1 : Fin 5 → Kˣ) (Fin.last 4) (-1)))⁻¹ =
      diagHom 5 (e ∘ σ.symm) := by
  rw [← permGL_mul_diagHom_mul_inv σ e]
  have hcomm := (diagHom_commute (K := K) (Function.update (1 : Fin 5 → Kˣ) (Fin.last 4) (-1))
    e).eq
  calc (permGL σ * diagHom 5 (Function.update (1 : Fin 5 → Kˣ) (Fin.last 4) (-1))) *
        diagHom 5 e *
        (permGL σ * diagHom 5 (Function.update (1 : Fin 5 → Kˣ) (Fin.last 4) (-1)))⁻¹ =
      permGL σ * (diagHom 5 (Function.update (1 : Fin 5 → Kˣ) (Fin.last 4) (-1)) * diagHom 5 e) *
        (diagHom 5 (Function.update (1 : Fin 5 → Kˣ) (Fin.last 4) (-1)))⁻¹ *
          (permGL σ)⁻¹ := by group
    _ = permGL σ * (diagHom 5 e * diagHom 5 (Function.update (1 : Fin 5 → Kˣ) (Fin.last 4) (-1))) *
        (diagHom 5 (Function.update (1 : Fin 5 → Kˣ) (Fin.last 4) (-1)))⁻¹ *
          (permGL σ)⁻¹ := by rw [hcomm]
    _ = permGL σ * diagHom 5 e * (permGL σ)⁻¹ := by group

theorem uE_swap (hK : UnitaryFieldData ℓ f K) (ζ : Kˣ) (hζ : ζ ^ 5 = 1) (j k : Fin 4)
    (hjk : j ≠ k) : ∃ w ∈ unitarySU ℓ f K 5,
      w * diagHom 5 (uE ζ hζ (Multiplicative.ofAdd (Pi.single j 1))) * w⁻¹ =
          diagHom 5 (uE ζ hζ (Multiplicative.ofAdd (Pi.single k 1))) ∧
        w * diagHom 5 (uE ζ hζ (Multiplicative.ofAdd (Pi.single k 1))) * w⁻¹ =
          diagHom 5 (uE ζ hζ (Multiplicative.ofAdd (Pi.single j 1))) := by
  have hne : j.castSucc ≠ k.castSucc := (Fin.castSucc_injective 4).ne hjk
  refine ⟨_, signedSwap_mem hK hne, ?_, ?_⟩
  · rw [signedSwap_conj]
    congr 1
    rw [Equiv.symm_swap]
    funext i
    simp only [uE_apply, toAdd_ofAdd, torusEntries, Function.comp_apply]
    rw [← torusExp_single_comp_swap j k]
    rfl
  · rw [signedSwap_conj]
    congr 1
    rw [Equiv.symm_swap]
    funext i
    simp only [uE_apply, toAdd_ofAdd, torusEntries, Function.comp_apply]
    rw [Equiv.swap_comm, ← torusExp_single_comp_swap k j]
    rfl

theorem uE_inv (hK : UnitaryFieldData ℓ f K) (ζ : Kˣ) (hζ : ζ ^ 5 = 1) (j : Fin 4) :
    ∃ w ∈ unitarySU ℓ f K 5,
      w * diagHom 5 (uE ζ hζ (Multiplicative.ofAdd (Pi.single j 1))) * w⁻¹ =
        (diagHom 5 (uE ζ hζ (Multiplicative.ofAdd (Pi.single j 1))))⁻¹ := by
  have hne : j.castSucc ≠ Fin.last 4 := (Fin.castSucc_lt_last j).ne
  refine ⟨_, signedSwap_mem hK hne, ?_⟩
  rw [signedSwap_conj, ← map_inv]
  congr 1
  rw [Equiv.symm_swap]
  have h2 : torusEntries ζ hζ (Pi.single j (1 : ZMod 5)) ∘ Equiv.swap j.castSucc (Fin.last 4) =
      torusEntries ζ hζ (-Pi.single j (1 : ZMod 5)) := by
    funext i
    simp only [torusEntries, Function.comp_apply]
    rw [← Pi.single_neg, ← torusExp_single_comp_swap_last j]
    rfl
  have h1 := torusEntries_neg ζ hζ (Pi.single j (1 : ZMod 5))
  show torusEntries ζ hζ (Pi.single j (1 : ZMod 5)) ∘ Equiv.swap j.castSucc (Fin.last 4) =
    (torusEntries ζ hζ (Pi.single j (1 : ZMod 5)))⁻¹
  rw [h2, h1]

end Torus

section Weyl

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem permGL_mem_unitarySU (hK : UnitaryFieldData ℓ f K) (σ : Equiv.Perm (Fin 5))
    (hσ : Equiv.Perm.sign σ = 1) : permGL σ ∈ unitarySU ℓ f K 5 := by
  rw [mem_unitarySU_iff hK]
  refine ⟨?_, permGL_unitary hK σ⟩
  rw [det_permGL, hσ]
  simp

@[expose] noncomputable def permU (hK : UnitaryFieldData ℓ f K) (σ : Equiv.Perm (Fin 5))
    (hσ : Equiv.Perm.sign σ = 1) : unitarySU ℓ f K 5 :=
  ⟨permGL σ, permGL_mem_unitarySU hK σ hσ⟩

theorem permU_pow (hK : UnitaryFieldData ℓ f K) (σ : Equiv.Perm (Fin 5))
    (hσ : Equiv.Perm.sign σ = 1) {n : ℕ} (hn : σ ^ n = 1) : (permU hK σ hσ) ^ n = 1 := by
  apply Subtype.ext
  show (permGL σ) ^ n = 1
  rw [← map_pow, hn, map_one]

theorem permU_inv (hK : UnitaryFieldData ℓ f K) (σ : Equiv.Perm (Fin 5))
    (hσ : Equiv.Perm.sign σ = 1) (hσ' : Equiv.Perm.sign σ⁻¹ = 1) :
    (permU hK σ hσ)⁻¹ = permU hK σ⁻¹ hσ' := by
  apply Subtype.ext
  show (permGL σ)⁻¹ = permGL σ⁻¹
  rw [map_inv]

theorem permU_conj_uTheta (hK : UnitaryFieldData ℓ f K) (ζ : Kˣ) (hζ : ζ ^ 5 = 1)
    (hζN : ζ ^ (ℓ ^ f + 1) = 1) (σ : Equiv.Perm (Fin 5)) (hσ : Equiv.Perm.sign σ = 1)
    (a : Multiplicative (Fin 4 → ZMod 5)) :
    unitaryProj hK 5 (permU hK σ hσ) * uTheta hK 5 4 (uE ζ hζ) (uE_mem hK ζ hζ hζN) a *
        (unitaryProj hK 5 (permU hK σ hσ))⁻¹ =
      uTheta hK 5 4 (uE ζ hζ) (uE_mem hK ζ hζ hζN)
        (Multiplicative.ofAdd (conjVec σ (Multiplicative.toAdd a))) := by
  show unitaryProj hK 5 (permU hK σ hσ) *
      unitaryProj hK 5 (uDelta 5 4 (uE ζ hζ) (uE_mem hK ζ hζ hζN) a) *
        (unitaryProj hK 5 (permU hK σ hσ))⁻¹ =
    unitaryProj hK 5 (uDelta 5 4 (uE ζ hζ) (uE_mem hK ζ hζ hζN)
      (Multiplicative.ofAdd (conjVec σ (Multiplicative.toAdd a))))
  rw [← map_inv, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  show permGL σ * diagHom 5 (uE ζ hζ a) * (permGL σ)⁻¹ =
    diagHom 5 (uE ζ hζ (Multiplicative.ofAdd (conjVec σ (Multiplicative.toAdd a))))
  rw [permGL_mul_diagHom_mul_inv, uE_apply, uE_apply, toAdd_ofAdd, torusEntries_comp_perm]

theorem uTheta_ker_exp (hK : UnitaryFieldData ℓ f K) {ζ : Kˣ} (hζo : orderOf ζ = 5)
    (hζ : ζ ^ 5 = 1) (hζN : ζ ^ (ℓ ^ f + 1) = 1) {a : Multiplicative (Fin 4 → ZMod 5)}
    (ha : uTheta hK 5 4 (uE ζ hζ) (uE_mem hK ζ hζ hζN) a = 1) (i i' : Fin 5) :
    torusExp (Multiplicative.toAdd a) i = torusExp (Multiplicative.toAdd a) i' := by
  have hmem : uDelta 5 4 (uE ζ hζ) (uE_mem hK ζ hζ hζN) a ∈ unitaryScalars hK 5 := by
    rw [← ker_unitaryProj hK 5]
    exact ha
  obtain ⟨c, -, -, hc⟩ := mem_unitaryScalars.mp hmem
  have hent : ∀ l, (torusEntries ζ hζ (Multiplicative.toAdd a) l : K) = c := by
    intro l
    have := congrArg (fun g : GL (Fin 5) K => (g : Matrix (Fin 5) (Fin 5) K) l l) hc
    simp only [Matrix.diagonal_apply_eq, Matrix.GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply] at this
    have h4 : ((uDelta 5 4 (uE ζ hζ) (uE_mem hK ζ hζ hζN) a : unitarySU ℓ f K 5) :
        GL (Fin 5) K) = diagHom 5 (uE ζ hζ a) := rfl
    rw [h4, coe_diagHom, Matrix.diagonal_apply_eq] at this
    exact this
  have h1 : torusEntries ζ hζ (Multiplicative.toAdd a) i =
      torusEntries ζ hζ (Multiplicative.toAdd a) i' := Units.ext ((hent i).trans (hent i').symm)
  have h2 := zmodPowHom_injective hζo hζ h1
  exact Multiplicative.ofAdd.injective h2

theorem permU_conj_gen_ne (hK : UnitaryFieldData ℓ f K) {ζ : Kˣ} (hζo : orderOf ζ = 5)
    (hζ : ζ ^ 5 = 1) (hζN : ζ ^ (ℓ ^ f + 1) = 1) {σ : Equiv.Perm (Fin 5)}
    (hσ : Equiv.Perm.sign σ = 1)
    (hne : ¬ ∀ i i' : Fin 5, torusExp (conjVec σ (Pi.single 0 1) - Pi.single 0 1) i =
      torusExp (conjVec σ (Pi.single 0 1) - Pi.single 0 1) i') :
    unitaryProj hK 5 (permU hK σ hσ) *
        uTheta hK 5 4 (uE ζ hζ) (uE_mem hK ζ hζ hζN) (Multiplicative.ofAdd (Pi.single 0 1)) *
          (unitaryProj hK 5 (permU hK σ hσ))⁻¹ ≠
      uTheta hK 5 4 (uE ζ hζ) (uE_mem hK ζ hζ hζN) (Multiplicative.ofAdd (Pi.single 0 1)) := by
  intro h
  rw [permU_conj_uTheta hK ζ hζ hζN σ hσ, toAdd_ofAdd] at h
  apply hne
  intro i i'
  have hker : uTheta hK 5 4 (uE ζ hζ) (uE_mem hK ζ hζ hζN)
      (Multiplicative.ofAdd (conjVec σ (Pi.single 0 1)) *
        (Multiplicative.ofAdd (Pi.single 0 1 : Fin 4 → ZMod 5))⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  have := uTheta_ker_exp hK hζo hζ hζN hker i i'
  simpa [sub_eq_add_neg] using this

theorem weylFive_psu {Y : Type} [Group Y] [Finite Y] (hK : UnitaryFieldData ℓ f K) {ζ : Kˣ}
    (hζo : orderOf ζ = 5) (hζ : ζ ^ 5 = 1) (hζN : ζ ^ (ℓ ^ f + 1) = 1)
    {φ : Y →* unitaryPSU hK 5} (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    (hodd : Odd (Nat.card φ.ker)) {z : Y} (hz : z ∈ φ.ker) (hz1 : z ≠ 1) (hzp : z ^ 5 = 1) :
    WeylFive Y := by
  classical
  have : NeZero 5 := ⟨by norm_num⟩
  obtain ⟨hDp, hF, hDcard⟩ := unitary_torus_package hK Nat.prime_five (by norm_num)
    (by norm_num : 1 ≤ 5) φ hφ hker (uE ζ hζ) (uE_mem hK ζ hζ hζN) (uE_injective hζo hζ)
    (uE_swap hK ζ hζ)
  set θ := uTheta hK 5 4 (uE ζ hζ) (uE_mem hK ζ hζ hζN) with hθ
  set S : Set (unitaryPSU hK 5) :=
    Set.range fun j : Fin 4 => θ (Multiplicative.ofAdd (Pi.single j 1)) with hS
  have hcl : Subgroup.closure S = θ.range := by
    have h1 : (Subgroup.closure (Set.range fun j : Fin 4 =>
        (Multiplicative.ofAdd (Pi.single j (1 : ZMod 5)) :
          Multiplicative (Fin 4 → ZMod 5)))).map θ = Subgroup.closure S := by
      rw [MonoidHom.map_closure, hS, ← Set.range_comp]
      rfl
    rw [← h1, closure_range_ofAdd_single, ← MonoidHom.range_eq_map]
  have hSp : ∀ s ∈ S, s ^ 5 = 1 := fun s hs => hDp s (by
    rw [← hcl]
    exact Subgroup.subset_closure hs)
  have hSinv : ∀ s ∈ S, ∃ g : unitaryPSU hK 5, g * s * g⁻¹ = s⁻¹ := by
    rintro _ ⟨j, rfl⟩
    obtain ⟨w, hw, hwj⟩ := uE_inv hK ζ hζ j
    refine ⟨unitaryProj hK 5 ⟨w, hw⟩, ?_⟩
    show unitaryProj hK 5 ⟨w, hw⟩ *
        unitaryProj hK 5 (uDelta 5 4 (uE ζ hζ) (uE_mem hK ζ hζ hζN)
          (Multiplicative.ofAdd (Pi.single j 1))) * (unitaryProj hK 5 ⟨w, hw⟩)⁻¹ =
      (unitaryProj hK 5 (uDelta 5 4 (uE ζ hζ) (uE_mem hK ζ hζ hζN)
        (Multiplicative.ofAdd (Pi.single j 1))))⁻¹
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact hwj
  have hF' : ∀ x ∈ (Subgroup.closure S).comap φ, ∀ y ∈ (Subgroup.closure S).comap φ,
      x * y = y * x := by
    rw [hcl]
    exact hF
  have hcard : 5 ^ 3 ≤ Nat.card (Subgroup.closure S) := by
    rw [hcl]
    simpa using hDcard
  have hnorm : ∀ (σ : Equiv.Perm (Fin 5)) (hσ : Equiv.Perm.sign σ = 1),
      ∀ d ∈ Subgroup.closure S, unitaryProj hK 5 (permU hK σ hσ) * d *
        (unitaryProj hK 5 (permU hK σ hσ))⁻¹ ∈ Subgroup.closure S := by
    intro σ hσ d hd
    rw [hcl] at hd ⊢
    obtain ⟨a, rfl⟩ := hd
    rw [hθ, permU_conj_uTheta hK ζ hζ hζN σ hσ]
    exact ⟨_, rfl⟩
  have hnorm' : ∀ (σ : Equiv.Perm (Fin 5)) (hσ : Equiv.Perm.sign σ = 1)
      (hσ' : Equiv.Perm.sign σ⁻¹ = 1), ∀ d ∈ Subgroup.closure S,
        (unitaryProj hK 5 (permU hK σ hσ))⁻¹ * d * unitaryProj hK 5 (permU hK σ hσ) ∈
          Subgroup.closure S := by
    intro σ hσ hσ' d hd
    have := hnorm σ⁻¹ hσ' d hd
    rwa [← permU_inv hK σ hσ hσ', map_inv, inv_inv] at this
  have hs₀ : θ (Multiplicative.ofAdd (Pi.single 0 1)) ∈ S := ⟨0, rfl⟩
  have hc3' : Equiv.Perm.sign c3⁻¹ = 1 := by rw [Equiv.Perm.sign_inv, c3_sign]
  have hc5' : Equiv.Perm.sign c5⁻¹ = 1 := by rw [Equiv.Perm.sign_inv, c5_sign]
  refine weylFive_of_cover hφ hker hodd hz hz1 hzp S hSp hSinv hF' hcard
    (w₃ := unitaryProj hK 5 (permU hK c3 c3_sign))
    (hnorm c3 c3_sign) (hnorm' c3 c3_sign hc3')
    (by rw [← map_pow, permU_pow hK c3 c3_sign c3_pow, map_one]) hs₀
    (permU_conj_gen_ne hK hζo hζ hζN c3_sign c3_ne)
    (w₅ := unitaryProj hK 5 (permU hK c5 c5_sign))
    (hnorm c5 c5_sign) (hnorm' c5 c5_sign hc5')
    (by rw [← map_pow, permU_pow hK c5 c5_sign c5_pow, map_one]) hs₀
    (permU_conj_gen_ne hK hζo hζ hζN c5_sign c5_ne)

end Weyl

end CFSG.RankThree.PartOne.K159W
