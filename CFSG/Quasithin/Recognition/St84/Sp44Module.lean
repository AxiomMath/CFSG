module

public import CFSG.Quasithin.Recognition.St84.Sp44Frame
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow
public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisGood

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.RankThree.PartOne.KCRootAxis
open CFSG.QuasithinUnique.Setup.X7b
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
open CFSG.CGT.PushingUpLit.CGT6.TwoThree
open scoped Matrix IsMulCommutative

namespace Sp44

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
variable {G : Type} [Group G] [Finite G]

theorem card_units_of_card_four (hF : Fintype.card F = 4) : Fintype.card Fˣ = 3 := by
  rw [Fintype.card_units, hF]

theorem pow_four_eq_self (hF : Fintype.card F = 4) (x : F) : x ^ 4 = x := by
  have h := FiniteField.pow_card (K := F) x
  rwa [hF] at h

theorem pow_three_eq_one (hF : Fintype.card F = 4) {x : F} (hx : x ≠ 0) : x ^ 3 = 1 := by
  have h := FiniteField.pow_card_sub_one_eq_one (K := F) x hx
  rwa [hF] at h

theorem exists_sq_eq (hF : Fintype.card F = 4) (x : F) : ∃ y : F, y ^ 2 = x := by
  have hinj : Function.Injective (fun y : F => y ^ 2) := by
    intro y z hyz
    have h : (y - z) * (y + z) = 0 := by linear_combination hyz
    rcases mul_eq_zero.mp h with h' | h'
    · exact sub_eq_zero.mp h'
    · have hy : y = -z := by linear_combination h'
      rw [hy, CharTwo.neg_eq]
  exact (Finite.surjective_of_injective hinj) x

theorem one_add_add_sq_eq_zero (hF : Fintype.card F = 4) {μ : Fˣ} (hμ : μ ≠ 1) :
    1 + (μ : F) + (μ : F) ^ 2 = 0 := by
  have h3 : (μ : F) ^ 3 = 1 := pow_three_eq_one hF (Units.ne_zero μ)
  have hprod : ((μ : F) - 1) * ((μ : F) ^ 2 + (μ : F) + 1) = 0 := by linear_combination h3
  have h1 : (μ : F) ≠ 1 := fun h => hμ (Units.ext h)
  have h2 : (μ : F) ^ 2 + (μ : F) + 1 = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (sub_ne_zero.mpr h1)
  linear_combination h2

theorem exists_unit_ne_one (hF : Fintype.card F = 4) : ∃ μ : Fˣ, μ ≠ 1 := by
  have h2 : 1 < Fintype.card Fˣ := by rw [card_units_of_card_four hF]; norm_num
  exact Fintype.exists_ne_of_one_lt_card h2 1

section Main

variable {Q Z K : Subgroup G} {τ : G}

theorem mul_comm_mem_Q (hQe : IsElemAbelian 2 Q) (x y : ↥Q) : x * y = y * x :=
  hQe.1.is_comm.comm x y

theorem mul_self_mem_Q (hQe : IsElemAbelian 2 Q) (x : ↥Q) : x * x = 1 := by
  have h : (x : G) ^ 2 = 1 := hQe.2 x x.2
  rw [pow_two] at h
  exact Subtype.ext h

theorem inv_eq_self_mem_Q (hQe : IsElemAbelian 2 Q) (x : ↥Q) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right (mul_self_mem_Q hQe x)

@[expose] def betaAdd (β : ↥Q →* Multiplicative (Fin 2 → F)) (q : ↥Q) : Fin 2 → F :=
  Multiplicative.toAdd (β q)

theorem betaAdd_mul {β : ↥Q →* Multiplicative (Fin 2 → F)} {x y : ↥Q} :
    betaAdd β (x * y) = betaAdd β x + betaAdd β y := by
  simp [betaAdd]

theorem betaAdd_one {β : ↥Q →* Multiplicative (Fin 2 → F)} : betaAdd β (1 : ↥Q) = 0 := by
  simp [betaAdd]

theorem betaAdd_eq_zero_iff {β : ↥Q →* Multiplicative (Fin 2 → F)}
    (hβk : ∀ q : ↥Q, β q = 1 ↔ (q : G) ∈ Z) (q : ↥Q) :
    betaAdd β q = 0 ↔ (q : G) ∈ Z := by
  simp [betaAdd, hβk q]

theorem betaAdd_conj {β : ↥Q →* Multiplicative (Fin 2 → F)} {α : ↥K ≃* SL₂ F}
    (hβe : ∀ (k : ↥K) (q q' : ↥Q), (q' : G) = k * q * k⁻¹ →
      Multiplicative.toAdd (β q') = (α k : Matrix (Fin 2) (Fin 2) F) *ᵥ
        Multiplicative.toAdd (β q))
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q) (k : ↥K) (q : ↥Q) :
    betaAdd β ⟨k * (q : G) * k⁻¹, hKQ k k.2 q q.2⟩ =
      (α k : Matrix (Fin 2) (Fin 2) F) *ᵥ betaAdd β q :=
  hβe k q _ rfl

theorem mem_Z_of_centralizes_K {β : ↥Q →* Multiplicative (Fin 2 → F)} {α : ↥K ≃* SL₂ F}
    (hβe : ∀ (k : ↥K) (q q' : ↥Q), (q' : G) = k * q * k⁻¹ →
      Multiplicative.toAdd (β q') = (α k : Matrix (Fin 2) (Fin 2) F) *ᵥ
        Multiplicative.toAdd (β q))
    (hβk : ∀ q : ↥Q, β q = 1 ↔ (q : G) ∈ Z)
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q)
    (q : ↥Q) (hq : ∀ k ∈ K, k * (q : G) = (q : G) * k) : (q : G) ∈ Z := by
  have hfix : ∀ M : SL₂ F, (M : Matrix (Fin 2) (Fin 2) F) *ᵥ betaAdd β q = betaAdd β q := by
    intro M
    obtain ⟨k, hk⟩ : ∃ k : ↥K, α k = M := ⟨α.symm M, α.apply_symm_apply M⟩
    have hval : ((k : ↥K) : G) * (q : G) * (k : G)⁻¹ = (q : G) := by
      rw [hq (k : G) k.2]; group
    have h1 := betaAdd_conj hβe hKQ k q
    have h2 : (⟨k * (q : G) * k⁻¹, hKQ k k.2 q q.2⟩ : ↥Q) = q := Subtype.ext hval
    rw [h2, hk] at h1
    exact h1.symm
  have h1 := hfix (CFSG.SL2MinimalFaithful.unipotent (1 : F))
  have h2 := hfix (CFSG.CGT.PushingUpLit.CGT6.TwoThree.lowerUni (1 : F))
  rw [CFSG.CGT.PushingUpLit.CGT6.TwoThree.unipotent_mulVec] at h1
  rw [CFSG.CGT.PushingUpLit.CGT6.TwoThree.lowerUni_mulVec] at h2
  have hb : betaAdd β q 1 = 0 := by
    have := congrFun h1 0
    simpa using this
  have ha : betaAdd β q 0 = 0 := by
    have := congrFun h2 1
    simpa using this
  exact (betaAdd_eq_zero_iff hβk q).mp (by
    ext i
    fin_cases i
    · exact ha
    · exact hb)

@[expose] def tauHom (hτQ : ∀ q ∈ Q, τ * q * τ⁻¹ ∈ Q) : ↥Q →* ↥Q where
  toFun q := ⟨τ * (q : G) * τ⁻¹, hτQ q q.2⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [Subgroup.coe_mul, Subtype.coe_mk]
    group

theorem tau_conj_mem_Z {β : ↥Q →* Multiplicative (Fin 2 → F)} {α : ↥K ≃* SL₂ F}
    (hβe : ∀ (k : ↥K) (q q' : ↥Q), (q' : G) = k * q * k⁻¹ →
      Multiplicative.toAdd (β q') = (α k : Matrix (Fin 2) (Fin 2) F) *ᵥ
        Multiplicative.toAdd (β q))
    (hβk : ∀ q : ↥Q, β q = 1 ↔ (q : G) ∈ Z)
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q)
    (hKZ : ∀ k ∈ K, ∀ z ∈ Z, k * z = z * k)
    (hτQ : ∀ q ∈ Q, τ * q * τ⁻¹ ∈ Q) (hτK : ∀ k ∈ K, τ * k = k * τ)
    (hZQ : Z ≤ Q) {z : G} (hz : z ∈ Z) : τ * z * τ⁻¹ ∈ Z := by
  refine mem_Z_of_centralizes_K hβe hβk hKQ ⟨τ * z * τ⁻¹, hτQ z (hZQ hz)⟩ (fun k hk => ?_)
  have hkτ : k * τ⁻¹ = τ⁻¹ * k := by
    have h := hτK k hk
    calc k * τ⁻¹ = τ⁻¹ * (τ * k) * τ⁻¹ := by group
      _ = τ⁻¹ * (k * τ) * τ⁻¹ := by rw [h]
      _ = τ⁻¹ * k := by group
  have hkτ' : τ * k = k * τ := hτK k hk
  calc k * (τ * z * τ⁻¹) = τ * k * z * τ⁻¹ := by rw [hkτ']; group
    _ = τ * (k * z) * τ⁻¹ := by group
    _ = τ * (z * k) * τ⁻¹ := by rw [hKZ k hk z hz]
    _ = τ * z * (k * τ⁻¹) := by group
    _ = τ * z * (τ⁻¹ * k) := by rw [hkτ]
    _ = (τ * z * τ⁻¹) * k := by group

theorem betaAdd_tauHom_congr {β : ↥Q →* Multiplicative (Fin 2 → F)}
    (hτQ : ∀ q ∈ Q, τ * q * τ⁻¹ ∈ Q)
    (hτZ : ∀ z ∈ Z, τ * z * τ⁻¹ ∈ Z)
    (hβk : ∀ q : ↥Q, β q = 1 ↔ (q : G) ∈ Z)
    {x y : ↥Q} (h : betaAdd β x = betaAdd β y) :
    betaAdd β (tauHom hτQ x) = betaAdd β (tauHom hτQ y) := by
  have hxy : betaAdd β (x * y⁻¹) = 0 := by
    have h1 : betaAdd β (x * y⁻¹) = betaAdd β x + betaAdd β y⁻¹ := betaAdd_mul
    have h2 : betaAdd β y⁻¹ = -betaAdd β y := by simp [betaAdd]
    rw [h1, h2, h, add_neg_cancel]
  have hZ : ((x * y⁻¹ : ↥Q) : G) ∈ Z := (betaAdd_eq_zero_iff hβk _).mp hxy
  have hz : betaAdd β (tauHom hτQ (x * y⁻¹)) = 0 :=
    (betaAdd_eq_zero_iff hβk _).mpr (hτZ _ hZ)
  calc betaAdd β (tauHom hτQ x) = betaAdd β (tauHom hτQ ((x * y⁻¹) * y)) := by
        rw [show (x * y⁻¹) * y = x from by group]
    _ = betaAdd β (tauHom hτQ (x * y⁻¹) * tauHom hτQ y) := by rw [map_mul]
    _ = betaAdd β (tauHom hτQ y) := by rw [betaAdd_mul, hz, zero_add]

noncomputable def betaSec {β : ↥Q →* Multiplicative (Fin 2 → F)}
    (hβs : Function.Surjective β) (v : Fin 2 → F) : ↥Q :=
  Classical.choose (hβs (Multiplicative.ofAdd v))

theorem betaAdd_betaSec {β : ↥Q →* Multiplicative (Fin 2 → F)}
    (hβs : Function.Surjective β) (v : Fin 2 → F) : betaAdd β (betaSec hβs v) = v := by
  have h := Classical.choose_spec (hβs (Multiplicative.ofAdd v))
  simp [betaSec, betaAdd, h]

noncomputable def tauScalarHom {β : ↥Q →* Multiplicative (Fin 2 → F)}
    (hτQ : ∀ q ∈ Q, τ * q * τ⁻¹ ∈ Q) (hτZ : ∀ z ∈ Z, τ * z * τ⁻¹ ∈ Z)
    (hβs : Function.Surjective β) (hβk : ∀ q : ↥Q, β q = 1 ↔ (q : G) ∈ Z) :
    (Fin 2 → F) →+ (Fin 2 → F) where
  toFun v := betaAdd β (tauHom hτQ (betaSec hβs v))
  map_zero' := by
    have hZ : ((betaSec hβs 0 : ↥Q) : G) ∈ Z :=
      (betaAdd_eq_zero_iff hβk _).mp (by rw [betaAdd_betaSec])
    exact (betaAdd_eq_zero_iff hβk _).mpr (hτZ _ hZ)
  map_add' v w := by
    have hsec : betaAdd β (betaSec hβs (v + w)) =
        betaAdd β (betaSec hβs v * betaSec hβs w) := by
      rw [betaAdd_betaSec, betaAdd_mul, betaAdd_betaSec, betaAdd_betaSec]
    exact (betaAdd_tauHom_congr hτQ hτZ hβk hsec).trans (by rw [map_mul, betaAdd_mul])

theorem tauScalarHom_eq {β : ↥Q →* Multiplicative (Fin 2 → F)}
    (hτQ : ∀ q ∈ Q, τ * q * τ⁻¹ ∈ Q) (hτZ : ∀ z ∈ Z, τ * z * τ⁻¹ ∈ Z)
    (hβs : Function.Surjective β) (hβk : ∀ q : ↥Q, β q = 1 ↔ (q : G) ∈ Z) (q : ↥Q) :
    betaAdd β (tauHom hτQ q) = tauScalarHom hτQ hτZ hβs hβk (betaAdd β q) := by
  exact (betaAdd_tauHom_congr hτQ hτZ hβk (betaAdd_betaSec hβs (betaAdd β q))).symm

theorem tauScalarHom_mulVec {β : ↥Q →* Multiplicative (Fin 2 → F)} {α : ↥K ≃* SL₂ F}
    (hβe : ∀ (k : ↥K) (q q' : ↥Q), (q' : G) = k * q * k⁻¹ →
      Multiplicative.toAdd (β q') = (α k : Matrix (Fin 2) (Fin 2) F) *ᵥ
        Multiplicative.toAdd (β q))
    (hβk : ∀ q : ↥Q, β q = 1 ↔ (q : G) ∈ Z)
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q)
    (hτQ : ∀ q ∈ Q, τ * q * τ⁻¹ ∈ Q) (hτZ : ∀ z ∈ Z, τ * z * τ⁻¹ ∈ Z)
    (hτK : ∀ k ∈ K, τ * k = k * τ) (hβs : Function.Surjective β)
    (M : Matrix (Fin 2) (Fin 2) F) (hM : M.det = 1) (v : Fin 2 → F) :
    tauScalarHom hτQ hτZ hβs hβk (M *ᵥ v) =
      M *ᵥ tauScalarHom hτQ hτZ hβs hβk v := by
  set k : ↥K := α.symm ⟨M, hM⟩ with hk
  have hMk : α k = ⟨M, hM⟩ := α.apply_symm_apply ⟨M, hM⟩
  have hMkv : ((α k : SL₂ F) : Matrix (Fin 2) (Fin 2) F) = M := by rw [hMk]
  have hxy : betaAdd β (betaSec hβs (M *ᵥ v)) =
      betaAdd β ⟨k * (betaSec hβs v : G) * k⁻¹, hKQ k k.2 _ (betaSec hβs v).2⟩ := by
    rw [betaAdd_conj hβe hKQ k (betaSec hβs v), betaAdd_betaSec, betaAdd_betaSec, hMkv]
  have hcongr := betaAdd_tauHom_congr hτQ hτZ hβk hxy
  have hconj : tauHom hτQ ⟨k * (betaSec hβs v : G) * k⁻¹,
        hKQ k k.2 _ (betaSec hβs v).2⟩ =
      ⟨k * (tauHom hτQ (betaSec hβs v) : G) * k⁻¹,
        hKQ k k.2 _ (tauHom hτQ (betaSec hβs v)).2⟩ := by
    refine Subtype.ext ?_
    simp only [tauHom, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.coe_mk]
    have hkτ : (↑k⁻¹ : G) * τ⁻¹ = τ⁻¹ * ↑k⁻¹ := by
      rw [Subgroup.coe_inv, ← mul_inv_rev, hτK k k.2, mul_inv_rev]
    calc τ * (k * (betaSec hβs v : G) * k⁻¹) * τ⁻¹
        = (τ * k) * (betaSec hβs v : G) * (k⁻¹ * τ⁻¹) := by group
      _ = (k * τ) * (betaSec hβs v : G) * (τ⁻¹ * k⁻¹) := by rw [hτK k k.2, hkτ]
      _ = k * (τ * (betaSec hβs v : G) * τ⁻¹) * k⁻¹ := by group
  change betaAdd β (tauHom hτQ (betaSec hβs (M *ᵥ v))) =
    M *ᵥ betaAdd β (tauHom hτQ (betaSec hβs v))
  rw [hcongr, hconj, betaAdd_conj hβe hKQ k (tauHom hτQ (betaSec hβs v)), hMkv]

theorem exists_tau_scalar {β : ↥Q →* Multiplicative (Fin 2 → F)} {α : ↥K ≃* SL₂ F}
    (hF : Fintype.card F = 4)
    (hβe : ∀ (k : ↥K) (q q' : ↥Q), (q' : G) = k * q * k⁻¹ →
      Multiplicative.toAdd (β q') = (α k : Matrix (Fin 2) (Fin 2) F) *ᵥ
        Multiplicative.toAdd (β q))
    (hβk : ∀ q : ↥Q, β q = 1 ↔ (q : G) ∈ Z)
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q)
    (hτQ : ∀ q ∈ Q, τ * q * τ⁻¹ ∈ Q) (hτZ : ∀ z ∈ Z, τ * z * τ⁻¹ ∈ Z)
    (hτK : ∀ k ∈ K, τ * k = k * τ) (hβs : Function.Surjective β) :
    ∃ ν : F, ∀ q : ↥Q, betaAdd β (tauHom hτQ q) = ν • betaAdd β q := by
  obtain ⟨ν, hν⟩ := eq_smul_of_commute_sl hF (tauScalarHom hτQ hτZ hβs hβk)
    (fun M v => tauScalarHom_mulVec hβe hβk hKQ hτQ hτZ hτK hβs (M : Matrix (Fin 2) (Fin 2) F)
      M.2 v)
  exact ⟨ν, fun q => by rw [tauScalarHom_eq hτQ hτZ hβs hβk q]; exact hν (betaAdd β q)⟩

theorem tau_scalar_pow_three {β : ↥Q →* Multiplicative (Fin 2 → F)} {ν : F}
    (hτQ : ∀ q ∈ Q, τ * q * τ⁻¹ ∈ Q)
    (hν : ∀ q : ↥Q, betaAdd β (tauHom hτQ q) = ν • betaAdd β q)
    (hβs : Function.Surjective β) (hτ3 : τ ^ 3 = 1) : ν ^ 3 = 1 := by
  set q : ↥Q := betaSec hβs ![1, 0] with hq
  have h3 : tauHom hτQ (tauHom hτQ (tauHom hτQ q)) = q := by
    refine Subtype.ext ?_
    simp only [tauHom, MonoidHom.coe_mk, OneHom.coe_mk, Subtype.coe_mk]
    calc τ * (τ * (τ * (q : G) * τ⁻¹) * τ⁻¹) * τ⁻¹
        = (τ * τ * τ) * (q : G) * (τ * τ * τ)⁻¹ := by group
      _ = (q : G) := by rw [show τ * τ * τ = τ ^ 3 from by rw [pow_three, mul_assoc], hτ3]; group
  have h1 : betaAdd β (tauHom hτQ (tauHom hτQ (tauHom hτQ q))) =
      ν • (ν • (ν • betaAdd β q)) := by
    rw [hν, hν, hν]
  rw [h3, betaAdd_betaSec] at h1
  have h2 : (ν • (ν • (ν • (![1, 0] : Fin 2 → F)))) 0 = ν ^ 3 := by
    simp only [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero, mul_one]
    ring
  rw [← h1] at h2
  simpa using h2.symm

theorem tau_scalar_ne_one (hF : Fintype.card F = 4)
    {β : ↥Q →* Multiplicative (Fin 2 → F)} {ν : F}
    (hτQ : ∀ q ∈ Q, τ * q * τ⁻¹ ∈ Q)
    (hν : ∀ q : ↥Q, betaAdd β (tauHom hτQ q) = ν • betaAdd β q)
    (hQe : IsElemAbelian 2 Q) (hZQ : Z ≤ Q) (hZc : Nat.card Z = 4)
    (hβk : ∀ q : ↥Q, β q = 1 ↔ (q : G) ∈ Z) (hβs : Function.Surjective β)
    (hτff : ∀ q ∈ Q, τ * q * τ⁻¹ = q → q = 1) :
    ν ≠ 1 := by
  intro hν1
  have hcardQ : Nat.card ↥Q = 64 := by
    have hker : β.ker = Z.subgroupOf Q := by
      ext q
      rw [MonoidHom.mem_ker]
      exact hβk q
    have h1 : Nat.card (Z.subgroupOf Q) = 4 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZQ).toEquiv, hZc]
    have h2 : Nat.card β.range = 16 := by
      rw [MonoidHom.range_eq_top.mpr hβs, Subgroup.card_top]
      simp [Nat.card_eq_fintype_card, hF]
    have h3 := Subgroup.card_ker_mul_card_range β
    rw [hker, h1, h2] at h3
    omega
  have hφmem : ∀ q : ↥Q, τ * (q : G) * τ⁻¹ * (q : G)⁻¹ ∈ Z := by
    intro q
    have h1 : betaAdd β (tauHom hτQ q * q⁻¹) = 0 := by
      rw [betaAdd_mul, hν, show betaAdd β q⁻¹ = -betaAdd β q from by simp [betaAdd],
        hν1, one_smul, add_neg_cancel]
    exact (betaAdd_eq_zero_iff hβk _).mp h1
  let φ : ↥Q → ↥Z := fun q => ⟨τ * (q : G) * τ⁻¹ * (q : G)⁻¹, hφmem q⟩
  have hφinj : Function.Injective φ := by
    intro q q' h
    haveI : IsMulCommutative ↥Q := hQe.1
    have h1 : (tauHom hτQ q * q⁻¹ : ↥Q) = tauHom hτQ q' * q'⁻¹ := by
      refine Subtype.ext ?_
      show τ * (q : G) * τ⁻¹ * (q : G)⁻¹ = τ * (q' : G) * τ⁻¹ * (q' : G)⁻¹
      simpa [φ] using congrArg Subtype.val h
    have h2 : tauHom hτQ (q * q'⁻¹) = q * q'⁻¹ := by
      rw [map_mul, map_inv]
      have h1' : tauHom hτQ q = tauHom hτQ q' * q'⁻¹ * q := by
        rw [show tauHom hτQ q = (tauHom hτQ q * q⁻¹) * q from by group, h1]
      rw [h1', show tauHom hτQ q' * q'⁻¹ * q * (tauHom hτQ q')⁻¹ =
        (tauHom hτQ q' * (tauHom hτQ q')⁻¹) * (q'⁻¹ * q) from by ac_rfl,
        mul_inv_cancel, one_mul]
      ac_rfl
    have h3 : ((q * q'⁻¹ : ↥Q) : G) = 1 := by
      refine hτff _ (q * q'⁻¹).2 ?_
      simpa only [tauHom, MonoidHom.coe_mk, OneHom.coe_mk] using congrArg Subtype.val h2
    calc q = q * q'⁻¹ * q' := by group
      _ = 1 * q' := by rw [show q * q'⁻¹ = 1 from Subtype.ext h3]
      _ = q' := by simp
  have hle := Nat.card_le_card_of_injective φ hφinj
  rw [hcardQ, hZc] at hle
  omega

noncomputable def xElt (α : ↥K ≃* SL₂ F) (t : F) : ↥K :=
  α.symm (CFSG.SL2MinimalFaithful.unipotent t)

@[expose] def Cplus (α : ↥K ≃* SL₂ F) (Q : Subgroup G) : Subgroup G :=
  Q ⊓ Subgroup.centralizer (Set.range fun t : F => ((xElt α t : ↥K) : G))

theorem Cplus_le_Q (α : ↥K ≃* SL₂ F) : Cplus α Q ≤ Q := inf_le_left

theorem mem_Cplus_iff {α : ↥K ≃* SL₂ F} {c : G} :
    c ∈ Cplus α Q ↔
      c ∈ Q ∧ ∀ t : F, ((xElt α t : ↥K) : G) * c = c * ((xElt α t : ↥K) : G) := by
  simp only [Cplus, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · rintro ⟨hQ, hc⟩
    refine ⟨hQ, fun t => ?_⟩
    exact hc ((xElt α t : ↥K) : G) ⟨t, rfl⟩
  · rintro ⟨hQ, hc⟩
    refine ⟨hQ, ?_⟩
    rintro _ ⟨t, rfl⟩
    exact hc t

theorem Z_le_Cplus {α : ↥K ≃* SL₂ F}
    (hKZ : ∀ k ∈ K, ∀ z ∈ Z, k * z = z * k) (hZQ : Z ≤ Q) :
    Z ≤ Cplus α Q := by
  intro z hz
  rw [mem_Cplus_iff]
  exact ⟨hZQ hz, fun t => hKZ _ (xElt α t).2 z hz⟩

theorem Cplus_beta_one {β : ↥Q →* Multiplicative (Fin 2 → F)} {α : ↥K ≃* SL₂ F}
    (hβe : ∀ (k : ↥K) (q q' : ↥Q), (q' : G) = k * q * k⁻¹ →
      Multiplicative.toAdd (β q') = (α k : Matrix (Fin 2) (Fin 2) F) *ᵥ
        Multiplicative.toAdd (β q))
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q)
    {c : ↥Q} (hc : (c : G) ∈ Cplus α Q) : betaAdd β c 1 = 0 := by
  obtain ⟨-, hcomm⟩ := mem_Cplus_iff.mp hc
  have h1 := betaAdd_conj hβe hKQ (xElt α 1) c
  have hα1 : α (xElt α 1) = CFSG.SL2MinimalFaithful.unipotent 1 :=
    α.apply_symm_apply _
  have h2 : (⟨((xElt α 1 : ↥K) : G) * (c : G) * (((xElt α 1)⁻¹ : ↥K) : G),
      hKQ _ (xElt α 1).2 c c.2⟩ : ↥Q) = c := by
    refine Subtype.ext ?_
    show ((xElt α 1 : ↥K) : G) * (c : G) * (((xElt α 1)⁻¹ : ↥K) : G) = (c : G)
    rw [Subgroup.coe_inv, hcomm 1]
    group
  rw [h2, hα1, CFSG.CGT.PushingUpLit.CGT6.TwoThree.unipotent_mulVec] at h1
  have h3 : betaAdd β c 0 = betaAdd β c 0 + betaAdd β c 1 := by
    simpa using congrFun h1 0
  exact add_left_cancel (by rw [add_zero]; exact h3.symm)

theorem Cplus_beta_eq {β : ↥Q →* Multiplicative (Fin 2 → F)} {α : ↥K ≃* SL₂ F}
    (hβe : ∀ (k : ↥K) (q q' : ↥Q), (q' : G) = k * q * k⁻¹ →
      Multiplicative.toAdd (β q') = (α k : Matrix (Fin 2) (Fin 2) F) *ᵥ
        Multiplicative.toAdd (β q))
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q)
    {c : ↥Q} (hc : (c : G) ∈ Cplus α Q) : betaAdd β c = ![betaAdd β c 0, 0] := by
  ext i
  fin_cases i
  · simp
  · simpa using Cplus_beta_one hβe hKQ hc

noncomputable def psiC (α : ↥K ≃* SL₂ F) (β : ↥Q →* Multiplicative (Fin 2 → F)) :
    ↥(Cplus α Q) →* Multiplicative F where
  toFun c := Multiplicative.ofAdd (betaAdd β ⟨(c : G), Cplus_le_Q α c.2⟩ 0)
  map_one' := by
    apply Multiplicative.toAdd.injective
    show (betaAdd β (1 : ↥Q)) 0 = 0
    rw [betaAdd_one]
    rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    show (betaAdd β ((⟨(x : G), Cplus_le_Q α x.2⟩ : ↥Q) *
      ⟨(y : G), Cplus_le_Q α y.2⟩)) 0 =
      (betaAdd β ⟨(x : G), Cplus_le_Q α x.2⟩) 0 + (betaAdd β ⟨(y : G), Cplus_le_Q α y.2⟩) 0
    rw [betaAdd_mul]
    rfl

theorem psiC_ker {β : ↥Q →* Multiplicative (Fin 2 → F)} {α : ↥K ≃* SL₂ F}
    (hβe : ∀ (k : ↥K) (q q' : ↥Q), (q' : G) = k * q * k⁻¹ →
      Multiplicative.toAdd (β q') = (α k : Matrix (Fin 2) (Fin 2) F) *ᵥ
        Multiplicative.toAdd (β q))
    (hβk : ∀ q : ↥Q, β q = 1 ↔ (q : G) ∈ Z)
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q) :
    (psiC α β).ker = Z.subgroupOf (Cplus α Q) := by
  ext c
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hb := Cplus_beta_eq (α := α) (β := β) (c := ⟨(c : G), Cplus_le_Q α c.2⟩) hβe hKQ c.2
  constructor
  · intro h
    have h0 : betaAdd β ⟨((c : G)), Cplus_le_Q α c.2⟩ 0 = 0 := by
      have := congrArg Multiplicative.toAdd h
      simpa [psiC] using this
    have hzero : betaAdd β ⟨((c : G)), Cplus_le_Q α c.2⟩ = 0 := by
      rw [hb, h0]
      ext i
      fin_cases i <;> rfl
    exact (betaAdd_eq_zero_iff hβk _).mp hzero
  · intro h
    have h0 : betaAdd β ⟨((c : G)), Cplus_le_Q α c.2⟩ = 0 :=
      (betaAdd_eq_zero_iff hβk _).mpr h
    rw [hb] at h0
    apply Multiplicative.toAdd.injective
    have h1 : betaAdd β ⟨((c : G)), Cplus_le_Q α c.2⟩ 0 = 0 := by
      simpa using congrFun h0 0
    simpa [psiC] using h1

theorem card_Cplus (hF : Fintype.card F = 4)
    {β : ↥Q →* Multiplicative (Fin 2 → F)} {α : ↥K ≃* SL₂ F}
    (hβe : ∀ (k : ↥K) (q q' : ↥Q), (q' : G) = k * q * k⁻¹ →
      Multiplicative.toAdd (β q') = (α k : Matrix (Fin 2) (Fin 2) F) *ᵥ
        Multiplicative.toAdd (β q))
    (hβk : ∀ q : ↥Q, β q = 1 ↔ (q : G) ∈ Z)
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q)
    (hKZ : ∀ k ∈ K, ∀ z ∈ Z, k * z = z * k) (hZQ : Z ≤ Q) (hZc : Nat.card Z = 4)
    (hT : 16 ≤ Nat.card ↥(Cplus α Q)) : Nat.card ↥(Cplus α Q) = 16 := by
  have h1 := Subgroup.card_ker_mul_card_range (psiC α β)
  have hker : Nat.card (psiC α β).ker = 4 := by
    rw [psiC_ker hβe hβk hKQ]
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Z_le_Cplus hKZ hZQ)).toEquiv, hZc]
  have hrange : Nat.card (psiC α β).range ≤ 4 := by
    have hle : Nat.card (psiC α β).range ≤ Nat.card (Multiplicative F) :=
      Nat.card_le_card_of_injective (fun x => (x : Multiplicative F)) Subtype.coe_injective
    rwa [show Nat.card (Multiplicative F) = 4 by simp [Nat.card_eq_fintype_card, hF]] at hle
  rw [hker] at h1
  have hge : 4 ≤ Nat.card (psiC α β).range := by omega
  have := le_antisymm hrange hge
  omega

theorem exists_Cplus_beta (hF : Fintype.card F = 4)
    {β : ↥Q →* Multiplicative (Fin 2 → F)} {α : ↥K ≃* SL₂ F}
    (hβe : ∀ (k : ↥K) (q q' : ↥Q), (q' : G) = k * q * k⁻¹ →
      Multiplicative.toAdd (β q') = (α k : Matrix (Fin 2) (Fin 2) F) *ᵥ
        Multiplicative.toAdd (β q))
    (hβk : ∀ q : ↥Q, β q = 1 ↔ (q : G) ∈ Z)
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q)
    (hKZ : ∀ k ∈ K, ∀ z ∈ Z, k * z = z * k) (hZQ : Z ≤ Q) (hZc : Nat.card Z = 4)
    (hT : 16 ≤ Nat.card ↥(Cplus α Q)) (a : F) :
    ∃ c : ↥Q, (c : G) ∈ Cplus α Q ∧ betaAdd β c = ![a, 0] := by
  have hcard := card_Cplus hF hβe hβk hKQ hKZ hZQ hZc hT
  have htop : (psiC α β).range = ⊤ := by
    refine Subgroup.eq_top_of_card_eq (H := (psiC α β).range) ?_
    have h1 := Subgroup.card_ker_mul_card_range (psiC α β)
    have hker : Nat.card (psiC α β).ker = 4 := by
      rw [psiC_ker hβe hβk hKQ]
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Z_le_Cplus hKZ hZQ)).toEquiv, hZc]
    rw [hker] at h1
    have h4 : Nat.card (psiC α β).range = 4 := by omega
    rw [h4]
    simp [Nat.card_eq_fintype_card, hF]
  have hmem : Multiplicative.ofAdd a ∈ (psiC α β).range := by rw [htop]; trivial
  obtain ⟨c, hc⟩ := hmem
  have h0 : betaAdd β ⟨(c : G), Cplus_le_Q α c.2⟩ 0 = a := by
    have := congrArg Multiplicative.toAdd hc
    simpa [psiC] using this
  exact ⟨⟨(c : G), Cplus_le_Q α c.2⟩, c.2, by
    rw [Cplus_beta_eq (α := α) (β := β) (c := ⟨(c : G), Cplus_le_Q α c.2⟩) hβe hKQ c.2, h0]⟩

noncomputable def mu0 (hF : Fintype.card F = 4) : Fˣ := Classical.choose (exists_unit_ne_one hF)

theorem mu0_ne_one (hF : Fintype.card F = 4) : mu0 hF ≠ 1 :=
  Classical.choose_spec (exists_unit_ne_one hF)

theorem mu0_val_ne_zero (hF : Fintype.card F = 4) : ((mu0 hF : Fˣ) : F) ≠ 0 :=
  Units.ne_zero _

theorem one_add_mu0_add_mu0_sq (hF : Fintype.card F = 4) :
    1 + ((mu0 hF : Fˣ) : F) + ((mu0 hF : Fˣ) : F) ^ 2 = 0 :=
  one_add_add_sq_eq_zero hF (mu0_ne_one hF)

noncomputable def hElt (α : ↥K ≃* SL₂ F) (hF : Fintype.card F = 4) : ↥K :=
  α.symm (diagSL (mu0 hF))

@[expose] def conjHom (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q) (k : ↥K) : ↥Q →* ↥Q where
  toFun q := ⟨(k : G) * (q : G) * (k : G)⁻¹, hKQ k k.2 q q.2⟩
  map_one' := by ext; simp
  map_mul' x y := by
    ext
    simp only [Subgroup.coe_mul, Subtype.coe_mk]
    group

noncomputable def normHom (hQe : IsElemAbelian 2 Q)
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q) (k : ↥K) : ↥Q →* ↥Q where
  toFun q := q * conjHom hKQ k q * conjHom hKQ (k ^ 2) q
  map_one' := by simp
  map_mul' x y := by
    haveI : IsMulCommutative ↥Q := hQe.1
    simp only [map_mul]
    ac_rfl

@[expose] noncomputable def Q1 (hQe : IsElemAbelian 2 Q)
    (hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q) (α : ↥K ≃* SL₂ F)
    (hF : Fintype.card F = 4) : Subgroup ↥Q :=
  (Cplus α Q).subgroupOf Q ⊓ (normHom hQe hKQ (hElt α hF)).ker

structure ModHyp (Q Z K : Subgroup G) (τ : G)
    (α : ↥K ≃* SL₂ F) (β : ↥Q →* Multiplicative (Fin 2 → F)) : Prop where
  elem : IsElemAbelian 2 Q
  le_Z : Z ≤ Q
  card_Z : Nat.card Z = 4
  norm_Q : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q
  cent_Z : ∀ k ∈ K, ∀ z ∈ Z, k * z = z * k
  surj : Function.Surjective β
  ker : ∀ q : ↥Q, β q = 1 ↔ (q : G) ∈ Z
  equiv : ∀ (k : ↥K) (q q' : ↥Q), (q' : G) = k * q * k⁻¹ →
    Multiplicative.toAdd (β q') = (α k : Matrix (Fin 2) (Fin 2) F) *ᵥ
      Multiplicative.toAdd (β q)
  indec : ∀ W : Subgroup G, W ≤ Q → (∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W) → W ⊔ Z = Q → W = Q
  cardT : 16 ≤ Nat.card ↥(Cplus α Q)
  tau_Q : ∀ q ∈ Q, τ * q * τ⁻¹ ∈ Q
  tau_K : ∀ k ∈ K, τ * k = k * τ
  tau_three : τ ^ 3 = 1
  tau_ff : ∀ q ∈ Q, τ * q * τ⁻¹ = q → q = 1

theorem units_inv_eq_sq (hF : Fintype.card F = 4) (l : Fˣ) :
    ((l⁻¹ : Fˣ) : F) = (l : F) ^ 2 := by
  have h3 : l ^ 3 = 1 := by
    have h := pow_card_eq_one (x := l)
    rwa [card_units_of_card_four hF] at h
  have h2 : l ^ 2 = l⁻¹ := by
    have h : l ^ 2 * l = 1 := by rw [← pow_succ, show 2 + 1 = 3 from rfl, h3]
    exact eq_inv_of_mul_eq_one_left h
  rw [← h2]
  simp

theorem units_mul_self_inv_val (hF : Fintype.card F = 4) (l : Fˣ) :
    (((l * l)⁻¹ : Fˣ) : F) = (l : F) := by
  rw [units_inv_eq_sq hF]
  have h : ((l * l : Fˣ) : F) = (l : F) ^ 2 := by
    push_cast
    ring
  rw [h]
  calc ((l : F) ^ 2) ^ 2 = (l : F) ^ 4 := by ring
    _ = (l : F) := pow_four_eq_self hF _

theorem diagSL_mulVec_four (hF : Fintype.card F = 4) (l : Fˣ) (v : Fin 2 → F) :
    ((diagSL l : SL₂ F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v =
      ![(l : F) * v 0, (l : F) ^ 2 * v 1] := by
  rw [CFSG.CGT.PushingUpLit.CGT6.TwoThree.diagSL_mulVec, units_inv_eq_sq hF]

theorem diagSL_mul_self_mulVec_four (hF : Fintype.card F = 4) (l : Fˣ) (v : Fin 2 → F) :
    ((diagSL (l * l) : SL₂ F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v =
      ![(l : F) ^ 2 * v 0, (l : F) * v 1] := by
  rw [CFSG.CGT.PushingUpLit.CGT6.TwoThree.diagSL_mulVec, units_mul_self_inv_val hF]
  have h : ((l * l : Fˣ) : F) = (l : F) ^ 2 := by
    push_cast
    ring
  rw [h]

theorem alpha_hElt (α : ↥K ≃* SL₂ F) (hF : Fintype.card F = 4) :
    α (hElt α hF) = diagSL (mu0 hF) :=
  α.apply_symm_apply _

theorem alpha_hElt_sq (α : ↥K ≃* SL₂ F) (hF : Fintype.card F = 4) :
    α ((hElt α hF) ^ 2) = diagSL (mu0 hF * mu0 hF) := by
  rw [map_pow, alpha_hElt, pow_two, diagSL_mul]

namespace ModHyp

variable {α : ↥K ≃* SL₂ F} {β : ↥Q →* Multiplicative (Fin 2 → F)}
variable (D : ModHyp Q Z K τ α β)

theorem betaAdd_conj_hElt (hF : Fintype.card F = 4) (q : ↥Q) :
    betaAdd β (conjHom D.norm_Q (hElt α hF) q) =
      ![((mu0 hF : Fˣ) : F) * betaAdd β q 0, ((mu0 hF : Fˣ) : F) ^ 2 * betaAdd β q 1] := by
  have h := betaAdd_conj D.equiv D.norm_Q (hElt α hF) q
  simp only [conjHom, MonoidHom.coe_mk, OneHom.coe_mk] at h ⊢
  rw [alpha_hElt α hF, diagSL_mulVec_four hF] at h
  exact h

theorem betaAdd_conj_hElt_sq (hF : Fintype.card F = 4) (q : ↥Q) :
    betaAdd β (conjHom D.norm_Q ((hElt α hF) ^ 2) q) =
      ![((mu0 hF : Fˣ) : F) ^ 2 * betaAdd β q 0, ((mu0 hF : Fˣ) : F) * betaAdd β q 1] := by
  have h := betaAdd_conj D.equiv D.norm_Q ((hElt α hF) ^ 2) q
  simp only [conjHom, MonoidHom.coe_mk, OneHom.coe_mk] at h ⊢
  rw [alpha_hElt_sq α hF, diagSL_mul_self_mulVec_four hF] at h
  exact h

theorem betaAdd_normHom_zero (hF : Fintype.card F = 4) (q : ↥Q) :
    betaAdd β (normHom D.elem D.norm_Q (hElt α hF) q) = 0 := by
  have hμ := one_add_mu0_add_mu0_sq hF
  have h1 := betaAdd_conj_hElt D hF q
  have h2 := betaAdd_conj_hElt_sq D hF q
  rw [show normHom D.elem D.norm_Q (hElt α hF) q =
    q * conjHom D.norm_Q (hElt α hF) q *
      conjHom D.norm_Q ((hElt α hF) ^ 2) q from rfl]
  rw [betaAdd_mul, betaAdd_mul, h1, h2]
  have h0 : betaAdd β q 0 + (mu0 hF : F) * betaAdd β q 0 +
      (mu0 hF : F) ^ 2 * betaAdd β q 0 = 0 := by
    linear_combination betaAdd β q 0 * hμ
  have h1 : betaAdd β q 1 + (mu0 hF : F) ^ 2 * betaAdd β q 1 +
      (mu0 hF : F) * betaAdd β q 1 = 0 := by
    linear_combination betaAdd β q 1 * hμ
  ext i
  fin_cases i
  · simpa [Matrix.vecHead, Matrix.vecTail] using h0
  · simpa [Matrix.vecHead, Matrix.vecTail] using h1

theorem weylSL_mulVec (v : Fin 2 → F) :
    ((weylSL : SL₂ F) : Matrix (Fin 2) (Fin 2) F) *ᵥ v = ![v 1, v 0] := by
  rw [coe_weylSL]
  ext i
  fin_cases i <;>
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, CharTwo.neg_eq]

theorem weylSL_mul_self : weylSL * weylSL = (1 : SL₂ F) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weylSL, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

theorem weylSL_mul_unipotent (t : F) :
    weylSL * CFSG.SL2MinimalFaithful.unipotent t * weylSL⁻¹ = lowerUni t := by
  have h := weylSL_conj_lowerUni (K := F) t
  rw [show (-t : F) = t from CharTwo.neg_eq t] at h
  calc weylSL * CFSG.SL2MinimalFaithful.unipotent t * weylSL⁻¹
      = weylSL * (weylSL⁻¹ * lowerUni t * weylSL) * weylSL⁻¹ := by rw [h]
    _ = lowerUni t := by group

theorem weylSL_mul_diagSL (l : Fˣ) :
    weylSL * diagSL l * weylSL⁻¹ = diagSL l⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_weylSL, coe_diagSL, Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

end ModHyp

namespace ModHyp

variable {α : ↥K ≃* SL₂ F} {β : ↥Q →* Multiplicative (Fin 2 → F)}
variable (D : ModHyp Q Z K τ α β)

theorem conjHom_eq_self_of_mem_Z (hF : Fintype.card F = 4) {z : ↥Q}
    (hz : (z : G) ∈ Z) (k : ↥K) : conjHom D.norm_Q k z = z := by
  refine Subtype.ext ?_
  show (k : G) * (z : G) * (k : G)⁻¹ = (z : G)
  rw [D.cent_Z k k.2 (z : G) hz]
  group

theorem normHom_eq_self_of_mem_Z (hF : Fintype.card F = 4) {z : ↥Q}
    (hz : (z : G) ∈ Z) : normHom D.elem D.norm_Q (hElt α hF) z = z := by
  rw [show normHom D.elem D.norm_Q (hElt α hF) z =
    z * conjHom D.norm_Q (hElt α hF) z * conjHom D.norm_Q ((hElt α hF) ^ 2) z from rfl,
    conjHom_eq_self_of_mem_Z D hF hz, conjHom_eq_self_of_mem_Z D hF hz]
  rw [mul_self_mem_Q D.elem z, one_mul]

theorem Q1_inf_Z (hF : Fintype.card F = 4) :
    Q1 D.elem D.norm_Q α hF ⊓ Z.subgroupOf Q = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro q hq
  rw [Subgroup.mem_bot]
  obtain ⟨hq1, hqZ⟩ := Subgroup.mem_inf.mp hq
  have hz : ((q : ↥Q) : G) ∈ Z := Subgroup.mem_subgroupOf.mp hqZ
  have hker : normHom D.elem D.norm_Q (hElt α hF) q = 1 := MonoidHom.mem_ker.mp hq1.2
  rw [normHom_eq_self_of_mem_Z D hF hz] at hker
  exact hker

theorem Q1_beta_surj (hF : Fintype.card F = 4) (a : F) :
    ∃ q ∈ Q1 D.elem D.norm_Q α hF, betaAdd β q = ![a, 0] := by
  obtain ⟨c, hcC, hcβ⟩ :=
    exists_Cplus_beta hF D.equiv D.ker D.norm_Q D.cent_Z D.le_Z D.card_Z D.cardT a
  have hN : ((normHom D.elem D.norm_Q (hElt α hF) c : ↥Q) : G) ∈ Z :=
    (betaAdd_eq_zero_iff D.ker _).mp (betaAdd_normHom_zero D hF c)
  refine ⟨c * normHom D.elem D.norm_Q (hElt α hF) c, ?_, ?_⟩
  · refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mul_mem _ hcC (Z_le_Cplus D.cent_Z D.le_Z hN)
    · rw [MonoidHom.mem_ker, map_mul,
        normHom_eq_self_of_mem_Z D hF hN, mul_self_mem_Q D.elem]
  · rw [betaAdd_mul, hcβ, betaAdd_normHom_zero D hF]
    ext i
    fin_cases i <;> simp

noncomputable def q1 (hF : Fintype.card F = 4) (a : F) : ↥Q :=
  Classical.choose (Q1_beta_surj D hF a)

theorem q1_mem (hF : Fintype.card F = 4) (a : F) :
    q1 D hF a ∈ Q1 D.elem D.norm_Q α hF :=
  (Classical.choose_spec (Q1_beta_surj D hF a)).1

theorem q1_beta (hF : Fintype.card F = 4) (a : F) :
    betaAdd β (q1 D hF a) = ![a, 0] :=
  (Classical.choose_spec (Q1_beta_surj D hF a)).2

theorem q1_mem_Cplus (hF : Fintype.card F = 4) (a : F) :
    ((q1 D hF a : ↥Q) : G) ∈ Cplus α Q :=
  Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp (q1_mem D hF a)).1

theorem q1_unique (hF : Fintype.card F = 4) {a : F} {q : ↥Q}
    (hq : q ∈ Q1 D.elem D.norm_Q α hF) (h : betaAdd β q = ![a, 0]) : q = q1 D hF a := by
  have hmem : q * (q1 D hF a)⁻¹ ∈ Q1 D.elem D.norm_Q α hF ⊓ Z.subgroupOf Q := by
    refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ hq (Subgroup.inv_mem _ (q1_mem D hF a)), ?_⟩
    rw [Subgroup.mem_subgroupOf]
    refine (betaAdd_eq_zero_iff D.ker _).mp ?_
    rw [betaAdd_mul, h, show betaAdd β (q1 D hF a)⁻¹ = -betaAdd β (q1 D hF a) from by
      simp [betaAdd], q1_beta]
    ext i
    fin_cases i <;> simp
  rw [Q1_inf_Z D hF, Subgroup.mem_bot] at hmem
  calc q = q * (q1 D hF a)⁻¹ * q1 D hF a := by group
    _ = q1 D hF a := by rw [hmem]; simp

theorem q1_add (hF : Fintype.card F = 4) (a b : F) :
    q1 D hF (a + b) = q1 D hF a * q1 D hF b := by
  refine (q1_unique D hF ?_ ?_).symm
  · exact Subgroup.mul_mem _ (q1_mem D hF a) (q1_mem D hF b)
  · rw [betaAdd_mul, q1_beta, q1_beta]
    ext i
    fin_cases i <;> simp

theorem q1_zero (hF : Fintype.card F = 4) : q1 D hF 0 = 1 := by
  refine (q1_unique D hF (Subgroup.one_mem _) ?_).symm
  rw [betaAdd_one]
  ext i
  fin_cases i <;> rfl

theorem conjHom_x_q1 (hF : Fintype.card F = 4) (t a : F) :
    conjHom D.norm_Q (xElt α t) (q1 D hF a) = q1 D hF a := by
  refine Subtype.ext ?_
  show ((xElt α t : ↥K) : G) * (q1 D hF a : G) * ((xElt α t : ↥K) : G)⁻¹ = (q1 D hF a : G)
  have hc := mem_Cplus_iff.mp (q1_mem_Cplus D hF a)
  rw [hc.2 t]
  group

noncomputable def yElt (α : ↥K ≃* SL₂ F) (t : F) : ↥K :=
  α.symm (lowerUni t)

noncomputable def wElt (α : ↥K ≃* SL₂ F) : ↥K := α.symm weylSL

theorem alpha_wElt (α : ↥K ≃* SL₂ F) : α (wElt α) = weylSL :=
  α.apply_symm_apply _

theorem alpha_yElt (α : ↥K ≃* SL₂ F) (t : F) : α (yElt α t) = lowerUni t :=
  α.apply_symm_apply _

theorem alpha_xElt (α : ↥K ≃* SL₂ F) (t : F) :
    α (xElt α t) = CFSG.SL2MinimalFaithful.unipotent t :=
  α.apply_symm_apply _

theorem wElt_conj_xElt (α : ↥K ≃* SL₂ F) (t : F) :
    wElt α * xElt α t * (wElt α)⁻¹ = yElt α t := by
  apply α.injective
  rw [map_mul, map_mul, map_inv, alpha_wElt, alpha_xElt α t, alpha_yElt α t]
  exact weylSL_mul_unipotent t

theorem wElt_mul_self (α : ↥K ≃* SL₂ F) : wElt α * wElt α = 1 := by
  apply α.injective
  rw [map_mul, map_one, alpha_wElt]
  exact weylSL_mul_self

end ModHyp

namespace ModHyp

variable {α : ↥K ≃* SL₂ F} {β : ↥Q →* Multiplicative (Fin 2 → F)}
variable (D : ModHyp Q Z K τ α β)

theorem conjHom_mul (k₁ k₂ : ↥K) (q : ↥Q) :
    conjHom D.norm_Q (k₁ * k₂) q = conjHom D.norm_Q k₁ (conjHom D.norm_Q k₂ q) := by
  refine Subtype.ext ?_
  show ((k₁ * k₂ : ↥K) : G) * (q : G) * ((k₁ * k₂ : ↥K) : G)⁻¹ =
    (k₁ : G) * ((k₂ : G) * (q : G) * (k₂ : G)⁻¹) * (k₁ : G)⁻¹
  simp only [Subgroup.coe_mul]
  group

theorem conjHom_one (q : ↥Q) : conjHom D.norm_Q (1 : ↥K) q = q := by
  refine Subtype.ext ?_
  show ((1 : ↥K) : G) * (q : G) * ((1 : ↥K) : G)⁻¹ = (q : G)
  simp

theorem q2_beta (hF : Fintype.card F = 4) (b : F) :
    betaAdd β (conjHom D.norm_Q (wElt α) (q1 D hF b)) = ![0, b] := by
  have h := betaAdd_conj D.equiv D.norm_Q (wElt α) (q1 D hF b)
  simp only [conjHom, MonoidHom.coe_mk, OneHom.coe_mk] at h ⊢
  rw [alpha_wElt α, weylSL_mulVec, q1_beta] at h
  exact h

noncomputable def q2 (hF : Fintype.card F = 4) (b : F) : ↥Q :=
  conjHom D.norm_Q (wElt α) (q1 D hF b)

theorem conjHom_w_q2 (hF : Fintype.card F = 4) (b : F) :
    conjHom D.norm_Q (wElt α) (q2 D hF b) = q1 D hF b := by
  rw [q2, ← conjHom_mul (α := α) (β := β) (D := D), wElt_mul_self,
    conjHom_one (α := α) (β := β) (D := D)]

theorem betaAdd_inv {β : ↥Q →* Multiplicative (Fin 2 → F)} (x : ↥Q) :
    betaAdd β x⁻¹ = -betaAdd β x := by
  show Multiplicative.toAdd (β x⁻¹) = -Multiplicative.toAdd (β x)
  rw [map_inv]
  rfl

theorem exists_decomp (hF : Fintype.card F = 4) (q : ↥Q) :
    betaAdd β (q * (q1 D hF (betaAdd β q 0) * q2 D hF (betaAdd β q 1))⁻¹) = 0 := by
  have hkey : ∀ v : Fin 2 → F, v + -(![v 0, 0] + ![0, v 1]) = 0 := by
    intro v
    ext i
    fin_cases i <;> simp
  simp only [q2]
  rw [betaAdd_mul, betaAdd_inv, betaAdd_mul, q1_beta, q2_beta]
  exact hkey _

theorem betaAdd_eq_pair (q : ↥Q) : betaAdd β q = ![betaAdd β q 0, betaAdd β q 1] := by
  ext i
  fin_cases i <;> rfl

noncomputable abbrev mu0sq (hF : Fintype.card F = 4) : F := ((mu0 hF : Fˣ) : F) ^ 2

theorem mu0_cube (hF : Fintype.card F = 4) : mu0 hF ^ 3 = 1 := by
  have h := pow_card_eq_one (x := mu0 hF)
  rwa [card_units_of_card_four hF] at h

theorem units_inv_mul_inv (hF : Fintype.card F = 4) (μ : Fˣ) : μ⁻¹ * μ⁻¹ = μ := by
  apply Units.ext
  simp only [Units.val_mul, units_inv_eq_sq hF]
  calc ((μ : Fˣ) : F) ^ 2 * ((μ : Fˣ) : F) ^ 2 = ((μ : Fˣ) : F) ^ 4 := by ring
    _ = ((μ : Fˣ) : F) := pow_four_eq_self hF _

theorem mu0_inv_mul_inv (hF : Fintype.card F = 4) : (mu0 hF)⁻¹ * (mu0 hF)⁻¹ = mu0 hF :=
  units_inv_mul_inv hF _

theorem diagSL_inv (l : Fˣ) : (diagSL l)⁻¹ = diagSL l⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [← diagSL_mul, mul_inv_cancel, diagSL_one])

theorem diagSL_mul_weylSL (hF : Fintype.card F = 4) (l : Fˣ) :
    diagSL l * weylSL = weylSL * diagSL l⁻¹ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_diagSL, coe_weylSL, Matrix.mul_apply, Fin.sum_univ_two,
      units_inv_eq_sq hF, CharTwo.neg_eq]

noncomputable def hOf (α : ↥K ≃* SL₂ F) (μ : Fˣ) : ↥K :=
  α.symm (diagSL μ)

theorem alpha_hOf (α : ↥K ≃* SL₂ F) (μ : Fˣ) : α (hOf α μ) = diagSL μ :=
  α.apply_symm_apply _

theorem hOf_cube (α : ↥K ≃* SL₂ F) (hF : Fintype.card F = 4) (μ : Fˣ) :
    (hOf α μ) ^ 3 = 1 := by
  have hμ : μ ^ 3 = 1 := by
    have h := pow_card_eq_one (x := μ)
    rwa [card_units_of_card_four hF] at h
  apply α.injective
  rw [map_pow, map_one, alpha_hOf]
  rw [show diagSL μ ^ 3 = diagSL (μ ^ 3) from by
    rw [pow_three, pow_three, diagSL_mul, diagSL_mul], hμ, diagSL_one]

theorem conj_hOf_x (α : ↥K ≃* SL₂ F) (μ : Fˣ) (s : F) :
    hOf α μ * xElt α s * (hOf α μ)⁻¹ = xElt α ((μ : F) ^ 2 * s) := by
  apply α.injective
  rw [map_mul, map_mul, map_inv, alpha_hOf, alpha_xElt, alpha_xElt]
  rw [CFSG.CGT.PushingUpLit.CGT6.TwoThree.diagSL_mul_unipotent]

theorem conj_hOf_x_inv (α : ↥K ≃* SL₂ F) (μ : Fˣ) (t : F) :
    (hOf α μ)⁻¹ * xElt α t * (hOf α μ) = xElt α (((μ : F) ^ 2)⁻¹ * t) := by
  have hμ2 : (μ : F) ^ 2 ≠ 0 := pow_ne_zero 2 (Units.ne_zero μ)
  have h := conj_hOf_x α μ (((μ : F) ^ 2)⁻¹ * t)
  rw [show (μ : F) ^ 2 * (((μ : F) ^ 2)⁻¹ * t) = t from by
    rw [← mul_assoc, mul_inv_cancel₀ hμ2, one_mul]] at h
  calc (hOf α μ)⁻¹ * xElt α t * (hOf α μ)
      = (hOf α μ)⁻¹ * (hOf α μ * xElt α (((μ : F) ^ 2)⁻¹ * t) * (hOf α μ)⁻¹) *
          (hOf α μ) := by rw [h]
    _ = xElt α (((μ : F) ^ 2)⁻¹ * t) := by group

theorem conj_hOf_w (α : ↥K ≃* SL₂ F) (hF : Fintype.card F = 4) (μ : Fˣ) :
    hOf α μ * wElt α * (hOf α μ)⁻¹ = wElt α * hOf α μ := by
  apply α.injective
  simp only [map_mul, map_inv, alpha_hOf, alpha_wElt, diagSL_inv]
  rw [diagSL_mul_weylSL hF, mul_assoc, ← diagSL_mul, units_inv_mul_inv hF]

theorem hOf_mul_hElt (α : ↥K ≃* SL₂ F) (hF : Fintype.card F = 4) (μ : Fˣ) :
    hOf α μ * hElt α hF = hElt α hF * hOf α μ := by
  apply α.injective
  simp only [map_mul, alpha_hOf, alpha_hElt, ← diagSL_mul, mul_comm]

end ModHyp

namespace ModHyp

variable {α : ↥K ≃* SL₂ F} {β : ↥Q →* Multiplicative (Fin 2 → F)}
variable (D : ModHyp Q Z K τ α β)

end ModHyp

end Main

end Sp44

end CFSG.Quasithin.F112R.St84
