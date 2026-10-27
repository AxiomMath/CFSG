module

public import CFSG.RankThree.GF2n.Stroth80.Sec5NatComm
public import CFSG.RankThree.GF2n.Stroth80.Sec5Vt

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {Q Z V : Subgroup G} {K' : Type} [Field K'] {γ : G → K'}
  {M₀ : Tim79.QuadModel Q Z K' γ} {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
  [(Z.subgroupOf V).Normal]

namespace KS93

structure VecData (M₀ : Tim79.QuadModel Q Z K' γ) (V : Subgroup G) [(Z.subgroupOf V).Normal]
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (θ : K' ≃+* K) : Prop where
  le : V ≤ Q
  smul : ∀ (c : K') (e : M₀.E), e ∈ M₀.img V → c • e ∈ M₀.img V
  compat : ∀ (c : K') (v w : ↥V), M₀.π w = c • M₀.π v → secVec ψ w = θ c • secVec ψ v

noncomputable def repV (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (b : ι → K) : ↥V :=
  (QuotientGroup.mk_surjective (ψ.symm (Multiplicative.ofAdd b))).choose

noncomputable def vecInv (M₀ : Tim79.QuadModel Q Z K' γ)
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (b : ι → K) : M₀.E :=
  M₀.π (repV ψ b)

variable (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K))

theorem secVec_repV (b : ι → K) : secVec ψ (repV ψ b) = b := by
  unfold secVec repV
  rw [(QuotientGroup.mk_surjective _).choose_spec, MulEquiv.apply_symm_apply, toAdd_ofAdd]

theorem pi_eq_of_secVec_eq (hVQ : V ≤ Q) {v w : ↥V} (h : secVec ψ v = secVec ψ w) :
    M₀.π v = M₀.π w := by
  have h1 : (v : G) * (w : G)⁻¹ ∈ Z := (secVec_eq_iff ψ v w).mp h
  have hv : (v : G) ∈ Q := hVQ v.2
  have hw : (w : G) ∈ Q := hVQ w.2
  have h2 : M₀.π ((v : G) * (w : G)⁻¹) = 0 := (M₀.π_ker _ (Q.mul_mem hv (Q.inv_mem hw))).mpr h1
  rw [M₀.π_mul _ hv _ (Q.inv_mem hw), M₀.pi_inv hw] at h2
  exact add_neg_eq_zero.mp h2

theorem secVec_eq_of_pi_eq (hVQ : V ≤ Q) {v w : ↥V} (h : M₀.π v = M₀.π w) :
    secVec ψ v = secVec ψ w := by
  rw [secVec_eq_iff]
  have hv : (v : G) ∈ Q := hVQ v.2
  have hw : (w : G) ∈ Q := hVQ w.2
  have h2 : M₀.π ((v : G) * (w : G)⁻¹) = 0 := by
    rw [M₀.π_mul _ hv _ (Q.inv_mem hw), M₀.pi_inv hw, h, add_neg_cancel]
  exact (M₀.π_ker _ (Q.mul_mem hv (Q.inv_mem hw))).mp h2

theorem vecInv_secVec (hVQ : V ≤ Q) (v : ↥V) : vecInv M₀ ψ (secVec ψ v) = M₀.π v :=
  pi_eq_of_secVec_eq ψ hVQ (secVec_repV ψ _)

theorem vecInv_mem_img (hVQ : V ≤ Q) (b : ι → K) : vecInv M₀ ψ b ∈ M₀.img V :=
  M₀.pi_mem_img (repV ψ b).2 (hVQ (repV ψ b).2)

theorem vecInv_injective (hVQ : V ≤ Q) : Function.Injective (vecInv M₀ ψ) := by
  intro b b' h
  rw [← secVec_repV ψ b, ← secVec_repV ψ b']
  exact secVec_eq_of_pi_eq ψ hVQ h

theorem vecInv_add (hVQ : V ≤ Q) (b b' : ι → K) :
    vecInv M₀ ψ (b + b') = vecInv M₀ ψ b + vecInv M₀ ψ b' := by
  have e : b + b' = secVec ψ (repV ψ b * repV ψ b') := by
    rw [secVec_mul, secVec_repV, secVec_repV]
  rw [e, vecInv_secVec ψ hVQ, Subgroup.coe_mul,
    M₀.π_mul _ (hVQ (repV ψ b).2) _ (hVQ (repV ψ b').2)]
  rfl

theorem vecInv_zero (hVQ : V ≤ Q) : vecInv M₀ ψ (0 : ι → K) = 0 := by
  have h := vecInv_add (M₀ := M₀) ψ hVQ 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem exists_vecInv_eq (hVQ : V ≤ Q) {e : M₀.E} (he : e ∈ M₀.img V) :
    ∃ b, vecInv M₀ ψ b = e := by
  obtain ⟨v, hvV, -, rfl⟩ := he
  exact ⟨secVec ψ ⟨v, hvV⟩, vecInv_secVec ψ hVQ ⟨v, hvV⟩⟩

variable {ψ} {θ : K' ≃+* K}

theorem VecData.vecInv_smul (hD : VecData M₀ V ψ θ) (c : K') (b : ι → K) :
    vecInv M₀ ψ (θ c • b) = c • vecInv M₀ ψ b := by
  obtain ⟨w, hwV, -, hw⟩ := hD.smul c _ (vecInv_mem_img ψ hD.le b)
  have h1 : secVec ψ ⟨w, hwV⟩ = θ c • secVec ψ (repV ψ b) := hD.compat c _ ⟨w, hwV⟩ hw
  rw [secVec_repV] at h1
  rw [← h1, vecInv_secVec ψ hD.le]
  exact hw

noncomputable def vecOf (M₀ : Tim79.QuadModel Q Z K' γ)
    (ψ : ↥V ⧸ Z.subgroupOf V ≃* Multiplicative (ι → K)) (e : M₀.E) : ι → K :=
  Function.invFun (vecInv M₀ ψ) e

theorem VecData.vecOf_vecInv (hD : VecData M₀ V ψ θ) (b : ι → K) :
    vecOf M₀ ψ (vecInv M₀ ψ b) = b :=
  Function.leftInverse_invFun (vecInv_injective ψ hD.le) b

theorem VecData.vecInv_vecOf (hD : VecData M₀ V ψ θ) {e : M₀.E} (he : e ∈ M₀.img V) :
    vecInv M₀ ψ (vecOf M₀ ψ e) = e :=
  Function.invFun_eq (exists_vecInv_eq ψ hD.le he)

theorem VecData.vecOf_pi (hD : VecData M₀ V ψ θ) (v : ↥V) : vecOf M₀ ψ (M₀.π v) = secVec ψ v := by
  rw [← vecInv_secVec ψ hD.le, hD.vecOf_vecInv]

theorem VecData.vecOf_add (hD : VecData M₀ V ψ θ) {e e' : M₀.E} (he : e ∈ M₀.img V)
    (he' : e' ∈ M₀.img V) : vecOf M₀ ψ (e + e') = vecOf M₀ ψ e + vecOf M₀ ψ e' := by
  obtain ⟨b, rfl⟩ := exists_vecInv_eq ψ hD.le he
  obtain ⟨b', rfl⟩ := exists_vecInv_eq ψ hD.le he'
  rw [← vecInv_add ψ hD.le, hD.vecOf_vecInv, hD.vecOf_vecInv, hD.vecOf_vecInv]

theorem VecData.vecOf_eq_zero_iff (hD : VecData M₀ V ψ θ) {e : M₀.E} (he : e ∈ M₀.img V) :
    vecOf M₀ ψ e = 0 ↔ e = 0 := by
  constructor
  · intro h
    rw [← hD.vecInv_vecOf he, h, vecInv_zero ψ hD.le]
  · rintro rfl
    rw [← vecInv_zero ψ hD.le, hD.vecOf_vecInv]

noncomputable def VecData.trSub (hD : VecData M₀ V ψ θ) (Y' : Submodule K' M₀.E) :
    Submodule K (ι → K) where
  carrier := {b | vecInv M₀ ψ b ∈ Y'}
  add_mem' {b b'} hb hb' := by
    show vecInv M₀ ψ (b + b') ∈ Y'
    rw [vecInv_add ψ hD.le]
    exact Y'.add_mem hb hb'
  zero_mem' := by
    show vecInv M₀ ψ 0 ∈ Y'
    rw [vecInv_zero ψ hD.le]
    exact Y'.zero_mem
  smul_mem' c b hb := by
    obtain ⟨c', rfl⟩ := θ.surjective c
    show vecInv M₀ ψ (θ c' • b) ∈ Y'
    rw [hD.vecInv_smul]
    exact Y'.smul_mem c' hb

theorem VecData.mem_trSub (hD : VecData M₀ V ψ θ) {Y' : Submodule K' M₀.E} {b : ι → K} :
    b ∈ hD.trSub Y' ↔ vecInv M₀ ψ b ∈ Y' := Iff.rfl

theorem VecData.trSub_mono (hD : VecData M₀ V ψ θ) {Y₁ Y₂ : Submodule K' M₀.E} (h : Y₁ ≤ Y₂) :
    hD.trSub Y₁ ≤ hD.trSub Y₂ := fun _ hb => h hb

theorem VecData.card_trSub (hD : VecData M₀ V ψ θ) (Y' : Submodule K' M₀.E) :
    Nat.card (hD.trSub Y') = Nat.card ↥(Y' ⊓ imgSub M₀ V hD.smul) := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun b => ⟨vecInv M₀ ψ (b : ι → K), b.2, vecInv_mem_img ψ hD.le _⟩) ⟨?_, ?_⟩)
  · intro b b' h
    exact Subtype.ext (vecInv_injective ψ hD.le (congrArg Subtype.val h))
  · rintro ⟨e, heY, heV⟩
    obtain ⟨b, rfl⟩ := exists_vecInv_eq ψ hD.le heV
    exact ⟨⟨b, heY⟩, rfl⟩

theorem VecData.finrank_trSub [Finite K'] [Finite K] (hD : VecData M₀ V ψ θ)
    (Y' : Submodule K' M₀.E) :
    Module.finrank K (hD.trSub Y') = Module.finrank K' ↥(Y' ⊓ imgSub M₀ V hD.smul) := by
  haveI : Finite M₀.E := Module.finite_of_finite K'
  have hKK : Nat.card K = Nat.card K' := Nat.card_congr θ.toEquiv.symm
  have h1 : 1 < Nat.card K' := Finite.one_lt_card
  have h := hD.card_trSub Y'
  have hA : Nat.card (hD.trSub Y') = Nat.card K ^ Module.finrank K (hD.trSub Y') :=
    Module.natCard_eq_pow_finrank
  have hB : Nat.card ↥(Y' ⊓ imgSub M₀ V hD.smul) =
      Nat.card K' ^ Module.finrank K' ↥(Y' ⊓ imgSub M₀ V hD.smul) :=
    Module.natCard_eq_pow_finrank
  rw [hA, hB, hKK] at h
  exact Nat.pow_right_injective h1 h

end KS93

end CFSG.RankThree.GF2n.Stroth80
