module

public import CFSG.LocalAnalysis.SignalizerFunctor.Helpers
public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Thm210SetupGlobal

public section

open CFSG.Open
open scoped commutatorElement IsMulCommutative

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

open Thm210

variable {Γ : Type*} [Group Γ] {p : ℕ} {A G J : Subgroup Γ}

theorem Thm210.mem_normalizer_commutator {H₁ H₂ : Subgroup Γ} {g : Γ}
    (h₁ : g ∈ Subgroup.normalizer (H₁ : Set Γ)) (h₂ : g ∈ Subgroup.normalizer (H₂ : Set Γ)) :
    g ∈ Subgroup.normalizer ((⁅H₁, H₂⁆ : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h₁ h₂ ⊢
  rw [Subgroup.map_commutator, h₁, h₂]

theorem Thm210.commutator_inf_centralizer_eq_bot [Finite Γ] {R : Subgroup Γ} [IsMulCommutative R]
    (hp : p.Prime) (hAR : A ≤ Subgroup.normalizer (R : Set Γ)) (hA : IsPGroup p A)
    (hcop : Nat.Coprime p (Nat.card R)) :
    ⁅R, A⁆ ⊓ Subgroup.centralizer (A : Set Γ) = ⊥ := by
  have := Fintype.ofFinite A
  have := Fact.mk hp
  let ψ : ↥A →* MulAut ↥R := R.normalizerMonoidHom.comp (Subgroup.inclusion hAR)
  have hψ : ∀ (a : ↥A) (r : ↥R), ((ψ a r : ↥R) : Γ) = a * r * (a : Γ)⁻¹ := fun a r => by
    simp [ψ]
  let σ : ↥R →* ↥R :=
    { toFun := fun r => ∏ a : ↥A, ψ a r
      map_one' := by simp
      map_mul' := fun r s => by simp [Finset.prod_mul_distrib] }
  have hσ : ∀ r, σ r = ∏ a : ↥A, ψ a r := fun _ => rfl
  have hσconj : ∀ (b : ↥A) (r : ↥R), σ (ψ b r) = σ r := by
    intro b r
    rw [hσ, hσ]
    exact Fintype.prod_equiv (Equiv.mulRight b) _ _ fun a => by simp [← MulAut.mul_apply, ← map_mul]
  have hσfix : ∀ r : ↥R, (∀ a : ↥A, ψ a r = r) → σ r = r ^ Fintype.card ↥A := by
    intro r hr
    rw [hσ, Finset.prod_congr rfl fun a _ => hr a, Finset.prod_const, Finset.card_univ]
  have hcomm : ⁅R, A⁆ ≤ (σ.ker).map R.subtype := by
    refine Subgroup.commutator_le.mpr fun x hx a ha => ?_
    refine ⟨⟨x, hx⟩ * ψ ⟨a, ha⟩ ⟨x, hx⟩⁻¹, ?_, ?_⟩
    · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, map_inv, hσconj, mul_inv_cancel]
    · have := hψ ⟨a, ha⟩ ⟨x, hx⟩⁻¹
      simp only [InvMemClass.coe_inv] at this
      change x * ((ψ ⟨a, ha⟩ ⟨x, hx⟩⁻¹ : ↥R) : Γ) = ⁅x, a⁆
      rw [this, commutatorElement_def]
      simp [mul_assoc]
  rw [eq_bot_iff]
  intro y hy
  obtain ⟨hyc, hyA⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨y', hy'ker, rfl⟩ := hcomm hyc
  have hfix : ∀ a : ↥A, ψ a y' = y' := by
    intro a
    apply Subtype.ext
    rw [hψ]
    have := Subgroup.mem_centralizer_iff.mp hyA a a.2
    change (a : Γ) * y' = (y' : Γ) * a at this
    rw [this]
    group
  have hy1 : y' ^ Fintype.card ↥A = 1 := by
    rw [← hσfix y' hfix]
    exact hy'ker
  obtain ⟨n, hn⟩ := hA.exists_card_eq
  have hcard : Fintype.card ↥A = p ^ n := by rw [← Nat.card_eq_fintype_card, hn]
  have hcop' : Nat.Coprime (Fintype.card ↥A) (Nat.card R) := by
    rw [hcard]
    exact hcop.pow_left n
  have hord : orderOf y' ∣ Fintype.card ↥A := orderOf_dvd_of_pow_eq_one hy1
  have hord' : orderOf y' ∣ Nat.card R := orderOf_dvd_natCard y'
  have h1 : orderOf y' = 1 := Nat.eq_one_of_dvd_coprimes hcop' hord hord'
  rw [orderOf_eq_one_iff] at h1
  rw [h1]
  exact Subgroup.one_mem _

theorem Thm210.commutator_le_of_normalizes {H Q : Subgroup Γ}
    (hQH : Q ≤ Subgroup.normalizer (H : Set Γ)) : ⁅H, Q⁆ ≤ H := by
  refine Subgroup.commutator_le.mpr fun x hx a ha => ?_
  have h1 := (Subgroup.mem_normalizer_iff.mp (hQH ha) x⁻¹).mp (inv_mem hx)
  have := mul_mem hx h1
  simpa [commutatorElement_def, mul_assoc] using this

theorem SemisimpleAction.isPGroup (h : SemisimpleAction p A G) : IsPGroup p A :=
  CFSG.SignalizerFunctor.Helpers.elementary_abelian_isPGroup p A h.elemAbelian

theorem SemisimpleAction.coprime_card_of_le (h : SemisimpleAction p A G) {X : Subgroup Γ}
    (hXG : X ≤ G) : Nat.Coprime p (Nat.card X) :=
  Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hXG) h.nearPSolvable.1

section Finite

variable [Finite Γ]

theorem SemisimpleAction.commutator_fProd_le
    (h : SemisimpleAction p A G) :
    ⁅fProd A G, A⁆ ≤ fProd A G :=
  commutator_le_of_normalizes h.admits_fProd

theorem SemisimpleAction.commutator_fProd_le_group
    (h : SemisimpleAction p A G) :
    ⁅fProd A G, A⁆ ≤ G :=
  h.commutator_fProd_le.trans (fProd_le A G)

theorem SemisimpleAction.admits_commutator_fProd
    (h : SemisimpleAction p A G) :
    Admits (cenIn G A ⊔ A) ⁅fProd A G, A⁆ := by
  refine sup_le (fun d hd => ?_) (fun a ha => ?_)
  · have hdK : d ∈ kProd A G := h.cenIn_le_kProd hd
    refine mem_normalizer_commutator (h.kProd_le_normalizer hdK) ?_
    exact Subgroup.centralizer_le_normalizer (A : Set Γ) (Subgroup.mem_inf.mp hd).2
  · exact mem_normalizer_commutator (h.admits_fProd ha) (Subgroup.le_normalizer ha)

theorem SemisimpleAction.commutator_fProd_inf_cenIn
    (h : SemisimpleAction p A G) :
    ⁅fProd A G, A⁆ ⊓ cenIn G A = ⊥ := by
  have := h.isMulCommutative_fProd
  have hbot := commutator_inf_centralizer_eq_bot h.prime h.admits_fProd h.isPGroup
    (h.coprime_card_of_le (fProd_le A G))
  rw [eq_bot_iff] at hbot ⊢
  intro x hx
  obtain ⟨hxc, hxD⟩ := Subgroup.mem_inf.mp hx
  exact hbot (Subgroup.mem_inf.mpr ⟨hxc, (Subgroup.mem_inf.mp hxD).2⟩)

end Finite

end CFSG.SignalizerFunctorTheorem.McBride.Near
