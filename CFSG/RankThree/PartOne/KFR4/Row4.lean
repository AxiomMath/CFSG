module

public import CFSG.RankThree.PartOne.KFR4.Model
public import CFSG.RankThree.PartOne.KFR4.Frame
public import CFSG.RankThree.PartOne.S15K.OrthModel

public section

namespace CFSG.RankThree.PartOne.KFR4

open QuadraticMap CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFCL CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.S15K CFSG.ClassicalGroups.Orthogonal CFSG.GroupTheory.WeirSylow
open CFSG.LieType.Universal.Spin (quadMinus)

@[expose] noncomputable def orthDerivedEquivProj {K : Type} [Field K] [Finite K] [CharP K 2]
    {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    {Q : QuadraticForm K V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) :
    orthDerived Q ≃* ProjOrthDerived Q := by
  have hinj := mk_injective_orth hQ
  have hsurj : Function.Surjective
      (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q))) :=
    QuotientGroup.mk'_surjective _
  exact MulEquiv.ofBijective (QuotientGroup.mk' ((scalars K V).subgroupOf (orthDerived Q)))
    ⟨hinj, hsurj⟩

theorem linConj_symm_linConj {K V V' : Type} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module K V'] (e : V ≃ₗ[K] V') (g : V ≃ₗ[K] V) :
    linConj e.symm (linConj e g) = g := by
  ext v
  simp [linConj_apply]

theorem rootModelRow_four : RootModelRow 4 := by
  intro G _ _ p A c L E h15 hF hF13 hout hEI
  have h := h15.h12
  obtain ⟨f, hf1, hpf, ⟨b, c', hbc, ⟨φ₀⟩⟩, -, hEA, -⟩ := hout
  have hp : p.Prime := h.prime
  have hp5 : 5 ≤ p := by
    have h3 : 3 < p := h.three_lt
    by_contra h4
    have : p = 4 := by omega
    exact absurd hp (by rw [this]; decide)
  have : NeZero f := ⟨by omega⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpq : p ∣ Nat.card (GaloisField 2 f) + 1 := by rw [hK]; exact hpf
  have hQ := polar_nondegenerate_quadMinus hbc
  have hdim : Module.finrank (GaloisField 2 f)
      (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField 2 f) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
  have hV : ¬ IsPlusType (quadMinus 4 (GaloisField 2 f) b c') :=
    not_isPlusType_quadMinus (by omega) hbc
  let ψ : ↥(lieGenerated p E) ≃* orthDerived (quadMinus 4 (GaloisField 2 f) b c') :=
    (φ₀.trans (projOmegaMinusEquivOrth (GaloisField 2 f) b c')).trans
      (orthDerivedEquivProj hQ).symm
  have hEel : IsElementaryAbelian p E := h.E_elem
  have hcommE : ∀ a ∈ E, ∀ a' ∈ E, a * a' = a' * a := fun a ha a' ha' => by
    have := congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨a, ha⟩ : ↥E) ⟨a', ha'⟩)
    simpa using this
  have hpowE : ∀ a ∈ E, a ^ p = 1 := fun a ha => elemPow_eq_one_of_isElementaryAbelian a ha
  have hEcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  set E' : Subgroup ↥(lieGenerated p E) := E.subgroupOf (lieGenerated p E) with hE'
  have hEcardI : Nat.card E' = p ^ 3 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEI).toEquiv).trans hEcard
  let θ : ↥(lieGenerated p E) →*
      ((Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField 2 f) ≃ₗ[GaloisField 2 f]
        (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2 → GaloisField 2 f)) :=
    (orthDerived (quadMinus 4 (GaloisField 2 f) b c')).subtype.comp ψ.toMonoidHom
  have hθinj : Function.Injective θ :=
    (orthDerived (quadMinus 4 (GaloisField 2 f) b c')).subtype_injective.comp ψ.injective
  have hcardÊ : Nat.card (E'.map θ) = p ^ 3 := by
    rw [Subgroup.card_map_of_injective hθinj]
    exact hEcardI
  have hexp : ∀ g ∈ E'.map θ, g ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow]
    have : x ^ p = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow]
      exact hpowE x.1 (Subgroup.mem_subgroupOf.1 hx))
    rw [this, map_one]
  have hcomm : ∀ g ∈ E'.map θ, ∀ g' ∈ E'.map θ, g * g' = g' * g := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcommE _ (Subgroup.mem_subgroupOf.1 hx) _ (Subgroup.mem_subgroupOf.1 hy))
  have hO : E'.map θ ≤
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 4 (GaloisField 2 f) b c') := by
    rintro _ ⟨x, -, rfl⟩
    exact (Subgroup.commutator_le.mpr fun g hg g' hg' => by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem hg hg') (inv_mem hg)) (inv_mem hg')) (ψ x).2
  obtain ⟨Ee, _, _, _, S, Φ, hΦ⟩ :=
    exists_frame (quadMinus 4 (GaloisField 2 f) b c') hQ hdim hV hp hp5 hpq (E'.map θ) hO hcardÊ
      hexp hcomm
  let ψ' : ↥(lieGenerated p E) ≃* ↥(Om S.D) := ψ.trans (orthDerivedEquiv Φ.symm)
  have hcoe : ∀ x : ↥(lieGenerated p E),
      (ψ' x : ↥(Om S.D)).1 = linConj Φ.toLinearEquiv.symm (θ x) := fun x => rfl
  have key : E'.map ψ'.toMonoidHom = TS S := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h1 : θ x ∈ (Tstd S).map (linConj Φ.toLinearEquiv).toMonoidHom := by
        rw [hΦ]
        exact ⟨x, hx, rfl⟩
      obtain ⟨t, ht, htx⟩ := h1
      show (ψ' x : ↥(Om S.D)).1 ∈ Tstd S
      rw [hcoe, ← htx]
      show linConj Φ.toLinearEquiv.symm (linConj Φ.toLinearEquiv t) ∈ Tstd S
      rw [linConj_symm_linConj]
      exact ht
    · intro hy
      have h1 : linConj Φ.toLinearEquiv (y : ↥(Om S.D)).1 ∈ E'.map θ := by
        rw [← hΦ]
        exact ⟨_, hy, rfl⟩
      obtain ⟨x, hx, hxy⟩ := h1
      refine ⟨x, hx, Subtype.ext ?_⟩
      show (ψ' x : ↥(Om S.D)).1 = (y : ↥(Om S.D)).1
      rw [hcoe, show θ x = linConj Φ.toLinearEquiv (y : ↥(Om S.D)).1 from hxy,
        linConj_symm_linConj]
  obtain ⟨R₀, ⟨rd⟩⟩ := (stdB3Data S).exists_rootData S.hp S.hp5
  have hT : (TS S).map ψ'.symm.toMonoidHom = E' := by
    rw [← key, Subgroup.map_map]
    have : ψ'.symm.toMonoidHom.comp ψ'.toMonoidHom = MonoidHom.id _ := by
      ext x
      simp
    rw [this, Subgroup.map_id]
  rw [← hT]
  exact ⟨R₀.map ψ'.symm, Or.inr ⟨rd.map ψ'.symm⟩⟩

end CFSG.RankThree.PartOne.KFR4
