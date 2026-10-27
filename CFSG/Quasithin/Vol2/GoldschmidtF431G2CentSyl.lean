module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2CentC
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2CentCount
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsG2Data
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.Cent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 CFSG.QuasithinUnique CFSG.Quasithin

set_option linter.unusedSectionVars false


variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem U_le_Pa : U K ≤ Pa K := fun g hg => by
  rw [mem_Pa_iff]
  have hle : posUnipotent Tag.G2 K ≤ borelGroup Tag.G2 K := le_sup_right
  exact borelGroup_le_parabolicSubgroup _ (hle hg)

theorem isSylowTwoOf_U_top : IsSylowTwoOf (U K) ⊤ :=
  CFSG.Quasithin.H13.Sec53F.G2.g2_sylow

theorem isSylowTwoOf_U_Pa : IsSylowTwoOf (U K) (Pa K) :=
  F7.isSylowTwoOf_mono_right isSylowTwoOf_U_top U_le_Pa le_top

theorem isSylowTwoOf_U_cent_xc (s : K) :
    IsSylowTwoOf (U K) (Subgroup.centralizer ({xc s} : Set (C K))) :=
  F7.isSylowTwoOf_mono_right isSylowTwoOf_U_top
    (fun _ hg => Subgroup.mem_centralizer_singleton_iff.2 (xc_comm_U hg s).symm) le_top

theorem card_conjSub (g : C K) (H : Subgroup (C K)) : Nat.card (conjSub g H) = Nat.card H :=
  (Nat.card_congr (Subgroup.equivMapOfInjective H (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).toEquiv).symm

theorem conj_xv_eq_nf {p : C K} (hp : p ∈ Pa K) :
    ∃ ν β γ : K, ν ≠ 0 ∧ p⁻¹ * xv 1 * p = nf 0 0 0 ν β γ := by
  have hpM : (p : ModGL Tag.G2 K) ∈ parabolicSubgroup Tag.G2 K {i0} := hp
  have hpM' : (p : ModGL Tag.G2 K)⁻¹ ∈ parabolicSubgroup Tag.G2 K {i0} := inv_mem hpM
  have htA : gX rV (1 : K) ∈ rootSpan Tag.G2 K TVBC :=
    pinnedX_mem_rootSpan (show rV ∈ TVBC from Or.inl rfl) 1
  have h1 : ((p⁻¹ * xv 1 * p : C K) : ModGL Tag.G2 K) ∈ rootSpan Tag.G2 K TVBC := by
    have := (Subgroup.mem_normalizer_iff.1 (parabolic_a_le_normalizer_TVBC hpM') _).1 htA
    rw [inv_inv] at this
    exact this
  obtain ⟨ν, β, γ, h⟩ := mem_rootSpan_TVBC_iff.1 h1
  refine ⟨ν, β, γ, ?_, Subtype.ext (h.trans ?_)⟩
  · intro h0
    have hV : ((p⁻¹ * xv 1 * p : C K) : ModGL Tag.G2 K) ∈ rootSpan Tag.G2 K TBC := by
      rw [h, h0, gX_zero, one_mul]
      exact mem_rootSpan_TBC_iff.2 ⟨β, γ, rfl⟩
    have htV : gX rV (1 : K) ∈ rootSpan Tag.G2 K TBC := by
      have := (Subgroup.mem_normalizer_iff.1 (parabolic_a_le_normalizer_TBC hpM) _).1 hV
      have e : (p : ModGL Tag.G2 K) * ((p : ModGL Tag.G2 K)⁻¹ * gX rV 1 * (p : ModGL Tag.G2 K)) *
          (p : ModGL Tag.G2 K)⁻¹ = gX rV 1 := by group
      rw [← e]
      exact this
    exact gX_rV_not_mem_TBC one_ne_zero htV
  · rw [nf_zero_zero_zero]
    rfl

theorem card_le_of_le_cent_xv {S' : Subgroup (C K)}
    (hS'D : S' ≤ Subgroup.centralizer ({xv 1} : Set (C K))) (hS' : IsPGroup 2 S') :
    Nat.card S' ≤ Nat.card K ^ 4 := by
  obtain ⟨p, hp, hle⟩ := F7.isSylowTwoOf_exists_conj_le isSylowTwoOf_U_Pa (hS'D.trans ct) hS'
  obtain ⟨ν, β, γ, hν, ht⟩ := conj_xv_eq_nf hp
  have h2 : conjSub p⁻¹ S' ≤ U K ⊓ Subgroup.centralizer ({nf 0 0 0 ν β γ} : Set (C K)) := by
    intro y hy
    rw [mem_conjSub, inv_inv] at hy
    refine ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · have := mem_conjSub.1 (hle hy)
      simpa [mul_assoc] using this
    · rw [← ht]
      have hc := Subgroup.mem_centralizer_singleton_iff.1 (hS'D hy)
      calc y * (p⁻¹ * xv 1 * p) = p⁻¹ * ((p * y * p⁻¹) * xv 1) * p := by group
        _ = p⁻¹ * (xv 1 * (p * y * p⁻¹)) * p := by rw [hc]
        _ = p⁻¹ * xv 1 * p * y := by group
  calc Nat.card S' = Nat.card (conjSub p⁻¹ S') := (card_conjSub _ _).symm
    _ ≤ Nat.card ↥(U K ⊓ Subgroup.centralizer ({nf 0 0 0 ν β γ} : Set (C K))) :=
        Subgroup.card_le_of_le h2
    _ = Nat.card K ^ 4 := card_inf_centralizer_nf hν

theorem card_U_inf_cent_xv :
    Nat.card ↥(U K ⊓ Subgroup.centralizer ({xv 1} : Set (C K))) = Nat.card K ^ 4 := by
  rw [xv_eq_nf]
  exact card_inf_centralizer_nf (K := K) (ν := 1) (β := 0) (γ := 0) one_ne_zero

theorem sylow_cent_xv :
    IsSylowTwoOf (U K ⊓ Subgroup.centralizer ({xv 1} : Set (C K)))
      (Subgroup.centralizer ({xv 1} : Set (C K))) := by
  have hSp : IsPGroup 2 ↥(U K ⊓ Subgroup.centralizer ({xv 1} : Set (C K))) :=
    isSylowTwoOf_U_top.2.1.to_le inf_le_left
  obtain ⟨S₂, hS₂, hSS₂⟩ := EscapingLocal.exists_isSylowTwoOf_ge inf_le_right hSp
  have hcard : Nat.card S₂ ≤ Nat.card ↥(U K ⊓ Subgroup.centralizer ({xv 1} : Set (C K))) := by
    rw [card_U_inf_cent_xv]
    exact card_le_of_le_cent_xv hS₂.1 hS₂.2.1
  rw [Subgroup.eq_of_le_of_card_ge hSS₂ hcard]
  exact hS₂

theorem card_centralizer_map (φ : MulAut (C K)) (x : C K) :
    Nat.card ↥(Subgroup.centralizer ({φ x} : Set (C K))) =
      Nat.card ↥(Subgroup.centralizer ({x} : Set (C K))) := by
  have h : (Subgroup.centralizer ({x} : Set (C K))).map φ.toMonoidHom =
      Subgroup.centralizer ({φ x} : Set (C K)) := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have := Subgroup.mem_centralizer_singleton_iff.1 hw
      simpa using congrArg φ this
    · intro hy
      refine ⟨φ.symm y, ?_, by simp⟩
      refine Subgroup.mem_centralizer_singleton_iff.2 ?_
      have := Subgroup.mem_centralizer_singleton_iff.1 hy
      apply φ.injective
      simpa using this
  rw [← h]
  exact (Nat.card_congr (Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).toEquiv).symm

theorem no_aut_xv_xc (s : K) (φ : MulAut (C K)) : φ (xv 1) ≠ xc s := by
  intro h
  have h1 : IsSylowIn 2 (U K ⊓ Subgroup.centralizer ({xv 1} : Set (C K)))
      (Subgroup.centralizer ({xv 1} : Set (C K))) := sylow_cent_xv
  have h2 : IsSylowIn 2 (U K) (Subgroup.centralizer ({xc s} : Set (C K))) :=
    isSylowTwoOf_U_cent_xc s
  have e1 := h1.card_eq
  have e2 := h2.card_eq
  rw [card_U_inf_cent_xv] at e1
  rw [card_U] at e2
  have e3 : Nat.card ↥(Subgroup.centralizer ({xc s} : Set (C K))) =
      Nat.card ↥(Subgroup.centralizer ({xv 1} : Set (C K))) := by
    rw [← h]
    exact card_centralizer_map φ (xv 1)
  rw [e3] at e2
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have hlt := Nat.pow_lt_pow_right hq (show 4 < 6 by norm_num)
  exact absurd (e2.trans e1.symm) (ne_of_gt hlt)

theorem no_aut_xc_xv (s : K) (φ : MulAut (C K)) : φ (xc s) ≠ xv 1 := fun h =>
  no_aut_xv_xc s φ.symm (by rw [← h, MulEquiv.symm_apply_apply])

theorem not_isConj_xc_xv (s : K) : ¬ IsConj (xc s) (xv 1) := by
  rw [isConj_iff]
  rintro ⟨c, hc⟩
  exact no_aut_xc_xv s (MulAut.conj c) (by simpa [MulAut.conj_apply] using hc)

end CFSG.Quasithin.H13.F431.G2.Cent
