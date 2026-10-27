module

public import CFSG.Quasithin.Recognition.J2RecCzModel
public import CFSG.Quasithin.Recognition.J2RecQ8D8

public section

namespace CFSG.Quasithin

open Equiv J2Cz J2Cz.QM

namespace S1421QA17

section Model

variable {P : Type*} [Group P]

private theorem anti_of_sq' {a b w : P} (ha : a * a = 1) (hb : b * b = 1) (hab : (a * b) ^ 2 = w)
    (hwa : w * a = a * w) : b * a = w * (a * b) := by
  have h1 : a * b * (a * b) = w := by rw [← sq]; exact hab
  calc b * a = a * (a * b * (a * b)) * b := by
        rw [show a * (a * b * (a * b)) * b = (a * a) * b * a * (b * b) by group, ha, hb]
        group
    _ = a * w * b := by rw [h1]
    _ = w * (a * b) := by rw [← hwa]; group

private theorem QM_comm_or_central : ∀ p : QM, p ≠ 1 →
    p = QM.z ∨ ∃ q : QM, q * p * q⁻¹ * p⁻¹ = QM.z := by
  decide +kernel

private theorem card_QM' : Nat.card QM = 32 := by
  rw [Nat.card_eq_fintype_card]
  rfl

theorem _root_.CFSG.Quasithin.IsQ8D8.nonempty_mulEquiv_QM (h : IsQ8D8 P) :
    Nonempty (P ≃* QM) := by
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [h.1]; norm_num)
  obtain ⟨φ, hsurj, hφeq, hφne, -⟩ := h.exists_hom
  set z : P := φ (QuaternionGroup.a 2, 1) with hzdef
  have hz2 : z * z = 1 := by
    rw [hzdef, ← map_mul]
    have : ((QuaternionGroup.a 2, 1) : QuaternionGroup 2 × DihedralGroup 4) *
        (QuaternionGroup.a 2, 1) = 1 := by decide
    rw [this, map_one]
  have hzc : z ∈ Subgroup.center P := by
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    obtain ⟨uv, rfl⟩ := hsurj g
    rw [hzdef, ← map_mul, ← map_mul]
    congr 1
    obtain ⟨u, v⟩ := uv
    revert u v
    decide
  obtain ⟨x', hx2, hxz, hxx, hprod⟩ := h.exists_fiveLines hzc hφne
  have hrel : LiftRel z (fun j : Fin 4 => x' j.succ) :=
    ⟨hz2, fun j => (hxz j.succ).symm, fun j => hx2 j.succ, fun i j hij =>
      anti_of_sq' (hx2 _) (hx2 _) (hxx _ _ fun e => hij.ne (Fin.succ_injective _ e))
        (hxz _).symm⟩
  have hχz : hrel.liftHom QM.z = z := by
    rw [LiftRel.liftHom_apply]
    simp [liftT, QM.z]
  have hinj : Function.Injective hrel.liftHom := by
    rw [injective_iff_map_eq_one]
    intro p hp
    by_contra hp1
    rcases QM_comm_or_central p hp1 with h1 | ⟨q, hq⟩
    · rw [h1, hχz] at hp
      exact hφne hp
    · have : hrel.liftHom (q * p * q⁻¹ * p⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hp]
        simp
      rw [hq, hχz] at this
      exact hφne this
  have hbij : Function.Bijective hrel.liftHom :=
    (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, by rw [card_QM', h.1]⟩
  exact ⟨(MulEquiv.ofBijective hrel.liftHom hbij).symm⟩

end Model

section Action

variable {G : Type} [Group G]

private theorem linePerm_conj' (p : QM) : linePerm (MulAut.conj p) = 1 :=
  Equiv.ext fun j => (linePerm_eq (conj_x p j)).trans (Perm.one_apply j).symm

theorem exists_hom_perm5 {H Q : Subgroup G} (hQH : Q ≤ H)
    (hQn : H ≤ Subgroup.normalizer (Q : Set G)) (hQ : IsQ8D8 ↥Q)
    (hC : ∀ x ∈ H, (∀ q ∈ Q, x * q = q * x) → x ∈ Q) :
    ∃ θ : ↥H →* Equiv.Perm (Fin 5), θ.ker = Q.subgroupOf H := by
  obtain ⟨χ⟩ := hQ.nonempty_mulEquiv_QM
  set ρ : ↥H →* MulAut ↥Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hQn) with hρdef
  have hρ : ∀ (g : ↥H) (q : ↥Q), ((ρ g q : ↥Q) : G) = (g : G) * q * (g : G)⁻¹ := fun g q => by
    rw [hρdef, MonoidHom.comp_apply, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  set θ : ↥H →* Equiv.Perm (Fin 5) :=
    linePermHom.comp ((MulAut.congr χ).toMonoidHom.comp ρ) with hθdef
  refine ⟨θ, ?_⟩
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro hg
    have hg' : linePerm ((MulAut.congr χ).toMonoidHom (ρ g)) = 1 := hg
    obtain ⟨p, hp⟩ := eq_conj_of_linePerm_eq_one hg'
    set q : ↥Q := χ.symm p with hq
    have hconj : ∀ r : ↥Q, (g : G) * r * (g : G)⁻¹ = (q : G) * r * (q : G)⁻¹ := fun r => by
      have h1 := DFunLike.congr_fun hp (χ r)
      rw [MulAut.conj_apply] at h1
      have h2 : χ (ρ g r) = χ (q * r * q⁻¹) := by
        rw [map_mul, map_mul, map_inv, hq, MulEquiv.apply_symm_apply]
        simpa [MulAut.congr_apply] using h1
      have h3 := congrArg (fun w : ↥Q => (w : G)) (χ.injective h2)
      rw [← hρ]
      exact h3
    have hmem : (q : G)⁻¹ * (g : G) ∈ Q := by
      apply hC
      · exact H.mul_mem (H.inv_mem (hQH q.2)) g.2
      · intro r hr
        have h1 := hconj ⟨r, hr⟩
        calc (q : G)⁻¹ * (g : G) * r = (q : G)⁻¹ * ((g : G) * r * (g : G)⁻¹) * (g : G) := by group
          _ = (q : G)⁻¹ * ((q : G) * r * (q : G)⁻¹) * (g : G) := by rw [h1]
          _ = r * ((q : G)⁻¹ * (g : G)) := by group
    have hg2 : (g : G) = (q : G) * ((q : G)⁻¹ * (g : G)) := by group
    rw [hg2]
    exact Q.mul_mem q.2 hmem
  · intro hg
    have hρq : ρ g = MulAut.conj (⟨(g : G), hg⟩ : ↥Q) := by
      refine MulEquiv.ext fun r => Subtype.ext ?_
      rw [hρ, MulAut.conj_apply]
      rfl
    have : (MulAut.congr χ).toMonoidHom (ρ g) = MulAut.conj (χ ⟨(g : G), hg⟩) := by
      refine MulEquiv.ext fun p => ?_
      rw [hρq]
      simp [MulAut.congr_apply, MulAut.conj_apply]
    show linePerm ((MulAut.congr χ).toMonoidHom (ρ g)) = 1
    rw [this, linePerm_conj']

theorem card_eq_mul_card_range {H Q : Subgroup G} (hQH : Q ≤ H) (hQ : IsQ8D8 ↥Q)
    {θ : ↥H →* Equiv.Perm (Fin 5)} (hker : θ.ker = Q.subgroupOf H) :
    Nat.card H = 32 * Nat.card θ.range := by
  have h1 := Subgroup.card_ker_mul_card_range θ
  rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQH).toEquiv, hQ.1] at h1
  exact h1.symm

theorem card_range_dvd {H : Type*} [Group H] (θ : H →* Equiv.Perm (Fin 5)) :
    Nat.card θ.range ∣ 120 := by
  have := Subgroup.card_subgroup_dvd_card θ.range
  rw [Nat.card_perm, Nat.card_fin] at this
  exact this

end Action

end S1421QA17

end CFSG.Quasithin
