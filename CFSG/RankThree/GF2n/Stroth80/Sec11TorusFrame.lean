module

public import CFSG.RankThree.GF2n.Stroth80.Ctx
public import CFSG.Timmesfeld.ARS.NaturalModule
import CFSG.RankThree.GF2n.Smith81.Lin26Torus
import CFSG.RankThree.GF2n.Stroth80.Sec11TorusComm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Frame

variable {G : Type} [Group G]

structure LBFrame (Q Z B : Subgroup G) where
  m : ℕ
  φ : ↥(Q ⊔ QB B) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 m)
  ψ : ↥(Z ⊔ B) ≃* Multiplicative (Fin 2 → GaloisField 2 m)
  card : Nat.card Z = 2 ^ m
  surj : Function.Surjective φ
  compat : ∀ (z : ↥(Q ⊔ QB B)) (w w' : ↥(Z ⊔ B)), (w' : G) = (z : G) * w * (z : G)⁻¹ →
    Multiplicative.toAdd (ψ w') =
      (φ z : Matrix (Fin 2) (Fin 2) (GaloisField 2 m)) *ᵥ Multiplicative.toAdd (ψ w)
  up : (Q.subgroupOf (Q ⊔ QB B)).map φ = Timmesfeld.upperUnipotent (GaloisField 2 m)
  low : ((QB B).subgroupOf (Q ⊔ QB B)).map φ = Timmesfeld.lowerUnipotent (GaloisField 2 m)
  memZ : ∀ w : ↥(Z ⊔ B), (w : G) ∈ Z ↔ Multiplicative.toAdd (ψ w) 1 = 0

abbrev LBFrame.K {Q Z B : Subgroup G} (fr : LBFrame Q Z B) : Type := GaloisField 2 fr.m

theorem conjSubgroup_inv_swap {n : G} {Z B : Subgroup G} (hZ : conjSubgroup n Z = B)
    (hB : conjSubgroup n B = Z) : conjSubgroup n⁻¹ Z = B ∧ conjSubgroup n⁻¹ B = Z := by
  constructor
  · rw [← hB, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  · rw [← hZ, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]

namespace LBFrame

variable {Q Z B : Subgroup G} (fr : LBFrame Q Z B)

theorem exists_lbRootU (t : fr.K) :
    ∃ x : G, ∃ hx : x ∈ Q, fr.φ ⟨x, Subgroup.mem_sup_left hx⟩ =
      Timmesfeld.RankOne.upperElt fr.K t := by
  have h : Timmesfeld.RankOne.upperElt fr.K t ∈ Timmesfeld.upperUnipotent fr.K :=
    (Timmesfeld.RankOne.mem_upperUnipotent_iff fr.K).2 ⟨t, rfl⟩
  rw [← fr.up] at h
  obtain ⟨g, hg, hgt⟩ := Subgroup.mem_map.mp h
  exact ⟨g, Subgroup.mem_subgroupOf.mp hg, hgt⟩

theorem exists_lbRootL (s : fr.K) :
    ∃ u : G, ∃ hu : u ∈ QB B, fr.φ ⟨u, Subgroup.mem_sup_right hu⟩ =
      Timmesfeld.RankOne.lowerElt fr.K s := by
  have h : Timmesfeld.RankOne.lowerElt fr.K s ∈ Timmesfeld.lowerUnipotent fr.K :=
    (Timmesfeld.RankOne.mem_lowerUnipotent_iff fr.K).2 ⟨s, rfl⟩
  rw [← fr.low] at h
  obtain ⟨g, hg, hgs⟩ := Subgroup.mem_map.mp h
  exact ⟨g, Subgroup.mem_subgroupOf.mp hg, hgs⟩

@[expose] noncomputable def lbRootU (t : fr.K) : G := (fr.exists_lbRootU t).choose

@[expose] noncomputable def lbRootL (s : fr.K) : G := (fr.exists_lbRootL s).choose

theorem lbRootU_mem (t : fr.K) : fr.lbRootU t ∈ Q := (fr.exists_lbRootU t).choose_spec.choose

theorem lbRootL_mem (s : fr.K) : fr.lbRootL s ∈ QB B := (fr.exists_lbRootL s).choose_spec.choose

theorem phi_lbRootU (t : fr.K) :
    fr.φ ⟨fr.lbRootU t, Subgroup.mem_sup_left (fr.lbRootU_mem t)⟩ =
      Timmesfeld.RankOne.upperElt fr.K t :=
  (fr.exists_lbRootU t).choose_spec.choose_spec

theorem phi_lbRootL (s : fr.K) :
    fr.φ ⟨fr.lbRootL s, Subgroup.mem_sup_right (fr.lbRootL_mem s)⟩ =
      Timmesfeld.RankOne.lowerElt fr.K s :=
  (fr.exists_lbRootL s).choose_spec.choose_spec

theorem exists_phi_eq_upperElt {x : G} (hx : x ∈ Q) :
    ∃ t : fr.K, fr.φ ⟨x, Subgroup.mem_sup_left hx⟩ = Timmesfeld.RankOne.upperElt fr.K t := by
  have h : fr.φ ⟨x, Subgroup.mem_sup_left hx⟩ ∈ Timmesfeld.upperUnipotent fr.K := by
    rw [← fr.up]
    exact Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  exact (Timmesfeld.RankOne.mem_upperUnipotent_iff fr.K).1 h

theorem exists_phi_eq_lowerElt {u : G} (hu : u ∈ QB B) :
    ∃ s : fr.K, fr.φ ⟨u, Subgroup.mem_sup_right hu⟩ = Timmesfeld.RankOne.lowerElt fr.K s := by
  have h : fr.φ ⟨u, Subgroup.mem_sup_right hu⟩ ∈ Timmesfeld.lowerUnipotent fr.K := by
    rw [← fr.low]
    exact Subgroup.mem_map.mpr ⟨_, Subgroup.mem_subgroupOf.mpr hu, rfl⟩
  exact (Timmesfeld.RankOne.mem_lowerUnipotent_iff fr.K).1 h

theorem diag_fix_Z (g : ↥(Q ⊔ QB B)) (c : fr.Kˣ)
    (hg : fr.φ g = Timmesfeld.ARS.NaturalModule.diagElt c) {v : G} (hv : v ∈ Z)
    (hgv : (g : G) * v = v * g) : c = 1 ∨ v = 1 := by
  have hv' : v ∈ Z ⊔ B := Subgroup.mem_sup_left hv
  have e := fr.compat g ⟨v, hv'⟩ ⟨v, hv'⟩
    (show v = (g : G) * v * (g : G)⁻¹ by rw [hgv]; group)
  rw [hg, Timmesfeld.ARS.NaturalModule.diagElt_mulVec] at e
  have h1 := (fr.memZ ⟨v, hv'⟩).mp hv
  have h0 := congrFun e 0
  simp only [Matrix.cons_val_zero] at h0
  by_cases hx : Multiplicative.toAdd (fr.ψ ⟨v, hv'⟩) 0 = 0
  · right
    have hψ : fr.ψ ⟨v, hv'⟩ = fr.ψ 1 := by
      rw [map_one]
      apply Multiplicative.toAdd.injective
      funext i
      fin_cases i
      · exact hx
      · exact h1
    exact congrArg Subtype.val (fr.ψ.injective hψ)
  · left
    apply Units.ext
    have h2 : ((c : fr.K) - 1) * Multiplicative.toAdd (fr.ψ ⟨v, hv'⟩) 0 = 0 := by
      rw [sub_mul, ← h0, one_mul, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hx

@[expose] noncomputable def lbWeylU (t : fr.K) : G := fr.lbRootU t * fr.lbRootL t⁻¹ * fr.lbRootU t

@[expose] noncomputable def lbWeylL (t : fr.K) : G := fr.lbRootL t * fr.lbRootU t⁻¹ * fr.lbRootL t

theorem lbWeylU_mem (t : fr.K) : fr.lbWeylU t ∈ Q ⊔ QB B :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left (fr.lbRootU_mem t))
    (Subgroup.mem_sup_right (fr.lbRootL_mem t⁻¹))) (Subgroup.mem_sup_left (fr.lbRootU_mem t))

theorem lbWeylL_mem (t : fr.K) : fr.lbWeylL t ∈ Q ⊔ QB B :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right (fr.lbRootL_mem t))
    (Subgroup.mem_sup_left (fr.lbRootU_mem t⁻¹))) (Subgroup.mem_sup_right (fr.lbRootL_mem t))

theorem phi_lbWeylU {t : fr.K} (ht : t ≠ 0) :
    (fr.φ ⟨fr.lbWeylU t, fr.lbWeylU_mem t⟩ : Matrix (Fin 2) (Fin 2) fr.K) = !![0, t; t⁻¹, 0] := by
  have e : (⟨fr.lbWeylU t, fr.lbWeylU_mem t⟩ : ↥(Q ⊔ QB B)) =
      ⟨fr.lbRootU t, Subgroup.mem_sup_left (fr.lbRootU_mem t)⟩ *
        ⟨fr.lbRootL t⁻¹, Subgroup.mem_sup_right (fr.lbRootL_mem t⁻¹)⟩ *
        ⟨fr.lbRootU t, Subgroup.mem_sup_left (fr.lbRootU_mem t)⟩ := rfl
  rw [e, map_mul, map_mul, fr.phi_lbRootU, fr.phi_lbRootL, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Timmesfeld.ARS.NaturalModule.coe_upperElt,
    Timmesfeld.ARS.NaturalModule.coe_lowerElt]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ht, CharTwo.add_self_eq_zero]

theorem phi_lbWeylL {t : fr.K} (ht : t ≠ 0) :
    (fr.φ ⟨fr.lbWeylL t, fr.lbWeylL_mem t⟩ : Matrix (Fin 2) (Fin 2) fr.K) = !![0, t⁻¹; t, 0] := by
  have e : (⟨fr.lbWeylL t, fr.lbWeylL_mem t⟩ : ↥(Q ⊔ QB B)) =
      ⟨fr.lbRootL t, Subgroup.mem_sup_right (fr.lbRootL_mem t)⟩ *
        ⟨fr.lbRootU t⁻¹, Subgroup.mem_sup_left (fr.lbRootU_mem t⁻¹)⟩ *
        ⟨fr.lbRootL t, Subgroup.mem_sup_right (fr.lbRootL_mem t)⟩ := rfl
  rw [e, map_mul, map_mul, fr.phi_lbRootU, fr.phi_lbRootL, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Timmesfeld.ARS.NaturalModule.coe_upperElt,
    Timmesfeld.ARS.NaturalModule.coe_lowerElt]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, ht, CharTwo.add_self_eq_zero]

theorem phi_conj_lbWeylU_one (s : fr.K)
    (h : fr.lbWeylU 1 * fr.lbRootU s * (fr.lbWeylU 1)⁻¹ ∈ Q ⊔ QB B) :
    fr.φ ⟨fr.lbWeylU 1 * fr.lbRootU s * (fr.lbWeylU 1)⁻¹, h⟩ =
      Timmesfeld.RankOne.lowerElt fr.K s := by
  have e : (⟨fr.lbWeylU 1 * fr.lbRootU s * (fr.lbWeylU 1)⁻¹, h⟩ : ↥(Q ⊔ QB B)) =
      ⟨fr.lbWeylU 1, fr.lbWeylU_mem 1⟩ *
        ⟨fr.lbRootU s, Subgroup.mem_sup_left (fr.lbRootU_mem s)⟩ *
        (⟨fr.lbWeylU 1, fr.lbWeylU_mem 1⟩ : ↥(Q ⊔ QB B))⁻¹ := rfl
  have hw := fr.phi_lbWeylU (one_ne_zero : (1 : fr.K) ≠ 0)
  ext i j
  rw [e, map_mul, map_mul, map_inv, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, hw, fr.phi_lbRootU,
    Timmesfeld.ARS.NaturalModule.coe_upperElt, Timmesfeld.ARS.NaturalModule.coe_lowerElt,
    Matrix.adjugate_fin_two]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, CharTwo.neg_eq]

@[expose] noncomputable def lbTorusElt (t : fr.K) : G := fr.lbWeylU t * fr.lbWeylL 1

theorem lbTorusElt_mem (t : fr.K) : fr.lbTorusElt t ∈ Q ⊔ QB B :=
  Subgroup.mul_mem _ (fr.lbWeylU_mem t) (fr.lbWeylL_mem 1)

theorem phi_lbTorusElt {t : fr.K} (ht : t ≠ 0) :
    fr.φ ⟨fr.lbTorusElt t, fr.lbTorusElt_mem t⟩ =
      Timmesfeld.ARS.NaturalModule.diagElt (Units.mk0 t ht) := by
  have e : (⟨fr.lbTorusElt t, fr.lbTorusElt_mem t⟩ : ↥(Q ⊔ QB B)) =
      ⟨fr.lbWeylU t, fr.lbWeylU_mem t⟩ * ⟨fr.lbWeylL 1, fr.lbWeylL_mem 1⟩ := rfl
  ext i j
  rw [e, map_mul, Matrix.SpecialLinearGroup.coe_mul, fr.phi_lbWeylU ht,
    fr.phi_lbWeylL (one_ne_zero : (1 : fr.K) ≠ 0), Timmesfeld.ARS.NaturalModule.coe_diagElt]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end LBFrame

end Frame

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.nonempty_lbFrame (hc : Ctx M Q Z B) : Nonempty (LBFrame Q Z B) := by
  obtain ⟨m, φ, ψ, hm, hs, hcompat, hup, hlow, hV⟩ := Smith81.Ctx.inducesSL2' hc
  exact ⟨⟨m, φ, ψ, hm, hs, hcompat, hup, hlow, hV⟩⟩

theorem Ctx.conj_PB_mem_P_of_swap (hc : Ctx M Q Z B) {n : G} (hZ : conjSubgroup n Z = B)
    (hB : conjSubgroup n B = Z) {a : G} (ha : a ∈ QB B ⊓ M) :
    n * a * n⁻¹ ∈ Q ⊓ Subgroup.centralizer (B : Set G) := by
  have ha' : a ∈ QB B ⊓ Subgroup.centralizer (Z : Set G) := (Ctx.QB_inf_M_eq hc).le ha
  have hmem : n * a * n⁻¹ ∈ conjSubgroup n (QB B ⊓ Subgroup.centralizer (Z : Set G)) :=
    mem_conjSubgroup.mpr (by rw [show n⁻¹ * (n * a * n⁻¹) * n = a by group]; exact ha')
  rwa [conjSubgroup_inf, conjSubgroup_centralizer, (hc.conj_Q_QB_of_swap hZ hB).2, hZ] at hmem

theorem Ctx.conj_P_mem_PB_of_swap (hc : Ctx M Q Z B) {n : G} (hZ : conjSubgroup n Z = B)
    (hB : conjSubgroup n B = Z) {p : G} (hp : p ∈ Q ⊓ Subgroup.centralizer (B : Set G)) :
    n * p * n⁻¹ ∈ QB B ⊓ M := by
  have hmem : n * p * n⁻¹ ∈ conjSubgroup n (Q ⊓ Subgroup.centralizer (B : Set G)) :=
    mem_conjSubgroup.mpr (by rw [show n⁻¹ * (n * p * n⁻¹) * n = p by group]; exact hp)
  rw [conjSubgroup_inf, conjSubgroup_centralizer, (hc.conj_Q_QB_of_swap hZ hB).1, hB] at hmem
  rw [Ctx.QB_inf_M_eq hc]
  exact hmem

namespace LBFrame

variable (fr : LBFrame Q Z B)

theorem mem_centralizer_of_phi_eq (hc : Ctx M Q Z B) {g g' : ↥(Q ⊔ QB B)}
    (h : fr.φ g = fr.φ g') :
    (g : G)⁻¹ * g' ∈ Subgroup.centralizer ((Z ⊔ B : Subgroup G) : Set G) := by
  have hN : Q ⊔ QB B ≤ Subgroup.normalizer ((Z ⊔ B : Subgroup G) : Set G) :=
    sup_le (Smith81.Ctx.Q_le_normalizer_ZB hc) (Smith81.Ctx.QB_le_normalizer_ZB hc)
  refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
  have hc1 : (g : G) * w * (g : G)⁻¹ ∈ Z ⊔ B :=
    (Subgroup.mem_normalizer_iff.mp (hN g.2) w).mp hw
  have hc2 : (g' : G) * w * (g' : G)⁻¹ ∈ Z ⊔ B :=
    (Subgroup.mem_normalizer_iff.mp (hN g'.2) w).mp hw
  have e1 := fr.compat g ⟨w, hw⟩ ⟨_, hc1⟩ rfl
  have e2 := fr.compat g' ⟨w, hw⟩ ⟨_, hc2⟩ rfl
  rw [h, ← e2] at e1
  have e3 : (g : G) * w * (g : G)⁻¹ = (g' : G) * w * (g' : G)⁻¹ :=
    congrArg Subtype.val (fr.ψ.injective (Multiplicative.toAdd.injective e1))
  calc w * ((g : G)⁻¹ * g') = (g : G)⁻¹ * ((g : G) * w * (g : G)⁻¹) * g' := by group
    _ = (g : G)⁻¹ * ((g' : G) * w * (g' : G)⁻¹) * g' := by rw [e3]
    _ = (g : G)⁻¹ * g' * w := by group

private theorem coord_zero_of_mem_B (hc : Ctx M Q Z B) (w : ↥(Z ⊔ B)) (hb : (w : G) ∈ B) :
    Multiplicative.toAdd (fr.ψ w) 0 = 0 := by
  have hu := fr.lbRootL_mem 1
  have e0 : (w : G) = fr.lbRootL 1 * w * (fr.lbRootL 1)⁻¹ := by
    rw [← Smith81.Ctx.B_central_QB hc hb hu]
    group
  have e := fr.compat ⟨fr.lbRootL 1, Subgroup.mem_sup_right hu⟩ w w e0
  rw [fr.phi_lbRootL, Timmesfeld.ARS.NaturalModule.lowerElt_mulVec] at e
  have h1 := congrFun e 1
  simpa using h1

theorem mem_B_iff_coord (hc : Ctx M Q Z B) (w : ↥(Z ⊔ B)) :
    (w : G) ∈ B ↔ Multiplicative.toAdd (fr.ψ w) 0 = 0 := by
  refine ⟨coord_zero_of_mem_B fr hc w, fun h0 => ?_⟩
  obtain ⟨z, hz, b, hb, hw⟩ := (Smith81.Ctx.mem_sup_iff hc).mp w.2
  have hzb : w = ⟨z, Subgroup.mem_sup_left hz⟩ * ⟨b, Subgroup.mem_sup_right hb⟩ := Subtype.ext hw
  have hb0 := coord_zero_of_mem_B fr hc ⟨b, Subgroup.mem_sup_right hb⟩ hb
  have hz1 := (fr.memZ ⟨z, Subgroup.mem_sup_left hz⟩).mp hz
  have hz0 : Multiplicative.toAdd (fr.ψ ⟨z, Subgroup.mem_sup_left hz⟩) 0 = 0 := by
    rw [hzb, map_mul, toAdd_mul, Pi.add_apply, hb0, add_zero] at h0
    exact h0
  have hψ : fr.ψ ⟨z, Subgroup.mem_sup_left hz⟩ = fr.ψ 1 := by
    rw [map_one]
    apply Multiplicative.toAdd.injective
    funext i
    fin_cases i
    · exact hz0
    · exact hz1
  have hz' : z = 1 := congrArg Subtype.val (fr.ψ.injective hψ)
  rw [hw, hz', one_mul]
  exact hb

theorem conj_swap_of_antidiag (hc : Ctx M Q Z B) (g : ↥(Q ⊔ QB B))
    (h00 : (fr.φ g : Matrix (Fin 2) (Fin 2) fr.K) 0 0 = 0)
    (h11 : (fr.φ g : Matrix (Fin 2) (Fin 2) fr.K) 1 1 = 0) :
    conjSubgroup (g : G) Z = B ∧ conjSubgroup (g : G) B = Z := by
  have hN := sup_le (Smith81.Ctx.Q_le_normalizer_ZB hc) (Smith81.Ctx.QB_le_normalizer_ZB hc) g.2
  have hW : ∀ x : G, (g : G)⁻¹ * x * g ∈ Z ⊔ B → x ∈ Z ⊔ B := fun x hx => by
    have := (Subgroup.mem_normalizer_iff.mp hN _).mp hx
    rwa [show (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ = x by group] at this
  have he : ∀ x : G, ∀ hx : (g : G)⁻¹ * x * g ∈ Z ⊔ B,
      Multiplicative.toAdd (fr.ψ ⟨x, hW x hx⟩) =
        (fr.φ g : Matrix (Fin 2) (Fin 2) fr.K) *ᵥ Multiplicative.toAdd (fr.ψ ⟨_, hx⟩) :=
    fun x hx => fr.compat g ⟨_, hx⟩ ⟨x, hW x hx⟩
      (show x = (g : G) * ((g : G)⁻¹ * x * g) * (g : G)⁻¹ by group)
  have hZB : conjSubgroup (g : G) Z ≤ B := fun x hx => by
    rw [mem_conjSubgroup] at hx
    have h1 := (fr.memZ ⟨_, Subgroup.mem_sup_left hx⟩).mp hx
    refine (fr.mem_B_iff_coord hc ⟨x, hW x (Subgroup.mem_sup_left hx)⟩).mpr ?_
    rw [he x (Subgroup.mem_sup_left hx)]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h00, h1]
  have hBZ : conjSubgroup (g : G) B ≤ Z := fun x hx => by
    rw [mem_conjSubgroup] at hx
    have h1 := (fr.mem_B_iff_coord hc ⟨_, Subgroup.mem_sup_right hx⟩).mp hx
    refine (fr.memZ ⟨x, hW x (Subgroup.mem_sup_right hx)⟩).mpr ?_
    rw [he x (Subgroup.mem_sup_right hx)]
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h11, h1]
  have hcB : Nat.card B = Nat.card Z := by
    obtain ⟨g0, hg0⟩ := hc.conj
    rw [hg0]
    exact Subgroup.card_map_of_injective (MulAut.conj g0).injective
  have hcg : ∀ S : Subgroup G, Nat.card (conjSubgroup (g : G) S) = Nat.card S := fun S =>
    Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective
  exact ⟨Subgroup.eq_of_le_of_card_ge hZB (by rw [hcg, hcB]),
    Subgroup.eq_of_le_of_card_ge hBZ (by rw [hcg, hcB])⟩

theorem diag_normalizes (hc : Ctx M Q Z B) (g : ↥(Q ⊔ QB B)) (c : fr.Kˣ)
    (hg : fr.φ g = Timmesfeld.ARS.NaturalModule.diagElt c) :
    (g : G) ∈ Subgroup.normalizer (Z : Set G) ∧ (g : G) ∈ Subgroup.normalizer (B : Set G) := by
  have hN := sup_le (Smith81.Ctx.Q_le_normalizer_ZB hc) (Smith81.Ctx.QB_le_normalizer_ZB hc) g.2
  have hW : ∀ x : G, x ∈ Z ⊔ B → (g : G) * x * (g : G)⁻¹ ∈ Z ⊔ B := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hN x).mp hx
  have he : ∀ x : G, ∀ hx : x ∈ Z ⊔ B,
      Multiplicative.toAdd (fr.ψ ⟨_, hW x hx⟩) =
        ![(c : fr.K) * Multiplicative.toAdd (fr.ψ ⟨x, hx⟩) 0,
          ((c⁻¹ : fr.Kˣ) : fr.K) * Multiplicative.toAdd (fr.ψ ⟨x, hx⟩) 1] := fun x hx => by
    rw [fr.compat g ⟨x, hx⟩ ⟨_, hW x hx⟩ rfl, hg,
      Timmesfeld.ARS.NaturalModule.diagElt_mulVec]
  constructor
  · refine Subgroup.mem_normalizer_fintype fun z hz => ?_
    have h1 := (fr.memZ ⟨z, Subgroup.mem_sup_left hz⟩).mp hz
    refine (fr.memZ ⟨_, hW z (Subgroup.mem_sup_left hz)⟩).mpr ?_
    rw [he z (Subgroup.mem_sup_left hz)]
    simp [h1]
  · refine Subgroup.mem_normalizer_fintype fun b hb => ?_
    have h1 := (fr.mem_B_iff_coord hc ⟨b, Subgroup.mem_sup_right hb⟩).mp hb
    refine (fr.mem_B_iff_coord hc ⟨_, hW b (Subgroup.mem_sup_right hb)⟩).mpr ?_
    rw [he b (Subgroup.mem_sup_right hb)]
    simp [h1]

theorem exists_orderOf_of_phi_eq_one (hc : Ctx M Q Z B) (g : ↥(Q ⊔ QB B)) (hg : fr.φ g = 1) :
    ∃ f : ℕ, orderOf (g : G) = 2 ^ f := by
  have hC : (g : G) ∈ Subgroup.centralizer ((Z ⊔ B : Subgroup G) : Set G) := by
    have := fr.mem_centralizer_of_phi_eq hc (g := 1) (g' := g) (by rw [hg, map_one])
    simpa using this
  obtain ⟨-, -, -, hCeq⟩ := hc.inducesSL2
  have hmem : (g : G) ∈ inSubgroup (pCore 2) (Q ⊔ QB B) := by
    rw [← hCeq]
    exact ⟨g.2, hC⟩
  obtain ⟨w', hw', hww'⟩ := Subgroup.mem_map.mp hmem
  obtain ⟨f, hf⟩ := (IsPGroup.iff_orderOf.mp
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(Q ⊔ QB B)))) ⟨w', hw'⟩
  refine ⟨f, ?_⟩
  rw [← hww']
  have e1 : orderOf (⟨w', hw'⟩ : ↥(pCore 2 ↥(Q ⊔ QB B))) = orderOf w' :=
    (Subgroup.orderOf_coe _).symm
  have e2 : orderOf ((Q ⊔ QB B).subtype w') = orderOf w' := Subgroup.orderOf_coe w'
  rw [e2, ← e1, hf]

theorem conj_lbWeylU (hc : Ctx M Q Z B) {t : fr.K} (ht : t ≠ 0) :
    conjSubgroup (fr.lbWeylU t) Z = B ∧ conjSubgroup (fr.lbWeylU t) B = Z := by
  have h := fr.phi_lbWeylU ht
  exact fr.conj_swap_of_antidiag hc ⟨fr.lbWeylU t, fr.lbWeylU_mem t⟩ (by rw [h]; rfl)
    (by rw [h]; rfl)

theorem conj_lbWeylL (hc : Ctx M Q Z B) {t : fr.K} (ht : t ≠ 0) :
    conjSubgroup (fr.lbWeylL t) Z = B ∧ conjSubgroup (fr.lbWeylL t) B = Z := by
  have h := fr.phi_lbWeylL ht
  exact fr.conj_swap_of_antidiag hc ⟨fr.lbWeylL t, fr.lbWeylL_mem t⟩ (by rw [h]; rfl)
    (by rw [h]; rfl)

end LBFrame

end CFSG.RankThree.GF2n.Stroth80
