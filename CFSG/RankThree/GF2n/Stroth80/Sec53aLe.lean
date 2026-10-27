module

public import CFSG.RankThree.GF2n.Stroth80.Sec53Hbound

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.vone_eq_inf_QB_sup (hc : Ctx M Q Z B) {n : ℕ} {t r : G} (hs : Sec5Hyp hc n t) :
    Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) =
      (Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t) ⊓ QB B) ⊔
        Vt M (LB M Q B) B Z t := by
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hVdef
  set V1 : Subgroup G := Vone Q B (conjSubgroup r B) V with hV1def
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hQV : Q ≤ Subgroup.normalizer (V : Set G) := by
    refine sec8_le_normalizer_of_conj fun x hx y hy => ?_
    have hc' : ⁅x, y⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hx (hVQ hy)
    rw [show x * y * x⁻¹ = ⁅x, y⁆ * y by rw [commutatorElement_def]; group]
    exact V.mul_mem (sec39_Z_le_Vt hc') hy
  apply le_antisymm
  · intro x hx
    have hx1 : x ∈ (Q ⊓ QB B) ⊔ V := hx.1
    obtain ⟨a, ha, v, hv, hxeq⟩ :=
      exists_mul_of_mem_sup_of_le_normalizer (H := Q ⊓ QB B) (K := V)
        (fun y hy => hQV hy.1) hx1
    have hvV1 : v ∈ V1 := by
      rw [hV1def]
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mem_sup_right hv, Subgroup.mem_sup_right hv⟩
    have haV1 : a ∈ V1 := by
      have h := V1.mul_mem hx (V1.inv_mem hvV1)
      have hx' : x * v⁻¹ = a := by rw [← hxeq]; group
      rwa [hx'] at h
    rw [← hxeq]
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨haV1, ha.2⟩) hv
  · intro x hx
    have hVleV1 : V ≤ V1 := by
      rw [hV1def]
      exact le_inf (le_sup_right (a := Q ⊓ QB B))
        (le_sup_right (a := Q ⊓ QB (conjSubgroup r B)))
    have hle : (V1 ⊓ QB B) ⊔ V ≤ V1 := sup_le inf_le_left hVleV1
    exact hle hx

theorem Ctx.card_vone_le (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h51 : Stroth51Statement) (hc : Ctx M Q Z B) {n m : ℕ} {t : G} (hs : Sec5Hyp hc n t) (hm : 2 ≤ m)
    (hV : SpMNat hc t m) {r : G} (hr : r ∈ Rt M (LB M Q B) t)
    (hplane : HypPlane Q Z B (conjSubgroup r B) t) :
    Nat.card ↥(Vone Q B (conjSubgroup r B) (Vt M (LB M Q B) B Z t))
      ≤ Nat.card ↥(Vt M (LB M Q B) B Z t) * Nat.card Z := by
  set V : Subgroup G := Vt M (LB M Q B) B Z t with hVdef
  set V1 : Subgroup G := Vone Q B (conjSubgroup r B) V with hV1def
  have hVkeep : SpMNat hc t m := hV
  have hsp : SpNat hc t := by
    obtain ⟨K, iF, iFin, hK, hrep⟩ := hVkeep
    exact ⟨K, iF, iFin, hK, m, hm, hrep⟩
  have hVQ : V ≤ Q := hc.Vt_le_Q t
  have hV1Q : V1 ≤ Q := vone_le_Q hVQ
  have hVtV1 : V ≤ V1 := le_inf le_sup_right le_sup_right
  have hZN : Z ≤ (QB B ⊓ M) ⊓ hc.CN t :=
    le_inf (le_inf hc.Z_le_QB.1 (hc.Z_le_Q.trans hc.hyp.Q_normal.1))
      (hc.Z_le_Q.trans (hc.Q_le_CN hs.mem))
  obtain ⟨S, hS⟩ := sec51_exists_subgroup ((QB B ⊓ M) ⊓ hc.CN t) Z hZN
  have hV1QB_le : V1 ⊓ QB B ≤ (Q ⊓ QB B) ⊓ S := by
    intro x hx
    have hx1 : x ∈ V1 := hx.1
    have hxQB : x ∈ QB B := hx.2
    have hxQ : x ∈ Q := hV1Q hx1
    refine ⟨⟨hxQ, hxQB⟩, ?_⟩
    change x ∈ S
    rw [hS x]
    intro l hl
    have hlx : ⁅l, x⁆ ∈ Z :=
      sec53_sp_comm_CN_vone_le_Z h34 h51 hc hs hsp hr hplane
        l hl.2 x hx1
    have := Z.inv_mem hlx
    rwa [commutatorElement_inv] at this
  have hbound := Ctx.card_inf_QB_S_le h34 hc hs hm hV S hS
  have hcardV1QB_le : Nat.card ↥(V1 ⊓ QB B) ≤ Nat.card Z ^ (2 * m + 1) := by
    refine le_trans ?_ hbound
    exact Nat.card_le_card_of_injective
      (fun x : ↥(V1 ⊓ QB B) => (⟨x.1, hV1QB_le x.2⟩ : ↥((Q ⊓ QB B) ⊓ S)))
      (fun a b h => Subtype.ext
        (congrArg (fun x : ↥((Q ⊓ QB B) ⊓ S) => (x : G)) h))
  have hVWnorm : V ≤ Subgroup.normalizer (V1 ⊓ QB B : Set G) := by
    intro v hv
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨hxV1, hxB⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hc.Q_le_normalizer_vone t (hVQ hv)) x).mp hxV1
    · have hxQ : x ∈ Q := hV1Q hxV1
      have hcomm : ⁅v, x⁆ ∈ (Z ⊔ B : Subgroup G) :=
        hc.comm_LB_inf_QB_mem_sup (sec39_Q_le_LB (hVQ hv)) ⟨hxQ, hxB⟩
      have hcommQB : ⁅v, x⁆ ∈ QB B := (sup_le hc.Z_le_QB.1 hc.B_le_QB) hcomm
      have e : v * x * v⁻¹ = ⁅v, x⁆ * x := by rw [commutatorElement_def]; group
      rw [e]
      exact (QB B).mul_mem hcommQB hxB
  have hprod :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := V) (K := V1 ⊓ QB B) hVWnorm
  rw [sup_comm] at hprod
  have hsup : (V1 ⊓ QB B) ⊔ V = V1 := by
    rw [hV1def, hVdef]
    exact (Ctx.vone_eq_inf_QB_sup hc hs).symm
  have hinf : V ⊓ (V1 ⊓ QB B) = V ⊓ QB B := by
    rw [← inf_assoc, inf_eq_left.mpr hVtV1]
  have hVinfQB : Nat.card ↥(V ⊓ QB B) = Nat.card Z ^ (2 * m) :=
    card_Vt_inf_QB_sp h34 hRoot hc hs hm hV
  have hVcard : Nat.card ↥V = Nat.card Z ^ (2 * m + 1) := SpMNat.card_V hV
  rw [hsup, hinf, hVinfQB] at hprod
  have harith : Nat.card ↥V * Nat.card Z ^ (2 * m + 1) =
      (Nat.card ↥V * Nat.card Z) * Nat.card Z ^ (2 * m) := by
    rw [hVcard, pow_succ (Nat.card Z) (2 * m)]
    ring
  have hle : Nat.card ↥V1 * Nat.card Z ^ (2 * m) ≤
      (Nat.card ↥V * Nat.card Z) * Nat.card Z ^ (2 * m) := by
    calc Nat.card ↥V1 * Nat.card Z ^ (2 * m)
        = Nat.card ↥V * Nat.card ↥(V1 ⊓ QB B) := hprod
      _ ≤ Nat.card ↥V * Nat.card Z ^ (2 * m + 1) :=
          Nat.mul_le_mul_left _ hcardV1QB_le
      _ = (Nat.card ↥V * Nat.card Z) * Nat.card Z ^ (2 * m) := harith
  exact Nat.le_of_mul_le_mul_right hle (pow_pos (Nat.card_pos (α := ↥Z)) (2 * m))

end CFSG.RankThree.GF2n.Stroth80
