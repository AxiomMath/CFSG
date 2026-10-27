module

public import CFSG.Quasithin.EmptyFaithful.S146zClaim

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin

section Rank

variable {G : Type} [Group G] [Finite G]

theorem mIdx_centralizerMod_zpowers_le {Z U A₁ D : Subgroup G} {x : G}
    (hUab : IsElemAbelian 2 U) (hUN : U ≤ Subgroup.normalizer (Z : Set G)) (hDU : D ≤ U)
    (hA₁c : Nat.card A₁ = 2) (hDN : D ≤ Subgroup.normalizer (A₁ : Set G)) (hx2 : x ^ 2 = 1)
    (hxA : ∀ a ∈ A₁, a * x = x * a) (hDx : ∀ d ∈ D, d * x * d⁻¹ * x⁻¹ ∈ A₁) :
    mIdx U (centralizerMod Z U (Subgroup.zpowers x)) ≤ mIdx U D + 1 := by
  classical
  have hUp2 : IsPGroup 2 U := isPGroup_of_isElemAbelian hUab
  have hDp2 : IsPGroup 2 D := hUp2.to_le hDU
  set Y : Subgroup G := Subgroup.zpowers x with hY
  have hYcard : Nat.card Y ≤ 2 := by
    rw [hY, Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hx2)
  have hYab : IsElemAbelian 2 Y := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      apply Subtype.ext
      show (a : G) * (b : G) = (b : G) * (a : G)
      rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have h2 : x ^ (2 : ℤ) = 1 := by simpa using hx2
      rw [sq, ← zpow_add, ← two_mul, zpow_mul, h2, one_zpow]
  have hYx : ∀ y ∈ Y, y = 1 ∨ y = x := by
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h2 : x ^ (2 : ℤ) = 1 := by simpa using hx2
    obtain ⟨k, hk | hk⟩ := Int.even_or_odd' i
    · left; rw [hk, zpow_mul, h2, one_zpow]
    · right; rw [hk, zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]
  have hcomm : ⁅D, Y⁆ ≤ A₁ := by
    rw [Subgroup.commutator_le]
    intro d hd y hy
    rcases hYx y hy with rfl | rfl
    · simp
    · exact hDx d hd
  have hCXc : A₁ ≤ Subgroup.centralizer (D : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hdN : d ∈ Subgroup.normalizer (A₁ : Set G) := hDN hd
    rw [normalizer_eq_centralizer_of_card_eq_two hA₁c] at hdN
    exact (Subgroup.mem_centralizer_iff.mp hdN a ha).symm
  have hCYc : A₁ ≤ Subgroup.centralizer (Y : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases hYx y hy with rfl | rfl
    · simp
    · exact (hxA a ha).symm
  have hpair := relIndex_eq_of_commutator_le (X := D) (Y := Y) (C := A₁) hYab hA₁c hcomm hCXc hCYc
  set CD := D ⊓ Subgroup.centralizer (Y : Set G) with hCD
  set CU := centralizerMod Z U Y with hCU
  have hCDle : CD ≤ CU := by
    intro d hd
    refine ⟨hDU hd.1, hUN (hDU hd.1), fun e he => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp hd.2 e he
    have e1 : d * e * d⁻¹ * e⁻¹ = 1 := by
      calc d * e * d⁻¹ * e⁻¹ = (e * d) * d⁻¹ * e⁻¹ := by rw [this]
        _ = 1 := by group
    rw [e1]; exact Z.one_mem
  have hf1 : mIdx U CU ≤ mIdx U D + mIdx D CD := by
    have h1 : mIdx U CU ≤ mIdx U CD := ThreeC.mIdx_anti_of_le (X := U) hCDle
    have h2 : mIdx U CD = mIdx U D + mIdx D CD := ThreeC.mIdx_add hUp2 hDU (inf_le_left : CD ≤ D)
    omega
  have hYp2 : IsPGroup 2 Y := isPGroup_of_isElemAbelian hYab
  have hmD : mIdx D CD ≤ 1 := by
    have e1 := HypF98.relIndex_eq_two_pow_mIdx (Y := CD) hDp2
    have e2 := HypF98.relIndex_eq_two_pow_mIdx (Y := Y ⊓ Subgroup.centralizer (D : Set G)) hYp2
    have hle : (Y ⊓ Subgroup.centralizer (D : Set G)).relIndex Y ≤ 2 := by
      refine le_trans ?_ hYcard
      have h3 := Subgroup.relIndex_mul_card (Y ⊓ Subgroup.centralizer (D : Set G)) Y
      rw [inf_eq_left.mpr inf_le_left] at h3
      have hpos : 0 < Nat.card ↥(Y ⊓ Subgroup.centralizer (D : Set G)) := Nat.card_pos
      calc (Y ⊓ Subgroup.centralizer (D : Set G)).relIndex Y
          ≤ (Y ⊓ Subgroup.centralizer (D : Set G)).relIndex Y *
              Nat.card ↥(Y ⊓ Subgroup.centralizer (D : Set G)) := Nat.le_mul_of_pos_right _ hpos
        _ = Nat.card Y := h3
    rw [e1, e2] at hpair
    have hm := Nat.pow_right_injective (le_refl 2) hpair
    rw [e2] at hle
    have h4 : 2 ^ mIdx Y (Y ⊓ Subgroup.centralizer (D : Set G)) ≤ 2 ^ 1 := by simpa using hle
    have h5 := (Nat.pow_le_pow_iff_right (by norm_num)).mp h4
    omega
  omega

end Rank

section Core

@[expose] def Input14624A6Rk : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M → HypB146 T M →
    ∀ (K U₁ U₂ : Subgroup G) (s u : G), Ctx24 T M K U₁ U₂ s u → KbarIsA6 K → K = perfectCore (mcOf T) →
      ∀ X : Subgroup G, QCrit (quasithinOmegaOneCenter T) (VZ T M) (mcOf T) X →
        2 * mIdx X (X ⊓ pCoreOf 2 (mcOf T)) =
            mIdx (conjClosure (VZ T M) (mcOf T))
              (centralizerMod (quasithinOmegaOneCenter T) (conjClosure (VZ T M) (mcOf T)) X) ∧
          ∃ x ∈ X, mIdx X (X ⊓ pCoreOf 2 (mcOf T)) + 2 ≤
            mIdx (conjClosure (VZ T M) (mcOf T))
              (centralizerMod (quasithinOmegaOneCenter T) (conjClosure (VZ T M) (mcOf T))
                (Subgroup.zpowers x))

end Core

section Main

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem input14624Two_of_a6rk (h : Input14624A6Rk) : Input14624Two := by
  intro G _ _ T M S hB K U₁ U₂ s u hctx γ γ' g hgeom hK3
  by_contra hnot
  have hA6 : KbarIsA6 K := by
    obtain ⟨-, -, -, -, c21, -⟩ := hctx
    rcases c21 with ⟨-, h1⟩ | ⟨-, h1⟩ | ⟨Kp, -, -, -, -, -, h1, -⟩
    · rcases h1 with h1 | h1
      · exact absurd h1 hnot
      · exact h1
    · exact absurd h1 hnot
    · exact absurd h1 hnot
  obtain ⟨hsetup, hDlt, hpos, hle, hlt, -⟩ := hgeom
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hF98 := (S.lemma_14_5_14 (S.isHz_iff.mpr hG)).2
  have hpos' : 0 < mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G))
      (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) := lt_of_lt_of_le hpos hle
  obtain ⟨hQC, hEq⟩ := hF98.F916_2_aux hsetup hpos' hle
  obtain ⟨hr2, x, hxX, hxr⟩ := h G T M S hB K U₁ U₂ s u hctx hA6 hK3 _ hQC
  have hDγ := hF98.Dγ_eq_inf_pCoreOf hsetup
  rw [← hDγ] at hr2 hxr
  obtain ⟨hmD, -, hcomm, hA₁c, hA₁Z, -⟩ := hEq hr2
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) (mcOf T)) := hF98.F911_3
  have hUN : conjClosure (VZ T M) (mcOf T) ≤
      Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := S.conjClosure_le_normalizer_Z hG
  have hXab : IsElemAbelian 2 (F8.Uγ (VZ T M) (mcOf T) (g : G)) := hF98.isElemAbelian_Uγ
  have hDU : F8.DH (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G) ≤
      conjClosure (VZ T M) (mcOf T) := centralizerMod_le_left _ _ _
  have hDN : F8.DH (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G) ≤
      Subgroup.normalizer ((F8.A₁ (quasithinOmegaOneCenter T) (g : G) : Subgroup G) : Set G) :=
    fun d hd => hd.2.1
  have hA₁U := hF98.A₁_le_Uγ (g := g)
  have hx2 : x ^ 2 = 1 := hXab.2 x hxX
  have hxA : ∀ a ∈ F8.A₁ (quasithinOmegaOneCenter T) (g : G), a * x = x * a := fun a ha =>
    isElemAbelian_comm hXab (hA₁U ha) hxX
  have hDx : ∀ d ∈ F8.DH (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G),
      d * x * d⁻¹ * x⁻¹ ∈ F8.A₁ (quasithinOmegaOneCenter T) (g : G) := fun d hd =>
    hd.2.2 x hxX
  have hrank := mIdx_centralizerMod_zpowers_le (Z := quasithinOmegaOneCenter T) hUab hUN hDU hA₁c hDN
    hx2 hxA hDx
  omega

end Main

end CFSG.Quasithin
