module

public import CFSG.RankThree.PartOne.S13K.Row1At
public import CFSG.RankThree.PartOne.S13K.Comm134
public import CFSG.RankThree.PartOne.N143.JDiag

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.N143
open CFSG.RankThree.PartOne.KFOUT3 (SL3 Tor IsZeta diagSL permSL permSL_conj_rt rt ent ent_ext tSep
  tSep_mem cover_three)
open scoped commutatorElement

section Generation

variable {K : Type} [Field K]

@[expose] def RootsIn (H : Subgroup (SL3 K)) (i j : Fin 3) : Prop :=
  ∀ (h : i ≠ j) (s : K), rt h s ∈ H

theorem RootsIn.mono {H H' : Subgroup (SL3 K)} (hle : H ≤ H') {i j : Fin 3} (h : RootsIn H i j) :
    RootsIn H' i j := fun hij s => hle (h hij s)

theorem rt_zero_one_mem_range (h : (0 : Fin 3) ≠ 1) (s : K) :
    rt h s ∈ (blkSL : Matrix.SpecialLinearGroup (Fin 2) K →* SL3 K).range := by
  refine ⟨Matrix.SpecialLinearGroup.transvection (zero_ne_one : (0 : Fin 2) ≠ 1) s, ?_⟩
  apply ent_ext
  intro a b
  rw [KFOUT3.ent_rt]
  fin_cases a <;> fin_cases b <;>
    simp [ent, coe_blkSL, blkMat, Matrix.SpecialLinearGroup.transvection_coe]

theorem rt_one_zero_mem_range (h : (1 : Fin 3) ≠ 0) (s : K) :
    rt h s ∈ (blkSL : Matrix.SpecialLinearGroup (Fin 2) K →* SL3 K).range := by
  refine ⟨Matrix.SpecialLinearGroup.transvection (one_ne_zero : (1 : Fin 2) ≠ 0) s, ?_⟩
  apply ent_ext
  intro a b
  rw [KFOUT3.ent_rt]
  fin_cases a <;> fin_cases b <;>
    simp [ent, coe_blkSL, blkMat, Matrix.SpecialLinearGroup.transvection_coe]

theorem eq_top_of_rootsIn {H : Subgroup (SL3 K)} {u m w : Fin 3} (hum : u ≠ m) (hmw : m ≠ w)
    (huw : u ≠ w) (h1 : RootsIn H u m) (h2 : RootsIn H m u) (h3 : RootsIn H m w)
    (h4 : RootsIn H w m) : H = ⊤ := by
  have c1 : ∀ s : K, rt huw s ∈ H := fun s => by
    have e : rt huw s = ⁅rt hum s, rt hmw (1 : K)⁆ := by
      rw [Matrix.SpecialLinearGroup.commutatorElement_transvection hum hmw huw s 1, mul_one]
    rw [e, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem (h1 hum s) (h3 hmw 1)) (H.inv_mem (h1 hum s)))
      (H.inv_mem (h3 hmw 1))
  have c2 : ∀ s : K, rt huw.symm s ∈ H := fun s => by
    have e : rt huw.symm s = ⁅rt hmw.symm s, rt hum.symm (1 : K)⁆ := by
      rw [Matrix.SpecialLinearGroup.commutatorElement_transvection hmw.symm hum.symm huw.symm s 1,
        mul_one]
    rw [e, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem (h4 hmw.symm s) (h2 hum.symm 1))
      (H.inv_mem (h4 hmw.symm s))) (H.inv_mem (h2 hum.symm 1))
  rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 3) (K := K),
    Subgroup.closure_le]
  rintro _ ⟨i, j, hij, c, rfl⟩
  rcases cover_three hum huw hmw i with rfl | rfl | rfl <;>
    rcases cover_three hum huw hmw j with rfl | rfl | rfl <;>
    first
    | exact absurd rfl hij
    | exact h1 hij c
    | exact h2 hij c
    | exact h3 hij c
    | exact h4 hij c
    | exact c1 c
    | exact c2 c

variable [CharP K 2]

@[expose] noncomputable def blockConj (τ : Equiv.Perm (Fin 3)) : Subgroup (SL3 K) :=
  (blkSL : Matrix.SpecialLinearGroup (Fin 2) K →* SL3 K).range.map
    (MulAut.conj (permSL τ)).toMonoidHom

theorem rootsIn_blockConj (τ : Equiv.Perm (Fin 3)) :
    RootsIn (blockConj (K := K) τ) (τ 0) (τ 1) ∧ RootsIn (blockConj (K := K) τ) (τ 1) (τ 0) := by
  have h01 : (0 : Fin 3) ≠ 1 := by decide
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  refine ⟨fun h s => ?_, fun h s => ?_⟩
  · refine ⟨rt h01 s, rt_zero_one_mem_range h01 s, ?_⟩
    show permSL τ * rt h01 s * (permSL τ)⁻¹ = rt h s
    exact permSL_conj_rt τ h01 s
  · refine ⟨rt h10 s, rt_one_zero_mem_range h10 s, ?_⟩
    show permSL τ * rt h10 s * (permSL τ)⁻¹ = rt h s
    exact permSL_conj_rt τ h10 s

theorem rootsIn_blockConj_of (τ : Equiv.Perm (Fin 3)) {i j : Fin 3}
    (hij : (τ 0 = i ∧ τ 1 = j) ∨ (τ 0 = j ∧ τ 1 = i)) :
    RootsIn (blockConj (K := K) τ) i j ∧ RootsIn (blockConj (K := K) τ) j i := by
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact rootsIn_blockConj τ
  · exact (rootsIn_blockConj τ).symm

theorem blockConj_sup_eq_top (τ τ' : Equiv.Perm (Fin 3))
    (hne : Equiv.swap (τ 0) (τ 1) ≠ Equiv.swap (τ' 0) (τ' 1)) :
    blockConj (K := K) τ ⊔ blockConj τ' = ⊤ := by
  have key : ∀ τ τ' : Equiv.Perm (Fin 3), Equiv.swap (τ 0) (τ 1) ≠ Equiv.swap (τ' 0) (τ' 1) →
      ∃ u m w : Fin 3, u ≠ m ∧ m ≠ w ∧ u ≠ w ∧
        ((τ 0 = u ∧ τ 1 = m) ∨ (τ 0 = m ∧ τ 1 = u)) ∧
        ((τ' 0 = m ∧ τ' 1 = w) ∨ (τ' 0 = w ∧ τ' 1 = m)) := by decide
  obtain ⟨u, m, w, hum, hmw, huw, hτ, hτ'⟩ := key τ τ' hne
  obtain ⟨a1, a2⟩ := rootsIn_blockConj_of (K := K) τ hτ
  obtain ⟨b1, b2⟩ := rootsIn_blockConj_of (K := K) τ' hτ'
  exact eq_top_of_rootsIn hum hmw huw (a1.mono le_sup_left) (a2.mono le_sup_left)
    (b1.mono le_sup_right) (b2.mono le_sup_right)

end Generation

section Cover

variable {G : Type} [Group G] {p : ℕ} {A J : Subgroup G} {K : Type} [Field K] [Finite K]
  {ρ : SL3 K →* G}

theorem ker_eq_bot_or_center (hρ : IsPSL3Cover p A J ρ) {f : ℕ} (hK : Nat.card K = 2 ^ f) :
    ρ.ker = ⊥ ∨ ρ.ker = Subgroup.center (SL3 K) := by
  have hcen : Nat.card (Subgroup.center (SL3 K)) ≤ 3 := by
    rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center, card_scalars (by norm_num),
      hK]
    exact Nat.gcd_le_left _ (by norm_num)
  by_cases hbot : ρ.ker = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨x, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hbot
    have hxc : (x : SL3 K) ∈ Subgroup.center (SL3 K) := hρ.ker_central x.2
    have hx3 : (x : SL3 K) ^ 3 = 1 := KFOUT3.center_pow_three hxc
    have hx1' : (x : SL3 K) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (x : SL3 K) = 3 := orderOf_eq_prime hx3 hx1'
    have hz : Subgroup.zpowers (x : SL3 K) = Subgroup.center (SL3 K) := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hxc) ?_
      rw [Nat.card_zpowers, hord]
      exact hcen
    refine le_antisymm hρ.ker_central ?_
    rw [← hz]
    exact Subgroup.zpowers_le.2 x.2

theorem centrallyLThree_of_cover (hρ : IsPSL3Cover p A J ρ) {f : ℕ} (hK : Nat.card K = 2 ^ f)
    (hf : 3 ≤ f) : CentrallyLThree f ↥J := by
  rcases ker_eq_bot_or_center hρ hK with hbot | hcen
  · have hinj : Function.Injective ρ := (MonoidHom.ker_eq_bot_iff ρ).1 hbot
    let e : ↥J ≃* SL3 K :=
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hρ.range_eq)).symm
    exact Or.inl ⟨K, inferInstance, inferInstance, hK,
      ⟨e.trans (specialLinearGroupEquivStatedSL 3 K)⟩⟩
  · have hadm : StatedLieAdmissible .PSL 3 2 f := by
      refine ⟨Nat.prime_two, by omega, by omega, ?_, ?_⟩
      · intro h
        simp only [Prod.mk.injEq] at h
        omega
      · intro h
        simp only [Prod.mk.injEq] at h
        omega
    have hcl : StatedClassicalModel (Matrix.ProjectiveSpecialLinearGroup (Fin 3) K) .PSL 3 2 f :=
      ⟨hadm, K, inferInstance, inferInstance, hK,
        ⟨projectiveSpecialLinearGroupEquivStatedProj 3 K⟩⟩
    let e : ↥J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 3) K :=
      (MulEquiv.subgroupCongr hρ.range_eq).symm.trans
        ((QuotientGroup.quotientKerEquivRange ρ).symm.trans (QuotientGroup.quotientMulEquivOfEq hcen))
    exact Or.inr (statedClassicalModel_of_equiv e.symm hcl)

end Cover

section Faithful

variable {G : Type} [Group G] {p : ℕ} {A J : Subgroup G} {K : Type} [Field K] {ρ : SL3 K →* G}

theorem actsBy_perm_eq_of_map_eq (hp : p.Prime) (hρ : IsPSL3Cover p A J ρ) {ζ : Kˣ}
    (hζ : IsZeta p ζ) {m m' : SL3 K} {σ σ' : Equiv.Perm (Fin 3)} (hm : ActsBy p m σ)
    (hm' : ActsBy p m' σ') (hv0 : ∏ k, tSep ζ 0 1 k = 1)
    (h : ρ (m * diagSL (tSep ζ 0 1) hv0 * m⁻¹) = ρ (m' * diagSL (tSep ζ 0 1) hv0 * m'⁻¹)) :
    σ = σ' := by
  have hw : diagSL (tSep ζ 0 1) hv0 ∈ Tor p K := tSep_mem hζ (by decide)
  have hv1 : ∀ i, tSep ζ 0 1 i ^ p = 1 := fun k =>
    (KFU.torusElt_mem (by decide : (0 : Fin 3) ≠ 1) hζ.pow :
      KFU.torusElt 0 1 ζ ∈ KFU.torusVec p 3 K).1 k
  have h1 : m * diagSL (tSep ζ 0 1) hv0 * m⁻¹ = m' * diagSL (tSep ζ 0 1) hv0 * m'⁻¹ :=
    hρ.eq_of_map_eq hp (by rw [conj_pow, Tor_pow_eq_one hw, mul_one, mul_inv_cancel])
      (by rw [conj_pow, Tor_pow_eq_one hw, mul_one, mul_inv_cancel]) h
  rw [hm _ hv0 hv1, hm' _ hv0 hv1] at h1
  have h2 : ∀ a, permVec σ (tSep ζ 0 1) a = permVec σ' (tSep ζ 0 1) a := by
    intro a
    have := congrArg (fun y : SL3 K => ent y a a) h1
    apply Units.ext
    simpa [KFOUT3.diagSL_apply] using this
  have h3 : ∀ a, σ⁻¹ a = σ'⁻¹ a := fun a => tSep_injective hζ (h2 a)
  exact inv_injective (Equiv.ext h3)

theorem nmh_mul_ne_of_mul_ne [Finite G] [Finite K] [CharP K 2] {c : G} (h : JGood p A c J)
    (hρ : IsPSL3Cover p A J ρ) {ζ : Kˣ} (hζ : IsZeta p ζ) {π π' : Equiv.Perm (Fin 3)}
    (hk : ρ (permSL π) ∈ Subgroup.normalizer (A : Set G))
    (hk' : ρ (permSL π') ∈ Subgroup.normalizer (A : Set G)) (hne : π * π' ≠ π' * π) :
    A.normalizerMonoidHom ⟨ρ (permSL π), hk⟩ * A.normalizerMonoidHom ⟨ρ (permSL π'), hk'⟩ ≠
      A.normalizerMonoidHom ⟨ρ (permSL π'), hk'⟩ * A.normalizerMonoidHom ⟨ρ (permSL π), hk⟩ := by
  intro hcomm
  apply hne
  have hp := h.hyp.prime
  have hv0 : ∏ k, tSep ζ 0 1 k = 1 := KFU.prod_torusElt 0 1 ζ
  have hw : diagSL (tSep ζ 0 1) hv0 ∈ Tor p K := tSep_mem hζ (by decide)
  have hA : ρ (diagSL (tSep ζ 0 1) hv0) ∈ A :=
    Tof_le A J (hρ.map_torus ▸ Subgroup.mem_map_of_mem ρ hw)
  have h1 : ρ (permSL π) * (ρ (permSL π') * ρ (diagSL (tSep ζ 0 1) hv0) * (ρ (permSL π'))⁻¹) *
      (ρ (permSL π))⁻¹ = ρ (permSL π') * (ρ (permSL π) * ρ (diagSL (tSep ζ 0 1) hv0) *
        (ρ (permSL π))⁻¹) * (ρ (permSL π'))⁻¹ :=
    congrArg (fun φ : MulAut A => (φ ⟨ρ (diagSL (tSep ζ 0 1) hv0), hA⟩ : G)) hcomm
  have h2 : ρ (permSL π * permSL π' * diagSL (tSep ζ 0 1) hv0 * (permSL π * permSL π')⁻¹) =
      ρ (permSL π' * permSL π * diagSL (tSep ζ 0 1) hv0 * (permSL π' * permSL π)⁻¹) := by
    simp only [map_mul, map_inv, mul_inv_rev, mul_assoc] at h1 ⊢
    exact h1
  exact actsBy_perm_eq_of_map_eq hp hρ hζ ((ActsBy.permSL π).mul (ActsBy.permSL π'))
    ((ActsBy.permSL π').mul (ActsBy.permSL π)) hv0 h2

end Faithful

section Main

variable {G : Type} [Group G] {p : ℕ} {A : Subgroup G} {c : G}

theorem swap_mul_ne_of_ne : ∀ a b a' b' : Fin 3, a ≠ b → a' ≠ b' →
    Equiv.swap a b ≠ Equiv.swap a' b' →
    Equiv.swap a b * Equiv.swap a' b' ≠ Equiv.swap a' b' * Equiv.swap a b := by decide

theorem range_blkφ_conj {K : Type} [Field K] [CharP K 2] (ρ : SL3 K →* G) (τ : Equiv.Perm (Fin 3)) :
    (blkφ (ρ.comp (MulAut.conj (permSL τ)).toMonoidHom)).range = (blockConj τ).map ρ := by
  rw [← map_blkSL_range_eq, blockConj, Subgroup.map_map]

theorem kfPairL_row1 [Finite G]
    (hGA : CFSG.Open.GriessAllModelsStatement)
    {L E : Subgroup G} (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hEA : E = A)
    {f : ℕ} (hf : p ∣ 2 ^ f - 1) (hf1 : 1 ≤ f)
    (hm : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 2 f) :
    ∀ s ∈ reflectionSet p E, s ∈ torusImage E L → ∀ t ∈ reflectionSet p E, t ∈ torusImage E L →
      s ≠ t → KFPairL p E f s t := by
  subst hEA
  have hJ : JGood p E c L := jGood_of_row1 h hF rfl ⟨f, hf1, hf, hm⟩
  obtain ⟨K, hKf, hKfin, hK, ρ, hρ⟩ := exists_psl3Data hGA hJ hf hm
  have hchar : CharP K 2 := charP_two_of_card hK
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hf3 := three_le_of_dvd_pred h5 hf1 hf
  obtain ⟨ζ, hζ⟩ := exists_isZeta hp h5 (by rw [hK]; exact hf)
  intro s hs hsL t ht htL hst
  obtain ⟨τ, -, hBs, hks, hse⟩ := kfAt_of_cover hJ hρ hK hf1 hf hs hsL
  obtain ⟨τ', -, hBt, hkt, hte⟩ := kfAt_of_cover hJ hρ hK hf1 hf ht htL
  have hne : Equiv.swap (τ 0) (τ 1) ≠ Equiv.swap (τ' 0) (τ' 1) := by
    intro heq
    apply hst
    have key : ∀ (π π' : Equiv.Perm (Fin 3))
        (hk : ρ (permSL π) ∈ Subgroup.normalizer (E : Set G))
        (hk' : ρ (permSL π') ∈ Subgroup.normalizer (E : Set G)), π = π' →
        E.normalizerMonoidHom ⟨ρ (permSL π), hk⟩ = E.normalizerMonoidHom ⟨ρ (permSL π'), hk'⟩ := by
      rintro π π' hk hk' rfl
      rfl
    rw [← hse, ← hte]
    exact key _ _ hks hkt heq
  have h01 : τ 0 ≠ τ 1 := τ.injective.ne (by decide)
  have h01' : τ' 0 ≠ τ' 1 := τ'.injective.ne (by decide)
  refine ⟨fun hcomm => ?_, fun _ => ?_⟩
  · exfalso
    rw [← hse, ← hte] at hcomm
    exact nmh_mul_ne_of_mul_ne hJ hρ hζ hks hkt (swap_mul_ne_of_ne _ _ _ _ h01 h01' hne) hcomm
  · have hjoin : kZero p E s ⊔ kZero p E t = L := by
      rw [hBs, hBt, range_blkφ_conj, range_blkφ_conj, ← Subgroup.map_sup,
        blockConj_sup_eq_top τ τ' hne, ← MonoidHom.range_eq_map, hρ.range_eq]
    rw [hjoin]
    exact centrallyLThree_of_cover hρ hK hf3

theorem kf141b_holds (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF141b := by
  intro G _ _ p A c L E f hH hF _ _ hf hpq hmodel hEA _ s hs hsL t ht htL hst
  exact kfPairL_row1 hGA hH hF hEA hpq hf hmodel s hs hsL t ht htL hst

end Main

end CFSG.RankThree.PartOne.S13K
