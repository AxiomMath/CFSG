module

public import CFSG.Quasithin.Vol2.KGNatSL3BorelOdd
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListSp4Block

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix
open CFSG.Assembly.LowTwoRank (StatedSp)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (pairRootElt coe_pairRootElt
  pairRootMat rootNil rootVec lineVec lineSign simpleRootVec simpleSnd rootSubgroup weylRep
  borelCuts pairRootElt_mem_rootSubgroup)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (unipotent borelSubgroup)
open CFSG.CGT.Timmesfeld75 (utri ltri utriElt ltriElt utriElt_apply_00 utriElt_apply_01
  utriElt_apply_10 utriElt_apply_11 ltriElt_apply_00 ltriElt_apply_01 ltriElt_apply_10
  ltriElt_apply_11)
open CFSG.QuasithinUnique.Vol2Native.A312L (spLevi spMat spMat_lam spMat_leviSp_one
  blkIdx_spLevi)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (pairMat statedSp_ext)
open scoped MatrixGroups

variable {F : Type} [Field F]

theorem rootVec_inr1_inl1 : rootVec (r := 2) (Sum.inr 1) (Sum.inl 1) = -simpleRootVec 2 1 := by
  ext i
  fin_cases i <;> simp [rootVec, lineVec, simpleRootVec]

theorem rootVec_inl1_inl0 : rootVec (r := 2) (Sum.inl 1) (Sum.inl 0) = -simpleRootVec 2 0 := by
  ext i
  fin_cases i <;> simp [rootVec, lineVec, simpleRootVec]

theorem rootVec_inl1_inr1 : rootVec (r := 2) (Sum.inl 1) (Sum.inr 1) = simpleRootVec 2 1 := by
  ext i
  fin_cases i <;> simp [rootVec, lineVec, simpleRootVec]

theorem rootVec_inl0_inl1 : rootVec (r := 2) (Sum.inl 0) (Sum.inl 1) = simpleRootVec 2 0 := by
  ext i
  fin_cases i <;> simp [rootVec, lineVec, simpleRootVec]

theorem spLevi_injective (j : Fin 2) : Function.Injective (spLevi (K := F) j) := by
  intro A B h
  apply Subtype.ext
  rw [← blkIdx_spLevi j A, ← blkIdx_spLevi j B, h]

theorem spLevi0_utri (s : F) :
    spLevi 0 (utriElt s) = pairRootElt (a := Sum.inl 1) (b := Sum.inr 1) Sum.inl_ne_inr s := by
  apply statedSp_ext
  change spMat (spLevi 0 (utriElt s)) = _
  rw [spMat_lam, coe_pairRootElt]
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
    simp [pairMat, pairRootMat, rootNil, utriElt_apply_00,
      utriElt_apply_01, utriElt_apply_10, utriElt_apply_11]

theorem spLevi0_ltri (t : F) :
    spLevi 0 (ltriElt t) = pairRootElt (a := Sum.inr 1) (b := Sum.inl 1) Sum.inr_ne_inl t := by
  apply statedSp_ext
  change spMat (spLevi 0 (ltriElt t)) = _
  rw [spMat_lam, coe_pairRootElt]
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
    simp [pairMat, pairRootMat, rootNil, ltriElt_apply_00,
      ltriElt_apply_01, ltriElt_apply_10, ltriElt_apply_11]

theorem spLevi1_utri (s : F) :
    spLevi 1 (utriElt s) = pairRootElt (a := Sum.inl 0) (b := Sum.inl 1)
      (by simp) s := by
  apply statedSp_ext
  change spMat (spLevi 1 (utriElt s)) = _
  rw [spMat_leviSp_one, coe_pairRootElt]
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
    simp [pairRootMat, rootNil, lineSign, Matrix.adjugate_fin_two,
      utriElt_apply_00, utriElt_apply_01, utriElt_apply_10,
      utriElt_apply_11]

theorem spLevi1_ltri (t : F) :
    spLevi 1 (ltriElt t) = pairRootElt (a := Sum.inl 1) (b := Sum.inl 0)
      (by simp) t := by
  apply statedSp_ext
  change spMat (spLevi 1 (ltriElt t)) = _
  rw [spMat_leviSp_one, coe_pairRootElt]
  ext x y
  rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
    simp [pairRootMat, rootNil, lineSign, Matrix.adjugate_fin_two,
      ltriElt_apply_00, ltriElt_apply_01, ltriElt_apply_10,
      ltriElt_apply_11]

theorem exists_SL2_le_of_weylRep_mem {Y : Subgroup (StatedSp 2 F)} (hU : unipotent 2 F ≤ Y)
    (k : Fin 2) (hk : weylRep F k ∈ Y) :
    ∃ φ : SL(2, F) →* StatedSp 2 F, Function.Injective φ ∧ ∀ A, φ A ∈ Y := by
  have hW : CFSG.QuasithinUnique.Setup.X7a.spWeylGroup F k ≤ Y :=
    sup_le hU ((Subgroup.closure_le _).mpr (by rintro _ rfl; exact hk))
  have hneg := (CFSG.QuasithinUnique.Setup.X7a.rootSubgroup_neg_le_spWeylGroup (K := F) k).trans hW
  have hpos : rootSubgroup F (simpleRootVec 2 k) ≤ Y :=
    (CFSG.QuasithinUnique.Setup.X7a.rootSubgroup_le_unipotent
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.simpleRootVec_mem_posRoots k)).trans hU
  have htop : utri F ⊔ ltri F = ⊤ := by
    rw [← CFSG.CGT.Timmesfeld75.conjSubgroup_wElt_utri,
      utri_sup_conj_eq_top CFSG.CGT.Timmesfeld75.wElt_not_mem_borel]
  have hmk : ∀ φ : SL(2, F) →* StatedSp 2 F, Function.Injective φ → (∀ s, φ (utriElt s) ∈ Y) →
      (∀ t, φ (ltriElt t) ∈ Y) → ∃ φ : SL(2, F) →* StatedSp 2 F,
        Function.Injective φ ∧ ∀ A, φ A ∈ Y := by
    intro φ hφ hu hl
    refine ⟨φ, hφ, fun A => ?_⟩
    have hle : utri F ⊔ ltri F ≤ Y.comap φ := by
      refine sup_le (fun u hu' => ?_) (fun l hl' => ?_)
      · obtain ⟨s, rfl⟩ := CFSG.CGT.Timmesfeld75.mem_utri_iff.mp hu'
        exact hu s
      · obtain ⟨t, rfl⟩ := CFSG.CGT.Timmesfeld75.mem_ltri_iff.mp hl'
        exact hl t
    exact hle (htop ▸ Subgroup.mem_top A)
  rcases CFSG.QuasithinUnique.Vol2Native.A312L.fin_two_cases k with rfl | rfl
  · refine hmk (spLevi 1) (spLevi_injective 1) (fun s => ?_) (fun t => ?_)
    · rw [spLevi1_utri]
      exact hpos (rootVec_inl0_inl1 ▸ pairRootElt_mem_rootSubgroup _ s)
    · rw [spLevi1_ltri]
      exact hneg (rootVec_inl1_inl0 ▸ pairRootElt_mem_rootSubgroup _ t)
  · refine hmk (spLevi 0) (spLevi_injective 0) (fun s => ?_) (fun t => ?_)
    · rw [spLevi0_utri]
      exact hpos (rootVec_inl1_inr1 ▸ pairRootElt_mem_rootSubgroup _ s)
    · rw [spLevi0_ltri]
      exact hneg (rootVec_inr1_inl1 ▸ pairRootElt_mem_rootSubgroup _ t)

theorem factBorelOddSp4_holds : Ch11.SecC.FactBorelOddSp4 := by
  intro F _ _ n hn hF Y U hUY hU2 hUcard hodd
  have : CharP F 2 := charP_two_of_card (by omega) hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.exists_sylow_unipotent (K := F) 2 2
  have hcard : Nat.card U = Nat.card P₀ := by
    rw [hUcard, hP₀, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_unipotent, hF,
      ← pow_mul]
    norm_num [mul_comm]
  have hidx : U.index = (P₀ : Subgroup (StatedSp 2 F)).index := by
    have h1 := Subgroup.card_mul_index U
    have h2 := Subgroup.card_mul_index (P₀ : Subgroup (StatedSp 2 F))
    rw [← h2, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hUi : ¬ 2 ∣ U.index := by rw [hidx]; exact P₀.not_dvd_index
  obtain ⟨g, hg⟩ := CFSG.CGT.Timmesfeld75.exists_conjSubgroup_eq_of_sylow P₀ (hU2.toSylow hUi)
  rw [IsPGroup.toSylow_coe] at hg
  set Y' := Y.comap (MulAut.conj g).toMonoidHom with hY'
  have hmemY' : ∀ z, z ∈ Y' ↔ g * z * g⁻¹ ∈ Y := fun z => Iff.rfl
  have hUY' : unipotent 2 F ≤ Y' := by
    intro u hu
    rw [hmemY']
    refine hUY (hg ▸ CFSG.CGT.Timmesfeld75.mem_conjSubgroup.mpr ?_)
    rw [show g⁻¹ * (g * u * g⁻¹) * g = u by group, hP₀]
    exact hu
  have key : ∀ k : Fin 2, weylRep F k ∉ Y' := by
    intro k hk
    obtain ⟨φ, hφ, hφY⟩ := exists_SL2_le_of_weylRep_mem hUY' k hk
    obtain ⟨x, p, hp, hx, hpq⟩ := exists_prime_order_dvd_succ (F := F)
    have hy : g * φ x * g⁻¹ ∈ Y := (hmemY' _).mp (hφY x)
    have hord : orderOf (g * φ x * g⁻¹) = p := by
      rw [show g * φ x * g⁻¹ = (MulAut.conj g).toMonoidHom (φ x) from rfl,
        orderOf_injective _ (MulAut.conj g).injective, orderOf_injective φ hφ, hx]
    have hp2 : p ≠ 2 := by
      rintro rfl
      rw [hF] at hpq
      have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
      omega
    have h1 := hodd _ hy (by rw [hord]; exact hp.odd_of_ne_two hp2)
    have h3 : p ∣ 2 ^ n - 1 := hord ▸ orderOf_dvd_of_pow_eq_one h1
    rw [hF] at hpq
    have h4 : p ∣ 2 := by
      have h5 := Nat.dvd_sub hpq h3
      rwa [show 2 ^ n + 1 - (2 ^ n - 1) = 2 by
        have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
        omega] at h5
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4)
  have hcuts : borelCuts F Y' = {1, 2} := by
    ext i
    constructor
    · rintro ⟨k, rfl, -⟩
      rcases CFSG.QuasithinUnique.Vol2Native.A312L.fin_two_cases k with rfl | rfl <;> simp
    · intro hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      rcases hi with rfl | rfl
      · exact ⟨0, rfl, key 0⟩
      · exact ⟨1, rfl, key 1⟩
  have hY'B : Y' ≤ borelSubgroup 2 F := by
    have h1 :=
      ((CFSG.QuasithinUnique.Setup.X7a.symplectic_unitriangular_overgroup_subflag_containment
        (r := 2) (K := F)).1 Y' hUY').1
    rwa [hcuts, ← CFSG.QuasithinUnique.Setup.X7a.borelSubgroup_eq_flagStabilizer] at h1
  intro y hy
  rw [← hg, mem_normalizer_conjSubgroup, hP₀,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.normalizer_unipotent]
  exact hY'B ((hmemY' _).mpr (by rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group]))

end CFSG.Quasithin.Vol2.KGNat
