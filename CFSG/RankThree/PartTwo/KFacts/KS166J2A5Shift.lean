module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Sig5
import CFSG.RankThree.PartTwo.KFacts.KS166J2A5Core
import CFSG.RankThree.PartTwo.KFacts.ONanKS17J2CentralizerNine
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS166

open Subgroup CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover

open scoped commutatorElement

private theorem exists_conj_of_normalizer
    {K : Subgroup GJ}
    (hKA : Nonempty (↥K ≃* alternatingGroup (Fin 5)))
    (hxN : xJ ∈ normalizer (K : Set GJ)) :
    ∃ k : ↥K, (∀ y : ↥K, (k : GJ) * (y : GJ) * (k : GJ)⁻¹ = xJ * (y : GJ) * xJ⁻¹) ∧
      (k : GJ) ^ 3 = 1 ∧ (k : GJ) * xJ = xJ * (k : GJ) := by
  classical
  obtain ⟨φ⟩ := hKA
  let xN : normalizer (K : Set GJ) := ⟨xJ, hxN⟩
  let α : MulAut ↥K := Subgroup.normalizerMonoidHom K xN
  have hα3 : α ^ 3 = 1 := by
    have hx3 : xN ^ 3 = 1 := Subtype.ext (by simpa using x_cube)
    calc α ^ 3 = Subgroup.normalizerMonoidHom K (xN ^ 3) := (map_pow _ xN 3).symm
      _ = 1 := by rw [hx3, map_one]
  obtain ⟨k, hk⟩ := exists_eq_conj_of_pow_three φ α hα3
  have hconj : ∀ y : ↥K, (k : GJ) * (y : GJ) * (k : GJ)⁻¹ = xJ * (y : GJ) * xJ⁻¹ := by
    intro y
    have h1 : ((α y : ↥K) : GJ) = xJ * (y : GJ) * xJ⁻¹ :=
      Subgroup.normalizerMonoidHom_apply_apply_coe K xN y
    have h2 : ((MulAut.conj k y : ↥K) : GJ) = (k : GJ) * (y : GJ) * (k : GJ)⁻¹ := by
      simp [MulAut.conj_apply]
    rw [hk] at h1
    rw [← h2]
    exact h1
  have hkx : (k : GJ) * xJ = xJ * (k : GJ) := by
    have h := hconj k
    calc (k : GJ) * xJ = ((k : GJ) * (k : GJ) * (k : GJ)⁻¹) * xJ := by group
      _ = (xJ * (k : GJ) * xJ⁻¹) * xJ := by rw [h]
      _ = xJ * (k : GJ) := by group
  have hk3K : k ^ 3 = 1 := by
    refine eq_one_of_commute_alt5 φ fun y => ?_
    have hconj3 : (MulAut.conj k) ^ 3 = 1 := by rw [← hk]; exact hα3
    have hy : (MulAut.conj (k ^ 3)) y = y := by
      rw [map_pow (MulAut.conj : ↥K →* MulAut ↥K) k 3, hconj3]
      rfl
    rw [MulAut.conj_apply] at hy
    calc k ^ 3 * y = ((k ^ 3) * y * (k ^ 3)⁻¹) * (k ^ 3) := by group
      _ = y * k ^ 3 := by rw [hy]
  refine ⟨k, hconj, ?_, hkx⟩
  have h := congrArg (fun z : ↥K => (z : GJ)) hk3K
  simpa using h

private theorem centralizes_and_commutes
    {K : Subgroup GJ} {k : ↥K} {w : GJ}
    (hw : w = (k : GJ)⁻¹ * xJ)
    (hconj : ∀ y : ↥K, (k : GJ) * (y : GJ) * (k : GJ)⁻¹ = xJ * (y : GJ) * xJ⁻¹)
    (hkx : (k : GJ) * xJ = xJ * (k : GJ)) (hk3 : (k : GJ) ^ 3 = 1)
    (hKz : K ≤ centralizer ({zJ} : Set GJ)) :
    w ∈ centralizer (K : Set GJ) ∧ w ^ 3 = 1 ∧ Commute w zJ := by
  have hwcent : w ∈ centralizer (K : Set GJ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h := hconj ⟨y, hy⟩
    have h' : w * y * w⁻¹ = y := by
      rw [hw]
      calc ((k : GJ)⁻¹ * xJ) * y * ((k : GJ)⁻¹ * xJ)⁻¹
          = (k : GJ)⁻¹ * (xJ * y * xJ⁻¹) * (k : GJ) := by group
        _ = (k : GJ)⁻¹ * ((k : GJ) * y * (k : GJ)⁻¹) * (k : GJ) := by rw [← h]
        _ = y := by group
    calc y * w = (w * y * w⁻¹) * w := by rw [h']
      _ = w * y := by group
  have hw3 : w ^ 3 = 1 := by
    have hcomm : Commute ((k : GJ)⁻¹) xJ := Commute.inv_left hkx
    calc w ^ 3 = ((k : GJ)⁻¹ * xJ) ^ 3 := by rw [hw]
      _ = ((k : GJ)⁻¹) ^ 3 * xJ ^ 3 := hcomm.mul_pow 3
      _ = 1 := by rw [inv_pow, hk3, x_cube]; simp
  have hwz : Commute w zJ := by
    have hkz : Commute (k : GJ) zJ :=
      Subgroup.mem_centralizer_singleton_iff.mp (hKz k.2)
    have hxz : Commute xJ zJ := by
      have hzx : Commute zJ xJ := by simpa [Commute, z_eq] using z_comm_x
      exact hzx.symm
    have h2 : Commute ((k : GJ)⁻¹ * xJ) zJ := hkz.inv_left.mul_left hxz
    simpa [hw] using h2
  exact ⟨hwcent, hw3, hwz⟩

private theorem xJ_not_mem_zpowers_zJ :
    xJ ∉ zpowers zJ := by
  intro hx
  have hle : E0 ≤ zpowers zJ := by
    rw [show E0 = closure ({⁅xJ, yJ⁆, xJ} : Set GJ) from rfl, closure_le]
    intro g hg
    rcases hg with rfl | rfl
    · simpa [z_eq] using Subgroup.mem_zpowers zJ
    · exact hx
  have h9 : Nat.card E0 = 9 := by rw [card_E0]; norm_num
  have hle' := Subgroup.card_le_of_le hle
  rw [card_zpowers_z, h9] at hle'
  omega

private theorem mem_zpowers_zJ_of_centralizes
    {K : Subgroup GJ} {w : GJ}
    (φ : ↥K ≃* alternatingGroup (Fin 5))
    (hKz : K ≤ centralizer ({zJ} : Set GJ))
    (hwcent : w ∈ centralizer (K : Set GJ)) (hw3 : w ^ 3 = 1) (hwz : Commute w zJ) :
    w ∈ zpowers zJ := by
  by_contra hw_not
  have hw1 : w ≠ 1 := fun h => hw_not (by rw [h]; exact Subgroup.one_mem _)
  have hw3o : orderOf w = 3 := orderOf_eq_prime hw3 hw1
  have hnorm : zpowers zJ ≤ Subgroup.normalizer (zpowers w : Set GJ) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_zpowers_of_commute hwz.symm
  have hinf : zpowers zJ ⊓ zpowers w = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Subgroup.mem_bot]
    by_contra hu1
    have hu3 : orderOf u = 3 := by
      refine orderOf_eq_prime ?_ hu1
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu.2
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hw3, one_zpow]
    have h1 : zpowers u = zpowers w :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hu.2)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hu3, hw3o])
    have h2 : zpowers u ≤ zpowers zJ := Subgroup.zpowers_le.mpr hu.1
    rw [h1] at h2
    exact hw_not (h2 (Subgroup.mem_zpowers w))
  have hE9 : Nat.card (zpowers zJ ⊔ zpowers w : Subgroup GJ) = 9 := by
    have h :=
      CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
        (H := zpowers zJ) (K := zpowers w) hnorm
    rw [hinf, Subgroup.card_bot, mul_one, card_zpowers_z, Nat.card_zpowers, hw3o] at h
    omega
  have hzJcent : zJ ∈ Subgroup.centralizer (K : Set GJ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKz hy)
  have hKleC : K ≤ Subgroup.centralizer ((zpowers zJ ⊔ zpowers w : Subgroup GJ) : Set GJ) := by
    rw [Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.zpowers_le.mpr hzJcent) (Subgroup.zpowers_le.mpr hwcent)
  have hKleE : K ≤ (zpowers zJ ⊔ zpowers w : Subgroup GJ) :=
    hKleC.trans (ks17J2CentralizerNine GJ ⟨nativeEquivP.symm⟩ _ hE9)
  have hdvd : 60 ∣ 9 := by
    have h := Subgroup.card_dvd_of_le hKleE
    rwa [card_of_alt5 φ, hE9] at h
  omega

theorem exists_aJ_mem
    {K : Subgroup GJ} (hKA : Nonempty (↥K ≃* alternatingGroup (Fin 5)))
    (hKz : K ≤ centralizer ({zJ} : Set GJ)) (hxN : xJ ∈ normalizer (K : Set GJ)) :
    ∃ m : Fin 3, aJ m ∈ K := by
  classical
  obtain ⟨φ⟩ := hKA
  obtain ⟨k, hconj, hk3, hkx⟩ := exists_conj_of_normalizer ⟨φ⟩ hxN
  set w : GJ := (k : GJ)⁻¹ * xJ with hwdef
  obtain ⟨hwcent, hw3, hwz⟩ := centralizes_and_commutes hwdef hconj hkx hk3 hKz
  have hw_in : w ∈ zpowers zJ := mem_zpowers_zJ_of_centralizes φ hKz hwcent hw3 hwz
  have hkE0 : (k : GJ) ∈ E0 := by
    have hwE : w ∈ E0 := Subgroup.zpowers_le.mpr zJ_mem_E0 hw_in
    have hk_eq : (k : GJ) = xJ * w⁻¹ := by
      rw [hwdef]
      group
    rw [hk_eq]
    exact E0.mul_mem x_mem_E0 (E0.inv_mem hwE)
  have hkz_not : (k : GJ) ∉ zpowers zJ := by
    intro hkz'
    apply xJ_not_mem_zpowers_zJ
    have hx_eq : xJ = (k : GJ) * w := by
      rw [hwdef]
      group
    rw [hx_eq]
    exact (zpowers zJ).mul_mem hkz' hw_in
  obtain ⟨m, hm⟩ := zpowers_eq_a hkE0 hkz_not
  refine ⟨m, ?_⟩
  have hle : Subgroup.zpowers (k : GJ) ≤ K := Subgroup.zpowers_le.mpr k.2
  rw [hm] at hle
  exact hle (Subgroup.mem_zpowers (aJ m))

theorem exists_frame2
    {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2))
    {K E : Subgroup X} (hKp : Group.IsPerfect ↥K)
    (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (hEK : E ≤ normalizer (K : Set X)) (hE9 : Nat.card E = 9) :
    ∃ ψ : X ≃* GJ, zJ ∈ E.map ψ.toMonoidHom ∧ xJ ∈ K.map ψ.toMonoidHom ∧
      K.map ψ.toMonoidHom ≤ centralizer ({zJ} : Set GJ) ∧
      Nonempty (↥(K.map ψ.toMonoidHom) ≃* alternatingGroup (Fin 5)) := by
  classical
  obtain ⟨ψ₁, hψE, hKA₁, hK₁z⟩ := exists_frame hX hKp hKA hEK hE9
  set K₁ : Subgroup GJ := K.map ψ₁.toMonoidHom with hK₁
  have hE0N : E0 ≤ Subgroup.normalizer (K₁ : Set GJ) := by
    rw [hK₁, ← Subgroup.map_equiv_normalizer_eq K ψ₁, ← hψE]
    exact Subgroup.map_mono hEK
  obtain ⟨m, hm⟩ := exists_aJ_mem hKA₁ hK₁z (hE0N x_mem_E0)
  have hzC : zJ ∈ centralizer ((P3 : Subgroup GJ) : Set GJ) := by
    have h1 : zJ ∈ P3 ⊓ centralizer ((P3 : Subgroup GJ) : Set GJ) := by
      rw [inf_centralizer_P3, ← z_eq]
      exact Subgroup.mem_zpowers zJ
    exact h1.2
  have hcomm : (cJ m) * zJ = zJ * (cJ m) :=
    Subgroup.mem_centralizer_iff.mp hzC (cJ m) (c_spec m).1
  set τ : MulAut GJ := MulAut.conj (cJ m)⁻¹ with hτ
  have hτz : τ zJ = zJ := by
    rw [hτ, MulAut.conj_apply, inv_inv]
    calc (cJ m)⁻¹ * zJ * (cJ m) = (cJ m)⁻¹ * ((cJ m) * zJ) := by
          rw [hcomm]; group
      _ = zJ := by group
  have hEψ : E.map (ψ₁.trans τ).toMonoidHom = E0.map τ.toMonoidHom := by
    rw [show (ψ₁.trans τ).toMonoidHom = τ.toMonoidHom.comp ψ₁.toMonoidHom from rfl,
      ← Subgroup.map_map, hψE]
  have hKψ : K.map (ψ₁.trans τ).toMonoidHom = K₁.map τ.toMonoidHom := by
    rw [hK₁, show (ψ₁.trans τ).toMonoidHom = τ.toMonoidHom.comp ψ₁.toMonoidHom from rfl,
      ← Subgroup.map_map]
  refine ⟨ψ₁.trans τ, ?_, ?_, ?_, ?_⟩
  · rw [hEψ]
    exact Subgroup.mem_map.mpr ⟨zJ, zJ_mem_E0, hτz⟩
  · rw [hKψ]
    refine Subgroup.mem_map.mpr ⟨aJ m, hm, ?_⟩
    rw [hτ]
    change (MulAut.conj (cJ m)⁻¹) (aJ m) = xJ
    rw [MulAut.conj_apply, inv_inv]
    exact conj_c_a m
  · rw [hKψ]
    intro y hy
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    have hg' : g ∈ Subgroup.centralizer ({zJ} : Set GJ) := hK₁z hg
    rw [Subgroup.mem_centralizer_singleton_iff] at hg' ⊢
    calc τ g * zJ = τ g * τ zJ := by rw [hτz]
      _ = τ (g * zJ) := (map_mul τ g zJ).symm
      _ = τ (zJ * g) := by rw [hg']
      _ = τ zJ * τ g := map_mul τ zJ g
      _ = zJ * τ g := by rw [hτz]
  · rw [hKψ]
    exact nonempty_alt5_map τ hKA₁

end CFSG.RankThree.PartTwo.KFacts.KS166
