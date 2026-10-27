module

public import CFSG.Quasithin.Vol2.Ch11SecOE7B
public import CFSG.Quasithin.EmptyFaithful.SzN2Lin
public import CFSG.Quasithin.Vol2.Ch11SecOE7G
public import CFSG.Quasithin.Vol2.Ch11SecOE8P
public import CFSG.Quasithin.Vol2.Ch11SecOE8Q
public import CFSG.Quasithin.Vol2.Ch11SecOE8R

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

namespace L3T

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.QuasithinUnique.Fin257.L3 CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.Quasithin.Vol2.Ch11.SecE3 (AlmostSimple)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem member_of_twisted {L T A : Subgroup G} [hLn : L.Normal] (h : AlmostSimple L)
    (hT : IsSylowIn 2 T ⊤) {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (e : ↥L ≃* projectiveSL 3 K)
    (he : ((T ⊓ L).subgroupOf L).map e.toMonoidHom = projUnitriangular 3 K)
    (hAT : A ≤ T) (hA : IsElemAbelian 2 A) (hcard : 2 ^ n < Nat.card A) {t : G} (htT : t ∈ T)
    (htA : ∀ a ∈ A, t * a = a * t) (htE : actHom e t ∉ semilinearAutGroup 3 K) :
    ∃ L₀ : Subgroup G, L₀ ≤ L ∧ ¬ Group.IsSolvable ↥L₀ ∧
      E1.IsE n ⊤ T A (L₀ ⊔ E1.tauOf ⊤ T A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hK4' : ∃ s : Finset K, s.card = 4 := exists_finset_card_four hK4
  set ψ := actHom e with hψdef
  have hψ : Function.Injective ψ := actHom_injective e h.centralizer_eq
  set ι : projectiveSL 3 K →* G := L.subtype.comp e.symm.toMonoidHom with hιdef
  have hι : Function.Injective ι := L.subtype_injective.comp e.symm.injective
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set E := A.map ψ with hEdef
  have h2 : ∀ α ∈ E, α * α = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← pow_two, hA.2 a ha, map_one]
  have hc : ∀ α ∈ E, ∀ β ∈ E, α * β = β * α := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hAc a ha b hb]
  have hU : ∀ α ∈ E, ∀ u ∈ projUnitriangular 3 K, α u ∈ projUnitriangular 3 K := by
    rintro _ ⟨a, ha, rfl⟩ u hu
    exact actHom_mem_U e he (hAT ha) u hu
  have hcardE : Nat.card K < Nat.card E := by
    rw [hEdef, Subgroup.card_map_of_injective hψ, hK]
    exact hcard
  have hθc : ∀ α ∈ E, ψ t * α = α * ψ t := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, htA a ha]
  obtain ⟨hBW, hB1, a', ha'E, ha'Es, ha'fix⟩ :=
    twisted_case hn hK E h2 hc hU htE (actHom_mem_U e he htT) hθc hcardE
  obtain ⟨a₁, ha₁A, rfl⟩ := ha'E
  obtain ⟨j, hj, hjr⟩ := exists_SL_two_fixed_of_twisted (by omega : 1 ≤ n) hK
    (h2 _ ⟨a₁, ha₁A, rfl⟩) ha'Es ha'fix
  set F₀ := fixedSubgroup (ψ a₁) with hF₀
  set L₀ := F₀.map ι with hL₀
  have hL₀r : L₀ = (ι.comp j).range := by rw [hL₀, ← hjr, MonoidHom.range_comp]
  have eL : ↥L₀ ≃* SL(2, K) :=
    ((MonoidHom.ofInjective (f := ι.comp j) (hι.comp hj)).trans
      (MulEquiv.subgroupCongr hL₀r.symm)).symm
  have hL₀L : L₀ ≤ L := by
    rintro _ ⟨p, -, rfl⟩
    exact (e.symm p).2
  have hL₀s : ¬ Group.IsSolvable ↥L₀ := fun hs => SzN2.not_isSolvable_sl2 hK4'
    (Group.isSolvable_of_isSolvable_injective (f := eL.symm.toMonoidHom) eL.symm.injective)
  have hτN : E1.tauOf ⊤ T A ≤ Subgroup.normalizer (L₀ : Set G) := by
    intro τ hτm
    have hτa : τ * a₁ = a₁ * τ :=
      Subgroup.mem_centralizer_singleton_iff.mp (tauOf_le_centralizer h ha₁A hτm)
    have hcomm : ψ τ * ψ a₁ = ψ a₁ * ψ τ := by rw [← map_mul, ← map_mul, hτa]
    apply mem_normalizer_map_iota e
    refine Subgroup.eq_of_le_of_card_ge ?_ (Subgroup.card_map_of_injective (ψ τ).injective).ge
    rintro _ ⟨x, hx, rfl⟩
    have hx' : ψ a₁ x = x := hx
    change ψ a₁ (ψ τ x) = ψ τ x
    rw [← MulAut.mul_apply, ← hcomm, MulAut.mul_apply, hx']
  have hTL : (projUnitriangular 3 K).map ι = T ⊓ L := by
    rw [← he, Subgroup.map_map]
    have hcomp : ι.comp e.toMonoidHom = L.subtype := by
      ext x
      simp [hιdef]
    rw [hcomp, Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
  have hWF : (Wg : Subgroup (projectiveSL 3 K)) ≤ F₀ := fun g hg => ha'fix g hg
  have hZT : (Wg : Subgroup (projectiveSL 3 K)).map ι ≤ T ⊓ L₀ := by
    refine le_inf ?_ (Subgroup.map_mono hWF)
    have : (Wg : Subgroup (projectiveSL 3 K)).map ι ≤ T ⊓ L := by
      rw [← hTL]
      exact Subgroup.map_mono (Wg_le_V1.trans V1_le_U)
    exact this.trans inf_le_left
  have hL : IsSylowIn 2 (T ⊓ L₀) L₀ := by
    refine ⟨inf_le_right, hT.2.1.to_le inf_le_left, fun h2r => ?_⟩
    have hmul := Subgroup.relIndex_mul_card (H := T ⊓ L₀) (K := L₀)
    rw [inf_of_le_left inf_le_right] at hmul
    obtain ⟨s, hs⟩ := Subgroup.card_dvd_of_le hZT
    rw [Subgroup.card_map_of_injective hι, card_Wg] at hs
    have hL₀c : Nat.card L₀ = Nat.card K * (Nat.card K ^ 2 - 1) := by
      rw [Nat.card_congr eL.toEquiv, card_SL_two]
    rw [hs, hL₀c] at hmul
    have hKpos : 0 < Nat.card K := Nat.card_pos
    have hrs : (T ⊓ L₀).relIndex L₀ * s = Nat.card K ^ 2 - 1 := by
      apply Nat.eq_of_mul_eq_mul_left hKpos
      rw [← hmul]
      ring
    have hev : Even (Nat.card K ^ 2) := by
      rw [hK, ← pow_mul]
      exact (Nat.even_pow' (by omega)).mpr even_two
    have hodd : Odd (Nat.card K ^ 2 - 1) :=
      Nat.Even.sub_odd (Nat.one_le_iff_ne_zero.mpr (by positivity)) hev odd_one
    rw [← hrs] at hodd
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2r.mul_right s))
  have hAC : ¬ A ≤ Subgroup.centralizer (L₀ : Set G) := by
    intro hAC'
    obtain ⟨⟨u, huB⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp hB1)
    have hu1' : u ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
    have huA : ι u ∈ A := by
      obtain ⟨a, ha, hau⟩ := huB
      rw [eq_iota_of_actHom_eq e h.centralizer_eq hau] at ha
      exact ha
    have huL₀ : ι u ∈ L₀ := ⟨u, hWF (hBW huB), rfl⟩
    have : IsSimpleGroup SL(2, K) := E1.RootLift.isSimpleGroup_SL2 hK4
    have hZ := SecE3.center_eq_bot_of_simple (SecE3.sl2_nonabelian (K := K))
    have hcen : eL ⟨ι u, huL₀⟩ ∈ Subgroup.center SL(2, K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨y, rfl⟩ := eL.surjective y
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (hAC' huA) y y.2)
    rw [hZ, Subgroup.mem_bot, map_eq_one_iff _ eL.injective] at hcen
    apply hu1'
    apply hι
    rw [map_one]
    exact congrArg Subtype.val hcen
  exact ⟨L₀, hL₀L, hL₀s, isE_sup_tauOf_of_sl2 hT hAT hA eL hK hK4 hτN hL hAC⟩

end L3T

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3
