module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154CritExcZ3Blk
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LinearAlgebra
open CFSG.LieType.BorelTits
open scoped commutatorElement

private theorem s16h_e3_Z3NineAAAAA_cent_le_normalizer
    {W : Type} [CommGroup W] [Finite W]
    {A L L₂ : Subgroup (MulAut W)} {x : MulAut W} (hB : s16h_Z3Blocks A L L₂ x)
    (hrk : rk ↥(commSub (⊤ : Subgroup W) L) = 6) :
    A ⊓ centSub (commSub (⊤ : Subgroup W) L₂) ≤
      A ⊓ Subgroup.normalizer (L : Set (MulAut W)) := by
  rintro k ⟨hkA, hkU₂⟩
  refine ⟨hkA, ?_⟩
  change k ∈ Subgroup.normalizer (L : Set (MulAut W))
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hkL₂ : L.map (MulAut.conj k).toMonoidHom = L₂ := by
    rcases hB.perm k hkA with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact absurd h1 hne
    · exact h1
  have hkU₂_map : ∀ u ∈ commSub (⊤ : Subgroup W) L, k u ∈ commSub (⊤ : Subgroup W) L₂ :=
    fun u hu =>
      commSub_top_map151b (X := L) (Y := L₂) (g := k)
        (fun l hl => by
          have h := Subgroup.mem_map_of_mem (MulAut.conj k).toMonoidHom hl
          rwa [hkL₂] at h) u hu
  have hk1U₂ : k⁻¹ ∈ centSub (commSub (⊤ : Subgroup W) L₂) :=
    (centSub (commSub (⊤ : Subgroup W) L₂)).inv_mem hkU₂
  have hUle : commSub (⊤ : Subgroup W) L ≤ commSub (⊤ : Subgroup W) L₂ := by
    intro u hu
    have h1 : k u ∈ commSub (⊤ : Subgroup W) L₂ := hkU₂_map u hu
    have h3 : k⁻¹ (k u) = k u := mem_centSub.mp hk1U₂ (k u) h1
    rw [MulAut.inv_apply_self] at h3
    rwa [← h3] at h1
  have hUbot : commSub (⊤ : Subgroup W) L = ⊥ := by
    rw [← le_bot_iff]
    calc commSub (⊤ : Subgroup W) L
        ≤ commSub (⊤ : Subgroup W) L ⊓ commSub (⊤ : Subgroup W) L₂ := le_inf le_rfl hUle
      _ = ⊥ := hB.inf
  have hrkU : rk ↥(commSub (⊤ : Subgroup W) L) = 6 := hrk
  rw [hUbot, rk_bot] at hrkU
  omega

private theorem s16h_e3_Z3NineAAAAA_inf_normalizer_L₂_eq
    {W : Type} [CommGroup W] {A L L₂ : Subgroup (MulAut W)} {x : MulAut W}
    (hB : s16h_Z3Blocks A L L₂ x) :
    A ⊓ Subgroup.normalizer (L₂ : Set (MulAut W)) =
      A ⊓ Subgroup.normalizer (L : Set (MulAut W)) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgA, hgN₂⟩ := Subgroup.mem_inf.mp hg
    have hgL₂ : L₂.map (MulAut.conj g).toMonoidHom = L₂ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN₂
    refine Subgroup.mem_inf.mpr ⟨hgA, Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_⟩
    rcases hB.perm g hgA with ⟨h1, -⟩ | ⟨h1, h2⟩
    · exact h1
    · exfalso
      exact hB.ne (h2.symm.trans hgL₂).symm
  · intro g hg
    obtain ⟨hgA, hgN⟩ := Subgroup.mem_inf.mp hg
    have hgL : L.map (MulAut.conj g).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgN
    refine Subgroup.mem_inf.mpr ⟨hgA, Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_⟩
    rcases hB.perm g hgA with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exfalso
      exact hB.ne (h1.symm.trans hgL)

theorem s16h_e3_Z3NineAAAAA_K1_pcore_bot
    {W : Type} [CommGroup W] [Finite W]
    {A L L₂ : Subgroup (MulAut W)} {x : MulAut W}
    (hB : s16h_Z3Blocks A L L₂ x)
    (hrk : rk ↥(commSub (⊤ : Subgroup W) L) = 6)
    (hO2 : ∀ P : Subgroup (MulAut W), P ≤ A → (P.subgroupOf A).Normal → IsPGroup 2 P → P = ⊥) :
    pCore 2 ↥(A ⊓ centSub (commSub (⊤ : Subgroup W) L₂)) = ⊥ := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let U₂ : Subgroup W := commSub (⊤ : Subgroup W) L₂
  let K1 : Subgroup (MulAut W) := A ⊓ centSub U₂
  let N : Subgroup (MulAut W) := A ⊓ Subgroup.normalizer (L : Set (MulAut W))
  have hK1leN : K1 ≤ N :=
    s16h_e3_Z3NineAAAAA_cent_le_normalizer hB (by simpa only [U₂] using hrk)
  have hcomp_x : ((MulAut.conj x⁻¹).toMonoidHom).comp ((MulAut.conj x).toMonoidHom) =
      MonoidHom.id (MulAut W) := by
    ext l
    simp only [MonoidHom.comp_apply, MonoidHom.id_apply, MulAut.conj_apply,
      MulEquiv.coe_toMonoidHom]
    group
  have hxinvL₂ : L₂.map (MulAut.conj x⁻¹).toMonoidHom = L := by
    calc L₂.map (MulAut.conj x⁻¹).toMonoidHom
        = (L.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom := by
          rw [hB.eq]
      _ = L.map (((MulAut.conj x⁻¹).toMonoidHom).comp ((MulAut.conj x).toMonoidHom)) := by
          rw [← Subgroup.map_map]
      _ = L.map (MonoidHom.id (MulAut W)) := by rw [hcomp_x]
      _ = L := by rw [Subgroup.map_id]
  have hK1_normal_N : (K1.subgroupOf N).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hK1leN]
    intro k n hk hn
    obtain ⟨hkA, hkU₂⟩ := Subgroup.mem_inf.mp hk
    obtain ⟨hnA, hnN⟩ := Subgroup.mem_inf.mp hn
    have hnL : L.map (MulAut.conj n).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hnN
    have hnstab := hB.stab n hnA hnL
    refine Subgroup.mem_inf.mpr ⟨A.mul_mem (A.mul_mem hnA hkA) (A.inv_mem hnA), ?_⟩
    rw [mem_centSub]
    intro v hv
    have hnv : n⁻¹ v ∈ U₂ := by
      have h : n (n⁻¹ v) ∈ U₂ := by simpa using hv
      exact (mem_stabSub.mp hnstab.2 (n⁻¹ v)).1 h
    have hfix : k (n⁻¹ v) = n⁻¹ v := mem_centSub.mp hkU₂ (n⁻¹ v) hnv
    change (n * k * n⁻¹) v = v
    rw [MulAut.mul_apply, MulAut.mul_apply, hfix, MulAut.apply_inv_self]
  have hN_le_normK1 : N ≤ Subgroup.normalizer (K1 : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK1leN).mp hK1_normal_N
  have hA_map : A.map (MulAut.conj x).toMonoidHom = A := by
    simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.mp (A.le_normalizer hB.mem))
  have hNmap : N.map (MulAut.conj x).toMonoidHom = N := by
    change (A ⊓ Subgroup.normalizer (L : Set (MulAut W))).map
        (MulAut.conj x).toMonoidHom =
      A ⊓ Subgroup.normalizer (L : Set (MulAut W))
    rw [Subgroup.map_inf A (Subgroup.normalizer (L : Set (MulAut W)))
      (MulAut.conj x).toMonoidHom (MulAut.conj x).injective]
    rw [hA_map]
    rw [Subgroup.map_normalizer_eq_of_bijective L (MulAut.conj x).bijective]
    rw [← hB.eq]
    exact s16h_e3_Z3NineAAAAA_inf_normalizer_L₂_eq hB
  have hN_le_norm_ON : N ≤ Subgroup.normalizer ((pCoreOf 2 N) : Set (MulAut W)) :=
    le_normalizer_pCoreOf 2 N
  have hx_ON : ((pCoreOf 2 N).map (MulAut.conj x).toMonoidHom) = pCoreOf 2 N := by
    have h := pCoreOf_map_mulEquiv 2 (MulAut.conj x) N
    rw [hNmap] at h
    exact h.symm
  have hA_le_norm_ON : A ≤ Subgroup.normalizer ((pCoreOf 2 N) : Set (MulAut W)) := by
    intro a ha
    rcases hB.perm a ha with ⟨haL, -⟩ | ⟨haL, -⟩
    · exact hN_le_norm_ON ⟨ha, Subgroup.mem_normalizer_iff_map_conj_eq.mpr haL⟩
    · have hnA : x⁻¹ * a ∈ A := A.mul_mem (A.inv_mem hB.mem) ha
      have hnN : x⁻¹ * a ∈ N := by
        refine ⟨hnA, Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_⟩
        calc L.map (MulAut.conj (x⁻¹ * a)).toMonoidHom
            = L.map ((MulAut.conj x⁻¹ * MulAut.conj a)).toMonoidHom := by rw [map_mul]
          _ = L.map (((MulAut.conj x⁻¹).toMonoidHom).comp
                ((MulAut.conj a).toMonoidHom)) := rfl
          _ = (L.map (MulAut.conj a).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom := by
                rw [← Subgroup.map_map]
          _ = L₂.map (MulAut.conj x⁻¹).toMonoidHom := by rw [haL]
          _ = L := hxinvL₂
      have hxnorm : x ∈ Subgroup.normalizer ((pCoreOf 2 N) : Set (MulAut W)) :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr hx_ON
      have hnnorm : x⁻¹ * a ∈ Subgroup.normalizer ((pCoreOf 2 N) : Set (MulAut W)) :=
        hN_le_norm_ON hnN
      have hmul : x * (x⁻¹ * a) ∈
          Subgroup.normalizer ((pCoreOf 2 N) : Set (MulAut W)) :=
        Subgroup.mul_mem _ hxnorm hnnorm
      simpa using hmul
  have hON_le_A : pCoreOf 2 N ≤ A := (pCoreOf_le 2 N).trans inf_le_left
  have hON_normal : ((pCoreOf 2 N).subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hON_le_A).mpr hA_le_norm_ON
  have hON_isP : IsPGroup 2 (pCoreOf 2 N) := pCoreOf_isPGroup 2 N
  have hONbot : pCoreOf 2 N = ⊥ := hO2 (pCoreOf 2 N) hON_le_A hON_normal hON_isP
  have hOK1_le_ON : pCoreOf 2 K1 ≤ pCoreOf 2 N := by
    refine le_pCoreOf 2 ?_ ?_ ?_
    · exact (pCoreOf_le 2 K1).trans hK1leN
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer ((pCoreOf_le 2 K1).trans hK1leN)]
      exact hN_le_normK1.trans (normalizer_le_normalizer_pCoreOf 2 K1)
    · exact pCoreOf_isPGroup 2 K1
  have hOK1bot : pCoreOf 2 K1 = ⊥ := le_bot_iff.mp (hOK1_le_ON.trans (le_of_eq hONbot))
  have hK1pcoreOf : (pCore 2 ↥K1).map K1.subtype = ⊥ := hOK1bot
  exact (Subgroup.map_eq_bot_iff_of_injective (pCore 2 ↥K1) K1.subtype_injective).mp hK1pcoreOf

end CFSG.LocalAnalysis.UniquenessCase.PartTwo