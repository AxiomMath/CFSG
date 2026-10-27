module

public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derModelDefs
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derLayer
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derSpComm
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derFixOrth
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derLayerSimple
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derPrePairTrans
public import CFSG.LocalAnalysis.StandardType.GGTBJNoB2derPrePairCent
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggB2der_prepair {G : Type} [Group G] [Finite G] {B : Subgroup G} {x : G} {L : Subgroup G}
    {hBL : B ≤ Subgroup.normalizer (L : Set G)} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2) {ψ : ↥L →* LargeEvenProj (LargeEvenSpGroup K 4)}
    {β : ↥B →* LargeEvenProj (LargeEvenSpGroup K 4)} (hM : GGB2derModelProp B L hBL ψ β)
    (hperf : commutator ↥L = ⊤) (hZ2 : IsPGroup 2 (Subgroup.center ↥L))
    (hB : IsElemAbelian 3 B) (hxB : x ∈ B) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hβx : β.ker.map B.subtype = Subgroup.zpowers x)
    {e : LargeEvenProj (LargeEvenSpGroup K 4)} (heE : e ∈ β.range) (he1 : e ≠ 1)
    (he6 : Module.finrank K (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers e)) = 6)
    (hkere : ∀ a ∈ β.range,
      (∀ v ∈ SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers e),
        (SmallRule.spRep a : Module.End K (Fin 4 ⊕ Fin 4 → K)) v = v) →
      a ∈ Subgroup.zpowers e) :
    ∃ D₁ J₁ : Subgroup G, LargeEvenStdSubPre 3 B x L D₁ J₁ ∧ ¬ LargeEvenSmall J₁ := by
  classical
  obtain ⟨b₀, hb₀⟩ := MonoidHom.mem_range.mp heE
  have hb03 : b₀ ^ 3 = 1 := Subtype.ext (by simpa using hB.2 (b₀ : G) b₀.2)
  have hb03G : (b₀ : G) ^ 3 = 1 := by simpa using congrArg Subtype.val hb03
  have hb0B : (b₀ : G) ∈ B := b₀.2
  have hb0_not_mem : (b₀ : G) ∉ Subgroup.zpowers x := by
    intro hb0x
    have hb0ker : b₀ ∈ β.ker := by
      have hmem : (b₀ : G) ∈ β.ker.map B.subtype := by rw [hβx]; exact hb0x
      rcases Subgroup.mem_map.mp hmem with ⟨k, hk, hkval⟩
      exact (Subtype.ext hkval) ▸ hk
    exact he1 (by rw [← hb₀]; exact MonoidHom.mem_ker.mp hb0ker)
  have hcardx : Nat.card (Subgroup.zpowers x) = 3 ^ 1 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1, pow_one]
  have hcomm_x_b0 : ∀ e ∈ Subgroup.zpowers x, e * (b₀ : G) = (b₀ : G) * e := by
    intro e he
    exact CFSG.Open.IsElemAbelian.comm hB (Subgroup.zpowers_le.mpr hxB he) hb0B
  obtain ⟨hDEA, hDcard⟩ := isElemAbelian_sup_zpowers_of_card (G := G) (p := 3) Nat.prime_three
    (CFSG.Open.isElemAbelian_zpowers hx3) hcardx hb03G hb0_not_mem hcomm_x_b0
  let D₁ : Subgroup G := Subgroup.zpowers x ⊔ Subgroup.zpowers (b₀ : G)
  have hb0norm : (b₀ : G) ∈ Subgroup.normalizer (L : Set G) := hBL b₀.2
  set e' : MulAut ↥L := L.normalizerMonoidHom (Subgroup.inclusion hBL b₀) with he'
  have hg : ∀ l : ↥L, ψ (e' l) = e * ψ l * e⁻¹ := by
    intro l
    have h := hM.conj b₀ l
    rw [hb₀, ← he'] at h
    exact h
  have he1' : e' ≠ 1 := by
    intro h1
    have hcen : e ∈ Subgroup.center (LargeEvenProj (LargeEvenSpGroup K 4)) := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hM.surj r
      have h := hM.conj b₀ l
      rw [hb₀, ← he', h1] at h
      simp only [MulAut.one_apply] at h
      have hcomm' : ψ l * e = e * ψ l := by
        have h2 := congrArg (fun y => y * e) h
        rw [h2]
        group
      exact hcomm'
    have hebot : e ∈ (⊥ : Subgroup (LargeEvenProj (LargeEvenSpGroup K 4))) := by
      rw [← TableBSymp.center_spProj_eq_bot (K := K) (m := 4)]
      exact hcen
    exact he1 (Subgroup.mem_bot.mp hebot)
  have he3' : e' ^ 3 = 1 := by
    have hinc : (Subgroup.inclusion hBL b₀) ^ 3 = 1 := by
      rw [← map_pow, hb03, map_one]
    rw [he', ← map_pow, hinc, map_one]
  have he3e : e ^ 3 = 1 := by
    rw [← hb₀, ← map_pow, hb03, map_one]
  obtain ⟨hcompl, -, -, -⟩ := ggB2der_fix_orth_decomp (K := K) hK SmallRule.spRep
    (SmallRule.spBilin K 4) SmallRule.spBilin_nondegenerate SmallRule.spBilin_isRefl
    SmallRule.spRep_isometry he3e
  obtain ⟨hcompA, hmapA, hsmallA⟩ :=
    ggB2der_layer_sixfix (K := K) hK (L' := ↥L) ψ hM.surj hM.ker_eq.le hperf hZ2
      (e := e') he1' he3' (g := e) hg he6
  obtain ⟨-, hSWcomm, -⟩ := ggB2der_spFixPerp_simple (K := K) hK he6 hcompl
  have hmapAeq : (LargeEvenLayer (ggFixSub e')).map ψ =
      ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers e)) :=
    hmapA.trans hSWcomm
  let A : Subgroup ↥L := ggFixSub e'
  have hLayerA : LargeEvenLayer A ≤ A := sSup_le fun _ hK => hK.1
  have hAdef : A = ggFixSub (L.normalizerMonoidHom ⟨(b₀ : G), hb0norm⟩) := by
    show ggFixSub e' = ggFixSub (L.normalizerMonoidHom ⟨(b₀ : G), hb0norm⟩)
    rfl
  obtain ⟨-, hLayermap, hcompTrans, hsmallTrans⟩ :=
    ggB2der_layer_transfer (x := x) (b := (b₀ : G)) hb0norm hxL (A := A) hAdef
  let J₁ : Subgroup G := (LargeEvenLayer A).map L.subtype
  have hJ₁eq : J₁ = LargeEvenLayer (L ⊓ Subgroup.centralizer (D₁ : Set G)) := hLayermap
  have hcompJ : IsComponentOf J₁ (L ⊓ Subgroup.centralizer (D₁ : Set G)) := hcompTrans hcompA
  have hsmallJ : ¬ LargeEvenSmall J₁ := hsmallTrans hsmallA
  have hJ₁_le_L : J₁ ≤ L := Subgroup.map_subtype_le (LargeEvenLayer A)
  have hxC_J : x ∈ Subgroup.centralizer (J₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact Subgroup.mem_centralizer_iff.mp hxL j (hJ₁_le_L hj)
  have hb0C_J : (b₀ : G) ∈ Subgroup.centralizer (J₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hj
    have haA : a ∈ A := hLayerA ha
    have hea : e' a = a := haA
    have hcoe : ((e' a : ↥L) : G) = (b₀ : G) * (a : G) * (b₀ : G)⁻¹ := by
      rw [he']
      exact Subgroup.normalizerMonoidHom_apply_apply_coe L (Subgroup.inclusion hBL b₀) a
    have hconj : (b₀ : G) * (a : G) * (b₀ : G)⁻¹ = (a : G) := by
      simp only [← hcoe, hea]
    calc (a : G) * (b₀ : G) = ((b₀ : G) * (a : G) * (b₀ : G)⁻¹) * (b₀ : G) := by
          simp only [hconj]
      _ = (b₀ : G) * (a : G) := by group
  have hD_le : D₁ ≤ B ⊓ Subgroup.centralizer (J₁ : Set G) :=
    le_inf (sup_le (Subgroup.zpowers_le.mpr hxB) (Subgroup.zpowers_le.mpr hb0B))
      (sup_le (Subgroup.zpowers_le.mpr hxC_J) (Subgroup.zpowers_le.mpr hb0C_J))
  have hkere' : ∀ a ∈ β.range,
      (∀ v ∈ SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers e),
        (SmallRule.spRep a : Module.End K (Fin 4 ⊕ Fin 4 → K)) v = v) →
      a ∈ Subgroup.zpowers (β b₀) := by
    intro a ha hfix
    rw [hb₀]
    exact hkere a ha hfix
  have hψJ' : (LargeEvenLayer A).map ψ =
      ggSpFixPerp (SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers e)) := hmapAeq
  have hle_D : B ⊓ Subgroup.centralizer (J₁ : Set G) ≤ D₁ := by
    intro g hg
    rcases Subgroup.mem_inf.mp hg with ⟨hgB, hgC⟩
    have hc : ∀ j ∈ LargeEvenLayer A,
        ((⟨g, hgB⟩ : ↥B) : G) * (j : G) = (j : G) * ((⟨g, hgB⟩ : ↥B) : G) := by
      intro j hj
      have hmem : (j : G) ∈ J₁ := ⟨j, hj, rfl⟩
      exact (Subgroup.mem_centralizer_iff.mp hgC (j : G) hmem).symm
    have hres := ggB2der_centralizer_eq (K := K) hK hM hβx (b := b₀)
      (W := SmallRule.fixSpaceOf SmallRule.spRep (Subgroup.zpowers e)) hcompl hkere' hψJ'
      ⟨g, hgB⟩ hc
    simpa using hres
  refine ⟨D₁, J₁, ?_, hsmallJ⟩
  refine ⟨?_, hDEA, ?_, ?_, hJ₁eq, hcompJ, ?_⟩
  · exact sup_le (Subgroup.zpowers_le.mpr hxB) (Subgroup.zpowers_le.mpr hb0B)
  · simpa using hDcard
  · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x)
  · exact le_antisymm hD_le hle_D

end CFSG.StandardType
