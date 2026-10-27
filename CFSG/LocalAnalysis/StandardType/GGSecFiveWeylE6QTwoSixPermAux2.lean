module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixPermAux
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoSixCenter
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection6.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Gorenstein.Chapter8_2
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
public import CFSG.GroupTheory.CardSupInf
public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.StandardType.E6QTwo

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)
open InndiagSU
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
variable {Bs L : Subgroup G} {x : G}

noncomputable def e6QTwoSixConjOnQuot
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (g : ↥L) : MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
  (MulAut.congr θ) (e6QTwoQuotCenterAutHom ↥L (MulAut.conj g))

theorem e6QTwoSixConjOnQuot_mk
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (g l : ↥L) :
    e6QTwoSixConjOnQuot θ g (θ (QuotientGroup.mk' (Subgroup.center L) l)) =
      θ (QuotientGroup.mk' (Subgroup.center L) (g * l * g⁻¹)) := by
  rw [e6QTwoSixConjOnQuot, e6QTwoMulAutCongrApply, e6QTwoQuotCenterAutHom_mk,
    MulAut.conj_apply]

noncomputable def e6QTwoSixPermPre (hK : Nat.card K = 4) {Q : GL (Fin 6) K}
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK) (idGram K 6))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (τ : Equiv.Perm (Fin 6)) : ↥L :=
  Classical.choose (QuotientGroup.mk'_surjective (Subgroup.center ↥L)
    (θ.symm (frameMk (USixTwo.fieldDataFour hK) Q hQ (USixTwo.permGLSU hK τ))))

theorem e6QTwoSixPermPre_spec (hK : Nat.card K = 4) {Q : GL (Fin 6) K}
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK) (idGram K 6))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (τ : Equiv.Perm (Fin 6)) :
    θ (QuotientGroup.mk' (Subgroup.center L) (e6QTwoSixPermPre hK hQ θ τ)) =
      frameMk (USixTwo.fieldDataFour hK) Q hQ (USixTwo.permGLSU hK τ) := by
  classical
  rw [show QuotientGroup.mk' (Subgroup.center L) (e6QTwoSixPermPre hK hQ θ τ) =
      θ.symm (frameMk (USixTwo.fieldDataFour hK) Q hQ (USixTwo.permGLSU hK τ)) from
    Classical.choose_spec (QuotientGroup.mk'_surjective (Subgroup.center ↥L)
      (θ.symm (frameMk (USixTwo.fieldDataFour hK) Q hQ (USixTwo.permGLSU hK τ)))),
    MulEquiv.apply_symm_apply]

theorem e6QTwoSixConjOnQuot_permPre (hK : Nat.card K = 4) {Q : GL (Fin 6) K}
    (hQ : Q ∈ primeFormUnitary (USixTwo.fieldDataFour hK) (idGram K 6))
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (τ : Equiv.Perm (Fin 6)) :
    e6QTwoSixConjOnQuot θ (e6QTwoSixPermPre hK hQ θ τ) = e6QTwoSixFramePerm hK hQ τ := by
  rw [e6QTwoSixConjOnQuot, e6QTwoQuotCenterAutHom_conj,
    ← e6QTwoMulAutConjCongr θ (QuotientGroup.mk' (Subgroup.center L) (e6QTwoSixPermPre hK hQ θ τ)),
    e6QTwoSixPermPre_spec hK hQ θ τ]
  rfl

theorem e6QTwoSixFrameAction_conj
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) {g : G} (hgL : g ∈ L)
    {b : ↥Bs} (hb : g * (b : G) * g⁻¹ ∈ Bs) :
    e6QTwoSixFrameAction hNL θ ⟨g * (b : G) * g⁻¹, hb⟩ =
      e6QTwoSixConjOnQuot θ ⟨g, hgL⟩ * e6QTwoSixFrameAction hNL θ b *
        (e6QTwoSixConjOnQuot θ ⟨g, hgL⟩)⁻¹ := by
  let Φ : MulAut ↥L →* MulAut (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
    (MulAut.congr θ).toMonoidHom.comp (e6QTwoQuotCenterAutHom ↥L)
  have hconj : e6QTwoBstarConjAction hNL ⟨g * (b : G) * g⁻¹, hb⟩ =
      MulAut.conj (⟨g, hgL⟩ : ↥L) * e6QTwoBstarConjAction hNL b *
        (MulAut.conj (⟨g, hgL⟩ : ↥L))⁻¹ := by
    ext l
    rw [e6QTwoBstarConjAction_apply]
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, Subgroup.coe_mul,
      Subgroup.coe_inv]
    rw [e6QTwoBstarConjAction_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hβ : e6QTwoSixFrameAction hNL θ ⟨g * (b : G) * g⁻¹, hb⟩ =
      Φ (e6QTwoBstarConjAction hNL ⟨g * (b : G) * g⁻¹, hb⟩) := rfl
  have hβb : e6QTwoSixFrameAction hNL θ b = Φ (e6QTwoBstarConjAction hNL b) := rfl
  have hw : e6QTwoSixConjOnQuot θ ⟨g, hgL⟩ = Φ (MulAut.conj (⟨g, hgL⟩ : ↥L)) := rfl
  rw [hβ, hβb, hw, hconj, map_mul, map_mul, map_inv]

theorem e6QTwoSixFrameAction_ker_eq
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) (hperf : commutator ↥L = ⊤)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x) :
    (e6QTwoSixFrameAction hNL θ).ker = (Subgroup.zpowers x).subgroupOf Bs := by
  rw [e6QTwoSixFrameAction_ker hNL θ hperf, hBL]

theorem e6QTwoSixFrameAction_eq_one_iff (θ : L ⧸ Subgroup.center L ≃*
    LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) (hperf : commutator ↥L = ⊤)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x) (b : ↥Bs) :
    e6QTwoSixFrameAction hNL θ b = 1 ↔ (b : G) ∈ Subgroup.zpowers x := by
  rw [← MonoidHom.mem_ker, e6QTwoSixFrameAction_ker_eq θ hNL hperf hBL,
    Subgroup.mem_subgroupOf]

variable {G : Type} [Group G] [Finite G] {K : Type} [Field K] [Finite K]
variable {Bs L : Subgroup G} {x : G}

theorem e6QTwoSixNormalizesCenter
    {Bs L : Subgroup G}
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) :
    Bs ≤ Subgroup.normalizer ((L ⊓ Subgroup.centralizer (L : Set G)) : Set G) := by
  have hC : Bs ≤ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
    hNL.trans (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup L)
  exact (le_inf hNL hC).trans
    (Subgroup.inf_normalizer_le_normalizer_inf (H := L)
      (K := Subgroup.centralizer (L : Set G)))

private theorem e6QTwoSix_index_eq
    (hBZ : Bs ≤ Subgroup.normalizer
    ((L ⊓ Subgroup.centralizer (L : Set G)) : Set G)) :
    (Bs.subgroupOf (Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G)))).index =
      ((Bs ⊓ (L ⊓ Subgroup.centralizer (L : Set G))).subgroupOf
        (L ⊓ Subgroup.centralizer (L : Set G))).index := by
  set Z : Subgroup G := L ⊓ Subgroup.centralizer (L : Set G)
  have hsup : Nat.card ↥(Bs ⊔ Z) * Nat.card ↥(Bs ⊓ Z) = Nat.card ↥Bs * Nat.card ↥Z :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hBZ
  have h1 : (Bs.subgroupOf (Bs ⊔ Z)).index * Nat.card ↥Bs = Nat.card ↥(Bs ⊔ Z) := by
    have h := Subgroup.relIndex_mul_card (H := Bs) (K := Bs ⊔ Z)
    rwa [inf_eq_left.mpr le_sup_left] at h
  have h2 : ((Bs ⊓ Z).subgroupOf Z).index * Nat.card ↥(Bs ⊓ Z) = Nat.card ↥Z := by
    have h := Subgroup.relIndex_mul_card (H := Bs ⊓ Z) (K := Z)
    rw [show (Bs ⊓ Z) ⊓ Z = Bs ⊓ Z from by rw [inf_assoc, inf_idem]] at h
    exact h
  have hpos : 0 < Nat.card ↥(Bs ⊓ Z) := Nat.card_pos
  have hpos2 : 0 < Nat.card ↥Bs := Nat.card_pos
  have step : (Bs.subgroupOf (Bs ⊔ Z)).index * Nat.card ↥Bs =
      ((Bs ⊓ Z).subgroupOf Z).index * Nat.card ↥Bs := by
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    calc (Bs.subgroupOf (Bs ⊔ Z)).index * Nat.card ↥Bs * Nat.card ↥(Bs ⊓ Z)
        = Nat.card ↥(Bs ⊔ Z) * Nat.card ↥(Bs ⊓ Z) := by rw [h1]
      _ = Nat.card ↥Bs * Nat.card ↥Z := hsup
      _ = Nat.card ↥Bs * (((Bs ⊓ Z).subgroupOf Z).index * Nat.card ↥(Bs ⊓ Z)) := by rw [h2]
      _ = ((Bs ⊓ Z).subgroupOf Z).index * Nat.card ↥Bs * Nat.card ↥(Bs ⊓ Z) := by ring
  exact Nat.eq_of_mul_eq_mul_right hpos2 step

private theorem e6QTwoSix_pow_three_mem
    (hK : Nat.card K = 4)
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hx : x ∈ Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) {z : G} (hzL : z ∈ L)
    (hzc : z ∈ Subgroup.centralizer (L : Set G)) {k : ℕ} (hz : z ^ 3 ^ k = 1) : z ∈ Bs := by
  have hmem := mem_zpowers_of_mem_center hK θ hperf hBs hBL hstar hNL hzL
    (fun l hl => (Subgroup.mem_centralizer_iff.mp hzc l hl).symm) hz
  exact Subgroup.zpowers_le.mpr hx hmem

theorem e6QTwoSixSylowIndex
    (hK : Nat.card K = 4) {x : G}
    (θ : L ⧸ Subgroup.center L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (hperf : commutator ↥L = ⊤) (hBs : IsElemAbelian 3 Bs) (hx : x ∈ Bs)
    (hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (hNL : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ¬ 3 ∣ (Bs.subgroupOf (Bs ⊔ (L ⊓ Subgroup.centralizer (L : Set G)))).index := by
  classical
  set Z : Subgroup G := L ⊓ Subgroup.centralizer (L : Set G)
  rw [e6QTwoSix_index_eq (e6QTwoSixNormalizesCenter hNL)]
  obtain ⟨P⟩ := Sylow.nonempty (p := 3) (G := ↥Z)
  have hPle : (P : Subgroup ↥Z) ≤ (Bs ⊓ Z).subgroupOf Z := by
    intro z hz
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨k, hk⟩ := (P.isPGroup'.exists_orderOf_dvd_pow (⟨z, hz⟩ : ↥P))
    have hzk : (z : G) ^ 3 ^ k = 1 := by
      have h1 : orderOf (z : ↥Z) ∣ 3 ^ k := by
        rw [← Subgroup.orderOf_mk (H := (P : Subgroup ↥Z)) z hz]
        exact hk
      have h2 : (z : ↥Z) ^ 3 ^ k = 1 := orderOf_dvd_iff_pow_eq_one.mp h1
      simpa using congrArg (fun w : ↥Z => (w : G)) h2
    refine ⟨e6QTwoSix_pow_three_mem hK θ hperf hBs hx hBL hstar hNL z.2.1 z.2.2 hzk, z.2⟩
  have hdvd : ((Bs ⊓ Z).subgroupOf Z).index ∣ (P : Subgroup ↥Z).index :=
    Subgroup.index_dvd_of_le hPle
  have h3 : ¬ 3 ∣ (P : Subgroup ↥Z).index := Sylow.not_dvd_index P
  exact fun h => h3 (h.trans hdvd)

end CFSG.StandardType.E6QTwo

end
