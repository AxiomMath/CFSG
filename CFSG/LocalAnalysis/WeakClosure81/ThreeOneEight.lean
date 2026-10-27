module

public import CFSG.LocalAnalysis.WeakClosure81.ThreeOneMap
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisGL3
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

namespace ThreeOne

private theorem centralizer_subgroupOf_eq {G : Type} [Group G] {K Q : Subgroup G}
    (hQK : Q ≤ K) (hQe : IsElemAbelian 2 Q)
    (hCQ : K ⊓ Subgroup.centralizer (Q : Set G) ≤ Q) :
    Subgroup.centralizer ((Q.subgroupOf K : Subgroup ↥K) : Set ↥K) = Q.subgroupOf K := by
  refine le_antisymm (fun x hx => ?_)
    (Subgroup.le_centralizer_iff_isMulCommutative.mpr (IsElemAbelian.subgroupOf hQe K).1)
  rw [Subgroup.mem_subgroupOf]
  refine hCQ ⟨x.2, ?_⟩
  change ∀ q ∈ Q, q * (x : G) = (x : G) * q
  intro q hq
  exact congrArg Subtype.val (hx ⟨q, hQK hq⟩ (Subgroup.mem_subgroupOf.mpr hq))

private theorem isL3_quotient_of_card_1344 {H : Type} [Group H] [Finite H] (V : Subgroup H)
    [V.Normal] (hVab : IsElemAbelian 2 V) (hV8 : Nat.card V = 8)
    (hC : Subgroup.centralizer (V : Set H) = V) (h1344 : Nat.card H = 1344) :
    IsL3 (H ⧸ V) 1 := by
  have hN : Subgroup.normalizer (V : Set H) = ⊤ := Subgroup.normalizer_eq_top V
  have h56 : 56 ∣ ((Subgroup.centralizer (V : Set H)).subgroupOf
      (Subgroup.normalizer (V : Set H))).index := by
    have hrel : ((Subgroup.centralizer (V : Set H)).subgroupOf
        (Subgroup.normalizer (V : Set H))).index = 168 := by
      change (Subgroup.centralizer (V : Set H)).relIndex
        (Subgroup.normalizer (V : Set H)) = 168
      rw [hN, Subgroup.relIndex_top_right, hC, Subgroup.index_eq_card_div, h1344, hV8]
    rw [hrel]
    norm_num
  obtain ⟨θ, hθsurj, hθker⟩ :=
    CFSG.ComponentClassification.GHarris.exists_GL32_of_dvd_index (G := H) hVab hV8 h56
  have hmemN : ∀ x : H, x ∈ Subgroup.normalizer (V : Set H) :=
    fun x => le_of_eq hN.symm (Subgroup.mem_top x)
  let ψ : H →* GL (Fin 3) (ZMod 2) :=
    MonoidHom.mk' (fun x : H => θ ⟨x, hmemN x⟩)
      (fun x y => by
        rw [← map_mul]
        exact congrArg θ (Subtype.ext rfl))
  have hψ_apply : ∀ x : H, ψ x = θ ⟨x, hmemN x⟩ := fun _ => rfl
  have hψker : ψ.ker = V := by
    ext x
    rw [MonoidHom.mem_ker, hψ_apply, ← MonoidHom.mem_ker, hθker, Subgroup.mem_subgroupOf, hC]
  have hψsurj : Function.Surjective ψ := fun g => by
    obtain ⟨n, hn⟩ := hθsurj g
    refine ⟨(n : H), ?_⟩
    rw [hψ_apply]
    have hn' : (⟨(n : H), hmemN (n : H)⟩ : ↥(Subgroup.normalizer (V : Set H))) = n :=
      Subtype.ext rfl
    rw [hn', hn]
  have he : (H ⧸ V) ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) :=
    ((QuotientGroup.quotientMulEquivOfEq hψker).symm.trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)).trans
        CFSG.ComponentClassification.GHarris.SL32EquivGL32.symm
  exact isL3_of_mulEquiv he

theorem isE8L3_of_isElemAbelian {G : Type} [Group G] [Finite G] {K Q : Subgroup G}
    (h1344 : Nat.card K = 1344) (hQK : Q ≤ K) (hQ : (Q.subgroupOf K).Normal)
    (hQe : IsElemAbelian 2 Q) (hQ8 : Nat.card Q = 8)
    (hCQ : K ⊓ Subgroup.centralizer (Q : Set G) ≤ Q) : IsE8L3 K := by
  haveI : (Q.subgroupOf K).Normal := hQ
  have hV8 : Nat.card (Q.subgroupOf K) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv, hQ8]
  have hC : Subgroup.centralizer ((Q.subgroupOf K : Subgroup ↥K) : Set ↥K) = Q.subgroupOf K :=
    centralizer_subgroupOf_eq hQK hQe hCQ
  exact ⟨Q, hQ, hQK, hQe, hQ8,
    isL3_quotient_of_card_1344 (Q.subgroupOf K) (IsElemAbelian.subgroupOf hQe K) hV8 hC h1344⟩

end ThreeOne

end CFSG.LocalAnalysis.WeakClosure81

end
