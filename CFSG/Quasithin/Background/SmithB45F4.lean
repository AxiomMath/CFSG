module

public import CFSG.Quasithin.Background.SmithB45TorF4
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LieType.Ree.LargeReeFixedGroupOddCore
public import CFSG.Quasithin.Background.SmithB45TorCrit

public section

namespace CFSG.Quasithin

open CFSG.Blueprint

namespace B45F4

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

open CFSG.Quasithin.B42Disp CFSG.Quasithin.B45Disp CFSG.Quasithin.B42F4
open CFSG.ComponentClassification.UnbalancedCatalog
  (large_Ree_full_inner_field_automorphism_normal_form mem_inner_of_sq_eq_one_of_odd)

variable
  {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem classTests_reeGamma (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) {V : Type*}
    [CommGroup V] [Finite V] (hV : ∀ v : V, v * v = 1) (L : Subgroup (MulAut V))
    (hZL : Subgroup.center L = ⊥) (e : L ⧸ Subgroup.center L ≃* F4.reeGamma K a) :
    B45Tor.ClassTests V L e (fun ξ => IsTConj a K (ξ : ModGL F4.tag K)) (6 * (2 * a + 1) - 1)
      (3 * (2 * a + 1) - 1) 0 := by
  have := finite_modGL (τ := F4.tag) (K := K)
  set f := 2 * a + 1 with hf
  have hq6 : (2 ^ f) ^ 6 = 2 ^ (6 * f) := by rw [← pow_mul, mul_comm]
  have hq3 : (2 ^ f) ^ 3 = 2 ^ (3 * f) := by rw [← pow_mul, mul_comm]
  have hodd : Odd (Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (F4.reeGamma K a))) := by
    obtain ⟨-, -, -, -, hcard, -⟩ :=
      large_Ree_full_inner_field_automorphism_normal_form a ha K hK
    rw [hcard]
    exact ⟨a, rfl⟩
  have hinner : ∀ α : MulAut (F4.reeGamma K a), α * α = 1 →
      α ∈ (MulAut.conj : F4.reeGamma K a →* MulAut (F4.reeGamma K a)).range := fun α hα =>
    mem_inner_of_sq_eq_one_of_odd hodd (by rw [sq]; exact hα)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro E hE
    have hlt := card_lt_of_isElem2 ha hK hE.1 hE.2
    rw [hq6] at hlt
    exact card_le_two_pow_pred (fun x => Subtype.ext (hE.2 _ x.2)) hlt
  ·
    intro E hE hpure
    have hlt := card_lt_of_pureZ ha hK hE.1 hE.2 (fun g hg hg1 => by
      have hg1' : (g : ModGL F4.tag K) ≠ 1 := fun h => hg1 (Subtype.ext h)
      have hsq : (g : ModGL F4.tag K) ^ 2 = 1 := by
        rw [← Subgroup.coe_pow, hE.2 g hg, Subgroup.coe_one]
      rcases isZConj_or_isTConj ha hK g.2 hsq hg1' with hz | ht
      · exact hz
      · exact absurd ht (hpure g hg hg1))
    rw [hq3] at hlt
    exact card_le_two_pow_pred (fun x => Subtype.ext (hE.2 _ x.2)) hlt
  ·
    intro F hF
    have hle : F ≤ (MulAut.conj : F4.reeGamma K a →* MulAut (F4.reeGamma K a)).range :=
      fun α hα => hinner α (by rw [← sq]; exact hF.2 α hα)
    rw [inf_eq_left.2 hle, pow_zero, one_mul]
  ·
    intro x _ _ hxB
    refine lt_of_lt_of_le ?_ (B45Tor.two_pow_le_index_classT ha hK hV L hZL e hxB)
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)
  ·
    intro x hx2 hxo
    exfalso
    apply hxo
    apply hinner
    rw [← map_mul, show x * x = 1 from Subtype.ext hx2, map_one]
  ·
    intro E _ _ hpure
    left
    intro x hx2 hx1 hxE
    have hπ1 : modelProj L e x ≠ 1 := fun h =>
      hx1 (B45Tor.modelProj_injective L hZL e (h.trans (map_one _).symm))
    have hsq : ((modelProj L e x : F4.reeGamma K a) : ModGL F4.tag K) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow, sq, ← map_mul, show x * x = 1 from Subtype.ext hx2, map_one,
        Subgroup.coe_one]
    have hπ1' : ((modelProj L e x : F4.reeGamma K a) : ModGL F4.tag K) ≠ 1 :=
      fun h => hπ1 (Subtype.ext h)
    have hz : IsZConj a K ((modelProj L e x : F4.reeGamma K a) : ModGL F4.tag K) := by
      rcases isZConj_or_isTConj ha hK (modelProj L e x).2 hsq hπ1' with hz | ht
      · exact hz
      · exact absurd ht (hpure _ hxE hπ1)
    refine lt_of_lt_of_le ?_ (B45Tor.two_pow_le_index_classZ ha hK hV L hZL e hz)
    exact Nat.pow_lt_pow_right (by norm_num) (by omega)


end B45F4

theorem asB45ReeF4Large_holds :
    AsB45No2FFor B42TypeReeF4Large := by
  refine B45Tor.asB45No2FFor_of_classTests fun V _ _ hV L hq hirr hX => ?_
  obtain ⟨f, -, -, hmodel⟩ := hX
  obtain ⟨a, K, _, _, _, ha, hfa, hK, ⟨e⟩⟩ :=
    CFSG.QuasithinUnique.Setup.X6.exists_mulEquiv_largeRee_model hmodel
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  have hZL : Subgroup.center ↥L = ⊥ := by
    have : Group.IsPerfect ↥L := hq.1
    have : Finite (MulAut V) := B42Disp.finite_mulAut
    set π : ↥L →* LieType.Ree.reeFixed LieType.Ree.ReeTag.F4 K a :=
      (LieType.Ree.ReeTag.reeFixedEquivReeGamma K a).symm.toMonoidHom.comp
        (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))) with hπ
    have hπs : Function.Surjective π :=
      (LieType.Ree.ReeTag.reeFixedEquivReeGamma K a).symm.surjective.comp
        (e.surjective.comp (QuotientGroup.mk'_surjective _))
    have hker : π.ker = Subgroup.center ↥L := by
      ext l
      simp only [MonoidHom.mem_ker, hπ, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
        Function.comp_apply, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
    have h0 := CFSG.SectionRank.LargeRee.large_ree_perfect_odd_cover_trivial_of_suzuki
      CFSG.SectionRank.LargeRee.suzukiBlockInputs ha (by rw [hK']; rfl) π hπs hker.le
      (by rw [hker]; exact B45Disp.odd_card_center_of_isIrrSec hV hirr)
    rwa [hker] at h0
  exact ⟨hZL, LieType.Ree.ReeTag.F4.reeGamma K a, inferInstance, e, _, _, _, _,
    B45F4.classTests_reeGamma ha hK' (fun v => by rw [← pow_two]; exact hV v) L hZL e⟩

end CFSG.Quasithin
