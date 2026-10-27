module

public import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCore
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJInner
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJCoreA5J2
import CFSG.RankThree.PartTwo.Sec14.Wales1411WHJFactor

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo Equiv

namespace Wales1411W.HJProd

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  rfl

theorem map_eq_of_a6Cover_a5 {X : Type*} [Group X] [Finite X] {U V : Subgroup X} [hUn : U.Normal]
    [hVn : V.Normal] (hUV : U ⊓ V = ⊥) (hUVt : U ⊔ V = ⊤)
    (hU : Sec4.IsTripleCover ↥U (alternatingGroup (Fin 6)))
    (hV : Nonempty (↥V ≃* alternatingGroup (Fin 5))) (β : MulAut X) :
    V.map β.toMonoidHom = V := by
  obtain ⟨ψ⟩ := hV
  have hcenV : Function.Injective (MulAut.conj : ↥V →* MulAut ↥V) :=
    conj_injective_of_mulEquiv ψ a5_facts.1
  set N := V.map β.toMonoidHom with hN
  haveI hNn : N.Normal := hVn.map _ β.surjective
  have hcardN : Nat.card N = 60 := by
    rw [hN, Subgroup.card_map_of_injective β.injective, Nat.card_congr ψ.toEquiv,
      card_alternatingGroup_five]
  have hcardV : Nat.card V = 60 := by
    rw [Nat.card_congr ψ.toEquiv, card_alternatingGroup_five]
  haveI : IsSimpleGroup ↥N :=
    ((V.equivMapOfInjective β.toMonoidHom β.injective).symm.trans ψ).isSimpleGroup
  haveI : ((N ⊓ V).subgroupOf N).Normal := (Subgroup.normal_inf_normal N V).subgroupOf N
  rcases Subgroup.Normal.eq_bot_or_eq_top ((N ⊓ V).subgroupOf N) with h | h
  · exfalso
    have hNV : N ⊓ V = ⊥ := by
      rw [eq_bot_iff]
      intro k hk
      have hk' : (⟨k, hk.1⟩ : ↥N) ∈ (N ⊓ V).subgroupOf N := Subgroup.mem_subgroupOf.mpr hk
      rw [h, Subgroup.mem_bot] at hk'
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hk')
    have hcomm : ⁅N, V⁆ = ⊥ := le_bot_iff.mp (hNV ▸ Subgroup.commutator_le_inf N V)
    have hNC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hUVc : ⁅U, V⁆ = ⊥ := le_bot_iff.mp (hUV ▸ Subgroup.commutator_le_inf U V)
    have hUC := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hUVc
    have hNU : N ≤ U := by
      intro g hg
      have hgt : g ∈ ((U ⊔ V : Subgroup X) : Set X) := by rw [hUVt]; trivial
      rw [Subgroup.mul_normal U V] at hgt
      obtain ⟨u, hu, v, hv, rfl⟩ := hgt
      have hv1 : v = 1 := by
        have hvc : MulAut.conj (⟨v, hv⟩ : ↥V) = MulAut.conj 1 := by
          ext w
          have h1 := Subgroup.mem_centralizer_iff.mp (hNC hg) w w.2
          have h2 := Subgroup.mem_centralizer_iff.mp (hUC hu) w w.2
          simp only [MulAut.conj_apply, map_one, MulAut.one_apply, Subgroup.coe_mul,
            Subgroup.coe_inv]
          have h3 : (w : X) * v = v * w := by
            have e1 : (w : X) * (u * v) = u * v * w := h1
            have e2 : (w : X) * u = u * w := h2
            have e3 : u * (w * v) = u * (v * w) := by
              calc u * (w * v) = (u * w) * v := by group
                _ = (w * u) * v := by rw [e2]
                _ = w * (u * v) := by group
                _ = u * v * w := e1
                _ = u * (v * w) := by group
            exact mul_left_cancel e3
          rw [← h3, mul_inv_cancel_right]
        exact congrArg Subtype.val (hcenV hvc)
      rw [hv1]
      show u * 1 ∈ U
      rw [mul_one]
      exact hu
    obtain ⟨hZ, ⟨χ⟩⟩ := hU
    set N' := N.subgroupOf U with hN'
    have hcardN' : Nat.card N' = 60 := by
      rw [hN', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNU).toEquiv, hcardN]
    haveI hN'n : N'.Normal := hNn.subgroupOf U
    set q := QuotientGroup.mk' (Subgroup.center ↥U) with hq
    haveI : IsSimpleGroup (↥U ⧸ Subgroup.center ↥U) :=
      haveI : IsSimpleGroup (alternatingGroup (Fin 6)) :=
        alternatingGroup.isSimpleGroup (by simp)
      χ.isSimpleGroup
    haveI : (N'.map q).Normal := hN'n.map q (QuotientGroup.mk'_surjective _)
    rcases Subgroup.Normal.eq_bot_or_eq_top (N'.map q) with h' | h'
    · have hle : N' ≤ Subgroup.center ↥U := by
        have := (Subgroup.map_eq_bot_iff N').mp h'
        rwa [QuotientGroup.ker_mk'] at this
      have := Subgroup.card_le_of_le hle
      rw [hcardN', hZ] at this
      norm_num at this
    · have hdvd := Subgroup.card_map_dvd N' q
      rw [h', Subgroup.card_top, Nat.card_congr χ.toEquiv, card_alternatingGroup_six,
        hcardN'] at hdvd
      norm_num at hdvd
  · have hNV : N ≤ V := fun n hn => by
      have : (⟨n, hn⟩ : ↥N) ∈ (N ⊓ V).subgroupOf N := h ▸ Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.mp this).2
    exact Subgroup.eq_of_le_of_card_ge hNV (by rw [hcardN, hcardV])

end Wales1411W.HJProd

open Wales1411W Wales1411W.HJProd Wales1411W.HJFactor in
theorem ks1411HJCoreA6A5 : KS1411HJCoreA6A5 := by
  intro M _ _ Ybar Abar Xbar Rbar abar hset hX S T hS hT hST hsupp
  exfalso
  obtain ⟨U, V, hUn, hVn, hUV, hUVt, hU, ⟨ψ⟩⟩ := hX
  haveI := HJInner.normal_X hset
  have hA3 : ∀ g ∈ Abar, g ^ 3 = 1 := hset.isElemAbelian.2
  set V' : Subgroup M := V.map Xbar.subtype with hV'
  set ψ' : ↥V' ≃* alternatingGroup (Fin 5) :=
    (V.equivMapOfInjective Xbar.subtype (Subgroup.subtype_injective _)).symm.trans ψ with hψ'
  have hV'Y : V' ≤ Ybar := (Subgroup.map_subtype_le V).trans hset.le_Y
  have hN : ∀ m : M, m ∈ Subgroup.normalizer (V' : Set M) := by
    intro m
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨v, hv, rfl⟩ := hn
    have hmem : (MulAut.conjNormal (H := Xbar) m) v ∈ V := by
      rw [← map_eq_of_a6Cover_a5 hUV hUVt hU ⟨ψ⟩ (MulAut.conjNormal (H := Xbar) m)]
      exact ⟨v, hv, rfl⟩
    exact ⟨_, hmem, by simp [MulAut.conjNormal_apply]⟩
  obtain ⟨⟨e, heA, heV, hea⟩, -⟩ := a5_factor hset hV'Y ⟨ψ'⟩ (fun a _ => hN a)
  obtain ⟨σ, τ, hσ, -, hστ⟩ := a5_three_noncomm
  set x : M := ((ψ'.symm σ : ↥V') : M) with hx
  have hxV : x ∈ V' := (ψ'.symm σ).2
  have hx3 : x ^ 3 = 1 := by
    rw [hx, ← Subgroup.coe_pow, ← map_pow, ← hσ, pow_orderOf_eq_one, map_one, Subgroup.coe_one]
  have hxc : ¬ V' ≤ Subgroup.centralizer ({x} : Set M) := by
    intro hle
    apply hστ
    apply ψ'.symm.injective
    apply Subtype.ext
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hle (ψ'.symm τ).2)
    simp only [map_mul, Subgroup.coe_mul]
    exact h.symm
  have heY : ¬ Ybar ≤ Subgroup.centralizer ({e} : Set M) := fun h =>
    hea (hset.mem_zpowers e heA h)
  exact false_of_factor hV'Y (fun y _ => hN y) hxV (by rw [hx3]; exact one_mem _) hxc heA
    (hA3 e heA) heV hS.prop hT.prop
    hST (hsupp e heA heY)

end CFSG.RankThree.PartTwo.Sec14
