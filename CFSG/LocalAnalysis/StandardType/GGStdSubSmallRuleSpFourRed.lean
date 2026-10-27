module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFourTrans
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.StandardType.SpFour

open CFSG.Assembly TableB CFSG.LieType.Steinberg.CentralExt
open CFSG.Open (StatedSp)

@[expose] def SpFourCore : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ Ã : Subgroup (StatedSp 4 K), IsElemAbelian 3 Ã → 3 ^ 3 ≤ Nat.card Ã →
      (∃ U : Subgroup (StatedSp 4 K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
        ∀ s ∈ Ã, ∀ u ∈ U, s * u * s⁻¹ ∈ U) →
      ∀ x ∈ Ã, x ≠ 1 → EndNodeAt Ã x → RuleAt Ã x → ConclAt Ã x

theorem ggSpTwoNormSmallRFour_of_core
    (hcore : SpFourCore) : GGSpTwoNormSmallRFour := by
  intro K _ _ hK L' _ _ ψ hψ hker hperf A hA hAI hr h3 hα a ha ha1 hcomp hcent hsm hrule
  have hKc : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (le_refl 1) (by rw [hK, pow_one])
  have : NeZero (4 : ℕ) := ⟨by norm_num⟩
  have hker1 := SpFin.ker_eq_bot (m := 4) hK (le_refl 4) ψ hψ hker hperf
  have hψinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hker1
  let e : L' ≃* StatedSp 4 K := (MulEquiv.ofBijective ψ ⟨hψinj, hψ⟩).trans
    (TableBSymp.spProjEquivSp (K := K) (m := 4))
  have he : ∀ l, e l = TableBSymp.spProjEquivSp (K := K) (m := 4) (ψ l) := fun l => rfl
  have hZ : ∀ l : L', MulAut.conj l = 1 → l = 1 := by
    intro l hl
    apply hψinj
    rw [map_one]
    have hc : ψ l ∈ Subgroup.center (LargeEvenProj (LargeEvenSpGroup K 4)) := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨x, rfl⟩ := hψ r
      have h1 := DFunLike.congr_fun hl x
      rw [MulAut.conj_apply, MulAut.one_apply] at h1
      rw [← map_mul, ← map_mul]
      congr 1
      calc x * l = (l * x * l⁻¹) * l := by rw [h1]
        _ = l * x := by group
    rw [TableBSymp.center_spProj_eq_bot, Subgroup.mem_bot] at hc
    exact hc
  have hconjinj : Function.Injective (MulAut.conj : L' →* MulAut L') :=
    (injective_iff_map_eq_one _).mpr hZ
  have hinner : ∀ b ∈ A, ∃ l : L', b = MulAut.conj l := by
    intro b hb
    obtain ⟨φ, hφI, hφ⟩ := hAI b hb
    obtain ⟨r, rfl⟩ := TableBSymp.sp_I_subset_inn hφI
    obtain ⟨l, rfl⟩ := hψ r
    refine ⟨l, ?_⟩
    ext x
    apply hψinj
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv, ← hφ x, MulAut.conj_apply]
  set ÃL : Subgroup L' := A.comap (MulAut.conj : L' →* MulAut L') with hÃLdef
  set Ã : Subgroup (StatedSp 4 K) := ÃL.map e.toMonoidHom with hÃdef
  have hmemÃ : ∀ y, y ∈ Ã ↔ MulAut.conj (e.symm y) ∈ A := fun y => by
    rw [hÃdef, Subgroup.mem_map_equiv]
    rfl
  have hÃLe : IsElemAbelian 3 ÃL := by
    refine ⟨⟨⟨fun y z => Subtype.ext (hconjinj ?_)⟩⟩, fun y hy => hconjinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA y.2 z.2
    · rw [map_pow, map_one]
      exact hA.2 _ hy
  have hÃe : IsElemAbelian 3 Ã := TableB.isElemAbelian_map hÃLe _
  have hcardÃL : Nat.card ÃL = Nat.card A := by
    refine Nat.card_congr (Equiv.ofBijective (fun y : ÃL => (⟨MulAut.conj (y : L'), y.2⟩ : A))
      ⟨?_, ?_⟩)
    · intro y z h
      exact Subtype.ext (hconjinj (congrArg Subtype.val h))
    · rintro ⟨b, hb⟩
      obtain ⟨l, rfl⟩ := hinner b hb
      exact ⟨⟨l, hb⟩, rfl⟩
  have hcardÃ : Nat.card Ã = Nat.card A := by
    rw [hÃdef, ← hcardÃL]
    exact (Nat.card_congr (ÃL.equivMapOfInjective e.toMonoidHom e.injective).toEquiv).symm
  obtain ⟨U₀, hU₀1, hU₀2, hU₀A⟩ := hα
  set U : Subgroup (StatedSp 4 K) :=
    U₀.map (TableBSymp.spProjEquivSp (K := K) (m := 4)).toMonoidHom with hUdef
  have hU1 : U ≠ ⊥ := by
    rw [Ne, hUdef, Subgroup.map_eq_bot_iff_of_injective _
      (TableBSymp.spProjEquivSp (K := K) (m := 4)).injective]
    exact hU₀1
  have hU2 : IsPGroup 2 U := hU₀2.map _
  have hUn : ∀ y ∈ Ã, ∀ u ∈ U, y * u * y⁻¹ ∈ U := by
    intro y hy u hu
    obtain ⟨r, hr0, rfl⟩ := hu
    obtain ⟨l', rfl⟩ := hψ r
    have h1 := hU₀A (MulAut.conj (e.symm y)) ((hmemÃ y).mp hy) l' hr0
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv] at h1
    refine ⟨ψ (e.symm y) * ψ l' * (ψ (e.symm y))⁻¹, h1, ?_⟩
    have hy' : TableBSymp.spProjEquivSp (K := K) (m := 4) (ψ (e.symm y)) = y := by
      rw [← he, e.apply_symm_apply]
    change TableBSymp.spProjEquivSp (K := K) (m := 4) (ψ (e.symm y) * ψ l' * (ψ (e.symm y))⁻¹) =
      y * TableBSymp.spProjEquivSp (K := K) (m := 4) (ψ l') * y⁻¹
    rw [map_mul, map_mul, map_inv, hy']
  obtain ⟨t, rfl⟩ := hinner a ha
  obtain ⟨htÃ, ht1, hENL⟩ :=
    (ggIsEndNode_conj_iff hinner hconjinj t).mp ⟨ha, ha1, hcomp, hcent⟩
  have hEN : EndNodeAt Ã (e t) := (endNodeAt_map_iff e ÃL t).mpr hENL
  have hRuleL : RuleAt ÃL t := by
    rintro ⟨z, hz, hz1, hENz, hnsz⟩
    have hlayz : LargeEvenLayer (ggFix (MulAut.conj z)) = layerC z := by
      rw [ggFix_conj]
      rfl
    have hlayt : LargeEvenLayer (ggFix (MulAut.conj t)) = layerC t := by
      rw [ggFix_conj]
      rfl
    rw [← hlayt]
    refine hrule rfl ⟨MulAut.conj z,
      (ggIsEndNode_conj_iff hinner hconjinj z).mpr ⟨hz, hz1, hENz⟩, ?_⟩
    rw [hlayz]
    exact hnsz
  have hRule : RuleAt Ã (e t) := (ruleAt_map_iff e ÃL t).mpr hRuleL
  have hxÃ : e t ∈ Ã := Subgroup.mem_map_of_mem _ htÃ
  have hx1 : e t ≠ 1 := fun h => ht1 (e.injective (by rw [h, map_one]))
  have hC := hcore K hK Ã hÃe (by rw [hcardÃ]; exact hr) ⟨U, hU1, hU2, hUn⟩ (e t) hxÃ hx1 hEN
    hRule
  exact conclAt_to_ggConcl hinner t (conclAt_of_map e ÃL t hC)

end CFSG.StandardType.SpFour
