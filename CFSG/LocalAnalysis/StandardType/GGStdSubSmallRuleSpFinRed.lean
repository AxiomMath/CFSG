module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleSpFinAbs
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameCenter
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.StandardType.SpFin

open CFSG.Assembly TableB CFSG.LieType.Steinberg.CentralExt
open CFSG.Open (StatedSp)

@[expose] def SpFinCore : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 → ∀ m : ℕ, 5 ≤ m →
    ∀ Ã : Subgroup (StatedSp m K), IsElemAbelian 3 Ã → 3 ^ (m - 1) ≤ Nat.card Ã →
      (∃ U : Subgroup (StatedSp m K), U ≠ ⊥ ∧ IsPGroup 2 U ∧
        ∀ y ∈ Ã, ∀ u ∈ U, y * u * y⁻¹ ∈ U) →
      ∀ x ∈ Ã, x ≠ 1 →
        ∃ Q : Subgroup (StatedSp m K), CFSG.IsQuasisimple Q ∧
          Q ≤ Subgroup.centralizer ({x} : Set (StatedSp m K)) ∧
          (∀ c ∈ Subgroup.centralizer ({x} : Set (StatedSp m K)), ∀ q ∈ Q, c * q * c⁻¹ ∈ Q) ∧
          ((∃ b ∈ Ã, b ∉ Subgroup.zpowers x ∧ ∀ q ∈ Q, b * q = q * b) ∨
            3 ^ 3 ≤ Nat.card (Ã ⊓ Q : Subgroup (StatedSp m K)))

section Closed

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem ker_eq_bot
    (hK : Nat.card K = 2) {m : ℕ} (hm : 4 ≤ m) {L' : Type}
    [Group L'] [Finite L'] (ψ : L' →* LargeEvenProj (LargeEvenSpGroup K m))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) :
    ψ.ker = ⊥ := by
  have : NeZero m := ⟨by omega⟩
  have hcard : ∃ k, Nat.card ψ.ker = 2 ^ k := by
    refine ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' fun {d} hd hdd => ?_⟩
    by_contra hd2
    have h1 : d ∣ Nat.card (Subgroup.center L') := hdd.trans (Subgroup.card_dvd_of_le hker)
    exact ggCenterPrime_sp (K := K) (m := m) hd hd2 L' ψ hψ hker hperf h1
  obtain ⟨k, hk⟩ := hcard
  haveI : Group.IsPerfect L' := ⟨hperf⟩
  exact SpClosed.psp_two_cover_trivial (K := K) (n := m) (f := 1) (by rw [hK, pow_one]) le_rfl
    (by omega) (fun h => absurd h (by omega)) L' ψ hψ hker (IsPGroup.of_card hk)

end Closed

section Main

theorem ggSpTwoNormSmallRHigh_of_core
    (hcore : SpFinCore) : GGSpTwoNormSmallRHigh := by
  intro K _ _ hK m hm L' _ _ ψ hψ hker hperf A hA hAI hr h3 hα a ha ha1 hcomp hcent hsm hrule
  exfalso
  have hKc : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (le_refl 1) (by rw [hK, pow_one])
  have : NeZero m := ⟨by omega⟩
  have hker1 := ker_eq_bot hK (by omega) ψ hψ hker hperf
  have hψinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hker1
  let e : L' ≃* StatedSp m K := (MulEquiv.ofBijective ψ ⟨hψinj, hψ⟩).trans
    (TableBSymp.spProjEquivSp (K := K) (m := m))
  have he : ∀ l, e l = TableBSymp.spProjEquivSp (K := K) (m := m) (ψ l) := fun l => rfl
  have hZ : ∀ l : L', MulAut.conj l = 1 → l = 1 := by
    intro l hl
    apply hψinj
    rw [map_one]
    have hc : ψ l ∈ Subgroup.center (LargeEvenProj (LargeEvenSpGroup K m)) := by
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
  let cj : StatedSp m K →* MulAut L' := (MulAut.conj : L' →* MulAut L').comp e.symm.toMonoidHom
  have hcj : ∀ y, cj y = MulAut.conj (e.symm y) := fun y => rfl
  have hcjinj : Function.Injective cj := hconjinj.comp e.symm.injective
  set Ã : Subgroup (StatedSp m K) := A.comap cj with hÃdef
  have hmemÃ : ∀ y, y ∈ Ã ↔ MulAut.conj (e.symm y) ∈ A := fun y => Iff.rfl
  have hÃe : IsElemAbelian 3 Ã := by
    refine ⟨⟨⟨fun y z => Subtype.ext (hcjinj ?_)⟩⟩, fun y hy => hcjinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA y.2 z.2
    · rw [map_pow, map_one]
      exact hA.2 _ hy
  have hAcjmem : ∀ b ∈ A, ∃ y ∈ Ã, cj y = b := by
    intro b hb
    obtain ⟨l, rfl⟩ := hinner b hb
    refine ⟨e l, ?_, ?_⟩
    · rw [hmemÃ, e.symm_apply_apply]
      exact hb
    · rw [hcj, e.symm_apply_apply]
  have hcardÃ : Nat.card Ã = Nat.card A := by
    refine Nat.card_congr (Equiv.ofBijective (fun y : Ã => (⟨cj y, y.2⟩ : A)) ⟨?_, ?_⟩)
    · intro y z h
      exact Subtype.ext (hcjinj (congrArg Subtype.val h))
    · rintro ⟨b, hb⟩
      obtain ⟨y, hy, rfl⟩ := hAcjmem b hb
      exact ⟨⟨y, hy⟩, rfl⟩
  obtain ⟨U₀, hU₀1, hU₀2, hU₀A⟩ := hα
  set U : Subgroup (StatedSp m K) :=
    U₀.map (TableBSymp.spProjEquivSp (K := K) (m := m)).toMonoidHom with hUdef
  have hU1 : U ≠ ⊥ := by
    rw [Ne, hUdef, Subgroup.map_eq_bot_iff_of_injective _
      (TableBSymp.spProjEquivSp (K := K) (m := m)).injective]
    exact hU₀1
  have hU2 : IsPGroup 2 U := hU₀2.map _
  have hUn : ∀ y ∈ Ã, ∀ u ∈ U, y * u * y⁻¹ ∈ U := by
    intro y hy u hu
    obtain ⟨r, hr0, rfl⟩ := hu
    obtain ⟨l', rfl⟩ := hψ r
    have h1 := hU₀A (MulAut.conj (e.symm y)) hy l' hr0
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv] at h1
    refine ⟨ψ (e.symm y) * ψ l' * (ψ (e.symm y))⁻¹, h1, ?_⟩
    have hy' : TableBSymp.spProjEquivSp (K := K) (m := m) (ψ (e.symm y)) = y := by
      rw [← he, e.apply_symm_apply]
    change TableBSymp.spProjEquivSp (K := K) (m := m) (ψ (e.symm y) * ψ l' * (ψ (e.symm y))⁻¹) =
      y * TableBSymp.spProjEquivSp (K := K) (m := m) (ψ l') * y⁻¹
    rw [map_mul, map_mul, map_inv, hy']
  obtain ⟨t, rfl⟩ := hinner a ha
  have hxÃ : e t ∈ Ã := by
    rw [hmemÃ, e.symm_apply_apply]
    exact ha
  have hx1 : e t ≠ 1 := by
    intro h
    apply ha1
    have : t = 1 := e.injective (by rw [h, map_one])
    rw [this, map_one]
  obtain ⟨Q, hQq, hQC, hQn, hdis⟩ := hcore K hK m hm Ã hÃe (hcardÃ ▸ hr) ⟨U, hU1, hU2, hUn⟩
    (e t) hxÃ hx1
  set QL : Subgroup L' := Q.map e.symm.toMonoidHom with hQLdef
  have hmemfix : ∀ l, l ∈ ggFix (MulAut.conj t) ↔ e t * e l = e l * e t := by
    intro l
    rw [mem_ggFix, MulAut.conj_apply, ← map_mul, ← map_mul, e.injective.eq_iff]
    constructor
    · intro h
      calc t * l = (t * l * t⁻¹) * t := by group
        _ = l * t := by rw [h]
    · intro h
      calc t * l * t⁻¹ = (l * t) * t⁻¹ := by rw [h]
        _ = l := by group
  have hQLC : QL ≤ ggFix (MulAut.conj t) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [hmemfix]
    change e t * e (e.symm q) = e (e.symm q) * e t
    rw [e.apply_symm_apply]
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hQC hq)).symm
  have hQLn : ∀ c ∈ ggFix (MulAut.conj t), ∀ q ∈ QL, c * q * c⁻¹ ∈ QL := by
    intro c hc q hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    have hec : e c ∈ Subgroup.centralizer ({e t} : Set (StatedSp m K)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr ((hmemfix c).mp hc).symm
    refine ⟨e c * q0 * (e c)⁻¹, hQn (e c) hec q0 hq0, ?_⟩
    simp [map_mul, map_inv]
  have hQLq : CFSG.IsQuasisimple QL :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (Q.equivMapOfInjective e.symm.toMonoidHom e.symm.injective) hQq
  refine false_of_normal_quasisimple hcomp hcent hsm hQLC hQLn hQLq ?_
  rcases hdis with ⟨b, hb, hbx, hbQ⟩ | h27
  · left
    refine ⟨cj b, hb, ?_, ?_⟩
    · intro hmem
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      apply hbx
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have h1 : MulAut.conj (t ^ k) = MulAut.conj (e.symm b) := by rw [map_zpow, hk, hcj]
      have h2 := hconjinj h1
      calc (e t) ^ k = e (t ^ k) := (map_zpow e t k).symm
        _ = e (e.symm b) := by rw [h2]
        _ = b := e.apply_symm_apply b
    · rintro _ ⟨q, hq, rfl⟩
      rw [hcj, MulAut.conj_apply]
      have h1 : e.symm (b * q * b⁻¹) = e.symm b * e.symm q * (e.symm b)⁻¹ := by
        simp [map_mul, map_inv]
      have h2 : b * q * b⁻¹ = q := by
        calc b * q * b⁻¹ = q * b * b⁻¹ := by rw [hbQ q hq]
          _ = q := by group
      change e.symm b * e.symm q * (e.symm b)⁻¹ = e.symm q
      rw [← h1, h2]
  · right
    have hEa : IsElemAbelian 3 (Ã ⊓ Q : Subgroup (StatedSp m K)) :=
      ⟨⟨⟨fun y z => Subtype.ext (TableB.IsElemAbelian.comm hÃe y.2.1 z.2.1)⟩⟩,
        fun y hy => hÃe.2 y hy.1⟩
    refine ⟨(Ã ⊓ Q : Subgroup (StatedSp m K)).map e.symm.toMonoidHom,
      Subgroup.map_mono inf_le_right, TableB.isElemAbelian_map hEa _, ?_, ?_, ?_⟩
    · intro a' ha' e0 he0
      obtain ⟨b, hb, rfl⟩ := hAcjmem a' ha'
      obtain ⟨y, hy, rfl⟩ := he0
      have hcomm : b * y = y * b := TableB.IsElemAbelian.comm hÃe hb hy.1
      rw [hcj, MulAut.conj_apply]
      have h1 : e.symm (b * y * b⁻¹) = e.symm b * e.symm y * (e.symm b)⁻¹ := by
        simp [map_mul, map_inv]
      have h2 : b * y * b⁻¹ = y := by
        calc b * y * b⁻¹ = y * b * b⁻¹ := by rw [hcomm]
          _ = y := by group
      change e.symm b * e.symm y * (e.symm b)⁻¹ = e.symm y
      rw [← h1, h2]
    · rintro e0 ⟨y, hy, rfl⟩
      exact hy.1
    · calc 3 ^ 3 ≤ Nat.card (Ã ⊓ Q : Subgroup (StatedSp m K)) := h27
        _ = Nat.card ((Ã ⊓ Q : Subgroup (StatedSp m K)).map e.symm.toMonoidHom) :=
          Nat.card_congr ((Ã ⊓ Q : Subgroup (StatedSp m K)).equivMapOfInjective
            e.symm.toMonoidHom e.symm.injective).toEquiv

end Main

end CFSG.StandardType.SpFin
