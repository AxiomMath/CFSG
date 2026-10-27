module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.KFixData
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.Mathlib.GroupTheory.LayerFixedJ
public import CFSG.Open.StatedAPI
public import CFSG.LocalAnalysis.SignalizerFunctor

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

private def autFixedSubgroup {H : Type*} [Group H] (β : MulAut H) : Subgroup H where
  carrier := {x | β x = x}
  one_mem' := map_one β
  mul_mem' := by
    intro a b ha hb
    have ha' : β a = a := ha
    have hb' : β b = b := hb
    show β (a * b) = a * b
    rw [map_mul, ha', hb']
  inv_mem' := by
    intro a ha
    have ha' : β a = a := ha
    show β a⁻¹ = a⁻¹
    rw [map_inv, ha']

private theorem mulAut_pow_apply_val {H : Type*} [Group H] {K : Subgroup H}
    (f : MulAut H) (g : MulAut ↥K)
    (hg : ∀ x : ↥K, ((g x : ↥K) : H) = f (x : H)) (n : ℕ) (x : ↥K) :
    (((g ^ n) x : ↥K) : H) = (f ^ n) (x : H) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ', MulAut.mul_apply, hg, ih, pow_succ', MulAut.mul_apply]

theorem exists_fixed_ksec {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {J B₂ A R : Subgroup G}
    (hJ : JData n L z J) (hR : RData b z J B₂ A R) :
    ∃ β : MulAut (Ksec R), β ^ 3 = 1 ∧
      (∀ k k' : ↥(ktil R), (k' : G) = b * (k : G) * b⁻¹ → β (ktilHom R k) = ktilHom R k') ∧
      ∃ O J' : Subgroup (Ksec R), (∀ x : Ksec R, x ∈ O ⊔ J' ↔ β x = x) ∧ O ⊓ J' = ⊥ ∧
        (∀ x ∈ O, ∀ y ∈ J', x * y = y * x) ∧ Nat.Coprime (Nat.card O) 3 ∧
        (StatedClassicalModel ↥J' .PSL 4 2 1 ∨ StatedClassicalModel ↥J' .PSL 5 2 1) := by
  obtain ⟨β₀, _, O₀, J₀, hF, hFcompat, _, hFmodel⟩ :=
    exists_kfixData h hJ hR
  let K : Subgroup (Xq R) := CFSG.layer (Xq R)
  have hKchar : K.Characteristic := CFSG.LocalCores.layer_characteristic
  have hKmap : K.map (β₀ : Xq R →* Xq R) = K :=
    Subgroup.characteristic_iff_map_eq.mp hKchar β₀
  let β : MulAut (Ksec R) :=
    (β₀.subgroupMap K).trans (MulEquiv.subgroupCongr hKmap)
  have hβ_coe : ∀ x : Ksec R, ((β x : Ksec R) : Xq R) = β₀ (x : Xq R) := by
    intro x
    change ((MulEquiv.subgroupCongr hKmap) ((β₀.subgroupMap K) x) : Xq R) = β₀ (x : Xq R)
    rw [MulEquiv.subgroupCongr_apply, MulEquiv.coe_subgroupMap_apply]
  have hβ3 : β ^ 3 = 1 := by
    ext x
    rw [mulAut_pow_apply_val β₀ β hβ_coe 3 x, hF.pow]
    rfl
  have hcompat : ∀ k k' : ↥(ktil R),
      (k' : G) = b * (k : G) * b⁻¹ → β (ktilHom R k) = ktilHom R k' := by
    intro k k' hkk'
    apply Subtype.ext
    rw [hβ_coe]
    have hx := hFcompat ⟨(k : G), ktil_le_centralizer R k.2⟩
      ⟨(k' : G), ktil_le_centralizer R k'.2⟩ hkk'
    change β₀ (QuotientGroup.mk ⟨(k : G), ktil_le_centralizer R k.2⟩) =
      QuotientGroup.mk ⟨(k' : G), ktil_le_centralizer R k'.2⟩
    exact hx
  have hcore : CFSG.pPrimeCore 3 (Xq R) = ⊥ :=
    CFSG.pPrimeCore_quotient_eq_bot (G := ↥(Subgroup.centralizer (R : Set G)))
      (p := 3) Nat.prime_three
  have hle := CFSG.LayerFixed.le_layer_of_fixData hcore (abelian_sylow_xq h hR) hF
  let O : Subgroup (Ksec R) := (O₀ ⊓ K).subgroupOf K
  let J' : Subgroup (Ksec R) := J₀.subgroupOf K
  have hOfix : O ≤ autFixedSubgroup β := by
    intro o ho
    have ho' : o ∈ (O₀ ⊓ K).subgroupOf K := by simpa [O] using ho
    have hoO : (o : Xq R) ∈ O₀ := (Subgroup.mem_subgroupOf.mp ho').1
    show β o = o
    apply Subtype.ext
    rw [hβ_coe]
    exact hF.fix_O (o : Xq R) hoO
  have hJfix : J' ≤ autFixedSubgroup β := by
    intro y hy
    have hy' : y ∈ J₀.subgroupOf K := by simpa [J'] using hy
    have hyJ : (y : Xq R) ∈ J₀ := Subgroup.mem_subgroupOf.mp hy'
    show β y = y
    apply Subtype.ext
    rw [hβ_coe]
    exact hF.fix_J (y : Xq R) hyJ
  have hfix : ∀ x : Ksec R, x ∈ O ⊔ J' ↔ β x = x := by
    intro x
    constructor
    · intro hx
      exact (sup_le hOfix hJfix) hx
    · intro hx
      have hxval : β₀ (x : Xq R) = (x : Xq R) := by
        have hx' := congrArg (fun y : Ksec R => (y : Xq R)) hx
        rwa [hβ_coe] at hx'
      obtain ⟨o, ho, y, hy, hxy⟩ := (hle.2 (x : Xq R) x.2).mp hxval
      have hoK : o ∈ K := ho.2
      have hyK : y ∈ K := hle.1 hy
      have hxmem : x = (⟨o, hoK⟩ : Ksec R) * (⟨y, hyK⟩ : Ksec R) := Subtype.ext hxy
      rw [hxmem]
      refine Subgroup.mul_mem_sup ?_ ?_
      · show (⟨o, hoK⟩ : Ksec R) ∈ O
        exact Subgroup.mem_subgroupOf.mpr ho
      · show (⟨y, hyK⟩ : Ksec R) ∈ J'
        exact Subgroup.mem_subgroupOf.mpr hy
  have hcenter : Subgroup.center J₀ = ⊥ := by
    rcases hF.simple.eq_bot_or_eq_top_of_normal (Subgroup.center J₀) with hbot | htop
    · exact hbot
    · exfalso
      obtain ⟨a, ha, c, hc, hac⟩ := hF.nonab
      have hcomm : ∀ x y : J₀, x * y = y * x := by
        intro x y
        have hx : x ∈ Subgroup.center J₀ := by rw [htop]; exact Subgroup.mem_top x
        exact (Subgroup.mem_center_iff.mp hx y).symm
      exact hac (by simpa using congrArg (fun z : J₀ => (z : Xq R)) (hcomm ⟨a, ha⟩ ⟨c, hc⟩))
  have hdisj : O ⊓ J' = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxO' : x ∈ (O₀ ⊓ K).subgroupOf K := by simpa [O] using hx.1
    have hxO : (x : Xq R) ∈ O₀ := (Subgroup.mem_subgroupOf.mp hxO').1
    have hxJ' : x ∈ J₀.subgroupOf K := by simpa [J'] using hx.2
    have hxJ : (x : Xq R) ∈ J₀ := Subgroup.mem_subgroupOf.mp hxJ'
    have hxZ : (⟨(x : Xq R), hxJ⟩ : J₀) ∈ Subgroup.center J₀ :=
      Subgroup.mem_center_iff.mpr fun y => Subtype.ext (hF.comm (x : Xq R) hxO (y : Xq R) y.2).symm
    have hx1 : (⟨(x : Xq R), hxJ⟩ : J₀) = 1 :=
      Subgroup.mem_bot.mp (hcenter ▸ hxZ)
    apply Subtype.ext
    simpa using congrArg (fun y : J₀ => (y : Xq R)) hx1
  have hcomm : ∀ x ∈ O, ∀ y ∈ J', x * y = y * x := by
    intro x hx y hy
    have hxO' : x ∈ (O₀ ⊓ K).subgroupOf K := by simpa [O] using hx
    have hxO : (x : Xq R) ∈ O₀ := (Subgroup.mem_subgroupOf.mp hxO').1
    have hyJ' : y ∈ J₀.subgroupOf K := by simpa [J'] using hy
    have hyJ : (y : Xq R) ∈ J₀ := Subgroup.mem_subgroupOf.mp hyJ'
    apply Subtype.ext
    exact hF.comm (x : Xq R) hxO (y : Xq R) hyJ
  have hcop : Nat.Coprime (Nat.card O) 3 := by
    have hcard : Nat.card O = Nat.card ↥(O₀ ⊓ K) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (H := O₀ ⊓ K) (K := K) inf_le_right).toEquiv
    have hdvd : Nat.card O ∣ Nat.card ↥O₀ := by
      rw [hcard]
      exact Subgroup.card_dvd_of_le (H := O₀ ⊓ K) (K := O₀) inf_le_left
    exact Nat.Coprime.symm
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => hF.coprime (h3.trans hdvd))
  have hmodel : StatedClassicalModel ↥J' .PSL 4 2 1 ∨
      StatedClassicalModel ↥J' .PSL 5 2 1 := by
    have e : J₀ ≃* ↥(J₀.subgroupOf K) := (Subgroup.subgroupOfEquivOfLe hle.1).symm
    rcases hFmodel with h4 | h5
    · exact Or.inl (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h4)
    · exact Or.inr (CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e h5)
  refine ⟨β, hβ3, hcompat, ?_⟩
  exact ⟨O, J', hfix, hdisj, hcomm, hcop, hmodel⟩

end CFSG.StandardType.FF81.PropOne

end
