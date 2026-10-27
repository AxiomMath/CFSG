module

public import CFSG.RankThree.GF2n.Tim78S4Basic
public import CFSG.RankThree.GF2n.Tim77Prop24
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate117
public import Certificates.Certificate43
public import Certificates.Certificate82
public import Certificates.Certificate83
public import Certificates.Certificate84
public import Certificates.Certificate85
public import Certificates.Certificate86
public import Certificates.Certificate87
public import Certificates.Certificate88
public import Certificates.Certificate89
public import Certificates.Certificate90
public import Certificates.Certificate91
public import Certificates.Certificate92
public import Certificates.Certificate93
public import Certificates.Certificate94
public import Certificates.Certificate95
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99
import CFSG.RankThree.GF2n.Tim77TI
import CFSG.RankThree.GF2n.Tim78RootType
import CFSG.RankThree.GF2n.Tim78P215
import CFSG.RankThree.GF2n.Tim78Involution
public import CFSG.RankThree.GF2n.Statements

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

namespace Hyp4

variable [Finite G] {M B Q P T : Subgroup G} (H : Hyp4 M B Q P T)
include H

section Root


theorem commute_of_root_aux (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {k : G} (hA : conjSubgroup k B ≤ M) {E : Subgroup G}
    (hEA : E ≤ conjSubgroup k B) (hEQ : E ≤ Q) (hE : E ≠ ⊥)
    (hN : ∀ c ∈ Q, (∀ e ∈ E, c * e * c⁻¹ ∈ E) → ∀ a ∈ conjSubgroup k B, c * a = a * c)
    {x : G} (hx : x ∈ M)
    (hL : conjSubgroup k B ⊓ Subgroup.normalizer (conjSubgroup x (conjSubgroup k B) : Set G) ≠ ⊥) :
    ∀ a ∈ conjSubgroup k B, ∀ b ∈ conjSubgroup x (conjSubgroup k B), a * b = b * a := by
  classical
  set A := conjSubgroup k B with hAdef
  set Ab := conjSubgroup x A with hAbdef
  have hAel : Assembly.IsElemAbelian 2 A := Tim77.isElemAbelian_map' H.elemAb _
  have hAbel : Assembly.IsElemAbelian 2 Ab := Tim77.isElemAbelian_map' hAel _
  have hAti : IsTI A := isTI_conjSubgroup H.ti k
  have hAbti : IsTI Ab := isTI_conjSubgroup hAti x
  have hAbM : Ab ≤ M := by
    intro z hz
    rw [hAbdef, mem_conjSubgroup] at hz
    have := M.mul_mem (M.mul_mem hx (hA hz)) (M.inv_mem hx)
    rwa [show x * (x⁻¹ * z * x) * x⁻¹ = z by group] at this
  by_cases hLA : A ⊓ Subgroup.normalizer (Ab : Set G) = A
  ·
    have hAN : A ≤ Subgroup.normalizer (Ab : Set G) := hLA ▸ inf_le_right
    have hconj : conjSubgroup x⁻¹ Ab = A := by
      rw [hAbdef, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]
    have h23 := Tim77.tim77_2_3 hAbel hAbti (g := x⁻¹) (by rw [hconj]; exact hAN)
    rw [hconj] at h23
    intro a ha b hb
    exact comm_of_isElemAbelian h23 (Subgroup.mem_sup_right ha) (Subgroup.mem_sup_left hb)
  · exfalso
    set L := A ⊓ Subgroup.normalizer (Ab : Set G) with hLdef
    set Lb := Ab ⊓ Subgroup.normalizer (A : Set G) with hLbdef
    have S : Tim77.Prop24Setup A Ab L Lb (L ⊔ Lb) := ⟨hAel, hAti, ⟨x, rfl⟩, rfl, rfl, rfl, hL, hLA⟩
    obtain ⟨hNorm, hO2, -⟩ := S.exists_models hCen hU
    have hYM : A ⊔ Ab ≤ M := sup_le hA hAbM
    have hYQle : (A ⊔ Ab) ⊓ Q ≤ L ⊔ Lb := by
      set Y := A ⊔ Ab with hY
      haveI : (Subgroup.subgroupOf (L ⊔ Lb) Y).Normal := hNorm
      let N : Subgroup ↥Y := (Y ⊓ Q).subgroupOf Y
      haveI hNn : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr
        fun y hy => mem_normalizer_inf (Subgroup.le_normalizer hy)
          (H.M_le_normalizer_Q (hYM hy))
      have hN2 : IsPGroup 2 N :=
        (H.isPGroup_Q.to_le (inf_le_right : Y ⊓ Q ≤ Q)).comap_of_injective Y.subtype
          Subtype.val_injective
      have hK : N.map (QuotientGroup.mk' ((L ⊔ Lb).subgroupOf Y)) = ⊥ :=
        hO2 _ (hNn.map _ (QuotientGroup.mk'_surjective _)) (hN2.map _)
      intro z hz
      have hzY : z ∈ Y := hz.1
      have hz' : (QuotientGroup.mk' ((L ⊔ Lb).subgroupOf Y)) ⟨z, hzY⟩ ∈
          N.map (QuotientGroup.mk' ((L ⊔ Lb).subgroupOf Y)) :=
        ⟨⟨z, hzY⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
      rw [hK, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hz'
      exact Subgroup.mem_subgroupOf.mp hz'
    have hEL : E ≤ L := by
      intro e he
      have h1 : e ∈ (A ⊔ Ab) ⊓ Q := ⟨Subgroup.mem_sup_left (hEA he), hEQ he⟩
      have h3 : e ∈ A ⊓ (L ⊔ Lb) := ⟨hEA he, hYQle h1⟩
      rwa [S.inf_M] at h3
    obtain ⟨⟨e, heE⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE
    set e' := x * e * x⁻¹ with he'
    have he'Ab : e' ∈ Ab := by
      rw [hAbdef, mem_conjSubgroup, he', show x⁻¹ * (x * e * x⁻¹) * x = e by group]
      exact hEA heE
    have he'Q : e' ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_Q hx) e).mp (hEQ heE)
    have he'Lb : e' ∈ Lb := by
      have h1 : e' ∈ (A ⊔ Ab) ⊓ Q := ⟨Subgroup.mem_sup_right he'Ab, he'Q⟩
      have h3 : e' ∈ Ab ⊓ (L ⊔ Lb) := ⟨he'Ab, hYQle h1⟩
      rwa [S.symm.inf_M] at h3
    have hnorm : ∀ e₂ ∈ E, e' * e₂ * e'⁻¹ ∈ E := fun e₂ he₂ => by
      have hc : e₂ * e' = e' * e₂ := S.comm_L_Lb (hEL he₂) he'Lb
      rw [show e' * e₂ * e'⁻¹ = e₂ by rw [← hc]; group]
      exact he₂
    have hca := hN e' he'Q hnorm
    obtain ⟨t, htA, htL⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
    have he'L : e' ∈ L :=
      S.mem_L_of_commute_M htA htL (Subgroup.mem_sup_right he'Lb) (hca t htA).symm
    have h1 : e' ∈ A ⊓ Ab := ⟨S.L_le he'L, he'Ab⟩
    rw [S.inf_eq_bot, Subgroup.mem_bot] at h1
    apply he1
    refine Subtype.ext ?_
    show e = 1
    calc e = x⁻¹ * e' * x := by rw [he']; group
      _ = 1 := by rw [h1]; group

theorem le_Q_of_root (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {k : G} (hA : conjSubgroup k B ≤ M) {E : Subgroup G}
    (hEA : E ≤ conjSubgroup k B) (hEQ : E ≤ Q) (hE : E ≠ ⊥)
    (hN : ∀ c ∈ Q, (∀ e ∈ E, c * e * c⁻¹ ∈ E) → ∀ a ∈ conjSubgroup k B, c * a = a * c) :
    conjSubgroup k B ≤ Q := by
  classical
  set A := conjSubgroup k B with hAdef
  have hAel : Assembly.IsElemAbelian 2 A := Tim77.isElemAbelian_map' H.elemAb _
  have hAti : IsTI A := isTI_conjSubgroup H.ti k
  set V : Subgroup ↥M := A.subgroupOf M with hV
  have hVel : Assembly.IsElemAbelian 2 V := Tim77.isElemAbelian_subgroupOf hAel M
  have hAconjM : ∀ x ∈ M, conjSubgroup x A ≤ M := by
    intro x hx z hz
    rw [mem_conjSubgroup] at hz
    have := M.mul_mem (M.mul_mem hx (hA hz)) (M.inv_mem hx)
    rwa [show x * (x⁻¹ * z * x) * x⁻¹ = z by group] at this
  have hVroot : IsRootTypeTI V := by
    refine ⟨isTI_subgroupOf (fun g _ => hAti g), fun g hg a ha b hb => ?_⟩
    obtain ⟨⟨u, hu⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hg
    have huV : u ∈ V := (Subgroup.mem_inf.mp hu).1
    have huN : u ∈ Subgroup.normalizer (conjSubgroup g V : Set ↥M) := (Subgroup.mem_inf.mp hu).2
    have huA : (u : G) ∈ A := huV
    have huN' : (u : G) ∈ Subgroup.normalizer (conjSubgroup (g : G) A : Set G) := by
      refine Subgroup.mem_normalizer_fintype fun z hz => ?_
      have hzM : z ∈ M := hAconjM g g.2 hz
      have hz' : (⟨z, hzM⟩ : ↥M) ∈ conjSubgroup g V := mem_conjSubgroup_subgroupOf.mpr hz
      exact mem_conjSubgroup_subgroupOf.mp ((Subgroup.mem_normalizer_iff.mp huN _).mp hz')
    have hL : A ⊓ Subgroup.normalizer (conjSubgroup (g : G) A : Set G) ≠ ⊥ := by
      intro hbot
      have : (u : G) ∈ A ⊓ Subgroup.normalizer (conjSubgroup (g : G) A : Set G) :=
        ⟨huA, huN'⟩
      rw [hbot, Subgroup.mem_bot] at this
      exact hu1 (Subtype.ext (Subtype.ext this))
    have := H.commute_of_root_aux hCen hU hA hEA hEQ hE hN g.2 hL a ha b
      (mem_conjSubgroup_subgroupOf.mp hb)
    exact Subtype.ext this
  have hQ' : ∀ z : ↥M, z ∈ pCore 2 ↥M ↔ (z : G) ∈ Q := fun z => by
    rw [H.hQ, inSubgroup]
    exact ⟨fun h => ⟨z, h, rfl⟩, fun ⟨w, hw, hwz⟩ => (Subtype.ext hwz : w = z) ▸ hw⟩
  rcases tim78_2_13 hVel hVroot with h | h
  · exfalso
    obtain ⟨⟨e, heE⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE
    have heM : e ∈ M := hA (hEA heE) |> fun h => by exact h
    have hmem : (⟨e, heM⟩ : ↥M) ∈ V ⊓ pCore 2 ↥M :=
      Subgroup.mem_inf.mpr ⟨hEA heE, (hQ' _).mpr (hEQ heE)⟩
    rw [h, Subgroup.mem_bot] at hmem
    have he : e = 1 := congrArg Subtype.val hmem
    exact he1 (Subtype.ext he)
  · intro z hz
    have hzM : z ∈ M := hA hz
    have hz' : (⟨z, hzM⟩ : ↥M) ∈ V := hz
    exact (hQ' _).mp (h hz')

theorem le_conj_Q_of_normalizer_eq (hCen : BenderCenterInput) (hU : UnitaryTwoGenerationInput)
    {g : G} (hBM : B ≤ conjSubgroup g M) {E : Subgroup G} (hEB : E ≤ B)
    (hEQ : E ≤ conjSubgroup g Q) (hE : E ≠ ⊥)
    (hN : ∀ c ∈ conjSubgroup g Q, (∀ e ∈ E, c * e * c⁻¹ ∈ E) → ∀ b ∈ B, c * b = b * c) :
    B ≤ conjSubgroup g Q := by
  have hA : conjSubgroup g⁻¹ B ≤ M := by
    intro z hz
    rw [mem_conjSubgroup, inv_inv] at hz
    have := hBM hz
    rwa [mem_conjSubgroup, show g⁻¹ * (g * z * g⁻¹) * g = z by group] at this
  have hEA : conjSubgroup g⁻¹ E ≤ conjSubgroup g⁻¹ B := Subgroup.map_mono hEB
  have hEQ' : conjSubgroup g⁻¹ E ≤ Q := by
    intro z hz
    rw [mem_conjSubgroup, inv_inv] at hz
    have := hEQ hz
    rwa [mem_conjSubgroup, show g⁻¹ * (g * z * g⁻¹) * g = z by group] at this
  have hE' : conjSubgroup g⁻¹ E ≠ ⊥ := by
    obtain ⟨⟨e, heE⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE
    intro hbot
    have hmem : g⁻¹ * e * g ∈ conjSubgroup g⁻¹ E := by
      rw [mem_conjSubgroup, inv_inv, show g * (g⁻¹ * e * g) * g⁻¹ = e by group]
      exact heE
    rw [hbot, Subgroup.mem_bot] at hmem
    refine he1 (Subtype.ext ?_)
    show e = 1
    calc e = g * (g⁻¹ * e * g) * g⁻¹ := by group
      _ = 1 := by rw [hmem]; group
  have hroot := H.le_Q_of_root hCen hU hA hEA hEQ' hE' (fun c hcQ hcN a ha => by
    have hc0 : g * c * g⁻¹ ∈ conjSubgroup g Q := by
      rw [mem_conjSubgroup, show g⁻¹ * (g * c * g⁻¹) * g = c by group]
      exact hcQ
    have hnorm : ∀ e ∈ E, g * c * g⁻¹ * e * (g * c * g⁻¹)⁻¹ ∈ E := by
      intro e he
      have hmem : g⁻¹ * e * g ∈ conjSubgroup g⁻¹ E := by
        rw [mem_conjSubgroup, inv_inv, show g * (g⁻¹ * e * g) * g⁻¹ = e by group]
        exact he
      have := hcN _ hmem
      rw [mem_conjSubgroup, inv_inv] at this
      rwa [show g * (c * (g⁻¹ * e * g) * c⁻¹) * g⁻¹ = g * c * g⁻¹ * e * (g * c * g⁻¹)⁻¹ by group]
        at this
    have haB : g * a * g⁻¹ ∈ B := by
      have := ha
      rwa [mem_conjSubgroup, inv_inv] at this
    have := hN _ hc0 hnorm _ haB
    calc c * a = g⁻¹ * ((g * c * g⁻¹) * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * a * g⁻¹) * (g * c * g⁻¹)) * g := by rw [this]
      _ = a * c := by group)
  intro b hb
  have hb' : g⁻¹ * b * g ∈ conjSubgroup g⁻¹ B := by
    rw [mem_conjSubgroup, inv_inv, show g * (g⁻¹ * b * g) * g⁻¹ = b by group]
    exact hb
  rw [mem_conjSubgroup]
  exact hroot hb'

end Root

end Hyp4

end CFSG.RankThree.GF2n.Tim78
