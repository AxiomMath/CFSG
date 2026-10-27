module

public import CFSG.RankThree.S4Free.Stellmacher34Mod
public import CFSG.RankThree.S4Free.Stellmacher33
public import CFSG.RankThree.S4Free.Stellmacher32
public import CFSG.RankThree.S4Free.StellmacherSzAll
public import CFSG.RankThree.S4Free.Stellmacher34Perf

public section

namespace CFSG.RankThree.S4Free.Stell34

open Subgroup CFSG.Blueprint CFSG.Quasithin
open CFSG.RankThree.S4Free.Stell33 (LCfgCore)
open scoped commutatorElement Pointwise IsMulCommutative

universe u v


theorem false_of_isL24Sz (h29 : Stell.Hyp29.{u} .sz) (h25 : Hyp25dSz.{u}) {S : Type u}
    [Group S] [Finite S] {G : Type u} [Group G] {κ : S →* G} (hκ : F2Host .sz κ)
    {L : Subgroup G}
    (hL : Stell.IsL24Sz κ.range (normalizer (((stellW .sz S).map κ : Subgroup G) : Set G))
      ((stellW .sz S).map κ) L) : False := by
  haveI := hκ.admissible.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinj := hκ.admissible.injective
  obtain ⟨Tsyl, hTsyl⟩ := hκ.admissible.sylow
  have hT : IsPGroup 2 κ.range := hTsyl ▸ Tsyl.isPGroup'
  have hTi : ¬ 2 ∣ κ.range.index := hTsyl ▸ Tsyl.not_dvd_index
  haveI : (stellW .sz S).Characteristic := stellW_characteristic
  set W := (stellW .sz S).map κ with hWdef
  have hW : CFSG.Open.IsElemAbelian 2 W := isElemAbelian_map isElemAbelian_stellW κ
  have hWT : W ≤ κ.range := map_le_range κ _
  have hTW : κ.range ≤ normalizer (W : Set G) :=
    range_le_normalizer_map κ (inferInstance : (stellW .sz S).Normal)
  obtain ⟨R, a, K, _, _, φ, hcfg⟩ := szCfg_of_isL24Sz hT hW hWT hTW hL
  obtain ⟨u, -, -, hc⟩ := hcfg.exists_lcfgCore
  obtain ⟨hR, hX⟩ := hcfg.eq_oTwo_and_eq_X hc
  have hC := centralizer_oTwo_le_of_isL24Sz hT hTi hTW hL hκ.admissible.centralizer_le hcfg hR
  obtain ⟨n, hn, hnat⟩ := hcfg.isNatSzExt hc hR hX hC h25
  haveI : IsMulCommutative (W.subgroupOf L) := hcfg.elemAb.1
  have hale := Stell.ale_one_autOn_of_isNatSzExt_of_isPGroup hcfg.isPGroup_T hcfg.not_dvd_index
    hcfg.elemAb hcfg.W_le_T hcfg.normalizer_le hC hcfg.not_le_oTwo hn hnat
  haveI : IsMulCommutative W := hW.1
  have hale' : Stell.ALe (autOn (κ.range ⊓ L) W) ⊤ 1 :=
    Stell.ALe.autOn_map L.subtype_injective hcfg.T_le_normalizer (subgroupOf_map_subtype _ _)
      (by rw [subgroupOf_map_subtype, inf_of_le_left hL.le]) hale
  have hale'' : Stell.ALe (autOn κ.range W) ⊤ 1 := hale'.mono (AutOn.autOn_mono inf_le_left)
  haveI : IsMulCommutative (stellW .sz S) := isElemAbelian_stellW.1
  have hgt := (Stell.agtOne_stellW (𝒦 := .sz) (S := S) h29).2
  have hiff := Stell.agt_autOn_map_iff (f := κ) hinj (P := ⊤) (U := stellW .sz S) (Y := W)
    (fun x _ => by rw [normalizer_eq_top_iff.mpr inferInstance]; exact mem_top x) le_rfl
    (by rw [← MonoidHom.range_eq_map]; exact hTW) (e := 1)
  rw [subgroupOf_self, ← MonoidHom.range_eq_map] at hiff
  exact Stell.not_ale_iff.mpr (hiff.mpr hgt) hale''

theorem stellW_normal_of_three_four (hThmA : Stell33.ThmA.{u} .sz) (h29 : Stell.Hyp29.{u} .sz)
    (h24 : Hyp24Sz.{u}) (h25 : Hyp25dSz.{u}) {S : Type u} [Group S] [Finite S]
    (Y : Type u) [Group Y] (κ : S →* Y) (hκ : F2Host .sz κ) :
    ((stellW .sz S).map κ).Normal := by
  suffices key : ∀ n : ℕ, ∀ (Y : Type u) [Group Y] (κ : S →* Y), F2Host .sz κ →
      Nat.card Y = n → ((stellW .sz S).map κ).Normal from key _ Y κ hκ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro Y _ κ hκ hn
  by_contra hnot
  haveI := hκ.admissible.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hmin, -, h32⟩ := hκ.minimal_counterexample h29
    (fun Y' _ κ' hκ' hcard => ih _ (hn ▸ hcard) Y' κ' hκ' rfl) hnot
  obtain ⟨hco, hcore⟩ := Stell33.isCoatom_normalizer_of_minimal hκ hnot hmin h32
  obtain ⟨Tsyl, hTsyl⟩ := hκ.admissible.sylow
  haveI : (stellW .sz S).Characteristic := stellW_characteristic
  have hhyp : Stell.Hyp24 κ.range (normalizer (((stellW .sz S).map κ : Subgroup Y) : Set Y))
      ((stellW .sz S).map κ) :=
    { isPGroup := hTsyl ▸ Tsyl.isPGroup'
      not_dvd_index := hTsyl ▸ Tsyl.not_dvd_index
      isCoatom := hco
      le_M := range_le_normalizer_map κ (inferInstance : (stellW .sz S).Normal)
      le_S := map_le_range κ _
      elemAb := isElemAbelian_map isElemAbelian_stellW κ
      not_le_normalCore := hcore }
  obtain ⟨L, hL | hL⟩ := h24 Y hκ.holds hhyp
  · exact Stell33.false_of_isL24 hThmA hκ le_rfl hL
  · exact false_of_isL24Sz h29 h25 hκ hL

theorem stellmacherClauseSz_of_inputs (hThmA : Stell33.ThmA.{u} .sz)
    (h29 : Stell.Hyp29.{u} .sz) (h24 : Hyp24Sz.{u}) (h25 : Hyp25dSz.{u}) {S : Type u} [Group S]
    [Finite S] [Nontrivial S] (hS : IsPGroup 2 S) : StellmacherClauseSz.{u, v} S :=
  stellmacherClauseSz_of_f2 hS fun _ _ _ hκ =>
    Stell.stellW_normal_of_f2_of_type
      (fun Y _ κ hκ' => stellW_normal_of_three_four hThmA h29 h24 h25 Y κ hκ') hκ

theorem stellmacherSzAll_of_inputs (hThmA : Stell33.ThmA.{u} .sz) (h29 : Stell.Hyp29.{u} .sz)
    (h24 : Hyp24Sz.{u}) (h25 : Hyp25dSz.{u}) : StellmacherSzAll.{u, v} :=
  fun _ _ _ hS hS1 =>
    haveI := hS1
    stellmacherClauseSz_of_inputs hThmA h29 h24 h25 hS

end CFSG.RankThree.S4Free.Stell34
