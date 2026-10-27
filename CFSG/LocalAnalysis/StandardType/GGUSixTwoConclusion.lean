module

public import CFSG.LocalAnalysis.StandardType.GGUSixTwoLemmaDWidth
public import CFSG.LocalAnalysis.StandardType.GGUSixTwoNotL12
public import CFSG.LargeExtraspecial.S14C12Lit
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.GroupTheory.GLnTwoSplitting.Transvection
public import CFSG.LargeExtraspecial.S14Claims
public import CFSG.LargeExtraspecial.S4EightA
public import CFSG.LargeExtraspecial.S4EightB
public import CFSG.LargeExtraspecial.S4EightC
public import CFSG.LargeExtraspecial.S4EightD
public import CFSG.LargeExtraspecial.S4EightE
public import CFSG.LargeExtraspecial.S4EightF4
public import CFSG.LargeExtraspecial.S4EightMain
public import CFSG.LargeExtraspecial.S4SevenB3
public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType.USixTwo

open CFSG.Assembly CFSG.Open CFSG.Blueprint Matrix
open scoped MatrixGroups

variable {K : Type} [Field K]

theorem chevalleyExceptionalModel_of_setting {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hK : Nat.card K = 4) {L : Subgroup G}
    (φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
    (S : CFSG.LargeExtraspecial.Setting G) (hw : S.width = 10) (hLM : L ≤ S.M)
    (hLQ : L ⊓ S.QG = ⊥) (hT : CFSG.LargeExtraspecial.Bridge.OrderMainFor G)
    (hRS : CFSG.LargeExtraspecial.S14.ReifartSmithU62Input)
    (hU12 : ¬ Nonempty (G ≃* timmesfeldPSU 12)) :
    ChevalleyExceptionalModel G .twistedE6 2 1 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKU : Nat.card K = (2 ^ 1) ^ 2 := by rw [hK]; norm_num
  haveI hfinK : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; norm_num)
  haveI hsimpleU : IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) :=
    CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K 2 1 hKU 6 (by norm_num)
      (by norm_num)
  haveI hsimpleL : IsSimpleGroup L := MulEquiv.isSimpleGroup φ
  haveI hperfU : Group.IsPerfect (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))) := by
    haveI : Group.IsPerfect ↥(LargeEvenSUGroup (Fin 6) K (2 ^ 1)) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU (p := 2) (f := 1) hKU (n := 6)
        (by norm_num) (by norm_num)
    exact Group.IsPerfect.ofSurjective
      (f := LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ 1)))
      (QuotientGroup.mk'_surjective _)
  haveI hperfL : Group.IsPerfect L :=
    Group.IsPerfect.ofSurjective
      (f := (φ.symm : LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1)) →* L))
      φ.symm.surjective
  have h11L : 11 ∣ Nat.card L := by
    rw [Nat.card_congr φ.toEquiv]
    change 11 ∣ Nat.card (CFSG.Open.StatedProj (CFSG.Open.StatedSU 6 (2 ^ 1) K))
    rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU (p := 2) (f := 1) (n := 6)
      Nat.prime_two le_rfl hKU (by norm_num)]
    decide
  have h11PSL : ¬ 11 ∣ Nat.card (PSL(6, ZMod 2)) := by
    change ¬ 11 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 6) (ZMod 2))
    rw [CFSG.OrderReductions.LinearOrders.card_projectiveSpecialLinear (ZMod 2) 6 (by norm_num),
      Nat.card_eq_fintype_card, ZMod.card]
    decide
  have hnonab : ∃ a b : G, a * b ≠ b * a := by
    have hnc : ¬ ∀ x y : L, x * y = y * x := by
      intro h
      exact Group.IsPerfect.not_isMulCommutative L ⟨⟨h⟩⟩
    by_contra hcon
    push Not at hcon
    exact hnc fun x y => Subtype.ext (hcon (x : G) (y : G))
  obtain ⟨a, b, hab⟩ := hnonab
  have h := (CFSG.LargeExtraspecial.Bridge.orderMainFor_iff G).mp hT ⟨a, b, hab⟩ S
  rw [hw] at h
  rw [CFSG.LargeExtraspecial.Bridge.timmesfeldOrderConclusion_iff] at h
  let ι : L →* S.Mbar := S.ρ.rangeRestrict.comp (Subgroup.inclusion hLM)
  have hιker : ι.ker = ⊥ := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_bot]
    constructor
    · intro hx
      have hxρ : S.ρ ⟨x, hLM x.2⟩ = 1 := by
        have h1 : ((ι x : S.Mbar) : S.O) = 1 := by rw [hx]; rfl
        exact h1
      have hxQ : (x : G) ∈ S.QG :=
        S.mem_QG_iff.mpr ⟨hLM x.2, by rw [← S.ker_ρ, MonoidHom.mem_ker]; exact hxρ⟩
      have hxbot : (x : G) ∈ L ⊓ S.QG := ⟨x.2, hxQ⟩
      rw [hLQ] at hxbot
      exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
    · intro hx
      rw [hx, map_one ι]
  have hιinj : Function.Injective ι := (MonoidHom.ker_eq_bot_iff ι).mp hιker
  rcases h with h1 | (h2a | h2b) | h3 | h4 | h5 | h6 | h7 | h8
  · exfalso; omega
  · exact absurd (show Nonempty (G ≃* PSL(12, ZMod 2)) from h2a)
      (not_nonempty_mulEquiv_psl12 hK φ)
  · exact absurd (show Nonempty (G ≃* timmesfeldPSU 12) from h2b) hU12
  · obtain ⟨-, -, q, -, hcase⟩ := h3
    have hcard1024 : Nat.card (Fin 10 → ZMod 2) = 1024 := by
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num
    have key : ∀ {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
        (X : Subgroup (V ≃ₗ[ZMod 2] V)) (e : S.Mbar ≃* (Equiv.Perm (Fin 3) × X)),
        Nat.card V = 1024 → False := by
      intro V _ _ _ X e hV
      let f : S.Mbar →* (V ≃ₗ[ZMod 2] V) :=
        X.subtype.comp ((MonoidHom.snd (Equiv.Perm (Fin 3)) X).comp e.toMonoidHom)
      let g : L →* (V ≃ₗ[ZMod 2] V) := f.comp ι
      rcases hsimpleL.eq_bot_or_eq_top_of_normal g.ker with hbot | htop
      · have hginj : Function.Injective g := (MonoidHom.ker_eq_bot_iff g).mp hbot
        have hψinj : Function.Injective (g.comp φ.symm.toMonoidHom) := by
          intro x y hxy
          exact φ.symm.injective (hginj hxy)
        have h20 := twenty_le_finrank_of_injective (V := V) hK (g.comp φ.symm.toMonoidHom) hψinj
        have hcard : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
          rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
        have h2 : 2 ^ 20 ≤ Nat.card V := by
          rw [hcard]
          exact Nat.pow_le_pow_right (by norm_num) h20
        rw [hV] at h2
        norm_num at h2
      · have htop2 : ∀ x : L, (e (ι x)).2 = 1 := by
          intro x
          have hmem : x ∈ g.ker := by rw [htop]; exact Subgroup.mem_top x
          have h1 : g x = 1 := by simpa using hmem
          have h2 : X.subtype ((e (ι x)).2) = X.subtype 1 := by
            simpa [g, f, MonoidHom.comp_apply] using h1
          exact X.subtype_injective h2
        let p : L →* Equiv.Perm (Fin 3) :=
          (MonoidHom.fst (Equiv.Perm (Fin 3)) X).comp (e.toMonoidHom.comp ι)
        have hpinj : Function.Injective p := by
          intro x y hxy
          have hxy' : (e (ι x)).1 = (e (ι y)).1 := hxy
          have h1 : e (ι x) = e (ι y) := by
            refine Prod.ext hxy' ?_
            rw [htop2 x, htop2 y]
          exact hιinj (e.injective h1)
        have hcard : Nat.card L ≤ Nat.card (Equiv.Perm (Fin 3)) :=
          Nat.card_le_card_of_injective p hpinj
        have hcard6 : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
          rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
          norm_num
        rw [hcard6] at hcard
        have h11 : 11 ≤ Nat.card L := Nat.le_of_dvd Nat.card_pos h11L
        omega
    rcases hcase with h | h
    · obtain ⟨e⟩ := h
      exfalso
      exact key _ e hcard1024
    · obtain ⟨e⟩ := h
      exfalso
      exact key _ e hcard1024
  · exfalso; obtain ⟨h, -⟩ := h4; omega
  · obtain ⟨-, hidx, hF⟩ := h5
    haveI hFnormal : (timmesfeldFStar S.Mbar).Normal := by
      rw [← CFSG.LargeExtraspecial.Bridge.generalizedFitting_eq_timmesfeldFStar]
      exact (CFSG.LocalCores.generalized_fitting_characteristic).2
    let q : S.Mbar →* (S.Mbar ⧸ timmesfeldFStar S.Mbar) := QuotientGroup.mk' _
    let g : L →* (S.Mbar ⧸ timmesfeldFStar S.Mbar) := q.comp ι
    rcases hsimpleL.eq_bot_or_eq_top_of_normal g.ker with hbot | htop
    · have hginj : Function.Injective g := (MonoidHom.ker_eq_bot_iff g).mp hbot
      have hqcard : Nat.card (S.Mbar ⧸ timmesfeldFStar S.Mbar) ≤ 2 := by
        rw [← Subgroup.index_eq_card]
        exact hidx
      have hle : Nat.card L ≤ Nat.card (S.Mbar ⧸ timmesfeldFStar S.Mbar) :=
        Nat.card_le_card_of_injective g hginj
      have h11 : 11 ≤ Nat.card L := Nat.le_of_dvd Nat.card_pos h11L
      omega
    · have hleF : ι.range ≤ timmesfeldFStar S.Mbar := by
        rintro _ ⟨x, rfl⟩
        have hmem : x ∈ g.ker := by rw [htop]; exact Subgroup.mem_top x
        have hx1 : (QuotientGroup.mk' (timmesfeldFStar S.Mbar)) (ι x) = 1 := by
          simpa [g, q, MonoidHom.comp_apply] using hmem
        rw [← QuotientGroup.ker_mk' (timmesfeldFStar S.Mbar), MonoidHom.mem_ker]
        exact hx1
      have h11F : 11 ∣ Nat.card (timmesfeldFStar S.Mbar) := by
        have h1 : 11 ∣ Nat.card ι.range := by
          rw [show ι.range = (⊤ : Subgroup L).map ι from (Subgroup.map_top ι).symm,
            Subgroup.card_map_of_injective hιinj, Subgroup.card_top]
          exact h11L
        exact h1.trans (Subgroup.card_dvd_of_le hleF)
      rcases hF with h | h
      · obtain ⟨e⟩ := h
        exfalso
        exact h11PSL (by rwa [Nat.card_congr e.toEquiv] at h11F)
      · obtain ⟨e⟩ := h
        exact hRS G S hw ⟨e⟩
  · exfalso; obtain ⟨h, -⟩ := h6; omega
  · exfalso; obtain ⟨h, -⟩ := h7; omega
  · exfalso; rcases h8.width_eq with h | h <;> omega

namespace LocalSetting

variable {ω : K} {hω : ω ^ 2 + ω + 1 = 0}

theorem chevalleyExceptionalModel {G : Type} [Group G] [Finite G] [IsSimpleGroup G] [Finite K]
    {b : G} {L : Subgroup G} {φ : L ≃* LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ 1))}
    {Bs : Subgroup G} (hG : IsCharTwoType G) (hS : LocalSetting hω b L φ Bs) {W : Subgroup G}
    (hW : W ≤ Subgroup.normalizer (Bs : Set G))
    (hWb : W ⊓ Subgroup.centralizer {b} ≤
      (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G))
    (hn : ∃ n ∈ W, ∃ hnL : n * b * n⁻¹ ∈ L, φ ⟨n * b * n⁻¹, hnL⟩ = threeA hω)
    (hr : ∃ g ∈ W, (∀ y ∈ Bs ⊓ L, g * y * g⁻¹ = y) ∧ g * b * g⁻¹ = b⁻¹)
    (hT : CFSG.LargeExtraspecial.Bridge.OrderMainFor G)
    (hRS : CFSG.LargeExtraspecial.S14.ReifartSmithU62Input)
    (hU12 : ¬ Nonempty (G ≃* timmesfeldPSU 12)) :
    ChevalleyExceptionalModel G .twistedE6 2 1 := by
  obtain ⟨n, hnW, hnL, hnφ⟩ := hn
  obtain ⟨g, hgW, hgB, hgb⟩ := hr
  obtain ⟨t, htg, htN, ht2, htb, htL⟩ := exists_involution hG hS hgB hgb
  have htW : t ∈ W := Subgroup.zpowers_le.mpr hgW htg
  have htnW : n⁻¹ * t * n ∈ W := W.mul_mem (W.mul_mem (W.inv_mem hnW) htW) hnW
  have htCb : n⁻¹ * t * n ∈ Subgroup.centralizer ({b} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hcomm : (n * b * n⁻¹) * t = t * (n * b * n⁻¹) :=
      Subgroup.mem_centralizer_iff.mp htL (n * b * n⁻¹) hnL
    calc (n⁻¹ * t * n) * b = n⁻¹ * (t * (n * b * n⁻¹)) * n := by group
      _ = n⁻¹ * ((n * b * n⁻¹) * t) * n := by rw [hcomm]
      _ = b * (n⁻¹ * t * n) := by group
  have htA : n⁻¹ * t * n ∈
      (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G) :=
    hWb (Subgroup.mem_inf.mpr ⟨htnW, htCb⟩)
  have hnA : ∃ n ∈ Subgroup.normalizer (Bs : Set G), ∃ hnL : n * b * n⁻¹ ∈ L,
      φ ⟨n * b * n⁻¹, hnL⟩ = threeA hω ∧ n⁻¹ * t * n ∈
        (L ⊓ Subgroup.normalizer (Bs : Set G)) ⊔ Subgroup.centralizer (Bs : Set G) := by
    refine ⟨n, hW hnW, ?_⟩
    exact ⟨hnL, hnφ, htA⟩
  obtain ⟨S, hz, hQG, hw⟩ := exists_setting_width_ten hG hS htN ht2 htb htL hnA
  have hLM : L ≤ S.M := by
    change L ≤ Subgroup.centralizer ({S.z} : Set G)
    rw [hz]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp htL) x hx)
  have hLQ : L ⊓ S.QG = ⊥ := by
    rw [hQG]
    exact inf_pCoreOf_centralizer_eq_bot hS htL
  exact chevalleyExceptionalModel_of_setting hS.card_K φ S hw hLM hLQ hT hRS hU12

end LocalSetting

end CFSG.StandardType.USixTwo

end
