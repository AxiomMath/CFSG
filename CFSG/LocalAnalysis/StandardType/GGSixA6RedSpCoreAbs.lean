module

public import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpDefs
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpSplit
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpFree
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpLie
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedSpA6
public import CFSG.LocalAnalysis.StandardType.GGSixA6RedNotShape

public section

namespace CFSG.StandardType.A6Red

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

private theorem ggA6SpFixer_orthogonal_le_centralizer
    {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (B : BilinForm F V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (U : Submodule F V) (hU : (B.restrict U).Nondegenerate)
    (A : Subgroup (V ≃ₗ[F] V)) (hA : A ≤ ggA6SpFixer B U) :
    ggA6SpFixer B (B.orthogonal U) ≤ Subgroup.centralizer (A : Set (V ≃ₗ[F] V)) := by
  intro h hh
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  have hcompl : IsCompl U (B.orthogonal U) :=
    LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hB.isRefl hU
  have horth : B.orthogonal (B.orthogonal U) = U :=
    LinearMap.BilinForm.orthogonal_orthogonal hnd hB.isRefl U
  have hhU : ∀ u ∈ U, h u ∈ U := by
    intro u hu
    rw [← horth, LinearMap.BilinForm.mem_orthogonal_iff]
    intro x hx
    have hxh : h x = x := hh.2 x hx
    have hiso : B (h x) (h u) = B x u :=
      TauCeti.BilinForm.mem_isometryGroup_iff.mp hh.1 x u
    rw [hxh] at hiso
    rw [hiso]
    exact hB.eq_iff.mpr (hx u hu)
  have haUorth : ∀ x ∈ B.orthogonal U, a x ∈ B.orthogonal U := by
    intro x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have hafix : a u = u := (hA ha).2 u hu
    have hiso : B (a u) (a x) = B u x :=
      TauCeti.BilinForm.mem_isometryGroup_iff.mp (hA ha).1 u x
    rw [hafix] at hiso
    rw [hiso]
    exact hx u hu
  apply LinearEquiv.ext
  intro v
  change a (h v) = h (a v)
  obtain ⟨w, hw, z, hz, hwz⟩ := Submodule.mem_sup.mp
    (show v ∈ U ⊔ B.orthogonal U by rw [hcompl.sup_eq_top]; exact Submodule.mem_top)
  rw [← hwz]
  simp only [map_add, hh.2 z hz, (hA ha).2 w hw, hh.2 (a z) (haUorth z hz),
    (hA ha).2 (h w) (hhU w hw)]

theorem ggA6_sp_core_abs
    {F : Type} [Field F] {V : Type} [AddCommGroup V] [Module F V] [Finite F] [CharP F 2]
    [FiniteDimensional F V] (B : BilinForm F V) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (P : Subgroup (V ≃ₗ[F] V)) (hPB : P ≤ TauCeti.BilinForm.isometryGroup B) (hodd : Odd (Nat.card P))
    (hab : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (x : V ≃ₗ[F] V) (hxP : x ∈ P)
    (J L : Subgroup (V ≃ₗ[F] V))
    (hJ : IsComponentOf J (TauCeti.BilinForm.isometryGroup B ⊓
      Subgroup.centralizer (P : Set (V ≃ₗ[F] V))))
    (hL : IsComponentOf L (TauCeti.BilinForm.isometryGroup B ⊓
      Subgroup.centralizer ({x} : Set (V ≃ₗ[F] V))))
    (hJL : J ≤ L) (hPL : ¬ P ≤ Subgroup.centralizer (L : Set (V ≃ₗ[F] V)))
    (hA6 : Nonempty (↥J ≃* alternatingGroup (Fin 6))) :
    Nat.card F = 2 ∧ ∃ m : ℕ, 3 ≤ m ∧ 2 * m ≤ Module.finrank F V ∧ LieModel ↥L .PSp m 2 1 := by
  let W : Submodule F V := ggA6SpFixed P
  let W' : Submodule F V := B.orthogonal W
  obtain ⟨hWnd, hWcompl⟩ := ggA6_sp_fixed_nondegenerate B hB hnd P hPB hodd
  rcases ggA6_sp_dichotomy B hB hnd P hPB hodd hJ with hJfixW' | hJfixW
  ·
    have hJleFixer : J ≤ ggA6SpFixer B W' := by
      intro j hj
      exact ⟨(Subgroup.mem_inf.mp (hJ.1 hj)).1, hJfixW' j hj⟩
    have hPfixW : P ≤ ggA6SpFixer B W := by
      intro p hp
      exact ⟨hPB hp, fun v hv => hv p hp⟩
    have hFixer_le : ggA6SpFixer B W' ≤ TauCeti.BilinForm.isometryGroup B ⊓
        Subgroup.centralizer (P : Set (V ≃ₗ[F] V)) := by
      have hcent : ggA6SpFixer B W' ≤ Subgroup.centralizer (P : Set (V ≃ₗ[F] V)) :=
        ggA6SpFixer_orthogonal_le_centralizer B hB hnd W hWnd P hPfixW
      intro g hg
      exact ⟨hg.1, hcent hg⟩
    have hJcomp : IsComponentOf J (ggA6SpFixer B W') :=
      IsComponentOf.of_le_of_le hJ hJleFixer hFixer_le
    obtain ⟨hdimW, hcardF⟩ := ggA6_spA6 B hB hnd W hWnd hJcomp hA6
    let A : Subgroup (V ≃ₗ[F] V) := Subgroup.zpowers x
    let Wx : Submodule F V := ggA6SpFixed A
    let Wx' : Submodule F V := B.orthogonal Wx
    have hAP : A ≤ P := by
      change Subgroup.zpowers x ≤ P
      exact Subgroup.zpowers_le.mpr hxP
    have hAsp : A ≤ TauCeti.BilinForm.isometryGroup B := hAP.trans hPB
    have hoddA : Odd (Nat.card A) := by
      change Odd (Nat.card ↥(Subgroup.zpowers x))
      rw [Nat.card_zpowers]
      have hdvdp : orderOf x ∣ Nat.card P := by
        have h := orderOf_dvd_natCard (⟨x, hxP⟩ : ↥P)
        rwa [← Subgroup.orderOf_coe (⟨x, hxP⟩ : ↥P)] at h
      by_contra hoddx
      have heven : Even (orderOf x) := Nat.not_odd_iff_even.mp hoddx
      exact (Nat.not_odd_iff_even.mpr
        (even_iff_two_dvd.mpr (even_iff_two_dvd.mp heven |>.trans hdvdp))) hodd
    have hcentA : Subgroup.centralizer (A : Set (V ≃ₗ[F] V)) =
        Subgroup.centralizer ({x} : Set (V ≃ₗ[F] V)) := by
      change Subgroup.centralizer (Subgroup.zpowers x : Set (V ≃ₗ[F] V)) = _
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
    have hLA : IsComponentOf L (TauCeti.BilinForm.isometryGroup B ⊓
        Subgroup.centralizer (A : Set (V ≃ₗ[F] V))) := by
      rwa [hcentA]
    obtain ⟨hWxnd, hWxcompl⟩ := ggA6_sp_fixed_nondegenerate B hB hnd A hAsp hoddA
    have hWleWx : W ≤ Wx := by
      intro v hv a ha
      exact hv a (hAP ha)
    rcases ggA6_sp_dichotomy B hB hnd A hAsp hoddA hLA with hLfixWx' | hLfixWx
    ·
      have hLleH : L ≤ ggA6SpFixer B Wx' := by
        intro l hl
        exact ⟨(Subgroup.mem_inf.mp (hLA.1 hl)).1, hLfixWx' l hl⟩
      have hAfixer : A ≤ ggA6SpFixer B Wx := by
        intro a ha
        exact ⟨hAsp ha, fun v hv => hv a ha⟩
      have hFixer_le_A : ggA6SpFixer B Wx' ≤ TauCeti.BilinForm.isometryGroup B ⊓
          Subgroup.centralizer (A : Set (V ≃ₗ[F] V)) := by
        have hcent : ggA6SpFixer B Wx' ≤ Subgroup.centralizer (A : Set (V ≃ₗ[F] V)) :=
          ggA6SpFixer_orthogonal_le_centralizer B hB hnd Wx hWxnd A hAfixer
        intro g hg
        exact ⟨hg.1, hcent hg⟩
      have hLcompH : IsComponentOf L (ggA6SpFixer B Wx') :=
        IsComponentOf.of_le_of_le hLA hLleH hFixer_le_A
      have hWxalt : (B.restrict Wx).IsAlt := fun u => by
        simpa using hB (u : V)
      obtain ⟨m, hdimWx⟩ : ∃ m, Module.finrank F Wx = 2 * m :=
        even_iff_exists_two_mul.mp (LinearMap.BilinForm.IsAlt.even_finrank hWxalt hWxnd)
      have h4le : 4 ≤ Module.finrank F Wx := by
        rw [← hdimW]
        exact Submodule.finrank_mono hWleWx
      have hLne : L ≠ ⊥ := by
        intro hLbot
        have hJle : J ≤ ⊥ := hJL.trans (le_of_eq hLbot)
        have hJbot : J = ⊥ := le_bot_iff.mp hJle
        obtain ⟨e⟩ := hA6
        haveI : Nontrivial ↥J := e.toEquiv.nontrivial
        haveI : Subsingleton ↥J := by rw [hJbot]; infer_instance
        obtain ⟨p, q, hpq⟩ := ‹Nontrivial ↥J›
        exact hpq (Subsingleton.elim p q)
      have hm3 : 3 ≤ m := by
        by_contra hm
        have hmle : m ≤ 2 := by omega
        have hmeq : m = 2 := by omega
        have hfin_eq : Module.finrank F W = Module.finrank F Wx := by
          rw [hdimW, hdimWx, hmeq]
        have hWeq : W = Wx := Submodule.eq_of_le_of_finrank_eq hWleWx hfin_eq
        have hLcompW' : IsComponentOf L (ggA6SpFixer B W') := by
          have hHeq : ggA6SpFixer B W' = ggA6SpFixer B Wx' := by
            change ggA6SpFixer B (B.orthogonal W) = ggA6SpFixer B (B.orthogonal Wx)
            rw [hWeq]
          rwa [hHeq]
        have hJLeq : J = L := ggA6_spFour B hB hnd W hWnd hcardF hdimW hJL hLcompW' hA6
        apply hPL
        have hPleCJ : P ≤ Subgroup.centralizer (J : Set (V ≃ₗ[F] V)) := by
          intro p hp
          rw [Subgroup.mem_centralizer_iff]
          intro j hj
          exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hJ.1 hj)).2 p hp).symm
        rwa [hJLeq] at hPleCJ
      have hcardpow : Nat.card F = 2 ^ 1 := by rw [hcardF, pow_one]
      obtain ⟨hsimpleH, hLieH⟩ :=
        ggA6_spLie B hB hnd Wx hWxnd m 1 hcardpow hdimWx hm3
      have hLH : L = ggA6SpFixer B Wx' := by
        have hsub : (L.subgroupOf (ggA6SpFixer B Wx')).IsSubnormal :=
          hLcompH.2.1.subgroupOf
        rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hsimpleH hsub with hbot | htop
        · exact absurd (by
            rw [Subgroup.eq_bot_iff_forall]
            intro l hl
            have hl' : (⟨l, hLleH hl⟩ : ↥(ggA6SpFixer B Wx')) ∈
                L.subgroupOf (ggA6SpFixer B Wx') := hl
            rw [hbot] at hl'
            simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hl')) hLne
        · exact le_antisymm hLleH (Subgroup.subgroupOf_eq_top.mp htop)
      refine ⟨hcardF, m, hm3, ?_, ?_⟩
      · rw [← hdimWx]
        exact Submodule.finrank_le Wx
      · exact LieModel.of_mulEquiv (MulEquiv.subgroupCongr hLH).symm hLieH
    ·
      exfalso
      have hJfixWx : ∀ j ∈ J, ∀ v ∈ Wx, j v = v := fun j hj => hLfixWx j (hJL hj)
      have hJfixW : ∀ j ∈ J, ∀ v ∈ W, j v = v := by
        intro j hj v hv
        exact hJfixWx j hj v (hWleWx hv)
      have hJbot : J = ⊥ := by
        rw [Subgroup.eq_bot_iff_forall]
        intro j hj
        apply LinearEquiv.ext
        intro v
        change j v = v
        obtain ⟨w, hw, z, hz, hwz⟩ := Submodule.mem_sup.mp
          (show v ∈ W ⊔ W' by rw [hWcompl.sup_eq_top]; exact Submodule.mem_top)
        rw [← hwz]
        rw [map_add, hJfixW j hj w hw, hJfixW' j hj z hz]
      obtain ⟨e⟩ := hA6
      haveI : Nontrivial ↥J := e.toEquiv.nontrivial
      haveI : Subsingleton ↥J := by rw [hJbot]; infer_instance
      obtain ⟨p, q, hpq⟩ := ‹Nontrivial ↥J›
      exact hpq (Subsingleton.elim p q)
  ·
    exfalso
    haveI : IsMulCommutative ↥P := ⟨⟨fun a b => Subtype.ext (hab a.1 a.2 b.1 b.2)⟩⟩
    have hnil : Group.IsNilpotent ↥P := inferInstance
    have hlie : GGA6CharTwoLie ↥J := ggA6_sp_freeShape B hB hnd P hPB hodd hnil hJ hJfixW
    exact (ggA6_not_shape_of_a6 ↥J ↥J hA6 ⟨MulEquiv.refl _⟩) hlie

end CFSG.StandardType.A6Red
