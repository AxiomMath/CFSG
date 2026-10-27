module

public import CFSG.LocalAnalysis.WeakClosure81.EightEightDefs

import CFSG.GroupTheory.PGroup.ExistsNeOneCommute
import CFSG.Models.Blueprint
import CFSG.LocalAnalysis.WeakClosure81.FiveFiveFstar
import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4Act
import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4Model

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsMaxParabolicOver SwapsParabolics)

theorem not_inf_centralizer_le_normalizer_of_isSimpleGroup {Q : Type} [Group Q] [Finite Q]
    {L T : Subgroup Q} (hLn : L.Normal) (hT : IsPGroup 2 T) (hTL : T ⊓ L ≠ ⊥) {a : Q}
    (haT : a ∈ T) (hs : IsSimpleGroup ↥(L ⊓ centralizer ({a} : Set Q)))
    (hnab : ∃ x y : ↥(L ⊓ centralizer ({a} : Set Q)), x * y ≠ y * x) :
    ¬ L ⊓ centralizer ({a} : Set Q) ≤ normalizer ((T ⊓ L : Subgroup Q) : Set Q) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : L.Normal := hLn
  rintro hX
  have haNorm : a ∈ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨hxT, hxL⟩
      exact ⟨by simpa [mul_assoc] using T.mul_mem (T.mul_mem haT hxT) (T.inv_mem haT),
        hLn.conj_mem x hxL a⟩
    · rintro ⟨hxT, hxL⟩
      refine ⟨?_, ?_⟩
      · have h := T.mul_mem (T.mul_mem (T.inv_mem haT) hxT) haT
        simpa [mul_assoc] using h
      · have h := hLn.conj_mem (a * x * a⁻¹) hxL a⁻¹
        simpa [mul_assoc] using h
  have hU2 : IsPGroup 2 (T ⊓ L : Subgroup Q) := hT.to_inf_left
  have hzp : IsPGroup 2 (Subgroup.zpowers a) := hT.to_le (Subgroup.zpowers_le.mpr haT)
  obtain ⟨u, huU, hu1, hucomm⟩ :=
    CFSG.GroupTheory.exists_ne_one_commute_of_normalizes (p := 2)
      (P := Subgroup.zpowers a) (O := (T ⊓ L : Subgroup Q)) hzp hU2 hTL
      (Subgroup.le_normalizer_iff.mp (Subgroup.zpowers_le.mpr haNorm))
  have huX : u ∈ L ⊓ centralizer ({a} : Set Q) := by
    refine Subgroup.mem_inf.mpr ⟨huU.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hucomm a (Subgroup.mem_zpowers a)).symm
  have hne : (T ⊓ L) ⊓ (L ⊓ centralizer ({a} : Set Q)) ≠ ⊥ := by
    intro hbot
    have hmem : u ∈ (⊥ : Subgroup Q) := by
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨huU, huX⟩
    exact hu1 (Subgroup.mem_bot.mp hmem)
  haveI hNorm : ((T ⊓ L).subgroupOf (L ⊓ centralizer ({a} : Set Q))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer_inf, Subgroup.le_normalizer_iff]
    intro x hx y hy
    exact Subgroup.mem_inf.mpr
      ⟨Subgroup.le_normalizer_iff.mp hX x hx y hy.1,
        (L ⊓ centralizer ({a} : Set Q)).mul_mem
          ((L ⊓ centralizer ({a} : Set Q)).mul_mem hx hy.2)
          ((L ⊓ centralizer ({a} : Set Q)).inv_mem hx)⟩
  haveI : IsSimpleGroup ↥(L ⊓ centralizer ({a} : Set Q)) := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((T ⊓ L).subgroupOf (L ⊓ centralizer ({a} : Set Q))) with hbot | htop
  · exact hne (disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hbot))
  ·
    have hXle : L ⊓ centralizer ({a} : Set Q) ≤ T ⊓ L :=
      Subgroup.subgroupOf_eq_top.mp htop
    have hX2 : IsPGroup 2 (L ⊓ centralizer ({a} : Set Q) : Subgroup Q) := hU2.to_le hXle
    haveI hNtriv : Nontrivial ↥(L ⊓ centralizer ({a} : Set Q)) := by
      obtain ⟨x, y, hxy⟩ := hnab
      exact ⟨x, y, fun h => hxy (by rw [h])⟩
    have hcenter : Subgroup.center ↥(L ⊓ centralizer ({a} : Set Q)) = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
          (Subgroup.center ↥(L ⊓ centralizer ({a} : Set Q))) with h | h
      · exact absurd h (IsPGroup.bot_lt_center (p := 2) hX2).ne'
      · exact h
    obtain ⟨x, y, hxy⟩ := hnab
    exact hxy (((Subgroup.mem_center_iff.mp (hcenter ▸ Subgroup.mem_top x)) y).symm)

private theorem isMaxParabolicOver_map_conj {Q : Type} [Group Q] {X S P : Subgroup Q} {g : Q}
    (hP : IsMaxParabolicOver X S P) :
    IsMaxParabolicOver (X.map (MulAut.conj g).toMonoidHom)
      (S.map (MulAut.conj g).toMonoidHom) (P.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨hPX, hN, hPne, hmax⟩ := hP
  refine ⟨Subgroup.map_mono hPX, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_equiv_normalizer_eq S (MulAut.conj g),
      ← Subgroup.map_inf X _ _ (MulAut.conj g).injective]
    exact Subgroup.map_mono hN
  · intro h
    exact hPne (Subgroup.map_injective (MulAut.conj g).injective h)
  · intro Y hPY hYX
    have hmapY : (Y.comap (MulAut.conj g).toMonoidHom).map (MulAut.conj g).toMonoidHom = Y :=
      Subgroup.map_comap_eq_self_of_surjective (MulAut.conj g).surjective Y
    have hle : P ≤ Y.comap (MulAut.conj g).toMonoidHom := by
      refine (Subgroup.map_le_map_iff_of_injective
        (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective).mp ?_
      rwa [hmapY]
    have hYX' : Y.comap (MulAut.conj g).toMonoidHom ≤ X := by
      intro y hy
      obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp (hYX hy)
      have hxy' : x = y := (MulAut.conj g).injective hxy
      rwa [hxy'] at hx
    rcases hmax (Y.comap (MulAut.conj g).toMonoidHom) hle hYX' with h | h
    · left; rw [← hmapY, h]
    · right; rw [← hmapY, h]

private theorem map_conj_map_conj {Q : Type} [Group Q] (A : Subgroup Q) (s t : Q) :
    (A.map (MulAut.conj s).toMonoidHom).map (MulAut.conj t).toMonoidHom =
      A.map (MulAut.conj (t * s)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_one {Q : Type} [Group Q] (A : Subgroup Q) :
    A.map (MulAut.conj (1 : Q)).toMonoidHom = A := by
  have h : MulAut.conj (1 : Q) = 1 := by ext x; simp
  rw [h]
  exact Subgroup.map_id A

theorem sp4_graph_involution_centralizer_escape {Q : Type}
    [Group Q] [Finite Q] {L T : Subgroup Q} (hLn : L.Normal) (hLs : IsSimpleGroup ↥L)
    (hnab : ∃ x y : ↥L, x * y ≠ y * x) {f : ℕ} (hL : CFSG.Models.LieModel ↥L .PSp 2 2 f)
    (hC : centralizer (L : Set Q) = ⊥) (hT : IsSylowIn 2 T ⊤) (hLT : L ⊔ T = ⊤) {a : Q}
    (haT : a ∈ T) (ha : a * a = 1) (haD : ActsOnDynkinMod ⊥ L a) :
    ¬ L ⊓ centralizer ({a} : Set Q) ≤ normalizer ((T ⊓ L : Subgroup Q) : Set Q) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨haNL, R, hR, hRmoved⟩ := haD
  have haL : a ∉ L := by
    intro h
    exact hRmoved a h (by rw [inv_mul_cancel, conjSubgroup_one])
  have hNtop : (L.subgroupOf (⊤ : Subgroup Q)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_top,
      Subgroup.normalizer_eq_top_iff.mpr hLn]
  have hUsyl : IsSylowIn 2 (T ⊓ L) L := hT.inf_normal (N := L) le_top hNtop
  obtain ⟨-, hRlt, hRmax, S, -, hSL, hSpow, hSodd, hSN⟩ := hR
  have hS2 : IsPGroup 2 S := by
    intro s
    obtain ⟨k, hk⟩ := hSpow s s.2
    exact ⟨k, Subtype.ext (by simpa using Subgroup.mem_bot.mp hk)⟩
  have hSsyl : IsSylowIn 2 S L := ⟨hSL, hS2, hSodd⟩
  have hTL : T ⊓ L ≠ ⊥ := by
    intro hbot
    have hLodd : ¬ 2 ∣ Nat.card ↥L := by
      have h := hUsyl.not_dvd_relIndex
      rwa [hbot, Subgroup.relIndex, Subgroup.bot_subgroupOf, Subgroup.index_bot] at h
    have hSbot : S = ⊥ := by
      obtain ⟨k, hk⟩ := hS2.exists_card_eq
      have hdvd : 2 ^ k ∣ Nat.card ↥L := hk ▸ Subgroup.card_dvd_of_le hSL
      have hk0 : k = 0 := by
        rcases Nat.eq_zero_or_pos k with h | h
        · exact h
        · exact absurd (dvd_trans (dvd_pow_self 2 h.ne') hdvd) hLodd
      have hk1 : Nat.card ↥S = 1 := by rw [hk, hk0, pow_zero]
      exact Subgroup.card_eq_one.mp hk1
    have hLeqR : L ≤ R := by
      have hnorm : Subgroup.normalizer ((⊥ : Subgroup Q) : Set Q) = ⊤ :=
        Subgroup.normalizer_eq_top_iff.mpr Subgroup.normal_bot
      rw [hSbot, hnorm, inf_top_eq] at hSN
      exact hSN
    exact absurd (le_antisymm hRlt.le hLeqR) hRlt.ne
  have hRover : IsMaxParabolicOver L S R := by
    refine ⟨hRlt.le, hSN, hRlt.ne, ?_⟩
    intro Y hRY hYL
    rcases eq_or_lt_of_le hRY with h | h
    · exact Or.inl h.symm
    · exact Or.inr (hRmax Y h hYL)
  obtain ⟨g, hgL, hg⟩ := Ch1Sec3.exists_conj_of_isSylowIn hSsyl hUsyl
  have hSW : T ⊓ L = S.map (MulAut.conj g).toMonoidHom := by
    ext x
    rw [hg x, Subgroup.mem_map]
    exact ⟨fun hx => ⟨g⁻¹ * x * g, hx, by simp [MulAut.conj_apply, mul_assoc]⟩,
      fun ⟨s, hs, hxs⟩ => by
        rw [← hxs]
        simpa [MulAut.conj_apply, mul_assoc] using hs⟩
  have hLmap : L.map (MulAut.conj g).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgL)
  set R' : Subgroup Q := R.map (MulAut.conj g).toMonoidHom with hR'def
  have hR'par : IsMaxParabolicOver L (T ⊓ L) R' := by
    have h := isMaxParabolicOver_map_conj (X := L) (S := S) (P := R) (g := g) hRover
    rwa [← hSW, hLmap] at h
  have hinv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hR'moved : R'.map (MulAut.conj a).toMonoidHom ≠ R' := by
    intro heq
    have hRinv : R = R'.map (MulAut.conj g⁻¹).toMonoidHom := by
      rw [hR'def, map_conj_map_conj R g g⁻¹, inv_mul_cancel]
      exact (map_conj_one R).symm
    have hkey : ∀ t : Q, R'.map (MulAut.conj (t * a)).toMonoidHom =
        R'.map (MulAut.conj t).toMonoidHom := by
      intro t
      rw [← map_conj_map_conj R' a t, heq]
    have hmL : (a * g⁻¹ * a) * g ∈ L := by
      have h1 : a * g⁻¹ * a ∈ L := by
        have h2 := hLn.conj_mem g⁻¹ (L.inv_mem hgL) a
        rwa [hinv] at h2
      exact L.mul_mem h1 hgL
    have hchain : R.map (MulAut.conj a).toMonoidHom =
        R.map (MulAut.conj ((a * g⁻¹ * a) * g)).toMonoidHom := by
      calc R.map (MulAut.conj a).toMonoidHom
          = (R'.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
              rw [hRinv]
        _ = R'.map (MulAut.conj (a * g⁻¹)).toMonoidHom := map_conj_map_conj R' g⁻¹ a
        _ = R'.map (MulAut.conj ((a * g⁻¹) * a)).toMonoidHom := (hkey (a * g⁻¹)).symm
        _ = R'.map (MulAut.conj (((a * g⁻¹ * a) * g) * g⁻¹)).toMonoidHom := by
              rw [show (a * g⁻¹ * a) * g * g⁻¹ = (a * g⁻¹) * a by group]
        _ = (R'.map (MulAut.conj g⁻¹).toMonoidHom).map
              (MulAut.conj ((a * g⁻¹ * a) * g)).toMonoidHom :=
              (map_conj_map_conj R' g⁻¹ ((a * g⁻¹ * a) * g)).symm
        _ = R.map (MulAut.conj ((a * g⁻¹ * a) * g)).toMonoidHom := by rw [← hRinv]
    have hconj_eq : conjSubgroup R a⁻¹ = conjSubgroup R ((a * g⁻¹ * a) * g)⁻¹ := by
      simpa [conjSubgroup] using hchain
    have hfinal : conjSubgroup R (a⁻¹ * ((a * g⁻¹ * a) * g)) = R := by
      rw [← conjSubgroup_conjSubgroup R a⁻¹, hconj_eq, conjSubgroup_conjSubgroup,
        inv_mul_cancel, conjSubgroup_one]
    exact hRmoved _ hmL hfinal
  have hnab' : ¬ ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := by
    rintro h
    obtain ⟨x, y, hxy⟩ := hnab
    exact hxy (Subtype.ext (h x x.2 y y.2))
  have hF : CFSG.LocalAnalysis.UniquenessCase.UC22.Fstar (⊤ : Subgroup Q) = L :=
    fstar_eq_of_isSimpleGroup_of_centralizer_eq_bot le_top hNtop hLs hnab'
      (by simpa using hC)
  have hSp : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSp4 ↥L f :=
    CFSG.Models.LieModel.toBlueprint (by decide) hL
  have hf2 : 2 ≤ f := by
    have h1 := hL.admissible
    have hle : 1 ≤ f := h1.2.1
    have hne : f ≠ 1 := by
      rintro rfl
      exact h1.2.2.2 (by norm_num)
    omega
  have hswap : SwapsParabolics T L := ⟨a, haT, R', hR'par, hR'moved⟩
  obtain ⟨P₀, P₁, F, hFld, hFin, w, hset⟩ :=
    SwapSp4.exists_setting (Q := Q) (L := L) (T := T) (n := f) hF hLs hSp hf2 hT hLT hswap
  letI : Field F := hFld
  letI : Finite F := hFin
  have hpar : ∀ Y : Subgroup Q, IsMaxParabolicOver L (T ⊓ L) Y → Y = P₀ ∨ Y = P₁ := by
    intro Y hY
    have hUY : T ⊓ L ≤ Y :=
      le_trans (le_inf inf_le_right Subgroup.le_normalizer) hY.2.1
    have hYlt : Y < L := lt_of_le_of_ne hY.1 hY.2.2.1
    rcases hset.le_or_le Y hUY hYlt with hle | hle
    · rcases hY.2.2.2 P₀ hle hset.par₀.1 with h | h
      · exact Or.inl h.symm
      · exact absurd h hset.par₀.2.2.1
    · rcases hY.2.2.2 P₁ hle hset.par₁.1 with h | h
      · exact Or.inr h.symm
      · exact absurd h hset.par₁.2.2.1
  have haUnorm : a ∈ Subgroup.normalizer ((T ⊓ L : Subgroup Q) : Set Q) :=
    Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer haT, haNL⟩)
  have hR'a : IsMaxParabolicOver L (T ⊓ L) (R'.map (MulAut.conj a).toMonoidHom) := by
    have hLmapA : L.map (MulAut.conj a).toMonoidHom = L := by
      simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp haNL
    have hUmapA : (T ⊓ L).map (MulAut.conj a).toMonoidHom = T ⊓ L := by
      simpa using Subgroup.mem_normalizer_iff_map_conj_eq.mp haUnorm
    have h := isMaxParabolicOver_map_conj (X := L) (S := T ⊓ L) (P := R') (g := a) hR'par
    rwa [hLmapA, hUmapA] at h
  have hcases : R' = P₀ ∨ R' = P₁ := hpar R' hR'par
  have hcases' : R'.map (MulAut.conj a).toMonoidHom = P₀ ∨
      R'.map (MulAut.conj a).toMonoidHom = P₁ := hpar _ hR'a
  have hsw : P₀.map (MulAut.conj a).toMonoidHom = P₁ := by
    rcases hcases with h0 | h1
    · rcases hcases' with h | h
      · exact absurd (h.trans h0.symm) hR'moved
      · rw [← h0]; exact h
    · rcases hcases' with h | h
      · calc P₀.map (MulAut.conj a).toMonoidHom
            = (R'.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
                rw [h]
          _ = R'.map (MulAut.conj (a * a)).toMonoidHom := map_conj_map_conj R' a a
          _ = R'.map (MulAut.conj (1 : Q)).toMonoidHom := by rw [ha]
          _ = R' := map_conj_one R'
          _ = P₁ := h1
      · rw [← h1] at h
        exact absurd h hR'moved
  have hodd : Odd f := SwapSp4.Setting.odd_of_swap hset haT ha hsw
  obtain ⟨hsimple, hnabC⟩ := hset.suzuki hodd a haT haL ha
  exact not_inf_centralizer_le_normalizer_of_isSimpleGroup hLn hT.isPGroup hTL haT hsimple
    hnabC

end CFSG.LocalAnalysis.WeakClosure81

end
