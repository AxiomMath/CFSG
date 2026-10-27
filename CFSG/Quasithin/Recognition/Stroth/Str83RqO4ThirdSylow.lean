module

public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.Recognition.Stroth.Str83RqVertexBase

import CFSG.Quasithin.Recognition.St84.L2Group
import CFSG.Timmesfeld.RankOne.Quotient

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.St84
open scoped Pointwise MatrixGroups

variable {G : Type} [Group G] [Finite G]

private lemma conj_smul_eq_map_conj {Y : Type*} [Group Y] (H : Subgroup Y) (g : Y) :
    MulAut.conj g • H = H.map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]
  rfl

private lemma map_subgroupOf_conjSub_eq {L A : Subgroup G} (hA : A ≤ L) (a : ↥L)
    {Y : Type*} [Group Y] (φ : ↥L →* Y) :
    ((conjSub (a : G) A).subgroupOf L).map φ =
      ((A.subgroupOf L).map φ).map (MulAut.conj (φ a)).toMonoidHom := by
  have hconj : (A.subgroupOf L).map (MulAut.conj a).toMonoidHom =
      (conjSub (a : G) A).subgroupOf L := by
    change MulAut.conj a • (A.subgroupOf L) = (conjSub (a : G) A).subgroupOf L
    rw [Subgroup.conj_smul_subgroupOf hA a]
    rfl
  rw [← hconj]
  exact CFSG.Timmesfeld.RankOne.map_map_conj φ (A.subgroupOf L) a

private lemma isSylowTwoOf_conjSub {L T : Subgroup G} (hT : IsSylowTwoOf T L) (g : ↥L) :
    IsSylowTwoOf (conjSub (g : G) T) L := by
  have h := F7.isSylowTwoOf_conj hT (g : G)
  have hfix : conjSub (g : G) L = L := by
    change MulAut.conj (g : G) • L = L
    exact Subgroup.conj_smul_eq_self_of_mem g.2
  rwa [hfix] at h

private lemma exists_smul_eq_of_sylow_ne {f : ℕ} (hf1 : 1 ≤ f)
    {S S' : Sylow 2 (PSL(2, GaloisField 2 f))} (hSne : S ≠ S') :
    ∃ x ∈ (S : Subgroup (PSL(2, GaloisField 2 f))),
      ∃ y ∈ (S' : Subgroup (PSL(2, GaloisField 2 f))),
        x ≠ 1 ∧ y • S = x • S' ∧ x • S' ≠ S' ∧ x • S' ≠ S := by
  classical
  have hcardS : 1 < Nat.card (S : Subgroup (PSL(2, GaloisField 2 f))) := by
    rw [psl2_sylow_two_card (f := f) hf1 S]
    calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf1
  obtain ⟨x, hxS, hx1⟩ : ∃ x : PSL(2, GaloisField 2 f),
      x ∈ (S : Subgroup (PSL(2, GaloisField 2 f))) ∧ x ≠ 1 := by
    haveI : Nontrivial ↥(S : Subgroup (PSL(2, GaloisField 2 f))) :=
      Finite.one_lt_card_iff_nontrivial.mp hcardS
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥(S : Subgroup (PSL(2, GaloisField 2 f))))
    exact ⟨x, x.2, fun h => hx (Subtype.ext h)⟩
  have hVS : x • S' ≠ S' := by
    intro h
    have hxN : x ∈ Subgroup.normalizer (S' : Set (PSL(2, GaloisField 2 f))) :=
      Sylow.smul_eq_iff_mem_normalizer.mp h
    exact hSne ((psl2_sylow_two_normalizes_iff (f := f) hf1 hxS hx1).mp hxN).symm
  have hWS : x • S' ≠ S := by
    intro h
    have h' : S' = x⁻¹ • S := by
      simpa [← mul_smul] using congrArg (fun U => x⁻¹ • U) h
    have hfix : x⁻¹ • S = S := by
      rw [Sylow.smul_eq_iff_mem_normalizer]
      exact Subgroup.le_normalizer (S.inv_mem hxS)
    exact hSne (h'.trans hfix).symm
  obtain ⟨y, hy⟩ := psl2_sylow_two_smul_eq_of_ne (f := f) hf1
    (U := S') (V := S) (W := x • S') hSne hVS
  exact ⟨x, hxS, y, y.2, hx1, hy, hVS, hWS⟩

private lemma exists_sylow_image_data {L T T' : Subgroup G} {f : ℕ}
    (hL2 : IsL2Quot f (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L) (hT' : IsSylowTwoOf T' L)
    (hne : T ≠ T') :
    ∃ (e : oTwoQuot ↥L ≃* PSL(2, GaloisField 2 f))
      (S S' : Sylow 2 (PSL(2, GaloisField 2 f))),
      (S : Subgroup (PSL(2, GaloisField 2 f))) =
        (T.subgroupOf L).map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 ↥L))) ∧
      (S' : Subgroup (PSL(2, GaloisField 2 f))) =
        (T'.subgroupOf L).map (e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 ↥L))) ∧
      S ≠ S' := by
  classical
  obtain ⟨e⟩ := hL2
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L)
  let ψ : ↥L →* PSL(2, GaloisField 2 f) := e.toMonoidHom.comp π
  obtain ⟨P, hP⟩ := exists_sylow_oTwoQuot_of_isSylowTwoOf (L := L) hT
  obtain ⟨P', hP'⟩ := exists_sylow_oTwoQuot_of_isSylowTwoOf (L := L) hT'
  let S : Sylow 2 (PSL(2, GaloisField 2 f)) :=
    P.mapSurjective (f := e.toMonoidHom) e.surjective
  let S' : Sylow 2 (PSL(2, GaloisField 2 f)) :=
    P'.mapSurjective (f := e.toMonoidHom) e.surjective
  have hScoe : (S : Subgroup (PSL(2, GaloisField 2 f))) =
      (T.subgroupOf L).map ψ := by
    change (P : Subgroup (oTwoQuot ↥L)).map e.toMonoidHom = _
    rw [hP, Subgroup.map_map]
  have hS'coe : (S' : Subgroup (PSL(2, GaloisField 2 f))) =
      (T'.subgroupOf L).map ψ := by
    change (P' : Subgroup (oTwoQuot ↥L)).map e.toMonoidHom = _
    rw [hP', Subgroup.map_map]
  have hneBar : (P : Subgroup (oTwoQuot ↥L)) ≠ (P' : Subgroup (oTwoQuot ↥L)) := by
    intro hEq
    exact hne (map_oTwoQuot_injective_of_isSylowTwoOf hT hT'
      (by simpa only [hP, hP'] using hEq))
  have hSne : S ≠ S' := by
    intro hSS
    apply hneBar
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    calc
      (P : Subgroup (oTwoQuot ↥L)).map e.toMonoidHom =
          (S : Subgroup (PSL(2, GaloisField 2 f))) := rfl
      _ = (S' : Subgroup (PSL(2, GaloisField 2 f))) := by rw [hSS]
      _ = (P' : Subgroup (oTwoQuot ↥L)).map e.toMonoidHom := rfl
  exact ⟨e, S, S', hScoe, hS'coe, hSne⟩

private theorem conjSub_ne_of_map_eq {L T T' : Subgroup G} {f : ℕ}
    {S S' : Sylow 2 (PSL(2, GaloisField 2 f))}
    {ψ : ↥L →* PSL(2, GaloisField 2 f)} {x : PSL(2, GaloisField 2 f)} {u : ↥L}
    (hScoe : (S : Subgroup (PSL(2, GaloisField 2 f))) = (T.subgroupOf L).map ψ)
    (hS'coe : (S' : Subgroup (PSL(2, GaloisField 2 f))) = (T'.subgroupOf L).map ψ)
    (himg : ((conjSub (u : G) T').subgroupOf L).map ψ =
      (S' : Subgroup (PSL(2, GaloisField 2 f))).map (MulAut.conj x).toMonoidHom)
    (hVS : x • S' ≠ S') (hWS : x • S' ≠ S) :
    conjSub (u : G) T' ≠ T' ∧ conjSub (u : G) T' ≠ T := by
  constructor
  · intro hEq
    have h' : (S' : Subgroup (PSL(2, GaloisField 2 f))).map
        (MulAut.conj x).toMonoidHom = S' := by
      rw [← himg, hEq, ← hS'coe]
    refine hVS (Sylow.ext ?_)
    rw [Sylow.coe_subgroup_smul, conj_smul_eq_map_conj]
    exact h'
  · intro hEq
    have h' : (S' : Subgroup (PSL(2, GaloisField 2 f))).map
        (MulAut.conj x).toMonoidHom = S := by
      rw [← himg, hEq, ← hScoe]
    refine hWS (Sylow.ext ?_)
    rw [Sylow.coe_subgroup_smul, conj_smul_eq_map_conj]
    exact h'

theorem exists_conj_eq_conj_ne_of_l2 {L T T' : Subgroup G} {f : ℕ} (hf : 1 ≤ f)
    (hL2 : IsL2Quot f (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L) (hT' : IsSylowTwoOf T' L)
    (hne : T ≠ T') :
    ∃ u ∈ T, ∃ h ∈ T', T'.map (MulAut.conj u).toMonoidHom =
        T.map (MulAut.conj h).toMonoidHom ∧
      T'.map (MulAut.conj u).toMonoidHom ≠ T ∧
      T'.map (MulAut.conj u).toMonoidHom ≠ T' := by
  obtain ⟨e, S, S', hScoe, hS'coe, hSne⟩ :=
    exists_sylow_image_data hL2 hT hT' hne
  let π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L)
  let ψ : ↥L →* PSL(2, GaloisField 2 f) := e.toMonoidHom.comp π
  obtain ⟨x, hxS, y, hyS', hx1, hy, hVS, hWS⟩ :=
    exists_smul_eq_of_sylow_ne hf hSne
  have hxS' : x ∈ (T.subgroupOf L).map ψ := by rwa [← hScoe]
  obtain ⟨tu, htu, hψu⟩ := Subgroup.mem_map.mp hxS'
  have huT : (tu : G) ∈ T := Subgroup.mem_subgroupOf.mp htu
  have hyS'' : y ∈ (T'.subgroupOf L).map ψ := by rwa [← hS'coe]
  obtain ⟨th, hth, hψh⟩ := Subgroup.mem_map.mp hyS''
  have hhT : (th : G) ∈ T' := Subgroup.mem_subgroupOf.mp hth
  have hVimg : ((conjSub (tu : G) T').subgroupOf L).map ψ =
      (S' : Subgroup (PSL(2, GaloisField 2 f))).map (MulAut.conj x).toMonoidHom := by
    rw [map_subgroupOf_conjSub_eq hT'.1 tu ψ, ← hS'coe, hψu]
  have hWimg : ((conjSub (th : G) T).subgroupOf L).map ψ =
      (S : Subgroup (PSL(2, GaloisField 2 f))).map
        (MulAut.conj y).toMonoidHom := by
    rw [map_subgroupOf_conjSub_eq hT.1 th ψ, ← hScoe, hψh]
  have hsmul : (S : Subgroup (PSL(2, GaloisField 2 f))).map
        (MulAut.conj y).toMonoidHom =
      (S' : Subgroup (PSL(2, GaloisField 2 f))).map (MulAut.conj x).toMonoidHom := by
    have h := congrArg
      (fun U : Sylow 2 (PSL(2, GaloisField 2 f)) =>
        (U : Subgroup (PSL(2, GaloisField 2 f)))) hy
    rw [Sylow.coe_subgroup_smul, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
      Subgroup.pointwise_smul_def] at h
    exact h
  have hEqψ : ((conjSub (tu : G) T').subgroupOf L).map ψ =
      ((conjSub (th : G) T).subgroupOf L).map ψ := by
    rw [hVimg, hWimg, hsmul]
  have hEqπ : ((conjSub (tu : G) T').subgroupOf L).map π =
      ((conjSub (th : G) T).subgroupOf L).map π := by
    apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
    rw [Subgroup.map_map, Subgroup.map_map]
    exact hEqψ
  have hA : IsSylowTwoOf (conjSub (tu : G) T') L := isSylowTwoOf_conjSub hT' tu
  have hB : IsSylowTwoOf (conjSub (th : G) T) L := isSylowTwoOf_conjSub hT th
  have hEq : conjSub (tu : G) T' = conjSub (th : G) T :=
    map_oTwoQuot_injective_of_isSylowTwoOf hA hB hEqπ
  obtain ⟨hVneT', hVneT⟩ := conjSub_ne_of_map_eq hScoe hS'coe hVimg hVS hWS
  refine ⟨(tu : G), huT, (th : G), hhT, hEq, hVneT, hVneT'⟩

theorem exists_conj_eq_conj_of_l2 {L T T' : Subgroup G} {f : ℕ} (hf : 1 ≤ f)
    (hL2 : IsL2Quot f (oTwoQuot ↥L)) (hT : IsSylowTwoOf T L) (hT' : IsSylowTwoOf T' L)
    (hne : T ≠ T') : ∃ u ∈ T, ∃ h ∈ T',
      T'.map (MulAut.conj u).toMonoidHom = T.map (MulAut.conj h).toMonoidHom := by
  obtain ⟨u, hu, h, hh, heq, -, -⟩ :=
    exists_conj_eq_conj_ne_of_l2 hf hL2 hT hT' hne
  exact ⟨u, hu, h, hh, heq⟩

end CFSG.Quasithin.Stroth.Rq

end
