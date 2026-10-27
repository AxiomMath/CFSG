module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOmega
import CFSG.LocalAnalysis.StandardType.GGCommutatorSupElemAbelian
import CFSG.LocalAnalysis.RankThreeEvenClassification.NormalSylowIntersection
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPreimages
import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion

public section

namespace CFSG.StandardType

open CFSG.Assembly Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

private theorem mem_centralizer_of_mem_sup_of_noTransvection {E C : Subgroup G}
    (hE : IsElemAbelian p E) (hNT : GGNoTransvection p E)
    (hEC : E ≤ normalizer (C : Set G)) (hcard : Nat.card (E ⊓ C : Subgroup G) ≤ p)
    {u : G} (hu : u ∈ E ⊔ C) (huE : u ∈ normalizer (E : Set G))
    {k : ℕ} (huk : u ^ p ^ k = 1) : u ∈ centralizer (E : Set G) := by
  classical
  have hp : p.Prime := Fact.out
  have hcomm : ∀ a b : E, a * b = b * a := fun a b => hE.1.is_comm.comm a b
  let f : E →* E :=
    { toFun := fun b => b⁻¹ * ggConjAut E huE b
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [map_mul, mul_inv_rev]
        calc b⁻¹ * a⁻¹ * (ggConjAut E huE a * ggConjAut E huE b)
            = b⁻¹ * (a⁻¹ * ggConjAut E huE a) * ggConjAut E huE b := by group
          _ = (a⁻¹ * ggConjAut E huE a) * b⁻¹ * ggConjAut E huE b := by rw [hcomm b⁻¹]
          _ = a⁻¹ * ggConjAut E huE a * (b⁻¹ * ggConjAut E huE b) := by group }
  have hfC : ∀ b : E, (f b : G) ∈ C := by
    intro b
    have hFcomm := commutator_sup_le_of_isElemAbelian hE hEC
    let a : ↥(E ⊔ C) := ⟨(b : G)⁻¹, inv_mem (mem_sup_left b.2)⟩
    let v : ↥(E ⊔ C) := ⟨u, hu⟩
    have hmem : ⁅a, v⁆ ∈ C.subgroupOf (E ⊔ C) :=
      hFcomm (Subgroup.commutator_mem_commutator (mem_top a) (mem_top v))
    change ((⁅a, v⁆ : ↥(E ⊔ C)) : G) ∈ C at hmem
    simpa [a, v, f, commutatorElement_def, ggConjAut_apply, mul_assoc] using hmem
  have hfle : f.range.map E.subtype ≤ E ⊓ C := by
    rintro _ ⟨z, ⟨b, rfl⟩, rfl⟩
    exact ⟨(f b).2, hfC b⟩
  have hfr : Nat.card f.range ≤ p := by
    have h := Subgroup.card_le_of_le hfle
    rw [Subgroup.card_map_of_injective E.subtype_injective] at h
    exact h.trans hcard
  let B : Subgroup G := f.ker.map E.subtype
  have hBE : B ≤ E := Subgroup.map_subtype_le _
  have hEB : Nat.card E ≤ p * Nat.card B := by
    have h := Subgroup.card_ker_mul_card_range f
    have hle := Nat.mul_le_mul_left (Nat.card f.ker) hfr
    rw [h, ← Subgroup.card_map_of_injective E.subtype_injective] at hle
    simpa [B, mul_comm] using hle
  have huB : u ∈ centralizer (B : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have hb1 : f b = 1 := MonoidHom.mem_ker.mp hb
    change b⁻¹ * ggConjAut E huE b = 1 at hb1
    have hbfix : ggConjAut E huE b = b := (inv_mul_eq_one.mp hb1).symm
    have hbfix' := congrArg Subtype.val hbfix
    rw [ggConjAut_apply] at hbfix'
    calc (b : G) * u = (u * b * u⁻¹) * u := by rw [hbfix']
      _ = u * b := by group
  rcases mem_centralizer_or_ggIsTransvection hp hBE hE hEB huE huB huk with h | h
  · exact h
  · exact (hNT _ (ggConjAut_mem_ggInduced (mem_top u) huE) h).elim

private theorem le_centralizer_of_mem_sup_of_noTransvection {E C S : Subgroup G}
    (hE : IsElemAbelian p E)
    (hSC : ∀ g ∈ centralizer (E : Set G), g ^ p = 1 → g ∈ E)
    (hNT : GGNoTransvection p E) (hEC : E ≤ normalizer (C : Set G))
    (hcard : Nat.card (E ⊓ C : Subgroup G) ≤ p)
    (hS : IsPGroup p S) (hES : E ≤ S) (hSF : S ≤ E ⊔ C) :
    S ≤ centralizer (E : Set G) := by
  have hN : ∀ u ∈ S, u ∈ normalizer (E : Set G) → u ∈ centralizer (E : Set G) := by
    intro u hu huE
    obtain ⟨k, hk⟩ := hS ⟨u, hu⟩
    exact mem_centralizer_of_mem_sup_of_noTransvection hE hNT hEC hcard (hSF hu) huE
      (show u ^ p ^ k = 1 from congrArg Subtype.val hk)
  have hEQ : E ≤ S ⊓ centralizer (E : Set G) := by
    refine le_inf hES ?_
    intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact congrArg Subtype.val (hE.1.is_comm.comm (⟨x, hx⟩ : E) ⟨e, he⟩)
  have hQ : S ⊓ centralizer (E : Set G) = S := by
    by_contra hne
    obtain ⟨v, hvS, hvN, hvQ⟩ :=
      exists_mem_normalizer_not_mem hS (lt_of_le_of_ne inf_le_left hne)
    apply hvQ
    refine ⟨hvS, hN v hvS ?_⟩
    have hle : E.map (MulAut.conj v).toMonoidHom ≤ E := by
      rintro _ ⟨e, he, rfl⟩
      have hconj : v * e * v⁻¹ ∈ S ⊓ centralizer (E : Set G) :=
        (Subgroup.mem_normalizer_iff.mp hvN e).mp (hEQ he)
      refine hSC _ hconj.2 ?_
      change (v * e * v⁻¹) ^ p = 1
      rw [conj_pow, hE.2 e he, mul_one, mul_inv_cancel]
    exact mem_normalizer_iff_map_conj.mpr (Subgroup.eq_of_le_of_card_ge hle
      (Subgroup.card_map_of_injective (MulAut.conj v).injective).ge)
  exact fun s hs => (hQ ▸ hs).2

private theorem isCyclic_of_le_centralizer_of_card_inf_le (hp2 : p ≠ 2)
    {E C S : Subgroup G}
    (hSC : ∀ g ∈ centralizer (E : Set G), g ^ p = 1 → g ∈ E)
    (hcard : Nat.card (E ⊓ C : Subgroup G) ≤ p) (hS : IsPGroup p S)
    (hSC' : S ≤ centralizer (E : Set G)) (hSC'' : S ≤ C) : IsCyclic S := by
  classical
  have hp : p.Prime := Fact.out
  by_cases hS0 : S = ⊥
  · subst S
    infer_instance
  have hdiv : p ∣ Nat.card S := hS.card_eq_or_dvd.resolve_left fun h =>
    hS0 (Subgroup.card_eq_one.mp h)
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := S) p hdiv
  have hall : ∀ U : Subgroup S, Nat.card U = p → U.map S.subtype ≤ E ⊓ C := by
    intro U hU
    rintro _ ⟨u, hu, rfl⟩
    refine ⟨hSC _ (hSC' u.2) ?_, hSC'' u.2⟩
    have hord : orderOf u ∣ p := hU ▸ U.orderOf_dvd_natCard hu
    exact congrArg Subtype.val (orderOf_dvd_iff_pow_eq_one.mp hord)
  let U : Subgroup S := zpowers a
  have hUcard : Nat.card U = p := by
    change Nat.card (zpowers a) = p
    rw [Nat.card_zpowers, ha]
  have hunique : ∀ V : Subgroup S, Nat.card V = p → V = U := by
    intro V hV
    have hcard' : Nat.card (E ⊓ C : Subgroup G) = p := by
      have h := Subgroup.card_le_of_le (hall U hUcard)
      rw [Subgroup.card_map_of_injective S.subtype_injective, hUcard] at h
      exact le_antisymm hcard h
    have heq : V.map S.subtype = E ⊓ C := Subgroup.eq_of_le_of_card_ge (hall V hV) (by
      rw [Subgroup.card_map_of_injective S.subtype_injective, hV, hcard'])
    have heq' : U.map S.subtype = E ⊓ C := Subgroup.eq_of_le_of_card_ge (hall U hUcard) (by
      rw [Subgroup.card_map_of_injective S.subtype_injective, hUcard, hcard'])
    exact Subgroup.map_injective S.subtype_injective (heq.trans heq'.symm)
  exact (CFSG.BenderSuzuki.External.huppert_III_8_2_pgroup_unique_order_prime_subgroup
    hp hS ⟨U, hUcard, hunique⟩).1 hp2

theorem ggSCNoTV_isCyclic (hp2 : p ≠ 2) {E C : Subgroup G} (hE : IsElemAbelian p E)
    (hSC : ∀ g ∈ Subgroup.centralizer (E : Set G), g ^ p = 1 → g ∈ E)
    (hNT : GGNoTransvection p E) (hEC : E ≤ Subgroup.normalizer (C : Set G))
    (hcard : Nat.card (E ⊓ C : Subgroup G) ≤ p) {P : Subgroup G} (hPC : P ≤ C)
    (hP : IsPGroup p P) : IsCyclic P := by
  classical
  have hp : p.Prime := Fact.out
  let F : Subgroup G := E ⊔ C
  have hCF : C ≤ F := le_sup_right
  have hCn : (C.subgroupOf F).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCF]
    exact sup_le hEC Subgroup.le_normalizer
  have hEp : IsPGroup p (E.subgroupOf F) := by
    intro e
    refine ⟨1, Subtype.ext ?_⟩
    exact Subtype.ext (by simpa using hE.2 e (Subgroup.mem_subgroupOf.mp e.2))
  obtain ⟨T, hET⟩ := hEp.exists_le_sylow
  let S : Subgroup G := (T : Subgroup F).map F.subtype
  have hES : E ≤ S := fun e he => ⟨⟨e, mem_sup_left he⟩, hET he, rfl⟩
  have hSF : S ≤ E ⊔ C := Subgroup.map_subtype_le _
  have hS : IsPGroup p S := T.isPGroup'.map F.subtype
  have hSE : S ≤ centralizer (E : Set G) :=
    le_centralizer_of_mem_sup_of_noTransvection hE hSC hNT hEC hcard hS hES hSF
  have hSCcyc : IsCyclic (S ⊓ C : Subgroup G) :=
    isCyclic_of_le_centralizer_of_card_inf_le hp2 hSC hcard
      (hS.to_le inf_le_left) (inf_le_left.trans hSE) inf_le_right
  have : (C.subgroupOf F).Normal := hCn
  let R : Sylow p (C.subgroupOf F) :=
    CFSG.RankThreeEvenClassification.Helpers.sylowNormalIntersection p hp T (C.subgroupOf F)
  let eC : C.subgroupOf F ≃* C := Subgroup.subgroupOfEquivOfLe hCF
  have heCs : Function.Surjective eC.toMonoidHom := by
    intro c
    obtain ⟨b, hb⟩ := eC.surjective c
    exact ⟨b, hb⟩
  let RC : Sylow p C := R.mapSurjective heCs
  have hRmap : (RC : Subgroup C).map C.subtype = S ⊓ C := by
    dsimp only [RC, R]
    rw [Sylow.coe_mapSurjective,
      CFSG.RankThreeEvenClassification.Helpers.sylowNormalIntersection_coe,
      Subgroup.map_map]
    have heC : C.subtype.comp eC.toMonoidHom = F.subtype.comp (C.subgroupOf F).subtype := by
      ext x
      rfl
    rw [heC]
    rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype,
      Subgroup.map_inf _ _ F.subtype F.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hCF]
  have hRCcyc : IsCyclic (RC : Subgroup C) := by
    have h := (Subgroup.equivMapOfInjective (RC : Subgroup C) C.subtype C.subtype_injective).isCyclic
    rw [hRmap] at h
    exact h.mpr hSCcyc
  have hP' : IsPGroup p (P.subgroupOf C) := hP.comap_subtype
  obtain ⟨PC, hPPC⟩ := hP'.exists_le_sylow
  have hPCcyc : IsCyclic (PC : Subgroup C) := (Sylow.equiv RC PC).isCyclic.mp hRCcyc
  have : IsCyclic (PC : Subgroup C) := hPCcyc
  have hPcyc : IsCyclic (P.subgroupOf C) := Subgroup.isCyclic_of_le hPPC
  exact (Subgroup.subgroupOfEquivOfLe hPC).isCyclic.mp hPcyc

end CFSG.StandardType

end
