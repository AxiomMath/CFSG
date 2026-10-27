module

public import CFSG.RankThree.PartTwo.KFacts.KS116
public import CFSG.RankThree.PartOne.S9.OddCore.RecognitionLifting
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item116PRank

open CFSG

theorem isElemAbelian_map_hom {H K : Type*} [Group H] [Group K] {p : ℕ} (f : H →* K)
    {E : Subgroup H} (hE : CFSG.Assembly.IsElemAbelian p E) :
    CFSG.Assembly.IsElemAbelian p (E.map f) := by
  exact CFSG.Open.IsElemAbelian.map hE f

theorem exists_pSubgroup_le_normalizer_sylow {X : Type*} [Group X] [Finite X] {N : Subgroup X}
    [N.Normal] {q p : ℕ} [Fact q.Prime] [Fact p.Prime] (S : Sylow q N)
    (Pbar : Subgroup (X ⧸ N)) (hP : IsPGroup p Pbar) :
    ∃ P : Subgroup X, IsPGroup p P ∧
      P ≤ Subgroup.normalizer (((S : Subgroup N).map N.subtype : Subgroup X) : Set X) ∧
      P.map (QuotientGroup.mk' N) = Pbar := by
  classical
  set T : Subgroup X := (S : Subgroup N).map N.subtype with hT
  set π : X →* X ⧸ N := QuotientGroup.mk' N with hπ
  have hfr : Subgroup.normalizer (T : Set X) ⊔ N = ⊤ := Sylow.normalizer_sup_eq_top S
  set M : Subgroup X := Subgroup.normalizer (T : Set X) ⊓ Pbar.comap π with hM
  have hMmap : M.map π = Pbar := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr inf_le_right) ?_
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hx : x ∈ (Subgroup.normalizer (T : Set X) ⊔ N : Subgroup X) := hfr ▸ Subgroup.mem_top x
    rw [← SetLike.mem_coe, Subgroup.mul_normal] at hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
    have hπb : π b = 1 := (QuotientGroup.eq_one_iff b).mpr hb
    have hπab : π (a * b) = π a := by rw [map_mul, hπb, mul_one]
    refine ⟨a, ⟨ha, ?_⟩, hπab.symm⟩
    show π a ∈ Pbar
    rw [← hπab]
    exact hy
  have hmem : ∀ m : M, (π.comp M.subtype) m ∈ Pbar := fun m => m.2.2
  let f : M →* Pbar := (π.comp M.subtype).codRestrict Pbar hmem
  have hf : Function.Surjective f := by
    rintro ⟨y, hy⟩
    rw [← hMmap] at hy
    obtain ⟨m, hm, rfl⟩ := hy
    exact ⟨⟨m, hm⟩, rfl⟩
  obtain ⟨Q⟩ : Nonempty (Sylow p M) := inferInstance
  have hQ : ((Q.mapSurjective hf : Sylow p Pbar) : Subgroup Pbar) = ⊤ :=
    ((Q.mapSurjective hf).is_maximal' (hP.to_subgroup ⊤) le_top).symm
  rw [Sylow.coe_mapSurjective] at hQ
  refine ⟨(Q : Subgroup M).map M.subtype, Q.isPGroup'.map _, ?_, ?_⟩
  · exact (Subgroup.map_subtype_le _).trans inf_le_left
  · have hcomp : π.comp M.subtype = Pbar.subtype.comp f := MonoidHom.ext fun _ => rfl
    rw [Subgroup.map_map, hcomp, ← Subgroup.map_map, hQ, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]

theorem exists_three_generators_of_even_normal (hB : KFacts.BlackburnRankTwo)
    {G : Type} [Group G] [Finite G] {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p)
    (hloc : CFSG.Assembly.RankThreeEven.localRank p G < 3) (C : Subgroup G) (N : Subgroup C)
    [N.Normal] (hev : Even (Nat.card N)) (Pbar : Subgroup (C ⧸ N)) (hP : IsPGroup p Pbar) :
    ∃ s : Finset Pbar, s.card ≤ 3 ∧ Subgroup.closure (s : Set Pbar) = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ : Nonempty (Sylow 2 N) := inferInstance
  obtain ⟨P, hPp, hPS, hPmap⟩ := exists_pSubgroup_le_normalizer_sylow S Pbar hP
  set T : Subgroup G := ((S : Subgroup N).map N.subtype).map C.subtype with hT
  have hT0 : T ≠ ⊥ := by
    have hS0 : (S : Subgroup N) ≠ ⊥ := S.ne_bot_of_dvd_card (even_iff_two_dvd.mp hev)
    intro h
    apply hS0
    rw [hT, Subgroup.map_map] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _
      (show Function.Injective (C.subtype.comp N.subtype) from
        C.subtype_injective.comp N.subtype_injective)).mp h
  have hT2 : IsPGroup 2 T := (S.isPGroup'.map _).map _
  set D : Subgroup G := P.map C.subtype with hD
  have hDT : D ≤ Subgroup.normalizer (T : Set G) :=
    (Subgroup.map_mono hPS).trans (Subgroup.le_normalizer_map C.subtype)
  have hrank : CFSG.pRank p ↥D ≤ CFSG.Assembly.RankThreeEven.localRank p G :=
    CFSG.RankThree.PartOne.OddCore37.pRank_le_localRank_of_le_normalizer hp.out hT0 hT2 hDT
  have hE : ∀ E : Subgroup P, CFSG.Assembly.IsElemAbelian p E → Nat.card E ≤ p ^ 2 := by
    intro E hE
    set E' : Subgroup G := (E.map P.subtype).map C.subtype with hE'def
    have hE'D : E' ≤ D := Subgroup.map_mono (Subgroup.map_subtype_le E)
    have hcard : Nat.card E' = Nat.card E := by
      rw [hE'def, Subgroup.card_map_of_injective C.subtype_injective,
        Subgroup.card_map_of_injective P.subtype_injective]
    have hE' : CFSG.Assembly.IsElemAbelian p E' :=
      isElemAbelian_map_hom _ (isElemAbelian_map_hom _ hE)
    obtain ⟨k, hk⟩ := (show IsPGroup p E' from fun x =>
      ⟨1, by rw [pow_one]; exact Subtype.ext (hE'.2 x x.2)⟩).exists_card_eq
    have hk2 : k ≤ 2 := by
      have h1 := CFSG.SectionRank.le_pRank hp.out.one_lt hE'D hE' hk
      have h2 := CFSG.RankThree.PartOne.assembly_pRank_eq hp.out D
      have h3 : CFSG.Assembly.pRank p D = CFSG.Open.pRank p D := rfl
      omega
    rw [← hcard, hk]
    exact Nat.pow_le_pow_right hp.out.pos hk2
  obtain ⟨⟨s, hs3, hs⟩, -⟩ := hB p hp5 P hPp hE
  have hmem : ∀ x : P, ((QuotientGroup.mk' N).comp P.subtype) x ∈ Pbar := fun x => by
    rw [← hPmap]
    exact ⟨x, x.2, rfl⟩
  let g : P →* Pbar := ((QuotientGroup.mk' N).comp P.subtype).codRestrict Pbar hmem
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    rw [← hPmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  refine ⟨s.image g, Finset.card_image_le.trans hs3, ?_⟩
  rw [Finset.coe_image, ← MonoidHom.map_closure, hs, ← MonoidHom.range_eq_map,
    MonoidHom.range_eq_top.mpr hg]

end CFSG.RankThree.PartTwo.Sec11.Item116PRank
