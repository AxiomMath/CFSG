module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07
import CFSG.GroupTheory.PCoreSurjective
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Nine24XU4Rank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC6U4Over
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem n924x_derInf_subgroupOf_map {L P X : Subgroup G} (hPL : P ≤ L)
    (hX : X = F07.DerInf P) :
    ((X.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) =
      F07.DerInf ((P.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) := by
  have h1 := CFSG.perfectResidual_subtype_subgroupOf P L hPL
  have hXsub : X.subgroupOf L =
      (CFSG.perfectResidual ↥(P.subgroupOf L)).map (P.subgroupOf L).subtype := by
    rw [← h1, hX]
    rfl
  rw [hXsub]
  exact SignalizerFunctorTheorem.Nonsolvable.map_perfectResidual_map
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) (P.subgroupOf L)

private theorem n924x_isL2_bar2_subgroupOf_map {L X : Subgroup G} {n : ℕ} (hXL : X ≤ L)
    (hL2 : IsL2 (Bar2 X) (2 * n)) :
    IsL2 (Bar2 ((X.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))) (2 * n) := by
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let Xb : Subgroup (Bar2 L) := (X.subgroupOf L).map π
  have hXb : IsL2 (Bar2 Xb) (2 * n) := by
    let g : ↥(X.subgroupOf L) →* ↥Xb :=
      (π.comp (X.subgroupOf L).subtype).codRestrict Xb
        (fun z => Subgroup.mem_map_of_mem π z.2)
    have hgsurj : Function.Surjective g := by
      intro y
      have hy : (y : Bar2 L) ∈ (X.subgroupOf L).map π := y.2
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨z, hz⟩, Subtype.ext hzy⟩
    have hgker : g.ker = (CFSG.pCore 2 ↥L).comap (X.subgroupOf L).subtype := by
      ext z
      rw [MonoidHom.mem_ker, Subgroup.mem_comap]
      constructor
      · intro hz
        have h1 : π (z : ↥L) = 1 := congrArg Subtype.val hz
        exact (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥L) (z : ↥L)).mp h1
      · intro hz
        apply Subtype.ext
        have h2 : (z : ↥L) ∈ π.ker := by
          rw [show π.ker = CFSG.pCore 2 ↥L from QuotientGroup.ker_mk' _]
          exact hz
        exact (MonoidHom.mem_ker).1 h2
    have hg2 : IsPGroup 2 g.ker := by
      rw [hgker]
      exact IsPGroup.comap_of_injective (CFSG.pCore_isPGroup (p := 2)) _
        (Subgroup.subtype_injective _)
    let eX : ↥(X.subgroupOf L) ≃* ↥X := Subgroup.subgroupOfEquivOfLe hXL
    let f : ↥X →* ↥Xb := g.comp eX.symm.toMonoidHom
    have hfsurj : Function.Surjective f := hgsurj.comp eX.symm.surjective
    have hf2 : IsPGroup 2 f.ker := by
      have hker : f.ker = g.ker.comap eX.symm.toMonoidHom := by
        ext x
        rw [Subgroup.mem_comap, MonoidHom.mem_ker]
        rfl
      rw [hker]
      exact IsPGroup.comap_of_injective hg2 _ eX.symm.injective
    obtain ⟨eBar⟩ :=
      CFSG.nonempty_quotient_pCore_equiv_of_surjective_of_isPGroup_ker f hfsurj hf2
    exact CFSG.Blueprint.LieModel.of_mulEquiv eBar hL2
  exact hXb

theorem le_parabolic_of_pRank_le_one {L P X J : Subgroup G} {n : ℕ} (hn : 1 < n)
    (hU : IsU4 (Bar2 L) n) (hP : ParabolicOf L P) (hX : X = F07.DerInf P)
    (hL2 : IsL2 (Bar2 X) (2 * n)) (hXJ : X ≤ J) (hJL : J ≤ L)
    (h3 : CFSG.Open.pRank 3 J ≤ 1) : J ≤ P := by
  have hPL : P ≤ L := hP.2.1
  have hXL : X ≤ L := hX ▸ (Subgroup.map_subtype_le _).trans hPL
  let π : ↥L →* Bar2 L := QuotientGroup.mk' (CFSG.pCore 2 ↥L)
  let Pb : Subgroup (Bar2 L) := (P.subgroupOf L).map π
  let Xb : Subgroup (Bar2 L) := (X.subgroupOf L).map π
  let Jb : Subgroup (Bar2 L) := (J.subgroupOf L).map π
  have hPb : IsParabolicTwo (Bar2 L) Pb := hP.2.2
  have hXb_eq : Xb = F07.DerInf Pb := n924x_derInf_subgroupOf_map hPL hX
  have hL2b : IsL2 (Bar2 Xb) (2 * n) := n924x_isL2_bar2_subgroupOf_map hXL hL2
  have hXbJb : Xb ≤ Jb := by
    intro y hy
    obtain ⟨x, hx, hxy⟩ := Subgroup.mem_map.mp hy
    rw [← hxy]
    exact Subgroup.mem_map_of_mem π
      (Subgroup.mem_subgroupOf.mpr (hXJ (Subgroup.mem_subgroupOf.mp hx)))
  rcases s16c6_u4_overgroup hn hU hPb hXb_eq hL2b hXbJb with htop | hle
  · exfalso
    have hker3 : ¬ 3 ∣ Nat.card π.ker := by
      rw [show π.ker = CFSG.pCore 2 ↥L from QuotientGroup.ker_mk' _]
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
      rw [hk]
      intro h
      exact absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num)
    have hle1 : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) ≤
        CFSG.Open.pRank 3 (⊤ : Subgroup ↥(J.subgroupOf L)) := by
      have h := CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd Nat.prime_three π hker3
        (J.subgroupOf L)
      have hJb : Jb = (J.subgroupOf L).map π := rfl
      rw [← hJb, htop, CFSG.SectionRank.pRank_eq_pRank_top_subgroup (J.subgroupOf L)] at h
      exact h
    have hle2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(J.subgroupOf L)) ≤ CFSG.Open.pRank 3 J := by
      rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup J,
        ← CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥(J.subgroupOf L),
        ← CFSG.SectionRank.pRank_eq_open_pRank_top 3 ↥J]
      exact le_of_eq (CFSG.pRank_congr_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJL) 3)
    have h2 := two_le_pRank_three_of_isU4 (show 2 ≤ n by omega) hU
    omega
  · intro j hj
    have hjL : j ∈ L := hJL hj
    have hjJb : π ⟨j, hjL⟩ ∈ Jb := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hj)
    have hjPb : π ⟨j, hjL⟩ ∈ Pb := hle hjJb
    obtain ⟨p, hpP, hpeq⟩ := Subgroup.mem_map.mp hjPb
    have hpPG : (p : G) ∈ P := Subgroup.mem_subgroupOf.mp hpP
    have hmem : (⟨j, hjL⟩ * p⁻¹ : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [← QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥L)]
      change π (⟨j, hjL⟩ * p⁻¹) = 1
      simp only [map_mul, map_inv, hpeq, mul_inv_cancel]
    have hmemG : j * (p : G)⁻¹ ∈ pCoreOf 2 L := by
      change ((⟨j, hjL⟩ * p⁻¹ : ↥L) : G) ∈ pCoreOf 2 L
      exact Subgroup.mem_map_of_mem L.subtype hmem
    have hcoreP : j * (p : G)⁻¹ ∈ P := hP.1 hmemG
    have hjeq : j = (j * (p : G)⁻¹) * (p : G) := by group
    rw [hjeq]
    exact P.mul_mem hcoreP hpPG

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
