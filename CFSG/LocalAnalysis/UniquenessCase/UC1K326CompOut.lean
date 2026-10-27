module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326CompDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G] {n : ℕ} {P : Subgroup G}

noncomputable def compOutHom (L : Subgroup G) [L.Normal] : G →* Outer ↥L :=
  (QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L)).comp
    (MulAut.conjNormal (H := L))

theorem compOutHom_ker_le_sup (L : Subgroup G) [hLn : L.Normal] :
    (compOutHom L).ker ≤ L ⊔ Subgroup.centralizer (L : Set G) := by
  intro g hg
  have hg1 : compOutHom L g = 1 := MonoidHom.mem_ker.mp hg
  have hmem : MulAut.conjNormal (H := L) g ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L := by
    rw [← QuotientGroup.eq_one_iff (N := CFSG.ComponentClassification.OuterAutomorphisms.inner ↥L)]
    simpa only [compOutHom, MonoidHom.comp_apply, QuotientGroup.mk'_apply] using hg1
  have hmem' : MulAut.conjNormal (H := L) g ∈ (MulAut.conj : ↥L →* MulAut ↥L).range := by
    simpa only [CFSG.ComponentClassification.OuterAutomorphisms.inner] using hmem
  obtain ⟨l, hl⟩ := MonoidHom.mem_range.mp hmem'
  have hval : MulAut.conjNormal (H := L) (l : G) = MulAut.conjNormal (H := L) g := by
    rw [MulAut.conjNormal_val (h := l)]
    exact hl
  have hone : MulAut.conjNormal (H := L) (g * (l : G)⁻¹) = 1 := by
    rw [map_mul, map_inv, hval, mul_inv_cancel]
  have hcent : g * (l : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxmem := congrArg (fun f : MulAut ↥L => (f ⟨x, hx⟩ : ↥L)) hone
    simp only [MulAut.one_apply] at hxmem
    have hc : (g * (l : G)⁻¹) * x * (g * (l : G)⁻¹)⁻¹ = x := by
      have h := congrArg (fun y : ↥L => (y : G)) hxmem
      simpa only [MulAut.conjNormal_apply, Subtype.coe_mk] using h
    calc x * (g * (l : G)⁻¹)
        = ((g * (l : G)⁻¹) * x * (g * (l : G)⁻¹)⁻¹) * (g * (l : G)⁻¹) := by
          rw [hc]
      _ = (g * (l : G)⁻¹) * x := by group
  rw [Subgroup.mem_sup_of_normal_left]
  refine ⟨(g * (l : G)⁻¹) * (l : G) * (g * (l : G)⁻¹)⁻¹, ?_,
    g * (l : G)⁻¹, hcent, ?_⟩
  · exact hLn.conj_mem (l : G) l.2 (g * (l : G)⁻¹)
  · group

theorem compOutHom_ker_le {L : Subgroup G} [L.Normal] {M : Subgroup G} (hLM : L ≤ M)
    (hCM : Subgroup.centralizer (L : Set G) ≤ M) : (compOutHom L).ker ≤ M :=
  (compOutHom_ker_le_sup L).trans (sup_le hLM hCM)

theorem compOutHom_map_le_sylow {L : Subgroup G} [L.Normal] {S : Subgroup (Outer ↥L)}
    (hSN : S.Normal) (hSp : IsPGroup 3 S) (hSidx : ¬ 3 ∣ S.index)
    (hψP : IsPGroup 3 (P.map (compOutHom L))) : P.map (compOutHom L) ≤ S := by
  haveI : Subgroup.Normal (hSp.toSylow hSidx : Subgroup (Outer ↥L)) := hSN
  refine (hψP.sylow_mem_fixedPoints_iff (Q := hSp.toSylow hSidx)).mp ?_
  rw [MulAction.mem_fixedPoints]
  intro m
  exact Sylow.smul_eq_of_normal

theorem comap_le_sup_ker_of_normal_sylow {H : Type} [Group H] (f : G →* H) {S : Subgroup H}
    (hSN : S.Normal) (hSp : IsPGroup 3 S) (hSidx : ¬ 3 ∣ S.index) {P : Subgroup G}
    (hP : IsSylowOf 3 P ⊤) : S.comap f ≤ P ⊔ f.ker := by
  haveI : S.Normal := hSN
  intro g hg
  have hPcard : Nat.card P = 3 ^ (Nat.card G).factorization 3 := by
    simpa [Subgroup.card_top] using hP.card_eq
  let QP : Sylow 3 G := Sylow.ofCard P hPcard
  let Q' : Sylow 3 f.range := QP.mapSurjective f.rangeRestrict_surjective
  have hQ'coe : (Q' : Subgroup f.range) = P.map f.rangeRestrict := by
    simp [Q', QP]
  have hSsub : S.subgroupOf f.range ≤ (Q' : Subgroup f.range) :=
    IsPGroup.le_sylow_of_normal (p := 3) (hSp.comap_subtype (K := f.range)) Q'
  have hmem : f.rangeRestrict g ∈ (Q' : Subgroup f.range) :=
    hSsub (by rw [Subgroup.mem_subgroupOf]; exact hg)
  rw [hQ'coe] at hmem
  obtain ⟨p, hp, hpg⟩ := Subgroup.mem_map.mp hmem
  have hker : p⁻¹ * g ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    have hval := congrArg (fun x : f.range => (x : H)) hpg
    simp only [MonoidHom.coe_rangeRestrict] at hval
    rw [map_mul, map_inv, hval, inv_mul_cancel]
  rw [Subgroup.mem_sup_of_normal_right]
  exact ⟨p, hp, p⁻¹ * g, hker, by group⟩

theorem comp_top_of_le (hO : SL3Out) (h : Hyp326 G n P) {L : Subgroup G} (hLn : L.Normal)
    (hS : IsSL3pi ↥L) {M : Subgroup G} (hPM : P ≤ M) (hLM : L ≤ M)
    (hCM : Subgroup.centralizer (L : Set G) ≤ M)
    (hNM : Subgroup.normalizer (P : Set G) ≤ M) : M = ⊤ := by
  haveI : L.Normal := hLn
  obtain ⟨S, hSN, hSp, hSidx⟩ := hO ↥L hS
  haveI : S.Normal := hSN
  have hPS : P.map (compOutHom L) ≤ S :=
    compOutHom_map_le_sylow hSN hSp hSidx (h.sylow.isPGroup.map (compOutHom L))
  have hPN : P ≤ S.comap (compOutHom L) := Subgroup.map_le_iff_le_comap.mp hPS
  have hNleM : S.comap (compOutHom L) ≤ M :=
    (comap_le_sup_ker_of_normal_sylow (compOutHom L) hSN hSp hSidx h.sylow).trans
      (sup_le hPM (compOutHom_ker_le hLM hCM))
  have hPcard : Nat.card P = 3 ^ (Nat.card G).factorization 3 := by
    simpa [Subgroup.card_top] using h.sylow.card_eq
  let QP : Sylow 3 G := Sylow.ofCard P hPcard
  have hPN' : (QP : Subgroup G) ≤ S.comap (compOutHom L) := hPN
  haveI : Finite (Sylow 3 (S.comap (compOutHom L))) :=
    Sylow.finite_of_finiteIndex (default : Sylow 3 (S.comap (compOutHom L)))
  have hfrattini : Subgroup.normalizer (QP : Subgroup G) ⊔ S.comap (compOutHom L) = ⊤ :=
    Sylow.normalizer_sup_eq_top' QP hPN'
  have hNQM : Subgroup.normalizer (QP : Subgroup G) ≤ M := by
    simpa only [QP, Sylow.coe_ofCard] using hNM
  refine eq_top_iff.mpr ?_
  rw [← hfrattini]
  exact sup_le hNQM hNleM

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
