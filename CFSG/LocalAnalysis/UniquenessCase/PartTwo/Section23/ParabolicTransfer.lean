module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs2
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

section Map

variable {X Y : Type} [Group X] [Group Y] [Finite X]

private theorem card_subgroupOf_map_conj {H : Subgroup X} (S : Sylow 2 X)
    (hSH : (S : Subgroup X) ≤ H) {x : X}
    (hx : x ∈ Subgroup.normalizer (H : Set X)) :
    Nat.card (((S : Subgroup X).map (MulAut.conj x).toMonoidHom).subgroupOf H) =
      2 ^ (Nat.card H).factorization 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAH : (S : Subgroup X).map (MulAut.conj x).toMonoidHom ≤ H := by
    rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hx s).mp (hSH hs)
  have h1 : Nat.card (((S : Subgroup X).map (MulAut.conj x).toMonoidHom).subgroupOf H) =
      Nat.card ((S : Subgroup X).map (MulAut.conj x).toMonoidHom) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAH).toEquiv
  rw [h1, Subgroup.card_map_of_injective (MulAut.conj x).injective]
  calc Nat.card (S : Subgroup X)
      = Nat.card (S.subtype hSH : Subgroup H) := by
        rw [Sylow.coe_subtype]
        exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSH).toEquiv).symm
    _ = 2 ^ (Nat.card H).factorization 2 := Sylow.card_eq_multiplicity (S.subtype hSH)

private theorem exists_mulAut_conj_map_eq_of_mem_normalizer {H : Subgroup X}
    (S : Sylow 2 X) (hSH : (S : Subgroup X) ≤ H) {x : X}
    (hx : x ∈ Subgroup.normalizer (H : Set X)) :
    ∃ h : X, h ∈ H ∧ (S : Subgroup X).map (MulAut.conj (h * x)).toMonoidHom = S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let A : Subgroup X := (S : Subgroup X).map (MulAut.conj x).toMonoidHom
  have hAH : A ≤ H := by
    rintro _ ⟨s, hs, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hx s).mp (hSH hs)
  let P₁ : Sylow 2 H := S.subtype hSH
  let Qsub : Subgroup H := A.subgroupOf H
  have hcard : Nat.card Qsub = 2 ^ (Nat.card H).factorization 2 :=
    card_subgroupOf_map_conj S hSH hx
  let Qsyl : Sylow 2 H := Sylow.ofCard Qsub hcard
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H Qsyl P₁
  have hh' : (A.subgroupOf H).map (MulAut.conj (h : H)).toMonoidHom =
      (S : Subgroup X).subgroupOf H := by
    have h := congrArg (fun R : Sylow 2 H => (R : Subgroup H)) hh
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, Sylow.coe_ofCard,
      Sylow.coe_subtype] at h
    exact h
  have hAS : A.map (MulAut.conj (h : X)).toMonoidHom = S := by
    have hmap := congrArg (Subgroup.map (Subgroup.subtype H)) hh'
    rw [Subgroup.map_map] at hmap
    rw [show (Subgroup.subtype H).comp (MulAut.conj (h : H)).toMonoidHom =
        (MulAut.conj (h : X)).toMonoidHom.comp (Subgroup.subtype H) from by
      ext z
      rfl,
      ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hAH,
      Subgroup.map_subgroupOf_eq_of_le hSH] at hmap
    exact hmap
  have hSconj : (S : Subgroup X).map (MulAut.conj ((h : X) * x)).toMonoidHom = S := by
    rw [show (MulAut.conj ((h : X) * x)).toMonoidHom =
        (MulAut.conj (h : X)).toMonoidHom.comp (MulAut.conj x).toMonoidHom from by
      ext z
      simp [MulAut.conj_apply, mul_assoc]]
    rw [← Subgroup.map_map]
    exact hAS
  exact ⟨(h : X), h.2, hSconj⟩

theorem normalizer_map_sylow_eq (f : X →* Y) (hf : Function.Surjective f)
    (S : Sylow 2 X) :
    Subgroup.normalizer (((S : Subgroup X).map f : Subgroup Y) : Set Y) =
      (Subgroup.normalizer (S : Set X)).map f := by
  refine le_antisymm ?_ (Subgroup.le_normalizer_map f)
  intro y hy
  obtain ⟨x, rfl⟩ := hf y
  let K : Subgroup X := f.ker
  let H : Subgroup X := (S : Subgroup X) ⊔ K
  have hH : H = ((S : Subgroup X).map f).comap f := by
    rw [Subgroup.comap_map_eq]
  have hSH : (S : Subgroup X) ≤ H := le_sup_left
  have hxH : x ∈ Subgroup.normalizer (H : Set X) := by
    rw [hH, ← Subgroup.comap_normalizer_eq_of_surjective
      (H := ((S : Subgroup X).map f)) hf]
    exact hy
  obtain ⟨h, hhH, hSconj⟩ := exists_mulAut_conj_map_eq_of_mem_normalizer S hSH hxH
  have hfhS : f h ∈ (S : Subgroup X).map f := by
    rw [hH] at hhH
    exact hhH
  have hfh : f h ∈ (Subgroup.normalizer (S : Set X)).map f :=
    Subgroup.map_mono Subgroup.le_normalizer hfhS
  have hfhx : f (h * x) ∈ (Subgroup.normalizer (S : Set X)).map f :=
    Subgroup.mem_map_of_mem f (Subgroup.mem_normalizer_iff_map_conj_eq.mpr hSconj)
  have hmem : f x = (f h)⁻¹ * f (h * x) := by
    rw [map_mul]
    group
  rw [hmem]
  exact Subgroup.mul_mem _ (((Subgroup.normalizer (S : Set X)).map f).inv_mem hfh) hfhx

theorem IsParabolicTwo.map {P : Subgroup X} (hP : IsParabolicTwo X P)
    (f : X →* Y) (hf : Function.Surjective f) : IsParabolicTwo Y (P.map f) := by
  obtain ⟨S, hN⟩ := hP
  refine ⟨S.mapSurjective (f := f) hf, ?_⟩
  change Subgroup.normalizer
      (((S.mapSurjective (f := f) hf : Sylow 2 Y) : Subgroup Y) : Set Y) ≤ P.map f
  rw [Sylow.coe_mapSurjective (f := f) hf S, normalizer_map_sylow_eq f hf S]
  exact Subgroup.map_mono hN

theorem IsParabolicTwo.comap (f : X →* Y) (hf : Function.Surjective f)
    {Q : Subgroup Y} (hQ : IsParabolicTwo Y Q) :
    IsParabolicTwo X (Q.comap f) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite Y := Finite.of_surjective f hf
  obtain ⟨S', hN⟩ := hQ
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective (f := f) hf 2 S'
  refine ⟨S, ?_⟩
  have hScoe : (S : Subgroup X).map f = (S' : Subgroup Y) := by
    rw [← Sylow.coe_mapSurjective (f := f) hf S]
    exact congrArg (fun T : Sylow 2 Y => (T : Subgroup Y)) hS
  intro x hx
  rw [Subgroup.mem_comap]
  apply hN
  change f x ∈ Subgroup.normalizer ((S' : Subgroup Y) : Set Y)
  have hfx : f x ∈ Subgroup.normalizer (((S : Subgroup X).map f) : Set Y) :=
    Subgroup.le_normalizer_map (H := (S : Subgroup X)) f
      (Subgroup.mem_map_of_mem f hx)
  rwa [hScoe] at hfx

theorem IsParabolicTwo.normalizer_le {P : Subgroup X} (hP : IsParabolicTwo X P)
    (S : Sylow 2 X) (hSP : (S : Subgroup X) ≤ P) :
    Subgroup.normalizer (S : Set X) ≤ P := by
  obtain ⟨S₀, hS₀N⟩ := hP
  have hS₀P : (S₀ : Subgroup X) ≤ P := Subgroup.le_normalizer.trans hS₀N
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S' : Sylow 2 P := S.subtype hSP
  let S₀' : Sylow 2 P := S₀.subtype hS₀P
  obtain ⟨p, hp⟩ := MulAction.exists_smul_eq P S₀' S'
  have hSmap : (S₀ : Subgroup X).map (MulAut.conj (p : X)).toMonoidHom = S := by
    have h := congrArg (fun R : Sylow 2 P => (R : Subgroup P)) hp
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
      MulDistribMulAction.toMonoidEnd_apply, Sylow.coe_subtype] at h
    change (S₀.subgroupOf P).map (MulAut.conj (p : P)).toMonoidHom =
      (S : Subgroup X).subgroupOf P at h
    have hmap := congrArg (Subgroup.map (Subgroup.subtype P)) h
    rw [Subgroup.map_map] at hmap
    rw [show (Subgroup.subtype P).comp (MulAut.conj (p : P)).toMonoidHom =
        (MulAut.conj (p : X)).toMonoidHom.comp (Subgroup.subtype P) from by
      ext z
      rfl,
      ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hS₀P,
      Subgroup.map_subgroupOf_eq_of_le hSP] at hmap
    exact hmap
  have hnorm : Subgroup.normalizer (S : Set X) =
      (Subgroup.normalizer (S₀ : Set X)).map (MulAut.conj (p : X)).toMonoidHom := by
    change Subgroup.normalizer ((S : Subgroup X) : Set X) =
      (Subgroup.normalizer (S₀ : Set X)).map (MulAut.conj (p : X)).toMonoidHom
    rw [← hSmap]
    exact (Subgroup.map_equiv_normalizer_eq S₀ (MulAut.conj (p : X))).symm
  rw [hnorm]
  rintro _ ⟨y, hy, rfl⟩
  simpa [MulAut.conj_apply] using
    P.mul_mem (P.mul_mem p.2 (hS₀N hy)) (P.inv_mem p.2)

theorem IsParabolicTwo.inf {P Q : Subgroup X} (hP : IsParabolicTwo X P)
    (hQ : IsParabolicTwo X Q) (S : Sylow 2 X) (hSP : (S : Subgroup X) ≤ P)
    (hSQ : (S : Subgroup X) ≤ Q) : IsParabolicTwo X (P ⊓ Q) :=
  ⟨S, le_inf (hP.normalizer_le S hSP) (hQ.normalizer_le S hSQ)⟩

theorem IsParabolicTwo.le_of_le_normalizer {P R : Subgroup X} (hP : IsParabolicTwo X P)
    (hR : IsPGroup 2 R) (hRN : R ≤ Subgroup.normalizer (P : Set X)) : R ≤ P := by
  obtain ⟨S, hN⟩ := hP
  have hSP : (S : Subgroup X) ≤ P := Subgroup.le_normalizer.trans hN
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := Subgroup.normalizer (P : Set X)
  have hSN : (S : Subgroup X) ≤ N := hSP.trans (Subgroup.le_normalizer)
  let S' : Sylow 2 N := S.subtype hSN
  have hR' : IsPGroup 2 (R.subgroupOf N) :=
    hR.of_equiv (Subgroup.subgroupOfEquivOfLe hRN).symm
  obtain ⟨T, hRT⟩ := hR'.exists_le_sylow
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N T S'
  have hn' : (T : Subgroup N).map (MulAut.conj (n : N)).toMonoidHom =
      (S : Subgroup X).subgroupOf N := by
    have h := congrArg (fun R : Sylow 2 N => (R : Subgroup N)) hn
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def,
      MulDistribMulAction.toMonoidEnd_apply, Sylow.coe_subtype] at h
    change (T : Subgroup N).map (MulAut.conj (n : N)).toMonoidHom =
      (S : Subgroup X).subgroupOf N at h
    exact h
  have hRle : R ≤ (S : Subgroup X).map (MulAut.conj ((n : X)⁻¹)).toMonoidHom := by
    intro r hr
    have hmem : (⟨r, hRN hr⟩ : N) ∈ (T : Subgroup N) :=
      hRT (Subgroup.mem_subgroupOf.mpr hr)
    have hmem' := hn' ▸ Subgroup.mem_map_of_mem (MulAut.conj (n : N)).toMonoidHom hmem
    have hSX : (n : X) * r * (n : X)⁻¹ ∈ (S : Subgroup X) := by
      simpa [MulAut.conj_apply] using Subgroup.mem_subgroupOf.mp hmem'
    refine Subgroup.mem_map.mpr ⟨(n : X) * r * (n : X)⁻¹, hSX, ?_⟩
    change (n : X)⁻¹ * ((n : X) * r * (n : X)⁻¹) * ((n : X)⁻¹)⁻¹ = r
    group
  have hleP : (S : Subgroup X).map (MulAut.conj ((n : X)⁻¹)).toMonoidHom ≤ P := by
    rintro _ ⟨s, hs, rfl⟩
    have hninN : (n : X)⁻¹ ∈ N := by
      simpa using N.inv_mem n.2
    simpa [MulAut.conj_apply] using
      (Subgroup.mem_normalizer_iff.mp hninN s).mp (hSP hs)
  exact fun r hr => hleP (hRle hr)

theorem IsParabolicTwo.center_le {P : Subgroup X} (hP : IsParabolicTwo X P) :
    Subgroup.center X ≤ P := by
  obtain ⟨S, hN⟩ := hP
  exact (Subgroup.center_le_normalizer (S : Set X)).trans hN

end Map

section ParabolicOf

variable {G : Type} [Group G] [Finite G]

theorem parabolicOf_iff {L P : Subgroup G} :
    ParabolicOf L P ↔ P ≤ L ∧ IsParabolicTwo ↥L (P.subgroupOf L) := by
  constructor
  · rintro ⟨hO, hPL, hpar⟩
    have hpc : CFSG.pCore 2 ↥L ≤ P.subgroupOf L := by
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr
        (hO (Subgroup.mem_map_of_mem (Subgroup.subtype L) hx))
    have hcomap : (((P.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) = P.subgroupOf L := by
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hpc]
    refine ⟨hPL, ?_⟩
    have h := IsParabolicTwo.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
      (QuotientGroup.mk'_surjective _) hpar
    rwa [hcomap] at h
  · rintro ⟨hPL, hpar⟩
    refine ⟨?_, hPL, ?_⟩
    · obtain ⟨S, hN⟩ := hpar
      have hpcS : CFSG.pCore 2 ↥L ≤ (S : Subgroup ↥L) :=
        CFSG.pCore_isPGroup.le_sylow_of_normal S
      intro x hx
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      exact Subgroup.mem_subgroupOf.mp (hN (Subgroup.le_normalizer (hpcS hy)))
    · exact IsParabolicTwo.map hpar (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
        (QuotientGroup.mk'_surjective _)

end ParabolicOf

section HinfMap

variable {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]

theorem Hinf_map (f : X →* Y) (H : Subgroup X) : (Hinf H).map f = Hinf (H.map f) := by
  unfold Hinf CFSG.inSubgroup
  have h := (CFSG.perfect_residual_transport (f.comp H.subtype)).1
  have hrange : (f.comp H.subtype).range = H.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange] at h
  rw [Subgroup.map_map, ← h]

end HinfMap

end CFSG.LocalAnalysis.UniquenessCase.UC22
