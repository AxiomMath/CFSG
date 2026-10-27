module

public import CFSG.RankThree.PartTwo.Sec13.F135LastR1Lin
public import CFSG.RankThree.PartTwo.Sec13.F135LastR1Z
public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofA7Z3
public import CFSG.GroupTheory.ABGDGroups.LinearEmbedding
public import CFSG.RankThree.PartTwo.Sec13.Item13Res7ProofOneTwoLinAlg

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartTwo.Sec13.Res7Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
open CritProof
open scoped commutatorElement IsMulCommutative

theorem r1_L_le_normalizer {G : Type} [Group G] [Finite G] {L : Subgroup G} {p : ℕ}
    {C : Subgroup (CFSG.pCore p L)} (hcrit : Crit135 L p C) :
    L ≤ Subgroup.normalizer (((omegaOneCore p C).map L.subtype : Subgroup G) : Set G) := by
  have hDn : (omegaOneCore p C).Normal := hcrit.criticalAt.normal
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨d, hd, rfl⟩
    exact ⟨⟨l, hl⟩ * d * ⟨l, hl⟩⁻¹, hDn.conj_mem d hd _, rfl⟩
  · rintro ⟨d, hd, hdg⟩
    refine ⟨⟨l, hl⟩⁻¹ * d * ⟨l, hl⟩⁻¹⁻¹, hDn.conj_mem d hd _, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv] at hdg ⊢
    rw [hdg]
    group

theorem r1d_seven_dvd : 7 ∣ Nat.card (alternatingGroup (Fin 7)) := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem r1d_exists_eigen_ne_zero {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (f : Module.End K V) (hf : ∀ v, f (f v) = v) (hv : ∃ v, f v ≠ v) :
    ∃ w ∈ Module.End.eigenspace f (-1 : K), w ≠ 0 := by
  obtain ⟨v, hv⟩ := hv
  refine ⟨v - f v, Module.End.mem_eigenspace_iff.mpr ?_, sub_ne_zero.mpr (Ne.symm hv)⟩
  rw [map_sub, hf, neg_one_smul, neg_sub]

theorem r1d_eigenspace_invariant {K V : Type*} [CommRing K] [AddCommGroup V] [Module K V]
    (f g : Module.End K V) (hfg : f * g = g * f) (μ : K) :
    ∀ w ∈ Module.End.eigenspace f μ, g w ∈ Module.End.eigenspace f μ := by
  intro w hw
  rw [Module.End.mem_eigenspace_iff] at hw ⊢
  have h1 : f (g w) = g (f w) := congrArg (fun φ : Module.End K V => φ w) hfg
  rw [h1, hw, map_smul]

theorem r1d_dim_of_data {L : Type} [Group L] [Finite L] {p : ℕ} [Fact p.Prime]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
    (ρ : L →* Module.End (ZMod p) V) {z : L} (hz2 : z * z = 1) (hex : ∃ v, ρ z v ≠ v)
    (O : Subgroup (Subgroup.centralizer ({z} : Set L))) [O.Normal]
    (hOodd : Odd (Nat.card O))
    (hperf : Group.IsPerfect (Subgroup.centralizer ({z} : Set L) ⧸ O))
    (hp5 : 5 ≤ p) {T : Type} [Group T] [Finite T] (hT : AltTarget T) (h7 : 7 ∣ Nat.card T)
    (ψ : Subgroup.centralizer ({z} : Set L) →* T) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.zpowers (⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ :
      Subgroup.centralizer ({z} : Set L)) ⊔ O) :
    4 ≤ Module.finrank (ZMod p) (Module.End.eigenspace (ρ z) (-1 : ZMod p)) ∧
      (Module.finrank (ZMod p) (Module.End.eigenspace (ρ z) (-1 : ZMod p)) ≤ 4 → 7 ≤ p) := by
  haveI : IsSimpleGroup T := hT.simple
  have hp2 : p ≠ 2 := by omega
  have hzmem : z ∈ Subgroup.centralizer ({z} : Set L) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hsq : ∀ v, ρ z (ρ z v) = v := fun v => by
    have h1 : ρ z * ρ z = 1 := by rw [← map_mul, hz2, map_one]
    exact congrArg (fun φ : Module.End (ZMod p) V => φ v) h1
  have hinv : ∀ y : Subgroup.centralizer ({z} : Set L),
      ∀ w ∈ Module.End.eigenspace (ρ z) (-1 : ZMod p),
        (ρ.comp (Subgroup.centralizer ({z} : Set L)).subtype) y w ∈
          Module.End.eigenspace (ρ z) (-1 : ZMod p) := by
    intro y
    have hcomm : ρ z * ρ (y : L) = ρ (y : L) * ρ z := by
      rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_singleton_iff.mp y.2).symm]
    exact r1d_eigenspace_invariant (ρ z) (ρ (y : L)) hcomm (-1 : ZMod p)
  obtain ⟨w₀, hw₀, hw₀0⟩ := r1d_exists_eigen_ne_zero (ρ z) hsq hex
  have hW : ∃ w : ↥(Module.End.eigenspace (ρ z) (-1 : ZMod p)), w ≠ 0 :=
    ⟨⟨w₀, hw₀⟩, fun h => hw₀0 (congrArg Subtype.val h)⟩
  have hzW : ∀ w : ↥(Module.End.eigenspace (ρ z) (-1 : ZMod p)),
      restrictRep (ρ.comp (Subgroup.centralizer ({z} : Set L)).subtype)
        (Module.End.eigenspace (ρ z) (-1 : ZMod p)) hinv ⟨z, hzmem⟩ w = -w := by
    intro w
    apply Subtype.ext
    rw [restrictRep_apply, Submodule.coe_neg]
    exact (Module.End.mem_eigenspace_iff.mp w.2).trans (neg_one_smul (ZMod p) _)
  haveI : FiniteDimensional (ZMod p) ↥(Module.End.eigenspace (ρ z) (-1 : ZMod p)) :=
    Module.finite_iff_finite.mpr inferInstance
  have hkerW := r1_ker_le O hOodd hperf hp2
    (restrictRep (ρ.comp (Subgroup.centralizer ({z} : Set L)).subtype)
      (Module.End.eigenspace (ρ z) (-1 : ZMod p)) hinv)
    (z := ⟨z, hzmem⟩) hzW hW ψ hψ hker
  refine ⟨?_, ?_⟩
  · exact r1_dim_ge_four O hOodd hperf hp5
      (restrictRep (ρ.comp (Subgroup.centralizer ({z} : Set L)).subtype)
        (Module.End.eigenspace (ρ z) (-1 : ZMod p)) hinv)
      (z := ⟨z, hzmem⟩) hzW hW hT ψ hψ hkerW
  · intro hW4
    by_contra hlt
    push Not at hlt
    have hprime : p.Prime := Fact.out
    have hp5' : p = 5 := by
      have h6 : p ≠ 6 := by
        rintro rfl
        norm_num at hprime
      omega
    subst hp5'
    exact r1_not_five hW4
      (restrictRep (ρ.comp (Subgroup.centralizer ({z} : Set L)).subtype)
        (Module.End.eigenspace (ρ z) (-1 : ZMod 5)) hinv)
      h7 ψ hψ hkerW

theorem r1_dim_W {G : Type} [Group G] [Finite G] {L : Subgroup G}
    {p : ℕ} [Fact p.Prime] {C : Subgroup (CFSG.pCore p L)} (hcrit : Crit135 L p C)
    [IsElementaryAbelian p (↥((omegaOneCore p C).map L.subtype) ⧸
      frattini ↥((omegaOneCore p C).map L.subtype))]
    (hZ : OddCoreAlt7 L (aschbacherSolvableCore 3 L))
    (hcenter : Nat.card (Subgroup.center (L ⧸ CFSG.oddCore L)) = 2)
    (e : L ⧸ aschbacherSolvableCore 3 L ≃* alternatingGroup (Fin 7)) :
    ∃ z : L, z * z = 1 ∧ z ≠ 1 ∧ (∀ x : L, x * z * x⁻¹ * z⁻¹ ∈ CFSG.oddCore L) ∧
      4 ≤ Module.finrank (ZMod p) (Module.End.eigenspace
        (frattiniLinN p ((omegaOneCore p C).map L.subtype)
          ⟨(z : G), r1_L_le_normalizer hcrit z.2⟩) (-1 : ZMod p)) ∧
      (Module.finrank (ZMod p) (Module.End.eigenspace
        (frattiniLinN p ((omegaOneCore p C).map L.subtype)
          ⟨(z : G), r1_L_le_normalizer hcrit z.2⟩) (-1 : ZMod p)) ≤ 4 → 7 ≤ p) := by
  have hDD : DData p ((omegaOneCore p C).map L.subtype) := dData_of_crit135 hcrit
  have hp5 : 5 ≤ p := hDD.five_le
  have hLN := r1_L_le_normalizer hcrit
  obtain ⟨z, hz2, hz1, hzc, hodd', hperf', ψ, hψ, hker⟩ :=
    r1_L_data (X := ↥L) (O := CFSG.oddCore L) (θ := aschbacherSolvableCore 3 L)
      (CFSG.ABGDGroups.odd_card_oddCore L) hZ.isQuasisimple.1 hcenter e hZ.comap_center
  have hyo : orderOf (Subgroup.inclusion hLN z) = 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    apply orderOf_eq_prime
    · rw [← map_pow, sq, hz2, map_one]
    · intro h
      exact hz1 (Subgroup.inclusion_injective hLN (h.trans (map_one (Subgroup.inclusion hLN)).symm))
  have hex : ∃ v, ((frattiniLinN p ((omegaOneCore p C).map L.subtype)).comp
      (Subgroup.inclusion hLN)) z v ≠ v := by
    by_contra hcon
    push Not at hcon
    have hy : frattiniLinN p ((omegaOneCore p C).map L.subtype) (Subgroup.inclusion hLN z) = 1 :=
      LinearMap.ext fun v => hcon v
    exact false_of_frattiniLinN_eq_one ((omegaOneCore p C).map L.subtype) hDD.pgroup hDD.ne_two
      hDD.odd hyo hy
  refine ⟨z, hz2, hz1, hzc, ?_⟩
  exact r1d_dim_of_data ((frattiniLinN p ((omegaOneCore p C).map L.subtype)).comp
    (Subgroup.inclusion hLN)) hz2 hex
    ((CFSG.oddCore L).subgroupOf (Subgroup.centralizer ({z} : Set L)))
    hodd' hperf' hp5 altTarget_seven r1d_seven_dvd ψ hψ hker

theorem r1e_count_abstract {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) {A B : Module.End K V}
    (hA : A * A = 1) (hAB : A * B = B * A)
    (hA1 : Module.finrank K ↥(Module.End.eigenspace A 1) ≤ 2)
    (hAB1 : Module.finrank K ↥(Module.End.eigenspace (A * B) 1) ≤ 2) :
    Module.finrank K ↥(Module.End.eigenspace B (-1 : K)) ≤ 4 ∧
      Module.finrank K ↥(Module.End.eigenspace B (-1 : K)) ≤
        Module.finrank K ↥(Module.End.eigenspace B (-1 : K) ⊓ Module.End.eigenspace A 1) + 2 := by
  have hWA : ∀ v ∈ Module.End.eigenspace B (-1 : K), A v ∈ Module.End.eigenspace B (-1 : K) := by
    intro v hv
    rw [mem_eigenspace_neg_one_iff'] at hv ⊢
    have hc : B (A v) = A (B v) := by
      have h := LinearMap.congr_fun hAB v
      rw [Module.End.mul_apply, Module.End.mul_apply] at h
      exact h.symm
    rw [hc, hv, map_neg]
  have hsplit := finrank_split h2 hA (Module.End.eigenspace B (-1 : K)) hWA
  have hplus : Module.finrank K ↥(Module.End.eigenspace B (-1 : K) ⊓ Module.End.eigenspace A 1) ≤ 2 :=
    le_trans (Submodule.finrank_mono inf_le_right) hA1
  have hsub : Module.End.eigenspace B (-1 : K) ⊓ Module.End.eigenspace A (-1 : K) ≤
      Module.End.eigenspace (A * B) 1 := by
    intro v hv
    obtain ⟨hvB, hvA⟩ := hv
    rw [SetLike.mem_coe, mem_eigenspace_neg_one_iff'] at hvB hvA
    rw [mem_eigenspace_one_iff', Module.End.mul_apply, hvB, map_neg, hvA, neg_neg]
  have hminus : Module.finrank K ↥(Module.End.eigenspace B (-1 : K) ⊓
      Module.End.eigenspace A (-1 : K)) ≤ 2 :=
    le_trans (Submodule.finrank_mono hsub) hAB1
  constructor
  · omega
  · omega

theorem r1_count {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Dg : Subgroup G}
    (hDD : DData p Dg) [IsElementaryAbelian p (↥Dg ⧸ frattini ↥Dg)]
    {z u : Subgroup.normalizer (Dg : Set G)} (hz : orderOf z = 2) (hu : orderOf u = 2)
    (hzu : u * z = z * u) (huz : u ≠ z) :
    Module.finrank (ZMod p) (Module.End.eigenspace (frattiniLinN p Dg z) (-1 : ZMod p)) ≤ 4 ∧
      Module.finrank (ZMod p) (Module.End.eigenspace (frattiniLinN p Dg z) (-1 : ZMod p)) ≤
        Module.finrank (ZMod p) (↥(Module.End.eigenspace (frattiniLinN p Dg z) (-1 : ZMod p) ⊓
          Module.End.eigenspace (frattiniLinN p Dg u) (1 : ZMod p))) + 2 := by
  haveI : Finite (Additive (↥Dg ⧸ frattini ↥Dg)) := inferInstance
  haveI : Module.Finite (ZMod p) (Additive (↥Dg ⧸ frattini ↥Dg)) := Module.Finite.of_finite
  have hz2 : z ^ 2 = 1 := by
    have h := pow_orderOf_eq_one z
    rwa [hz] at h
  have hu2 : u ^ 2 = 1 := by
    have h := pow_orderOf_eq_one u
    rwa [hu] at h
  have hzz : z * z = 1 := by rw [← sq]; exact hz2
  have huu : u * u = 1 := by rw [← sq]; exact hu2
  have hA2 : frattiniLinN p Dg u * frattiniLinN p Dg u = 1 := by
    rw [← map_mul, ← sq, hu2, map_one]
  have hcomm : frattiniLinN p Dg u * frattiniLinN p Dg z =
      frattiniLinN p Dg z * frattiniLinN p Dg u := by
    rw [← map_mul, ← map_mul, hzu]
  have hA1 : Module.finrank (ZMod p)
      ↥(Module.End.eigenspace (frattiniLinN p Dg u) (1 : ZMod p)) ≤ 2 :=
    hDD.finrank_fixed u.2 (by rw [Subgroup.orderOf_coe]; exact hu)
  have huz1 : u * z ≠ 1 := by
    intro h
    apply huz
    calc u = u * (z * z) := by rw [hzz, mul_one]
      _ = u * z * z := by rw [mul_assoc]
      _ = z := by rw [h, one_mul]
  have hsq : (u * z) ^ 2 = 1 := by
    rw [sq]
    calc u * z * (u * z) = u * (z * u) * z := by simp only [mul_assoc]
      _ = u * (u * z) * z := by rw [← hzu]
      _ = u * u * (z * z) := by simp only [mul_assoc]
      _ = 1 := by rw [hzz, mul_one, huu]
  have hzuord : orderOf (u * z) = 2 := orderOf_eq_prime hsq huz1
  have hAB1 : Module.finrank (ZMod p)
      ↥(Module.End.eigenspace (frattiniLinN p Dg u * frattiniLinN p Dg z) (1 : ZMod p)) ≤ 2 := by
    rw [← map_mul]
    exact hDD.finrank_fixed (u * z).2 (by rw [Subgroup.orderOf_coe]; exact hzuord)
  exact r1e_count_abstract hDD.two_ne_zero' hA2 hcomm hA1 hAB1

end CFSG.RankThree.PartTwo.Sec13.Res7Proof
