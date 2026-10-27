module

public import CFSG.Quasithin.Background.C35InspLevi
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListLevi
public import CFSG.Quasithin.Background.C35InspL45B

public section

namespace CFSG.Quasithin.C35Levi

open CFSG.Open CFSG.QuasithinUnique C35Pf CFSG.QuasithinUnique.Setup.X6
  CFSG.QuasithinUnique.Vol2Native.L239.Lie

variable {A : Type} [Group A] {K : Subgroup A} {G' : Type} [Group G']

theorem exists_noncomm_of_parabolicFacts {G : Type*} [Group G] [Finite G] {C P Q : Subgroup G}
    (hPC : P ≤ C) (hF : ParabolicFacts P Q) {T : Type*} [Group T] [Finite T] [IsSimpleGroup T]
    (hT : ∃ a b : T, a * b ≠ b * a) (g : ↥(perfectCore (P.subgroupOf C)) →* T)
    (hg : Function.Surjective g) :
    ∃ r x : ↥(perfectCore (P.subgroupOf C)), g r = 1 ∧ x * r ≠ r * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmap := CFSG.QuasithinUnique.Vol2Native.A312L.perfectCore_map_subgroupOf hPC
  have hP1 : perfectCore P ≠ ⊥ := by
    intro h
    obtain ⟨a, b, hab⟩ := hT
    apply hab
    obtain ⟨a', rfl⟩ := hg a
    obtain ⟨b', rfl⟩ := hg b
    have hbot : perfectCore (P.subgroupOf C) = ⊥ := by
      rw [← hmap] at h
      exact (Subgroup.map_eq_bot_iff_of_injective _ C.subtype_injective).1 h
    have h1 : ∀ z : ↥(perfectCore (P.subgroupOf C)), z = 1 := fun z =>
      Subtype.ext ((Subgroup.eq_bot_iff_forall _).1 hbot z z.2)
    rw [h1 a', h1 b']
  rcases hF.levi with hle | ⟨hQ, -⟩
  · exact absurd (C48Pf.FMod.eq_bot_of_perfect_of_isPGroup (perfectCore_perfect P)
      (hF.pGroup.to_le hle)) hP1
  · have hQ1 : Q ≠ ⊥ := by
      intro h
      obtain ⟨x, hx, y, hy, hxy⟩ := hF.nonabelian
      rw [h, Subgroup.mem_bot] at hx hy
      rw [hx, hy] at hxy
      exact hxy rfl
    obtain ⟨q, hq, x, hx, hxq⟩ := exists_noncomm_of_le_commutator hQ hQ1
    have hQC : Q ≤ perfectCore P := by
      refine hQ.trans (Subgroup.commutator_le.2 fun q hq c hc => ?_)
      have hqN : q ∈ Subgroup.normalizer (perfectCore P : Set G) :=
        normalizer_le_normalizer_perfectCore P (Subgroup.le_normalizer (hF.le hq))
      rw [commutatorElement_def]
      exact mul_mem ((Subgroup.mem_normalizer_iff.1 hqN c).1 hc) (inv_mem hc)
    have hq' : q ∈ (perfectCore (P.subgroupOf C)).map C.subtype := hmap ▸ hQC hq
    have hx' : x ∈ (perfectCore (P.subgroupOf C)).map C.subtype := hmap ▸ hx
    obtain ⟨q', hq'm, rfl⟩ := hq'
    obtain ⟨x', hx'm, rfl⟩ := hx'
    set ι : ↥(perfectCore (P.subgroupOf C)) →* G :=
      C.subtype.comp (perfectCore (P.subgroupOf C)).subtype with hι
    set R : Subgroup ↥(perfectCore (P.subgroupOf C)) := Q.comap ι with hR
    have hRn : R.Normal := by
      refine ⟨fun r hr n => ?_⟩
      have hnP : ((n : ↥C) : G) ∈ P :=
        Subgroup.mem_subgroupOf.1 (perfectCore_le (P.subgroupOf C) n.2)
      show ι (n * r * n⁻¹) ∈ Q
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 (hF.normalizes hnP) _).1 hr
    have hR2 : IsPGroup 2 R := by
      intro r
      obtain ⟨k, hk⟩ := hF.pGroup ⟨ι r, r.2⟩
      refine ⟨k, Subtype.ext ?_⟩
      have h1 := congrArg Subtype.val hk
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
      apply Subtype.ext
      apply Subtype.ext
      simpa [hι] using h1
    have hrR : (⟨q', hq'm⟩ : ↥(perfectCore (P.subgroupOf C))) ∈ R := hq
    refine ⟨⟨q', hq'm⟩, ⟨x', hx'm⟩, le_ker_of_isPGroup hT g hg hR2 hrR, fun h => hxq ?_⟩
    have := congrArg (fun z : ↥(perfectCore (P.subgroupOf C)) => ((z : ↥C) : G)) h
    simpa using this

theorem img_perfectCore_ne_bot [Finite A] {Y : Subgroup A} (hZ : IsPGroup 2 ↥(centerOf K))
    (hYK : Y ≤ K) (θ : ↥K →* G') (hθ : θ.ker ≤ Subgroup.center ↥K) (hX0 : perfectCore Y ≠ ⊥) :
    img θ (perfectCore Y) ≠ ⊥ := by
  intro h
  apply hX0
  have hXK : perfectCore Y ≤ K := (perfectCore_le Y).trans hYK
  have hXZ : perfectCore Y ≤ centerOf K := by
    intro x hx
    have h1 : θ ⟨x, hXK hx⟩ ∈ img θ (perfectCore Y) :=
      ⟨⟨x, hXK hx⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact mem_centerOf_iff.2 (hθ h1)
  exact C48Pf.FMod.eq_bot_of_perfect_of_isPGroup (perfectCore_perfect Y) (hZ.to_le hXZ)

theorem exists_residual [Finite A] {Y : Subgroup A} (hZ : IsPGroup 2 ↥(centerOf K))
    (hpar : IsParabolic2 K Y) (hne : Y ≠ K) (hX0 : perfectCore Y ≠ ⊥) {S : Type} [Group S]
    [Finite S] (φ : ↥K →* S) (hker : φ.ker ≤ Subgroup.center ↥K) (hφ : Function.Surjective φ)
    {U : Subgroup S} (hU : IsSylowTwoOf U ⊤) {P : Fin 2 → Subgroup S}
    (hP : ResidualOvergroupsAt S U P) :
    ∃ (θ : ↥K →* S) (j : Fin 2), θ.ker ≤ Subgroup.center ↥K ∧
      img θ (perfectCore Y) = perfectCore (P j) := by
  obtain ⟨g, hNY, hne', hns⟩ := exists_conj_normalizer hZ hpar hne hX0 φ hker hφ hU
  set θ := (MulAut.conj g⁻¹).toMonoidHom.comp φ with hθ
  have hUY : U ≤ img θ Y := Subgroup.le_normalizer.trans hNY
  obtain ⟨j, -, hd⟩ := hP.2.2.2.2.1 (img θ Y) hUY hne' hns
  refine ⟨θ, j, by rw [hθ, ker_conj_comp]; exact hker, ?_⟩
  rw [img_perfectCore θ hpar.1,
    ← CFSG.QuasithinUnique.Vol2Native.A312L.dInf_eq_perfectCore, hd,
    CFSG.QuasithinUnique.Vol2Native.A312L.dInf_eq_perfectCore]

theorem leviConcl_of_residual [Finite A] {Y : Subgroup A} (hZ : IsPGroup 2 ↥(centerOf K))
    (hpar : IsParabolic2 K Y) (hne : Y ≠ K) (hX0 : perfectCore Y ≠ ⊥) {S : Type} [Group S]
    [Finite S] (φ : ↥K →* S) (hker : φ.ker ≤ Subgroup.center ↥K) (hφ : Function.Surjective φ)
    {U : Subgroup S} (hU : IsSylowTwoOf U ⊤) {P : Fin 2 → Subgroup S}
    (hP : ResidualOvergroupsAt S U P)
    (hlevi : ∀ j, perfectCore (P j) ≠ ⊥ → ∃ (T : Type) (_ : Group T) (_ : Finite T)
      (_ : IsSimpleGroup T) (g : ↥(perfectCore (P j)) →* T), (∃ a b : T, a * b ≠ b * a) ∧
      Function.Surjective g ∧ IsPGroup 2 g.ker ∧ (∃ r x, g r = 1 ∧ x * r ≠ r * x) ∧
      SmallLevi T) : LeviConcl K Y := by
  obtain ⟨θ, j, hθ, himg⟩ := exists_residual hZ hpar hne hX0 φ hker hφ hU hP
  have hj : perfectCore (P j) ≠ ⊥ := himg ▸ img_perfectCore_ne_bot hZ hpar.1 θ hθ hX0
  obtain ⟨T, _, _, _, g, hT, hg, hgk, hnc, hs⟩ := hlevi j hj
  have himg' : img θ (perfectCore Y) = (perfectCore (P j)).map (MonoidHom.id S) := by
    rw [Subgroup.map_id, himg]
  obtain ⟨hc, ⟨eT⟩⟩ := levi_of_model hZ hpar.1 θ hθ (MonoidHom.id S)
    (fun _ _ _ _ h => h) himg' hT g hg hgk hnc
  exact leviConcl_of_small hc (hs.of_mulEquiv eT.symm)

end CFSG.Quasithin.C35Levi
