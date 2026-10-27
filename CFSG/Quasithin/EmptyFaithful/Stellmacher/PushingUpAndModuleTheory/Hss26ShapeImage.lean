module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.Hss26ShapeQuot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FrattiniBasic
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.SitSigma
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreBasic

public section

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique.Setup.Campbell CFSG.Quasithin.F7 CFSG.Quasithin.F53Push
  CosetGeom Equiv
open CFSG.QuasithinUnique (IsSylowTwoOf)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem noNormalTwo_oTwoQuot (X : Subgroup G) : NoNormalTwo (OTwoQuot X) := by
  intro N hN hN2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := CFSG.Open.pCore 2 ↥X with hC
  let π : ↥X →* OTwoQuot X := QuotientGroup.mk' C
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective C
  have hN' : (N.comap π).Normal := hN.comap π
  have hCp : IsPGroup 2 C := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hp : IsPGroup 2 (N.comap π) := by
    intro g
    obtain ⟨k, hk⟩ := hN2 ⟨π g, g.2⟩
    have h1 : (g : ↥X) ^ 2 ^ k ∈ C := by
      have : π ((g : ↥X) ^ 2 ^ k) = 1 := by
        rw [map_pow]
        exact congrArg Subtype.val hk
      exact (QuotientGroup.eq_one_iff _).mp this
    obtain ⟨l, hl⟩ := hCp ⟨_, h1⟩
    refine ⟨k + l, Subtype.ext ?_⟩
    have := congrArg Subtype.val hl
    simpa [pow_add, pow_mul] using this
  have hle : N.comap π ≤ C := CFSG.LieType.BorelTits.le_pCore 2 hN' hp
  refine (Subgroup.eq_bot_iff_forall N).mpr fun q hq => ?_
  obtain ⟨x, rfl⟩ := hπ q
  exact (QuotientGroup.eq_one_iff _).mpr (hle hq)

theorem NoNormalTwo.of_mulEquiv {Q Q' : Type*} [Group Q] [Group Q'] (e : Q ≃* Q')
    (h : NoNormalTwo Q) : NoNormalTwo Q' := by
  intro N hN hN2
  have h1 : N.comap e.toMonoidHom = ⊥ := by
    refine h _ (hN.comap _) ?_
    intro g
    obtain ⟨k, hk⟩ := hN2 ⟨e g, g.2⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (e (g : Q)) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h2 : (g : Q) ^ 2 ^ k = 1 := e.injective (by rw [map_pow, map_one]; exact h1)
    exact h2
  rw [eq_bot_iff]
  intro y hy
  have hy' : e.symm y ∈ N.comap e.toMonoidHom := by simpa using hy
  rw [h1, Subgroup.mem_bot] at hy'
  have : y = e (e.symm y) := (e.apply_symm_apply y).symm
  rw [this, hy', map_one]
  exact Subgroup.one_mem _

namespace SitSigma

variable {δ μ : Geo H M} {X : Subgroup G}

noncomputable def redHom {n : ℕ} (ψ : ↥(stab δ) →* Perm (Fin n)) (hX : X ≤ stab δ) :
    ↥X →* Perm (Fin n) :=
  ψ.comp (Subgroup.inclusion hX)

theorem redHom_ker {n : ℕ} (ψ : ↥(stab δ) →* Perm (Fin n))
    (hker : ∀ x : ↥(stab δ), ψ x = 1 ↔ (x : G) ∈ Qv δ) (h : SitSigma δ μ X)
    (hRQ : pCoreOf 2 X ≤ Qv δ) :
    (redHom ψ h.le_stab).ker = CFSG.Open.pCore 2 ↥X := by
  ext x
  rw [MonoidHom.mem_ker, F1.mem_pCore_iff_coe]
  change ψ (Subgroup.inclusion h.le_stab x) = 1 ↔ _
  rw [hker]
  constructor
  · intro hx
    exact h.inf_Qv_le_R ⟨x.2, hx⟩
  · intro hx
    exact hRQ hx

theorem redHom_eq_one_iff {n : ℕ} (ψ : ↥(stab δ) →* Perm (Fin n))
    (hker : ∀ x : ↥(stab δ), ψ x = 1 ↔ (x : G) ∈ Qv δ) (h : SitSigma δ μ X)
    (hRQ : pCoreOf 2 X ≤ Qv δ) (x : ↥X) :
    redHom ψ h.le_stab x = 1 ↔ (x : G) ∈ pCoreOf 2 X := by
  rw [← MonoidHom.mem_ker, redHom_ker ψ hker h hRQ, F1.mem_pCore_iff_coe]

theorem sylow_image {n : ℕ} {X P : Subgroup G} (hP : IsSylowTwoOf P X)
    (φ : ↥X →* Perm (Fin n)) (hφ : ∀ x : ↥X, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 X)
    (hPR : ¬ P ≤ pCoreOf 2 X) :
    Nonempty (OTwoQuot X ≃* φ.range) ∧ NoNormalTwo ↥φ.range ∧
      ∃ T : Subgroup ↥φ.range, IsPGroup 2 T ∧ ¬ 2 ∣ T.index ∧ T ≠ ⊥ := by
  have hk : φ.ker = CFSG.Open.pCore 2 ↥X := by
    ext x
    rw [MonoidHom.mem_ker, hφ, F1.mem_pCore_iff_coe]
  have e : OTwoQuot X ≃* φ.range :=
    (QuotientGroup.quotientMulEquivOfEq hk.symm).trans (QuotientGroup.quotientKerEquivRange φ)
  set T : Subgroup ↥φ.range := ((P).subgroupOf X).map φ.rangeRestrict with hT
  have hT2 : IsPGroup 2 T :=
    (hP.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP.1).symm).map _
  have hkerP : φ.rangeRestrict.ker ≤ P.subgroupOf X := by
    intro x hx
    rw [MonoidHom.ker_rangeRestrict, hk, F1.mem_pCore_iff_coe] at hx
    exact isSylowTwoOf_pCoreOf_le hP hx
  have hTi : ¬ 2 ∣ T.index := by
    rw [hT, Subgroup.index_map_eq (f := φ.rangeRestrict) (H := P.subgroupOf X)
      φ.rangeRestrict_surjective hkerP]
    exact hP.2.2
  have hT0 : T ≠ ⊥ := by
    intro hT0
    apply hPR
    intro p hp
    have hpT : φ.rangeRestrict ⟨p, hP.1 hp⟩ ∈ T :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hp)
    rw [hT0, Subgroup.mem_bot] at hpT
    have h1 : φ ⟨p, hP.1 hp⟩ = 1 := by
      have := congrArg Subtype.val hpT
      simpa using this
    exact (hφ _).mp h1
  exact ⟨⟨e⟩, (noNormalTwo_oTwoQuot X).of_mulEquiv e, T, hT2, hTi, hT0⟩

theorem shape_of_hom_three {X P : Subgroup G} (hP : IsSylowTwoOf P X)
    (φ : ↥X →* Perm (Fin 3)) (hφ : ∀ x : ↥X, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 X)
    (hPR : ¬ P ≤ pCoreOf 2 X) : Nonempty (OTwoQuot X ≃* Perm (Fin 3)) := by
  obtain ⟨⟨e⟩, hK, T, hT2, hTi, hT0⟩ := sylow_image hP φ hφ hPR
  exact (perm3_shape _ hT2 hTi hT0 hK).map fun e' => e.trans e'

theorem shape_of_hom_five {X P : Subgroup G} (hP : IsSylowTwoOf P X)
    (φ : ↥X →* Perm (Fin 5)) (hφ : ∀ x : ↥X, φ x = 1 ↔ (x : G) ∈ pCoreOf 2 X)
    (hPR : ¬ P ≤ pCoreOf 2 X) :
    Nonempty (OTwoQuot X ≃* Perm (Fin 3)) ∨
      (φ.range = alternatingGroup (Fin 5) ∧
        Nonempty (OTwoQuot X ≃* ↥(alternatingGroup (Fin 5)))) ∨
      (φ.range = ⊤ ∧ Nonempty (OTwoQuot X ≃* Perm (Fin 5))) ∨
      (∃ x : ↥X, ∃ y : Perm (Fin 5), φ x = y ∧ orderOf y = 5 ∧
        ∀ t ∈ φ.range, t * t = 1 → t ≠ 1 → t * y * t⁻¹ = y⁻¹) := by
  obtain ⟨⟨e⟩, hK, T, hT2, hTi, hT0⟩ := sylow_image hP φ hφ hPR
  rcases perm5_shape _ hT2 hTi hT0 hK with h3 | hA5 | htop | ⟨y, hy, hy5, hinv⟩
  · exact Or.inl (h3.map fun e' => e.trans e')
  · exact Or.inr (Or.inl ⟨hA5, ⟨e.trans (MulEquiv.subgroupCongr hA5)⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨htop, ⟨e.trans ((MulEquiv.subgroupCongr htop).trans
      Subgroup.topEquiv)⟩⟩))
  · obtain ⟨x, hx⟩ := hy
    exact Or.inr (Or.inr (Or.inr ⟨x, y, hx, hy5, hinv⟩))

end SitSigma

end CFSG.Quasithin.F53
