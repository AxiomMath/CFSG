module

public import CFSG.Quasithin.Vol2.Ch11SecABasicV
public import CFSG.Quasithin.Vol2.Ch11SecBK5Base6
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch11SecOE3B

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE3

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

structure Setting (G : Type) [Group G] [Finite G] (T K I : Subgroup G) (r : ℕ) : Prop where
  fsu : FSU G T K I
  normal : T ≤ Subgroup.normalizer (K : Set G)
  prime : r.Prime
  five_le : 5 ≤ r
  shape : R2Shape r (↥K ⧸ CFSG.pCore 2 ↥K)

theorem reducedAggregate_le_centralizer' (X : Subgroup G) :
    reducedAggregate X ≤ Subgroup.centralizer (pCoreOf 2 X : Set G) := by
  obtain ⟨-, -, hZ⟩ := primeReducedAggregate_normal_elementaryAbelian (E := ↥X) 2
  rintro _ ⟨x', hx', rfl⟩
  obtain ⟨-, h2, -⟩ := BlueprintB2.mem_centerTorsion_iff.mp (hZ hx')
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨k, hk, rfl⟩
  exact congrArg Subtype.val (h2 k hk)

omit [Finite G] in
theorem I_le_V (T I : Subgroup G) : I ≤ fsuV T I := le_conjClosure I T

omit [Finite G] in
theorem exists_autOn_hom {K V : Subgroup G} (hKN : K ≤ Subgroup.normalizer (V : Set G)) :
    ∃ f : ↥K →* ↥(autOn K V), Function.Surjective f ∧
      ∀ k : ↥K, f k = 1 ↔ ∀ v ∈ V, (k : G) * v * (k : G)⁻¹ = v := by
  refine ⟨((conjAct V).subgroupMap (K.subgroupOf (Subgroup.normalizer (V : Set G)))).comp
      (Subgroup.subgroupOfEquivOfLe hKN).symm.toMonoidHom,
    (MonoidHom.subgroupMap_surjective _ _).comp (Subgroup.subgroupOfEquivOfLe hKN).symm.surjective,
    fun k => ?_⟩
  constructor
  · intro hk v hv
    have h1 := congrArg (fun φ : ↥(autOn K V) => ((φ : MulAut ↥V) ⟨v, hv⟩ : G)) hk
    change ((conjAct V ⟨k, hKN k.2⟩ ⟨v, hv⟩ : ↥V) : G) = v at h1
    rwa [SecB.K5.conjAct_coe] at h1
  · intro hk
    apply Subtype.ext
    refine MulEquiv.ext fun v => Subtype.ext ?_
    change ((conjAct V ⟨k, hKN k.2⟩ v : ↥V) : G) = v
    rw [SecB.K5.conjAct_coe]
    exact hk v v.2

namespace Setting

variable {T K I : Subgroup G} {r : ℕ} (h : Setting G T K I r)
include h

theorem fsuL0_eq : fsuL0 T K = K :=
  le_antisymm (conjClosure_le fun _ ht k hk => (Subgroup.mem_normalizer_iff.1 (h.normal ht) k).1 hk)
    (le_conjClosure K T)

theorem le_reducedAggregate : fsuV T I ≤ reducedAggregate (K ⊔ T) := by
  have hN := (Vol2.Ch11.SecA.reducedAggregate_props (K ⊔ T)).2.2.2
  refine conjClosure_le fun t ht z hz => ?_
  exact (Subgroup.mem_normalizer_iff.mp (hN (Subgroup.mem_sup_right ht)) z).mp
    (h.fsu.irrPlus.1 hz)

theorem pCoreOf_le_centralizer : pCoreOf 2 (K ⊔ T) ≤ Subgroup.centralizer (fsuV T I : Set G) :=
  fun x hx => Subgroup.mem_centralizer_iff.mpr fun _ hv =>
    (Subgroup.mem_centralizer_iff.mp
      (reducedAggregate_le_centralizer' (K ⊔ T) (h.le_reducedAggregate hv)) x hx).symm

theorem pCoreOf_K_le : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left) ?_
    (pCoreOf_isPGroup 2 K)
  exact sup_le (le_normalizer_pCoreOf 2 K) (h.normal.trans (normalizer_le_normalizer_pCoreOf 2 K))

theorem le_normalizer_I : K ≤ Subgroup.normalizer (I : Set G) := by
  have := h.fsu.irrPlus.2.2.1
  rwa [show conjClosure K T = K from h.fsuL0_eq] at this

theorem commutator_I : ⁅I, K⁆ = I := by
  have := h.fsu.irrPlus.2.2.2.1
  rwa [show conjClosure K T = K from h.fsuL0_eq] at this

theorem le_normalizer_V : K ≤ Subgroup.normalizer (fsuV T I : Set G) :=
  Vol2.Ch11.SecA.le_normalizer_conjClosure_of_le' h.le_normalizer_I h.normal

theorem I_ne_bot : I ≠ ⊥ := h.fsu.irrPlus.2.1

theorem not_le_centralizer : ¬ K ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  intro hK
  apply h.I_ne_bot
  rw [← h.commutator_I, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact (I_le_V T I).trans (Subgroup.le_centralizer_iff.mp hK)

theorem exists_quot_hom : ∃ ψ : (↥K ⧸ CFSG.pCore 2 ↥K) →* ↥(autOn K (fsuV T I)),
    Function.Surjective ψ ∧ ∃ x, ψ x ≠ 1 := by
  obtain ⟨f, hfs, hf⟩ := exists_autOn_hom h.le_normalizer_V
  have hN : CFSG.pCore 2 ↥K ≤ f.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, hf]
    intro v hv
    have hxK : (x : G) ∈ pCoreOf 2 K :=
      ⟨x, by assumption, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp (h.pCoreOf_le_centralizer (h.pCoreOf_K_le hxK)) v hv
    rw [← h1, mul_inv_cancel_right]
  refine ⟨QuotientGroup.lift _ f hN, fun y => ?_, ?_⟩
  · obtain ⟨k, rfl⟩ := hfs y
    exact ⟨QuotientGroup.mk k, rfl⟩
  · by_contra hall
    push Not at hall
    apply h.not_le_centralizer
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := (hf ⟨k, hk⟩).mp (hall (QuotientGroup.mk ⟨k, hk⟩)) v hv
    calc v * k = k * v * k⁻¹ * k := by rw [h1]
      _ = k * v := by group

theorem shape_autOn : R2Shape r ↥(autOn K (fsuV T I)) := by
  obtain ⟨ψ, hψs, hψnt⟩ := h.exists_quot_hom
  exact h.shape.of_surjective h.prime h.five_le hψs hψnt

end Setting

end CFSG.Quasithin.Vol2.Ch11.OE3
