module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin.MS93.S4A

open CFSG.Quasithin CFSG.QuasithinUnique

section Quot

variable {H : Type} [Group H] {N : Subgroup H} [N.Normal]
  {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
  {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}

@[expose] noncomputable def natQuot (α : ↥(⊤ : Subgroup H) →* ↥Γ)
    (hN : ∀ n ∈ N, α ⟨n, Subgroup.mem_top n⟩ = 1) :
    ↥(⊤ : Subgroup (H ⧸ N)) →* ↥Γ :=
  (QuotientGroup.lift N (α.comp (Subgroup.topEquiv (G := H)).symm.toMonoidHom) fun n hn => by
      rw [MonoidHom.mem_ker]
      exact hN n hn).comp (⊤ : Subgroup (H ⧸ N)).subtype

theorem map_mk_le_map_mk_iff {A B : Subgroup H} :
    A.map (QuotientGroup.mk' N) ≤ B.map (QuotientGroup.mk' N) ↔ A ≤ B ⊔ N := by
  rw [Subgroup.map_le_iff_le_comap, Subgroup.comap_map_eq, QuotientGroup.ker_mk']

theorem map_mk_eq_bot_iff {A : Subgroup H} :
    A.map (QuotientGroup.mk' N) = ⊥ ↔ A ≤ N := by
  rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

theorem isSumOfNaturalModulesVia_quotient {V Z : Subgroup H} {α : ↥(⊤ : Subgroup H) →* ↥Γ}
    {dual : Bool} {k : ℕ} (h : IsSumOfNaturalModulesVia ⊤ V Z α dual k)
    (hN : ∀ n ∈ N, α ⟨n, Subgroup.mem_top n⟩ = 1) (hVN : V ⊓ N ≤ Z) :
    IsSumOfNaturalModulesVia (⊤ : Subgroup (H ⧸ N)) (V.map (QuotientGroup.mk' N))
      (Z.map (QuotientGroup.mk' N)) (natQuot α hN) dual k := by
  obtain ⟨hVn, hZV, β, hβs, hβk, hβc⟩ := h
  set π := QuotientGroup.mk' N with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective N
  set πV : ↥V →* ↥(V.map π) := π.subgroupMap V with hπV
  have hπVs : Function.Surjective πV := π.subgroupMap_surjective V
  have hkerV : πV.ker ≤ β.ker := by
    intro v hv
    rw [MonoidHom.mem_ker] at hv
    have hvN : (v : H) ∈ N := by
      have := congrArg Subtype.val hv
      rw [π.subgroupMap_apply_coe] at this
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      exact this
    rw [hβk, Subgroup.mem_subgroupOf]
    exact hVN ⟨v.2, hvN⟩
  set β' : ↥(V.map π) →* Multiplicative (Fin k → ι → F) :=
    (πV.liftOfRightInverse (Function.surjInv hπVs) (Function.rightInverse_surjInv hπVs))
      ⟨β, hkerV⟩ with hβ'
  have hβ'π : ∀ v : ↥V, β' (πV v) = β v := fun v =>
    πV.liftOfRightInverse_comp_apply _ _ ⟨β, hkerV⟩ v
  have hZiff : ∀ v : ↥V, (π v ∈ Z.map π) ↔ (v : H) ∈ Z := by
    intro v
    constructor
    · rintro ⟨z, hz, hzv⟩
      have hN' : (z : H)⁻¹ * v ∈ N := by
        rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker, map_mul, map_inv, ← hπ, hzv,
          inv_mul_cancel]
      have := hVN ⟨V.mul_mem (V.inv_mem (hZV hz)) v.2, hN'⟩
      simpa using Z.mul_mem hz this
    · intro hv
      exact ⟨v, hv, rfl⟩
  refine ⟨?_, Subgroup.map_mono hZV, β', ?_, ?_, ?_⟩
  ·
    intro q _
    obtain ⟨g, rfl⟩ := hπs q
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g : H, ∀ x ∈ V.map π, π g * x * (π g)⁻¹ ∈ V.map π := by
      rintro g _ ⟨v, hv, rfl⟩
      refine ⟨g * v * g⁻¹, (Subgroup.mem_normalizer_iff.mp (hVn (Subgroup.mem_top g)) v).mp hv,
        ?_⟩
      simp
    intro x
    constructor
    · exact key g x
    · intro hx
      have := key g⁻¹ _ hx
      simpa [mul_assoc] using this
  ·
    intro y
    obtain ⟨v, rfl⟩ := hβs y
    exact ⟨πV v, hβ'π v⟩
  ·
    ext x
    obtain ⟨v, rfl⟩ := hπVs x
    rw [MonoidHom.mem_ker, hβ'π, ← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf,
      Subgroup.mem_subgroupOf, π.subgroupMap_apply_coe, hZiff]
  ·
    intro a u v huv i
    obtain ⟨g, hg⟩ := hπs (a : H ⧸ N)
    have ha : a = ⟨π g, Subgroup.mem_top _⟩ := Subtype.ext hg.symm
    subst ha
    obtain ⟨u', rfl⟩ := hπVs u
    obtain ⟨v', rfl⟩ := hπVs v
    have hgu : g * u' * g⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.mp (hVn (Subgroup.mem_top g)) u').mp u'.2
    have hcong : πV v' = πV ⟨g * u' * g⁻¹, hgu⟩ := by
      apply Subtype.ext
      rw [π.subgroupMap_apply_coe, π.subgroupMap_apply_coe]
      rw [π.subgroupMap_apply_coe, π.subgroupMap_apply_coe] at huv
      rw [huv]
      simp
    rw [hcong, hβ'π, hβ'π]
    exact hβc ⟨g, Subgroup.mem_top g⟩ u' ⟨_, hgu⟩ rfl i

end Quot

end CFSG.Quasithin.MS93.S4A
