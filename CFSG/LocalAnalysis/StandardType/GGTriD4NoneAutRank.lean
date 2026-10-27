module

public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section AutRank

variable {R : Type} [Group R]

theorem normal_range_conj_mulAut : ((MulAut.conj : R →* MulAut R).range).Normal := by
  refine ⟨?_⟩
  rintro _ ⟨r, rfl⟩ g
  refine ⟨g r, ?_⟩
  ext x
  simp [MulAut.conj_apply]

theorem conj_injective_of_center_eq_bot (hZ : Subgroup.center R = ⊥) :
    Function.Injective (MulAut.conj : R →* MulAut R) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  ext r
  rw [MonoidHom.mem_ker, Subgroup.mem_bot, ← Subgroup.mem_bot (G := R), ← hZ,
    Subgroup.mem_center_iff]
  constructor
  · intro h s
    have := congrArg (fun φ : MulAut R => φ s) h
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc s * r = r * s * r⁻¹ * r := by rw [this]
      _ = r * s := by group
  · intro h
    ext s
    simp only [MulAut.conj_apply, MulAut.one_apply]
    calc r * s * r⁻¹ = s * r * r⁻¹ := by rw [← h s]
      _ = s := by group

variable [Finite R]

theorem card_le_of_isElemAbelian_aut {p : ℕ} (hp : p.Prime) (hZ : Subgroup.center R = ⊥)
    (hOut : ∃ φ₀ : MulAut R, ∀ α : MulAut R,
      α ∈ (MulAut.conj : R →* MulAut R).range ⊔ Subgroup.zpowers φ₀) {c : ℕ}
    (hR : ∀ E : Subgroup R, IsElemAbelian p E → Nat.card E ≤ p ^ c)
    {A : Subgroup (MulAut R)} (hA : IsElemAbelian p A) : Nat.card A ≤ p ^ (c + 1) := by
  classical
  haveI : ((MulAut.conj : R →* MulAut R).range).Normal := normal_range_conj_mulAut
  set Inn : Subgroup (MulAut R) := (MulAut.conj : R →* MulAut R).range with hInn
  have hfin : Finite (MulAut R) := inferInstance
  let π : A →* MulAut R ⧸ Inn := (QuotientGroup.mk' Inn).comp A.subtype
  obtain ⟨φ₀, hφ₀⟩ := hOut
  have hcyc : IsCyclic (MulAut R ⧸ Inn) := by
    refine ⟨⟨QuotientGroup.mk φ₀, fun q => ?_⟩⟩
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨i, hi, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 (hφ₀ α)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff i).2 hi, one_mul, QuotientGroup.mk_zpow]
  haveI : Finite π.range := Finite.of_surjective _ π.rangeRestrict_surjective
  have hrange : Nat.card π.range ≤ p := by
    refine TableB.card_le_of_isCyclic hp.pos (Subgroup.isCyclic π.range) ?_
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ p = 1 := Subtype.ext (by simpa using hA.2 a a.2)
    rw [this, map_one]
  have hinj : Function.Injective (MulAut.conj : R →* MulAut R) :=
    conj_injective_of_center_eq_bot hZ
  have hk : π.ker = (A ⊓ Inn).subgroupOf A := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    change (QuotientGroup.mk (a : MulAut R) : MulAut R ⧸ Inn) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff]
    exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩
  set E : Subgroup R := (A ⊓ Inn).comap (MulAut.conj : R →* MulAut R) with hE
  have hEab : IsElemAbelian p E :=
    CFSG.Open.IsElemAbelian.comap (CFSG.Open.IsElemAbelian.mono hA inf_le_left) hinj
  have hEmap : E.map (MulAut.conj : R →* MulAut R) = A ⊓ Inn := by
    rw [hE, Subgroup.map_comap_eq]
    exact inf_eq_right.2 inf_le_right
  have hEcard : Nat.card E = Nat.card π.ker := by
    rw [hk, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A ⊓ Inn ≤ A)).toEquiv,
      ← hEmap]
    exact (Subgroup.card_map_of_injective hinj).symm
  have hker : Nat.card π.ker ≤ p ^ c := hEcard ▸ hR E hEab
  calc Nat.card A = Nat.card π.range * Nat.card π.ker :=
        (TableB.card_range_mul_card_ker π).symm
    _ ≤ p * p ^ c := Nat.mul_le_mul hrange hker
    _ = p ^ (c + 1) := by rw [pow_succ, mul_comm]

end AutRank

end CFSG.StandardType
