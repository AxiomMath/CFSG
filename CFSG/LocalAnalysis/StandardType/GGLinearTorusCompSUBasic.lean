module

public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompBasic
import CFSG.RankThree.PartOne.S15K.CentralCover

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial

namespace SUTorus

variable {K : Type} [Field K] {f n : ℕ} {G : Type*} [Group G]

@[expose] def suPairs (ψ : ↥(unitarySU 2 f K n) →* G) : Subgroup (G × GL (Fin n) K) where
  carrier := {x | x.2 ∈ Subgroup.normalizer ((unitarySU 2 f K n : Set (GL (Fin n) K))) ∧
    ∀ u v : ↥(unitarySU 2 f K n), (v : GL (Fin n) K) = x.2 * u * x.2⁻¹ →
      x.1 * ψ u * x.1⁻¹ = ψ v}
  one_mem' := ⟨Subgroup.one_mem _, fun u v h => by
    have hv : v = u := Subtype.ext (by rw [h]; simp)
    simp [hv]⟩
  mul_mem' := by
    rintro ⟨a, A⟩ ⟨b, B⟩ ⟨hA, ha⟩ ⟨hB, hb⟩
    refine ⟨Subgroup.mul_mem _ hA hB, fun u v h => ?_⟩
    let w : ↥(unitarySU 2 f K n) := ⟨B * u * B⁻¹, (Subgroup.mem_normalizer_iff.mp hB u).mp u.2⟩
    have hw := hb u w rfl
    have hv := ha w v (by
      change (v : GL (Fin n) K) = A * (B * u * B⁻¹) * A⁻¹
      rw [h]
      change A * B * u * (A * B)⁻¹ = A * (B * u * B⁻¹) * A⁻¹
      group)
    change a * b * ψ u * (a * b)⁻¹ = ψ v
    calc a * b * ψ u * (a * b)⁻¹ = a * (b * ψ u * b⁻¹) * a⁻¹ := by group
      _ = a * ψ w * a⁻¹ := by rw [hw]
      _ = ψ v := hv
  inv_mem' := by
    rintro ⟨a, A⟩ ⟨hA, ha⟩
    refine ⟨Subgroup.inv_mem _ hA, fun u v h => ?_⟩
    have hu := ha v u (by
      change (v : GL (Fin n) K) = A⁻¹ * u * A⁻¹⁻¹ at h
      rw [h]
      group)
    change a⁻¹ * ψ u * a⁻¹⁻¹ = ψ v
    rw [← hu]
    group

theorem mem_suPairs {ψ : ↥(unitarySU 2 f K n) →* G} {y : G} {B : GL (Fin n) K} :
    (y, B) ∈ suPairs ψ ↔ B ∈ Subgroup.normalizer ((unitarySU 2 f K n : Set (GL (Fin n) K))) ∧
      ∀ u v : ↥(unitarySU 2 f K n), (v : GL (Fin n) K) = B * u * B⁻¹ → y * ψ u * y⁻¹ = ψ v :=
  Iff.rfl

theorem scalar_mem_normalizer (c : Kˣ) :
    Matrix.GeneralLinearGroup.scalar (Fin n) c ∈
      Subgroup.normalizer ((unitarySU 2 f K n : Set (GL (Fin n) K))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  rw [TypeA.PGLTor.scalar_mul_comm, mul_inv_cancel_right]

theorem one_scalar_mem_suPairs (ψ : ↥(unitarySU 2 f K n) →* G) (c : Kˣ) :
    ((1 : G), Matrix.GeneralLinearGroup.scalar (Fin n) c) ∈ suPairs ψ := by
  refine ⟨scalar_mem_normalizer c, fun u v hv => ?_⟩
  have hvu : v = u := Subtype.ext (by
    rw [hv, TypeA.PGLTor.scalar_mul_comm, mul_inv_cancel_right])
  rw [hvu, one_mul, inv_one, mul_one]

theorem mem_centralizer_of_mem_suPairs_one {ψ : ↥(unitarySU 2 f K n) →* G} {y : G}
    (hy : (y, (1 : GL (Fin n) K)) ∈ suPairs ψ) : y ∈ Subgroup.centralizer (ψ.range : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨u, rfl⟩
  have h1 := hy.2 u u (by simp)
  calc ψ u * y = y * ψ u * y⁻¹ * y := by rw [h1]
    _ = y * ψ u := by group

theorem exists_scalar_of_mem_suPairs_one (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (3, 2)) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1)
    {ψ : ↥(unitarySU 2 f K n) →* G} (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n))
    {B : GL (Fin n) K} (hB : ((1 : G), B) ∈ suPairs ψ) :
    ∃ c : Kˣ, B = Matrix.GeneralLinearGroup.scalar (Fin n) c := by
  have : Finite K := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := h.charP
  have hperf : Group.IsPerfect ↥(unitarySU 2 f K n) :=
    CFSG.ClassicalGroups.Unitary.isPerfect_statedSU h.card_eq_sq hn hnq
  have key := CFSG.RankThree.PartOne.S15K.eq_of_perfect_of_map_eq ψ hker hperf
    ((unitarySU 2 f K n).normalizerMonoidHom ⟨B, hB.1⟩).toMonoidHom (MonoidHom.id _)
    (fun u => by
      have h1 : (1 : G) * ψ u * (1 : G)⁻¹ =
          ψ ((unitarySU 2 f K n).normalizerMonoidHom ⟨B, hB.1⟩ u) := hB.2 u _ rfl
      simp only [one_mul, inv_one, mul_one] at h1
      exact h1.symm)
  have hcomm : ∀ g ∈ unitarySU 2 f K n, B * g = g * B := by
    intro g hg
    have h2 := congrArg Subtype.val (key ⟨g, hg⟩)
    change B * g * B⁻¹ = g at h2
    calc B * g = B * g * B⁻¹ * B := by group
      _ = g * B := by rw [h2]
  obtain ⟨c, hc⟩ := TableBUE.mem_scalars_of_commute h hp hpq hcomm
  exact ⟨c, hc.symm⟩

theorem exists_scalar_mul_of_mem_suPairs (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (3, 2)) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1)
    {ψ : ↥(unitarySU 2 f K n) →* G} (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n))
    {e : G} {A A' : GL (Fin n) K} (hA : (e, A) ∈ suPairs ψ) (hA' : (e, A') ∈ suPairs ψ) :
    ∃ c : Kˣ, A' = Matrix.GeneralLinearGroup.scalar (Fin n) c * A := by
  have h1 := (suPairs ψ).mul_mem ((suPairs ψ).inv_mem hA) hA'
  rw [Prod.inv_mk, Prod.mk_mul_mk, inv_mul_cancel] at h1
  obtain ⟨c, hc⟩ := exists_scalar_of_mem_suPairs_one h hn hnq hp hpq hker h1
  refine ⟨c, ?_⟩
  rw [TypeA.PGLTor.scalar_mul_comm, ← hc, mul_inv_cancel_left]

variable (ψ : ↥(unitarySU 2 f K n) →* G) in
@[expose] def inducedMatrices (E : Subgroup G) : Subgroup (GL (Fin n) K) :=
  ((E.prod ⊤) ⊓ suPairs ψ).map (MonoidHom.snd G (GL (Fin n) K))

theorem mem_inducedMatrices {ψ : ↥(unitarySU 2 f K n) →* G} {E : Subgroup G}
    {A : GL (Fin n) K} : A ∈ inducedMatrices ψ E ↔ ∃ e ∈ E, (e, A) ∈ suPairs ψ := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x.1, (Subgroup.mem_prod.mp (Subgroup.mem_inf.mp hx).1).1, (Subgroup.mem_inf.mp hx).2⟩
  · rintro ⟨e, he, hA⟩
    exact ⟨(e, A), Subgroup.mem_inf.mpr ⟨Subgroup.mem_prod.mpr ⟨he, Subgroup.mem_top A⟩, hA⟩, rfl⟩

theorem isProjElem_inducedMatrices (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (3, 2)) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1)
    {ψ : ↥(unitarySU 2 f K n) →* G} (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n))
    {E : Subgroup G} (hE : IsElemAbelian p E) :
    TypeA.PGLTor.IsProjElem p (inducedMatrices ψ E) where
  scalar_mem u := mem_inducedMatrices.mpr ⟨1, E.one_mem, one_scalar_mem_suPairs ψ u⟩
  pow_scalar g hg := by
    obtain ⟨e, he, hge⟩ := mem_inducedMatrices.mp hg
    have h1 := (suPairs ψ).pow_mem hge p
    rw [Prod.pow_mk, hE.2 e he] at h1
    exact exists_scalar_of_mem_suPairs_one h hn hnq hp hpq hker h1
  comm_scalar g hg k hk := by
    obtain ⟨e, he, hge⟩ := mem_inducedMatrices.mp hg
    obtain ⟨e', he', hke'⟩ := mem_inducedMatrices.mp hk
    have hc : e * e' = e' * e := congrArg Subtype.val (hE.1.is_comm.comm ⟨e, he⟩ ⟨e', he'⟩)
    have h1 := (suPairs ψ).mul_mem ((suPairs ψ).mul_mem hge hke')
      ((suPairs ψ).inv_mem ((suPairs ψ).mul_mem hke' hge))
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.inv_mk, Prod.mk_mul_mk, hc, mul_inv_cancel] at h1
    obtain ⟨u, hu⟩ := exists_scalar_of_mem_suPairs_one h hn hnq hp hpq hker h1
    exact ⟨u, by rw [← hu, inv_mul_cancel_right]⟩

theorem card_inducedMatrices (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (3, 2)) {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ f + 1)
    {ψ : ↥(unitarySU 2 f K n) →* G} (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n))
    {E : Subgroup G} (hEA : ∀ e ∈ E, ∃ A, (e, A) ∈ suPairs ψ)
    (hEC : E ⊓ Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    Nat.card (inducedMatrices ψ E) = Nat.card E * (Nat.card K - 1) := by
  have : Finite K := h.finite
  have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  set P := (E.prod ⊤) ⊓ suPairs ψ with hP
  set g := (MonoidHom.snd G (GL (Fin n) K)).comp P.subtype with hg
  have hginj : Function.Injective g := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ hx1
    have hx2 : x.2 = 1 := hx1
    have hxP := Subgroup.mem_inf.mp hx
    have h1 : (x.1, (1 : GL (Fin n) K)) ∈ suPairs ψ := by
      rw [← hx2]
      exact hxP.2
    have h3 : x.1 ∈ E ⊓ Subgroup.centralizer (ψ.range : Set G) :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_prod.mp hxP.1).1, mem_centralizer_of_mem_suPairs_one h1⟩
    rw [hEC, Subgroup.mem_bot] at h3
    exact Subtype.ext (Prod.ext h3 hx2)
  have hgr : g.range = inducedMatrices ψ E := by
    rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
    rfl
  have h1 : Nat.card P = Nat.card (inducedMatrices ψ E) := by
    rw [← hgr]
    exact Nat.card_congr (MonoidHom.ofInjective hginj).toEquiv
  set k := (MonoidHom.fst G (GL (Fin n) K)).comp P.subtype with hk
  have hkr : k.range = E := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (Subgroup.mem_prod.mp (Subgroup.mem_inf.mp x.2).1).1
    · intro e he
      obtain ⟨A, hA⟩ := hEA e he
      exact ⟨⟨(e, A), Subgroup.mem_inf.mpr ⟨Subgroup.mem_prod.mpr ⟨he, Subgroup.mem_top A⟩, hA⟩⟩,
        rfl⟩
  have hkk : Nat.card k.ker = Nat.card Kˣ := by
    symm
    refine Nat.card_eq_of_bijective (fun u => ⟨⟨(1, Matrix.GeneralLinearGroup.scalar (Fin n) u),
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_prod.mpr ⟨E.one_mem, Subgroup.mem_top _⟩,
        one_scalar_mem_suPairs ψ u⟩⟩, rfl⟩) ⟨fun u v huv => ?_, fun x => ?_⟩
    · have h2 := congrArg (fun y : k.ker => ((y : P) : G × GL (Fin n) K).2) huv
      exact TypeA.PGLTor.scalar_injective h2
    · obtain ⟨⟨⟨e, A⟩, hx⟩, hxk⟩ := x
      have he : e = 1 := hxk
      subst he
      obtain ⟨u, hu⟩ := exists_scalar_of_mem_suPairs_one h hn hnq hp hpq hker
        (Subgroup.mem_inf.mp hx).2
      subst hu
      exact ⟨u, rfl⟩
  rw [← h1, ← Subgroup.card_ker_mul_card_range k, hkr, hkk, Nat.card_units, mul_comm]

theorem dvd_card_sub_one (h : UnitaryFieldData 2 f K) {p : ℕ} (hpq : p ∣ 2 ^ f + 1) :
    p ∣ Nat.card K - 1 := by
  rw [h.card_eq_sq]
  have h3 : 2 ^ f * 2 ^ f - 1 = (2 ^ f + 1) * (2 ^ f - 1) := by
    have := Nat.mul_self_sub_mul_self_eq (2 ^ f) 1
    simpa using this
  rw [sq, h3]
  exact Dvd.dvd.mul_right hpq _

theorem isToral_inducedMatrices (h : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    (hnq : (n, 2 ^ f) ≠ (3, 2)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ f + 1)
    {ψ : ↥(unitarySU 2 f K n) →* G} (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 f K n))
    {E : Subgroup G} (hE : IsElemAbelian p E) (hbig : p ^ (n / p + 1) < Nat.card E)
    (hEA : ∀ e ∈ E, ∃ A, (e, A) ∈ suPairs ψ)
    (hEC : E ⊓ Subgroup.centralizer (ψ.range : Set G) = ⊥) :
    TypeA.PGLTor.IsToral (inducedMatrices ψ E) := by
  have : Finite K := h.finite
  rcases TypeA.PGLTor.toral_or_card_le hp hp2 (dvd_card_sub_one h hpq)
    (isProjElem_inducedMatrices h hn hnq hp hpq hker hE) with hT | hle
  · exact hT
  · exfalso
    rw [card_inducedMatrices h hn hnq hp hpq hker hEA hEC, Fintype.card_fin] at hle
    have hK1 : 0 < Nat.card K - 1 := by
      have := Finite.one_lt_card (α := K)
      omega
    have := Nat.le_of_mul_le_mul_right hle hK1
    omega

end SUTorus

end CFSG.StandardType
