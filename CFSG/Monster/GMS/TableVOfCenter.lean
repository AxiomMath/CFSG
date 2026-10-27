module

public import CFSG.Monster.GMS.TableVOfCentralizer

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

section Model

variable {H : Type*} [Group H]

namespace TableVOf

theorem factorization_tableVOrderZ : tableVOrderZ.factorization 2 = 42 := by
  have : tableVOrderZ = 2 ^ 42 * (3 ^ 6 * 5 ^ 3 * 7 * 11 * 23) := by
    unfold tableVOrderZ
    ring
  rw [this, Nat.factorization_mul (by positivity) (by positivity), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), smul_eq_mul, mul_one, add_zero]

theorem tableVOrderZ_ne_twoBabyOrder : tableVOrderZ ≠ twoBabyOrder := by
  unfold tableVOrderZ twoBabyOrder
  norm_num

theorem exists_card_two_pow_of_mem [Finite H] {K : Subgroup H} {c : H} (hcK : c ∈ K)
    (hc : orderOf c = 2) {n : ℕ} (hn : (Nat.card K).factorization 2 = n) :
    ∃ T : Subgroup H, T ≤ K ∧ c ∈ T ∧ Nat.card T = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 (Subgroup.zpowers (⟨c, hcK⟩ : K)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hc, pow_one]
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  refine ⟨(Q : Subgroup K).map K.subtype, Subgroup.map_subtype_le _,
    ⟨⟨c, hcK⟩, hQ (Subgroup.mem_zpowers _), rfl⟩, ?_⟩
  rw [Subgroup.card_map_of_injective K.subtype_injective, Sylow.card_eq_multiplicity, hn]

theorem eq_of_forall_commute [Finite H] {a b z u : H} (hV : TableV a b z u) {c : H}
    (hc : c ∈ Subgroup.centralizer ({a} : Set H))
    (hcen : ∀ g ∈ Subgroup.centralizer ({a} : Set H), g * c = c * g) (hc2 : orderOf c = 2) :
    c = a := by
  obtain ⟨-, hz, -, -, -, -, -, -, -, -, hC, -, hcz, -, hsyl⟩ := hV
  have hcK : c ∈ Subgroup.centralizer ({a} : Set H) ⊓ Subgroup.centralizer {z} :=
    ⟨hc, Subgroup.mem_centralizer_singleton_iff.mpr (hcen z hz).symm⟩
  obtain ⟨T, hTK, hcT, hTcard⟩ := exists_card_two_pow_of_mem hcK hc2 (n := 42)
    (by rw [hcz]; exact factorization_tableVOrderZ)
  have key := (hsyl T hTK hTcard c).mp ⟨hcT, fun s hs => (hcen s (hTK hs).1).symm⟩
  have hzcen : (∀ g ∈ Subgroup.centralizer ({a} : Set H), g * z = z * g) → False := by
    intro h
    have hle : Subgroup.centralizer ({a} : Set H) ≤ Subgroup.centralizer {z} := fun g hg =>
      Subgroup.mem_centralizer_singleton_iff.mpr (h g hg)
    refine tableVOrderZ_ne_twoBabyOrder ?_
    rw [← hcz, ← hC, inf_eq_left.mpr hle]
  rcases key with h1 | h1 | h1 | h1
  · exact absurd h1 (ne_one_of_orderOf hc2)
  · exact h1
  · subst h1
    exact (hzcen hcen).elim
  · subst h1
    refine (hzcen fun g hg => ?_).elim
    have h2 := hcen g hg
    have h3 : g * a = a * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    refine mul_left_cancel (a := a) ?_
    calc a * (g * z) = (a * g) * z := by rw [mul_assoc]
      _ = (g * a) * z := by rw [h3]
      _ = g * (a * z) := by rw [mul_assoc]
      _ = (a * z) * g := h2
      _ = a * (z * g) := by rw [mul_assoc]

theorem mul_selfMem_comm {G : Type*} [Group G] {a : G} (x : Subgroup.centralizer ({a} : Set G)) :
    x * selfMem a = selfMem a * x :=
  Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.2)

end TableVOf

theorem TableV.centralizerMulEquiv_apply_eq [Finite H] {a₀ b₀ z₀ u₀ : H}
    (hV : TableV a₀ b₀ z₀ u₀) {G : Type*} [Group G] {a : G} (ha : orderOf a = 2)
    (φ : Subgroup.centralizer ({a₀} : Set H) ≃* Subgroup.centralizer ({a} : Set G))
    (c : Subgroup.centralizer ({a₀} : Set H)) (hc : (c : H) = a₀) : (φ c : G) = a := by
  have hdcen : ∀ g ∈ Subgroup.centralizer ({a₀} : Set H),
      g * ((φ.symm (TableVOf.selfMem a) : Subgroup.centralizer ({a₀} : Set H)) : H) =
        ((φ.symm (TableVOf.selfMem a) : Subgroup.centralizer ({a₀} : Set H)) : H) * g := by
    intro g hg
    have h1 : (⟨g, hg⟩ : Subgroup.centralizer ({a₀} : Set H)) * φ.symm (TableVOf.selfMem a) =
        φ.symm (TableVOf.selfMem a) * ⟨g, hg⟩ := by
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact TableVOf.mul_selfMem_comm (φ ⟨g, hg⟩)
    exact congrArg Subtype.val h1
  have hd2 : orderOf ((φ.symm (TableVOf.selfMem a) : Subgroup.centralizer ({a₀} : Set H)) : H) =
      2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe,
      TableVOf.coe_selfMem]
    exact ha
  have hda := TableVOf.eq_of_forall_commute hV (φ.symm (TableVOf.selfMem a)).2 hdcen hd2
  have hcd : c = φ.symm (TableVOf.selfMem a) := Subtype.ext (hc.trans hda.symm)
  rw [hcd, MulEquiv.apply_symm_apply]
  rfl

end Model

end CFSG.Monster.GMS
