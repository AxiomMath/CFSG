module

public import CFSG.Sporadic.Schreier.TitsInv
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LieType.Ree.SuzukiOvoidAction
public import CFSG.LieType.Ree.SuzukiOrder

public noncomputable section

namespace CFSG.Sporadic.Schreier.Tits

open CFSG.Blueprint CFSG.LieType.Ree

theorem not_isQuasisimple_of_solvable (Q : Type*) [Group Q] [Group.IsSolvable Q] :
    ¬ CFSG.IsQuasisimple Q := by
  rintro ⟨hperf, -, a, b, hab⟩
  have htop : ∀ n, derivedSeries Q n = ⊤ := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [derivedSeries_succ, ih, ← commutator_def, hperf.commutator_eq_top]
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := Q)
  rw [htop n] at hn
  have hsub : Subsingleton Q := by
    constructor
    intro x y
    have hx : x ∈ (⊥ : Subgroup Q) := hn ▸ Subgroup.mem_top x
    have hy : y ∈ (⊥ : Subgroup Q) := hn ▸ Subgroup.mem_top y
    rw [Subgroup.mem_bot] at hx hy
    rw [hx, hy]
  apply hab
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  rw [Subsingleton.elim a b]

theorem not_isComponent_of_solvable {G : Type*} [Group G] (L : Subgroup G)
    (hL : Group.IsSolvable L) : ¬ CFSG.IsComponent L :=
  fun h => not_isQuasisimple_of_solvable L h.1

@[expose] def HasTwoCore (G : Type*) [Group G] : Prop :=
  ∃ J : Subgroup G, J.Normal ∧ IsPGroup 2 J ∧ Subgroup.centralizer (J : Set G) ≤ J

theorem HasTwoCore.of_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : HasTwoCore H) : HasTwoCore G := by
  obtain ⟨J, hJ, hJ2, hJC⟩ := h
  refine ⟨J.map e.symm.toMonoidHom, hJ.map _ e.symm.surjective,
    hJ2.of_equiv (J.equivMapOfInjective _ e.symm.injective), fun g hg => ?_⟩
  have he : e g ∈ Subgroup.centralizer (J : Set H) := by
    rw [Subgroup.mem_centralizer_iff] at hg ⊢
    intro y hy
    have := hg (e.symm y) ⟨y, hy, rfl⟩
    have := congrArg e this
    simpa using this
  exact ⟨e g, hJC he, by simp⟩

theorem not_isComponent_of_hasTwoCore {G : Type*} [Group G] [Finite G] (h : HasTwoCore G)
    (L : Subgroup G) : ¬ CFSG.IsComponent L := by
  intro hL
  obtain ⟨J, hJ, hJ2, hJC⟩ := h
  have hle : L ≤ J := by
    rcases CFSG.LocalCores.component_normal_subgroup hL hJ with h | h
    · exact h
    · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h).trans hJC
  have hL2 : IsPGroup 2 L := hJ2.to_le hle
  have : Group.IsNilpotent L := hL2.isNilpotent
  exact not_isComponent_of_solvable L inferInstance hL

theorem hasTwoCore_titsH :
    HasTwoCore titsH :=
  have := AT_Tits_intrinsic_local_pair.2.2.2.2.2.2.1
  ⟨titsJ.subgroupOf titsH, this,
    IsPGroup.of_card (n := 9)
      (by rw [card_subgroupOf_eq titsJ_le_titsH, titsQJ_facts.2.2.2]; norm_num),
    centralizer_subgroupOf_le titsJ_le_titsH CHJ_le_J⟩

theorem hasTwoCore_titsCt :
    HasTwoCore titsCt :=
  ⟨titsQ.subgroupOf titsCt, titsQ_normal,
    IsPGroup.of_card (n := 8) (by rw [card_subgroupOf_eq inf_le_left, card_titsQ]; norm_num),
    centralizer_subgroupOf_le inf_le_left titsCCQ_le⟩

theorem hasTwoCore_centralizer_of_conj {x y : titsD} (h : IsConj y x)
    (hy : HasTwoCore (Subgroup.centralizer {y})) : HasTwoCore (Subgroup.centralizer {x}) := by
  obtain ⟨g, hg⟩ := isConj_iff.1 h
  have e : Subgroup.centralizer {y} ≃* Subgroup.centralizer {x} :=
    ((Subgroup.centralizer {y}).equivMapOfInjective _ (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr (by rw [map_conj_centralizer, hg]))
  exact hy.of_equiv e.symm

theorem hasTwoCore_centralizer_of_map_eq {y : titsD} {X : Subgroup (Equiv.Perm (Fin 1755))}
    (hX : titsD ⊓ Subgroup.centralizer {(y : Equiv.Perm (Fin 1755))} = X) (h : HasTwoCore X) :
    HasTwoCore (Subgroup.centralizer {y}) :=
  h.of_equiv (((Subgroup.centralizer {y}).equivMapOfInjective _ titsD.subtype_injective).trans
    (MulEquiv.subgroupCongr (by rw [map_subtype_centralizer, hX])))

theorem titsD_involution_centralizer_component_free
    (x : titsD) (hx : orderOf x = 2)
    (L : Subgroup (Subgroup.centralizer {x})) : ¬ CFSG.IsComponent L := by
  have hz : HasTwoCore (Subgroup.centralizer {titsZD}) :=
    hasTwoCore_centralizer_of_map_eq titsD_centralizer_z hasTwoCore_titsH
  have ht : HasTwoCore (Subgroup.centralizer {titsTD}) :=
    hasTwoCore_centralizer_of_map_eq titsD_centralizer_t.1.symm hasTwoCore_titsCt
  rcases titsD_involution_conj x hx with h | h
  · exact not_isComponent_of_hasTwoCore (hasTwoCore_centralizer_of_conj h hz) L
  · exact not_isComponent_of_hasTwoCore (hasTwoCore_centralizer_of_conj h ht) L

section Suzuki

variable {a : ℕ} {K : Type} [Field K] [Finite K]

theorem suzukiU_isSylow (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    IsPGroup 2 (suzukiU a K) ∧ ¬ 2 ∣ (suzukiU a K).index := by
  have hU := (suzuki_unipotent_structure hK).2.1
  have hG := suzuki_order hK
  set q := 2 ^ (2 * a + 1) with hq
  refine ⟨IsPGroup.of_card (n := 2 * (2 * a + 1)) (by rw [hU, hq, ← pow_mul]; ring_nf), ?_⟩
  have hidx := Subgroup.card_mul_index (suzukiU a K)
  rw [hU, hG, mul_assoc] at hidx
  have hq0 : 0 < q ^ 2 := by positivity
  have hidx' : (suzukiU a K).index = (q - 1) * (q ^ 2 + 1) :=
    Nat.eq_of_mul_eq_mul_left hq0 hidx
  rw [hidx']
  have hev : Even q := by rw [hq]; exact Nat.even_pow.2 ⟨even_two, by omega⟩
  have hq1 : 1 ≤ q := Nat.one_le_two_pow
  have h1 : Odd (q - 1) := by
    obtain ⟨r, hr⟩ := hev
    exact ⟨r - 1, by omega⟩
  have h2 : Odd (q ^ 2 + 1) := (hev.pow_of_ne_zero (n := 2) two_ne_zero).add_one
  rw [← even_iff_two_dvd, Nat.not_even_iff_odd]
  exact h1.mul h2

theorem centralizer_le_suzukiB
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {u : suzukiGroup a K}
    (hu : u ∈ suzukiU a K) (hu1 : u ≠ 1) : Subgroup.centralizer {u} ≤ suzukiB a K := by
  intro c hc
  rw [← (suzuki_ovoid_stabilizer hK).1, MulAction.mem_stabilizer_iff]
  have hcu : c * u = u * c := Subgroup.mem_centralizer_singleton_iff.1 hc
  have huB : u ∈ MulAction.stabilizer (suzukiGroup a K) (suzukiInfty K) :=
    suzukiB_le_stabilizer hK (le_sup_left (a := suzukiU a K) hu)
  rw [MulAction.mem_stabilizer_iff] at huB
  have hfix : u • (c • suzukiInfty K) = c • suzukiInfty K := by
    rw [← mul_smul, ← hcu, mul_smul, huB]
  by_contra hne
  have hmem : c • suzukiInfty K ∈ suzukiOmega a K \ {suzukiInfty K} :=
    ⟨suzuki_smul_mem_suzukiOmega hK c (suzukiInfty_mem_suzukiOmega a K), hne⟩
  obtain ⟨g, -, huniq⟩ := (suzuki_ovoid_unipotent_action hK).2.2.2.2.2.1 _ hmem _ hmem
  have h1 := huniq ⟨u, hu⟩ hfix
  have h2 := huniq 1 (one_smul _ _)
  exact hu1 (congrArg Subtype.val (h1.trans h2.symm))

theorem suzuki_involution_centralizer_solvable
    (hK : Nat.card K = 2 ^ (2 * a + 1))
    (t : suzukiGroup a K) (ht : orderOf t = 2) : Group.IsSolvable (Subgroup.centralizer {t}) := by
  obtain ⟨hU2, hUidx⟩ := suzukiU_isSylow hK
  obtain ⟨g, hg⟩ := exists_conj_mem_sylow (hU2.toSylow hUidx) (isPGroup_zpowers_of_orderOf_two ht)
  rw [IsPGroup.toSylow_coe] at hg
  have hne : g * t * g⁻¹ ≠ 1 := by
    intro h
    have : t = 1 := by
      calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
        _ = 1 := by rw [h, mul_one, inv_mul_cancel]
    rw [this, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hle := centralizer_le_suzukiB hK hg hne
  have hB := (suzuki_borel_solvable hK).1
  have hsolv : Group.IsSolvable (Subgroup.centralizer {g * t * g⁻¹}) :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have e : Subgroup.centralizer {t} ≃* Subgroup.centralizer {g * t * g⁻¹} :=
    ((Subgroup.centralizer {t}).equivMapOfInjective _ (MulAut.conj g).injective).trans
      (MulEquiv.subgroupCongr (map_conj_centralizer g t))
  exact Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective

end Suzuki

theorem CTI_Suzuki_Tits_involution_centralizers_component_free :
    (∀ (a : ℕ) (k : Type) [Field k] [Finite k], Nat.card k = 2 ^ (2 * a + 1) →
      ∀ t : suzukiGroup a k, orderOf t = 2 →
        ∀ L : Subgroup (Subgroup.centralizer {t}), ¬ CFSG.IsComponent L) ∧
    (∀ t : titsD, orderOf t = 2 →
      ∀ L : Subgroup (Subgroup.centralizer {t}), ¬ CFSG.IsComponent L) := by
  refine ⟨fun a k _ _ hk t ht L => ?_, titsD_involution_centralizer_component_free⟩
  have := suzuki_involution_centralizer_solvable hk t ht
  exact not_isComponent_of_solvable L inferInstance

end CFSG.Sporadic.Schreier.Tits
