module

public import CFSG.Quasithin.Recognition.J2RecLocal
public import CFSG.Quasithin.EmptyFaithful.SzI47J2NoA4Gen

public section

namespace CFSG.Quasithin.SzI47J2NoA4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem eq_one_of_commute_of_pow_five : ∀ σ : Equiv.Perm (Fin 5), σ ≠ 1 → σ ^ 5 = 1 →
    ∀ τ : Equiv.Perm (Fin 5), σ * τ = τ * σ → τ * τ = 1 → τ = 1 := by
  decide +kernel

theorem orderOf_dvd_card_of_mem {Γ : Type*} [Group Γ] (C : Subgroup Γ) {x : Γ} (hx : x ∈ C) :
    orderOf x ∣ Nat.card C := by
  have h := orderOf_dvd_natCard (⟨x, hx⟩ : ↥C)
  rwa [← Subgroup.orderOf_coe (⟨x, hx⟩ : ↥C)] at h

variable {G : Type} [Group G] [Finite G] {z : G}

theorem exists_orderOf_eq_five (hH : IsTypeH2 G z) :
    ∃ g : G, g ∈ Subgroup.centralizer ({z} : Set G) ∧ orderOf g = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({z} : Set G)) 5
    (by rw [hH.card_centralizer]; norm_num)
  exact ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx⟩

omit [Finite G] in
theorem not_mem_pCoreOf_of_orderOf_eq_five (hH : IsTypeH2 G z) {g : G} (hg5 : orderOf g = 5)
    (hgQ : g ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G))) : False := by
  have h := orderOf_dvd_card_of_mem _ hgQ
  rw [hg5, hH.card_pCoreOf] at h
  omega

theorem card_pCoreOf_inf_centralizer (hH : IsTypeH2 G z) {g : G}
    (hgH : g ∈ Subgroup.centralizer ({z} : Set G)) (hg5 : orderOf g = 5) :
    Nat.card ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ⊓
      Subgroup.centralizer ({g} : Set G)) = 2 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hP : IsPGroup 5 (Subgroup.zpowers g) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hg5, pow_one])
  set Q := pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) with hQ
  have hS : ∀ k ∈ Subgroup.zpowers g, ∀ x ∈ (Q : Set G), k * x * k⁻¹ ∈ (Q : Set G) := by
    intro k hk x hx
    have hkH : k ∈ Subgroup.centralizer ({z} : Set G) := Subgroup.zpowers_le.2 hgH hk
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hkH) x).mp hx
  have hmod := card_modEq_card_fixed 5 (Subgroup.zpowers g) hP (Q : Set G) hS
  have hfix : {x : G | x ∈ (Q : Set G) ∧ ∀ k ∈ Subgroup.zpowers g, k * x = x * k} =
      ((Q ⊓ Subgroup.centralizer ({g} : Set G) : Subgroup G) : Set G) := by
    ext x
    constructor
    · rintro ⟨hxQ, hc⟩
      exact ⟨hxQ, Subgroup.mem_centralizer_singleton_iff.mpr (hc g (Subgroup.mem_zpowers g)).symm⟩
    · rintro ⟨hxQ, hxc⟩
      refine ⟨hxQ, fun k hk => ?_⟩
      have hg : g ∈ Subgroup.centralizer ({x} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp hxc).symm
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.zpowers_le.2 hg hk)
  rw [hfix] at hmod
  have h32 : Nat.card (Q : Set G) = 32 := hH.card_pCoreOf
  have hc : Nat.card (((Q ⊓ Subgroup.centralizer ({g} : Set G) : Subgroup G)) : Set G) =
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({g} : Set G)) := rfl
  rw [h32, hc] at hmod
  have hdvd : Nat.card ↥(Q ⊓ Subgroup.centralizer ({g} : Set G)) ∣ 32 := by
    rw [← hH.card_pCoreOf]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hne : Nat.card ↥(Q ⊓ Subgroup.centralizer ({g} : Set G)) ≠ 32 := by
    intro h
    have heq : Q ⊓ Subgroup.centralizer ({g} : Set G) = Q :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hH.card_pCoreOf, h])
    have hQC : Q ≤ Subgroup.centralizer ({g} : Set G) := inf_eq_left.mp heq
    have hgc : g ∈ Subgroup.centralizer (Q : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun q hq =>
        Subgroup.mem_centralizer_singleton_iff.mp (hQC hq)
    have hCT : Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer (Q : Set G) ≤ Q :=
      hH.charTwo
    exact not_mem_pCoreOf_of_orderOf_eq_five hH hg5 (hCT ⟨hgH, hgc⟩)
  have hle : Nat.card ↥(Q ⊓ Subgroup.centralizer ({g} : Set G)) ≤ 32 :=
    Nat.le_of_dvd (by norm_num) hdvd
  have hmod' : 32 % 5 = Nat.card ↥(Q ⊓ Subgroup.centralizer ({g} : Set G)) % 5 := hmod
  generalize Nat.card ↥(Q ⊓ Subgroup.centralizer ({g} : Set G)) = c at hdvd hne hle hmod' ⊢
  interval_cases c <;> omega

omit [Finite G] in
theorem mem_pCoreOf_of_commute (hH : IsTypeH2 G z) {g w : G}
    (hgH : g ∈ Subgroup.centralizer ({z} : Set G)) (hg5 : orderOf g = 5)
    (hwH : w ∈ Subgroup.centralizer ({z} : Set G)) (hwg : w * g = g * w) (hw2 : w * w = 1) :
    w ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) := by
  obtain ⟨e⟩ := hH.quot
  set H := Subgroup.centralizer ({z} : Set G) with hHdef
  let π : ↥H →* alternatingGroup (Fin 5) :=
    (e : OTwoQuot H →* alternatingGroup (Fin 5)).comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))
  have hker : ∀ x : ↥H, π x = 1 → (x : G) ∈ pCoreOf 2 H := by
    intro x hx
    have h1 : (QuotientGroup.mk x : OTwoQuot H) = 1 :=
      e.injective (hx.trans (map_one e).symm)
    exact ⟨x, (QuotientGroup.eq_one_iff x).mp h1, rfl⟩
  have hσ1 : π ⟨g, hgH⟩ ≠ 1 := fun h => not_mem_pCoreOf_of_orderOf_eq_five hH hg5 (hker _ h)
  have hσ5 : π ⟨g, hgH⟩ ^ 5 = 1 := by
    rw [← map_pow]
    have h5 : (⟨g, hgH⟩ : ↥H) ^ 5 = 1 :=
      Subtype.ext (by rw [← hg5]; exact pow_orderOf_eq_one g)
    rw [h5, map_one]
  have hcomm : π ⟨g, hgH⟩ * π ⟨w, hwH⟩ = π ⟨w, hwH⟩ * π ⟨g, hgH⟩ := by
    rw [← map_mul, ← map_mul]
    exact congrArg π (Subtype.ext hwg.symm)
  have hτ2 : π ⟨w, hwH⟩ * π ⟨w, hwH⟩ = 1 := by
    rw [← map_mul]
    have h2 : (⟨w, hwH⟩ : ↥H) * ⟨w, hwH⟩ = 1 := Subtype.ext hw2
    rw [h2, map_one]
  have key := eq_one_of_commute_of_pow_five (π ⟨g, hgH⟩ : Equiv.Perm (Fin 5))
    (fun h => hσ1 (Subtype.ext h))
    (by simpa using congrArg Subtype.val hσ5) (π ⟨w, hwH⟩ : Equiv.Perm (Fin 5))
    (by simpa using congrArg Subtype.val hcomm) (by simpa using congrArg Subtype.val hτ2)
  exact hker _ (Subtype.ext key)

theorem eq_one_or_eq_of_commute (hH : IsTypeH2 G z) {g w : G}
    (hgH : g ∈ Subgroup.centralizer ({z} : Set G)) (hg5 : orderOf g = 5)
    (hwz : w * z = z * w) (hwg : w * g = g * w) (hw2 : w * w = 1) : w = 1 ∨ w = z := by
  have hwH : w ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hwz
  have hwQ : w ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) :=
    mem_pCoreOf_of_commute hH hgH hg5 hwH hwg hw2
  have hcard := card_pCoreOf_inf_centralizer hH hgH hg5
  have hzD : z ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ⊓
      Subgroup.centralizer ({g} : Set G) :=
    ⟨hH.z_mem_pCoreOf, Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hgH).symm⟩
  have hwD : w ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ⊓
      Subgroup.centralizer ({g} : Set G) :=
    ⟨hwQ, Subgroup.mem_centralizer_singleton_iff.mpr hwg⟩
  obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(pCoreOf 2 (Subgroup.centralizer
    ({z} : Set G)) ⊓ Subgroup.centralizer ({g} : Set G)))).mp hcard
  by_cases hw1 : w = 1
  · exact Or.inl hw1
  · right
    have h1 := huniq ⟨w, hwD⟩ (fun h => hw1 (congrArg Subtype.val h))
    have h2 := huniq ⟨z, hzD⟩ (fun h => hH.ne_one (congrArg Subtype.val h))
    exact congrArg Subtype.val (h1.trans h2.symm)

end CFSG.Quasithin.SzI47J2NoA4
