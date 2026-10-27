module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore

public section

namespace CFSG.RankThree.PartOne.Sec9B

open CFSG Subgroup CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem mem_normalizer_of_forall_conj_mem {K : Subgroup G} {g : G}
    (h1 : ∀ x ∈ K, g * x * g⁻¹ ∈ K) (h2 : ∀ x ∈ K, g⁻¹ * x * g ∈ K) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  simpa [mul_assoc] using this

theorem mem_normalizer_iSup {ι : Sort*} {M : ι → Subgroup G} {g : G}
    (h : ∀ i, g ∈ Subgroup.normalizer (M i : Set G)) :
    g ∈ Subgroup.normalizer ((⨆ i, M i : Subgroup G) : Set G) := by
  apply SteinbergBY.mem_normalizer_of_map_conj_eq
  rw [Subgroup.map_iSup]
  exact iSup_congr fun i => SteinbergBY.map_conj_eq_of_mem_normalizer (h i)

theorem conj_mem_centralizer_of_mem_normalizer {S : Subgroup G} {g h : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) (hh : h ∈ Subgroup.centralizer (S : Set G)) :
    g * h * g⁻¹ ∈ Subgroup.centralizer (S : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hs' : g⁻¹ * s * g ∈ S := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) s).mp hs
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hh _ hs'
  calc s * (g * h * g⁻¹) = g * ((g⁻¹ * s * g) * h) * g⁻¹ := by group
    _ = g * (h * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
    _ = g * h * g⁻¹ * s := by group

theorem mem_normalizer_centralizer_of_mem_normalizer {S : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) :=
  mem_normalizer_of_forall_conj_mem (fun _ hx => conj_mem_centralizer_of_mem_normalizer hg hx)
    (fun _ hx => by simpa using conj_mem_centralizer_of_mem_normalizer (inv_mem hg) hx)

theorem normalizer_zpowers_le_normalizer_centralizer (b : G) :
    Subgroup.normalizer (Subgroup.zpowers b : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer ({b} : Set G) : Set G) := by
  intro g hg
  rw [SteinbergBY.centralizer_singleton_eq_centralizer_zpowers]
  exact mem_normalizer_centralizer_of_mem_normalizer hg

theorem commutator_le_centralizer_of_centralizes {M X Y : Subgroup G}
    (hY : Y ≤ Subgroup.normalizer (M : Set G))
    (hXC : X ≤ Subgroup.centralizer (M : Set G)) : ⁅Y, X⁆ ≤ Subgroup.centralizer (M : Set G) := by
  rw [Subgroup.commutator_le]
  intro y hy x hx
  refine Subgroup.mem_centralizer_iff.mpr fun m hm => ?_
  have hxc : ∀ n ∈ M, n * x = x * n := Subgroup.mem_centralizer_iff.mp (hXC hx)
  have hm1 : y⁻¹ * m * y ∈ M := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem (hY hy)) m).mp hm
    simpa using this
  have h1 := hxc _ hm1
  have h2 := hxc m hm
  have e1 : m = y * (y⁻¹ * m * y) * y⁻¹ := by group
  calc m * ⁅y, x⁆ = y * ((y⁻¹ * m * y) * x) * y⁻¹ * x⁻¹ := by
        simp only [commutatorElement_def]
        conv_lhs => rw [e1]
        group
    _ = y * (x * (y⁻¹ * m * y)) * y⁻¹ * x⁻¹ := by rw [h1]
    _ = ⁅y, x⁆ * m := by
        simp only [commutatorElement_def]
        have : x⁻¹ * m = m * x⁻¹ := by
          calc x⁻¹ * m = x⁻¹ * (m * x) * x⁻¹ := by group
            _ = x⁻¹ * (x * m) * x⁻¹ := by rw [h2]
            _ = m * x⁻¹ := by group
        calc y * (x * (y⁻¹ * m * y)) * y⁻¹ * x⁻¹
            = y * x * y⁻¹ * (m * x⁻¹) := by group
          _ = y * x * y⁻¹ * (x⁻¹ * m) := by rw [this]
          _ = _ := by group

@[expose] def conjClosure (L E : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | ∃ l ∈ L, ∃ e ∈ E, x = l⁻¹ * e * l}

theorem le_conjClosure (L E : Subgroup G) : E ≤ conjClosure L E := fun e he =>
  Subgroup.subset_closure ⟨1, Subgroup.one_mem _, e, he, by simp⟩

theorem conjClosure_le_of_le {L E : Subgroup G} (hEL : E ≤ L) : conjClosure L E ≤ L := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨l, hl, e, he, rfl⟩
  exact L.mul_mem (L.mul_mem (L.inv_mem hl) (hEL he)) hl

theorem conjClosure_le {L E M : Subgroup G} (hEM : E ≤ M)
    (hLM : L ≤ Subgroup.normalizer (M : Set G)) : conjClosure L E ≤ M := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro _ ⟨l, hl, e, he, rfl⟩
  have := (Subgroup.mem_normalizer_iff.mp (hLM (L.inv_mem hl)) e).mp (hEM he)
  simpa using this

theorem conj_mem_conjClosure_of_mem {L E : Subgroup G} {g : G} (hg : g ∈ L) {x : G}
    (hx : x ∈ conjClosure L E) : g * x * g⁻¹ ∈ conjClosure L E := by
  have : conjClosure L E ≤ (conjClosure L E).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨l, hl, e, he, rfl⟩
    refine Subgroup.mem_comap.mpr (Subgroup.subset_closure ⟨l * g⁻¹, L.mul_mem hl (L.inv_mem hg),
      e, he, ?_⟩)
    simp [mul_assoc]
  exact this hx

theorem le_normalizer_conjClosure (L E : Subgroup G) :
    L ≤ Subgroup.normalizer (conjClosure L E : Set G) := fun g hg =>
  mem_normalizer_of_forall_conj_mem (fun _ hx => conj_mem_conjClosure_of_mem hg hx)
    (fun _ hx => by simpa using conj_mem_conjClosure_of_mem (L.inv_mem hg) hx)

theorem mem_normalizer_conjClosure_of_normalizes {L E : Subgroup G} {g : G}
    (hgL : g ∈ Subgroup.normalizer (L : Set G)) (hgE : g ∈ Subgroup.normalizer (E : Set G)) :
    g ∈ Subgroup.normalizer (conjClosure L E : Set G) := by
  have key : ∀ {g : G}, g ∈ Subgroup.normalizer (L : Set G) →
      g ∈ Subgroup.normalizer (E : Set G) → ∀ x ∈ conjClosure L E,
        g * x * g⁻¹ ∈ conjClosure L E := by
    intro g hgL hgE x hx
    have : conjClosure L E ≤ (conjClosure L E).comap (MulAut.conj g).toMonoidHom := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨l, hl, e, he, rfl⟩
      refine Subgroup.mem_comap.mpr (Subgroup.subset_closure ⟨g * l * g⁻¹,
        (Subgroup.mem_normalizer_iff.mp hgL l).mp hl, g * e * g⁻¹,
        (Subgroup.mem_normalizer_iff.mp hgE e).mp he, ?_⟩)
      simp [mul_assoc]
    exact this hx
  exact mem_normalizer_of_forall_conj_mem (key hgL hgE) (fun x hx => by
    simpa using key (inv_mem hgL) (inv_mem hgE) x hx)

section PPrimeCore

theorem map_inSubgroup_pPrimeCore_of_injective {H : Type*} [Group H] (r : ℕ) (f : G →* H)
    (hf : Function.Injective f) (K : Subgroup G) :
    (inSubgroup (pPrimeCore r) K).map f = inSubgroup (pPrimeCore r) (K.map f) := by
  rw [inSubgroup, inSubgroup, ← pPrimeCore_map_iso r (K.equivMapOfInjective f hf),
    Subgroup.map_map, Subgroup.map_map]
  rfl

theorem normalizer_le_normalizer_inSubgroup_pPrimeCore (r : ℕ) (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (inSubgroup (pPrimeCore r) X : Set G) := fun _ hg =>
  SteinbergBY.mem_normalizer_of_map_conj_eq (by
    rw [map_inSubgroup_pPrimeCore_of_injective r (MulAut.conj _).toMonoidHom
      (MulAut.conj _).injective, SteinbergBY.map_conj_eq_of_mem_normalizer hg])

theorem inSubgroup_pPrimeCore_le (r : ℕ) (X : Subgroup G) : inSubgroup (pPrimeCore r) X ≤ X :=
  Subgroup.map_subtype_le _

theorem le_inSubgroup_pPrimeCore {r : ℕ} {Q X : Subgroup G} (hQ : Nat.Coprime r (Nat.card Q))
    (hQX : Q ≤ X) (hXQ : X ≤ Subgroup.normalizer (Q : Set G)) :
    Q ≤ inSubgroup (pPrimeCore r) X := by
  have hn : (Q.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hQX).mpr hXQ
  have hc : Nat.Coprime r (Nat.card (Q.subgroupOf X)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQX).toEquiv]
  have hle : Q.subgroupOf X ≤ pPrimeCore r X := le_sSup ⟨hn, hc⟩
  intro x hx
  exact ⟨⟨x, hQX hx⟩, hle hx, rfl⟩

theorem coprime_card_inSubgroup_pPrimeCore {r : ℕ} [Fact r.Prime] [Finite G] (Y : Subgroup G) :
    Nat.Coprime r (Nat.card (inSubgroup (pPrimeCore r) Y)) := by
  rw [inSubgroup, Subgroup.card_map_of_injective Y.subtype_injective]
  exact pPrimeCore_coprime_card

theorem inSubgroup_pPrimeCore_mono {r : ℕ} [Fact r.Prime] [Finite G] {X Y : Subgroup G}
    (hYX : Y ≤ X) (hXY : X ≤ Subgroup.normalizer (Y : Set G)) :
    inSubgroup (pPrimeCore r) Y ≤ inSubgroup (pPrimeCore r) X :=
  le_inSubgroup_pPrimeCore (coprime_card_inSubgroup_pPrimeCore Y)
    ((inSubgroup_pPrimeCore_le r Y).trans hYX)
    (hXY.trans (normalizer_le_normalizer_inSubgroup_pPrimeCore r Y))

end PPrimeCore

section Theta

variable [Finite G] {p : ℕ}

theorem inSubgroup_theta_mono_of_normal (hp : p.Prime) {Y X : Subgroup G} (hYX : Y ≤ X)
    (hXY : X ≤ Subgroup.normalizer (Y : Set G)) :
    inSubgroup (aschbacherSolvableCore p) Y ≤ inSubgroup (aschbacherSolvableCore p) X := by
  rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp,
    inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp]
  exact RankThreeEvenClassification.Helpers.thetaCoreOf_mono_of_normal p hp Y X hYX
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hYX).mpr hXY)

theorem isSolvable_of_le_theta (hp : p.Prime) {K C : Subgroup G}
    (hK : K ≤ inSubgroup (aschbacherSolvableCore p) C) : Group.IsSolvable ↥K := by
  rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp] at hK
  have := RankThreeEvenClassification.Helpers.thetaCoreOf_solvable p hp C
  exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hK)
    (Subgroup.inclusion_injective hK)

theorem not_dvd_card_of_le_theta (hp : p.Prime) {K C : Subgroup G}
    (hK : K ≤ inSubgroup (aschbacherSolvableCore p) C) : ¬ p ∣ Nat.card ↥K := by
  rw [inSubgroup_aschbacherSolvableCore_eq_thetaCoreOf hp] at hK
  exact fun h => RankThreeEvenClassification.Helpers.thetaCoreOf_prime_complement p hp C
    (h.trans (Subgroup.card_dvd_of_le hK))

end Theta

theorem eq_one_of_mem_isPGroup_of_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {P Q : Subgroup G} (hP : IsPGroup p ↥P) (hQ : IsPGroup q ↥Q) {x : G} (hxP : x ∈ P)
    (hxQ : x ∈ Q) : x = 1 := by
  obtain ⟨a, ha⟩ := hP ⟨x, hxP⟩
  obtain ⟨b, hb⟩ := hQ ⟨x, hxQ⟩
  have h1 : x ^ (p ^ a) = 1 := by simpa using congrArg Subtype.val ha
  have h2 : x ^ (q ^ b) = 1 := by simpa using congrArg Subtype.val hb
  have hcop : Nat.Coprime (p ^ a) (q ^ b) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hpq)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one h1)
    (orderOf_dvd_of_pow_eq_one h2))

theorem center_eq_bot_of_simple (hs : IsSimpleGroup G) (hnon : ∃ a b : G, a * b ≠ b * a) :
    Subgroup.center G = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnon
    have ha : a ∈ Subgroup.center G := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

end CFSG.RankThree.PartOne.Sec9B
