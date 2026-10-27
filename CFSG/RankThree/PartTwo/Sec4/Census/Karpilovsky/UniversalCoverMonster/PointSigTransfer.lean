module

import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators
import CFSG.GroupTheory.BurnsideNormalComplement
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec14
open scoped commutatorElement

variable {Γ : Type} [Group Γ]

@[expose] noncomputable def thL (L : Subgroup Γ) : Subgroup Γ := inSubgroup (aschbacherSolvableCore 3) L

structure Data [Finite Γ] (A L R : Subgroup Γ) (b : Γ) : Prop where
  isE27 : Late.IsE27 A
  mem : b ∈ A
  ne_one : b ≠ 1
  le_centralizer : L ≤ Subgroup.centralizer ({b} : Set Γ)
  normL : A ≤ Subgroup.normalizer (L : Set Γ)
  triple : Sec4.IsTripleCover (↥L ⧸ aschbacherSolvableCore 3 ↥L) CFSG.Blueprint.NativeSporadic.ON
  quasi : IsQuasisimple (↥L ⧸ aschbacherSolvableCore 3 ↥L)
  le : A ≤ L
  inf_theta : A ⊓ thL L = ⊥
  cop : Nat.Coprime 3 (Nat.card R)
  normR_L : L ≤ Subgroup.normalizer (R : Set Γ)
  normL_R : R ≤ Subgroup.normalizer (L : Set Γ)
  normR_A : A ≤ Subgroup.normalizer (R : Set Γ)

section Basic

variable [Finite Γ]

theorem card_thL_coprime (L : Subgroup Γ) : ¬ 3 ∣ Nat.card (thL L) := by
  rw [thL, inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
  exact (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1

theorem isSolvable_thL (L : Subgroup Γ) : Group.IsSolvable (aschbacherSolvableCore 3 ↥L) :=
  (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1

theorem normalizer_le_normalizer_thL (L : Subgroup Γ) :
    Subgroup.normalizer (L : Set Γ) ≤ Subgroup.normalizer (thL L : Set Γ) := by
  have : (aschbacherSolvableCore 3 ↥L).Characteristic :=
    (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.1
  exact CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _

omit [Finite Γ] in
theorem mk_eq_one_iff (L : Subgroup Γ) (y : ↥L) :
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) y = 1 ↔ (y : Γ) ∈ thL L := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨y, h, rfl⟩
  · rintro ⟨y', hy', hyy'⟩
    have : y' = y := Subtype.ext hyy'
    rw [← this]
    exact hy'

theorem normal_coprime_eq_bot {X : Type} [Group X] [Finite X] (hq : IsQuasisimple X)
    (hZ : Nat.card (Subgroup.center X) = 3) {N : Subgroup X} (hN : N.Normal)
    (h3 : ¬ 3 ∣ Nat.card N) : N = ⊥ := by
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hN with h | h
  · exfalso
    apply h3
    rw [h, Subgroup.card_top]
    rw [← hZ]
    exact Subgroup.card_subgroup_dvd_card _
  · have h1 : Nat.card N ∣ 3 := hZ ▸ Subgroup.card_dvd_of_le h
    have h2 : Nat.card N = 1 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
      · exact h
      · exact absurd ⟨1, by omega⟩ h3
    exact Subgroup.eq_bot_of_card_eq N h2

variable {A L R : Subgroup Γ} {b : Γ}

theorem Data.inf_le_thL (d : Data A L R b) : L ⊓ R ≤ thL L := by
  set π : ↥L →* ↥L ⧸ aschbacherSolvableCore 3 ↥L := QuotientGroup.mk' _ with hπ
  set M : Subgroup ↥L := (L ⊓ R).subgroupOf L with hM
  set N : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) := M.map π with hN
  have hMn : ∀ l : ↥L, ∀ m ∈ M, l * m * l⁻¹ ∈ M := by
    intro l m hm
    rw [hM, Subgroup.mem_subgroupOf] at hm ⊢
    obtain ⟨hmL, hmR⟩ := hm
    refine ⟨?_, ?_⟩
    · simpa using L.mul_mem (L.mul_mem l.2 hmL) (L.inv_mem l.2)
    · have := (Subgroup.mem_normalizer_iff.mp (d.normR_L l.2) (m : Γ)).mp hmR
      simpa using this
  have hNn : N.Normal := by
    refine ⟨fun n hn x => ?_⟩
    obtain ⟨m, hm, rfl⟩ := hn
    obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective _ x
    refine ⟨l * m * l⁻¹, hMn l m hm, ?_⟩
    simp [hπ]
  have h3 : ¬ 3 ∣ Nat.card N := by
    intro h
    have h1 : Nat.card N ∣ Nat.card M := Subgroup.card_map_dvd _ _
    have h2 : Nat.card M ∣ Nat.card R := by
      have hc : M.map L.subtype = (L ⊓ R) ⊓ L := Subgroup.subgroupOf_map_subtype _ _
      have h4 : Nat.card M = Nat.card (M.map L.subtype) :=
        (Subgroup.card_map_of_injective L.subtype_injective).symm
      rw [hc] at h4
      rw [h4]
      exact Subgroup.card_dvd_of_le (inf_le_left.trans inf_le_right)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp d.cop (h.trans (h1.trans h2))
  have hbot := normal_coprime_eq_bot d.quasi d.triple.1 hNn h3
  intro g hg
  have hgM : (⟨g, hg.1⟩ : ↥L) ∈ M := by
    rw [hM, Subgroup.mem_subgroupOf]
    exact hg
  have : π ⟨g, hg.1⟩ ∈ N := ⟨_, hgM, rfl⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact (mk_eq_one_iff L ⟨g, hg.1⟩).mp this

theorem Data.exists_mul (d : Data A L R b) {g : Γ} (hg : g ∈ L ⊔ R) :
    ∃ l ∈ L, ∃ r ∈ R, g = l * r := by
  have hconj : ∀ r ∈ R, ∀ l ∈ L, r * l * r⁻¹ ∈ L := fun r hr l hl =>
    (Subgroup.mem_normalizer_iff.mp (d.normL_R hr) l).mp hl
  let S : Subgroup Γ :=
    { carrier := {g | ∃ l ∈ L, ∃ r ∈ R, g = l * r}
      one_mem' := ⟨1, one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨l₁, hl₁, r₁, hr₁, rfl⟩ ⟨l₂, hl₂, r₂, hr₂, rfl⟩
        refine ⟨l₁ * (r₁ * l₂ * r₁⁻¹), L.mul_mem hl₁ (hconj r₁ hr₁ l₂ hl₂), r₁ * r₂,
          R.mul_mem hr₁ hr₂, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨l, hl, r, hr, rfl⟩
        refine ⟨r⁻¹ * l⁻¹ * r⁻¹⁻¹, ?_, r⁻¹, R.inv_mem hr, ?_⟩
        · exact hconj r⁻¹ (R.inv_mem hr) l⁻¹ (L.inv_mem hl)
        · group }
  have hle : L ⊔ R ≤ S := sup_le (fun l hl => ⟨l, hl, 1, one_mem _, by simp⟩)
    (fun r hr => ⟨1, one_mem _, r, hr, by simp⟩)
  exact hle hg

theorem Data.pi_conj (d : Data A L R b) {l r : Γ} (hl : l ∈ L) (hr : r ∈ R) :
    ∃ h : r * l * r⁻¹ ∈ L,
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ⟨r * l * r⁻¹, h⟩ =
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ⟨l, hl⟩ := by
  have hL : r * l * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (d.normL_R hr) l).mp hl
  refine ⟨hL, ?_⟩
  have hc : r * l * r⁻¹ * l⁻¹ ∈ L ⊓ R := by
    refine ⟨L.mul_mem hL (L.inv_mem hl), ?_⟩
    have h1 : l * r⁻¹ * l⁻¹ ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (d.normR_L hl) r⁻¹).mp (R.inv_mem hr)
      exact this
    have : r * (l * r⁻¹ * l⁻¹) = r * l * r⁻¹ * l⁻¹ := by group
    rw [← this]
    exact R.mul_mem hr h1
  have h2 := (mk_eq_one_iff L ⟨r * l * r⁻¹ * l⁻¹, hc.1⟩).mpr (d.inf_le_thL hc)
  have h3 : (⟨r * l * r⁻¹ * l⁻¹, hc.1⟩ : ↥L) = ⟨r * l * r⁻¹, hL⟩ * ⟨l, hl⟩⁻¹ := rfl
  rw [h3, map_mul, map_inv, mul_inv_eq_one] at h2
  exact h2

theorem Data.pi_eq (d : Data A L R b) {l l' r r' : Γ} (hl : l ∈ L) (hl' : l' ∈ L) (hr : r ∈ R)
    (hr' : r' ∈ R) (h : l * r = l' * r') :
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ⟨l, hl⟩ =
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L)) ⟨l', hl'⟩ := by
  have hc : l'⁻¹ * l ∈ L ⊓ R := by
    refine ⟨L.mul_mem (L.inv_mem hl') hl, ?_⟩
    have : l'⁻¹ * l = r' * r⁻¹ := by
      have h' : l = l' * r' * r⁻¹ := by rw [← h]; group
      rw [h']
      group
    rw [this]
    exact R.mul_mem hr' (R.inv_mem hr)
  have h2 := (mk_eq_one_iff L ⟨l'⁻¹ * l, hc.1⟩).mpr (d.inf_le_thL hc)
  have h3 : (⟨l'⁻¹ * l, hc.1⟩ : ↥L) = ⟨l', hl'⟩⁻¹ * ⟨l, hl⟩ := rfl
  rw [h3, map_mul, map_inv, inv_mul_eq_one] at h2
  exact h2.symm

omit [Finite Γ] in
theorem le_normalizer_of_conj_mem {S T : Subgroup Γ} (h : ∀ a ∈ T, ∀ g ∈ S, a * g * a⁻¹ ∈ S) :
    T ≤ Subgroup.normalizer (S : Set Γ) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨h a ha g, fun hg => ?_⟩
  have := h a⁻¹ (inv_mem ha) _ hg
  simpa [mul_assoc] using this

theorem eq_one_of_pow_three_of_not_dvd {G' : Type*} [Group G'] [Finite G'] {S : Subgroup G'}
    (hS : ¬ 3 ∣ Nat.card S) {x : G'} (hx : x ∈ S) (h3 : x ^ 3 = 1) : x = 1 := by
  have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h2 : orderOf x ∣ Nat.card S := Subgroup.orderOf_dvd_natCard S hx
  have hcop : Nat.Coprime 3 (Nat.card S) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hS
  have : orderOf x ∣ Nat.gcd 3 (Nat.card S) := Nat.dvd_gcd h1 h2
  rw [hcop] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)

omit [Finite Γ] in
theorem eq_top_of_pow_three_mem {T : Type*} [Group T] [Finite T] (hperf : Group.IsPerfect T)
    (hq : IsQuasisimple (T ⧸ aschbacherSolvableCore 3 T)) (h3 : 3 ∣ Nat.card T)
    (N : Subgroup T) [N.Normal] (hN : ∀ x : T, ∀ k : ℕ, x ^ 3 ^ k = 1 → x ∈ N) : N = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hsolθ, hchar, h3θ, -⟩ :=
    solvable_prime_complement_core_characterization (H := T) Nat.prime_three
  set θ := aschbacherSolvableCore 3 T with hθ
  have : θ.Characteristic := hchar
  have : θ.Normal := inferInstance
  set mk := QuotientGroup.mk' θ with hmk
  have hN' : (N.map mk).Normal := Subgroup.Normal.map ‹_› mk (QuotientGroup.mk'_surjective θ)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hN' with htop | hcent
  ·
    have hsur : ∀ t : T, ∃ n ∈ N, mk n = mk t := fun t => by
      have : mk t ∈ N.map mk := htop ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnt⟩ := this
      exact ⟨n, hn, hnt⟩
    let f : θ →* T ⧸ N := (QuotientGroup.mk' N).comp θ.subtype
    have hf : Function.Surjective f := by
      intro q
      obtain ⟨t, rfl⟩ := QuotientGroup.mk'_surjective N q
      obtain ⟨n, hn, hnt⟩ := hsur t
      have h1 : n⁻¹ * t ∈ θ := QuotientGroup.eq.mp hnt
      refine ⟨⟨n⁻¹ * t, h1⟩, ?_⟩
      change QuotientGroup.mk' N (n⁻¹ * t) = QuotientGroup.mk' N t
      have h0 : QuotientGroup.mk' N n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
      rw [map_mul, map_inv, h0, inv_one, one_mul]
    have : Group.IsSolvable θ := hsolθ
    have : Group.IsSolvable (T ⧸ N) := Group.isSolvable_of_surjective hf
    have hperfQ : Group.IsPerfect (T ⧸ N) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
    have hsub : Subsingleton (T ⧸ N) := by
      by_contra hne
      have hn : Nontrivial (T ⧸ N) := not_subsingleton_iff_nontrivial.mp hne
      have := Group.IsSolvable.commutator_lt_top_of_nontrivial (T ⧸ N)
      rw [hperfQ.commutator_eq_top] at this
      exact lt_irrefl _ this
    rw [eq_top_iff]
    intro t _
    have : QuotientGroup.mk' N t = QuotientGroup.mk' N 1 := Subsingleton.elim _ _
    simpa using (QuotientGroup.eq_one_iff t).mp (by simpa using this)
  · exfalso
    have hA : ∀ x' : T ⧸ θ, ∀ k : ℕ, x' ^ 3 ^ k = 1 → x' ∈ N.map mk := by
      intro x' k hk
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θ x'
      have hu : x ^ 3 ^ k ∈ θ := by
        rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk'_apply] at *
        simpa [← map_pow] using hk
      have hm : Nat.Coprime 3 (orderOf (x ^ 3 ^ k)) :=
        Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard θ hu)
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3θ)
      set m := orderOf (x ^ 3 ^ k) with hmdef
      have hy : (x ^ m) ^ 3 ^ k = 1 := by
        rw [← pow_mul, mul_comm, pow_mul, hmdef, pow_orderOf_eq_one]
      have hym : mk (x ^ m) ∈ N.map mk := ⟨x ^ m, hN _ k hy, rfl⟩
      have hord : orderOf (mk x) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
      have hcop : Nat.Coprime m (orderOf (mk x)) :=
        Nat.Coprime.coprime_dvd_right hord (Nat.Coprime.pow_right k (Nat.Coprime.symm hm))
      obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hcop
      rw [← hn]
      have : mk (x ^ m) = (mk x) ^ m := map_pow _ _ _
      rw [← this]
      exact pow_mem hym n
    obtain Q : Sylow 3 (T ⧸ θ) := Classical.arbitrary _
    have hQc : (Q : Subgroup (T ⧸ θ)) ≤ Subgroup.center (T ⧸ θ) := by
      intro x hx
      obtain ⟨k, hk⟩ := (Q.isPGroup' ⟨x, hx⟩)
      have : x ^ 3 ^ k = 1 := congrArg Subtype.val hk
      exact hcent (hA x k this)
    have hP : Subgroup.normalizer (Q : Set (T ⧸ θ)) ≤ Subgroup.centralizer (Q : Set (T ⧸ θ)) := by
      intro g _
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      exact ((Subgroup.mem_center_iff.mp (hQc hh)) g).symm
    obtain ⟨K, hKn, hK3, hKidx, -, -, -, -, -, -, hab⟩ :=
      CFSG.GroupTheory.burnside_normal_complement Q hP
    have hperfT : Group.IsPerfect (T ⧸ θ) := hq.1
    have hperfQ : Group.IsPerfect ((T ⧸ θ) ⧸ K) :=
      Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' K) (QuotientGroup.mk'_surjective K)
    have hsolQ : Group.IsSolvable ((T ⧸ θ) ⧸ K) := Group.isSolvable_of_comm hab
    have hsub : Subsingleton ((T ⧸ θ) ⧸ K) := by
      by_contra hne
      have hn : Nontrivial ((T ⧸ θ) ⧸ K) := not_subsingleton_iff_nontrivial.mp hne
      have := Group.IsSolvable.commutator_lt_top_of_nontrivial ((T ⧸ θ) ⧸ K)
      rw [hperfQ.commutator_eq_top] at this
      exact lt_irrefl _ this
    have hK1 : K.index = 1 := by
      rw [Subgroup.index, Nat.card_eq_one_iff_unique]
      refine ⟨inferInstance, ⟨1⟩⟩
    rw [hK1] at hKidx
    have hQ1 : Nat.card Q = 1 := hKidx.symm
    have hnd : ¬ 3 ∣ Nat.card (T ⧸ θ) := by
      intro hd
      have := Sylow.card_eq_multiplicity Q
      rw [hQ1] at this
      have hpos : 0 < (Nat.card (T ⧸ θ)).factorization 3 :=
        Nat.Prime.factorization_pos_of_dvd Nat.prime_three Nat.card_pos.ne' hd
      have : 3 ^ (Nat.card (T ⧸ θ)).factorization 3 = 1 := this.symm
      have h3' := Nat.one_lt_pow hpos.ne' (by norm_num : 1 < 3)
      omega
    have hcard : Nat.card T = Nat.card (T ⧸ θ) * Nat.card θ :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup θ
    rw [hcard] at h3
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
    · exact hnd h
    · exact h3θ h

theorem exists_fixed_coset {H N : Subgroup Γ} (hH : IsPGroup 3 H) (hN : ¬ 3 ∣ Nat.card N)
    (hHN : H ≤ Subgroup.normalizer (N : Set Γ)) {g : Γ}
    (hg : ∀ h ∈ H, h * g * h⁻¹ * g⁻¹ ∈ N) :
    ∃ c : Γ, c * g⁻¹ ∈ N ∧ ∀ h ∈ H, h * c * h⁻¹ = c := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let α : ↥H →* MulAut Γ := (MulAut.conj : Γ →* MulAut Γ).comp H.subtype
  have := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hH α N hN g).1 (by
    intro a x hx
    have hax : α a x = a * x * (a : Γ)⁻¹ := rfl
    rw [hax]
    have h1 : (a : Γ) * (x * g⁻¹) * (a : Γ)⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hHN a.2) _).mp hx
    have h2 := hg a a.2
    have e : (a : Γ) * x * (a : Γ)⁻¹ * g⁻¹ =
        (a : Γ) * (x * g⁻¹) * (a : Γ)⁻¹ * ((a : Γ) * g * (a : Γ)⁻¹ * g⁻¹) := by group
    rw [e]
    exact N.mul_mem h1 h2)
  obtain ⟨c, hc, hfix⟩ := this
  exact ⟨c, hc, fun h hh => hfix ⟨h, hh⟩⟩

theorem not_dvd_card_of_no_order_three {S : Subgroup Γ} (h : ∀ g ∈ S, g ^ 3 = 1 → g = 1) :
    ¬ 3 ∣ Nat.card S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro hdvd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := S) 3 hdvd
  have h3 : (x : Γ) ^ 3 = 1 := by
    have := pow_orderOf_eq_one x
    rw [hx] at this
    exact congrArg Subtype.val this
  have h1 := h x x.2 h3
  have : x = 1 := Subtype.ext h1
  rw [this, orderOf_one] at hx
  exact absurd hx (by norm_num)

end Basic

section Rho

variable [Finite Γ] {A L R : Subgroup Γ} {b : Γ} (d : Data A L R b)

noncomputable def rhoFun (g : ↥(L ⊔ R)) : ↥L ⧸ aschbacherSolvableCore 3 ↥L :=
  QuotientGroup.mk' _ ⟨(d.exists_mul g.2).choose, (d.exists_mul g.2).choose_spec.1⟩

theorem rhoFun_eq (g : ↥(L ⊔ R)) {l r : Γ} (hl : l ∈ L) (hr : r ∈ R) (h : (g : Γ) = l * r) :
    rhoFun d g = QuotientGroup.mk' _ ⟨l, hl⟩ := by
  obtain ⟨r₀, hr₀, h₀⟩ := (d.exists_mul g.2).choose_spec.2
  exact d.pi_eq _ hl hr₀ hr (h₀.symm.trans h)

noncomputable def rho : ↥(L ⊔ R) →* ↥L ⧸ aschbacherSolvableCore 3 ↥L where
  toFun := rhoFun d
  map_one' := by
    rw [rhoFun_eq d 1 (one_mem L) (one_mem R) (by simp)]
    rfl
  map_mul' g₁ g₂ := by
    obtain ⟨l₁, hl₁, r₁, hr₁, h₁⟩ := d.exists_mul g₁.2
    obtain ⟨l₂, hl₂, r₂, hr₂, h₂⟩ := d.exists_mul g₂.2
    obtain ⟨hc, hcπ⟩ := d.pi_conj hl₂ hr₁
    have hprod : ((g₁ * g₂ : ↥(L ⊔ R)) : Γ) = (l₁ * (r₁ * l₂ * r₁⁻¹)) * (r₁ * r₂) := by
      change (g₁ : Γ) * g₂ = _
      rw [h₁, h₂]
      group
    rw [rhoFun_eq d _ (L.mul_mem hl₁ hc) (R.mul_mem hr₁ hr₂) hprod, rhoFun_eq d g₁ hl₁ hr₁ h₁,
      rhoFun_eq d g₂ hl₂ hr₂ h₂]
    have : (⟨l₁ * (r₁ * l₂ * r₁⁻¹), L.mul_mem hl₁ hc⟩ : ↥L) = ⟨l₁, hl₁⟩ * ⟨r₁ * l₂ * r₁⁻¹, hc⟩ :=
      rfl
    rw [this, map_mul, hcπ]

theorem rho_mk_of_mem {g : Γ} (hg : g ∈ L ⊔ R) (hgL : g ∈ L) :
    rho d ⟨g, hg⟩ = QuotientGroup.mk' _ ⟨g, hgL⟩ :=
  rhoFun_eq d ⟨g, hg⟩ hgL (one_mem R) (by simp)

theorem rho_mk_of_mem' {g : Γ} (hgL : g ∈ L) :
    rho d ⟨g, Subgroup.mem_sup_left hgL⟩ = QuotientGroup.mk' _ ⟨g, hgL⟩ :=
  rho_mk_of_mem d _ hgL

theorem Data.eq_one_of_rho_one (g : ↥(L ⊔ R)) (h1 : rho d g = 1) (h3 : (g : Γ) ^ 3 = 1) :
    (g : Γ) = 1 := by
  obtain ⟨l, hl, r, hr, hg⟩ := d.exists_mul g.2
  have hrho : rho d g = QuotientGroup.mk' _ ⟨l, hl⟩ := rhoFun_eq d g hl hr hg
  have hlθ : l ∈ thL L := (mk_eq_one_iff L ⟨l, hl⟩).mp (hrho ▸ h1)
  have hrN : r ∈ Subgroup.normalizer (thL L : Set Γ) :=
    normalizer_le_normalizer_thL L (d.normL_R hr)
  have hconj : ∀ x ∈ thL L, r * x * r⁻¹ ∈ thL L := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp hrN x).mp hx
  have hl1 := hconj l hlθ
  have hl2 := hconj _ hl1
  have hr3 : r ^ 3 ∈ thL L := by
    have e : (g : Γ) ^ 3 =
        l * (r * l * r⁻¹) * (r * (r * l * r⁻¹) * r⁻¹) * r ^ 3 := by
      rw [hg]
      simp only [pow_succ, pow_zero, one_mul]
      group
    rw [h3] at e
    have : r ^ 3 = (l * (r * l * r⁻¹) * (r * (r * l * r⁻¹) * r⁻¹))⁻¹ := by
      exact eq_inv_of_mul_eq_one_right e.symm
    rw [this]
    exact (thL L).inv_mem (mul_mem (mul_mem hlθ hl1) hl2)
  have hrθ : r ∈ thL L := by
    have hord : orderOf r ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hr
    have hcop : Nat.Coprime 3 (orderOf r) := Nat.Coprime.coprime_dvd_right hord d.cop
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
    rw [← hm]
    exact pow_mem hr3 m
  have hgθ : (g : Γ) ∈ thL L := by
    rw [hg]
    exact mul_mem hlθ hrθ
  have hord1 : orderOf (g : Γ) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have hord2 : orderOf (g : Γ) ∣ Nat.card (thL L) := Subgroup.orderOf_dvd_natCard _ hgθ
  have hcop : Nat.Coprime 3 (Nat.card (thL L)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (card_thL_coprime L)
  have : orderOf (g : Γ) ∣ Nat.gcd 3 (Nat.card (thL L)) := Nat.dvd_gcd hord1 hord2
  rw [hcop] at this
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)

omit d in
theorem Data.mem_L_of_pow_three_pow (d : Data A L R b) {g : Γ} (hg : g ∈ L ⊔ R) {k : ℕ} (hk : g ^ 3 ^ k = 1) :
    g ∈ L := by
  obtain ⟨l, hl, r, hr, rfl⟩ := d.exists_mul hg
  have hconj : ∀ x ∈ L, r * x * r⁻¹ ∈ L := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (d.normL_R hr) x).mp hx
  have hconjpow : ∀ n : ℕ, ∀ x ∈ L, r ^ n * x * (r ^ n)⁻¹ ∈ L := by
    intro n
    induction n with
    | zero => intro x hx; simpa using hx
    | succ n ih =>
      intro x hx
      have := hconj _ (ih x hx)
      simpa [pow_succ', mul_assoc] using this
  have hform : ∀ n : ℕ, ∃ ln ∈ L, (l * r) ^ n = ln * r ^ n := by
    intro n
    induction n with
    | zero => exact ⟨1, one_mem _, by simp⟩
    | succ n ih =>
      obtain ⟨ln, hln, h⟩ := ih
      refine ⟨ln * (r ^ n * l * (r ^ n)⁻¹), L.mul_mem hln (hconjpow n l hl), ?_⟩
      rw [pow_succ, h]
      group
  obtain ⟨ln, hln, h⟩ := hform (3 ^ k)
  rw [hk] at h
  have hrk : r ^ 3 ^ k ∈ L := by
    have : r ^ 3 ^ k = ln⁻¹ := eq_inv_of_mul_eq_one_right h.symm
    rw [this]
    exact L.inv_mem hln
  have hord : orderOf r ∣ Nat.card R := Subgroup.orderOf_dvd_natCard R hr
  have hcop : Nat.Coprime (3 ^ k) (orderOf r) :=
    Nat.Coprime.pow_left k (Nat.Coprime.coprime_dvd_right hord d.cop)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hrL : r ∈ L := by
    rw [← hm]
    exact pow_mem hrk m
  exact L.mul_mem hl hrL

end Rho

section Bar

variable [Finite Γ] {A L R : Subgroup Γ} {b : Γ} (d : Data A L R b)

noncomputable def bar (U : Subgroup Γ) : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
  (U.subgroupOf (L ⊔ R)).map (rho d)

theorem mem_bar {U : Subgroup Γ} {x : ↥L ⧸ aschbacherSolvableCore 3 ↥L} :
    x ∈ bar d U ↔ ∃ (g : Γ) (hg : g ∈ L ⊔ R), g ∈ U ∧ rho d ⟨g, hg⟩ = x := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, y.2, hy, rfl⟩
  · rintro ⟨g, hg, hgU, rfl⟩
    exact ⟨⟨g, hg⟩, hgU, rfl⟩

theorem rho_mem_bar {U : Subgroup Γ} {g : Γ} (hg : g ∈ L ⊔ R) (hgU : g ∈ U) :
    rho d ⟨g, hg⟩ ∈ bar d U :=
  (mem_bar d).mpr ⟨g, hg, hgU, rfl⟩

theorem bar_mono {U V : Subgroup Γ} (h : U ≤ V) : bar d U ≤ bar d V := by
  rintro x hx
  obtain ⟨g, hg, hgU, rfl⟩ := (mem_bar d).mp hx
  exact rho_mem_bar d hg (h hgU)

theorem conj_mem_bar {U : Subgroup Γ} {a : Γ} (ha : a ∈ L) (haU : a ∈ Subgroup.normalizer (U : Set Γ))
    {x : ↥L ⧸ aschbacherSolvableCore 3 ↥L} (hx : x ∈ bar d U) :
    QuotientGroup.mk' _ ⟨a, ha⟩ * x * (QuotientGroup.mk' _ ⟨a, ha⟩)⁻¹ ∈ bar d U := by
  obtain ⟨g, hg, hgU, rfl⟩ := (mem_bar d).mp hx
  have haLR : a ∈ L ⊔ R := Subgroup.mem_sup_left ha
  have h1 : rho d ⟨a, haLR⟩ = QuotientGroup.mk' _ ⟨a, ha⟩ := rho_mk_of_mem' d ha
  have hconj : a * g * a⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp haU g).mp hgU
  have hconjLR : a * g * a⁻¹ ∈ L ⊔ R :=
    mul_mem (mul_mem haLR hg) (inv_mem haLR)
  have : QuotientGroup.mk' _ ⟨a, ha⟩ * rho d ⟨g, hg⟩ * (QuotientGroup.mk' _ ⟨a, ha⟩)⁻¹ =
      rho d ⟨a * g * a⁻¹, hconjLR⟩ := by
    rw [← h1, ← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [this]
  exact rho_mem_bar d hconjLR hconj

theorem pi_mem_normalizer_bar {U : Subgroup Γ} {a : Γ} (ha : a ∈ L)
    (haU : a ∈ Subgroup.normalizer (U : Set Γ)) :
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨a, ha⟩ :
        ↥L ⧸ aschbacherSolvableCore 3 ↥L) ∈
      Subgroup.normalizer (↑(bar d U) : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => conj_mem_bar d ha haU hx, fun hx => ?_⟩
  have haU' : a⁻¹ ∈ Subgroup.normalizer (U : Set Γ) := inv_mem haU
  have := conj_mem_bar d (L.inv_mem ha) haU' hx
  have e : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨a⁻¹, L.inv_mem ha⟩ =
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨a, ha⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [e, inv_inv] at this
  simpa [mul_assoc] using this

omit d in
theorem Data.le_sup (d : Data A L R b) : A ≤ L ⊔ R := d.le.trans le_sup_left

theorem Data.eq_one_of_rho_one_of_mem_A {g : Γ} (hgA : g ∈ A) (hg : g ∈ L ⊔ R)
    (h : rho d ⟨g, hg⟩ = 1) : g = 1 := by
  have hgL : g ∈ L := d.le hgA
  rw [rho_mk_of_mem d hg hgL] at h
  have : g ∈ A ⊓ thL L := ⟨hgA, (mk_eq_one_iff L ⟨g, hgL⟩).mp h⟩
  rw [d.inf_theta, Subgroup.mem_bot] at this
  exact this

theorem card_bar_of_le {U : Subgroup Γ} (hU : U ≤ A) : Nat.card (bar d U) = Nat.card U := by
  have hULR : U ≤ L ⊔ R := hU.trans d.le_sup
  have hinj : Function.Injective ((rho d).domRestrict (U.subgroupOf (L ⊔ R))) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [Subgroup.mem_bot]
    have hg1 : rho d (g : ↥(L ⊔ R)) = 1 := hg
    have h0 := d.eq_one_of_rho_one_of_mem_A (hU g.2) (g : ↥(L ⊔ R)).2 (by simpa using hg1)
    exact Subtype.ext (Subtype.ext h0)
  rw [bar, ← MonoidHom.domRestrict_range,
    ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hULR).toEquiv]

theorem isE27_bar : Late.IsE27 (bar d A) := by
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (d.isE27.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  refine ⟨⟨⟨⟨fun u v => Subtype.ext ?_⟩⟩, ?_⟩, by rw [card_bar_of_le d le_rfl, d.isE27.2]⟩
  · obtain ⟨u, hu⟩ := u
    obtain ⟨v, hv⟩ := v
    obtain ⟨g, hg, hgA, rfl⟩ := (mem_bar d).mp hu
    obtain ⟨h, hh, hhA, rfl⟩ := (mem_bar d).mp hv
    change rho d ⟨g, hg⟩ * rho d ⟨h, hh⟩ = rho d ⟨h, hh⟩ * rho d ⟨g, hg⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm g hgA h hhA)
  · intro x hx
    obtain ⟨g, hg, hgA, rfl⟩ := (mem_bar d).mp hx
    rw [← map_pow]
    have : (⟨g, hg⟩ : ↥(L ⊔ R)) ^ 3 = 1 := Subtype.ext (d.isE27.1.2 g hgA)
    rw [this, map_one]

theorem pi_b_mem_center :
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨b, d.le d.mem⟩ :
      ↥L ⧸ aschbacherSolvableCore 3 ↥L) ∈ Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
  rw [Subgroup.mem_center_iff]
  intro q
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥L) q
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  exact (Subgroup.mem_centralizer_singleton_iff.mp (d.le_centralizer l.2))

theorem pi_b_ne_one :
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨b, d.le d.mem⟩ :
      ↥L ⧸ aschbacherSolvableCore 3 ↥L) ≠ 1 := by
  intro h
  have : b ∈ A ⊓ thL L := ⟨d.mem, (mk_eq_one_iff L ⟨b, d.le d.mem⟩).mp h⟩
  rw [d.inf_theta, Subgroup.mem_bot] at this
  exact d.ne_one this

theorem center_eq_zpowers_pi_b :
    Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) =
      Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨b, d.le d.mem⟩) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have htop := zpowers_eq_top_of_prime_card (G := Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L))
    d.triple.1 (g := ⟨_, pi_b_mem_center d⟩) (fun h => pi_b_ne_one d (congrArg Subtype.val h))
  apply le_antisymm
  · intro x hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (htop ▸ Subgroup.mem_top (⟨x, hx⟩ :
      Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simpa using congrArg Subtype.val hn⟩
  · rw [Subgroup.zpowers_le]
    exact pi_b_mem_center d

theorem center_le_bar {B : Subgroup Γ} (hB : B ≤ A) (hbB : b ∈ B) :
    Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≤ bar d B := by
  rw [center_eq_zpowers_pi_b d, Subgroup.zpowers_le]
  have := rho_mem_bar d (d.le_sup (hB hbB)) hbB
  rwa [rho_mk_of_mem d _ (d.le (hB hbB))] at this

theorem isHyperplane_bar {B : Subgroup Γ} (hB : IsHyperplane A B) :
    IsHyperplane (bar d A) (bar d B) := by
  refine ⟨bar_mono d hB.1, ?_⟩
  rw [card_bar_of_le d le_rfl, card_bar_of_le d hB.1]
  exact hB.2

theorem exists_hyperplane_of_bar {H : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)}
    (hH : IsHyperplane (bar d A) H) : ∃ B : Subgroup Γ, IsHyperplane A B ∧ bar d B = H := by
  set ρA : ↥A →* ↥L ⧸ aschbacherSolvableCore 3 ↥L :=
    (rho d).comp (Subgroup.inclusion d.le_sup) with hρA
  set B : Subgroup Γ := (H.comap ρA).map A.subtype with hB
  have hBA : B ≤ A := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  have hbar : bar d B = H := by
    apply le_antisymm
    · intro x hx
      obtain ⟨g, hg, ⟨a, ha, rfl⟩, rfl⟩ := (mem_bar d).mp hx
      exact ha
    · intro x hx
      obtain ⟨g, hg, hgA, rfl⟩ := (mem_bar d).mp (hH.1 hx)
      exact (mem_bar d).mpr ⟨g, hg, ⟨⟨g, hgA⟩, hx, rfl⟩, rfl⟩
  refine ⟨B, ⟨hBA, ?_⟩, hbar⟩
  have h1 := hH.2
  rw [card_bar_of_le d le_rfl] at h1
  rw [h1, ← hbar, card_bar_of_le d hBA]

theorem subgroupOf_commutator_of_le {G : Type*} [Group G] {K U V : Subgroup G} (hU : U ≤ K)
    (hV : V ≤ K) :
    (⁅U, V⁆).subgroupOf K = ⁅U.subgroupOf K, V.subgroupOf K⁆ := by
  have hUV : ⁅U, V⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro u hu v hv
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem (hU hu) (hV hv)) (K.inv_mem (hU hu))) (K.inv_mem (hV hv))
  apply Subgroup.map_injective K.subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hU,
    Subgroup.map_subgroupOf_eq_of_le hV, Subgroup.map_subgroupOf_eq_of_le hUV]

theorem bar_commutator {U V : Subgroup Γ} (hU : U ≤ L ⊔ R) (hV : V ≤ L ⊔ R) :
    bar d ⁅U, V⁆ = ⁅bar d U, bar d V⁆ := by
  rw [bar, bar, bar, subgroupOf_commutator_of_le hU hV, Subgroup.map_commutator]

omit d in
theorem Data.isPGroup_A (d : Data A L R b) : IsPGroup 3 A := fun g =>
  ⟨1, Subtype.ext (by simpa using d.isE27.1.2 g g.2)⟩

noncomputable def kerΓ : Subgroup Γ := (rho d).ker.map (L ⊔ R).subtype

theorem mem_kerΓ {g : Γ} : g ∈ kerΓ d ↔ ∃ hg : g ∈ L ⊔ R, rho d ⟨g, hg⟩ = 1 := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem not_dvd_card_of_le_ker {S : Subgroup Γ} (hS : S ≤ kerΓ d) : ¬ 3 ∣ Nat.card S :=
  not_dvd_card_of_no_order_three fun g hg h3 => by
    obtain ⟨hgLR, h1⟩ := (mem_kerΓ d).mp (hS hg)
    exact d.eq_one_of_rho_one ⟨g, hgLR⟩ h1 h3

theorem A_le_normalizer_kerΓ : A ≤ Subgroup.normalizer (kerΓ d : Set Γ) := by
  have key : ∀ a ∈ A, ∀ g ∈ kerΓ d, a * g * a⁻¹ ∈ kerΓ d := by
    intro a ha g hg
    obtain ⟨hgLR, h1⟩ := (mem_kerΓ d).mp hg
    have haLR : a ∈ L ⊔ R := d.le_sup ha
    have hconj : a * g * a⁻¹ ∈ L ⊔ R := mul_mem (mul_mem haLR hgLR) (inv_mem haLR)
    refine (mem_kerΓ d).mpr ⟨hconj, ?_⟩
    have : (⟨a * g * a⁻¹, hconj⟩ : ↥(L ⊔ R)) = ⟨a, haLR⟩ * ⟨g, hgLR⟩ * ⟨a, haLR⟩⁻¹ := rfl
    rw [this, map_mul, map_mul, h1, mul_one, map_inv, mul_inv_cancel]
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key a ha g, fun h => ?_⟩
  have := key a⁻¹ (inv_mem ha) _ h
  simpa [mul_assoc] using this

theorem exists_centralizer_lift {W H : Subgroup Γ} (hW : W ≤ L ⊔ R) (hH : H ≤ A)
    (hHW : H ≤ Subgroup.normalizer (W : Set Γ)) {x : ↥L ⧸ aschbacherSolvableCore 3 ↥L}
    (hx : x ∈ bar d W)
    (hxc : x ∈ Subgroup.centralizer (↑(bar d H) : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) :
    ∃ c ∈ W ⊓ Subgroup.centralizer (H : Set Γ), ∃ hc : c ∈ L ⊔ R, rho d ⟨c, hc⟩ = x := by
  obtain ⟨w, hwLR, hwW, rfl⟩ := (mem_bar d).mp hx
  have hN : W ⊓ kerΓ d ≤ kerΓ d := inf_le_right
  obtain ⟨c, hc, hfix⟩ := exists_fixed_coset (H := H) (N := W ⊓ kerΓ d)
    (IsPGroup.to_le (Data.isPGroup_A d) hH) (not_dvd_card_of_le_ker d hN)
    (fun h hh => Subgroup.inf_normalizer_le_normalizer_inf ⟨hHW hh, A_le_normalizer_kerΓ d (hH hh)⟩)
    (g := w) (by
      intro h hh
      have hhLR : h ∈ L ⊔ R := d.le_sup (hH hh)
      refine ⟨?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.mp (hHW hh) w).mp hwW
        exact W.mul_mem this (W.inv_mem hwW)
      · have hconjLR : h * w * h⁻¹ * w⁻¹ ∈ L ⊔ R :=
          mul_mem (mul_mem (mul_mem hhLR hwLR) (inv_mem hhLR)) (inv_mem hwLR)
        refine (mem_kerΓ d).mpr ⟨hconjLR, ?_⟩
        have hbarh : rho d ⟨h, hhLR⟩ ∈ bar d H := rho_mem_bar d hhLR hh
        have hcomm := Subgroup.mem_centralizer_iff.mp hxc _ hbarh
        have : (⟨h * w * h⁻¹ * w⁻¹, hconjLR⟩ : ↥(L ⊔ R)) =
            ⟨h, hhLR⟩ * ⟨w, hwLR⟩ * ⟨h, hhLR⟩⁻¹ * ⟨w, hwLR⟩⁻¹ := rfl
        rw [this, map_mul, map_mul, map_mul, map_inv, map_inv]
        have hc2 : rho d ⟨h, hhLR⟩ * rho d ⟨w, hwLR⟩ = rho d ⟨w, hwLR⟩ * rho d ⟨h, hhLR⟩ :=
          hcomm
        rw [hc2]
        group)
  have hcW : c ∈ W := by
    have h1 : c * w⁻¹ ∈ W := hc.1
    have := mul_mem h1 hwW
    simpa using this
  have hcLR : c ∈ L ⊔ R := hW hcW
  refine ⟨c, ⟨hcW, ?_⟩, hcLR, ?_⟩
  · refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    have := hfix h hh
    calc h * c = h * c * h⁻¹ * h := by group
      _ = c * h := by rw [this]
  · have hker := (mem_kerΓ d).mp hc.2
    obtain ⟨hcwLR, hrk⟩ := hker
    have : (⟨c, hcLR⟩ : ↥(L ⊔ R)) = ⟨c * w⁻¹, hcwLR⟩ * ⟨w, hwLR⟩ := by
      apply Subtype.ext
      simp
    rw [this, map_mul, hrk, one_mul]

theorem card_bar_dvd {U : Subgroup Γ} (hU : U ≤ L ⊔ R) : Nat.card (bar d U) ∣ Nat.card U := by
  have h1 : Nat.card (bar d U) ∣ Nat.card (U.subgroupOf (L ⊔ R)) := Subgroup.card_map_dvd _ _
  rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hU).toEquiv] at h1

theorem bar_le_normalizer_bar {K' O : Subgroup Γ}
    (hKO : K' ≤ Subgroup.normalizer (O : Set Γ)) :
    bar d K' ≤ Subgroup.normalizer (↑(bar d O) : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
  have key : ∀ g ∈ K', ∀ (hg : g ∈ L ⊔ R), ∀ y ∈ bar d O,
      rho d ⟨g, hg⟩ * y * (rho d ⟨g, hg⟩)⁻¹ ∈ bar d O := by
    intro g hgK hg y hy
    obtain ⟨o, ho, hoO, rfl⟩ := (mem_bar d).mp hy
    have hconj : g * o * g⁻¹ ∈ O := (Subgroup.mem_normalizer_iff.mp (hKO hgK) o).mp hoO
    have hconjLR : g * o * g⁻¹ ∈ L ⊔ R := mul_mem (mul_mem hg ho) (inv_mem hg)
    have : rho d ⟨g, hg⟩ * rho d ⟨o, ho⟩ * (rho d ⟨g, hg⟩)⁻¹ = rho d ⟨g * o * g⁻¹, hconjLR⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this]
    exact rho_mem_bar d hconjLR hconj
  intro x hx
  obtain ⟨g, hg, hgK, rfl⟩ := (mem_bar d).mp hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g hgK hg y, fun hy => ?_⟩
  have hinv : g⁻¹ ∈ K' := inv_mem hgK
  have hinvLR : g⁻¹ ∈ L ⊔ R := inv_mem hg
  have := key g⁻¹ hinv hinvLR _ hy
  have e : rho d ⟨g⁻¹, hinvLR⟩ = (rho d ⟨g, hg⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [e, inv_inv] at this
  simpa [mul_assoc] using this

theorem bar_pPrimeCoreOf_le {K' : Subgroup Γ} (hK : K' ≤ L ⊔ R) :
    bar d (pPrimeCoreOf 3 K') ≤ pPrimeCoreOf 3 (bar d K') := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hO : pPrimeCoreOf 3 K' ≤ K' := pPrimeCoreOf_le 3 K'
  refine le_pPrimeCoreOf (bar_mono d hO)
    (bar_le_normalizer_bar d (le_normalizer_pPrimeCoreOf 3 K')) ?_
  have h1 := card_bar_dvd d (hO.trans hK)
  have h2 := coprime_card_pPrimeCoreOf 3 K'
  exact Nat.Coprime.coprime_dvd_right h1 h2

theorem bar_inf_centralizer {W H : Subgroup Γ} (hW : W ≤ L ⊔ R) (hH : H ≤ A)
    (hHW : H ≤ Subgroup.normalizer (W : Set Γ)) :
    bar d (W ⊓ Subgroup.centralizer (H : Set Γ)) =
      bar d W ⊓ Subgroup.centralizer (↑(bar d H) : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨g, hg, ⟨hgW, hgC⟩, rfl⟩ := (mem_bar d).mp hx
    refine ⟨rho_mem_bar d hg hgW, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    obtain ⟨h, hh, hhH, rfl⟩ := (mem_bar d).mp hy
    have hcomm : h * g = g * h := Subgroup.mem_centralizer_iff.mp hgC h hhH
    change rho d ⟨h, hh⟩ * rho d ⟨g, hg⟩ = rho d ⟨g, hg⟩ * rho d ⟨h, hh⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcomm
  · rintro x ⟨hxW, hxC⟩
    obtain ⟨c, ⟨hcW, hcC⟩, hc, hcx⟩ := exists_centralizer_lift d hW hH hHW hxW hxC
    exact (mem_bar d).mpr ⟨c, hc, ⟨hcW, hcC⟩, hcx⟩

theorem exists_lift_signalizer {W H : Subgroup Γ} (hW : W ≤ L ⊔ R) (hHA : H ≤ A)
    (hAW : A ≤ Subgroup.normalizer (W : Set Γ)) {V' : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L)}
    (hV'W : V' ≤ bar d W)
    (hV'C : V' ≤ Subgroup.centralizer (↑(bar d H) : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)))
    (hV' : V' ∈ invariantPiSubgroups ⊤ (bar d A) (piCompl 3)) (hV'c : V' = ⁅V', bar d A⁆) :
    ∃ V : Subgroup Γ, V ≤ W ⊓ Subgroup.centralizer (H : Set Γ) ∧
      V ∈ invariantPiSubgroups ⊤ A (piCompl 3) ∧ V = ⁅V, A⁆ ∧ V' ≤ bar d V := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hV'3 : ¬ 3 ∣ Nat.card V' := fun h =>
    (hV'.2.1 ⟨3, Nat.prime_three⟩ h) rfl
  have hHW : H ≤ Subgroup.normalizer (W : Set Γ) := hHA.trans hAW
  set Vt : Subgroup Γ := W ⊓ (V'.comap (rho d)).map (L ⊔ R).subtype with hVt
  have hmemVt : ∀ g : Γ, g ∈ Vt ↔ g ∈ W ∧ ∃ hg : g ∈ L ⊔ R, rho d ⟨g, hg⟩ ∈ V' := by
    intro g
    rw [hVt, Subgroup.mem_inf, Subgroup.mem_map]
    constructor
    · rintro ⟨hgW, y, hy, rfl⟩
      exact ⟨hgW, y.2, hy⟩
    · rintro ⟨hgW, hg, h⟩
      exact ⟨hgW, ⟨⟨g, hg⟩, h, rfl⟩⟩
  have hVtW : Vt ≤ W := inf_le_left
  have hVtLR : Vt ≤ L ⊔ R := hVtW.trans hW
  have hAVt : A ≤ Subgroup.normalizer (Vt : Set Γ) := by
    refine le_normalizer_of_conj_mem fun a ha g hg => ?_
    obtain ⟨hgW, hgLR, hgV⟩ := (hmemVt g).mp hg
    have haLR : a ∈ L ⊔ R := d.le_sup ha
    have hconjLR : a * g * a⁻¹ ∈ L ⊔ R := mul_mem (mul_mem haLR hgLR) (inv_mem haLR)
    refine (hmemVt _).mpr ⟨(Subgroup.mem_normalizer_iff.mp (hAW ha) g).mp hgW, hconjLR, ?_⟩
    have hra : rho d ⟨a, haLR⟩ ∈ bar d A := rho_mem_bar d haLR ha
    have : rho d ⟨a * g * a⁻¹, hconjLR⟩ =
        rho d ⟨a, haLR⟩ * rho d ⟨g, hgLR⟩ * (rho d ⟨a, haLR⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [this]
    exact (Subgroup.mem_normalizer_iff.mp (hV'.2.2 hra) _).mp hgV
  have hVt3 : ¬ 3 ∣ Nat.card Vt := not_dvd_card_of_no_order_three fun g hg h3 => by
    obtain ⟨-, hgLR, hgV⟩ := (hmemVt g).mp hg
    have : (rho d ⟨g, hgLR⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨g, hgLR⟩ : ↥(L ⊔ R)) ^ 3 = 1 := Subtype.ext h3
      rw [this, map_one]
    have h1 : rho d ⟨g, hgLR⟩ = 1 := eq_one_of_pow_three_of_not_dvd hV'3 hgV this
    exact d.eq_one_of_rho_one ⟨g, hgLR⟩ h1 h3
  set C : Subgroup Γ := Vt ⊓ Subgroup.centralizer (H : Set Γ) with hC
  have hCVt : C ≤ Vt := inf_le_left
  have hV'bar : V' ≤ bar d C := by
    intro v hv
    obtain ⟨c, ⟨hcW, hcC⟩, hcLR, hcv⟩ := exists_centralizer_lift d hW hHA hHW (hV'W hv) (hV'C hv)
    refine (mem_bar d).mpr ⟨c, hcLR, ⟨(hmemVt c).mpr ⟨hcW, hcLR, hcv ▸ hv⟩, hcC⟩, hcv⟩
  have hAC : A ≤ Subgroup.normalizer (C : Set Γ) := by
    refine le_normalizer_of_conj_mem fun a ha g hg => ?_
    have hgVt := hg.1
    have hgC := hg.2
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hAVt ha) g).mp hgVt, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (d.isE27.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have h1 : h * a = a * h := hcomm h (hHA hh) a ha
    have h2 : h * g = g * h := Subgroup.mem_centralizer_iff.mp hgC h hh
    calc h * (a * g * a⁻¹) = (h * a) * g * a⁻¹ := by group
      _ = a * (h * g) * a⁻¹ := by rw [h1]; group
      _ = a * (g * h) * a⁻¹ := by rw [h2]
      _ = a * g * a⁻¹ * h := by
        have : a⁻¹ * h = h * a⁻¹ := by
          calc a⁻¹ * h = a⁻¹ * (h * a) * a⁻¹ := by group
            _ = a⁻¹ * (a * h) * a⁻¹ := by rw [h1]
            _ = h * a⁻¹ := by group
        calc a * (g * h) * a⁻¹ = a * g * (h * a⁻¹) := by group
          _ = a * g * (a⁻¹ * h) := by rw [← this]
          _ = a * g * a⁻¹ * h := by group
  have hC3 : ¬ 3 ∣ Nat.card C := fun h => hVt3 (h.trans (Subgroup.card_dvd_of_le hCVt))
  have hAp := Data.isPGroup_A d
  refine ⟨⁅C, A⁆, ?_, ⟨le_top, ?_, ?_⟩, ?_, ?_⟩
  · have hle : ⁅C, A⁆ ≤ C :=
      CFSG.LargeEvenClassification.Helpers.commutator_le_of_normalized C A hAC
    exact le_inf ((hle.trans hCVt).trans hVtW) (hle.trans inf_le_right)
  · intro q hq
    have hle : ⁅C, A⁆ ≤ C :=
      CFSG.LargeEvenClassification.Helpers.commutator_le_of_normalized C A hAC
    have hq3 : ¬ 3 ∣ Nat.card (⁅C, A⁆ : Subgroup Γ) := fun h => hC3 (h.trans (Subgroup.card_dvd_of_le hle))
    show (q : ℕ) ≠ 3
    intro h
    exact hq3 (h ▸ hq)
  · exact Subgroup.normalizer_commutator_ge_right C A
  · exact (CFSG.LargeEvenClassification.Helpers.coprime_normalized_commutator_idempotent
      Nat.prime_three A C hAp hC3 hAC).symm
  · have hCLR : C ≤ L ⊔ R := hCVt.trans hVtLR
    have hALR : A ≤ L ⊔ R := d.le_sup
    rw [bar_commutator d hCLR hALR]
    calc V' = ⁅V', bar d A⁆ := hV'c
      _ ≤ ⁅bar d C, bar d A⁆ := Subgroup.commutator_mono hV'bar le_rfl

theorem sig_bar {W : Subgroup Γ} (hW : W ≤ L ⊔ R) (hAW : A ≤ Subgroup.normalizer (W : Set Γ))
    (hsig : ∀ H : Subgroup Γ, IsHyperplane A H → ∀ V : Subgroup Γ,
      V ≤ W ⊓ Subgroup.centralizer (H : Set Γ) → V ∈ invariantPiSubgroups ⊤ A (piCompl 3) →
      V = ⁅V, A⁆ → V ≤ pPrimeCoreOf 3 (W ⊓ Subgroup.centralizer (H : Set Γ))) :
    ∀ H' : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L), IsHyperplane (bar d A) H' →
      ∀ V' : Subgroup (↥L ⧸ aschbacherSolvableCore 3 ↥L),
        V' ≤ bar d W ⊓ Subgroup.centralizer (↑H' : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L)) →
        V' ∈ invariantPiSubgroups ⊤ (bar d A) (piCompl 3) → V' = ⁅V', bar d A⁆ →
        V' ≤ pPrimeCoreOf 3
          (bar d W ⊓ Subgroup.centralizer (↑H' : Set (↥L ⧸ aschbacherSolvableCore 3 ↥L))) := by
  intro H' hH' V' hV' hV'inv hV'c
  obtain ⟨H, hH, rfl⟩ := exists_hyperplane_of_bar d hH'
  obtain ⟨V, hVle, hVinv, hVc, hV'V⟩ :=
    exists_lift_signalizer d hW hH.1 hAW (le_inf_iff.mp hV').1 (le_inf_iff.mp hV').2 hV'inv hV'c
  have h1 := hsig H hH V hVle hVinv hVc
  have hK : W ⊓ Subgroup.centralizer (H : Set Γ) ≤ L ⊔ R := inf_le_left.trans hW
  have h2 := bar_pPrimeCoreOf_le d hK
  rw [bar_inf_centralizer d hW hH.1 (hH.1.trans hAW)] at h2
  exact hV'V.trans ((bar_mono d h1).trans h2)

theorem mem_bar_inf_L_of_pow_three {W : Subgroup Γ}
    {x : ↥L ⧸ aschbacherSolvableCore 3 ↥L} (hx : x ∈ bar d W) {k : ℕ} (hk : x ^ 3 ^ k = 1) :
    x ∈ bar d (W ⊓ L) := by
  obtain ⟨w, hwLR, hwW, rfl⟩ := (mem_bar d).mp hx
  have hu : (w ^ 3 ^ k) ∈ kerΓ d := by
    refine (mem_kerΓ d).mpr ⟨pow_mem hwLR _, ?_⟩
    have : (⟨w ^ 3 ^ k, pow_mem hwLR _⟩ : ↥(L ⊔ R)) = (⟨w, hwLR⟩ : ↥(L ⊔ R)) ^ 3 ^ k := rfl
    rw [this, map_pow, hk]
  have hker3 : ¬ 3 ∣ Nat.card (kerΓ d) := not_dvd_card_of_le_ker d le_rfl
  have hm : Nat.Coprime 3 (orderOf (w ^ 3 ^ k)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard _ hu)
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hker3)
  set m := orderOf (w ^ 3 ^ k) with hmdef
  have hw'pow : (w ^ m) ^ 3 ^ k = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hmdef, pow_orderOf_eq_one]
  have hw'L : w ^ m ∈ L := Data.mem_L_of_pow_three_pow d (pow_mem hwLR m) hw'pow
  have hxm : rho d ⟨w ^ m, pow_mem hwLR m⟩ ∈ bar d (W ⊓ L) :=
    rho_mem_bar d (pow_mem hwLR m) ⟨pow_mem hwW m, hw'L⟩
  have hxm' : rho d ⟨w ^ m, pow_mem hwLR m⟩ = (rho d ⟨w, hwLR⟩) ^ m := by
    rw [← map_pow]
    rfl
  rw [hxm'] at hxm
  have hord : orderOf (rho d ⟨w, hwLR⟩) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime m (orderOf (rho d ⟨w, hwLR⟩)) :=
    Nat.Coprime.coprime_dvd_right hord
      (Nat.Coprime.pow_right k (Nat.Coprime.symm hm))
  obtain ⟨n, hn⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hn]
  exact pow_mem hxm n

end Bar

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig
