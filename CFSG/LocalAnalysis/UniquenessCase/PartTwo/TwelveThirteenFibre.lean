module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteenBlocks
import CFSG.Holt.H78.Sec4AltSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteen

open Equiv Equiv.Perm MulAction Subgroup CFSG.Open

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

theorem eq_one_of_mem_fibreStab {ι : Type} {β : Ω → ι} {p : ℕ} (hp : p.Prime)
    (hβ : ∀ x, Nat.card {y // β y = β x} < p) {g : Perm Ω} (hg : g ∈ fibreStab β)
    (hgp : g ^ p = 1) : g = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hZ : IsPGroup p (zpowers g) := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hgp) with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  ext x
  obtain ⟨k, hk⟩ := hZ.card_orbit x
  have hsub : Nat.card (orbit (zpowers g) x) ≤ Nat.card {y // β y = β x} := by
    refine Nat.card_le_card_of_injective (fun z => ⟨z.1, ?_⟩) (fun a b h => ?_)
    · obtain ⟨⟨h, hh⟩, hz⟩ := z.2
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hh
      rw [← hz]
      change β ((g ^ i) x) = β x
      exact (zpow_mem hg i) x
    · exact Subtype.ext (by simpa using congrArg Subtype.val h)
  have hk0 : k = 0 := by
    by_contra h0
    have : p ≤ p ^ k := Nat.le_self_pow h0 p
    have := hβ x
    omega
  rw [hk0, pow_zero] at hk
  have hmem : g x ∈ orbit (zpowers g) x := ⟨⟨g, mem_zpowers g⟩, rfl⟩
  have hself : x ∈ orbit (zpowers g) x := mem_orbit_self x
  have := Nat.card_eq_one_iff_unique.1 hk
  have h2 := this.1.elim ⟨_, hmem⟩ ⟨_, hself⟩
  simpa using congrArg Subtype.val h2

theorem isElemAbelian_of_le_fibreStab {ι : Type} {β : Ω → ι}
    (hβ : ∀ x, Nat.card {y // β y = β x} ≤ 5) {P : Subgroup (Perm Ω)} (hP : IsPGroup 3 P)
    (hPβ : P ≤ fibreStab β) : IsElemAbelian 3 P := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsmall : ∀ x : Ω, Nat.card (MulAction.toPermHom P (orbit P x)).range ∣ 3 := by
    intro x
    have hcardO : Nat.card (orbit P x) ≤ 5 := by
      calc Nat.card (orbit P x) ≤ Nat.card {y // β y = β x} := by
            refine Nat.card_le_card_of_injective (fun z => ⟨z.1, ?_⟩) (fun a b hab => ?_)
            · obtain ⟨q, hq⟩ := z.2
              rw [← hq]
              exact hPβ q.2 x
            · exact Subtype.ext (by simpa using congrArg Subtype.val hab)
        _ ≤ 5 := hβ x
    have hR : IsPGroup 3 (MulAction.toPermHom P (orbit P x)).range :=
      hP.of_surjective _ (MulAction.toPermHom P (orbit P x)).rangeRestrict_surjective
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hR
    have hdvd : Nat.card (MulAction.toPermHom P (orbit P x)).range ∣ 120 := by
      refine (Subgroup.card_subgroup_dvd_card _).trans ?_
      rw [Nat.card_perm]
      exact (Nat.factorial_dvd_factorial hcardO).trans (by norm_num [Nat.factorial])
    rw [hk] at hdvd ⊢
    have hk1 : k ≤ 1 := by
      by_contra h
      have : 3 ^ 2 ∣ 3 ^ k := Nat.pow_dvd_pow 3 (by omega)
      have := this.trans hdvd
      norm_num at this
    interval_cases k <;> norm_num
  refine ⟨⟨⟨fun g h => ?_⟩⟩, fun g hg => ?_⟩
  · apply Subtype.ext
    apply Equiv.Perm.ext
    intro x
    set φ := MulAction.toPermHom P (orbit P x)
    have hc : IsMulCommutative φ.range := by
      rcases (Nat.dvd_prime Nat.prime_three).1 (hsmall x) with h1 | h3
      · haveI : Subsingleton φ.range := (Nat.card_eq_one_iff_unique.1 h1).1
        exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
      · haveI : Fact (Nat.Prime (Nat.card φ.range)) := ⟨h3 ▸ Nat.prime_three⟩
        haveI := isCyclic_of_prime_card (α := φ.range) rfl
        exact ⟨⟨fun a b => IsCyclic.commGroup.mul_comm a b⟩⟩
    have h1 : φ (g * h) = φ (h * g) := by
      have := hc.is_comm.comm ⟨φ g, g, rfl⟩ ⟨φ h, h, rfl⟩
      rw [map_mul, map_mul]
      exact congrArg Subtype.val this
    have h2 := congrArg (fun π : Perm (orbit P x) => ((π ⟨x, mem_orbit_self x⟩ : orbit P x) : Ω)) h1
    simpa [φ, MulAction.toPermHom_apply, Subgroup.smul_def, Perm.smul_def] using h2
  · apply Equiv.Perm.ext
    intro x
    set φ := MulAction.toPermHom P (orbit P x)
    have h3 : φ ⟨g, hg⟩ ^ 3 = 1 := by
      have h' : (⟨φ ⟨g, hg⟩, ⟨g, hg⟩, rfl⟩ : φ.range) ^ 3 = 1 :=
        (orderOf_dvd_iff_pow_eq_one.1 ((_root_.orderOf_dvd_natCard _).trans (hsmall x)))
      exact congrArg Subtype.val h'
    rw [← map_pow] at h3
    have h2 := congrArg (fun π : Perm (orbit P x) => ((π ⟨x, mem_orbit_self x⟩ : orbit P x) : Ω)) h3
    simpa [φ, MulAction.toPermHom_apply, Subgroup.smul_def, Perm.smul_def] using h2

private theorem exists_sylow_top {Q : Subgroup (Perm Ω)} (hQ : IsPGroup 2 Q) :
    ∃ P₂ : Subgroup (Perm Ω), Q ≤ P₂ ∧ fusionIsSylowIn 2 P₂ ⊤ := by
  obtain ⟨P₂, hQP₂⟩ := hQ.exists_le_sylow
  exact ⟨P₂, hQP₂, le_top, P₂.isPGroup', fun R _ hR hle => P₂.is_maximal' hR hle⟩

private theorem card_fibreStab {ι : Type} [Fintype ι] [DecidableEq ι] (f : Ω → ι) :
    Nat.card (fibreStab f) = ∏ i, (Fintype.card {a // f a = i}).factorial := by
  rw [← DomMulAct.stabilizer_card f, ← Nat.card_eq_fintype_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g =>
    ⟨fun h => funext h, fun h x => congrFun h x⟩)

private theorem ncard_small_le {P : Subgroup (Perm Ω)} (hP : fusionIsSylowIn 2 P ⊤) :
    {x : Ω | Nat.card (orbit P x) < 4}.ncard ≤ 3 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsize : ∀ x : Ω, Nat.card (orbit P x) < 4 →
      Nat.card (orbit P x) = 1 ∨ Nat.card (orbit P x) = 2 := by
    intro x hx
    obtain ⟨k, hk⟩ := hP.2.1.card_orbit x
    rw [hk] at hx ⊢
    have hk2 : k < 2 := by
      by_contra h
      have : 2 ^ 2 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    interval_cases k <;> simp
  have hsub : ∀ m : ℕ, {x : Ω | Nat.card (orbit P x) = m}.ncard ≤ m := by
    intro m
    rcases Set.eq_empty_or_nonempty {x : Ω | Nat.card (orbit P x) = m} with h | ⟨x, hx⟩
    · rw [h, Set.ncard_empty]
      exact Nat.zero_le m
    · have hle : {x : Ω | Nat.card (orbit P x) = m} ⊆ orbit P x := by
        intro y hy
        have hxy : Nat.card (orbit P y) = Nat.card (orbit P x) :=
          (show Nat.card (orbit P y) = m from hy).trans (show Nat.card (orbit P x) = m from hx).symm
        rw [← CFSG.Holt.H78.orbit_eq_of_card_orbit_eq_of_fusionIsSylowIn_top hP hxy]
        exact mem_orbit_self y
      calc {x : Ω | Nat.card (orbit P x) = m}.ncard ≤ (orbit P x).ncard := Set.ncard_le_ncard hle
        _ = m := by rw [← Nat.card_coe_set_eq]; exact hx
  calc {x : Ω | Nat.card (orbit P x) < 4}.ncard
      ≤ ({x : Ω | Nat.card (orbit P x) = 1} ∪ {x : Ω | Nat.card (orbit P x) = 2}).ncard := by
        refine Set.ncard_le_ncard fun x hx => ?_
        rcases hsize x hx with h | h
        · exact Or.inl h
        · exact Or.inr h
    _ ≤ {x : Ω | Nat.card (orbit P x) = 1}.ncard + {x : Ω | Nat.card (orbit P x) = 2}.ncard :=
        Set.ncard_union_le _ _
    _ ≤ 1 + 2 := Nat.add_le_add (hsub 1) (hsub 2)

theorem exists_fibre_subgroup {Q : Subgroup (Perm Ω)} (hQ : IsPGroup 2 Q)
    (h8 : 8 ≤ Fintype.card Ω) :
    ∃ J : Subgroup (Perm Ω), J ≤ alternatingGroup Ω ∧ Q ≤ normalizer (J : Set (Perm Ω)) ∧
      (∀ p : ℕ, p.Prime → p ∣ Nat.card J → p = 2 ∨ p = 3) ∧
      (∀ P : Subgroup (Perm Ω), P ≤ J → IsPGroup 3 P → IsElemAbelian 3 P) ∧
      9 ∣ Nat.card J ∧ (12 ≤ Fintype.card Ω → 27 ∣ Nat.card J) := by
  classical
  obtain ⟨P₂, hQP₂, hP₂⟩ := exists_sylow_top hQ
  obtain ⟨β, h1, -, h3, h4, h5⟩ := exists_blocks hP₂.2.1
  have hfib : ∀ x, Nat.card {y // β y = β x} = (β x).ncard := by
    intro x
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun y => (h1 x y).symm)
  have hfib4 : ∀ x, Nat.card {y // β y = β x} ≤ 4 := by
    intro x
    rw [hfib x]
    by_cases hx : Nat.card (orbit P₂ x) < 4
    · rw [h3 x hx, ← Nat.card_coe_set_eq]
      omega
    · rw [h4 x (by omega)]
  set J : Subgroup (Perm Ω) := fibreStab β ⊓ alternatingGroup Ω with hJ
  set L : Set Ω := {x | 4 ≤ Nat.card (orbit P₂ x)} with hL
  have hLc : Fintype.card Ω ≤ L.ncard + 3 := by
    have hc := Set.ncard_add_ncard_compl L
    have hcomp : Lᶜ = {x : Ω | Nat.card (orbit P₂ x) < 4} := by
      ext x
      simp [hL, not_le]
    rw [hcomp, Nat.card_eq_fintype_card] at hc
    have := ncard_small_le hP₂
    omega
  have hne : ∀ x y, y ∉ β x → β y ≠ β x := fun x y hy h => hy ((h1 x y).2 h)
  have key : ∀ s : Finset (Set Ω), (∀ i ∈ s, ∃ x ∈ L, β x = i) → 3 ^ s.card ∣ Nat.card J := by
    intro s hs
    have h24 : ∀ i ∈ s, (Fintype.card {a // β a = i}).factorial = 24 := by
      intro i hi
      obtain ⟨x, hxL, rfl⟩ := hs i hi
      rw [← Nat.card_eq_fintype_card, hfib x, h4 x hxL]
      rfl
    have hdvdD : 3 ^ s.card ∣ Nat.card (fibreStab β) := by
      rw [card_fibreStab β]
      refine (pow_dvd_pow_of_dvd (by norm_num : 3 ∣ 24) s.card).trans ?_
      rw [← Finset.prod_const, ← Finset.prod_congr rfl h24]
      exact Finset.prod_dvd_prod_of_subset s Finset.univ _ (Finset.subset_univ s)
    have hrel := Subgroup.relIndex_mul_card (alternatingGroup Ω) (fibreStab β)
    have hnt : Nontrivial Ω := Fintype.one_lt_card_iff_nontrivial.1 (by omega)
    have hr2 : (alternatingGroup Ω).relIndex (fibreStab β) ∣ 2 := by
      rw [← alternatingGroup.index_eq_two (α := Ω)]
      exact Subgroup.relIndex_dvd_index_of_normal _ _
    rw [inf_comm] at hrel
    have h2J : 3 ^ s.card ∣ 2 * Nat.card J := by
      rw [← hrel] at hdvdD
      exact hdvdD.trans (Nat.mul_dvd_mul_right hr2 _)
    exact (Nat.Coprime.pow_left _ (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_left h2J
  refine ⟨J, inf_le_right, ?_, ?_, ?_, ?_⟩
  · refine hQP₂.trans (le_trans ?_ inf_normalizer_le_normalizer_inf)
    refine le_inf (le_normalizer_fibreStab fun q hq x y => ?_) le_normalizer_of_normal
    rw [h5 q hq x, h5 q hq y]
    exact (Set.image_injective.2 q.injective).eq_iff
  · intro p hp hpJ
    haveI : Fact p.Prime := ⟨hp⟩
    by_contra hp23
    obtain ⟨hp2, hp3⟩ := not_or.1 hp23
    have hp4 : p ≠ 4 := fun h => by rw [h] at hp; norm_num at hp
    have hp5 : 5 ≤ p := by
      have := hp.two_le
      omega
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hpJ
    have hgp : ((g : Perm Ω)) ^ p = 1 := by
      rw [← Subgroup.coe_pow, ← hg, pow_orderOf_eq_one, Subgroup.coe_one]
    have hg1 := eq_one_of_mem_fibreStab hp (fun x => (hfib4 x).trans_lt (by omega)) g.2.1 hgp
    have : g = 1 := Subtype.ext hg1
    rw [this, orderOf_one] at hg
    exact hp.one_lt.ne hg
  · intro P hPJ hP
    exact isElemAbelian_of_le_fibreStab (fun x => (hfib4 x).trans (by norm_num)) hP
      (hPJ.trans inf_le_left)
  · obtain ⟨x₁, hx₁⟩ : L.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
    obtain ⟨x₂, hx₂L, hx₂⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (s := β x₁) (t := L)
      (by rw [h4 x₁ hx₁]; omega)
    have h12 : β x₂ ≠ β x₁ := hne x₁ x₂ hx₂
    refine ⟨?_, fun h12' => ?_⟩
    · have h := key {β x₁, β x₂} (by
        intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact ⟨x₁, hx₁, rfl⟩
        · rw [Finset.mem_singleton.1 hi]
          exact ⟨x₂, hx₂L, rfl⟩)
      rw [Finset.card_pair h12.symm] at h
      simpa using h
    · obtain ⟨x₃, hx₃L, hx₃⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard (s := β x₁ ∪ β x₂)
        (t := L) (by
          have := Set.ncard_union_le (β x₁) (β x₂)
          rw [h4 x₁ hx₁, h4 x₂ hx₂L] at this
          omega)
      have h13 : β x₃ ≠ β x₁ := hne x₁ x₃ fun h => hx₃ (Or.inl h)
      have h23 : β x₃ ≠ β x₂ := hne x₂ x₃ fun h => hx₃ (Or.inr h)
      have h := key {β x₁, β x₂, β x₃} (by
        intro i hi
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact ⟨x₁, hx₁, rfl⟩
        rcases Finset.mem_insert.1 hi with rfl | hi
        · exact ⟨x₂, hx₂L, rfl⟩
        · rw [Finset.mem_singleton.1 hi]
          exact ⟨x₃, hx₃L, rfl⟩)
      rw [Finset.card_insert_of_notMem (by simp [h12.symm, h13.symm]),
        Finset.card_pair h23.symm] at h
      simpa using h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteen
