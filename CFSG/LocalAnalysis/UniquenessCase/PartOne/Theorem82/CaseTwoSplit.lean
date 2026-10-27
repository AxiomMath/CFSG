module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

variable {G : Type} [Group G] [Finite G]

namespace SylowThreeData

private noncomputable def permFun (d : SylowThreeData G)
    (hinj : Function.Injective d.Lf)
    (hperm : ∀ m ∈ d.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (m : ↥d.M) : Fin 3 → Fin 3 :=
  fun i => Classical.choose (hperm (m : G) m.2 i)

private theorem permFun_spec (d : SylowThreeData G)
    (hinj : Function.Injective d.Lf)
    (hperm : ∀ m ∈ d.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (m : ↥d.M) (i : Fin 3) :
    (d.Lf i).map (MulAut.conj (m : G)).toMonoidHom = d.Lf (permFun d hinj hperm m i) :=
  Classical.choose_spec (hperm (m : G) m.2 i)

private theorem permFun_injective (d : SylowThreeData G)
    (hinj : Function.Injective d.Lf)
    (hperm : ∀ m ∈ d.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (m : ↥d.M) : Function.Injective (permFun d hinj hperm m) := by
  intro a b hab
  apply hinj
  have h1 := permFun_spec d hinj hperm m a
  have h2 := permFun_spec d hinj hperm m b
  exact Subgroup.map_injective (f := (MulAut.conj (m : G)).toMonoidHom)
    (MulAut.conj (m : G)).injective (h1.trans ((congrArg d.Lf hab).trans h2.symm))

private noncomputable def permEquiv (d : SylowThreeData G)
    (hinj : Function.Injective d.Lf)
    (hperm : ∀ m ∈ d.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (m : ↥d.M) : Equiv.Perm (Fin 3) :=
  Equiv.ofBijective (permFun d hinj hperm m)
    ⟨permFun_injective d hinj hperm m,
      Finite.injective_iff_surjective.mp (permFun_injective d hinj hperm m)⟩

private theorem permEquiv_one (d : SylowThreeData G)
    (hinj : Function.Injective d.Lf)
    (hperm : ∀ m ∈ d.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j) :
    permEquiv d hinj hperm 1 = 1 := by
  apply Equiv.ext
  intro i
  show permFun d hinj hperm 1 i = i
  apply hinj
  rw [← permFun_spec]
  have h1 : ((1 : ↥d.M) : G) = (1 : G) := rfl
  rw [h1]
  have h2 : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    ext z
    simp [MulAut.conj_apply]
  rw [h2, Subgroup.map_id]

private theorem permEquiv_mul (d : SylowThreeData G)
    (hinj : Function.Injective d.Lf)
    (hperm : ∀ m ∈ d.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    (m n : ↥d.M) :
    permEquiv d hinj hperm (m * n) = permEquiv d hinj hperm m * permEquiv d hinj hperm n := by
  apply Equiv.ext
  intro i
  show permFun d hinj hperm (m * n) i = permFun d hinj hperm m (permFun d hinj hperm n i)
  apply hinj
  have h1 := permFun_spec d hinj hperm (m * n) i
  have h2 := permFun_spec d hinj hperm m (permFun d hinj hperm n i)
  have h3 := permFun_spec d hinj hperm n i
  rw [← h1, ← h2, ← h3]
  have hcomp : (MulAut.conj (((m * n : ↥d.M) : G))).toMonoidHom =
      (MulAut.conj (m : G)).toMonoidHom.comp (MulAut.conj (n : G)).toMonoidHom := by
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  rw [hcomp, Subgroup.map_map]

variable (d : SylowThreeData G) (hinj : Function.Injective d.Lf)
  (hperm : ∀ m ∈ d.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)

noncomputable def permHom : ↥d.M →* Equiv.Perm (Fin 3) where
  toFun := permEquiv d hinj hperm
  map_one' := permEquiv_one d hinj hperm
  map_mul' := permEquiv_mul d hinj hperm

theorem map_conj_Lf_eq (m : ↥d.M) (i : Fin 3) :
    (d.Lf i).map (MulAut.conj (m : G)).toMonoidHom = d.Lf (d.permHom hinj hperm m i) :=
  permFun_spec d hinj hperm m i

theorem mem_normalizer_Lf_iff (m : ↥d.M) (i : Fin 3) :
    (m : G) ∈ Subgroup.normalizer (d.Lf i : Set G) ↔ d.permHom hinj hperm m i = i := by
  have hiff : (m : G) ∈ Subgroup.normalizer (d.Lf i : Set G) ↔
      Subgroup.map (MulAut.conj (m : G)).toMonoidHom (d.Lf i) = d.Lf i :=
    Subgroup.mem_normalizer_iff_map_conj_eq
  rw [hiff, map_conj_Lf_eq d hinj hperm m i]
  exact ⟨fun h => hinj h, fun h => by rw [h]⟩

private theorem perm_three (σ : Equiv.Perm (Fin 3)) (hσ : σ ^ 3 = 1) :
    σ = 1 ∨ ∀ i, σ i ≠ i := by
  have h : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 → σ = 1 ∨ ∀ i, σ i ≠ i := by decide
  exact h σ hσ

theorem forall_mem_normalizer_or_forall_map_ne (hinj : Function.Injective d.Lf)
    (hperm : ∀ m ∈ d.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j) {g : G}
    (hg : g ∈ d.M) (hg3 : IsPGroup 3 (Subgroup.zpowers g)) :
    (∀ i, g ∈ Subgroup.normalizer (d.Lf i : Set G)) ∨
      ∀ i, (d.Lf i).map (MulAut.conj g).toMonoidHom ≠ d.Lf i := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hg3.exists_card_eq
  have hord : orderOf g = 3 ^ k := by
    rw [← Nat.card_zpowers, hk]
  have hmk : (⟨g, hg⟩ : ↥d.M) ^ (3 ^ k) = 1 := by
    apply Subtype.ext
    show g ^ (3 ^ k) = (1 : G)
    rw [← hord, pow_orderOf_eq_one]
  have hσpow : (d.permHom hinj hperm ⟨g, hg⟩) ^ (3 ^ k) = 1 := by
    rw [← map_pow, hmk, map_one]
  have hdvd1 : orderOf (d.permHom hinj hperm ⟨g, hg⟩) ∣ 3 ^ k :=
    orderOf_dvd_of_pow_eq_one hσpow
  have hdvd2 : orderOf (d.permHom hinj hperm ⟨g, hg⟩) ∣ 6 := by
    have h := orderOf_dvd_natCard (d.permHom hinj hperm ⟨g, hg⟩)
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin] at h
    norm_num at h
    exact h
  obtain ⟨j, -, hdj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd1
  rw [hdj] at hdvd2
  have hj1 : j ≤ 1 := by
    by_contra hcon
    have h2 : 2 ≤ j := by omega
    have h9 : 9 ≤ 3 ^ j := by
      calc (9 : ℕ) = 3 ^ 2 := by norm_num
        _ ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) h2
    have hle : 3 ^ j ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd2
    omega
  have hσ3 : (d.permHom hinj hperm ⟨g, hg⟩) ^ 3 = 1 := by
    rw [← orderOf_dvd_iff_pow_eq_one, hdj]
    interval_cases j <;> simp
  rcases perm_three (d.permHom hinj hperm ⟨g, hg⟩) hσ3 with h1 | h1
  · left
    intro i
    exact (mem_normalizer_Lf_iff d hinj hperm ⟨g, hg⟩ i).mpr (by rw [h1]; rfl)
  · right
    intro i hconj
    exact h1 i (hinj ((map_conj_Lf_eq d hinj hperm ⟨g, hg⟩ i).symm.trans hconj))

theorem forall_le_normalizer_or_exists_forall_map_ne (hinj : Function.Injective d.Lf)
    (hperm : ∀ m ∈ d.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    {P : Subgroup G} (hPM : P ≤ d.M) (hP3 : IsPGroup 3 P) :
    (∀ i, P ≤ Subgroup.normalizer (d.Lf i : Set G)) ∨
      ∃ y ∈ P, ∀ i, (d.Lf i).map (MulAut.conj y).toMonoidHom ≠ d.Lf i := by
  by_cases h : ∀ i, P ≤ Subgroup.normalizer (d.Lf i : Set G)
  · exact Or.inl h
  · right
    obtain ⟨i, hi⟩ := not_forall.mp h
    obtain ⟨x, hxP, hxN⟩ : ∃ x, x ∈ P ∧ x ∉ Subgroup.normalizer (d.Lf i : Set G) := by
      by_contra hcon
      exact hi fun x hxP => by
        by_contra hxN
        exact hcon ⟨x, hxP, hxN⟩
    rcases forall_mem_normalizer_or_forall_map_ne d hinj hperm (hPM hxP)
      (hP3.to_le (Subgroup.zpowers_le.mpr hxP)) with hall | hmove
    · exact absurd (hall i) hxN
    · exact ⟨x, hxP, hmove⟩

theorem kernel_sup_zpowers_eq (hinj : Function.Injective d.Lf)
    (hperm : ∀ m ∈ d.M, ∀ i, ∃ j, (d.Lf i).map (MulAut.conj m).toMonoidHom = d.Lf j)
    {P : Subgroup G} (hPM : P ≤ d.M) (hP3 : IsPGroup 3 P) {y : G} (hyP : y ∈ P)
    (hy : ∀ i, (d.Lf i).map (MulAut.conj y).toMonoidHom ≠ d.Lf i) :
    (P ⊓ ⨅ i, Subgroup.normalizer (d.Lf i : Set G)).relIndex P = 3 ∧
      (P ⊓ ⨅ i, Subgroup.normalizer (d.Lf i : Set G)) ⊔ Subgroup.zpowers y = P := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let N : Subgroup G := ⨅ i, Subgroup.normalizer (d.Lf i : Set G)
  let P₀ : Subgroup G := P ⊓ N
  let φ : ↥P →* Equiv.Perm (Fin 3) := (d.permHom hinj hperm).comp (Subgroup.inclusion hPM)
  have hmemN : ∀ x : G, x ∈ N ↔ ∀ i, x ∈ Subgroup.normalizer (d.Lf i : Set G) :=
    fun x => Subgroup.mem_iInf
  have hyM : y ∈ d.M := hPM hyP
  have hker : φ.ker = P₀.subgroupOf P := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    change (d.permHom hinj hperm ⟨(x : G), hPM x.2⟩ = 1) ↔ ((x : G) ∈ P ∧ (x : G) ∈ N)
    constructor
    · intro hx
      refine ⟨x.2, (hmemN (x : G)).mpr fun i => ?_⟩
      exact (mem_normalizer_Lf_iff d hinj hperm ⟨(x : G), hPM x.2⟩ i).mpr (by rw [hx]; rfl)
    · rintro ⟨-, hx⟩
      apply Equiv.ext
      intro i
      exact (mem_normalizer_Lf_iff d hinj hperm ⟨(x : G), hPM x.2⟩ i).mp
        ((hmemN (x : G)).mp hx i)
  have hyNe : φ ⟨y, hyP⟩ ≠ 1 := by
    intro h1
    have h2 : d.permHom hinj hperm ⟨y, hyM⟩ = 1 := h1
    have h3 : d.permHom hinj hperm ⟨y, hyM⟩ 0 = 0 := by rw [h2]; rfl
    have h4 := map_conj_Lf_eq d hinj hperm ⟨y, hyM⟩ 0
    rw [h3] at h4
    exact hy 0 h4
  have hrange : Nat.card ↥φ.range = 3 := by
    have h3g : IsPGroup 3 ↥φ.range :=
      IsPGroup.of_surjective hP3 φ.rangeRestrict φ.rangeRestrict_surjective
    obtain ⟨k, hk⟩ := h3g.exists_card_eq
    have hdvd : 3 ^ k ∣ 6 := by
      rw [← hk]
      refine (Subgroup.card_dvd_of_le (le_top : φ.range ≤ ⊤)).trans ?_
      rw [Subgroup.card_top, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
      norm_num
    have hne : 3 ^ k ≠ 1 := by
      intro h1
      have hbot : φ.range = ⊥ := Subgroup.eq_bot_of_card_eq _ (by rw [hk, h1])
      have hmem : φ ⟨y, hyP⟩ ∈ φ.range := ⟨⟨y, hyP⟩, rfl⟩
      rw [hbot] at hmem
      exact hyNe (Subgroup.mem_bot.mp hmem)
    have hk1 : k = 1 := by
      have hle : 3 ^ k ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
      have hk0 : k ≠ 0 := fun h => hne (by rw [h]; norm_num)
      have hk2 : k ≤ 1 := by
        by_contra hcon
        have h2 : 2 ≤ k := by omega
        have h9 : 9 ≤ 3 ^ k := by
          calc (9 : ℕ) = 3 ^ 2 := by norm_num
            _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h2
        omega
      omega
    rw [hk, hk1]
    norm_num
  have hquot : Nat.card (↥P ⧸ φ.ker) = 3 :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv).trans hrange
  have hcardP : Nat.card ↥P = 3 * Nat.card ↥P₀ := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [hquot] at h1
    rw [h1, hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : P₀ ≤ P)).toEquiv]
  have hP₀P : P₀ ≤ P := inf_le_left
  have hrel : P₀.relIndex P = 3 := by
    have h := Subgroup.relIndex_mul_card (H := P₀) (K := P)
    rw [show P₀ ⊓ P = P₀ from inf_eq_left.mpr hP₀P, hcardP] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.card_pos) h
  have hyNotP₀ : y ∉ P₀ := by
    intro hy0
    have hyN : y ∈ N := (Subgroup.mem_inf.mp hy0).2
    have h3 : d.permHom hinj hperm ⟨y, hyM⟩ 0 = 0 :=
      (mem_normalizer_Lf_iff d hinj hperm ⟨y, hyM⟩ 0).mp ((hmemN y).mp hyN 0)
    have h4 := map_conj_Lf_eq d hinj hperm ⟨y, hyM⟩ 0
    rw [h3] at h4
    exact hy 0 h4
  have hsup : P₀ ⊔ Subgroup.zpowers y = P := by
    have hQle : P₀ ⊔ Subgroup.zpowers y ≤ P :=
      sup_le hP₀P (Subgroup.zpowers_le.mpr hyP)
    have hP₀Q : P₀ ≤ P₀ ⊔ Subgroup.zpowers y := le_sup_left
    have hrelQ : P₀.relIndex (P₀ ⊔ Subgroup.zpowers y) ≠ 1 := fun h1 =>
      hyNotP₀ ((Subgroup.relIndex_eq_one.mp h1) (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))
    have hmul := Subgroup.relIndex_mul_relIndex P₀ (P₀ ⊔ Subgroup.zpowers y) P hP₀Q hQle
    rw [hrel] at hmul
    have hb1 : (P₀ ⊔ Subgroup.zpowers y).relIndex P = 1 := by
      have hadvd : P₀.relIndex (P₀ ⊔ Subgroup.zpowers y) ∣ 3 := ⟨_, hmul.symm⟩
      rcases (Nat.dvd_prime Nat.prime_three).mp hadvd with h1 | h1
      · exact absurd h1 hrelQ
      · rw [h1] at hmul
        omega
    exact le_antisymm hQle (Subgroup.relIndex_eq_one.mp hb1)
  exact ⟨hrel, hsup⟩

end SylowThreeData

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
