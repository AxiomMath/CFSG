module

public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralCyclic
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeNonToralFpf

public section

namespace CFSG.StandardType.E6NonToralThree

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.Three TableBExc.E6Three

private theorem weylImage_ne_bot
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) (hET : ¬ E ≤ torusGroup .E6 L) :
    (E.subgroupOf (monomialSubgroup .E6 L)).map (weylQuotientHom .E6 L) ≠ ⊥ := by
  intro hbot
  apply hET
  intro e he
  have hle : E.subgroupOf (monomialSubgroup .E6 L) ≤ (weylQuotientHom .E6 L).ker :=
    (Subgroup.map_eq_bot_iff (H := E.subgroupOf (monomialSubgroup .E6 L))
      (f := weylQuotientHom .E6 L)).mp hbot
  have hmem : (⟨e, hEM he⟩ : monomialSubgroup .E6 L) ∈ (weylQuotientHom .E6 L).ker :=
    hle (Subgroup.mem_subgroupOf.mpr he)
  rw [CFSG.StandardType.TableBExc.weylQuotientHom_surjective_ker.2,
    Subgroup.mem_subgroupOf] at hmem
  exact hmem

private theorem weylImage_card_dvd
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) (hcard : Nat.card E = 3 ^ 4) :
    Nat.card ((E.subgroupOf (monomialSubgroup .E6 L)).map (weylQuotientHom .E6 L)) ∣
      3 ^ 4 := by
  have h := Subgroup.card_map_dvd (E.subgroupOf (monomialSubgroup .E6 L))
    (weylQuotientHom .E6 L)
  have hK : Nat.card (E.subgroupOf (monomialSubgroup .E6 L)) = 3 ^ 4 := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEM).toEquiv
  rwa [hK] at h

theorem weylImage_card_cases
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) (hcard : Nat.card E = 3 ^ 4)
    (hET : ¬ E ≤ torusGroup .E6 L) :
    Nat.card ((E.subgroupOf (monomialSubgroup .E6 L)).map (weylQuotientHom .E6 L)) = 3 ∨
      9 ≤ Nat.card ((E.subgroupOf (monomialSubgroup .E6 L)).map
        (weylQuotientHom .E6 L)) := by
  let A : Subgroup (WeylGroup .E6) := (E.subgroupOf (monomialSubgroup .E6 L)).map
    (weylQuotientHom .E6 L)
  have hA : A = (E.subgroupOf (monomialSubgroup .E6 L)).map
      (weylQuotientHom .E6 L) := rfl
  have hne : A ≠ ⊥ := by
    rw [hA]
    exact weylImage_ne_bot hEM hET
  have hdiv : Nat.card A ∣ 3 ^ 4 := by
    rw [hA]
    exact weylImage_card_dvd hEM hcard
  by_cases h3 : Nat.card A = 3
  · exact Or.inl h3
  · right
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdiv
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.card_eq_one.mp (by simpa using hk))
    have hk1 : k ≠ 1 := by
      rintro rfl
      exact h3 (by simpa using hk)
    have hk2 : 2 ≤ k := by omega
    calc
      9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 3) hk2
      _ = Nat.card A := hk.symm

private theorem weylImage_le_modelRange
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range) :
    (E.subgroupOf (monomialSubgroup .E6 L)).map (weylQuotientHom .E6 L) ≤
      modelHomE6.range := by
  rintro w ⟨e, he, rfl⟩
  have heE : (e : ModGL .E6 L) ∈ E := Subgroup.mem_subgroupOf.mp he
  have heq : (⟨(e : ModGL .E6 L), hEM heE⟩ : monomialSubgroup .E6 L) = e :=
    Subtype.ext rfl
  simpa [heq] using hAS (e : ModGL .E6 L) heE

private theorem isElemAbelian_weylImage
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hE : IsElemAbelian 3 E) :
    IsElemAbelian 3 ((E.subgroupOf (monomialSubgroup .E6 L)).map
      (weylQuotientHom .E6 L)) :=
  (hE.subgroupOf (monomialSubgroup .E6 L)).map (weylQuotientHom .E6 L)

private theorem weylImage_not_mem_gE6
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i) :
    ∀ i, gE6 i ∉ ((E.subgroupOf (monomialSubgroup .E6 L)).map
      (weylQuotientHom .E6 L)) := by
  intro i hmem
  obtain ⟨e, he, heq⟩ := Subgroup.mem_map.mp hmem
  have heE : (e : ModGL .E6 L) ∈ E := Subgroup.mem_subgroupOf.mp he
  have heq' : (⟨(e : ModGL .E6 L), hEM heE⟩ : monomialSubgroup .E6 L) = e :=
    Subtype.ext rfl
  rw [← heq'] at heq
  exact hAg (e : ModGL .E6 L) heE i heq

private theorem commute_of_centralizer
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    (x : ModGL .E6 L) (hx : x ∈ adjointGroup .E6 L)
    (y : ModGL .E6 L) (hy : y ∈ adjointGroup .E6 L)
    (hxE : ∀ e ∈ E, x * e = e * x) (hyE : ∀ e ∈ E, y * e = e * y) :
    x * y = y * x := by
  obtain ⟨e₁, he₁, t₁, ht₁, ht₁E, rfl⟩ :=
    exists_mul_torus_of_commute hL hEM hE hcard hET hAS hAg hx hxE
  obtain ⟨e₂, he₂, t₂, ht₂, ht₂E, rfl⟩ :=
    exists_mul_torus_of_commute hL hEM hE hcard hET hAS hAg hy hyE
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht₁
  have ht12 : rootDiagUnit .E6 a * t₂ = t₂ * rootDiagUnit .E6 a :=
    rootDiagUnit_mul_comm_of_mem_torusGroup a ht₂
  calc
    (e₁ * rootDiagUnit .E6 a) * (e₂ * t₂) =
        e₁ * (rootDiagUnit .E6 a * e₂) * t₂ := by group
    _ = e₁ * (e₂ * rootDiagUnit .E6 a) * t₂ := by
      rw [ht₁E e₂ he₂]
    _ = e₁ * e₂ * (rootDiagUnit .E6 a * t₂) := by group
    _ = e₂ * e₁ * (t₂ * rootDiagUnit .E6 a) := by
      rw [hE.comm he₁ he₂, ht12]
    _ = e₂ * (e₁ * t₂) * rootDiagUnit .E6 a := by group
    _ = e₂ * (t₂ * e₁) * rootDiagUnit .E6 a := by
      rw [ht₂E e₁ he₁]
    _ = (e₂ * t₂) * (e₁ * rootDiagUnit .E6 a) := by group

private theorem exists_mul_pow_of_centralizer
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    (hA3 : Nat.card ((E.subgroupOf (monomialSubgroup .E6 L)).map
      (weylQuotientHom .E6 L)) = 3)
    {c : ModGL .E6 L} (hc : c ∈ adjointGroup .E6 L) (hcE : ∀ e ∈ E, c * e = e * c) :
    ∃ e ∈ E, ∃ d : ModGL .E6 L, (∀ m : ℕ, ∃ c' ∈ adjointGroup .E6 L,
      (∀ e ∈ E, c' * e = e * c') ∧ d = c' ^ 3 ^ m) ∧ c = e * d := by
  obtain ⟨e, he, t, ht, htE, hce⟩ :=
    exists_mul_torus_of_commute hL hEM hE hcard hET hAS hAg hc hcE
  obtain ⟨e', he', d, hd, hte⟩ :=
    exists_mul_pow_of_torus hL hEM hE hcard hET hAS hAg hA3 ht htE
  exact ⟨e * e', E.mul_mem he he', d, hd, by rw [hce, hte]; group⟩

theorem mem_of_centralizer_of_weyl_fpf
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    {n : ModGL .E6 L} (hnE : n ∈ E)
    {v : Multiplicative (Fin 3 → ZMod 3)} (hv : ∀ i, v.toAdd i ≠ 0)
    (hnv : weylQuotientHom .E6 L ⟨n,hEM hnE⟩ = modelHomE6 (SemidirectProduct.inl v))
    {c : ModGL .E6 L} (hc : c ∈ adjointGroup .E6 L) (hcE : ∀ e ∈ E, c * e = e * c) :
    c ∈ E := by
  obtain ⟨e, he, t, ht, htE, rfl⟩ :=
    exists_mul_torus_of_commute hL hEM hE hcard hET hAS hAg hc hcE
  have ht3 : t ^ 3 = 1 :=
    pow_three_eq_one_of_commute (hEM hnE) hv hnv ht (htE (n : ModGL .E6 L) hnE)
  exact E.mul_mem he
    (mem_of_torus_of_commute hL hEM hE hcard hET hAS hAg ht htE ht3)

theorem mem_of_centralizer_of_nine
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    (hA9 : 9 ≤ Nat.card ((E.subgroupOf (monomialSubgroup .E6 L)).map
      (weylQuotientHom .E6 L)))
    {c : ModGL .E6 L} (hc : c ∈ adjointGroup .E6 L) (hcE : ∀ e ∈ E, c * e = e * c) :
    c ∈ E := by
  obtain ⟨v, hv, hvA⟩ := exists_inl_mem
    ((E.subgroupOf (monomialSubgroup .E6 L)).map (weylQuotientHom .E6 L))
    (weylImage_le_modelRange hEM hAS) (isElemAbelian_weylImage hE)
    (weylImage_not_mem_gE6 hEM hAg) hA9
  obtain ⟨n, hnsub, hnv⟩ := Subgroup.mem_map.mp hvA
  have hnE : (n : ModGL .E6 L) ∈ E := Subgroup.mem_subgroupOf.mp hnsub
  have hnv' : weylQuotientHom .E6 L ⟨(n : ModGL .E6 L), hEM hnE⟩ =
      modelHomE6 (SemidirectProduct.inl v) := by
    rw [show (⟨(n : ModGL .E6 L), hEM hnE⟩ : monomialSubgroup .E6 L) = n from
      Subtype.ext rfl]
    exact hnv
  exact mem_of_centralizer_of_weyl_fpf hL hEM hE hcard hET hAS hAg hnE hv hnv' hc hcE

theorem exists_mul_connected_of_centralizer
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    {c : ModGL .E6 L} (hc : c ∈ adjointGroup .E6 L) (hcE : ∀ e ∈ E, c * e = e * c) :
    ∃ e ∈ E, ∃ d ∈ CFSG.LieType.AlgebraicGroups.closedIdentityComponent
      (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))), c = e * d := by
  rcases weylImage_card_cases hEM hcard hET with hA3 | hA9
  · obtain ⟨e, he, t, ht, htE, hct⟩ :=
      exists_mul_torus_of_commute hL hEM hE hcard hET hAS hAg hc hcE
    obtain ⟨e', he', d, hd, htd⟩ :=
      exists_mul_connected_of_torus hL hEM hE hcard hET hAS hAg hA3 ht htE
    exact ⟨e * e', E.mul_mem he he', d, hd, by rw [hct, htd]; group⟩
  · exact ⟨c, mem_of_centralizer_of_nine hL hEM hE hcard hET hAS hAg hA9 hc hcE,
      1, Subgroup.one_mem _, by simp⟩

theorem cube_mem_closedIdentityComponent_of_mem_centralizer
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i)
    {c : ModGL .E6 L}
    (hc : c ∈ adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))) :
    c ^ 3 ∈ CFSG.LieType.AlgebraicGroups.closedIdentityComponent
      (adjointGroup .E6 L ⊓ Subgroup.centralizer (E : Set (ModGL .E6 L))) := by
  obtain ⟨e, he, d, hd, rfl⟩ := exists_mul_connected_of_centralizer hL hEM hE hcard hET hAS hAg
    hc.1 (fun x hx => (Subgroup.mem_centralizer_iff.mp hc.2 x hx).symm)
  have he3 : e ^ 3 = 1 := hE.2 e he
  have hdC := (CFSG.LieType.AlgebraicGroups.closedIdentityComponent_le _ hd).2
  have hcomm : Commute e d := Subgroup.mem_centralizer_iff.mp hdC e he
  rw [hcomm.mul_pow, he3, one_mul]
  exact Subgroup.pow_mem _ hd 3

theorem centralizer_clauses
    {L : Type} [Field L] [IsAlgClosed L] (hL : ringChar L ≠ 3)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ 4) (hET : ¬ E ≤ torusGroup .E6 L)
    (hAS : ∀ e (he : e ∈ E), weylQuotientHom .E6 L ⟨e, hEM he⟩ ∈ modelHomE6.range)
    (hAg : ∀ e (he : e ∈ E) i, weylQuotientHom .E6 L ⟨e, hEM he⟩ ≠ gE6 i) :
    (∀ x ∈ adjointGroup .E6 L, ∀ y ∈ adjointGroup .E6 L,
        (∀ e ∈ E, x * e = e * x) → (∀ e ∈ E, y * e = e * y) → x * y = y * x) ∧
      (∀ c ∈ adjointGroup .E6 L, (∀ e ∈ E, c * e = e * c) →
        ∃ e ∈ E, ∃ d : ModGL .E6 L, (∀ m : ℕ, ∃ c' ∈ adjointGroup .E6 L,
          (∀ e ∈ E, c' * e = e * c') ∧ d = c' ^ 3 ^ m) ∧ c = e * d) ∧
      {d : ModGL .E6 L | (∀ m : ℕ, ∃ c' ∈ adjointGroup .E6 L,
        (∀ e ∈ E, c' * e = e * c') ∧ d = c' ^ 3 ^ m) ∧ d ^ 3 = 1}.encard ≤ 9 := by
  have hAcase := weylImage_card_cases hEM hcard hET
  refine ⟨commute_of_centralizer hL hEM hE hcard hET hAS hAg, ?_, ?_⟩
  · intro c hc hcE
    rcases hAcase with hA3 | hA9
    · exact exists_mul_pow_of_centralizer hL hEM hE hcard hET hAS hAg hA3 hc hcE
    · have hmem : c ∈ E :=
        mem_of_centralizer_of_nine hL hEM hE hcard hET hAS hAg hA9 hc hcE
      exact ⟨c, hmem, 1, fun m =>
        ⟨1, one_mem (adjointGroup .E6 L), (by intro e he; simp), (by simp)⟩, by simp⟩
  · rcases hAcase with hA3 | hA9
    · exact encard_le_nine hL hEM hE hcard hET hAS hAg hA3
    · have hsub : {d : ModGL .E6 L | (∀ m : ℕ, ∃ c' ∈ adjointGroup .E6 L,
          (∀ e ∈ E, c' * e = e * c') ∧ d = c' ^ 3 ^ m) ∧ d ^ 3 = 1} ⊆ {1} := by
        rintro d ⟨hd, -⟩
        obtain ⟨c', hc'G, hc'E, hd1⟩ := hd 1
        have hc'mem : c' ∈ E :=
          mem_of_centralizer_of_nine hL hEM hE hcard hET hAS hAg hA9 hc'G hc'E
        have hd1' : d = c' ^ 3 := by simpa using hd1
        rw [Set.mem_singleton_iff, hd1']
        exact hE.2 c' hc'mem
      refine (Set.encard_le_encard hsub).trans ?_
      rw [Set.encard_singleton]
      norm_num

end CFSG.StandardType.E6NonToralThree
