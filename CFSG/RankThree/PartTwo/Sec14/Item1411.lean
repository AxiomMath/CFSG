module

public import CFSG.RankThree.PartTwo.Sec14.Closure

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

variable {G : Type*} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

theorem isPGroup_of_mem_scriptQPi {p : ℕ} (hp : p.Prime) {Y Q : Subgroup G}
    (hQ : Q ∈ scriptQPi A LB Y (piOf p)) : IsPGroup p Q :=
  (isPiSubgroup_piOf_iff hp Q).mp hQ.2

omit [Finite G] in
theorem mem_scriptQPi_of_le {Y Q R : Subgroup G} {π : Set Nat.Primes}
    (hQ : Q ∈ scriptQPi A LB Y π) (hRQ : R ≤ Q) (hAR : A ≤ Subgroup.normalizer (R : Set G)) :
    R ∈ scriptQPi A LB Y π :=
  ⟨⟨mem_scriptQ_of_le hQ.1.1 hRQ hAR, hRQ.trans hQ.1.2⟩,
    fun q hq => hQ.2 q (hq.trans (Subgroup.card_dvd_of_le hRQ))⟩

omit [Finite G] in
theorem map_conj_mem_scriptQPi_top (hnat : IsNaturalFamily A LB) {w : G}
    (hw : w ∈ Subgroup.normalizer (A : Set G)) {Q : Subgroup G} {π : Set Nat.Primes}
    (hQ : Q ∈ scriptQPi A LB ⊤ π) : Q.map (MulAut.conj w).toMonoidHom ∈ scriptQPi A LB ⊤ π :=
  ⟨⟨rank3II_14_4_5 hnat hw hQ.1.1, le_top⟩, fun q hq => hQ.2 q (by
    rwa [Subgroup.card_map_of_injective (MulAut.conj w).injective] at hq)⟩

omit [Finite G] in
theorem maxIn_scriptQPi_top (Y : Subgroup G) (π : Set Nat.Primes) :
    maxIn (scriptQPi A LB ⊤ π) Y = scriptQPiStar A LB Y π := by
  have h : ∀ R, (R ∈ scriptQPi A LB ⊤ π ∧ R ≤ Y) ↔ R ∈ scriptQPi A LB Y π := fun R =>
    ⟨fun ⟨⟨⟨h1, _⟩, h2⟩, h3⟩ => ⟨⟨h1, h3⟩, h2⟩, fun ⟨⟨h1, h3⟩, h2⟩ => ⟨⟨⟨h1, le_top⟩, h2⟩, h3⟩⟩
  ext S
  simp only [maxIn, scriptQPiStar, Set.mem_ofPred_eq, h]

omit [Finite G] in
theorem ne_bot_of_not_isConjIn {V S T : Subgroup G} {π : Set Nat.Primes}
    (hS : Maximal (· ∈ scriptQPi A LB ⊤ π) S) (hT : Maximal (· ∈ scriptQPi A LB ⊤ π) T)
    (hST : ¬ IsConjIn V S T) : S ≠ ⊥ := by
  rintro rfl
  have hT' : T = ⊥ := le_bot_iff.mp (hS.2 hT.prop bot_le)
  exact hST (hT' ▸ isConjIn_refl V ⊥)

theorem exists_meet_of_not_isConjIn {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (hA : IsE27 A)
    {X S T : Subgroup G} (hS : S ∈ scriptQPiStar A LB ⊤ (piOf p))
    (hT : T ∈ scriptQPiStar A LB ⊤ (piOf p)) (hST : ¬ IsConjIn X S T) :
    ∃ a ∈ A, a ≠ 1 ∧ S ⊓ Subgroup.centralizer {a} ≠ ⊥ ∧ T ⊓ Subgroup.centralizer {a} ≠ ⊥ := by
  have hS0 : S ≠ ⊥ := ne_bot_of_not_isConjIn hS hT hST
  have hT0 : T ≠ ⊥ := ne_bot_of_not_isConjIn hT hS fun h => hST h.symm
  have hcop : ∀ Q : Subgroup G, Q ∈ scriptQPi A LB ⊤ (piOf p) → Nat.Coprime 3 (Nat.card Q) :=
    fun Q hQ => by
      have : Fact p.Prime := ⟨hp⟩
      obtain ⟨k, hk⟩ := (isPGroup_of_mem_scriptQPi hp hQ).exists_card_eq
      rw [hk]
      exact Nat.Coprime.pow_right k ((Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3))
  exact exists_ne_one_inf_centralizer_ne_bot hA hS0 hT0 hS.prop.1.1.1.2.2 hT.prop.1.1.1.2.2
    (hcop S hS.prop) (hcop T hT.prop)

theorem rank3II_14_17_1 (hA : IsE27 A) {X S T : Subgroup G}
    (hS : S ∈ scriptQPiStar A LB ⊤ (piOf 2)) (hT : T ∈ scriptQPiStar A LB ⊤ (piOf 2))
    (hST : ¬ IsConjIn X S T) :
    ∃ a ∈ A, a ≠ 1 ∧ S ⊓ Subgroup.centralizer {a} ≠ ⊥ ∧ T ⊓ Subgroup.centralizer {a} ≠ ⊥ :=
  exists_meet_of_not_isConjIn Nat.prime_two (by norm_num) hA hS hT hST

theorem normalizer_ne_top_of_isPGroup (hsimp : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {p : ℕ} [Fact p.Prime] {D : Subgroup G} (hD : D ≠ ⊥)
    (hDp : IsPGroup p D) : Subgroup.normalizer (D : Set G) ≠ ⊤ := by
  intro htop
  have : IsSimpleGroup G := hsimp
  have : D.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal D with h | h
  · exact hD h
  · subst h
    obtain ⟨a, b, hab⟩ := hnab
    have hGp : IsPGroup p G := hDp.of_equiv Subgroup.topEquiv
    have : Group.IsNilpotent G := hGp.isNilpotent
    have : IsSimpleGroup G := hsimp
    exact hab (IsSimpleGroup.comm_iff_isSolvable.2 inferInstance a b)

omit [Finite G] in
theorem centralizer_singleton_ne_top (hsimp : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) {a : G} (ha : a ≠ 1) :
    Subgroup.centralizer ({a} : Set G) ≠ ⊤ := by
  intro htop
  have hz : a ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ Subgroup.centralizer ({a} : Set G) := htop ▸ Subgroup.mem_top g
    exact Subgroup.mem_centralizer_singleton_iff.mp hg
  have : IsSimpleGroup G := hsimp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h, Subgroup.mem_bot] at hz
    exact ha hz
  · obtain ⟨x, y, hxy⟩ := hnab
    have hy : y ∈ Subgroup.center G := h ▸ Subgroup.mem_top y
    exact hxy ((Subgroup.mem_center_iff.mp hy x))

theorem isConjIn_of_local_scriptY {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    (hsimp : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hA : IsE27 A) (hnat : IsNaturalFamily A LB) {V : Subgroup G}
    (hVA : V ≤ Subgroup.normalizer (A : Set G))
    (hloc : ∀ Y ∈ scriptY A, ∀ S ∈ scriptQPiStar A LB Y (piOf p),
      ∀ T ∈ scriptQPiStar A LB Y (piOf p), IsConjIn (V ⊓ Y) S T)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A LB ⊤ (piOf p))
    (hT : T ∈ scriptQPiStar A LB ⊤ (piOf p)) : IsConjIn V S T := by
  have hp : p.Prime := Fact.out
  have hAab : IsMulCommutative A := hA.1.1
  have hlocY : ∀ Y ∈ scriptY A, IsLocallyTransitive V (scriptQPi A LB ⊤ (piOf p)) Y := by
    intro Y hY S' hS' T' hT'
    rw [maxIn_scriptQPi_top] at hS' hT'
    exact hloc Y hY S' hS' T' hT'
  refine isConjIn_of_maximal (p := p) (A := A)
    (hp := fun Q hQ => isPGroup_of_mem_scriptQPi hp hQ)
    (hA := fun Q hQ => hQ.1.1.1.2.2) (hsub := fun Q hQ R hRQ hAR => mem_scriptQPi_of_le hQ hRQ hAR)
    (hW := fun Q hQ w hw => map_conj_mem_scriptQPi_top hnat (hVA hw) hQ) ?_ hAab ?_ ?_ hS hT
  ·
    intro D hD hD0
    refine hlocY _ ⟨normalizer_ne_top_of_isPGroup hsimp hnab hD0
      (isPGroup_of_mem_scriptQPi hp hD), ?_⟩
    exact hD.1.1.1.2.2.trans Subgroup.le_normalizer
  ·
    intro a ha ha1
    refine hlocY _ ⟨centralizer_singleton_ne_top hsimp hnab ha1, ?_⟩
    refine le_trans (fun b hb => ?_) Subgroup.le_normalizer
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hAab.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩)
  ·
    intro S' T' hS' hT' hST' _
    exact exists_meet_of_not_isConjIn hp hp3 hA hS' hT' hST'

theorem rank3II_14_11_reduction (hsimp : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hA : IsE27 A) (hnat : IsNaturalFamily A LB) {V : Subgroup G}
    (hVA : V ≤ Subgroup.normalizer (A : Set G))
    (hloc : ∀ Y ∈ scriptY A, ∀ S ∈ scriptQPiStar A LB Y (piOf 2),
      ∀ T ∈ scriptQPiStar A LB Y (piOf 2), IsConjIn (V ⊓ Y) S T)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A LB ⊤ (piOf 2))
    (hT : T ∈ scriptQPiStar A LB ⊤ (piOf 2)) : IsConjIn V S T :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  isConjIn_of_local_scriptY (by norm_num) hsimp hnab hA hnat hVA hloc hS hT

theorem rank3II_14_11_1_reduction (hsimp : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hA : IsE27 A) (hnat : IsNaturalFamily A LB)
    (hloc : ∀ Y ∈ scriptY A, ∀ S ∈ scriptQPiStar A LB Y (piOf 2),
      ∀ T ∈ scriptQPiStar A LB Y (piOf 2),
        IsConjIn (Subgroup.normalizer (A : Set G) ⊓ Y) S T)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A LB ⊤ (piOf 2))
    (hT : T ∈ scriptQPiStar A LB ⊤ (piOf 2)) :
    IsConjIn (Subgroup.normalizer (A : Set G)) S T :=
  rank3II_14_11_reduction hsimp hnab hA hnat le_rfl hloc hS hT

theorem rank3II_14_11_2_reduction (hsimp : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hA : IsE27 A) (hnat : IsNaturalFamily A LB)
    (hloc : ∀ Y ∈ scriptY A, ∀ S ∈ scriptQPiStar A LB Y (piOf 2),
      ∀ T ∈ scriptQPiStar A LB Y (piOf 2),
        IsConjIn (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y) S T)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A LB ⊤ (piOf 2))
    (hT : T ∈ scriptQPiStar A LB ⊤ (piOf 2)) :
    IsConjIn (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) S T :=
  rank3II_14_11_reduction hsimp hnab hA hnat
    ((pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)) hloc hS hT

theorem rank3II_17_24_2_reduction {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    (hsimp : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hA : IsE27 A) (hnat : IsNaturalFamily A LB)
    (hloc : ∀ Y ∈ scriptY A, ∀ S ∈ scriptQPiStar A LB Y (piOf p),
      ∀ T ∈ scriptQPiStar A LB Y (piOf p),
        IsConjIn (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) ⊓ Y) S T)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A LB ⊤ (piOf p))
    (hT : T ∈ scriptQPiStar A LB ⊤ (piOf p)) :
    IsConjIn (pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G))) S T :=
  isConjIn_of_local_scriptY hp3 hsimp hnab hA hnat
    ((pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)) hloc hS hT

theorem rank3II_14_15_reduction (hnat : IsNaturalFamily A LB) {X : Subgroup G}
    (hXA : X ≤ Subgroup.normalizer (A : Set G))
    (hloc : ∀ U ∈ scriptQPi A LB ⊤ (piOf 2), U ≠ ⊥ →
      ∀ S ∈ scriptQPiStar A LB (Subgroup.normalizer (U : Set G)) (piOf 2),
      ∀ T ∈ scriptQPiStar A LB (Subgroup.normalizer (U : Set G)) (piOf 2),
        IsConjIn (X ⊓ Subgroup.normalizer (U : Set G)) S T)
    {S T : Subgroup G} (hS : S ∈ scriptQPiStar A LB ⊤ (piOf 2))
    (hT : T ∈ scriptQPiStar A LB ⊤ (piOf 2)) (hST : ¬ IsConjIn X S T) : S ⊓ T = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine inf_eq_bot_of_not_isConjIn (p := 2) (A := A)
    (hp := fun Q hQ => isPGroup_of_mem_scriptQPi Nat.prime_two hQ)
    (hA := fun Q hQ => hQ.1.1.1.2.2) (hsub := fun Q hQ R hRQ hAR => mem_scriptQPi_of_le hQ hRQ hAR)
    (hW := fun Q hQ w hw => map_conj_mem_scriptQPi_top hnat (hXA hw) hQ) ?_ hS hT hST
  intro D hD hD0 S' hS' T' hT'
  rw [maxIn_scriptQPi_top] at hS' hT'
  exact hloc D hD hD0 S' hS' T' hT'

end CFSG.RankThree.PartTwo.Sec14
