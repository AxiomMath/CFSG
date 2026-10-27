module

public import CFSG.Quasithin.H13.NQBlockOddRankOneBridge
public import CFSG.LocalAnalysis.SectionRank.ClassicalOdd
public import CFSG.LinearAlgebra.SteinbergBQEvenSL2OddCyclic

public section

namespace CFSG.Quasithin.H13.QTESylow

open CFSG.ComponentClassification.CatalogueSchreierLinearTwo CFSG.LinearGroups
  CFSG.Assembly.LowTwoRank CFSG.Open
open scoped Pointwise MatrixGroups

theorem not_isCyclic_of_isElemAbelian {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    {A : Subgroup G} (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) : ¬ IsCyclic A := by
  intro hcyc
  have hfin : Finite A := Nat.finite_of_card_ne_zero (by rw [hAc]; exact pow_ne_zero _ hp.ne_zero)
  have hexp : Monoid.exponent A ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hA.2 x x.2)
  rw [IsCyclic.exponent_eq_card, hAc] at hexp
  have := Nat.le_of_dvd hp.pos hexp
  have h2 : p < p ^ 2 := by
    rw [sq]
    exact lt_mul_self hp.one_lt
  omega

theorem isCyclic_of_mulEquiv_of_pGroups_cyclic {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {p : ℕ} {A : Subgroup X} (hA : IsPGroup p A)
    (hY : ∀ P : Subgroup Y, IsPGroup p P → IsCyclic P) :
    IsCyclic A := by
  have hcyc := hY (A.map e.toMonoidHom) (hA.map e.toMonoidHom)
  have e' := A.equivMapOfInjective e.toMonoidHom e.injective
  exact isCyclic_of_surjective e'.symm.toMonoidHom e'.symm.surjective

theorem center_sl2_eq_bot_of_charTwo {K : Type*} [Field K] [CharP K 2] :
    Subgroup.center (SL(2, K)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hA
  obtain ⟨r, hr, hrA⟩ := hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have h : (r - 1) ^ 2 = 0 := by
      have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      have e1 : (r - 1) ^ 2 = r ^ 2 - 2 * r + 1 := by ring
      have e2 : (1 : K) + 1 = 2 := by norm_num
      rw [e1, hr, h2, zero_mul, sub_zero, e2, h2]
    exact sub_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 h)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, hr1]
  simp

@[expose] noncomputable def pslEquivSlOfCharTwo (K : Type*) [Field K] [CharP K 2] :
    Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃* SL(2, K) :=
  (QuotientGroup.quotientMulEquivOfEq center_sl2_eq_bot_of_charTwo).trans
    (QuotientGroup.quotientBot)

section Coordinate

variable {K : Type} [Field K]

theorem translation_one_ne_one : translation K 1 ≠ 1 := by
  intro h
  have := congrArg (fun g : Equiv.Perm (Omega K) => g (some 0)) h
  simp [translation_some] at this

theorem coordinateU_subgroupOf_ne_bot :
    (coordinateU K).subgroupOf (coordinateG K) ≠ ⊥ := by
  intro h
  have hmem : (⟨translation K 1, coordinateU_le_coordinateG (translation_mem_coordinateU 1)⟩ :
      coordinateG K) ∈ (coordinateU K).subgroupOf (coordinateG K) := by
    rw [Subgroup.mem_subgroupOf]
    exact translation_mem_coordinateU 1
  rw [h, Subgroup.mem_bot] at hmem
  exact translation_one_ne_one (congrArg Subtype.val hmem)

theorem coordinateU_le_stabilizer :
    (coordinateU K).subgroupOf (coordinateG K) ≤
      MulAction.stabilizer (coordinateG K) (none : Omega K) := by
  rw [← coordinateB_subgroupOf_eq_stabilizer]
  intro u hu
  rw [Subgroup.mem_subgroupOf] at hu ⊢
  exact coordinateU_le_coordinateB hu

theorem coordinateU_normal_stabilizer :
    (((coordinateU K).subgroupOf (coordinateG K)).subgroupOf
      (MulAction.stabilizer (coordinateG K) (none : Omega K))).Normal := by
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hn ⊢
  have hg : ((g : coordinateG K) : Equiv.Perm (Omega K)) ∈ coordinateB K := by
    have hg' : ((g : coordinateG K) : Equiv.Perm (Omega K)) none = none := g.2
    exact mem_coordinateB_iff.2 ⟨(g : coordinateG K).2, hg'⟩
  exact conj_mem_coordinateU hg hn

theorem coordinateU_transitive (β γ : Omega K) (hβ : β ≠ none) (hγ : γ ≠ none) :
    ∃ u ∈ (coordinateU K).subgroupOf (coordinateG K), u • β = γ := by
  obtain ⟨x, rfl⟩ := Option.ne_none_iff_exists'.1 hβ
  obtain ⟨y, rfl⟩ := Option.ne_none_iff_exists'.1 hγ
  refine ⟨⟨translation K (y - x), coordinateU_le_coordinateG (translation_mem_coordinateU _)⟩,
    ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact translation_mem_coordinateU _
  · show translation K (y - x) (some x) = some y
    rw [translation_some]
    congr 1
    ring

theorem le_stabilizer_of_coordinateU_le [IsSimpleGroup (coordinateG K)]
    {M : Subgroup (coordinateG K)} (hM : M < ⊤)
    (hUM : (coordinateU K).subgroupOf (coordinateG K) ≤ M) :
    M ≤ MulAction.stabilizer (coordinateG K) (none : Omega K) :=
  CFSG.Quasithin.H13.U3.simple_transitive_root_proper_overgroups (none : Omega K)
    coordinateU_subgroupOf_ne_bot coordinateU_le_stabilizer coordinateU_normal_stabilizer
    coordinateU_transitive hM hUM

end Coordinate

theorem not_pow_two_of_odd {q k : ℕ} (hq : 5 ≤ q) (hodd : Odd q) : q * q - 1 ≠ 2 * 2 ^ k := by
  intro h
  obtain ⟨m, rfl⟩ := hodd
  have hfac : (2 * m + 1) * (2 * m + 1) - 1 = 4 * (m * (m + 1)) := by
    have : (2 * m + 1) * (2 * m + 1) = 4 * (m * (m + 1)) + 1 := by ring
    omega
  rw [hfac] at h
  have hk : 1 ≤ k := by
    rcases k with _ | k
    · have : 2 ≤ m := by omega
      have : 4 * (m * (m + 1)) ≥ 24 := by nlinarith
      norm_num at h
      omega
    · omega
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  have h' : m * (m + 1) = 2 ^ k' := by
    have : 4 * (m * (m + 1)) = 4 * 2 ^ k' := by rw [h]; ring
    omega
  have hm : m ∣ 2 ^ k' := ⟨m + 1, h'.symm⟩
  have hm1 : m + 1 ∣ 2 ^ k' := ⟨m, by rw [← h']; ring⟩
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hm
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hm1
  have h2m : 2 ≤ m := by omega
  have ha1 : 1 ≤ a := by
    rcases a with _ | a
    · simp at ha
      omega
    · omega
  have hb1 : 1 ≤ b := by
    rcases b with _ | b
    · simp at hb
      omega
    · omega
  have hev : Even m := by
    rw [ha]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have hev1 : Even (m + 1) := by
    rw [hb]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩)
  exact (Nat.not_even_iff_odd.2 (Even.add_one hev)) hev1

theorem false_of_mul_comm_card_sq {S : Type} [Group S] [Finite S] [IsSimpleGroup S] {K : Type}
    [Field K] [Finite K] {p : ℕ} [hp : Fact p.Prime] [CharP K p] (hp5 : 5 ≤ p)
    (hK : Nat.card K = p ^ 2) (Φ : S ≃* coordinateG K) (T : Sylow 2 S) (A : Subgroup S)
    (hAc : Nat.card A = p ^ 2) (hcardS : Nat.card S = p ^ 2 * (((p ^ 2) ^ 2 - 1) / 2))
    (hAT : (A : Set S) * (T : Set S) = (T : Set S) * (A : Set S)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (coordinateG K) := Φ.symm.isSimpleGroup
  have hUcard : Nat.card ((coordinateU K).subgroupOf (coordinateG K)) = p ^ 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe coordinateU_le_coordinateG).toEquiv,
      card_coordinateU, hK]
  have hA'card : Nat.card (A.map Φ.toMonoidHom) = p ^ 2 := by
    rw [Subgroup.card_map_of_injective Φ.injective, hAc]
  obtain ⟨R, hR⟩ := (IsPGroup.of_card hA'card).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (coordinateG K) (coordinateUSylow K p) R
  have hRU : (R : Subgroup (coordinateG K)) =
      ((coordinateU K).subgroupOf (coordinateG K)).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, coe_coordinateUSylow, Subgroup.pointwise_smul_def]
    rfl
  have hRcard : Nat.card (R : Subgroup (coordinateG K)) = p ^ 2 := by
    rw [hRU, Subgroup.card_map_of_injective (MulAut.conj g).injective, hUcard]
  have hA'R : A.map Φ.toMonoidHom = R := Subgroup.eq_of_le_of_card_ge hR (by rw [hRcard, hA'card])
  set c : S →* coordinateG K := (MulAut.conj g⁻¹).toMonoidHom.comp Φ.toMonoidHom with hc
  have hcinj : Function.Injective c := (MulAut.conj g⁻¹).injective.comp Φ.injective
  have hcA : A.map c = (coordinateU K).subgroupOf (coordinateG K) := by
    rw [hc, ← Subgroup.map_map, hA'R, hRU, Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id ((coordinateU K).subgroupOf (coordinateG K))]
    congr 1
    ext x
    simp
  set V : Subgroup (coordinateG K) := (T : Subgroup S).map c with hV
  have hVcard : Nat.card V = Nat.card (T : Subgroup S) := Subgroup.card_map_of_injective hcinj
  have hUV : (((coordinateU K).subgroupOf (coordinateG K) : Subgroup (coordinateG K)) :
      Set (coordinateG K)) * (V : Set (coordinateG K)) =
      (V : Set (coordinateG K)) * ((coordinateU K).subgroupOf (coordinateG K) : Set _) := by
    have hAT' : (A : Set S) * ((T : Subgroup S) : Set S) =
        ((T : Subgroup S) : Set S) * (A : Set S) := hAT
    rw [← hcA, hV, Subgroup.coe_map, Subgroup.coe_map, ← Set.image_mul, hAT', Set.image_mul]
  set M := CFSG.Quasithin.H13.NQBlock.mulCommSubgroup _ _ hUV with hM
  have hUM : (coordinateU K).subgroupOf (coordinateG K) ≤ M := fun u hu =>
    ⟨u, hu, 1, V.one_mem, mul_one u⟩
  have hVM : V ≤ M := fun v hv =>
    ⟨1, ((coordinateU K).subgroupOf (coordinateG K)).one_mem, v, hv, one_mul v⟩
  have hMle : Nat.card M ≤ p ^ 2 * Nat.card (T : Subgroup S) := by
    have h1 : Nat.card M ≤ Nat.card ((coordinateU K).subgroupOf (coordinateG K)) * Nat.card V :=
      Set.natCard_mul_le
    rwa [hUcard, hVcard] at h1
  have hG : Nat.card (coordinateG K) = Nat.card S := (Nat.card_congr Φ.toEquiv).symm
  have hpodd : Odd p := hp.out.odd_of_ne_two (by omega)
  have hqodd : Odd (p ^ 2) := hpodd.pow
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp T.isPGroup'
  have hTdvd : Nat.card (T : Subgroup S) ∣ Nat.card S := Subgroup.card_subgroup_dvd_card _
  by_cases hMtop : M = ⊤
  ·
    have h1 : Nat.card S ≤ p ^ 2 * Nat.card (T : Subgroup S) := by
      rw [← hG, ← Subgroup.card_top (G := coordinateG K), ← hMtop]
      exact hMle
    rw [hcardS] at h1 hTdvd
    have h2 : ((p ^ 2) ^ 2 - 1) / 2 ≤ 2 ^ k := by
      rw [hk] at h1
      exact Nat.le_of_mul_le_mul_left h1 (by positivity)
    have hcop : Nat.Coprime (2 ^ k) (p ^ 2) :=
      Nat.Coprime.pow_left k ((Nat.coprime_two_left).2 hqodd)
    have h3 : 2 ^ k ∣ ((p ^ 2) ^ 2 - 1) / 2 := by
      rw [hk] at hTdvd
      exact hcop.dvd_of_dvd_mul_left hTdvd
    have hpos : 0 < ((p ^ 2) ^ 2 - 1) / 2 := by
      have : 25 ≤ p ^ 2 := by nlinarith
      have : 625 ≤ (p ^ 2) ^ 2 := by nlinarith
      omega
    have h4 : ((p ^ 2) ^ 2 - 1) / 2 = 2 ^ k := le_antisymm h2 (Nat.le_of_dvd hpos h3)
    have h5 : p ^ 2 * p ^ 2 - 1 = 2 * 2 ^ k := by
      have hev : Even ((p ^ 2) ^ 2 - 1) := by
        have : Odd ((p ^ 2) ^ 2) := hqodd.pow
        exact Nat.Odd.sub_odd this odd_one
      rw [← sq, ← h4]
      obtain ⟨r, hr⟩ := hev
      omega
    exact not_pow_two_of_odd (by nlinarith) hqodd h5
  ·
    have hMst := le_stabilizer_of_coordinateU_le (lt_top_iff_ne_top.2 hMtop) hUM
    have hVst := hVM.trans hMst
    have hst : Nat.card (MulAction.stabilizer (coordinateG K) (none : Omega K)) =
        Nat.card (coordinateB K) := by
      rw [← coordinateB_subgroupOf_eq_stabilizer,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe coordinateB_le_coordinateG).toEquiv]
    have h1 : Nat.card (T : Subgroup S) ∣ Nat.card (coordinateB K) := by
      rw [← hst, ← hVcard]
      exact Subgroup.card_dvd_of_le hVst
    have h2 : 2 * Nat.card (T : Subgroup S) ∣ Nat.card S := by
      rw [← hG, card_coordinateG, hK]
      have hev : Even (p ^ 2 + 1) := hqodd.add_one
      obtain ⟨r, hr⟩ := hev
      rw [hr, show r + r = 2 * r by ring, mul_assoc]
      exact mul_dvd_mul_left 2 (Dvd.dvd.mul_left h1 r)
    have h3 := Subgroup.card_mul_index (T : Subgroup S)
    have hTpos : 0 < Nat.card (T : Subgroup S) := Nat.card_pos
    have h4 : 2 ∣ (T : Subgroup S).index := by
      rw [← h3, mul_comm] at h2
      exact Nat.dvd_of_mul_dvd_mul_left hTpos h2
    exact T.not_dvd_index h4

theorem projective_linear_two_odd_plane_sylow_product_exclusion (S : Type) [Group S] [Finite S]
    [IsSimpleGroup S] (hSQT : CFSG.IsStronglyQuasithin S) {ℓ f : ℕ}
    (hS : StatedClassicalModel S .PSL 2 ℓ f) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (T : Sylow 2 S) (A : Subgroup S) (hA : IsElemAbelian p A) (hAc : Nat.card A = p ^ 2) :
    (A : Set S) * (T : Set S) ≠ (T : Set S) * (A : Set S) := by
  classical
  intro hAT
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnc := not_isCyclic_of_isElemAbelian hp hA hAc
  have hAp : IsPGroup p A := IsPGroup.of_card hAc
  obtain ⟨⟨hℓ, hf, -⟩, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := id hS
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fintype K := Fintype.ofFinite K
  have hchar : CharP K ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hKcard])
  set ψ : S ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) K :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm with hψ
  by_cases hℓ2 : ℓ = 2
  ·
    subst hℓ2
    apply hnc
    refine isCyclic_of_mulEquiv_of_pGroups_cyclic (ψ.trans (pslEquivSlOfCharTwo K)) hAp
      fun P hP => ?_
    exact CFSG.LinearAlgebra.even_SL2_odd_prime_subgroups_cyclic (by omega) P hP
  obtain ⟨-, -, hcardS, -, -, -, hcyc⟩ := CFSG.SectionRank.OddCover.odd_psl_two_sylow_data
    (K := K) hℓ2 hKcard
  have hcardS' : Nat.card S = ℓ ^ f * (((ℓ ^ f) ^ 2 - 1) / 2) := by
    rw [Nat.card_congr e.toEquiv, hcardS]
  by_cases hpℓ : p = ℓ
  swap
  · apply hnc
    have hpcyc : ∀ P : Subgroup (StatedProj (StatedSL 2 K)), IsPGroup p P → IsCyclic P := by
      intro P hP
      obtain ⟨R, hR⟩ := hP.exists_le_sylow
      have := hcyc p hp (by omega) hpℓ R
      exact Subgroup.isCyclic_of_le hR
    exact isCyclic_of_mulEquiv_of_pGroups_cyclic e hAp hpcyc
  subst hpℓ
  have hrank : ∀ q : ℕ, q.Prime → q ≠ 2 → CFSG.Open.pRank q (⊤ : Subgroup S) ≤ 2 := by
    intro q hq hq2
    have := hSQT q hq hq2
    rwa [CFSG.SectionRank.pRank_eq_open_pRank_top] at this
  rcases CFSG.SectionRank.sqt_odd_classical_restriction hrank hℓ2 hS with
    ⟨-, -, hf12⟩ | ⟨-, h, -⟩ | ⟨h, -⟩
  · rcases hf12 with rfl | rfl
    ·
      have hdvd := Subgroup.card_subgroup_dvd_card A
      rw [hAc, hcardS', pow_one] at hdvd
      have hdvd' : p * p ∣ p * ((p ^ 2 - 1) / 2) := by
        rw [← sq]
        exact hdvd
      have h1 : p ∣ (p ^ 2 - 1) / 2 := Nat.dvd_of_mul_dvd_mul_left hp.pos hdvd'
      have h2 : p ∣ p ^ 2 - 1 := h1.trans (Nat.div_dvd_of_dvd (by
        have : Odd (p ^ 2) := (hp.odd_of_ne_two (by omega)).pow
        exact (Nat.Odd.sub_odd this odd_one).two_dvd))
      have h3 : p ∣ p ^ 2 := dvd_pow_self p (by norm_num)
      have h4 : p ∣ 1 := by
        have := Nat.dvd_sub h3 h2
        rwa [Nat.sub_sub_self (Nat.one_le_pow _ _ hp.pos)] at this
      exact hp.one_lt.ne' (Nat.dvd_one.1 h4)
    ·
      exact false_of_mul_comm_card_sq hp5 hKcard (ψ.trans (pslEquivCoordinateG K)) T A hAc
        hcardS' hAT
  · exact absurd h (by norm_num)
  · exact absurd h (by decide)

end CFSG.Quasithin.H13.QTESylow
