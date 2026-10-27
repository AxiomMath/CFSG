module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148SComp
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SSylow
public import CFSG.RankThree.PartTwo.Sec13.Item131bProofHeis

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.Blueprint
open CFSG.RankThree.PartTwo.Toolkit

theorem isExtOf_A6_of_card {X : Type} [Group X] [Finite X] (hX : IsType425 X)
    (h : Nat.card X = 1080) :
    IsExtOf X (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) := by
  have hZ3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  rcases hX with hX | ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩ | ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩ | ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩
  · exact absurd h (Sec13.Item131bProof.card_ne_of_isSLThreePi hX)
  · exact ⟨N, hN, ⟨eN⟩, ⟨eQ⟩⟩
  all_goals
    exfalso
    have hcard : Nat.card X = Nat.card N * Nat.card (X ⧸ N) :=
      (Subgroup.card_eq_card_quotient_mul_card_subgroup N).trans (mul_comm _ _)
    rw [Nat.card_congr eN.toEquiv, Nat.card_congr eQ.toEquiv, hZ3, h] at hcard
  · rw [KFacts.KS14.card_alternatingGroup_fin (by norm_num)] at hcard
    norm_num [Nat.factorial] at hcard
  · rw [KFacts.KS14.card_nativeM22] at hcard
    norm_num at hcard

section A6Facts

@[expose] def m12c3 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 1 2

@[expose] def m12d3 : Equiv.Perm (Fin 6) := Equiv.swap 3 4 * Equiv.swap 4 5

@[expose] def m12y0 : Equiv.Perm (Fin 6) :=
  Equiv.swap 0 4 * Equiv.swap 0 1 * Equiv.swap 0 3 * Equiv.swap 2 5

@[expose] def m12L9 : List (Equiv.Perm (Fin 6)) :=
  [1, m12c3, m12c3 * m12c3, m12d3, m12d3 * m12d3, m12c3 * m12d3, m12c3 * m12c3 * m12d3,
    m12c3 * m12d3 * m12d3, m12c3 * m12c3 * m12d3 * m12d3]

theorem m12L9_mul : ∀ p ∈ m12L9, ∀ q ∈ m12L9, p * q ∈ m12L9 := by decide +kernel

theorem m12L9_inv : ∀ p ∈ m12L9, p⁻¹ ∈ m12L9 := by decide +kernel

theorem m12L9_one : (1 : Equiv.Perm (Fin 6)) ∈ m12L9 := by decide +kernel

theorem m12L9_sign : ∀ p ∈ m12L9, Equiv.Perm.sign p = 1 := by decide +kernel

theorem m12L9_card : m12L9.toFinset.card = 9 := by decide +kernel

theorem m12y0_sign : Equiv.Perm.sign m12y0 = 1 := by decide +kernel

theorem m12L9_conj : ∀ p ∈ m12L9, m12y0 * p * m12y0⁻¹ ∈ m12L9 := by decide +kernel

theorem m12L9_conj' : ∀ p ∈ m12L9, m12y0⁻¹ * p * m12y0 ∈ m12L9 := by decide +kernel

theorem m12y0_sq_not_mem : m12y0 * m12y0 ∉ m12L9 := by decide +kernel

theorem m12y0_mem : m12y0 ∈ alternatingGroup (Fin 6) :=
  Equiv.Perm.mem_alternatingGroup.mpr m12y0_sign

@[expose] def m12y0A : alternatingGroup (Fin 6) := ⟨m12y0, m12y0_mem⟩

theorem coe_m12y0A : ((m12y0A : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) = m12y0 := rfl

@[expose] def m12Q0 : Subgroup (Equiv.Perm (Fin 6)) where
  carrier := {x | x ∈ m12L9}
  mul_mem' := fun {a b} ha hb => m12L9_mul a ha b hb
  one_mem' := m12L9_one
  inv_mem' := fun {a} ha => m12L9_inv a ha

theorem m12Q0_le : m12Q0 ≤ alternatingGroup (Fin 6) := by
  intro x hx
  exact Equiv.Perm.mem_alternatingGroup.mpr (m12L9_sign x hx)

theorem card_m12Q0 : Nat.card m12Q0 = 9 := by
  have h : (m12Q0 : Set (Equiv.Perm (Fin 6))) = ↑m12L9.toFinset := by
    ext x
    simp [m12Q0]
  rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq, Set.ncard_coe_finset, m12L9_card]

@[expose] def A6Q0 : Subgroup (alternatingGroup (Fin 6)) :=
  m12Q0.subgroupOf (alternatingGroup (Fin 6))

theorem mem_A6Q0_iff (a : alternatingGroup (Fin 6)) :
    a ∈ A6Q0 ↔ (a : Equiv.Perm (Fin 6)) ∈ m12L9 := Iff.rfl

theorem card_A6Q0 : Nat.card A6Q0 = 9 := by
  rw [← card_m12Q0]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe m12Q0_le).toEquiv

theorem card_alternatingGroup6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [KFacts.KS14.card_alternatingGroup_fin (by norm_num)]
  decide

theorem A6Q0_conj (a : alternatingGroup (Fin 6)) :
    a ∈ A6Q0 ↔ m12y0A * a * m12y0A⁻¹ ∈ A6Q0 := by
  have h : ((m12y0A * a * m12y0A⁻¹ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) =
      m12y0 * (a : Equiv.Perm (Fin 6)) * m12y0⁻¹ := by
    simp [coe_m12y0A]
  rw [mem_A6Q0_iff, mem_A6Q0_iff, h]
  constructor
  · exact m12L9_conj _
  · intro hm
    have h2 := m12L9_conj' _ hm
    have h3 : m12y0⁻¹ * (m12y0 * (a : Equiv.Perm (Fin 6)) * m12y0⁻¹) * m12y0 =
        (a : Equiv.Perm (Fin 6)) := by group
    rwa [h3] at h2

theorem card_comap_A6Q0 {K : Type} [Group K] [Finite K] (f : K →* alternatingGroup (Fin 6))
    (hf : Function.Surjective f) (hK : Nat.card K = 1080) :
    Nat.card (A6Q0.comap f) = 27 := by
  have h1 := Subgroup.index_mul_card (H := A6Q0)
  rw [card_A6Q0, card_alternatingGroup6] at h1
  have ha : A6Q0.index = 40 := by omega
  have h2 := Subgroup.index_mul_card (H := A6Q0.comap f)
  rw [Subgroup.index_comap_of_surjective (H := A6Q0) hf, ha, hK] at h2
  omega

end A6Facts

theorem theta_eq_bot_of_m12 {S : Type} [Group S] [Finite S] {K : Subgroup S}
    (hKq : IsQuasisimple K) (P : Sylow 3 S) (hPK : (P : Subgroup S) ≤ K)
    (hP : M12SylowData (P : Subgroup S)) : aschbacherSolvableCore 3 K = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, -, -, -, -, E, F, A, A', hset, -, -, -, -, -, -, -, hcE, -, -, -, -, -⟩ := hP
  have hEP : E ≤ (P : Subgroup S) := by
    have hmem : E ∈ {B : Subgroup S | B ≤ (P : Subgroup S) ∧ Nat.card B = 9} := by
      rw [hset]
      simp
    exact hmem.1
  have hZ : ∀ z : K, z ∈ Subgroup.center K → (z : S) ∈ (P : Subgroup S) := by
    intro z hz
    have hcent : (z : S) ∈ Subgroup.centralizer ((P : Subgroup S) : Set S) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hxK : x ∈ K := hPK hx
      have h1 := Subgroup.mem_center_iff.mp hz ⟨x, hxK⟩
      have h2 := congrArg Subtype.val h1
      simpa using h2
    have hcentE : (z : S) ∈ Subgroup.centralizer ((E : Subgroup S) : Set S) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hEP) hcent
    rw [hcE] at hcentE
    exact hEP hcentE
  have hθ3 : IsPGroup 3 (Subgroup.center K) := by
    have hP3 : IsPGroup 3 ((P : Subgroup S).comap K.subtype) :=
      P.isPGroup'.comap_of_injective K.subtype K.subtype_injective
    refine hP3.to_le ?_
    intro z hz
    exact hZ z hz
  exact theta_eq_bot_of_center_three hKq hθ3

theorem noCQ425_of_m12 {S : Type} [Group S] [Finite S] (hS : Nat.card S = 95040)
    (hloc : M12ThreeLocalData S) : NoCQ425 S := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro s K hs3 hsK hKs hKq hT
  have h81 : ¬ 81 ∣ Nat.card S := by rw [hS]; norm_num
  obtain ⟨P0, hP0K, -, -⟩ := exists_sylow_le h81 hs3 hsK hKs hKq hT
  have hθ : aschbacherSolvableCore 3 K = ⊥ := theta_eq_bot_of_m12 hKq P0 hP0K (hloc P0)
  have hdvd : Nat.card (K ⧸ aschbacherSolvableCore 3 K) ∣ 95040 := by
    rw [← hS]
    exact (card_theta_quot_dvd K).trans (Subgroup.card_subgroup_dvd_card K)
  have hmem := card_mem_typeOrders425 (isQuasisimple_theta_quot hKq) (M := 95040) (B := 46)
    (by norm_num) (by norm_num) hT hdvd
  have htype : typeOrders425 95040 46 = [1080] := by decide +kernel
  rw [htype] at hmem
  have h1080 : Nat.card (K ⧸ aschbacherSolvableCore 3 K) = 1080 := List.mem_singleton.mp hmem
  let e : K ⧸ aschbacherSolvableCore 3 K ≃* K :=
    (QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot
  have hK : Nat.card K = 1080 := (Nat.card_congr e.toEquiv).symm.trans h1080
  have hext := isExtOf_congr e (isExtOf_A6_of_card hT h1080)
  obtain ⟨N, hN, hker, hquot⟩ := hext
  obtain ⟨eQ⟩ := hquot
  obtain ⟨f, hf⟩ : ∃ f : K →* alternatingGroup (Fin 6), Function.Surjective f :=
    ⟨eQ.toMonoidHom.comp (QuotientGroup.mk' N),
      eQ.surjective.comp (QuotientGroup.mk'_surjective N)⟩
  have hRcard : Nat.card (A6Q0.comap f) = 27 := card_comap_A6Q0 f hf hK
  obtain ⟨P1, hP1def⟩ : ∃ P1 : Subgroup S, P1 = (A6Q0.comap f).map K.subtype := ⟨_, rfl⟩
  have hP1card : Nat.card P1 = 27 := by
    rw [hP1def, Subgroup.card_map_of_injective K.subtype_injective, hRcard]
  have hP1 : IsPGroup 3 P1 := IsPGroup.of_card (n := 3) (by rw [hP1card]; norm_num)
  obtain ⟨P', hP'⟩ := hP1.exists_le_sylow
  obtain ⟨-, hP'card, -, hQ, -⟩ := hloc P'
  have hPeq : P1 = (P' : Subgroup S) :=
    Subgroup.eq_of_le_of_card_ge hP' (by rw [hP'card, hP1card])
  have hmemP1 : ∀ x : S, x ∈ P1 ↔ ∃ y : K, y ∈ A6Q0.comap f ∧ (y : S) = x := by
    intro x
    rw [hP1def, Subgroup.mem_map]
    rfl
  obtain ⟨k, hk⟩ := hf m12y0A
  have hconjR : ∀ x : K, x ∈ A6Q0.comap f ↔ k * x * k⁻¹ ∈ A6Q0.comap f := by
    intro x
    rw [Subgroup.mem_comap, Subgroup.mem_comap, map_mul, map_mul, map_inv, hk]
    exact A6Q0_conj (f x)
  have hconjS : ∀ x : S, x ∈ P1 ↔ (k : S) * x * (k : S)⁻¹ ∈ P1 := by
    intro x
    rw [hmemP1, hmemP1]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨k * y * k⁻¹, (hconjR y).mp hy, ?_⟩
      simp
    · rintro ⟨z, hz, hzx⟩
      refine ⟨k⁻¹ * z * k, (hconjR (k⁻¹ * z * k)).mpr ?_, ?_⟩
      · have hyz : k * (k⁻¹ * z * k) * k⁻¹ = z := by group
        rw [hyz]
        exact hz
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hzx]
        group
  have hkN : (k : S) ∈ Subgroup.normalizer ((P' : Subgroup S) : Set S) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [← hPeq]
    exact hconjS x
  have hsq : (k : S) ^ 2 ∈ (P' : Subgroup S) := by
    have hexp : ∀ g : Subgroup.normalizer ((P' : Subgroup S) : Set S) ⧸
        (P' : Subgroup S).subgroupOf (Subgroup.normalizer ((P' : Subgroup S) : Set S)),
        g ^ 2 = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p 2 _)
    have h2 := hexp (QuotientGroup.mk (⟨(k : S), hkN⟩ :
      Subgroup.normalizer ((P' : Subgroup S) : Set S)))
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h2
    simpa using h2
  have hsq1 : (k : S) ^ 2 ∈ P1 := by
    rw [hPeq]
    exact hsq
  obtain ⟨y, hy, hyk⟩ := (hmemP1 _).mp hsq1
  have hyk' : y = k ^ 2 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hyk)
  rw [hyk'] at hy
  have h4 : m12y0A ^ 2 ∈ A6Q0 := by
    rw [Subgroup.mem_comap, map_pow, hk] at hy
    exact hy
  rw [mem_A6Q0_iff, Subgroup.coe_pow, coe_m12y0A, sq] at h4
  exact m12y0_sq_not_mem h4

section RowM12


theorem noCQOf_m12 : NoCQOf (Spor .M12) := by
  intro S _ _ _ _ ⟨e⟩
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  have b' : NativeSporadic.M12 ≃* Spor .M12 := b
  have e' : S ≃* NativeSporadic.M12 := e.trans b'.symm
  exact noCQ425_of_m12 ((Nat.card_congr e'.toEquiv).trans CFSG.Sporadic.Mathieu.card_M12)
    (m12ThreeLocalData S ⟨e'⟩)

theorem rowOf425_m12 : RowOf425 (Spor .M12) := rowOf425_of_noCQ noCQOf_m12

end RowM12

end CFSG.RankThree.PartTwo.Sec4.Ronan148S
