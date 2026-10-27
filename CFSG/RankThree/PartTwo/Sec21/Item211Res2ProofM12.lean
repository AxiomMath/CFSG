module

public import CFSG.RankThree.PartTwo.Sec21.Item211Res2ProofSmall
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.LocalAnalysis.ComponentClassification.M12CoverAut
import CFSG.RankThree.GroupTheory.SteinbergBYRelativeCores
import CFSG.RankThree.PartTwo.Sec4.Item47Kinds

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)


namespace Item211Res2Proof

theorem card_le_four_of_normal_of_isPGroup
    {K : Subgroup (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4))} (hK : K.Normal)
    (hK2 : IsPGroup 2 K) : Nat.card K ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) = 72 := by
    rw [Nat.card_prod, Nat.card_perm, nat_card_alternatingGroup]
    simp [Nat.factorial]
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hK2
  have hdvd : 2 ^ j ∣ 72 := by
    rw [← hj, ← hcard]
    exact Subgroup.card_subgroup_dvd_card K
  have hj3 : j ≤ 3 := by
    by_contra h
    have h4 : 2 ^ 4 ∣ 2 ^ j := Nat.pow_dvd_pow 2 (by omega)
    have := Nat.dvd_trans h4 hdvd
    norm_num at this
  rcases Nat.lt_or_ge j 3 with hj2 | hj2
  · rw [hj]
    calc 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 4 := by norm_num
  · exfalso
    have hj' : j = 3 := le_antisymm hj3 hj2
    have hQ : Nat.card ((Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) ⧸ K) = 9 := by
      have h := K.card_eq_card_quotient_mul_card_subgroup
      rw [hcard, hj, hj'] at h
      omega
    have hinv : ∀ τ : Equiv.Perm (Fin 3) × alternatingGroup (Fin 4), τ ^ 2 = 1 → τ ∈ K := by
      intro τ hτ
      have h1 : (QuotientGroup.mk τ : _ ⧸ K) ^ 2 = 1 := by
        rw [← QuotientGroup.mk_pow, hτ, QuotientGroup.mk_one]
      have h2 : orderOf (QuotientGroup.mk τ : _ ⧸ K) ∣ 9 := hQ ▸ orderOf_dvd_natCard _
      have h3 : orderOf (QuotientGroup.mk τ : _ ⧸ K) ∣ 2 := orderOf_dvd_of_pow_eq_one h1
      have h4 : orderOf (QuotientGroup.mk τ : _ ⧸ K) = 1 :=
        Nat.eq_one_of_dvd_coprimes (by norm_num) h3 h2
      rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h4
      exact h4
    have h1 : ((Equiv.swap 0 1, 1) : Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) ∈ K :=
      hinv _ (Prod.ext (by decide) (by simp))
    have h2 : ((Equiv.swap 0 2, 1) : Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) ∈ K :=
      hinv _ (Prod.ext (by decide) (by simp))
    have h12 := K.mul_mem h1 h2
    have h3 : (((Equiv.swap 0 1, 1) : Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) *
        (Equiv.swap 0 2, 1)) ^ 3 = 1 := Prod.ext (by decide) (by simp)
    have hne : (((Equiv.swap 0 1, 1) : Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) *
        (Equiv.swap 0 2, 1)) ≠ 1 := fun h => by
      have := congrArg Prod.fst h
      revert this
      decide
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hord : orderOf (⟨_, h12⟩ : K) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime h3 hne
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hK2) ⟨_, h12⟩
    rw [hord] at hk
    have h2dvd : 2 ∣ 3 := by
      rcases k with _ | k
      · simp at hk
      · rw [hk, pow_succ]
        exact Dvd.intro_left _ rfl
    omega

theorem mem_range_conj_M12 {d : MulAut NativeSporadic.M12} (hd : d ^ 3 = 1) :
    d ∈ (MulAut.conj : NativeSporadic.M12 →* MulAut NativeSporadic.M12).range :=
  Sec4.cubeInner_of_not_three_dvd_card_outer
    (by rw [CFSG.ComponentClassification.M12Cover.card_outer]; norm_num) d hd

theorem card_le_two_of_invariant_eq_bot {B : Subgroup NativeSporadic.M12}
    (hB : invariantPiSubgroups ⊤ B (piOf 2) = {⊥}) {T : Subgroup (MulAut NativeSporadic.M12)}
    (hT : IsPGroup 2 T)
    (hBT : B.map (MulAut.conj : NativeSporadic.M12 →* MulAut NativeSporadic.M12) ≤
      Subgroup.normalizer (T : Set (MulAut NativeSporadic.M12))) :
    Nat.card T ≤ 2 := by
  set ι : NativeSporadic.M12 →* MulAut NativeSporadic.M12 := MulAut.conj with hι
  have hinj : Function.Injective ι := CFSG.ComponentClassification.M12Cover.conj_injective
  set T₀ := T.comap ι with hT₀
  have hT₀2 : IsPGroup 2 T₀ := hT.comap_of_injective ι hinj
  have hBT₀ : B ≤ Subgroup.normalizer (T₀ : Set NativeSporadic.M12) := by
    intro b hb
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp (hBT ⟨b, hb, rfl⟩) (ι y)).mp hy
    change ι (b * y * b⁻¹) ∈ T
    rwa [map_mul, map_mul, map_inv]
  have hmem : T₀ ∈ invariantPiSubgroups ⊤ B (piOf 2) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hT₀2, hBT₀⟩
  rw [hB, Set.mem_singleton_iff] at hmem
  have hTinn : T ⊓ inner NativeSporadic.M12 = ⊥ := by
    rw [eq_bot_iff]
    rintro τ ⟨hτT, y, rfl⟩
    have hy : y ∈ T₀ := hτT
    rw [hmem, Subgroup.mem_bot] at hy
    rw [hy, map_one]
    exact Subgroup.one_mem _
  set φ := (QuotientGroup.mk' (inner NativeSporadic.M12)).comp T.subtype with hφ
  have hφinj : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro τ hτ
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hτ
    have h1 : (τ : MulAut NativeSporadic.M12) ∈ T ⊓ inner NativeSporadic.M12 := ⟨τ.2, hτ⟩
    rw [hTinn, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  have h := Nat.card_le_card_of_injective φ hφinj
  have hout : Nat.card (Outer NativeSporadic.M12) = 2 :=
    CFSG.ComponentClassification.M12Cover.card_outer
  change Nat.card T ≤ Nat.card (Outer NativeSporadic.M12) at h
  omega

theorem card_pCore_centralizer_le_four {X : Type} [Group X] [Finite X] {a : X}
    (e : Subgroup.normalizer (Subgroup.zpowers a : Set X) ≃*
      Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) :
    Nat.card (inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({a} : Set X))) ≤ 4 := by
  set C := Subgroup.centralizer ({a} : Set X) with hC
  set N := Subgroup.normalizer (Subgroup.zpowers a : Set X) with hN
  set O := inSubgroup (CFSG.pCore 2) C with hO
  have hO2 : IsPGroup 2 O := (CFSG.pCore_isPGroup).map C.subtype
  have hCN : C ≤ N := by
    intro x hx
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨k, rfl⟩ := hy
    have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    refine ⟨k, ?_⟩
    change a ^ k = x * a ^ k * x⁻¹
    rw [(Commute.zpow_right hxa k).eq, mul_inv_cancel_right]
  have hOC : O ≤ C := Subgroup.map_subtype_le _
  have hNC : N ≤ Subgroup.normalizer (C : Set X) := by
    intro n hn
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have hxa : x * a = a * x := Subgroup.mem_centralizer_singleton_iff.mp hx
    have h1 : n⁻¹ * a * n⁻¹⁻¹ ∈ Subgroup.zpowers a :=
      (Subgroup.mem_normalizer_iff.mp (N.inv_mem hn) a).mp (Subgroup.mem_zpowers a)
    obtain ⟨k, hk⟩ := h1
    have hk' : a ^ k = n⁻¹ * a * n := by simpa using hk
    have h2 : x * (n⁻¹ * a * n) = (n⁻¹ * a * n) * x := by
      rw [← hk']
      exact (Commute.zpow_right hxa k).eq
    calc n * x * n⁻¹ * a = n * (x * (n⁻¹ * a * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * a * n) * x) * n⁻¹ := by rw [h2]
      _ = a * (n * x * n⁻¹) := by group
  have hNO : N ≤ Subgroup.normalizer (O : Set X) :=
    hNC.trans (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_pCore
      2 C)
  set O' := O.subgroupOf N with hO'
  have hO'n : O'.Normal := by
    constructor
    intro x hx n
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hNO n.2) x).mp hx
  have hO'2 : IsPGroup 2 O' := hO2.comap_subtype
  set K := O'.map e.toMonoidHom with hK
  have hKn : K.Normal := Subgroup.Normal.map hO'n e.toMonoidHom e.surjective
  have hK2 : IsPGroup 2 K := hO'2.map _
  have h := card_le_four_of_normal_of_isPGroup hKn hK2
  rw [hK, Subgroup.card_map_of_injective e.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hOC.trans hCN)).toEquiv] at h
  exact h

theorem card_le_four_of_caseA (h14 : Sec4.Item4_14) (P : Sylow 3 NativeSporadic.M12)
    {A : Subgroup NativeSporadic.M12} (hAP : A ≤ P) (hA9 : Nat.card A = 9)
    (hAut : Nonempty (Sec4.autIn ⊤ A ≃* Equiv.Perm (Fin 3)))
    (hNa : ∀ a ∈ A, a ∉ (P : Subgroup NativeSporadic.M12) ⊓
        Subgroup.centralizer ((P : Subgroup NativeSporadic.M12) : Set NativeSporadic.M12) →
      Nonempty (Subgroup.normalizer (Subgroup.zpowers a : Set NativeSporadic.M12) ≃*
        Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)))
    (hZ3 : Nat.card ((P : Subgroup NativeSporadic.M12) ⊓
      Subgroup.centralizer ((P : Subgroup NativeSporadic.M12) : Set NativeSporadic.M12) :
        Subgroup NativeSporadic.M12) ≤ 3)
    {T : Subgroup (MulAut NativeSporadic.M12)} (hT : IsPGroup 2 T)
    (hAT : A.map (MulAut.conj : NativeSporadic.M12 →* MulAut NativeSporadic.M12) ≤
      Subgroup.normalizer (T : Set (MulAut NativeSporadic.M12))) :
    Nat.card T ≤ 4 := by
  obtain ⟨a, haA, haZ⟩ : ∃ a ∈ A, a ∉ (P : Subgroup NativeSporadic.M12) ⊓
      Subgroup.centralizer ((P : Subgroup NativeSporadic.M12) : Set NativeSporadic.M12) := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show A ≤ (P : Subgroup NativeSporadic.M12) ⊓
      Subgroup.centralizer ((P : Subgroup NativeSporadic.M12) : Set NativeSporadic.M12) from hcon)
    omega
  obtain ⟨e⟩ := hNa a haA haZ
  have hsig := ((h14.2 _ ⟨MulEquiv.refl _⟩ P A hAP hA9).2 hAut).2 a haA haZ
  have hTmem : T ∈ invariantPiSubgroups ⊤
      (A.map (MulAut.conj : NativeSporadic.M12 →* MulAut NativeSporadic.M12)) (piOf 2) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top, hT, hAT⟩
  obtain ⟨S, hS, hTS⟩ := exists_le_mem_maxInvariantPiSubgroups hTmem
  rw [← hsig] at hS
  obtain ⟨x, -, rfl⟩ := hS
  have hcard := card_pCore_centralizer_le_four e
  calc Nat.card T ≤ Nat.card ((conjugate (inSubgroup (CFSG.pCore 2)
        (Subgroup.centralizer ({a} : Set NativeSporadic.M12))) x).map
          (MulAut.conj : NativeSporadic.M12 →* MulAut NativeSporadic.M12)) :=
        Subgroup.card_le_of_le hTS
    _ = Nat.card (inSubgroup (CFSG.pCore 2)
        (Subgroup.centralizer ({a} : Set NativeSporadic.M12))) := by
        rw [Subgroup.card_map_of_injective CFSG.ComponentClassification.M12Cover.conj_injective,
          conjugate, Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective]
    _ ≤ 4 := hcard

end Item211Res2Proof

open Item211Res2Proof

theorem ks211TwoLocalM12_of
    (h14 : Sec4.Item4_14) : KS211TwoLocalM12 := by
  intro T D hT hD hD9 hDT
  set ι : NativeSporadic.M12 →* MulAut NativeSporadic.M12 := MulAut.conj with hι
  have hinj : Function.Injective ι := CFSG.ComponentClassification.M12Cover.conj_injective
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hDinn : D ≤ ι.range := fun d hd => mem_range_conj_M12 (hD.2 d hd)
  set Dh := D.comap ι with hDh
  have hDmap : Dh.map ι = D := Subgroup.map_comap_eq_self hDinn
  have hDh9 : Nat.card Dh = 9 := by
    rw [← hD9, ← hDmap, Subgroup.card_map_of_injective hinj]
  have hDh3 : IsPGroup 3 Dh := fun g =>
    ⟨1, Subtype.ext (hinj (by simpa using hD.2 _ g.2))⟩
  obtain ⟨P, hDhP⟩ := hDh3.exists_le_sylow
  obtain ⟨hHeis, -, E, F, A, t, -, -, hset, hE, hF, hA, hNa⟩ :=
    h14.1 _ ⟨MulEquiv.refl _⟩ P
  have hZ3 : Nat.card ((P : Subgroup NativeSporadic.M12) ⊓
      Subgroup.centralizer ((P : Subgroup NativeSporadic.M12) : Set NativeSporadic.M12) :
        Subgroup NativeSporadic.M12) ≤ 3 := by
    have hc := hHeis.1.2.2.2
    refine le_of_le_of_eq (Nat.card_le_card_of_injective (fun z => (⟨⟨z, z.2.1⟩, ?_⟩ :
      Subgroup.center (P : Subgroup NativeSporadic.M12))) ?_) hc
    · rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp z.2.2) w w.2)
    · intro z₁ z₂ h
      exact Subtype.ext (congrArg (fun w : Subgroup.center (P : Subgroup NativeSporadic.M12) =>
        ((w : (P : Subgroup NativeSporadic.M12)) : NativeSporadic.M12)) h)
  have hmem : Dh ∈ {B : Subgroup NativeSporadic.M12 | B ≤ P ∧ Nat.card B = 9} := ⟨hDhP, hDh9⟩
  have hmemE : E ∈ {B : Subgroup NativeSporadic.M12 | B ≤ P ∧ Nat.card B = 9} := by
    rw [hset]; simp
  have hmemF : F ∈ {B : Subgroup NativeSporadic.M12 | B ≤ P ∧ Nat.card B = 9} := by
    rw [hset]; simp
  have hmemA : A ∈ {B : Subgroup NativeSporadic.M12 | B ≤ P ∧ Nat.card B = 9} := by
    rw [hset]; simp
  rw [hset] at hmem
  rcases hmem with h | h | h | h
  ·
    have hB := (h14.2 _ ⟨MulEquiv.refl _⟩ P E hmemE.1 hmemE.2).1 hE
    have := card_le_two_of_invariant_eq_bot hB hT (by rw [← h, hDmap]; exact hDT)
    omega
  ·
    have hB := (h14.2 _ ⟨MulEquiv.refl _⟩ P F hmemF.1 hmemF.2).1 hF
    have := card_le_two_of_invariant_eq_bot hB hT (by rw [← h, hDmap]; exact hDT)
    omega
  ·
    exact card_le_four_of_caseA h14 P hmemA.1 hmemA.2 hA hNa hZ3 hT
      (by rw [← h, hDmap]; exact hDT)
  ·
    rw [Set.mem_singleton_iff] at h
    set γ : MulAut (MulAut NativeSporadic.M12) := MulAut.conj (ι t) with hγ
    have hTγ : IsPGroup 2 (T.map γ.toMonoidHom) := hT.map _
    have hDγ : D.map γ.toMonoidHom = A.map ι := by
      rw [← hDmap, h, conjugate, Subgroup.map_map, Subgroup.map_map]
      congr 1
      ext y
      simp [hγ, hι, MulAut.conj_apply, map_mul, map_inv]
    have hnorm : A.map ι ≤ Subgroup.normalizer ((T.map γ.toMonoidHom : Subgroup _) :
        Set (MulAut NativeSporadic.M12)) := by
      rw [← hDγ, ← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hDT
    have := card_le_four_of_caseA h14 P hmemA.1 hmemA.2 hA hNa hZ3 hTγ hnorm
    rwa [Subgroup.card_map_of_injective γ.injective] at this

section Certs


theorem item211ResidualSmall_of_item414
    (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (h14 : Sec4.Item4_14) (hS : KS211TwoLocalS7) (hON : Item211ResidualON) :
    Item211ResidualSmall :=
  item211ResidualSmall_of h45 h66 (ks211TwoLocalM12_of h14) hS hON

end Certs

end CFSG.RankThree.PartTwo.Sec21
