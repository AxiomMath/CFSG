module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12InvPlan
import CFSG.Sporadic.Schreier.RuElemAut
public import CFSG.RankThree.Asc83Table.GL23
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Transport

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace M12Inv

def invAut (B : Type*) [Group B] (hc : ∀ x y : B, x * y = y * x) : MulAut B where
  toFun x := x⁻¹
  invFun x := x⁻¹
  left_inv x := inv_inv x
  right_inv x := inv_inv x
  map_mul' x y := by rw [mul_inv_rev]; exact hc _ _

theorem exists_inverting_of_card_autIn {X : Type} [Group X] (B : Subgroup X)
    (hB9 : Nat.card B = 9) (hexp : ∀ x ∈ B, x ^ 3 = 1)
    (h48 : Nat.card (Sec4.autIn ⊤ B) = 48) :
    ∃ t ∈ Subgroup.normalizer (B : Set X), ∀ x ∈ B, t * x * t⁻¹ = x⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcomm : ∀ x y : B, x * y = y * x := fun x y =>
    (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hB9).is_comm.comm x y
  have hpow : ∀ x : B, x ^ 3 = 1 := fun x => Subtype.ext (by simpa using hexp x x.2)
  haveI : Finite B := Nat.finite_of_card_ne_zero (by omega)
  have hMulAut : Nat.card (MulAut B) = 48 := by
    rw [CFSG.Sporadic.RuSchreier.ru_card_mulAut_elementary hcomm hpow (n := 2)
      (by rw [hB9]; norm_num)]
    simp [Fin.prod_univ_succ]
  have htop : Sec4.autIn ⊤ B = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [h48, hMulAut])
  have hι : invAut B hcomm ∈ Sec4.autIn ⊤ B := htop ▸ Subgroup.mem_top _
  obtain ⟨h, hN, -, hh⟩ := Sec4.mem_autIn_iff.mp hι
  refine ⟨h, hN, fun x hx => ?_⟩
  have := congrArg (fun σ : MulAut B => ((σ ⟨x, hx⟩ : B) : X)) hh
  simpa [Sec4.normalizerMonoidHom_apply_coe, invAut] using this

theorem exists_two_normalized_of_perm_alt {X : Type} [Group X] {N : Subgroup X}
    (e : N ≃* Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) :
    ∃ V : Subgroup X, V ≠ ⊥ ∧ IsPGroup 2 V ∧ N ≤ Subgroup.normalizer (V : Set X) := by
  have h4 : Nat.card (Fin 4) = 4 := by simp
  haveI : (alternatingGroup.kleinFour (Fin 4)).Normal := alternatingGroup.normal_kleinFour h4
  set V0 : Subgroup (Equiv.Perm (Fin 3) × alternatingGroup (Fin 4)) :=
    (⊥ : Subgroup (Equiv.Perm (Fin 3))).prod (alternatingGroup.kleinFour (Fin 4)) with hV0
  haveI : V0.Normal := Subgroup.prod_normal _ _
  set V1 : Subgroup N := V0.map e.symm.toMonoidHom with hV1
  haveI : V1.Normal := Subgroup.Normal.map inferInstance _ e.symm.surjective
  have hV1mem : ∀ n : N, n ∈ V1 ↔ (e n).1 = 1 ∧ (e n).2 ∈ alternatingGroup.kleinFour (Fin 4) := by
    intro n
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa [hV0, Subgroup.mem_prod] using hw
    · rintro ⟨h1, h2⟩
      refine ⟨e n, ?_, by simp⟩
      show e n ∈ V0
      rw [hV0, Subgroup.mem_prod, h1]
      exact ⟨Subgroup.one_mem _, h2⟩
  refine ⟨V1.map N.subtype, ?_, ?_, ?_⟩
  ·
    have hk4 : Nat.card (alternatingGroup.kleinFour (Fin 4)) = 4 :=
      alternatingGroup.kleinFour_card_of_card_eq_four h4
    obtain ⟨k, hk1⟩ : ∃ k : alternatingGroup.kleinFour (Fin 4), k ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : Subsingleton (alternatingGroup.kleinFour (Fin 4)) :=
        ⟨fun x y => (hcon x).trans (hcon y).symm⟩
      have := Finite.card_le_one_iff_subsingleton.mpr this
      omega
    intro hbot
    have hmem : (e.symm (1, (k : alternatingGroup (Fin 4))) : N) ∈ V1 := by
      rw [hV1mem]
      simp
    have h1 : ((e.symm (1, (k : alternatingGroup (Fin 4))) : N) : X) ∈ V1.map N.subtype :=
      Subgroup.mem_map_of_mem _ hmem
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : e.symm (1, (k : alternatingGroup (Fin 4))) = 1 := Subtype.ext h1
    have h3 : ((1 : Equiv.Perm (Fin 3)), (k : alternatingGroup (Fin 4))) = 1 := by
      have := congrArg e h2
      simpa using this
    apply hk1
    apply Subtype.ext
    simpa using congrArg Prod.snd h3
  ·
    refine IsPGroup.map (p := 2) (H := V1) ?_ N.subtype
    rintro ⟨g, hg⟩
    refine ⟨1, Subtype.ext ?_⟩
    have h1 : (e g).1 = 1 := ((hV1mem g).mp hg).1
    have h2 := ((hV1mem g).mp hg).2
    have hexp : Monoid.exponent (alternatingGroup.kleinFour (Fin 4)) = 2 :=
      alternatingGroup.exponent_kleinFour_of_card_eq_four h4
    have hsq : ((e g).2) ^ 2 = 1 := by
      have := Monoid.pow_exponent_eq_one (⟨(e g).2, h2⟩ : alternatingGroup.kleinFour (Fin 4))
      rw [hexp] at this
      simpa using congrArg Subtype.val this
    have h3 : e (g ^ 2) = 1 := by
      rw [map_pow]
      refine Prod.ext ?_ ?_
      · simp [h1]
      · simpa using hsq
    have h4' : g ^ 2 = 1 := e.injective (h3.trans e.map_one.symm)
    simpa using h4'
  ·
    have hVN : V1.map N.subtype ≤ N := Subgroup.map_subtype_le V1
    have hcomap : (V1.map N.subtype).subgroupOf N = V1 :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective V1
    have : ((V1.map N.subtype).subgroupOf N).Normal := by
      rw [hcomap]
      infer_instance
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hVN).mp this

theorem exists_two_normalized_conj {X : Type} [Group X] {B V : Subgroup X} (g : X)
    (hV1 : V ≠ ⊥) (hV2 : IsPGroup 2 V) (hB : B ≤ Subgroup.normalizer (V : Set X)) :
    ∃ V' : Subgroup X, V' ≠ ⊥ ∧ IsPGroup 2 V' ∧
      B.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (V' : Set X) := by
  refine ⟨V.map (MulAut.conj g).toMonoidHom, ?_, hV2.map _, ?_⟩
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective V (f := (MulAut.conj g).toMonoidHom)
      (MulAut.conj g).injective]
  · have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hB
    rwa [Subgroup.map_equiv_normalizer_eq] at h

end M12Inv

open M12Inv in
theorem invPartE_of (h414 : Sec4.Item4_14_local) : InvPartE := by
  intro X _ hX B hB9
  obtain ⟨e⟩ := hX
  haveI : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num)
  obtain ⟨P, hBP⟩ := hB3.exists_le_sylow
  obtain ⟨hHeis, -, E, F, A, t, ht, -, hΔ, ⟨eE⟩, ⟨eF⟩, -, hNa⟩ := h414 X ⟨e⟩ P
  have hexpP : ∀ x ∈ (P : Subgroup X), x ^ 3 = 1 := by
    intro x hx
    have := Monoid.pow_exponent_eq_one (⟨x, hx⟩ : (P : Subgroup X))
    rw [hHeis.2.2] at this
    simpa using congrArg Subtype.val this
  have h48 : Nat.card (GL (Fin 2) (ZMod 3)) = 48 := CFSG.RankThree.Asc83Table.card_GL23
  have hBmem : B ∈ {B' : Subgroup X | B' ≤ (P : Subgroup X) ∧ Nat.card B' = 9} := ⟨hBP, hB9⟩
  rw [hΔ] at hBmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hBmem
  have hAmem : A ∈ {B' : Subgroup X | B' ≤ (P : Subgroup X) ∧ Nat.card B' = 9} := by
    rw [hΔ]
    simp
  obtain ⟨hAP, hA9⟩ := hAmem
  have hZP : Nat.card ((P : Subgroup X) ⊓
      Subgroup.centralizer ((P : Subgroup X) : Set X) : Subgroup X) = 3 := by
    rw [Sec4.Sporadic.inf_centralizer_eq_map_center,
      Subgroup.card_map_of_injective (P : Subgroup X).subtype_injective]
    exact hHeis.1.2.2.2
  obtain ⟨a, haA, haZ⟩ : ∃ a ∈ A, a ∉ (P : Subgroup X) ⊓
      Subgroup.centralizer ((P : Subgroup X) : Set X) := by
    by_contra hcon
    push Not at hcon
    have hle : A ≤ (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) :=
      fun a ha => hcon a ha
    have := Subgroup.card_le_of_le hle
    rw [hA9, hZP] at this
    omega
  have hAV : ∃ V : Subgroup X, V ≠ ⊥ ∧ IsPGroup 2 V ∧ A ≤ Subgroup.normalizer (V : Set X) := by
    have hAcomm : ∀ x y : A, x * y = y * x := fun x y =>
      (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) hA9).is_comm.comm x y
    have hAN : A ≤ Subgroup.normalizer (Subgroup.zpowers a : Set X) := by
      intro x hx
      exact centralizer_le_normalizer_zpowers a (Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hAcomm ⟨x, hx⟩ ⟨a, haA⟩)))
    obtain ⟨e'⟩ := hNa a haA haZ
    obtain ⟨V, hV1, hV2, hNV⟩ := exists_two_normalized_of_perm_alt e'
    exact ⟨V, hV1, hV2, hAN.trans hNV⟩
  rcases hBmem with rfl | rfl | rfl | rfl
  · exact Or.inl (exists_inverting_of_card_autIn B hB9 (fun x hx => hexpP x (hBP hx))
      (by rw [Nat.card_congr eE.toEquiv, h48]))
  · exact Or.inl (exists_inverting_of_card_autIn B hB9 (fun x hx => hexpP x (hBP hx))
      (by rw [Nat.card_congr eF.toEquiv, h48]))
  · obtain ⟨V, hV1, hV2, hNV⟩ := hAV
    exact Or.inr ⟨V, hV1, hV2, hNV⟩
  · obtain ⟨V, hV1, hV2, hNV⟩ := hAV
    obtain ⟨V', hV'1, hV'2, hNV'⟩ := exists_two_normalized_conj t⁻¹ hV1 hV2 hNV
    exact Or.inr ⟨V', hV'1, hV'2, hNV'⟩

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
