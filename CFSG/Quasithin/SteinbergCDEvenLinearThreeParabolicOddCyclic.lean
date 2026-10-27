module

public import CFSG.LieType.SteinbergBRLinearSmallParabolic

public section

namespace CFSG.Quasithin.SteinbergCD

open Subgroup Matrix Module CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.SteinbergBR.BlockPar

variable {F : Type*} [Field F]

theorem isCyclic_of_injective_GL_one {G : Type*} [Group G] [Finite G] (f : G →* GL (Fin 1) F)
    (hf : Function.Injective f) : IsCyclic G := by
  refine isCyclic_of_injective_ringHom
    (((Units.coeHom F).comp Matrix.GeneralLinearGroup.det).comp f) fun x y hxy => hf ?_
  have h : ((f x : GL (Fin 1) F) : Matrix (Fin 1) (Fin 1) F) 0 0 =
      ((f y : GL (Fin 1) F) : Matrix (Fin 1) (Fin 1) F) 0 0 := by
    have e := hxy
    simp only [MonoidHom.comp_apply, Units.coeHom_apply, Matrix.GeneralLinearGroup.val_det_apply,
      Matrix.det_unique] at e
    exact e
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]
  exact h

theorem isCyclic_quotient_of_ker_le [Finite F] {n d e : ℕ} (h : d + e = n)
    {s : SpecialLinearGroup (Fin n) F} {W : Submodule F (Fin n → F)}
    (hs : (flagSpace n F d).map (mulVecLin s.val) = W) {P B : Subgroup (projectiveSL n F)}
    (hP : P = (stabilizer W).map (proj n F)) [(B.subgroupOf P).Normal]
    (χ : (parQ : Subgroup (SpecialLinearGroup (Fin d ⊕ Fin e) F)) →* GL (Fin 1) F)
    (hχ : ∀ M ∈ χ.ker, proj n F (transportSL F h s M) ∈ B) :
    IsCyclic (P ⧸ B.subgroupOf P) := by
  have hmem : ∀ M : (parQ : Subgroup (SpecialLinearGroup (Fin d ⊕ Fin e) F)),
      proj n F (transportSL F h s M) ∈ P := fun M => by
    rw [hP]
    exact ⟨_, (mem_parQ_iff_transport h hs M).1 M.2, rfl⟩
  set Ψ : (parQ : Subgroup (SpecialLinearGroup (Fin d ⊕ Fin e) F)) →* P ⧸ B.subgroupOf P :=
    (QuotientGroup.mk' (B.subgroupOf P)).comp
      (((proj n F).comp ((transportSL F h s).toMonoidHom.comp parQ.subtype)).codRestrict P
        hmem) with hΨ
  have hΨs : Function.Surjective Ψ := by
    intro x
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective (B.subgroupOf P) x
    have hx' := hx
    rw [hP] at hx'
    obtain ⟨g, hg, rfl⟩ := hx'
    refine ⟨⟨(transportSL F h s).symm g, (mem_parQ_iff_transport h hs _).2 (by
      rwa [MulEquiv.apply_symm_apply])⟩, ?_⟩
    rw [hΨ, MonoidHom.comp_apply]
    congr 1
    apply Subtype.ext
    change proj n F (transportSL F h s ((transportSL F h s).symm g)) = proj n F g
    rw [MulEquiv.apply_symm_apply]
  have hker : χ.ker ≤ Ψ.ker := fun M hM => by
    rw [MonoidHom.mem_ker, hΨ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, mem_subgroupOf]
    exact hχ M hM
  have : IsCyclic ((parQ : Subgroup (SpecialLinearGroup (Fin d ⊕ Fin e) F)) ⧸ χ.ker) :=
    isCyclic_of_injective_GL_one (QuotientGroup.kerLift χ) (QuotientGroup.kerLift_injective χ)
  exact isCyclic_of_surjective (QuotientGroup.lift χ.ker Ψ hker)
    (QuotientGroup.lift_surjective_of_surjective _ _ hΨs _)

theorem even_projective_linear_three_parabolic_solvable_normal_odd_cyclic {k : Type*} [Field k]
    [Finite k] (hk : Even (Nat.card k)) (hk4 : 4 ≤ Nat.card k) (E : Submodule k (Fin 3 → k))
    (hE : finrank k E = 1 ∨ finrank k E = 2) {P N : Subgroup (projectiveSL 3 k)}
    (hP : P = (stabilizer E).map (proj 3 k)) (hNP : N ≤ P) (hNn : (N.subgroupOf P).Normal)
    (hN : Group.IsSolvable N) :
    (∀ A : Subgroup (projectiveSL 3 k), A ≤ N → ∀ r m : ℕ, r.Prime → r ≠ 2 →
        Nat.card A = r ^ m → IsCyclic A) ∧
      ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ S : Sylow r N, IsCyclic (S : Subgroup N) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : ringChar k = 2 := by
    have := Fintype.ofFinite k
    rw [FiniteField.even_card_iff_char_two, ← Nat.card_eq_fintype_card, ← Nat.even_iff]
    exact hk
  have : CharP k 2 := ringChar.of_eq hchar
  obtain ⟨f, hqf⟩ : ∃ f : ℕ, Nat.card k = 2 ^ f := by
    have := Fintype.ofFinite k
    obtain ⟨f, -, hf⟩ := FiniteField.card k 2
    exact ⟨f, by rw [Nat.card_eq_fintype_card, hf]⟩
  set d := finrank k E with hd
  have hd1 : 1 ≤ d := by omega
  have hd3 : d < 3 := by omega
  set B := (CFSG.perfectResidual P).map P.subtype with hB
  have hBP : B ≤ P := map_subtype_le _
  have hB' : B.subgroupOf P = CFSG.perfectResidual P :=
    comap_map_eq_self_of_injective P.subtype_injective _
  have : (B.subgroupOf P).Normal := by
    rw [hB']
    infer_instance
  obtain ⟨-, -, -, -, hRad, -, -, hcardU, -⟩ :=
    CFSG.LieType.linear_small_parabolic_perfect_residual_structure hk hd1 hd3
      (Or.inl ⟨rfl, hk4⟩) E hd.symm hP hB
  have hcyc : IsCyclic (P ⧸ B.subgroupOf P) := by
    obtain ⟨s, hs⟩ := exists_map_flagSpace_eq E
    rcases hE with h1 | h2
    · rw [← hd, h1] at hs
      obtain ⟨-, hR1, -⟩ := CFSG.LieType.linear_small_parabolic_perfect_residual_structure hk
        (d := 1) le_rfl (by norm_num) (Or.inl ⟨rfl, hk4⟩) E (hd.symm.trans h1) hP hB
      have hset := (hR1 (by norm_num)).2 s hs
      refine isCyclic_quotient_of_ker_le (Nat.add_sub_of_le (by norm_num : 1 < 3).le) hs hP
        (chiL k (Fin 1) (Fin (3 - 1))) fun M hM => ?_
      have hM' := hM
      rw [ker_chiL, mem_subgroupOf, mem_parJR] at hM'
      have hdet := det_eq_of_mem_parQ hM'.1
      rw [hM'.2, det_one, one_mul] at hdet
      have hmem : proj 3 k (transportSL k (Nat.add_sub_of_le (by norm_num : 1 < 3).le) s M) ∈
          (B : Set (projectiveSL 3 k)) := by
        rw [hset]
        exact ⟨M, ⟨mem_parQ.1 hM'.1, hM'.2, hdet⟩, rfl⟩
      exact hmem
    · rw [← hd, h2] at hs
      obtain ⟨hL2, -⟩ := CFSG.LieType.linear_small_parabolic_perfect_residual_structure hk
        (d := 2) (by norm_num) (by norm_num) (Or.inl ⟨rfl, hk4⟩) E (hd.symm.trans h2) hP hB
      have hset := (hL2 (by norm_num)).2 s hs
      refine isCyclic_quotient_of_ker_le (Nat.add_sub_of_le (by norm_num : 2 < 3).le) hs hP
        (chiR k (Fin 2) (Fin (3 - 2))) fun M hM => ?_
      have hM' := hM
      rw [ker_chiR, mem_subgroupOf, mem_parJL] at hM'
      have hdet := det_eq_of_mem_parQ hM'.1
      rw [hM'.2, det_one, mul_one] at hdet
      have hmem : proj 3 k (transportSL k (Nat.add_sub_of_le (by norm_num : 2 < 3).le) s M) ∈
          (B : Set (projectiveSL 3 k)) := by
        rw [hset]
        exact ⟨M, ⟨mem_parQ.1 hM'.1, hdet, hM'.2⟩, rfl⟩
      exact hmem
  have hU2 : IsPGroup 2 ((radU k E).map (proj 3 k)) :=
    IsPGroup.of_card (n := f * (d * (3 - d)))
      (by rw [hcardU, hqf, ← pow_mul])
  have hNB : N ⊓ B ≤ (radU k E).map (proj 3 k) := by
    intro x hx
    obtain ⟨hxN, hxB⟩ := mem_inf.1 hx
    have hnormal : (N.subgroupOf B).Normal := ⟨fun n hn b => by
      rw [mem_subgroupOf] at hn ⊢
      have h := hNn.conj_mem ⟨n, hNP hn⟩ hn ⟨b, hBP b.2⟩
      exact h⟩
    have := hN
    have hsolv : Group.IsSolvable (N.subgroupOf B) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (B.subtype.comp (N.subgroupOf B).subtype).codRestrict N fun y => y.2)
        fun y z hyz => Subtype.ext (Subtype.ext
          (congrArg (fun w : N => (w : projectiveSL 3 k)) hyz))
    have hle : N.subgroupOf B ≤ CFSG.solvableRadical B := le_sSup ⟨hnormal, hsolv⟩
    have h := hle (show (⟨x, hxB⟩ : B) ∈ N.subgroupOf B from hxN)
    rw [hRad, mem_subgroupOf] at h
    exact h
  have hmain : ∀ A : Subgroup (projectiveSL 3 k), A ≤ N → ∀ r m : ℕ, r.Prime → r ≠ 2 →
      Nat.card A = r ^ m → IsCyclic A := by
    intro A hAN r m hr hr2 hcard
    have : Fact r.Prime := ⟨hr⟩
    have hA : IsPGroup r A := IsPGroup.of_card hcard
    have hdisj := IsPGroup.disjoint_of_ne r 2 hr2 A _ hA hU2
    have hι : Function.Injective ((QuotientGroup.mk' (B.subgroupOf P)).comp
        (inclusion (hAN.trans hNP))) := by
      rw [injective_iff_map_eq_one]
      intro a ha
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        mem_subgroupOf, coe_inclusion] at ha
      have hx : (a : projectiveSL 3 k) ∈ A ⊓ (radU k E).map (proj 3 k) :=
        ⟨a.2, hNB ⟨hAN a.2, ha⟩⟩
      have h1 := disjoint_iff_inf_le.1 hdisj hx
      rw [mem_bot] at h1
      exact Subtype.ext h1
    have e := MonoidHom.ofInjective hι
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  refine ⟨hmain, fun r hr hr2 S => ?_⟩
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 (S.isPGroup'.map N.subtype)
  have hc := hmain _ (map_subtype_le _) r m hr hr2 hm
  have e : (S : Subgroup N) ≃* (S : Subgroup N).map N.subtype :=
    (S : Subgroup N).equivMapOfInjective _ N.subtype_injective
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

end CFSG.Quasithin.SteinbergCD
