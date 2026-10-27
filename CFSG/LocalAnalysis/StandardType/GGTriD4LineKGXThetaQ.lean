module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineKGXFix
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineLocalANormal

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KGD

private lemma triD4LineThetaQ_map_injective {k L : Type} [Field k] [Field L] [Algebra k L] :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 3) (algebraMap k L)) := by
  intro A B h
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  have h' : (algebraMap k L) ((A : Matrix (Fin 3) (Fin 3) k) i j) =
      (algebraMap k L) ((B : Matrix (Fin 3) (Fin 3) k) i j) := by
    have := congrArg (fun (M : Matrix.SpecialLinearGroup (Fin 3) L) =>
      (M : Matrix (Fin 3) (Fin 3) L) i j) h
    rwa [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.map_apply_coe,
      RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at this
  exact (algebraMap k L).injective h'

private lemma triD4LineThetaQ_map_map {k L : Type} [Field k] [Field L] [Algebra k L]
    (Fr : L →+* L) (hFr : ∀ c : k, Fr (algebraMap k L c) = algebraMap k L c)
    (s : Matrix.SpecialLinearGroup (Fin 3) k) :
    Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map (algebraMap k L) s) =
      Matrix.SpecialLinearGroup.map (algebraMap k L) s := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply]
  exact hFr (s i j)

private lemma triD4LineThetaQ_d4A2Qv_le_adjointGroup {L : Type} [Field L]
    (v : WeylGroup Tag.D4) :
    d4A2Qv L v ≤ adjointGroup Tag.D4 L := by
  have hsub : subsystemGroup Tag.D4 L d4SuppA2 ≤ adjointGroup Tag.D4 L := by
    rw [subsystemGroup]
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨i, _, c, hg⟩
    rcases hg with rfl | rfl
    · exact xUnit_mem_adjointGroup i c
    · exact yUnit_mem_adjointGroup i c
  intro u hu
  rw [d4A2Qv, Subgroup.mem_map] at hu
  obtain ⟨s, hs, rfl⟩ := hu
  have hn := canonicalRep_mem_adjointGroup (coxeterSystem Tag.D4) L v
  exact mul_mem (mul_mem hn (hsub hs)) (inv_mem hn)

theorem triD4Line_exists_thetaQ
    {n : ℕ} (K : Type) [Field K] (hK : Nat.card K = (2 ^ n) ^ 3) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ 2 ^ n) (k : Type) [Field k] [Algebra k K] (hk : Nat.card k = 2 ^ n)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [Algebra k L] :
    ∃ θ : ↥(triD4LineNR K σ L) ≃* ↥(triD4LineN0 k K),
      ∀ (m : ↥(triD4LineNR K σ L)) (s : Matrix.SpecialLinearGroup (Fin 3) k),
        (θ m : TriD4LineX k K) = triD4LineSL3 k K s ↔
          (d4A2QvEquiv (K := L) triD4LineV ⟨triEmb K σ L m, m.2⟩ :
              Matrix.SpecialLinearGroup (Fin 3) L) =
            Matrix.SpecialLinearGroup.map (algebraMap k L) s := by
  classical
  haveI : Finite K := Nat.finite_of_card_ne_zero
    (by rw [hK]; exact pow_ne_zero 3 (pow_ne_zero n (by norm_num)))
  haveI : Fintype K := Fintype.ofFinite K
  have hcard2 : 2 ≤ Nat.card K := by
    rw [Nat.card_eq_fintype_card]
    have hlt := Fintype.one_lt_card (α := K)
    omega
  have hn : 1 ≤ n := by
    by_contra hn
    have h0 : n = 0 := by omega
    rw [h0, pow_zero, one_pow] at hK
    rw [Nat.card_eq_fintype_card] at hK
    have hlt := Fintype.one_lt_card (α := K)
    omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n * 3) (by
    rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  haveI : Finite k := Nat.finite_of_card_ne_zero
    (by rw [hk]; exact pow_ne_zero n (by norm_num))
  set Fr : L →+* L := iterateFrobenius L 2 n with hFrdef
  have hFr : ∀ c : L, Fr c = c ^ 2 ^ n := by
    intro c
    rw [hFrdef, congrFun (coe_iterateFrobenius L 2 n) c]
    exact iterate_frobenius 2 n c
  have hcomm : (algebraMap K L).comp σ.toRingHom = Fr.comp (algebraMap K L) := by
    ext c
    simp only [RingHom.comp_apply]
    change (algebraMap K L) (σ c) = Fr ((algebraMap K L) c)
    rw [hσ, map_pow, hFr]
  have hFrAlg : ∀ c : k, Fr (algebraMap k L c) = algebraMap k L c := fun c =>
    (CFSG.RankThree.PartOne.KE.frobenius_fixed_iff (K := k) (L := L) Fr
      (fun x => by rw [hFr, hk]) (algebraMap k L c)).2 ⟨c, rfl⟩
  let ψ : ↥(triD4LineNR K σ L) →* Matrix.SpecialLinearGroup (Fin 3) L :=
    (d4A2QvEquiv (K := L) triD4LineV).toMonoidHom.comp
      (MonoidHom.subgroupComap (triEmb K σ L) (d4A2Qv L triD4LineV))
  have hψ_apply : ∀ m : ↥(triD4LineNR K σ L),
      ψ m = d4A2QvEquiv (K := L) triD4LineV ⟨triEmb K σ L m, m.2⟩ := fun m => rfl
  have hψ : Function.Injective ψ := by
    have hsub_inj : Function.Injective
        (MonoidHom.subgroupComap (triEmb K σ L) (d4A2Qv L triD4LineV)) := by
      intro a b h
      apply Subtype.ext
      apply triEmb_injective (K := K) (σ := σ) (L := L)
      exact congrArg Subtype.val h
    intro a b hab
    exact hsub_inj ((d4A2QvEquiv (K := L) triD4LineV).injective hab)
  let φ : Matrix.SpecialLinearGroup (Fin 3) k →* Matrix.SpecialLinearGroup (Fin 3) L :=
    Matrix.SpecialLinearGroup.map (n := Fin 3) (algebraMap k L)
  have hφ : Function.Injective φ := triD4LineThetaQ_map_injective
  have hmem : ∀ m : ↥(triD4LineNR K σ L), ψ m ∈ φ.range := by
    intro m
    have hfixΦ : twistHom TwistTag.D4 L Fr (triEmb K σ L m) = triEmb K σ L m :=
      triEmb_fixed Fr hcomm m
    have hentry := triD4Line_twistHom_eq_entrywise L Fr (triEmb K σ L m) m.2
    have hFrFix : Units.map (entrywiseHom Fr) (triEmb K σ L m) = triEmb K σ L m :=
      hentry ▸ hfixΦ
    obtain ⟨hq', hentry2⟩ := triD4Line_entrywise_d4A2Qv L Fr (triEmb K σ L m) m.2
    have hmapx : Matrix.SpecialLinearGroup.map Fr (ψ m) = ψ m := by
      rw [hψ_apply m, ← hentry2]
      congr 1
      exact Subtype.ext hFrFix
    have hentry_fixed : ∀ i j,
        Fr (((ψ m : Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j) =
          ((ψ m : Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j := by
      intro i j
      have h := congrArg (fun (y : Matrix.SpecialLinearGroup (Fin 3) L) =>
        (y : Matrix (Fin 3) (Fin 3) L) i j) hmapx
      rwa [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply] at h
    let sM : Matrix (Fin 3) (Fin 3) k := fun i j => Classical.choose
      ((CFSG.RankThree.PartOne.KE.frobenius_fixed_iff (K := k) (L := L) Fr
        (fun x => by rw [hFr, hk])
        (((ψ m : Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j)).1
        (hentry_fixed i j))
    have hsM : ∀ i j, algebraMap k L (sM i j) =
        ((ψ m : Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j :=
      fun i j => Classical.choose_spec
        ((CFSG.RankThree.PartOne.KE.frobenius_fixed_iff (K := k) (L := L) Fr
          (fun x => by rw [hFr, hk])
          (((ψ m : Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j)).1
          (hentry_fixed i j))
    have hmat : sM.map (algebraMap k L) =
        ((ψ m : Matrix.SpecialLinearGroup (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) := by
      ext i j
      rw [Matrix.map_apply, hsM i j]
    have hsdet : sM.det = 1 := by
      apply (algebraMap k L).injective
      rw [map_one, RingHom.map_det, RingHom.mapMatrix_apply, hmat, (ψ m).2]
    let sSL : Matrix.SpecialLinearGroup (Fin 3) k := ⟨sM, hsdet⟩
    have hmapSL : φ sSL = ψ m := by
      change Matrix.SpecialLinearGroup.map (algebraMap k L) sSL = ψ m
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
      exact hmat
    exact ⟨sSL, hmapSL⟩
  have hpre : ∀ s : Matrix.SpecialLinearGroup (Fin 3) k, φ s ∈ ψ.range := by
    intro s
    let q' : ↥(d4A2Qv L triD4LineV) := (d4A2QvEquiv (K := L) triD4LineV).symm (φ s)
    have hq'_eq : d4A2QvEquiv (K := L) triD4LineV q' = φ s :=
      (d4A2QvEquiv (K := L) triD4LineV).apply_symm_apply (φ s)
    have hmapfix : Matrix.SpecialLinearGroup.map Fr (φ s) = φ s :=
      triD4LineThetaQ_map_map Fr hFrAlg s
    have hq'_entry : Units.map (entrywiseHom Fr) (q' : ModGL Tag.D4 L) =
        (q' : ModGL Tag.D4 L) := by
      obtain ⟨hq'', hentry''⟩ := triD4Line_entrywise_d4A2Qv L Fr (q' : ModGL Tag.D4 L) q'.2
      have hEq : (⟨Units.map (entrywiseHom Fr) (q' : ModGL Tag.D4 L), hq''⟩ :
          ↥(d4A2Qv L triD4LineV)) = q' := by
        apply (d4A2QvEquiv (K := L) triD4LineV).injective
        rw [hentry'']
        change Matrix.SpecialLinearGroup.map Fr
            (d4A2QvEquiv (K := L) triD4LineV ⟨(q' : ModGL Tag.D4 L), q'.2⟩) =
          d4A2QvEquiv (K := L) triD4LineV ⟨(q' : ModGL Tag.D4 L), q'.2⟩
        rw [hq'_eq, hmapfix]
      exact congrArg Subtype.val hEq
    have hΦq' : twistHom TwistTag.D4 L Fr (q' : ModGL Tag.D4 L) = (q' : ModGL Tag.D4 L) := by
      rw [triD4Line_twistHom_eq_entrywise L Fr (q' : ModGL Tag.D4 L) q'.2, hq'_entry]
    have hrange_triEmb := triEmb_range (ℓ := 2) (f := n) Nat.prime_two hn hK hσ Fr hFr
    have hq'mem : (q' : ModGL Tag.D4 L) ∈ (triEmb K σ L).range :=
      hrange_triEmb.symm ▸ Subgroup.mem_inf.2
        ⟨triD4LineThetaQ_d4A2Qv_le_adjointGroup triD4LineV q'.2, hΦq'⟩
    obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 hq'mem
    refine ⟨⟨y, ?_⟩, ?_⟩
    · exact (Subgroup.mem_comap).2 (hy.symm ▸ q'.2)
    · have hy' : (triEmb K σ L y : ModGL Tag.D4 L) = (q' : ModGL Tag.D4 L) := hy
      rw [hψ_apply]
      exact Eq.trans (congrArg (d4A2QvEquiv (K := L) triD4LineV) (Subtype.ext hy')) hq'_eq
  have hrange : ψ.range = φ.range := by
    apply le_antisymm
    · intro y hy
      obtain ⟨m, rfl⟩ := MonoidHom.mem_range.1 hy
      exact hmem m
    · intro y hy
      obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hy
      exact hpre s
  let eψ : ↥(triD4LineNR K σ L) ≃* ↥ψ.range := MonoidHom.ofInjective hψ
  let eC : ↥ψ.range ≃* ↥φ.range := MulEquiv.subgroupCongr hrange
  let eφ : Matrix.SpecialLinearGroup (Fin 3) k ≃* ↥φ.range := MonoidHom.ofInjective hφ
  let e : ↥(triD4LineNR K σ L) ≃* Matrix.SpecialLinearGroup (Fin 3) k :=
    eψ.trans (eC.trans eφ.symm)
  let eSL3 : Matrix.SpecialLinearGroup (Fin 3) k ≃* ↥(triD4LineN0 k K) :=
    (MonoidHom.ofInjective (triD4LineSL3_injective k K)).trans
      (MulEquiv.subgroupCongr (triD4LineSL3_range k K))
  have heSL3 : ∀ s : Matrix.SpecialLinearGroup (Fin 3) k,
      ((eSL3 s : ↥(triD4LineN0 k K)) : TriD4LineX k K) = triD4LineSL3 k K s := by
    intro s
    show ((MulEquiv.subgroupCongr (triD4LineSL3_range k K))
        (MonoidHom.ofInjective (triD4LineSL3_injective k K) s) : TriD4LineX k K) =
      triD4LineSL3 k K s
    exact MonoidHom.ofInjective_apply (triD4LineSL3_injective k K)
  have hvalC : ∀ x : ↥ψ.range,
      ((eC x : ↥φ.range) : Matrix.SpecialLinearGroup (Fin 3) L) =
        (x : Matrix.SpecialLinearGroup (Fin 3) L) := fun _ => rfl
  have hvalψ : ∀ m, ((eψ m : ↥ψ.range) : Matrix.SpecialLinearGroup (Fin 3) L) = ψ m :=
    fun m => MonoidHom.ofInjective_apply hψ
  have hvalφ : ∀ s, ((eφ s : ↥φ.range) : Matrix.SpecialLinearGroup (Fin 3) L) = φ s :=
    fun s => MonoidHom.ofInjective_apply hφ
  have he_apply : ∀ (m : ↥(triD4LineNR K σ L)) (s : Matrix.SpecialLinearGroup (Fin 3) k),
      e m = s ↔ ψ m = φ s := by
    intro m s
    have h1 : eφ (e m) = eC (eψ m) := by
      show eφ (eφ.symm (eC (eψ m))) = eC (eψ m)
      rw [MulEquiv.apply_symm_apply]
    have key : eφ (e m) = eφ s ↔ ψ m = φ s := by
      rw [h1]
      constructor
      · intro h
        have h2 := congrArg (fun x : ↥φ.range =>
          (x : Matrix.SpecialLinearGroup (Fin 3) L)) h
        rwa [hvalC, hvalφ, hvalψ] at h2
      · intro h
        apply Subtype.ext
        rw [hvalC, hvalφ, hvalψ]
        exact h
    exact ⟨fun h => key.1 (by rw [h]), fun h => eφ.injective (key.2 h)⟩
  let θ : ↥(triD4LineNR K σ L) ≃* ↥(triD4LineN0 k K) := e.trans eSL3
  refine ⟨θ, ?_⟩
  intro m s
  constructor
  · intro h
    have hθ : θ m = eSL3 s := by
      apply Subtype.ext
      rw [heSL3 s]
      exact h
    have he : e m = s := eSL3.injective hθ
    exact (he_apply m s).1 he
  · intro h
    have he : e m = s := (he_apply m s).2 h
    have hθ : θ m = eSL3 s := by
      rw [show θ m = eSL3 (e m) from rfl, he]
    rw [show (θ m : TriD4LineX k K) = (eSL3 s : TriD4LineX k K) from
      congrArg (fun x : ↥(triD4LineN0 k K) => (x : TriD4LineX k K)) hθ, heSL3 s]

end CFSG.StandardType
