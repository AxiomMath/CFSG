module

public import CFSG.LocalAnalysis.StandardType.GGL45NtExcFrame
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcRee
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcIdxRee
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcCentral
public import CFSG.LocalAnalysis.StandardType.GGL45NtExcIsoNoLang
public import CFSG.Blueprint.ChevalleyRoots

public section

namespace CFSG.HardMathSupport.C14Exc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly CFSG.StandardType
  CFSG.StandardType.LieCore CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Ree CFSG.HardMathSupport.C14Idx CFSG.HardMathSupport.C14ExcIso



private theorem eR1_finite_of_frobTwist
    {τ : Tag} {L' : Type} [Field L'] [CharP L' 2]
    {e n m : ℕ} (he : 1 ≤ e) (hn : 1 ≤ n) (hm : 1 ≤ m) {Q : ModGL τ L'}
    (hQF : entrywiseFrobGL τ L' 2 e Q = Q) (hQm : Q ^ m = 1) :
    Finite ↥(ratPts τ L' (endPow (frobTwistGL τ L' 2 e Q) n)) := by
  classical
  set q : ℕ := 2 ^ (e * n * m) with hqdef
  have hq2 : 2 ≤ q := by
    have hk : 1 ≤ e * n * m := Nat.mul_pos (Nat.mul_pos he hn) hm
    rw [hqdef]
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (e * n * m) := Nat.pow_le_pow_right (by norm_num) hk
  have hentry : ∀ (g : ratPts τ L' (endPow (frobTwistGL τ L' 2 e Q) n)) (a b : Label τ),
      (((g : ModGL τ L') : Module.End L' (RootModule τ L')) (Finsupp.single b 1) a) ^ q =
        ((g : ModGL τ L') : Module.End L' (RootModule τ L')) (Finsupp.single b 1) a := by
    intro g a b
    have hgS : (frobTwistGL τ L' 2 e Q)^[n] (g : ModGL τ L') = (g : ModGL τ L') := by
      rw [← endPow_apply]
      exact ratPts_fix g.2
    have hfix : (frobTwistGL τ L' 2 e Q)^[n * m] (g : ModGL τ L') = (g : ModGL τ L') := by
      rw [Function.iterate_mul]
      exact Function.iterate_fixed hgS m
    have hiter := frobTwistGL_iterate (p := 2) e hQF (n * m) (g : ModGL τ L')
    rw [hfix] at hiter
    have hQnm : Q ^ (n * m) = 1 := by
      rw [Nat.mul_comm n m, pow_mul, hQm, one_pow]
    rw [hQnm, one_mul, inv_one, mul_one] at hiter
    have hF : entrywiseFrobGL τ L' 2 (e * (n * m)) (g : ModGL τ L') = (g : ModGL τ L') :=
      hiter.symm
    have hcoord := congrArg (fun B : ModGL τ L' =>
      (B : Module.End L' (RootModule τ L')) (Finsupp.single b 1) a) hF
    simp only [Units.coe_map] at hcoord
    change entrywise (iterateFrobenius L' 2 (e * (n * m))) _ (Finsupp.single b 1) a = _ at hcoord
    rw [entrywise_single, Finsupp.mapRange_apply, iterateFrobenius_def] at hcoord
    rw [hqdef]
    rwa [Nat.mul_assoc e n m]
  have hSfin : Finite {x : L' // x ^ q = x} := by
    have hp : (Polynomial.X : Polynomial L') ^ q - Polynomial.X ≠ 0 := by
      intro h
      have hc := congrArg (fun p : Polynomial L' => p.coeff q) h
      rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow_self, Polynomial.coeff_X,
        if_neg (by omega), sub_zero, Polynomial.coeff_zero] at hc
      exact one_ne_zero hc
    have hset : {x : L' | x ^ q = x} =
        {x : L' | Polynomial.IsRoot (Polynomial.X ^ q - Polynomial.X) x} := by
      ext x
      simp only [Set.mem_setOf_eq]
      change x ^ q = x ↔ Polynomial.eval x ((Polynomial.X : Polynomial L') ^ q - Polynomial.X) = 0
      rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
    have hfin : ({x : L' | x ^ q = x} : Set L').Finite := by
      rw [hset]
      exact Polynomial.finite_setOf_isRoot hp
    exact hfin.to_subtype
  haveI : Finite {x : L' // x ^ q = x} := hSfin
  refine Finite.of_injective
    (fun (g : ratPts τ L' (endPow (frobTwistGL τ L' 2 e Q) n)) (a b : Label τ) =>
      (⟨_, hentry g a b⟩ : {x : L' // x ^ q = x})) ?_
  intro g g' hgg'
  exact Subtype.ext (Units.ext (by
    refine Finsupp.lhom_ext' fun b => LinearMap.ext_ring (Finsupp.ext fun a => ?_)
    simp only [LinearMap.comp_apply, Finsupp.lsingle_apply]
    exact congrArg Subtype.val (congrFun (congrFun hgg' a) b)))

theorem finite_ratPts_endPow_frobTwistGL
    {τ : Tag} {L' : Type} [Field L'] [CharP L' 2] {e n : ℕ}
    (he : 1 ≤ e) (hn : 1 ≤ n) {Q : ModGL τ L'} (hQ : IsDiagramTwistMatrix τ L' Q) :
    Finite ↥(ratPts τ L' (endPow (frobTwistGL τ L' 2 e Q) n)) := by
  rcases hQ with hQ1 | ⟨t, j, htag, hQeq⟩
  · subst Q
    exact eR1_finite_of_frobTwist he hn (le_refl 1) (Q := 1) (map_one _) (one_pow 1)
  · cases htag
    subst Q
    have horder : 1 ≤ t.order := by cases t <;> decide
    exact eR1_finite_of_frobTwist he hn horder
      (Q := diagramMap t L' ^ j) (entrywiseFrobGL_diagramMap_zpow t 2 e j)
      (diagramMap_zpow_pow_order t j)

theorem ree_sq_apply
    {L : Type} [Field L] [IsAlgClosed L] [CharP L ReeTag.F4.prime]
    (hf : ReeTag.F4.ShortFaithful L) (a₀ : ℕ) (g : adjointGroup ReeTag.F4.tag L) :
    (((ReeTag.F4.reeEndo L hf a₀) ((ReeTag.F4.reeEndo L hf a₀) g) :
      adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
      frobTwistGL ReeTag.F4.tag L 2 (2 * a₀ + 1) 1 g := by
  have hsq := congrArg
    (fun f : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L => f g)
    (CFSG.HardMathSupport.C14ExcRee.reeEndo_comp_self (t := ReeTag.F4) hf a₀)
  simp only [MonoidHom.comp_apply] at hsq
  rw [hsq, coe_frobeniusTwist, frobTwistGL_apply]
  simp only [one_mul, inv_one, mul_one]
  rfl

private lemma eR3_endPow_mul
                                      {Γ : Type*} [Monoid Γ] (F₀ : Γ →* Γ) (m n : ℕ) (x : Γ) :
    endPow F₀ (m * n) x = endPow (endPow F₀ m) n x := by
  have hfun : (F₀^[m] : Γ → Γ) = ⇑(endPow F₀ m) :=
    funext (fun y => (endPow_apply F₀ m y).symm)
  rw [endPow_apply, endPow_apply, Function.iterate_mul, hfun]

theorem absGeo_of_sq
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Γ : Type*} [Group Γ] (F₀ : Γ →* Γ)
    {G E Z : Subgroup Γ} (hGfix : ∀ g ∈ G, endPow F₀ p g = g)
    (hZc : ∀ z ∈ Z, ∀ z' ∈ Z, z * z' = z' * z)
    (hZcent : ∀ z ∈ Z, ∀ w ∈ G, (∀ e ∈ E, w * e = e * w) → w * z = z * w)
    (hZstab : ∀ z ∈ Z, F₀ z ∈ Z) (hpZ : ∀ u ∈ pCent p G E, u ∈ Z)
    (hZG : ∀ z ∈ Z, (∃ n : ℕ, z ^ p ^ n = 1) → endPow F₀ p z = z → z ∈ pCent p G E)
    {N₂ : ℕ} (hN₂ : 2 ≤ N₂)
    (hpow : ∀ z ∈ Z, (∃ n : ℕ, z ^ p ^ n = 1) → endPow F₀ (2 * p) z = z →
      endPow F₀ 2 z = z ^ N₂)
    (hnorm : ∀ y ∈ Z, (∃ n : ℕ, y ^ p ^ n = 1) → endPow F₀ 2 y = y →
      ∃ z ∈ Z, (∃ n : ℕ, z ^ p ^ n = 1) ∧ endPow F₀ (2 * p) z = z ∧
        y = z ^ ∑ i ∈ Finset.range p, N₂ ^ i) :
    AbsGeo p G F₀ E := by
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp2le : 2 ≤ p := hp.two_le
  have hN : 2 ≤ N₂ ^ ((p + 1) / 2) := by
    have h1 : 1 < N₂ ^ ((p + 1) / 2) :=
      Nat.one_lt_pow (n := (p + 1) / 2) (a := N₂) (by omega) (by omega)
    omega
  refine ⟨?_, ?_, N₂ ^ ((p + 1) / 2), hN, ?_, ?_⟩
  · intro u hu v hv
    exact hZc u (hpZ u hu) v (hpZ v hv)
  · intro u hu w hwG hwcent
    exact hZcent u (hpZ u hu) w hwG hwcent
  · intro u hu
    have huZ := hpZ u hu
    have huG : u ∈ G := hu.1
    have huP : ∃ n, u ^ p ^ n = 1 := hu.2.2
    have hfixu : endPow F₀ p u = u := hGfix u huG
    have huFp : F₀^[p] u = u := by rw [← endPow_apply]; exact hfixu
    have h2pu : endPow F₀ (2 * p) u = u := by
      rw [endPow_apply, show 2 * p = p * 2 by ring, Function.iterate_mul]
      exact Function.iterate_fixed huFp 2
    have hψu : endPow F₀ 2 u = u ^ N₂ := hpow u huZ huP h2pu
    have h2k : 2 * ((p + 1) / 2) = p + 1 := by
      obtain ⟨k, hk⟩ := hpodd
      omega
    have hF0_eq : F₀ u = endPow F₀ (p + 1) u := by
      rw [endPow_apply, Function.iterate_succ_apply']
      rw [← endPow_apply, hfixu]
    have hstep : endPow F₀ (p + 1) u = endPow (endPow F₀ 2) ((p + 1) / 2) u := by
      nth_rewrite 1 [← h2k]
      rw [eR3_endPow_mul F₀ 2 ((p + 1) / 2) u]
    rw [hF0_eq, hstep, endPow_pow hψu]
  · intro a ha hF0a
    have haZ := hpZ a ha
    have haG : a ∈ G := ha.1
    have haP : ∃ n, a ^ p ^ n = 1 := ha.2.2
    have hfixa : endPow F₀ p a = a := hGfix a haG
    have hψa : endPow F₀ 2 a = a := by
      have h := endPow_pow (F₀ := F₀) (N := 1) (u := a) (by rw [pow_one]; exact hF0a) 2
      simpa using h
    obtain ⟨z, hzZ, hzP, hz2p, haeq⟩ := hnorm a haZ haP hψa
    obtain ⟨s, hs⟩ := hzP
    have hΦzZ : endPow F₀ p z ∈ Z := endPow_mem hZstab p hzZ
    have hΦΦz : endPow F₀ p (endPow F₀ p z) = z := by
      rw [endPow_apply, endPow_apply, ← Function.iterate_add_apply,
        show p + p = 2 * p by ring, ← endPow_apply]
      exact hz2p
    have hpoddPow : Odd (p ^ s) := hpodd.pow
    obtain ⟨t, ht⟩ := hpoddPow
    let u₀ : ℕ := (p ^ s + 1) / 2
    have h2u₀ : 2 * u₀ = p ^ s + 1 := by
      dsimp [u₀]
      omega
    let b : Γ := z ^ u₀ * (endPow F₀ p z) ^ u₀
    have hbZ : b ∈ Z := by
      dsimp [b]
      exact Z.mul_mem (Z.pow_mem hzZ u₀) (Z.pow_mem hΦzZ u₀)
    have hzΦz : Commute z (endPow F₀ p z) := hZc z hzZ (endPow F₀ p z) hΦzZ
    have hΦb : endPow F₀ p b = b := by
      dsimp [b]
      rw [map_mul, map_pow, map_pow, hΦΦz]
      exact (hzΦz.pow_pow u₀ u₀).eq.symm
    have hΦzps : (endPow F₀ p z) ^ p ^ s = 1 := by
      rw [← map_pow, hs, map_one]
    have hz1 : z ^ (u₀ * p ^ s) = 1 := by
      rw [Nat.mul_comm, pow_mul, hs, one_pow]
    have hΦz1 : (endPow F₀ p z) ^ (u₀ * p ^ s) = 1 := by
      rw [Nat.mul_comm, pow_mul, hΦzps, one_pow]
    have hbP : ∃ n, b ^ p ^ n = 1 := by
      refine ⟨s, ?_⟩
      dsimp [b]
      rw [(hzΦz.pow_pow u₀ u₀).mul_pow (p ^ s), ← pow_mul, ← pow_mul, hz1, hΦz1, one_mul]
    set Sg : ℕ := ∑ i ∈ Finset.range p, N₂ ^ i with hSg
    have ha_ps : a ^ p ^ s = 1 := by
      rw [haeq, ← pow_mul, Nat.mul_comm Sg (p ^ s), pow_mul, hs, one_pow]
    have hPhizSg : (endPow F₀ p z) ^ Sg = a := by
      rw [← map_pow, ← haeq, hfixa]
    have hbSg : b ^ Sg = a := by
      have hcomm := (hzΦz.pow_pow u₀ u₀).mul_pow Sg
      dsimp [b]
      rw [hcomm]
      rw [show (z ^ u₀) ^ Sg = a ^ u₀ by
            rw [← pow_mul, Nat.mul_comm u₀ Sg, pow_mul, ← haeq],
          show ((endPow F₀ p z) ^ u₀) ^ Sg = a ^ u₀ by
            rw [← pow_mul, Nat.mul_comm u₀ Sg, pow_mul, hPhizSg]]
      rw [← pow_add, show u₀ + u₀ = 2 * u₀ by ring, h2u₀, pow_succ, ha_ps, one_mul]
    have h2pb : endPow F₀ (2 * p) b = b := by
      rw [endPow_apply, show 2 * p = p * 2 by ring, Function.iterate_mul]
      have hbFp : F₀^[p] b = b := by rw [← endPow_apply]; exact hΦb
      exact Function.iterate_fixed hbFp 2
    have hψb : endPow F₀ 2 b = b ^ N₂ := hpow b hbZ hbP h2pb
    have hbpψ : endPow (endPow F₀ 2) p b = b := by
      rw [← eR3_endPow_mul F₀ 2 p b]
      exact h2pb
    have hj : ¬ p ∣ (p + 1) / 2 := by
      intro hdvd
      have hpos : 0 < (p + 1) / 2 := by omega
      have hle : p ≤ (p + 1) / 2 := Nat.le_of_dvd hpos hdvd
      omega
    have hbA : b ∈ pCent p G E := hZG b hbZ hbP hΦb
    have hnr := norm_reindex (F₀ := endPow F₀ 2) hp hj hψb hbpψ
    rw [← hSg] at hnr
    exact ⟨b, hbA, (hnr.trans hbSg).symm⟩

theorem ree_frame_mem_famM
    {L : Type} [Field L] [IsAlgClosed L] [CharP L ReeTag.F4.prime]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {ι : Type} [Finite ι]
    (a : ι → Fin ReeTag.F4.tag.rank → Lˣ) (ha : ∀ i j, a i j ^ p = 1)
    (F' : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L)
    (hfix : ∀ (i : ι) (h : rootDiagUnit ReeTag.F4.tag (a i) ∈ adjointGroup ReeTag.F4.tag L),
      F' ⟨rootDiagUnit ReeTag.F4.tag (a i), h⟩ = ⟨rootDiagUnit ReeTag.F4.tag (a i), h⟩) :
    ∀ g ∈ famM a, F' g ∈ famM a := by
  intro g hg
  change g ∈ (familyGroup a).subgroupOf (adjointGroup ReeTag.F4.tag L) at hg
  change F' g ∈ (familyGroup a).subgroupOf (adjointGroup ReeTag.F4.tag L)
  rw [Subgroup.mem_subgroupOf] at hg ⊢
  rw [mem_familyGroup_iff hp hp2 (fun _ => hp3) (fun h => by cases h) a ha (F' g).2]
  intro i
  have hd_mem : rootDiagUnit ReeTag.F4.tag (a i) ∈ adjointGroup ReeTag.F4.tag L :=
    torusGroup_le_adjointGroup (rootDiagUnit_mem_torusGroup (a i))
  have hcomm_g : rootDiagUnit ReeTag.F4.tag (a i) * (g : ModGL ReeTag.F4.tag L) *
      (rootDiagUnit ReeTag.F4.tag (a i))⁻¹ = (g : ModGL ReeTag.F4.tag L) :=
    (mem_familyGroup_iff hp hp2 (fun _ => hp3) (fun h => by cases h) a ha g.2).1 hg i
  have hd_g : (⟨rootDiagUnit ReeTag.F4.tag (a i), hd_mem⟩ : adjointGroup ReeTag.F4.tag L) * g *
      (⟨rootDiagUnit ReeTag.F4.tag (a i), hd_mem⟩ : adjointGroup ReeTag.F4.tag L)⁻¹ = g := by
    apply Subtype.ext
    simpa using hcomm_g
  have hF := congrArg F' hd_g
  rw [map_mul, map_mul, map_inv, hfix i hd_mem] at hF
  simpa using Subtype.ext_iff.mp hF

theorem prop43_ree_abstract
                                      {Γ : Type*} [Group Γ] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (F₀ : Γ →* Γ) (M Z S E : Subgroup Γ) (hZM : Z ≤ M) (hSM : S ≤ M)
    (hMS : ∀ m ∈ M, ∃ z ∈ Z, ∃ s ∈ S, m = z * s) (hZc : ∀ z ∈ Z, ∀ m ∈ M, z * m = m * z)
    (hFM : ∀ g ∈ M, F₀ g ∈ M) (hFZ : ∀ z ∈ Z, F₀ z ∈ Z) (hFS : ∀ s ∈ S, F₀ s ∈ S)
    [Finite ↥(Z ⊓ S)] (hK : ¬ p ∣ Nat.card ↥(Z ⊓ S))
    [Finite ↥(S ⊓ fixG (endPow F₀ p))]
    (hEM : ∀ x ∈ E, ∀ m ∈ M, x * m = m * x)
    (hsat0 : ∀ y ∈ M, F₀ y = y → y ^ p = 1 → y ∈ E)
    (hidx : ¬ p ∣ ((Subgroup.closure {x | x ∈ S ⊓ fixG F₀ ∧ ∃ k : ℕ, x ^ 2 ^ k = 1}).subgroupOf
      (S ⊓ fixG F₀)).index) :
    ∀ y ∈ M, endPow F₀ p y = y → (∃ n : ℕ, y ^ p ^ n = 1) → y ∈ Z := by
  intro y hyM hyfix hgp
  have hFMp : ∀ g ∈ M, endPow F₀ p g ∈ M := fun g hg => endPow_mem hFM p hg
  let F₁ : ↥M →* ↥M := eC1_restrictEnd (endPow F₀ p) M hFMp
  haveI : Finite ↥((Z.subgroupOf M) ⊓ (S.subgroupOf M)) := by
    refine Finite.of_injective
      (fun x : ↥((Z.subgroupOf M) ⊓ (S.subgroupOf M)) =>
        (⟨(x : Γ), ?_⟩ : ↥(Z ⊓ S))) ?_
    · rw [Subgroup.mem_inf]
      exact ⟨Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp x.2).1,
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp x.2).2⟩
    · intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val hxy
  haveI : Finite ↥(fixG F₁ ⊓ S.subgroupOf M) := by
    refine Finite.of_injective
      (fun x : ↥(fixG F₁ ⊓ S.subgroupOf M) =>
        (⟨(x.1 : Γ), ?_⟩ : ↥(S ⊓ fixG (endPow F₀ p)))) ?_
    · rw [Subgroup.mem_inf]
      refine ⟨Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp x.2).2, ?_⟩
      have hxF : (eC1_restrictEnd (endPow F₀ p) M hFMp) x.1 = x.1 :=
        mem_fixG.1 (Subgroup.mem_inf.mp x.2).1
      rw [mem_fixG]
      rw [← eC1_restrictEnd_coe (endPow F₀ p) M hFMp x.1]
      exact congrArg Subtype.val hxF
    · intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val hxy
  have hsub : (Z.subgroupOf M) ⊓ (S.subgroupOf M) = (Z ⊓ S).subgroupOf M := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  have hcardK : Nat.card ↥((Z.subgroupOf M) ⊓ (S.subgroupOf M)) = Nat.card ↥(Z ⊓ S) := by
    rw [hsub]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_trans inf_le_left hZM)).toEquiv
  have hK' : ¬ p ∣ Nat.card ↥((Z.subgroupOf M) ⊓ (S.subgroupOf M)) := by
    rwa [hcardK]
  have hcardS : Nat.card ↥(fixG F₁ ⊓ S.subgroupOf M) =
      Nat.card ↥(S ⊓ fixG (endPow F₀ p)) := by
    have hcomm : fixG F₁ ⊓ S.subgroupOf M = S.subgroupOf M ⊓ fixG F₁ := inf_comm _ _
    rw [hcomm]
    exact eC1_card_subgroupOf_inf_fixG (endPow F₀ p) M S hSM hFMp
  have hS' : ¬ p ∣ Nat.card ↥(fixG F₁ ⊓ S.subgroupOf M) := by
    rw [hcardS]
    exact eC1_not_dvd_card_fixed_S hp hp2 F₀ M S E hSM hFS hEM hsat0 hidx
  have hZ' : Z.subgroupOf M ≤ Subgroup.center ↥M := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz
    rw [Subgroup.mem_center_iff]
    intro m
    exact Subtype.ext (hZc z hz m m.2).symm
  have hZF' : ∀ z ∈ Z.subgroupOf M, F₁ z ∈ Z.subgroupOf M := by
    intro z hz
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    rw [eC1_restrictEnd_coe]
    exact endPow_mem hFZ p hz
  have hSF' : ∀ s ∈ S.subgroupOf M, F₁ s ∈ S.subgroupOf M := by
    intro s hs
    rw [Subgroup.mem_subgroupOf] at hs ⊢
    rw [eC1_restrictEnd_coe]
    exact endPow_mem hFS p hs
  have hZS' : ∀ m : ↥M, ∃ z ∈ Z.subgroupOf M, ∃ s ∈ S.subgroupOf M, m = z * s := by
    intro m
    obtain ⟨z, hz, s, hs, hms⟩ := hMS (m : Γ) m.2
    exact ⟨⟨z, hZM hz⟩, Subgroup.mem_subgroupOf.2 hz, ⟨s, hSM hs⟩,
      Subgroup.mem_subgroupOf.2 hs, Subtype.ext hms⟩
  have hy' : F₁ ⟨y, hyM⟩ = ⟨y, hyM⟩ := by
    apply Subtype.ext
    rw [eC1_restrictEnd_coe]
    exact hyfix
  have hgp' : ∃ n : ℕ, (⟨y, hyM⟩ : ↥M) ^ p ^ n = 1 := by
    obtain ⟨n, hn⟩ := hgp
    exact ⟨n, Subtype.ext (by simpa using hn)⟩
  have hmem := pElt_mem_of_central_product hp F₁ (Z.subgroupOf M) (S.subgroupOf M) hZ' hZF'
    hSF' hZS' hK' hS' ⟨y, hyM⟩ hy' hgp'
  exact Subgroup.mem_subgroupOf.1 hmem

theorem exc_ree_central
    {L : Type} [Field L] [IsAlgClosed L] [CharP L ReeTag.F4.prime]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {ι : Type} [Finite ι]
    (hBor : ExcBorelInput) (hF4 : ExcF4PowSixInput) (a : ι → Fin ReeTag.F4.tag.rank → Lˣ)
    (ha : ∀ i j, a i j ^ p = 1) (F' : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L)
    (hFM : ∀ g ∈ famM a, F' g ∈ famM a)
    (hFZ : ∀ g : adjointGroup ReeTag.F4.tag L, (g : ModGL ReeTag.F4.tag L) ∈ famZ a →
      (F' g : ModGL ReeTag.F4.tag L) ∈ famZ a)
    (hfin : Finite ↥((endPow F' p).eqLocus (MonoidHom.id _)))
    (hidx : IdxConclusion p a F')
    (hsat0 : ∀ y : adjointGroup ReeTag.F4.tag L, (y : ModGL ReeTag.F4.tag L) ∈ familyGroup a →
      F' y = y → y ^ p = 1 → (y : ModGL ReeTag.F4.tag L) ∈ famSub ReeTag.F4.tag L a) :
    ∀ y : adjointGroup ReeTag.F4.tag L, (y : ModGL ReeTag.F4.tag L) ∈ familyGroup a →
      endPow F' p y = y → (∃ n : ℕ, y ^ p ^ n = 1) → (y : ModGL ReeTag.F4.tag L) ∈ famZ a := by
  let M : Subgroup (adjointGroup ReeTag.F4.tag L) := famM a
  let Z : Subgroup (adjointGroup ReeTag.F4.tag L) :=
    (famZ a).subgroupOf (adjointGroup ReeTag.F4.tag L)
  let S : Subgroup (adjointGroup ReeTag.F4.tag L) := famS a
  let E : Subgroup (adjointGroup ReeTag.F4.tag L) :=
    (famSub ReeTag.F4.tag L a).subgroupOf (adjointGroup ReeTag.F4.tag L)
  have hstruct := central_structure hBor a
  have hZM : Z ≤ M := hstruct.1
  have hSM : S ≤ M := hstruct.2.1
  have hMS : ∀ m ∈ M, ∃ z ∈ Z, ∃ s ∈ S, m = z * s := hstruct.2.2.1
  have hZc : ∀ z ∈ Z, ∀ m ∈ M, z * m = m * z := hstruct.2.2.2.1
  haveI hZS : Finite ↥(Z ⊓ S) := hstruct.2.2.2.2.2
  have hK : ¬ p ∣ Nat.card ↥(Z ⊓ S) := by
    have hcard : Nat.card ↥(Z ⊓ S) =
        Nat.card {g : adjointGroup Tag.F4 L //
          (g : ModGL Tag.F4 L) ∈ famZ a ∧ g ∈ famS a} := rfl
    rw [hcard]
    exact exc_not_dvd_card_F4_of_input hBor hF4 hp hp2 hp3 a
  have hFS : ∀ s ∈ S, F' s ∈ S := fun s hs =>
    commutator_stable F' (famM a) hFM s hs
  have hFZ' : ∀ z ∈ Z, F' z ∈ Z := fun z hz =>
    Subgroup.mem_subgroupOf.mpr (hFZ z (Subgroup.mem_subgroupOf.mp hz))
  haveI hfin' : Finite ↥((endPow F' p).eqLocus (MonoidHom.id _)) := hfin
  haveI hSfix : Finite ↥(S ⊓ fixG (endPow F' p)) :=
    Finite.of_injective _ (Subgroup.inclusion_injective
      (inf_le_right : S ⊓ fixG (endPow F' p) ≤ fixG (endPow F' p)))
  have hEM : ∀ x ∈ E, ∀ m ∈ M, x * m = m * x := by
    intro x hx m hm
    apply Subtype.ext
    show (x : ModGL ReeTag.F4.tag L) * (m : ModGL ReeTag.F4.tag L) =
      (m : ModGL ReeTag.F4.tag L) * (x : ModGL ReeTag.F4.tag L)
    have hxsub : (x : ModGL ReeTag.F4.tag L) ∈ famSub ReeTag.F4.tag L a :=
      Subgroup.mem_subgroupOf.mp hx
    have hmG : (m : ModGL ReeTag.F4.tag L) ∈ familyGroup a :=
      Subgroup.mem_subgroupOf.mp hm
    have hmAdj : (m : ModGL ReeTag.F4.tag L) ∈ adjointGroup ReeTag.F4.tag L :=
      (m : adjointGroup ReeTag.F4.tag L).2
    have h3 : ReeTag.F4.tag = .F4 ∨ ReeTag.F4.tag = .E6 ∨ ReeTag.F4.tag = .E7 ∨
        ReeTag.F4.tag = .E8 → p ≠ 3 := fun _ => hp3
    have h5 : ReeTag.F4.tag = .E8 → p ≠ 5 := fun hh => by cases hh
    have hle : famSub ReeTag.F4.tag L a ≤
        Subgroup.centralizer ({(m : ModGL ReeTag.F4.tag L)} :
          Set (ModGL ReeTag.F4.tag L)) := by
      refine (Subgroup.closure_le _).2 ?_
      rintro g ⟨i, rfl⟩
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      rw [Set.mem_singleton_iff] at hy
      subst hy
      have h := (mem_familyGroup_iff hp hp2 h3 h5 a ha hmAdj).mp hmG i
      calc (m : ModGL ReeTag.F4.tag L) * rootDiagUnit ReeTag.F4.tag (a i)
          = (rootDiagUnit ReeTag.F4.tag (a i) * (m : ModGL ReeTag.F4.tag L) *
              (rootDiagUnit ReeTag.F4.tag (a i))⁻¹) *
              rootDiagUnit ReeTag.F4.tag (a i) := by rw [h]
        _ = rootDiagUnit ReeTag.F4.tag (a i) * (m : ModGL ReeTag.F4.tag L) := by group
    exact (Subgroup.mem_centralizer_iff.1 (hle hxsub) _ (Set.mem_singleton _)).symm
  have hsat0' : ∀ y ∈ M, F' y = y → y ^ p = 1 → y ∈ E := by
    intro y hyM hyF hyP
    exact Subgroup.mem_subgroupOf.mpr (hsat0 y (Subgroup.mem_subgroupOf.mp hyM) hyF hyP)
  have hidx' : ¬ p ∣ ((Subgroup.closure {x | x ∈ S ⊓ fixG F' ∧
      ∃ k : ℕ, x ^ 2 ^ k = 1}).subgroupOf (S ⊓ fixG F')).index := by
    simpa [IdxConclusion, S] using hidx
  have hprop := prop43_ree_abstract (Γ := adjointGroup ReeTag.F4.tag L) hp hp2 F' M Z S E
    hZM hSM hMS hZc hFM hFZ' hFS hK hEM hsat0' hidx'
  intro y hyFam hyFix hyPow
  have hyM : y ∈ M := Subgroup.mem_subgroupOf.mpr hyFam
  exact Subgroup.mem_subgroupOf.mp (hprop y hyM hyFix hyPow)

private theorem rR3_diagKer_mul_comm
    {L : Type} [Field L] [IsAlgClosed L] [CharP L ReeTag.F4.prime] {ι : Type}
    (a : ι → Fin ReeTag.F4.tag.rank → Lˣ)
    {x y : ModGL ReeTag.F4.tag L}
    (hx : x ∈ diagKer ReeTag.F4.tag L (familyKernel a))
    (hy : y ∈ diagKer ReeTag.F4.tag L (familyKernel a)) : x * y = y * x := by
  obtain ⟨t, rfl, -⟩ := hx
  obtain ⟨s, rfl, -⟩ := hy
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm t s]

private theorem rR3_diagKer_le_adjointGroup
    {L : Type} [Field L]
    [IsAlgClosed L] [CharP L ReeTag.F4.prime] {ι : Type}
    (a : ι → Fin ReeTag.F4.tag.rank → Lˣ) :
    diagKer ReeTag.F4.tag L (familyKernel a) ≤ adjointGroup ReeTag.F4.tag L := by
  intro g hg
  obtain ⟨t, rfl, -⟩ := hg
  exact torusGroup_le_adjointGroup (rootDiagUnit_mem_torusGroup t)

private theorem rR3_famSub_le_torusGroup
    {L : Type} [Field L]
    [IsAlgClosed L] [CharP L ReeTag.F4.prime] {ι : Type}
    (a : ι → Fin ReeTag.F4.tag.rank → Lˣ) :
    famSub ReeTag.F4.tag L a ≤ torusGroup ReeTag.F4.tag L :=
  (Subgroup.closure_le (torusGroup ReeTag.F4.tag L)).2 fun _ ⟨i, hi⟩ =>
    hi ▸ rootDiagUnit_mem_torusGroup (a i)

private theorem rR3_list_prod_pow
                                      {Γ : Type*} [Monoid Γ] (z : Γ) (N n : ℕ) :
    ((List.range n).map fun i => z ^ N ^ i).prod = z ^ (∑ i ∈ Finset.range n, N ^ i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.prod_append, ih, Finset.sum_range_succ, pow_add]
    simp

private theorem rR3_coe_endPow
                                      {L : Type} [Field L] [IsAlgClosed L] [CharP L ReeTag.F4.prime]
    (f : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L)
    (c : ModGL ReeTag.F4.tag L →* ModGL ReeTag.F4.tag L)
    (h : ∀ x : adjointGroup ReeTag.F4.tag L,
      ((f x : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
        c (x : ModGL ReeTag.F4.tag L))
    (n : ℕ) (x : adjointGroup ReeTag.F4.tag L) :
    ((endPow f n x : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
      endPow c n (x : ModGL ReeTag.F4.tag L) := by
  rw [endPow_apply, endPow_apply]
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', h, ih]

private theorem rR3_coe_sq
    {L : Type} [Field L]
    [IsAlgClosed L] [CharP L ReeTag.F4.prime] {e : ℕ} (w : WeylGroup ReeTag.F4.tag)
    (F' : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L)
    (hF'sq : ∀ g : adjointGroup ReeTag.F4.tag L,
      ((F' (F' g) : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
        twFw ReeTag.F4.tag L e 1 w g) (x : adjointGroup ReeTag.F4.tag L) :
    ((endPow F' 2 x : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
      twFw ReeTag.F4.tag L e 1 w (x : ModGL ReeTag.F4.tag L) := by
  rw [endPow_apply, show (F'^[2]) x = F' (F' x) from rfl]
  exact hF'sq x

private theorem rR3_coe_endPow_two
    {L : Type} [Field L]
    [IsAlgClosed L] [CharP L ReeTag.F4.prime] {e : ℕ} (w : WeylGroup ReeTag.F4.tag)
    (F' : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L)
    (hF'sq : ∀ g : adjointGroup ReeTag.F4.tag L,
      ((F' (F' g) : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
        twFw ReeTag.F4.tag L e 1 w g) (n : ℕ) (x : adjointGroup ReeTag.F4.tag L) :
    ((endPow F' (2 * n) x : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
      endPow (twFw ReeTag.F4.tag L e 1 w) n (x : ModGL ReeTag.F4.tag L) := by
  rw [eR3_endPow_mul F' 2 n x]
  exact rR3_coe_endPow (endPow F' 2) (twFw ReeTag.F4.tag L e 1 w)
    (fun x => rR3_coe_sq w F' hF'sq x) n x

theorem exc_ree_frame_absGeo
    {L : Type} [Field L] [IsAlgClosed L] [CharP L ReeTag.F4.prime]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) {ι : Type}
    [Finite ι] (hBor : ExcBorelInput) (hF4 : ExcF4PowSixInput) {e : ℕ} (he : 1 ≤ e)
    (w : WeylGroup ReeTag.F4.tag) (a : ι → Fin ReeTag.F4.tag.rank → Lˣ) (ha : ∀ i j, a i j ^ p = 1)
    (F' : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L)
    (hF'sq : ∀ g : adjointGroup ReeTag.F4.tag L,
      ((F' (F' g) : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
        twFw ReeTag.F4.tag L e 1 w g)
    (hfix : ∀ (i : ι) (h : rootDiagUnit ReeTag.F4.tag (a i) ∈ adjointGroup ReeTag.F4.tag L),
      F' ⟨rootDiagUnit ReeTag.F4.tag (a i), h⟩ = ⟨rootDiagUnit ReeTag.F4.tag (a i), h⟩)
    (hstab : (∀ g : adjointGroup ReeTag.F4.tag L, (g : ModGL ReeTag.F4.tag L) ∈ famZ a →
        (F' g : ModGL ReeTag.F4.tag L) ∈ famZ a) ∧
      ∀ g : adjointGroup ReeTag.F4.tag L,
        (g : ModGL ReeTag.F4.tag L) ∈ diagKer ReeTag.F4.tag L (familyKernel a) →
          (F' g : ModGL ReeTag.F4.tag L) ∈ diagKer ReeTag.F4.tag L (familyKernel a))
    (hidx : IdxConclusion p a F')
    (hfin : Finite ↥((endPow F' p).eqLocus (MonoidHom.id _)))
    (hfinψ : Finite ↥(ratPts ReeTag.F4.tag L (endPow (twFw ReeTag.F4.tag L e 1 w) p)))
    (hcard : p ^ 2 ≤ Nat.card (famSub ReeTag.F4.tag L a))
    (hsat0 : ∀ y : adjointGroup ReeTag.F4.tag L, (y : ModGL ReeTag.F4.tag L) ∈ familyGroup a →
      F' y = y → y ^ p = 1 → (y : ModGL ReeTag.F4.tag L) ∈ famSub ReeTag.F4.tag L a) :
    AbsGeo p ((endPow F' p).eqLocus (MonoidHom.id _)) F'
      ((famSub ReeTag.F4.tag L a).subgroupOf (adjointGroup ReeTag.F4.tag L)) := by
  have h3 : ReeTag.F4.tag = .F4 ∨ ReeTag.F4.tag = .E6 ∨ ReeTag.F4.tag = .E7 ∨
      ReeTag.F4.tag = .E8 → p ≠ 3 := fun _ => hp3
  have h3D : ReeTag.F4.tag = .D4 → p ≠ 3 := fun h => by cases h
  have h5 : ReeTag.F4.tag = .E8 → p ≠ 5 := fun h => by cases h
  have hQ : IsDiagramTwistMatrix ReeTag.F4.tag L (1 : ModGL ReeTag.F4.tag L) := Or.inl rfl
  have hfix' : ∀ i : ι, twFw ReeTag.F4.tag L e 1 w (rootDiagUnit ReeTag.F4.tag (a i)) =
      rootDiagUnit ReeTag.F4.tag (a i) := by
    intro i
    have hd : rootDiagUnit ReeTag.F4.tag (a i) ∈ adjointGroup ReeTag.F4.tag L :=
      torusGroup_le_adjointGroup (rootDiagUnit_mem_torusGroup (a i))
    have h := hF'sq ⟨rootDiagUnit ReeTag.F4.tag (a i), hd⟩
    rw [hfix i hd, hfix i hd] at h
    simpa using h.symm
  obtain ⟨N, hN2, hNpow⟩ :=
    exc_frame_power (τ := ReeTag.F4.tag) hp hp2 h3 h3D h5 he hQ w a ha hfix' hfinψ
  have hsat := exc_frame_hsat (τ := ReeTag.F4.tag) hp hp2 h3 h5 a ha hcard
  refine absGeo_of_sq hp hp2 F'
    (G := (endPow F' p).eqLocus (MonoidHom.id _))
    (E := (famSub ReeTag.F4.tag L a).subgroupOf (adjointGroup ReeTag.F4.tag L))
    (Z := (diagKer ReeTag.F4.tag L (familyKernel a)).subgroupOf (adjointGroup ReeTag.F4.tag L))
    ?_ ?_ ?_ ?_ ?_ ?_ (N₂ := N) hN2 ?_ ?_
  · intro g hg
    exact hg
  · intro z hz z' hz'
    have hzD : (z : ModGL ReeTag.F4.tag L) ∈ diagKer ReeTag.F4.tag L (familyKernel a) :=
      Subgroup.mem_subgroupOf.mp hz
    have hz'D : (z' : ModGL ReeTag.F4.tag L) ∈ diagKer ReeTag.F4.tag L (familyKernel a) :=
      Subgroup.mem_subgroupOf.mp hz'
    exact Subtype.ext (rR3_diagKer_mul_comm a hzD hz'D)
  · intro z hz w hw hwcomm
    have hzD : (z : ModGL ReeTag.F4.tag L) ∈ diagKer ReeTag.F4.tag L (familyKernel a) :=
      Subgroup.mem_subgroupOf.mp hz
    have hwfam : (w : ModGL ReeTag.F4.tag L) ∈ familyGroup a := by
      rw [mem_familyGroup_iff hp hp2 h3 h5 a ha w.2]
      intro i
      have hdi : (⟨rootDiagUnit ReeTag.F4.tag (a i),
          torusGroup_le_adjointGroup (rootDiagUnit_mem_torusGroup (a i))⟩ :
          adjointGroup ReeTag.F4.tag L) ∈
          (famSub ReeTag.F4.tag L a).subgroupOf (adjointGroup ReeTag.F4.tag L) :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure (Set.mem_range_self i))
      have hc := hwcomm _ hdi
      have hc' : (w : ModGL ReeTag.F4.tag L) * rootDiagUnit ReeTag.F4.tag (a i) =
          rootDiagUnit ReeTag.F4.tag (a i) * (w : ModGL ReeTag.F4.tag L) :=
        congrArg Subtype.val hc
      rw [← hc']
      group
    exact Subtype.ext (diagKer_central a hzD hwfam).symm
  · intro z hz
    have hzD : (z : ModGL ReeTag.F4.tag L) ∈ diagKer ReeTag.F4.tag L (familyKernel a) :=
      Subgroup.mem_subgroupOf.mp hz
    exact Subgroup.mem_subgroupOf.mpr (hstab.2 z hzD)
  · intro u hu
    obtain ⟨huG, hucomm, hupow⟩ := hu
    have hFM : ∀ g ∈ famM a, F' g ∈ famM a :=
      ree_frame_mem_famM hp hp2 hp3 a ha F' hfix
    have hfam : (u : ModGL ReeTag.F4.tag L) ∈ familyGroup a := by
      rw [mem_familyGroup_iff hp hp2 h3 h5 a ha u.2]
      intro i
      have hdi : (⟨rootDiagUnit ReeTag.F4.tag (a i),
          torusGroup_le_adjointGroup (rootDiagUnit_mem_torusGroup (a i))⟩ :
          adjointGroup ReeTag.F4.tag L) ∈
          (famSub ReeTag.F4.tag L a).subgroupOf (adjointGroup ReeTag.F4.tag L) :=
        Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure (Set.mem_range_self i))
      have hc := hucomm _ hdi
      have hc' : (u : ModGL ReeTag.F4.tag L) * rootDiagUnit ReeTag.F4.tag (a i) =
          rootDiagUnit ReeTag.F4.tag (a i) * (u : ModGL ReeTag.F4.tag L) :=
        congrArg Subtype.val hc
      rw [← hc']
      group
    have huZ := exc_ree_central hp hp2 hp3 hBor hF4 a ha F' hFM hstab.1 hfin hidx hsat0
      u hfam huG hupow
    exact Subgroup.mem_subgroupOf.mpr (famZ_le_diagKer a huZ)
  · intro z hz hzp hzfix
    refine ⟨?_, ?_, hzp⟩
    · show endPow F' p z = z
      exact hzfix
    · intro e he
      have hzD : (z : ModGL ReeTag.F4.tag L) ∈ diagKer ReeTag.F4.tag L (familyKernel a) :=
        Subgroup.mem_subgroupOf.mp hz
      obtain ⟨t, ht, -⟩ := hzD
      have heT : (e : ModGL ReeTag.F4.tag L) ∈ torusGroup ReeTag.F4.tag L :=
        rR3_famSub_le_torusGroup a (Subgroup.mem_subgroupOf.mp he)
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ht]
      exact rootDiagUnit_mul_comm_of_mem_torusGroup t heT
  · intro z hzZ hzp hz2p
    have hzD : (z : ModGL ReeTag.F4.tag L) ∈ diagKer ReeTag.F4.tag L (familyKernel a) :=
      Subgroup.mem_subgroupOf.mp hzZ
    have hzp' : ∃ n : ℕ, (z : ModGL ReeTag.F4.tag L) ^ p ^ n = 1 := by
      obtain ⟨n, hn⟩ := hzp
      exact ⟨n, by rw [← Subgroup.coe_pow, hn, Subgroup.coe_one]⟩
    have hzfix : endPow (twFw ReeTag.F4.tag L e 1 w) p (z : ModGL ReeTag.F4.tag L) =
        (z : ModGL ReeTag.F4.tag L) := by
      have h := rR3_coe_endPow_two w F' hF'sq p z
      rw [hz2p] at h
      exact h.symm
    have hNz := hNpow (z : ModGL ReeTag.F4.tag L) hzD hzp' hzfix
    apply Subtype.ext
    rw [Subgroup.coe_pow, rR3_coe_sq w F' hF'sq z, hNz]
  · intro y hyZ hyp hyfix
    have hyD : (y : ModGL ReeTag.F4.tag L) ∈ diagKer ReeTag.F4.tag L (familyKernel a) :=
      Subgroup.mem_subgroupOf.mp hyZ
    have hyp' : ∃ n : ℕ, (y : ModGL ReeTag.F4.tag L) ^ p ^ n = 1 := by
      obtain ⟨n, hn⟩ := hyp
      exact ⟨n, by rw [← Subgroup.coe_pow, hn, Subgroup.coe_one]⟩
    have hyfix' : twFw ReeTag.F4.tag L e 1 w (y : ModGL ReeTag.F4.tag L) =
        (y : ModGL ReeTag.F4.tag L) := by
      have hcoe := rR3_coe_sq w F' hF'sq y
      rw [hyfix] at hcoe
      exact hcoe.symm
    obtain ⟨z', hz'D, hz'p, hz'fix, hz'prod⟩ :=
      exc_frame_norm (τ := ReeTag.F4.tag) hp hp2 h3 h3D h5 he hQ w a ha hfix' hsat
        (y : ModGL ReeTag.F4.tag L) hyD hyp' hyfix'
    let z : adjointGroup ReeTag.F4.tag L :=
      ⟨z', rR3_diagKer_le_adjointGroup a hz'D⟩
    have hzval : (z : ModGL ReeTag.F4.tag L) = z' := rfl
    refine ⟨z, Subgroup.mem_subgroupOf.mpr ?_, ?_, ?_, ?_⟩
    · rw [hzval]; exact hz'D
    · obtain ⟨n, hn⟩ := hz'p
      exact ⟨n, Subtype.ext (by rw [Subgroup.coe_pow, hzval, hn, Subgroup.coe_one])⟩
    · apply Subtype.ext
      rw [rR3_coe_endPow_two w F' hF'sq p z, hzval, hz'fix]
    · apply Subtype.ext
      rw [Subgroup.coe_pow, hzval]
      have hNz : twFw ReeTag.F4.tag L e 1 w z' = z' ^ N := hNpow z' hz'D hz'p hz'fix
      have hmap : (List.range p).map (fun i => endPow (twFw ReeTag.F4.tag L e 1 w) i z') =
          (List.range p).map (fun i => z' ^ N ^ i) := by
        apply List.map_congr_left
        intro i _
        exact endPow_pow hNz i
      have hprod : ((List.range p).map fun i => (endPow (twFw ReeTag.F4.tag L e 1 w) i) z').prod =
          z' ^ (∑ i ∈ Finset.range p, N ^ i) := by
        rw [hmap, rR3_list_prod_pow]
      rw [← hz'prod]
      exact hprod

theorem excAlgGeoRee_of_frame
    (hM1 : GGLieToralPosition) (hM2 : GGLieLangPosition)
    (hBor : ExcBorelInput) (hIdx : ExcIdxReeInput) (hF4 : ExcF4PowSixInput)
    (hStab : ExcReeCentralStab) : ExcAlgGeoRee := by
  intro L _ _ _ _ hAlg p hp hp2 hp3 hf a₀ hfin E hEG hEab hcard hEfix hsat0
  let F₀ : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L :=
    ReeTag.F4.reeEndo L hf a₀
  change ∀ x ∈ E, F₀ x = x at hEfix
  let e : ℕ := 2 * a₀ + 1
  let ψ : ModGL ReeTag.F4.tag L →* ModGL ReeTag.F4.tag L :=
    frobTwistGL ReeTag.F4.tag L 2 e 1
  have he : 1 ≤ e := by simp [e]
  have hψ : ∀ g : adjointGroup ReeTag.F4.tag L,
      ((F₀ (F₀ g) : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) = ψ g := by
    intro g
    simpa [F₀, ψ, e] using ree_sq_apply hf a₀ g
  have hfinE : Finite E :=
    Finite.of_injective (Subgroup.inclusion hEG) (Subgroup.inclusion_injective hEG)
  let Emap : Subgroup (ModGL ReeTag.F4.tag L) := E.map (adjointGroup ReeTag.F4.tag L).subtype
  have hfinEmap : Finite Emap :=
    Finite.of_equiv E (Subgroup.equivMapOfInjective E (adjointGroup ReeTag.F4.tag L).subtype
      (Subgroup.subtype_injective _))
  have hEab' : IsElemAbelian p Emap :=
    CFSG.SectionRank.isElemAbelian_map hEab (adjointGroup ReeTag.F4.tag L).subtype
  have hcardEmap : Nat.card Emap = Nat.card E :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  have hcard' : p ^ 2 ≤ Nat.card Emap := by rw [hcardEmap]; exact hcard
  have hEmap_le : Emap ≤ adjointGroup ReeTag.F4.tag L := by
    intro x hx
    obtain ⟨e0, he0, hxeq⟩ := Subgroup.mem_map.mp hx
    rw [← hxeq]; exact e0.2
  have hEF : Emap ≤ ratPts ReeTag.F4.tag L ψ := by
    intro x hx
    obtain ⟨e0, he0, rfl⟩ := Subgroup.mem_map.mp hx
    rw [ratPts, Subgroup.mem_inf]
    refine ⟨e0.2, ?_⟩
    show ψ (e0 : ModGL ReeTag.F4.tag L) = (e0 : ModGL ReeTag.F4.tag L)
    rw [← hψ e0]
    simp only [F₀, hEfix e0 he0]
  have hfinψ : Finite ↥(ratPts ReeTag.F4.tag L (endPow ψ p)) := by
    simpa only [ψ] using
      finite_ratPts_endPow_frobTwistGL (τ := ReeTag.F4.tag) (L' := L) (e := e) (n := p)
        he hp.one_le (Q := (1 : ModGL ReeTag.F4.tag L)) (Or.inl rfl)
  have hL : letI := ZMod.algebra L 2; Algebra.IsAlgebraic (ZMod 2) L := by
    have h : ZMod.algebra L 2 = (inferInstance : Algebra (ZMod 2) L) := Subsingleton.elim _ _
    rw [h]; exact hAlg
  have h3 : ReeTag.F4.tag = .F4 ∨ ReeTag.F4.tag = .E6 ∨ ReeTag.F4.tag = .E7 ∨
      ReeTag.F4.tag = .E8 → p ≠ 3 := fun _ => hp3
  have h5 : ReeTag.F4.tag = .E8 → p ≠ 5 := fun h => by cases h
  obtain ⟨w, h, a, hh, hEa, hF, hC⟩ :=
    exc_lang_frame (τ := ReeTag.F4.tag) hM1 hM2 hL hp hp2 h3 h5 (e := e) he (Q := 1)
      (Or.inl rfl) hfinψ hEab' hEF
  have ha : ∀ i j, a i j ^ p = 1 := by
    intro i j
    have hxp : (i : ModGL ReeTag.F4.tag L) ^ p = 1 := hEab'.2 i i.2
    have h1 : (rootDiagUnit ReeTag.F4.tag (a i)) ^ p = 1 := by
      rw [← hEa i]
      have hconj : h * (i : ModGL ReeTag.F4.tag L) * h⁻¹ = (MulAut.conj h) (i : ModGL ReeTag.F4.tag L) := by
        rw [MulAut.conj_apply]
      rw [hconj, ← map_pow, hxp, map_one]
    have h2 : rootDiagUnit ReeTag.F4.tag ((a i) ^ p) = 1 := by
      have hm := (rootDiagUnitHom ReeTag.F4.tag L).map_pow (a i) p
      change (rootDiagUnitHom ReeTag.F4.tag L) ((a i) ^ p) = 1
      rw [hm]
      exact h1
    have h3 : (a i) ^ p = 1 :=
      rootDiagUnit_injective (by rw [h2, rootDiagUnit_one])
    simpa using congrFun h3 j
  have hfin_tw : Finite ↥(ratPts ReeTag.F4.tag L (endPow (twFw ReeTag.F4.tag L e 1 w) p)) := by
    haveI : Finite ↥(ratPts ReeTag.F4.tag L (endPow ψ p)) := hfinψ
    have hψconj : ∀ z : ModGL ReeTag.F4.tag L,
        endPow (twFw ReeTag.F4.tag L e 1 w) p (h * z * h⁻¹) = h * endPow ψ p z * h⁻¹ :=
      fun z => endPow_conj ψ (twFw ReeTag.F4.tag L e 1 w) h (fun y => hF y) p z
    refine Finite.of_injective
      (fun y : ↥(ratPts ReeTag.F4.tag L (endPow (twFw ReeTag.F4.tag L e 1 w) p)) =>
        (⟨h⁻¹ * (y : ModGL ReeTag.F4.tag L) * h, ?_⟩ :
          ↥(ratPts ReeTag.F4.tag L (endPow ψ p)))) ?_
    · rw [ratPts, Subgroup.mem_inf]
      refine ⟨?_, ?_⟩
      · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh)
          (Subgroup.mem_inf.mp y.2).1) hh
      · show endPow ψ p (h⁻¹ * (y : ModGL ReeTag.F4.tag L) * h) =
            h⁻¹ * (y : ModGL ReeTag.F4.tag L) * h
        have hyfix : endPow (twFw ReeTag.F4.tag L e 1 w) p (y : ModGL ReeTag.F4.tag L) =
            (y : ModGL ReeTag.F4.tag L) := (Subgroup.mem_inf.mp y.2).2
        have hconj := hψconj (h⁻¹ * (y : ModGL ReeTag.F4.tag L) * h)
        rw [show h * (h⁻¹ * (y : ModGL ReeTag.F4.tag L) * h) * h⁻¹ =
            (y : ModGL ReeTag.F4.tag L) from by group] at hconj
        rw [hyfix] at hconj
        have := congrArg (fun t : ModGL ReeTag.F4.tag L => h⁻¹ * t * h) hconj
        calc endPow ψ p (h⁻¹ * (y : ModGL ReeTag.F4.tag L) * h)
            = h⁻¹ * (h * endPow ψ p (h⁻¹ * (y : ModGL ReeTag.F4.tag L) * h) * h⁻¹) * h := by
              group
          _ = h⁻¹ * (y : ModGL ReeTag.F4.tag L) * h := this.symm
    · intro x y hxy
      have h2 : h⁻¹ * (x : ModGL ReeTag.F4.tag L) * h =
          h⁻¹ * (y : ModGL ReeTag.F4.tag L) * h := congrArg Subtype.val hxy
      apply Subtype.ext
      calc (x : ModGL ReeTag.F4.tag L)
          = h * (h⁻¹ * (x : ModGL ReeTag.F4.tag L) * h) * h⁻¹ := by group
        _ = h * (h⁻¹ * (y : ModGL ReeTag.F4.tag L) * h) * h⁻¹ := by rw [h2]
        _ = (y : ModGL ReeTag.F4.tag L) := by group
  let hΓ : adjointGroup ReeTag.F4.tag L := ⟨h, hh⟩
  let F' : adjointGroup ReeTag.F4.tag L →* adjointGroup ReeTag.F4.tag L :=
    (MulAut.conj hΓ).toMonoidHom.comp (F₀.comp (MulAut.conj hΓ⁻¹).toMonoidHom)
  have hF'def : ∀ y : adjointGroup ReeTag.F4.tag L,
      F' y = hΓ * F₀ (hΓ⁻¹ * y * hΓ) * hΓ⁻¹ := by
    intro y; rfl
  have hconj : IsReeConj hf a₀ hΓ F' := by
    intro g
    rw [hF'def]
  have hF0fix : ∀ (x : ModGL ReeTag.F4.tag L) (hx : x ∈ Emap),
      (F₀ ⟨x, hEmap_le hx⟩ : ModGL ReeTag.F4.tag L) = x := by
    intro x hx
    obtain ⟨e0, he0, hxeq⟩ := Subgroup.mem_map.mp hx
    have heq : (⟨x, hEmap_le hx⟩ : adjointGroup ReeTag.F4.tag L) = e0 :=
      Subtype.ext hxeq.symm
    rw [heq]
    have h1 : (F₀ e0 : ModGL ReeTag.F4.tag L) = x := by
      rw [← hxeq]
      exact congrArg Subtype.val (hEfix e0 he0)
    exact h1
  have hfix : ∀ (i : Emap) (hi : rootDiagUnit ReeTag.F4.tag (a i) ∈ adjointGroup ReeTag.F4.tag L),
      F' ⟨rootDiagUnit ReeTag.F4.tag (a i), hi⟩ = ⟨rootDiagUnit ReeTag.F4.tag (a i), hi⟩ := by
    intro i hi
    apply Subtype.ext
    show (F' ⟨rootDiagUnit ReeTag.F4.tag (a i), hi⟩ : ModGL ReeTag.F4.tag L) =
      rootDiagUnit ReeTag.F4.tag (a i)
    rw [hF'def]
    have key : hΓ⁻¹ * (⟨rootDiagUnit ReeTag.F4.tag (a i), hi⟩ : adjointGroup ReeTag.F4.tag L) *
        hΓ = (⟨(i : ModGL ReeTag.F4.tag L), hEmap_le i.2⟩ : adjointGroup ReeTag.F4.tag L) := by
      apply Subtype.ext
      show h⁻¹ * rootDiagUnit ReeTag.F4.tag (a i) * h = (i : ModGL ReeTag.F4.tag L)
      rw [← hEa i]; group
    rw [key]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hF0fix (i : ModGL ReeTag.F4.tag L) i.2]
    show h * (i : ModGL ReeTag.F4.tag L) * h⁻¹ = rootDiagUnit ReeTag.F4.tag (a i)
    exact hEa i
  have hFM : ∀ g ∈ famM a, F' g ∈ famM a :=
    ree_frame_mem_famM hp hp2 hp3 a ha F' hfix
  let cΓ : MulAut (adjointGroup ReeTag.F4.tag L) := MulAut.conj hΓ
  have hF'conj : ∀ y : adjointGroup ReeTag.F4.tag L,
      hΓ * F₀ (hΓ⁻¹ * y * hΓ) * hΓ⁻¹ = F' y := fun y => (hF'def y).symm
  have hc : ∀ y : adjointGroup ReeTag.F4.tag L, F' (cΓ y) = cΓ (F₀ y) := by
    intro y
    rw [hF'def]
    show hΓ * F₀ (hΓ⁻¹ * (cΓ y) * hΓ) * hΓ⁻¹ = hΓ * F₀ y * hΓ⁻¹
    have hidx : hΓ⁻¹ * (cΓ y) * hΓ = y := by rw [MulAut.conj_apply]; group
    rw [hidx]
  have hfinF₀ : Finite ↥(F₀.eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag L))) := by
    haveI : Finite ↥((endPow F₀ p).eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag L))) := hfin
    refine Finite.of_injective
      (Subgroup.inclusion (show F₀.eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag L)) ≤
        (endPow F₀ p).eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag L)) from fun g hg => ?_))
      (Subgroup.inclusion_injective _)
    show endPow F₀ p g = g
    rw [endPow_apply]
    exact Function.iterate_fixed (mem_fixG.mp hg) p
  have hfinF'p : Finite ↥((endPow F' p).eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag L))) := by
    haveI : Finite ↥((endPow F₀ p).eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag L))) := hfin
    refine Finite.of_injective
      (fun x : ↥((endPow F' p).eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag L))) =>
        (⟨cΓ.symm (x : adjointGroup ReeTag.F4.tag L), ?_⟩ :
          ↥((endPow F₀ p).eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag L))))) ?_
    · show endPow F₀ p (cΓ.symm (x : adjointGroup ReeTag.F4.tag L)) =
          cΓ.symm (x : adjointGroup ReeTag.F4.tag L)
      have hx' : endPow F' p (x : adjointGroup ReeTag.F4.tag L) = x := mem_fixG.mp x.2
      have hy : hΓ * (cΓ.symm (x : adjointGroup ReeTag.F4.tag L)) * hΓ⁻¹ = x := by
        rw [← MulAut.conj_apply]
        exact cΓ.apply_symm_apply x
      have h := endPow_conj F₀ F' hΓ hF'conj p (cΓ.symm (x : adjointGroup ReeTag.F4.tag L))
      rw [hy] at h
      rw [hx'] at h
      have h2 : cΓ (endPow F₀ p (cΓ.symm (x : adjointGroup ReeTag.F4.tag L))) =
          cΓ (cΓ.symm (x : adjointGroup ReeTag.F4.tag L)) := by
        rw [cΓ.apply_symm_apply, MulAut.conj_apply]; exact h.symm
      exact cΓ.injective h2
    · intro x y hxy
      have h2 : cΓ.symm (x : adjointGroup ReeTag.F4.tag L) =
          cΓ.symm (y : adjointGroup ReeTag.F4.tag L) := Subtype.ext_iff.mp hxy
      exact Subtype.ext (cΓ.symm.injective h2)
  have hfinF' : Finite ↥(F'.eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag L))) := by
    haveI : Finite ↥((endPow F' p).eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag L))) := hfinF'p
    refine Finite.of_injective
      (Subgroup.inclusion (show F'.eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag L)) ≤
        (endPow F' p).eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag L)) from fun g hg => ?_))
      (Subgroup.inclusion_injective _)
    show endPow F' p g = g
    rw [endPow_apply]
    exact Function.iterate_fixed (mem_fixG.mp hg) p
  have hstab := hStab L a hf a₀ hΓ F' hconj hFM
  have hTp : CorootPSaturated p (familyKernel a) :=
    CFSG.HardMathSupport.C14Coroot.corootPSaturated_of_nonTorsion hp hp2 h3 h5 a
  have hidx : IdxConclusion p a F' :=
    hIdx L p hp hp2 a hf a₀ hΓ F' hconj hFM hfinF' hTp
  have hF'sq : ∀ g : adjointGroup ReeTag.F4.tag L,
      ((F' (F' g) : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
        twFw ReeTag.F4.tag L e 1 w g := by
    intro g
    have hstep : ((F' (F' g) : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
        h * ψ (h⁻¹ * (g : ModGL ReeTag.F4.tag L) * h) * h⁻¹ := by
      have hFF : F' (F' g) = hΓ * F₀ (F₀ (hΓ⁻¹ * g * hΓ)) * hΓ⁻¹ := by
        rw [hF'def, hF'def]
        have hinner : hΓ⁻¹ * (hΓ * F₀ (hΓ⁻¹ * g * hΓ) * hΓ⁻¹) * hΓ =
            F₀ (hΓ⁻¹ * g * hΓ) := by group
        rw [hinner]
      rw [hFF]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hψ (hΓ⁻¹ * g * hΓ)]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rfl
    rw [hstep, hF (g : ModGL ReeTag.F4.tag L)]
  have hG : ∀ g : adjointGroup ReeTag.F4.tag L,
      g ∈ (endPow F₀ p).eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag L)) ↔
        cΓ g ∈ (endPow F' p).eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag L)) := by
    intro g
    have hconj := endPow_conj F₀ F' hΓ hF'conj p g
    show endPow F₀ p g = g ↔ endPow F' p (cΓ g) = cΓ g
    rw [show cΓ g = hΓ * g * hΓ⁻¹ from MulAut.conj_apply hΓ g]
    rw [hconj]
    constructor
    · intro h; rw [h]
    · intro h; exact mul_left_cancel (mul_right_cancel h)
  have hrange : Set.range (fun i : Emap => rootDiagUnit ReeTag.F4.tag (a i)) =
      (MulAut.conj h).toMonoidHom '' (Emap : Set (ModGL ReeTag.F4.tag L)) := by
    ext y; constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, i.2, hEa i⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (hEa ⟨x, hx⟩).symm⟩
  have hmap : famSub ReeTag.F4.tag L a = Emap.map (MulAut.conj h).toMonoidHom := by
    apply le_antisymm
    · rw [famSub]
      refine (Subgroup.closure_le _).2 ?_
      rw [hrange]
      exact fun y hy => hy
    · rw [famSub, hrange]
      exact fun y hy => Subgroup.subset_closure hy
  have hE : ∀ g : adjointGroup ReeTag.F4.tag L,
      g ∈ E ↔ cΓ g ∈ (famSub ReeTag.F4.tag L a).subgroupOf (adjointGroup ReeTag.F4.tag L) := by
    intro g
    rw [Subgroup.mem_subgroupOf, hmap, Subgroup.mem_map]
    constructor
    · intro hg
      refine ⟨(g : ModGL ReeTag.F4.tag L), ?_, ?_⟩
      · exact ⟨g, hg, rfl⟩
      · rfl
    · rintro ⟨x, hx, hxeq⟩
      obtain ⟨e0, he0, hex⟩ := Subgroup.mem_map.mp hx
      have hce : (MulAut.conj h) x = ((cΓ e0 : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) := by
        rw [← hex]; rfl
      have hcg : ((cΓ e0 : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) =
          ((cΓ g : adjointGroup ReeTag.F4.tag L) : ModGL ReeTag.F4.tag L) := by
        rw [← hce]; exact hxeq
      have heg : e0 = g := cΓ.injective (Subtype.ext hcg)
      exact heg ▸ he0
  have hcardfam : p ^ 2 ≤ Nat.card (famSub ReeTag.F4.tag L a) := by
    rw [hmap]
    rw [Subgroup.card_map_of_injective (MulAut.conj h).injective]
    rw [hcardEmap]
    exact hcard
  have hsat0' : ∀ y : adjointGroup ReeTag.F4.tag L,
      (y : ModGL ReeTag.F4.tag L) ∈ familyGroup a → F' y = y → y ^ p = 1 →
        (y : ModGL ReeTag.F4.tag L) ∈ famSub ReeTag.F4.tag L a := by
    intro y hyFam hyF hyP
    let z : adjointGroup ReeTag.F4.tag L := hΓ⁻¹ * y * hΓ
    have hyz : y = cΓ z := by
      show y = hΓ * z * hΓ⁻¹
      dsimp [z]; group
    have hzF : F₀ z = z := by
      have h := hc z
      rw [← hyz] at h
      rw [hyF] at h
      exact (cΓ.injective (hyz.symm.trans h)).symm
    have hzG : z ∈ (endPow F₀ p).eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag L)) := by
      show endPow F₀ p z = z
      rw [endPow_apply]
      exact Function.iterate_fixed hzF p
    have hzP : z ^ p = 1 := by
      have hzconj : z = (MulAut.conj hΓ⁻¹) y := by
        dsimp [z]; group
      rw [hzconj, ← map_pow, hyP, map_one]
    have hzcomm : ∀ x ∈ E, z * x = x * z := by
      intro x hx
      have hxEmap : (x : ModGL ReeTag.F4.tag L) ∈ Emap := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
      let xE : Emap := ⟨(x : ModGL ReeTag.F4.tag L), hxEmap⟩
      have hdx : rootDiagUnit ReeTag.F4.tag (a xE) = h * (x : ModGL ReeTag.F4.tag L) * h⁻¹ :=
        (hEa xE).symm
      have hycomm : (y : ModGL ReeTag.F4.tag L) * rootDiagUnit ReeTag.F4.tag (a xE) =
          rootDiagUnit ReeTag.F4.tag (a xE) * (y : ModGL ReeTag.F4.tag L) := by
        have h := (mem_familyGroup_iff hp hp2 h3 h5 a ha (y.2)).1 hyFam xE
        calc (y : ModGL ReeTag.F4.tag L) * rootDiagUnit ReeTag.F4.tag (a xE)
            = (rootDiagUnit ReeTag.F4.tag (a xE) * (y : ModGL ReeTag.F4.tag L) *
                (rootDiagUnit ReeTag.F4.tag (a xE))⁻¹) *
                rootDiagUnit ReeTag.F4.tag (a xE) := by rw [h]
          _ = rootDiagUnit ReeTag.F4.tag (a xE) * (y : ModGL ReeTag.F4.tag L) := by group
      apply Subtype.ext
      show (z : ModGL ReeTag.F4.tag L) * (x : ModGL ReeTag.F4.tag L) =
        (x : ModGL ReeTag.F4.tag L) * (z : ModGL ReeTag.F4.tag L)
      have hzcoe : (z : ModGL ReeTag.F4.tag L) = h⁻¹ * (y : ModGL ReeTag.F4.tag L) * h := rfl
      rw [hzcoe]
      calc h⁻¹ * (y : ModGL ReeTag.F4.tag L) * h * (x : ModGL ReeTag.F4.tag L)
          = h⁻¹ * (y : ModGL ReeTag.F4.tag L) * (h * (x : ModGL ReeTag.F4.tag L)) := by group
        _ = h⁻¹ * (y : ModGL ReeTag.F4.tag L) *
              ((h * (x : ModGL ReeTag.F4.tag L) * h⁻¹) * h) := by group
        _ = h⁻¹ * (y : ModGL ReeTag.F4.tag L) *
              (rootDiagUnit ReeTag.F4.tag (a xE) * h) := by rw [hEa xE]
        _ = h⁻¹ * ((y : ModGL ReeTag.F4.tag L) * rootDiagUnit ReeTag.F4.tag (a xE)) * h := by
              group
        _ = h⁻¹ * (rootDiagUnit ReeTag.F4.tag (a xE) * (y : ModGL ReeTag.F4.tag L)) * h := by
              rw [hycomm]
        _ = h⁻¹ * ((h * (x : ModGL ReeTag.F4.tag L) * h⁻¹) * (y : ModGL ReeTag.F4.tag L)) * h := by
              rw [hdx]
        _ = (x : ModGL ReeTag.F4.tag L) * (h⁻¹ * (y : ModGL ReeTag.F4.tag L) * h) := by group
    have hzE : z ∈ E := hsat0 z hzG hzP hzcomm hzF
    have hzEmap : (z : ModGL ReeTag.F4.tag L) ∈ Emap := Subgroup.mem_map.mpr ⟨z, hzE, rfl⟩
    let zE : Emap := ⟨(z : ModGL ReeTag.F4.tag L), hzEmap⟩
    have hdz : rootDiagUnit ReeTag.F4.tag (a zE) = h * (z : ModGL ReeTag.F4.tag L) * h⁻¹ :=
      (hEa zE).symm
    have hy_eq : (y : ModGL ReeTag.F4.tag L) = h * (z : ModGL ReeTag.F4.tag L) * h⁻¹ := by
      have h1 := congrArg (fun t : adjointGroup ReeTag.F4.tag L => (t : ModGL ReeTag.F4.tag L)) hyz
      rw [MulAut.conj_apply] at h1
      simpa using h1
    rw [hy_eq, ← hdz]
    exact Subgroup.subset_closure ⟨zE, rfl⟩
  have hAbs : AbsGeo p ((endPow F' p).eqLocus (MonoidHom.id (adjointGroup ReeTag.F4.tag L))) F'
      ((famSub ReeTag.F4.tag L a).subgroupOf (adjointGroup ReeTag.F4.tag L)) :=
    exc_ree_frame_absGeo hp hp2 hp3 hBor hF4 he w a ha F' hF'sq hfix hstab hidx hfinF'p hfin_tw hcardfam hsat0'
  exact absGeo_of_mulEquiv cΓ hG hc hE hAbs

end CFSG.HardMathSupport.C14Exc
