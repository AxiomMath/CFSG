module

public import CFSG.RankThree.PartTwo.Sec10.Item1012Res3Proof
import CFSG.Alternating.Multipliers.Small
import CFSG.GH74.Generic.GKFCover
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
import CFSG.LieType.Steinberg.CentralExt.PSLSmall
import CFSG.RankThree.PartTwo.KFacts.K72SLPiCField
public import CFSG.RankThree.PerfectCover.HopfFormula

public section

namespace CFSG.RankThree.PartTwo.Sec10.Item1012Res3Proof

open CFSG

theorem exists_pow_three_eq_one_of_map {E Ē : Type*} [Group E] [Finite E] [Group Ē]
    (π : E →* Ē) (hker : ¬ 3 ∣ Nat.card π.ker) {c : E} (hc : π c ^ 3 = 1) :
    ∃ c' ∈ Subgroup.zpowers c, c' ^ 3 = 1 ∧ π c' = π c := by
  obtain ⟨k, m, hm3, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c).ne' 3
    (by norm_num)
  obtain ⟨t, ht⟩ : ∃ t, m * m = 3 * t + 1 := ⟨m * m / 3, by
    have h : m % 3 = 1 ∨ m % 3 = 2 := by omega
    have hmm : m * m % 3 = 1 := by
      rw [Nat.mul_mod]
      rcases h with h | h <;> rw [h]
    omega⟩
  refine ⟨c ^ (m * m), Subgroup.npow_mem_zpowers c _, ?_, ?_⟩
  · have hc'k : (c ^ (m * m)) ^ 3 ^ k = 1 := by
      rw [← pow_mul, show m * m * 3 ^ k = (3 ^ k * m) * m by ring, pow_mul, ← hn,
        pow_orderOf_eq_one, one_pow]
    have hmem : (c ^ (m * m)) ^ 3 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow, map_pow, ← pow_mul, mul_comm, pow_mul, hc, one_pow]
    have h1 : orderOf ((c ^ (m * m)) ^ 3) ∣ 3 ^ k :=
      orderOf_dvd_of_pow_eq_one (by
        rw [← pow_mul, show 3 * 3 ^ k = 3 ^ k * 3 by ring, pow_mul, hc'k, one_pow])
    have h2 : orderOf ((c ^ (m * m)) ^ 3) ∣ Nat.card π.ker := by
      have h := orderOf_dvd_natCard (⟨_, hmem⟩ : π.ker)
      rwa [Subgroup.orderOf_mk] at h
    have hcop : Nat.Coprime (3 ^ k) (Nat.card π.ker) :=
      Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hker)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)
  · rw [map_pow, ht, pow_succ, pow_mul, hc, one_pow, one_mul]

theorem isCyclic_of_pow_three_mem {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 3 Q)
    (Z : Subgroup Q) (hZ : Nat.card Z ≤ 3) (h : ∀ x : Q, x ^ 3 = 1 → x ∈ Z) : IsCyclic Q := by
  by_contra hnc
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (IsPGroup 3 Q) := ⟨hQ⟩
  obtain ⟨S, -, hS9, hSel⟩ := CFSG.lemma_4_5_a (p := 3) (by norm_num) hnc
  have hSZ : S ≤ Z := fun x hx => h x (elemPow_eq_one_of_isElementaryAbelian x hx)
  have h9 := Subgroup.card_le_of_le hSZ
  rw [hS9] at h9
  omega

theorem mulAut_commute_of_isCyclic {Q : Type*} [Group Q] [IsCyclic Q] (σ τ : MulAut Q) :
    σ * τ = τ * σ := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Q)
  obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp (hg (σ g))
  obtain ⟨b, hb⟩ := Subgroup.mem_zpowers_iff.mp (hg (τ g))
  have hσ : ∀ n : ℤ, σ (g ^ n) = g ^ (a * n) := fun n => by rw [map_zpow, ← ha, ← zpow_mul]
  have hτ : ∀ n : ℤ, τ (g ^ n) = g ^ (b * n) := fun n => by rw [map_zpow, ← hb, ← zpow_mul]
  ext x
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg x)
  rw [MulAut.mul_apply, MulAut.mul_apply, hτ, hσ, hσ, hτ]
  congr 1
  ring

theorem commute_of_isPerfect_of_isCyclic {E : Type*} [Group E] (hE : Group.IsPerfect E)
    {Q : Subgroup E} [Q.Normal] (hQ : IsCyclic Q) (g : E) {q : E} (hq : q ∈ Q) :
    g * q * g⁻¹ = q := by
  set ρ : E →* MulAut Q := MulAut.conjNormal with hρ
  have hker : commutator E ≤ ρ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact mulAut_commute_of_isCyclic (ρ x) (ρ y)
  have hg : ρ g = 1 := by
    have h1 : g ∈ commutator E := by
      rw [Group.IsPerfect.commutator_eq_top]
      exact Subgroup.mem_top g
    exact hker h1
  have h2 := MulAut.conjNormal_apply (H := Q) g ⟨q, hq⟩
  rw [← hρ, hg] at h2
  exact h2.symm

theorem mem_center_of_mk_mem_center {E : Type*} [Group E] (hE : Group.IsPerfect E)
    {N : Subgroup E} [N.Normal] (hN : N ≤ Subgroup.center E) {m : E}
    (hm : (m : E ⧸ N) ∈ Subgroup.center (E ⧸ N)) : m ∈ Subgroup.center E := by
  have hcomm : ∀ x : E, m * x * m⁻¹ * x⁻¹ ∈ N := fun x => by
    rw [← QuotientGroup.eq_one_iff]
    have h := Subgroup.mem_center_iff.mp hm (x : E ⧸ N)
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rw [← h]
    group
  have hNc : ∀ n ∈ N, ∀ y : E, n * y = y * n := fun n hn y =>
    (Subgroup.mem_center_iff.mp (hN hn) y).symm
  have : IsMulCommutative N := ⟨⟨fun a b => Subtype.ext (hNc a a.2 b)⟩⟩
  let f : E →* N :=
    { toFun := fun x => ⟨m * x * m⁻¹ * x⁻¹, hcomm x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul]
        have hy := hNc _ (hcomm y) x⁻¹
        calc m * (x * y) * m⁻¹ * (x * y)⁻¹
            = m * x * m⁻¹ * (m * y * m⁻¹ * y⁻¹ * x⁻¹) := by group
          _ = m * x * m⁻¹ * (x⁻¹ * (m * y * m⁻¹ * y⁻¹)) := by rw [hy]
          _ = m * x * m⁻¹ * x⁻¹ * (m * y * m⁻¹ * y⁻¹) := by group }
  have hker : commutator E ≤ f.ker := Abelianization.commutator_subset_ker f
  rw [Group.IsPerfect.commutator_eq_top] at hker
  rw [Subgroup.mem_center_iff]
  intro x
  have h1 : f x = 1 := hker (Subgroup.mem_top x)
  have h2 : m * x * m⁻¹ * x⁻¹ = 1 := congrArg Subtype.val h1
  calc x * m = (m * x * m⁻¹ * x⁻¹)⁻¹ * (m * x) := by group
    _ = m * x := by rw [h2, inv_one, one_mul]

theorem card_comap_center {E : Type*} [Group E] [Finite E] (N : Subgroup E) [N.Normal] :
    Nat.card ((Subgroup.center (E ⧸ N)).comap (QuotientGroup.mk' N)) =
      Nat.card N * Nat.card (Subgroup.center (E ⧸ N)) := by
  set K := (Subgroup.center (E ⧸ N)).comap (QuotientGroup.mk' N) with hK
  let φ : K →* Subgroup.center (E ⧸ N) :=
    { toFun := fun k => ⟨QuotientGroup.mk' N (k : E), k.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        simp }
  have hφs : Function.Surjective φ := by
    rintro ⟨w, hw⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N w
    exact ⟨⟨x, hw⟩, rfl⟩
  have hNK : N ≤ K := fun x hx => by
    rw [hK, Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact Subgroup.one_mem _
  have hker : φ.ker = N.subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h1
      exact (QuotientGroup.eq_one_iff (k : E)).mp (congrArg Subtype.val h1)
    · intro h1
      exact Subtype.ext ((QuotientGroup.eq_one_iff (k : E)).mpr h1)
  have h1 := φ.ker.card_mul_index
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hφs, Subgroup.card_top, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNK).toEquiv] at h1
  exact h1.symm

theorem eq_bot_of_le_center_of_mulEquiv {E X : Type} [Group E] [Finite E] [Group X]
    (hE : Group.IsPerfect E) {N : Subgroup E} [N.Normal] (hN : N ≤ Subgroup.center E)
    (hN3 : IsPGroup 3 N) (hZ : Nat.card (Subgroup.center (E ⧸ N)) = 3)
    (e : (E ⧸ N) ⧸ Subgroup.center (E ⧸ N) ≃* X)
    (hM : Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier X) ∣ 48) : N = ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set q : E →* X := e.toMonoidHom.comp
    ((QuotientGroup.mk' (Subgroup.center (E ⧸ N))).comp (QuotientGroup.mk' N)) with hq
  have hqs : Function.Surjective q :=
    e.surjective.comp ((QuotientGroup.mk'_surjective _).comp (QuotientGroup.mk'_surjective _))
  have hqker : q.ker = (Subgroup.center (E ⧸ N)).comap (QuotientGroup.mk' N) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap, hq, MonoidHom.comp_apply, MonoidHom.comp_apply,
      MulEquiv.coe_toMonoidHom, map_eq_one_iff e e.injective, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  have hcen : q.ker ≤ Subgroup.center E := by
    rw [hqker]
    intro x hx
    exact mem_center_of_mk_mem_center hE hN hx
  have hdvd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hE q hqs hcen
  rw [hqker, card_comap_center, hZ] at hdvd
  have h16 : Nat.card N ∣ 16 := by
    have h48 := hdvd.trans hM
    rw [show (48 : ℕ) = 16 * 3 by norm_num] at h48
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h48
  obtain ⟨j, hj⟩ := hN3.exists_card_eq
  have hj0 : j = 0 := by
    by_contra hj0
    have h3 : 3 ∣ Nat.card N := by
      rw [hj]
      exact dvd_pow_self 3 hj0
    have := h3.trans h16
    norm_num at this
  rw [hj0, pow_zero] at hj
  exact Subgroup.eq_bot_of_card_eq N hj

theorem eq_bot_of_le_center_of_type
    {E : Type} [Group E]
    [Finite E] (hE : Group.IsPerfect E) {N : Subgroup E} [N.Normal]
    (hN : N ≤ Subgroup.center E) (hN3 : IsPGroup 3 N)
    (htype : Sec4.IsSLThreePiAt (E ⧸ N) 4 ∨
      Sec4.IsTripleCover (E ⧸ N) (alternatingGroup (Fin 6))) : N = ⊥ := by
  rcases htype with h4 | h6
  · have h4' : Sec4.IsSLThreePiAt (E ⧸ N) (2 ^ 2) := h4
    have hZ := KFacts.card_center_of_isSLThreePiAt_two_pow (by norm_num) h4'
    obtain ⟨K, _, _, ⟨hK, -, ⟨eW⟩⟩ | ⟨-, h3, -⟩⟩ := h4
    · set e₁ : (E ⧸ N) ≃* Matrix.SpecialLinearGroup (Fin 3) K :=
        eW.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K).symm
      set e₂ : (E ⧸ N) ⧸ Subgroup.center (E ⧸ N) ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 3) K :=
        QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      set φ : K ≃+* GaloisField 2 2 :=
        CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 2 (by norm_num) (by rw [hK]; norm_num)
      set e : (E ⧸ N) ⧸ Subgroup.center (E ⧸ N) ≃*
          Matrix.ProjectiveSpecialLinearGroup (Fin 3) (GaloisField 2 2) :=
        e₂.trans (CFSG.ClassicalModels.projectiveSpecialLinearFieldEquiv φ (Fin 3))
      refine eq_bot_of_le_center_of_mulEquiv hE hN hN3 hZ e ?_
      obtain ⟨-, ⟨eM⟩⟩ := CFSG.LieType.Steinberg.CentralExt.SLClosed.psl_three_four_hopfMultiplier
      rw [← Nat.card_congr (CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).toEquiv,
        Nat.card_congr eM.toEquiv]
      norm_num [Nat.card_eq_fintype_card]
    · norm_num at h3
  · obtain ⟨hZ, ⟨e⟩⟩ := h6
    refine eq_bot_of_le_center_of_mulEquiv hE hN hN3 hZ e ?_
    rw [CFSG.Alternating.Multipliers.hopfMultiplier_alternatingGroup_six.2]
    norm_num

theorem ks1012CoverThree_holds :
    KS1012CoverThree := by
  intro E _ _ hEperf C _ hCs Z hZc hZ3 hCZ htype
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O' := pPrimeCore 3 C with hO'
  set O := O'.map C.subtype with hOdef
  have hOC : O ≤ C := Subgroup.map_subtype_le _
  have hO3 : ¬ 3 ∣ Nat.card O := by
    rw [hOdef, Subgroup.card_map_of_injective C.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp pPrimeCore_coprime_card
  have hOn : O.Normal := by
    constructor
    rintro _ ⟨n, hn, rfl⟩ g
    have hσ := pPrimeCore_map_iso 3 (MulAut.conjNormal (H := C) g)
    refine ⟨MulAut.conjNormal g n, ?_, MulAut.conjNormal_apply g n⟩
    have h1 : MulAut.conjNormal g n ∈
        (pPrimeCore 3 C).map (MulAut.conjNormal (H := C) g).toMonoidHom := ⟨n, hn, rfl⟩
    rwa [hσ] at h1
  set π := QuotientGroup.mk' O with hπ
  have hπker : π.ker = O := QuotientGroup.ker_mk' O
  have hEb : Group.IsPerfect (E ⧸ O) := by
    have := hEperf
    exact Group.IsPerfect.ofSurjective (f := π) (QuotientGroup.mk'_surjective O)
  set Cb := C.map π with hCbdef
  have hCbn : Cb.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective O)
  set κ : C →* Cb := (π.comp C.subtype).codRestrict Cb (fun c => ⟨c, c.2, rfl⟩) with hκ
  have hκs : Function.Surjective κ := by
    rintro ⟨_, ⟨c, hc, rfl⟩⟩
    exact ⟨⟨c, hc⟩, rfl⟩
  have hκker : κ.ker = O' := by
    ext c
    rw [MonoidHom.mem_ker]
    constructor
    · intro h1
      have h2 : π (c : E) = 1 := congrArg Subtype.val h1
      rw [← MonoidHom.mem_ker, hπker, hOdef] at h2
      exact (Subgroup.mem_map_iff_mem C.subtype_injective).mp h2
    · intro h1
      apply Subtype.ext
      change π (c : E) = 1
      rw [← MonoidHom.mem_ker, hπker, hOdef]
      exact Subgroup.mem_map_of_mem _ h1
  set eCb : C ⧸ O' ≃* Cb := (QuotientGroup.quotientMulEquivOfEq hκker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective κ hκs) with heCb
  have hCbcore : pPrimeCore 3 Cb = ⊥ := by
    have h0 : pPrimeCore 3 (C ⧸ O') = ⊥ := CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
    rw [← pPrimeCore_map_iso 3 eCb, h0, Subgroup.map_bot]
  have hCbs : Group.IsSolvable Cb := by
    have := hCs
    exact Group.isSolvable_of_surjective hκs
  set Q := pCore 3 Cb with hQdef
  have hFQ : fittingSubgroup Cb = Q := Fitting_eq_pcore Cb 3 hCbcore
  set Zb := Z.map π with hZbdef
  have hZb : Nat.card Zb ≤ 3 :=
    (Nat.card_le_card_of_surjective _ (π.subgroupMap_surjective Z)).trans
      (Nat.le_of_dvd (by norm_num) hZ3)
  have hQ3 : ∀ x : Q, x ^ 3 = 1 → ((x : Cb) : E ⧸ O) ∈ Zb := by
    intro x hx
    obtain ⟨c, hcC, hc⟩ := (x : Cb).2
    have hc3 : π c ^ 3 = 1 := by
      rw [hc]
      have h1 : ((x : Cb) : E ⧸ O) ^ 3 = ((x ^ 3 : Q) : Cb) := rfl
      rw [h1, hx]
      rfl
    obtain ⟨c', hc'z, hc'3, hc'π⟩ :=
      exists_pow_three_eq_one_of_map π (by rw [hπker]; exact hO3) hc3
    have hc'C : c' ∈ C := (Subgroup.zpowers_le.mpr hcC) hc'z
    exact ⟨c', hCZ c' hc'C hc'3, hc'π.trans hc⟩
  set ZQ : Subgroup Q := Zb.comap (Cb.subtype.comp Q.subtype) with hZQ
  have hZQcard : Nat.card ZQ ≤ 3 := by
    let f : ZQ → Zb := fun z => ⟨Cb.subtype.comp Q.subtype z, z.2⟩
    refine (Nat.card_le_card_of_injective f ?_).trans hZb
    intro z z' h
    have h1 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (Subtype.ext h1))
  have hQcyc : IsCyclic Q := isCyclic_of_pow_three_mem pCore_isPGroup ZQ hZQcard
    (fun x hx => hQ3 x hx)
  set Qh := Q.map Cb.subtype with hQh
  have hQhn : Qh.Normal := by
    constructor
    rintro _ ⟨n, hn, rfl⟩ g
    have hσ := pCore_map_iso 3 (MulAut.conjNormal (H := Cb) g)
    refine ⟨MulAut.conjNormal g n, ?_, MulAut.conjNormal_apply g n⟩
    have h1 : MulAut.conjNormal g n ∈
        (pCore 3 Cb).map (MulAut.conjNormal (H := Cb) g).toMonoidHom := ⟨n, hn, rfl⟩
    rwa [hσ] at h1
  have hQhcyc : IsCyclic Qh := by
    have := hQcyc
    exact isCyclic_of_surjective (Q.equivMapOfInjective Cb.subtype Cb.subtype_injective).toMonoidHom
      (Q.equivMapOfInjective Cb.subtype Cb.subtype_injective).surjective
  have hcent : ∀ (g q : E ⧸ O), q ∈ Qh → g * q * g⁻¹ = q := fun g q hq =>
    commute_of_isPerfect_of_isCyclic hEb hQhcyc g hq
  have hCbQ : ∀ y : Cb, y ∈ Q := by
    intro y
    rw [← hFQ]
    refine centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hCbs ?_
    rw [hFQ, Subgroup.mem_centralizer_iff]
    intro x hx
    apply Subtype.ext
    have h := hcent (y : E ⧸ O) (x : E ⧸ O) ⟨x, hx, rfl⟩
    simp only [Subgroup.coe_mul]
    calc (x : E ⧸ O) * y = (y * x * (y : E ⧸ O)⁻¹) * y := by rw [h]
      _ = y * x := by group
  have hCb3 : IsPGroup 3 Cb := fun y => by
    obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 3) (G := Cb)) ⟨y, hCbQ y⟩
    exact ⟨k, Subtype.ext (congrArg (fun z : Q => ((z : Cb) : E ⧸ O)) hk)⟩
  have hCbZ : Cb ≤ Subgroup.center (E ⧸ O) := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro g
    have h := hcent g y ⟨⟨y, hy⟩, hCbQ ⟨y, hy⟩, rfl⟩
    calc g * y = g * y * g⁻¹ * g := by group
      _ = y * g := by rw [h]
  have htype' : Sec4.IsSLThreePiAt ((E ⧸ O) ⧸ Cb) 4 ∨
      Sec4.IsTripleCover ((E ⧸ O) ⧸ Cb) (alternatingGroup (Fin 6)) :=
    type_of_mulEquiv (QuotientGroup.quotientQuotientEquivQuotient O C hOC).symm htype
  have hCbbot : Cb = ⊥ := eq_bot_of_le_center_of_type hEb hCbZ hCb3 htype'
  have hCO : C ≤ O := fun c hc => by
    have h1 : π c ∈ Cb := ⟨c, hc, rfl⟩
    rw [hCbbot, Subgroup.mem_bot] at h1
    rw [← hπker]
    exact h1
  rw [le_antisymm hCO hOC]
  exact hO3

end CFSG.RankThree.PartTwo.Sec10.Item1012Res3Proof

