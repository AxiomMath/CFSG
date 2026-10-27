module

public import CFSG.RankThree.PartOne.D4RC.SylowSplit
public import CFSG.RankThree.PartOne.D4RC.Center

public noncomputable section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical2 (fixSubgroup unitarySet)
open scoped Matrix MatrixGroups Pointwise

set_option linter.unusedSectionVars false

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

section Group

variable {G : Type*} [Group G]

theorem rct_exists_mul_of_mem_sup {H N : Subgroup G} (hHN : H ≤ Subgroup.normalizer (N : Set G))
    {z : G} (hz : z ∈ H ⊔ N) : ∃ h ∈ H, ∃ n ∈ N, z = h * n := by
  have hconj : ∀ h ∈ H, ∀ n ∈ N, h⁻¹ * n * h ∈ N := fun h hh n hn => by
    have := (Subgroup.mem_normalizer_iff.1 (hHN (H.inv_mem hh)) n).1 hn
    simpa using this
  let P : Subgroup G :=
    { carrier := {z | ∃ h ∈ H, ∃ n ∈ N, z = h * n}
      mul_mem' := by
        rintro _ _ ⟨h, hh, n, hn, rfl⟩ ⟨h', hh', n', hn', rfl⟩
        refine ⟨h * h', H.mul_mem hh hh', h'⁻¹ * n * h' * n', N.mul_mem (hconj h' hh' n hn) hn', ?_⟩
        group
      one_mem' := ⟨1, H.one_mem, 1, N.one_mem, by group⟩
      inv_mem' := by
        rintro _ ⟨h, hh, n, hn, rfl⟩
        refine ⟨h⁻¹, H.inv_mem hh, h * n⁻¹ * h⁻¹, ?_, by group⟩
        have := hconj h⁻¹ (H.inv_mem hh) n⁻¹ (N.inv_mem hn)
        simpa using this }
  have hle : H ⊔ N ≤ P := sup_le (fun h hh => ⟨h, hh, 1, N.one_mem, by group⟩)
    (fun n hn => ⟨1, H.one_mem, n, hn, by group⟩)
  exact hle hz

theorem rct_pow_mul_mem {N : Subgroup G} {h : G} (hh : h ∈ Subgroup.normalizer (N : Set G))
    {n : G} (hn : n ∈ N) (k : ℕ) : ∃ n' ∈ N, (h * n) ^ k = h ^ k * n' := by
  induction k with
  | zero => exact ⟨1, N.one_mem, by group⟩
  | succ k ih =>
    obtain ⟨n', hn', he⟩ := ih
    refine ⟨h⁻¹ * n' * h * n, N.mul_mem ?_ hn, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hh) n').1 hn'
      simpa using this
    · rw [pow_succ, he]
      group

end Group

section Frame

variable {L : Type} [Field L]

theorem rct_diag_of_mem_torus {ρ : SL(3, L) →* ModGL TwistTag.D4.tag L}
    {σ' : Fin 3 → Fin 3 → Fin TwistTag.D4.tag.rank → ℤ} (hρ : IsA2Frame ρ σ') {X : SL(3, L)}
    (hX : ρ X ∈ torusGroup TwistTag.D4.tag L) :
    ∀ i j, i ≠ j → (X : Matrix (Fin 3) (Fin 3) L) i j = 0 := by
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hX
  intro i j hij
  obtain ⟨e, he⟩ := hρ.transv j i hij.symm
  have hc : X * Matrix.SpecialLinearGroup.transvection hij.symm 1 * X⁻¹ =
      Matrix.SpecialLinearGroup.transvection hij.symm (rootChar b (σ' j i) : L) := by
    apply hρ.injective
    rw [map_mul, map_mul, map_inv, hb, he, he, rootDiagUnit_conj_pinnedX b (hρ.isRoot j i hij.symm)]
    congr 1
    ring
  have hm : X * Matrix.SpecialLinearGroup.transvection hij.symm 1 =
      Matrix.SpecialLinearGroup.transvection hij.symm (rootChar b (σ' j i) : L) * X := by
    rw [← hc]
    group
  have h := congrFun (congrFun (congrArg (fun Y : SL(3, L) => (Y : Matrix (Fin 3) (Fin 3) L)) hm)
    i) i
  simp only [Matrix.SpecialLinearGroup.coe_mul] at h
  fin_cases i <;> fin_cases j <;> (try exact absurd rfl hij) <;>
    simp_all [Matrix.SpecialLinearGroup.transvection,
    Matrix.transvection, Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply,
    Matrix.one_apply, Matrix.add_apply]

theorem rct_exists_sq [CharP L 2] [IsAlgClosed L] {ρ : SL(3, L) →* ModGL TwistTag.D4.tag L}
    {σ' : Fin 3 → Fin 3 → Fin TwistTag.D4.tag.rank → ℤ} (hρ : IsA2Frame ρ σ')
    {t : ModGL TwistTag.D4.tag L} (ht : t ∈ torusGroup TwistTag.D4.tag L ⊓ ρ.range) :
    ∃ s ∈ torusGroup TwistTag.D4.tag L ⊓ ρ.range, s ^ 2 = t := by
  classical
  obtain ⟨htT, X, rfl⟩ := ht
  have hd := rct_diag_of_mem_torus hρ htT
  have hXd : (X : Matrix (Fin 3) (Fin 3) L) =
      Matrix.diagonal fun i => (X : Matrix (Fin 3) (Fin 3) L) i i := by
    ext a b
    by_cases hab : a = b
    · subst hab
      simp
    · rw [hd a b hab, Matrix.diagonal_apply_ne _ hab]
  choose y hy using fun i : Fin 3 =>
    IsAlgClosed.exists_pow_nat_eq ((X : Matrix (Fin 3) (Fin 3) L) i i) two_pos
  have hdet : (Matrix.diagonal y).det = 1 := by
    have h1 : ((Matrix.diagonal y).det) ^ 2 = 1 := by
      rw [Matrix.det_diagonal, ← Finset.prod_pow, Finset.prod_congr rfl (fun i _ => hy i),
        ← Matrix.det_diagonal, ← hXd, Matrix.SpecialLinearGroup.det_coe]
    have h2 : ((Matrix.diagonal y).det) ^ 2 = 1 ^ 2 := by rw [h1, one_pow]
    exact (frobenius_inj L 2) h2
  set Y : SL(3, L) := ⟨Matrix.diagonal y, hdet⟩ with hY
  have hYd : ∀ a b, a ≠ b → (Y : Matrix (Fin 3) (Fin 3) L) a b = 0 := fun a b hab => by
    rw [hY]
    exact Matrix.diagonal_apply_ne _ hab
  refine ⟨ρ Y, ⟨hρ.diag Y hYd, Y, rfl⟩, ?_⟩
  rw [← map_pow]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hY]
  change Matrix.diagonal y ^ 2 = _
  rw [Matrix.diagonal_pow, hXd]
  congr 1
  funext i
  exact hy i

theorem rct_exists_pow_two_pow [CharP L 2] [IsAlgClosed L]
    {ρ : SL(3, L) →* ModGL TwistTag.D4.tag L}
    {σ' : Fin 3 → Fin 3 → Fin TwistTag.D4.tag.rank → ℤ} (hρ : IsA2Frame ρ σ') (k : ℕ) :
    ∀ t ∈ torusGroup TwistTag.D4.tag L ⊓ ρ.range,
      ∃ s ∈ torusGroup TwistTag.D4.tag L ⊓ ρ.range, s ^ (2 ^ k) = t := by
  induction k with
  | zero => exact fun t ht => ⟨t, ht, by rw [pow_zero, pow_one]⟩
  | succ k ih =>
    intro t ht
    obtain ⟨s, hs, hst⟩ := ih t ht
    obtain ⟨r, hr, hrs⟩ := rct_exists_sq hρ hs
    exact ⟨r, hr, by rw [pow_succ, pow_mul', hrs, hst]⟩

theorem rct_eq_one_of_pow_two_pow [CharP L 2] {t : ModGL TwistTag.D4.tag L}
    (ht : t ∈ torusGroup TwistTag.D4.tag L) {k : ℕ} (h : t ^ (2 ^ k) = 1) : t = 1 := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
  have h1 : rootDiagUnitHom TwistTag.D4.tag L (a ^ (2 ^ k)) =
      rootDiagUnitHom TwistTag.D4.tag L 1 := by
    rw [map_pow, map_one]
    exact h
  have h2 : a ^ (2 ^ k) = 1 := rootDiagUnit_injective h1
  have h3 : a = 1 := by
    funext i
    have h4 : (a i) ^ (2 ^ k) = 1 := congrFun h2 i
    have h5 : ((a i : L) - 1) ^ (2 ^ k) = 0 := by
      rw [sub_pow_char_pow, ← Units.val_pow_eq_pow_val, h4, Units.val_one, one_pow, sub_self]
    have h6 : (a i : L) = 1 := sub_eq_zero.1 ((pow_eq_zero_iff (by positivity)).1 h5)
    exact Units.ext h6
  rw [h3]
  exact rootDiagUnit_one

theorem rct_mem_range_of_pow [IsAlgClosed L] (h2 : (2 : L) = 0)
    {ρ : SL(3, L) →* ModGL TwistTag.D4.tag L}
    {σ' : Fin 3 → Fin 3 → Fin TwistTag.D4.tag.rank → ℤ} (hρ : IsA2Frame ρ σ')
    {t : ModGL TwistTag.D4.tag L} (ht : t ∈ torusGroup TwistTag.D4.tag L) {k : ℕ}
    (htk : t ^ (2 ^ k) ∈ ρ.range) : t ∈ ρ.range := by
  have : CharP L 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h2)
  obtain ⟨s, hs, hsk⟩ := rct_exists_pow_two_pow hρ k _ ⟨Subgroup.pow_mem _ ht _, htk⟩
  have hc : Commute t s⁻¹ := by
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup ht
    exact rootDiagUnit_mul_comm_of_mem_torusGroup a (Subgroup.inv_mem _ hs.1)
  have hts : (t * s⁻¹) ^ (2 ^ k) = 1 := by
    rw [hc.mul_pow, inv_pow, hsk, mul_inv_cancel]
  have hts1 := rct_eq_one_of_pow_two_pow (Subgroup.mul_mem _ ht (Subgroup.inv_mem _ hs.1)) hts
  rw [mul_inv_eq_one.1 hts1]
  exact hs.2

end Frame

section Quasisimple

theorem rct_normal_dichotomy {Q : Type*} [Group Q] (h : CFSG.IsQuasisimple Q)
    (M : Subgroup Q) [M.Normal] : M ≤ Subgroup.center Q ∨ M = ⊤ := by
  obtain ⟨hperf, hsimple, -⟩ := h
  rcases hsimple.eq_bot_or_eq_top_of_normal (M.map (QuotientGroup.mk' (Subgroup.center Q))) with
    h0 | h1
  · left
    intro x hx
    have : QuotientGroup.mk' (Subgroup.center Q) x ∈ (⊥ : Subgroup (Q ⧸ Subgroup.center Q)) :=
      h0 ▸ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp this)
  · right
    have hMZ : M ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) M
      rw [h1, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hle : commutator Q ≤ M := by
      have e : commutator Q = ⁅M ⊔ Subgroup.center Q, M ⊔ Subgroup.center Q⁆ := by
        rw [hMZ]; rfl
      rw [e]
      rw [Subgroup.commutator_sup_right, Subgroup.commutator_center_left, sup_bot_eq,
        Subgroup.commutator_sup_left, Subgroup.commutator_center_right, sup_bot_eq]
      exact Subgroup.commutator_le_left M M
    rw [hperf.commutator_eq_top] at hle
    exact top_le_iff.mp hle

end Quasisimple

section Special

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ε : ℤ}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

theorem rct_mem_rclPx_of_two (F : RclFrame ℓ f K σ ε p L) {x : 𝒞[K, σ]} {i : Fin 4}
    (sp : RclSpecial F x i) {m : 𝒞[K, σ]} (hm : m ∈ Subgroup.centralizer ({x} : Set 𝒞[K, σ]))
    {k : ℕ} (hmk : m ^ (2 ^ k) = 1) : m ∈ rclPx sp := by
  classical
  obtain ⟨D⟩ := rcl_exists_algData F i
  have hrange : D.ρ.range = rootSpan TwistTag.D4.tag L (d4Sigma i) := by
    rw [D.frame.range, D.sigma_eq]
  obtain ⟨-, -, hTL, hfix, -, -, -, -⟩ := rcl_psi_props F sp
  have h2 : (2 : L) = 0 := by
    have h := CharP.cast_eq_zero L ℓ
    rw [F.hℓ2] at h
    exact_mod_cast h
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set m' : Subgroup.centralizer ({x} : Set 𝒞[K, σ]) := ⟨m, hm⟩ with hm'
  have hS : ∀ α ∈ d4Sigma i, IsRoot TwistTag.D4.tag α := fun α hα => isRoot_of_mem_d4Sigma hα
  have hnorm := CFSG.RankThree.PartOne.KE.torusGroup_le_normalizer_rootSpan (L := L) hS
  obtain ⟨t, ht, u, hu, htu⟩ := rct_exists_mul_of_mem_sup hnorm (hTL m')
  obtain ⟨u', hu', hpow⟩ := rct_pow_mul_mem (hnorm ht) hu (2 ^ k)
  have h1 : (rclPsi sp m') ^ (2 ^ k) = 1 := by
    rw [← map_pow]
    have : m' ^ (2 ^ k) = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hmk)
    rw [this, map_one]
  rw [htu, hpow] at h1
  have htk : t ^ (2 ^ k) ∈ D.ρ.range := by
    rw [hrange, eq_inv_of_mul_eq_one_left h1]
    exact Subgroup.inv_mem _ hu'
  have htR := rct_mem_range_of_pow h2 D.frame ht htk
  have hψN : rclPsi sp m' ∈ rootSpan TwistTag.D4.tag L (d4Sigma i) := by
    rw [htu]
    refine Subgroup.mul_mem _ ?_ hu
    rw [← hrange]
    exact htR
  exact (mem_rclPx_iff sp hm).2 (Subgroup.mem_inf.2 ⟨hψN, mem_twistedFixedPoints.2 (hfix m')⟩)

theorem rct_odd_relIndex (F : RclFrame ℓ f K σ ε p L) {x : 𝒞[K, σ]} {i : Fin 4}
    (sp : RclSpecial F x i) :
    Odd ((rclPx sp).relIndex (Subgroup.centralizer ({x} : Set 𝒞[K, σ]))) := by
  classical
  set H := Subgroup.centralizer ({x} : Set 𝒞[K, σ]) with hH
  set P := (rclPx sp).subgroupOf H with hP
  have hPn : P.Normal := ⟨fun n hn g => by
    rw [hP, Subgroup.mem_subgroupOf] at hn ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact rclPx_normal sp g.2 hn⟩
  rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
  intro h2
  have h2' : 2 ∣ Nat.card (H ⧸ P) := by
    rw [← Subgroup.index_eq_card]
    exact h2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := H ⧸ P) 2 h2'
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨n, hn⟩ : ∃ n, orderOf g = 2 ^ (orderOf g).factorization 2 * n ∧ ¬ 2 ∣ n :=
    ⟨orderOf g / 2 ^ (orderOf g).factorization 2, (Nat.mul_div_cancel' (Nat.ordProj_dvd _ _)).symm,
      Nat.not_dvd_ordCompl Nat.prime_two (orderOf_pos g).ne'⟩
  set a := (orderOf g).factorization 2
  have hga : (g ^ n) ^ (2 ^ a) = 1 := by
    rw [← pow_mul, mul_comm, ← hn.1, pow_orderOf_eq_one]
  have hmem : ((g ^ n : H) : 𝒞[K, σ]) ∈ rclPx sp :=
    rct_mem_rclPx_of_two F sp (g ^ n).2 (by rw [← Subgroup.coe_pow, hga, Subgroup.coe_one])
  have hq : ((g ^ n : H) : H ⧸ P) = 1 := (QuotientGroup.eq_one_iff _).2 hmem
  rw [QuotientGroup.mk_pow] at hq
  have hdvd : orderOf (g : H ⧸ P) ∣ n := orderOf_dvd_of_pow_eq_one hq
  rw [hg] at hdvd
  exact hn.2 hdvd

theorem rct_two_eq_bot (F : RclFrame ℓ f K σ ε p L) {x : 𝒞[K, σ]} {i : Fin 4}
    (sp : RclSpecial F x i) (M : Subgroup 𝒞[K, σ]) (hMP : M ≤ rclPx sp)
    (hMn : rclPx sp ≤ Subgroup.normalizer (M : Set 𝒞[K, σ])) (hM2 : IsPGroup 2 M) : M = ⊥ := by
  classical
  obtain ⟨hQfin, hq, -, -, -, hQψ, -, -⟩ := rcl_psi_props F sp
  have hψ : Function.Injective (rclPsi sp) := d4QPsi_injective triEmb_injective F.g0 sp.c x
  set W := (rclQ F i).comap (rclPsi sp) with hW
  have hWQ : W.map (rclPsi sp) = rclQ F i := by
    rw [hW, Subgroup.map_comap_eq, inf_eq_right.2 hQψ]
  let e1 : ↥(rclPx sp) ≃* ↥W :=
    (Subgroup.equivMapOfInjective W _ (Subgroup.subtype_injective _)).symm
  let e2 : ↥W ≃* ↥(W.map (rclPsi sp)) := Subgroup.equivMapOfInjective W _ hψ
  let e : ↥(rclPx sp) ≃* ↥(rclQ F i) := (e1.trans e2).trans (MulEquiv.subgroupCongr hWQ)
  set M' : Subgroup ↥(rclPx sp) := M.subgroupOf (rclPx sp) with hM'
  have hM'n : M'.Normal := ⟨fun n hn g => by
    rw [hM', Subgroup.mem_subgroupOf] at hn ⊢
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hMn g.2) n).1 hn⟩
  have hM''n : (M'.map e.toMonoidHom).Normal := Subgroup.Normal.map hM'n _ e.surjective
  rcases rct_normal_dichotomy hq (M'.map e.toMonoidHom) with hZ | hT
  · rw [eq_bot_iff]
    intro z hz
    have hzP := hMP hz
    have hzc : ((⟨z, hzP⟩ : ↥(rclPx sp)) : ↥(rclPx sp)) ∈ Subgroup.center ↥(rclPx sp) := by
      have h1 : e ⟨z, hzP⟩ ∈ Subgroup.center ↥(rclQ F i) := hZ ⟨⟨z, hzP⟩, hz, rfl⟩
      rw [Subgroup.mem_center_iff] at h1 ⊢
      intro g
      apply e.injective
      rw [map_mul, map_mul]
      exact h1 (e g)
    have hzC : z ∈ Subgroup.centralizer (rclPx sp : Set 𝒞[K, σ]) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have := Subgroup.mem_center_iff.1 hzc ⟨u, hu⟩
      exact congrArg Subtype.val this
    have h3 := rcy_pow_three_of_mem_center F sp hzP hzC
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hM2) ⟨z, hz⟩
    have hk' : orderOf z = 2 ^ k := (Subgroup.orderOf_coe (⟨z, hz⟩ : M)).trans hk
    have h4 : 2 ^ k ∣ 3 := hk' ▸ orderOf_dvd_of_pow_eq_one h3
    have hk0 : k = 0 := by
      by_contra hk0
      have h5 : 2 ∣ 3 := (dvd_pow_self 2 hk0).trans h4
      omega
    rw [hk0, pow_zero] at hk'
    rw [Subgroup.mem_bot]
    exact orderOf_eq_one_iff.1 hk'
  · exfalso
    have hM'top : M' = ⊤ := by
      apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
      rw [hT, Subgroup.map_top_of_surjective _ e.surjective]
    have hP2 : IsPGroup 2 ↥(rclPx sp) := hM2.to_le (fun u hu => by
      have : (⟨u, hu⟩ : ↥(rclPx sp)) ∈ M' := by rw [hM'top]; exact Subgroup.mem_top _
      exact this)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hfin : Finite ↥(rclPx sp) := Nat.finite_of_card_ne_zero (by
      rw [card_rclPx]
      exact Nat.card_pos.ne')
    obtain ⟨n, hn⟩ := hP2.exists_card_eq
    have hℓ : ℓ.Prime := Fact.out
    have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by have := F.hf; omega) hℓ.one_lt
    obtain ⟨hc1, hc2⟩ := rcl_card_rclQ F i
    rw [card_rclPx] at hn
    have hodd : ∃ m, m ∣ 2 ^ n ∧ Odd m ∧ 1 < m := by
      rcases F.hε with h | h
      · refine ⟨(ℓ ^ f) ^ 3 - 1, ?_, ?_, ?_⟩
        · rw [← hn, hc1 h]
          exact Dvd.intro_left _ rfl
        · have h8 : 2 ∣ ℓ ^ f := by rw [F.hℓ2]; exact dvd_pow_self 2 (by have := F.hf; omega)
          have h9 : 2 ∣ (ℓ ^ f) ^ 3 := dvd_pow h8 (by norm_num)
          have h10 : 1 ≤ (ℓ ^ f) ^ 3 := Nat.one_le_pow _ _ (by omega)
          rw [Nat.odd_iff]
          omega
        · have : 8 ≤ (ℓ ^ f) ^ 3 := by
            calc 8 = 2 ^ 3 := by norm_num
              _ ≤ (ℓ ^ f) ^ 3 := Nat.pow_le_pow_left hq2 3
          omega
      · refine ⟨(ℓ ^ f) ^ 3 + 1, ?_, ?_, ?_⟩
        · rw [← hn, hc2 h]
          exact Dvd.intro_left _ rfl
        · have h8 : 2 ∣ ℓ ^ f := by rw [F.hℓ2]; exact dvd_pow_self 2 (by have := F.hf; omega)
          have h9 : 2 ∣ (ℓ ^ f) ^ 3 := dvd_pow h8 (by norm_num)
          rw [Nat.odd_iff]
          omega
        · have : 1 ≤ (ℓ ^ f) ^ 3 := Nat.one_le_pow _ _ (by omega)
          omega
    obtain ⟨m, hm2, hmo, hm1⟩ := hodd
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hm2
    rcases j with _ | j
    · simp at hm1
    · rw [pow_succ] at hmo
      exact (Nat.not_even_iff_odd.2 hmo) (even_two.mul_left _)

theorem rct_twoCoreLocal (F : RclFrame ℓ f K σ ε p L) {x : 𝒞[K, σ]} {i : Fin 4}
    (sp : RclSpecial F x i) {Γ : Subgroup 𝒞[K, σ]} (hΓ : rclPx sp ≤ Γ) : TwoCoreLocal Γ x := by
  right
  refine ⟨rclPx sp, ⊥, hΓ, fun M hM hMn hM2 => rct_two_eq_bot F sp M hM hMn hM2, ?_, ?_,
    rclPx_le_centralizer sp, bot_le, ?_, ?_⟩
  · rw [Subgroup.card_bot]
    exact odd_one
  · intro r _ c hc
    rw [Subgroup.mem_bot] at hc
    rw [hc, mul_one, one_mul]
  · rw [sup_bot_eq]
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · exact fun hu => rclPx_normal sp hg hu
    · intro hu
      have := rclPx_normal sp (Subgroup.inv_mem _ hg) hu
      rwa [inv_inv, show g⁻¹ * (g * u * g⁻¹) * g = u by group] at this
  · rw [sup_bot_eq]
    exact rct_odd_relIndex F sp

end Special

end CFSG.RankThree.PartOne.D4RC
