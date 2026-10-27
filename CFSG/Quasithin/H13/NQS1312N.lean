module

public import CFSG.Quasithin.H13.NQS1312Z
public import CFSG.Quasithin.EmptyFaithful.S153QPC5

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3.NLine

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCB CFSG.Assembly.LowTwoRank CFSG.Quasithin.QP
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.SteinbergBR.BlockPar
open scoped IsMulCommutative commutatorElement

section SL3

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem three_dvd_card_sub_one_of_normal_flag1_line (h4 : 4 ≤ Nat.card F)
    {N : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)}
    (hNQ : N ≤ stabilizer (flagSpace 3 F 1))
    (hnorm : ∀ q ∈ stabilizer (flagSpace 3 F 1), ∀ y ∈ N, q * y * q⁻¹ ∈ N)
    (hcomm : IsPGroup 2 ↥⁅N, N⁆) {x : Matrix.SpecialLinearGroup (Fin 3) F} (hx : x ∈ N)
    (hx3 : orderOf x = 3) : 3 ∣ Nat.card F - 1 := by
  set Q := stabilizer (flagSpace 3 F 1) with hQ
  have hcN : ∀ q ∈ Q, ∀ y ∈ ⁅N, N⁆, q * y * q⁻¹ ∈ ⁅N, N⁆ := by
    intro q hq y hy
    have h1 : N.map (MulAut.conj q).toMonoidHom ≤ N := by
      rintro _ ⟨z, hz, rfl⟩
      exact hnorm q hq z hz
    have h2 : ((MulAut.conj q).toMonoidHom y) ∈ ⁅N, N⁆.map (MulAut.conj q).toMonoidHom :=
      ⟨y, hy, rfl⟩
    rw [Subgroup.map_commutator] at h2
    exact Subgroup.commutator_mono h1 h1 h2
  have hrad : ⁅N, N⁆ ≤ radU F (flagSpace 3 F 1) :=
    le_radU_of_isPGroup (by norm_num) (by norm_num) hcomm hcN
  have hxQ : x ∈ Q := hNQ hx
  set N₁ : Subgroup ↥Q := N.subgroupOf Q with hN₁
  set N₀ : Subgroup (GL (Fin 2) F) := N₁.map levi with hN₀
  have hρx : levi ⟨x, hxQ⟩ ∈ N₀ := ⟨⟨x, hxQ⟩, hx, rfl⟩
  have hnormal : N₀.Normal := by
    refine ⟨fun n hn A => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hn
    obtain ⟨q, rfl⟩ := levi_surjective A
    refine ⟨q * y * q⁻¹, ?_, by simp⟩
    show ((q * y * q⁻¹ : ↥Q) : Matrix.SpecialLinearGroup (Fin 3) F) ∈ N
    simpa using hnorm q q.2 y hy
  have habel : ∀ a ∈ N₀, ∀ b ∈ N₀, a * b = b * a := by
    rintro _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    have hy' : (y : Matrix.SpecialLinearGroup (Fin 3) F) ∈ N := hy
    have hz' : (z : Matrix.SpecialLinearGroup (Fin 3) F) ∈ N := hz
    have hyz : ((⁅y, z⁆ : ↥Q) : Matrix.SpecialLinearGroup (Fin 3) F) ∈ ⁅N, N⁆ := by
      have := Subgroup.commutator_mem_commutator hy' hz'
      simpa [commutatorElement_def] using this
    have h1 : levi ⁅y, z⁆ = 1 := (levi_eq_one_iff (⁅y, z⁆).2).2 (hrad hyz)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hρx3 : (levi ⟨x, hxQ⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨x, hxQ⟩ : ↥Q) ^ 3 = 1 := by
      apply Subtype.ext
      simp only [Subgroup.coe_pow, Subgroup.coe_one]
      have h1 := pow_orderOf_eq_one x
      rwa [hx3] at h1
    rw [this, map_one]
  have hρx1 : levi ⟨x, hxQ⟩ ≠ 1 := by
    intro h
    have hxr : x ∈ radU F (flagSpace 3 F 1) := (levi_eq_one_iff hxQ).1 h
    have h2 := radU_mul_self hxr
    have h3 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2)
    rw [hx3] at h3
    omega
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ := exists_scalar_of_abelian_normal h4 N₀ habel hρx
  have hc3 : c ^ 3 = 1 := by
    have h1 := congrArg (fun A : GL (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 0) hρx3
    simp only [Units.val_pow_eq_pow_val, Units.val_one, hc] at h1
    rw [← map_pow] at h1
    simpa [Matrix.scalar_apply, ← Units.val_pow_eq_pow_val] using h1
  have hc1 : c ≠ 1 := by
    intro h
    apply hρx1
    apply Units.ext
    rw [hc, h]
    simp
  have hcord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
  have := orderOf_dvd_natCard c
  rwa [hcord, Nat.card_units] at this

theorem three_dvd_card_sub_one_of_normal_parabolic_line (h4 : 4 ≤ Nat.card F)
    {P N : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)}
    (hP : IsMaxParabolic2 (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) P) (hNP : N ≤ P)
    (hnorm : ∀ p ∈ P, ∀ y ∈ N, p * y * p⁻¹ ∈ N) {x : Matrix.SpecialLinearGroup (Fin 3) F}
    (hx : x ∈ N) (hx3 : orderOf x = 3) (h2 : IsPGroup 2 ↥⁅N, N⁆) : 3 ∣ Nat.card F - 1 := by
  obtain ⟨θ, hθ⟩ := exists_aut_map_eq_stabilizer_flag1 hP
  set θ' := (θ : Matrix.SpecialLinearGroup (Fin 3) F →* Matrix.SpecialLinearGroup (Fin 3) F)
    with hθ'
  refine three_dvd_card_sub_one_of_normal_flag1_line h4 (N := N.map θ') ?_ ?_ ?_ (x := θ x)
    ⟨x, hx, rfl⟩ ?_
  · rintro _ ⟨n, hn, rfl⟩
    rw [← hθ]
    exact ⟨n, hNP hn, rfl⟩
  · intro q hq y hy
    rw [← hθ] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    obtain ⟨n, hn, rfl⟩ := hy
    refine ⟨p * n * p⁻¹, hnorm p hp n hn, ?_⟩
    simp [hθ']
  · rw [← Subgroup.map_commutator]
    exact h2.of_equiv (⁅N, N⁆.equivMapOfInjective θ' θ.injective)
  · exact (orderOf_injective θ' θ.injective x).trans hx3

end SL3

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem false_of_sl3_parabolic_three {J V Mx K₁ : Subgroup G} {F : Type} [Field F] [Finite F]
    [CharP F 2] (hJV : J ≤ normalizer (V : Set G))
    (e : ↥(autOn J V) ≃* Matrix.SpecialLinearGroup (Fin 3) F)
    (hmax : IsMaxParabolic2 (autOn J V) (autOn (Mx ⊓ J) V))
    (hK₁M : K₁ ≤ Mx ⊓ J) (hK₁N : ∀ b ∈ Mx ⊓ J, ∀ k ∈ K₁, b * k * b⁻¹ ∈ K₁)
    {a : G} (haK : a ∈ K₁) (ha3 : orderOf a = 3) (haV : a ∉ centralizer (V : Set G))
    (h2 : IsPGroup 2 ↥⁅K₁, K₁⁆) (h4 : 4 ≤ Nat.card F) (h3 : ¬ 3 ∣ Nat.card F - 1) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := SBc17.actOn hJV with hπdef
  set φ : ↥J →* Matrix.SpecialLinearGroup (Fin 3) F := e.toMonoidHom.comp π with hφdef
  have haJ : a ∈ J := (hK₁M haK).2
  set a' : ↥J := ⟨a, haJ⟩ with ha'
  have ha'3 : a' ^ 3 = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, ha']
    have h1 := pow_orderOf_eq_one a
    rwa [ha3] at h1
  have hφa : φ a' ≠ 1 := by
    intro h1
    have h2 : π a' = 1 := e.injective (by simpa [hφdef] using h1)
    exact haV ((SBc17.actOn_eq_one_iff hJV a').1 h2)
  set K' : Subgroup ↥J := K₁.subgroupOf J with hK'
  have haK' : a' ∈ K' := haK
  set N : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) := K'.map φ with hN
  have hxN : φ a' ∈ N := ⟨a', haK', rfl⟩
  have hx3 : orderOf (φ a') = 3 := by
    refine orderOf_eq_prime ?_ hφa
    rw [← map_pow, ha'3, map_one]
  have hP := isMaxParabolic2_top_of_mulEquiv hmax e
  set P : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F) :=
    ((autOn (Mx ⊓ J) V).subgroupOf (autOn J V)).map e.toMonoidHom with hPdef
  have hNP : N ≤ P := by
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨π k, ?_, rfl⟩
    show ((π k : ↥(autOn J V)) : MulAut ↥V) ∈ autOn (Mx ⊓ J) V
    rw [hπdef, SBc17.coe_actOn]
    exact SBc17.mem_autOn_iff.2 ⟨k, hJV k.2, hK₁M hk, rfl⟩
  have hnorm : ∀ p ∈ P, ∀ y ∈ N, p * y * p⁻¹ ∈ N := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨k, hk, rfl⟩
    have hs' : (s : MulAut ↥V) ∈ autOn (Mx ⊓ J) V := hs
    obtain ⟨b, hbV, hb, hbs⟩ := SBc17.mem_autOn_iff.mp hs'
    have hbJ : b ∈ J := hb.2
    have hsπ : s = π ⟨b, hbJ⟩ :=
      Subtype.ext (by rw [hπdef, SBc17.coe_actOn]; exact hbs.symm)
    refine ⟨⟨b, hbJ⟩ * k * ⟨b, hbJ⟩⁻¹, ?_, ?_⟩
    · show ((⟨b, hbJ⟩ * k * ⟨b, hbJ⟩⁻¹ : ↥J) : G) ∈ K₁
      simpa using hK₁N b hb k hk
    · rw [hsπ]
      simp [hφdef]
  have h2N : IsPGroup 2 ↥⁅N, N⁆ := by
    have hcomm : ⁅N, N⁆ = ⁅K', K'⁆.map φ := (Subgroup.map_commutator K' K' φ).symm
    have hcG : ⁅K', K'⁆.map J.subtype = ⁅K₁, K₁⁆ := by
      rw [Subgroup.map_commutator, hK', Subgroup.map_subgroupOf_eq_of_le (hK₁M.trans inf_le_right)]
    intro y
    have hy : (y : Matrix.SpecialLinearGroup (Fin 3) F) ∈ ⁅K', K'⁆.map φ := by
      rw [← hcomm]
      exact y.2
    obtain ⟨c, hc, hcy⟩ := hy
    have hcG' : ((c : ↥J) : G) ∈ ⁅K₁, K₁⁆ := hcG ▸ ⟨c, hc, rfl⟩
    obtain ⟨m, hm⟩ := h2 ⟨(c : G), hcG'⟩
    refine ⟨m, ?_⟩
    apply Subtype.ext
    have hcm : c ^ 2 ^ m = 1 := by
      have h1 : ((c : ↥J) : G) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      apply Subtype.ext
      simpa using h1
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hcy, ← map_pow, hcm, map_one]
  exact h3 (three_dvd_card_sub_one_of_normal_parabolic_line h4 hP hNP hnorm hxN hx3 h2N)

theorem c6List_conj_k : ∀ e ∈ c6List, mul6 e kc = mul6 kc e ∨ mul6 e kc = mul6 (mul6 kc kc) e := by
  decide +kernel

omit [Finite G] in
theorem tau_conj_mem_zpowers_k
    {V : Subgroup G} [IsElementaryAbelian 2 V]
    {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hΦN : ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
      linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k)
    {n : G} (hn : n ∈ normalizer (V : Set G))
    (h15 : n * ptOf Φ (vecOf 15) * n⁻¹ = ptOf Φ (vecOf 15))
    (h52 : n * ptOf Φ (vecOf 52) * n⁻¹ = ptOf Φ (vecOf 52)) :
    tau Φ ⟨n, hn⟩ * kGL * (tau Φ ⟨n, hn⟩)⁻¹ ∈ zpowers kGL := by
  obtain ⟨κ, -, hκ, e, he, hκe⟩ := exists_c6List_of_centralizes hΦN hn h15 h52
  have hτ : tau Φ ⟨n, hn⟩ = κ := tau_eq_iff.2 hκ
  rw [hτ]
  rcases c6List_conj_k e he with h | h
  · have hc : κ * kGL = kGL * κ := Units.ext (by
      rw [Units.val_mul, Units.val_mul, hκe, coe_kGL, ← colMat_mul6, ← colMat_mul6, h])
    rw [hc, mul_inv_cancel_right]
    exact mem_zpowers _
  · have hc : κ * kGL = kGL * kGL * κ := Units.ext (by
      rw [Units.val_mul, Units.val_mul, Units.val_mul, hκe, coe_kGL, ← colMat_mul6,
        ← colMat_mul6, ← colMat_mul6, h])
    rw [hc, mul_inv_cancel_right]
    exact Subgroup.mul_mem _ (mem_zpowers _) (mem_zpowers _)

theorem exists_orderOf_three_sl3 (F : Type) [Field F] :
    ∃ g : Matrix.SpecialLinearGroup (Fin 3) F, orderOf g = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let A : Matrix (Fin 3) (Fin 3) F := !![0, 0, 1; 1, 0, 0; 0, 1, 0]
  have hA3 : A ^ 3 = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [A, pow_succ, Matrix.mul_apply, Fin.sum_univ_three]
  have hdet : A.det = 1 := by
    simp [A, Matrix.det_fin_three]
  refine ⟨⟨A, hdet⟩, orderOf_eq_prime ?_ ?_⟩
  · apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_one]
    exact hA3
  · intro h
    have h1 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 3) F =>
      (g : Matrix (Fin 3) (Fin 3) F) 0 0) h
    simp [A] at h1

theorem not_three_dvd_two_pow_sub_one_of_odd {n : ℕ} (hn : Odd n) : ¬ 3 ∣ 2 ^ n - 1 := by
  obtain ⟨m, rfl⟩ := hn
  have h4 : 4 ^ m % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h2 : 2 ^ (2 * m + 1) = 2 * 4 ^ m := by
    rw [pow_succ, pow_mul]
    norm_num
    ring
  rw [h2]
  omega

omit [Finite G] in
theorem isPGroup_commutator_of_tau_k {L V : Subgroup G} [IsElementaryAbelian 2 V]
    {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hCL : IsPGroup 2 ↥(L ⊓ centralizer (V : Set G))) {K₁ : Subgroup G}
    (hK₁ : K₁ ≤ (((zpowers kGL).comap (tau Φ)).map (normalizer (V : Set G)).subtype) ⊓ L) :
    IsPGroup 2 ↥⁅K₁, K₁⁆ := by
  refine hCL.to_le (Subgroup.commutator_le.2 fun a ha b hb => ?_)
  obtain ⟨⟨na, hna, rfl⟩, haL⟩ := hK₁ ha
  obtain ⟨⟨nb, hnb, rfl⟩, hbL⟩ := hK₁ hb
  have hcL : ⁅(na : G), (nb : G)⁆ ∈ L := by
    rw [commutatorElement_def]
    exact L.mul_mem (L.mul_mem (L.mul_mem haL hbL) (L.inv_mem haL)) (L.inv_mem hbL)
  refine ⟨hcL, ?_⟩
  have key : ((na * nb * na⁻¹ * nb⁻¹ : ↥(normalizer (V : Set G))) : G) ∈
      centralizer (V : Set G) := by
    refine (tau_eq_one_iff (Φ := Φ)).1 ?_
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 (Subgroup.mem_comap.1 hna)
    obtain ⟨j, hj⟩ := mem_zpowers_iff.1 (Subgroup.mem_comap.1 hnb)
    rw [← hi, ← hj, (Commute.zpow_zpow_self kGL i j).eq]
    group
  have e : ((na * nb * na⁻¹ * nb⁻¹ : ↥(normalizer (V : Set G))) : G) =
      ⁅((normalizer (V : Set G)).subtype na), ((normalizer (V : Set G)).subtype nb)⁆ := by
    simp [commutatorElement_def]
  rw [← e]
  exact key

theorem false_of_c27SL3_odd_line
    (h1332 : Stmt13_3_2) (h38 : A38ForSQTK) (hA3 : A3Orbits G)
    {T L V : Subgroup G} {z : G} [IsElementaryAbelian 2 V] (hH : QTH13 G T L)
    (hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1) (hF : QTU3InternalFrame T L V z)
    {Φ : Additive V ≃ₗ[ZMod 2] W6}
    (hΦLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j)
    (hΦN : ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
      linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k)
    (hΦT : ∀ (t : G) (ht : t ∈ T), ∃ s ∈ S0, linConj Φ
      (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨t, hF.2.2.2.2.2.2.2.1 ht⟩) = glLin s)
    {K : Subgroup G} (hK : K ∈ cComp (lineH Φ)) (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hQK : pCoreOf 2 (L ⊔ T) ≤ normalizer (K : Set G))
    {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : Odd n) (hn1 : n ≠ 1)
    (hcard : Fintype.card F = 2 ^ n)
    (e : ↥(autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T))))) ≃*
      ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F))
    (hmax : IsMaxParabolic2 (autOn K (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T)))))
      (autOn ((lineH Φ ⊓ normalizer (L : Set G)) ⊓ K)
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 (L ⊔ T)))))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, -, -, hVQ, -, hLV, -, -, -, hTC, -, -⟩ := id hF
  obtain ⟨-, -, -, -, hTI⟩ := u3_selected_local_normalizer_and_TI_of_1332 h1332 hH hF
  set Q := pCoreOf 2 (L ⊔ T) with hQ
  set VK := omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) with hVK
  set Mh := lineH Φ ⊓ normalizer (L : Set G) with hMh
  have hQp : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hQC : Q ≤ centralizer (V : Set G) := hTC ▸ inf_le_right
  have hKV : K ≤ normalizer (VK : Set G) := SBc17.le_normalizer_V K Q
  have hKH : K ≤ lineH Φ := le_of_mem_cComp hK
  have hyp : HypC23 (lineH Φ) Q Mh := hypC23_line h1332 hH hF hΦLs hΦN
  have hKc : CharTwo K :=
    charTwo_of_isSubnormal_line (subnormal_of_mem_cComp hK) (charTwo_lineH hH hF hΦT)
  have hKQc : CharTwo (K ⊔ Q) := Vol2Native.L239.charTwo_sup_of_le_normalizer hKc hQp hQK
  have hO : pCoreOf 2 (K ⊔ Q) ≤ Q :=
    c2_1_pCore_le (C2Push.isTwoRadicalIn_sup_of_le_normalizer hyp.radical hK hq hQK)
  have hVV : V ≤ VK := le_omegaOneCenterOf_line hKQc hO hVQ hQC
  set e' : ↥(autOn K VK) ≃* Matrix.SpecialLinearGroup (Fin 3) F :=
    e.trans (specialLinearGroupEquivStatedSL 3 F).symm with he'
  obtain ⟨g, hg⟩ := exists_orderOf_three_sl3 F
  have hK3 : 3 ∣ Nat.card K :=
    three_dvd_card_of_surjective (e'.toMonoidHom.comp (SBc17.actOn hKV))
      (e'.surjective.comp (SBc17.actOn_surjective hKV)) hg
  obtain ⟨k₁, hk₁L, x, hxL, hk₁3, hx3, hxk, hk₁τ, hxτ⟩ := exists_e9 hU3 hF hΦLs
  have hk₁H := mem_lineH_of_tau_k (hLV hk₁L) hk₁τ
  obtain ⟨hk₁K, -⟩ := le_normalizer_of_commute_three hA3 h38 (isSQTKIn_lineN hH) lineH_le_lineN
    lineN_le_normalizer_lineH (cComp_mem_of_subnormal isSubnormal_lineH hK) hKH hK3
    (mem_lineN_of_tau_k2 (hLV hxL) hxτ) (lineH_le_lineN hk₁H) hx3 hk₁3 hxk hk₁H
    (not_mem_lineH_of_tau_k2 (hLV hxL) hxτ)
  have hk₁M : k₁ ∈ Mh ⊓ K := ⟨⟨hk₁H, Subgroup.le_normalizer hk₁L⟩, hk₁K⟩
  have hk₁V : k₁ ∉ centralizer (VK : Set G) := by
    intro h
    have h1 : tau Φ ⟨k₁, hLV hk₁L⟩ = 1 :=
      tau_eq_one_iff.2 (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hVV) h)
    rw [hk₁τ] at h1
    exact kGL_spec.2 h1
  have hHu : lineH Φ ≤ centralizer ({ptOf Φ (vecOf 15)} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Set.mem_insert _ _))
  have hMhV : Mh ≤ normalizer (V : Set G) := fun y hy =>
    hTI _ (ptOf_mem _) ptOf_fifteen_ne_one ⟨hy.2, hHu hy.1⟩
  have hcen : ∀ y ∈ lineH Φ, y * ptOf Φ (vecOf 15) * y⁻¹ = ptOf Φ (vecOf 15) ∧
      y * ptOf Φ (vecOf 52) * y⁻¹ = ptOf Φ (vecOf 52) := by
    intro y hy
    rw [lineH, mem_centralizer_iff] at hy
    refine ⟨?_, ?_⟩
    · rw [← hy _ (Set.mem_insert _ _)]; group
    · rw [← hy _ (Set.mem_insert_of_mem _ rfl)]; group
  set K₁ : Subgroup G := Subgroup.closure {y | ∃ m ∈ Mh ⊓ K, y = m * k₁ * m⁻¹} with hK₁
  have hK₁M : K₁ ≤ Mh ⊓ K := by
    rw [hK₁, Subgroup.closure_le]
    rintro _ ⟨m, hm, rfl⟩
    exact (Mh ⊓ K).mul_mem ((Mh ⊓ K).mul_mem hm hk₁M) ((Mh ⊓ K).inv_mem hm)
  have hK₁N : ∀ b ∈ Mh ⊓ K, ∀ y ∈ K₁, b * y * b⁻¹ ∈ K₁ := by
    intro b hb y hy
    refine Subgroup.closure_induction (p := fun y _ => b * y * b⁻¹ ∈ K₁) ?_ ?_ ?_ ?_ hy
    · rintro _ ⟨m, hm, rfl⟩
      refine Subgroup.subset_closure ⟨b * m, (Mh ⊓ K).mul_mem hb hm, ?_⟩
      group
    · simp
    · intro u w _ _ hu hw
      have : b * (u * w) * b⁻¹ = (b * u * b⁻¹) * (b * w * b⁻¹) := by group
      rw [this]
      exact K₁.mul_mem hu hw
    · intro u _ hu
      have : b * u⁻¹ * b⁻¹ = (b * u * b⁻¹)⁻¹ := by group
      rw [this]
      exact K₁.inv_mem hu
  have hk₁K₁ : k₁ ∈ K₁ := Subgroup.subset_closure ⟨1, (Mh ⊓ K).one_mem, by group⟩
  have hK₁A : K₁ ≤ (((zpowers kGL).comap (tau Φ)).map (normalizer (V : Set G)).subtype) ⊓ L := by
    rw [hK₁, Subgroup.closure_le]
    rintro _ ⟨m, hm, rfl⟩
    have hmV : m ∈ normalizer (V : Set G) := hMhV hm.1
    refine ⟨⟨⟨m, hmV⟩ * ⟨k₁, hLV hk₁L⟩ * ⟨m, hmV⟩⁻¹, ?_, rfl⟩, ?_⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_inv, hk₁τ]
      exact tau_conj_mem_zpowers_k hΦN hmV (hcen m hm.1.1).1 (hcen m hm.1.1).2
    · exact (mem_normalizer_iff.1 hm.1.2 k₁).1 hk₁L
  have hCL : IsPGroup 2 ↥(L ⊓ centralizer (V : Set G)) := by
    rw [(u3_internal_frame_kernel hLV hU3 hF).1]
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have h2 : IsPGroup 2 ↥⁅K₁, K₁⁆ := isPGroup_commutator_of_tau_k hCL hK₁A
  have hchar : CharP F 2 := charP_two_of_card_line (by obtain ⟨m, rfl⟩ := hn; omega) hcard
  have hn3 : 3 ≤ n := by
    obtain ⟨m, rfl⟩ := hn
    omega
  have hcardN : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hcard]
  have h4 : 4 ≤ Nat.card F := by
    rw [hcardN]
    calc 4 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  have h3 : ¬ 3 ∣ Nat.card F - 1 := by
    rw [hcardN]
    exact not_three_dvd_two_pow_sub_one_of_odd hn
  exact false_of_sl3_parabolic_three hKV e' hmax hK₁M hK₁N hk₁K₁ hk₁3 hk₁V h2 h4 h3

end CFSG.Quasithin.H13.U3.NLine
