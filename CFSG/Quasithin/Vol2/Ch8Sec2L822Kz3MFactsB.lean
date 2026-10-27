module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Facts
public import CFSG.Quasithin.Vol2.Ch8Sec2L822R1

public section

namespace CFSG.Quasithin.H13

open CFSG.Quasithin
open scoped commutatorElement

private theorem eq_one_of_pow_three_of_pow_two_pow_kz3b {G : Type*} [Group G] {z : G} (h3 : z ^ 3 = 1)
    {n : ℕ} (h2 : z ^ 2 ^ n = 1) : z = 1 := by
  have hcop : Nat.Coprime 3 (2 ^ n) := Nat.Coprime.pow_right _ (by norm_num)
  have h := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
  rw [hcop.gcd_eq_one] at h
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h)

theorem pow_index_mem_commutator_of_central_kz3b {Q : Type*} [Group Q] [Finite Q]
    (hQ : Group.IsPerfect Q) (W : Subgroup Q) {z : Q} (hz : z ∈ Subgroup.center Q) :
    z ^ W.index ∈ ⁅W, W⁆ := by
  have hkey : ∀ (k : ℕ) (g₀ : Q), g₀⁻¹ * z ^ k * g₀ ∈ W → g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    have hc : z ^ k ∈ Subgroup.center Q := Subgroup.pow_mem _ hz k
    rw [mul_assoc, ← Subgroup.mem_center_iff.mp hc g₀, inv_mul_cancel_left]
  let T : Q →* Abelianization ↥W := MonoidHom.transfer (Abelianization.of : ↥W →* Abelianization ↥W)
  have hT := MonoidHom.transfer_eq_pow (Abelianization.of : ↥W →* Abelianization ↥W) z hkey
  have hTone : T z = 1 := by
    haveI := hQ
    have hle : commutator Q ≤ T.ker := Abelianization.commutator_subset_ker T
    exact MonoidHom.mem_ker.mp (hle Group.IsPerfect.mem_commutator)
  have hmem : (⟨z ^ W.index, MonoidHom.transfer_eq_pow_aux z hkey⟩ : ↥W) ∈
      (Abelianization.of : ↥W →* Abelianization ↥W).ker := by
    rw [MonoidHom.mem_ker, ← hT]
    exact hTone
  rw [Abelianization.ker_of] at hmem
  rw [← Subgroup.map_subtype_commutator]
  exact Subgroup.mem_map_of_mem W.subtype hmem

theorem commutator_eq_self_of_central_cover_kz3b {Q : Type*} [Group Q] [Finite Q]
    (hQ : Group.IsPerfect Q) {Z W : Subgroup Q} [Z.Normal] (hZc : Z ≤ Subgroup.center Q) (hZW : Z ≤ W)
    (hZ3 : Nat.card Z = 3) (hindex : ¬ 3 ∣ W.index)
    (hbar : ⁅W.map (QuotientGroup.mk' Z), W.map (QuotientGroup.mk' Z)⁆ = W.map (QuotientGroup.mk' Z)) :
    ⁅W, W⁆ = W := by
  have hZD : Z ≤ ⁅W, W⁆ := by
    intro z hz
    have hz3 : z ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
      rw [hZ3] at h
      exact congrArg Subtype.val h
    have hpow := pow_index_mem_commutator_of_central_kz3b hQ W (hZc hz)
    have hmod : z ^ W.index = z ^ (W.index % 3) := by
      conv_lhs => rw [← Nat.div_add_mod W.index 3, pow_add, pow_mul, hz3, one_pow, one_mul]
    rw [hmod] at hpow
    have h12 : W.index % 3 = 1 ∨ W.index % 3 = 2 := by omega
    rcases h12 with h | h
    · rwa [h, pow_one] at hpow
    · rw [h] at hpow
      have hzz : (z ^ 2) ^ 2 = z := by
        calc (z ^ 2) ^ 2 = z ^ 3 * z := by rw [← pow_mul, ← pow_succ]
          _ = z := by rw [hz3, one_mul]
      rw [← hzz]
      exact Subgroup.pow_mem _ hpow 2
  refine le_antisymm (Subgroup.commutator_le_self W) ?_
  intro w hw
  have hmem : QuotientGroup.mk' Z w ∈ ⁅W.map (QuotientGroup.mk' Z), W.map (QuotientGroup.mk' Z)⁆ := by
    rw [hbar]
    exact Subgroup.mem_map_of_mem _ hw
  rw [← Subgroup.map_commutator] at hmem
  obtain ⟨d, hd, hdw⟩ := Subgroup.mem_map.mp hmem
  have hdz : d⁻¹ * w ∈ Z := QuotientGroup.eq.mp hdw
  have hw' : w = d * (d⁻¹ * w) := by group
  rw [hw']
  exact Subgroup.mul_mem _ hd (hZD hdz)

theorem exists_two_complement_of_central_kz3b {M : Type*} [Group M] [Finite M] {Z : Subgroup M}
    (hZ : Z ≤ Subgroup.center M) (hZ3 : Nat.card Z = 3) (h2 : ∀ x : M, ∃ n : ℕ, x ^ 2 ^ n ∈ Z) :
    ∃ K : Subgroup M, IsPGroup 2 K ∧ K ⊔ Z = ⊤ ∧
      ∀ x : M, (∃ n : ℕ, x ^ 2 ^ n = 1) → x ∈ K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Z.Normal := Subgroup.normal_of_le_center hZ
  have hquot : IsPGroup 2 (M ⧸ Z) := by
    intro g
    induction g using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨n, hn⟩ := h2 x
      exact ⟨n, by rw [← QuotientGroup.mk_pow]; exact (QuotientGroup.eq_one_iff _).mpr hn⟩
  obtain ⟨i, hi⟩ := (IsPGroup.iff_card).mp hquot
  have hindex : Z.index = 2 ^ i := hi
  have hcop : Nat.Coprime (Nat.card Z) Z.index := by
    rw [hZ3, hindex]
    exact Nat.Coprime.pow_right _ (by norm_num)
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hK2 : IsPGroup 2 K := by
    have hc := hK.card_mul
    have h3 := Subgroup.card_mul_index Z
    refine IsPGroup.of_card (n := i) ?_
    rw [← hindex]
    rw [← h3, hZ3] at hc
    exact Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3) (by rw [hZ3] at h3; omega)
  refine ⟨K, hK2, by rw [sup_comm]; exact hK.sup_eq_top, fun x ⟨n, hn⟩ => ?_⟩
  have hx : x ∈ K ⊔ Z := by rw [sup_comm, hK.sup_eq_top]; exact Subgroup.mem_top x
  obtain ⟨k, hk, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  have hcomm : Commute k z := Subgroup.mem_center_iff.mp (hZ hz) k
  have hz3 : z ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
    rw [hZ3] at h
    exact congrArg Subtype.val h
  rw [hcomm.mul_pow] at hn
  have hzn : z ^ 2 ^ n ∈ K := by
    have : z ^ 2 ^ n = (k ^ 2 ^ n)⁻¹ := eq_inv_of_mul_eq_one_right hn
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hk _)
  have hz1 : z ^ 2 ^ n = 1 := Subgroup.disjoint_def.mp hK.disjoint (Subgroup.pow_mem _ hz _) hzn
  have hz0 : z = 1 := eq_one_of_pow_three_of_pow_two_pow_kz3b hz3 hz1
  rw [hz0, mul_one]
  exact hk

theorem comap_pCore_eq_sup_ker_kz3b {X B : Type} [Group X] [Finite X] [Group B] (ρ : X →* B)
    (hρ : Function.Surjective ρ) (hZ : ρ.ker ≤ Subgroup.center X) (hZ3 : Nat.card ρ.ker = 3) :
    (CFSG.pCore 2 B).comap ρ = CFSG.pCore 2 X ⊔ ρ.ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · set M : Subgroup X := (CFSG.pCore 2 B).comap ρ
    have hMnormal : M.Normal := Subgroup.Normal.comap CFSG.pCore_normal ρ
    have hZM : ρ.ker ≤ M := MonoidHom.ker_le_comap ρ _
    let Z' : Subgroup M := ρ.ker.subgroupOf M
    have hZ'c : Z' ≤ Subgroup.center M := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro m
      exact Subtype.ext (Subgroup.mem_center_iff.mp (hZ hz) m.1)
    have hZ'3 : Nat.card Z' = 3 := by
      rw [← hZ3]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZM).toEquiv
    have h2 : ∀ x : M, ∃ n : ℕ, x ^ 2 ^ n ∈ Z' := by
      intro x
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := B)) ⟨ρ x.1, x.2⟩
      refine ⟨n, ?_⟩
      show (x ^ 2 ^ n : M).1 ∈ ρ.ker
      rw [MonoidHom.mem_ker]
      have := congrArg Subtype.val hn
      simpa [map_pow] using this
    obtain ⟨K, hK2, hKZ, hK⟩ := exists_two_complement_of_central_kz3b hZ'c hZ'3 h2
    let K' : Subgroup X := K.map M.subtype
    have hK'2 : IsPGroup 2 K' := hK2.map M.subtype
    have hK'M : K' ⊔ ρ.ker = M := by
      have h1 := congrArg (Subgroup.map M.subtype) hKZ
      rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype] at h1
      have h2' : Z'.map M.subtype = ρ.ker := by
        rw [Subgroup.subgroupOf_map_subtype]
        exact inf_eq_left.mpr hZM
      rw [h2'] at h1
      exact h1
    have hK'norm : K'.Normal := by
      refine ⟨fun k hk g => ?_⟩
      obtain ⟨k0, hk0, rfl⟩ := Subgroup.mem_map.mp hk
      obtain ⟨n, hn⟩ := hK2 ⟨k0, hk0⟩
      have hn1 : k0 ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
      have hn' : (k0 : X) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn1
      have hgM : g * (k0 : X) * g⁻¹ ∈ M := hMnormal.conj_mem _ k0.2 g
      have hmem := hK ⟨g * (k0 : X) * g⁻¹, hgM⟩ ⟨n, Subtype.ext (by
        show (g * (k0 : X) * g⁻¹) ^ 2 ^ n = 1
        rw [conj_pow, hn', mul_one, mul_inv_cancel])⟩
      exact Subgroup.mem_map.mpr ⟨_, hmem, rfl⟩
    have hK'le : K' ≤ CFSG.pCore 2 X := CFSG.LieType.BorelTits.le_pCore 2 hK'norm hK'2
    calc M = K' ⊔ ρ.ker := hK'M.symm
      _ ≤ CFSG.pCore 2 X ⊔ ρ.ker := sup_le_sup_right hK'le _
  · refine sup_le ?_ (MonoidHom.ker_le_comap ρ _)
    have hle : (CFSG.pCore 2 X).map ρ ≤ CFSG.pCore 2 B := by
      apply CFSG.LieType.BorelTits.le_pCore 2
      · exact Subgroup.Normal.map CFSG.pCore_normal ρ hρ
      · exact IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := X)) ρ
    exact Subgroup.map_le_iff_le_comap.mp hle

private theorem alternatingGroup_six_not_comm_kz3b :
    ¬ ∀ a b : alternatingGroup (Fin 6), a * b = b * a := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hcard : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    have h := two_mul_nat_card_alternatingGroup (α := Fin 6)
    have hperm : Nat.card (Equiv.Perm (Fin 6)) = 720 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm]
      simp [Nat.factorial]
    omega
  exact res822_nonabelian_of_not_prime (by rw [hcard]; norm_num)

theorem isHat_quot_pCore_of_central_cover_kz3b {X B : Type} [Group X] [Finite X] [Group B]
    (ρ : X →* B) (hρ : Function.Surjective ρ) (hZ : ρ.ker ≤ Subgroup.center X)
    (hZ3 : Nat.card ρ.ker = 3) (hperf : Group.IsPerfect X)
    (hA : IsAlt 6 (B ⧸ CFSG.pCore 2 B)) :
    IsHat (X ⧸ CFSG.pCore 2 X) (alternatingGroup (Fin 6)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eA⟩ := hA
  haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  haveI : IsSimpleGroup (B ⧸ CFSG.pCore 2 B) := MulEquiv.isSimpleGroup eA
  have hSnab : ¬ ∀ a b : B ⧸ CFSG.pCore 2 B, a * b = b * a := by
    intro hc
    apply alternatingGroup_six_not_comm_kz3b
    intro a b
    have h2 := congrArg eA (hc (eA.symm a) (eA.symm b))
    simpa using h2
  let σ : X →* B ⧸ CFSG.pCore 2 B := (QuotientGroup.mk' (CFSG.pCore 2 B)).comp ρ
  have hσ : Function.Surjective σ := (QuotientGroup.mk'_surjective _).comp hρ
  have hσker : σ.ker = CFSG.pCore 2 X ⊔ ρ.ker := by
    have h1 : σ.ker = (CFSG.pCore 2 B).comap ρ := by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact h1.trans (comap_pCore_eq_sup_ker_kz3b ρ hρ hZ hZ3)
  set N : Subgroup X := CFSG.pCore 2 X
  have hNσ : N ≤ σ.ker := hσker ▸ le_sup_left
  let σ' : X ⧸ N →* B ⧸ CFSG.pCore 2 B := QuotientGroup.lift N σ hNσ
  have hσ' : Function.Surjective σ' := by
    intro s
    obtain ⟨x, rfl⟩ := hσ s
    exact ⟨QuotientGroup.mk x, rfl⟩
  have hNmap : N.map (QuotientGroup.mk' N) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨n, hn, rfl⟩
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff n).mpr hn
  have hσ'ker : σ'.ker = ρ.ker.map (QuotientGroup.mk' N) := by
    rw [QuotientGroup.ker_lift, hσker, Subgroup.map_sup, hNmap, bot_sup_eq]
  have hctr_ge : σ'.ker ≤ Subgroup.center (X ⧸ N) := by
    rw [hσ'ker]
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    induction g using QuotientGroup.induction_on with
    | H x =>
      show (QuotientGroup.mk x : X ⧸ N) * QuotientGroup.mk z = QuotientGroup.mk z * QuotientGroup.mk x
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp (hZ hz) x]
  have hctr_le : Subgroup.center (X ⧸ N) ≤ σ'.ker := by
    intro y hy
    have hc : σ' y ∈ Subgroup.center (B ⧸ CFSG.pCore 2 B) := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨g, rfl⟩ := hσ' s
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hy g]
    rw [res822_center_bot_of_simple hSnab, Subgroup.mem_bot] at hc
    exact MonoidHom.mem_ker.mpr hc
  have hctr : Subgroup.center (X ⧸ N) = σ'.ker := le_antisymm hctr_le hctr_ge
  have hinj : Function.Injective ((QuotientGroup.mk' N).comp ρ.ker.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have haN : (a : X) ∈ N := (QuotientGroup.eq_one_iff _).mp ha
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨a.1, haN⟩
    have h2 : (a : X) ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    have h3 : (a : X) ^ 3 = 1 := by
      have h := pow_card_eq_one' (G := ρ.ker) (x := a)
      rw [hZ3] at h
      exact congrArg Subtype.val h
    exact Subtype.ext (eq_one_of_pow_three_of_pow_two_pow_kz3b h3 h2)
  have hcardZ : Nat.card (ρ.ker.map (QuotientGroup.mk' N)) = 3 := by
    rw [← hZ3]
    have h := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [MonoidHom.range_comp, Subgroup.range_subtype] at h
    exact h.symm
  have e : ((X ⧸ N) ⧸ Subgroup.center (X ⧸ N)) ≃* alternatingGroup (Fin 6) :=
    ((QuotientGroup.quotientMulEquivOfEq hctr).trans
      (QuotientGroup.quotientKerEquivOfSurjective σ' hσ')).trans eA
  haveI : Group.IsPerfect X := hperf
  obtain ⟨a0, b0, hab⟩ : ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
    have h := alternatingGroup_six_not_comm_kz3b
    push Not at h
    exact h
  refine ⟨⟨inferInstance, MulEquiv.isSimpleGroup e, e.symm a0, e.symm b0, fun h => hab ?_⟩, ?_, ⟨e⟩⟩
  · have h2 := congrArg e h
    simp only [map_mul, MulEquiv.apply_symm_apply] at h2
    exact h2
  · rw [hctr, hσ'ker]
    exact hcardZ

theorem kzM22Cover17280_kz3_of (h1 : KzM22Sub5760_kz3) :
    KzM22Cover17280_kz3 := by
  intro Q _ _ hQ W hZW hW
  obtain ⟨hqs, hZ3, ⟨e⟩⟩ := hQ
  have hperfQ : Group.IsPerfect Q := hqs.1
  let π : Q →* Q ⧸ Subgroup.center Q := QuotientGroup.mk' (Subgroup.center Q)
  let ρ : ↥W →* ↥(W.map π) := π.subgroupMap W
  have hρ : Function.Surjective ρ := MonoidHom.subgroupMap_surjective π W
  have hρker : ρ.ker = (Subgroup.center Q).subgroupOf W := by
    rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk']
  have hρcard : Nat.card ρ.ker = 3 := by
    rw [hρker, ← hZ3]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZW).toEquiv
  have hρcen : ρ.ker ≤ Subgroup.center ↥W := by
    rw [hρker]
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (Subgroup.mem_center_iff.mp (Subgroup.mem_subgroupOf.mp hz) w.1)
  have hM22 : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 :=
    CFSG.Sporadic.Mathieu.card_M22
  have hQcard : Nat.card Q = 3 * 443520 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q), hZ3,
      Nat.card_congr e.toEquiv, hM22, mul_comm]
  have hindex : W.index = 77 := by
    have h := Subgroup.card_mul_index W
    rw [hW, hQcard] at h
    omega
  have hWbar : Nat.card (W.map π) = 5760 := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv, hρcard, hW] at h
    omega
  obtain ⟨hperfbar, hAlt⟩ := h1 (Q ⧸ Subgroup.center Q) ⟨e⟩ (W.map π) hWbar
  have hWperf : ⁅W, W⁆ = W :=
    commutator_eq_self_of_central_cover_kz3b hperfQ le_rfl hZW hZ3 (by rw [hindex]; norm_num)
      hperfbar
  exact ⟨hWperf, isHat_quot_pCore_of_central_cover_kz3b ρ hρ hρcen hρcard
    (Subgroup.isPerfect_iff.mpr hWperf) hAlt⟩

end CFSG.Quasithin.H13
