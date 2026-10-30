module

public import CFSG.Assembly.OrderReductions.FixedPointLifting
public import CFSG.RankThree.PartTwo.Sec14.Item14Tools

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153Obs

open Subgroup

section ObsLift

theorem lift_of_maximal {M : Type*} [Group M] [Finite M] (N : Subgroup M) [N.Normal]
    (hN : (Nat.card N).Coprime 3) (A : Subgroup M) (hA : IsPGroup 3 A)
    (hmax : ∀ x : M, orderOf x = 3 → x ∈ Subgroup.centralizer (A : Set M) → x ∈ A)
    (x : M ⧸ N) (hx : orderOf x = 3) (hxA : ∀ a ∈ A, Commute x (a : M ⧸ N)) :
    ∃ y ∈ A, (y : M ⧸ N) = x := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : ¬ 3 ∣ Nat.card (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hN.symm
  obtain ⟨g, hgx, hgfix⟩ :=
    CFSG.OrderReductions.FixedPointLifting.exists_fixed_lift_of_coprime_kernel 3 hA
      ((MulAut.conj : M →* MulAut M).comp A.subtype)
      ((MulAut.conj : (M ⧸ N) →* MulAut (M ⧸ N)).comp ((QuotientGroup.mk' N).comp A.subtype))
      (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) hcop
      (fun a g => by simp [MulAut.conj_apply])
      x
      (fun a => by
        change ((a : M) : M ⧸ N) * x * ((a : M) : M ⧸ N)⁻¹ = x
        rw [mul_inv_eq_iff_eq_mul]
        exact (hxA (a : M) a.2).symm.eq)
  have hcomm : ∀ a ∈ A, a * g = g * a := by
    intro a ha
    have h2 : a * g * a⁻¹ = g := hgfix ⟨a, ha⟩
    exact mul_inv_eq_iff_eq_mul.mp h2
  have h3dvd : 3 ∣ orderOf g := by
    have h := orderOf_map_dvd (QuotientGroup.mk' N) g
    rw [hgx, hx] at h
    exact h
  obtain ⟨u, hu⟩ := h3dvd
  have hupos : 0 < u := by
    have := orderOf_pos g
    omega
  have hu3 : ¬ 3 ∣ u := by
    intro h3u
    have hxu : x ^ u = 1 := by
      apply orderOf_dvd_iff_pow_eq_one.mp
      rw [hx]
      exact h3u
    have hmemN : g ^ u ∈ N := by
      have hker : g ^ u ∈ (QuotientGroup.mk' N).ker := by
        rw [MonoidHom.mem_ker, map_pow, hgx, hxu]
      rwa [QuotientGroup.ker_mk'] at hker
    have hpow3 : (g ^ u) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, ← hu, pow_orderOf_eq_one]
    have hne1 : g ^ u ≠ 1 := by
      intro h1
      have hdvd : orderOf g ∣ u := orderOf_dvd_of_pow_eq_one h1
      rw [hu] at hdvd
      have := Nat.le_of_dvd hupos hdvd
      omega
    have hord3 : orderOf (g ^ u) = 3 := orderOf_eq_prime hpow3 hne1
    have hdvdN : orderOf (⟨g ^ u, hmemN⟩ : N) ∣ Nat.card N := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hord3] at hdvdN
    exact absurd (Nat.Coprime.eq_one_of_dvd hN.symm hdvdN) (by norm_num)
  have hmod : u * u % 3 = 1 := by
    have h : u % 3 = 1 ∨ u % 3 = 2 := by omega
    rcases h with h | h <;> simp [Nat.mul_mod, h]
  have hxpow : x ^ (u * u) = x := by
    have h := pow_mod_orderOf x (u * u)
    rw [hx, hmod, pow_one] at h
    exact h.symm
  have hφy : (QuotientGroup.mk' N) (g ^ (u * u)) = x := by
    rw [map_pow, hgx, hxpow]
  have hy3 : (g ^ (u * u)) ^ 3 = 1 := by
    rw [← pow_mul]
    have h : u * u * 3 = orderOf g * u := by
      rw [hu]
      ring
    rw [h, pow_mul, pow_orderOf_eq_one, one_pow]
  have hy1 : g ^ (u * u) ≠ 1 := by
    intro h1
    have h2 : x = 1 := by
      rw [← hφy, h1, map_one]
    have h3 : orderOf x = 1 := by
      rw [h2, orderOf_one]
    omega
  have hyord : orderOf (g ^ (u * u)) = 3 := orderOf_eq_prime hy3 hy1
  have hycent : g ^ (u * u) ∈ Subgroup.centralizer (A : Set M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hc : Commute h g := hcomm h hh
    exact (hc.pow_right (u * u)).eq
  exact ⟨g ^ (u * u), hmax _ hyord hycent, hφy⟩

end ObsLift

section ObsFixNC

theorem core_central {G : Type*} [Group G] [Finite G] (N A : Subgroup G) [N.Normal]
    (hNA : N ⊔ A = ⊤) (hA : IsPGroup 3 A) (hN3 : 3 ∣ Nat.card N) :
    ∃ x ∈ N, orderOf x = 3 ∧ ∀ a ∈ A, Commute x a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c, hc⟩ : ∃ c : ℕ, N.index = 3 ^ c := by
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hA
    have h1 : N.index = N.relIndex A := by
      rw [← Subgroup.relIndex_top_right, ← hNA, Subgroup.relIndex_sup_left]
    have h2 : N.relIndex A ∣ Nat.card A := Subgroup.index_dvd_card (N.subgroupOf A)
    rw [ha] at h2
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 h2
    exact ⟨i, h1.trans hi⟩
  obtain ⟨P, hPp, hAP, hPidx⟩ : ∃ P : Subgroup G, IsPGroup 3 P ∧ A ≤ P ∧ ¬ 3 ∣ P.index := by
    obtain ⟨S, hAS⟩ := IsPGroup.exists_le_sylow hA
    exact ⟨(S : Subgroup G), S.isPGroup', hAS, Sylow.not_dvd_index S⟩
  have hGdiv : 3 ^ (c + 1) ∣ Nat.card G := by
    rw [← Subgroup.card_mul_index N, hc, pow_succ']
    exact mul_dvd_mul_right hN3 _
  have hcop : Nat.Coprime (3 ^ (c + 1)) P.index :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hPidx)
  have hPdiv : 3 ^ (c + 1) ∣ Nat.card P := by
    apply hcop.dvd_of_dvd_mul_left
    rw [Subgroup.index_mul_card]
    exact hGdiv
  have hT0 : N.subgroupOf P ≠ ⊥ := by
    intro hbot
    have h1 : N.relIndex P = Nat.card P := by
      show (N.subgroupOf P).index = Nat.card P
      rw [hbot, Subgroup.index_bot]
    have h2 : N.relIndex P ∣ 3 ^ c := by
      rw [← hc]
      exact Subgroup.relIndex_dvd_index_of_normal N P
    rw [h1] at h2
    have h3 : Nat.card P ≤ 3 ^ c := Nat.le_of_dvd (by positivity) h2
    have h4 : 3 ^ (c + 1) ≤ Nat.card P := Nat.le_of_dvd Nat.card_pos hPdiv
    have h5 : 0 < 3 ^ c := by positivity
    rw [pow_succ'] at h4
    linarith
  haveI : Group.IsNilpotent P := IsPGroup.isNilpotent hPp
  haveI : (N.subgroupOf P).Normal := inferInstance
  have hX : N.subgroupOf P ⊓ Subgroup.center ↥P ≠ ⊥ :=
    Group.IsNilpotent.inf_center_ne_bot_of_normal hT0
  have hXdvd : 3 ∣ Nat.card ↥(N.subgroupOf P ⊓ Subgroup.center ↥P) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hPp
    have hd : Nat.card ↥(N.subgroupOf P ⊓ Subgroup.center ↥P) ∣ 3 ^ n := by
      rw [← hn]
      exact Subgroup.card_subgroup_dvd_card _
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 hd
    rw [hk]
    have hk0 : k ≠ 0 := by
      rintro rfl
      apply hX
      rw [Subgroup.eq_bot_iff_card, hk, pow_zero]
    exact dvd_pow_self 3 hk0
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 3 hXdvd
  have hgN : ((g : ↥P) : G) ∈ N := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp g.2).1
  have hgz : (g : ↥P) ∈ Subgroup.center ↥P := (Subgroup.mem_inf.mp g.2).2
  refine ⟨((g : ↥P) : G), hgN, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hg]
  · intro a ha
    have h1 : a * ((g : ↥P) : G) = ((g : ↥P) : G) * a :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hgz ⟨a, hAP ha⟩)
    exact h1.symm

theorem exists_fixed_noncentral_of_coprime_center {Q : Type*} [Group Q] [Finite Q]
    (K Abar : Subgroup Q) (hKperf : ⁅K, K⁆ = K)
    (hKq : ∀ H : Subgroup Q, H ≤ K → (H.subgroupOf K).Normal → H = K ∨ H ≤ Subgroup.centralizer (K : Set Q))
    (h3K : 3 ∣ Nat.card K) (hZ : ¬ 3 ∣ Nat.card (K ⊓ Subgroup.centralizer (K : Set Q) : Subgroup Q))
    (hA : IsPGroup 3 Abar) (hAK : Abar ≤ Subgroup.normalizer (K : Set Q)) :
    ∃ x ∈ K, orderOf x = 3 ∧ x ∉ Subgroup.centralizer (K : Set Q) ∧ ∀ a ∈ Abar, Commute x a := by
  have hKM : (K.subgroupOf (K ⊔ Abar)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hAK)
  haveI := hKM
  have hNA : K.subgroupOf (K ⊔ Abar) ⊔ Abar.subgroupOf (K ⊔ Abar) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hA' : IsPGroup 3 (Abar.subgroupOf (K ⊔ Abar)) := IsPGroup.comap_subtype hA
  have h3 : 3 ∣ Nat.card (K.subgroupOf (K ⊔ Abar)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv]
    exact h3K
  obtain ⟨x, hxN, hxord, hxA⟩ :=
    core_central (K.subgroupOf (K ⊔ Abar)) (Abar.subgroupOf (K ⊔ Abar)) hNA hA' h3
  have hxK : ((x : (K ⊔ Abar : Subgroup Q)) : Q) ∈ K := Subgroup.mem_subgroupOf.mp hxN
  have hxord' : orderOf ((x : (K ⊔ Abar : Subgroup Q)) : Q) = 3 := by
    rw [Subgroup.orderOf_coe]
    exact hxord
  refine ⟨((x : (K ⊔ Abar : Subgroup Q)) : Q), hxK, hxord', ?_, ?_⟩
  · intro hc
    have hmem : ((x : (K ⊔ Abar : Subgroup Q)) : Q) ∈ K ⊓ Subgroup.centralizer (K : Set Q) :=
      Subgroup.mem_inf.mpr ⟨hxK, hc⟩
    apply hZ
    have hdvd := orderOf_dvd_natCard (⟨_, hmem⟩ : ↥(K ⊓ Subgroup.centralizer (K : Set Q)))
    rw [Subgroup.orderOf_mk, hxord'] at hdvd
    exact hdvd
  · intro a ha
    have haM : a ∈ K ⊔ Abar := (le_sup_right : Abar ≤ K ⊔ Abar) ha
    exact (hxA ⟨a, haM⟩ (Subgroup.mem_subgroupOf.mpr ha)).map (K ⊔ Abar).subtype

end ObsFixNC

section ObsIdx2

theorem exists_centralizing_not_mem_of_index_two {M : Type*} [Group M] [Finite M]
    (R R₀ A : Subgroup M) (hR : (Nat.card R).Coprime 3) (hA : IsPGroup 3 A)
    (hAR : A ≤ Subgroup.normalizer (R : Set M)) (hAR₀ : A ≤ Subgroup.normalizer (R₀ : Set M))
    (hR₀R : R₀ ≤ R) (hidx : R₀.relIndex R = 2) :
    ∃ g ∈ R, g ∉ R₀ ∧ g ∈ Subgroup.centralizer (A : Set M) := by
  have hcardR : Nat.card R = 2 * Nat.card R₀ := by
    have h : R₀.relIndex R * Nat.card (R₀ ⊓ R : Subgroup M) = Nat.card R :=
      Subgroup.relIndex_mul_card R₀ R
    rw [inf_of_le_left hR₀R, hidx] at h
    omega
  have hcardS : Nat.card ↥((R : Set M) \ (R₀ : Set M)) + Nat.card R₀ = Nat.card R := by
    have h1 := Set.ncard_diff_add_ncard_of_subset (SetLike.coe_subset_coe.mpr hR₀R)
    have h2 : Nat.card ↥((R : Set M) \ (R₀ : Set M)) = ((R : Set M) \ (R₀ : Set M)).ncard :=
      Nat.card_coe_set_eq _
    have h3 : Nat.card R₀ = (R₀ : Set M).ncard := Nat.card_coe_set_eq (R₀ : Set M)
    have h4 : Nat.card R = (R : Set M).ncard := Nat.card_coe_set_eq (R : Set M)
    omega
  have hcop : ¬ 3 ∣ Nat.card R := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hR.symm
  have hnd : ¬ 3 ∣ Nat.card ↥((R : Set M) \ (R₀ : Set M)) := by
    omega
  have hmem : ∀ (a : A) (x : ↥((R : Set M) \ (R₀ : Set M))),
      (a : M) * (x : M) * (a : M)⁻¹ ∈ ((R : Set M) \ (R₀ : Set M)) := by
    intro a x
    have h1 := Subgroup.mem_set_normalizer_iff.mp (hAR a.2) (x : M)
    have h2 := Subgroup.mem_set_normalizer_iff.mp (hAR₀ a.2) (x : M)
    exact ⟨h1.mp x.2.1, fun h => x.2.2 (h2.mpr h)⟩
  letI : MulAction A ↥((R : Set M) \ (R₀ : Set M)) :=
    { smul := fun a x => ⟨(a : M) * (x : M) * (a : M)⁻¹, hmem a x⟩
      one_smul := fun x => Subtype.ext (by
        show ((1 : A) : M) * (x : M) * ((1 : A) : M)⁻¹ = (x : M)
        simp)
      mul_smul := fun a b x => Subtype.ext (by
        show ((a * b : A) : M) * (x : M) * ((a * b : A) : M)⁻¹
          = (a : M) * ((b : M) * (x : M) * (b : M)⁻¹) * (a : M)⁻¹
        simp [mul_assoc]) }
  obtain ⟨x, hx⟩ := IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card hA _ hnd
  rw [MulAction.mem_fixedPoints] at hx
  refine ⟨(x : M), x.2.1, x.2.2, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hfix := congrArg Subtype.val (hx ⟨h, hh⟩)
  change h * (x : M) * h⁻¹ = (x : M) at hfix
  rw [mul_inv_eq_iff_eq_mul] at hfix
  exact hfix

end ObsIdx2

section ObsComm2

theorem conj_mem_of_subgroupOf_normal {Q : Type*} [Group Q] {T H : Subgroup Q}
    (hH : (H.subgroupOf T).Normal) (hHT : H ≤ T) {g k : Q} (hg : g ∈ T) (hk : k ∈ H) :
    g * k * g⁻¹ ∈ H := by
  have h := hH.conj_mem ⟨k, hHT hk⟩ (Subgroup.mem_subgroupOf.mpr hk) ⟨g, hg⟩
  rw [Subgroup.mem_subgroupOf] at h
  simpa using h

theorem commute_of_normal_quasisimple {Q : Type*} [Group Q] (T K K' : Subgroup Q)
    (hK : (K.subgroupOf T).Normal) (hK' : (K'.subgroupOf T).Normal) (hKT : K ≤ T)
    (hK'T : K' ≤ T)
    (hKperf : ⁅K, K⁆ = K)
    (hKq : ∀ H : Subgroup Q, H ≤ K → (H.subgroupOf K).Normal →
      H = K ∨ H ≤ Subgroup.centralizer (K : Set Q))
    (hne : ¬ K ≤ K') :
    ⁅K, K'⁆ = ⊥ := by
  have hDnorm : ((K ⊓ K').subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hnK, hnK'⟩ := Subgroup.mem_inf.mp hn
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    refine Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem g.2 hnK) (K.inv_mem g.2), ?_⟩
    exact conj_mem_of_subgroupOf_normal hK' hK'T (hKT g.2) hnK'
  have hD : K ⊓ K' ≤ Subgroup.centralizer (K : Set Q) := by
    rcases hKq (K ⊓ K') inf_le_left hDnorm with h | h
    · exact absurd (h.symm.le.trans inf_le_right) hne
    · exact h
  have hcomm : ⁅K, K'⁆ ≤ K ⊓ K' := by
    refine Subgroup.commutator_le.mpr ?_
    intro g₁ hg₁ g₂ hg₂
    show g₁ * g₂ * g₁⁻¹ * g₂⁻¹ ∈ K ⊓ K'
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · have h := conj_mem_of_subgroupOf_normal hK hKT (hK'T hg₂) (K.inv_mem hg₁)
      simpa only [mul_assoc] using K.mul_mem hg₁ h
    · have h := conj_mem_of_subgroupOf_normal hK' hK'T (hKT hg₁) hg₂
      exact K'.mul_mem h (K'.inv_mem hg₂)
  have hcomm' : ⁅K', K⁆ ≤ K ⊓ K' := (Subgroup.commutator_comm_le K' K).trans hcomm
  have hDK : ⁅K ⊓ K', K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hD
  have h1 : ⁅⁅K, K'⁆, K⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono hcomm (le_refl K)).trans hDK.le)
  have h2 : ⁅⁅K', K⁆, K⁆ = ⊥ :=
    le_bot_iff.mp ((Subgroup.commutator_mono hcomm' (le_refl K)).trans hDK.le)
  have h3 : ⁅⁅K, K⁆, K'⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
  rw [hKperf] at h3
  exact h3

end ObsComm2

section ObsStep1b

private theorem oPrimeResidualOf_three_le_of_le_sup {M : Type*} [Group M] {H K S : Subgroup M}
    (hcop : Nat.Coprime 3 (Nat.card S)) (hSK : S ≤ Subgroup.normalizer (K : Set M))
    (hH : H ≤ K ⊔ S) : CFSG.GH74.GLS.oPrimeResidualOf 3 H ≤ K := by
  rw [CFSG.RankThree.PartTwo.Sec14.oPrimeResidualOf_eq_closure 3 H, Subgroup.closure_le]
  rintro y ⟨hy, k, hk⟩
  exact CFSG.RankThree.PartTwo.Sec14.mem_left_of_pow_prime_pow Nat.prime_three hSK hcop (hH hy) hk

theorem conj_eq_of_image_eq {M : Type*} [Group M] [Finite M] (N X Y : Subgroup M) [N.Normal] (hN : (Nat.card N).Coprime 3)
    [X.Normal] (hYX : Y ≤ X) (hXY : X ≤ Subgroup.normalizer (Y : Set M))
    (hY3 : Y = CFSG.GH74.GLS.oPrimeResidualOf 3 Y) (s : M)
    (h : (Y.map (MulAut.conj s).toMonoidHom).map (QuotientGroup.mk' N) =
      Y.map (QuotientGroup.mk' N)) :
    Y.map (MulAut.conj s).toMonoidHom = Y := by
  have hφX : ∀ y ∈ X, (MulAut.conj s).toMonoidHom y ∈ X := by
    intro y hy
    show s * y * s⁻¹ ∈ X
    exact Subgroup.Normal.conj_mem ‹X.Normal› y hy s
  have hsup : Y.map (MulAut.conj s).toMonoidHom ≤ Y ⊔ (X ⊓ N) := by
    rintro _ ⟨y, hy, rfl⟩
    have hmem : QuotientGroup.mk' N ((MulAut.conj s).toMonoidHom y) ∈
        Y.map (QuotientGroup.mk' N) := by
      rw [← h]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hy)
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp hmem
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hzeq
    have hzN : z⁻¹ * (MulAut.conj s).toMonoidHom y ∈ N := QuotientGroup.eq.mp hzeq
    have hzX : z⁻¹ * (MulAut.conj s).toMonoidHom y ∈ X :=
      mul_mem (inv_mem (hYX hz)) (hφX y (hYX hy))
    have key : z * (z⁻¹ * (MulAut.conj s).toMonoidHom y) ∈ Y ⊔ (X ⊓ N) :=
      mul_mem (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hzX, hzN⟩))
    rwa [mul_inv_cancel_left] at key
  have hS3 : Nat.Coprime 3 (Nat.card (X ⊓ N : Subgroup M)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le (inf_le_right : X ⊓ N ≤ N)) hN.symm
  have hO : CFSG.GH74.GLS.oPrimeResidualOf 3 (Y.map (MulAut.conj s).toMonoidHom) ≤ Y :=
    oPrimeResidualOf_three_le_of_le_sup hS3 (le_trans (inf_le_left : X ⊓ N ≤ X) hXY) hsup
  have hfix : Y.map (MulAut.conj s).toMonoidHom ≤
      CFSG.GH74.GLS.oPrimeResidualOf 3 (Y.map (MulAut.conj s).toMonoidHom) := by
    rw [Subgroup.map_le_iff_le_comap]
    refine hY3.le.trans ?_
    rw [CFSG.RankThree.PartTwo.Sec14.oPrimeResidualOf_eq_closure 3 Y, Subgroup.closure_le]
    rintro x ⟨hx, k, hk⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap,
      CFSG.RankThree.PartTwo.Sec14.oPrimeResidualOf_eq_closure 3 (Y.map (MulAut.conj s).toMonoidHom)]
    apply Subgroup.subset_closure
    exact ⟨Subgroup.mem_map_of_mem _ hx, k, by rw [← map_pow, hk, map_one]⟩
  have hle : Y.map (MulAut.conj s).toMonoidHom ≤ Y := hfix.trans hO
  have hcard : Nat.card Y ≤ Nat.card (Y.map (MulAut.conj s).toMonoidHom) :=
    (Subgroup.card_map_of_injective (f := (MulAut.conj s).toMonoidHom)
      (MulAut.conj s).injective).ge
  exact Subgroup.eq_of_le_of_card_ge hle hcard

end ObsStep1b

section ObsE81

private lemma commute_of_commutator_eq_bot {G : Type*} [Group G] {H₁ H₂ : Subgroup G}
    (h : ⁅H₁, H₂⁆ = ⊥) {g k : G} (hg : g ∈ H₁) (hk : k ∈ H₂) : Commute g k := by
  have h1 : g ∈ Subgroup.centralizer (H₂ : Set G) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) hg
  exact (Subgroup.mem_centralizer_iff.mp h1 k hk).symm

theorem card_closure_eq_eightyOne {Q : Type*} [Group Q] [Finite Q] (K : Fin 4 → Subgroup Q)
    (hcomm : ∀ i j, i ≠ j → ⁅K i, K j⁆ = ⊥) (x : Fin 4 → Q) (hxK : ∀ i, x i ∈ K i)
    (hx3 : ∀ i, orderOf (x i) = 3)
    (hxZ : ∀ i, x i ∉ Subgroup.centralizer ((K i : Subgroup Q) : Set Q)) :
    Nat.card (Subgroup.closure (Set.range x)) = 81 ∧
      (∀ e ∈ Subgroup.closure (Set.range x), e ^ 3 = 1) ∧
      (∀ a ∈ Subgroup.closure (Set.range x), ∀ b ∈ Subgroup.closure (Set.range x),
        a * b = b * a) := by
  have hpowmod : ∀ (i : Fin 4) (n : ℕ), x i ^ (n % 3) = x i ^ n := by
    intro i n
    have h := pow_mod_orderOf (x i) n
    rwa [hx3 i] at h
  obtain ⟨f, hf⟩ : ∃ f : ∀ _ : Fin 4, Multiplicative (ZMod 3) →* Q,
      ∀ (i : Fin 4) (a : Multiplicative (ZMod 3)), f i a = x i ^ (Multiplicative.toAdd a).val :=
    ⟨fun i => MonoidHom.mk' (fun a => x i ^ (Multiplicative.toAdd a).val) (fun a b => by
      show x i ^ (Multiplicative.toAdd (a * b)).val
        = x i ^ (Multiplicative.toAdd a).val * x i ^ (Multiplicative.toAdd b).val
      rw [toAdd_mul, ZMod.val_add, hpowmod i, pow_add]), fun _ _ => rfl⟩
  have hfK : ∀ (i : Fin 4) (a : Multiplicative (ZMod 3)), f i a ∈ K i := by
    intro i a
    rw [hf]
    exact Subgroup.pow_mem _ (hxK i) _
  have hfcomm : Pairwise fun i j : Fin 4 =>
      ∀ a b : Multiplicative (ZMod 3), Commute (f i a) (f j b) := by
    intro i j hij a b
    exact commute_of_commutator_eq_bot (hcomm i j hij) (hfK i a) (hfK j b)
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : (Fin 4 → Multiplicative (ZMod 3)) →* Q,
      ∀ (i : Fin 4) (a : Multiplicative (ZMod 3)), Φ (Pi.mulSingle i a) = f i a :=
    ⟨MonoidHom.noncommPiCoprod f hfcomm, fun i a => by simp⟩
  have hxmem : ∀ i, x i ∈ Subgroup.closure (Set.range x) :=
    fun i => Subgroup.subset_closure ⟨i, rfl⟩
  have hfmem : ∀ (i : Fin 4) (a : Multiplicative (ZMod 3)),
      f i a ∈ Subgroup.closure (Set.range x) := by
    intro i a
    rw [hf]
    exact Subgroup.pow_mem _ (hxmem i) _
  have hprod : ∀ (S : Subgroup Q) (s : Finset (Fin 4)) (d : Fin 4 → Multiplicative (ZMod 3)),
      (∀ i ∈ s, f i (d i) ∈ S) → Φ (∏ i ∈ s, Pi.mulSingle i (d i)) ∈ S := by
    intro S s d hs
    refine Finset.prod_induction (fun i => Pi.mulSingle i (d i)) (fun y => Φ y ∈ S)
      (fun a b ha hb => ?_) ?_ (fun i hi => ?_)
    · show Φ (a * b) ∈ S
      rw [map_mul]
      exact S.mul_mem ha hb
    · show Φ 1 ∈ S
      rw [map_one]
      exact S.one_mem
    · show Φ (Pi.mulSingle i (d i)) ∈ S
      rw [hΦ]
      exact hs i hi
  have hsub : ∀ d, Φ d ∈ Subgroup.closure (Set.range x) := by
    intro d
    have key := hprod (Subgroup.closure (Set.range x)) Finset.univ d (fun i _ => hfmem i (d i))
    rwa [Finset.univ_prod_mulSingle] at key
  have hrange : Φ.range = Subgroup.closure (Set.range x) := by
    apply le_antisymm
    · intro y hy
      obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp hy
      exact hsub d
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      refine MonoidHom.mem_range.mpr ⟨Pi.mulSingle i (Multiplicative.ofAdd 1), ?_⟩
      rw [hΦ, hf]
      show x i ^ (1 : ZMod 3).val = x i
      rw [show (1 : ZMod 3).val = 1 from rfl, pow_one]
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_one]
    intro e he
    by_contra hne
    obtain ⟨j, hj⟩ : ∃ j, e j ≠ 1 := by
      by_contra h
      exact hne (funext fun j => Classical.byContradiction fun hj => h ⟨j, hj⟩)
    have hsplit : e = Pi.mulSingle j (e j) * ∏ i ∈ Finset.univ.erase j, Pi.mulSingle i (e i) := by
      conv_lhs => rw [← Finset.univ_prod_mulSingle e]
      exact (Finset.mul_prod_erase Finset.univ (fun i => Pi.mulSingle i (e i))
        (Finset.mem_univ j)).symm
    have hfZ : ∀ (i : Fin 4) (a : Multiplicative (ZMod 3)), i ≠ j →
        f i a ∈ Subgroup.centralizer ((K j : Subgroup Q) : Set Q) := by
      intro i a hij
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact (commute_of_commutator_eq_bot (hcomm i j hij) (hfK i a) hk).symm.eq
    have hw := hprod (Subgroup.centralizer ((K j : Subgroup Q) : Set Q)) (Finset.univ.erase j) e
      (fun i hi => hfZ i (e i) (Finset.ne_of_mem_erase hi))
    have hfj : f j (e j) ∈ Subgroup.centralizer ((K j : Subgroup Q) : Set Q) := by
      have h1 : Φ (Pi.mulSingle j (e j) * ∏ i ∈ Finset.univ.erase j, Pi.mulSingle i (e i))
          = 1 := by
        rw [← hsplit]
        exact he
      rw [map_mul, hΦ] at h1
      rw [eq_inv_of_mul_eq_one_left h1]
      exact Subgroup.inv_mem _ hw
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (Multiplicative.toAdd (e j)).val = m := ⟨_, rfl⟩
    have hm3 : m < 3 := by
      rw [← hm]
      exact ZMod.val_lt _
    have hm0 : m ≠ 0 := by
      rw [← hm]
      intro h0
      apply hj
      exact toAdd_eq_zero.mp ((ZMod.val_eq_zero _).mp h0)
    have hmm : m * m % 3 = 1 := by
      interval_cases m <;> omega
    have hfm : f j (e j) = x j ^ m := by
      rw [hf, hm]
    have hxj : x j = f j (e j) ^ m := by
      rw [hfm, ← pow_mul, ← hpowmod j (m * m), hmm, pow_one]
    apply hxZ j
    rw [hxj]
    exact Subgroup.pow_mem _ hfj m
  have hcube : ∀ a : Multiplicative (ZMod 3), a ^ 3 = 1 := by
    intro a
    have h := pow_card_eq_one (x := a)
    rwa [Fintype.card_multiplicative, ZMod.card] at h
  have hcard : Nat.card (Subgroup.closure (Set.range x)) =
      Nat.card (Fin 4 → Multiplicative (ZMod 3)) := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have h3 : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hdom : Nat.card (Fin 4 → Multiplicative (ZMod 3)) = 81 := by
    rw [Nat.card_fun, h3]
    simp
  refine ⟨by rw [hcard, hdom], ?_, ?_⟩
  · intro e he
    rw [← hrange] at he
    obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp he
    have hd3 : d ^ 3 = 1 := by
      funext i
      rw [Pi.pow_apply, Pi.one_apply]
      exact hcube (d i)
    rw [← map_pow, hd3, map_one]
  · intro a ha b hb
    rw [← hrange] at ha hb
    obtain ⟨d, rfl⟩ := MonoidHom.mem_range.mp ha
    obtain ⟨d', rfl⟩ := MonoidHom.mem_range.mp hb
    rw [← map_mul, ← map_mul, mul_comm d d']

end ObsE81

section ObsLiftE

theorem exists_elemAbelian_lift {M : Type*} [Group M] [Finite M] (N X : Subgroup M) [N.Normal]
    (hN : (Nat.card N).Coprime 3) (E : Subgroup (M ⧸ N)) (hEX : E ≤ X.map (QuotientGroup.mk' N))
    (hE3 : ∀ e ∈ E, e ^ 3 = 1) (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) :
    ∃ F : Subgroup M, F ≤ X ∧ (∀ f ∈ F, f ^ 3 = 1) ∧ (∀ a ∈ F, ∀ b ∈ F, a * b = b * a) ∧
      Nat.card F = Nat.card E := by
  obtain ⟨E', hE'⟩ : ∃ E' : Subgroup M, E' = X ⊓ E.comap (QuotientGroup.mk' N) := ⟨_, rfl⟩
  have hmemE' : ∀ x, x ∈ E' ↔ x ∈ X ∧ QuotientGroup.mk' N x ∈ E := by
    intro x
    rw [hE', Subgroup.mem_inf, Subgroup.mem_comap]
  have hmapE' : E'.map (QuotientGroup.mk' N) = E := by
    ext e
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ((hmemE' x).1 hx).2
    · intro he
      obtain ⟨x, hxX, hxe⟩ := Subgroup.mem_map.1 (hEX he)
      exact ⟨x, (hmemE' x).2 ⟨hxX, by rw [hxe]; exact he⟩, hxe⟩
  have hEp : IsPGroup 3 ↥E := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using hE3 g.1 g.2)⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hEp
  have hdvd : 3 ^ a ∣ Nat.card E' := by
    rw [← ha]
    have h := Subgroup.card_map_dvd (H := E') (QuotientGroup.mk' N)
    rwa [hmapE'] at h
  obtain ⟨F, hFle, hFcard⟩ : ∃ F : Subgroup M, F ≤ E' ∧ Nat.card F = 3 ^ a := by
    obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥E') 3 hdvd
    refine ⟨P.map E'.subtype, ?_, ?_⟩
    · rintro _ ⟨y, _, rfl⟩
      exact y.2
    · rw [Subgroup.card_map_of_injective E'.subtype_injective]
      exact hP
  have hFN : F ⊓ N = ⊥ := by
    apply Subgroup.inf_eq_bot_of_coprime
    rw [hFcard]
    exact Nat.Coprime.pow_left a hN.symm
  have hker : ∀ x ∈ F, QuotientGroup.mk' N x = 1 → x = 1 := by
    intro x hx hx1
    have hxN : x ∈ N := (QuotientGroup.eq_one_iff (N := N) x).1 hx1
    have hxb : x ∈ F ⊓ N := Subgroup.mem_inf.2 ⟨hx, hxN⟩
    rw [hFN] at hxb
    exact Subgroup.mem_bot.1 hxb
  have hmemE : ∀ x ∈ F, QuotientGroup.mk' N x ∈ E := fun x hx => ((hmemE' x).1 (hFle hx)).2
  have hFX : F ≤ X := fun x hx => ((hmemE' x).1 (hFle hx)).1
  refine ⟨F, hFX, ?_, ?_, hFcard.trans ha.symm⟩
  · intro f hf
    apply hker (f ^ 3) (F.pow_mem hf 3)
    rw [map_pow]
    exact hE3 _ (hmemE f hf)
  · intro a' ha' b hb
    have h1 : (a' * b)⁻¹ * (b * a') ∈ F :=
      F.mul_mem (F.inv_mem (F.mul_mem ha' hb)) (F.mul_mem hb ha')
    have h2 : (a' * b)⁻¹ * (b * a') = 1 := by
      apply hker _ h1
      simp only [map_mul, map_inv]
      rw [hEc _ (hmemE a' ha') _ (hmemE b hb)]
      exact inv_mul_cancel _
    exact inv_mul_eq_one.1 h2

end ObsLiftE

section ObsAsm

open Subgroup

variable {M : Type*} [Group M] [Finite M]

@[expose] def QSLike {Q : Type*} [Group Q] (K : Subgroup Q) : Prop :=
  ⁅K, K⁆ = K ∧ ∀ H : Subgroup Q, H ≤ K → (H.subgroupOf K).Normal →
    H = K ∨ H ≤ Subgroup.centralizer (K : Set Q)



theorem map_conj_map_mk (N Y : Subgroup M) [N.Normal] (s : M) :
    (Y.map (MulAut.conj s).toMonoidHom).map (QuotientGroup.mk' N) =
      (Y.map (QuotientGroup.mk' N)).map (MulAut.conj (QuotientGroup.mk' N s)).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem le_normalizer_conj (X Y : Subgroup M) [X.Normal]
    (hXY : X ≤ Subgroup.normalizer (Y : Set M)) (s : M) :
    X ≤ Subgroup.normalizer ((Y.map (MulAut.conj s).toMonoidHom : Subgroup M) : Set M) := by
  intro x hx
  have hx' : s⁻¹ * x * s ∈ X := by
    have := ‹X.Normal›.conj_mem x hx s⁻¹
    simpa [mul_assoc] using this
  have hN := hXY hx'
  rw [Subgroup.mem_normalizer_iff] at hN ⊢
  intro h
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨(s⁻¹ * x * s) * y * (s⁻¹ * x * s)⁻¹, (hN y).mp hy, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]
  · rintro ⟨y, hy, hyeq⟩
    refine ⟨(s⁻¹ * x * s)⁻¹ * y * (s⁻¹ * x * s), ?_, ?_⟩
    · have := (hN ((s⁻¹ * x * s)⁻¹ * y * (s⁻¹ * x * s))).mpr (by simpa [mul_assoc] using hy)
      exact this
    · have h2 : x * h * x⁻¹ = s * y * s⁻¹ := by simpa [MulAut.conj_apply] using hyeq.symm
      have : h = x⁻¹ * (s * y * s⁻¹) * x := by rw [← h2]; group
      rw [this]; simp [MulAut.conj_apply]; group

theorem normal_map_of_le_normalizer (N X Y : Subgroup M) [N.Normal] (hYX : Y ≤ X)
    (hXY : X ≤ Subgroup.normalizer (Y : Set M)) :
    ((Y.map (QuotientGroup.mk' N)).subgroupOf (X.map (QuotientGroup.mk' N))).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hYX)]
  rintro h k ⟨y, hy, rfl⟩ ⟨x, hx, rfl⟩
  exact ⟨x * y * x⁻¹, ((Subgroup.mem_normalizer_iff.mp (hXY hx)) y).mp hy, by simp⟩

theorem card_map_conj {Q : Type*} [Group Q] (K : Subgroup Q) (g : Q) :
    Nat.card (K.map (MulAut.conj g).toMonoidHom) = Nat.card K :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem commute_of_conj_ne (N X Y : Subgroup M) [N.Normal] (hN : (Nat.card N).Coprime 3)
    [X.Normal] (hYX : Y ≤ X) (hXY : X ≤ Subgroup.normalizer (Y : Set M))
    (hY3 : Y = CFSG.GH74.GLS.oPrimeResidualOf 3 Y)
    (hK : QSLike (Y.map (QuotientGroup.mk' N))) (s : M)
    (hs : Y.map (MulAut.conj s).toMonoidHom ≠ Y) :
    ⁅Y.map (QuotientGroup.mk' N), (Y.map (MulAut.conj s).toMonoidHom).map (QuotientGroup.mk' N)⁆ = ⊥ := by
  set π := QuotientGroup.mk' N
  have hYsX : Y.map (MulAut.conj s).toMonoidHom ≤ X := by
    rintro _ ⟨y, hy, rfl⟩
    exact ‹X.Normal›.conj_mem y (hYX hy) s
  have hXYs := le_normalizer_conj X Y hXY s
  refine commute_of_normal_quasisimple (X.map π) _ _
    (normal_map_of_le_normalizer N X Y hYX hXY)
    (normal_map_of_le_normalizer N X _ hYsX hXYs)
    (Subgroup.map_mono hYX) (Subgroup.map_mono hYsX) hK.1 hK.2 ?_
  intro hle
  apply hs
  apply conj_eq_of_image_eq N X Y hN hYX hXY hY3 s
  symm
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [map_conj_map_mk, card_map_conj]

theorem conj_eq_of_mem_centralizer (N X Y A : Subgroup M) [N.Normal] (hN : (Nat.card N).Coprime 3)
    [X.Normal] (hYX : Y ≤ X) (hXY : X ≤ Subgroup.normalizer (Y : Set M))
    (hY3 : Y = CFSG.GH74.GLS.oPrimeResidualOf 3 Y)
    (hK : QSLike (Y.map (QuotientGroup.mk' N)))
    (y : M) (hyA : y ∈ A) (hyK : QuotientGroup.mk' N y ∈ Y.map (QuotientGroup.mk' N))
    (hyZ : QuotientGroup.mk' N y ∉
      Subgroup.centralizer ((Y.map (QuotientGroup.mk' N) : Subgroup (M ⧸ N)) : Set (M ⧸ N)))
    (g : M) (hg : g ∈ Subgroup.centralizer (A : Set M)) :
    Y.map (MulAut.conj g).toMonoidHom = Y := by
  by_contra hne
  set π := QuotientGroup.mk' N
  have hc := commute_of_conj_ne N X Y hN hYX hXY hY3 hK g hne
  apply hyZ
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hkg : π g * k * (π g)⁻¹ ∈ (Y.map (MulAut.conj g).toMonoidHom).map π := by
    rw [map_conj_map_mk]
    exact ⟨k, hk, by simp [MulAut.conj_apply]; rfl⟩
  have hcomm : π y * (π g * k * (π g)⁻¹) = (π g * k * (π g)⁻¹) * π y := by
    have hyc := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc) hyK
    exact ((Subgroup.mem_centralizer_iff.mp hyc) _ hkg).symm
  have hgy : π g * π y = π y * π g := by
    have : g * y = y * g := (Subgroup.mem_centralizer_iff.mp hg y hyA).symm
    simpa [map_mul] using congrArg π this
  have : π y * k = k * π y := by
    have h1 : π g * (π y * k) * (π g)⁻¹ = π g * (k * π y) * (π g)⁻¹ := by
      calc π g * (π y * k) * (π g)⁻¹ = π y * (π g * k * (π g)⁻¹) := by
            rw [← mul_assoc, hgy]; group
        _ = (π g * k * (π g)⁻¹) * π y := hcomm
        _ = π g * (k * π y) * (π g)⁻¹ := by
            rw [show (π g * k * (π g)⁻¹) * π y = π g * k * (π g)⁻¹ * π y by rfl]
            have hgy' : (π g)⁻¹ * π y = π y * (π g)⁻¹ := by
              rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hgy, mul_assoc, mul_inv_cancel, mul_one]
            rw [mul_assoc (π g * k), hgy']; group
    simpa using h1
  exact this.symm

theorem map_conj_map_conj (Y : Subgroup M) (a b : M) :
    (Y.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      Y.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

theorem false_of_four_conj (N X Y : Subgroup M) [N.Normal] (hN : (Nat.card N).Coprime 3)
    [X.Normal] (hYX : Y ≤ X) (hXY : X ≤ Subgroup.normalizer (Y : Set M))
    (hY3 : Y = CFSG.GH74.GLS.oPrimeResidualOf 3 Y)
    (hK : QSLike (Y.map (QuotientGroup.mk' N)))
    (x : M ⧸ N) (hxK : x ∈ Y.map (QuotientGroup.mk' N)) (hx3 : orderOf x = 3)
    (hxZ : x ∉
      Subgroup.centralizer ((Y.map (QuotientGroup.mk' N) : Subgroup (M ⧸ N)) : Set (M ⧸ N)))
    (h3 : ∀ E : Subgroup M, E ≤ X → (∀ e ∈ E, e ^ 3 = 1) → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      Nat.card E ≤ 27)
    (s : Fin 4 → M) (hs : Function.Injective fun i => Y.map (MulAut.conj (s i)).toMonoidHom) :
    False := by
  set π := QuotientGroup.mk' N
  set K := Y.map π with hKdef
  let c : Fin 4 → MulAut (M ⧸ N) := fun i => MulAut.conj (π (s i))
  let Ki : Fin 4 → Subgroup (M ⧸ N) := fun i => (Y.map (MulAut.conj (s i)).toMonoidHom).map π
  have hKi : ∀ i, Ki i = K.map (c i).toMonoidHom := fun i => map_conj_map_mk N Y (s i)
  let xi : Fin 4 → M ⧸ N := fun i => c i x
  have hxiK : ∀ i, xi i ∈ Ki i := fun i => by rw [hKi]; exact ⟨x, hxK, rfl⟩
  have hxi3 : ∀ i, orderOf (xi i) = 3 := fun i => by
    rw [← hx3]
    exact orderOf_injective (c i).toMonoidHom (c i).injective x
  have hxiZ : ∀ i, xi i ∉ Subgroup.centralizer ((Ki i : Subgroup (M ⧸ N)) : Set (M ⧸ N)) := by
    intro i hmem
    apply hxZ
    rw [Subgroup.mem_centralizer_iff] at hmem ⊢
    intro k hk
    have hk' : c i k ∈ Ki i := by rw [hKi]; exact ⟨k, hk, rfl⟩
    have := hmem _ hk'
    apply (c i).injective
    simpa [xi, map_mul] using this
  have hcomm : ∀ i j, i ≠ j → ⁅Ki i, Ki j⁆ = ⊥ := by
    intro i j hij
    have hne : Y.map (MulAut.conj ((s i)⁻¹ * s j)).toMonoidHom ≠ Y := by
      intro heq
      apply hij
      apply hs
      show Y.map (MulAut.conj (s i)).toMonoidHom = Y.map (MulAut.conj (s j)).toMonoidHom
      calc Y.map (MulAut.conj (s i)).toMonoidHom
          = (Y.map (MulAut.conj ((s i)⁻¹ * s j)).toMonoidHom).map (MulAut.conj (s i)).toMonoidHom := by
            rw [heq]
        _ = Y.map (MulAut.conj (s j)).toMonoidHom := by
            rw [map_conj_map_conj, mul_inv_cancel_left]
    have h := commute_of_conj_ne N X Y hN hYX hXY hY3 hK ((s i)⁻¹ * s j) hne
    have h2 := congrArg (Subgroup.map (c i).toMonoidHom) h
    rw [Subgroup.map_commutator, Subgroup.map_bot] at h2
    rw [hKi i, ← h2]
    congr 1
    rw [map_conj_map_mk, Subgroup.map_map]
    show (Y.map (MulAut.conj (s j)).toMonoidHom).map π = _
    rw [map_conj_map_mk]
    congr 1
    ext z
    simp [c, π, MulAut.conj_apply, mul_assoc]
  obtain ⟨hcard, hexp, hab⟩ :=
    card_closure_eq_eightyOne Ki hcomm xi hxiK hxi3 hxiZ
  have hEX : Subgroup.closure (Set.range xi) ≤ X.map π := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    have hYsX : Y.map (MulAut.conj (s i)).toMonoidHom ≤ X := by
      rintro _ ⟨y, hy, rfl⟩
      exact ‹X.Normal›.conj_mem y (hYX hy) (s i)
    exact Subgroup.map_mono hYsX (hxiK i)
  obtain ⟨F, hFX, hF3, hFc, hFcard⟩ := exists_elemAbelian_lift N X hN _ hEX hexp hab
  have := h3 F hFX hF3 hFc
  omega

theorem mem_normalizer_of_map_conj_eq {Y : Subgroup M} {g : M}
    (h : Y.map (MulAut.conj g).toMonoidHom = Y) : g ∈ Subgroup.normalizer (Y : Set M) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    rw [← h]
    exact ⟨z, hz, rfl⟩
  · intro hz
    rw [← h] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    have : w = z := by
      have := (MulAut.conj g).injective (a₁ := w) (a₂ := z)
      apply this
      simpa [MulAut.conj_apply] using hwz
    exact this ▸ hw

theorem map_conj_eq_iff_mem {Y : Subgroup M} (a b : M) :
    Y.map (MulAut.conj a).toMonoidHom = Y.map (MulAut.conj b).toMonoidHom ↔
      b⁻¹ * a ∈ Subgroup.normalizer (Y : Set M) := by
  constructor
  · intro h
    apply mem_normalizer_of_map_conj_eq
    rw [← map_conj_map_conj, h, map_conj_map_conj, inv_mul_cancel]
    ext z; simp [MulAut.conj_apply]
  · intro h
    have hY : Y.map (MulAut.conj (b⁻¹ * a)).toMonoidHom = Y := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ((Subgroup.mem_normalizer_iff.mp h) w).mp hw
      · intro hz
        refine ⟨(b⁻¹ * a)⁻¹ * z * (b⁻¹ * a), ?_, by simp [MulAut.conj_apply, mul_assoc]⟩
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ h)) z
        simpa [mul_assoc] using this.mp hz
    calc Y.map (MulAut.conj a).toMonoidHom
        = (Y.map (MulAut.conj (b⁻¹ * a)).toMonoidHom).map (MulAut.conj b).toMonoidHom := by
          rw [map_conj_map_conj, mul_inv_cancel_left]
      _ = Y.map (MulAut.conj b).toMonoidHom := by rw [hY]

theorem normalizes_of_coprime_invariant (N X Y A R : Subgroup M) [N.Normal]
    (hN : (Nat.card N).Coprime 3) [X.Normal] (hYX : Y ≤ X)
    (hXY : X ≤ Subgroup.normalizer (Y : Set M))
    (hY3 : Y = CFSG.GH74.GLS.oPrimeResidualOf 3 Y)
    (hK : QSLike (Y.map (QuotientGroup.mk' N)))
    (hA : ∀ a ∈ A, a ^ 3 = 1) (hAY : A ≤ Subgroup.normalizer (Y : Set M))
    (y : M) (hyA : y ∈ A) (hyK : QuotientGroup.mk' N y ∈ Y.map (QuotientGroup.mk' N))
    (hyZ : QuotientGroup.mk' N y ∉
      Subgroup.centralizer ((Y.map (QuotientGroup.mk' N) : Subgroup (M ⧸ N)) : Set (M ⧸ N)))
    (h3 : ∀ E : Subgroup M, E ≤ X → (∀ e ∈ E, e ^ 3 = 1) → (∀ a ∈ E, ∀ b ∈ E, a * b = b * a) →
      Nat.card E ≤ 27)
    (hR : (Nat.card R).Coprime 3) (hAR : A ≤ Subgroup.normalizer (R : Set M)) :
    R ≤ Subgroup.normalizer (Y : Set M) := by
  classical
  set π := QuotientGroup.mk' N
  set R₀ : Subgroup M := R ⊓ Subgroup.normalizer (Y : Set M) with hR₀
  have hy3 : orderOf (π y) = 3 := by
    have hne : π y ≠ 1 := by
      intro h1; apply hyZ; rw [h1]; exact Subgroup.one_mem _
    have hpow : π y ^ 3 = 1 := by rw [← map_pow, hA y hyA, map_one]
    exact orderOf_eq_prime hpow hne
  have hle3 : R₀.relIndex R ≤ 3 := by
    by_contra hgt
    push Not at hgt
    set Q := ↥R ⧸ R₀.subgroupOf R
    have hcardQ : 4 ≤ Nat.card Q := by
      have hQ : Nat.card Q = R₀.relIndex R := rfl
      omega
    haveI : Fintype Q := Fintype.ofFinite Q
    obtain ⟨f⟩ : Nonempty (Fin 4 ↪ Q) :=
      Function.Embedding.nonempty_of_card_le (by simpa [Nat.card_eq_fintype_card] using hcardQ)
    let s : Fin 4 → M := fun i => ((f i).out : R)
    apply false_of_four_conj N X Y hN hYX hXY hY3 hK (π y) hyK hy3 hyZ h3 s
    intro i j hij
    simp only at hij
    have hmem := (map_conj_eq_iff_mem (Y := Y) (s i) (s j)).mp hij
    apply f.injective
    rw [← Quotient.out_eq (f i), ← Quotient.out_eq (f j)]
    apply Quotient.sound
    show (QuotientGroup.leftRel _).r _ _
    rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (((f i).out)⁻¹ * (f j).out).2
    · have := Subgroup.inv_mem _ hmem
      simpa [s, mul_inv_rev] using this
  have hdvd : R₀.relIndex R ∣ Nat.card R := (R₀.subgroupOf R).index_dvd_card
  have hne3 : R₀.relIndex R ≠ 3 := by
    intro h3'
    rw [h3'] at hdvd
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hR.symm hdvd
  have hne2 : R₀.relIndex R ≠ 2 := by
    intro h2
    have hA3 : IsPGroup 3 A := fun ⟨a, ha⟩ => ⟨1, by rw [pow_one]; exact Subtype.ext (by simpa using hA a ha)⟩
    have hAR₀ : A ≤ Subgroup.normalizer (R₀ : Set M) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro z
      have hRa := (Subgroup.mem_normalizer_iff.mp (hAR ha)) z
      have hYa : z ∈ Subgroup.normalizer (Y : Set M) ↔
          a * z * a⁻¹ ∈ Subgroup.normalizer (Y : Set M) := by
        have haN : a ∈ Subgroup.normalizer (Y : Set M) := hAY ha
        constructor
        · intro hz; exact Subgroup.mul_mem _ (Subgroup.mul_mem _ haN hz) (Subgroup.inv_mem _ haN)
        · intro hz
          have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ haN) hz) haN
          simpa [mul_assoc] using this
      simp only [hR₀, Subgroup.mem_inf]
      exact ⟨fun ⟨h1, h2⟩ => ⟨hRa.mp h1, hYa.mp h2⟩, fun ⟨h1, h2⟩ => ⟨hRa.mpr h1, hYa.mpr h2⟩⟩
    obtain ⟨g, hgR, hgR₀, hgA⟩ :=
      exists_centralizing_not_mem_of_index_two R R₀ A hR hA3 hAR hAR₀
        inf_le_left h2
    apply hgR₀
    refine Subgroup.mem_inf.mpr ⟨hgR, mem_normalizer_of_map_conj_eq ?_⟩
    exact conj_eq_of_mem_centralizer N X Y A hN hYX hXY hY3 hK y hyA hyK hyZ g hgA
  have hpos : R₀.relIndex R ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : R₀.relIndex R = 1 := by omega
  have := Subgroup.relIndex_eq_one.mp h1
  exact fun r hr => (Subgroup.mem_inf.mp (this hr)).2

end ObsAsm

end CFSG.RankThree.PartTwo.Sec15.F153Obs
