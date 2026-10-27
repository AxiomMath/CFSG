module

public import CFSG.Sporadic.Th.Recog.CentralLayer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Sporadic.Th.Recog

open CFSG
open CFSG.Sporadic.Th.Max3
open CFSG.Sporadic.Th.Max3.InvRep
open CFSG.RankThree.Literature.FSmith
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem ncard_involutions_le_of_lt {H : Type} [Group H] [Finite H]
    {A R : Subgroup H} (hAR : A < R) (hR : Nat.card R = 2 ^ 8) :
    {w : H | w ∈ A ∧ w * w = 1 ∧ w ≠ 1}.ncard ≤ 127 := by
  have hA_lt : Nat.card A < 2 ^ 8 := by
    rw [← hR]
    exact Subgroup.card_lt_of_lt hAR
  have hR_2 : IsPGroup 2 R := IsPGroup.of_card (p := 2) (n := 8) hR
  have hA_2 : IsPGroup 2 A := hR_2.to_le hAR.le
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_eq (p := 2) hA_2
  have hn8 : n < 8 := by
    rw [hn] at hA_lt
    exact (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hA_lt
  have hA_le : Nat.card A ≤ 2 ^ 7 := by
    rw [hn]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hsub : {w : H | w ∈ A ∧ w * w = 1 ∧ w ≠ 1} ⊆
      ((A : Set H) \ {1}) := by
    intro w hw
    exact ⟨hw.1, hw.2.2⟩
  have hcard : ((A : Set H) \ {1}).ncard = Nat.card A - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _)]
    rfl
  calc {w : H | w ∈ A ∧ w * w = 1 ∧ w ≠ 1}.ncard
      ≤ ((A : Set H) \ {1}).ncard := Set.ncard_le_ncard hsub
    _ = Nat.card A - 1 := hcard
    _ ≤ 2 ^ 7 - 1 := by omega
    _ = 127 := by norm_num

namespace ThSetting

theorem exists_isSylow_le_H (S : ThSetting G) :
    ∃ T : Sylow 2 G, (T : Subgroup G) ≤ S.H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2H : IsPGroup 2 (S.Q.subgroupOf S.H) :=
    S.ext.1.of_equiv (Subgroup.subgroupOfEquivOfLe S.Q_le_H).symm
  haveI hQnorm : (S.Q.subgroupOf S.H).Normal := S.Q_normal
  obtain ⟨T_H, hQT_H⟩ := IsPGroup.exists_le_sylow (p := 2) hQ2H
  let T : Subgroup G := (T_H : Subgroup S.H).map S.H.subtype
  have hT2 : IsPGroup 2 T := (T_H.isPGroup').map S.H.subtype
  have hTleH : T ≤ S.H := Subgroup.map_subtype_le _
  have hQleT : S.Q ≤ T := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, S.Q_le_H hx⟩, hQT_H (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hcenter_le : Subgroup.center T ≤
      Subgroup.zpowers (⟨S.z, hQleT S.z_mem_Q⟩ : T) := by
    intro x hx
    have hxH : (x : G) ∈ S.H := hTleH x.2
    have hxcent : (x : G) ∈ Subgroup.centralizer (S.Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hx ⟨y, hQleT hy⟩)
    have hxQ : (x : G) ∈ S.Q :=
      S.centralizer_Q_le (Subgroup.mem_inf.mpr ⟨hxcent, hxH⟩)
    let xH : S.H := ⟨(x : G), hxH⟩
    have hxQH : xH ∈ S.toSetting.Q := by
      rw [S.toSetting_Q_eq]
      exact Subgroup.mem_subgroupOf.mpr hxQ
    have hxcenterQ : (⟨xH, hxQH⟩ : S.toSetting.Q) ∈
        Subgroup.center S.toSetting.Q := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      apply Subtype.ext
      have hyQ : ((y : S.toSetting.M) : G) ∈ S.Q := by
        rw [← S.toSetting_QG]
        exact Subgroup.mem_map.mpr ⟨(y : S.toSetting.M), y.2, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp hxcent ((y : S.toSetting.M) : G) hyQ
    rcases (S.toSetting.mem_center_Q_iff).mp hxcenterQ with h1 | hz
    · have hx1 : (x : G) = 1 := congrArg Subtype.val (congrArg Subtype.val h1)
      refine ⟨0, ?_⟩
      apply Subtype.ext
      simp [hx1]
    · have hxz : (x : G) = S.z :=
        congrArg Subtype.val (congrArg Subtype.val hz)
      refine ⟨1, ?_⟩
      apply Subtype.ext
      simp [hxz]
  have hzT_center :
      (⟨S.z, hQleT S.z_mem_Q⟩ : T) ∈ Subgroup.center T := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (hTleH y.2)
  have hnormalizer_le_H : Subgroup.normalizer (T : Set G) ≤ S.H := by
    intro x hxN
    have hxT : ∀ y : G, y ∈ T ↔ x * y * x⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp hxN)
    have hxzT : x * S.z * x⁻¹ ∈ T :=
      (hxT S.z).mp (hQleT S.z_mem_Q)
    have hxzx_center :
        (⟨x * S.z * x⁻¹, hxzT⟩ : T) ∈ Subgroup.center T := by
      rw [Subgroup.mem_center_iff]
      intro t
      apply Subtype.ext
      have ht' : x⁻¹ * (t : G) * x ∈ T :=
        (hxT (x⁻¹ * (t : G) * x)).mpr (by simpa [mul_assoc] using t.2)
      have hcomm := Subgroup.mem_center_iff.mp hzT_center
        ⟨x⁻¹ * (t : G) * x, ht'⟩
      have hcomm' : (x⁻¹ * (t : G) * x) * S.z = S.z * (x⁻¹ * (t : G) * x) :=
        congrArg Subtype.val hcomm
      change (t : G) * (x * S.z * x⁻¹) = (x * S.z * x⁻¹) * (t : G)
      calc (t : G) * (x * S.z * x⁻¹)
          = x * ((x⁻¹ * (t : G) * x) * S.z) * x⁻¹ := by group
        _ = x * (S.z * (x⁻¹ * (t : G) * x)) * x⁻¹ := by rw [hcomm']
        _ = (x * S.z * x⁻¹) * (t : G) := by group
    rcases (Subgroup.mem_zpowers_iff.mp (hcenter_le hxzx_center)) with ⟨k, hk⟩
    have hx_ne_one : (⟨x * S.z * x⁻¹, hxzT⟩ : T) ≠ 1 := by
      intro h
      have h' : x * S.z * x⁻¹ = 1 := congrArg Subtype.val h
      have hz1 : S.z = 1 := by
        calc S.z = x⁻¹ * (x * S.z * x⁻¹) * x := by group
          _ = x⁻¹ * 1 * x := by rw [h']
          _ = 1 := by group
      exact S.toSetting.z_ne_one hz1
    have hzpow : (⟨x * S.z * x⁻¹, hxzT⟩ : T) =
        (⟨S.z, hQleT S.z_mem_Q⟩ : T) := by
      have hzT_sq : (⟨S.z, hQleT S.z_mem_Q⟩ : T) ^ 2 = 1 := by
        apply Subtype.ext
        rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]
        exact S.toSetting.z_mul_z
      have hord : orderOf (⟨S.z, hQleT S.z_mem_Q⟩ : T) = 2 :=
        orderOf_eq_prime hzT_sq (by
          intro h
          apply S.toSetting.z_ne_one
          exact congrArg Subtype.val h)
      have hk' : (⟨S.z, hQleT S.z_mem_Q⟩ : T) ^ (k % 2) =
          (⟨x * S.z * x⁻¹, hxzT⟩ : T) := by
        rw [← hk, ← zpow_mod_orderOf (x := (⟨S.z, hQleT S.z_mem_Q⟩ : T)) (z := k),
          hord, show ((2 : ℕ) : ℤ) = 2 from rfl]
      rcases Int.emod_two_eq_zero_or_one k with h | h
      · rw [h, zpow_zero] at hk'
        exact absurd hk'.symm hx_ne_one
      · rw [h, zpow_one] at hk'
        exact hk'.symm
    have hxz : x * S.z * x⁻¹ = S.z := congrArg Subtype.val hzpow
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * S.z = (x * S.z * x⁻¹) * x := by group
      _ = S.z * x := by rw [hxz]
  have hTmax : ∀ P : Subgroup G, IsPGroup 2 P → T ≤ P → P = T := by
    intro P hP hTP
    by_contra hne
    have hlt : T < P := lt_of_le_of_ne hTP (Ne.symm hne)
    let IP : Subgroup P := T.subgroupOf P
    have hIPlt : IP < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      apply hne
      refine le_antisymm ?_ hTP
      intro y hy
      have hyIP : (⟨y, hy⟩ : P) ∈ IP := by rw [htop]; trivial
      have hyT : ((⟨y, hy⟩ : P) : G) ∈ T := Subgroup.mem_subgroupOf.mp hyIP
      simpa using hyT
    haveI : Finite P := Subtype.finite
    have hnil : Group.IsNilpotent P := hP.isNilpotent
    have hnc : NormalizerCondition P := Group.normalizerCondition_of_isNilpotent
    have hgrowth : IP < Subgroup.normalizer (IP : Set P) := hnc IP hIPlt
    obtain ⟨x, hxN, hxnotIP⟩ := SetLike.exists_of_lt hgrowth
    have hxNormT : (x : G) ∈ Subgroup.normalizer (T : Set G) := by
      have hxsub : x ∈ (Subgroup.normalizer (T : Set G)).subgroupOf P := by
        rw [Subgroup.subgroupOf_normalizer_eq hTP]
        exact hxN
      exact Subgroup.mem_subgroupOf.mp hxsub
    have hxH : (x : G) ∈ S.H := hnormalizer_le_H hxNormT
    have hxnotT : (x : G) ∉ T := by
      intro hxT
      apply hxnotIP
      exact Subgroup.mem_subgroupOf.mpr hxT
    let PH : Subgroup S.H := P.subgroupOf S.H
    have hPH2 : IsPGroup 2 PH := hP.comap_subtype
    have hTHlePH : T_H ≤ PH := by
      intro y hy
      exact Subgroup.mem_subgroupOf.mpr
        (hTP (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩))
    have hxPH : (⟨(x : G), hxH⟩ : S.H) ∈ PH :=
      Subgroup.mem_subgroupOf.mpr x.2
    have hxnotTH : (⟨(x : G), hxH⟩ : S.H) ∉ (T_H : Subgroup S.H) := by
      intro hxTH
      exact hxnotT (Subgroup.mem_map.mpr ⟨⟨(x : G), hxH⟩, hxTH, rfl⟩)
    have hPH_eq : PH = (T_H : Subgroup S.H) := T_H.is_maximal' hPH2 hTHlePH
    exact hxnotTH (by simpa [hPH_eq] using hxPH)
  exact ⟨Sylow.mk T hT2 (fun {Q} hQ hle => hTmax Q hQ hle), hTleH⟩

end ThSetting

namespace FibreData

variable {S : ThSetting G}

private theorem map_zM_of_mem_F (Fd : FibreData S) (e : S.toSetting.M ≃* Max3.M)
    (he : ∀ h, (h, e h) ∈ Fd.F) :
    e S.toSetting.zM = (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M) := by
  have hzM1 : S.toSetting.zM ≠ 1 := by
    intro h
    apply S.toSetting.z_ne_one
    rw [← S.toSetting.coe_zM, h]
    rfl
  have hzF : (S.toSetting.zM, (1 : Max3.M)) ∈ Fd.F :=
    (Fd.mk_one_mem_F_iff S.toSetting.zM).mpr (Or.inr S.toSetting.coe_zM)
  have h1F : ((1 : S.toSetting.M), e S.toSetting.zM) ∈ Fd.F := by
    have h := Fd.F.mul_mem (he S.toSetting.zM) (Fd.F.inv_mem hzF)
    simpa using h
  rcases (Fd.one_mk_mem_F_iff (e S.toSetting.zM)).mp h1F with h1 | h1
  · exact absurd (e.injective (by rw [h1, map_one])) hzM1
  · exact Subtype.ext h1

private theorem q0_ne_z : Max3.q 0 ≠ Max3.z := by
  intro h
  have hq := Max3.q_mul_q 0 1
  rw [h] at hq
  have hc : (Max3.c 0 1).val = 1 := rfl
  rw [hc, pow_one] at hq
  have hzq : Max3.z * Max3.q 1 = Max3.q 1 * Max3.z := Max3.z_mul_q 1
  rw [hzq] at hq
  have hz1 : Max3.z = 1 := by
    have h' : (Max3.q 1 * Max3.z)⁻¹ * (Max3.q 1 * Max3.z) =
        (Max3.q 1 * Max3.z)⁻¹ * ((Max3.q 1 * Max3.z) * Max3.z) :=
      congrArg (fun x => (Max3.q 1 * Max3.z)⁻¹ * x) hq
    rw [inv_mul_cancel, inv_mul_cancel_left] at h'
    exact h'.symm
  exact Max3.z_ne_one hz1

private theorem exists_conj_q0_of_mem_Q {m : Max3.M}
    (hmQ : (m : J) ∈ Max3.Q) (hm2 : m * m = 1) (hm1 : m ≠ 1)
    (hmz : m ≠ (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M)) :
    ∃ g : Max3.M,
      g * m * g⁻¹ = (⟨Max3.q 0, Max3.Q_le_M (Max3.q_mem_Q 0)⟩ : Max3.M) := by
  have hm2' : (m : J) * (m : J) = 1 := by
    rw [← Subgroup.coe_mul, hm2, Subgroup.coe_one]
  have hm1' : (m : J) ≠ 1 := fun h => hm1 (Subtype.ext h)
  obtain ⟨g, hgM, hg⟩ := Max3.InvRep.exists_conj_of_mem_Q hmQ hm2' hm1'
  rcases hg with hz | hq
  · exfalso
    apply hmz
    have hgz : g * (m : J) * g⁻¹ = Max3.z := hz
    have hzcomm : g * Max3.z = Max3.z * g :=
      (Max3.commute_z_of_mem_M hgM).symm
    have hm_eq : (m : J) = Max3.z := by
      calc (m : J) = g⁻¹ * (g * (m : J) * g⁻¹) * g := by group
        _ = g⁻¹ * Max3.z * g := by rw [hgz]
        _ = Max3.z := by
          calc g⁻¹ * Max3.z * g = g⁻¹ * (Max3.z * g) := by group
            _ = g⁻¹ * (g * Max3.z) := by rw [hzcomm]
            _ = Max3.z := by group
    exact Subtype.ext hm_eq
  · refine ⟨⟨g, hgM⟩, ?_⟩
    apply Subtype.ext
    exact hq

theorem mem_Q_iff_of_mulEquiv (Fd : FibreData S) (e : S.toSetting.M ≃* Max3.M)
    (he : ∀ h, (h, e h) ∈ Fd.F) (h : S.toSetting.M) :
    h ∈ S.toSetting.Q ↔ ((e h : Max3.M) : J) ∈ Max3.Q := by
  have hk : Max3.InvRep.kap (e h) = Fd.θ h :=
    ((Fd.mem_F_iff h (e h)).mp (he h)).1
  constructor
  · intro hh
    rw [← Max3.InvRep.kap_eq_one_iff, hk, ← MonoidHom.mem_ker, Fd.θ_ker]
    exact hh
  · intro hh
    have hk1 : Max3.InvRep.kap (e h) = 1 := Max3.InvRep.kap_eq_one_iff.mpr hh
    have hθ : Fd.θ h = 1 := by rw [← hk, hk1]
    rw [← Fd.θ_ker, MonoidHom.mem_ker]
    exact hθ

private theorem exists_conj_of_mem_Q_involution (Fd : FibreData S)
    (e : S.toSetting.M ≃* Max3.M) (he : ∀ h, (h, e h) ∈ Fd.F)
    {h₁ : S.toSetting.Q}
    (hφh : (((Fd.φQ h₁ : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) = Max3.q 0)
    (hh1H2 : (h₁ : S.toSetting.M) * (h₁ : S.toSetting.M) = 1)
    (hh1_ne_one : (h₁ : S.toSetting.M) ≠ 1)
    (hh1_ne_z : (h₁ : S.toSetting.M) ≠ S.toSetting.zM) :
    ∀ k : S.toSetting.M, k ∈ S.toSetting.Q → k * k = 1 → k ≠ 1 →
      k ≠ S.toSetting.zM →
      ∃ c : S.toSetting.M, c * k * c⁻¹ = (h₁ : S.toSetting.M) := by
  intro k hkQ hk2 hk1 hkz
  let aM : Max3.M := ⟨Max3.z, Max3.z_mem_M⟩
  let q0M : Max3.M := ⟨Max3.q 0, Max3.Q_le_M (Max3.q_mem_Q 0)⟩
  have he_z : e S.toSetting.zM = aM := by
    simpa [aM] using map_zM_of_mem_F Fd e he
  have heh1Q : ((e (h₁ : S.toSetting.M) : Max3.M) : J) ∈ Max3.Q :=
    (mem_Q_iff_of_mulEquiv Fd e he (h₁ : S.toSetting.M)).mp h₁.2
  have heh1_2 : e (h₁ : S.toSetting.M) * e (h₁ : S.toSetting.M) = 1 := by
    rw [← map_mul, hh1H2, map_one]
  have heh1_ne_a : e (h₁ : S.toSetting.M) ≠ aM := by
    intro h
    exact hh1_ne_z (e.injective (by rw [h, he_z]))
  have heh1_ne_one : e (h₁ : S.toSetting.M) ≠ 1 := fun h =>
    hh1_ne_one (e.injective (by rw [h, map_one]))
  have hekQ : ((e k : Max3.M) : J) ∈ Max3.Q :=
    (mem_Q_iff_of_mulEquiv Fd e he k).mp hkQ
  have hek2 : e k * e k = 1 := by rw [← map_mul, hk2, map_one]
  have hek1 : e k ≠ 1 := fun h => hk1 (e.injective (by rw [h, map_one]))
  have hek_ne_a : e k ≠ aM := by
    intro h
    exact hkz (e.injective (by rw [h, he_z]))
  obtain ⟨m₂, hm₂⟩ := exists_conj_q0_of_mem_Q hekQ hek2 hek1 hek_ne_a
  obtain ⟨m₁, hm₁⟩ := exists_conj_q0_of_mem_Q heh1Q heh1_2 heh1_ne_one heh1_ne_a
  refine ⟨e.symm (m₁⁻¹ * m₂), ?_⟩
  apply e.injective
  simp only [map_mul, map_inv, e.apply_symm_apply]
  calc (m₁⁻¹ * m₂) * e k * (m₁⁻¹ * m₂)⁻¹
      = m₁⁻¹ * (m₂ * e k * m₂⁻¹) * m₁ := by group
    _ = m₁⁻¹ * q0M * m₁ := by rw [hm₂]
    _ = m₁⁻¹ * (m₁ * e (h₁ : S.toSetting.M) * m₁⁻¹) * m₁ := by rw [hm₁]
    _ = e (h₁ : S.toSetting.M) := by group

private theorem exists_conj_outside_Q (Fd : FibreData S) (e : S.toSetting.M ≃* Max3.M)
    (he : ∀ h, (h, e h) ∈ Fd.F) :
    ∀ k : S.toSetting.M, k ∉ S.toSetting.Q → k * k = 1 → k ≠ 1 →
      ∃ c : S.toSetting.M, c * k * c⁻¹ =
        e.symm (⟨Max3.x, Max3.x_mem_M⟩ : Max3.M) := by
  intro k hkQ hk2 hk1
  have hekQ : ((e k : Max3.M) : J) ∉ Max3.Q :=
    fun h => hkQ ((mem_Q_iff_of_mulEquiv Fd e he k).mpr h)
  have hek2M : e k * e k = 1 := by rw [← map_mul, hk2, map_one]
  have hek2J : (e k : J) * (e k : J) = 1 := by
    rw [← Subgroup.coe_mul, hek2M, Subgroup.coe_one]
  obtain ⟨m, hmM, hm⟩ :=
    Max3.InvRep.exists_conj_x_of_not_mem_Q (e k).2 hekQ hek2J
  refine ⟨e.symm ⟨m, hmM⟩, ?_⟩
  apply e.injective
  simp only [map_mul, map_inv, e.apply_symm_apply]
  exact Subtype.ext hm

private theorem exists_conj_z_of_mem_Q (Fd : FibreData S) (e : S.toSetting.M ≃* Max3.M)
    (he : ∀ h, (h, e h) ∈ Fd.F) {h₁ : S.toSetting.Q} {g₀ : G}
    (hφh : (((Fd.φQ h₁ : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) = Max3.q 0)
    (hg₀z : g₀ * S.z * g₀⁻¹ = ((h₁ : S.toSetting.M) : G))
    (hh1H2 : (h₁ : S.toSetting.M) * (h₁ : S.toSetting.M) = 1)
    (hh1_ne_one : (h₁ : S.toSetting.M) ≠ 1)
    (hh1_ne_z : (h₁ : S.toSetting.M) ≠ S.toSetting.zM) :
    ∀ k : S.toSetting.M, k ∈ S.toSetting.Q → k * k = 1 → k ≠ 1 →
      ∃ g : G, g * S.z * g⁻¹ = (k : G) := by
  intro k hkQ hk2 hk1
  by_cases hkz : k = S.toSetting.zM
  · subst hkz
    exact ⟨1, by simp [S.toSetting.coe_zM]⟩
  · obtain ⟨c, hc⟩ :=
      exists_conj_of_mem_Q_involution Fd e he hφh hh1H2 hh1_ne_one hh1_ne_z
        k hkQ hk2 hk1 hkz
    refine ⟨(c : G)⁻¹ * g₀, ?_⟩
    calc ((c : G)⁻¹ * g₀) * S.z * ((c : G)⁻¹ * g₀)⁻¹
        = (c : G)⁻¹ * (g₀ * S.z * g₀⁻¹) * c := by group
      _ = (c : G)⁻¹ * ((h₁ : S.toSetting.M) : G) * c := by rw [hg₀z]
      _ = (c : G)⁻¹ * ((c : G) * (k : G) * (c : G)⁻¹) * c := by
          rw [show ((c : G) * (k : G) * (c : G)⁻¹) = ((h₁ : S.toSetting.M) : G) from
            congrArg (fun z : S.toSetting.M => (z : G)) hc]
      _ = (k : G) := by group

private theorem card_centralizer_Q_eq (Fd : FibreData S) {h₁ : S.toSetting.Q}
    (hφh : (((Fd.φQ h₁ : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) = Max3.q 0)
    (h256 : Nat.card ↥(Max3.Q ⊓ Subgroup.centralizer ({Max3.q 0} : Set J)) = 2 ^ 8) :
    Nat.card ↥(S.toSetting.Q ⊓
      Subgroup.centralizer ({(h₁ : S.toSetting.M)} : Set S.toSetting.M)) = 2 ^ 8 := by
  let P : Subgroup S.toSetting.M :=
    S.toSetting.Q ⊓ Subgroup.centralizer ({(h₁ : S.toSetting.M)} : Set S.toSetting.M)
  let QM : Subgroup Max3.M := Max3.Q.subgroupOf Max3.M
  let q0QM : QM :=
    ⟨⟨Max3.q 0, Max3.Q_le_M (Max3.q_mem_Q 0)⟩,
      Subgroup.mem_subgroupOf.mpr (Max3.q_mem_Q 0)⟩
  have hφhQM : Fd.φQ h₁ = q0QM := by
    apply Subtype.ext
    exact Subtype.ext hφh
  let toQM : P →* QM :=
    { toFun := fun p => Fd.φQ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩
      map_one' := map_one Fd.φQ
      map_mul' := fun p q =>
        map_mul Fd.φQ ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩
          ⟨q.1, (Subgroup.mem_inf.mp q.2).1⟩ }
  have htoQM_inj : Function.Injective toQM := by
    intro p q hpq
    have hq : (⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ : S.toSetting.Q) =
        ⟨q.1, (Subgroup.mem_inf.mp q.2).1⟩ :=
      Fd.φQ.injective hpq
    have hpq' : (p : S.toSetting.M) = (q : S.toSetting.M) :=
      congrArg (fun z : S.toSetting.Q => (z : S.toSetting.M)) hq
    exact Subtype.ext hpq'
  have hPmap_eq : Subgroup.map toQM ⊤ =
      Subgroup.centralizer ({q0QM} : Set QM) := by
    ext x
    constructor
    · intro hx
      obtain ⟨p, -, rfl⟩ := Subgroup.mem_map.mp hx
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hp2 : p.1 ∈ Subgroup.centralizer ({(h₁ : S.toSetting.M)} : Set S.toSetting.M) :=
        (Subgroup.mem_inf.mp p.2).2
      have hpcomm : (⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ : S.toSetting.Q) * h₁ =
          h₁ * ⟨p.1, (Subgroup.mem_inf.mp p.2).1⟩ :=
        Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hp2)
      have h := congrArg Fd.φQ hpcomm
      rw [map_mul, map_mul, hφhQM] at h
      exact h
    · intro hx
      rw [Subgroup.mem_centralizer_singleton_iff] at hx
      let q : S.toSetting.Q := Fd.φQ.symm x
      have hqcomm : q * h₁ = h₁ * q := by
        apply Fd.φQ.injective
        have hqφ : Fd.φQ q = x := Fd.φQ.apply_symm_apply x
        rw [map_mul, map_mul, hφhQM, hqφ]
        exact hx
      refine ⟨⟨q.1, Subgroup.mem_inf.mpr ⟨q.2, ?_⟩⟩, Subgroup.mem_top _, ?_⟩
      · exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val hqcomm)
      · show Fd.φQ ⟨q.1, q.2⟩ = x
        exact Fd.φQ.apply_symm_apply x
  have hCeq : (Subgroup.centralizer ({q0QM} : Set QM)).map QM.subtype =
      (Max3.Q ⊓ Subgroup.centralizer ({Max3.q 0} : Set J)).subgroupOf Max3.M := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine Subgroup.mem_subgroupOf.mpr ⟨Subgroup.mem_subgroupOf.mp x.2, ?_⟩
      have hx' : q0QM * x = x * q0QM :=
        Subgroup.mem_centralizer_iff.mp hx q0QM (by simp)
      change (x : J) ∈ Subgroup.centralizer ({Max3.q 0} : Set J)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hxJ : ((x : QM) : J) * Max3.q 0 = Max3.q 0 * ((x : QM) : J) := by
        have h := congrArg (fun z : QM => ((z : Max3.M) : J)) hx'
        exact h.symm
      exact hxJ
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      obtain ⟨hyQ, hyC⟩ := hy
      let yQM : QM :=
        ⟨⟨y, Max3.Q_le_M hyQ⟩, Subgroup.mem_subgroupOf.mpr hyQ⟩
      refine ⟨yQM, ?_, rfl⟩
      change yQM ∈ Subgroup.centralizer ({q0QM} : Set QM)
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      apply Subtype.ext
      have hyC' : Max3.q 0 * y = y * Max3.q 0 :=
        Subgroup.mem_centralizer_iff.mp hyC (Max3.q 0) (by simp)
      exact hyC'.symm
  have hCcard : Nat.card (Subgroup.centralizer ({q0QM} : Set QM)) = 2 ^ 8 := by
    have hmap : Nat.card ((Subgroup.centralizer ({q0QM} : Set QM)).map QM.subtype) =
        Nat.card (Subgroup.centralizer ({q0QM} : Set QM)) :=
      Subgroup.card_map_of_injective QM.subtype_injective
    rw [← hmap, hCeq,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left.trans Max3.Q_le_M)).toEquiv, h256]
  have hPcard : Nat.card P = 2 ^ 8 := by
    have hmapcard : Nat.card (Subgroup.map toQM ⊤) = Nat.card P := by
      rw [Subgroup.card_map_of_injective htoQM_inj, Subgroup.card_top]
    rw [← hmapcard, hPmap_eq, hCcard]
  exact hPcard

private theorem map_centralizer_Q_eq (h₁ : S.toSetting.Q) :
    (S.toSetting.Q ⊓
      Subgroup.centralizer ({(h₁ : S.toSetting.M)} : Set S.toSetting.M)).map
        S.toSetting.M.subtype =
      S.Q ⊓ Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G) := by
  ext x
  constructor
  · rintro ⟨p, hpP, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← S.toSetting_QG]
      exact Subgroup.mem_map.mpr ⟨p, (Subgroup.mem_inf.mp hpP).1, rfl⟩
    · change S.toSetting.M.subtype p ∈
        Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hp2 : p ∈ Subgroup.centralizer
          ({(h₁ : S.toSetting.M)} : Set S.toSetting.M) :=
        (Subgroup.mem_inf.mp hpP).2
      exact congrArg (fun z : S.toSetting.M => (z : G))
        (Subgroup.mem_centralizer_singleton_iff.mp hp2)
  · rintro ⟨hxQ, hxC⟩
    rw [← S.toSetting_QG] at hxQ
    obtain ⟨q, hqQ, hqx⟩ := Subgroup.mem_map.mp hxQ
    have hpP : q ∈ S.toSetting.Q ⊓
        Subgroup.centralizer ({(h₁ : S.toSetting.M)} : Set S.toSetting.M) := by
      refine Subgroup.mem_inf.mpr ⟨hqQ, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      have hcomm : (q : G) * ((h₁ : S.toSetting.M) : G) =
          ((h₁ : S.toSetting.M) : G) * (q : G) := by
        have hx' : x * ((h₁ : S.toSetting.M) : G) =
            ((h₁ : S.toSetting.M) : G) * x :=
          Subgroup.mem_centralizer_singleton_iff.mp hxC
        rwa [← hqx] at hx'
      exact hcomm
    exact Subgroup.mem_map.mpr ⟨q, hpP, hqx⟩

private theorem card_inf_centralizer_eq (Fd : FibreData S) {h₁ : S.toSetting.Q}
    (hφh : (((Fd.φQ h₁ : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) = Max3.q 0)
    (h256 : Nat.card ↥(Max3.Q ⊓ Subgroup.centralizer ({Max3.q 0} : Set J)) = 2 ^ 8) :
    Nat.card ↥(S.Q ⊓
      Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G)) = 2 ^ 8 := by
  have hP := card_centralizer_Q_eq Fd hφh h256
  rw [← map_centralizer_Q_eq h₁,
    Subgroup.card_map_of_injective S.toSetting.M.subtype_injective, hP]

private theorem R_le_H {h₁ : S.toSetting.Q} {g₀ : G}
    (hg₀h : g₀ * ((h₁ : S.toSetting.M) : G) * g₀⁻¹ = S.z) :
    (S.Q ⊓ Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G)).map
      (MulAut.conj g₀).toMonoidHom ≤ S.toSetting.M := by
  intro r hr
  obtain ⟨p, hpPG, rfl⟩ := Subgroup.mem_map.mp hr
  have hpQ : p ∈ S.Q := (Subgroup.mem_inf.mp hpPG).1
  have hpC : p ∈ Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G) :=
    (Subgroup.mem_inf.mp hpPG).2
  have hpz : p ∈ Subgroup.centralizer ({S.z} : Set G) := S.Q_le_H hpQ
  change g₀ * p * g₀⁻¹ ∈ Subgroup.centralizer ({S.toSetting.z} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  change (g₀ * p * g₀⁻¹) * S.z = S.z * (g₀ * p * g₀⁻¹)
  rw [← hg₀h]
  calc (g₀ * p * g₀⁻¹) * (g₀ * ((h₁ : S.toSetting.M) : G) * g₀⁻¹)
      = g₀ * (p * ((h₁ : S.toSetting.M) : G)) * g₀⁻¹ := by group
    _ = g₀ * (((h₁ : S.toSetting.M) : G) * p) * g₀⁻¹ := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hpC]
    _ = (g₀ * ((h₁ : S.toSetting.M) : G) * g₀⁻¹) * (g₀ * p * g₀⁻¹) := by group

private theorem R_le_C {h₁ : S.toSetting.Q} {g₀ : G}
    (hg₀z : g₀ * S.z * g₀⁻¹ = ((h₁ : S.toSetting.M) : G)) :
    (S.Q ⊓ Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G)).map
      (MulAut.conj g₀).toMonoidHom ≤
        Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G) := by
  intro r hr
  obtain ⟨p, hpPG, rfl⟩ := Subgroup.mem_map.mp hr
  have hpQ : p ∈ S.Q := (Subgroup.mem_inf.mp hpPG).1
  have hpz : p ∈ Subgroup.centralizer ({S.z} : Set G) := S.Q_le_H hpQ
  rw [Subgroup.mem_centralizer_singleton_iff]
  rw [← hg₀z]
  calc (g₀ * p * g₀⁻¹) * (g₀ * S.z * g₀⁻¹)
      = g₀ * (p * S.z) * g₀⁻¹ := by group
    _ = g₀ * (S.z * p) * g₀⁻¹ := by
        rw [Subgroup.mem_centralizer_singleton_iff.mp hpz]
    _ = (g₀ * S.z * g₀⁻¹) * (g₀ * p * g₀⁻¹) := by group

private theorem R_not_le_Q (Fd : FibreData S) {h₁ : S.toSetting.Q} {g₀ : G}
    (hφh : (((Fd.φQ h₁ : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) = Max3.q 0)
    (hg₀z : g₀ * S.z * g₀⁻¹ = ((h₁ : S.toSetting.M) : G))
    (hh1_ne_one : ((h₁ : S.toSetting.M) : G) ≠ 1)
    (hh1_ne_z : ((h₁ : S.toSetting.M) : G) ≠ S.z)
    (hnc : ∃ u ∈ Max3.Q, ∃ v ∈ Max3.Q, u * Max3.q 0 = Max3.q 0 * u ∧
      v * Max3.q 0 = Max3.q 0 * v ∧ u * v ≠ v * u) :
    ¬ (S.Q ⊓ Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G)).map
        (MulAut.conj g₀).toMonoidHom ≤ S.Q := by
  intro hRQ
  let QM : Subgroup Max3.M := Max3.Q.subgroupOf Max3.M
  let q0QM : QM :=
    ⟨⟨Max3.q 0, Max3.Q_le_M (Max3.q_mem_Q 0)⟩,
      Subgroup.mem_subgroupOf.mpr (Max3.q_mem_Q 0)⟩
  have hφhQM : Fd.φQ h₁ = q0QM := by
    apply Subtype.ext
    exact Subtype.ext hφh
  have hRleC := R_le_C (h₁ := h₁) (g₀ := g₀) hg₀z
  have hRlePG : (S.Q ⊓
      Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G)).map
        (MulAut.conj g₀).toMonoidHom ≤
      S.Q ⊓ Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G) :=
    le_inf hRQ hRleC
  obtain ⟨u₀, hu₀Q, v₀, hv₀Q, hu₀q, hv₀q, huv₀⟩ := hnc
  let uQM : QM :=
    ⟨⟨u₀, Max3.Q_le_M hu₀Q⟩, Subgroup.mem_subgroupOf.mpr hu₀Q⟩
  let vQM : QM :=
    ⟨⟨v₀, Max3.Q_le_M hv₀Q⟩, Subgroup.mem_subgroupOf.mpr hv₀Q⟩
  have huQMq : uQM * q0QM = q0QM * uQM := by
    apply Subtype.ext
    apply Subtype.ext
    exact hu₀q
  have hvQMq : vQM * q0QM = q0QM * vQM := by
    apply Subtype.ext
    apply Subtype.ext
    exact hv₀q
  let u : S.toSetting.Q := Fd.φQ.symm uQM
  let v : S.toSetting.Q := Fd.φQ.symm vQM
  have huC : ((u : S.toSetting.M) : G) ∈
      Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hq : u * h₁ = h₁ * u := by
      apply Fd.φQ.injective
      rw [map_mul, map_mul, Fd.φQ.apply_symm_apply, hφhQM]
      exact huQMq
    exact congrArg (fun z : S.toSetting.Q => ((z : S.toSetting.M) : G)) hq
  have hvC : ((v : S.toSetting.M) : G) ∈
      Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hq : v * h₁ = h₁ * v := by
      apply Fd.φQ.injective
      rw [map_mul, map_mul, Fd.φQ.apply_symm_apply, hφhQM]
      exact hvQMq
    exact congrArg (fun z : S.toSetting.Q => ((z : S.toSetting.M) : G)) hq
  have huQ : ((u : S.toSetting.M) : G) ∈ S.Q := by
    rw [← S.toSetting_QG]
    exact Subgroup.mem_map.mpr ⟨(u : S.toSetting.M), u.2, rfl⟩
  have hvQ : ((v : S.toSetting.M) : G) ∈ S.Q := by
    rw [← S.toSetting_QG]
    exact Subgroup.mem_map.mpr ⟨(v : S.toSetting.M), v.2, rfl⟩
  have huPG : ((u : S.toSetting.M) : G) ∈
      S.Q ⊓ Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G) :=
    Subgroup.mem_inf.mpr ⟨huQ, huC⟩
  have hvPG : ((v : S.toSetting.M) : G) ∈
      S.Q ⊓ Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G) :=
    Subgroup.mem_inf.mpr ⟨hvQ, hvC⟩
  have huv : u * v ≠ v * u := by
    intro h
    apply huv₀
    have h' : Fd.φQ (u * v) = Fd.φQ (v * u) := congrArg Fd.φQ h
    rw [map_mul, map_mul, Fd.φQ.apply_symm_apply, Fd.φQ.apply_symm_apply] at h'
    simpa [uQM, vQM] using h'
  have huv_eq_z : ⁅u, v⁆ = S.toSetting.zQ := by
    have hc := (S.toSetting.mem_center_Q_iff).mp
      (commutatorElement_mem_center S.toSetting.extraspecial u v)
    rcases hc with h1 | hz
    · exfalso
      exact huv (commutatorElement_eq_one_iff_commute.mp h1)
    · exact hz
  have huR : g₀ * ((u : S.toSetting.M) : G) * g₀⁻¹ ∈
      (S.Q ⊓ Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G)).map
        (MulAut.conj g₀).toMonoidHom := by
    exact Subgroup.mem_map.mpr ⟨((u : S.toSetting.M) : G), huPG, rfl⟩
  have hvR : g₀ * ((v : S.toSetting.M) : G) * g₀⁻¹ ∈
      (S.Q ⊓ Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G)).map
        (MulAut.conj g₀).toMonoidHom := by
    exact Subgroup.mem_map.mpr ⟨((v : S.toSetting.M) : G), hvPG, rfl⟩
  have huQ' : g₀ * ((u : S.toSetting.M) : G) * g₀⁻¹ ∈ S.Q := hRQ huR
  have hvQ' : g₀ * ((v : S.toSetting.M) : G) * g₀⁻¹ ∈ S.Q := hRQ hvR
  let uH : S.Q := ⟨g₀ * ((u : S.toSetting.M) : G) * g₀⁻¹, huQ'⟩
  let vH : S.Q := ⟨g₀ * ((v : S.toSetting.M) : G) * g₀⁻¹, hvQ'⟩
  have hcommG : ((⁅uH, vH⁆ : S.Q) : G) =
      g₀ * ((⁅u, v⁆ : S.toSetting.Q) : G) * g₀⁻¹ := by
    rw [commutatorElement_def, commutatorElement_def]
    change (g₀ * ((u : S.toSetting.M) : G) * g₀⁻¹) *
        (g₀ * ((v : S.toSetting.M) : G) * g₀⁻¹) *
        (g₀ * ((u : S.toSetting.M) : G) * g₀⁻¹)⁻¹ *
        (g₀ * ((v : S.toSetting.M) : G) * g₀⁻¹)⁻¹ =
      g₀ * (((u : S.toSetting.M) : G) * ((v : S.toSetting.M) : G) *
        ((u : S.toSetting.M) : G)⁻¹ * ((v : S.toSetting.M) : G)⁻¹) * g₀⁻¹
    group
  have hcommG' : ((⁅uH, vH⁆ : S.Q) : G) = ((h₁ : S.toSetting.M) : G) := by
    rw [hcommG, huv_eq_z]
    simpa using hg₀z
  have hcenter : ⁅uH, vH⁆ ∈ Subgroup.center S.Q :=
    commutatorElement_mem_center S.ext uH vH
  have hzcenter : (⟨S.z, S.z_mem_Q⟩ : S.Q) ∈ Subgroup.center S.Q := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp (S.Q_le_H g.2)
  have hz_ne_one : (⟨S.z, S.z_mem_Q⟩ : S.Q) ≠ 1 := by
    intro h
    exact S.toSetting.z_ne_one (congrArg Subtype.val h)
  rcases eq_or_ne ⁅uH, vH⁆ 1 with h1 | hne
  · rw [h1] at hcommG'
    exact hh1_ne_one (by simpa using hcommG'.symm)
  · have hz := eq_of_mem_center S.ext hcenter hzcenter hne hz_ne_one
    rw [hz] at hcommG'
    exact hh1_ne_z (by simpa using hcommG'.symm)

private theorem card_involutions_R_ge (Fd : FibreData S) (e : S.toSetting.M ≃* Max3.M)
    (he : ∀ h, (h, e h) ∈ Fd.F) {h₁ : S.toSetting.Q} {g₀ : G}
    (hφh : (((Fd.φQ h₁ : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) = Max3.q 0)
    (h143 : {w : J | w ∈ Max3.Q ∧ w * Max3.q 0 = Max3.q 0 * w ∧ w * w = 1 ∧
      w ≠ 1}.ncard = 143) :
    143 ≤ {w : G | w ∈ (S.Q ⊓
        Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G)).map
          (MulAut.conj g₀).toMonoidHom ∧ w * w = 1 ∧ w ≠ 1}.ncard := by
  classical
  let QM : Subgroup Max3.M := Max3.Q.subgroupOf Max3.M
  let q0QM : QM :=
    ⟨⟨Max3.q 0, Max3.Q_le_M (Max3.q_mem_Q 0)⟩,
      Subgroup.mem_subgroupOf.mpr (Max3.q_mem_Q 0)⟩
  have hφhQM : Fd.φQ h₁ = q0QM := by
    apply Subtype.ext
    exact Subtype.ext hφh
  let InvQ : Set J := {w : J | w ∈ Max3.Q ∧ w * Max3.q 0 = Max3.q 0 * w ∧
    w * w = 1 ∧ w ≠ 1}
  let InvR : Set G := {w : G | w ∈ (S.Q ⊓
      Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G)).map
        (MulAut.conj g₀).toMonoidHom ∧ w * w = 1 ∧ w ≠ 1}
  have hInvQ : InvQ.ncard = 143 := h143
  let yQMof : (y : J) → y ∈ InvQ → QM := fun y hy =>
    eQM.symm ⟨y, hy.1⟩
  let qof : (y : J) → y ∈ InvQ → S.toSetting.Q := fun y hy =>
    Fd.φQ.symm (yQMof y hy)
  let f : (y : J) → y ∈ InvQ → G := fun y hy =>
    g₀ * ((qof y hy : S.toSetting.M) : G) * g₀⁻¹
  have hf_maps : ∀ (y : J) (hy : y ∈ InvQ), f y hy ∈ InvR := by
    intro y hy
    have heQM_y : (eQM (yQMof y hy) : J) = y := by
      rw [show yQMof y hy = eQM.symm ⟨y, hy.1⟩ from rfl,
        eQM.apply_symm_apply]
    have heQM_q : (eQM q0QM : J) = Max3.q 0 := eQM_val q0QM
    have hyQMq : yQMof y hy * q0QM = q0QM * yQMof y hy := by
      apply eQM.injective
      rw [map_mul, map_mul]
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [heQM_y, heQM_q]
      simpa using hy.2.1
    have hqcomm : qof y hy * h₁ = h₁ * qof y hy := by
      apply Fd.φQ.injective
      have hqφ : Fd.φQ (qof y hy) = yQMof y hy :=
        Fd.φQ.apply_symm_apply (yQMof y hy)
      rw [map_mul, map_mul, hφhQM, hqφ]
      exact hyQMq
    have hyQM2 : yQMof y hy * yQMof y hy = 1 := by
      apply eQM.injective
      rw [map_mul, map_one]
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [heQM_y]
      simpa using hy.2.2.1
    have hq2 : qof y hy * qof y hy = 1 := by
      apply Fd.φQ.injective
      have hqφ : Fd.φQ (qof y hy) = yQMof y hy :=
        Fd.φQ.apply_symm_apply (yQMof y hy)
      rw [map_mul, hqφ, map_one]
      exact hyQM2
    have hq1 : qof y hy ≠ 1 := by
      intro h
      apply hy.2.2.2
      have hqφ : Fd.φQ (qof y hy) = yQMof y hy :=
        Fd.φQ.apply_symm_apply (yQMof y hy)
      have h' : yQMof y hy = 1 := by
        rw [← hqφ, h, map_one]
      have h'' : (eQM (yQMof y hy) : J) = 1 := by
        rw [h', map_one]
        rfl
      rw [heQM_y] at h''
      exact h''
    have hqG : ((qof y hy : S.toSetting.M) : G) ∈ S.Q := by
      rw [← S.toSetting_QG]
      exact Subgroup.mem_map.mpr ⟨(qof y hy : S.toSetting.M), (qof y hy).2, rfl⟩
    have hqC : ((qof y hy : S.toSetting.M) : G) ∈
        Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg (fun z : S.toSetting.Q => ((z : S.toSetting.M) : G)) hqcomm
    have hqPG : ((qof y hy : S.toSetting.M) : G) ∈
        S.Q ⊓ Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G) :=
      Subgroup.mem_inf.mpr ⟨hqG, hqC⟩
    have hf_eq : f y hy = g₀ * ((qof y hy : S.toSetting.M) : G) * g₀⁻¹ := rfl
    rw [hf_eq]
    refine ⟨?_, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨_, hqPG, rfl⟩
    · calc (g₀ * ((qof y hy : S.toSetting.M) : G) * g₀⁻¹) *
          (g₀ * ((qof y hy : S.toSetting.M) : G) * g₀⁻¹)
          = g₀ * (((qof y hy : S.toSetting.M) : G) *
              ((qof y hy : S.toSetting.M) : G)) * g₀⁻¹ := by group
        _ = 1 := by
          rw [show ((qof y hy : S.toSetting.M) : G) *
              ((qof y hy : S.toSetting.M) : G) = 1 from
            congrArg (fun z : S.toSetting.Q => ((z : S.toSetting.M) : G)) hq2]
          group
    · intro h
      apply hq1
      have h' : g₀ * ((qof y hy : S.toSetting.M) : G) * g₀⁻¹ = 1 := h
      have h'' : ((qof y hy : S.toSetting.M) : G) = 1 := by
        calc ((qof y hy : S.toSetting.M) : G) =
            g₀⁻¹ * (g₀ * ((qof y hy : S.toSetting.M) : G) * g₀⁻¹) * g₀ := by group
          _ = 1 := by rw [h']; group
      apply Subtype.ext
      apply Subtype.ext
      exact h''
  have hf_inj : ∀ (y₁ : J) (hy₁ : y₁ ∈ InvQ) (y₂ : J) (hy₂ : y₂ ∈ InvQ),
      f y₁ hy₁ = f y₂ hy₂ → y₁ = y₂ := by
    intro y₁ hy₁ y₂ hy₂ heq
    have hq : qof y₁ hy₁ = qof y₂ hy₂ := by
      apply Subtype.ext
      have := congrArg (fun z => g₀⁻¹ * z * g₀) heq
      change g₀⁻¹ * (g₀ * ((qof y₁ hy₁ : S.toSetting.M) : G) * g₀⁻¹) * g₀ =
        g₀⁻¹ * (g₀ * ((qof y₂ hy₂ : S.toSetting.M) : G) * g₀⁻¹) * g₀ at this
      simpa using this
    have hyQM : yQMof y₁ hy₁ = yQMof y₂ hy₂ := by
      have := congrArg Fd.φQ hq
      simpa only [qof, Fd.φQ.apply_symm_apply] using this
    have h1 : (eQM (yQMof y₁ hy₁) : J) = y₁ :=
      congrArg Subtype.val (eQM.apply_symm_apply ⟨y₁, hy₁.1⟩)
    have h2 : (eQM (yQMof y₂ hy₂) : J) = y₂ :=
      congrArg Subtype.val (eQM.apply_symm_apply ⟨y₂, hy₂.1⟩)
    calc y₁ = (eQM (yQMof y₁ hy₁) : J) := h1.symm
      _ = (eQM (yQMof y₂ hy₂) : J) :=
        congrArg (fun z : QM => (eQM z : J)) hyQM
      _ = y₂ := h2
  have hInvR_ge : 143 ≤ InvR.ncard := by
    rw [← hInvQ]
    have hle := Nat.card_le_card_of_injective
      (fun y : ↥InvQ => (⟨f y.1 y.2, hf_maps y.1 y.2⟩ : ↥InvR))
      (fun y₁ y₂ h => Subtype.ext (hf_inj y₁.1 y₁.2 y₂.1 y₂.2
        (congrArg Subtype.val h)))
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact hle
  exact hInvR_ge

private theorem card_R_eq (Fd : FibreData S) {h₁ : S.toSetting.Q} {g₀ : G}
    (hφh : (((Fd.φQ h₁ : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) = Max3.q 0)
    (h256 : Nat.card ↥(Max3.Q ⊓ Subgroup.centralizer ({Max3.q 0} : Set J)) = 2 ^ 8) :
    Nat.card ↥((S.Q ⊓
      Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G)).map
        (MulAut.conj g₀).toMonoidHom) = 2 ^ 8 := by
  rw [Subgroup.card_map_of_injective (MulAut.conj g₀).injective,
    card_inf_centralizer_eq Fd hφh h256]

private theorem all_involutions_conj_of_aux (S : ThSetting G)
    (e : S.toSetting.M ≃* Max3.M)
    (conjQ_G : ∀ k : S.toSetting.M, k ∈ S.toSetting.Q → k * k = 1 → k ≠ 1 →
      ∃ g : G, g * S.z * g⁻¹ = (k : G))
    (conjOutside : ∀ k : S.toSetting.M, k ∉ S.toSetting.Q → k * k = 1 → k ≠ 1 →
      ∃ c : S.toSetting.M, c * k * c⁻¹ =
        e.symm (⟨Max3.x, Max3.x_mem_M⟩ : Max3.M))
    (hx_conj_z : ∃ g : G, g * S.z * g⁻¹ =
      ((e.symm (⟨Max3.x, Max3.x_mem_M⟩ : Max3.M) : S.toSetting.M) : G)) :
    ∀ j : G, orderOf j = 2 → ∃ g : G, g * S.z * g⁻¹ = j := by
  intro j hj
  have hj2 : j * j = 1 := by
    rw [← pow_two, ← hj, pow_orderOf_eq_one]
  obtain ⟨T, hTleH⟩ := S.exists_isSylow_le_H
  have hjP : IsPGroup 2 (Subgroup.zpowers j) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hj]; norm_num)
  obtain ⟨T', hjT'⟩ := IsPGroup.exists_le_sylow hjP
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T' T
  have hjT' : j ∈ (T' : Subgroup G) := hjT' (Subgroup.mem_zpowers j)
  have hgjT : g * j * g⁻¹ ∈ (T : Subgroup G) := by
    rw [← hg]
    change g * j * g⁻¹ ∈
      Subgroup.map (MulAut.conj g).toMonoidHom (T' : Subgroup G)
    exact Subgroup.mem_map.mpr ⟨j, hjT', rfl⟩
  have hgjH : g * j * g⁻¹ ∈ S.toSetting.M := hTleH hgjT
  have hgj2 : (⟨g * j * g⁻¹, hgjH⟩ : S.toSetting.M) *
      ⟨g * j * g⁻¹, hgjH⟩ = 1 := by
    apply Subtype.ext
    calc (g * j * g⁻¹) * (g * j * g⁻¹) = g * (j * j) * g⁻¹ := by group
      _ = 1 := by rw [hj2]; group
  have hgj1 : (⟨g * j * g⁻¹, hgjH⟩ : S.toSetting.M) ≠ 1 := by
    intro h
    have h' : g * j * g⁻¹ = 1 := congrArg Subtype.val h
    have hj1 : j = 1 := by
      calc j = g⁻¹ * (g * j * g⁻¹) * g := by group
        _ = 1 := by rw [h']; group
    rw [hj1, orderOf_one] at hj
    exact absurd hj (by norm_num)
  by_cases hz : (⟨g * j * g⁻¹, hgjH⟩ : S.toSetting.M) = S.toSetting.zM
  · refine ⟨g⁻¹, ?_⟩
    have h' : g * j * g⁻¹ = S.z :=
      congrArg (fun z : S.toSetting.M => (z : G)) hz
    rw [← h']
    group
  · by_cases hQ : (⟨g * j * g⁻¹, hgjH⟩ : S.toSetting.M) ∈ S.toSetting.Q
    · obtain ⟨k, hk⟩ := conjQ_G ⟨g * j * g⁻¹, hgjH⟩ hQ hgj2 hgj1
      refine ⟨g⁻¹ * k, ?_⟩
      calc (g⁻¹ * k) * S.z * (g⁻¹ * k)⁻¹
          = g⁻¹ * (k * S.z * k⁻¹) * g := by group
        _ = g⁻¹ * (g * j * g⁻¹) * g := by rw [hk]
        _ = j := by group
    · obtain ⟨c, hc⟩ := conjOutside ⟨g * j * g⁻¹, hgjH⟩ hQ hgj2 hgj1
      obtain ⟨k, hk⟩ := hx_conj_z
      refine ⟨g⁻¹ * (c : G)⁻¹ * k, ?_⟩
      have hcG : (c : G) * (g * j * g⁻¹) * (c : G)⁻¹ =
          ((e.symm (⟨Max3.x, Max3.x_mem_M⟩ : Max3.M) : S.toSetting.M) : G) :=
        congrArg (fun z : S.toSetting.M => (z : G)) hc
      calc (g⁻¹ * (c : G)⁻¹ * k) * S.z * (g⁻¹ * (c : G)⁻¹ * k)⁻¹
          = g⁻¹ * (c : G)⁻¹ * (k * S.z * k⁻¹) * (c : G) * g := by group
        _ = g⁻¹ * (c : G)⁻¹ * ((e.symm (⟨Max3.x, Max3.x_mem_M⟩ : Max3.M) : S.toSetting.M) : G) *
            (c : G) * g := by rw [hk]
        _ = j := by
            calc g⁻¹ * (c : G)⁻¹ * ((e.symm (⟨Max3.x, Max3.x_mem_M⟩ : Max3.M) : S.toSetting.M) : G) *
                (c : G) * g
                = g⁻¹ * (c : G)⁻¹ * ((c : G) * (g * j * g⁻¹) * (c : G)⁻¹) *
                    (c : G) * g := by
                  rw [show ((e.symm (⟨Max3.x, Max3.x_mem_M⟩ : Max3.M) : S.toSetting.M) : G) =
                    (c : G) * (g * j * g⁻¹) * (c : G)⁻¹ from hcG.symm]
              _ = j := by group


theorem all_involutions_conj_of (Fd : FibreData S) (e : S.toSetting.M ≃* Max3.M)
    (he : ∀ h, (h, e h) ∈ Fd.F)
    (h256 : Nat.card ↥(Max3.Q ⊓ Subgroup.centralizer ({Max3.q 0} : Set J)) = 2 ^ 8)
    (h143 : {w : J | w ∈ Max3.Q ∧ w * Max3.q 0 = Max3.q 0 * w ∧ w * w = 1 ∧
      w ≠ 1}.ncard = 143)
    (hnc : ∃ u ∈ Max3.Q, ∃ v ∈ Max3.Q, u * Max3.q 0 = Max3.q 0 * u ∧
      v * Max3.q 0 = Max3.q 0 * v ∧ u * v ≠ v * u)
    (hswap : ∃ h₁ : S.toSetting.Q,
      (((Fd.φQ h₁ : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) = Max3.q 0 ∧
      ∃ g : G, g * S.z * g⁻¹ = ((h₁ : S.toSetting.M) : G) ∧
        g * ((h₁ : S.toSetting.M) : G) * g⁻¹ = S.z) :
    ∀ j : G, orderOf j = 2 → ∃ g : G, g * S.z * g⁻¹ = j := by
  classical
  obtain ⟨h₁, hφh, g₀, hg₀z, hg₀h⟩ := hswap
  have hh1G2 : ((h₁ : S.toSetting.M) : G) * ((h₁ : S.toSetting.M) : G) = 1 := by
    rw [show ((h₁ : S.toSetting.M) : G) = g₀ * S.z * g₀⁻¹ from hg₀z.symm]
    calc (g₀ * S.z * g₀⁻¹) * (g₀ * S.z * g₀⁻¹)
        = g₀ * (S.z * S.z) * g₀⁻¹ := by group
      _ = 1 := by
        have hz2 : S.z * S.z = 1 := S.toSetting.z_mul_z
        rw [hz2]
        group
  have hh1H2 : (h₁ : S.toSetting.M) * (h₁ : S.toSetting.M) = 1 := by
    apply Subtype.ext
    exact hh1G2
  have hh1_ne_zM : (h₁ : S.toSetting.M) ≠ S.toSetting.zM := by
    intro h
    have h' : ((h₁ : S.toSetting.M) : G) = S.z :=
      congrArg (fun z : S.toSetting.M => (z : G)) h
    have hφz : (Fd.φQ S.toSetting.zQ : Max3.M) =
        (⟨Max3.z, Max3.z_mem_M⟩ : Max3.M) := by
      apply Subtype.ext
      exact Fd.φQ_z
    have hφhM : (Fd.φQ h₁ : Max3.M) =
        (⟨Max3.q 0, Max3.Q_le_M (Max3.q_mem_Q 0)⟩ : Max3.M) := by
      apply Subtype.ext
      exact hφh
    have hq0z : Max3.q 0 = Max3.z := by
      calc Max3.q 0 = (((Fd.φQ h₁ : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) := hφh.symm
        _ = (((Fd.φQ S.toSetting.zQ : ↥(Max3.Q.subgroupOf Max3.M)) : Max3.M) : J) := by
            rw [show h₁ = S.toSetting.zQ from Subtype.ext h]
        _ = Max3.z := Fd.φQ_z
    exact q0_ne_z hq0z
  have hh1_ne_oneH : (h₁ : S.toSetting.M) ≠ 1 := by
    intro h
    have h1G_eq : ((h₁ : S.toSetting.M) : G) = 1 := by rw [h]; rfl
    have hz1 : S.z = 1 := by
      calc S.z = g₀⁻¹ * (g₀ * S.z * g₀⁻¹) * g₀ := by group
        _ = g₀⁻¹ * ((h₁ : S.toSetting.M) : G) * g₀ := by rw [hg₀z]
        _ = 1 := by rw [h1G_eq]; group
    exact S.toSetting.z_ne_one hz1
  have hh1_ne_oneG : ((h₁ : S.toSetting.M) : G) ≠ 1 :=
    fun h => hh1_ne_oneH (Subtype.ext h)
  have hh1_ne_zG : ((h₁ : S.toSetting.M) : G) ≠ S.z :=
    fun h => hh1_ne_zM (Subtype.ext h)
  have conjQ := exists_conj_of_mem_Q_involution Fd e he hφh hh1H2 hh1_ne_oneH hh1_ne_zM
  have conjOutside := exists_conj_outside_Q Fd e he
  have conjQ_G := exists_conj_z_of_mem_Q Fd e he hφh hg₀z hh1H2 hh1_ne_oneH hh1_ne_zM
  let R : Subgroup G := (S.Q ⊓
    Subgroup.centralizer ({((h₁ : S.toSetting.M) : G)} : Set G)).map
      (MulAut.conj g₀).toMonoidHom
  have hRcard : Nat.card R = 2 ^ 8 := card_R_eq Fd hφh h256
  have hRleH : R ≤ S.toSetting.M := R_le_H hg₀h
  have hRnotQ : ¬ R ≤ S.Q := R_not_le_Q Fd hφh hg₀z hh1_ne_oneG hh1_ne_zG hnc
  let InvR : Set G := {w : G | w ∈ R ∧ w * w = 1 ∧ w ≠ 1}
  have hInvR_ge : 143 ≤ InvR.ncard := card_involutions_R_ge Fd e he hφh h143
  have hRQ_lt : R ⊓ S.Q < R := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    apply hRnotQ
    rw [← heq]
    exact inf_le_right
  have hInvRQ_le : {w : G | w ∈ R ⊓ S.Q ∧ w * w = 1 ∧ w ≠ 1}.ncard ≤ 127 :=
    ncard_involutions_le_of_lt hRQ_lt hRcard
  have hInvRQ_lt : {w : G | w ∈ R ⊓ S.Q ∧ w * w = 1 ∧ w ≠ 1}.ncard < InvR.ncard :=
    lt_of_le_of_lt hInvRQ_le (lt_of_lt_of_le (by norm_num : 127 < 143) hInvR_ge)
  obtain ⟨w', hw'R, hw'notRQ⟩ :=
    Set.exists_mem_notMem_of_ncard_lt_ncard hInvRQ_lt
  have hw'R' : w' ∈ R := hw'R.1
  have hw'sq : w' * w' = 1 := hw'R.2.1
  have hw'ne1 : w' ≠ 1 := hw'R.2.2
  have hw'notQ : w' ∉ S.Q := by
    intro hQ
    exact hw'notRQ ⟨⟨hw'R', hQ⟩, hw'sq, hw'ne1⟩
  have hw'H : w' ∈ S.toSetting.M := hRleH hw'R'
  have hw'_conj_z : ∃ k : G, k * S.z * k⁻¹ = w' := by
    obtain ⟨p, hpPG, hp_eq⟩ := Subgroup.mem_map.mp hw'R'
    have hpQ : p ∈ S.Q := (Subgroup.mem_inf.mp hpPG).1
    rw [← S.toSetting_QG] at hpQ
    obtain ⟨q, hqQ, hqp⟩ := Subgroup.mem_map.mp hpQ
    have hw'q : w' = g₀ * (q : G) * g₀⁻¹ := by
      rw [← hp_eq, ← hqp]
      rfl
    have hq2 : q * q = 1 := by
      apply Subtype.ext
      have h' : (q : G) * (q : G) = 1 := by
        have := hw'sq
        rw [hw'q] at this
        calc (q : G) * (q : G) =
            g₀⁻¹ * ((g₀ * (q : G) * g₀⁻¹) * (g₀ * (q : G) * g₀⁻¹)) * g₀ := by group
          _ = 1 := by rw [this]; group
      exact h'
    have hq1 : q ≠ 1 := by
      intro h
      apply hw'ne1
      calc w' = g₀ * (q : G) * g₀⁻¹ := hw'q
        _ = g₀ * 1 * g₀⁻¹ := by
          rw [h]
          rfl
        _ = 1 := by group
    obtain ⟨k, hk⟩ := conjQ_G q hqQ hq2 hq1
    refine ⟨g₀ * k, ?_⟩
    calc (g₀ * k) * S.z * (g₀ * k)⁻¹
        = g₀ * (k * S.z * k⁻¹) * g₀⁻¹ := by group
      _ = g₀ * (q : G) * g₀⁻¹ := by rw [hk]
      _ = w' := hw'q.symm
  have hw'Hinv : (⟨w', hw'H⟩ : S.toSetting.M) * ⟨w', hw'H⟩ = 1 := by
    apply Subtype.ext
    exact hw'sq
  have hw'Hne1 : (⟨w', hw'H⟩ : S.toSetting.M) ≠ 1 := by
    intro h
    exact hw'ne1 (congrArg Subtype.val h)
  have hw'HnotQ : (⟨w', hw'H⟩ : S.toSetting.M) ∉ S.toSetting.Q := by
    intro h
    apply hw'notQ
    have h' : (⟨w', hw'H⟩ : S.toSetting.M) ∈ S.Q.subgroupOf S.H := by
      rwa [← S.toSetting_Q_eq]
    exact Subgroup.mem_subgroupOf.mp h'
  obtain ⟨c, hc⟩ := conjOutside ⟨w', hw'H⟩ hw'HnotQ hw'Hinv hw'Hne1
  obtain ⟨k, hk⟩ := hw'_conj_z
  have hx_conj_z : ∃ g : G, g * S.z * g⁻¹ =
      ((e.symm (⟨Max3.x, Max3.x_mem_M⟩ : Max3.M) : S.toSetting.M) : G) := by
    refine ⟨(c : G) * k, ?_⟩
    have hcG : (c : G) * w' * (c : G)⁻¹ =
        ((e.symm (⟨Max3.x, Max3.x_mem_M⟩ : Max3.M) : S.toSetting.M) : G) :=
      congrArg (fun z : S.toSetting.M => (z : G)) hc
    calc ((c : G) * k) * S.z * ((c : G) * k)⁻¹
        = (c : G) * (k * S.z * k⁻¹) * (c : G)⁻¹ := by group
      _ = (c : G) * w' * (c : G)⁻¹ := by rw [hk]
      _ = ((e.symm (⟨Max3.x, Max3.x_mem_M⟩ : Max3.M) : S.toSetting.M) : G) := hcG
  exact all_involutions_conj_of_aux S e conjQ_G conjOutside hx_conj_z

end FibreData

end CFSG.Sporadic.Th.Recog

