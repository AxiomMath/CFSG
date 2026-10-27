module

public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Background.C2A3Orbits

public section

namespace CFSG.Quasithin.C48

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {H R M L V : Subgroup G}

theorem pCoreOf_le_M (h : HypC28 H R M L V) : pCoreOf 2 H ≤ M :=
  (c2_1_pCore_le (c2_9_two h).2).trans h.le_M

theorem preimageModTwoCore_le (h : HypC28 H R M L V) {X : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)}
    (hX : X ≤ (M.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) :
    preimageModTwoCore H X ≤ M := by
  have hQM := pCoreOf_le_M h
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨m, hm, hmx⟩ := Subgroup.mem_map.mp (hX (Subgroup.mem_comap.mp hx))
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hmx
  have h1 : (m : G)⁻¹ * x ∈ pCoreOf 2 H := by
    have : (m⁻¹ * x : ↥H) ∈ CFSG.pCore 2 ↥H := hmx
    rw [pCoreOf]
    exact ⟨_, this, by simp⟩
  have e : (x : G) = m * ((m : G)⁻¹ * x) := by group
  show (x : G) ∈ M
  rw [e]
  exact mul_mem (Subgroup.mem_subgroupOf.mp hm) (hQM h1)

theorem exists_cComp_not_le (h : HypC28 H R M L V) (hF : oTwoFIn H ≤ M)
    (hFs : ¬ oTwoFstarIn H ≤ M) :
    ∃ K ∈ cComp H, CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) ∧ ¬ K ≤ M := by
  by_contra hall
  push Not at hall
  apply hFs
  set N := CFSG.pCore 2 ↥H with hN
  set Mb : Subgroup (↥H ⧸ N) := (M.subgroupOf H).map (QuotientGroup.mk' N) with hMb
  have hFb : CFSG.fittingSubgroup (↥H ⧸ N) ≤ Mb := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N y
    have hxF : (x : G) ∈ oTwoFIn H := ⟨x, Subgroup.mem_comap.mpr hy, rfl⟩
    exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_subgroupOf.mpr (hF hxF), rfl⟩
  have hEb : CFSG.layer (↥H ⧸ N) ≤ Mb := by
    refine sSup_le fun J hJ => ?_
    obtain ⟨K, hK, hKJ⟩ := exists_cComp_modO2Image_eq (mem_cComp_top_of_isComponent hJ)
    have hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K) := by
      obtain ⟨e⟩ := modO2_mulEquiv hK
      have hJq : CFSG.IsQuasisimple ↥(modO2Image H K) := by rw [hKJ]; exact hJ.1
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hJq
    have hKM := hall K hK hKq
    rw [← hKJ]
    exact Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      (hKM (Subgroup.mem_subgroupOf.mp hx))
  exact preimageModTwoCore_le h (sup_le hFb hEb)

omit [Finite G] in
theorem mk_eq_one_iff {K : Subgroup G} {x : K} :
    (x : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 ↔ (x : G) ∈ pCoreOf 2 K := by
  rw [QuotientGroup.eq_one_iff, pCoreOf]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]

theorem le_of_map_eq_top {K N : Subgroup G} (hNK : N ≤ K) (hN : (N.subgroupOf K).Normal)
    (hperf : ⁅K, K⁆ = K)
    (h : (N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) = ⊤) : K ≤ N := by
  have hsup : K = N ⊔ pCoreOf 2 K := by
    refine le_antisymm (fun x hx => ?_) (sup_le hNK (CFSG.LieType.BorelTits.pCoreOf_le 2 K))
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨x, hx⟩ : K) ∈
        (N.subgroupOf K).map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) := by rw [h]; trivial
    obtain ⟨n, hn, hnx⟩ := hmem
    have h1 : ((n⁻¹ * ⟨x, hx⟩ : K) : ↥K ⧸ CFSG.pCore 2 ↥K) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have : ((n : K) : ↥K ⧸ CFSG.pCore 2 ↥K) = ((⟨x, hx⟩ : K) : ↥K ⧸ CFSG.pCore 2 ↥K) := hnx
      rw [this, inv_mul_cancel]
    have h2 := mk_eq_one_iff.mp h1
    have e : x = (n : G) * ((n⁻¹ * ⟨x, hx⟩ : K) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem_sup hn h2
  have hsolv : Group.IsSolvable ↥(pCoreOf 2 K) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).isNilpotent
    infer_instance
  have hpc := perfectCore_le_of_sup_solvable hNK hN hsup hsolv
  rwa [perfectCore_eq_self_of_perfect hperf] at hpc

theorem mem_oddCoreIn_of_mem_center {K : Subgroup G} (hK : IsSubnormal K H) {y : G}
    (hyK : y ∈ K) (hyc : ∀ k ∈ K, k * y = y * k) (hodd : Odd (orderOf y)) :
    y ∈ oddCoreIn H := by
  have hKH : K ≤ H := A3.subnormal_le hK
  have hsub : (K.subgroupOf H).IsSubnormal := by
    have h1 := A3.subnormal_comap H.subtype hK
    have h2 : Subgroup.comap H.subtype H = ⊤ := by simp
    rw [h2] at h1
    exact A3.subnormal_top_iff.mp h1
  have hyH : y ∈ H := hKH hyK
  set yK : K.subgroupOf H := ⟨⟨y, hyH⟩, hyK⟩ with hyKdef
  have hcen : yK ∈ Subgroup.center (K.subgroupOf H) := by
    rw [Subgroup.mem_center_iff]
    intro k
    exact Subtype.ext (Subtype.ext (hyc _ k.2))
  have hordK : orderOf yK = orderOf y := by
    rw [← Subgroup.orderOf_coe yK]
    change orderOf (⟨y, hyH⟩ : H) = _
    rw [← Subgroup.orderOf_coe (⟨y, hyH⟩ : H)]
  have hle : Subgroup.zpowers yK ≤ CFSG.oddCore (K.subgroupOf H) := by
    apply le_sSup
    exact ⟨Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcen),
      by rw [Nat.card_zpowers, hordK]; exact hodd⟩
  have hmem : yK ∈ CFSG.oddCore (K.subgroupOf H) := hle (Subgroup.mem_zpowers yK)
  have hπ := CFSG.LocalCores.prime_set_core_subnormal_intersection
    {q : Nat.Primes | q.val ≠ 2} hsub
  rw [← CFSG.oddCore_eq_piCore, ← CFSG.oddCore_eq_piCore] at hπ
  have himg : (⟨y, hyH⟩ : H) ∈ (CFSG.oddCore (K.subgroupOf H)).map (K.subgroupOf H).subtype :=
    ⟨yK, hmem, rfl⟩
  rw [hπ] at himg
  exact ⟨⟨y, hyH⟩, himg.2, rfl⟩

theorem isComponentOf_or_charTwo (hO : oddCoreIn H = ⊥) {K : Subgroup G} (hK : K ∈ cComp H)
    (hq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) :
    CFSG.Open.IsComponentOf K H ∨ CharTwo K := by
  by_cases hC : CharTwo K
  · exact Or.inr hC
  left
  have hKH : K ≤ H := le_of_mem_cComp hK
  set C := K ⊓ Subgroup.centralizer (pCoreOf 2 K : Set G) with hCdef
  have hCK : C ≤ K := inf_le_left
  have hQn : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hnorm : (C.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCK]
    intro c k hc hk
    refine Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem hk (hCK hc)) (K.inv_mem hk), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : k⁻¹ * q * k ∈ pCoreOf 2 K := by
      have := (Subgroup.mem_normalizer_iff.mp (hQn (K.inv_mem hk)) q).mp hq
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hc).2 _ hq'
    calc q * (k * c * k⁻¹) = k * ((k⁻¹ * q * k) * c) * k⁻¹ := by group
      _ = k * (c * (k⁻¹ * q * k)) * k⁻¹ := by rw [h1]
      _ = k * c * k⁻¹ * q := by group
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (hnorm.map (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)) with h | h
  ·
    have hperf := perfect_of_mem_cComp hK
    have hKC : K ≤ C := le_of_map_eq_top hCK hnorm hperf h
    have hker : (QuotientGroup.mk' (CFSG.pCore 2 ↥K)).ker ≤ Subgroup.center ↥K := by
      intro x hx
      rw [QuotientGroup.ker_mk'] at hx
      have hxQ : (x : G) ∈ pCoreOf 2 K := by
        rw [pCoreOf]
        exact ⟨x, hx, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro w
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hKC w.2)).2 _ hxQ).symm
    have hP : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr hperf
    have hqK : CFSG.IsQuasisimple ↥K :=
      (CFSG.LocalCores.isQuasisimple_iff_of_surjective hP _ (QuotientGroup.mk'_surjective _)
        hker).mpr hq
    exact ⟨hKH, subnormal_of_mem_cComp hK, A3.isQuasisimple_iff_open.mp hqK⟩
  ·
    exfalso
    apply hC
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hQp := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
    have hodd1 : ∀ w ∈ C, Odd (orderOf w) → w = 1 := by
      intro w hw hodd
      have hwK : w ∈ K := hCK hw
      have hcen : ∀ g ∈ K, g * w = w * g := by
        intro g hg
        have hz : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (⟨w, hwK⟩ : K) ∈
            Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := h ⟨⟨w, hwK⟩, hw, rfl⟩
        have hc := Subgroup.mem_center_iff.mp hz (QuotientGroup.mk' _ ⟨g, hg⟩)
        rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq] at hc
        set q : G := w⁻¹ * (g * w * g⁻¹) with hqdef
        have hqQ : q ∈ pCoreOf 2 K := by
          have h1 : ((⟨g, hg⟩ * ⟨w, hwK⟩ : K)⁻¹ * (⟨w, hwK⟩ * ⟨g, hg⟩) : K) ∈
              CFSG.pCore 2 ↥K := hc
          have h2 : (((⟨g, hg⟩ * ⟨w, hwK⟩ : K)⁻¹ * (⟨w, hwK⟩ * ⟨g, hg⟩) : K) : G) ∈
              pCoreOf 2 K := by
            rw [pCoreOf]
            exact ⟨_, h1, rfl⟩
          have h3 : q = g * (((⟨g, hg⟩ * ⟨w, hwK⟩ : K)⁻¹ * (⟨w, hwK⟩ * ⟨g, hg⟩) : K) : G)⁻¹ *
              g⁻¹ := by
            simp only [hqdef, Subgroup.coe_mul, Subgroup.coe_inv]
            group
          rw [h3]
          exact (Subgroup.mem_normalizer_iff.mp (hQn hg) _).mp ((pCoreOf 2 K).inv_mem h2)
        have hwq : w * q = q * w :=
          (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hw).2 q hqQ).symm
        have hpow : q ^ orderOf w = 1 := by
          have h1 : (g * w * g⁻¹) ^ orderOf w = 1 := by
            rw [conj_pow, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
          have h2 : g * w * g⁻¹ = w * q := by rw [hqdef]; group
          rw [h2, (Commute.mul_pow hwq), pow_orderOf_eq_one, one_mul] at h1
          exact h1
        obtain ⟨k, hk⟩ := hQp ⟨q, hqQ⟩
        have hk' : q ^ 2 ^ k = 1 := by
          have := congrArg Subtype.val hk
          simpa using this
        have hq1 : orderOf q = 1 := by
          have hcop : Nat.Coprime (2 ^ k) (orderOf w) :=
            Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
          have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one hpow)
          rw [hcop.gcd_eq_one] at hd
          exact Nat.dvd_one.mp hd
        have hq1' : q = 1 := orderOf_eq_one_iff.mp hq1
        have : g * w * g⁻¹ = w := by
          have h2 : g * w * g⁻¹ = w * q := by rw [hqdef]; group
          rw [h2, hq1', mul_one]
        calc g * w = g * w * g⁻¹ * g := by group
          _ = w * g := by rw [this]
      have hmem := mem_oddCoreIn_of_mem_center (subnormal_of_mem_cComp hK) hwK hcen hodd
      rw [hO] at hmem
      exact Subgroup.mem_bot.mp hmem
    have hCp : IsPGroup 2 ↥C := by
      intro c
      obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (c : G)).ne'
      have h2a : 2 ^ a ∣ orderOf (c : G) := ⟨m, ham⟩
      have hord : orderOf ((c : G) ^ 2 ^ a) = m := by
        rw [orderOf_pow_of_dvd (by positivity) h2a, ham, Nat.mul_div_cancel_left _ (by positivity)]
      have h1 := hodd1 _ (C.pow_mem c.2 _) (hord ▸ hm)
      exact ⟨a, Subtype.ext (by simpa using h1)⟩
    exact CFSG.LieType.BorelTits.le_pCoreOf 2 hCK hnorm hCp

theorem a38_of_not_le_normalizer
    (h36 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A36Statement Y)
    (h38 : ∀ (Y : Type) [Group Y], SQTKHyp Y → A38Part3 Y) (hH : IsSQTKIn H)
    {L : Subgroup G} (hL : L ∈ cComp H) (hn : ¬ H ≤ Subgroup.normalizer (L : Set G)) :
    CFSG.IsQuasisimple (ModO2 L) ∧ A38Types (ModO2 L) := by
  have hGb : SQTKHyp (↥H ⧸ CFSG.pCore 2 ↥H) := SQTKHyp.of_sqtkGroup _ hH
  have hL' : L.subgroupOf H ∈ cComp (⊤ : Subgroup ↥H) := subgroupOf_mem_cComp hL
  have hLb : modO2Image H L ∈ cComp (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    modO2Image_mem_cComp hL
  obtain ⟨e⟩ := modO2_mulEquiv hL
  rcases (h38 _ hGb _ hLb).1 with hnorm | ⟨htypes, t, -, hcomm, -, -⟩
  ·
    exfalso
    apply hn
    intro h hh
    have hsolv : Group.IsSolvable ↥(CFSG.pCore 2 ↥H) := by
      have := (CFSG.pCore_isPGroup (G := ↥H) (p := 2)).isNilpotent
      infer_instance
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
    set h' : ↥H := ⟨h, hh⟩ with hh'
    have hconj : (L.subgroupOf H).map (MulAut.conj h').toMonoidHom = L.subgroupOf H := by
      refine (cComp_quotient_bijOn (CFSG.pCore 2 ↥H) hsolv).injOn
        (C2A3Orbits.conj_mem_cComp_top hL' h') hL' ?_
      show ((L.subgroupOf H).map (MulAut.conj h').toMonoidHom).map π = (L.subgroupOf H).map π
      rw [← C2A3Orbits.map_conj_map π (L.subgroupOf H) h']
      refine A38.map_conj_eq_iff.mpr ?_
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => hnorm.conj_mem x hx _, fun hx => ?_⟩
      have := hnorm.conj_mem _ hx (π h')⁻¹
      rwa [show (π h')⁻¹ * (π h' * x * (π h')⁻¹) * (π h')⁻¹⁻¹ = x by group] at this
    have h1 := (C2A3Orbits.mem_normalizer_map_subtype H (L.subgroupOf H) h').mpr
      (A38.map_conj_eq_iff.mp hconj)
    rwa [Subgroup.map_subgroupOf_eq_of_le (le_of_mem_cComp hL)] at h1
  · refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
      (A38.isQuasisimple_of_commuting_conj hGb hLb (h36 _ hGb _ hLb) hcomm), ?_⟩
    rcases htypes with ⟨n, h⟩ | ⟨n, h⟩ | h | ⟨p, hp, hp3, h⟩
    · exact Or.inl ⟨n, IsPSL.of_mulEquiv e.symm h⟩
    · exact Or.inr (Or.inl ⟨n, IsSz.of_mulEquiv e.symm h⟩)
    · exact Or.inr (Or.inr (Or.inl (IsSporadic.of_mulEquiv e.symm h)))
    · exact Or.inr (Or.inr (Or.inr ⟨p, hp, hp3, IsPSL.of_mulEquiv e.symm h⟩))

end CFSG.Quasithin.C48
