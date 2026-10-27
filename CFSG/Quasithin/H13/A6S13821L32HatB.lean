module

public import CFSG.Quasithin.H13.A6S13821L32HatKN
public import CFSG.Quasithin.H13.A6S13821L32HatBound

public section

namespace CFSG.Quasithin.H13.A6

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)

namespace L32HatStep

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem centralizer_inf_K_le {H K : Subgroup G} (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hP : IsPSL 3 2 1 (L32A.cStar K))
    (hTsylH : IsSylowTwoOf T H) :
    ∀ n ∈ centralizerMod (pCoreOf 2 K) H K, n ∈ K → n ∈ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨π, hπ, hker, -⟩ := exists_pi_sl3 hK hKn hTsylH hP
  intro n hn hnK
  have hcomm : ∀ u ∈ K, n * u * n⁻¹ * u⁻¹ ∈ pCoreOf 2 K := fun u hu => hn.2.2 u hu
  set kn : ↥K := ⟨n, hnK⟩ with hkn
  have hcen : π kn ∈ Subgroup.center SL3.S := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨u, rfl⟩ := hπ g
    have h1 : π (kn * u * kn⁻¹ * u⁻¹) = 1 := by
      refine (hker _).mpr ?_
      have e : ((kn * u * kn⁻¹ * u⁻¹ : ↥K) : G) = n * (u : G) * n⁻¹ * (u : G)⁻¹ := by
        simp [kn]
      rw [e]
      exact hcomm u u.2
    have h3 : π kn * π u * (π kn)⁻¹ * (π u)⁻¹ = 1 := by
      simpa [map_mul, map_inv] using h1
    calc π u * π kn = (π kn * π u * (π kn)⁻¹ * (π u)⁻¹)⁻¹ * (π kn * π u) := by group
      _ = π kn * π u := by rw [h3, inv_one, one_mul]
  have hkn1 : π kn = 1 := by
    have : π kn ∈ (⊥ : Subgroup SL3.S) := by
      rw [← L32HatSL3.center_S_eq_bot]
      exact hcen
    exact Subgroup.mem_bot.mp this
  exact (hker kn).mp hkn1

theorem mul_decomp_of_sup {K M : Subgroup G} (hM : M ≤ Subgroup.normalizer (K : Set G)) :
    ∀ x ∈ K ⊔ M, ∃ k ∈ K, ∃ m ∈ M, x = k * m := by
  let D : Subgroup G :=
    { carrier := {x | ∃ k ∈ K, ∃ m ∈ M, x = k * m}
      one_mem' := ⟨1, K.one_mem, 1, M.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨k1, hk1, m1, hm1, rfl⟩ ⟨k2, hk2, m2, hm2, rfl⟩
        refine ⟨k1 * (m1 * k2 * m1⁻¹), K.mul_mem hk1 ?_, m1 * m2, M.mul_mem hm1 hm2, by group⟩
        exact (Subgroup.mem_normalizer_iff.mp (hM hm1) k2).mp hk2
      inv_mem' := by
        rintro _ ⟨k, hk, m, hm, rfl⟩
        refine ⟨m⁻¹ * k⁻¹ * m, ?_, m⁻¹, M.inv_mem hm, by group⟩
        have := (Subgroup.mem_normalizer_iff.mp (hM (M.inv_mem hm)) k⁻¹).mp (K.inv_mem hk)
        simpa using this }
  have hsub : K ⊔ M ≤ D :=
    sup_le (fun k hk => ⟨k, hk, 1, M.one_mem, by simp⟩)
      (fun m hm => ⟨1, K.one_mem, m, hm, by simp⟩)
  intro x hx
  obtain ⟨k, hk, m, hm, rfl⟩ := hsub hx
  exact ⟨k, hk, m, hm, rfl⟩

theorem R_le_K_mul_Q {S : Setting4 G T L V}
    (h139 : Stmt13_3_9) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h1334 : Stmt13_3_4)
    (hS : S.Hyp138) (hhat : IsHatA6 L) {H K : Subgroup G} (hH : H ∈ S.Hz) (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hP : IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K))
    (hHK : H = K ⊔ (S.L1 ⊔ T)) :
    ∀ r ∈ pCoreOf 2 (S.L1 ⊔ T), ∃ k ∈ K, ∃ q ∈ pCoreOf 2 H, r = k * q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hL1H : S.L1 ⊔ T ≤ H := hH.1.1
  have hTH : T ≤ H := le_sup_right.trans hL1H
  have hTsylH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hP' : IsPSL 3 2 1 (L32A.cStar K) := IsPSL.of_mulEquiv (L32A.C.cStarEquiv K).symm hP
  have hdec := H_le_K_mul_N h139 h37 h38 h1334 hS hhat hH hK hKn hP hHK
  have hcentral := centralizer_inf_K_le hK hKn hP' hTsylH
  have hHN : H ≤ Subgroup.normalizer ((pCoreOf 2 K : Subgroup G) : Set G) :=
    hKn.trans (normalizer_le_normalizer_pCoreOf 2 K)
  have hNnorm : H ≤ Subgroup.normalizer
      ((centralizerMod (pCoreOf 2 K) H K : Subgroup G) : Set G) :=
    le_normalizer_centralizerMod hHN Subgroup.le_normalizer hKn
  have hNnorm' : ((centralizerMod (pCoreOf 2 K) H K).subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNnorm
  have hNH : centralizerMod (pCoreOf 2 K) H K ≤ H := centralizerMod_le_left _ _ _
  haveI hKH' : (K.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hKn
  set φ : ↥H →* ↥H ⧸ K.subgroupOf H := QuotientGroup.mk' (K.subgroupOf H) with hφ
  have hφK : ∀ k : ↥H, (k : G) ∈ K → φ k = 1 := fun k hk => by
    rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hk
  set R : Subgroup G := pCoreOf 2 (S.L1 ⊔ T) with hRdef
  have hRH : R ≤ H := (pCoreOf_le 2 _).trans hL1H
  have hN1 : S.L1 ⊔ T ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 (S.L1 ⊔ T))
  have hL1R : ∀ m ∈ S.L1 ⊔ T, ∀ x ∈ R, m * x * m⁻¹ ∈ R := fun m hm x hx =>
    (Subgroup.mem_normalizer_iff.mp (hN1 hm) x).mp hx
  set R' : Subgroup ↥H := R.subgroupOf H with hR'
  set Rb : Subgroup (↥H ⧸ K.subgroupOf H) := R'.map φ with hRb
  have hRb_norm : ∀ g : ↥H ⧸ K.subgroupOf H, ∀ y ∈ Rb, g * y * g⁻¹ ∈ Rb := by
    intro g y hy
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective (K.subgroupOf H) g
    obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨k, hk, m, hm, hhkm⟩ :=
      mul_decomp_of_sup (hL1H.trans hKn) (h : G) (by rw [← hHK]; exact h.2)
    have hkH : k ∈ H := hKH hk
    have hmH : m ∈ H := hL1H hm
    have hh : h = (⟨k, hkH⟩ : ↥H) * ⟨m, hmH⟩ := Subtype.ext (by simp [hhkm])
    have hφh : φ h = φ ⟨m, hmH⟩ := by
      rw [hh, map_mul, hφK ⟨k, hkH⟩ hk, one_mul]
    have hmem : (⟨m, hmH⟩ : ↥H) * r' * (⟨m, hmH⟩ : ↥H)⁻¹ ∈ R' := by
      rw [hR', Subgroup.mem_subgroupOf]
      have := hL1R m hm _ (Subgroup.mem_subgroupOf.mp hr')
      simpa using this
    rw [hφh, ← map_inv, ← map_mul, ← map_mul]
    exact Subgroup.mem_map_of_mem φ hmem
  haveI hRbn : Rb.Normal := ⟨fun y hy g => hRb_norm g y hy⟩
  set Ntil : Subgroup ↥H := ((centralizerMod (pCoreOf 2 K) H K).subgroupOf H) ⊓ Rb.comap φ with hNt
  haveI hNtn : Ntil.Normal := by
    rw [hNt]
    infer_instance
  have hNt2 : IsPGroup 2 ↥Ntil := by
    intro x
    obtain ⟨hxN, hxR⟩ := x.2
    obtain ⟨r', hr', hφr⟩ := Subgroup.mem_map.mp hxR
    have hr'R : (r' : G) ∈ R := Subgroup.mem_subgroupOf.mp hr'
    obtain ⟨a, ha⟩ := pCoreOf_isPGroup 2 (S.L1 ⊔ T) ⟨(r' : G), hr'R⟩
    have ha' : (r' : G) ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have ha'' : r' ^ 2 ^ a = 1 := Subtype.ext (by simpa using ha')
    have hpow : φ ((x : ↥H) ^ 2 ^ a) = 1 := by
      rw [map_pow, ← hφr, ← map_pow, ha'', map_one]
    have hKx : (((x : ↥H) ^ 2 ^ a : ↥H) : G) ∈ K := by
      have h1 := hpow
      rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      exact h1
    have hNx : (((x : ↥H) ^ 2 ^ a : ↥H) : G) ∈ centralizerMod (pCoreOf 2 K) H K := by
      have := (centralizerMod (pCoreOf 2 K) H K).pow_mem (Subgroup.mem_subgroupOf.mp hxN) (2 ^ a)
      simpa using this
    obtain ⟨b, hb⟩ := pCoreOf_isPGroup 2 K ⟨_, hcentral _ hNx hKx⟩
    have hb' : (((x : ↥H) ^ 2 ^ a : ↥H) : G) ^ 2 ^ b = 1 := by
      simpa using congrArg Subtype.val hb
    have hb'' : ((x : ↥H) ^ 2 ^ a) ^ 2 ^ b = 1 := Subtype.ext (by simpa using hb')
    have key : ((x : ↥H) ^ 2 ^ a) ^ 2 ^ b = (x : ↥H) ^ 2 ^ (a + b) := by
      rw [← pow_mul, ← pow_add]
    refine ⟨a + b, Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← key]
    exact hb''
  have hNt_le : Ntil ≤ CFSG.pCore 2 ↥H := le_sSup ⟨hNtn, hNt2⟩
  intro r hr
  have hrH : r ∈ H := hRH hr
  obtain ⟨k, hk, n, hn, hrkn⟩ := hdec r hrH
  refine ⟨k, hk, n, ?_, hrkn⟩
  have hnH : n ∈ H := hNH hn
  have hkH : k ∈ H := hKH hk
  have hnNt : (⟨n, hnH⟩ : ↥H) ∈ Ntil := by
    rw [hNt]
    refine ⟨Subgroup.mem_subgroupOf.mpr hn, ?_⟩
    have hφn : φ ⟨n, hnH⟩ = φ ⟨r, hrH⟩ := by
      have e : (⟨n, hnH⟩ : ↥H) = (⟨k, hkH⟩ : ↥H)⁻¹ * ⟨r, hrH⟩ :=
        Subtype.ext (by simp [hrkn])
      rw [e, map_mul, map_inv, hφK ⟨k, hkH⟩ hk, inv_one, one_mul]
    show φ ⟨n, hnH⟩ ∈ Rb
    rw [hφn]
    exact Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.mpr hr)
  have hmem := hNt_le hnNt
  show n ∈ (CFSG.pCore 2 ↥H).map H.subtype
  exact Subgroup.mem_map.mpr ⟨⟨n, hnH⟩, hmem, rfl⟩

theorem image_is_parabolic {H K M T : Subgroup G} (hK : K ∈ cComp H)
    {π : ↥K →* SL3.S} (hπ : Function.Surjective π)
    (hker : ∀ k : ↥K, π k = 1 ↔ (k : G) ∈ pCoreOf 2 K)
    (hD : (T.subgroupOf K).map π = SL3.P0) (hMK : M ≤ K) (hsolv : Group.IsSolvable ↥M)
    (hTM : ∀ t ∈ T, t ∈ K → t ∈ M) {c : G} (hcK : c ∈ K) (hcM : c ∈ M) (hc3 : c ^ 3 = 1)
    (hcO : c ∉ pCoreOf 2 K) :
    (M.subgroupOf K).map π = SL3.X1 ∨ (M.subgroupOf K).map π = SL3.X2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I : Subgroup SL3.S := (M.subgroupOf K).map π with hI
  have hP0I : SL3.P0 ≤ I := by
    rw [← hD]
    have hle : T.subgroupOf K ≤ M.subgroupOf K := by
      intro t ht
      exact Subgroup.mem_subgroupOf.mpr (hTM _ (Subgroup.mem_subgroupOf.mp ht) t.2)
    exact Subgroup.map_mono hle
  have hItop : I ≠ ⊤ := by
    intro htop
    have hKs : K ≤ M ⊔ pCoreOf 2 K := by
      intro k hk
      have hmem : π ⟨k, hk⟩ ∈ I := by
        rw [htop]
        exact Subgroup.mem_top _
      obtain ⟨m, hm, hmk⟩ := Subgroup.mem_map.mp hmem
      have h1 : π (m⁻¹ * ⟨k, hk⟩) = 1 := by
        rw [map_mul, map_inv, hmk, inv_mul_cancel]
      have h2 : ((m⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ pCoreOf 2 K := (hker _).mp h1
      have e : k = (m : G) * ((m⁻¹ * ⟨k, hk⟩ : ↥K) : G) := by simp
      rw [e]
      exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hm) h2
    haveI hNs : Group.IsSolvable ↥(pCoreOf 2 K) := by
      haveI := IsPGroup.isNilpotent (pCoreOf_isPGroup 2 K)
      infer_instance
    have hMN : M ≤ Subgroup.normalizer ((pCoreOf 2 K : Subgroup G) : Set G) :=
      hMK.trans (Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 K))
    haveI hsup : Group.IsSolvable ↥(pCoreOf 2 K ⊔ M) :=
      CFSG.Quasithin.C126.isSolvable_sup_of_le_normalizer' hMN hNs hsolv
    have hKsolv : Group.IsSolvable ↥K := by
      have hKs' : K ≤ pCoreOf 2 K ⊔ M := by
        rw [sup_comm]
        exact hKs
      exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hKs')
        (Subgroup.inclusion_injective hKs')
    exact not_isSolvable_of_mem_cComp hK hKsolv
  have hπc1 : π ⟨c, hcK⟩ ≠ 1 := fun h => hcO ((hker _).mp h)
  have hπc3 : (π ⟨c, hcK⟩) ^ 3 = 1 := by
    rw [← map_pow]
    have h3 : (⟨c, hcK⟩ : ↥K) ^ 3 = 1 := Subtype.ext hc3
    rw [h3, map_one]
  have hπcI : π ⟨c, hcK⟩ ∈ I := Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hcM)
  have hπcP0 : π ⟨c, hcK⟩ ∉ SL3.P0 := by
    intro hP0
    obtain ⟨k, hk⟩ := SL3.P0_sylow.1 ⟨π ⟨c, hcK⟩, hP0⟩
    have hk' : (π ⟨c, hcK⟩) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact hπc1 (eq_one_of_pow_three_pow_two hπc3 hk')
  rcases SL3.overgroups_SL3 I hP0I with h | h | h | h
  · exact absurd (h ▸ hπcI) hπcP0
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hItop

theorem K_inf_pCoreOf_le {H K : Subgroup G} (hKH : K ≤ H) (hHN : H ≤ Subgroup.normalizer
    ((pCoreOf 2 H : Subgroup G) : Set G)) :
    ∀ x ∈ K, x ∈ pCoreOf 2 H → x ∈ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : ∀ k ∈ K, ∀ x ∈ K ⊓ pCoreOf 2 H, k * x * k⁻¹ ∈ K ⊓ pCoreOf 2 H := by
    intro k hk x hx
    refine ⟨K.mul_mem (K.mul_mem hk hx.1) (K.inv_mem hk), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hHN (hKH hk)) x).mp hx.2
  have hn : ((K ⊓ pCoreOf 2 H).subgroupOf K).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have := hnorm (g : G) g.2 _ hn
    simpa using this
  have h2 : IsPGroup 2 ↥((K ⊓ pCoreOf 2 H).subgroupOf K) := by
    intro x
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 H ⟨((x : ↥K) : G), (Subgroup.mem_subgroupOf.mp x.2).2⟩
    refine ⟨k, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have hle : (K ⊓ pCoreOf 2 H).subgroupOf K ≤ CFSG.pCore 2 ↥K := le_sSup ⟨hn, h2⟩
  intro x hxK hxQ
  have hmem : (⟨x, hxK⟩ : ↥K) ∈ (K ⊓ pCoreOf 2 H).subgroupOf K :=
    Subgroup.mem_subgroupOf.mpr ⟨hxK, hxQ⟩
  have := Subgroup.mem_map_of_mem K.subtype (hle hmem)
  exact this

theorem relIndex_le_four {S : Setting4 G T L V}
    (h139 : Stmt13_3_9) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h1334 : Stmt13_3_4)
    (hS : S.Hyp138) (hhat : IsHatA6 L) {H K : Subgroup G} (hH : H ∈ S.Hz) (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hP : IsPSL 3 2 1 (↥K ⧸ CFSG.pCore 2 ↥K))
    (hHK : H = K ⊔ (S.L1 ⊔ T)) :
    (pCoreOf 2 H).relIndex (pCoreOf 2 (S.L1 ⊔ T)) ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hL1H : S.L1 ⊔ T ≤ H := hH.1.1
  have hTH : T ≤ H := le_sup_right.trans hL1H
  have hTsylH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.h13.sylow hTH
  have hP' : IsPSL 3 2 1 (L32A.cStar K) := IsPSL.of_mulEquiv (L32A.C.cStarEquiv K).symm hP
  obtain ⟨π, hπ, hker, hD⟩ := exists_pi_sl3 hK hKn hTsylH hP'
  have hL0K : l0 L ≤ K := S.l0_le_of_hat h139 h37 h38 hhat hH hK hKn hP
  have hO2KH : pCoreOf 2 K ≤ pCoreOf 2 H :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)
  set Q : Subgroup G := pCoreOf 2 H with hQdef
  set R : Subgroup G := pCoreOf 2 (S.L1 ⊔ T) with hRdef
  have hHNQ : H ≤ Subgroup.normalizer (Q : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 H)
  have hQ2 : IsPGroup 2 ↥Q := pCoreOf_isPGroup 2 H
  have hKQ : ∀ k ∈ K, ∀ q ∈ Q, k * q * k⁻¹ ∈ Q := fun k hk q hq =>
    (Subgroup.mem_normalizer_iff.mp (hHNQ (hKH hk)) q).mp hq
  have hK_inf : ∀ x ∈ K, x ∈ Q → x ∈ pCoreOf 2 K := K_inf_pCoreOf_le hKH hHNQ
  have hRH : R ≤ H := (pCoreOf_le 2 _).trans hL1H
  have hα := R_le_K_mul_Q h139 h37 h38 h1334 hS hhat hH hK hKn hP hHK
  have hN1 : S.L1 ⊔ T ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_pCoreOf 2 (S.L1 ⊔ T))
  have hL1R : ∀ m ∈ S.L1 ⊔ T, ∀ x ∈ R, m * x * m⁻¹ ∈ R := fun m hm x hx =>
    (Subgroup.mem_normalizer_iff.mp (hN1 hm) x).mp hx
  have hpi_eq : ∀ (k k' : ↥K) (q q' : G), q ∈ Q → q' ∈ Q → (k : G) * q = (k' : G) * q' →
      π k = π k' := by
    intro k k' q q' hq hq' h
    have e : ((k⁻¹ * k' : ↥K) : G) = q * q'⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      have h' : (k' : G) = (k : G) * q * q'⁻¹ := by
        rw [h]
        group
      rw [h']
      group
    have hmemK : ((k⁻¹ * k' : ↥K) : G) ∈ K := (k⁻¹ * k').2
    have hmemQ : ((k⁻¹ * k' : ↥K) : G) ∈ Q := by
      rw [e]
      exact Q.mul_mem hq (Q.inv_mem hq')
    have h1 : π (k⁻¹ * k') = 1 := (hker _).mpr (hK_inf _ hmemK hmemQ)
    rw [map_mul, map_inv] at h1
    exact inv_mul_eq_one.mp h1
  have hα' : ∀ r ∈ R, ∃ k : ↥K, ∃ q ∈ Q, r = (k : G) * q := by
    intro r hr
    obtain ⟨k, hk, q, hq, h⟩ := hα r hr
    exact ⟨⟨k, hk⟩, q, hq, h⟩
  let Fv : ↥R → SL3.S := fun r => π (Classical.choose (hα' r.1 r.2))
  have hFv_spec : ∀ r : ↥R, ∃ q ∈ Q, (r : G) = ((Classical.choose (hα' r.1 r.2) : ↥K) : G) * q :=
    fun r => Classical.choose_spec (hα' r.1 r.2)
  have hdecomp : ∀ r : ↥R, ∃ k : ↥K, ∃ q ∈ Q, (r : G) = (k : G) * q ∧ Fv r = π k := by
    intro r
    obtain ⟨q₀, hq₀, h₀⟩ := hFv_spec r
    exact ⟨_, q₀, hq₀, h₀, rfl⟩
  have hFv_eq : ∀ (r : ↥R) (k : ↥K) (q : G), q ∈ Q → (r : G) = (k : G) * q → Fv r = π k := by
    intro r k q hq h
    obtain ⟨q₀, hq₀, h₀⟩ := hFv_spec r
    exact hpi_eq _ k q₀ q hq₀ hq (h₀.symm.trans h)
  have hFv_one : Fv 1 = 1 := by
    have := hFv_eq 1 1 1 Q.one_mem (by simp)
    rw [this, map_one]
  have hFv_mul : ∀ a b : ↥R, Fv (a * b) = Fv a * Fv b := by
    intro a b
    obtain ⟨q₁, hq₁, h₁⟩ := hFv_spec a
    obtain ⟨q₂, hq₂, h₂⟩ := hFv_spec b
    set k₁ := Classical.choose (hα' a.1 a.2)
    set k₂ := Classical.choose (hα' b.1 b.2)
    have hq₁' : (k₂ : G)⁻¹ * q₁ * (k₂ : G) ∈ Q := by
      have := hKQ ((k₂ : G)⁻¹) (K.inv_mem k₂.2) q₁ hq₁
      simpa [mul_assoc] using this
    have hprod : ((a * b : ↥R) : G) = ((k₁ * k₂ : ↥K) : G) * (((k₂ : G)⁻¹ * q₁ * (k₂ : G)) * q₂) := by
      simp only [Subgroup.coe_mul]
      rw [h₁, h₂]
      group
    rw [hFv_eq (a * b) (k₁ * k₂) _ (Q.mul_mem hq₁' hq₂) hprod, map_mul]
  let F : ↥R →* SL3.S := { toFun := Fv, map_one' := hFv_one, map_mul' := hFv_mul }
  have hF : ∀ r : ↥R, F r = Fv r := fun r => rfl
  have hker_F : F.ker = Q.subgroupOf R := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hF]
    constructor
    · intro h
      obtain ⟨q₀, hq₀, h₀⟩ := hFv_spec r
      have h' : π (Classical.choose (hα' r.1 r.2)) = 1 := h
      have hk : ((Classical.choose (hα' r.1 r.2) : ↥K) : G) ∈ pCoreOf 2 K := (hker _).mp h'
      rw [h₀]
      exact Q.mul_mem (hO2KH hk) hq₀
    · intro hr
      have := hFv_eq r 1 r hr (by simp)
      rw [this, map_one]
  have hidx : (Q.subgroupOf R).index = Nat.card F.range := by
    rw [← hker_F, Subgroup.index_ker]
  show (Q.subgroupOf R).index ≤ 4
  rw [hidx]
  haveI hQsolv : Group.IsSolvable ↥Q := by
    haveI := IsPGroup.isNilpotent hQ2
    infer_instance
  haveI hLsolv : Group.IsSolvable ↥(S.L1 ⊔ T) := S.isSolvable_L1T h1334 hS
  set A : Subgroup G := (S.L1 ⊔ T) ⊔ Q with hAdef
  have hAsolv : Group.IsSolvable ↥A := by
    have hTN : S.L1 ⊔ T ≤ Subgroup.normalizer (Q : Set G) := hL1H.trans hHNQ
    have := CFSG.Quasithin.C126.isSolvable_sup_of_le_normalizer' hTN hQsolv hLsolv
    rw [hAdef, sup_comm]
    exact this
  have hA_L1 : ∀ m ∈ S.L1, m ∈ A := fun m hm => Subgroup.mem_sup_left (Subgroup.mem_sup_left hm)
  have hA_L1T : ∀ m ∈ S.L1 ⊔ T, m ∈ A := fun m hm => Subgroup.mem_sup_left hm
  have hA_Q : ∀ q ∈ Q, q ∈ A := fun q hq => Subgroup.mem_sup_right hq
  have hA_T : ∀ t ∈ T, t ∈ A := fun t ht => hA_L1T t (Subgroup.mem_sup_right ht)
  have hA_R : R ≤ A := fun r hr => hA_L1T r (pCoreOf_le 2 (S.L1 ⊔ T) hr)
  obtain ⟨c, hcl0, hc3, hcO, -⟩ := l0_decomp hhat
  have hc1 : c ≠ 1 := fun h1 => hcO (h1 ▸ Subgroup.one_mem _)
  have hcK : c ∈ K := hL0K hcl0
  have hcOK : c ∉ pCoreOf 2 K := by
    intro h
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 K ⟨c, h⟩
    have hk' : c ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact hc1 (eq_one_of_pow_three_pow_two hc3 hk')
  have hPA : (((K ⊓ A).subgroupOf K).map π) = SL3.X1 ∨ (((K ⊓ A).subgroupOf K).map π) = SL3.X2 := by
    haveI : Group.IsSolvable ↥(K ⊓ A) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion (inf_le_right : K ⊓ A ≤ A))
        (Subgroup.inclusion_injective _)
    exact image_is_parabolic hK hπ hker hD inf_le_left inferInstance
      (fun t ht htK => Subgroup.mem_inf.mpr ⟨htK, hA_T t ht⟩) hcK
      (Subgroup.mem_inf.mpr ⟨hcK, hA_L1 c (S.l0_le_L1 hcl0)⟩) hc3 hcOK
  have hPL : (((K ⊓ (S.L1 ⊔ T)).subgroupOf K).map π) = SL3.X1 ∨
      (((K ⊓ (S.L1 ⊔ T)).subgroupOf K).map π) = SL3.X2 := by
    haveI : Group.IsSolvable ↥(K ⊓ (S.L1 ⊔ T)) :=
      Group.isSolvable_of_isSolvable_injective
        (f := Subgroup.inclusion (inf_le_right : K ⊓ (S.L1 ⊔ T) ≤ S.L1 ⊔ T))
        (Subgroup.inclusion_injective _)
    exact image_is_parabolic hK hπ hker hD inf_le_left inferInstance
      (fun t ht htK => Subgroup.mem_inf.mpr ⟨htK, Subgroup.mem_sup_right ht⟩)
      hcK (Subgroup.mem_inf.mpr ⟨hcK, Subgroup.mem_sup_left (S.l0_le_L1 hcl0)⟩) hc3 hcOK
  have hPLPA : (((K ⊓ (S.L1 ⊔ T)).subgroupOf K).map π) = (((K ⊓ A).subgroupOf K).map π) := by
    have hle : ((K ⊓ (S.L1 ⊔ T)).subgroupOf K).map π ≤ ((K ⊓ A).subgroupOf K).map π := by
      apply Subgroup.map_mono
      intro x hx
      obtain ⟨hxK, hxL⟩ := Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hxK, hA_L1T _ hxL⟩)
    rcases hPL with h1 | h1 <;> rcases hPA with h2 | h2
    · rw [h1, h2]
    · exfalso
      rw [h1, h2] at hle
      exact X1_not_le_X2 hle
    · exfalso
      rw [h1, h2] at hle
      exact X2_not_le_X1 hle
    · rw [h1, h2]
  have hYPA : F.range ≤ ((K ⊓ A).subgroupOf K).map π := by
    rintro _ ⟨r, rfl⟩
    obtain ⟨q₀, hq₀, h₀⟩ := hFv_spec r
    obtain ⟨k₀, q₀, hq₀, h₀, hFr⟩ := hdecomp r
    have hFr' : F r = π k₀ := hFr
    have hk₀A : ((k₀ : ↥K) : G) ∈ A := by
      have e : ((k₀ : ↥K) : G) = (r : G) * q₀⁻¹ := by
        rw [h₀]
        group
      rw [e]
      exact A.mul_mem (hA_R r.2) (hA_Q _ (Q.inv_mem hq₀))
    rw [hFr']
    exact Subgroup.mem_map_of_mem π
      (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨k₀.2, hk₀A⟩))
  have hHQconj : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q := fun h hh q hq =>
    (Subgroup.mem_normalizer_iff.mp (hHNQ hh) q).mp hq
  have hconj : ∀ a : ↥K, (a : G) ∈ S.L1 ⊔ T → ∀ r : ↥R,
      ∃ r' : ↥R, F r' = π a * F r * (π a)⁻¹ := by
    intro a ha r
    have hr' : (a : G) * (r : G) * (a : G)⁻¹ ∈ R := hL1R a ha r r.2
    obtain ⟨k, q₀, hq₀, h₀, hFr⟩ := hdecomp r
    have haH : (a : G) ∈ H := hL1H ha
    have hak : (a : G) * ((k : ↥K) : G) * (a : G)⁻¹ ∈ K :=
      K.mul_mem (K.mul_mem a.2 k.2) (K.inv_mem a.2)
    have haq : (a : G) * q₀ * (a : G)⁻¹ ∈ Q := hHQconj (a : G) haH q₀ hq₀
    refine ⟨⟨(a : G) * (r : G) * (a : G)⁻¹, hr'⟩, ?_⟩
    have hfeq : F ⟨(a : G) * (r : G) * (a : G)⁻¹, hr'⟩ =
        π ⟨(a : G) * ((k : ↥K) : G) * (a : G)⁻¹, hak⟩ := by
      apply hFv_eq ⟨(a : G) * (r : G) * (a : G)⁻¹, hr'⟩ ⟨(a : G) * ((k : ↥K) : G) * (a : G)⁻¹, hak⟩
        ((a : G) * q₀ * (a : G)⁻¹) haq
      have e3 : (a : G) * (r : G) * (a : G)⁻¹ =
          ((a : G) * ((k : ↥K) : G) * (a : G)⁻¹) * ((a : G) * q₀ * (a : G)⁻¹) := by
        rw [h₀]
        group
      exact e3
    have hFr' : F r = π k := hFr
    rw [hfeq, hFr']
    have e2 : (⟨(a : G) * ((k : ↥K) : G) * (a : G)⁻¹, hak⟩ : ↥K) = a * k * a⁻¹ :=
      Subtype.ext (by simp)
    rw [e2, map_mul, map_mul, map_inv]
  have hYn : ∀ x ∈ ((K ⊓ A).subgroupOf K).map π, ∀ y ∈ F.range, x * y * x⁻¹ ∈ F.range := by
    intro x hx y hy
    rw [← hPLPA] at hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨r, rfl⟩ := MonoidHom.mem_range.mp hy
    obtain ⟨r', hr'⟩ := hconj a (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp ha)).2 r
    exact ⟨r', hr'⟩
  have hY2 : IsPGroup 2 ↥F.range := by
    intro y
    obtain ⟨r, hr⟩ := MonoidHom.mem_range.mp y.2
    obtain ⟨a, ha⟩ := pCoreOf_isPGroup 2 (S.L1 ⊔ T) r
    refine ⟨a, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, Subgroup.coe_one, ← hr, ← map_pow, ha, map_one]
  exact card_le_four_of_normal hPA hYPA hYn hY2



end L32HatStep

end CFSG.Quasithin.H13.A6
