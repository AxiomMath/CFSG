module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7QL
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7QN
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem5C
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem7Q

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

theorem iterate_odd_eq627 {α : Type*} {σ : α → α} (hσ : ∀ c, σ (σ c) = c) (j : ℕ) (c : α) :
    σ^[2 * j + 1] c = σ c := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, Function.iterate_add_apply]
    show σ^[2 * j + 1] (σ (σ c)) = σ c
    rw [hσ, ih]

theorem Hyp6Sec2.mem_centralizer_V_of_odd627 (h : Hyp6Sec2 G T M L V) {t : G} (htT : t ∈ T)
    (ht : IsInvolutoryFieldAut L t) {y : G} (hyV : y ∈ Subgroup.normalizer (V : Set G))
    (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyU : y ∈ Subgroup.centralizer ((V ⊓ Subgroup.centralizer ({t} : Set G) : Subgroup G) :
      Set G)) {m : ℕ} (hm : Odd m) (hym : y ^ m = 1) :
    y ∈ Subgroup.centralizer (V : Set G) := by
  obtain ⟨u₁, u₂, hu₁, hu₂, hdet⟩ := h.toHyp611Nat.exists_basis_fix htT ht
  set yy : Subgroup.normalizer (V : Set G) := ⟨y, hyV⟩ with hyy
  have h1 := h.toHyp611Nat.conj_eq_of_fix htT hyV hyU hu₁
  have h2 := h.toHyp611Nat.conj_eq_of_fix htT hyV hyU hu₂
  obtain ⟨σ, hσ⟩ := h.data.exists_semilinear yy hyL
  have hpow : ∀ (k : ℕ) (c : h.data.K), h.data.conj (yy ^ k) (c • u₁) = σ^[k] c • u₁ := by
    intro k
    induction k with
    | zero => intro c; rw [pow_zero, h.conj_one_ch625]; rfl
    | succ k ih =>
      intro c
      rw [pow_succ, h.data.conj_mul, hσ, h1, ih, Function.iterate_succ_apply]
  have hσ1 : ∀ c, σ c = c := by
    rcases ringAut_ch625 h.card_K_ch625 σ with hs | hs
    · exact hs
    · exfalso
      obtain ⟨ω, hω0, hω1⟩ := exists_ne_zero_ne_one_ch625 h.card_K_ch625
      have hyym : yy ^ m = 1 := Subtype.ext (by simpa using hym)
      have h3 := hpow m ω
      rw [hyym, h.conj_one_ch625] at h3
      have hu0 : u₁ ≠ 0 := by
        intro h0
        apply hdet
        simp [h0, det2]
      have h4 : ω = σ^[m] ω := by
        by_contra hne
        apply hu0
        have h5 : (ω - σ^[m] ω) • u₁ = 0 := by rw [sub_smul, h3, sub_self]
        exact (smul_eq_zero.mp h5).resolve_left (sub_ne_zero.mpr hne)
      obtain ⟨j, rfl⟩ := hm
      rw [iterate_odd_eq627 (fun c => by rw [hs, hs, sq_sq_ch625 h.card_K_ch625]) j ω, hs] at h4
      apply hω1
      have h5 : ω * (ω - 1) = 0 := by linear_combination -h4
      rcases mul_eq_zero.mp h5 with h6 | h6
      · exact absurd h6 hω0
      · exact sub_eq_zero.mp h6
  apply h.data.mem_centralizer_of_conj_eq yy
  intro w
  rw [eq_add_of_det2_ne_zero hdet w, map_add, hσ, hσ, hσ1, hσ1, h1, h2]

theorem card_eq_four_of_sylow627 {X : Type*} [Group X] [Finite X] {S K : Subgroup X}
    (hS : IsSylowTwoOf S K) (hK : Nat.card K = 60) : Nat.card S = 4 := by
  obtain ⟨hSK, hS2, hidx⟩ := hS
  obtain ⟨k, hk⟩ := hS2.exists_card_eq
  have hmul := (S.subgroupOf K).index_mul_card
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSK).toEquiv, hk, hK] at hmul
  have hk5 : k ≤ 5 := by
    by_contra hcon
    have : 2 ^ 6 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h0 : (S.subgroupOf K).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have : 2 ^ k ≤ 60 := by
      rw [← hmul]
      exact Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h0)
    omega
  rw [hk]
  interval_cases k <;> omega

theorem res627Q_of_L24 (hM : Res627QL24) : Res627Q := by
  intro G _ _ T M L V h t A D g ht hf U H UH R LU B a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12
    a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31 a32 a33 a34
    a35 a36 a37
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUHc : ∀ a ∈ UH, ∀ b ∈ UH, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm a9 ha hb
  have hnorm : (U.subgroupOf UH).Normal := by
    refine ⟨fun x hx y => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have e : ((y * x * y⁻¹ : ↥UH) : G) = (x : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hUHc _ y.2 _ x.2, mul_inv_cancel_right]
    rw [e]
    exact hx
  have hcomm : CommModCh611 UH U := ⟨fun a ha b hb => by
    rw [hUHc a ha b hb, mul_inv_cancel_right, mul_inv_cancel]
    exact U.one_mem⟩
  obtain ⟨K, hOK, hKH, hAK, hHK, hDK, hnat, hsum⟩ := hM G T M L V h t A D g ht hf a1 a2 a3 a4 a5
    a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 a24 a25 a26 a27 a28 a29
    a30 a31 a32 a33 a34 a35 a36 a37
  have hUUH : U ≤ UH := a13.1
  have hHUH : H ≤ Subgroup.normalizer (UH : Set G) := a13.2.2.1
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := a13.2.2.2.1
  have hO2t := a13.2.2.2.2.2
  set Q := ↥UH ⧸ U.subgroupOf UH with hQdef
  have : Finite (MulAut Q) :=
    Finite.of_injective (fun g : MulAut Q => (g : Q → Q)) DFunLike.coe_injective
  have hDL : D ≤ L := a31.trans ((oTwoUpper_le _).trans inf_le_left)
  have hDNU : D ≤ Subgroup.normalizer (U : Set G) :=
    a31.trans ((oTwoUpper_le _).trans inf_le_right)
  have hDNV : D ≤ Subgroup.normalizer (V : Set G) := hDL.trans h.toHyp611.L_le_normalizer
  have hDNH : D ≤ Subgroup.normalizer (H : Set G) := fun d hd =>
    mem_normalizer_centralizer_ch62 (hDNU hd)
  have hDNUH : D ≤ Subgroup.normalizer (UH : Set G) := fun d hd =>
    mem_normalizer_conjClosure_ch62 (hDNV hd) (hDNH hd)
  have hD3 : ∀ d ∈ D, d ^ 3 = 1 := by
    intro d hd
    have := Subgroup.orderOf_dvd_natCard D hd
    rw [a32] at this
    exact orderOf_dvd_iff_pow_eq_one.mp this
  set HD := H ⊔ D with hHDdef
  have hHDUH : HD ≤ Subgroup.normalizer (UH : Set G) := sup_le hHUH hDNUH
  have hHDU : HD ≤ Subgroup.normalizer (U : Set G) := sup_le hHU hDNU
  set ρ := actQuot UH U H hHUH hHU with hρ
  set ρ' := actQuot UH U HD hHDUH hHDU with hρ'
  set Gm := ρ.range with hGm
  have hρρ' : ∀ (x : G) (hx : x ∈ H), ρ ⟨x, hx⟩ = ρ' ⟨x, (le_sup_left : H ≤ HD) hx⟩ :=
    fun x hx => rfl
  have hconjρ : ∀ (y : G) (hy : y ∈ HD) (x : G) (hx : x ∈ H) (hyx : y * x * y⁻¹ ∈ H),
      ρ' ⟨y, hy⟩ * ρ ⟨x, hx⟩ * (ρ' ⟨y, hy⟩)⁻¹ = ρ ⟨y * x * y⁻¹, hyx⟩ := by
    intro y hy x hx hyx
    rw [hρρ' x hx, hρρ' _ hyx, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hHDNH : HD ≤ Subgroup.normalizer (H : Set G) := sup_le Subgroup.le_normalizer hDNH
  set Ks := (K.subgroupOf H).map ρ with hKs
  have hnat' : BinaryNaturalSL Ks (commV Ks) ⊥ 2 2 := hnat
  have hsum' : IsIntDirect (commV Ks) (fixV Ks) ⊤ := hsum
  obtain ⟨D₀⟩ := natData627_of hnat'
  have hKsGm : Ks ≤ Gm := Subgroup.map_le_range _ _
  have hKsN : ∀ x ∈ Gm, x ∈ Subgroup.normalizer (Ks : Set (MulAut Q)) := by
    rintro _ ⟨⟨x, hx⟩, rfl⟩
    refine mem_normalizer_of_conj_mem627 ?_
    rintro _ ⟨⟨k, hkH⟩, hkK, rfl⟩
    have hkK' : k ∈ K := hkK
    have hxk : x * k * x⁻¹ ∈ H := H.mul_mem (H.mul_mem hx hkH) (H.inv_mem hx)
    refine ⟨⟨x * k * x⁻¹, hxk⟩, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp (hHK hx) k).mp hkK'
    · rw [← map_inv, ← map_mul, ← map_mul]
      rfl
  have hDKs : ∀ (d : G) (hd : d ∈ D), ρ' ⟨d, (le_sup_right : D ≤ HD) hd⟩ ∈
      Subgroup.normalizer (Ks : Set (MulAut Q)) := by
    intro d hd
    refine mem_normalizer_of_conj_mem627 ?_
    rintro _ ⟨⟨k, hkH⟩, hkK, rfl⟩
    have hkK' : k ∈ K := hkK
    have hdk : d * k * d⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (hDNH hd) k).mp hkH
    rw [hconjρ d _ k hkH hdk]
    exact ⟨⟨d * k * d⁻¹, hdk⟩, (Subgroup.mem_normalizer_iff.mp (hDK hd) k).mp hkK', rfl⟩
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.toHyp611.toHyp5_0_1.T_le_normalizer
  have hQeq : ch6Q T V = pCoreOf 2 (L ⊔ T) := h.toHyp611.centralizer_eq
  have hO2L : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans le_sup_left) (sup_le ?_ ?_)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
    · exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L
    · exact hTL.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)
  have htU : ∀ u ∈ U, u * t = t * u := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mp hu.2
  have hdtQ : ∀ d ∈ D, d * t * d⁻¹ * t⁻¹ ∈ ch6Q T V := by
    intro d hd
    have hdL : d ∈ L := hDL hd
    have hcL : d * t * d⁻¹ * t⁻¹ ∈ L := by
      have h1 : t * d⁻¹ * t⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (hTL ht) _).mp (L.inv_mem hdL)
      have e : d * t * d⁻¹ * t⁻¹ = d * (t * d⁻¹ * t⁻¹) := by group
      rw [e]
      exact L.mul_mem hdL h1
    have hcU : d * t * d⁻¹ * t⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu' : d⁻¹ * u * d ∈ U := by
        simpa using (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem
          (hDNU hd)) u).mp hu
      have h1 := htU u hu
      have h2 := htU _ hu'
      calc u * (d * t * d⁻¹ * t⁻¹) = d * ((d⁻¹ * u * d) * t) * d⁻¹ * t⁻¹ := by group
        _ = d * (t * (d⁻¹ * u * d)) * d⁻¹ * t⁻¹ := by rw [h2]
        _ = d * t * d⁻¹ * (u * t⁻¹) := by group
        _ = d * t * d⁻¹ * (t⁻¹ * u) := by
            congr 1
            calc u * t⁻¹ = t⁻¹ * (t * u) * t⁻¹ := by group
              _ = t⁻¹ * (u * t) * t⁻¹ := by rw [h1]
              _ = t⁻¹ * u := by group
        _ = d * t * d⁻¹ * t⁻¹ * u := by group
    have hcV := h.toHyp611Nat.mem_centralizer_V_of_U ht hf hcL hcU
    rw [hQeq]
    exact hO2L (h.toHyp611.toHyp5_0_1.inf_centralizer_le h.toHyp611.L_le_normalizer
      h.toHyp611.module.2.2 ⟨hcL, hcV⟩)
  have hDR : ∀ d ∈ D, d ∈ Subgroup.normalizer (R : Set G) := by
    intro d hd
    have hdQ : d ∈ Subgroup.normalizer (ch6Q T V : Set G) := by
      rw [hQeq]
      exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)
        ((le_sup_left : L ≤ L ⊔ T) (hDL hd))
    have hQmap : (ch6Q T V).map (MulAut.conj d).toMonoidHom = ch6Q T V :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hdQ
    have hle : R.map (MulAut.conj d).toMonoidHom ≤ R := by
      rw [Subgroup.map_sup, hQmap]
      refine sup_le le_sup_left ?_
      rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
      have e : (MulAut.conj d).toMonoidHom t = (d * t * d⁻¹ * t⁻¹) * t := by
        simp [MulAut.conj_apply]
      rw [e]
      exact R.mul_mem ((le_sup_left : ch6Q T V ≤ R) (hdtQ d hd))
        ((le_sup_right : Subgroup.zpowers t ≤ R) (Subgroup.mem_zpowers t))
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj d).injective]))
  set Rs := (R.subgroupOf H).map ρ with hRs
  have hRsyl : IsSylowTwoOf Rs Gm := by
    refine ⟨Subgroup.map_le_range _ _, ?_, ?_⟩
    · have hR2 : IsPGroup 2 (R.subgroupOf H) := by
        intro x
        obtain ⟨k, hk⟩ := a3.2.1 ⟨(x : ↥H), x.2⟩
        exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hk))⟩
      exact hR2.map ρ
    · intro h2
      apply a3.2.2
      have e : Rs.relIndex Gm = ((R.subgroupOf H) ⊔ ρ.ker).index := by
        rw [hRs, hGm, MonoidHom.range_eq_map, Subgroup.relIndex_map_map, top_sup_eq,
          Subgroup.relIndex_top_right]
      have h3 : 2 ∣ ((R.subgroupOf H) ⊔ ρ.ker).index := e ▸ h2
      exact h3.trans (Subgroup.index_dvd_of_le le_sup_left)
  have hRsGm : Rs ≤ Gm := hRsyl.1
  have hKsnorm : (Ks.subgroupOf Gm).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKsGm]
    exact fun x hx => hKsN x hx
  have hSsyl : IsSylowTwoOf (Rs ⊓ Ks) Ks :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hRsyl hKsGm hKsnorm.isSubnormal
  have hS4 : Nat.card ↥(Rs ⊓ Ks) = 4 := card_eq_four_of_sylow627 hSsyl D₀.card_Ks
  have : Finite ↥(Rs ⊓ Ks) := Nat.finite_of_card_ne_zero (by rw [hS4]; norm_num)
  obtain ⟨D', hS⟩ := D₀.exists_sylow_coords (inf_le_right : Rs ⊓ Ks ≤ Ks) hS4
  have hRsylH : IsSylowTwoOf R H := ⟨a3.1, a3.2.1, a3.2.2⟩
  have hOR : pCoreOf 2 H ≤ R := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hRsylH
  have hRpre : ∀ (x : G) (hx : x ∈ H), ρ ⟨x, hx⟩ ∈ Rs → x ∈ R := by
    intro x hx hxR
    obtain ⟨⟨r, hrH⟩, hrR, hre⟩ := hxR
    have hrR' : r ∈ R := hrR
    have h1 : ρ ((⟨r, hrH⟩ : ↥H)⁻¹ * ⟨x, hx⟩) = 1 := by
      rw [map_mul, map_inv, hre, inv_mul_cancel]
    have h2 := (mem_centralizerMod_iff_actQuot' (hKU := hHUH) (hKZ := hHU) _).mpr h1
    rw [a12] at h2
    have h3 := R.mul_mem hrR' (hOR h2)
    simpa using h3
  have hU4 : Nat.card U = 4 := h.toHyp611Nat.card_fix_of_fieldAut ht hf
  have hU1 : U ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hU4
    omega
  have hVUH : V ≤ UH := a26 ▸ le_sup_left
  by_cases hinner : ∀ r ∈ Rs, ∃ k ∈ Ks, ∀ x ∈ Ks, r * x * r⁻¹ = k * x * k⁻¹
  ·
    obtain ⟨y, hyK, hyS, hy3, hyfpf⟩ := D'.exists_fpf627 (inf_le_right : Rs ⊓ Ks ≤ Ks) hS
    have hyR : y ∈ Subgroup.normalizer (Rs : Set (MulAut Q)) :=
      mem_normalizer_of_inner627 hKsGm hRsGm hRsyl.2.1
        (fun P hP hRP hPG => hRsyl.eq_of_le hRP hPG hP)
        (fun k hk hc => D₀.eq_one_of_central627 hk hc) hinner hyK hyS
    obtain ⟨⟨y₁, hy₁H⟩, hy₁K, hy₁ρ⟩ := hyK
    have hy₁K' : y₁ ∈ K := hy₁K
    have hy₁R : y₁ ∈ Subgroup.normalizer (R : Set G) := by
      refine mem_normalizer_of_conj_mem627 (S := R) fun r hr => ?_
      have hrH : r ∈ H := a3.1 hr
      have hyr : y₁ * r * y₁⁻¹ ∈ H := H.mul_mem (H.mul_mem hy₁H hrH) (H.inv_mem hy₁H)
      refine hRpre _ hyr ?_
      have e : ρ ⟨y₁ * r * y₁⁻¹, hyr⟩ = y * ρ ⟨r, hrH⟩ * y⁻¹ := by
        rw [← hy₁ρ, ← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e]
      exact (Subgroup.mem_normalizer_iff.mp hyR _).mp ⟨⟨r, hrH⟩, hr, rfl⟩
    obtain ⟨a, m, hmodd, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y₁).ne'
    set y₂ := y₁ ^ 2 ^ a with hy₂
    have hy₂m : y₂ ^ m = 1 := by rw [hy₂, ← pow_mul, ← hord, pow_orderOf_eq_one]
    have hy₂H : y₂ ∈ H := H.pow_mem hy₁H _
    have hy₂R : y₂ ∈ Subgroup.normalizer (R : Set G) := Subgroup.pow_mem _ hy₁R _
    have hy₂M : y₂ ∈ M := a5 (a4 hy₂R)
    have hy₂MV : y₂ ∈ ch6MV M V := h.toHyp611Nat.normalizer_le hU1 inf_le_left ⟨hy₂M, hHU hy₂H⟩
    have hy₂C : y₂ ∈ Subgroup.centralizer (V : Set G) :=
      h.mem_centralizer_V_of_odd627 ht hf hy₂MV.2 (h.normal hy₂M) hy₂H hmodd hy₂m
    have hρy₂ : ρ ⟨y₂, hy₂H⟩ = y ^ 2 ^ a := by
      rw [← hy₁ρ, ← map_pow]
      rfl
    have hy4 : ∀ j : ℕ, y ^ 4 ^ j = y := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ, pow_mul, ih, show y ^ 4 = y ^ 3 * y by rw [pow_succ], hy3, one_mul]
    have hy₂Ks : y ^ 2 ^ a ∈ Ks := Ks.pow_mem ⟨⟨y₁, hy₁H⟩, hy₁K, hy₁ρ⟩ _
    have hfpf₂ : ∀ v, (y ^ 2 ^ a) (D'.ψ (Multiplicative.ofAdd v)) =
        D'.ψ (Multiplicative.ofAdd v) → v = 0 := by
      intro v hv
      apply hyfpf v
      have hpowfix : ∀ n : ℕ, ((y ^ 2 ^ a) ^ n) (D'.ψ (Multiplicative.ofAdd v)) =
          D'.ψ (Multiplicative.ofAdd v) := by
        intro n
        induction n with
        | zero => rfl
        | succ n ih => rw [pow_succ, MulAut.mul_apply, hv, ih]
      have e : y = (y ^ 2 ^ a) ^ 2 ^ a := by
        rw [← pow_mul, ← mul_pow, show (2 : ℕ) * 2 = 4 by norm_num, hy4]
      rw [e]
      exact hpowfix _
    have hVfix : ∀ v (hv : v ∈ V), ((⟨v, hVUH hv⟩ : ↥UH) : Q) ∈ fixV Ks := by
      intro v hv
      refine D'.mem_fixV_of_fix627 hsum' hy₂Ks hfpf₂ ?_
      rw [← hρy₂, hρ, actQuot_mk_eq_iff]
      have : y₂ * v * y₂⁻¹ = v := by
        rw [(Subgroup.mem_centralizer_iff.mp hy₂C v hv).symm, mul_inv_cancel_right]
      show y₂ * v * y₂⁻¹ * v⁻¹ ∈ U
      rw [this, mul_inv_cancel]
      exact U.one_mem
    apply a18
    intro a' ha'
    refine mem_normalizer_of_conj_mem627 (S := V) fun v hv => ?_
    have hfx := hVfix v hv
    have haK : ρ ⟨a', a20 ha'⟩ ∈ Ks := ⟨⟨a', a20 ha'⟩, hAK ha', rfl⟩
    have h1 := hfx _ haK
    rw [hρ, actQuot_mk_eq_iff] at h1
    have h2 : a' * v * a'⁻¹ = (a' * v * a'⁻¹ * v⁻¹) * v := by group
    rw [h2]
    exact V.mul_mem (inf_le_left (a := V) (h1 : _ ∈ U)) hv
  ·
    push Not at hinner
    obtain ⟨r, hrR, hrout⟩ := hinner
    have hr : ¬ ∃ k ∈ Ks, ∀ x ∈ Ks, r * x * r⁻¹ = k * x * k⁻¹ := by
      rintro ⟨k, hk, hkx⟩
      obtain ⟨x, hx, hne⟩ := hrout k hk
      exact hne (hkx x hx)
    set rr : ↥(Subgroup.normalizer (Ks : Set (MulAut Q))) := ⟨r, hKsN r (hRsGm hrR)⟩ with hrr
    have hrS : r ∈ Subgroup.normalizer ((Rs ⊓ Ks : Subgroup (MulAut Q)) : Set (MulAut Q)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hrR) x
      have h2 := Subgroup.mem_normalizer_iff.mp (hKsN r (hRsGm hrR)) x
      simp only [Subgroup.mem_inf]
      exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩
    have hδ : ∀ (d : G) (hd : d ∈ D),
        (∀ q ∈ commV Ks, ρ' ⟨d, (le_sup_right : D ≤ HD) hd⟩ q = q) ∧
          ∀ x ∈ Ks, ρ' ⟨d, (le_sup_right : D ≤ HD) hd⟩ * x =
            x * ρ' ⟨d, (le_sup_right : D ≤ HD) hd⟩ := by
      intro d hd
      set δ := ρ' ⟨d, (le_sup_right : D ≤ HD) hd⟩ with hδdef
      set dd : ↥(Subgroup.normalizer (Ks : Set (MulAut Q))) := ⟨δ, hDKs d hd⟩ with hdd
      have hδR : δ ∈ Subgroup.normalizer (Rs : Set (MulAut Q)) := by
        refine mem_normalizer_of_conj_mem627 (S := Rs) ?_
        rintro _ ⟨⟨r₀, hr₀H⟩, hr₀R, rfl⟩
        have hr₀R' : r₀ ∈ R := hr₀R
        have hdr : d * r₀ * d⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp (hDR d hd) r₀).mp hr₀R'
        rw [hδdef, hconjρ d _ r₀ hr₀H (a3.1 hdr)]
        exact ⟨⟨_, a3.1 hdr⟩, hdr, rfl⟩
      have hdS : δ ∈ Subgroup.normalizer
          ((Rs ⊓ Ks : Subgroup (MulAut Q)) : Set (MulAut Q)) := by
        rw [Subgroup.mem_normalizer_iff]
        intro x
        have h1 := Subgroup.mem_normalizer_iff.mp hδR x
        have h2 := Subgroup.mem_normalizer_iff.mp (hDKs d hd) x
        simp only [Subgroup.mem_inf]
        exact ⟨fun hx => ⟨h1.mp hx.1, h2.mp hx.2⟩, fun hx => ⟨h1.mpr hx.1, h2.mpr hx.2⟩⟩
      have hδ3 : δ ^ 3 = 1 := by
        rw [hδdef, ← map_pow]
        have : (⟨d, (le_sup_right : D ≤ HD) hd⟩ : ↥HD) ^ 3 = 1 :=
          Subtype.ext (by simpa using hD3 d hd)
        rw [this, map_one]
      have hd3 : dd ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hδ3)
      have hc : ∃ n : ℕ, (rr * dd * rr⁻¹ * dd⁻¹) ^ 2 ^ n = 1 := by
        have hmem : r * δ * r⁻¹ * δ⁻¹ ∈ Rs := by
          have h1 : δ * r⁻¹ * δ⁻¹ ∈ Rs :=
            (Subgroup.mem_normalizer_iff.mp hδR _).mp (Rs.inv_mem hrR)
          have e : r * δ * r⁻¹ * δ⁻¹ = r * (δ * r⁻¹ * δ⁻¹) := by group
          rw [e]
          exact Rs.mul_mem hrR h1
        obtain ⟨n, hn⟩ := hRsyl.2.1 ⟨_, hmem⟩
        refine ⟨n, Subtype.ext ?_⟩
        have := congrArg Subtype.val hn
        simpa using this
      have hhat := D'.hat_eq_one_of_outer627 (inf_le_right : Rs ⊓ Ks ≤ Ks) hS dd rr hdS hrS hd3
        hr hc
      obtain ⟨hfix, hcomm'⟩ := D'.fix_of_hat_eq_one dd hhat
      refine ⟨fun q hq => ?_, hcomm'⟩
      obtain ⟨v, rfl⟩ := D'.exists_ψ hq
      exact hfix v
    have hKD : ∀ k ∈ K, ∀ d ∈ D, k * d * k⁻¹ * d⁻¹ ∈
        centralizerMod U (Subgroup.normalizer (U : Set G)) UH := by
      intro k hk d hd
      have hkH := hKH hk
      have hkHD : k ∈ HD := (le_sup_left : H ≤ HD) hkH
      have hdHD : d ∈ HD := (le_sup_right : D ≤ HD) hd
      have hcHD : k * d * k⁻¹ * d⁻¹ ∈ HD :=
        HD.mul_mem (HD.mul_mem (HD.mul_mem hkHD hdHD) (HD.inv_mem hkHD)) (HD.inv_mem hdHD)
      have hcN : k * d * k⁻¹ * d⁻¹ ∈ Subgroup.normalizer (U : Set G) := hHDU hcHD
      refine ⟨hcN, hcN, ?_⟩
      have hkKs : ρ ⟨k, hkH⟩ ∈ Ks := ⟨⟨k, hkH⟩, hk, rfl⟩
      have hρc : ρ' ⟨k * d * k⁻¹ * d⁻¹, hcHD⟩ = 1 := by
        have e : ρ' ⟨k * d * k⁻¹ * d⁻¹, hcHD⟩ =
            ρ ⟨k, hkH⟩ * ρ' ⟨d, hdHD⟩ * (ρ ⟨k, hkH⟩)⁻¹ * (ρ' ⟨d, hdHD⟩)⁻¹ := by
          rw [hρρ' k hkH, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
          rfl
        rw [e, ← (hδ d hd).2 _ hkKs]
        group
      exact (actQuot_eq_one_iff (U := UH) (Z := U) _).mp hρc
    set W : Subgroup G :=
      ((commV Ks).comap (QuotientGroup.mk' (U.subgroupOf UH))).map UH.subtype with hWdef
    have hUHK : ⁅UH, K⁆ ≤ W := by
      rw [Subgroup.commutator_le]
      intro u hu k hk
      have hkH := hKH hk
      have hku : k * u⁻¹ * k⁻¹ ∈ UH :=
        (Subgroup.mem_normalizer_iff.mp (hHUH hkH) _).mp (UH.inv_mem hu)
      have hcUH : ⁅u, k⁆ ∈ UH := by
        rw [commutatorElement_def]
        have e : u * k * u⁻¹ * k⁻¹ = u * (k * u⁻¹ * k⁻¹) := by group
        rw [e]
        exact UH.mul_mem hu hku
      refine ⟨⟨_, hcUH⟩, ?_, rfl⟩
      show (QuotientGroup.mk' (U.subgroupOf UH)) ⟨⁅u, k⁆, hcUH⟩ ∈ commV Ks
      have hgen : ρ ⟨k, hkH⟩ ((⟨u, hu⟩ : ↥UH) : Q) * ((⟨u, hu⟩ : ↥UH) : Q)⁻¹ ∈ commV Ks :=
        Subgroup.subset_closure ⟨_, ⟨⟨k, hkH⟩, hk, rfl⟩, _, rfl⟩
      have e : (QuotientGroup.mk' (U.subgroupOf UH)) ⟨⁅u, k⁆, hcUH⟩ =
          (ρ ⟨k, hkH⟩ ((⟨u, hu⟩ : ↥UH) : Q) * ((⟨u, hu⟩ : ↥UH) : Q)⁻¹)⁻¹ := by
        rw [hρ, actQuot_mk, mul_inv_rev, inv_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
          QuotientGroup.mk'_apply]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, commutatorElement_def]
        group
      rw [e]
      exact (commV Ks).inv_mem hgen
    have hWD : ⁅W, D⁆ ≤ U := by
      rw [Subgroup.commutator_le]
      rintro _ ⟨⟨w, hwUH⟩, hwV, rfl⟩ d hd
      have hwV' : ((⟨w, hwUH⟩ : ↥UH) : Q) ∈ commV Ks := hwV
      have h1 := (hδ d hd).1 _ hwV'
      have h2 := (actQuot_mk_eq_iff (U := UH) (Z := U) (K := HD) (hKU := hHDUH) (hKZ := hHDU)
        ⟨d, (le_sup_right : D ≤ HD) hd⟩ ⟨w, hwUH⟩).mp h1
      have h3 := U.inv_mem h2
      rw [commutatorElement_def]
      simp only [Subgroup.coe_subtype]
      convert h3 using 1
      group
    exact a34 K hKH hAK hKD ((Subgroup.commutator_mono hUHK le_rfl).trans hWD)

end CFSG.Quasithin.H13
