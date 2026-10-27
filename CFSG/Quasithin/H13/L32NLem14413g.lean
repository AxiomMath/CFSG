module

public import CFSG.Quasithin.H13.L32NLem14413f
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7IsoBase
public import CFSG.Quasithin.Vol2.Ch12Sec2Action

public section

namespace CFSG.Quasithin.H13.L14413

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13.A6
open CFSG.Quasithin.H13.L32A
open scoped IsMulCommutative

theorem sl3_perfect : ⁅(⊤ : Subgroup SL3.S), (⊤ : Subgroup SL3.S)⁆ = ⊤ := by
  have hS : IsSimpleGroup SL3.S := Vol2Native.A312L.Seven.slThree_isSimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ⁅(⊤ : Subgroup SL3.S), (⊤ : Subgroup SL3.S)⁆
    with h | h
  · exfalso
    have hc : SL3.ex * SL3.ey * SL3.ex⁻¹ * SL3.ey⁻¹ ∈
        ⁅(⊤ : Subgroup SL3.S), (⊤ : Subgroup SL3.S)⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [h, Subgroup.mem_bot] at hc
    exact absurd hc (by decide +kernel)
  · exact h

theorem not_isPGroup_top : ¬ IsPGroup 2 ↥(⊤ : Subgroup SL3.S) := by
  intro hP
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [Subgroup.card_top, SL3.card_S] at hk
  have h7 : 7 ∣ 2 ^ k := hk ▸ (by norm_num : (7 : ℕ) ∣ 168)
  exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h7) (by norm_num)

theorem subnormal_eq_bot_or_top {S : Type*} [Group S] [IsSimpleGroup S] {A B : Subgroup S}
    (h : IsSubnormal A B) (hB : B = ⊤) : A = ⊥ ∨ A = ⊤ :=
  by subst hB; exact h.eq_bot_or_top

theorem pow_eight_or_three_X1 : ∀ c : SL3.S, SL3.InX1 c → c ^ 8 = 1 ∨ c ^ 3 = 1 := by
  decide +kernel

theorem pow_eight_or_three_X2 : ∀ c : SL3.S, SL3.InX2 c → c ^ 8 = 1 ∨ c ^ 3 = 1 := by
  decide +kernel

theorem exists_inv_X1 : ∀ c : SL3.S, SL3.InX1 c → c ^ 3 = 1 →
    ∃ p ∈ SL3.P0list, p * c * p⁻¹ = c⁻¹ := by
  decide +kernel

theorem exists_inv_X2 : ∀ c : SL3.S, SL3.InX2 c → c ^ 3 = 1 →
    ∃ p ∈ SL3.P0list, p * c * p⁻¹ = c⁻¹ := by
  decide +kernel

theorem P0list_le : ∀ p ∈ SL3.P0list, p ∈ SL3.P0 := SL3.P0list_mem le_rfl

theorem pow_three_of_odd {Q : Type*} [Group Q] {c : Q} {m : ℕ} (hm : Odd m) (hc : c ^ m = 1)
    (h83 : c ^ 8 = 1 ∨ c ^ 3 = 1) : c ^ 3 = 1 := by
  rcases h83 with h8 | h3
  · have hg : Nat.Coprime m (2 ^ 3) := Nat.Coprime.pow_right 3 (Nat.coprime_two_right.mpr hm)
    have := pow_gcd_eq_one.mpr ⟨hc, (show c ^ (2 ^ 3) = 1 from h8)⟩
    rw [Nat.Coprime.gcd_eq_one hg, pow_one] at this
    rw [this, one_pow]
  · exact h3

variable {G : Type} [Group G]

theorem absorb {Q : Type*} [Group Q] {H Lp Y : Subgroup G} (φ : ↥H →* Q)
    (hLp : H ≤ Subgroup.normalizer (Lp : Set G)) (hYH : Y ≤ H)
    (hR : ∀ r (hr : r ∈ Y), φ ⟨r, hYH hr⟩ = 1 → ∃ k : ℕ, r ^ 2 ^ k = 1)
    {y : G} (hy : y ∈ Y) (hodd : Odd (orderOf y)) {s : G} (hsL : s ∈ Lp)
    (hsY : s ∈ Subgroup.normalizer (Y : Set G)) (hsH : s ∈ H)
    (hinv : φ ⟨s, hsH⟩ * φ ⟨y, hYH hy⟩ * (φ ⟨s, hsH⟩)⁻¹ = (φ ⟨y, hYH hy⟩)⁻¹) : y ∈ Lp := by
  have hyH := hYH hy
  set c := y * s * y⁻¹ * s⁻¹ with hc
  have hcL : c ∈ Lp :=
    Lp.mul_mem ((Subgroup.mem_normalizer_iff.mp (hLp hyH) s).mp hsL) (Lp.inv_mem hsL)
  have hcY : c ∈ Y := by
    rw [hc, show y * s * y⁻¹ * s⁻¹ = y * (s * y⁻¹ * s⁻¹) by group]
    exact Y.mul_mem hy ((Subgroup.mem_normalizer_iff.mp hsY y⁻¹).mp (Y.inv_mem hy))
  have hφc : φ ⟨c, hYH hcY⟩ = φ ⟨y, hyH⟩ * φ ⟨y, hyH⟩ := by
    have hcc : (⟨c, hYH hcY⟩ : ↥H) = ⟨y, hyH⟩ * ⟨s, hsH⟩ * ⟨y, hyH⟩⁻¹ * ⟨s, hsH⟩⁻¹ := rfl
    rw [hcc, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h2 : φ ⟨s, hsH⟩ * (φ ⟨y, hyH⟩)⁻¹ * (φ ⟨s, hsH⟩)⁻¹ = φ ⟨y, hyH⟩ := by
      calc φ ⟨s, hsH⟩ * (φ ⟨y, hyH⟩)⁻¹ * (φ ⟨s, hsH⟩)⁻¹ =
          (φ ⟨s, hsH⟩ * φ ⟨y, hyH⟩ * (φ ⟨s, hsH⟩)⁻¹)⁻¹ := by group
        _ = φ ⟨y, hyH⟩ := by rw [hinv, inv_inv]
    rw [show φ ⟨y, hyH⟩ * φ ⟨s, hsH⟩ * (φ ⟨y, hyH⟩)⁻¹ * (φ ⟨s, hsH⟩)⁻¹ =
      φ ⟨y, hyH⟩ * (φ ⟨s, hsH⟩ * (φ ⟨y, hyH⟩)⁻¹ * (φ ⟨s, hsH⟩)⁻¹) by group, h2]
  have hrY : c⁻¹ * (y * y) ∈ Y := Y.mul_mem (Y.inv_mem hcY) (Y.mul_mem hy hy)
  have hr1 : φ ⟨c⁻¹ * (y * y), hYH hrY⟩ = 1 := by
    have hrr : (⟨c⁻¹ * (y * y), hYH hrY⟩ : ↥H) = (⟨c, hYH hcY⟩)⁻¹ * (⟨y, hyH⟩ * ⟨y, hyH⟩) :=
      rfl
    rw [hrr, map_mul, map_inv, map_mul, hφc, inv_mul_cancel]
  obtain ⟨k, hk⟩ := hR _ hrY hr1
  have : (Lp.subgroupOf Y).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hYH.trans hLp)
  let π := QuotientGroup.mk' (Lp.subgroupOf Y)
  have hπc : π ⟨c, hcY⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr hcL
  have hπ2 : π ⟨y, hy⟩ ^ 2 ^ (k + 1) = 1 := by
    have hyy : (⟨y, hy⟩ : ↥Y) * ⟨y, hy⟩ = ⟨c, hcY⟩ * ⟨c⁻¹ * (y * y), hrY⟩ := by
      apply Subtype.ext
      show y * y = c * (c⁻¹ * (y * y))
      group
    have hrk : (⟨c⁻¹ * (y * y), hrY⟩ : ↥Y) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [pow_succ, pow_mul', sq, ← map_mul, hyy, map_mul, hπc, one_mul, ← map_pow, hrk, map_one]
  have hπo : π ⟨y, hy⟩ ^ orderOf y = 1 := by
    rw [← map_pow]
    have : (⟨y, hy⟩ : ↥Y) ^ orderOf y = 1 := Subtype.ext (by simp [pow_orderOf_eq_one])
    rw [this, map_one]
  have hcop : Nat.Coprime (2 ^ (k + 1)) (orderOf y) :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hodd)
  have h1 : π ⟨y, hy⟩ = 1 := by
    have := pow_gcd_eq_one.mpr ⟨hπ2, hπo⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this
  have h2 : (⟨y, hy⟩ : ↥Y) ∈ Lp.subgroupOf Y :=
    (QuotientGroup.eq_one_iff (N := Lp.subgroupOf Y) _).mp h1
  exact h2

variable [Finite G]

theorem exists_cComp_map_eq_top {H : Subgroup G} (φ : ↥H →* SL3.S) (hφ : φ.range = ⊤)
    (hspan : cCompSpan H = perfectCore H) : ∃ Lp ∈ cComp H, (Lp.subgroupOf H).map φ = ⊤ := by
  have hS : IsSimpleGroup SL3.S := Vol2Native.A312L.Seven.slThree_isSimple
  by_contra hno
  push Not at hno
  have hker : ∀ L' ∈ cComp H, L' ≤ φ.ker.map H.subtype := by
    intro L' hL'
    have hsn : IsSubnormal ((L'.subgroupOf H).map φ) ⊤ := by
      have h1 := A3.subnormal_map φ (A3.subnormal_comap H.subtype (subnormal_of_mem_cComp hL'))
      rwa [show H.comap H.subtype = ⊤ from Subgroup.subgroupOf_self H, ← MonoidHom.range_eq_map,
        hφ] at h1
    rcases subnormal_eq_bot_or_top hsn rfl with h | h
    · intro x hx
      have hxH : x ∈ H := le_of_mem_cComp hL' hx
      refine ⟨⟨x, hxH⟩, ?_, rfl⟩
      have : φ ⟨x, hxH⟩ ∈ (L'.subgroupOf H).map φ := ⟨⟨x, hxH⟩, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      exact this
    · exact absurd h (hno L' hL')
  have hpc : perfectCore H ≤ φ.ker.map H.subtype := by
    have : cCompSpan H ≤ φ.ker.map H.subtype := sSup_le hker
    rwa [hspan] at this
  have hpc' : perfectCore (⊤ : Subgroup ↥H) ≤ φ.ker := by
    intro x hx
    have hx' : (x : G) ∈ perfectCore H := by
      have := map_perfectCore H.subtype (⊤ : Subgroup ↥H)
      rw [Subgroup.map_top, Subgroup.range_subtype] at this
      rw [← this]
      exact ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hpc hx'
    rwa [Subtype.ext hyx] at hy
  have himg : (perfectCore (⊤ : Subgroup ↥H)).map φ = ⊤ := by
    rw [map_perfectCore, ← MonoidHom.range_eq_map, hφ,
      perfectCore_eq_self_of_perfect sl3_perfect]
  have hbot : (perfectCore (⊤ : Subgroup ↥H)).map φ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    exact hpc'
  rw [himg] at hbot
  have hex : SL3.ex ∈ (⊥ : Subgroup SL3.S) := hbot ▸ Subgroup.mem_top _
  rw [Subgroup.mem_bot] at hex
  exact absurd hex (by decide +kernel)

omit [Finite G] in
theorem map_conj_eq_top {H Lp : Subgroup G} (φ : ↥H →* SL3.S)
    (hφ : (Lp.subgroupOf H).map φ = ⊤) {h : G} (hh : h ∈ H) :
    ((Lp.map (MulAut.conj h).toMonoidHom).subgroupOf H).map φ = ⊤ := by
  rw [eq_top_iff]
  intro A _
  have hA : (φ ⟨h, hh⟩)⁻¹ * A * φ ⟨h, hh⟩ ∈ (Lp.subgroupOf H).map φ := hφ ▸ Subgroup.mem_top _
  obtain ⟨⟨l, hlH⟩, hlL, hlA⟩ := hA
  have hmem : h * l * h⁻¹ ∈ H := mul_mem (mul_mem hh hlH) (inv_mem hh)
  refine ⟨⟨h * l * h⁻¹, hmem⟩, ⟨l, hlL, rfl⟩, ?_⟩
  have hprod : (⟨h * l * h⁻¹, hmem⟩ : ↥H) = ⟨h, hh⟩ * ⟨l, hlH⟩ * ⟨h, hh⟩⁻¹ := rfl
  rw [hprod, map_mul, map_mul, map_inv, hlA]
  group

theorem le_normalizer_of_map_eq_top {H Lp : Subgroup G} (φ : ↥H →* SL3.S)
    (h37 : A37Statement (↥H ⧸ CFSG.pCore 2 ↥H)) (hLp : Lp ∈ cComp H)
    (hφ : (Lp.subgroupOf H).map φ = ⊤) : H ≤ Subgroup.normalizer (Lp : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hLpH : Lp ≤ H := le_of_mem_cComp hLp
  have hLh : Lp.map (MulAut.conj h).toMonoidHom ∈ cComp H := by
    have h1 := cComp_map_mulEquiv (MulAut.conj h) hLp
    have h2 : H.map (MulAut.conj h).toMonoidHom = H :=
      Subgroup.mem_normalizer_iff_map_conj_eq.1 (Subgroup.le_normalizer hh)
    rwa [h2] at h1
  have hc := commutator_le_pCoreOf_of_ne h37 hLp hLh (Ne.symm hne)
  have hcomm : ⁅Lp.subgroupOf H, (Lp.map (MulAut.conj h).toMonoidHom).subgroupOf H⁆.map
      H.subtype = ⁅Lp, Lp.map (MulAut.conj h).toMonoidHom⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hLpH,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (le_of_mem_cComp hLh)]
  have hle : ⁅Lp.subgroupOf H, (Lp.map (MulAut.conj h).toMonoidHom).subgroupOf H⁆ ≤
      (pCoreOf 2 H).subgroupOf H := by
    intro x hx
    have hx' : (x : G) ∈ ⁅Lp, Lp.map (MulAut.conj h).toMonoidHom⁆ := hcomm ▸ ⟨x, hx, rfl⟩
    exact hc hx'
  have h2 : IsPGroup 2 ↥((pCoreOf 2 H).subgroupOf H) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).of_equiv
      (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 H)).symm
  have himg : ⁅Lp.subgroupOf H, (Lp.map (MulAut.conj h).toMonoidHom).subgroupOf H⁆.map φ =
      ⊤ := by
    rw [Subgroup.map_commutator, hφ, map_conj_eq_top φ hφ hh, sl3_perfect]
  apply not_isPGroup_top
  rw [← himg]
  exact (h2.to_le hle).map φ

namespace XCtx

variable {T L V V₂ X : Subgroup G} {g : G}

section Basic

variable (C : XCtx G T L V V₂ X g)
include C

theorem VX_le_H3 : ⁅V₂, X⁆ ≤ lOne L V₂ ⊔ X ⊔ T := C.VXU.trans C.U_le_H3

theorem pCoreOf_H3_ne_bot : pCoreOf 2 (lOne L V₂ ⊔ X ⊔ T) ≠ ⊥ := by
  have hle := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 C.VX_le_H3
    C.H3_le_normalizer (C.hyp.fsu.sylow.1.to_le (C.VXU.trans C.UT))
  intro hb
  rw [hb, le_bot_iff] at hle
  have := C.Y.2.2.2.2.1
  rw [hle, Subgroup.card_bot] at this
  omega

theorem sylow_H3 : IsSylowTwoOf T (lOne L V₂ ⊔ X ⊔ T) :=
  isSylowTwoOf_of_quasithinIsSylowTwo C.hyp.fsu.sylow T_le_H3

theorem T_le_normalizer_L2 : T ≤ Subgroup.normalizer (lOne L V₂ : Set G) := by
  intro t ht
  have htN : t ∈ Subgroup.normalizer ((L ⊓ Subgroup.normalizer (V₂ : Set G) : Subgroup G) :
      Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨C.s1282.hyp.hyp.normalizes ht,
      Subgroup.le_normalizer (C.TV₂ ht)⟩
  exact Subgroup.mem_normalizer_fintype fun y hy => conj_mem_oTwoUpper htN hy

end Basic

variable {C : XCtx G T L V V₂ X g} (K : C.Coords)

theorem Coords.φ_eq_one_iff (h : ↥(lOne L V₂ ⊔ X ⊔ T)) :
    K.φ h = 1 ↔ (h : G) ∈ Subgroup.centralizer ((⁅V₂, X⁆ : Subgroup G) : Set G) := by
  rw [← MonoidHom.mem_ker, show K.φ.ker = _ from repV_ker C.H3_le_normalizer K.e,
    Subgroup.mem_subgroupOf]

theorem Coords.exists_Lp (h39 : A39ForSQTK) :
    ∃ Lp ∈ cComp (lOne L V₂ ⊔ X ⊔ T), (Lp.subgroupOf (lOne L V₂ ⊔ X ⊔ T)).map K.φ = ⊤ :=
  exists_cComp_map_eq_top K.φ K.range_eq_top
    (lemma_1_2_1_one C.hyp.fsu.qtke C.hyp.fsu.simple C.hyp.fsu.nonabelian h39
      C.pCoreOf_H3_ne_bot)

theorem Coords.normal_Lp (h37 : A37ForSQTK) {Lp : Subgroup G}
    (hLp : Lp ∈ cComp (lOne L V₂ ⊔ X ⊔ T))
    (hφ : (Lp.subgroupOf (lOne L V₂ ⊔ X ⊔ T)).map K.φ = ⊤) :
    lOne L V₂ ⊔ X ⊔ T ≤ Subgroup.normalizer (Lp : Set G) :=
  le_normalizer_of_map_eq_top K.φ (h37 _ (sqtkHyp_quotient_of_pCoreOf_ne_bot C.hyp.fsu.qtke
    C.hyp.fsu.simple C.hyp.fsu.nonabelian C.pCoreOf_H3_ne_bot)) hLp hφ

end XCtx

end CFSG.Quasithin.H13.L14413
