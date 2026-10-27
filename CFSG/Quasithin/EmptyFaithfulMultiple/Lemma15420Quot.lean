module

public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.LocalAnalysis.QuasithinUnique.BenderInterfaces
public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15420Diag

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

namespace L15420

variable {G : Type*} [Group G]

@[expose] def conjRestr (L : Subgroup G) (g : G) (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    ↥L ≃* ↥L where
  toFun l := ⟨g * l * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg l).mp l.2⟩
  invFun l := ⟨g⁻¹ * l * g, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) l).mp l.2
    simpa using this⟩
  left_inv l := Subtype.ext (by simp [mul_assoc])
  right_inv l := Subtype.ext (by simp [mul_assoc])
  map_mul' l m := Subtype.ext (by simp [mul_assoc])

omit [Group G] in
theorem conjRestr_apply_coe [Group G] {L : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (l : L) :
    ((conjRestr L g hg l : L) : G) = g * l * g⁻¹ := rfl

@[expose] noncomputable def quotConj (L : Subgroup G) (g : G)
    (hg : g ∈ Subgroup.normalizer (L : Set G)) : MulAut (↥L ⧸ CFSG.pCore 2 ↥L) :=
  QuotientGroup.congr (CFSG.pCore 2 ↥L) (CFSG.pCore 2 ↥L) (conjRestr L g hg) (by
    exact CFSG.LieType.BorelTits.map_pCore_mulEquiv 2 (conjRestr L g hg))

variable {L : Subgroup G}

theorem quotConj_mk {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) (l : L) :
    quotConj L g hg (l : ↥L ⧸ CFSG.pCore 2 ↥L) =
      ((conjRestr L g hg l : L) : ↥L ⧸ CFSG.pCore 2 ↥L) :=
  rfl

theorem quotConj_mul {g h : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (hh : h ∈ Subgroup.normalizer (L : Set G)) :
    quotConj L (g * h) (Subgroup.mul_mem _ hg hh) = quotConj L g hg * quotConj L h hh := by
  ext x
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  rw [MulAut.mul_apply, quotConj_mk, quotConj_mk, quotConj_mk]
  congr 1
  apply Subtype.ext
  simp only [conjRestr_apply_coe]
  group

theorem quotConj_one : quotConj L 1 (Subgroup.one_mem _) = 1 := by
  ext x
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  rw [quotConj_mk, MulAut.one_apply]
  congr 1
  apply Subtype.ext
  simp only [conjRestr_apply_coe]
  group

theorem quotConj_congr {g₁ g₂ : G} (e : g₁ = g₂) (h₁ : g₁ ∈ Subgroup.normalizer (L : Set G))
    (h₂ : g₂ ∈ Subgroup.normalizer (L : Set G)) : quotConj L g₁ h₁ = quotConj L g₂ h₂ := by
  subst e
  rfl

theorem quotConj_pow {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) (n : ℕ) :
    quotConj L (g ^ n) (Subgroup.pow_mem _ hg n) = quotConj L g hg ^ n := by
  induction n with
  | zero =>
    rw [pow_zero (quotConj L g hg)]
    exact (quotConj_congr (pow_zero g) _ (Subgroup.one_mem _)).trans quotConj_one
  | succ n ih =>
    rw [pow_succ (quotConj L g hg) n, ← ih, ← quotConj_mul]
    exact quotConj_congr (pow_succ g n) _ _

theorem quotConj_of_mem {g : G} (hgL : g ∈ L) :
    quotConj L g (Subgroup.le_normalizer hgL) =
      MulAut.conj ((⟨g, hgL⟩ : L) : ↥L ⧸ CFSG.pCore 2 ↥L) := by
  ext x
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
  rw [quotConj_mk, MulAut.conj_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul]
  congr 1

theorem mk_eq_one_iff {x : L} :
    (x : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 ↔ (x : G) ∈ pCoreOf 2 L := by
  rw [QuotientGroup.eq_one_iff, pCoreOf]
  constructor
  · intro h
    exact ⟨x, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    rwa [← Subtype.ext hyx]

theorem quotConj_eq_one_iff {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) :
    quotConj L g hg = 1 ↔ ∀ l ∈ L, g * l * g⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
  constructor
  · intro h l hl
    have h1 := congrArg (fun α => α ((⟨l, hl⟩ : L) : ↥L ⧸ CFSG.pCore 2 ↥L)) h
    simp only [MulAut.one_apply, quotConj_mk] at h1
    rw [← div_eq_one, ← QuotientGroup.mk_div] at h1
    have := mk_eq_one_iff.mp h1
    simpa [conjRestr_apply_coe, div_eq_mul_inv] using this
  · intro h
    ext x
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    rw [quotConj_mk, MulAut.one_apply, ← div_eq_one, ← QuotientGroup.mk_div, mk_eq_one_iff]
    simpa [conjRestr_apply_coe, div_eq_mul_inv] using h l l.2

theorem quotConj_fix {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) {l : L}
    (hgl : g * l = l * g) :
    quotConj L g hg (l : ↥L ⧸ CFSG.pCore 2 ↥L) = (l : ↥L ⧸ CFSG.pCore 2 ↥L) := by
  rw [quotConj_mk]
  congr 1
  apply Subtype.ext
  rw [conjRestr_apply_coe, hgl]
  group

end L15420

namespace L15420

section CComp

variable {G : Type} [Group G] [Finite G] {H L : Subgroup G}

theorem isSolvable_pCoreOf (L : Subgroup G) : Group.IsSolvable ↥(pCoreOf 2 L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).isNilpotent
  infer_instance

omit [Finite G] in
theorem le_pCoreOf_of_map_eq_bot {N : Subgroup G} (hNL : N ≤ L)
    (h : (N.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊥) : N ≤ pCoreOf 2 L := by
  intro x hx
  have hx' : (⟨x, hNL hx⟩ : L) ∈ N.subgroupOf L := hx
  have : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨x, hNL hx⟩ : L) = 1 := by
    rw [← Subgroup.mem_bot, ← h]
    exact Subgroup.mem_map_of_mem _ hx'
  exact mk_eq_one_iff.mp this

theorem le_of_map_eq_top {N : Subgroup G} (hNL : N ≤ L) (hN : (N.subgroupOf L).Normal)
    (hperf : ⁅L, L⁆ = L)
    (h : (N.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤) : L ≤ N := by
  have hsup : L = N ⊔ pCoreOf 2 L := by
    refine le_antisymm (fun x hx => ?_) (sup_le hNL (CFSG.LieType.BorelTits.pCoreOf_le 2 L))
    have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨x, hx⟩ : L) ∈
        (N.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by rw [h]; trivial
    obtain ⟨n, hn, hnx⟩ := hmem
    have h1 : ((n⁻¹ * ⟨x, hx⟩ : L) : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      have : ((n : L) : ↥L ⧸ CFSG.pCore 2 ↥L) = ((⟨x, hx⟩ : L) : ↥L ⧸ CFSG.pCore 2 ↥L) := hnx
      rw [this, inv_mul_cancel]
    have h2 := mk_eq_one_iff.mp h1
    have e : x = (n : G) * ((n⁻¹ * ⟨x, hx⟩ : L) : G) := by simp
    rw [e]
    exact Subgroup.mul_mem_sup hn h2
  have hpc := perfectCore_le_of_sup_solvable hNL hN hsup (isSolvable_pCoreOf L)
  rwa [perfectCore_eq_self_of_perfect hperf] at hpc

theorem commutator_le_pCoreOf_of_ne {L' : Subgroup G} (hL : L ∈ cComp H) (hL' : L' ∈ cComp H)
    (hne : L ≠ L') (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥) : ⁅L, L'⁆ ≤ pCoreOf 2 L := by
  have hLL' : L' ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_mem_cComp hL hL'
  have hL'L : L ≤ Subgroup.normalizer (L' : Set G) := le_normalizer_of_mem_cComp hL' hL
  have hNL : ⁅L, L'⁆ ≤ L := commutator_le_of_le_normalizer hLL'
  have hNL' : ⁅L, L'⁆ ≤ L' := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_of_le_normalizer hL'L
  have hnorm : (⁅L, L'⁆.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNL]
    intro l hl
    exact Ch1Sec3.commutator_le_normalizer (Subgroup.le_normalizer hl) (hL'L hl)
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (hnorm.map (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)) with h | h
  · exfalso
    have hle : L ≤ L' := (le_of_map_eq_top hNL hnorm (perfect_of_mem_cComp hL) h).trans hNL'
    have hlt : L < L' := lt_of_le_of_ne hle hne
    exact not_subnormal_of_mem_cComp hL' hlt (ne_bot_of_mem_cComp hL) (perfect_of_mem_cComp hL)
      (subnormal_of_mem_cComp hL)
  · rw [hZ, le_bot_iff] at h
    exact le_pCoreOf_of_map_eq_bot hNL h

theorem mem_normalizer_of_conj_mem (hL : L ∈ cComp H)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥) {y : G} (hyL : y ∈ L)
    (hy3 : orderOf y = 3) {r : G} (hr : r ∈ H) {N : Subgroup G} (hN : IsPGroup 2 N)
    (hNL : N ≤ Subgroup.normalizer (L : Set G)) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (hd : r * y * r⁻¹ * (y ^ ε)⁻¹ ∈ N) : r ∈ Subgroup.normalizer (L : Set G) := by
  by_contra hrL
  set L' := L.map (MulAut.conj r).toMonoidHom with hL'def
  have hL' : L' ∈ cComp H := by
    have h1 := cComp_map_mulEquiv (MulAut.conj r) hL
    rwa [map_conj_eq_self_of_mem hr] at h1
  have hne : L ≠ L' := by
    intro h
    apply hrL
    rw [mem_normalizer_iff_map_conj]
    exact h.symm
  have hcomm := commutator_le_pCoreOf_of_ne hL hL' hne hq hZ
  have hy'L' : r * y * r⁻¹ ∈ L' := ⟨y, hyL, rfl⟩
  have hy'N : r * y * r⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
    le_normalizer_of_mem_cComp hL hL' hy'L'
  have h1 : quotConj L (r * y * r⁻¹) hy'N = 1 := by
    rw [quotConj_eq_one_iff]
    intro l hl
    have := Subgroup.commutator_mem_commutator hl hy'L'
    have h2 : ⁅l, r * y * r⁻¹⁆⁻¹ ∈ pCoreOf 2 L := Subgroup.inv_mem _ (hcomm this)
    simpa [commutatorElement_def, mul_assoc] using h2
  have hyε : (y ^ ε)⁻¹ ∈ L := L.inv_mem (L.zpow_mem hyL ε)
  set d := r * y * r⁻¹ * (y ^ ε)⁻¹ with hddef
  have hdN : d ∈ Subgroup.normalizer (L : Set G) := hNL hd
  have h2 : quotConj L d hdN =
      MulAut.conj ((⟨(y ^ ε)⁻¹, hyε⟩ : L) : ↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [quotConj_congr hddef hdN (Subgroup.mul_mem _ hy'N (Subgroup.le_normalizer hyε)),
      quotConj_mul hy'N (Subgroup.le_normalizer hyε), h1, one_mul, quotConj_of_mem hyε]
  obtain ⟨k, hk⟩ := hN ⟨d, hd⟩
  have hdk : d ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  have h3 : MulAut.conj (((⟨(y ^ ε)⁻¹, hyε⟩ : L) : ↥L ⧸ CFSG.pCore 2 ↥L) ^ 2 ^ k) = 1 := by
    rw [map_pow, ← h2, ← quotConj_pow hdN]
    rw [quotConj_congr hdk (Subgroup.pow_mem _ hdN _) (Subgroup.one_mem _)]
    exact quotConj_one
  have h4 : (((⟨(y ^ ε)⁻¹, hyε⟩ : L) : ↥L ⧸ CFSG.pCore 2 ↥L) ^ 2 ^ k) ∈
      Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro x
    set w := ((⟨(y ^ ε)⁻¹, hyε⟩ : L) : ↥L ⧸ CFSG.pCore 2 ↥L) ^ 2 ^ k with hw
    have := congrArg (fun α => α x) h3
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc x * w = (w * x * w⁻¹) * w := by rw [this]
      _ = w * x := by group
  rw [hZ, Subgroup.mem_bot, ← QuotientGroup.mk_pow, mk_eq_one_iff] at h4
  have h5 : y ^ 2 ^ k ∈ pCoreOf 2 L := by
    simp only [Subgroup.coe_pow] at h4
    rcases hε with rfl | rfl
    · simpa [inv_pow] using h4
    · simpa using h4
  have h6 : y ∈ pCoreOf 2 L := L15420.mem_of_pow_mem_of_pow_mem
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)) h5
    (by rw [← hy3, pow_orderOf_eq_one]; exact Subgroup.one_mem _)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨y, h6⟩
  have hym : y ^ 2 ^ m = 1 := by
    have := congrArg Subtype.val hm
    simpa using this
  have hdvd : 3 ∣ 2 ^ m := hy3 ▸ orderOf_dvd_of_pow_eq_one hym
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd)
  omega

omit [Finite G] in
theorem mem_normalizer_centralizer {Q : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Q : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (Q : Set G) : Set G) := by
  have key : ∀ {x : G}, x ∈ Subgroup.normalizer (Q : Set G) →
      ∀ c ∈ Subgroup.centralizer (Q : Set G), x * c * x⁻¹ ∈ Subgroup.centralizer (Q : Set G) := by
    intro x hx c hc
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : x⁻¹ * q * x ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hx) q).mp hq
      simpa using this
    have := Subgroup.mem_centralizer_iff.mp hc _ hq'
    calc q * (x * c * x⁻¹) = x * ((x⁻¹ * q * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * q * x)) * x⁻¹ := by rw [this]
      _ = x * c * x⁻¹ * q := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key hg c, fun h => ?_⟩
  have := key (Subgroup.inv_mem _ hg) _ h
  simpa [mul_assoc] using this

theorem charTwo_or_isComponentIn (hL : L ∈ cComp H)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hZ : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥) : CharTwo L ∨ IsComponentIn L H := by
  by_cases hC : CharTwo L
  · exact Or.inl hC
  right
  set C := L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) with hCdef
  have hCL : C ≤ L := inf_le_left
  have hnorm : (C.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCL]
    intro l hl
    exact mem_normalizer_inf (Subgroup.le_normalizer hl)
      (mem_normalizer_centralizer (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L hl))
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq
      (hnorm.map (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)) with h | h
  swap
  · rw [hZ, le_bot_iff] at h
    exact absurd (le_pCoreOf_of_map_eq_bot hCL h) hC
  have hLC : L ≤ C := le_of_map_eq_top hCL hnorm (perfect_of_mem_cComp hL) h
  have hLH : L ≤ H := le_of_mem_cComp hL
  have hcenter : Subgroup.center ↥L = CFSG.pCore 2 ↥L := by
    apply le_antisymm
    · intro x hx
      have h1 : (x : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
        rw [Subgroup.mem_center_iff] at hx ⊢
        intro w
        obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hx w]
      rw [hZ, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h1
      exact h1
    · intro x hx
      rw [Subgroup.mem_center_iff]
      intro w
      have hxQ : (x : G) ∈ pCoreOf 2 L := by
        rw [pCoreOf]
        exact ⟨x, hx, rfl⟩
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (hLC w.2).2 _ hxQ).symm
  have hqL : CFSG.IsQuasisimple ↥L := by
    obtain ⟨-, hs, a, b, hab⟩ := hq
    have e : (↥L ⧸ Subgroup.center ↥L) ≃*
        ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
      (QuotientGroup.quotientMulEquivOfEq hcenter).trans
        (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm))
    have := hs
    refine ⟨Subgroup.isPerfect_iff.mpr (perfect_of_mem_cComp hL), e.isSimpleGroup, e.symm a,
      e.symm b, fun hc => hab ?_⟩
    have := congrArg e hc
    simpa using this
  refine ⟨hLH, CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hLH).symm hqL, ?_⟩
  have h1 := A3.subnormal_comap H.subtype (subnormal_of_mem_cComp hL)
  have h2 : Subgroup.comap H.subtype H = ⊤ := by simp
  rw [h2] at h1
  exact A3.subnormal_top_iff.mp h1

end CComp

end L15420

end CFSG.Quasithin.EmptyFaithfulMultiple
