module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.B2Module
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.CenBOdd
public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.CenTauSylow
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Nilpotent

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open CFSG.StandardType.GGFF

private theorem conj_pow_eq_pow {G : Type*} [Group G] {g b : G} {k : ℤ}
    (h : g * b * g⁻¹ = b ^ k) (n : ℕ) :
    g ^ n * b * (g ^ n)⁻¹ = b ^ (k ^ n) := by
  induction n with
  | zero => simp
  | succ m ih =>
    have hstep : g ^ (m + 1) * b * (g ^ (m + 1))⁻¹ = g * (g ^ m * b * (g ^ m)⁻¹) * g⁻¹ := by
      group
    rw [hstep, ih, ← conj_zpow (a := g) (b := b) (i := (k ^ m : ℤ)), h, ← zpow_mul,
      pow_succ']

private theorem conj_eq_self_of_mem_zpowers {G : Type*} [Group G] {g b : G} {k : ℤ} {e : ℕ}
    (hb : orderOf b = 3) (hg : g ^ 3 ^ e = 1) (hconj : g * b * g⁻¹ = b ^ k) :
    g * b * g⁻¹ = b := by
  have hb_eq : b = b ^ (k ^ (3 ^ e)) := by
    have h := conj_pow_eq_pow hconj (3 ^ e)
    rw [hg] at h
    simpa using h
  have hmod : k ^ (3 ^ e) ≡ 1 [ZMOD (3 : ℤ)] := by
    have h2 : b ^ (1 : ℤ) = b ^ (k ^ (3 ^ e)) := by rw [zpow_one]; exact hb_eq
    have h3 := (zpow_eq_zpow_iff_modEq.mp h2)
    simpa [hb] using h3.symm
  have hzmod : (k : ZMod 3) = 1 := by
    have hcast : ((k ^ (3 ^ e) : ℤ) : ZMod 3) = 1 := by
      have h : ((k ^ (3 ^ e) : ℤ) : ZMod 3) = ((1 : ℤ) : ZMod 3) := by
        rw [ZMod.intCast_eq_intCast_iff]
        exact hmod
      simpa using h
    have hpow : ((k ^ (3 ^ e) : ℤ) : ZMod 3) = (k : ZMod 3) ^ 3 ^ e := by
      push_cast
      rfl
    calc (k : ZMod 3) = (k : ZMod 3) ^ 3 ^ e :=
          (ZMod.pow_card_pow (p := 3) (n := e) (x := (k : ZMod 3))).symm
      _ = ((k ^ (3 ^ e) : ℤ) : ZMod 3) := hpow.symm
      _ = 1 := hcast
  have hmodk : k ≡ 1 [ZMOD (3 : ℤ)] :=
    (ZMod.intCast_eq_intCast_iff k 1 3).mp (by simpa using hzmod)
  rw [hconj]
  have hfin : b ^ k = b ^ (1 : ℤ) := zpow_eq_zpow_iff_modEq.mpr (by simpa [hb] using hmodk)
  simpa using hfin

private theorem mem_sup_zpowers_of_mem_normalizer {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {B₂ : Subgroup G}
    {τ c : G} (hB₂ : B2Package b z B₂) (hτc : TauC z τ c) {T : Subgroup G}
    (hTW : T ≤ Subgroup.centralizer ({τ} : Set G) ⊓ Subgroup.normalizer (B₂ : Set G))
    (hT3 : IsPGroup 3 T) {g : G} (hgT : g ∈ T)
    (hgN : g ∈ Subgroup.normalizer
      (((Subgroup.zpowers b ⊔ Subgroup.zpowers c : Subgroup G)) : Set G)) :
    g ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers c := by
  have hgNB2 : g ∈ Subgroup.normalizer (B₂ : Set G) := (hTW hgT).2
  have hgNB2inv : g⁻¹ ∈ Subgroup.normalizer (B₂ : Set G) := Subgroup.inv_mem _ hgNB2
  have hqQ : g * b * g⁻¹ ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp hgN b).1 (Subgroup.mem_sup_left (Subgroup.mem_zpowers b))
  have hclosure_le : Subgroup.closure
        {r : G | ∃ x ∈ B₂, r = (g * b * g⁻¹) * x * (g * b * g⁻¹)⁻¹ * x⁻¹} ≤
      (bOne z).map (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.closure_le]
    rintro r ⟨x, hx, rfl⟩
    have hxg : g⁻¹ * x * g ∈ B₂ := by
      simpa using (Subgroup.mem_normalizer_iff.mp hgNB2inv x).mp hx
    have hinner : b * (g⁻¹ * x * g) * b⁻¹ * (g⁻¹ * x * g)⁻¹ ∈ bOne z := hB₂.comm _ hxg
    refine Subgroup.mem_map.mpr ⟨_, hinner, ?_⟩
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe, MulAut.conj_apply]
    group
  have hcard_cl : Nat.card ↥(Subgroup.closure
        {r : G | ∃ x ∈ B₂, r = (g * b * g⁻¹) * x * (g * b * g⁻¹)⁻¹ * x⁻¹}) ≤ 3 ^ 3 := by
    calc Nat.card ↥(Subgroup.closure
            {r : G | ∃ x ∈ B₂, r = (g * b * g⁻¹) * x * (g * b * g⁻¹)⁻¹ * x⁻¹})
        ≤ Nat.card ↥((bOne z).map (MulAut.conj g).toMonoidHom) := Subgroup.card_le_of_le hclosure_le
      _ = Nat.card ↥(bOne z) := Subgroup.card_map_of_injective (MulAut.conj g).injective
      _ = 27 := h.settingCore.card_torG
      _ = 3 ^ 3 := by norm_num
  have hq_zp : g * b * g⁻¹ ∈ Subgroup.zpowers b :=
    (card_commutator_le_iff h hB₂ hτc hqQ).mp hcard_cl
  obtain ⟨e, he⟩ := hT3 ⟨g, hgT⟩
  have he' : g ^ 3 ^ e = 1 := by simpa using congrArg Subtype.val he
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hq_zp
  have hconj : g * b * g⁻¹ = b ^ k := by rw [← hk]
  have hgb : g * b * g⁻¹ = b := conj_eq_self_of_mem_zpowers h.hypA.ord he' hconj
  have hcard_sup : Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers c) = 9 := by
    have hz01 : zs z 0 ≠ zs z 1 := by
      intro hh
      have hL : z 0 = z 1 := Subtype.ext hh
      exact absurd (h.model.eq_of_z_eq (Or.inl hL)) (by decide)
    have hc_ne_one : c ≠ 1 := by
      intro hc1
      have hh := hτc.cyc₀
      rw [hc1] at hh
      exact hz01 (by simpa using hh)
    have hc3 : orderOf c = 3 := by
      have hdvd : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one hτc.c_cube
      have hne1 : orderOf c ≠ 1 := fun h1 => hc_ne_one (orderOf_eq_one_iff.mp h1)
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp hdvd with h1 | h3
      · exact absurd h1 hne1
      · exact h3
    have hcommbc : Commute b c :=
      (Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le hτc.c_mem)).symm
    have hcomm_zp : ∀ y ∈ Subgroup.zpowers b, ∀ y' ∈ Subgroup.zpowers c, y * y' = y' * y := by
      intro y hy y' hy'
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
      exact (Commute.zpow_zpow hcommbc i j).eq
    have h_inter : Subgroup.zpowers b ⊓ Subgroup.zpowers c = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      rw [Subgroup.mem_bot]
      obtain ⟨hxb, hxc⟩ := Subgroup.mem_inf.mp hx
      have hxL : x ∈ L := (Subgroup.zpowers_le.2 hτc.c_mem) hxc
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxb
      have hbjL : b ^ j ∈ L := hj.symm ▸ hxL
      have hbj1 : b ^ j = 1 := h.settingCore.zpow_eq_one_of_mem hbjL
      rw [← hj, hbj1]
    let ψ : ↥(Subgroup.zpowers b) × ↥(Subgroup.zpowers c) →* G :=
      { toFun := fun p => (p.1 : G) * p.2
        map_one' := by simp
        map_mul' := by
          intro p q
          have hq : (q.1 : G) * (p.2 : G) = (p.2 : G) * (q.1 : G) :=
            hcomm_zp q.1 q.1.2 p.2 p.2.2
          show (p.1 : G) * q.1 * (p.2 * q.2) = (p.1 : G) * p.2 * (q.1 * q.2)
          calc (p.1 : G) * q.1 * (p.2 * q.2) = (p.1 : G) * (q.1 * p.2) * q.2 := by group
            _ = (p.1 : G) * (p.2 * q.1) * q.2 := by rw [hq]
            _ = (p.1 : G) * p.2 * (q.1 * q.2) := by group }
    have hψrange : ψ.range = Subgroup.zpowers b ⊔ Subgroup.zpowers c := by
      apply le_antisymm
      · rintro x ⟨p, rfl⟩
        exact Subgroup.mul_mem_sup p.1.2 p.2.2
      · refine sup_le ?_ ?_
        · exact Subgroup.zpowers_le.2
            ⟨(⟨b, Subgroup.mem_zpowers b⟩, 1), by simp [ψ]⟩
        · exact Subgroup.zpowers_le.2
            ⟨(1, ⟨c, Subgroup.mem_zpowers c⟩), by simp [ψ]⟩
    let f : ↥(Subgroup.zpowers b) × ↥(Subgroup.zpowers c) →
        ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers c) :=
      fun p => ⟨(p.1 : G) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
    have hf : Function.Bijective f := by
      refine ⟨?_, ?_⟩
      · rintro ⟨y1, z1⟩ ⟨y2, z2⟩ hh
        have hyz : (y1 : G) * z1 = (y2 : G) * z2 := Subtype.ext_iff.mp hh
        have heq : (y1 : G)⁻¹ * y2 = (z1 : G) * (z2 : G)⁻¹ := by
          calc (y1 : G)⁻¹ * y2 = (y1 : G)⁻¹ * ((y2 : G) * z2) * (z2 : G)⁻¹ := by group
            _ = (y1 : G)⁻¹ * ((y1 : G) * z1) * (z2 : G)⁻¹ := by rw [← hyz]
            _ = (z1 : G) * (z2 : G)⁻¹ := by group
        have hmem : (y1 : G)⁻¹ * y2 ∈ Subgroup.zpowers b ⊓ Subgroup.zpowers c := by
          refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
          · exact (Subgroup.zpowers b).mul_mem ((Subgroup.zpowers b).inv_mem y1.2) y2.2
          · rw [heq]
            exact (Subgroup.zpowers c).mul_mem z1.2 ((Subgroup.zpowers c).inv_mem z2.2)
        rw [h_inter, Subgroup.mem_bot] at hmem
        have hz : (z1 : G) * (z2 : G)⁻¹ = 1 := by rw [← heq]; exact hmem
        exact Prod.ext (Subtype.ext (inv_mul_eq_one.mp hmem))
          (Subtype.ext (mul_inv_eq_one.mp hz))
      · rintro ⟨x, hx⟩
        have hxr : x ∈ ψ.range := hψrange.symm ▸ hx
        obtain ⟨p, hp⟩ := hxr
        exact ⟨p, Subtype.ext hp⟩
    have hbij : Nat.card ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers c) =
        Nat.card (Subgroup.zpowers b × Subgroup.zpowers c) :=
      (Nat.card_congr (Equiv.ofBijective f hf)).symm
    rw [hbij, Nat.card_prod, Nat.card_zpowers, Nat.card_zpowers, h.hypA.ord, hc3]
  have hbCb : b ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hbCτ : b ∈ Subgroup.centralizer ({τ} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le hτc.tau_mem)).symm
  have hbNb1 : b ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) := by
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    have hxcomm : x * b = b * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le (SettingCore.tor_le z hx))
    rw [show b * x * b⁻¹ = x by rw [← hxcomm]; group]
    exact hx
  have hcCb : c ∈ Subgroup.centralizer ({b} : Set G) := h.hypA.le hτc.c_mem
  have hcCτ : c ∈ Subgroup.centralizer ({τ} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hτc.comm
  have hcNb1 : c ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) := by
    refine mem_nor_of_closure (S := Set.range (zs z)) fun s hs => ?_
    obtain ⟨i, rfl⟩ := hs
    refine Subgroup.subset_closure ?_
    fin_cases i
    · exact ⟨1, hτc.cyc₀.symm⟩
    · exact ⟨2, hτc.cyc₁.symm⟩
    · exact ⟨0, hτc.cyc₂.symm⟩
  have hgb_comm : g * b = b * g := by
    calc g * b = g * b * g⁻¹ * g := by group
      _ = b * g := by rw [hgb]
  have hgCb : g ∈ Subgroup.centralizer ({b} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hgb_comm
  have hgCτ : g ∈ Subgroup.centralizer ({τ} : Set G) := (hTW hgT).1
  have hgNb1 : g ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) := by
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    have hxB2 : x ∈ B₂ := hB₂.B₁_le hx
    have hxgB2 : g * x * g⁻¹ ∈ B₂ := (Subgroup.mem_normalizer_iff.mp hgNB2 x).1 hxB2
    have hxcomm : x * b = b * x :=
      Subgroup.mem_centralizer_singleton_iff.mp (h.hypA.le (SettingCore.tor_le z hx))
    have hgb' : g⁻¹ * b * g = b := by
      have hh := congrArg (fun y => g⁻¹ * y * g) hgb
      have hb : g⁻¹ * (g * b * g⁻¹) * g = b := by group
      rw [hb] at hh
      exact hh.symm
    have hgb_inv : g⁻¹ * b = b * g⁻¹ := by
      have hh : (g⁻¹ * b * g) * g⁻¹ = b * g⁻¹ := by rw [hgb']
      simpa using hh
    have hcomm : g * x * g⁻¹ * b = b * (g * x * g⁻¹) := by
      calc g * x * g⁻¹ * b = g * x * (g⁻¹ * b) := by group
        _ = g * x * (b * g⁻¹) := by rw [hgb_inv]
        _ = g * (x * b) * g⁻¹ := by group
        _ = g * (b * x) * g⁻¹ := by rw [hxcomm]
        _ = g * b * g⁻¹ * (g * x * g⁻¹) := by group
        _ = b * (g * x * g⁻¹) := by rw [hgb]
    exact hB₂.fix _ hxgB2 hcomm
  have hmem_b : b ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({τ} : Set G) ⊓
      Subgroup.normalizer ((bOne z : Subgroup G) : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hbCb, hbCτ⟩, hbNb1⟩
  have hmem_c : c ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({τ} : Set G) ⊓
      Subgroup.normalizer ((bOne z : Subgroup G) : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hcCb, hcCτ⟩, hcNb1⟩
  have hmem_g : g ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({τ} : Set G) ⊓
      Subgroup.normalizer ((bOne z : Subgroup G) : Set G) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hgCb, hgCτ⟩, hgNb1⟩
  have hQle : Subgroup.zpowers b ⊔ Subgroup.zpowers c ≤
      Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({τ} : Set G) ⊓
        Subgroup.normalizer ((bOne z : Subgroup G) : Set G) :=
    sup_le (Subgroup.zpowers_le.2 hmem_b) (Subgroup.zpowers_le.2 hmem_c)
  have hgle : Subgroup.zpowers g ≤
      Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({τ} : Set G) ⊓
        Subgroup.normalizer ((bOne z : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.2 hmem_g
  have hQ3 : IsPGroup 3 ↥(Subgroup.zpowers b ⊔ Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 2) (by rw [hcard_sup]; norm_num)
  have hg3 : IsPGroup 3 ↥(Subgroup.zpowers g) :=
    IsPGroup.of_card_dvd_pow (n := e) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one he')
  have hR3 : IsPGroup 3 ↥((Subgroup.zpowers b ⊔ Subgroup.zpowers c) ⊔ Subgroup.zpowers g) :=
    IsPGroup.to_sup_of_normal_left' hQ3 hg3 (Subgroup.zpowers_le.2 hgN)
  have hRle : (Subgroup.zpowers b ⊔ Subgroup.zpowers c) ⊔ Subgroup.zpowers g ≤
      Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({τ} : Set G) ⊓
        Subgroup.normalizer ((bOne z : Subgroup G) : Set G) :=
    sup_le hQle hgle
  have hcardR : Nat.card ↥((Subgroup.zpowers b ⊔ Subgroup.zpowers c) ⊔ Subgroup.zpowers g) ≤
      3 ^ 2 :=
    card_le_nine_of_isPGroup h (odd_cen h) hτc hR3 hRle
  have hReq : (Subgroup.zpowers b ⊔ Subgroup.zpowers c) ⊔ Subgroup.zpowers g =
      Subgroup.zpowers b ⊔ Subgroup.zpowers c :=
    (Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hcard_sup]; simpa using hcardR)).symm
  rw [← hReq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g)

theorem maximal_in_cen_tau {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {B₂ : Subgroup G} {τ c : G}
    (hB₂ : B2Package b z B₂) (hτc : TauC z τ c) :
    ∀ T : Subgroup G, T ≤ Subgroup.centralizer ({τ} : Set G) ⊓ Subgroup.normalizer (B₂ : Set G) →
      IsPGroup 3 T → Subgroup.zpowers b ⊔ Subgroup.zpowers c ≤ T →
        T = Subgroup.zpowers b ⊔ Subgroup.zpowers c := by
  intro T hTW hT3 hQT
  have hnil : Group.IsNilpotent ↥T :=
    IsPGroup.isNilpotent (p := 3) (hp := ⟨by norm_num⟩) hT3
  have hcond : NormalizerCondition ↥T := Group.normalizerCondition_of_isNilpotent (h := hnil)
  by_contra hne
  have hQ'lt : (Subgroup.zpowers b ⊔ Subgroup.zpowers c).subgroupOf T < ⊤ := by
    refine lt_of_le_of_ne le_top fun he => ?_
    apply hne
    apply le_antisymm _ hQT
    intro t ht
    have : (⟨t, ht⟩ : ↥T) ∈ (Subgroup.zpowers b ⊔ Subgroup.zpowers c).subgroupOf T := by
      rw [he]; trivial
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨g, hgN, hgQ'⟩ := SetLike.exists_of_lt
    (hcond ((Subgroup.zpowers b ⊔ Subgroup.zpowers c).subgroupOf T) hQ'lt)
  have hgQ : (g : G) ∉ Subgroup.zpowers b ⊔ Subgroup.zpowers c :=
    fun hq => hgQ' (Subgroup.mem_subgroupOf.mpr hq)
  have hgNQ : (g : G) ∈ Subgroup.normalizer
      (((Subgroup.zpowers b ⊔ Subgroup.zpowers c : Subgroup G)) : Set G) := by
    apply Subgroup.mem_normalizer_fintype
    intro x hx
    have hx' : (⟨x, hQT hx⟩ : ↥T) ∈ (Subgroup.zpowers b ⊔ Subgroup.zpowers c).subgroupOf T :=
      Subgroup.mem_subgroupOf.mpr hx
    have h1 : g * (⟨x, hQT hx⟩ : ↥T) * g⁻¹ ∈
        (Subgroup.zpowers b ⊔ Subgroup.zpowers c).subgroupOf T :=
      ((Subgroup.mem_normalizer_iff.mp hgN (⟨x, hQT hx⟩ : ↥T)).1 hx')
    simpa using Subgroup.mem_subgroupOf.mp h1
  exact hgQ (mem_sup_zpowers_of_mem_normalizer h hB₂ hτc hTW hT3 g.2 hgNQ)

end CFSG.StandardType.FF81.PropOne

end
