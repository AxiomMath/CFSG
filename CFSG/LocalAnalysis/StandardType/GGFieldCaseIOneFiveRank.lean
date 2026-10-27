module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseIOneRankXAbs
public import CFSG.LocalAnalysis.StandardType.GGPropFourOneThompson
public import Mathlib.Tactic.Module
public import Mathlib.Data.Nat.Prime.Int

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Core

variable {G : Type*} [Group G]

theorem exists_zpow_mul_zpow_eq_one_of_isCyclic {C : Subgroup G} [IsCyclic C] [Finite C] {p : ℕ}
    [hp : Fact p.Prime] {a b : G} (ha : a ∈ C) (hb : b ∈ C) (hap : a ^ p = 1) (hbp : b ^ p = 1) :
    ∃ i j : ℤ, ¬ ((p : ℤ) ∣ i ∧ (p : ℤ) ∣ j) ∧ a ^ i * b ^ j = 1 := by
  have hp1 : ¬ (p : ℤ) ∣ 1 := by
    intro h
    exact hp.out.not_dvd_one (Int.natCast_dvd_natCast.mp (by simpa using h))
  by_cases h1 : a = 1
  · exact ⟨1, 0, fun h => hp1 h.1, by simp [h1]⟩
  set a' : C := ⟨a, ha⟩
  set b' : C := ⟨b, hb⟩
  have hoa : orderOf a' = p := orderOf_eq_prime (Subtype.ext (by simpa [a'] using hap))
    (fun h => h1 (by simpa [a'] using congrArg Subtype.val h))
  have hle : Subgroup.zpowers b' ≤ Subgroup.zpowers a' := by
    rw [IsCyclic.subgroup_le_iff_card_dvd, Nat.card_zpowers, Nat.card_zpowers, hoa]
    exact orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa [b'] using hbp))
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hle (Subgroup.mem_zpowers b'))
  have hm' : a ^ m = b := by simpa [a', b'] using congrArg Subtype.val hm
  refine ⟨-m, 1, fun h => hp1 h.2, ?_⟩
  rw [← hm']
  group

private theorem conj_inv_zpow_aux (g t : G) (n : ℤ) : (g⁻¹ * t * g) ^ n = g⁻¹ * t ^ n * g := by
  have := map_zpow (MulAut.conj g⁻¹) t n
  simpa [MulAut.conj_apply] using this.symm

private theorem conj_inv_pow_aux (g t : G) (n : ℕ) : (g⁻¹ * t * g) ^ n = g⁻¹ * t ^ n * g := by
  have := map_pow (MulAut.conj g⁻¹) t n
  simpa [MulAut.conj_apply] using this.symm

theorem normalizer_le_normalizer_of_rank_three [Finite G] {p s : ℕ} [hp : Fact p.Prime]
    (hs : 1 ≤ s) {U U₁ V H C : Subgroup G} [IsCyclic C] (hVC : ∀ v ∈ V, v ^ p = 1 → v ∈ C)
    (hpU : IsPGroup p U) (hU₁U : U₁ ≤ U) (hUN : U ≤ Subgroup.normalizer (U₁ : Set G))
    (hcyc : ∃ u₀ ∈ U, U ≤ Subgroup.zpowers u₀ ⊔ U₁)
    (hcomm : ∀ a ∈ U₁, ∀ b ∈ U₁, a * b * a⁻¹ * b⁻¹ ∈ V)
    (hHU : H ≤ U₁) (hHc : ∀ a ∈ H, ∀ b ∈ H, a * b = b * a)
    (hexp : ∀ h ∈ H, h ^ p ^ s = 1)
    (hpow : ∀ w ∈ U, w ∉ U₁ → w ^ p ∈ U₁ →
      ∃ k : ℕ, ¬ p ∣ k ∧ ∀ h ∈ H, w⁻¹ * h * w = h ^ (1 + p ^ (s - 1) * k))
    (h3 : ∃ h₁ ∈ H, ∃ h₂ ∈ H, ∃ h₃ ∈ H, ∀ i j l : ℤ,
      h₁ ^ ((p ^ (s - 1) : ℕ) * i) * h₂ ^ ((p ^ (s - 1) : ℕ) * j) *
        h₃ ^ ((p ^ (s - 1) : ℕ) * l) = 1 →
      (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j ∧ (p : ℤ) ∣ l) :
    Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (U₁ : Set G) := by
  intro g hg
  by_contra hgN
  have hgU : ∀ y ∈ U, g * y * g⁻¹ ∈ U := fun y hy => (Subgroup.mem_normalizer_iff.mp hg y).mp hy
  have hgU' : ∀ y ∈ U, g⁻¹ * y * g ∈ U := fun y hy => by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hy
  obtain ⟨u, hu, hwu⟩ : ∃ u ∈ U₁, g * u * g⁻¹ ∉ U₁ := by
    by_contra hall
    push Not at hall
    apply hgN
    have hmap : U₁.map (MulAut.conj g).toMonoidHom ≤ U₁ := by
      rintro _ ⟨v, hv, rfl⟩
      exact hall v hv
    have heq : U₁.map (MulAut.conj g).toMonoidHom = U₁ :=
      Subgroup.eq_of_le_of_card_ge hmap
        (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨hall n, fun hn => ?_⟩
    rw [← heq] at hn
    obtain ⟨m, hm, hmn⟩ := hn
    have : m = n := by
      simpa [MulAut.conj_apply] using hmn
    exact this ▸ hm
  set w₀ := g * u * g⁻¹ with hw₀
  have hw₀U : w₀ ∈ U := hgU u (hU₁U hu)
  obtain ⟨N, hN⟩ := hpU ⟨w₀, hw₀U⟩
  have hN' : w₀ ^ p ^ N = 1 := by simpa using congrArg Subtype.val hN
  have hex : ∃ j, w₀ ^ p ^ (j + 1) ∈ U₁ := ⟨N, by
    rw [pow_succ, pow_mul, hN', one_pow]; exact U₁.one_mem⟩
  classical
  set j₀ := Nat.find hex with hj₀
  set u' := u ^ p ^ j₀ with hu'
  have hu'U₁ : u' ∈ U₁ := U₁.pow_mem hu _
  have hw : w₀ ^ p ^ j₀ = g * u' * g⁻¹ := by rw [hw₀, conj_pow]
  set w := g * u' * g⁻¹ with hwdef
  have hwU : w ∈ U := hgU _ (hU₁U hu'U₁)
  have hwp : w ^ p ∈ U₁ := by
    rw [← hw, ← pow_mul, ← pow_succ]
    exact Nat.find_spec hex
  have hwn : w ∉ U₁ := by
    rw [← hw]
    rcases Nat.eq_zero_or_pos j₀ with h0 | hpos
    · rw [h0]; simpa using hwu
    · obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
      have := Nat.find_min hex (show j < j₀ by omega)
      rwa [hj] at *
  obtain ⟨k, hkp, hk⟩ := hpow w hwU hwn hwp
  have key : ∀ h ∈ H, g⁻¹ * h * g ∈ U₁ → g⁻¹ * h ^ (p ^ (s - 1) * k) * g ∈ V := by
    intro h hh hhg
    have hc := hcomm _ (U₁.inv_mem hhg) _ (U₁.inv_mem hu'U₁)
    have e1 : h⁻¹ * (w⁻¹ * h * w) = h ^ (p ^ (s - 1) * k) := by
      rw [hk h hh, pow_add, pow_one]; group
    have e2 : (g⁻¹ * h * g)⁻¹ * u'⁻¹ * (g⁻¹ * h * g)⁻¹⁻¹ * u'⁻¹⁻¹ =
        g⁻¹ * (h⁻¹ * (w⁻¹ * h * w)) * g := by
      rw [hwdef]; group
    rw [e2, e1] at hc
    exact hc
  haveI hnorm : (U₁.subgroupOf U).Normal :=
    (Subgroup.normal_subgroupOf_iff hU₁U).mpr fun a b ha hb =>
      (Subgroup.mem_normalizer_iff.mp (hUN hb) a).mp ha
  obtain ⟨u₀, hu₀, hU⟩ := hcyc
  have hz : Subgroup.zpowers u₀ ≤ Subgroup.normalizer (U₁ : Set G) :=
    (Subgroup.zpowers_le).mpr (hUN hu₀)
  haveI hQcyc : IsCyclic (U ⧸ U₁.subgroupOf U) := by
    refine ⟨⟨QuotientGroup.mk ⟨u₀, hu₀⟩, fun q => ?_⟩⟩
    induction q using QuotientGroup.induction_on with
    | H y =>
      have hy : (y : G) ∈ ((Subgroup.zpowers u₀ ⊔ U₁ : Subgroup G) : Set G) := hU y.2
      rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hz] at hy
      obtain ⟨a, ha, z, hz', hyz⟩ := hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      rw [← QuotientGroup.mk_zpow, QuotientGroup.eq]
      have : (((⟨u₀, hu₀⟩ : U) ^ n)⁻¹ * y : U) = ⟨z, hU₁U hz'⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
        rw [← hyz]; group
      rw [this, Subgroup.mem_subgroupOf]
      exact hz'
  have hQp : IsPGroup p (U ⧸ U₁.subgroupOf U) := hpU.to_quotient _
  have htot : ∀ c c' : U ⧸ U₁.subgroupOf U,
      Subgroup.zpowers c ≤ Subgroup.zpowers c' ∨ Subgroup.zpowers c' ≤ Subgroup.zpowers c := by
    intro c c'
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (hQp.to_subgroup (Subgroup.zpowers c))
    obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp (hQp.to_subgroup (Subgroup.zpowers c'))
    rw [IsCyclic.subgroup_le_iff_card_dvd, IsCyclic.subgroup_le_iff_card_dvd, ha, hb]
    rcases le_total a b with hab | hab
    · exact Or.inl (Nat.pow_dvd_pow p hab)
    · exact Or.inr (Nat.pow_dvd_pow p hab)
  let cl : ∀ h ∈ H, U ⧸ U₁.subgroupOf U := fun h hh =>
    QuotientGroup.mk ⟨g⁻¹ * h * g, hgU' h (hU₁U (hHU hh))⟩
  have core : ∀ (a b c : G) (ha : a ∈ H) (hb : b ∈ H) (hc : c ∈ H),
      (∀ i j l : ℤ, a ^ ((p ^ (s - 1) : ℕ) * i) * b ^ ((p ^ (s - 1) : ℕ) * j) *
        c ^ ((p ^ (s - 1) : ℕ) * l) = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j ∧ (p : ℤ) ∣ l) →
      cl b hb ∈ Subgroup.zpowers (cl a ha) → cl c hc ∈ Subgroup.zpowers (cl a ha) → False := by
    intro a b c ha hb hc hind hba hca
    have hlift : ∀ d (hd : d ∈ H), cl d hd ∈ Subgroup.zpowers (cl a ha) →
        ∃ m : ℤ, g⁻¹ * (a ^ (-m) * d) * g ∈ U₁ := by
      intro d hd hda
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hda
      refine ⟨m, ?_⟩
      rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hm
      convert hm using 1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
      rw [conj_inv_zpow_aux]
      group
    obtain ⟨m, hm⟩ := hlift b hb hba
    obtain ⟨m', hm'⟩ := hlift c hc hca
    have hy2 : a ^ (-m) * b ∈ H := H.mul_mem (H.zpow_mem ha _) hb
    have hy3 : a ^ (-m') * c ∈ H := H.mul_mem (H.zpow_mem ha _) hc
    have hA := key _ hy2 hm
    have hB := key _ hy3 hm'
    have hpow1 : ∀ y ∈ H, (g⁻¹ * y ^ (p ^ (s - 1) * k) * g) ^ p = 1 := by
      intro y hy
      rw [conj_inv_pow_aux, ← pow_mul, show p ^ (s - 1) * k * p = p ^ s * k by
        rw [mul_comm (p ^ (s - 1)) k, mul_assoc, ← pow_succ, Nat.sub_add_cancel hs, mul_comm],
        pow_mul, hexp y hy, one_pow]
      group
    obtain ⟨i, j, hij, hijeq⟩ := exists_zpow_mul_zpow_eq_one_of_isCyclic (C := C)
      (hVC _ hA (hpow1 _ hy2)) (hVC _ hB (hpow1 _ hy3)) (hpow1 _ hy2) (hpow1 _ hy3)
    have h' : ((a ^ (-m) * b) ^ (p ^ (s - 1) * k)) ^ i *
        ((a ^ (-m') * c) ^ (p ^ (s - 1) * k)) ^ j = 1 := by
      rw [conj_inv_zpow_aux, conj_inv_zpow_aux] at hijeq
      have := congrArg (fun r => g * r * g⁻¹) hijeq
      simpa [mul_assoc] using this
    have hrel : (a ^ (-m) * b) ^ ((p ^ (s - 1) * k : ℕ) * i) *
        (a ^ (-m') * c) ^ ((p ^ (s - 1) * k : ℕ) * j) = 1 := by
      rw [zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
      exact h'
    letI : CommGroup H :=
      { (inferInstance : Group H) with mul_comm := fun x y => Subtype.ext (hHc x x.2 y y.2) }
    set A : H := ⟨a, ha⟩
    set B : H := ⟨b, hb⟩
    set C' : H := ⟨c, hc⟩
    have hexpandH : (A ^ (-m) * B) ^ ((p ^ (s - 1) * k : ℕ) * i) *
        (A ^ (-m') * C') ^ ((p ^ (s - 1) * k : ℕ) * j) =
        A ^ ((p ^ (s - 1) : ℕ) * (-(k * m * i) - k * m' * j)) *
          B ^ ((p ^ (s - 1) : ℕ) * (k * i)) * C' ^ ((p ^ (s - 1) : ℕ) * (k * j)) := by
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      push_cast
      module
    have hrelH : (A ^ (-m) * B) ^ ((p ^ (s - 1) * k : ℕ) * i) *
        (A ^ (-m') * C') ^ ((p ^ (s - 1) * k : ℕ) * j) = 1 := by
      apply Subtype.ext
      simpa [A, B, C'] using hrel
    rw [hexpandH] at hrelH
    have hrel3 := congrArg Subtype.val hrelH
    simp only [Subgroup.coe_mul, Subgroup.coe_zpow, OneMemClass.coe_one, A, B, C'] at hrel3
    obtain ⟨-, hi, hj⟩ := hind _ _ _ hrel3
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
    have hkZ : ¬ (p : ℤ) ∣ (k : ℤ) := fun h => hkp (Int.natCast_dvd_natCast.mp h)
    exact hij ⟨(hpZ.dvd_or_dvd hi).resolve_left hkZ, (hpZ.dvd_or_dvd hj).resolve_left hkZ⟩
  obtain ⟨h₁, hh₁, h₂, hh₂, h₃, hh₃, hind⟩ := h3
  have sw12 : ∀ (x y z : G), x ∈ H → y ∈ H → z ∈ H → ∀ a b c : ℤ,
      x ^ a * y ^ b * z ^ c = y ^ b * x ^ a * z ^ c := fun x y z hx hy _ a b c => by
    rw [((show Commute x y from hHc x hx y hy).zpow_zpow a b).eq]
  have sw23 : ∀ (x y z : G), x ∈ H → y ∈ H → z ∈ H → ∀ a b c : ℤ,
      x ^ a * y ^ b * z ^ c = x ^ a * z ^ c * y ^ b := fun x y z _ hy hz a b c => by
    rw [mul_assoc, ((show Commute y z from hHc y hy z hz).zpow_zpow b c).eq, ← mul_assoc]
  have mem : ∀ c c' : U ⧸ U₁.subgroupOf U, Subgroup.zpowers c ≤ Subgroup.zpowers c' →
      c ∈ Subgroup.zpowers c' := fun c c' h => h (Subgroup.mem_zpowers c)
  have i1 := core h₁ h₂ h₃ hh₁ hh₂ hh₃ hind
  have i2 := core h₂ h₁ h₃ hh₂ hh₁ hh₃ (fun i j l h => by
    rw [sw12 _ _ _ hh₂ hh₁ hh₃] at h
    obtain ⟨a, b, c⟩ := hind j i l h
    exact ⟨b, a, c⟩)
  have i3 := core h₃ h₁ h₂ hh₃ hh₁ hh₂ (fun i j l h => by
    rw [sw12 _ _ _ hh₃ hh₁ hh₂, sw23 _ _ _ hh₁ hh₃ hh₂] at h
    obtain ⟨a, b, c⟩ := hind j l i h
    exact ⟨c, a, b⟩)
  rcases htot (cl h₁ hh₁) (cl h₂ hh₂) with h12 | h21
  · rcases htot (cl h₂ hh₂) (cl h₃ hh₃) with h23 | h32
    · exact i3 (mem _ _ (h12.trans h23)) (mem _ _ h23)
    · exact i2 (mem _ _ h12) (mem _ _ h32)
  · rcases htot (cl h₁ hh₁) (cl h₃ hh₃) with h13 | h31
    · exact i3 (mem _ _ h13) (mem _ _ (h21.trans h13))
    · exact i1 (mem _ _ h21) (mem _ _ h31)

end Core

@[expose] def GGL45FiveRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGL45Config p B Bs x L D J X B₂ d y K U U₁ → Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D →
    (∀ v ∈ U ⊓ Subgroup.centralizer (K : Set G), v ^ p = 1 → v ∈ Subgroup.zpowers d) →
      (((∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a) → ∀ A ∈ thompsonAbelianSubgroups U, A = U₁) ∧
        ∀ g ∈ Subgroup.normalizer (U : Set G), g ∉ Subgroup.normalizer (U₁ : Set G) →
          ∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a) ∨
      ∃ s : ℕ, 1 ≤ s ∧ U ⊓ K ≤ U₁ ∧ (∀ a ∈ U ⊓ K, ∀ b ∈ U ⊓ K, a * b = b * a) ∧
        (∀ h ∈ U ⊓ K, h ^ p ^ s = 1) ∧
        (∀ w ∈ U, w ∉ U₁ → w ^ p ∈ U₁ →
          ∃ k : ℕ, ¬ p ∣ k ∧ ∀ h ∈ U ⊓ K, w⁻¹ * h * w = h ^ (1 + p ^ (s - 1) * k)) ∧
        ∃ h₁ ∈ U ⊓ K, ∃ h₂ ∈ U ⊓ K, ∃ h₃ ∈ U ⊓ K, ∀ i j l : ℤ,
          h₁ ^ ((p ^ (s - 1) : ℕ) * i) * h₂ ^ ((p ^ (s - 1) : ℕ) * j) *
            h₃ ^ ((p ^ (s - 1) : ℕ) * l) = 1 →
          (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j ∧ (p : ℤ) ∣ l

theorem ggL45FiveIOneInput_of_rank (hT : GGL45TorusIOneInput) (hpc : GGRawPCyclicOn GGNotD4Three)
    (hD4 : GGL45CyclicD4IOneInput) (hR : GGL45FiveRankInput) : GGL45FiveIOneInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hcfg hI1 _ _ hΩ _ r hr _
  haveI : Fact p.Prime := ⟨hcfg.prime⟩
  suffices hN : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (U₁ : Set G) from hN hr.1
  rcases hR G p B Bs x L D J X B₂ d y K U U₁ hcfg hI1 hΩ with
    ⟨hJ, hab⟩ | ⟨s, hs, hHU, hHc, hexp, hpow, h3⟩
  · intro g hg
    by_contra hgN
    exact hgN (normalizer_le_normalizer_of_forall_eq (hJ (hab g hg hgN)) hg)
  · obtain ⟨_, -, hcomm, -⟩ := hT G p B Bs x L D J X B₂ d y K U U₁ hcfg hI1
    exact normalizer_le_normalizer_of_rank_three (C := Subgroup.zpowers d) hs hΩ
      hcfg.2.2.2.2.2.2.1.2.1 hcfg.2.2.2.2.2.2.2.1.2.1 hcfg.2.2.2.2.2.2.2.2
      (hcfg.exists_cyclic_of_iOne hpc hD4 hI1) hcomm hHU hHc hexp hpow h3

end CFSG.StandardType
