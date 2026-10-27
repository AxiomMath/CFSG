module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rl
import CFSG.Goldschmidt.Steps.Components

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

section Rank

theorem uc22p22r_pRank_map_le {G' : Type} [Group G'] [Finite G'] {p : ℕ} (hp : p.Prime) (f : G →* G')
    {A : Subgroup G} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    CFSG.Open.pRank p (A.map f) ≤ CFSG.Open.pRank p A := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨E, hEA, hE, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (A.map f)
  set P : Subgroup G := A ⊓ E.comap f with hPdef
  have hPc : ∀ a b : ↥P, a * b = b * a := fun a b => Subtype.ext (hA a a.2.1 b b.2.1)
  let φ : ↥P →* ↥P :=
    { toFun := fun a => a ^ p
      map_one' := one_pow p
      map_mul' := fun a b => (Commute.mul_pow (hPc a b) p) }
  let ψ : ↥P →* ↥E := (f.comp P.subtype).codRestrict E (fun a => a.2.2)
  have hψ : Function.Surjective ψ := by
    rintro ⟨e, he⟩
    obtain ⟨a, ha, hae⟩ := hEA he
    refine ⟨⟨a, ha, ?_⟩, Subtype.ext ?_⟩
    · show f a ∈ E
      rw [hae]
      exact he
    · show f a = e
      exact hae
  have hrange : φ.range ≤ ψ.ker := by
    rintro _ ⟨a, rfl⟩
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    show f ((a : G) ^ p) = 1
    rw [map_pow]
    exact hE.2 _ (ψ a).2
  have h1 : Nat.card ↥P = Nat.card ↥E * Nat.card ψ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψ).toEquiv]
  have h2 : Nat.card ↥P = Nat.card φ.ker * Nat.card φ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, mul_comm]
  have h3 : Nat.card φ.range ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hrange
  have hpos : 0 < Nat.card φ.range := Nat.card_pos
  have hEle : Nat.card ↥E ≤ Nat.card φ.ker := by
    by_contra hlt
    push Not at hlt
    have : Nat.card φ.ker * Nat.card φ.range < Nat.card ↥E * Nat.card ψ.ker :=
      (Nat.mul_lt_mul_of_pos_right hlt hpos).trans_le (Nat.mul_le_mul_left _ h3)
    omega
  set Ω : Subgroup G := φ.ker.map P.subtype with hΩ
  have hΩA : Ω ≤ A := fun _ ⟨a, _, hae⟩ => hae ▸ a.2.1
  have hΩcard : Nat.card Ω = Nat.card φ.ker :=
    Nat.card_congr (Subgroup.equivMapOfInjective φ.ker P.subtype P.subtype_injective).toEquiv.symm
  have hΩe : IsElemAbelian p Ω := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
    · obtain ⟨a', -, ha'⟩ := a.2
      obtain ⟨b', -, hb'⟩ := b.2
      show (a : G) * b = b * a
      rw [← ha', ← hb']
      exact hA _ a'.2.1 _ b'.2.1
    · rintro _ ⟨a, ha, rfl⟩
      have : φ a = 1 := ha
      exact congrArg Subtype.val this
  have hΩp : IsPGroup p Ω := fun g => ⟨1, by
    apply Subtype.ext
    simpa using hΩe.2 g g.2⟩
  obtain ⟨j, hj⟩ := hΩp.exists_card_eq
  have hkj : CFSG.Open.pRank p (A.map f) ≤ j := by
    have h4 : p ^ CFSG.Open.pRank p (A.map f) ≤ p ^ j := by
      rw [← hcard, ← hj, hΩcard]
      exact hEle
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h4
  exact hkj.trans (CFSG.SectionRank.le_pRank hp.one_lt hΩA hΩe hj)

end Rank

section Odd

theorem uc22p22r_mem_of_two_power_odd {K B : Subgroup G} {m : ℕ} (hm : Odd m)
    (hBK : B ≤ normalizer (K : Set G)) (hBm : ∀ u ∈ B, u ^ m = 1) {k u t : G} (hk : k ∈ K) (hu : u ∈ B)
    (htku : t = k * u) (ht : ∃ a : ℕ, t ^ 2 ^ a = 1) : t ∈ K := by
  obtain ⟨a, ha⟩ := ht
  have hnorm : ∀ j : ℕ, ∀ y ∈ K, u ^ j * y * (u ^ j)⁻¹ ∈ K := by
    intro j y hy
    have hj : u ^ j ∈ normalizer (K : Set G) := Subgroup.pow_mem _ (hBK hu) j
    exact (Subgroup.mem_normalizer_iff.1 hj y).1 hy
  obtain ⟨κ, hκ, hpow⟩ := uc22p22r_pow_mul_mem (K := K) (k := k) (u := u) hk (fun j => hnorm j k hk) hnorm (2 ^ a)
  have hu2 : u ^ 2 ^ a ∈ K := by
    have h1 : κ * u ^ 2 ^ a = 1 := by rw [← hpow, ← htku, ha]
    have h2 : u ^ 2 ^ a = κ⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [h2]
    exact K.inv_mem hκ
  have hcop : Nat.Coprime m (2 ^ a) := Nat.Coprime.pow_right a (Nat.coprime_two_right.2 hm)
  obtain ⟨r, s, hrs⟩ : ∃ r s : ℤ, (m : ℤ) * r + (2 ^ a : ℕ) * s = 1 := by
    obtain ⟨r, s, h⟩ := Nat.isCoprime_iff_coprime.2 hcop
    exact ⟨r, s, by simpa [mul_comm] using h⟩
  have hu1 : u = (u ^ 2 ^ a) ^ s := by
    have hm1 : u ^ (m : ℤ) = 1 := by simpa using hBm u hu
    calc u = u ^ ((m : ℤ) * r + (2 ^ a : ℕ) * s) := by rw [hrs, zpow_one]
      _ = (u ^ (m : ℤ)) ^ r * (u ^ ((2 ^ a : ℕ) : ℤ)) ^ s := by
        rw [zpow_add, zpow_mul, zpow_mul]
      _ = (u ^ 2 ^ a) ^ s := by rw [hm1, one_zpow, one_mul, zpow_natCast]
  have huK : u ∈ K := by
    rw [hu1]
    exact K.zpow_mem hu2 s
  rw [htku]
  exact K.mul_mem hk huK

theorem uc22p22r_permutes_inf_odd {K B T : Subgroup G} {m : ℕ} (hm : Odd m)
    (hBm : ∀ u ∈ B, u ^ m = 1) (hBK : B ≤ normalizer (K : Set G)) (hT : IsPGroup 2 T)
    (hBT : Permutes B T) : Permutes B (T ⊓ K) := by
  unfold Permutes at hBT ⊢
  have h2 : ∀ t ∈ T, ∃ a : ℕ, t ^ 2 ^ a = 1 := by
    intro t ht
    obtain ⟨a, ha⟩ := hT ⟨t, ht⟩
    exact ⟨a, by simpa using congrArg Subtype.val ha⟩
  ext z
  constructor
  · rintro ⟨x, hx, t, ht, rfl⟩
    have hmem : x * t ∈ (T : Set G) * (B : Set G) := by
      rw [← hBT]
      exact ⟨x, hx, t, ht.1, rfl⟩
    obtain ⟨t', ht', x', hx', hxt⟩ := hmem
    have hk : x * t * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 (hBK hx) t).1 ht.2
    have hu : x * x'⁻¹ ∈ B := B.mul_mem hx (B.inv_mem hx')
    have htku : t' = (x * t * x⁻¹) * (x * x'⁻¹) := by
      have : t' = x * t * x'⁻¹ := by rw [← hxt]; group
      rw [this]
      group
    have ht'K := uc22p22r_mem_of_two_power_odd hm hBK hBm hk hu htku (h2 t' ht')
    exact ⟨t', ⟨ht', ht'K⟩, x', hx', hxt⟩
  · rintro ⟨t, ht, x, hx, rfl⟩
    have hmem : t * x ∈ (B : Set G) * (T : Set G) := by
      rw [hBT]
      exact ⟨t, ht.1, x, hx, rfl⟩
    obtain ⟨x', hx', t', ht', hxt⟩ := hmem
    have hk : x'⁻¹ * t * x' ∈ K := by
      have h := (Subgroup.mem_normalizer_iff.1 (hBK (B.inv_mem hx')) t).1 ht.2
      simpa using h
    have hu : x'⁻¹ * x ∈ B := B.mul_mem (B.inv_mem hx') hx
    have htku : t' = (x'⁻¹ * t * x') * (x'⁻¹ * x) := by
      have : t' = x'⁻¹ * (t * x) := by rw [← hxt]; group
      rw [this]
      group
    have ht'K := uc22p22r_mem_of_two_power_odd hm hBK hBm hk hu htku (h2 t' ht')
    exact ⟨x', hx', t', ⟨ht', ht'K⟩, hxt⟩

end Odd

section Hall

variable {K B : Subgroup G} (hBK : B ≤ normalizer (K : Set G))

theorem uc22p22rImg_eq_map (A : Subgroup G) :
    uc22p22rImg hBK A = (A.subgroupOf (K ⊔ B)).map (uc22p22rPi K B hBK) := by
  ext g
  rw [uc22p22r_mem_img, Subgroup.mem_map]
  simp only [Subgroup.mem_subgroupOf]

theorem uc22p22r_rho_ne_one_of_le {M : Subgroup G} {x : G} {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hxB : x ∈ B) (hxq : x ^ q = 1) (hKq : CFSG.Open.IsQuasisimple (Bar2 K))
    (hO2 : pCoreOf 2 K ≤ M)
    (h0 : ∀ Y : Subgroup G, Subgroup.zpowers x ≤ Y → Y ≤ M → ∀ n ∈ K ⊔ B, n ∈ normalizer (Y : Set G) →
      n ∈ M)
    (hxM : x ∈ M) (hKM : ¬ K ≤ M) :
    uc22p22rRho K B hBK ⟨x, Subgroup.mem_sup_right hxB⟩ ≠ 1 := by
  intro h1
  apply hKM
  have hxK : x ∈ normalizer (K : Set G) := hBK hxB
  set nx : ↥(K ⊔ B) := ⟨x, Subgroup.mem_sup_right hxB⟩ with hnx
  have hα : ∀ k : Bar2 K, uc22p22rRho1 K B hBK nx k * k⁻¹ ∈ Subgroup.center (Bar2 K) := by
    intro k
    have h2 : uc22p22rRho K B hBK nx (QuotientGroup.mk k : uc22p22rKt K) =
        (QuotientGroup.mk k : uc22p22rKt K) := by
      rw [h1]
      rfl
    rw [uc22p22rRho_mk] at h2
    have h3 := QuotientGroup.eq.1 h2
    have hz := Subgroup.inv_mem _ h3
    have hc := Subgroup.mem_center_iff.1 hz (uc22p22rRho1 K B hBK nx k)
    have e : uc22p22rRho1 K B hBK nx k * k⁻¹ =
        (uc22p22rRho1 K B hBK nx k) * ((uc22p22rRho1 K B hBK nx k)⁻¹ * k)⁻¹ *
          (uc22p22rRho1 K B hBK nx k)⁻¹ := by group
    rw [e, hc]
    simpa using hz
  have hα1 : uc22p22rRho1 K B hBK nx = 1 := CFSG.Goldschmidt.N8f (Bar2 K) hKq _ hα
  have htriv : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
    intro k hk
    have h2 := DFunLike.congr_fun hα1 (QuotientGroup.mk ⟨k, hk⟩ : Bar2 K)
    rw [uc22p22rRho1_mk] at h2
    have h3 := QuotientGroup.eq.1 (show (QuotientGroup.mk (uc22p22rRho0 K B hBK nx ⟨k, hk⟩) : Bar2 K) =
      QuotientGroup.mk ⟨k, hk⟩ from h2)
    have h4 : (x * k * x⁻¹)⁻¹ * k ∈ pCoreOf 2 K := by
      have h5 : (((uc22p22rRho0 K B hBK nx ⟨k, hk⟩)⁻¹ * ⟨k, hk⟩ : ↥K)) ∈ CFSG.pCore 2 ↥K := h3
      have h6 : ((((uc22p22rRho0 K B hBK nx ⟨k, hk⟩)⁻¹ * ⟨k, hk⟩ : ↥K)) : G) ∈ pCoreOf 2 K :=
        ⟨_, h5, rfl⟩
      have e : ((((uc22p22rRho0 K B hBK nx ⟨k, hk⟩)⁻¹ * ⟨k, hk⟩ : ↥K)) : G) = (x * k * x⁻¹)⁻¹ * k := by
        simp [uc22p22rRho0_apply, hnx]
      rw [e] at h6
      exact h6
    have h7 := uc22p22f_conj_mem_pCoreOf_self hk ((pCoreOf 2 K).inv_mem h4)
    have e : k * ((x * k * x⁻¹)⁻¹ * k)⁻¹ * k⁻¹ = x * k * x⁻¹ * k⁻¹ := by group
    rwa [e] at h7
  have hC : ∀ k ∈ K, x * k * x⁻¹ = k → k ∈ M := by
    intro k hk hcomm
    have hkc : ∀ a ∈ Subgroup.zpowers x, k * a * k⁻¹ = a := by
      intro a ha
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      have hc : Commute k x := by
        have : x * k = k * x := by
          calc x * k = (x * k * x⁻¹) * x := by group
            _ = k * x := by rw [hcomm]
        exact this.symm
      exact (hc.zpow_right i).eq ▸ by group
    have hkN : k ∈ normalizer ((Subgroup.zpowers x : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro a
      constructor
      · intro ha
        rw [hkc a ha]
        exact ha
      · intro ha
        have h2 : k * (k * a * k⁻¹) * k⁻¹ = k * a * k⁻¹ := hkc _ ha
        have h3 : a = k * a * k⁻¹ := by
          calc a = k⁻¹ * (k * a * k⁻¹) * k := by group
            _ = k⁻¹ * (k * (k * a * k⁻¹) * k⁻¹) * k := by rw [h2]
            _ = k * a * k⁻¹ := by group
        rw [h3]
        exact ha
    exact h0 (Subgroup.zpowers x) le_rfl (Subgroup.zpowers_le.2 hxM) k (Subgroup.mem_sup_left hk) hkN
  exact uc22p22r_le_of_trivial_action hq hq2 hxq hxK htriv hC hO2

theorem uc22p22r_sylow_img_odd {T' : Subgroup G} (hBo : Odd (Nat.card B))
    (hT' : CFSG.ABGLocalTools.IsSylowOf 2 T' K) :
    CFSG.ABGLocalTools.IsSylowOf 2 (uc22p22rImg hBK T') ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT'K := hT'.le
  have hKN : K ≤ K ⊔ B := le_sup_left
  haveI : (K.subgroupOf (K ⊔ B)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKN).2 (uc22p22r_sup_le_normalizer hBK)
  have hsurj : Function.Surjective ((QuotientGroup.mk' (K.subgroupOf (K ⊔ B))).comp
      (Subgroup.inclusion (le_sup_right : B ≤ K ⊔ B))) := by
    intro c
    obtain ⟨⟨n, hn⟩, rfl⟩ := QuotientGroup.mk'_surjective _ c
    have hnmem : n ∈ (K : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left K B hBK]
      exact hn
    obtain ⟨k, hk, x₁, hx₁, rfl⟩ := hnmem
    refine ⟨⟨x₁, hx₁⟩, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := (Subgroup.mem_normalizer_iff.1 (hBK (Subgroup.inv_mem _ hx₁)) k).1 hk
    simpa [mul_assoc] using h
  have hdvd : Nat.card (↥(K ⊔ B) ⧸ K.subgroupOf (K ⊔ B)) ∣ Nat.card ↥B :=
    Subgroup.card_dvd_of_surjective hsurj
  have hodd2 : ¬ 2 ∣ K.relIndex (K ⊔ B) := by
    intro h2
    have h3 : K.relIndex (K ⊔ B) = Nat.card (↥(K ⊔ B) ⧸ K.subgroupOf (K ⊔ B)) := by
      rw [Subgroup.relIndex, Subgroup.index_eq_card]
    rw [h3] at h2
    have h4 := h2.trans hdvd
    exact (Nat.not_even_iff_odd.2 hBo) (even_iff_two_dvd.2 h4)
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 (T'.subgroupOf (K ⊔ B)) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    refine ⟨le_top, hT'.isPGroup.comap_subtype, ?_⟩
    rw [Subgroup.relIndex_top_right]
    have h1 : (T'.subgroupOf (K ⊔ B)).index = T'.relIndex (K ⊔ B) := rfl
    rw [h1, ← Subgroup.relIndex_mul_relIndex T' K (K ⊔ B) hT'K hKN]
    have hodd1 : ¬ 2 ∣ T'.relIndex K := (CFSG.ABGLocalTools.isSylowOf_iff.1 hT').2.2
    intro hdvd'
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 hdvd' with h | h
    · exact hodd1 h
    · exact hodd2 h
  rw [uc22p22rImg_eq_map]
  exact uc22p22r_isSylowOf_map_top (uc22p22rPi_surjective hBK) hSyl

end Hall

end CFSG.LocalAnalysis.UniquenessCase.UC22
