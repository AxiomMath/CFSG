module

public import CFSG.RankThree.PartOne.S12.Sec159FiveCfg
public import CFSG.RankThree.PartOne.S12.Sec159Hom

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree StrongP
open Sec159Cfg

namespace Sec159Five

variable {p : ℕ} {M : Type} [Group M] [Finite M] {X E A P N : Subgroup M} [X.Normal]
  {θ : Subgroup ↥X} [θ.Characteristic] {x : M}

theorem Cfg5.isSylowOf_map (h : Cfg5 p X E A P N θ x) :
    IsSylowOf p (P.map (QuotientGroup.mk' (actQ X θ).ker)) ⊤ := by
  refine ⟨le_top, h.Psyl.2.1.map _, ?_⟩
  rw [Subgroup.relIndex_top_right]
  intro hd
  have h1 := Subgroup.index_map_dvd (QuotientGroup.mk'_surjective (actQ X θ).ker) (H := P)
  have h2 := h.Psyl.2.2
  rw [Subgroup.relIndex_top_right] at h2
  exact h2 (hd.trans h1)

theorem Cfg5.omegaOne_map (h : Cfg5 p X E A P N θ x) :
    omegaOne p (P.map (QuotientGroup.mk' (actQ X θ).ker)) =
      E.map (QuotientGroup.mk' (actQ X θ).ker) := by
  have : Fact p.Prime := ⟨h.prime⟩
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨y, hyP, rfl⟩, hy1⟩
    have hyK : y ^ p ∈ (actQ X θ).ker := by
      have : (QuotientGroup.mk' (actQ X θ).ker) (y ^ p) = 1 := by
        rw [map_pow]; exact hy1
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    have hyX : y ^ p ∈ X := pow_mem_of_sup_eq_top h.sup h.pow_E y
    have hypP : y ^ p ∈ P := P.pow_mem hyP p
    have hmem : y ^ p ∈ (actQ X θ).ker ⊓ E ⊓ X :=
      ⟨h.ker_inf_P ▸ ⟨hyK, hypP⟩, hyX⟩
    rw [h.U_inf_X, Subgroup.mem_bot] at hmem
    have hyE : y ∈ E := h.Pomega ▸ Subgroup.subset_closure ⟨hyP, hmem⟩
    exact ⟨y, hyE, rfl⟩
  · rintro _ ⟨e, he, rfl⟩
    refine Subgroup.subset_closure ⟨⟨e, h.EP he, rfl⟩, ?_⟩
    rw [← map_pow, h.pow_E e he, map_one]

theorem Cfg5.card_map_E (h : Cfg5 p X E A P N θ x) :
    Nat.card ↥(E.map (QuotientGroup.mk' (actQ X θ).ker)) *
      Nat.card ↥((actQ X θ).ker ⊓ E : Subgroup M) = p ^ 4 := by
  have h1 := card_map_mul_card_inf_ker (QuotientGroup.mk' (actQ X θ).ker) E
  rw [QuotientGroup.ker_mk', h.Ecard] at h1
  exact h1

theorem Cfg5.card_map_A (h : Cfg5 p X E A P N θ x) :
    Nat.card ↥(A.map (QuotientGroup.mk' (actQ X θ).ker)) = p ^ 2 := by
  have h1 := card_map_mul_card_inf_ker (QuotientGroup.mk' (actQ X θ).ker) A
  rw [QuotientGroup.ker_mk', h.ker_inf_A, Nat.card_zpowers, h.orderOf_x, h.Acard] at h1
  have : Nat.card ↥(A.map (QuotientGroup.mk' (actQ X θ).ker)) * p = p ^ 2 * p := by
    rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_right h.prime.pos this

theorem Cfg5.card_U_cases (h : Cfg5 p X E A P N θ x) :
    Nat.card ↥((actQ X θ).ker ⊓ E : Subgroup M) = p ∨
      Nat.card ↥((actQ X θ).ker ⊓ E : Subgroup M) = p ^ 2 := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have h1 := h.card_map_E
  have h2 := h.card_map_A
  have hAE : A.map (QuotientGroup.mk' (actQ X θ).ker) ≤ E.map (QuotientGroup.mk' (actQ X θ).ker) :=
    Subgroup.map_mono h.AE
  have h3 : p ^ 2 ≤ Nat.card ↥(E.map (QuotientGroup.mk' (actQ X θ).ker)) := by
    rw [← h2]; exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hAE)
  have hU1 : 1 ≤ Nat.card ↥((actQ X θ).ker ⊓ E : Subgroup M) := Nat.card_pos
  have hUp : IsPGroup p ↥((actQ X θ).ker ⊓ E : Subgroup M) :=
    (h.Eel.isPGroup p ↥E).to_le inf_le_right
  obtain ⟨n, hn⟩ := hUp.exists_card_eq
  have hxU : x ∈ (actQ X θ).ker ⊓ E := ⟨h.x_mem_ker, h.AE h.xA⟩
  have hpU : p ∣ Nat.card ↥((actQ X θ).ker ⊓ E : Subgroup M) := by
    have := orderOf_dvd_natCard (⟨x, hxU⟩ : ↥((actQ X θ).ker ⊓ E : Subgroup M))
    rwa [Subgroup.orderOf_mk, h.orderOf_x] at this
  rw [hn] at h1 hpU ⊢
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp at hpU
    exact h.prime.one_lt.ne' hpU
  have hn2 : n ≤ 2 := by
    by_contra hlt
    have h4 : p ^ 3 ≤ p ^ n := Nat.pow_le_pow_right hp.pos (by omega)
    have h5 : p ^ 2 * p ^ n ≤ Nat.card ↥(E.map (QuotientGroup.mk' (actQ X θ).ker)) * p ^ n :=
      Nat.mul_le_mul_right _ h3
    rw [h1] at h5
    have h6 : p ^ 2 * p ^ 3 ≤ p ^ 2 * p ^ n := Nat.mul_le_mul_left _ h4
    have h7 : p ^ 5 ≤ p ^ 4 := by
      calc p ^ 5 = p ^ 2 * p ^ 3 := by ring
        _ ≤ p ^ 4 := h6.trans h5
    have := Nat.pow_lt_pow_right hp.one_lt (show 4 < 5 by norm_num)
    omega
  have hn12 : n = 1 ∨ n = 2 := by omega
  rcases hn12 with rfl | rfl
  · left; simp
  · right; rfl

theorem Cfg5.isSylowOf_sup (h : Cfg5 p X E A P N θ x) {R : Subgroup M} (hRE : R ≤ E)
    (hUR : (actQ X θ).ker ⊓ E ≤ R) :
    CFSG.ABGLocalTools.IsSylowOf p R ((actQ X θ).ker ⊔ R) := by
  have : Fact p.Prime := ⟨h.prime⟩
  set K := (actQ X θ).ker with hK
  have hKn : K.Normal := (actQ X θ).normal_ker
  have hRK : R ⊓ K = K ⊓ E := by
    refine le_antisymm ?_ (le_inf (hUR) inf_le_left)
    intro y hy
    exact ⟨hy.2, hRE hy.1⟩
  refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨le_sup_right, h.Psyl.2.1.to_le (hRE.trans h.EP), ?_⟩
  rw [CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal K R, ← Subgroup.inf_relIndex_right R K,
    hRK]
  exact (CFSG.ABGLocalTools.isSylowOf_iff.1 h.isSylowOf_U_ker).2.2

theorem Cfg5.exists_ker_mul_mem_normalizer (h : Cfg5 p X E A P N θ x) {R : Subgroup M}
    (hRE : R ≤ E) (hUR : (actQ X θ).ker ⊓ E ≤ R) {g₀ : M}
    (hconj : ∀ r ∈ R, g₀ * r * g₀⁻¹ ∈ (actQ X θ).ker ⊔ R) :
    ∃ k ∈ (actQ X θ).ker, k⁻¹ * g₀ ∈ Subgroup.normalizer (R : Set M) := by
  have : Fact p.Prime := ⟨h.prime⟩
  set K := (actQ X θ).ker with hK
  have hKn : K.Normal := (actQ X θ).normal_ker
  have hRsyl := h.isSylowOf_sup hRE hUR
  have hle : StrongP.conjSub g₀ R ≤ K ⊔ R := by
    rintro _ ⟨r, hr, rfl⟩
    simpa [MulAut.conj_apply] using hconj r hr
  have hcs : CFSG.ABGLocalTools.IsSylowOf p (StrongP.conjSub g₀ R) (K ⊔ R) := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card hle ?_
    rw [StrongP.card_conjSub]
    exact hRsyl.card_eq
  obtain ⟨k, hk, hkconj⟩ := hRsyl.exists_mem_conj hcs
  obtain ⟨k₁, hk₁, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.1 hk
  refine ⟨k₁, hk₁, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  have hA : g₀ * y * g₀⁻¹ ∈ StrongP.conjSub g₀ R ↔ y ∈ R := by
    rw [StrongP.mem_conjSub_iff]
    simp [mul_assoc]
  have hB := hkconj (g₀ * y * g₀⁻¹)
  have hC : (k₁ * z)⁻¹ * (g₀ * y * g₀⁻¹) * (k₁ * z) =
      z⁻¹ * ((k₁⁻¹ * g₀) * y * (k₁⁻¹ * g₀)⁻¹) * z := by group
  have hD : ∀ w, z⁻¹ * w * z ∈ R ↔ w ∈ R := by
    intro w
    constructor
    · intro hw
      have := R.mul_mem (R.mul_mem hz hw) (R.inv_mem hz)
      simpa [mul_assoc] using this
    · intro hw
      exact R.mul_mem (R.mul_mem (R.inv_mem hz) hw) hz
  rw [← hA, hB, hC, hD]

theorem Cfg5.normalizer_le (h : Cfg5 p X E A P N θ x)
    {F : Subgroup (M ⧸ (actQ X θ).ker)}
    (hFA : F ≤ A.map (QuotientGroup.mk' (actQ X θ).ker)) (hF1 : F ≠ ⊥) :
    Subgroup.normalizer (F : Set (M ⧸ (actQ X θ).ker)) ≤
      N.map (QuotientGroup.mk' (actQ X θ).ker) := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  set K := (actQ X θ).ker with hK
  have hKn : K.Normal := (actQ X θ).normal_ker
  set π := QuotientGroup.mk' K with hπ
  set U : Subgroup M := K ⊓ E with hU
  set A₁ : Subgroup M := A ⊓ F.comap π with hA₁
  set R : Subgroup M := U ⊔ A₁ with hR
  have hUE : U ≤ E := inf_le_right
  have hA₁A : A₁ ≤ A := inf_le_left
  have hRE : R ≤ E := sup_le hUE (hA₁A.trans h.AE)
  have hUR : U ≤ R := le_sup_left
  have hπU : ∀ u ∈ U, π u = 1 := fun u hu => (QuotientGroup.eq_one_iff u).2 hu.1
  have hFR : F = R.map π := by
    ext f
    constructor
    · intro hf
      obtain ⟨a, ha, rfl⟩ := hFA hf
      exact ⟨a, Subgroup.mem_sup_right ⟨ha, Subgroup.mem_comap.2 hf⟩, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      have hRF : R ≤ F.comap π := sup_le
        (fun u hu => by rw [Subgroup.mem_comap, hπU u hu]; exact F.one_mem) inf_le_right
      exact hRF hr
  have hRne : R ≠ U := by
    intro hRU
    obtain ⟨f, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hF1
    have hfR : (f : M ⧸ K) ∈ R.map π := hFR ▸ f.2
    obtain ⟨r, hr, hrf⟩ := hfR
    apply hf1
    apply Subtype.ext
    have hrU : r ∈ U := hRU ▸ hr
    simpa [hπU r hrU] using hrf.symm
  have hNR : Subgroup.normalizer (R : Set M) ≤ N := by
    by_cases hUA : U ≤ A
    ·
      have hUx : U = Subgroup.zpowers x := by
        refine le_antisymm (fun u hu => ?_) (Subgroup.zpowers_le.2 ⟨h.x_mem_ker, h.AE h.xA⟩)
        have : u ∈ K ⊓ A := ⟨hu.1, hUA hu⟩
        rwa [h.ker_inf_A] at this
      have hRA : R ≤ A := sup_le hUA hA₁A
      refine h.normA R hRA ?_
      intro hcyc
      obtain ⟨g, hg⟩ := hcyc.exists_generator
      have hgp : (g : M) ^ p = 1 := h.pow_E g (hRE g.2)
      have hord : orderOf g = Nat.card ↥R := orderOf_eq_card_of_forall_mem_zpowers hg
      have hdvd : Nat.card ↥R ∣ p := by
        rw [← hord]
        exact orderOf_dvd_of_pow_eq_one (Subtype.ext hgp)
      have hxR : x ∈ R := hUR (hUx ▸ Subgroup.mem_zpowers x)
      have hbp : p ∣ Nat.card ↥R := by
        have := orderOf_dvd_natCard (⟨x, hxR⟩ : ↥R)
        rwa [Subgroup.orderOf_mk, h.orderOf_x] at this
      have hcard : Nat.card ↥R = p := Nat.dvd_antisymm hdvd hbp
      have hle : Subgroup.zpowers x ≤ R := Subgroup.zpowers_le.2 hxR
      have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, Nat.card_zpowers, h.orderOf_x])
      exact hRne (hUx ▸ heq.symm)
    ·
      refine h.normE R hRE ?_
      have h1 := card_map_mul_card_inf_ker π R
      have hRK : K ⊓ R = U := by
        refine le_antisymm (fun y hy => ⟨hy.1, hRE hy.2⟩) (le_inf inf_le_left hUR)
      have hker : π.ker = K := QuotientGroup.ker_mk' K
      rw [hker, hRK, ← hFR] at h1
      have hxU : x ∈ U := ⟨h.x_mem_ker, h.AE h.xA⟩
      have hUp : IsPGroup p ↥U := (h.Eel.isPGroup p ↥E).to_le hUE
      obtain ⟨n, hn⟩ := hUp.exists_card_eq
      have hn2 : 2 ≤ n := by
        by_contra hlt
        have hn1 : n ≤ 1 := by omega
        have hUcard : Nat.card ↥U ≤ p := by
          rw [hn]; calc p ^ n ≤ p ^ 1 := Nat.pow_le_pow_right h.prime.pos hn1
            _ = p := pow_one p
        have hxcard : Nat.card ↥(Subgroup.zpowers x) = p := by
          rw [Nat.card_zpowers, h.orderOf_x]
        have hle : Subgroup.zpowers x ≤ U := Subgroup.zpowers_le.2 hxU
        have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hxcard]; exact hUcard)
        exact hUA (heq ▸ (Subgroup.zpowers_le.2 h.xA))
      have hUc : p ^ 2 ≤ Nat.card ↥U := by
        rw [hn]; exact Nat.pow_le_pow_right h.prime.pos hn2
      have hFp : IsPGroup p ↥F := by
        have hEp : IsPGroup p ↥(E.map π) := (h.Eel.isPGroup p ↥E).map π
        exact hEp.to_le (by rw [hFR]; exact Subgroup.map_mono hRE)
      have hFc : p ≤ Nat.card ↥F := by
        have hdvd : p ∣ Nat.card ↥F := by
          rcases hFp.card_eq_or_dvd with h0 | h0
          · exact absurd (Subgroup.card_eq_one.mp h0) hF1
          · exact h0
        exact Nat.le_of_dvd Nat.card_pos hdvd
      have : p * p ^ 2 ≤ Nat.card ↥F * Nat.card ↥U := Nat.mul_le_mul hFc hUc
      calc p ^ 3 = p * p ^ 2 := by ring
        _ ≤ Nat.card ↥F * Nat.card ↥U := this
        _ = Nat.card ↥R := h1
  have hcomap : F.comap π = R ⊔ K := by
    conv_lhs => rw [hFR]
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  intro g hg
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective K g
  have hconj : ∀ r ∈ R, g₀ * r * g₀⁻¹ ∈ K ⊔ R := by
    intro r hr
    have hrF : π r ∈ F := hFR ▸ ⟨r, hr, rfl⟩
    have h1 : π (g₀ * r * g₀⁻¹) ∈ F := by
      have h3 := (Subgroup.mem_normalizer_iff.1 hg (π r)).1 hrF
      rw [map_mul, map_mul, map_inv]
      exact h3
    have h2 : g₀ * r * g₀⁻¹ ∈ F.comap π := h1
    rw [hcomap] at h2
    rwa [sup_comm]
  obtain ⟨k, hk, hkn⟩ := h.exists_ker_mul_mem_normalizer hRE hUR hconj
  have hπk : π k = 1 := (QuotientGroup.eq_one_iff k).2 hk
  have : π g₀ = π (k⁻¹ * g₀) := by rw [map_mul, map_inv, hπk]; simp
  rw [this]
  exact ⟨_, hNR hkn, rfl⟩

theorem Cfg5.map_E_eq_map_A (h : Cfg5 p X E A P N θ x)
    (hU : Nat.card ↥((actQ X θ).ker ⊓ E : Subgroup M) = p ^ 2) :
    E.map (QuotientGroup.mk' (actQ X θ).ker) = A.map (QuotientGroup.mk' (actQ X θ).ker) := by
  have h1 := h.card_map_E
  rw [hU] at h1
  have hE2 : Nat.card ↥(E.map (QuotientGroup.mk' (actQ X θ).ker)) = p ^ 2 := by
    have : Nat.card ↥(E.map (QuotientGroup.mk' (actQ X θ).ker)) * p ^ 2 = p ^ 2 * p ^ 2 := by
      rw [h1]; ring
    exact Nat.eq_of_mul_eq_mul_right (pow_pos h.prime.pos 2) this
  symm
  exact Subgroup.eq_of_le_of_card_ge (Subgroup.map_mono h.AE) (by rw [hE2, h.card_map_A])

theorem Cfg5.stronglyPEmbedded_map (h : Cfg5 p X E A P N θ x)
    (hU : Nat.card ↥((actQ X θ).ker ⊓ E : Subgroup M) = p ^ 2) :
    IsStronglyPEmbedded p (N.map (QuotientGroup.mk' (actQ X θ).ker)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  set K := (actQ X θ).ker with hK
  set π := QuotientGroup.mk' K with hπ
  have hPH := h.isSylowOf_map
  have hEA := h.map_E_eq_map_A hU
  have hPne : P.map π ≠ ⊥ := by
    intro hbot
    have hle : E.map π ≤ P.map π := Subgroup.map_mono h.EP
    rw [hbot, le_bot_iff] at hle
    have h2 := h.card_map_E
    rw [hle, Subgroup.card_bot, hU] at h2
    have h3 : p ^ 2 < p ^ 4 := Nat.pow_lt_pow_right h.prime.one_lt (by norm_num)
    omega
  have hNe : N.map π ≠ ⊤ := by
    intro htop
    have h1 : N ⊔ K = ⊤ := by
      have := congrArg (Subgroup.comap π) htop
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at this
    have h2 : N = ⊤ := by
      rw [← h1]; exact (sup_eq_left.2 h.ker_le_N).symm
    exact h.XN (h2 ▸ le_top)
  refine stronglyPEmbedded_of_normalizers_le h.prime hPH hPne (Subgroup.map_mono h.PN) hNe ?_
  intro R hRP hR1
  have hRp : IsPGroup p R := hPH.2.1.to_le hRP
  have hF1 : omegaOne p R ≠ ⊥ := omegaOne_ne_bot_of_isPGroup hRp hR1
  have hFP : omegaOne p R ≤ A.map π := by
    rw [← hEA, ← h.omegaOne_map]
    exact Subgroup.closure_mono fun y ⟨hy, hy1⟩ => ⟨hRP hy, hy1⟩
  exact (normalizer_le_normalizer_omegaOne (q := p) (K := R)).trans (h.normalizer_le hFP hF1)

end Sec159Five

end CFSG.RankThree.PartOne
