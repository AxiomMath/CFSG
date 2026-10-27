module

public import CFSG.RankThree.PartOne.S12.Sec159Cfg
public import CFSG.RankThree.PartOne.S12.Sec15SPL

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree StrongP

namespace Sec159Cfg

theorem card_map_mul_card_inf_ker {G H : Type*} [Group G] [Group H] [Finite G] (f : G →* H)
    (A : Subgroup G) :
    Nat.card ↥(A.map f) * Nat.card ↥(f.ker ⊓ A : Subgroup G) = Nat.card ↥A := by
  set g : ↥A →* H := f.comp A.subtype with hg
  have h1 := Subgroup.card_ker_mul_card_range g
  have hrange : g.range = A.map f := by
    ext x
    simp only [MonoidHom.mem_range, Subgroup.mem_map, hg, MonoidHom.comp_apply, Subgroup.coe_subtype]
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨y, hy⟩, rfl⟩
  have hker : Nat.card g.ker = Nat.card ↥(f.ker ⊓ A : Subgroup G) := by
    have : g.ker = f.ker.subgroupOf A := rfl
    rw [this, ← Subgroup.card_map_of_injective A.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  rw [hrange, hker] at h1
  linarith

variable {p : ℕ} {M : Type} [Group M] [Finite M] {X E P N : Subgroup M} [X.Normal]
  {θ : Subgroup ↥X} [θ.Characteristic] {b : M}

theorem Cfg159.isSylowOf_map (h : Cfg159 p X E P N θ b) :
    IsSylowOf p (P.map (QuotientGroup.mk' (actQ X θ).ker)) ⊤ := by
  refine ⟨le_top, h.Psyl.2.1.map _, ?_⟩
  rw [Subgroup.relIndex_top_right]
  intro hd
  have h1 := Subgroup.index_map_dvd (QuotientGroup.mk'_surjective (actQ X θ).ker) (H := P)
  have h2 := h.Psyl.2.2
  rw [Subgroup.relIndex_top_right] at h2
  exact h2 (hd.trans h1)

theorem Cfg159.omegaOne_map (h : Cfg159 p X E P N θ b) :
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
    have hmem : y ^ p ∈ Subgroup.zpowers b ⊓ X := ⟨h.ker_inf_P ▸ ⟨hyK, hypP⟩, hyX⟩
    rw [h.zpowers_inf_X, Subgroup.mem_bot] at hmem
    have hyE : y ∈ E := h.Pomega ▸ Subgroup.subset_closure ⟨hyP, hmem⟩
    exact ⟨y, hyE, rfl⟩
  · rintro _ ⟨e, he, rfl⟩
    refine Subgroup.subset_closure ⟨⟨e, h.EP he, rfl⟩, ?_⟩
    rw [← map_pow, h.pow_E e he, map_one]

theorem Cfg159.card_map_E (h : Cfg159 p X E P N θ b) :
    Nat.card ↥(E.map (QuotientGroup.mk' (actQ X θ).ker)) = p ^ 2 := by
  have h1 := card_map_mul_card_inf_ker (QuotientGroup.mk' (actQ X θ).ker) E
  rw [QuotientGroup.ker_mk', h.ker_inf_E, Nat.card_zpowers, h.orderOf_b, h.Ecard] at h1
  have hp0 : 0 < p := h.prime.pos
  have : Nat.card ↥(E.map (QuotientGroup.mk' (actQ X θ).ker)) * p = p ^ 2 * p := by
    rw [h1]; ring
  exact Nat.eq_of_mul_eq_mul_right hp0 this

theorem omegaOne_conj_mem {G : Type*} [Group G] {q : ℕ} {K : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) {x : G} (hx : x ∈ omegaOne q K) :
    g * x * g⁻¹ ∈ omegaOne q K := by
  have hle : omegaOne q K ≤ (omegaOne q K).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨hyK, hy1⟩
    refine Subgroup.mem_comap.2 (Subgroup.subset_closure ⟨?_, ?_⟩)
    · exact (Subgroup.mem_normalizer_iff.1 hg y).1 hyK
    · change (g * y * g⁻¹) ^ q = 1
      rw [conj_pow, hy1]; simp
  simpa [MulAut.conj_apply] using hle hx

theorem normalizer_le_normalizer_omegaOne {G : Type*} [Group G] {q : ℕ} {K : Subgroup G} :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer ((omegaOne q K : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => omegaOne_conj_mem hg hx, fun hx => ?_⟩
  have := omegaOne_conj_mem ((Subgroup.normalizer (K : Set G)).inv_mem hg) hx
  simpa [mul_assoc] using this

theorem Cfg159.isSylowOf_sup (h : Cfg159 p X E P N θ b) {R : Subgroup M} (hRE : R ≤ E)
    (hbR : b ∈ R) :
    CFSG.ABGLocalTools.IsSylowOf p R ((actQ X θ).ker ⊔ R) := by
  have : Fact p.Prime := ⟨h.prime⟩
  set K := (actQ X θ).ker with hK
  have hKn : K.Normal := (actQ X θ).normal_ker
  have hRK : R ⊓ K = Subgroup.zpowers b := by
    refine le_antisymm ?_ (Subgroup.zpowers_le.2 ⟨hbR, h.b_mem_ker⟩)
    intro x hx
    have : x ∈ K ⊓ E := ⟨hx.2, hRE hx.1⟩
    rwa [h.ker_inf_E] at this
  refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨le_sup_right, h.Psyl.2.1.to_le (hRE.trans h.EP), ?_⟩
  rw [CFSG.ABGLocalTools.relIndex_sup_eq_relIndex_of_normal K R, ← Subgroup.inf_relIndex_right R K,
    hRK]
  exact (CFSG.ABGLocalTools.isSylowOf_iff.1 h.isSylowOf_zpowers_ker).2.2

theorem Cfg159.exists_ker_mul_mem_normalizer (h : Cfg159 p X E P N θ b) {R : Subgroup M}
    (hRE : R ≤ E) (hbR : b ∈ R) {g₀ : M}
    (hconj : ∀ r ∈ R, g₀ * r * g₀⁻¹ ∈ (actQ X θ).ker ⊔ R) :
    ∃ k ∈ (actQ X θ).ker, k⁻¹ * g₀ ∈ Subgroup.normalizer (R : Set M) := by
  have : Fact p.Prime := ⟨h.prime⟩
  set K := (actQ X θ).ker with hK
  have hKn : K.Normal := (actQ X θ).normal_ker
  have hRsyl := h.isSylowOf_sup hRE hbR
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
  intro x
  have hA : g₀ * x * g₀⁻¹ ∈ StrongP.conjSub g₀ R ↔ x ∈ R := by
    rw [StrongP.mem_conjSub_iff]
    simp [mul_assoc]
  have hB := hkconj (g₀ * x * g₀⁻¹)
  have hC : (k₁ * z)⁻¹ * (g₀ * x * g₀⁻¹) * (k₁ * z) =
      z⁻¹ * ((k₁⁻¹ * g₀) * x * (k₁⁻¹ * g₀)⁻¹) * z := by group
  have hD : ∀ w, z⁻¹ * w * z ∈ R ↔ w ∈ R := by
    intro w
    constructor
    · intro hw
      have := R.mul_mem (R.mul_mem hz hw) (R.inv_mem hz)
      simpa [mul_assoc] using this
    · intro hw
      exact R.mul_mem (R.mul_mem (R.inv_mem hz) hw) hz
  rw [← hA, hB, hC, hD]

theorem Cfg159.normalizer_le (h : Cfg159 p X E P N θ b)
    {F : Subgroup (M ⧸ (actQ X θ).ker)}
    (hFE : F ≤ E.map (QuotientGroup.mk' (actQ X θ).ker)) (hF1 : F ≠ ⊥) :
    Subgroup.normalizer (F : Set (M ⧸ (actQ X θ).ker)) ≤
      N.map (QuotientGroup.mk' (actQ X θ).ker) := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  set K := (actQ X θ).ker with hK
  have hKn : K.Normal := (actQ X θ).normal_ker
  set π := QuotientGroup.mk' K with hπ
  set R : Subgroup M := E ⊓ F.comap π with hR
  have hRE : R ≤ E := inf_le_left
  have hπb : π b = 1 := (QuotientGroup.eq_one_iff b).2 h.b_mem_ker
  have hbR : b ∈ R := ⟨h.bE, Subgroup.mem_comap.2 (by rw [hπb]; exact F.one_mem)⟩
  have hFR : F = R.map π := by
    ext f
    constructor
    · intro hf
      obtain ⟨e, he, rfl⟩ := hFE hf
      exact ⟨e, ⟨he, Subgroup.mem_comap.2 hf⟩, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      exact hr.2
  have hRne : R ≠ Subgroup.zpowers b := by
    intro hRb
    obtain ⟨f, hf1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hF1
    have hfR : (f : M ⧸ K) ∈ R.map π := hFR ▸ f.2
    obtain ⟨r, hr, hrf⟩ := hfR
    apply hf1
    apply Subtype.ext
    have hrb : r ∈ Subgroup.zpowers b := hRb ▸ hr
    have hrK : r ∈ K := Subgroup.zpowers_le.2 h.b_mem_ker hrb
    have : π r = 1 := (QuotientGroup.eq_one_iff r).2 hrK
    simpa [this] using hrf.symm
  have hNR : Subgroup.normalizer (R : Set M) ≤ N := h.normN hRE hbR hRne
  have hcomap : F.comap π = R ⊔ K := by
    conv_lhs => rw [hFR]
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  intro g hg
  obtain ⟨g₀, rfl⟩ := QuotientGroup.mk'_surjective K g
  have hconj : ∀ r ∈ R, g₀ * r * g₀⁻¹ ∈ K ⊔ R := by
    intro r hr
    have hrF : π r ∈ F := hr.2
    have h1 : π (g₀ * r * g₀⁻¹) ∈ F := by
      have h3 := (Subgroup.mem_normalizer_iff.1 hg (π r)).1 hrF
      rw [map_mul, map_mul, map_inv]
      exact h3
    have h2 : g₀ * r * g₀⁻¹ ∈ F.comap π := h1
    rw [hcomap] at h2
    rwa [sup_comm]
  obtain ⟨k, hk, hkn⟩ := h.exists_ker_mul_mem_normalizer hRE hbR hconj
  have hπk : π k = 1 := (QuotientGroup.eq_one_iff k).2 hk
  have : π g₀ = π (k⁻¹ * g₀) := by rw [map_mul, map_inv, hπk]; simp
  rw [this]
  exact ⟨_, hNR hkn, rfl⟩

theorem omegaOne_ne_bot_of_isPGroup {G : Type*} [Group G] [Finite G] {q : ℕ} [Fact q.Prime]
    {R : Subgroup G} (hR : IsPGroup q R) (hR1 : R ≠ ⊥) : omegaOne q R ≠ ⊥ := by
  have hdvd : q ∣ Nat.card ↥R := by
    rcases hR.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.card_eq_one.mp h) hR1
    · exact h
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥R) q hdvd
  intro hbot
  have hxmem : (x : G) ∈ omegaOne q R :=
    Subgroup.subset_closure ⟨x.2, by
      have := pow_orderOf_eq_one x
      rw [hx] at this
      exact congrArg Subtype.val this⟩
  rw [hbot, Subgroup.mem_bot] at hxmem
  have : x = 1 := Subtype.ext hxmem
  rw [this, orderOf_one] at hx
  exact (Fact.out : q.Prime).one_lt.ne hx

theorem Cfg159.stronglyPEmbedded_map (h : Cfg159 p X E P N θ b) :
    IsStronglyPEmbedded p (N.map (QuotientGroup.mk' (actQ X θ).ker)) := by
  have : Fact p.Prime := ⟨h.prime⟩
  set K := (actQ X θ).ker with hK
  set π := QuotientGroup.mk' K with hπ
  have hPH := h.isSylowOf_map
  have hPne : P.map π ≠ ⊥ := by
    intro hbot
    have hle : E.map π ≤ P.map π := Subgroup.map_mono h.EP
    rw [hbot, le_bot_iff] at hle
    have h2 := h.card_map_E
    rw [hle, Subgroup.card_bot] at h2
    have := h.prime.two_le
    have h3 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) h.prime.one_lt
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
  have hFP : omegaOne p R ≤ E.map π := by
    rw [← h.omegaOne_map]
    exact Subgroup.closure_mono fun x ⟨hx, hx1⟩ => ⟨hRP hx, hx1⟩
  exact (normalizer_le_normalizer_omegaOne (q := p) (K := R)).trans (h.normalizer_le hFP hF1)

end Sec159Cfg

end CFSG.RankThree.PartOne
