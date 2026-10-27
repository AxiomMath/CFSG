module

public import CFSG.Quasithin.H13.NQBlockRankTwoRigidity
public import CFSG.Quasithin.SteinbergCCLocalSylowAction
public import CFSG.Quasithin.H13.NQTermPerfectSmallFamily
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic
import CFSG.LocalAnalysis.SectionRank.GroupRankTransport

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj exists_conj_eq_of_isSylowOf)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_of_card)
open scoped commutatorElement

section Defs

variable {G : Type*} [Group G]

@[expose] def IsFrattiniIrreducible (X H : Subgroup G) : Prop :=
  ∀ Y : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
    (∀ h : normalizer (X : Set G), (h : G) ∈ H → ∀ y ∈ Y, normalizerFrattiniConj X h y ∈ Y) →
    Y = ⊥ ∨ Y = ⊤

theorem IsFrattiniIrreducible.mono {X H H' : Subgroup G} (h : IsFrattiniIrreducible X H)
    (hHH' : H ≤ H') : IsFrattiniIrreducible X H' :=
  fun Y hY => h Y fun n hn => hY n (hHH' hn)

end Defs

section Tools

theorem map_frattini_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    (frattini A).map e.toMonoidHom = frattini B := by
  apply le_antisymm
  · rw [map_le_iff_le_comap]
    exact frattini_le_comap_frattini_of_surjective e.surjective
  · intro b hb
    have h := frattini_le_comap_frattini_of_surjective (φ := e.symm.toMonoidHom)
      e.symm.surjective hb
    exact ⟨e.symm b, h, by simp⟩

theorem ker_comp_symm {A B C : Type*} [Group A] [Group B] [Group C] (f : A →* C) (e : A ≃* B) :
    (f.comp e.symm.toMonoidHom).ker = f.ker.map e.toMonoidHom := by
  ext b
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
  constructor
  · intro hb
    exact ⟨e.symm b, hb, by simp⟩
  · rintro ⟨a, ha, rfl⟩
    simpa using ha

theorem frattini_lt_top {A : Type*} [Group A] [Finite A] [Nontrivial A] : frattini A < ⊤ := by
  obtain ⟨K, hK⟩ : ∃ K : Subgroup A, IsCoatom K := by
    rcases IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Subgroup A) with h | ⟨K, hK, -⟩
    · exact absurd h bot_ne_top
    · exact ⟨K, hK⟩
  exact lt_of_le_of_lt (frattini_le_coatom hK) hK.1.lt_top

theorem isPGroup_two_of_card_dvd {A : Type*} [Group A] {k : ℕ} (h : Nat.card A ∣ 2 ^ k) :
    IsPGroup 2 A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h
  exact IsPGroup.of_card hj

theorem pRank_congr {p : ℕ} (_hp : 1 < p) {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) : CFSG.pRank p A = CFSG.pRank p B := CFSG.pRank_congr_of_mulEquiv e p

theorem pow_eq_one_of_mulEquiv {Γ B : Type*} [Group Γ] [Group B] {p : ℕ} {K : Subgroup Γ}
    (e : K ≃* B) (hB : ∀ b : B, b ^ p = 1) : ∀ x ∈ K, x ^ p = 1 := by
  intro x hx
  have h := congrArg Subtype.val (e.injective (show e (⟨x, hx⟩ ^ p) = e 1 by
    rw [map_pow, hB, map_one]))
  simpa using h

theorem frattini_lattice_irreducible {Γ W : Type*} [Group Γ] [Group W] {P S : Subgroup Γ}
    (hSP : S ≤ normalizer (P : Set Γ)) (θ : P →* W) (hker : θ.ker = frattini P)
    (hirr : ∀ Y : Subgroup W, (∀ s ∈ S, ∀ y z : P, (z : Γ) = s * y * s⁻¹ → θ y ∈ Y →
      θ z ∈ Y) → Y = ⊥ ∨ Y = ⊤) (Y : Subgroup Γ) (hΦY : (frattini P).map P.subtype ≤ Y)
    (hYP : Y ≤ P) (hYn : normalizer (P : Set Γ) ≤ normalizer (Y : Set Γ)) :
    Y = (frattini P).map P.subtype ∨ Y = P := by
  set Y' : Subgroup P := Y.subgroupOf P with hY'
  have hΦY' : frattini P ≤ Y' := fun y hy => hΦY ⟨y, hy, rfl⟩
  have hYeq : Y = Y'.map P.subtype := (map_subgroupOf_eq_of_le hYP).symm
  have hmem : ∀ y₁ y : P, y₁ ∈ Y' → θ y₁ = θ y → y ∈ Y' := by
    intro y₁ y hy₁ hyy
    have hk : y₁⁻¹ * y ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyy, inv_mul_cancel]
    rw [hker] at hk
    have := Y'.mul_mem hy₁ (hΦY' hk)
    simpa using this
  have hinv : ∀ s ∈ S, ∀ y z : P, (z : Γ) = s * y * s⁻¹ → θ y ∈ Y'.map θ →
      θ z ∈ Y'.map θ := by
    intro s hs y z hz hy
    obtain ⟨y₁, hy₁, hyy⟩ := hy
    have hyY : (y : Γ) ∈ Y := hmem y₁ y hy₁ hyy
    have hsY : s ∈ normalizer (Y : Set Γ) := hYn (hSP hs)
    have hzY : (z : Γ) ∈ Y := by
      rw [hz]
      exact (mem_normalizer_iff.mp hsY y).mp hyY
    exact ⟨z, hzY, rfl⟩
  rcases hirr (Y'.map θ) hinv with h | h
  · left
    apply le_antisymm _ hΦY
    rw [hYeq]
    apply map_mono
    intro y hy
    have h1 : θ y ∈ Y'.map θ := ⟨y, hy, rfl⟩
    rw [h, mem_bot] at h1
    rw [← hker]
    exact h1
  · right
    apply le_antisymm hYP
    intro x hx
    have h1 : θ ⟨x, hx⟩ ∈ Y'.map θ := h ▸ mem_top _
    obtain ⟨y', hy', hyy⟩ := h1
    exact hmem y' ⟨x, hx⟩ hy' hyy

variable {G : Type*} [Group G]

theorem mem_conjugate_iff {H : Subgroup G} {g z : G} :
    z ∈ CFSG.conjugate H g ↔ g * z * g⁻¹ ∈ H := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hh
  · intro hz
    refine ⟨g * z * g⁻¹, hz, ?_⟩
    simp [mul_assoc]

theorem card_conjugate (H : Subgroup G) (g : G) : Nat.card (CFSG.conjugate H g) = Nat.card H :=
  card_map_of_injective (MulAut.conj g⁻¹).injective

noncomputable def conjugateEquiv (H : Subgroup G) (g : G) : H ≃* CFSG.conjugate H g :=
  H.equivMapOfInjective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective

theorem conjugate_le_normalizer {K M : Subgroup G} (hMK : M ≤ normalizer (K : Set G)) (g : G) :
    CFSG.conjugate M g ≤ normalizer (CFSG.conjugate K g : Set G) := by
  intro j hj
  rw [mem_normalizer_iff]
  intro z
  rw [mem_conjugate_iff, mem_conjugate_iff]
  have hj' := mem_normalizer_iff.mp (hMK (mem_conjugate_iff.mp hj)) (g * z * g⁻¹)
  have : g * (j * z * j⁻¹) * g⁻¹ = g * j * g⁻¹ * (g * z * g⁻¹) * (g * j * g⁻¹)⁻¹ := by group
  rw [this]
  exact hj'

theorem normalizer_le_normalizer_map_pCore (p : ℕ) (X : Subgroup G) :
    normalizer (X : Set G) ≤
      normalizer (((CFSG.pCore p X).map X.subtype : Subgroup G) : Set G) := by
  intro n hn
  rw [mem_normalizer_iff]
  intro z
  have hfix := (CFSG.pCore_characteristic (p := p) (G := X)).fixed (X.normalizerMonoidHom ⟨n, hn⟩)
  have key : ∀ y : X, (y ∈ CFSG.pCore p X ↔ X.normalizerMonoidHom ⟨n, hn⟩ y ∈ CFSG.pCore p X) := by
    intro y
    constructor
    · intro hy
      have h1 : y ∈ (CFSG.pCore p X).comap (X.normalizerMonoidHom ⟨n, hn⟩).toMonoidHom := by
        rw [hfix]
        exact hy
      exact h1
    · intro hy
      have h1 : y ∈ (CFSG.pCore p X).comap (X.normalizerMonoidHom ⟨n, hn⟩).toMonoidHom := hy
      rwa [hfix] at h1
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, (key y).mp hy, rfl⟩
  · rintro ⟨y, hy, hyz⟩
    have hz : z ∈ X := by
      have h1 : n * z * n⁻¹ ∈ X := by rw [← hyz]; exact y.2
      exact (mem_normalizer_iff.mp hn z).mpr h1
    refine ⟨⟨z, hz⟩, (key ⟨z, hz⟩).mpr ?_, rfl⟩
    have : X.normalizerMonoidHom ⟨n, hn⟩ ⟨z, hz⟩ = y := Subtype.ext (by
      change n * z * n⁻¹ = (y : G)
      exact hyz.symm)
    rw [this]
    exact hy

theorem isSylowOf_map_conj [Finite G] {p : ℕ} [Fact p.Prime] {P X : Subgroup G}
    (hP : IsSylowOf p P X) {h : G} (hh : h ∈ normalizer (X : Set G)) :
    IsSylowOf p (P.map (MulAut.conj h).toMonoidHom) X := by
  refine isSylowOf_of_card ?_ ?_
  · rintro _ ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hh y).mp (hP.le hy)
  · rw [card_map_of_injective (MulAut.conj h).injective]
    exact hP.card_eq

end Tools

section Trivial

variable {G : Type*} [Group G] [Finite G]

theorem normalizerFrattiniConj_eq_one_of_mem {p : ℕ} [Fact p.Prime] {X : Subgroup G}
    (hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X)) (x : normalizer (X : Set G)) (hx : (x : G) ∈ X) :
    normalizerFrattiniConj X x = 1 := by
  have : Fact (IsPGroup p (X ⧸ CFSG.pCore 2 X)) := ⟨hXp⟩
  ext w
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective w
  change ((((X.normalizerMonoidHom x y : X) : X ⧸ CFSG.pCore 2 X)) :
      (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) =
    (((y : X ⧸ CFSG.pCore 2 X)) : (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X))
  have hxy : X.normalizerMonoidHom x y = ⟨x, hx⟩ * y * (⟨x, hx⟩ : X)⁻¹ := Subtype.ext rfl
  rw [hxy, QuotientGroup.eq]
  set a : X ⧸ CFSG.pCore 2 X := ((⟨x, hx⟩ : X) : X ⧸ CFSG.pCore 2 X)
  set b : X ⧸ CFSG.pCore 2 X := (y : X ⧸ CFSG.pCore 2 X)
  have hc : (QuotientGroup.mk (⟨x, hx⟩ * y * (⟨x, hx⟩ : X)⁻¹) : X ⧸ CFSG.pCore 2 X)⁻¹ * b =
      ⁅a, b⁻¹⁆ := by
    rw [commutatorElement_def]
    simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv, a, b]
    group
  rw [hc]
  exact CFSG.commutator_le_frattini_of_isPGroup (p := p)
    (Subgroup.commutator_mem_commutator (mem_top a) (mem_top b⁻¹))

end Trivial

variable {G : Type} [Group G] [Finite G]

theorem irreducible_residual_normalizer_conjugate_uniqueness {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {X M : Subgroup G} (hXM : X ≤ M) (_hXn : (X.subgroupOf M).Normal)
    (hMp : CFSG.pRank p M ≤ 2) (hN : normalizer (X : Set G) = M) (hX2 : NoPQuotient 2 X)
    (hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p)
    (hrk : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2) {H : Subgroup G} (hXH : X ≤ H)
    (_hHM : H ≤ M) (hirr : IsFrattiniIrreducible X H) (g : G) (hg : H ≤ CFSG.conjugate M g) :
    g ∈ M ∧ CFSG.conjugate M g = M := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp1 : 1 < p := hp.one_lt
  have hpow : ∀ w : X ⧸ CFSG.pCore 2 X, w ^ p = 1 := fun w => by
    rw [← hexp]
    exact Monoid.pow_exponent_eq_one w
  have hXp : IsPGroup p (X ⧸ CFSG.pCore 2 X) := fun w => ⟨1, by rw [pow_one, hpow]⟩
  have hXnt : Nontrivial (X ⧸ CFSG.pCore 2 X) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have h1 : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = 1 := Monoid.exp_eq_one_iff.mpr hnt
    rw [hexp] at h1
    exact hp.one_lt.ne' h1
  set A : Subgroup G := (CFSG.pCore 2 X).map X.subtype with hA
  set J : Subgroup G := CFSG.conjugate M g with hJ
  set Xg : Subgroup G := CFSG.conjugate X g with hXg
  set Ag : Subgroup G := CFSG.conjugate A g with hAg
  have hAX : A ≤ X := map_subtype_le _
  have hA2 : IsPGroup 2 A := CFSG.pCore_isPGroup.map _
  have hXJ : X ≤ J := hXH.trans hg
  have hXgJ : Xg ≤ J := map_mono hXM
  have hAgXg : Ag ≤ Xg := map_mono hAX
  have hAgJ : Ag ≤ J := hAgXg.trans hXgJ
  have hAg2 : IsPGroup 2 Ag := hA2.map _
  have hMX : M ≤ normalizer (X : Set G) := hN.ge
  have hMA : M ≤ normalizer (A : Set G) := hMX.trans (normalizer_le_normalizer_map_pCore 2 X)
  have hJXg : J ≤ normalizer (Xg : Set G) := conjugate_le_normalizer hMX g
  have hJAg : J ≤ normalizer (Ag : Set G) := conjugate_le_normalizer hMA g
  set Ag' : Subgroup J := Ag.subgroupOf J with hAg'
  have hAg'n : Ag'.Normal := (normal_subgroupOf_iff_le_normalizer hAgJ).mpr hJAg
  set π : J →* J ⧸ Ag' := QuotientGroup.mk' Ag' with hπ
  have hAg'2 : IsPGroup 2 Ag' := hAg2.comap_subtype
  have hpAg' : ¬ p ∣ Nat.card Ag' := by
    intro hdvd
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hAg'2
    rw [hk] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  have hΓrk : CFSG.pRank p (J ⧸ Ag') ≤ 2 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top, CFSG.SectionRank.pRank_quotient_eq Ag' hpAg',
      ← CFSG.SectionRank.pRank_eq_open_pRank_top, ← pRank_congr hp1 (conjugateEquiv M g)]
    exact hMp
  set c : X →* J := ((MulAut.conj g⁻¹).toMonoidHom.comp X.subtype).codRestrict J
    (fun x => mem_map_of_mem _ (hXM x.2)) with hc
  set φ : X →* J ⧸ Ag' := π.comp c with hφ
  have hkerφ : φ.ker = CFSG.pCore 2 X := by
    ext x
    rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    change (MulAut.conj g⁻¹) (x : G) ∈ Ag ↔ _
    constructor
    · rintro ⟨a, ⟨b, hb, rfl⟩, hab⟩
      have hbx : b = x := Subtype.ext ((MulAut.conj g⁻¹).injective hab)
      rwa [← hbx]
    · intro h
      exact ⟨x, ⟨x, h, rfl⟩, rfl⟩
  set R : Subgroup (J ⧸ Ag') := (Xg.subgroupOf J).map π with hR
  have hrangeφ : φ.range = R := by
    rw [hφ, MonoidHom.range_comp]
    congr 1
    ext j
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, hxj⟩
      exact ⟨⟨x, hx⟩, Subtype.ext hxj⟩
  let eR : (X ⧸ CFSG.pCore 2 X) ≃* R :=
    (QuotientGroup.quotientMulEquivOfEq hkerφ.symm).trans
      ((QuotientGroup.quotientKerEquivRange φ).trans (MulEquiv.subgroupCongr hrangeφ))
  have hXg'n : (Xg.subgroupOf J).Normal := (normal_subgroupOf_iff_le_normalizer hXgJ).mpr hJXg
  have hRn : R.Normal := hXg'n.map π (QuotientGroup.mk'_surjective _)
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow p X))
  set P : Subgroup G := (P₀ : Subgroup X).map X.subtype with hP
  have hPsyl : IsSylowOf p P X := ⟨P₀, rfl⟩
  have hPX : P ≤ X := map_subtype_le _
  have hPp : IsPGroup p P := hPsyl.isPGroup
  have hPAg : Disjoint P Ag := IsPGroup.disjoint_of_ne p 2 hp2 P Ag hPp hAg2
  set e₀ : (P₀ : Subgroup X) ≃* X ⧸ CFSG.pCore 2 X :=
    MulEquiv.ofBijective _ (NQTerm.sylow_bijective_coreQuot hp2 hXp P₀) with he₀
  set Pbar : Subgroup (J ⧸ Ag') := (P.subgroupOf J).map π with hPbar
  set ι₀ : (P₀ : Subgroup X) →* J := (X.subtype.comp (P₀ : Subgroup X).subtype).codRestrict J
    (fun y => hXJ (y : X).2) with hι₀
  set ψ : (P₀ : Subgroup X) →* J ⧸ Ag' := π.comp ι₀ with hψ
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    rw [hψ, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
    have h1 : ((y : X) : G) ∈ P ⊓ Ag := ⟨⟨y, y.2, rfl⟩, hy⟩
    rw [disjoint_iff.mp hPAg, mem_bot] at h1
    exact Subtype.ext (Subtype.ext h1)
  have hrangeψ : ψ.range = Pbar := by
    rw [hψ, MonoidHom.range_comp]
    congr 1
    ext j
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩
    · rintro ⟨y, hy, hyj⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hyj⟩
  let eP : (P₀ : Subgroup X) ≃* Pbar :=
    (MonoidHom.ofInjective hψinj).trans (MulEquiv.subgroupCongr hrangeψ)
  have heP : ∀ y : (P₀ : Subgroup X), ((eP y : Pbar) : J ⧸ Ag') = ψ y := fun _ => rfl
  have hRrk : CFSG.pRank p R = 2 := by rw [← pRank_congr hp1 eR, hrk]
  have hPrk : CFSG.pRank p Pbar = 2 := by rw [pRank_congr hp1 (eP.symm.trans e₀), hrk]
  have hRexp : ∀ x ∈ R, x ^ p = 1 := pow_eq_one_of_mulEquiv eR.symm hpow
  have hPexp : ∀ x ∈ Pbar, x ^ p = 1 := pow_eq_one_of_mulEquiv (eP.symm.trans e₀) hpow
  have hPnt : Nontrivial Pbar := (eP.symm.trans e₀).toEquiv.nontrivial
  have hΦlt : (frattini Pbar).map Pbar.subtype < Pbar := by
    refine lt_of_le_of_ne (map_subtype_le _) fun heq => (frattini_lt_top (A := Pbar)).ne ?_
    rw [eq_top_iff]
    intro x _
    have h1 : (x : J ⧸ Ag') ∈ (frattini Pbar).map Pbar.subtype := by rw [heq]; exact x.2
    obtain ⟨y, hy, hyx⟩ := h1
    rwa [← Subtype.ext hyx]
  set S : Subgroup (J ⧸ Ag') := ((H ⊓ normalizer (P : Set G)).subgroupOf J).map π with hS
  have hSP : S ≤ normalizer (Pbar : Set (J ⧸ Ag')) := by
    refine (map_mono ?_).trans (le_normalizer_map π)
    intro j hj
    have hjN : (j : G) ∈ normalizer (P : Set G) := (mem_inf.mp hj).2
    rw [mem_normalizer_iff]
    intro k
    simp only [mem_subgroupOf, coe_mul, coe_inv]
    exact mem_normalizer_iff.mp hjN k
  set θ : Pbar →* (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X) :=
    ((QuotientGroup.mk' (frattini (X ⧸ CFSG.pCore 2 X))).comp e₀.toMonoidHom).comp
      eP.symm.toMonoidHom with hθ
  have hθker : θ.ker = frattini Pbar := by
    rw [hθ, ker_comp_symm]
    have h1 := ker_comp_symm (QuotientGroup.mk' (frattini (X ⧸ CFSG.pCore 2 X))) e₀.symm
    rw [MulEquiv.symm_symm, QuotientGroup.ker_mk', map_frattini_mulEquiv] at h1
    rw [h1, map_frattini_mulEquiv]
  have hθψ : ∀ y : (P₀ : Subgroup X), θ (eP y) =
      ((((y : X) : X ⧸ CFSG.pCore 2 X)) :
        (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) := by
    intro y
    rw [hθ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      MonoidHom.comp_apply]
    rfl
  have hirrS : ∀ Y : Subgroup ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)),
      (∀ s ∈ S, ∀ y z : Pbar, (z : J ⧸ Ag') = s * y * s⁻¹ → θ y ∈ Y → θ z ∈ Y) →
      Y = ⊥ ∨ Y = ⊤ := by
    intro Y hY
    apply hirr Y
    intro h hhH w hw
    obtain ⟨x, hxX, hx⟩ := exists_conj_eq_of_isSylowOf hPsyl (isSylowOf_map_conj hPsyl h.2)
    set n : G := x⁻¹ * h with hn
    have hnH : n ∈ H := H.mul_mem (H.inv_mem (hXH hxX)) hhH
    have hnPeq : P.map (MulAut.conj n).toMonoidHom = P := by
      have h1 := congrArg (fun K : Subgroup G => K.map (MulAut.conj x⁻¹).toMonoidHom) hx
      simp only [map_map] at h1
      have e1 : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom =
          MonoidHom.id G := by
        ext y
        change x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y
        group
      have e2 : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj (h : G)).toMonoidHom =
          (MulAut.conj n).toMonoidHom := by
        ext y
        simp [MulAut.conj_apply, hn, mul_assoc]
      rw [e1, e2, map_id] at h1
      exact h1.symm
    have hnP : n ∈ normalizer (P : Set G) := by
      rw [mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [← hnPeq]
        exact ⟨y, hy, rfl⟩
      · intro hy
        rw [← hnPeq] at hy
        obtain ⟨y', hy', hyy⟩ := hy
        have : y' = y := by
          have h1 : n * y' * n⁻¹ = n * y * n⁻¹ := hyy
          simpa using h1
        rwa [← this]
    have hxN : x ∈ normalizer (X : Set G) := hMX (hXM hxX)
    have hnN : n ∈ normalizer (X : Set G) := mul_mem (inv_mem hxN) h.2
    have hsplit : normalizerFrattiniConj X h = normalizerFrattiniConj X ⟨n, hnN⟩ := by
      have : h = ⟨x, hxN⟩ * ⟨n, hnN⟩ := Subtype.ext (by simp [hn])
      rw [this, map_mul, normalizerFrattiniConj_eq_one_of_mem hXp _ hxX, one_mul]
    rw [hsplit]
    obtain ⟨y₀, rfl⟩ : ∃ y₀ : (P₀ : Subgroup X), θ (eP y₀) = w := by
      obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective w
      obtain ⟨y₀, hy₀⟩ := e₀.surjective q
      exact ⟨y₀, by rw [hθψ, ← hy₀]; rfl⟩
    have hnyP : n * ((y₀ : X) : G) * n⁻¹ ∈ P := (mem_normalizer_iff.mp hnP _).mp ⟨y₀, y₀.2, rfl⟩
    obtain ⟨z₀, hz₀, hz₀y⟩ := hnyP
    set z : (P₀ : Subgroup X) := ⟨z₀, hz₀⟩ with hz
    have hnJ : n ∈ J := hg hnH
    have hsS : π ⟨n, hnJ⟩ ∈ S := ⟨⟨n, hnJ⟩, mem_inf.mpr ⟨hnH, hnP⟩, rfl⟩
    have hconj : ((eP z : Pbar) : J ⧸ Ag') =
        π ⟨n, hnJ⟩ * ((eP y₀ : Pbar) : J ⧸ Ag') * (π ⟨n, hnJ⟩)⁻¹ := by
      rw [heP, heP, hψ, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_inv, ← map_mul,
        ← map_mul]
      congr 1
      exact Subtype.ext hz₀y
    have h1 := hY _ hsS (eP y₀) (eP z) hconj hw
    rw [hθψ] at h1 ⊢
    have h2 : X.normalizerMonoidHom ⟨n, hnN⟩ (y₀ : X) = z₀ := Subtype.ext hz₀y.symm
    change (((X.normalizerMonoidHom ⟨n, hnN⟩ (y₀ : X) : X) : X ⧸ CFSG.pCore 2 X) :
      (X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) ∈ Y
    rw [h2]
    exact h1
  have hRP : R = Pbar :=
    NQBlock.nq_normal_rank_two_prime_torsion_rigidity hp2 hΓrk R Pbar hRrk hPrk hRexp hPexp
      ⟨hΦlt, fun Y hΦY hYP hYn => frattini_lattice_irreducible hSP θ hθker hirrS Y hΦY hYP hYn⟩
  have hPXg : P ≤ Xg := by
    rintro _ ⟨y, hy, rfl⟩
    have hyJ : (y : G) ∈ J := hXJ y.2
    have h1 : π ⟨y, hyJ⟩ ∈ R := by
      rw [hRP]
      exact ⟨⟨y, hyJ⟩, ⟨y, hy, rfl⟩, rfl⟩
    obtain ⟨z, hz, hzy⟩ := h1
    have h2 : z⁻¹ * ⟨y, hyJ⟩ ∈ Ag' := QuotientGroup.eq.mp hzy
    have h3 : (z : G)⁻¹ * y ∈ Xg := hAgXg h2
    have h4 : (y : G) = z * ((z : G)⁻¹ * y) := by group
    change (y : G) ∈ Xg
    rw [h4]
    exact Xg.mul_mem hz h3
  set N₀ : Subgroup X := Xg.subgroupOf X with hN₀
  have hN₀n : N₀.Normal := ⟨fun a ha b => by
    simp only [hN₀, mem_subgroupOf, coe_mul, coe_inv] at ha ⊢
    exact (mem_normalizer_iff.mp (hJXg (hXJ b.2)) _).mp ha⟩
  have hP₀N₀ : (P₀ : Subgroup X) ≤ N₀ := fun y hy => hPXg ⟨y, hy, rfl⟩
  have hidx : (P₀ : Subgroup X).index = Nat.card (CFSG.pCore 2 X) := by
    have h1 := (P₀ : Subgroup X).card_mul_index
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 X)
    rw [Nat.card_congr e₀.toEquiv] at h1
    rw [h2] at h1
    have hpos : 0 < Nat.card (X ⧸ CFSG.pCore 2 X) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_left hpos h1
  have hN₀2 : IsPGroup 2 (X ⧸ N₀) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := X))
    refine isPGroup_two_of_card_dvd (k := k) ?_
    rw [← hk, ← hidx]
    exact index_dvd_of_le hP₀N₀
  have hXXg : X ≤ Xg := by
    intro x hx
    have h1 : (⟨x, hx⟩ : X) ∈ N₀ := by rw [hX2 N₀ hN₀2]; exact mem_top _
    exact h1
  have hXeq : X = Xg := eq_of_le_of_card_ge hXXg (by rw [card_conjugate])
  have hgN : g ∈ normalizer (X : Set G) := by
    rw [mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have h1 : z ∈ Xg := hXeq ▸ hz
      exact mem_conjugate_iff.mp h1
    · intro hz
      have h1 : z ∈ Xg := mem_conjugate_iff.mpr hz
      rwa [← hXeq] at h1
  have hgM : g ∈ M := hN ▸ hgN
  refine ⟨hgM, ?_⟩
  ext z
  rw [mem_conjugate_iff]
  constructor
  · intro hz
    have h1 : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [h1]
    exact M.mul_mem (M.mul_mem (M.inv_mem hgM) hz) hgM
  · intro hz
    exact M.mul_mem (M.mul_mem hgM hz) (M.inv_mem hgM)

end CFSG.Quasithin.H13.NQRigid
