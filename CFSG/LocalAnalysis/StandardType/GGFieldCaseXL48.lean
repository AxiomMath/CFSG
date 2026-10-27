module

public import CFSG.LocalAnalysis.StandardType.GGFieldCase

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open scoped commutatorElement

section Defs

variable {G : Type} [Group G]

@[expose] def ggL48H0 (x : G) (U₁ : Subgroup G) : Subgroup G :=
  Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.normalizer (U₁ : Set G)

@[expose] def ggL48U2 (x : G) (U₁ : Subgroup G) : Subgroup G :=
  U₁ ⊓ Subgroup.centralizer ({x} : Set G)

end Defs

@[expose] def GGL48QuotInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ → GGL46 p Bs x X U U₁ →
      ∀ R : Subgroup G, IsPGroup p R → (∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R) →
        U ≤ R → (∀ A ∈ thompsonAbelianSubgroups R, A = U₁) →
        ∃ ψ : Subgroup.normalizer (U₁ : Set G) →* Multiplicative (ZMod p), ψ ≠ 1

@[expose] def GGL48CentInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ → GGL46 p Bs x X U U₁ →
      ∀ R : Subgroup G, IsPGroup p R → (∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R) →
        U ≤ R → (∀ A ∈ thompsonAbelianSubgroups R, A = U₁) →
        x ∉ ⁅ggL48H0 x U₁, ggL48H0 x U₁⁆ ⊔ ggL48U2 x U₁

@[expose] def GGL48NonCoverInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ → GGL46 p Bs x X U U₁ →
      ∀ R : Subgroup G, IsPGroup p R → (∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R) →
        U ≤ R → (∀ A ∈ thompsonAbelianSubgroups R, A = U₁) →
        x ∉ ⁅ggL48H0 x U₁, ggL48H0 x U₁⁆ ⊔ ggL48U2 x U₁ →
        ¬ Subgroup.normalizer (U₁ : Set G) ≤
          ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G) →
        ∃ ψ : Subgroup.normalizer (U₁ : Set G) →* Multiplicative (ZMod p), ψ ≠ 1

@[expose] def GGL48NonCoverXInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁ → GGL46 p Bs x X U U₁ →
      ∀ R : Subgroup G, IsPGroup p R → (∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R) →
        U ≤ R → (∀ A ∈ thompsonAbelianSubgroups R, A = U₁) →
        x ∉ ⁅ggL48H0 x U₁, ggL48H0 x U₁⁆ ⊔ ggL48U2 x U₁ →
        ¬ Subgroup.normalizer (U₁ : Set G) ≤
          ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G) →
        x ∉ ⁅Subgroup.normalizer (U₁ : Set G), Subgroup.normalizer (U₁ : Set G)⁆

namespace GGL48

variable {G : Type} [Group G]

theorem commutator_le_self' (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem ha hb) (H.inv_mem ha)) (H.inv_mem hb)

theorem le_normalizer_commutator (H : Subgroup G) :
    H ≤ Subgroup.normalizer ((⁅H, H⁆ : Subgroup G) : Set G) :=
  Subgroup.le_normalizer_iff_commutator_le_left.mpr
    (Subgroup.commutator_mono (commutator_le_self' H) le_rfl)

theorem conj_mem_sup {A B : Subgroup G} {g : G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) {t : G} (ht : t ∈ A ⊔ B) : g * t * g⁻¹ ∈ A ⊔ B := by
  have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun a ha => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hA a).mp ha))
      (fun b hb => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hB b).mp hb))
  exact hle ht

theorem exists_conj_mem_of_isPGroup [Finite G] {p : ℕ} [Fact p.Prime] {Q : Subgroup G}
    (hQ : IsPGroup p Q) (S : Sylow p G) : ∃ g : G, ∀ q ∈ Q, g * q * g⁻¹ ∈ (S : Subgroup G) := by
  obtain ⟨T, hT⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G T S
  refine ⟨g, fun q hq => ?_⟩
  rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simpa [MulAut.smul_def, MulAut.conj_apply, mul_assoc] using hT hq

theorem mem_of_mem_centralizer_of_pow_eq_one [Finite G] {p : ℕ} [Fact p.Prime]
    {R U₁ : Subgroup G} (hRp : IsPGroup p R)
    (hRmax : ∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R)
    (hA : ∀ A ∈ thompsonAbelianSubgroups R, A = U₁) {g : G}
    (hg : g ∈ Subgroup.centralizer (U₁ : Set G)) {k : ℕ} (hgk : g ^ p ^ k = 1) : g ∈ U₁ := by
  obtain ⟨hU₁R, hU₁ab, hU₁max⟩ := mem_thompsonAbelianSubgroups_of_forall_eq hA
  set Q : Subgroup G := U₁ ⊔ Subgroup.zpowers g with hQdef
  have hZC : Subgroup.zpowers g ≤ Subgroup.centralizer (U₁ : Set G) :=
    Subgroup.zpowers_le.mpr hg
  have hU₁C : U₁ ≤ Subgroup.centralizer (U₁ : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hU₁ab
  have hQU₁ : Q ≤ Subgroup.centralizer (U₁ : Set G) := sup_le hU₁C hZC
  have hQZ : Q ≤ Subgroup.centralizer (Subgroup.zpowers g : Set G) :=
    sup_le (Subgroup.le_centralizer_iff.mp hZC) (Subgroup.le_centralizer _)
  have hQab : IsMulCommutative Q :=
    Subgroup.le_centralizer_iff_isMulCommutative.mp
      (sup_le (Subgroup.le_centralizer_iff.mp hQU₁) (Subgroup.le_centralizer_iff.mp hQZ))
  have hgp : IsPGroup p (Subgroup.zpowers g) := by
    rintro ⟨z, hz⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨k, Subtype.ext ?_⟩
    change (g ^ n) ^ p ^ k = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hgk, one_zpow]
  have hQp : IsPGroup p Q :=
    IsPGroup.to_sup_of_normal_right' (hRp.to_le hU₁R) hgp
      ((Subgroup.le_centralizer_iff.mp hZC).trans (Subgroup.centralizer_le_normalizer _))
  let S : Sylow p G := ⟨R, hRp, fun {Q'} hQ' hRQ' => hRmax Q' hQ' hRQ'⟩
  obtain ⟨c, hc⟩ := exists_conj_mem_of_isPGroup hQp S
  set A : Subgroup G := Q.map (MulAut.conj c).toMonoidHom with hAdef
  have hAR : A ≤ R := by
    rintro _ ⟨q, hq, rfl⟩
    simpa [MulAut.conj_apply] using hc q hq
  have hAcard : Nat.card A = Nat.card Q :=
    Subgroup.card_map_of_injective (MulAut.conj c).injective
  have hle : Nat.card Q ≤ Nat.card U₁ :=
    hAcard ▸ hU₁max A hAR (isMulCommutative_map hQab _)
  have hQeq : U₁ = Q := Subgroup.eq_of_le_of_card_ge le_sup_left hle
  rw [hQeq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g)

theorem pow_inv_mul_mul_pow_eq {U₁ : Subgroup G} {x' : G} {e : ℕ}
    (hx : ∀ u ∈ U₁, x'⁻¹ * u * x' = u ^ e) (j : ℕ) :
    ∀ u ∈ U₁, (x' ^ j)⁻¹ * u * x' ^ j = u ^ (e ^ j) := by
  induction j with
  | zero => intro u _; simp
  | succ j ih =>
    intro u hu
    have hmem : (x' ^ j)⁻¹ * u * x' ^ j ∈ U₁ := (ih u hu) ▸ U₁.pow_mem hu _
    calc (x' ^ (j + 1))⁻¹ * u * x' ^ (j + 1) = x'⁻¹ * ((x' ^ j)⁻¹ * u * x' ^ j) * x' := by
          group
      _ = ((x' ^ j)⁻¹ * u * x' ^ j) ^ e := hx _ hmem
      _ = u ^ (e ^ (j + 1)) := by rw [ih u hu, ← pow_mul, ← pow_succ]

theorem conj_mul_inv_mem_centralizer {U₁ : Subgroup G} {x : G} {e : ℕ}
    (hx : ∀ u ∈ U₁, x⁻¹ * u * x = u ^ e) {n : G}
    (hn : n ∈ Subgroup.normalizer (U₁ : Set G)) :
    n * x * n⁻¹ * x⁻¹ ∈ Subgroup.centralizer (U₁ : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hu' : n⁻¹ * u * n ∈ U₁ := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) u).mp hu
    simpa using this
  have hpow : (n⁻¹ * u * n) ^ e = n⁻¹ * u ^ e * n := by
    rw [show n⁻¹ * u * n = n⁻¹ * u * n⁻¹⁻¹ by rw [inv_inv], conj_pow, inv_inv]
  have h1 : (n * x * n⁻¹)⁻¹ * u * (n * x * n⁻¹) = x⁻¹ * u * x := by
    calc (n * x * n⁻¹)⁻¹ * u * (n * x * n⁻¹) = n * (x⁻¹ * (n⁻¹ * u * n) * x) * n⁻¹ := by group
      _ = n * (n⁻¹ * u * n) ^ e * n⁻¹ := by rw [hx _ hu']
      _ = u ^ e := by rw [hpow]; group
      _ = x⁻¹ * u * x := (hx u hu).symm
  calc u * (n * x * n⁻¹ * x⁻¹)
      = (n * x * n⁻¹) * ((n * x * n⁻¹)⁻¹ * u * (n * x * n⁻¹)) * x⁻¹ := by group
    _ = (n * x * n⁻¹) * (x⁻¹ * u * x) * x⁻¹ := by rw [h1]
    _ = (n * x * n⁻¹ * x⁻¹) * u := by group

theorem not_mem_commutator_of_le_sup {N₀ H₀ C₀ : Subgroup G} (hH₀ : H₀ ≤ N₀)
    (hN : N₀ ≤ Subgroup.normalizer (C₀ : Set G)) (hcov : N₀ ≤ H₀ ⊔ C₀) {x : G} (hx : x ∈ H₀)
    (hxn : x ∉ ⁅H₀, H₀⁆ ⊔ (H₀ ⊓ C₀)) : x ∉ ⁅N₀, N₀⁆ := by
  have hHC : H₀ ≤ Subgroup.normalizer (C₀ : Set G) := hH₀.trans hN
  have hdec : ∀ g ∈ N₀, ∃ h ∈ H₀, ∃ c ∈ C₀, h * c = g := by
    intro g hg
    have hg' : g ∈ ((H₀ ⊔ C₀ : Subgroup G) : Set G) := hcov hg
    rw [Subgroup.coe_mul_of_left_le_normalizer_right H₀ C₀ hHC] at hg'
    obtain ⟨h, hh, c, hc, hgc⟩ := hg'
    exact ⟨h, hh, c, hc, hgc⟩
  have hconj : ∀ n ∈ N₀, ∀ c ∈ C₀, n * c * n⁻¹ ∈ C₀ := fun n hn c hc =>
    (Subgroup.mem_normalizer_iff.mp (hN hn) c).mp hc
  set S : Subgroup G := ⁅H₀, H₀⁆ ⊔ C₀ with hS
  have hcomm : ⁅N₀, N₀⁆ ≤ S := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    obtain ⟨h₁, hh₁, c₁, hc₁, rfl⟩ := hdec a ha
    obtain ⟨h₂, hh₂, c₂, hc₂, rfl⟩ := hdec b hb
    have e : ⁅h₁ * c₁, h₂ * c₂⁆ =
        (h₁ * ⁅c₁, h₂ * c₂⁆ * h₁⁻¹) * ⁅h₁, h₂⁆ * (h₂ * ⁅h₁, c₂⁆ * h₂⁻¹) := by
      simp only [commutatorElement_def]
      group
    have hm1 : ⁅c₁, h₂ * c₂⁆ ∈ C₀ := by
      rw [commutatorElement_def]
      have := C₀.mul_mem hc₁ (hconj _ hb _ (C₀.inv_mem hc₁))
      simpa [mul_assoc] using this
    have hm2 : ⁅h₁, c₂⁆ ∈ C₀ := by
      rw [commutatorElement_def]
      exact C₀.mul_mem (hconj _ (hH₀ hh₁) _ hc₂) (C₀.inv_mem hc₂)
    rw [e]
    exact S.mul_mem (S.mul_mem (Subgroup.mem_sup_right (hconj _ (hH₀ hh₁) _ hm1))
      (Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hh₁ hh₂)))
      (Subgroup.mem_sup_right (hconj _ (hH₀ hh₂) _ hm2))
  intro hxN
  have hxS : x ∈ (S : Set G) := hcomm hxN
  rw [hS, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    ((commutator_le_self' H₀).trans hHC)] at hxS
  obtain ⟨k, hk, c, hc, rfl⟩ := hxS
  apply hxn
  have hkH : k ∈ H₀ := commutator_le_self' H₀ hk
  have hcH : c ∈ H₀ := by
    have := H₀.mul_mem (H₀.inv_mem hkH) hx
    simpa using this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right ⟨hcH, hc⟩)

theorem not_mem_sup_inf_of_not_mem_sup [Finite G] {p : ℕ} [Fact p.Prime] {H₀ C₀ U₂ : Subgroup G}
    (hU₂n : H₀ ≤ Subgroup.normalizer (U₂ : Set G))
    (hCn : H₀ ≤ Subgroup.normalizer (C₀ : Set G))
    (hpel : ∀ c ∈ H₀ ⊓ C₀, ∀ k : ℕ, c ^ p ^ k = 1 → c ∈ U₂) {x : G} (hxH : x ∈ H₀)
    (hxp : x ^ p = 1) (hxn : x ∉ ⁅H₀, H₀⁆ ⊔ U₂) : x ∉ ⁅H₀, H₀⁆ ⊔ (H₀ ⊓ C₀) := by
  have hpp : p.Prime := Fact.out
  intro hx
  have hHn : H₀ ≤ Subgroup.normalizer ((H₀ ⊓ C₀ : Subgroup G) : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hCn hg⟩
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
    ((commutator_le_self' H₀).trans hHn)] at hx
  obtain ⟨k, hk, c, hc, rfl⟩ := hx
  apply hxn
  set T : Subgroup G := ⁅H₀, H₀⁆ ⊔ U₂ with hT
  have hkH : k ∈ H₀ := commutator_le_self' H₀ hk
  have hTn : (T.subgroupOf H₀).Normal := ⟨fun t ht g => by
    rw [Subgroup.mem_subgroupOf] at ht ⊢
    exact conj_mem_sup (le_normalizer_commutator H₀ g.2) (hU₂n g.2) ht⟩
  set π := QuotientGroup.mk' (T.subgroupOf H₀) with hπ
  have hπk : π ⟨k, hkH⟩ = 1 := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_sup_left hk
  have hπx : π ⟨k * c, hxH⟩ = π ⟨c, hc.1⟩ := by
    rw [show (⟨k * c, hxH⟩ : H₀) = ⟨k, hkH⟩ * ⟨c, hc.1⟩ from rfl, map_mul, hπk, one_mul]
  obtain ⟨a, m, hm, hcm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos c).ne' p
    hpp.one_lt.ne'
  have hcmT : c ^ m ∈ U₂ := by
    refine hpel _ ⟨H₀.pow_mem hc.1 m, C₀.pow_mem hc.2 m⟩ a ?_
    rw [← pow_mul, mul_comm, ← hcm, pow_orderOf_eq_one]
  have h1 : π ⟨k * c, hxH⟩ ^ m = 1 := by
    rw [hπx, ← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact Subgroup.mem_sup_right (by simpa using hcmT)
  have h2 : π ⟨k * c, hxH⟩ ^ p = 1 := by
    rw [← map_pow]
    have : (⟨k * c, hxH⟩ : H₀) ^ p = 1 := Subtype.ext (by simpa using hxp)
    rw [this, map_one]
  have hcop : Nat.Coprime m p :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hm)
  have h3 : π ⟨k * c, hxH⟩ = 1 := by
    have := pow_gcd_eq_one.mpr ⟨h1, h2⟩
    rwa [hcop.gcd_eq_one, pow_one] at this
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h3
  exact h3

end GGL48

section Config

variable {G : Type} [Group G] [Finite G]

theorem ggL48_facts {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J X B₂ : Subgroup G} {d y : G}
    {K U U₁ : Subgroup G} (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁)
    (h46 : GGL46 p Bs x X U U₁) {R : Subgroup G} (hRp : IsPGroup p R)
    (hRmax : ∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R)
    (hA : ∀ A ∈ thompsonAbelianSubgroups R, A = U₁) :
    p.Prime ∧ x ^ p = 1 ∧ x ∈ Subgroup.normalizer (U₁ : Set G) ∧
      (∃ e : ℕ, ∀ u ∈ U₁, x⁻¹ * u * x = u ^ e) ∧
      ∀ g ∈ Subgroup.centralizer (U₁ : Set G), ∀ k : ℕ, g ^ p ^ k = 1 → g ∈ U₁ := by
  have hcfg := hS.1.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hcfg.1.2.2.2.2.2.2.1.2.1
  have hBsU : Bs ≤ U := hS.2.2.2.2.2.2.1.2.2.2
  obtain ⟨-, ⟨s, -, -, -, ⟨x', hx'x, hx'⟩, -⟩, hJU, -⟩ := h46
  refine ⟨hp, hBs.2 x hxBs, normalizer_le_normalizer_of_forall_eq hJU
    (Subgroup.le_normalizer (hBsU hxBs)), ?_, fun g hg k hgk =>
      GGL48.mem_of_mem_centralizer_of_pow_eq_one hRp hRmax hA hg hgk⟩
  have hxz : x ∈ Submonoid.powers x' := by
    rw [mem_powers_iff_mem_zpowers, hx'x]
    exact Subgroup.mem_zpowers x
  obtain ⟨j, rfl⟩ := hxz
  exact ⟨(1 + p ^ (s - 1)) ^ j, GGL48.pow_inv_mul_mul_pow_eq hx' j⟩

theorem not_mem_commutator_of_cover {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (h46 : GGL46 p Bs x X U U₁)
    {R : Subgroup G} (hRp : IsPGroup p R) (hRmax : ∀ Q : Subgroup G, IsPGroup p Q → R ≤ Q → Q = R)
    (hA : ∀ A ∈ thompsonAbelianSubgroups R, A = U₁)
    (hcent : x ∉ ⁅ggL48H0 x U₁, ggL48H0 x U₁⁆ ⊔ ggL48U2 x U₁)
    (hcov : Subgroup.normalizer (U₁ : Set G) ≤
      ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)) :
    x ∉ ⁅Subgroup.normalizer (U₁ : Set G), Subgroup.normalizer (U₁ : Set G)⁆ := by
  obtain ⟨hp, hxp, hxN, -, hpel⟩ := ggL48_facts hS h46 hRp hRmax hA
  have : Fact p.Prime := ⟨hp⟩
  have hxH : x ∈ ggL48H0 x U₁ :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, hxN⟩
  have hNC : Subgroup.normalizer (U₁ : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (U₁ : Set G) : Set G) :=
    ggNormalizer_le_normalizer_centralizer U₁
  have hHN : ggL48H0 x U₁ ≤ Subgroup.normalizer (U₁ : Set G) := inf_le_right
  have hU₂n : ggL48H0 x U₁ ≤ Subgroup.normalizer (ggL48U2 x U₁ : Set G) := fun g hg =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hg.2, Subgroup.le_normalizer hg.1⟩
  refine GGL48.not_mem_commutator_of_le_sup hHN hNC hcov hxH ?_
  refine GGL48.not_mem_sup_inf_of_not_mem_sup hU₂n (hHN.trans hNC) ?_ hxH hxp hcent
  intro c hc k hck
  exact ⟨hpel c hc.2 k hck, hc.1.1⟩

end Config

theorem ggL48QuotInput_of_ggL48Input (h : GGL48Input) : GGL48QuotInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS h46 R hRp hRmax hUR hA
  obtain ⟨hp, hxp, hxN, -, -⟩ := ggL48_facts hS h46 hRp hRmax hA
  have : Fact p.Prime := ⟨hp⟩
  exact exists_monoidHom_zmod_ne_one_of_not_mem_commutator' hxN hxp
    (h G p B Bs x L D J X B₂ d y K U U₁ hS h46 R hRp hRmax hUR hA)

theorem ggL48NonCoverInput_of_x (h : GGL48NonCoverXInput) : GGL48NonCoverInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS h46 R hRp hRmax hUR hA hcent hcov
  obtain ⟨hp, hxp, hxN, -, -⟩ := ggL48_facts hS h46 hRp hRmax hA
  have : Fact p.Prime := ⟨hp⟩
  exact exists_monoidHom_zmod_ne_one_of_not_mem_commutator' hxN hxp
    (h G p B Bs x L D J X B₂ d y K U U₁ hS h46 R hRp hRmax hUR hA hcent hcov)

theorem ggL48Input_of_cent (hC : GGL48CentInput) (hN : GGL48NonCoverXInput) : GGL48Input := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS h46 R hRp hRmax hUR hA
  have hcent := hC G p B Bs x L D J X B₂ d y K U U₁ hS h46 R hRp hRmax hUR hA
  by_cases hcov : Subgroup.normalizer (U₁ : Set G) ≤
      ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)
  · exact not_mem_commutator_of_cover hS h46 hRp hRmax hA hcent hcov
  · exact hN G p B Bs x L D J X B₂ d y K U U₁ hS h46 R hRp hRmax hUR hA hcent hcov

theorem ggL48QuotInput_of_cent (hC : GGL48CentInput) (hN : GGL48NonCoverInput) :
    GGL48QuotInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS h46 R hRp hRmax hUR hA
  have hcent := hC G p B Bs x L D J X B₂ d y K U U₁ hS h46 R hRp hRmax hUR hA
  by_cases hcov : Subgroup.normalizer (U₁ : Set G) ≤
      ggL48H0 x U₁ ⊔ Subgroup.centralizer (U₁ : Set G)
  · obtain ⟨hp, hxp, hxN, -, -⟩ := ggL48_facts hS h46 hRp hRmax hA
    have : Fact p.Prime := ⟨hp⟩
    exact exists_monoidHom_zmod_ne_one_of_not_mem_commutator' hxN hxp
      (not_mem_commutator_of_cover hS h46 hRp hRmax hA hcent hcov)
  · exact hN G p B Bs x L D J X B₂ d y K U U₁ hS h46 R hRp hRmax hUR hA hcent hcov

end CFSG.StandardType

end
