module

public import CFSG.RankThree.PartOne.S12.Sec1511Fam
public import CFSG.RankThree.PartOne.S12.Sec1511Tools
public import CFSG.RankThree.PartOne.S12.Sec153
public import CFSG.RankThree.PartOne.U5K.KernelTwo

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

namespace Sec1511

@[expose] def KFU5Irr : Prop :=
  ∀ (f : ℕ), 1 ≤ f → 5 ∣ 2 ^ f + 1 →
    ∀ (Ab : Subgroup (MulAut (projSU 5 2 f))), Ab ≤ U5K.U5Inndiag f → IsElementaryAbelian 5 ↥Ab →
      Nat.card ↥Ab = 5 ^ 3 →
      ∀ xb : MulAut (projSU 5 2 f), xb ∈ Subgroup.normalizer (Ab : Set (MulAut (projSU 5 2 f))) →
        xb ^ 5 = 1 → (∃ a ∈ Ab, xb * a * xb⁻¹ ≠ a) →
        ∀ Rb : Subgroup (MulAut (projSU 5 2 f)), IsPGroup 2 ↥Rb →
          Ab ≤ Subgroup.normalizer (Rb : Set (MulAut (projSU 5 2 f))) →
          xb ∈ Subgroup.normalizer (Rb : Set (MulAut (projSU 5 2 f))) → Rb = ⊥

section Core

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_O2_of_centralizes (hchar : CFSG.IsCharacteristicPType G 2) {M : Subgroup G}
    (hloc : CFSG.IsPLocal 2 M) {y : G} (hy : y ∈ M) (hcomm : ∀ r ∈ O2 M, y * r = r * y) :
    y ∈ O2 M := by
  have hchP := hchar M hloc
  have hmem : (⟨y, hy⟩ : ↥M) ∈
      Subgroup.centralizer ((CFSG.pCore 2 ↥M : Subgroup ↥M) : Set ↥M) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    apply Subtype.ext
    exact (hcomm (z : G) ⟨z, hz, rfl⟩).symm
  exact ⟨⟨y, hy⟩, hchP hmem, rfl⟩

theorem le_of_normalized_by_plane {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {A R N : Subgroup G}
    (hA : IsElementaryAbelian p ↥A) (hAcard : Nat.card ↥A = p ^ 3) (hR2 : IsPGroup 2 ↥R)
    (hAR : A ≤ Subgroup.normalizer (R : Set G))
    (hcent : ∀ a ∈ A, a ≠ 1 → Subgroup.centralizer ({a} : Set G) ≤ N) : R ≤ N := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite ↥A := inferInstance
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥A) p
    (show p ^ 2 ∣ Nat.card ↥A by rw [hAcard]; exact pow_dvd_pow p (by norm_num))
  set B₂ : Subgroup G := K.map A.subtype with hB₂
  have hB₂A : B₂ ≤ A := Subgroup.map_subtype_le K
  have hB₂card : Nat.card ↥B₂ = p ^ 2 := by
    rw [hB₂, Subgroup.card_map_of_injective A.subtype_injective]
    exact hK
  have hpow : ∀ member : ↥B₂, member ^ p = 1 := fun m => by
    have := hA
    have h1 : ((⟨(m : G), hB₂A m.2⟩ : ↥A)) ^ p = 1 :=
      Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p ↥A) _
    exact Subtype.ext (by simpa using congrArg Subtype.val h1)
  have hcompl : ¬ p ∣ Nat.card ↥R := by
    have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := hR2.exists_card_eq
    rw [hn]
    intro h5
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h5)
    exact hp2 this
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane p hp
    B₂ R hpow hB₂card hcompl (fun b hb => hAR (hB₂A hb))
  rw [hgen]
  refine iSup_le fun m => iSup_le fun hm => ?_
  refine inf_le_right.trans (hcent (m : G) (hB₂A m.2) fun h => hm (Subtype.ext h))

theorem exists_maximal {A : Subgroup G} {x : G} {S : Subgroup G} (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 ↥S)
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) (hxS : x ∈ Subgroup.normalizer (S : Set G)) :
    ∃ R : Subgroup G, R ≠ ⊥ ∧ IsPGroup 2 ↥R ∧ O2 (Subgroup.normalizer (R : Set G)) = R ∧
      A ≤ Subgroup.normalizer (R : Set G) ∧ x ∈ Subgroup.normalizer (R : Set G) := by
  classical
  let 𝒴 : Set (Subgroup G) := {M | (∃ S' : Subgroup G, S' ≠ ⊥ ∧ IsPGroup 2 ↥S' ∧
    M = Subgroup.normalizer (S' : Set G)) ∧ A ≤ M ∧ x ∈ M}
  have hne : 𝒴.Nonempty := ⟨Subgroup.normalizer (S : Set G), ⟨S, hS1, hS2, rfl⟩, hAS, hxS⟩
  obtain ⟨M₁, ⟨⟨S₁, hS₁1, hS₁2, hM₁⟩, hAM₁, hxM₁⟩, hmax⟩ :=
    Set.exists_max_image 𝒴 (fun M => Nat.card ↥(O2 M)) (Set.toFinite 𝒴) hne
  have hS₁O : S₁ ≤ O2 M₁ := by
    rw [hM₁]
    exact le_O2 Subgroup.le_normalizer hS₁2
      (fun y hy t ht => (Subgroup.mem_normalizer_iff.1 hy t).1 ht)
  have hR1 : O2 M₁ ≠ ⊥ := fun h => hS₁1 (le_bot_iff.1 (h ▸ hS₁O))
  have hM₁le : M₁ ≤ Subgroup.normalizer (O2 M₁ : Set G) := le_normalizer_O2 M₁
  have hM₂ : Subgroup.normalizer (O2 M₁ : Set G) ∈ 𝒴 :=
    ⟨⟨O2 M₁, hR1, O2_isPGroup M₁, rfl⟩, hAM₁.trans hM₁le, hM₁le hxM₁⟩
  have hcard := hmax _ hM₂
  have hle : O2 M₁ ≤ O2 (Subgroup.normalizer (O2 M₁ : Set G)) :=
    le_O2 Subgroup.le_normalizer (O2_isPGroup M₁)
      (fun y hy t ht => (Subgroup.mem_normalizer_iff.1 hy t).1 ht)
  have heq : O2 M₁ = O2 (Subgroup.normalizer (O2 M₁ : Set G)) :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  exact ⟨O2 M₁, hR1, O2_isPGroup M₁, heq.symm, hAM₁.trans hM₁le, hM₁le hxM₁⟩

end Core

section Main

theorem kf1511A_of_inputs (h1510 : Node1510) (hU5 : U5FiveInndiag) (hMod : KFU5Mod) (hAt : KFU5At)
    (hIrr : KFU5Irr) : KF1511A := by
  classical
  intro G _ _ p A c L E h15 hF hout hp5
  subst hp5
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h := h15.h12
  have hEel : IsElementaryAbelian 5 ↥E := h.E_elem
  have hAE : A ≤ E := h.A_le_E
  have hAcard : Nat.card ↥A = 5 ^ 3 := h.A_card
  have hAel : IsElementaryAbelian 5 ↥A := elemAbelian_of_le hEel hAE
  have hchar : CFSG.IsCharacteristicPType G 2 := h.setup.2.2.2.1
  have hout' : Outcome152 5 E A (lieGenerated 5 E) := Or.inr (Or.inr (Or.inr (Or.inr hout)))
  have hN : ∀ U : Subgroup G, U ≤ E → U ≠ ⊥ →
      Subgroup.normalizer (U : Set G) ≤ lieNormalizer 5 E :=
    fun U hU hU1 => h1510 G 5 A c L E h15 hF hout' U hU hU1
  have hfaith := Sec153.u5_faithful_of hMod hAt G 5 A c L E h15 hF hout
  obtain ⟨f, hf1, hf5, ⟨e⟩, -⟩ := id hout
  have hA1 : A ≠ ⊥ := by
    intro hbot
    have h1 := hAcard
    rw [hbot, Subgroup.card_bot] at h1
    omega
  have hE1 : E ≠ ⊥ := fun hbot => hA1 (le_bot_iff.1 (hbot ▸ hAE))
  have hEN : E ≤ lieNormalizer 5 E := Subgroup.le_normalizer.trans (hN E le_rfl hE1)
  have hAN : A ≤ lieNormalizer 5 E := hAE.trans hEN
  have hcent : ∀ a ∈ A, a ≠ 1 → Subgroup.centralizer ({a} : Set G) ≤ lieNormalizer 5 E := by
    intro a ha ha1
    refine (StrongP.centralizer_singleton_le_normalizer_zpowers a).trans
      (hN _ (Subgroup.zpowers_le.2 (hAE ha)) ?_)
    rw [Ne, Subgroup.zpowers_eq_bot]
    exact ha1
  intro Y P hY2 _hYN hP hPE x hxP hxN hx5
  by_contra hxC
  obtain ⟨S, hS1, hS2, hYS⟩ := hY2
  have hAY : A ≤ Y := by
    rw [← hPE]
    exact inf_le_left.trans hP.1
  have hxY : x ∈ Y := hP.1 hxP
  obtain ⟨R, hR1, hR2, hRO, hAR, hxR⟩ :=
    exists_maximal hS1 hS2 (hAY.trans hYS) (hYS hxY)
  have hRN : R ≤ lieNormalizer 5 E :=
    le_of_normalized_by_plane Nat.prime_five (by norm_num) hAel hAcard hR2 hAR hcent
  have hxN' : x ∈ lieNormalizer 5 E := hN A hAE hA1 hxN
  set I : Subgroup G := lieGenerated 5 E with hI
  set Nn : Subgroup G := Subgroup.normalizer (I : Set G) with hNn
  let ρ : ↥Nn →* MulAut (projSU 5 2 f) := U5K.U5Act I e
  have hρinj : ∀ (u v : G) (hu : u ∈ Nn) (hv : v ∈ Nn), u ∈ E → v ∈ E →
      ρ ⟨u, hu⟩ = ρ ⟨v, hv⟩ → u = v := by
    intro u v hu hv huE hvE huv
    have hmem : u * v⁻¹ ∈ Nn := Nn.mul_mem hu (Nn.inv_mem hv)
    have h1 : ρ ⟨u * v⁻¹, hmem⟩ = 1 := by
      have : (⟨u * v⁻¹, hmem⟩ : ↥Nn) = ⟨u, hu⟩ * ⟨v, hv⟩⁻¹ := rfl
      rw [this, map_mul, map_inv, huv, mul_inv_cancel]
    exact mul_inv_eq_one.1 (hfaith f e (u * v⁻¹) hmem (E.mul_mem huE (E.inv_mem hvE)) h1)
  let A' : Subgroup ↥Nn := A.subgroupOf Nn
  let R' : Subgroup ↥Nn := R.subgroupOf Nn
  let Ab : Subgroup (MulAut (projSU 5 2 f)) := A'.map ρ
  let Rb : Subgroup (MulAut (projSU 5 2 f)) := R'.map ρ
  have hxNn : x ∈ Nn := hxN'
  let xb : MulAut (projSU 5 2 f) := ρ ⟨x, hxNn⟩
  have hAbInn : Ab ≤ U5K.U5Inndiag f := by
    rintro _ ⟨⟨a, haN⟩, ha, rfl⟩
    exact hU5 G 5 A c L E h15 hF hout rfl f e a haN (hAE (Subgroup.mem_subgroupOf.1 ha))
  have hAbel : IsElementaryAbelian 5 ↥Ab := by
    have := hAel
    have : IsElementaryAbelian 5 ↥A' := IsElementaryAbelian.subgroupOf hAN
    exact IsElementaryAbelian.map ρ
  have hAbcard : Nat.card ↥Ab = 5 ^ 3 := by
    have hinj : Function.Injective (ρ.comp A'.subtype) := by
      intro a b hab
      have h1 : ρ a.1 = ρ b.1 := hab
      have h2 := hρinj (a.1 : G) (b.1 : G) a.1.2 b.1.2 (hAE (Subgroup.mem_subgroupOf.1 a.2))
        (hAE (Subgroup.mem_subgroupOf.1 b.2)) h1
      exact Subtype.ext (Subtype.ext h2)
    have hrange : Ab = (ρ.comp A'.subtype).range := by
      ext y
      simp [Ab, Subgroup.mem_map, MonoidHom.mem_range]
    have hcardA' : Nat.card ↥A' = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAN).toEquiv
    rw [hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcardA', hAcard]
  have hxA' : (⟨x, hxNn⟩ : ↥Nn) ∈ Subgroup.normalizer (A' : Set ↥Nn) := by
    rw [Subgroup.mem_normalizer_iff]
    intro a
    have := Subgroup.mem_normalizer_iff.1 hxN (a : G)
    simpa [A', Subgroup.mem_subgroupOf] using this
  have hxb : xb ∈ Subgroup.normalizer (Ab : Set (MulAut (projSU 5 2 f))) :=
    Subgroup.le_normalizer_map ρ ⟨⟨x, hxNn⟩, hxA', rfl⟩
  have hxb5 : xb ^ 5 = 1 := by
    have h1 : (⟨x, hxNn⟩ : ↥Nn) ^ 5 = 1 := Subtype.ext (by simpa using hx5)
    show ρ ⟨x, hxNn⟩ ^ 5 = 1
    rw [← map_pow, h1, map_one]
  have hnt : ∃ a ∈ Ab, xb * a * xb⁻¹ ≠ a := by
    obtain ⟨a, haA, hax⟩ : ∃ a ∈ A, ¬ (a * x = x * a) := by
      by_contra hcon
      push Not at hcon
      exact hxC (Subgroup.mem_centralizer_iff.2 hcon)
    have hxa : x * a * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 hxN a).1 haA
    have haN : a ∈ Nn := hAN haA
    have hxaN : x * a * x⁻¹ ∈ Nn := Nn.mul_mem (Nn.mul_mem hxNn haN) (Nn.inv_mem hxNn)
    refine ⟨ρ ⟨a, haN⟩, ⟨⟨a, haN⟩, Subgroup.mem_subgroupOf.2 haA, rfl⟩, ?_⟩
    intro hcon
    have h2 : xb * ρ ⟨a, haN⟩ * xb⁻¹ = ρ ⟨x * a * x⁻¹, hxaN⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h2] at hcon
    have h3 := hρinj (x * a * x⁻¹) a hxaN haN (hAE hxa) (hAE haA) hcon
    exact hax (mul_inv_eq_iff_eq_mul.1 h3).symm
  have hRb2 : IsPGroup 2 ↥Rb := hR2.comap_subtype.map ρ
  have hnormR : ∀ g : G, g ∈ Subgroup.normalizer (R : Set G) → ∀ hg : g ∈ Nn,
      (⟨g, hg⟩ : ↥Nn) ∈ Subgroup.normalizer (R' : Set ↥Nn) := by
    intro g hg hgN
    rw [Subgroup.mem_normalizer_iff]
    intro r
    have := Subgroup.mem_normalizer_iff.1 hg (r : G)
    simpa [R', Subgroup.mem_subgroupOf] using this
  have hAbR : Ab ≤ Subgroup.normalizer (Rb : Set (MulAut (projSU 5 2 f))) := by
    rintro _ ⟨⟨a, haN⟩, ha, rfl⟩
    exact Subgroup.le_normalizer_map ρ
      ⟨⟨a, haN⟩, hnormR a (hAR (Subgroup.mem_subgroupOf.1 ha)) haN, rfl⟩
  have hxbR : xb ∈ Subgroup.normalizer (Rb : Set (MulAut (projSU 5 2 f))) :=
    Subgroup.le_normalizer_map ρ ⟨⟨x, hxNn⟩, hnormR x hxR hxNn, rfl⟩
  have hRb : Rb = ⊥ := hIrr f hf1 hf5 Ab hAbInn hAbel hAbcard xb hxb hxb5 hnt Rb hRb2 hAbR hxbR
  have hρR : ∀ r (hr : r ∈ R), ρ ⟨r, hRN hr⟩ = 1 := by
    intro r hr
    have hmem : ρ ⟨r, hRN hr⟩ ∈ Rb := ⟨⟨r, hRN hr⟩, Subgroup.mem_subgroupOf.2 hr, rfl⟩
    rw [hRb] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hcomm : ∀ g ∈ U5K.commI I, ∀ r ∈ R, g * r = r * g := by
    intro g hg r hr
    exact Subgroup.mem_centralizer_iff.1
      (U5K.kerG_le_centralizer_commI e (U5K.mem_kerG.2 ⟨hRN hr, hρR r hr⟩)) g hg
  have hloc : CFSG.IsPLocal 2 (Subgroup.normalizer (R : Set G)) := ⟨R, hR1, hR2, rfl⟩
  have hcommI : U5K.commI I ≤ R := by
    intro g hg
    have hgN : g ∈ Subgroup.normalizer (R : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro n
      constructor
      · intro hn
        have h1 := hcomm g hg n hn
        have h2 : g * n * g⁻¹ = n := by
          calc g * n * g⁻¹ = n * g * g⁻¹ := by rw [h1]
            _ = n := by group
        rw [h2]
        exact hn
      · intro hn
        have hginv : g⁻¹ ∈ U5K.commI I := (U5K.commI I).inv_mem hg
        have h1 := hcomm g⁻¹ hginv _ hn
        have h2 : n = g * n * g⁻¹ := by
          calc n = g⁻¹ * (g * n * g⁻¹) * g := by group
            _ = (g * n * g⁻¹) * g⁻¹ * g := by rw [h1]
            _ = g * n * g⁻¹ := by group
        rw [h2]
        exact hn
    have hgO : g ∈ O2 (Subgroup.normalizer (R : Set G)) :=
      mem_O2_of_centralizes hchar hloc hgN (fun r hr' => hcomm g hg r (hRO ▸ hr'))
    rw [hRO] at hgO
    exact hgO
  have hperf : Group.IsPerfect ↥(U5K.commI I) := U5K.isPerfect_commI e hf1
  have hne : U5K.commI I ≠ ⊥ := U5K.commI_ne_bot e hf1
  have hnil : Group.IsNilpotent ↥(U5K.commI I) := (hR2.to_le hcommI).isNilpotent
  have : Nontrivial ↥(U5K.commI I) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  exact (Group.IsPerfect.not_isNilpotent (G := ↥(U5K.commI I))) hnil

end Main

end Sec1511

end CFSG.RankThree.PartOne
