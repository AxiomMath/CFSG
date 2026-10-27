module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import CFSG.LocalAnalysis.StandardType.GGPumpupCentral
public import CFSG.LocalAnalysis.StandardType.GGFieldNbrTableB

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ComponentClassification

section General

variable {G : Type} [Group G]

theorem comm_pow_mem_of_comm_mem {O : Subgroup G} {k w : G}
    (hw : w ∈ Subgroup.normalizer (O : Set G)) (h : k * w * k⁻¹ * w⁻¹ ∈ O) (n : ℕ) :
    k * w ^ n * k⁻¹ * (w ^ n)⁻¹ ∈ O := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : k * w ^ (n + 1) * k⁻¹ * (w ^ (n + 1))⁻¹ =
        (k * w ^ n * k⁻¹ * (w ^ n)⁻¹) * (w ^ n * (k * w * k⁻¹ * w⁻¹) * (w ^ n)⁻¹) := by
      group
    rw [e]
    exact O.mul_mem ih ((Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hw n) _).mp h)

theorem commutator_zpowers_le_of_forall [Finite G] {O K : Subgroup G} {w : G}
    (hw : w ∈ Subgroup.normalizer (O : Set G)) (h : ∀ k ∈ K, k * w * k⁻¹ * w⁻¹ ∈ O) :
    (⁅K, Subgroup.zpowers w⁆ : Subgroup G) ≤ O := by
  rw [Subgroup.commutator_le]
  intro k hk z hz
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hz)
  rw [commutatorElement_def]
  exact comm_pow_mem_of_comm_mem hw (h k hk) n

theorem comm_mul_mem_of_comm_mem {O : Subgroup G} {k a b : G}
    (ha : a ∈ Subgroup.normalizer (O : Set G)) (h1 : k * a * k⁻¹ * a⁻¹ ∈ O)
    (h2 : k * b * k⁻¹ * b⁻¹ ∈ O) : k * (a * b) * k⁻¹ * (a * b)⁻¹ ∈ O := by
  have e : k * (a * b) * k⁻¹ * (a * b)⁻¹ =
      (k * a * k⁻¹ * a⁻¹) * (a * (k * b * k⁻¹ * b⁻¹) * a⁻¹) := by group
  rw [e]
  exact O.mul_mem h1 ((Subgroup.mem_normalizer_iff.mp ha _).mp h2)

theorem comm_mem_of_conj {O K : Subgroup G} {g w : G}
    (hg : g ∈ Subgroup.normalizer (O : Set G))
    (h : ∀ k ∈ K.map (MulAut.conj g).toMonoidHom,
      k * (g * w * g⁻¹) * k⁻¹ * (g * w * g⁻¹)⁻¹ ∈ O) :
    ∀ k ∈ K, k * w * k⁻¹ * w⁻¹ ∈ O := by
  intro k hk
  have h1 := h (g * k * g⁻¹) (Subgroup.mem_map.mpr ⟨k, hk, by simp⟩)
  have e : g * k * g⁻¹ * (g * w * g⁻¹) * (g * k * g⁻¹)⁻¹ * (g * w * g⁻¹)⁻¹ =
      g * (k * w * k⁻¹ * w⁻¹) * g⁻¹ := by group
  rw [e] at h1
  exact (Subgroup.mem_normalizer_iff.mp hg _).mpr h1

theorem mem_zpowers_mul_self {b : G} {p : ℕ} (hp : Odd p) (hb : b ^ p = 1) :
    b ∈ Subgroup.zpowers (b * b) := by
  obtain ⟨m, rfl⟩ := hp
  refine Subgroup.mem_zpowers_iff.mpr ⟨((m + 1 : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast, ← sq, ← pow_mul]
  calc b ^ (2 * (m + 1)) = b ^ (2 * m + 1) * b := by
        rw [← pow_succ, show 2 * m + 1 + 1 = 2 * (m + 1) by ring]
    _ = b := by rw [hb, one_mul]

variable [Finite G]

theorem commutator_le_lBalancePrimeCore_of_ne {p : ℕ} [Fact p.Prime] {Y A A' : Subgroup G}
    (hA : LargeEvenPComponent p Y A) (hA' : LargeEvenPComponent p Y A') (hne : A ≠ A') :
    (⁅A, A'⁆ : Subgroup G) ≤ CFSG.Open.lBalancePrimeCore p Y := by
  obtain ⟨hAY, hAl⟩ := (largeEvenPComponent_iff_lBalance p Y A).1 hA
  obtain ⟨hA'Y, hA'l⟩ := (largeEvenPComponent_iff_lBalance p Y A').1 hA'
  have h1 := (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p Y A hAY).mpr hAl
  have h2 := (CatalogueBAlternating.pComponent_subgroupOf_iff_lBalance p Y A' hA'Y).mpr hA'l
  have hne' : A.subgroupOf Y ≠ A'.subgroupOf Y := by
    intro h
    apply hne
    have h' := congrArg (Subgroup.map Y.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hAY, Subgroup.map_subgroupOf_eq_of_le hA'Y] at h'
  have hc := (CatalogueBPrimeJoin.mutual_normalization_core_commutation p _ _ h1 h2 hne').2.2
  have hc' := Subgroup.map_mono (f := Y.subtype) (hc.trans inf_le_left)
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hAY,
    Subgroup.map_subgroupOf_eq_of_le hA'Y, GGPumpup.map_map_pPrimeCore_subgroupOf hAY] at hc'
  exact hc'.trans (largeEvenPPrimeCoreOf_le_of_isSubnormal hA.2.1)

theorem mem_normalizer_of_comm_commute {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {d g b : G}
    {J K : Subgroup G}
    (hK : LargeEvenPComponent p (Subgroup.centralizer ({d} : Set G)) K) (hJK : J ≤ K)
    (hJq : CFSG.Assembly.IsQuasisimple J) (hpJ : p ∣ Nat.card J) (hbJ : b ∈ J)
    (hbC : b ∉ Subgroup.centralizer (J : Set G)) (hbp : b ^ p = 1)
    (hgd : g ∈ Subgroup.centralizer ({d} : Set G))
    (hcg : g * b * g⁻¹ * b⁻¹ * g = g * (g * b * g⁻¹ * b⁻¹))
    (hcb : g * b * g⁻¹ * b⁻¹ * b = b * (g * b * g⁻¹ * b⁻¹)) :
    g ∈ Subgroup.normalizer (K : Set G) := by
  have hp : p.Prime := Fact.out
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  set Y := Subgroup.centralizer ({d} : Set G) with hYdef
  set O := CFSG.Open.lBalancePrimeCore p Y with hOdef
  have hON : Y ≤ Subgroup.normalizer (O : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (LBalance.primeCore_le p Y)).mp
      (LBalance.primeCore_normal p Y)
  have hKY : K ≤ Y := hK.1
  have hJY : J ≤ Y := hJK.trans hKY
  have hbK : b ∈ K := hJK hbJ
  have hbY : b ∈ Y := hKY hbK
  have hgO : g ∈ Subgroup.normalizer (O : Set G) := hON hgd
  set K₁ := K.map (MulAut.conj g).toMonoidHom with hK₁def
  set K₂ := K₁.map (MulAut.conj g).toMonoidHom with hK₂def
  have hK₁ : LargeEvenPComponent p Y K₁ := by
    have h := largeEvenPComponent_map_conj' hK g
    rwa [map_conj_eq_of_mem hgd] at h
  have hK₂ : LargeEvenPComponent p Y K₂ := by
    have h := largeEvenPComponent_map_conj' hK₁ g
    rwa [map_conj_eq_of_mem hgd] at h
  by_contra hgK
  have hne : K₁ ≠ K := fun h => hgK (mem_normalizer_iff_map_conj.mpr h)
  have hne₁₂ : K₂ ≠ K₁ := fun h => hne (Subgroup.map_injective (MulAut.conj g).injective h)
  have hβ₁K : g * b * g⁻¹ ∈ K₁ := Subgroup.mem_map.mpr ⟨b, hbK, by simp⟩
  have hβ₂K : g * (g * b * g⁻¹) * g⁻¹ ∈ K₂ := Subgroup.mem_map.mpr ⟨_, hβ₁K, by simp⟩
  have hβ₁Y : g * b * g⁻¹ ∈ Y := hK₁.1 hβ₁K
  have hgc : g * (g * b * g⁻¹ * b⁻¹) * g⁻¹ = g * b * g⁻¹ * b⁻¹ := by
    calc g * (g * b * g⁻¹ * b⁻¹) * g⁻¹ = g * b * g⁻¹ * b⁻¹ * g * g⁻¹ := by rw [hcg]
      _ = g * b * g⁻¹ * b⁻¹ := by group
  have hβ₂ : g * (g * b * g⁻¹) * g⁻¹ = g * b * g⁻¹ * (g * b * g⁻¹) * b⁻¹ := by
    calc g * (g * b * g⁻¹) * g⁻¹
        = (g * (g * b * g⁻¹ * b⁻¹) * g⁻¹) * (g * b * g⁻¹) := by group
      _ = (g * b * g⁻¹ * b⁻¹) * (g * b * g⁻¹) := by rw [hgc]
      _ = (g * b * g⁻¹ * b⁻¹) * ((g * b * g⁻¹ * b⁻¹) * b) := by group
      _ = (g * b * g⁻¹ * b⁻¹) * (b * (g * b * g⁻¹ * b⁻¹)) := by rw [hcb]
      _ = g * b * g⁻¹ * (g * b * g⁻¹) * b⁻¹ := by group
  have hbO : ∀ k ∈ K, k * b * k⁻¹ * b⁻¹ ∈ O := by
    by_cases hK2 : K₂ = K
    ·
      have hsqK : g * b * g⁻¹ * (g * b * g⁻¹) ∈ K := by
        have h := K.mul_mem (hK2 ▸ hβ₂K : g * (g * b * g⁻¹) * g⁻¹ ∈ K) hbK
        rwa [hβ₂, inv_mul_cancel_right] at h
      have h1 : ∀ k ∈ K₁, k * (g * (b * b) * g⁻¹) * k⁻¹ * (g * (b * b) * g⁻¹)⁻¹ ∈ O := by
        intro k hk
        have e : g * (b * b) * g⁻¹ = g * b * g⁻¹ * (g * b * g⁻¹) := by group
        rw [e, ← commutatorElement_def]
        exact commutator_le_lBalancePrimeCore_of_ne hK₁ hK hne
          (Subgroup.commutator_mem_commutator hk hsqK)
      have h2 := comm_mem_of_conj hgO h1
      have h3 := commutator_zpowers_le_of_forall (hON (Y.mul_mem hbY hbY)) h2
      intro k hk
      have hz : b ∈ Subgroup.zpowers (b * b) := mem_zpowers_mul_self hpodd hbp
      have h4 := h3 (Subgroup.commutator_mem_commutator hk hz)
      rwa [commutatorElement_def] at h4
    ·
      have h1 : ∀ k ∈ K₂, k * (g * (g * b * g⁻¹) * g⁻¹) * k⁻¹ *
          (g * (g * b * g⁻¹) * g⁻¹)⁻¹ ∈ O := by
        intro k hk
        rw [hβ₂]
        refine comm_mul_mem_of_comm_mem (hON (Y.mul_mem hβ₁Y hβ₁Y)) ?_ ?_
        · rw [← commutatorElement_def]
          exact commutator_le_lBalancePrimeCore_of_ne hK₂ hK₁ hne₁₂
            (Subgroup.commutator_mem_commutator hk (K₁.mul_mem hβ₁K hβ₁K))
        · rw [← commutatorElement_def]
          exact commutator_le_lBalancePrimeCore_of_ne hK₂ hK hK2
            (Subgroup.commutator_mem_commutator hk (K.inv_mem hbK))
      exact comm_mem_of_conj hgO (comm_mem_of_conj hgO h1)
  have hJO : (⁅J, Subgroup.zpowers b⁆ : Subgroup G) ≤ O :=
    (Subgroup.commutator_mono hJK le_rfl).trans (commutator_zpowers_le_of_forall (hON hbY) hbO)
  exact hbC (mem_centralizer_of_commutator_le_coprime hp hJq hpJ (LBalance.primeCore_coprime p Y)
    (hJY.trans hON) (Subgroup.le_normalizer hbJ) hJO)

end General

section Config

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_of_ggL44i {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J X : Subgroup G}
    (hFC : GGFieldCaseNoBL5 p B Bs x L D J X) (h44 : GGL44i p Bs x X) (hpJ : p ∣ Nat.card J)
    (hI2 : ∃ b ∈ Bs ⊓ J, b ∉ Subgroup.centralizer (J : Set G))
    {d : G} (hd : d ∈ Subgroup.centralizer (X : Set G)) {K : Subgroup G}
    (hK : LargeEvenPComponent p (Subgroup.centralizer ({d} : Set G)) K) (hJK : J ≤ K) :
    X ≤ Subgroup.normalizer (K : Set G) := by
  intro g hg
  have hcfg := hFC.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  obtain ⟨b, ⟨hbBs, hbJ⟩, hbC⟩ := hI2
  have hc := h44.2.1 g hg b hbBs
  have hcg : g * b * g⁻¹ * b⁻¹ * g = g * (g * b * g⁻¹ * b⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp hc.2 g hg).symm
  have hcb : g * b * g⁻¹ * b⁻¹ * b = b * (g * b * g⁻¹ * b⁻¹) :=
    mul_comm_of_isElemAbelian hBs hc.1 hbBs
  have hgd : g ∈ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hd g hg)
  exact mem_normalizer_of_comm_commute hp2 hK hJK hcfg.2.2.1.2.2.2.2.2.1.2.2 hpJ hbJ hbC
    (hBs.2 b hbBs) hgd hcg hcb

omit [Finite G] in
theorem card_bstar_le_of_ggL43 {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G} {x : G}
    (hBs : IsElemAbelian p Bs) (hxBs : x ∈ Bs) (hx1 : x ≠ 1) (h43 : GGL43 Bs x X) :
    Nat.card Bs ≤ Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) * p := by
  set B₁ := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁def
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (B₁ : Set G) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact mul_comm_of_isElemAbelian hBs hc.1 hxBs
  have hcoe := Subgroup.coe_mul_of_right_le_normalizer_left B₁ _ hle
  have h := Set.natCard_mul_le (s := (B₁ : Set G)) (t := (Subgroup.zpowers x : Set G))
  rw [← hcoe, ← h43.2] at h
  have h2 : Nat.card (Subgroup.zpowers x : Set G) = p := by
    have h3 : Nat.card (Subgroup.zpowers x : Set G) = orderOf x := Nat.card_zpowers x
    rw [h3, orderOf_eq_prime (hBs.2 x hxBs) hx1]
  rw [h2] at h
  exact h

theorem false_of_eq_sup {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J X B₂ : Subgroup G}
    (hFC : GGFieldCaseNoBL5 p B Bs x L D J X) (hM : GGTableBModule p Bs x L B₂)
    (h43 : GGL43 Bs x X) (h44ii : GGL44ii Bs x X B₂) (hpJ : p ∣ Nat.card J)
    {K : Subgroup G} (hJK : J ≤ K) (hxK : x ∈ Subgroup.normalizer (K : Set G))
    (hXK : X ≤ Subgroup.normalizer (K : Set G))
    (hKJ : K = J ⊔ LargeEvenPPrimeCoreOf p K) : False := by
  obtain ⟨hI, hBstar, hDJ⟩ := hFC.1
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType p B x L := hI.2.2.2.2.2.2.2
  have hBs : IsElemAbelian p Bs := hBstar.2.1
  have hBBs : B ≤ Bs := hBstar.1
  have hxD : x ∈ D := hDJ.1.2.2.2.1
  have hxBs : x ∈ Bs := hBBs (hDJ.1.1 hxD)
  set B₁ := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁def
  set O := LargeEvenPPrimeCoreOf p K with hOdef
  have hON : Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (O : Set G) :=
    fun g hg => mem_normalizer_largeEvenPPrimeCoreOf hg
  have hKN : K ≤ Subgroup.normalizer (O : Set G) := Subgroup.le_normalizer.trans hON
  have hOcop : Nat.Coprime p (Nat.card O) := by
    rw [hOdef, LargeEvenPPrimeCoreOf, Subgroup.card_map_of_injective K.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hJx : J ≤ Subgroup.centralizer ({x} : Set G) := by
    intro j hj
    have hj' := (hDJ.1.2.2.2.2.2.1.1 hj).2
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hj' x hxD).symm
  have hxO : (⁅K, Subgroup.zpowers x⁆ : Subgroup G) ≤ O :=
    commutator_le_of_le_sup hxK hJx hJK hKJ.le
  have hcommD : ∀ g ∈ X, g * x * g⁻¹ * x⁻¹ ∈ B → g * x * g⁻¹ * x⁻¹ ∈ D := by
    intro g hg htB
    have hgK : g ∈ Subgroup.normalizer (K : Set G) := hXK hg
    have hgxK : g * x * g⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgK hxK) (Subgroup.inv_mem _ hgK)
    have htK : g * x * g⁻¹ * x⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
      Subgroup.mul_mem _ hgxK (Subgroup.inv_mem _ hxK)
    have hk : ∀ k ∈ K, k * (g * x * g⁻¹ * x⁻¹) * k⁻¹ * (g * x * g⁻¹ * x⁻¹)⁻¹ ∈ O := by
      intro k hk
      refine comm_mul_mem_of_comm_mem (hON hgxK) ?_ ?_
      · have hk' : g⁻¹ * k * g ∈ K := by
          have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgK) k).mp hk
          simpa using h
        have h1 : g⁻¹ * k * g * x * (g⁻¹ * k * g)⁻¹ * x⁻¹ ∈ O := by
          have h := hxO (Subgroup.commutator_mem_commutator hk' (Subgroup.mem_zpowers x))
          rwa [commutatorElement_def] at h
        have e : k * (g * x * g⁻¹) * k⁻¹ * (g * x * g⁻¹)⁻¹ =
            g * (g⁻¹ * k * g * x * (g⁻¹ * k * g)⁻¹ * x⁻¹) * g⁻¹ := by group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hON hgK) _).mp h1
      · have h := hxO (Subgroup.commutator_mem_commutator hk
          (Subgroup.inv_mem _ (Subgroup.mem_zpowers x)))
        rwa [commutatorElement_def] at h
    have hJt : (⁅J, Subgroup.zpowers (g * x * g⁻¹ * x⁻¹)⁆ : Subgroup G) ≤ O :=
      (Subgroup.commutator_mono hJK le_rfl).trans (commutator_zpowers_le_of_forall (hON htK) hk)
    have htC := mem_centralizer_of_commutator_le_coprime hp hDJ.1.2.2.2.2.2.1.2.2 hpJ hOcop
      (hJK.trans hKN) (le_normalizer_of_stdSub hS hst hDJ.1 htB) hJt
    rw [hDJ.1.2.2.2.2.2.2]
    exact ⟨htB, htC⟩
  have hS1 : B ⊓ (B₁ ⊓ B₂) ≤ D ⊓ B₁ := by
    rintro s ⟨hsB, hsB₁, hsB₂⟩
    obtain ⟨g, hg, rfl⟩ : ∃ g ∈ X, g * x * g⁻¹ * x⁻¹ = s := by
      rcases h44ii with h | ⟨-, h⟩
      · exact (h s).1 hsB₁
      · exact (h s).1 ⟨hsB₁, hsB₂⟩
    exact ⟨hcommD g hg hsB, hsB₁⟩
  obtain ⟨d', hd', hd'1⟩ := exists_inf_eq_zpowers_of_ggL43 hFC.1 h43
  have hDB₁ : Nat.card (D ⊓ B₁ : Subgroup G) = p := by
    have hd'Bs : d' ∈ Bs := by
      have h : d' ∈ D ⊓ B₁ := by
        rw [hd']
        exact Subgroup.mem_zpowers d'
      exact h.2.1
    rw [hd', Nat.card_zpowers]
    exact orderOf_eq_prime (hBs.2 d' hd'Bs) hd'1
  have hc1 : Nat.card (B ⊓ (B₁ ⊓ B₂) : Subgroup G) ≤ p := hDB₁ ▸ Subgroup.card_le_of_le hS1
  have hc2 : Nat.card (B₁ ⊓ B₂ : Subgroup G) ≤ p * Nat.card (B ⊓ (B₁ ⊓ B₂) : Subgroup G) :=
    card_le_mul_card_inf (inf_le_left.trans inf_le_left) hBBs hBstar.2.2.1
  have hc3 : Nat.card B₁ ≤ p * Nat.card (B₂ ⊓ B₁ : Subgroup G) :=
    card_le_mul_card_inf inf_le_left hM.2.1 hM.2.2.1
  rw [inf_comm B₂ B₁] at hc3
  have hc4 : Nat.card Bs ≤ Nat.card B₁ * p :=
    card_bstar_le_of_ggL43 hBs hxBs hS.2.2.1 h43
  have hB4 : p ^ 4 ≤ Nat.card B := by
    rw [hS.1.2.1]
    exact Nat.pow_le_pow_right hp.pos hI.2.2.2.2.2.1.2.2.2
  have hBle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBBs
  have h5 : Nat.card Bs ≤ p * p * Nat.card (B₁ ⊓ B₂ : Subgroup G) := by
    calc Nat.card Bs ≤ Nat.card B₁ * p := hc4
      _ ≤ (p * Nat.card (B₁ ⊓ B₂ : Subgroup G)) * p := Nat.mul_le_mul_right p hc3
      _ = p * p * Nat.card (B₁ ⊓ B₂ : Subgroup G) := by ring
  have h6 : Nat.card (B₁ ⊓ B₂ : Subgroup G) ≤ p * p := hc2.trans (Nat.mul_le_mul_left p hc1)
  have h7 : Nat.card Bs ≤ p ^ 4 := by
    calc Nat.card Bs ≤ p * p * Nat.card (B₁ ⊓ B₂ : Subgroup G) := h5
      _ ≤ p * p * (p * p) := Nat.mul_le_mul_left _ h6
      _ = p ^ 4 := by ring
  have hBeq : B = Bs := Subgroup.eq_of_le_of_card_ge hBBs (h7.trans hB4)
  have he : B ⊓ (B₁ ⊓ B₂) = B₁ ⊓ B₂ := by
    rw [hBeq]
    exact inf_eq_right.mpr (inf_le_left.trans inf_le_left)
  rw [he] at hc1
  have h8 : Nat.card Bs ≤ p * p * p := h5.trans (Nat.mul_le_mul_left _ hc1)
  have h9 : p * p * p < p ^ 4 := by
    have h10 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    calc p * p * p = p ^ 3 := by ring
      _ < p ^ 4 := h10
  omega

theorem ggL44iiiNbrInput_of_pumpup (hPU : GGPumpupInput) (hJp : GGStdSubPrimeInput)
    (hI2 : GGStdSubBstarMeetInput) : GGL44iiiNbrInput := by
  intro G _ _ p B Bs x L D J X B₂ hFC hM h43 h44 h44ii d hd hd1
  have hcfg := hFC.1
  have hI := hcfg.1
  have hDJ := hcfg.2.2
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have : Fact p.Prime := ⟨hp⟩
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hxp : x ^ p = 1 := hS.1.1.2 x hS.2.1
  have hpJ : p ∣ Nat.card J := hJp G p B x L D J hI hDJ
  have hdx : d ∉ Subgroup.zpowers x := fun h =>
    h43.1 (Subgroup.zpowers_le.mpr hd.2 (mem_zpowers_of_mem_zpowers_of_ne_one hp hxp h hd1))
  have hD : D = Subgroup.closure {x, d} := eq_closure_pair_of_mem hI hDJ hd.1 hdx
  obtain ⟨hK, hJK, hxK, -⟩ := pumpup_of_stdSub hPU hI hDJ hpJ hD
  rcases ggNbr_or_eq_sup_of_stdSub hPU hI hDJ hpJ hD with h | h
  · exact ⟨d, _, h, rfl⟩
  · exact (false_of_eq_sup hFC hM h43 h44ii hpJ hJK hxK
      (le_normalizer_of_ggL44i hFC h44 hpJ (hI2 G p B Bs x L D J hcfg) hd.2.2 hK hJK) h).elim

end Config

@[expose] def GGStdSubCenterCyclicInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L D J : Subgroup G),
    GGThmIHyp p B x L → LargeEvenStdSub p B x L D J →
      ∀ S : Subgroup G, S ≤ J → S ≤ Subgroup.centralizer (J : Set G) → IsPGroup p S → IsCyclic S

theorem ggStdSubBstarMeetInput_of_small_cyclic (hs : GGStdSubSmallInput)
    (hcyc : GGStdSubCenterCyclicInput) : GGStdSubBstarMeetInput := by
  intro G _ _ p B Bs x L D J hcfg
  by_cases hsm : Nat.card (Bs ⊓ J : Subgroup G) < p ^ 3
  · exact (hs G p B Bs x L D J hcfg hsm).2
  · by_contra hcon
    have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
    have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
    have hC : Bs ⊓ J ≤ Subgroup.centralizer (J : Set G) := by
      intro b hb
      by_contra hbC
      exact hcon ⟨b, hb, hbC⟩
    have hpow : ∀ g : ↥(Bs ⊓ J), g ^ p = 1 := fun g => Subtype.ext (hBs.2 g g.2.1)
    have hpg : IsPGroup p (Bs ⊓ J : Subgroup G) := fun g => ⟨1, by rw [pow_one]; exact hpow g⟩
    have hcy : IsCyclic ↥(Bs ⊓ J) :=
      hcyc G p B x L D J hcfg.1 hcfg.2.2 (Bs ⊓ J) inf_le_right hC hpg
    have hdvd : Nat.card ↥(Bs ⊓ J) ∣ p := by
      rw [← IsCyclic.exponent_eq_card]
      exact Monoid.exponent_dvd_of_forall_pow_eq_one hpow
    have hle : Nat.card ↥(Bs ⊓ J) ≤ p := Nat.le_of_dvd hp.pos hdvd
    have hlt : p < p ^ 3 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega

theorem ggStdSubBstarMeetInput_of_small_centralizer (hs : GGStdSubSmallInput)
    (h1 : GGStdSubBstarCentralizerInput) : GGStdSubBstarMeetInput := by
  intro G _ _ p B Bs x L D J hcfg
  by_cases hsm : Nat.card (Bs ⊓ J : Subgroup G) < p ^ 3
  · exact (hs G p B Bs x L D J hcfg hsm).2
  · by_contra hcon
    have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
    have hle : Bs ⊓ J ≤ D := fun b hb => h1 G p B Bs x L D J hcfg
      ⟨hb.1, by
        by_contra hbC
        exact hcon ⟨b, hb, hbC⟩⟩
    have hcard := Subgroup.card_le_of_le hle
    rw [hcfg.2.2.1.2.2.1] at hcard
    have hlt : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega

theorem ggL44iiiNbrInput_of_small_cyclic (hPU : GGPumpupInput) (hJp : GGStdSubPrimeInput)
    (hs : GGStdSubSmallInput) (hcyc : GGStdSubCenterCyclicInput) : GGL44iiiNbrInput :=
  ggL44iiiNbrInput_of_pumpup hPU hJp (ggStdSubBstarMeetInput_of_small_cyclic hs hcyc)

theorem ggL44iiiNbrInput_of_center (hPU : GGPumpupInput) (ha₀ : GGLNoncyclicInput)
    (hJp : GGStdSubPrimeInput) (hcen : GGStdSubCenterMeetInput) : GGL44iiiNbrInput :=
  ggL44iiiNbrInput_of_pumpup hPU hJp (ggStdSubBstarMeetInput_of_center ha₀ hJp hcen)

end CFSG.StandardType

end
