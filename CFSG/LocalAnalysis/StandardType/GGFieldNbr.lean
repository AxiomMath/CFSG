module

public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Core

open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem map_conj_eq_or_le_centralizer {d : G} {K : Subgroup G}
    (hK : IsComponentOf K (Subgroup.centralizer ({d} : Set G))) {g : G}
    (hgd : g ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G)) :
    K.map (MulAut.conj g).toMonoidHom = K ∨
      K.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (K : Set G) := by
  have hzd : Subgroup.zpowers (g * d * g⁻¹) = Subgroup.zpowers d := by
    have h1 : Subgroup.zpowers (g * d * g⁻¹) =
        (Subgroup.zpowers d).map (MulAut.conj g).toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      simp
    rw [h1]
    exact map_conj_eq_of_mem_normalizer hgd
  have hCd : (Subgroup.centralizer ({d} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({d} : Set G) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton]
    exact centralizer_singleton_eq_of_zpowers_eq hzd
  have hK' := CFSG.LocalAnalysis.ComponentInitial.isComponentOf_map_conj hK g
  rw [hCd] at hK'
  rcases CFSG.LocalAnalysis.ComponentInitial.isComponentOf_eq_or_commute hK' hK with h | h
  · exact Or.inl h
  · exact Or.inr (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h)

theorem normalizer_inf_le_of_inf_centralizer_le {d : G} {K B₁ : Subgroup G}
    (hK : IsComponentOf K (Subgroup.centralizer ({d} : Set G)))
    (hC : B₁ ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers d)
    {b : G} (hbB : b ∈ B₁) (hbK : b ∈ K) (hbd : b ∉ Subgroup.zpowers d) :
    Subgroup.normalizer (B₁ : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
  rintro g ⟨hgB, hgd⟩
  rcases map_conj_eq_or_le_centralizer hK hgd with h | hle
  · exact mem_normalizer_iff_map_conj.mpr h
  · exfalso
    apply hbd
    have hgb : g * b * g⁻¹ ∈ Subgroup.zpowers d :=
      hC ⟨(Subgroup.mem_normalizer_iff.mp hgB b).mp hbB, hle ⟨b, hbK, rfl⟩⟩
    exact (Subgroup.mem_normalizer_iff.mp hgd b).mpr hgb

theorem normalizer_inf_le_of_card_lt {d : G} {K B₁ : Subgroup G}
    (hK : IsComponentOf K (Subgroup.centralizer ({d} : Set G)))
    (hcard : Nat.card (B₁ ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) <
      Nat.card (B₁ ⊓ K : Subgroup G)) :
    Subgroup.normalizer (B₁ : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers d : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
  rintro g ⟨hgB, hgd⟩
  rcases map_conj_eq_or_le_centralizer hK hgd with h | hle
  · exact mem_normalizer_iff_map_conj.mpr h
  · exfalso
    have hmap : (B₁ ⊓ K).map (MulAut.conj g).toMonoidHom ≤
        B₁ ⊓ Subgroup.centralizer (K : Set G) := by
      rintro _ ⟨b, ⟨hbB, hbK⟩, rfl⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hgB b).mp hbB, hle ⟨b, hbK, rfl⟩⟩
    have h1 := Subgroup.card_le_of_le hmap
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective] at h1
    exact absurd hcard (not_lt.mpr h1)

theorem mem_zpowers_of_mem_zpowers_of_ne_one {p : ℕ} (hp : p.Prime) {x a : G} (hxp : x ^ p = 1)
    (ha : a ∈ Subgroup.zpowers x) (ha1 : a ≠ 1) : x ∈ Subgroup.zpowers a := by
  have := Fact.mk hp
  have hx1 : x ≠ 1 := by
    rintro rfl
    exact ha1 (by simpa using ha)
  have hox : orderOf x = p := orderOf_eq_prime hxp hx1
  have hoa : orderOf a = p := by
    have hdvd : orderOf a ∣ p := hox ▸ orderOf_dvd_of_mem_zpowers ha
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) ha1
    · exact h1
  have heq : Subgroup.zpowers a = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ha)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hox, hoa])
  exact heq ▸ Subgroup.mem_zpowers x

theorem mem_zpowers_of_mem_closure_pair {p : ℕ} (hp : p.Prime) {x y c : G} {C : Subgroup G}
    (hxp : x ^ p = 1) (hxy : x * y = y * x) (hyC : y ∈ C) (hxC : x ∉ C)
    (hc : c ∈ Subgroup.closure ({x, y} : Set G)) (hcC : c ∈ C) : c ∈ Subgroup.zpowers y := by
  have := Fact.mk hp
  have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.zpow_left hxy k).symm).eq.symm
  rw [closure_pair_eq_sup] at hc
  have hc' : c ∈ (Subgroup.zpowers x : Set G) * (Subgroup.zpowers y : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hyN]
    exact hc
  obtain ⟨a, ha, e, he, rfl⟩ := hc'
  have heC : e ∈ C := Subgroup.zpowers_le.mpr hyC he
  have haC : a ∈ C := by
    have := C.mul_mem hcC (C.inv_mem heC)
    rwa [mul_inv_cancel_right] at this
  have ha1 : a = 1 := by
    by_contra ha1
    exact hxC (Subgroup.zpowers_le.mpr haC (mem_zpowers_of_mem_zpowers_of_ne_one hp hxp ha ha1))
  simpa [ha1] using he

end Core

@[expose] def GGStdSubBstarCentralizerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D

@[expose] def GGStdSubBstarMeetInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → ∃ b ∈ Bs ⊓ J, b ∉ Subgroup.centralizer (J : Set G)

@[expose] def GGNbrSubcomponentInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B : Subgroup G) (x : G) (L D J : Subgroup G),
    GGThmIHyp p B x L → LargeEvenStdSub p B x L D J →
      ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → J ≤ K

section InnerDef

variable {G : Type} [Group G] [Finite G]

@[expose] def GGFieldNbrInner (p : ℕ) (B Bs : Subgroup G) (x : G) (D J : Subgroup G) : Prop :=
  ∀ X : Subgroup G, X ≤ Subgroup.normalizer (Bs : Set G) →
    Subgroup.centralizer (Bs : Set G) ≤ X →
    (X.subgroupOf (Subgroup.normalizer (Bs : Set G))).Normal →
    (∀ g ∈ X, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) →
    ¬ X ≤ Subgroup.centralizer (Bs : Set G) →
    ∀ d ∈ D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)), d ≠ 1 →
    ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      Subgroup.zpowers y = Subgroup.zpowers d →
      Bs ⊓ K ≤ Bs ⊓ Subgroup.centralizer (X : Set G)

end InnerDef

@[expose] def GGFieldNbrInnerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → GGFieldNbrInner p B Bs x D J

section Reduction

variable {G : Type} [Group G] [Finite G]

theorem ggFieldNbrCanonical_of_inner {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (h1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D)
    (h2 : ∃ b ∈ Bs ⊓ J, b ∉ Subgroup.centralizer (J : Set G))
    (h3 : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → J ≤ K)
    (h4 : GGFieldNbrInner p B Bs x D J) : GGFieldNbrCanonical p B Bs x D J := by
  intro X hXN hCX hXn hXp hXC d hd hd1 y K hnbr hyd
  have hI := hcfg.1
  have hS : LargeEvenSStar p B x L := hI.2.2.2.2.2.2.1
  have hst : LargeEvenStandardType p B x L := hI.2.2.2.2.2.2.2
  have hDJ : LargeEvenStdSub p B x L D J := hcfg.2.2
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  obtain ⟨hKc, -⟩ := isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hDJ hnbr)
  rw [centralizer_singleton_eq_of_zpowers_eq hyd] at hKc
  have hJK : J ≤ K := h3 y K hnbr
  have hCKJ : Subgroup.centralizer (K : Set G) ≤ Subgroup.centralizer (J : Set G) :=
    Subgroup.centralizer_le hJK
  have hyK : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hnbr.1.2.2.2.1 hk)
  have hxK : x ∉ Subgroup.centralizer (K : Set G) := by
    intro hx
    apply hnbr.2.2.2
    have hz : Subgroup.zpowers x ≤ Subgroup.centralizer (K : Set G) :=
      Subgroup.zpowers_le.mpr hx
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hz)]
    exact bot_le
  have hxB : x ∈ B := hS.2.1
  have hyB : y ∈ B := hnbr.1.2.1
  have hxp : x ^ p = 1 := hS.1.1.2 x hxB
  have hxy : x * y = y * x :=
    congrArg Subtype.val (hS.1.1.1.is_comm.comm (⟨x, hxB⟩ : ↥B) ⟨y, hyB⟩)
  have hF1 : (Bs ⊓ Subgroup.centralizer (X : Set G)) ⊓ Subgroup.centralizer (K : Set G) ≤
      Subgroup.zpowers d := by
    rw [← hyd]
    rintro c ⟨⟨hcBs, -⟩, hcK⟩
    have hcD : c ∈ D := h1 ⟨hcBs, hCKJ hcK⟩
    rw [hnbr.2.1] at hcD
    exact mem_zpowers_of_mem_closure_pair hp hxp hxy hyK hxK hcD hcK
  obtain ⟨b, ⟨hbBs, hbJ⟩, hbC⟩ := h2
  have hbB₁ := h4 X hXN hCX hXn hXp hXC d hd hd1 y K hnbr hyd ⟨hbBs, hJK hbJ⟩
  have hbd : b ∉ Subgroup.zpowers d := by
    rw [← hyd]
    intro hb
    exact hbC (hCKJ (Subgroup.zpowers_le.mpr hyK hb))
  exact normalizer_inf_le_of_inf_centralizer_le hKc hF1 hbB₁ (hJK hbJ) hbd

theorem ggFieldNbrCanonicalInput_of_inputs (h1 : GGStdSubBstarCentralizerInput)
    (h2 : GGStdSubBstarMeetInput) (h3 : GGNbrSubcomponentInput) (h4 : GGFieldNbrInnerInput) :
    GGFieldNbrCanonicalInput := fun G _ _ p B Bs x L D J hcfg =>
  ggFieldNbrCanonical_of_inner hcfg (h1 G p B Bs x L D J hcfg) (h2 G p B Bs x L D J hcfg)
    (h3 G p B x L D J hcfg.1 hcfg.2.2) (h4 G p B Bs x L D J hcfg)

theorem card_le_mul_card_inf {p : ℕ} {H B S : Subgroup G} (hHS : H ≤ S) (hBS : B ≤ S)
    (hS : Nat.card S ≤ p * Nat.card B) : Nat.card H ≤ p * Nat.card (B ⊓ H : Subgroup G) := by
  have h1 : Nat.card (B ⊓ H : Subgroup G) * B.relIndex H = Nat.card H := by
    have h := Subgroup.card_mul_index (B.subgroupOf H)
    rwa [← Subgroup.card_map_of_injective H.subtype_injective,
      Subgroup.subgroupOf_map_subtype] at h
  have h2 : B.relIndex H ≤ B.relIndex S :=
    Subgroup.relIndex_le_of_le_right hHS (Subgroup.index_ne_zero_of_finite (H := B.subgroupOf S))
  have h3 : Nat.card B * B.relIndex S = Nat.card S := by
    have h := Subgroup.card_mul_index (B.subgroupOf S)
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBS).toEquiv] at h
  have hB : 0 < Nat.card B := Nat.card_pos
  have h4 : B.relIndex S ≤ p := by
    have h5 : Nat.card B * B.relIndex S ≤ Nat.card B * p := by
      rw [h3, mul_comm]
      exact hS
    exact Nat.le_of_mul_le_mul_left h5 hB
  calc Nat.card H = Nat.card (B ⊓ H : Subgroup G) * B.relIndex H := h1.symm
    _ ≤ Nat.card (B ⊓ H : Subgroup G) * p := Nat.mul_le_mul_left _ (h2.trans h4)
    _ = p * Nat.card (B ⊓ H : Subgroup G) := mul_comm _ _

theorem card_bstar_inf_centralizer_le {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K) :
    Nat.card (Bs ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) ≤ p ^ 2 := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have := Fact.mk hp
  have hBBs : B ≤ Bs := hcfg.2.1.1
  have h1 := card_le_mul_card_inf (inf_le_left : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Bs)
    hBBs hcfg.2.1.2.2.1
  have h2 : B ⊓ (Bs ⊓ Subgroup.centralizer (K : Set G)) = Subgroup.zpowers y := by
    rw [← inf_assoc, inf_eq_left.mpr hBBs]
    exact inf_centralizer_eq_zpowers_of_sHat hnbr.1
  have hy : orderOf y = p := orderOf_eq_prime (hnbr.1.1.1.2 y hnbr.1.2.1) hnbr.1.2.2.1
  rw [h2, Nat.card_zpowers, hy] at h1
  rw [sq]
  exact h1

theorem ggFieldNbrCanonical_of_card {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hR : p ^ 3 ≤ Nat.card (Bs ⊓ J : Subgroup G))
    (h3 : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → J ≤ K)
    (h4 : GGFieldNbrInner p B Bs x D J) : GGFieldNbrCanonical p B Bs x D J := by
  intro X hXN hCX hXn hXp hXC d hd hd1 y K hnbr hyd
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hKc, -⟩ := isComponentOf_of_isNeighborOf hcfg.1.2.2.2.2.2.2.2
    (isNeighborOf_of_ggNbr hcfg.2.2 hnbr)
  rw [centralizer_singleton_eq_of_zpowers_eq hyd] at hKc
  have hJK : J ≤ K := h3 y K hnbr
  have hle : Bs ⊓ J ≤ (Bs ⊓ Subgroup.centralizer (X : Set G)) ⊓ K := fun b hb =>
    ⟨h4 X hXN hCX hXn hXp hXC d hd hd1 y K hnbr hyd ⟨hb.1, hJK hb.2⟩, hJK hb.2⟩
  have hC : Nat.card ((Bs ⊓ Subgroup.centralizer (X : Set G)) ⊓
      Subgroup.centralizer (K : Set G) : Subgroup G) ≤ p ^ 2 :=
    (Subgroup.card_le_of_le (inf_le_inf_right _ inf_le_left)).trans
      (card_bstar_inf_centralizer_le hcfg hnbr)
  refine normalizer_inf_le_of_card_lt hKc ?_
  calc Nat.card ((Bs ⊓ Subgroup.centralizer (X : Set G)) ⊓
        Subgroup.centralizer (K : Set G) : Subgroup G) ≤ p ^ 2 := hC
    _ < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    _ ≤ Nat.card (Bs ⊓ J : Subgroup G) := hR
    _ ≤ Nat.card ((Bs ⊓ Subgroup.centralizer (X : Set G)) ⊓ K : Subgroup G) :=
      Subgroup.card_le_of_le hle

theorem ggFieldNbrCanonical_of_small {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (h3 : ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K → J ≤ K)
    (h4 : GGFieldNbrInner p B Bs x D J)
    (hsmall : Nat.card (Bs ⊓ J : Subgroup G) < p ^ 3 →
      Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D ∧
        ∃ b ∈ Bs ⊓ J, b ∉ Subgroup.centralizer (J : Set G)) :
    GGFieldNbrCanonical p B Bs x D J := by
  by_cases hR : p ^ 3 ≤ Nat.card (Bs ⊓ J : Subgroup G)
  · exact ggFieldNbrCanonical_of_card hcfg hR h3 h4
  · obtain ⟨h1, h2⟩ := hsmall (not_le.mp hR)
    exact ggFieldNbrCanonical_of_inner hcfg h1 h2 h3 h4

end Reduction

@[expose] def GGStdSubSmallInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig p B Bs x L D J → Nat.card (Bs ⊓ J : Subgroup G) < p ^ 3 →
      Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D ∧
        ∃ b ∈ Bs ⊓ J, b ∉ Subgroup.centralizer (J : Set G)

theorem ggFieldNbrCanonicalInput_of_small (h3 : GGNbrSubcomponentInput)
    (h4 : GGFieldNbrInnerInput) (hs : GGStdSubSmallInput) : GGFieldNbrCanonicalInput :=
  fun G _ _ p B Bs x L D J hcfg =>
    ggFieldNbrCanonical_of_small hcfg (h3 G p B x L D J hcfg.1 hcfg.2.2)
      (h4 G p B Bs x L D J hcfg) (hs G p B Bs x L D J hcfg)

theorem ggStdSubSmallInput_of_inputs (h1 : GGStdSubBstarCentralizerInput)
    (h2 : GGStdSubBstarMeetInput) : GGStdSubSmallInput :=
  fun G _ _ p B Bs x L D J hcfg _ => ⟨h1 G p B Bs x L D J hcfg, h2 G p B Bs x L D J hcfg⟩

section Split

variable {G : Type} [Group G] [Finite G]

@[expose] def GGFieldNbrSplit (p : ℕ) (Bs : Subgroup G) (x : G) : Prop :=
  ∀ X : Subgroup G, X ≤ Subgroup.normalizer (Bs : Set G) →
    Subgroup.centralizer (Bs : Set G) ≤ X →
    (X.subgroupOf (Subgroup.normalizer (Bs : Set G))).Normal →
    (∀ g ∈ X, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) →
    ¬ X ≤ Subgroup.centralizer (Bs : Set G) →
    Bs ≤ (Bs ⊓ Subgroup.centralizer (X : Set G)) ⊔ Subgroup.zpowers x

@[expose] def GGFieldNbrFieldAut (p : ℕ) (B Bs : Subgroup G) (x : G) (D J : Subgroup G) : Prop :=
  ∀ X : Subgroup G, X ≤ Subgroup.normalizer (Bs : Set G) →
    Subgroup.centralizer (Bs : Set G) ≤ X →
    (X.subgroupOf (Subgroup.normalizer (Bs : Set G))).Normal →
    (∀ g ∈ X, ∃ k : ℕ, g ^ p ^ k ∈ Subgroup.centralizer (Bs : Set G)) →
    ¬ X ≤ Subgroup.centralizer (Bs : Set G) →
    ∀ d ∈ D ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)), d ≠ 1 →
    ∀ (y : G) (K : Subgroup G), GGNbr p B x D J y K →
      Subgroup.zpowers y = Subgroup.zpowers d →
      x ∉ (Bs ⊓ Subgroup.centralizer (X : Set G)) ⊔ K

open scoped Pointwise in
theorem ggFieldNbrInner_of_split {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hsplit : GGFieldNbrSplit p Bs x)
    (hfield : GGFieldNbrFieldAut p B Bs x D J) : GGFieldNbrInner p B Bs x D J := by
  intro X hXN hCX hXn hXp hXC d hd hd1 y K hnbr hyd b hb
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hS.2.1
  have hxp : x ^ p = 1 := hS.1.1.2 x hS.2.1
  set B₁ := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  have hxN : Subgroup.zpowers x ≤ Subgroup.normalizer (B₁ : Set G) := by
    rw [Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro c hc
    exact congrArg Subtype.val
      (hcfg.2.1.2.1.1.is_comm.comm (⟨c, hc.1⟩ : ↥Bs) ⟨x, hxBs⟩)
  have hb' : b ∈ (B₁ : Set G) * (Subgroup.zpowers x : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hxN]
    exact hsplit X hXN hCX hXn hXp hXC hb.1
  obtain ⟨b₁, hb₁, e, he, hbe⟩ := hb'
  have heBK : e ∈ B₁ ⊔ K := by
    have h1 : b₁⁻¹ ∈ B₁ ⊔ K := Subgroup.mem_sup_left (B₁.inv_mem hb₁)
    have h2 : b ∈ B₁ ⊔ K := Subgroup.mem_sup_right hb.2
    have := (B₁ ⊔ K).mul_mem h1 h2
    rwa [← hbe, ← mul_assoc, inv_mul_cancel, one_mul] at this
  have he1 : e = 1 := by
    by_contra he1
    exact hfield X hXN hCX hXn hXp hXC d hd hd1 y K hnbr hyd
      (Subgroup.zpowers_le.mpr heBK (mem_zpowers_of_mem_zpowers_of_ne_one hp hxp he he1))
  rw [← hbe, he1]
  simpa using hb₁

theorem ggFieldNbrInnerInput_of_split
    (hsplit : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G), GGConfig p B Bs x L D J → GGFieldNbrSplit p Bs x)
    (hfield : ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
      (L D J : Subgroup G), GGConfig p B Bs x L D J → GGFieldNbrFieldAut p B Bs x D J) :
    GGFieldNbrInnerInput := fun G _ _ p B Bs x L D J hcfg =>
  ggFieldNbrInner_of_split hcfg (hsplit G p B Bs x L D J hcfg) (hfield G p B Bs x L D J hcfg)

end Split

end CFSG.StandardType

end
