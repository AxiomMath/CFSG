module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RankXTriality
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45RestRank

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

@[expose] def GGL45D4BoneRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGL45Config p B Bs x L D J X B₂ d y K U U₁ → p = 3 →
    LargeEvenMarking K (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 4) →
      27 * Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (K : Set G) :
          Subgroup G) ≤ Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)

@[expose] def GGL45D4BstarProperInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G)
    (L D J X B₂ : Subgroup G) (d y : G) (K U U₁ : Subgroup G),
    GGL45Config p B Bs x L D J X B₂ d y K U U₁ → p = 3 →
    LargeEvenMarking K (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 4) →
    LargeEvenTwoLocalRank 3 G = 4 → B ≠ Bs

section Rank

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem GGL45Config.pow_five_le_card_bstar (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (h : LargeEvenTwoLocalRank p G = 4 → B ≠ Bs) : p ^ 5 ≤ Nat.card Bs := by
  have hp : p.Prime := hcfg.prime
  have : Fact p.Prime := ⟨hp⟩
  have hI := hcfg.1.1.1
  have hB : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hI.2.2.2.2.2.2.1.1.2.1
  have hm4 : 4 ≤ LargeEvenTwoLocalRank p G := hI.2.2.2.2.2.1.2.2.2
  have hBBs : B ≤ Bs := hcfg.1.1.2.1.1
  have hle : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hBBs
  rcases Nat.lt_or_ge 4 (LargeEvenTwoLocalRank p G) with h5 | h4
  · calc p ^ 5 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos h5
      _ = Nat.card B := hB.symm
      _ ≤ Nat.card Bs := hle
  · have hm : LargeEvenTwoLocalRank p G = 4 := le_antisymm h4 hm4
    have hne := h hm
    have hlt : Nat.card B < Nat.card Bs := by
      refine lt_of_le_of_ne hle fun heq => hne ?_
      exact Subgroup.eq_of_le_of_card_ge hBBs heq.ge
    have hpg : IsPGroup p Bs := fun g => ⟨1, by
      rw [pow_one]; exact Subtype.ext (hcfg.isElemAbelian.2 g g.2)⟩
    obtain ⟨n, hn⟩ := hpg.exists_card_eq
    rw [hB, hm, hn] at hlt
    rw [hn]
    exact Nat.pow_le_pow_right hp.pos ((Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt)

theorem GGL45Config.card_bone_ge (hcfg : GGL45Config 3 B Bs x L D J X B₂ d y K U U₁)
    (hcent : Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (K : Set G) ≤
      Subgroup.zpowers d) (h5 : 3 ^ 5 ≤ Nat.card Bs) :
    27 * Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) ⊓ Subgroup.centralizer (K : Set G) :
        Subgroup G) ≤ Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h43 : GGL43 Bs x X := hcfg.2.2.1
  have hx1 : x ≠ 1 := fun h => h43.1 (h ▸ one_mem _)
  have hle := card_bstar_le_of_ggL43 hcfg.isElemAbelian hcfg.x_mem hx1 h43
  have hd : Nat.card (Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hcfg.d_pow hcfg.d_ne]
  have hC := Subgroup.card_le_of_le hcent
  rw [hd] at hC
  omega

end Rank

namespace L45RankX

theorem conj_injective_of_simple {R : Type*} [Group R] (hs : IsSimpleGroup R)
    (hna : ∃ a b : R, a * b ≠ b * a) : Function.Injective (MulAut.conj : R →* MulAut R) := by
  refine mulAut_conj_injective ?_
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center R := by rw [h]; exact Subgroup.mem_top a
    exact absurd (Subgroup.mem_center_iff.mp ha b).symm hab

theorem exists_fixed_of_range_le_inn {R A : Type*} [Group R] [Group A]
    (hinj : Function.Injective (MulAut.conj : R →* MulAut R))
    (hA : ∀ a b : A, a * b = b * a) (hA3 : ∀ a : A, a ^ 3 = 1) (β : A →* MulAut R)
    (hβ : β.range ≤ (MulAut.conj : R →* MulAut R).range) :
    ∃ E : Subgroup R, IsElemAbelian 3 E ∧ Nat.card E = Nat.card β.range ∧
      ∀ φ : MulAut R, (∀ a : A, φ * β a = β a * φ) → ∀ e ∈ E, φ e = e := by
  refine ⟨β.range.comap MulAut.conj, ⟨⟨⟨fun a b => ?_⟩⟩, fun e he => ?_⟩, ?_, ?_⟩
  · obtain ⟨a', ha'⟩ := a.2
    obtain ⟨b', hb'⟩ := b.2
    apply Subtype.ext
    apply hinj
    change MulAut.conj ((a : R) * b) = MulAut.conj ((b : R) * a)
    rw [map_mul, map_mul, ← ha', ← hb', ← map_mul, ← map_mul, hA]
  · obtain ⟨a', ha'⟩ := he
    apply hinj
    rw [map_pow, ← ha', ← map_pow, hA3, map_one, map_one]
  · rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq_self hβ]
  · intro φ hφ e he
    obtain ⟨a, ha⟩ := he
    apply hinj
    have h1 : φ * MulAut.conj e = MulAut.conj (φ e) * φ := D4Rank.mulAut_mul_conj φ e
    have h2 : φ * MulAut.conj e = MulAut.conj e * φ := by rw [← ha]; exact hφ a
    exact mul_right_cancel (h1.symm.trans h2)

end L45RankX

section Cyclic

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem GGL45Config.exists_cyclic_d4 (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcfg : GGL45Config 3 B Bs x L D J X B₂ d y K U U₁)
    (h27 : 27 * Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) ⊓
        Subgroup.centralizer (K : Set G) : Subgroup G) ≤
      Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G))
    (hmk : LargeEvenMarking K (fun lab _ _ I _ θ => lab.tag = .D ∧ lab.rank = 4 ∧
      ∀ u ∈ U, u ∈ U₁ ↔ ∃ φ ∈ I, LargeEvenInduces θ (fun k k' => (k' : G) = u⁻¹ * k * u) φ)) :
    ∃ g ∈ U, U ≤ Subgroup.zpowers g ⊔ U₁ := by
  obtain ⟨hB₁U₁, -, -⟩ := ggL4546_basic hraw hiso hcfg
  have hUp : IsPGroup 3 U := hcfg.isPGroup
  have hUN := hcfg.le_normalizer
  have hUC := hcfg.le_centralizer
  obtain ⟨hperf, lab, hlab, hraw1⟩ := hmk
  obtain ⟨R₀, _, I₀, F₀, -, -, θ₀, ht, h4, -⟩ := largeEvenRawDatum_exists hraw1
  obtain ⟨R, _, I, F, ⟨hs, hna, θ, -, -, hθ⟩, hcyc⟩ :=
    largeEvenRawDatum_exists (largeEvenLabelAll_d4ThreeFixCyclic ht h4 _ hraw1)
  obtain ⟨hI, S, hInnS, hgen, hfixS⟩ := hcyc hs hna
  subst hI
  set J : Subgroup (MulAut R) := (MulAut.conj : R →* MulAut R).range with hJ
  have hinj := L45RankX.conj_injective_of_simple hs hna
  let ρ : U →* MulAut R := (ggLAut K θ).comp (Subgroup.inclusion hUN)
  have hρ : ∀ u : U, ρ u = ggLAut K θ ⟨u, hUN u.2⟩ := fun _ => rfl
  have hmem : ∀ u : U, (u : G) ∈ U₁ ↔ ρ u ∈ J := fun u => by
    rw [hθ u u.2, hρ]
    constructor
    · rintro ⟨φ, hφ, hind⟩
      rw [eq_ggLAut_of_induces K θ (hUN u.2) hind] at hφ
      have hφ' : ggLAut K θ ⟨(u : G)⁻¹, inv_mem (hUN u.2)⟩ ∈ J := hφ
      have := J.inv_mem hφ'
      rw [← map_inv] at this
      convert this using 2
      exact Subtype.ext (by simp)
    · intro hm
      refine ⟨ggLAut K θ ⟨(u : G)⁻¹, inv_mem (hUN u.2)⟩, ?_,
        largeEvenInduces_ggLAut_inv K θ (inv_mem (hUN u.2))⟩
      show ggLAut K θ ⟨(u : G)⁻¹, inv_mem (hUN u.2)⟩ ∈ J
      have := J.inv_mem hm
      rw [← map_inv] at this
      convert this using 2
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  have hB₁U : B₁ ≤ U := fun b hb => hcfg.bs_le hb.1
  let β : B₁ →* MulAut R := ρ.comp (Subgroup.inclusion hB₁U)
  have hβJ : β.range ≤ J := by
    rintro _ ⟨b, rfl⟩
    exact (hmem _).1 (hB₁U₁ b.2)
  have hcommB : ∀ a b : B₁, a * b = b * a := fun a b =>
    Subtype.ext (mul_comm_of_isElemAbelian hcfg.isElemAbelian a.2.1 b.2.1)
  have hB₁3 : ∀ a : B₁, a ^ 3 = 1 := fun a => Subtype.ext (hcfg.isElemAbelian.2 a a.2.1)
  obtain ⟨E, hE, hEcard, hEfix⟩ :=
    L45RankX.exists_fixed_of_range_le_inn hinj hcommB hB₁3 β hβJ
  have hker : Nat.card β.ker ≤ Nat.card (B₁ ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) := by
    have hle : β.ker.map B₁.subtype ≤ B₁ ⊓ Subgroup.centralizer (K : Set G) := by
      rintro _ ⟨b, hb, rfl⟩
      refine ⟨b.2, ?_⟩
      have hb' : ggLAut K θ ⟨b, hUN (hB₁U b.2)⟩ = 1 := hb
      exact mem_centralizer_of_ggLAut_eq_one K θ hperf hb'
    calc Nat.card β.ker = Nat.card (β.ker.map B₁.subtype) :=
          (Subgroup.card_map_of_injective B₁.subtype_injective).symm
      _ ≤ _ := Subgroup.card_le_of_le hle
  have hcard := Subgroup.card_ker_mul_card_range β
  have hpos : 0 < Nat.card (B₁ ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) := Nat.card_pos
  have hE27 : 27 ≤ Nat.card E := by
    rw [hEcard]
    by_contra hlt
    push Not at hlt
    have h1 : Nat.card B₁ ≤ Nat.card (B₁ ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) *
        Nat.card β.range := by
      rw [← hcard]
      exact Nat.mul_le_mul_right _ hker
    have h2 : Nat.card (B₁ ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) *
        Nat.card β.range < Nat.card (B₁ ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) * 27 :=
      Nat.mul_lt_mul_of_pos_left hlt hpos
    omega
  have hρS : ∀ u : U, ρ u ∈ S := fun u => by
    obtain ⟨k, hk⟩ := hUp u
    refine hfixS (ρ u) ⟨k, by rw [← map_pow, hk, map_one]⟩ E hE (by omega)
      (hEfix (ρ u) fun b => ?_)
    show ρ u * ρ (Subgroup.inclusion hB₁U b) = ρ (Subgroup.inclusion hB₁U b) * ρ u
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext
      (Subgroup.mem_centralizer_iff.mp (hUC u.2) (b : G) b.2).symm
  exact exists_le_zpowers_sup_of_cyclic ρ ((ggInnNormal R).subgroupOf S) hgen hρS hmem

end Cyclic

theorem ggL45CyclicD4Input_of_boneRank (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hR : GGL45D4BoneRankInput) : GGL45CyclicD4Input := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hcfg hp3 hmk
  subst hp3
  refine hcfg.exists_cyclic_d4 hraw hiso
    (hR G 3 B Bs x L D J X B₂ d y K U U₁ hcfg rfl
      (largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨h.1, h.2.1⟩) hmk)) hmk

theorem ggL45D4BoneRankInput_of_proper (hcent : GGL45CentInput) (hR : GGL45D4BstarProperInput) :
    GGL45D4BoneRankInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hcfg hp3 hmk
  subst hp3
  exact hcfg.card_bone_ge (hcent G 3 B Bs x L D J X B₂ d y K U U₁ hcfg)
    (hcfg.pow_five_le_card_bstar (hR G 3 B Bs x L D J X B₂ d y K U U₁ hcfg rfl hmk))

theorem ggL45CyclicD4Input_of_proper (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hcent : GGL45CentInput) (hR : GGL45D4BstarProperInput) : GGL45CyclicD4Input :=
  ggL45CyclicD4Input_of_boneRank hraw hiso (ggL45D4BoneRankInput_of_proper hcent hR)

end CFSG.StandardType
