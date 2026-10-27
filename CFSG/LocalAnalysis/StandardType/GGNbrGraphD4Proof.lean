module

public import CFSG.LocalAnalysis.StandardType.GGNbrGraphD4ProofOut
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphField

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGNbrGraphD4SmallInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → LargeEvenTwoLocalRank 3 G ≤ 5 →
      ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K →
        ∀ hN : Bs ≤ Subgroup.normalizer (K : Set G),
          GGMarkingAll (K := ↥K) fun lab _ _ I F θ => lab.tag = .D → lab.rank = 4 →
            (LargeEvenTwoLocalRank 3 G = 5 → 3 ∣ lab.n) →
            ∀ (b : G) (hb : b ∈ Bs), ∃ u ∈ I, ∃ f ∈ Subgroup.closure F,
              ggLAut K θ ⟨b, hN hb⟩ = u * f

@[expose] def GGNbrD4BstarRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B Bs : Subgroup G) (x : G) (L D J : Subgroup G),
    GGConfig 3 B Bs x L D J → LargeEvenTwoLocalRank 3 G ≤ 5 →
      ∀ (y : G) (K : Subgroup G), GGNbr 3 B x D J y K → Bs ≤ Subgroup.normalizer (K : Set G) →
        LargeEvenMarking ↥K (fun lab _ _ _ _ _ => lab.tag = .D ∧ lab.rank = 4 ∧
          (LargeEvenTwoLocalRank 3 G = 5 → 3 ∣ lab.n)) →
          27 * Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ Nat.card ↥(Bs ⊓ K)

section Core

variable {G : Type} [Group G]

theorem isElemAbelian_range_of_comm {X Y : Type*} [Group X] [Group Y]
    (hcomm : ∀ a b : X, a * b = b * a) (hexp : ∀ a : X, a ^ 3 = 1) (f : X →* Y) :
    IsElemAbelian 3 f.range := by
  refine ⟨⟨⟨fun u v => ?_⟩⟩, ?_⟩
  · obtain ⟨_, ⟨a, rfl⟩⟩ := u
    obtain ⟨_, ⟨b, rfl⟩⟩ := v
    apply Subtype.ext
    change f a * f b = f b * f a
    rw [← map_mul, ← map_mul, hcomm a b]
  · rintro _ ⟨a, rfl⟩
    rw [← map_pow, hexp a, map_one]

noncomputable abbrev ggBstarAut {Bs K : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R) : ↥Bs →* MulAut R :=
  (ggLAut K θ).comp (Subgroup.inclusion hN)

theorem isElemAbelian_range_ggBstarAut {Bs K : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) : IsElemAbelian 3 (ggBstarAut hN θ).range :=
  isElemAbelian_range_of_comm (fun a b => hBs.1.is_comm.comm a b)
    (fun a => Subtype.ext (by simpa using hBs.2 a a.2)) _

theorem exists_inner_mul_field_of_card {Bs K : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {R : Type} [Group R] {I F : Set (MulAut R)}
    (hKG : GGD4TrialityAutRank I F) (θ : K ⧸ Subgroup.center K ≃* R)
    (h81 : 81 < Nat.card (ggBstarAut hN θ).range) {b : G} (hb : b ∈ Bs) :
    ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, ggLAut K θ ⟨b, hN hb⟩ = u * f := by
  by_contra hnot
  have h := hKG _ (isElemAbelian_range_ggBstarAut hBs hN θ) _ ⟨⟨b, hb⟩, rfl⟩ hnot
  omega

theorem exists_inner_mul_field_of_card27 {Bs K : Subgroup G} (hBs : IsElemAbelian 3 Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {R : Type} [Group R] {I F : Set (MulAut R)}
    (hKG : GGD4TrialityAutRankNF I F) (θ : K ⧸ Subgroup.center K ≃* R)
    (h27 : 27 < Nat.card (ggBstarAut hN θ).range) {b : G} (hb : b ∈ Bs) :
    ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, ggLAut K θ ⟨b, hN hb⟩ = u * f := by
  by_contra hnot
  have h := hKG _ (isElemAbelian_range_ggBstarAut hBs hN θ) _ ⟨⟨b, hb⟩, rfl⟩ hnot
  omega

theorem exists_inner_mul_field_of_bstarRank [Finite G] {Bs K : Subgroup G}
    (hBs : IsElemAbelian 3 Bs) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (h27 : 27 * Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) ≤ Nat.card ↥(Bs ⊓ K))
    {R : Type} [Group R] {I F : Set (MulAut R)} (hKG : GGD4TrialityCentBound I F)
    (θ : K ⧸ Subgroup.center K ≃* R) {b : G} (hb : b ∈ Bs) :
    ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, ggLAut K θ ⟨b, hN hb⟩ = u * f := by
  by_contra hnot
  have hcommB : ∀ a ∈ Bs, ∀ c ∈ Bs, a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (hBs.1.is_comm.comm ⟨a, ha⟩ ⟨c, hc⟩)
  set π : ↥(Bs ⊓ K) →* R := θ.toMonoidHom.comp ((QuotientGroup.mk' (Subgroup.center ↥K)).comp
    (Subgroup.inclusion (inf_le_right : Bs ⊓ K ≤ K))) with hπdef
  have hπ : ∀ k : ↥(Bs ⊓ K), π k = θ ((⟨k, k.2.2⟩ : ↥K) : ↥K ⧸ Subgroup.center ↥K) :=
    fun _ => rfl
  have hE : IsElemAbelian 3 π.range :=
    isElemAbelian_range_of_comm (fun a c => Subtype.ext (hcommB _ a.2.1 _ c.2.1))
      (fun a => Subtype.ext (by simpa using hBs.2 a a.2.1)) π
  have hfix : ∀ e ∈ π.range, ggLAut K θ ⟨b, hN hb⟩ e = e := by
    rintro _ ⟨k, rfl⟩
    have hk : K.normalizerMonoidHom ⟨b, hN hb⟩ ⟨k, k.2.2⟩ = ⟨k, k.2.2⟩ := by
      apply Subtype.ext
      rw [normalizerMonoidHom_coe]
      change b * (k : G) * b⁻¹ = k
      rw [hcommB b hb k k.2.1, mul_inv_cancel_right]
    rw [hπ, ggLAut_apply, hk]
  have hφ3 : ggLAut K θ ⟨b, hN hb⟩ ^ 3 = 1 := ggLAut_pow_eq_one K θ (hN hb) (hBs.2 b hb)
  have h9 := hKG _ hφ3 hnot π.range hE hfix
  have hker : Nat.card π.ker ≤ Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) := by
    have hle : π.ker.map (Bs ⊓ K).subtype ≤ Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G) := by
      rintro _ ⟨k, hk, rfl⟩
      refine ⟨k.2, ?_⟩
      have hk' : π k = 1 := hk
      rw [hπ] at hk'
      have h1 : ((⟨k, k.2.2⟩ : ↥K) : ↥K ⧸ Subgroup.center ↥K) = 1 :=
        θ.injective (hk'.trans (map_one θ).symm)
      have h2 := (QuotientGroup.eq_one_iff _).1 h1
      show (k : G) ∈ Subgroup.centralizer (K : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 h2 ⟨g, hg⟩)
    calc Nat.card π.ker = Nat.card (π.ker.map (Bs ⊓ K).subtype) :=
          (Subgroup.card_map_of_injective (Bs ⊓ K).subtype_injective).symm
      _ ≤ _ := Subgroup.card_le_of_le hle
  have hcard := Subgroup.card_ker_mul_card_range π
  have hpos : 0 < Nat.card π.ker := Nat.card_pos
  have : 27 * Nat.card π.ker ≤ Nat.card π.ker * 9 :=
    calc 27 * Nat.card π.ker ≤ 27 * Nat.card ↥(Bs ⊓ K ⊓ Subgroup.centralizer (K : Set G)) :=
          Nat.mul_le_mul_left _ hker
      _ ≤ Nat.card ↥(Bs ⊓ K) := h27
      _ = Nat.card π.ker * Nat.card π.range := hcard.symm
      _ ≤ Nat.card π.ker * 9 := Nat.mul_le_mul_left _ h9
  omega

end Core

section Config

variable {G : Type} [Group G] [Finite G]

theorem three_pow_le_card_range_ggBstarAut {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr 3 B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hperf : commutator K = ⊤) {R : Type} [Group R]
    (θ : K ⧸ Subgroup.center K ≃* R) :
    3 ^ LargeEvenTwoLocalRank 3 G ≤ 3 * Nat.card (ggBstarAut hN θ).range := by
  have := Fact.mk Nat.prime_three
  have hB : IsElemAbelian 3 B := hC.1.2.2.2.2.2.2.1.1.1
  have hBc : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hC.1.2.2.2.2.2.2.1.1.2.1
  have hBBs : B ≤ Bs := hC.2.1.1
  have hS : LargeEvenSHat 3 B y K := hK.1
  set α : ↥B →* MulAut R := (ggBstarAut hN θ).comp (Subgroup.inclusion hBBs) with hα
  have hker : α.ker ≤ (Subgroup.zpowers y).subgroupOf B := by
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    rw [Subgroup.mem_subgroupOf, ← inf_centralizer_eq_zpowers_of_sHat hS]
    exact ⟨b.2, mem_centralizer_of_ggLAut_eq_one K θ hperf (g := ⟨b, hN (hBBs b.2)⟩) hb⟩
  have hyB : y ∈ B := hS.2.1
  have hy : Nat.card ((Subgroup.zpowers y).subgroupOf B) = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.zpowers_le.mpr hyB)).toEquiv,
      Nat.card_zpowers, orderOf_eq_prime (hB.2 y hyB) hS.2.2.1]
  have hk : Nat.card α.ker ≤ 3 := hy ▸ Subgroup.card_le_of_le hker
  have h1 := Subgroup.card_ker_mul_card_range α
  have hle : α.range ≤ (ggBstarAut hN θ).range := by
    rintro _ ⟨b, rfl⟩
    exact ⟨_, rfl⟩
  have : Finite (ggBstarAut hN θ).range :=
    Finite.of_surjective _ (ggBstarAut hN θ).rangeRestrict_surjective
  have h2 := Subgroup.card_le_of_le hle
  rw [← hBc, ← h1]
  calc Nat.card α.ker * Nat.card α.range ≤ 3 * Nat.card α.range := Nat.mul_le_mul_right _ hk
    _ ≤ 3 * Nat.card (ggBstarAut hN θ).range := Nat.mul_le_mul_left _ h2

theorem exists_inner_mul_field_of_large {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr 3 B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hperf : commutator K = ⊤) {R : Type} [Group R]
    {I F : Set (MulAut R)} (hKG : GGD4TrialityAutRank I F) (θ : K ⧸ Subgroup.center K ≃* R)
    (hm : 5 < LargeEvenTwoLocalRank 3 G) {b : G} (hb : b ∈ Bs) :
    ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, ggLAut K θ ⟨b, hN hb⟩ = u * f := by
  refine exists_inner_mul_field_of_card hC.2.1.2.1 hN hKG θ ?_ hb
  have h := three_pow_le_card_range_ggBstarAut hC hK hN hperf θ
  have h6 : 729 ≤ 3 ^ LargeEvenTwoLocalRank 3 G :=
    calc (729 : ℕ) = 3 ^ 6 := by norm_num
      _ ≤ 3 ^ LargeEvenTwoLocalRank 3 G := Nat.pow_le_pow_right (by norm_num) hm
  omega

theorem exists_inner_mul_field_of_five {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hC : GGConfig 3 B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr 3 B x D J y K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hperf : commutator K = ⊤) {R : Type} [Group R]
    {I F : Set (MulAut R)} (hKG : GGD4TrialityAutRankNF I F) (θ : K ⧸ Subgroup.center K ≃* R)
    (hm : 4 < LargeEvenTwoLocalRank 3 G) {b : G} (hb : b ∈ Bs) :
    ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, ggLAut K θ ⟨b, hN hb⟩ = u * f := by
  refine exists_inner_mul_field_of_card27 hC.2.1.2.1 hN hKG θ ?_ hb
  have h := three_pow_le_card_range_ggBstarAut hC hK hN hperf θ
  have h5 : 243 ≤ 3 ^ LargeEvenTwoLocalRank 3 G :=
    calc (243 : ℕ) = 3 ^ 5 := by norm_num
      _ ≤ 3 ^ LargeEvenTwoLocalRank 3 G := Nat.pow_le_pow_right (by norm_num) hm
  omega

end Config

theorem ggNbrGraphD4Input_of_small (hS : GGNbrGraphD4SmallInput) : GGNbrGraphD4Input := by
  intro G _ _ p B Bs x L D J hC hp y K hK hN P hP
  subst hp
  rcases Nat.lt_or_ge 5 (LargeEvenTwoLocalRank 3 G) with hm | hm
  · obtain ⟨hperf, lab, hlab, hraw⟩ := hP
    by_cases hD : lab.tag = .D ∧ lab.rank = 4
    · have hraw' := largeEvenLabelAll_d4TrialityAutRank hD.1 hD.2 hlab.1 _ hraw
      refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw'⟩
      rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hKG⟩
      exact ⟨hs, hna, θ, hθ, fun _ _ b hb =>
        exists_inner_mul_field_of_large hC hK hN hperf hKG θ hm hb⟩
    · refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
      rintro R _ I F ⟨hs, hna, θ, hθ⟩
      exact ⟨hs, hna, θ, hθ, fun h1 h2 => absurd ⟨h1, h2⟩ hD⟩
  · obtain ⟨hperf, lab, hlab, hraw⟩ := hS G B Bs x L D J hC hm y K hK hN P hP
    by_cases hD : lab.tag = .D ∧ lab.rank = 4
    · have hraw' := largeEvenLabelAll_d4TrialityAutRankNF hD.1 hD.2 hlab.1 _ hraw
      refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw'⟩
      rintro R _ I F ⟨⟨hs, hna, θ, hθP, hθQ⟩, hNF⟩
      refine ⟨hs, hna, θ, hθP, fun h1 h2 b hb => ?_⟩
      by_cases h5 : LargeEvenTwoLocalRank 3 G = 5 → 3 ∣ lab.n
      · exact hθQ h1 h2 h5 b hb
      · push Not at h5
        exact exists_inner_mul_field_of_five hC hK hN hperf (hNF h5.2) θ (by omega) hb
    · refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
      rintro R _ I F ⟨hs, hna, θ, hθP, -⟩
      exact ⟨hs, hna, θ, hθP, fun h1 h2 => absurd ⟨h1, h2⟩ hD⟩

theorem ggNbrGraphD4SmallInput_of_bstarRank (hR : GGNbrD4BstarRankInput) :
    GGNbrGraphD4SmallInput := by
  intro G _ _ B Bs x L D J hC hm y K hK hN P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  by_cases hD : lab.tag = .D ∧ lab.rank = 4 ∧ (LargeEvenTwoLocalRank 3 G = 5 → 3 ∣ lab.n)
  · have hmark : LargeEvenMarking ↥K fun lab' _ _ _ _ _ => lab'.tag = .D ∧ lab'.rank = 4 ∧
        (LargeEvenTwoLocalRank 3 G = 5 → 3 ∣ lab'.n) :=
      ⟨hperf, lab, hlab, largeEvenRawDatum_mono
        (fun R _ I F ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, hD⟩) hraw⟩
    have h27 := hR G B Bs x L D J hC hm y K hK hN hmark
    have hraw' := largeEvenLabelAll_d4TrialityCentBound hD.1 hD.2.1 _ hraw
    refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw'⟩
    rintro R _ I F ⟨⟨hs, hna, θ, hθ⟩, hKG⟩
    exact ⟨hs, hna, θ, hθ, fun _ _ _ b hb =>
      exists_inner_mul_field_of_bstarRank hC.2.1.2.1 hN h27 hKG θ hb⟩
  · refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    rintro R _ I F ⟨hs, hna, θ, hθ⟩
    exact ⟨hs, hna, θ, hθ, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hD⟩

theorem ggNbrGraphD4SmallInput_of_input (h : GGNbrGraphD4Input) : GGNbrGraphD4SmallInput := by
  intro G _ _ B Bs x L D J hC _ y K hK hN P hP
  refine largeEvenMarking_mono ?_ (h G 3 B Bs x L D J hC rfl y K hK hN P hP)
  rintro lab R _ I F θ ⟨hθ, hQ⟩
  exact ⟨hθ, fun h1 h2 _ => hQ h1 h2⟩

theorem ggNbrGraphD4Input_of_bstarRank (hR : GGNbrD4BstarRankInput) : GGNbrGraphD4Input :=
  ggNbrGraphD4Input_of_small (ggNbrGraphD4SmallInput_of_bstarRank hR)


end CFSG.StandardType
