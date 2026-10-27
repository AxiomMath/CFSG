module

public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6
public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFComp

public section

namespace CFSG.StandardType.TCResidual

open CFSG.Assembly

section ResidualExclusion

variable {G : Type} [Group G]

def ggInnPart (L T : Subgroup G) (hTL : T ≤ Subgroup.normalizer (L : Set G)) : Subgroup G where
  carrier := {l | l ∈ L ∧ ∃ t ∈ T, ∀ g ∈ L, l * g * l⁻¹ = t * g * t⁻¹}
  one_mem' := ⟨L.one_mem, 1, T.one_mem, fun g _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨haL, s, hs, has⟩ ⟨hbL, u, hu, hbu⟩
    refine ⟨L.mul_mem haL hbL, s * u, T.mul_mem hs hu, fun g hg => ?_⟩
    have hug : u * g * u⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hTL hu) g).mp hg
    calc a * b * g * (a * b)⁻¹ = a * (b * g * b⁻¹) * a⁻¹ := by group
      _ = a * (u * g * u⁻¹) * a⁻¹ := by rw [hbu g hg]
      _ = s * (u * g * u⁻¹) * s⁻¹ := has _ hug
      _ = s * u * g * (s * u)⁻¹ := by group
  inv_mem' := by
    rintro a ⟨haL, s, hs, has⟩
    refine ⟨L.inv_mem haL, s⁻¹, T.inv_mem hs, fun g hg => ?_⟩
    have h1 : a⁻¹ * g * a ∈ L := L.mul_mem (L.mul_mem (L.inv_mem haL) hg) haL
    calc a⁻¹ * g * a⁻¹⁻¹ = s⁻¹ * (s * (a⁻¹ * g * a) * s⁻¹) * s := by group
      _ = s⁻¹ * (a * (a⁻¹ * g * a) * a⁻¹) * s := by rw [has _ h1]
      _ = s⁻¹ * g * s⁻¹⁻¹ := by group

theorem ggInn_pow {L T : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G)) {l t : G}
    (ht : t ∈ T) (h : ∀ g ∈ L, l * g * l⁻¹ = t * g * t⁻¹) (n : ℕ) :
    ∀ g ∈ L, l ^ n * g * (l ^ n)⁻¹ = t ^ n * g * (t ^ n)⁻¹ := by
  induction n with
  | zero => intro g _; simp
  | succ n ih =>
    intro g hg
    have htn : t ^ n * g * (t ^ n)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hTL (T.pow_mem ht n)) g).mp hg
    calc l ^ (n + 1) * g * (l ^ (n + 1))⁻¹ = l * (l ^ n * g * (l ^ n)⁻¹) * l⁻¹ := by
          rw [pow_succ']; group
      _ = l * (t ^ n * g * (t ^ n)⁻¹) * l⁻¹ := by rw [ih g hg]
      _ = t * (t ^ n * g * (t ^ n)⁻¹) * t⁻¹ := h _ htn
      _ = t ^ (n + 1) * g * (t ^ (n + 1))⁻¹ := by rw [pow_succ']; group

theorem ggMem_centralizer_of_conj {L : Subgroup G} {l : G} (h : ∀ g ∈ L, l * g * l⁻¹ = g) :
    l ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have := h g hg
  rw [mul_inv_eq_iff_eq_mul] at this
  exact this.symm

variable [Finite G]

theorem ggStepTwo {L T B : Subgroup G} (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hT2 : IsPGroup 2 T) (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hBT : B ≤ Subgroup.normalizer (T : Set G))
    (hB0 : ∀ S : Subgroup G, S ≤ L → IsPGroup 2 S → B ≤ Subgroup.normalizer (S : Set G) → S = ⊥)
    {t l : G} (ht : t ∈ T) (hl : l ∈ L) (htl : ∀ g ∈ L, t * g * t⁻¹ = l * g * l⁻¹) :
    t ∈ Subgroup.centralizer (L : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := ggInnPart L T hTL with hXdef
  have hpow : ∀ a ∈ X, ∃ k : ℕ, a ^ (2 ^ k) ∈ Subgroup.centralizer (L : Set G) := by
    rintro a ⟨-, s, hs, has⟩
    obtain ⟨k, hk⟩ := hT2 ⟨s, hs⟩
    have hk' : s ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
    refine ⟨k, ggMem_centralizer_of_conj fun g hg => ?_⟩
    rw [ggInn_pow hTL hs has (2 ^ k) g hg, hk']
    simp
  have hcen : ∀ a : X, (a : G) ∈ Subgroup.centralizer (L : Set G) → a ∈ Subgroup.center X := by
    intro a ha
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp ha) g g.2.1)
  have hQ : IsPGroup 2 (X ⧸ Subgroup.center X) := by
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := hpow a a.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact hcen _ hk
  haveI : Group.IsNilpotent (X ⧸ Subgroup.center X) := hQ.isNilpotent
  haveI : Group.IsNilpotent X :=
    isNilpotent_of_ker_le_center (QuotientGroup.mk' (Subgroup.center X))
      (by rw [QuotientGroup.ker_mk'])
  let P : Sylow 2 X := default
  have hPn : (P : Subgroup X).Normal := inferInstance
  have hchar : (P : Subgroup X).Characteristic := Sylow.characteristic_of_normal P hPn
  have hBX : ∀ b ∈ B, ∀ a ∈ X, b * a * b⁻¹ ∈ X := by
    rintro b hb a ⟨haL, s, hs, has⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hBL hb) a).mp haL, b * s * b⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hBT hb) s).mp hs, fun g hg => ?_⟩
    have hg' : b⁻¹ * g * b ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hBL (B.inv_mem hb)) g).mp hg
    calc b * a * b⁻¹ * g * (b * a * b⁻¹)⁻¹ = b * (a * (b⁻¹ * g * b) * a⁻¹) * b⁻¹ := by group
      _ = b * (s * (b⁻¹ * g * b) * s⁻¹) * b⁻¹ := by rw [has _ hg']
      _ = b * s * b⁻¹ * g * (b * s * b⁻¹)⁻¹ := by group
  let φ : ∀ b ∈ B, X ≃* X := fun b hb =>
    { toFun := fun a => ⟨b * a * b⁻¹, hBX b hb a a.2⟩
      invFun := fun a => ⟨b⁻¹ * a * b, by simpa using hBX b⁻¹ (B.inv_mem hb) a a.2⟩
      left_inv := fun a => Subtype.ext (by simp [mul_assoc])
      right_inv := fun a => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a c => Subtype.ext (by simp [mul_assoc]) }
  set S : Subgroup G := (P : Subgroup X).map X.subtype with hSdef
  have hSL : S ≤ L := (Subgroup.map_subtype_le _).trans fun _ h => h.1
  have hS2 : IsPGroup 2 S := P.isPGroup'.map X.subtype
  have hfwd : ∀ b ∈ B, ∀ h ∈ S, b * h * b⁻¹ ∈ S := by
    rintro b hb _ ⟨a, ha, rfl⟩
    exact ⟨φ b hb a, (Subgroup.characteristic_iff_le_comap.mp hchar (φ b hb)) ha, rfl⟩
  have hSB : B ≤ Subgroup.normalizer (S : Set G) := by
    intro b hb
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨hfwd b hb h, fun h' => ?_⟩
    simpa [mul_assoc] using hfwd b⁻¹ (B.inv_mem hb) _ h'
  have hPbot : (P : Subgroup X) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp (hB0 S hSL hS2 hSB)
  have hodd : ¬ 2 ∣ Nat.card X := fun hd => P.ne_bot_of_dvd_card hd hPbot
  have hlX : l ∈ X := ⟨hl, t, ht, fun g hg => (htl g hg).symm⟩
  obtain ⟨k, hk⟩ := hT2 ⟨t, ht⟩
  have hk' : t ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hlk : l ^ (2 ^ k) ∈ Subgroup.centralizer (L : Set G) :=
    ggMem_centralizer_of_conj fun g hg => by
      rw [ggInn_pow hTL ht (fun g hg => (htl g hg).symm) (2 ^ k) g hg, hk']
      simp
  have hcop : (2 ^ k).Coprime (orderOf l) := by
    refine Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr ?_)
    exact fun h2 => hodd (h2.trans (Subgroup.orderOf_dvd_natCard X hlX))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hlC : l ∈ Subgroup.centralizer (L : Set G) := hm ▸ Subgroup.pow_mem _ hlk m
  refine ggMem_centralizer_of_conj fun g hg => ?_
  rw [htl g hg]
  have := (Subgroup.mem_centralizer_iff.mp hlC) g hg
  rw [← this]
  group

theorem ggStepOne {x : G} {L T : Subgroup G} (hrank : LargeEvenTwoLocalRank 3 G ≤ 4)
    (hL : IsComponentOf L (Subgroup.centralizer {x})) (hTx : T ≤ Subgroup.centralizer {x})
    (hF1 : ∃ E ≤ L, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4)
    (hF2 : ∃ y ∈ L, y ^ 3 = 1 ∧ y ∉ Subgroup.centralizer (L : Set G) ∧
      ∃ s ∈ L, s ≠ 1 ∧ s ^ 2 = 1 ∧ y * s = s * y) :
    T ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro t ht
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  set L' := L.map (MulAut.conj t).toMonoidHom with hL'
  have hL'c : IsComponentOf L' (Subgroup.centralizer {x}) := ggIsComponentOf_conj hL (hTx ht)
  have hsub : (L'.subgroupOf (Subgroup.centralizer {x})).IsSubnormal :=
    (ggAssemblyIsSubnormal_iff hL'c.1).mp hL'c.2.1
  have hmemL' : ∀ g ∈ L, t * g * t⁻¹ ∈ Subgroup.centralizer {x} ⊓ L' := fun g hg =>
    ⟨hL'c.1 ⟨g, hg, rfl⟩, ⟨g, hg, rfl⟩⟩
  rcases ggComponent_le_or_commute hL hsub with hle | hcomm
  · have hcard : Nat.card L' = Nat.card L :=
      Subgroup.card_map_of_injective (MulAut.conj t).injective
    exact hne (Subgroup.eq_of_le_of_card_ge hle hcard.le).symm
  · obtain ⟨E, hEL, hE, hEc⟩ := hF1
    obtain ⟨y, hyL, hy3, hyc, s, hsL, hs1, hs2, hys⟩ := hF2
    have hy'3 : (t * y * t⁻¹) ^ 3 = 1 := by rw [conj_pow, hy3]; group
    have hs'2 : (t * s * t⁻¹) ^ 2 = 1 := by rw [conj_pow, hs2]; group
    have hs'1 : t * s * t⁻¹ ≠ 1 := fun h => hs1 (by simpa using h)
    have hy'E : t * y * t⁻¹ ∉ E := by
      intro hy'E
      apply hyc
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h1 := hcomm _ (hEL hy'E) _ (hmemL' g hg)
      have h2 : t⁻¹ * (t * y * t⁻¹ * (t * g * t⁻¹)) * t =
          t⁻¹ * (t * g * t⁻¹ * (t * y * t⁻¹)) * t := by rw [h1]
      have h3 : y * g = g * y := by simpa [mul_assoc] using h2
      exact h3.symm
    obtain ⟨hab, hcard⟩ := isElemAbelian_sup_zpowers_of_card Nat.prime_three hE hEc hy'3 hy'E
      (fun e he => hcomm e (hEL he) _ (hmemL' y hyL))
    have hU : Subgroup.zpowers (t * s * t⁻¹) ≠ ⊥ := by
      rwa [Ne, Subgroup.zpowers_eq_bot]
    have hU2 : IsPGroup 2 (Subgroup.zpowers (t * s * t⁻¹)) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime hs'2 hs'1, pow_one])
    have hnorm : ∀ g : G, g * (t * s * t⁻¹) = t * s * t⁻¹ * g →
        g ∈ Subgroup.normalizer ((Subgroup.zpowers (t * s * t⁻¹) : Subgroup G) : Set G) := by
      intro g hg
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_left (Commute.symm hg) n).eq
    have hEU : E ⊔ Subgroup.zpowers (t * y * t⁻¹) ≤
        Subgroup.normalizer ((Subgroup.zpowers (t * s * t⁻¹) : Subgroup G) : Set G) := by
      refine sup_le (fun e he => hnorm e (hcomm e (hEL he) _ (hmemL' s hsL))) ?_
      rw [Subgroup.zpowers_le]
      apply hnorm
      simp only [mul_assoc, inv_mul_cancel_left]
      rw [← mul_assoc y, hys, mul_assoc]
    have := le_twoLocalRank_of_normalizes Nat.prime_three hU hU2 hab hEU hcard
    omega

theorem ggResidual_commutator_eq_bot {x : G} {L B T : Subgroup G}
    (hrank : LargeEvenTwoLocalRank 3 G ≤ 4)
    (hL : IsComponentOf L (Subgroup.centralizer {x}))
    (hBL : B ≤ Subgroup.normalizer (L : Set G))
    (hB0 : ∀ S : Subgroup G, S ≤ L → IsPGroup 2 S → B ≤ Subgroup.normalizer (S : Set G) → S = ⊥)
    (hT2 : IsPGroup 2 T) (hTx : T ≤ Subgroup.centralizer {x})
    (hBT : B ≤ Subgroup.normalizer (T : Set G))
    (hF1 : ∃ E ≤ L, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4)
    (hF1' : ∃ E ≤ L ⊔ Subgroup.zpowers x, IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 5)
    (hF2 : ∃ y ∈ L, y ^ 3 = 1 ∧ y ∉ Subgroup.centralizer (L : Set G) ∧
      ∃ s ∈ L, s ≠ 1 ∧ s ^ 2 = 1 ∧ y * s = s * y)
    (hOut : ∀ T' : Subgroup G, IsPGroup 2 T' → T' ≤ Subgroup.normalizer (L : Set G) →
      (∀ t ∈ T', ∀ l ∈ L, (∀ g ∈ L, t * g * t⁻¹ = l * g * l⁻¹) →
        t ∈ Subgroup.centralizer (L : Set G)) →
      Nat.card T' ≤ 2 * Nat.card (T' ⊓ Subgroup.centralizer (L : Set G) : Subgroup G)) :
    ⁅T, B⁆ = ⊥ := by
  classical
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := ggStepOne hrank hL hTx hF1 hF2
  have hT0 : T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    by_contra hne
    obtain ⟨E, hEle, hE, hEc⟩ := hF1'
    have hEN : E ≤ Subgroup.normalizer
        ((T ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) := by
      refine hEle.trans (le_trans (sup_le ?_ ?_) (Subgroup.centralizer_le_normalizer _))
      · intro l hl
        rw [Subgroup.mem_centralizer_iff]
        rintro u ⟨-, hu⟩
        exact ((Subgroup.mem_centralizer_iff.mp hu) l hl).symm
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        rintro u ⟨hu, -⟩
        exact Subgroup.mem_centralizer_singleton_iff.mp (hTx hu)
    have := le_twoLocalRank_of_normalizes Nat.prime_three hne (hT2.to_le inf_le_left) hE hEN hEc
    omega
  have hcardT : Nat.card T ≤ 2 := by
    have := hOut T hT2 hTL fun t ht l hl h => ggStepTwo hTL hT2 hBL hBT hB0 ht hl h
    rwa [hT0, Subgroup.card_bot, mul_one] at this
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro t ht
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hbt : b * t * b⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp (hBT hb) t).mp ht
  by_contra hne
  have h1 : b * t * b⁻¹ ≠ t := fun h => hne (by
    calc b * t = b * t * b⁻¹ * b := by group
      _ = t * b := by rw [h])
  have ht1 : t ≠ 1 := by rintro rfl; simp at hne
  have h2 : b * t * b⁻¹ ≠ 1 := fun h => ht1 (by simpa using h)
  haveI : Fintype T := Fintype.ofFinite _
  have h3 : ({1, ⟨t, ht⟩, ⟨b * t * b⁻¹, hbt⟩} : Finset T).card = 3 := by
    refine Finset.card_eq_three.mpr ⟨_, _, _, ?_, ?_, ?_, rfl⟩
    · exact fun h => ht1 (congrArg Subtype.val h).symm
    · exact fun h => h2 (congrArg Subtype.val h).symm
    · exact fun h => h1 (congrArg Subtype.val h).symm
  have h4 := Finset.card_le_univ ({1, ⟨t, ht⟩, ⟨b * t * b⁻¹, hbt⟩} : Finset T)
  rw [h3, Fintype.card_eq_nat_card] at h4
  omega

end ResidualExclusion

end CFSG.StandardType.TCResidual

end
