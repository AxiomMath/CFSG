module

public import CFSG.Quasithin.EmptyFaithful.S152VR3
public import CFSG.Quasithin.EmptyFaithful.S152VR4
public import CFSG.Quasithin.EmptyFaithful.S152VR5
public import CFSG.Quasithin.Background.F420Orders
public import CFSG.Quasithin.EmptyFaithful.R3c3Base
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Transport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma32LeKOut
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoSporadicJ4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open scoped commutatorElement

@[expose] def NineSporadic (s : TauCeti.SporadicName) : Prop :=
  s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J2 ∨ s = .HS ∨ s = .He ∨ s = .Ru

@[expose] def SporadicInvolution3Rank : Prop :=
  ∀ (s : TauCeti.SporadicName), NineSporadic s → ∀ (Γ : Type) [Group Γ] [Finite Γ],
    Nonempty (Γ ≃* NativeSporadic.Carrier s) →
      S152V.Rank2 Γ ∧ (∀ α : MulAut Γ, α ^ 3 = 1 → ∃ g : Γ, α = MulAut.conj g) ∧
        ∀ t : Γ, orderOf t = 2 → (∃ S : Sylow 2 Γ, ∀ x ∈ S, x * t = t * x) →
          ¬ 9 ∣ Nat.card (Subgroup.centralizer ({t} : Set Γ))

namespace S152V

open Equiv Equiv.Perm

theorem rank2_of_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : Rank2 Y) : Rank2 X := by
  obtain ⟨E, hc, he, hcard⟩ := h
  refine ⟨E.map e.symm.toMonoidHom, ⟨⟨fun a b => ?_⟩⟩, ?_, ?_⟩
  · obtain ⟨a', ha', ha⟩ := a.2
    obtain ⟨b', hb', hb⟩ := b.2
    apply Subtype.ext
    show (a : X) * b = b * a
    rw [← ha, ← hb, ← map_mul, ← map_mul]
    exact congrArg e.symm (congrArg Subtype.val (hc.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩))
  · rintro _ ⟨a', ha', rfl⟩
    rw [← map_pow, he a' ha', map_one]
  · rw [Subgroup.card_map_of_injective e.symm.injective, hcard]

theorem rank2_alt6 : Rank2 (alternatingGroup (Fin 6)) := by
  refine ⟨H6.subgroupOf (alternatingGroup (Fin 6)), ⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    exact H6_comm _ a.2 _ b.2
  · apply Subtype.ext
    have hx' : ((x : alternatingGroup (Fin 6)) : Perm (Fin 6)) ∈ H6 := hx
    simpa using H6_exp _ hx'
  · rw [← H6_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe H6_alt).toEquiv

theorem rank2_alt7 : Rank2 (alternatingGroup (Fin 7)) := by
  refine ⟨H7.subgroupOf (alternatingGroup (Fin 7)), ⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    exact H7_comm _ a.2 _ b.2
  · apply Subtype.ext
    have hx' : ((x : alternatingGroup (Fin 7)) : Perm (Fin 7)) ∈ H7 := hx
    simpa using H7_exp _ hx'
  · rw [← H7_card]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe H7_alt).toEquiv

theorem rank2_S3 : Rank2 CFSG.QuasithinUnique.Unc25K1.S3 := by
  obtain ⟨E, ⟨hc, he⟩, hcard⟩ := CFSG.QuasithinUnique.Unc25K1.exists_E9_S3
  exact ⟨E, hc, he, hcard⟩

section Common

variable {G : Type} [Group G] [Finite G]

theorem center_eq_bot_of_card {X : Type*} [Group X] [Finite X] (h2 : IsPGroup 2 (Subgroup.center X))
    (hc : Nat.card (Subgroup.center X) = 1 ∨ Nat.card (Subgroup.center X) = 3) :
    Subgroup.center X = ⊥ := by
  obtain ⟨a, ha⟩ := h2.exists_card_eq
  rcases hc with h | h
  · exact Subgroup.card_eq_one.1 h
  · exfalso
    rw [h] at ha
    rcases a with _ | a
    · norm_num at ha
    · rw [pow_succ] at ha
      omega

theorem ne_bot_of_quasisimple {G : Type} [Group G] {L : Subgroup G} (hq : CFSG.IsQuasisimple ↥L) : L ≠ ⊥ := by
  intro hL
  obtain ⟨-, -, a, b, hab⟩ := hq
  apply hab
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  have hx : x = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall L).1 hL x.1 x.2)
  have hy : y = 1 := Subtype.ext ((Subgroup.eq_bot_iff_forall L).1 hL y.1 y.2)
  rw [hx, hy]

omit [Finite G] in
theorem exists_nontrivial_action {L : Subgroup G} {z : G} (hcomm : ⁅L, Subgroup.zpowers z⁆ = L)
    (hL1 : L ≠ ⊥) : ∃ x ∈ L, z⁻¹ * x * z ≠ x := by
  by_contra hcon
  push Not at hcon
  apply hL1
  rw [← le_bot_iff, ← hcomm]
  refine (Subgroup.commutator_le).2 fun g₁ hg₁ g₂ hg₂ => ?_
  have hc1 : g₁ * z = z * g₁ := by
    have := hcon g₁ hg₁
    calc g₁ * z = z * (z⁻¹ * g₁ * z) := by group
      _ = z * g₁ := by rw [this]
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg₂
  rw [Subgroup.mem_bot]
  exact commutatorElement_eq_one_iff_mul_comm.2 ((Commute.zpow_right (show Commute g₁ z from hc1) n).eq)

theorem exists_H_of_cfg_bot {I L P : Subgroup G} {z : G} (hLI : L ≤ I) (hPI : P ≤ I)
    (hI : SQTKGroup ↥I) (hperf : Group.IsPerfect ↥L) (hZ : Subgroup.center ↥L = ⊥)
    (hOut : ∀ α : MulAut ↥L, α ^ 3 = 1 → ∃ g : ↥L, α = MulAut.conj g) (hrank : Rank2 ↥L)
    (hPN : P ≤ Subgroup.normalizer (L : Set G)) (hz : z ∈ Subgroup.normalizer (L : Set G))
    (hPz : ∀ x ∈ P, x * z = z * x) (hexp : ∀ x ∈ P, x ^ 3 = 1) (hcard : Nat.card P = 9) :
    ∃ H : Subgroup ↥L, Nat.card H = 9 ∧ (∀ g ∈ H, g ^ 3 = 1) ∧ ∀ g ∈ H, z⁻¹ * (g : G) * z = g := by
  have hZ2 : ∀ y ∈ L, (∀ w ∈ L, w * y = y * w) → ∃ k : ℕ, y ^ (2 ^ k) = 1 := by
    intro y hy hc
    refine ⟨0, ?_⟩
    have hmem : (⟨y, hy⟩ : ↥L) ∈ Subgroup.center ↥L := Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext (hc g g.2)
    rw [hZ] at hmem
    have := congrArg Subtype.val (Subgroup.mem_bot.1 hmem)
    simpa using this
  have hfaith := centralizer_trivial_of_rank hLI hPI hrank hI hZ2 hexp
  obtain ⟨H, hc, h3, hf⟩ :=
    exists_centralizing_subgroup_of_config_bot hperf hZ hOut hPN hz hPz hexp hfaith
  exact ⟨H, hc.trans hcard, h3, hf⟩

theorem contradiction_of_atlas {I L P : Subgroup G} {z l : G} (hLI : L ≤ I) (hPI : P ≤ I)
    (hI : SQTKGroup ↥I) (hperf : Group.IsPerfect ↥L) (hZ2 : IsPGroup 2 (Subgroup.center ↥L))
    (hrank : Rank2 (↥L ⧸ Subgroup.center ↥L))
    (hOut : ∀ α : MulAut (↥L ⧸ Subgroup.center ↥L), α ^ 3 = 1 → ∃ g, α = MulAut.conj g)
    (hcent : ∀ t : ↥L ⧸ Subgroup.center ↥L, orderOf t = 2 →
      (∃ S : Sylow 2 (↥L ⧸ Subgroup.center ↥L), ∀ x ∈ S, x * t = t * x) →
        ¬ 9 ∣ Nat.card (Subgroup.centralizer ({t} : Set (↥L ⧸ Subgroup.center ↥L))))
    (hPN : P ≤ Subgroup.normalizer (L : Set G)) (hz2 : z ^ 2 = 1) (hPz : ∀ x ∈ P, x * z = z * x)
    (hexp : ∀ x ∈ P, x ^ 3 = 1) (hcard : Nat.card P = 9) (hl : l ∈ L)
    (hlz : ∀ x ∈ L, z⁻¹ * x * z = l⁻¹ * x * l) (hnc : ∃ x ∈ L, z⁻¹ * x * z ≠ x) (P' : Subgroup G)
    (hP' : IsSylowTwoOf P' L) (hcom : ∀ p ∈ P', ⁅p, l⁆ ∈ Subgroup.centralizer (L : Set G)) :
    False := by
  have : Group.IsPerfect ↥L := hperf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥L) := by
    obtain ⟨a, ha⟩ := hZ2.exists_card_eq
    rw [ha]
    intro h
    have h2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hrankL : Rank2 ↥L := rank2_lift _ hZ3 hrank
  have hZ2' : ∀ y ∈ L, (∀ w ∈ L, w * y = y * w) → ∃ k : ℕ, y ^ (2 ^ k) = 1 := by
    intro y hy hc
    have hmem : (⟨y, hy⟩ : ↥L) ∈ Subgroup.center ↥L :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (hc g g.2)
    obtain ⟨k, hk⟩ := hZ2 ⟨⟨y, hy⟩, hmem⟩
    refine ⟨k, ?_⟩
    have := congrArg (fun t : ↥(Subgroup.center ↥L) => ((t : ↥L) : G)) hk
    simpa using this
  have hfaith := centralizer_trivial_of_rank hLI hPI hrankL hI hZ2' hexp
  have hz : z ∈ Subgroup.normalizer (L : Set G) :=
    normalizer_of_involution hz2 fun x hx => by
      rw [hlz x hx]
      exact L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl
  have hZΓ : Subgroup.center (↥L ⧸ Subgroup.center ↥L) = ⊥ :=
    Group.IsPerfect.center_quotient_center_eq_bot ↥L
  obtain ⟨H, hHcard, hH3, hHfix⟩ :=
    exists_fixedSubgroup_of_config hperf (MulEquiv.refl (↥L ⧸ Subgroup.center ↥L)) hZΓ hOut hPN hz
      hPz hexp hfaith
  let lam : ↥L := ⟨l, hl⟩
  let t : ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk lam
  have hHcomm : ∀ g ∈ H, g * t = t * g := by
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    have h1 := hHfix _ hg
    have h2 : (inducedAut (MulEquiv.refl (↥L ⧸ Subgroup.center ↥L))
        (L.normalizerMonoidHom ⟨z⁻¹, Subgroup.inv_mem _ hz⟩)) (QuotientGroup.mk x) =
        QuotientGroup.mk (lam⁻¹ * x * lam) := by
      have := inducedAut_apply (MulEquiv.refl (↥L ⧸ Subgroup.center ↥L))
        (L.normalizerMonoidHom ⟨z⁻¹, Subgroup.inv_mem _ hz⟩) x
      refine this.trans ?_
      show QuotientGroup.mk (L.normalizerMonoidHom ⟨z⁻¹, Subgroup.inv_mem _ hz⟩ x) = _
      congr 1
      apply Subtype.ext
      have h3 := Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨z⁻¹, Subgroup.inv_mem _ hz⟩ x
      rw [h3]
      show z⁻¹ * (x : G) * (z⁻¹)⁻¹ = l⁻¹ * (x : G) * l
      rw [inv_inv]
      exact hlz x x.2
    rw [h2] at h1
    have h4 : t⁻¹ * QuotientGroup.mk x * t = QuotientGroup.mk x := h1
    calc QuotientGroup.mk x * t = t * (t⁻¹ * QuotientGroup.mk x * t) := by group
      _ = t * QuotientGroup.mk x := by rw [h4]
  have hc2 := inner_sq_central hz2 hl hlz
  have ht2 : t ^ 2 = 1 := by
    have hmem : (⟨l * l, L.mul_mem hl hl⟩ : ↥L) ∈ Subgroup.center ↥L :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (hc2 g g.2).symm
    rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    exact hmem
  have ht1 : t ≠ 1 := by
    intro h1
    have hmem : lam ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨x, hx, hxne⟩ := hnc
    apply hxne
    rw [hlz x hx]
    have h2 : x * l = l * x := congrArg Subtype.val (Subgroup.mem_center_iff.1 hmem ⟨x, hx⟩)
    calc l⁻¹ * x * l = l⁻¹ * (x * l) := by group
      _ = l⁻¹ * (l * x) := by rw [h2]
      _ = x := by group
  have ht : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  have hPl2 : IsPGroup 2 ↥(P'.subgroupOf L) := hP'.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hP'.1).symm
  let Q : Sylow 2 ↥L := hPl2.toSylow hP'.2.2
  have hQc : (Q : Subgroup ↥L) = P'.subgroupOf L := IsPGroup.toSylow_coe _ _
  let S : Sylow 2 (↥L ⧸ Subgroup.center ↥L) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center ↥L)) Q
  have hS : ∀ x ∈ S, x * t = t * x := by
    intro x hx
    have hx' : x ∈ (Q : Subgroup ↥L).map (QuotientGroup.mk' (Subgroup.center ↥L)) := hx
    obtain ⟨q, hq, rfl⟩ := hx'
    rw [hQc] at hq
    have hq' : (q : G) ∈ P' := hq
    have hqc := hcom (q : G) hq'
    have hqL : ⁅(q : G), l⁆ ∈ L := by
      rw [commutatorElement_def]
      exact L.mul_mem (L.mul_mem (L.mul_mem q.2 hl) (L.inv_mem q.2)) (L.inv_mem hl)
    have hmem : (⟨⁅(q : G), l⁆, hqL⟩ : ↥L) ∈ Subgroup.center ↥L :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_centralizer_iff.1 hqc g g.2)
    have h1 : QuotientGroup.mk (⁅q, lam⁆ : ↥L) = (1 : ↥L ⧸ Subgroup.center ↥L) :=
      (QuotientGroup.eq_one_iff _).2 hmem
    have h2 : ⁅(QuotientGroup.mk q : ↥L ⧸ Subgroup.center ↥L), t⁆ = 1 := by
      rw [← h1]
      exact (map_commutatorElement (QuotientGroup.mk' (Subgroup.center ↥L)) q lam).symm
    exact commutatorElement_eq_one_iff_mul_comm.1 h2
  apply hcent t ht ⟨S, hS⟩
  have hle : H ≤ Subgroup.centralizer ({t} : Set (↥L ⧸ Subgroup.center ↥L)) := fun g hg =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact (hHcomm g hg).symm
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hHcard, hcard] at hdvd
  exact hdvd

end Common

end S152V

open Equiv Equiv.Perm in
open S152V in
theorem tail15215Rank_of
    (hA3 : ∀ (G : Type) [Group G] [Finite G], A3Orbits G)
    (hM : CFSG.ComponentClassification.RankTwoSporadic.J4.J4NoDoubleCover)
    (hSpor : SporadicInvolution3Rank) : Tail15215Rank := by
  intro G _ _ I S Mi L L₀ K P z cfg hnot
  have hq : CFSG.IsQuasisimple ↥L := BenderBranch.isQuasisimple_of_isComponentIn cfg.comp
  have hperf : Group.IsPerfect ↥L := hq.1
  have hLI : L ≤ I := cfg.comp.1
  have hKI : K ≤ I := fun x hx => by
    have := cfg.K_le hx
    rw [cfg.hMi] at this
    exact this.1
  have hPI : P ≤ I := cfg.P_le.trans hKI
  have hPN : P ≤ Subgroup.normalizer (L : Set G) := cfg.P_le.trans (K_le_normalizer_of_cfg hA3 cfg)
  have hPz : ∀ x ∈ P, x * z = z * x := fun x hx => by
    have h1 := cfg.K_le (cfg.P_le hx)
    rw [cfg.hMi] at h1
    exact (Subgroup.mem_centralizer_iff.1 h1.2 z (Set.mem_singleton z)).symm
  have hZeq : Subgroup.center ↥L = CFSG.pCore 2 ↥L := center_eq_pCore cfg.center
  have hZ2 : IsPGroup 2 (Subgroup.center ↥L) := by
    rw [hZeq]
    exact CFSG.pCore_isPGroup
  have hnc : ∃ x ∈ L, z⁻¹ * x * z ≠ x := exists_nontrivial_action cfg.comm (ne_bot_of_quasisimple hq)
  rcases cfg.cases with hA | hB | hC | hD | hE | hF
  ·
    obtain ⟨hs, hlie, -⟩ := hA
    exact absurd (Lemma115LieCharTwo.of_mulEquiv
      (CFSG.Quasithin.R3c3.quotCenterEquivOfSimple hs hperf) hlie) cfg.notLie
  ·
    obtain ⟨-, hZO, hmod, -⟩ := hB
    refine absurd (Lemma115LieCharTwo.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZO) ?_)
      cfg.notLie
    rcases hmod with h | h
    · exact Or.inl (Or.inl (Or.inl ⟨2, Or.inr (Or.inl ⟨by norm_num, h⟩)⟩))
    · exact Or.inl (Or.inl (Or.inl ⟨2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by norm_num, h⟩))))⟩))
  ·
    exfalso
    obtain ⟨φ, σ, hc3, hσ, hperm⟩ := hC
    have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_card hZ2 hc3
    let ψ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    let e6 : ↥L ≃* alternatingGroup (Fin 6) := ψ.symm.trans φ
    have hOut : ∀ α : MulAut ↥L, α ^ 3 = 1 → ∃ g : ↥L, α = MulAut.conj g := fun α hα => by
      obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.DoubleA3.kInEight_aut_three_inner hq
        (Or.inr (Or.inl ⟨e6⟩)) α hα
      exact ⟨g, hg.symm⟩
    have hz := normalizer_of_involution cfg.z2 hperm.1
    obtain ⟨H, hHc, hH3, hHf⟩ := exists_H_of_cfg_bot hLI hPI cfg.sqtk hperf hZ hOut
      (rank2_of_equiv e6 rank2_alt6) hPN hz hPz cfg.P_exp cfg.P_card
    let H6' : Subgroup (Perm (Fin 6)) :=
      (H.map e6.toMonoidHom).map (alternatingGroup (Fin 6)).subtype
    have hcardH : Nat.card H6' = 9 := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
        Subgroup.card_map_of_injective e6.injective]
      exact hHc
    have halt : H6' ≤ alternatingGroup (Fin 6) := by
      rintro _ ⟨a, -, rfl⟩
      exact a.2
    have hσ2 : σ ^ 2 = 1 := by
      have := pow_orderOf_eq_one σ
      rwa [hσ.orderOf] at this
    refine no_commuting_involution_alt6 H6' halt hcardH σ hσ2 hσ.isCycle.ne_one ?_
    rintro _ ⟨a, ⟨g, hg, rfl⟩, rfl⟩
    have hye := hperm.2 g g (hHf g hg).symm
    have he6 : ((e6 g : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
        ((φ (QuotientGroup.mk g) : alternatingGroup (Fin 6)) : Perm (Fin 6)) := rfl
    show σ * ((e6 g : alternatingGroup (Fin 6)) : Perm (Fin 6)) =
      ((e6 g : alternatingGroup (Fin 6)) : Perm (Fin 6)) * σ
    rw [he6]
    calc σ * ((φ (QuotientGroup.mk g) : alternatingGroup (Fin 6)) : Perm (Fin 6))
        = σ * (σ⁻¹ * ((φ (QuotientGroup.mk g) : alternatingGroup (Fin 6)) : Perm (Fin 6)) * σ) := by
          rw [← hye]
      _ = _ := by group
  ·
    exfalso
    obtain ⟨φ, σ, hc3, hσ, hperm⟩ := hD
    have hZ : Subgroup.center ↥L = ⊥ := center_eq_bot_of_card hZ2 hc3
    let ψ : (↥L ⧸ Subgroup.center ↥L) ≃* ↥L :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    let e7 : ↥L ≃* alternatingGroup (Fin 7) := ψ.symm.trans φ
    have hOut : ∀ α : MulAut ↥L, α ^ 3 = 1 → ∃ g : ↥L, α = MulAut.conj g := fun α hα => by
      obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.DoubleA3.kInEight_aut_three_inner hq
        (Or.inr (Or.inr (Or.inl ⟨e7⟩))) α hα
      exact ⟨g, hg.symm⟩
    have hz := normalizer_of_involution cfg.z2 hperm.1
    obtain ⟨H, hHc, hH3, hHf⟩ := exists_H_of_cfg_bot hLI hPI cfg.sqtk hperf hZ hOut
      (rank2_of_equiv e7 rank2_alt7) hPN hz hPz cfg.P_exp cfg.P_card
    let H7' : Subgroup (Perm (Fin 7)) :=
      (H.map e7.toMonoidHom).map (alternatingGroup (Fin 7)).subtype
    have hcardH : Nat.card H7' = 9 := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
        Subgroup.card_map_of_injective e7.injective]
      exact hHc
    have halt : H7' ≤ alternatingGroup (Fin 7) := by
      rintro _ ⟨a, -, rfl⟩
      exact a.2
    have hord : orderOf σ = 2 := by
      rw [← Equiv.Perm.lcm_cycleType, hσ]
      decide
    have hσ2 : σ ^ 2 = 1 := by
      have := pow_orderOf_eq_one σ
      rwa [hord] at this
    have hσ1 : σ ≠ 1 := by
      intro h1
      rw [h1, Equiv.Perm.cycleType_one] at hσ
      exact absurd hσ (by decide)
    refine no_commuting_involution_alt7 H7' halt hcardH σ hσ2 hσ1 ?_
    rintro _ ⟨a, ⟨g, hg, rfl⟩, rfl⟩
    have hye := hperm.2 g g (hHf g hg).symm
    have he7 : ((e7 g : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
        ((φ (QuotientGroup.mk g) : alternatingGroup (Fin 7)) : Perm (Fin 7)) := rfl
    show σ * ((e7 g : alternatingGroup (Fin 7)) : Perm (Fin 7)) =
      ((e7 g : alternatingGroup (Fin 7)) : Perm (Fin 7)) * σ
    rw [he7]
    calc σ * ((φ (QuotientGroup.mk g) : alternatingGroup (Fin 7)) : Perm (Fin 7))
        = σ * (σ⁻¹ * ((φ (QuotientGroup.mk g) : alternatingGroup (Fin 7)) : Perm (Fin 7)) * σ) := by
          rw [← hye]
      _ = _ := by group
  ·
    obtain ⟨hmodel, hinn⟩ := hE
    rcases hmodel with h33 | hex
    · exfalso
      have hZ : Subgroup.center ↥L = ⊥ := CFSG.Quasithin.F420.center_eq_bot_of_statedPSL h33
      let eS : ↥L ≃* CFSG.QuasithinUnique.Unc25K1.S3 :=
        ((CFSG.QuasithinUnique.Unc25K1.psl33_equiv h33).some).trans
          CFSG.QuasithinUnique.Unc25K1.psl33EquivS3
      have hOut : ∀ α : MulAut ↥L, α ^ 3 = 1 → ∃ g : ↥L, α = MulAut.conj g := fun α hα => by
        obtain ⟨g, hg⟩ := CFSG.QuasithinUnique.DoubleA3.kInEight_aut_three_inner hq
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h33))))))) α hα
        exact ⟨g, hg.symm⟩
      obtain ⟨l, hl, hlz⟩ := hinn
      have hz := normalizer_of_involution cfg.z2 fun x hx => by
        rw [hlz x hx]
        exact L.mul_mem (L.mul_mem (L.inv_mem hl) hx) hl
      obtain ⟨H, hHc, hH3, hHf⟩ := exists_H_of_cfg_bot hLI hPI cfg.sqtk hperf hZ hOut
        (rank2_of_equiv eS rank2_S3) hPN hz hPz cfg.P_exp cfg.P_card
      have hl1 : l ≠ 1 := inner_ne_one hlz hnc
      have hll : l * l = 1 := inner_sq_eq_one_of_center_bot hZ cfg.z2 hl hlz
      let lam : ↥L := ⟨l, hl⟩
      have hlam1 : lam ≠ 1 := fun h => hl1 (congrArg Subtype.val h)
      have hlam2 : lam ^ 2 = 1 := Subtype.ext (by simpa [pow_two] using hll)
      refine no_commuting_involution_S3 (H.map eS.toMonoidHom) ?_ ?_ (eS lam) ?_ ?_ ?_
      · rw [Subgroup.card_map_of_injective eS.injective]
        exact hHc
      · rintro _ ⟨g, hg, rfl⟩
        rw [← map_pow]
        show eS (g ^ 3) = 1
        rw [hH3 g hg, map_one]
      · intro h
        exact hlam1 (eS.injective (h.trans (map_one eS).symm))
      · rw [← map_pow, hlam2, map_one]
      · rintro _ ⟨g, hg, rfl⟩
        show eS lam * eS g = eS g * eS lam
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        show l * (g : G) = (g : G) * l
        have h1 := hlz g g.2
        rw [hHf g hg] at h1
        calc l * (g : G) = l * (l⁻¹ * (g : G) * l) := by rw [← h1]
          _ = (g : G) * l := by group
    · exact absurd hex hnot
  ·
    obtain ⟨⟨s, hs, ⟨φ⟩⟩, hF⟩ := hF
    by_cases hJ : s = .J4
    · subst hJ
      exact CFSG.ComponentClassification.RankTwoSporadic.J4.isSporadic_J4_of_quot hM
        (Group.isPerfect_def.1 hperf) ((QuotientGroup.quotientMulEquivOfEq hZeq).trans φ)
    · exfalso
      have hs9 : NineSporadic s := by
        rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | exact absurd rfl hJ | simp [NineSporadic]
      obtain ⟨hrank, hOut, hcent⟩ := hSpor s hs9 (↥L ⧸ Subgroup.center ↥L)
        ⟨(QuotientGroup.quotientMulEquivOfEq hZeq).trans φ⟩
      obtain ⟨l, hl, hlz, hnc', P', hP', hcom⟩ := hF
      exact contradiction_of_atlas hLI hPI cfg.sqtk hperf hZ2 hrank hOut hcent hPN cfg.z2 hPz
        cfg.P_exp cfg.P_card hl hlz hnc' P' hP' hcom

end CFSG.Quasithin
