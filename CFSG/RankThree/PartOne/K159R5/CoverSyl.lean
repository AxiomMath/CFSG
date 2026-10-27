module

public import CFSG.RankThree.PartOne.S15K.AutLayer
public import CFSG.RankThree.PartOne.K159R5.SylTransfer

public section

namespace CFSG.RankThree.PartOne.K159R5

open scoped commutatorElement
open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S15K CFSG.RankThree.PartOne.KCUnitary

variable {G : Type} [Group G] [Finite G]

@[expose] def LayerDataWS (p : ℕ) (E I : Subgroup G) : Prop :=
  ∀ b ∈ E, b ≠ 1 → ∃ (ι : Type) (Q : ι → Subgroup G),
    (∀ i, Q i ≤ I ⊓ Subgroup.centralizer ({b} : Set G)) ∧
    (∀ i, IsComponent ((Q i).subgroupOf (I ⊓ Subgroup.centralizer ({b} : Set G)))) ∧
    (∀ Y : Subgroup G, Y ≤ I ⊓ Subgroup.centralizer ({b} : Set G) → Group.IsPerfect ↥Y →
      Y ≤ ⨆ i, Q i) ∧
    (∀ i, (∀ e ∈ E, ∃ x ∈ Q i, ∃ y ∈ Subgroup.centralizer (Q i : Set G), e = x * y) ∧
      ¬ p ∣ Nat.card ↥(Q i ⊓ Subgroup.centralizer (Q i : Set G))) ∧
    ∀ i, SylAb p (Q i)

omit [Finite G] in
theorem LayerDataWS.toW {p : ℕ} {E I : Subgroup G} (h : LayerDataWS p E I) : LayerDataW p E I := by
  intro b hb hb1
  obtain ⟨ι, Q, h1, h2, h3, h4, -⟩ := h b hb hb1
  exact ⟨ι, Q, h1, h2, h3, h4⟩

theorem exists_components_of_cover_syl {p : ℕ} (hp : p.Prime) {Hs : Subgroup G} {C : Type} [Group C]
    (Φ : ↥Hs →* C) (hΦs : Function.Surjective Φ) (hΦk : Φ.ker ≤ Subgroup.center ↥Hs)
    (hΦn : ¬ p ∣ Nat.card Φ.ker) {ι : Type} (F' : ι → Subgroup C) (hcomp : ∀ i, IsComponent (F' i))
    (hperf : ∀ Y : Subgroup C, ⁅Y, Y⁆ = Y → Y ≤ ⨆ i, F' i)
    (hcen : ∀ i, ∀ u ∈ F' i, (∀ f ∈ F' i, u * f = f * u) → u ^ p = 1 → u = 1)
    (hsyl : ∀ i, SylAb p (F' i)) :
    ∃ Q : ι → Subgroup G, (∀ i, Q i ≤ Hs) ∧ (∀ i, IsComponent ((Q i).subgroupOf Hs)) ∧
      (∀ Y : Subgroup G, Y ≤ Hs → Group.IsPerfect ↥Y → Y ≤ ⨆ i, Q i) ∧
      (∀ i, ¬ p ∣ Nat.card ↥(Q i ⊓ Subgroup.centralizer (Q i : Set G))) ∧
      (∀ i, SylAb p (Q i)) ∧
      ∀ (i : ι) (e : G) (τ : ↥Hs →* ↥Hs), (∀ y : ↥Hs, ((τ y : ↥Hs) : G) = e * y * e⁻¹) →
        ∀ x ∈ F' i, (∀ y : ↥Hs, Φ y ∈ F' i → Φ (τ y) = x * Φ y * x⁻¹) →
          ∃ x' ∈ Q i, ∃ y' ∈ Subgroup.centralizer (Q i : Set G), e = x' * y' := by
  classical
  have hperfF : ∀ i, ⁅F' i, F' i⁆ = F' i := fun i => Subgroup.isPerfect_iff.1 (hcomp i).1.1
  obtain ⟨Qs, hQs⟩ : ∃ Qs : ι → Subgroup ↥Hs,
      ∀ i, Qs i = ⁅(F' i).comap Φ, (F' i).comap Φ⁆ :=
    ⟨fun i => ⁅(F' i).comap Φ, (F' i).comap Φ⁆, fun _ => rfl⟩
  have hQF : ∀ i, (Qs i).map Φ = F' i := fun i => by
    rw [hQs i]; exact map_commutator_comap hΦs (hperfF i)
  have hQperf : ∀ i, ⁅Qs i, Qs i⁆ = Qs i := fun i => by
    rw [hQs i]; exact commutator_comap_perfect hΦs hΦk (hperfF i)
  have hQcomp : ∀ i, IsComponent (Qs i) := fun i => by
    rw [hQs i]
    exact ⟨isQuasisimple_commutator_comap hΦs hΦk (hcomp i).1,
      isSubnormal_commutator_comap (hcomp i).2⟩
  have hQle : ∀ i, Qs i ≤ (F' i).comap Φ := fun i => by
    rw [hQs i]; exact commutator_self_le _
  refine ⟨fun i => (Qs i).map Hs.subtype, fun i => Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have : ((Qs i).map Hs.subtype).subgroupOf Hs = Qs i :=
      Subgroup.comap_map_eq_self_of_injective Hs.subtype_injective _
    rw [this]
    exact hQcomp i
  · intro Y hY hYp
    have hperfY' : ⁅Y.subgroupOf Hs, Y.subgroupOf Hs⁆ = Y.subgroupOf Hs := by
      have : Group.IsPerfect ↥Y := hYp
      have : Group.IsPerfect ↥(Y.subgroupOf Hs) :=
        Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hY).symm.toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hY).symm.surjective
      exact Subgroup.isPerfect_iff.1 this
    have hle : (Y.subgroupOf Hs).map Φ ≤ ⨆ i, F' i :=
      hperf _ (by rw [← Subgroup.map_commutator, hperfY'])
    have h2 := le_iSup_of_isPerfect_of_map_le hΦk (Q := Qs) (F := F') hQF hperfY' hle
    calc Y = (Y.subgroupOf Hs).map Hs.subtype := (Subgroup.map_subgroupOf_eq_of_le hY).symm
      _ ≤ (⨆ i, Qs i).map Hs.subtype := Subgroup.map_mono h2
      _ = ⨆ i, (Qs i).map Hs.subtype := Subgroup.map_iSup _ _
  · intro i hdvd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hu1 : (u : G) ∈ (Qs i).map Hs.subtype := u.2.1
    have hu2 : (u : G) ∈ Subgroup.centralizer (((Qs i).map Hs.subtype : Subgroup G) : Set G) :=
      u.2.2
    obtain ⟨u', hu'Q, hu'⟩ := hu1
    have hup : u' ^ p = 1 := by
      apply Hs.subtype_injective
      rw [map_pow, hu', map_one]
      have := pow_orderOf_eq_one u
      rw [hu] at this
      exact congrArg Subtype.val this
    have hcomm : ∀ f ∈ Qs i, u' * f = f * u' := by
      intro f hf
      apply Hs.subtype_injective
      rw [map_mul, map_mul, hu']
      exact (Subgroup.mem_centralizer_iff.mp hu2 (f : G) (Subgroup.mem_map_of_mem _ hf)).symm
    have hΦu : Φ u' = 1 := by
      refine hcen i (Φ u') (hQF i ▸ Subgroup.mem_map_of_mem Φ hu'Q) (fun f' hf' => ?_)
        (by rw [← map_pow, hup, map_one])
      obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp (hQF i ▸ hf')
      rw [← map_mul, hcomm f hf, map_mul]
    have hu'k : u' ∈ Φ.ker := hΦu
    have h1 : (⟨u', hu'k⟩ : Φ.ker) = 1 :=
      eq_one_of_pow_eq_one_of_not_dvd_card hp hΦn (Subtype.ext (by simpa using hup))
    have h2 : u' = 1 := congrArg Subtype.val h1
    have h3 : u = 1 := Subtype.ext (by rw [← hu', h2]; rfl)
    rw [h3, orderOf_one] at hu
    exact hp.one_lt.ne hu
  · intro i
    have h1 : SylAb p (Qs i) := SylAb.of_cover hp Φ hΦn (by rw [hQF i]; exact hsyl i)
    exact SylAb.map_of_injOn Hs.subtype (fun x _ y _ hxy => Subtype.ext hxy) h1
  · intro i e τ hτ x hx hcompat
    obtain ⟨x', hx'Q, hx'⟩ := exists_inner_of_map_eq_conj hΦk (hQperf i) (hQF i) τ hx
      (fun y hy => hcompat y (hQF i ▸ Subgroup.mem_map_of_mem Φ hy))
    refine ⟨(x' : G), Subgroup.mem_map_of_mem _ hx'Q, (x' : G)⁻¹ * e, ?_, by group⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u', hu'Q, rfl⟩
    have h1 : ((τ u' : ↥Hs) : G) = (x' : G) * u' * (x' : G)⁻¹ := by
      have := congrArg (fun z : ↥Hs => (z : G)) (hx' u' hu'Q)
      simpa using this
    rw [hτ u'] at h1
    change (u' : G) * ((x' : G)⁻¹ * e) = ((x' : G)⁻¹ * e) * (u' : G)
    calc (u' : G) * ((x' : G)⁻¹ * e) = (x' : G)⁻¹ * ((x' : G) * u' * (x' : G)⁻¹) * e := by group
      _ = (x' : G)⁻¹ * (e * u' * e⁻¹) * e := by rw [h1]
      _ = ((x' : G)⁻¹ * e) * (u' : G) := by group


theorem layerDataWS_of_autFamily {p : ℕ} (hp : p.Prime) {E I : Subgroup G} {P : Type} [Group P]
    (e₀ : ↥I ⧸ Subgroup.center ↥I ≃* P) (hEI : E ≤ Subgroup.normalizer (I : Set G))
    (hEexp : ∀ x ∈ E, x ^ p = 1) (hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥I)) (act : ↥E →* MulAut P)
    (hact : ∀ (x : ↥E) (y : ↥I), act x (e₀ (y : ↥I ⧸ Subgroup.center ↥I)) =
      e₀ ((I.normalizerMonoidHom ⟨(x : G), hEI x.2⟩ y : ↥I) : ↥I ⧸ Subgroup.center ↥I))
    (hfam : ∀ b : ↥E, b ≠ 1 → ∃ (ι : Type) (F : ι → Subgroup P),
      AutLayerFamily p (act b) (Set.range act) F ∧ ∀ i, SylAb p (F i)) :
    LayerDataWS p E I := by
  classical
  intro b hb hb1
  obtain ⟨ι, F, hF, hFs⟩ := hfam ⟨b, hb⟩ (fun h => hb1 (congrArg Subtype.val h))
  obtain ⟨Φ, hΦs, hΦk, hΦn, hΦv⟩ := exists_cover hp e₀ hEI hZ hb (hEexp b hb) (act ⟨b, hb⟩)
    (fun y => hact ⟨b, hb⟩ y)
  have hperf : ∀ Y : Subgroup ↥(fixedSub (act ⟨b, hb⟩)), ⁅Y, Y⁆ = Y →
      Y ≤ ⨆ i, (F i).subgroupOf (fixedSub (act ⟨b, hb⟩)) := by
    intro Y hY
    have h1 : Y.map (fixedSub (act ⟨b, hb⟩)).subtype ≤ ⨆ i, F i := by
      refine hF.perfect _ (Subgroup.map_subtype_le _) (Subgroup.isPerfect_iff.2 ?_)
      rw [← Subgroup.map_commutator, hY]
    have hmapF : (⨆ i, (F i).subgroupOf (fixedSub (act ⟨b, hb⟩))).map
        (fixedSub (act ⟨b, hb⟩)).subtype = ⨆ i, F i := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun i => Subgroup.map_subgroupOf_eq_of_le (hF.le i)
    rw [← Subgroup.map_le_map_iff_of_injective (fixedSub (act ⟨b, hb⟩)).subtype_injective, hmapF]
    exact h1
  have hcen : ∀ i, ∀ u ∈ (F i).subgroupOf (fixedSub (act ⟨b, hb⟩)),
      (∀ f ∈ (F i).subgroupOf (fixedSub (act ⟨b, hb⟩)), u * f = f * u) → u ^ p = 1 → u = 1 := by
    intro i u hu hc hup
    apply Subtype.ext
    have := hF.center i (u : P) hu (fun f hf => congrArg Subtype.val (hc ⟨f, hF.le i hf⟩ hf))
      (by simpa using congrArg Subtype.val hup)
    simpa using this
  have hsyl' : ∀ i, SylAb p ((F i).subgroupOf (fixedSub (act ⟨b, hb⟩))) := fun i =>
    SylAb.of_map (fixedSub (act ⟨b, hb⟩)).subtype
      (fun t _ _ ht => Subtype.ext (by simpa using ht))
      (by rw [Subgroup.map_subgroupOf_eq_of_le (hF.le i)]; exact hFs i)
  obtain ⟨Q, hQle, hQcomp, hQperf, hQcen, hQsyl, hQinner⟩ := exists_components_of_cover_syl hp Φ hΦs hΦk hΦn
    (fun i => (F i).subgroupOf (fixedSub (act ⟨b, hb⟩))) (fun i => hF.comp i) hperf hcen hsyl'
  refine ⟨ι, Q, hQle, hQcomp, hQperf, fun i => ⟨?_, hQcen i⟩, hQsyl⟩
  intro e he
  obtain ⟨τ, hτ⟩ := exists_conj_hom hEI hEcomm hb he
  obtain ⟨x₀, hx₀F, hx₀⟩ := hF.inner (act ⟨e, he⟩) ⟨⟨e, he⟩, rfl⟩ i
  refine hQinner i e τ hτ ⟨x₀, hF.le i hx₀F⟩ hx₀F ?_
  intro y hy
  apply Subtype.ext
  have h1 : (⟨((τ y : _) : G), (τ y).2.1⟩ : ↥I) =
      I.normalizerMonoidHom ⟨e, hEI he⟩ ⟨(y : G), y.2.1⟩ := by
    apply Subtype.ext
    rw [hτ y]
    exact (Subgroup.normalizerMonoidHom_apply_apply_coe I ⟨e, hEI he⟩ ⟨(y : G), y.2.1⟩).symm
  have h2 := hact ⟨e, he⟩ ⟨(y : G), y.2.1⟩
  rw [← h1, ← hΦv y] at h2
  have h3 : ((Φ (τ y) : ↥(fixedSub (act ⟨b, hb⟩))) : P) = act ⟨e, he⟩ ((Φ y : _) : P) := by
    rw [hΦv (τ y), h2]
  rw [h3]
  exact hx₀ _ hy


end CFSG.RankThree.PartOne.K159R5
