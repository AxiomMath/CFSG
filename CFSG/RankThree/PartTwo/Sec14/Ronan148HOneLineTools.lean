module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148HYd
import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONTwoRank
import CFSG.RankThree.GroupTheory.CentralLineComponentAction
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAReciprocalFusion
public import CFSG.LocalAnalysis.SignalizerFunctor.ElementaryComplements
public import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.Walter.TwoRank

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148H

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank
open scoped Pointwise

theorem range_comp_subtype {G H : Type*} [Group G] [Group H] (f : G →* H) (K : Subgroup G) :
    (f.comp K.subtype).range = K.map f := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype]

section TwoRank


theorem card_le_eight_of_isTripleCover {X : Type} [Group X] [Finite X]
    (hT : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) (E : Subgroup X)
    (hE : CFSG.Assembly.IsElemAbelian 2 E) : Nat.card E ≤ 8 := by
  obtain ⟨hZ, ⟨e⟩⟩ := hT
  set π : X →* CFSG.Blueprint.NativeSporadic.ON :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X)) with hπ
  have hker : ∀ x ∈ E, π x = 1 → x = 1 := by
    intro x hx h1
    have hxZ : x ∈ Subgroup.center X := by
      have : QuotientGroup.mk' (Subgroup.center X) x = 1 := e.injective (by
        rw [map_one]; exact h1)
      exact (QuotientGroup.eq_one_iff x).mp this
    have h3 : x ^ 3 = 1 := by
      have := orderOf_dvd_natCard (⟨x, hxZ⟩ : Subgroup.center X)
      rw [hZ, Subgroup.orderOf_mk] at this
      exact orderOf_dvd_iff_pow_eq_one.mp this
    have h2 : x ^ 2 = 1 := hE.2 x hx
    have : x = x ^ 3 * (x ^ 2)⁻¹ := by group
    rw [this, h3, h2, inv_one, one_mul]
  have hinj : Function.Injective (π.comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hker x x.2 hx)
  have hcard : Nat.card (E.map π) = Nat.card E := by
    rw [← range_comp_subtype, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
  have hEmap : CFSG.Assembly.IsElemAbelian 2 (E.map π) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp x.2
      obtain ⟨v, hv, hvy⟩ := Subgroup.mem_map.mp y.2
      apply Subtype.ext
      change (x : CFSG.Blueprint.NativeSporadic.ON) * y = y * x
      rw [← hux, ← hvy, ← map_mul, ← map_mul]
      exact congrArg π (congrArg Subtype.val (hE.1.is_comm.comm (⟨u, hu⟩ : E) ⟨v, hv⟩))
    · obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
      rw [← map_pow, hE.2 u hu, map_one]
  rw [← hcard]
  exact CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONTwoRank.card_le_eight_of_isElemAbelian_ON
    _ hEmap

end TwoRank

theorem exists_elemAbelian_card_four_of_two_le_twoRank {G : Type*} [Group G] [Finite G]
    (h : 2 ≤ CFSG.Open.twoRank G) :
    ∃ V : Subgroup G, CFSG.Assembly.IsElemAbelian 2 V ∧ Nat.card V = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S : Set ℕ := {k | ∃ E : Subgroup G, E ≤ ⊤ ∧ CFSG.Open.IsElemAbelian 2 E ∧
    Nat.card E = 2 ^ k} with hS
  have hne : S.Nonempty :=
    ⟨0, ⊥, le_top, ⟨inferInstance, fun x hx => by rw [(Subgroup.mem_bot).1 hx, one_pow]⟩,
      by simp⟩
  have hbdd : BddAbove S := by
    refine ⟨Nat.card G, ?_⟩
    rintro k' ⟨E', -, -, hk'⟩
    have h1 : 2 ^ k' ≤ Nat.card G := hk' ▸ Subgroup.card_le_card_group E'
    exact (Nat.lt_pow_self (by norm_num : 1 < 2)).le.trans h1
  obtain ⟨E, -, hE, hk⟩ := Nat.sSup_mem hne hbdd
  have hdvd : 2 ^ 2 ∣ Nat.card E := by
    rw [hk]
    exact Nat.pow_dvd_pow 2 h
  obtain ⟨V, hV⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  refine ⟨V.map E.subtype, ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨u, -, hux⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨v, -, hvy⟩ := Subgroup.mem_map.mp y.2
    apply Subtype.ext
    change (x : G) * y = y * x
    rw [← hux, ← hvy]
    exact congrArg Subtype.val (hE.1.is_comm.comm u v)
  · obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hx
    exact hE.2 u u.2
  · rw [Subgroup.card_map_of_injective E.subtype_injective, hV]
    rfl

theorem exists_elemAbelian_four_of_isQuasisimple {K : Type} [Group K] [Finite K]
    (hK : IsQuasisimple K) (hodd : Odd (Nat.card (Subgroup.center K))) :
    ∃ V : Subgroup K, CFSG.Assembly.IsElemAbelian 2 V ∧ Nat.card V = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hsimple, hnab⟩ := hK
  set Z := Subgroup.center K with hZdef
  have heven : Even (Nat.card (K ⧸ Z)) := by
    by_contra hne
    have hsol := CFSG.Milestones.odd_order_solvable (Nat.not_even_iff_odd.mp hne)
    obtain ⟨a, b, hab⟩ := hnab
    exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := K ⧸ Z)).mpr hsol a b)
  obtain ⟨W, hW, hW4⟩ :=
    exists_elemAbelian_card_four_of_two_le_twoRank (CFSG.Walter.two_le_twoRank (K ⧸ Z) hnab heven)
  set π := QuotientGroup.mk' Z with hπ
  set T := W.comap π with hT
  have hZT : Z ≤ T := fun z hz => by
    have h1 : π z = 1 := by
      rw [hπ, QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff z).mpr hz
    show π z ∈ W
    rw [h1]
    exact W.one_mem
  set f : T →* W := (π.comp T.subtype).codRestrict W (fun t => t.2) with hf
  have hfs : Function.Surjective f := by
    rintro ⟨w, hw⟩
    obtain ⟨k, rfl⟩ := QuotientGroup.mk'_surjective Z w
    exact ⟨⟨k, hw⟩, rfl⟩
  have hfker : ∀ t : T, f t = 1 ↔ (t : K) ∈ Z := by
    intro t
    constructor
    · intro h
      exact (QuotientGroup.eq_one_iff (t : K)).mp (congrArg Subtype.val h)
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff (t : K)).mpr h)
  have hker : f.ker = Z.subgroupOf T := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hfker t
  have hcardT : Nat.card T = Nat.card Z * 4 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hfs).toEquiv, hW4, hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZT).toEquiv, mul_comm]
  obtain ⟨R⟩ : Nonempty (Sylow 2 T) := inferInstance
  have hfac : (Nat.card T).factorization 2 = 2 := by
    rw [hcardT, Nat.factorization_mul (Nat.card_pos.ne') (by norm_num),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd (fun h2 =>
        (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2))]
    rw [show (4 : ℕ) = 2 ^ 2 from rfl, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hR4 : Nat.card (R : Subgroup T) = 4 := by
    rw [Sylow.card_eq_multiplicity, hfac]
    rfl
  have hRinj : Function.Injective (f.comp (R : Subgroup T).subtype) := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have hrZ : ((r : T) : K) ∈ Z := (hfker r).mp hr
    have hr2 : IsPGroup 2 (R : Subgroup T) := R.isPGroup'
    obtain ⟨n, hn⟩ := hr2 r
    have hz : orderOf (((r : T) : K)) ∣ 2 ^ n := by
      apply orderOf_dvd_of_pow_eq_one
      have := congrArg (fun s : (R : Subgroup T) => ((s : T) : K)) hn
      simpa using this
    have hzodd : orderOf (⟨((r : T) : K), hrZ⟩ : Z) ∣ Nat.card Z := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk] at hzodd
    have hco : Nat.Coprime (orderOf (((r : T) : K))) 2 := by
      have hZ2 : Nat.Coprime (Nat.card Z) 2 :=
        Nat.coprime_two_right.mpr hodd
      exact Nat.Coprime.coprime_dvd_left hzodd hZ2
    have h1 : orderOf (((r : T) : K)) = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right n hco) hz
    apply Subtype.ext
    apply Subtype.ext
    exact orderOf_eq_one_iff.mp h1
  have hRW : Nat.card ((R : Subgroup T).map f) = 4 := by
    rw [← range_comp_subtype,
      Nat.card_congr (MonoidHom.ofInjective hRinj).toEquiv.symm, hR4]
  refine ⟨(R : Subgroup T).map T.subtype, ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp x.2
    obtain ⟨v, hv, hvy⟩ := Subgroup.mem_map.mp y.2
    apply Subtype.ext
    change (x : K) * y = y * x
    rw [← hux, ← hvy]
    have hc : f u * f v = f v * f u := by
      have := hW.1.is_comm.comm (f u) (f v)
      exact this
    have : (⟨u, hu⟩ : (R : Subgroup T)) * ⟨v, hv⟩ = ⟨v, hv⟩ * ⟨u, hu⟩ := by
      apply hRinj
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_mul, Subgroup.coe_mul]
      exact hc
    exact congrArg (fun s : (R : Subgroup T) => ((s : T) : K)) this
  · obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    have h2 : (f u) ^ 2 = 1 := hW.2 (f u) (f u).2 |> fun h => Subtype.ext (by simpa using h)
    have : (⟨u, hu⟩ : (R : Subgroup T)) ^ 2 = 1 := by
      apply hRinj
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, map_pow, Subgroup.coe_pow, map_one]
      exact h2
    have := congrArg (fun s : (R : Subgroup T) => ((s : T) : K)) this
    simpa using this
  · rw [Subgroup.card_map_of_injective T.subtype_injective, hR4]

theorem eq_of_mem_thetaComponents {H : Type} [Group H] [Finite H]
    (hθ : aschbacherSolvableCore 3 H = ⊥)
    (h8 : ∀ E : Subgroup H, CFSG.Assembly.IsElemAbelian 2 E → Nat.card E ≤ 8)
    {L₁ L₂ : Subgroup H} (h₁ : L₁ ∈ thetaComponents 3 H) (h₂ : L₂ ∈ thetaComponents 3 H) :
    L₁ = L₂ := by
  by_contra hne
  set N := aschbacherSolvableCore 3 H with hN
  set ρ := QuotientGroup.mk' N with hρ
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := H) Nat.prime_three
  set K₁ := L₁.map ρ with hK₁def
  set K₂ := L₂.map ρ with hK₂def
  have hK₁ : IsComponent K₁ := hbij.mapsTo h₁
  have hK₂ : IsComponent K₂ := hbij.mapsTo h₂
  have hKne : K₁ ≠ K₂ := fun h => hne (hbij.injOn h₁ h₂ h)
  have hθq : aschbacherSolvableCore 3 (H ⧸ N) = ⊥ := theta_thetaQuot_eq_bot
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxN : x ∈ N := (QuotientGroup.eq_one_iff x).mp hx
    rw [hθ] at hxN
    exact (Subgroup.mem_bot).mp hxN
  have hodd : ∀ K : Subgroup (H ⧸ N), IsComponent K → Odd (Nat.card (Subgroup.center K)) := by
    intro K hK
    have hle := center_component_le_pCore Nat.prime_three hθq hK
    have hp3 : IsPGroup 3 ((Subgroup.center K).map K.subtype) :=
      (CFSG.pCore_isPGroup (p := 3) (G := H ⧸ N)).to_le hle
    have hp3' : IsPGroup 3 (Subgroup.center K) :=
      hp3.of_equiv (Subgroup.equivMapOfInjective _ _ K.subtype_injective).symm
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := hp3'.exists_card_eq
    rw [hn]
    exact Odd.pow (by decide)
  obtain ⟨V₁, hV₁, hV₁4⟩ := exists_elemAbelian_four_of_isQuasisimple hK₁.1 (hodd _ hK₁)
  obtain ⟨V₂, hV₂, hV₂4⟩ := exists_elemAbelian_four_of_isQuasisimple hK₂.1 (hodd _ hK₂)
  set W₁ := V₁.map K₁.subtype with hW₁
  set W₂ := V₂.map K₂.subtype with hW₂
  have hcomm : ⁅K₁, K₂⁆ = ⊥ := by
    rcases CFSG.LocalCores.distinct_components_commute hK₁ hK₂ with h | h
    · exact absurd h hKne
    · exact h
  have hW₁W₂ : ∀ x ∈ W₁, ∀ y ∈ W₂, x * y = y * x := by
    intro x hx y hy
    have hxK : x ∈ K₁ := (Subgroup.map_subtype_le _) hx
    have hyK : y ∈ K₂ := (Subgroup.map_subtype_le _) hy
    have := Subgroup.commutator_mem_commutator hxK hyK
    rw [hcomm, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hab₁ : ∀ x ∈ W₁, ∀ y ∈ W₁, x * y = y * x := by
    intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
    exact congrArg Subtype.val (congrArg Subtype.val (hV₁.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩))
  have hab₂ : ∀ x ∈ W₂, ∀ y ∈ W₂, x * y = y * x := by
    intro x hx y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hy
    exact congrArg Subtype.val (congrArg Subtype.val (hV₂.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩))
  have hsq₁ : ∀ x ∈ W₁, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hV₁.2 u hu, map_one]
  have hsq₂ : ∀ x ∈ W₂, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    rw [← map_pow, hV₂.2 u hu, map_one]
  have hW₂n : W₂ ≤ Subgroup.normalizer (W₁ : Set (H ⧸ N)) := by
    refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hW₁W₂ x hx y hy
  have hdisj : Disjoint W₁ W₂ := by
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hx₁, hx₂⟩
    rw [Subgroup.mem_bot]
    have hxK₁ : x ∈ K₁ := (Subgroup.map_subtype_le _) hx₁
    have hxK₂ : x ∈ K₂ := (Subgroup.map_subtype_le _) hx₂
    have hxZ : (⟨x, hxK₁⟩ : K₁) ∈ Subgroup.center K₁ := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      have := Subgroup.commutator_mem_commutator g.2 hxK₂
      rw [hcomm, Subgroup.mem_bot] at this
      exact commutatorElement_eq_one_iff_mul_comm.mp this
    have hdvd := orderOf_dvd_natCard (⟨⟨x, hxK₁⟩, hxZ⟩ : Subgroup.center K₁)
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk] at hdvd
    have h2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (hsq₁ x hx₁)
    have hco : Nat.Coprime (orderOf x) 2 :=
      Nat.Coprime.coprime_dvd_left hdvd (Nat.coprime_two_right.mpr (hodd _ hK₁))
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hco h2)
  have hmem : ∀ z ∈ W₁ ⊔ W₂, ∃ a ∈ W₁, ∃ b ∈ W₂, a * b = z := by
    intro z hz
    have hz' : z ∈ ((W₁ : Set (H ⧸ N)) * (W₂ : Set (H ⧸ N))) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left W₁ W₂ hW₂n]
      exact hz
    obtain ⟨a, ha, b, hb, hab⟩ := hz'
    exact ⟨a, ha, b, hb, hab⟩
  have hE : CFSG.Assembly.IsElemAbelian 2 (W₁ ⊔ W₂) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun z hz => ?_⟩
    · obtain ⟨a, ha, b, hb, hx⟩ := hmem x x.2
      obtain ⟨a', ha', b', hb', hy⟩ := hmem y y.2
      apply Subtype.ext
      change (x : H ⧸ N) * y = y * x
      rw [← hx, ← hy]
      calc a * b * (a' * b') = a * (b * a') * b' := by group
        _ = a * (a' * b) * b' := by rw [← hW₁W₂ a' ha' b hb]
        _ = (a * a') * (b * b') := by group
        _ = (a' * a) * (b' * b) := by rw [hab₁ a ha a' ha', hab₂ b hb b' hb']
        _ = a' * (a * b') * b := by group
        _ = a' * (b' * a) * b := by rw [hW₁W₂ a ha b' hb']
        _ = a' * b' * (a * b) := by group
    · obtain ⟨a, ha, b, hb, rfl⟩ := hmem z hz
      calc (a * b) ^ 2 = a * (b * a) * b := by rw [sq]; simp only [mul_assoc]
        _ = a * (a * b) * b := by rw [hW₁W₂ a ha b hb]
        _ = a ^ 2 * b ^ 2 := by rw [sq, sq]; simp only [mul_assoc]
        _ = 1 := by rw [hsq₁ a ha, hsq₂ b hb, one_mul]
  have hEcard : Nat.card (W₁ ⊔ W₂ : Subgroup (H ⧸ N)) = 16 := by
    rw [CFSG.ComponentClassification.UnbalancedGS.ReciprocalFusion.card_sup_eq_mul_of_disjoint
      W₁ W₂ hW₂n hdisj, hW₁, hW₂, Subgroup.card_map_of_injective K₁.subtype_injective,
      Subgroup.card_map_of_injective K₂.subtype_injective, hV₁4, hV₂4]
  set E : Subgroup H := (W₁ ⊔ W₂).comap ρ with hEdef
  have hEmap : E.map ρ = W₁ ⊔ W₂ :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective N) _
  have hE' : CFSG.Assembly.IsElemAbelian 2 E := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hρinj ?_)⟩⟩, fun x hx => hρinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact congrArg Subtype.val (hE.1.is_comm.comm ⟨ρ x, x.2⟩ ⟨ρ y, y.2⟩)
    · rw [map_pow, map_one]
      exact hE.2 (ρ x) hx
  have hcardE : Nat.card E = 16 := by
    rw [← Subgroup.card_map_of_injective hρinj, hEmap, hEcard]
  have := h8 E hE'
  omega

section Sup

variable {X : Type*} [Group X] [Finite X]

theorem exists_mul_of_mem_sup {Y P : Subgroup X} (hPY : P ≤ Subgroup.normalizer (Y : Set X))
    {g : X} (hg : g ∈ Y ⊔ P) : ∃ y ∈ Y, ∃ p ∈ P, y * p = g := by
  have : g ∈ ((Y : Set X) * (P : Set X)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left Y P hPY]
    exact hg
  obtain ⟨y, hy, p, hp, h⟩ := this
  exact ⟨y, hy, p, hp, h⟩

theorem normal_subgroupOf_sup {Y P : Subgroup X} (hPY : P ≤ Subgroup.normalizer (Y : Set X)) :
    (Y.subgroupOf (Y ⊔ P)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le Subgroup.le_normalizer hPY)

theorem isPGroup_quotient_sup {Y P : Subgroup X} (hPY : P ≤ Subgroup.normalizer (Y : Set X))
    (hP : IsPGroup 3 P) :
    haveI := normal_subgroupOf_sup hPY
    IsPGroup 3 (↥(Y ⊔ P) ⧸ Y.subgroupOf (Y ⊔ P)) := by
  haveI := normal_subgroupOf_sup hPY
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨y, hy, p, hp, hyp⟩ := exists_mul_of_mem_sup hPY g.2
  obtain ⟨n, hn⟩ := hP ⟨p, hp⟩
  refine ⟨n, ?_⟩
  have hg : g = (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ P)) * ⟨p, Subgroup.mem_sup_right hp⟩ :=
    Subtype.ext hyp.symm
  have hy1 : (QuotientGroup.mk (⟨y, Subgroup.mem_sup_left hy⟩ : ↥(Y ⊔ P)) :
      ↥(Y ⊔ P) ⧸ Y.subgroupOf (Y ⊔ P)) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hy
  have hp1 : (⟨p, Subgroup.mem_sup_right hp⟩ : ↥(Y ⊔ P)) ^ 3 ^ n = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hn
    simpa using this
  rw [hg, QuotientGroup.mk_mul, hy1, one_mul, ← QuotientGroup.mk_pow, hp1, QuotientGroup.mk_one]

theorem le_of_le_sup_of_not_dvd {Y P S : Subgroup X} (hPY : P ≤ Subgroup.normalizer (Y : Set X))
    (hP : IsPGroup 3 P) (hS : S ≤ Y ⊔ P) (hS3 : ¬ 3 ∣ Nat.card S) : S ≤ Y := by
  haveI := normal_subgroupOf_sup hPY
  have hq := isPGroup_quotient_sup hPY hP
  intro s hs
  set s' : ↥(Y ⊔ P) := ⟨s, hS hs⟩ with hs'
  set π := QuotientGroup.mk' (Y.subgroupOf (Y ⊔ P)) with hπ
  have hos : orderOf s ∣ Nat.card S := by
    have := orderOf_dvd_natCard (⟨s, hs⟩ : S)
    rwa [Subgroup.orderOf_mk] at this
  have hco : Nat.Coprime (orderOf (π s')) 3 := by
    have h1 : orderOf (π s') ∣ orderOf s' := orderOf_map_dvd π s'
    have h2 : orderOf s' = orderOf s := Subgroup.orderOf_mk s (hS hs)
    rw [h2] at h1
    exact (Nat.Coprime.coprime_dvd_left (h1.trans hos)
      ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hS3))))
  obtain ⟨n, hn⟩ := hq (π s')
  have hdvd : orderOf (π s') ∣ 3 ^ n := orderOf_dvd_of_pow_eq_one hn
  have h1 : π s' = 1 :=
    orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right n hco) hdvd)
  have : s' ∈ Y.subgroupOf (Y ⊔ P) := (QuotientGroup.eq_one_iff s').mp h1
  exact this

theorem le_of_le_sup_of_isPerfect {Y P S : Subgroup X} (hPY : P ≤ Subgroup.normalizer (Y : Set X))
    (hP : IsPGroup 3 P) (hS : S ≤ Y ⊔ P) (hSp : Group.IsPerfect S) : S ≤ Y := by
  haveI := normal_subgroupOf_sup hPY
  have hq := isPGroup_quotient_sup hPY hP
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set π := QuotientGroup.mk' (Y.subgroupOf (Y ⊔ P)) with hπ
  set S' := S.subgroupOf (Y ⊔ P) with hS'
  have hS'p : Group.IsPerfect S' :=
    isPerfect_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hS).symm hSp
  have hTp : Group.IsPerfect (S'.map π) := by
    have := hS'p
    exact Group.IsPerfect.ofSurjective (f := π.subgroupMap S') (π.subgroupMap_surjective S')
  have hsol : Group.IsSolvable (S'.map π) := by
    have : Group.IsNilpotent (↥(Y ⊔ P) ⧸ Y.subgroupOf (Y ⊔ P)) := hq.isNilpotent
    infer_instance
  have hbot : S'.map π = ⊥ := by
    by_contra hne
    have : Nontrivial (S'.map π) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isSolvable _ hsol
  intro s hs
  have hmem : π ⟨s, hS hs⟩ ∈ S'.map π := ⟨⟨s, hS hs⟩, hs, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have := (QuotientGroup.eq_one_iff (N := Y.subgroupOf (Y ⊔ P))
    (⟨s, hS hs⟩ : ↥(Y ⊔ P))).mp hmem
  exact this

end Sup

theorem exists_complement_of_isE27 {X : Type*} [Group X] {P Z : Subgroup X} (hP : Late.IsE27 P)
    (hZP : Z ≤ P) : ∃ B : Subgroup X, B ≤ P ∧ B ⊓ Z = ⊥ ∧ B ⊔ Z = P := by
  have hc : ∀ x y : P, x * y = y * x := fun x y => hP.1.1.is_comm.comm x y
  let _ : CommGroup P := { (inferInstance : Group P) with mul_comm := hc }
  obtain ⟨C, hC⟩ := CFSG.SignalizerFunctor.Helpers.elementary_abelian_isCompl_exists 3
    Nat.prime_three P (fun x => Subtype.ext (by simpa using hP.1.2 x x.2)) (Z.subgroupOf P)
  refine ⟨C.map P.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxC, hxZ⟩
    obtain ⟨c, hcC, rfl⟩ := Subgroup.mem_map.mp hxC
    have hcZ : c ∈ Z.subgroupOf P := hxZ
    have : c ∈ Z.subgroupOf P ⊓ C := ⟨hcZ, hcC⟩
    rw [hC.disjoint.eq_bot, Subgroup.mem_bot] at this
    rw [this, map_one]
    exact Subgroup.one_mem _
  · have h := congrArg (Subgroup.map P.subtype) hC.sup_eq_top
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZP,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    rw [sup_comm]
    exact h

end CFSG.RankThree.PartTwo.Sec14.Ronan148H
