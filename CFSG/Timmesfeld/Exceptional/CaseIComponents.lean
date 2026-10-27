module

public import CFSG.Timmesfeld.Exceptional.CaseIConnected

public section

namespace CFSG.Timmesfeld.Moufang

variable {G : Type*} [Group G] {D : Set G}

@[expose] def CollStep (D : Set G) (a b : G) : Prop :=
  a ∈ D ∧ b ∈ D ∧ Commute a b ∧ a * b ∈ D

theorem CollStep.symm {a b : G} (h : CollStep D a b) : CollStep D b a :=
  ⟨h.2.1, h.1, h.2.2.1.symm, by rw [← h.2.2.1.eq]; exact h.2.2.2⟩

@[expose] def CollComp (D : Set G) (a b : G) : Prop :=
  Relation.ReflTransGen (CollStep D) a b

namespace CollComp

theorem refl (D : Set G) (a : G) : CollComp D a a :=
  Relation.ReflTransGen.refl

theorem single {a b : G} (h : CollStep D a b) : CollComp D a b :=
  Relation.ReflTransGen.single h

theorem tail {a b c : G} (h : CollComp D a b) (h' : CollStep D b c) : CollComp D a c :=
  Relation.ReflTransGen.tail h h'

theorem trans {a b c : G} (h : CollComp D a b) (h' : CollComp D b c) : CollComp D a c :=
  Relation.ReflTransGen.trans h h'

theorem symm {a b : G} (h : CollComp D a b) : CollComp D b a := by
  unfold CollComp at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact Relation.ReflTransGen.head hbc.symm ih

theorem mem {a b : G} (ha : a ∈ D) (h : CollComp D a b) : b ∈ D := by
  unfold CollComp at h
  induction h with
  | refl => exact ha
  | tail _ hbc _ => exact hbc.2.1

theorem conj (hconj : ∀ g x : G, x ∈ D → g * x * g⁻¹ ∈ D) (g : G) {a b : G}
    (h : CollComp D a b) : CollComp D (g * a * g⁻¹) (g * b * g⁻¹) := by
  unfold CollComp at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail b' c' _ hbc ih =>
    refine ih.tail ⟨hconj g b' hbc.1, hconj g c' hbc.2.1, ?_, ?_⟩
    · show g * b' * g⁻¹ * (g * c' * g⁻¹) = g * c' * g⁻¹ * (g * b' * g⁻¹)
      rw [show g * b' * g⁻¹ * (g * c' * g⁻¹) = g * (b' * c') * g⁻¹ by group, hbc.2.2.1.eq]
      group
    · rw [show g * b' * g⁻¹ * (g * c' * g⁻¹) = g * (b' * c') * g⁻¹ by group]
      exact hconj g _ hbc.2.2.2

end CollComp

theorem collStep_sq_of_orderOf_eq_four (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d e : G} (hd : d ∈ D) (he : e ∈ D)
    (h4 : orderOf (d * e) = 4) : CollStep D d ((d * e) ^ 2) := by
  obtain ⟨hz, hdz, -, -⟩ := sq_mem_of_orderOf_eq_four hD hd he h4
  exact ⟨hd, hz, hdz, mul_sq_mem_of_orderOf_eq_four hclass hD hd he h4⟩

theorem collComp_of_orderOf_eq_four (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {d e : G} (hd : d ∈ D) (he : e ∈ D)
    (h4 : orderOf (d * e) = 4) : CollComp D d e := by
  have h4' : orderOf (e * d) = 4 := by rw [orderOf_mul_comm_eq]; exact h4
  have h2 := collStep_sq_of_orderOf_eq_four hclass hD he hd h4'
  rw [Bridge.mul_sq_comm_of_orderOf_eq_four hD hd he h4] at h2
  exact (CollComp.single (collStep_sq_of_orderOf_eq_four hclass hD hd he h4)).tail h2.symm

theorem commute_of_collStep (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {x c c' : G} (hx : x ∈ D) (hst : CollStep D c c')
    (hxc : Commute x c) (hnc : ¬ CollComp D c x) : Commute x c' := by
  have hconj : ∀ g y : G, y ∈ D → g * y * g⁻¹ ∈ D := fun g y hy =>
    conj_mem_of_isClass hclass g hy
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hx hst.2.1 with h | h4 | ⟨hodd, -⟩
  · exact h
  · have h4' : orderOf (c' * x) = 4 := by rw [orderOf_mul_comm_eq]; exact h4
    exact absurd ((CollComp.single hst).trans
      (collComp_of_orderOf_eq_four hclass hD hst.2.1 hx h4')) hnc
  · have hodd' : Odd (orderOf (c' * x)) := by rw [orderOf_mul_comm_eq]; exact hodd
    obtain ⟨g, hg, hgc⟩ := exists_conj_of_odd_orderOf_mul (hD.mul_self_eq_one hst.2.1)
      (hD.mul_self_eq_one hx) hodd'
    have hle : Subgroup.closure ({c', x} : Set G) ≤ Subgroup.centralizer {c} := by
      rw [Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      rcases hy with rfl | hy
      · exact hst.2.2.1.eq
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact hxc.symm.eq
    have hcg : c * g = g * c := Subgroup.mem_centralizer_iff.1 (hle hg) c rfl
    have h := CollComp.conj hconj g (CollComp.single hst)
    rw [hgc, show g * c * g⁻¹ = c by rw [← hcg, mul_inv_cancel_right]] at h
    exact absurd h hnc

theorem commute_of_collComp (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) {x c c' : G} (hx : x ∈ D) (hcc' : CollComp D c c')
    (hxc : Commute x c) (hnc : ¬ CollComp D c x) : Commute x c' := by
  unfold CollComp at hcc'
  induction hcc' with
  | refl => exact hxc
  | tail hab hbc ih => exact commute_of_collStep hclass hD hx hbc ih fun h => hnc (hab.trans h)

theorem isConj_subgroup_of_odd {K : Subgroup G} {u v : G} (hu : u ∈ K) (hv : v ∈ K)
    (hu2 : u * u = 1) (hv2 : v * v = 1) (hodd : Odd (orderOf (u * v))) :
    IsConj (⟨u, hu⟩ : K) ⟨v, hv⟩ := by
  obtain ⟨g, hg, hgu⟩ := exists_conj_of_odd_orderOf_mul hu2 hv2 hodd
  have hgK : g ∈ K := by
    refine (Subgroup.closure_le K).2 ?_ hg
    intro z hz
    rcases hz with rfl | hz
    · exact hu
    · rw [Set.mem_singleton_iff] at hz
      subst hz
      exact hv
  exact isConj_iff.2 ⟨⟨g, hgK⟩, Subtype.ext hgu⟩

theorem false_of_commute_of_not_collComp (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hnd : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4)
    (hIH : ∀ K : Subgroup G, K ≠ ⊤ → ∀ D' : Set K, (∃ d₀ : K, D' = {g | IsConj d₀ g}) →
      IsRootInvolutionSet D' → Subgroup.closure D' = ⊤ →
      (∃ d ∈ D', ∃ e ∈ D', orderOf (d * e) = 4) → ExcCollConnected D')
    {s x y : G} (hs : s ∈ D) (hx : x ∈ D) (hy : y ∈ D) (hxC : ¬ CollComp D s x)
    (hxZ : ∀ c, CollComp D s c → Commute x c) (hxy : Commute x y) (hyC : ¬ CollComp D s y)
    (hyZ : ¬ ∀ c, CollComp D s c → Commute y c) : False := by
  have hconj : ∀ g z : G, z ∈ D → g * z * g⁻¹ ∈ D := fun g z hz =>
    conj_mem_of_isClass hclass g hz
  have hCB : ∀ c, CollComp D s c → ∀ b, CollComp D x b → Commute c b := fun c hc b hb =>
    commute_of_collComp hclass hD (hc.mem hs) hb (hxZ c hc).symm fun h => hxC (hc.trans h.symm)
  have hyB : ¬ CollComp D x y := fun h => hyZ fun c hc => (hCB c hc y h).symm
  have hBA : ∀ b, CollComp D x b → ∀ a, CollComp D y a → Commute b a := fun b hb a ha =>
    commute_of_collComp hclass hD (hb.mem hx) ha
      (commute_of_collComp hclass hD hy hb hxy.symm hyB).symm fun h => hyB (hb.trans h.symm)
  have hCA : ∀ c, CollComp D s c → ∀ a, CollComp D y a → ¬ Commute c a := by
    intro c hc a ha hca
    have hcy : Commute c y := commute_of_collComp hclass hD (hc.mem hs) ha.symm hca
      fun h => hyC (hc.trans (h.symm.trans ha.symm))
    exact hyZ fun c' hc' => commute_of_collComp hclass hD hy (hc.symm.trans hc') hcy.symm
      fun h => hyC (hc.trans h)
  have hodd : ∀ c, CollComp D s c → ∀ a, CollComp D y a → Odd (orderOf (c * a)) := by
    intro c hc a ha
    rcases commute_or_orderOf_mul_eq_four_or_odd hD (hc.mem hs) (ha.mem hy) with h | h4 | ⟨h, -⟩
    · exact absurd h (hCA c hc a ha)
    · exact absurd (hc.trans ((collComp_of_orderOf_eq_four hclass hD (hc.mem hs) (ha.mem hy)
        h4).trans ha.symm)) hyC
    · exact h
  obtain ⟨X, hX⟩ : ∃ X : Set G, X = {g | CollComp D s g} ∪ {g | CollComp D y g} := ⟨_, rfl⟩
  have hCX : ∀ c, CollComp D s c → c ∈ Subgroup.closure X := fun c hc =>
    Subgroup.subset_closure (by rw [hX]; exact Or.inl hc)
  have hAX : ∀ a, CollComp D y a → a ∈ Subgroup.closure X := fun a ha =>
    Subgroup.subset_closure (by rw [hX]; exact Or.inr ha)
  have hKx : Subgroup.closure X ≤ Subgroup.centralizer {x} := by
    rw [Subgroup.closure_le]
    intro g hg
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    rw [hX] at hg
    rcases hg with hg | hg
    · exact (hxZ g hg).eq
    · exact (hBA h (CollComp.refl D h) g hg).eq
  have hKne : Subgroup.closure X ≠ ⊤ := by
    intro htop
    obtain ⟨d, hd, e, he, h4⟩ := hnd
    have hcent : ∀ g : G, x * g = g * x := fun g =>
      Subgroup.mem_centralizer_iff.1 (hKx (htop ▸ Subgroup.mem_top g)) x rfl
    have hDx : ∀ z ∈ D, z = x := fun z hz => by
      obtain ⟨c, hc⟩ := isConj_iff.1 (isConj_of_isClass hclass hx hz)
      rw [← hc, ← hcent c, mul_inv_cancel_right]
    rw [hDx d hd, hDx e he, hD.mul_self_eq_one hx, orderOf_one] at h4
    exact absurd h4 (by decide)
  have hsK := hCX s (CollComp.refl D s)
  obtain ⟨D', hD'⟩ : ∃ D' : Set (Subgroup.closure X),
      D' = {k | IsConj (⟨s, hsK⟩ : Subgroup.closure X) k} := ⟨_, rfl⟩
  have hmem : ∀ k ∈ D', (k : G) ∈ D := by
    intro k hk
    rw [hD'] at hk
    obtain ⟨c, rfl⟩ := isConj_iff.1 hk
    exact hconj (c : G) s hs
  have hconjD' : ∀ k ∈ D', ∀ c : Subgroup.closure X, c * k * c⁻¹ ∈ D' := by
    intro k hk c
    rw [hD'] at hk ⊢
    exact hk.trans (isConj_iff.2 ⟨c, rfl⟩)
  have hAD' : ∀ a, CollComp D y a → ∀ ha : a ∈ Subgroup.closure X, ⟨a, ha⟩ ∈ D' := by
    intro a ha haK
    rw [hD']
    exact isConj_subgroup_of_odd hsK haK (hD.mul_self_eq_one hs)
      (hD.mul_self_eq_one (ha.mem hy)) (hodd s (CollComp.refl D s) a ha)
  have hCD' : ∀ c, CollComp D s c → ∀ hc : c ∈ Subgroup.closure X, ⟨c, hc⟩ ∈ D' := by
    intro c hc hcK
    have hsy := hAD' y (CollComp.refl D y) (hAX y (CollComp.refl D y))
    rw [hD'] at hsy ⊢
    exact hsy.trans (isConj_subgroup_of_odd hcK (hAX y (CollComp.refl D y))
      (hD.mul_self_eq_one (hc.mem hs)) (hD.mul_self_eq_one hy) (hodd c hc y
        (CollComp.refl D y))).symm
  have hroot : IsRootInvolutionSet D' := by
    refine ⟨fun k hk => ?_, fun k hk k' hk' => ?_, fun k hk k' hk' h4 => ?_⟩
    · rw [← Subgroup.orderOf_coe]
      exact hD.orderOf_eq_two (hmem k hk)
    · rw [← Subgroup.orderOf_coe, Subgroup.coe_mul]
      exact hD.orderOf_mul (hmem k hk) (hmem k' hk')
    · have h4G : orderOf ((k : G) * k') = 4 := by
        rw [← Subgroup.coe_mul, Subgroup.orderOf_coe]
        exact h4
      have hk0 := hk
      rw [hD'] at hk0
      obtain ⟨h, hh⟩ := isConj_iff.1 hk0
      have hc := CollComp.conj hconj (h : G)⁻¹
        (CollComp.single (collStep_sq_of_orderOf_eq_four hclass hD (hmem k hk) (hmem k' hk')
          h4G))
      rw [show (h : G)⁻¹ * k * (h : G)⁻¹⁻¹ = s by
        rw [← hh]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        group] at hc
      have hwK : (h : G)⁻¹ * ((k : G) * k') ^ 2 * (h : G)⁻¹⁻¹ ∈ Subgroup.closure X :=
        ((h⁻¹ * (k * k') ^ 2 * h⁻¹⁻¹ : Subgroup.closure X)).2
      have hw := hconjD' _ (hCD' _ hc hwK) h
      convert hw using 1
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_pow, inv_inv]
      group
  have hgen : Subgroup.closure D' = ⊤ := by
    rw [eq_top_iff, ← Subgroup.closure_closure_coe_preimage (k := X)]
    apply Subgroup.closure_mono
    intro k hk
    have hXmem : ∀ g, g ∈ X → CollComp D s g ∨ CollComp D y g := fun g hg => by
      rw [hX] at hg
      exact hg
    rcases hXmem _ hk with hk | hk
    · exact hCD' _ hk k.2
    · exact hAD' _ hk k.2
  have hnd' : ∃ d ∈ D', ∃ e ∈ D', orderOf (d * e) = 4 := by
    obtain ⟨d₀, hd₀, e₀, he₀, h4⟩ := hnd
    obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_of_isClass hclass hd₀ hs)
    have he₁ := hconj g e₀ he₀
    have h4' : orderOf (s * (g * e₀ * g⁻¹)) = 4 := by
      rw [← hg, show g * d₀ * g⁻¹ * (g * e₀ * g⁻¹) = g * (d₀ * e₀) * g⁻¹ by group,
        orderOf_conj_eq]
      exact h4
    have hce := collComp_of_orderOf_eq_four hclass hD hs he₁ h4'
    refine ⟨_, hCD' s (CollComp.refl D s) hsK, _, hCD' _ hce (hCX _ hce), ?_⟩
    rw [← Subgroup.orderOf_coe]
    exact h4'
  have hcc := hIH _ hKne D' ⟨_, hD'⟩ hroot hgen hnd'
  have hsub := hcc {k | k ∈ D' ∧ CollComp D s k} (fun k hk => hk.1)
    ⟨_, hCD' s (CollComp.refl D s) hsK, CollComp.refl D s⟩
    (fun k hk k' hk' hkk' hkk'D => ⟨hk', hk.2.tail ⟨hmem k hk.1, hmem k' hk',
      congrArg Subtype.val hkk', hmem _ hkk'D⟩⟩)
    (hAD' y (CollComp.refl D y) (hAX y (CollComp.refl D y)))
  exact hyC hsub.2

theorem collConnected_of_commConnected_of_subgroups (hcomm : Closure.CommConnected D)
    (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) (hD : IsRootInvolutionSet D)
    (hgen : Subgroup.closure D = ⊤) (hnd : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4)
    (hIH : ∀ K : Subgroup G, K ≠ ⊤ → ∀ D' : Set K, (∃ d₀ : K, D' = {g | IsConj d₀ g}) →
      IsRootInvolutionSet D' → Subgroup.closure D' = ⊤ →
      (∃ d ∈ D', ∃ e ∈ D', orderOf (d * e) = 4) → ExcCollConnected D') :
    ExcCollConnected D := by
  intro S hSD ⟨s, hs⟩ hScl
  have hsD := hSD hs
  have hconj : ∀ g z : G, z ∈ D → g * z * g⁻¹ ∈ D := fun g z hz =>
    conj_mem_of_isClass hclass g hz
  have hCS : ∀ y, CollComp D s y → y ∈ S := by
    intro y hy
    unfold CollComp at hy
    induction hy with
    | refl => exact hs
    | tail _ hbc ih => exact hScl _ ih _ hbc.2.1 hbc.2.2.1 hbc.2.2.2
  suffices hDC : ∀ d ∈ D, CollComp D s d from fun d hd => hCS d (hDC d hd)
  have hE := hcomm {z | z ∈ D ∧ (CollComp D s z ∨ ∀ c, CollComp D s c → Commute z c)}
    (fun z hz => hz.1) ⟨s, hsD, Or.inl (CollComp.refl D s)⟩ (by
      rintro x ⟨hx, hxE⟩ y hy hxy
      refine ⟨hy, ?_⟩
      by_cases hyC : CollComp D s y
      · exact Or.inl hyC
      right
      by_cases hxC : CollComp D s x
      · intro c hc
        exact commute_of_collComp hclass hD hy (hxC.symm.trans hc) hxy.symm
          fun h => hyC (hxC.trans h)
      · by_contra hyZ
        exact false_of_commute_of_not_collComp hclass hD hnd hIH hsD hx hy hxC
          (hxE.resolve_left hxC) hxy hyC hyZ)
  have hnorm : ∀ g ∈ Subgroup.closure D, ∀ c, CollComp D s c →
      CollComp D s (g * c * g⁻¹) ∧ CollComp D s (g⁻¹ * c * g) := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem d hd =>
      intro c hc
      have hd2 : d⁻¹ = d := hD.inv_eq hd
      have key : CollComp D s (d * c * d⁻¹) := by
        rcases (hE hd).2 with hdC | hdZ
        · have h1 := CollComp.conj hconj d hdC
          rw [mul_inv_cancel_right] at h1
          exact hdC.trans (h1.symm.trans (CollComp.conj hconj d hc))
        · rw [(hdZ c hc).eq, mul_inv_cancel_right]
          exact hc
      refine ⟨key, ?_⟩
      rw [hd2] at key ⊢
      exact key
    | one => intro c hc; simpa using hc
    | mul g h _ _ ihg ihh =>
      intro c hc
      constructor
      · have := (ihg _ (ihh c hc).1).1
        rwa [show g * (h * c * h⁻¹) * g⁻¹ = g * h * c * (g * h)⁻¹ by group] at this
      · have := (ihh _ (ihg c hc).2).2
        rwa [show h⁻¹ * (g⁻¹ * c * g) * h = (g * h)⁻¹ * c * (g * h) by group] at this
    | inv g _ ih =>
      intro c hc
      rw [inv_inv]
      exact ⟨(ih c hc).2, (ih c hc).1⟩
  intro d hd
  obtain ⟨g, hg⟩ := isConj_iff.1 (isConj_of_isClass hclass hsD hd)
  have := (hnorm g (hgen ▸ Subgroup.mem_top g) s (CollComp.refl D s)).1
  rwa [hg] at this

theorem collConnected_of_commConnected
    (hcomm : ∀ (G : Type) [Group G] [Finite G] (D : Set G),
      (∃ d₀ : G, D = {g | IsConj d₀ g}) → IsRootInvolutionSet D → Subgroup.closure D = ⊤ →
      (∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) → Closure.CommConnected D)
    {G : Type} [Group G] [Finite G] {D : Set G} (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g})
    (hD : IsRootInvolutionSet D) (hgen : Subgroup.closure D = ⊤)
    (hnd : ∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) : ExcCollConnected D := by
  suffices key : ∀ n : ℕ, ∀ (G : Type) [Group G] [Finite G] (D : Set G), Nat.card G = n →
      (∃ d₀ : G, D = {g | IsConj d₀ g}) → IsRootInvolutionSet D → Subgroup.closure D = ⊤ →
      (∃ d ∈ D, ∃ e ∈ D, orderOf (d * e) = 4) → ExcCollConnected D from
    key _ G D rfl hclass hD hgen hnd
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro G _ _ D hn hclass hD hgen hnd
    refine collConnected_of_commConnected_of_subgroups (hcomm G D hclass hD hgen hnd) hclass hD
      hgen hnd fun K hK D' h1 h2 h3 h4 => ih _ ?_ K D' rfl h1 h2 h3 h4
    rw [← hn]
    exact (Subgroup.card_le_card_group K).lt_of_ne fun h =>
      hK ((Subgroup.card_eq_iff_eq_top K).1 h)

end CFSG.Timmesfeld.Moufang
