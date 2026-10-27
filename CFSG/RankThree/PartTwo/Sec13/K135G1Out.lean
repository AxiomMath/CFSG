module

public import CFSG.RankThree.PartTwo.Sec13.K135G1
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.Assembly.OrderReductions.FrattiniAutomorphisms
public import CFSG.RankThree.PartTwo.Sec13.F135LastKF135
public import CFSG.RankThree.PartTwo.Sec13.K135K3Core

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open CFSG Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

@[expose] def KFactOutTwo : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    Sec4.Census.List42 S → ∀ V : Subgroup (MulAut S), IsPGroup 2 V →
      ∃ a ∈ V, ∃ b ∈ V,
        V ≤ Subgroup.closure ({a, b} : Set (MulAut S)) ⊔ (MulAut.conj : S →* MulAut S).range

theorem g1o_aut_eq_one_of_card_lt {Q : Type*} [Group Q] [Finite Q] {p : ℕ} (hp : p.Prime)
    (hQ : Nat.card Q < p) (α : MulAut Q) (hα : α ^ p = 1) : α = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hA : IsPGroup p (Subgroup.zpowers α) := by
    intro g
    refine ⟨1, ?_⟩
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp g.2
    apply Subtype.ext
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hα, one_zpow]
  have h1 : Nat.card Q ≡ Nat.card (MulAction.fixedPoints (Subgroup.zpowers α) Q) [MOD p] :=
    hA.card_modEq_card_fixedPoints Q
  have hFle : Nat.card (MulAction.fixedPoints (Subgroup.zpowers α) Q) ≤ Nat.card Q :=
    Finite.card_subtype_le (fun x => x ∈ MulAction.fixedPoints (Subgroup.zpowers α) Q)
  have hFlt : Nat.card (MulAction.fixedPoints (Subgroup.zpowers α) Q) < p :=
    lt_of_le_of_lt hFle hQ
  have hcard : Nat.card (MulAction.fixedPoints (Subgroup.zpowers α) Q) = Nat.card Q :=
    (h1.eq_of_lt_of_lt hQ hFlt).symm
  have hall : MulAction.fixedPoints (Subgroup.zpowers α) Q = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) (le_of_eq ?_)
    rw [Set.ncard_univ, ← Nat.card_coe_set_eq, hcard]
  refine MulEquiv.ext (fun s => ?_)
  have hs : s ∈ MulAction.fixedPoints (Subgroup.zpowers α) Q := by
    rw [hall]
    exact Set.mem_univ s
  have hfix : α s = s := (MulAction.mem_fixedPoints.mp hs) ⟨α, Subgroup.mem_zpowers α⟩
  rw [MulAut.one_apply]
  exact hfix

lemma g1o_comm_of_sq {Q : Type*} [Group Q] (hsq : ∀ q : Q, q * q = 1) (u v : Q) :
    u * v = v * u := by
  have h1 : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right (hsq (u * v))
  have hu : u⁻¹ = u := inv_eq_of_mul_eq_one_right (hsq u)
  have hv : v⁻¹ = v := inv_eq_of_mul_eq_one_right (hsq v)
  rw [mul_inv_rev, hu, hv] at h1
  exact h1.symm

lemma g1o_mul_four {Q : Type*} [Group Q] {a b : Q} (hsq : ∀ q : Q, q * q = 1) (x y : Q)
    (hx : x = 1 ∨ x = a ∨ x = b ∨ x = a * b) (hy : y = 1 ∨ y = a ∨ y = b ∨ y = a * b) :
    x * y = 1 ∨ x * y = a ∨ x * y = b ∨ x * y = a * b := by
  have hA : a * a = 1 := hsq a
  have hB : b * b = 1 := hsq b
  have hBA : b * a = a * b := g1o_comm_of_sq hsq b a
  have hAAB : a * (a * b) = b := by rw [← mul_assoc, hA, one_mul]
  have hBAB : b * (a * b) = a := by rw [← mul_assoc, hBA, mul_assoc, hB, mul_one]
  have hABA : a * b * a = b := by rw [g1o_comm_of_sq hsq (a * b) a, hAAB]
  have hABB : a * b * b = a := by rw [g1o_comm_of_sq hsq (a * b) b, hBAB]
  have hABAB : a * b * (a * b) = 1 := hsq (a * b)
  rcases hx with h | h | h | h <;> rcases hy with h' | h' | h' | h' <;> rw [h, h'] <;>
    simp [hA, hB, hBA, hAAB, hBAB, hABA, hABB, hABAB]

lemma g1o_mk_four_of_closure {G : Type*} [Group G] {N : Subgroup G} [N.Normal]
    (hsq : ∀ q : G ⧸ N, q * q = 1) {a b x : G} (hx : x ∈ Subgroup.closure ({a, b} : Set G)) :
    (x : G ⧸ N) = 1 ∨ (x : G ⧸ N) = (a : G ⧸ N) ∨ (x : G ⧸ N) = (b : G ⧸ N) ∨
      (x : G ⧸ N) = (a : G ⧸ N) * (b : G ⧸ N) := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h
    · exact Or.inr (Or.inl (congrArg (fun g : G => (g : G ⧸ N)) h))
    · exact Or.inr (Or.inr (Or.inl (congrArg (fun g : G => (g : G ⧸ N)) h)))
  | one => exact Or.inl (by simp)
  | mul y z _ _ hy hz =>
    rw [QuotientGroup.mk_mul]
    exact g1o_mul_four hsq _ _ hy hz
  | inv y _ hy =>
    have hinv : ((y : G ⧸ N))⁻¹ = (y : G ⧸ N) := inv_eq_of_mul_eq_one_right (hsq _)
    rw [QuotientGroup.mk_inv, hinv]
    exact hy

theorem g1o_card_frattini_quotient_le_four {G : Type*} [Group G] [Finite G] (hG : IsPGroup 2 G)
    {a b : G} (hab : Subgroup.closure ({a, b} : Set G) = ⊤) :
    Nat.card (G ⧸ frattini G) ≤ 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (IsPGroup 2 G) := ⟨hG⟩
  have hsq : ∀ q : G ⧸ frattini G, q * q = 1 := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, ← pow_two]
    exact CFSG.pth_power_mem_frattini_of_isPGroup (p := 2) (R := G) x
  have hmem : ∀ x : G, x ∈ Subgroup.closure ({a, b} : Set G) := by
    intro x
    rw [hab]
    exact Subgroup.mem_top x
  have hgen : ∀ q : G ⧸ frattini G, q = 1 ∨ q = (a : G ⧸ frattini G) ∨
      q = (b : G ⧸ frattini G) ∨ q = (a : G ⧸ frattini G) * (b : G ⧸ frattini G) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact g1o_mk_four_of_closure hsq (hmem x)
  have hsurj : Function.Surjective
      (![1, (a : G ⧸ frattini G), (b : G ⧸ frattini G), (a : G ⧸ frattini G) * (b : G ⧸ frattini G)] :
        Fin 4 → G ⧸ frattini G) := by
    intro q
    rcases hgen q with h | h | h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
    · exact ⟨2, by simp [h]⟩
    · exact ⟨3, by simp [h]⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  exact hle.trans (Nat.card_fin 4).le

theorem g1o_pow_formula {Γ : Type*} [Group Γ] (y : Γ) (W : Subgroup Γ) (φ : MulAut ↥W)
    (hφ : ∀ w : ↥W, ((φ w : ↥W) : Γ) = y * (w : Γ) * y⁻¹) :
    ∀ n : ℕ, ∀ w : ↥W, (((φ ^ n) w : ↥W) : Γ) = y ^ n * (w : Γ) * (y ^ n)⁻¹ := by
  intro n
  induction n with
  | zero => intro w; simp
  | succ k ih =>
    intro w
    rw [pow_succ φ k, MulAut.mul_apply, ih, hφ, pow_succ y k, mul_inv_rev]
    simp only [mul_assoc]

theorem g1o_exists_conj_aut {Γ : Type*} [Group Γ] [Finite Γ] (y : Γ) (W : Subgroup Γ)
    (hW : ∀ w ∈ W, y * w * y⁻¹ ∈ W) :
    ∃ φ : MulAut ↥W, ∀ n : ℕ, ∀ w : ↥W, (((φ ^ n) w : ↥W) : Γ) = y ^ n * (w : Γ) * (y ^ n)⁻¹ := by
  have hinv : ∀ w ∈ W, y⁻¹ * w * y ∈ W := by
    let f : ↥W → ↥W := fun w => ⟨y * (w : Γ) * y⁻¹, hW (w : Γ) w.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have h := congrArg Subtype.val hab
      simpa [f] using h
    have hs : Function.Surjective f := Finite.surjective_of_injective hf
    intro w hw
    obtain ⟨w', hw'⟩ := hs ⟨w, hw⟩
    have h3 : y * (w' : Γ) * y⁻¹ = w := congrArg Subtype.val hw'
    have h4 : y⁻¹ * w * y = (w' : Γ) := by
      rw [← h3]
      group
    rw [h4]
    exact w'.2
  obtain ⟨φ, hφ⟩ : ∃ φ : MulAut ↥W, ∀ w : ↥W, ((φ w : ↥W) : Γ) = y * (w : Γ) * y⁻¹ := by
    refine ⟨{ toFun := fun w => ⟨y * (w : Γ) * y⁻¹, hW (w : Γ) w.2⟩,
              invFun := fun w => ⟨y⁻¹ * (w : Γ) * y, hinv (w : Γ) w.2⟩,
              left_inv := fun w => Subtype.ext (by simp [mul_assoc]),
              right_inv := fun w => Subtype.ext (by simp [mul_assoc]),
              map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }, fun w => rfl⟩
  exact ⟨φ, g1o_pow_formula y W φ hφ⟩

theorem g1o_lift_of_V_le_inn {I : Type} [Group I] [Finite I] (hQ : IsQuasisimple I) (f : MulAut I)
    (V : Subgroup (MulAut (I ⧸ Subgroup.center I))) (hV1 : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (hVn : ∀ v ∈ V, centerQuotMulAut I f * v * (centerQuotMulAut I f)⁻¹ ∈ V)
    (hVinn : V ≤ (MulAut.conj : (I ⧸ Subgroup.center I) →*
      MulAut (I ⧸ Subgroup.center I)).range) :
    ∃ T : Subgroup I, T ≠ ⊥ ∧ IsPGroup 2 T ∧ T.map f.toMonoidHom = T := by
  have hcen := center_quot_eq_bot hQ
  have hinj := conj_injective_of_center_eq_bot hcen
  refine exists_invariant_two_subgroup_of_central (QuotientGroup.mk' (Subgroup.center I))
    (QuotientGroup.mk'_surjective _) ?_ f (centerQuotMulAut I f) (fun x => rfl)
    (V.comap (MulAut.conj : (I ⧸ Subgroup.center I) →* MulAut (I ⧸ Subgroup.center I)))
    ?_ (hV2.comap_of_injective _ hinj) ?_
  · intro x hx
    rwa [QuotientGroup.ker_mk'] at hx
  · intro h
    apply hV1
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨s, rfl⟩ := hVinn hv
    have hs : s ∈ V.comap (MulAut.conj : (I ⧸ Subgroup.center I) →*
        MulAut (I ⧸ Subgroup.center I)) := hv
    rw [h, Subgroup.mem_bot] at hs
    rw [hs, map_one]
    exact Subgroup.one_mem _
  · intro s hs
    rw [Subgroup.mem_comap] at hs ⊢
    have hconj : (MulAut.conj : (I ⧸ Subgroup.center I) →*
        MulAut (I ⧸ Subgroup.center I)) (centerQuotMulAut I f s) =
        centerQuotMulAut I f * MulAut.conj s * (centerQuotMulAut I f)⁻¹ := by
      ext x
      simp [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
    rw [hconj]
    exact hVn _ hs

theorem kFactG1_of_outTwo (hOT : KFactOutTwo) : KFactG1 := by
  intro I _ _ hQ hL p hp hp7 f hf V hV1 hV2 hVn hVc
  haveI : Fact p.Prime := ⟨hp⟩
  have hnab : ∃ a b : I ⧸ Subgroup.center I, a * b ≠ b * a := hQ.2.2
  obtain ⟨a, haV, b, hbV, hVab⟩ := hOT (I ⧸ Subgroup.center I) hQ.2.1 hnab hL V hV2
  refine g1o_lift_of_V_le_inn hQ f V hV1 hV2 hVn ?_
  let π : MulAut (I ⧸ Subgroup.center I) →* Outer (I ⧸ Subgroup.center I) :=
    QuotientGroup.mk' (inner (I ⧸ Subgroup.center I))
  let fb : MulAut (I ⧸ Subgroup.center I) := centerQuotMulAut I f
  let W : Subgroup (Outer (I ⧸ Subgroup.center I)) := V.map π
  let y : Outer (I ⧸ Subgroup.center I) := π fb
  have hW2 : IsPGroup 2 W := hV2.map π
  have hyW : ∀ w ∈ W, y * w * y⁻¹ ∈ W := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨fb * v * fb⁻¹, hVn v hv, by simp only [map_mul, map_inv, y]⟩
  have hWc : ⁅W, Subgroup.zpowers y⁆ = W := by
    have := congrArg (Subgroup.map π) hVc
    rwa [Subgroup.map_commutator, MonoidHom.map_zpowers] at this
  have hfp : f ^ p = 1 := by
    have := pow_orderOf_eq_one f
    rwa [hf] at this
  have hy : y ^ p = 1 := by
    have h1 : fb ^ p = 1 := by
      show (centerQuotMulAut I f) ^ p = 1
      rw [← map_pow, hfp, map_one]
    show (π fb) ^ p = 1
    rw [← map_pow, h1, map_one]
  have hWle : W ≤ Subgroup.closure ({π a, π b} : Set (Outer (I ⧸ Subgroup.center I))) := by
    have h1 := Subgroup.map_mono (f := π) hVab
    rw [Subgroup.map_sup, MonoidHom.map_closure, Set.image_pair] at h1
    have h2 : (MulAut.conj : (I ⧸ Subgroup.center I) →*
        MulAut (I ⧸ Subgroup.center I)).range.map π = ⊥ :=
      QuotientGroup.map_mk'_self (inner (I ⧸ Subgroup.center I))
    rw [h2, sup_bot_eq] at h1
    exact h1
  let α : ↥W := ⟨π a, ⟨a, haV, rfl⟩⟩
  let β : ↥W := ⟨π b, ⟨b, hbV, rfl⟩⟩
  have hgenW : Subgroup.closure ({α, β} : Set ↥W) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have key : ∀ g (hg : g ∈ Subgroup.closure ({π a, π b} : Set (Outer (I ⧸ Subgroup.center I)))),
        ∃ hgW : g ∈ W, (⟨g, hgW⟩ : ↥W) ∈ Subgroup.closure ({α, β} : Set ↥W) := by
      intro g hg
      induction hg using Subgroup.closure_induction with
      | mem g hg =>
        rcases hg with rfl | rfl
        · exact ⟨α.2, Subgroup.subset_closure (Or.inl rfl)⟩
        · exact ⟨β.2, Subgroup.subset_closure (Or.inr rfl)⟩
      | one => exact ⟨W.one_mem, one_mem _⟩
      | mul g h _ _ ihg ihh =>
        obtain ⟨hgW, hgc⟩ := ihg
        obtain ⟨hhW, hhc⟩ := ihh
        exact ⟨W.mul_mem hgW hhW, mul_mem hgc hhc⟩
      | inv g _ ih =>
        obtain ⟨hgW, hgc⟩ := ih
        exact ⟨W.inv_mem hgW, inv_mem hgc⟩
    obtain ⟨hxW, hxc⟩ := key _ (hWle x.2)
    exact hxc
  have hq4 : Nat.card (↥W ⧸ frattini ↥W) ≤ 4 := g1o_card_frattini_quotient_le_four hW2 hgenW
  obtain ⟨φ, hφ⟩ := g1o_exists_conj_aut y W hyW
  have hφp : φ ^ p = 1 := by
    refine MulEquiv.ext fun w => Subtype.ext ?_
    rw [MulAut.one_apply, hφ p w, hy]
    simp
  have hφ1 : φ = 1 := by
    by_contra hne
    have hord : orderOf φ = p := orderOf_eq_prime hφp hne
    have hnd : ¬ p ∣ Nat.card ↥W := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hW2
      rw [hn]
      intro hdvd
      have h2 := Nat.Prime.dvd_of_dvd_pow hp hdvd
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    have hker : φ ∈ (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
        (frattini ↥W)).ker := by
      have h1 : (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
          (frattini ↥W) φ) ^ p = 1 := by
        rw [← map_pow, hφp, map_one]
      exact g1o_aut_eq_one_of_card_lt hp (lt_of_le_of_lt hq4 (by omega)) _ h1
    exact hne (CFSG.OrderReductions.FrattiniAutomorphisms.prime_order_frattini_kernel_trivial p φ
      hord hnd hker)
  have hcomm : ∀ w ∈ W, y * w = w * y := by
    intro w hw
    have h1 := hφ 1 ⟨w, hw⟩
    rw [hφ1, one_pow, MulAut.one_apply, pow_one] at h1
    have h2 : w = y * w * y⁻¹ := h1
    calc y * w = (y * w * y⁻¹) * y := by group
      _ = w * y := by rw [← h2]
  have hWbot : W = ⊥ := by
    rw [eq_bot_iff, ← hWc, Subgroup.commutator_le]
    intro w hw z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Commute.zpow_right (show Commute w y from (hcomm w hw).symm) k).eq
  intro v hv
  have hπ : π v ∈ W := ⟨v, hv, rfl⟩
  rw [hWbot, Subgroup.mem_bot] at hπ
  exact (QuotientGroup.eq_one_iff (N := inner (I ⧸ Subgroup.center I)) v).mp hπ

end CFSG.RankThree.PartTwo.Sec13.F135Last
