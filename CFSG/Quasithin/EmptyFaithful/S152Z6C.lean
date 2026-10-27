module

public import CFSG.Quasithin.EmptyFaithful.S152NBasic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S152Z6

variable {G : Type} [Group G]

private noncomputable local instance w3Fintype : Fintype S152N.W3 :=
  Fintype.ofEquiv _
    (RegularWreathProduct.equivProd (Equiv.Perm (Fin 3)) (Multiplicative (ZMod 2))).symm

private local instance w3DecEq : DecidableEq S152N.W3 := fun a b =>
  decidable_of_iff (a.left = b.left ∧ a.right = b.right) (by
    constructor
    · rintro ⟨h1, h2⟩
      exact RegularWreathProduct.ext h1 h2
    · rintro rfl
      exact ⟨rfl, rfl⟩)

private local instance w3MemP0 : DecidablePred (· ∈ S152N.W3.P0) := fun a =>
  inferInstanceAs (Decidable (∀ q, a.left q = 1 ∨ a.left q = S152N.W3.s01))

section action

variable {D Q Λ : Type} [Group D] [Group Q] [MulAction D Λ]

private def act (w : D ≀ᵣ Q) (f : Q → Λ) : Q → Λ := fun x => w.left x • f (w.right⁻¹ * x)

private theorem act_one (f : Q → Λ) : act (1 : D ≀ᵣ Q) f = f := by
  funext x
  simp [act]

private theorem act_mul (a b : D ≀ᵣ Q) (f : Q → Λ) : act (a * b) f = act a (act b f) := by
  funext x
  simp [act, mul_assoc, mul_smul]

end action

private abbrev Pt : Type := Multiplicative (ZMod 2) → Fin 3

private def f0 : Pt := fun _ => 2

set_option maxRecDepth 100000 in
private theorem act_f0_iff : ∀ a : S152N.W3, act a f0 = f0 ↔ a ∈ S152N.W3.P0 := by
  decide +kernel

set_option maxRecDepth 100000 in
private theorem eq_one_of_act : ∀ a : S152N.W3, (∀ f : Pt, act a f = f) → a = 1 := by
  decide +kernel

private def IsInvAct (u : S152N.W3) : Prop :=
  (∀ f : Pt, act u (act u f) = f) ∧ ∃ f : Pt, act u f ≠ f

private instance : DecidablePred IsInvAct := fun u => by unfold IsInvAct; infer_instance

private def CommAct (u v : S152N.W3) : Prop :=
  (∀ f : Pt, act u (act v f) = act v (act u f)) ∧ ∃ f : Pt, act u (act v f) ≠ f

private instance (u v : S152N.W3) : Decidable (CommAct u v) := by
  unfold CommAct; infer_instance

private def regPts (u v : S152N.W3) : Finset Pt :=
  Finset.univ.filter (fun f : Pt => act u f ≠ f ∧ act v f ≠ f ∧ act u (act v f) ≠ f)

set_option maxRecDepth 100000 in
private theorem regPts_card_le :
    ∀ u v : S152N.W3, IsInvAct u → IsInvAct v → CommAct u v → (regPts u v).card ≤ 4 := by
  decide +kernel

private theorem card_le_four_of_regular {ι : Type} {u v : S152N.W3} (hu : u * u = 1)
    (hv : v * v = 1) (huv : u * v = v * u) (hu1 : u ≠ 1) (hv1 : v ≠ 1) (hw : u * v ≠ 1)
    (S : Finset ι) (g : ι → S152N.W3)
    (hreg : ∀ i ∈ S, g i * u * (g i)⁻¹ ∉ S152N.W3.P0 ∧ g i * v * (g i)⁻¹ ∉ S152N.W3.P0 ∧
      g i * (u * v) * (g i)⁻¹ ∉ S152N.W3.P0)
    (hdist : ∀ i ∈ S, ∀ j ∈ S, g i * (g j)⁻¹ ∈ S152N.W3.P0 → i = j) : S.card ≤ 4 := by
  have hnf : ∀ a : S152N.W3, a ≠ 1 → ∃ f : Pt, act a f ≠ f := fun a ha => by
    by_contra h
    push Not at h
    exact ha (eq_one_of_act a h)
  have hI : ∀ a : S152N.W3, a * a = 1 → a ≠ 1 → IsInvAct a := fun a h1 h2 =>
    ⟨fun f => by rw [← act_mul, h1, act_one], hnf a h2⟩
  have hC : CommAct u v := by
    refine ⟨fun f => by rw [← act_mul, ← act_mul, huv], ?_⟩
    obtain ⟨f, hf⟩ := hnf (u * v) hw
    exact ⟨f, by rwa [act_mul] at hf⟩
  have hcore := regPts_card_le u v (hI u hu hu1) (hI v hv hv1) hC
  have hx : ∀ i ∈ S, ∀ x : S152N.W3, g i * x * (g i)⁻¹ ∉ S152N.W3.P0 →
      act x (act (g i)⁻¹ f0) ≠ act (g i)⁻¹ f0 := by
    intro i _ x hx heq
    apply hx
    rw [← act_f0_iff, act_mul, act_mul, heq, ← act_mul, mul_inv_cancel, act_one]
  have key : S.card ≤ (regPts u v).card := by
    refine Finset.card_le_card_of_injOn (fun i => act (g i)⁻¹ f0) ?_ ?_
    · intro i hi
      obtain ⟨h1, h2, h3⟩ := hreg i hi
      have h3' := hx i hi (u * v) h3
      rw [act_mul] at h3'
      show act (g i)⁻¹ f0 ∈ regPts u v
      rw [regPts, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hx i hi u h1, hx i hi v h2, h3'⟩
    · intro i hi j hj hij
      refine (hdist j hj i hi ?_).symm
      rw [← act_f0_iff, act_mul]
      have hij' : act (g i)⁻¹ f0 = act (g j)⁻¹ f0 := hij
      rw [hij', ← act_mul, mul_inv_cancel, act_one]
  omega

private noncomputable def toW3 (H : Subgroup G) (φ : OTwoQuot H ≃* S152N.W3) :
    ↥H →* S152N.W3 :=
  (φ : OTwoQuot H →* S152N.W3).comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))

private theorem toW3_eq_one_iff {H : Subgroup G} (φ : OTwoQuot H ≃* S152N.W3) (x : ↥H) :
    toW3 H φ x = 1 ↔ (x : G) ∈ pCoreOf 2 H := by
  constructor
  · intro hx
    have h1 : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) x = 1 :=
      (map_eq_one_iff (φ : OTwoQuot H →* S152N.W3) φ.injective).1 hx
    exact ⟨x, (QuotientGroup.eq_one_iff x).1 h1, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have hyx' : y = x := Subtype.ext hyx
    subst hyx'
    show φ (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) y) = 1
    rw [show QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H) y = 1 from (QuotientGroup.eq_one_iff y).2 hy]
    exact map_one φ

private theorem toW3_mem_map_iff {H T : Subgroup G} (hQT : pCoreOf 2 H ≤ T)
    (φ : OTwoQuot H ≃* S152N.W3) (x : ↥H) :
    toW3 H φ x ∈ (T.subgroupOf H).map (toW3 H φ) ↔ (x : G) ∈ T := by
  constructor
  · rintro ⟨t, ht, hte⟩
    have h1 : toW3 H φ (t⁻¹ * x) = 1 := by rw [map_mul, map_inv, hte, inv_mul_cancel]
    have h2 : ((t⁻¹ * x : ↥H) : G) ∈ T := hQT ((toW3_eq_one_iff φ _).1 h1)
    have h3 : (t : G) ∈ T := ht
    have h4 : (x : G) = (t : G) * ((t⁻¹ * x : ↥H) : G) := by simp
    rw [h4]
    exact T.mul_mem h3 h2
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem isSylowTwoOf_map_toW3 [Finite G] {H T : Subgroup G} (hT : IsSylowTwoOf T H)
    (φ : OTwoQuot H ≃* S152N.W3) :
    IsSylowTwoOf ((T.subgroupOf H).map (toW3 H φ)) ⊤ := by
  have h := S152N.isSylowTwoOf_image hT φ
  rwa [Subgroup.map_map] at h

private theorem exists_three_not_mem {A Q : Subgroup G} (hrel : (A ⊓ Q).relIndex A = 4) :
    ∃ a₁ ∈ A, ∃ a₂ ∈ A, a₁ ∉ Q ∧ a₂ ∉ Q ∧ a₁ * a₂ ∉ Q := by
  by_contra hno
  push Not at hno
  have h1 : ((A ⊓ Q).subgroupOf A).index = 4 := hrel
  have hne : ∃ a ∈ A, a ∉ Q := by
    by_contra h
    push Not at h
    have : (A ⊓ Q).subgroupOf A = ⊤ := by
      rw [eq_top_iff]
      intro x _
      exact ⟨x.2, h x x.2⟩
    rw [this, Subgroup.index_top] at h1
    omega
  obtain ⟨a, haA, haQ⟩ := hne
  have h2 : ((A ⊓ Q).subgroupOf A).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨a, haA⟩, fun b => ?_⟩
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.coe_mul]
    by_cases hb : (b : G) ∈ Q
    · have : (b : G) * a ∉ Q := fun h => haQ (by simpa using Q.mul_mem (Q.inv_mem hb) h)
      simp [hb, this, b.2, A.mul_mem b.2 haA]
    · have := hno b b.2 a haA hb haQ
      simp [hb, this, b.2, A.mul_mem b.2 haA]
  omega

private theorem mem_normalizer_conjSubgroup {V : Subgroup G} {h a : G}
    (ha : h * a * h⁻¹ ∈ Subgroup.normalizer (V : Set G)) :
    a ∈ Subgroup.normalizer ((conjSubgroup V h : Subgroup G) : Set G) := by
  rw [Subgroup.mem_set_normalizer_iff] at ha ⊢
  intro x
  simp only [SetLike.mem_coe, mem_conjSubgroup_iff]
  have h1 := ha (h * x * h⁻¹)
  have e : h * a * h⁻¹ * (h * x * h⁻¹) * (h * a * h⁻¹)⁻¹ = h * (a * x * a⁻¹) * h⁻¹ := by group
  rw [e] at h1
  exact h1

private theorem conjSubgroup_eq_of_mem {V : Subgroup G} {h h' : G}
    (hn : h' * h⁻¹ ∈ Subgroup.normalizer (V : Set G)) :
    conjSubgroup V h = conjSubgroup V h' := by
  have e1 : conjSubgroup V (h' * h⁻¹) = V := conjSubgroup_eq_iff_mem_normalizer.2 hn
  have e2 : conjSubgroup (conjSubgroup V (h' * h⁻¹)) h = conjSubgroup V ((h' * h⁻¹) * h) :=
    conjSubgroup_conjSubgroup _ _ _
  rw [e1] at e2
  rw [e2]
  congr 1
  group

theorem regular_conj_card_le_four {G : Type} [Group G] [Finite G] {T Mc M H A : Subgroup G}
    (hs : Setting152 T Mc M) (hH : IsHStar T M H) (φ : OTwoQuot H ≃* S152N.W3) (hAH : A ≤ H)
    (hA : IsElemAbelian 2 A) (hrel : (A ⊓ pCoreOf 2 H).relIndex A = 4) (S : Finset (Subgroup G))
    (hS : ∀ V' ∈ S, (∃ h ∈ H, V' = conjSubgroup (V154 T Mc M) h) ∧
        A ⊓ Subgroup.normalizer (V' : Set G) ≤ pCoreOf 2 H) : S.card ≤ 4 := by
  have hT : IsSylowTwoOf T H := S152N.isSylowTwoOf_hStar hs hH
  have hQT : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hT
  have hNV : H ⊓ Subgroup.normalizer (V154 T Mc M : Set G) = T :=
    S152N.inf_normalizer_eq_of_W3 hs hH φ
  have hTN : T ≤ Subgroup.normalizer (V154 T Mc M : Set G) := hNV.ge.trans inf_le_right
  obtain ⟨c, -, hc⟩ :=
    A4.exists_conj_of_isSylowTwoOf S152N.W3.P0_isSylowTwoOf (isSylowTwoOf_map_toW3 hT φ)
  obtain ⟨a₁, ha₁, a₂, ha₂, h₁Q, h₂Q, h₁₂Q⟩ := exists_three_not_mem hrel
  set ψ := toW3 H φ
  set x₁ : ↥H := ⟨a₁, hAH ha₁⟩
  set x₂ : ↥H := ⟨a₂, hAH ha₂⟩
  have hu : ψ x₁ * ψ x₁ = 1 := by
    rw [← map_mul]
    have : x₁ * x₁ = 1 := Subtype.ext (by simpa [pow_two] using hA.2 a₁ ha₁)
    rw [this, map_one]
  have hv : ψ x₂ * ψ x₂ = 1 := by
    rw [← map_mul]
    have : x₂ * x₂ = 1 := Subtype.ext (by simpa [pow_two] using hA.2 a₂ ha₂)
    rw [this, map_one]
  have huv : ψ x₁ * ψ x₂ = ψ x₂ * ψ x₁ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (B2F.isElemAbelian_comm hA ha₁ ha₂)
  have hu1 : ψ x₁ ≠ 1 := fun h => h₁Q ((toW3_eq_one_iff φ x₁).1 h)
  have hv1 : ψ x₂ ≠ 1 := fun h => h₂Q ((toW3_eq_one_iff φ x₂).1 h)
  have hw : ψ x₁ * ψ x₂ ≠ 1 := by
    rw [← map_mul]
    exact fun h => h₁₂Q ((toW3_eq_one_iff φ (x₁ * x₂)).1 h)
  have hex : ∀ V' ∈ S, ∃ h : ↥H, V' = conjSubgroup (V154 T Mc M) (h : G) := fun V' hV' => by
    obtain ⟨h, hh, hV⟩ := (hS V' hV').1
    exact ⟨⟨h, hh⟩, hV⟩
  choose! hf hfV using hex
  have hreg1 : ∀ a (ha : a ∈ A), a ∉ pCoreOf 2 H → ∀ V' ∈ S,
      ψ (hf V') * ψ ⟨a, hAH ha⟩ * (ψ (hf V'))⁻¹ ∉ (T.subgroupOf H).map ψ := by
    intro a ha haQ V' hV' hmem
    have h1 : ψ (hf V' * ⟨a, hAH ha⟩ * (hf V')⁻¹) ∈ (T.subgroupOf H).map ψ := by
      simpa [map_mul, map_inv] using hmem
    have h2 := (toW3_mem_map_iff hQT φ _).1 h1
    have h3 : (hf V' : G) * a * (hf V' : G)⁻¹ ∈ Subgroup.normalizer (V154 T Mc M : Set G) :=
      hTN h2
    have h4 := mem_normalizer_conjSubgroup h3
    rw [← hfV V' hV'] at h4
    exact haQ ((hS V' hV').2 ⟨ha, h4⟩)
  refine card_le_four_of_regular hu hv huv hu1 hv1 hw S (fun V' => c⁻¹ * ψ (hf V')) ?_ ?_
  · intro V' hV'
    have key : ∀ y : S152N.W3, ψ (hf V') * y * (ψ (hf V'))⁻¹ ∉ (T.subgroupOf H).map ψ →
        c⁻¹ * ψ (hf V') * y * (c⁻¹ * ψ (hf V'))⁻¹ ∉ S152N.W3.P0 := by
      intro y hy hmem
      apply hy
      rw [hc]
      have e : c⁻¹ * (ψ (hf V') * y * (ψ (hf V'))⁻¹) * c =
          c⁻¹ * ψ (hf V') * y * (c⁻¹ * ψ (hf V'))⁻¹ := by group
      rw [e]
      exact hmem
    refine ⟨key _ (hreg1 a₁ ha₁ h₁Q V' hV'), key _ (hreg1 a₂ ha₂ h₂Q V' hV'), ?_⟩
    have h12 := hreg1 (a₁ * a₂) (A.mul_mem ha₁ ha₂) h₁₂Q V' hV'
    have hmul : ψ ⟨a₁ * a₂, hAH (A.mul_mem ha₁ ha₂)⟩ = ψ x₁ * ψ x₂ := by
      rw [← map_mul]
      rfl
    rw [hmul] at h12
    exact key _ h12
  · intro V' hV' V'' hV'' hmem
    have e : c⁻¹ * ψ (hf V') * (c⁻¹ * ψ (hf V''))⁻¹ =
        c⁻¹ * ψ (hf V' * (hf V'')⁻¹) * c := by
      simp only [map_mul, map_inv]
      group
    rw [e, ← hc] at hmem
    have h2 := (toW3_mem_map_iff hQT φ _).1 hmem
    have h3 : (hf V' : G) * (hf V'' : G)⁻¹ ∈ Subgroup.normalizer (V154 T Mc M : Set G) := hTN h2
    rw [hfV V' hV', hfV V'' hV'']
    exact (conjSubgroup_eq_of_mem h3).symm

end S152Z6

end CFSG.Quasithin
