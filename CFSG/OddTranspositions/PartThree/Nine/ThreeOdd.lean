module

public import CFSG.OddTranspositions.PartThree.Nine.ThreeOddLocal
public import CFSG.OddTranspositions.PartThree.Nine.Goldschmidt
public import CFSG.GH74.Uniqueness.Bender.Outer
public import CFSG.OddTranspositions.WidthSylowSetup

public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
theorem commute_of_mem_blockClass (hC : HypothesisC D)
    (hαc : ∀ a ∈ hC.alpha, ∀ b ∈ hC.alpha, Commute a b) {γ : Set G}
    (hγ : γ ∈ blockClass hC.alpha) {x y : G} (hx : x ∈ γ) (hy : y ∈ γ) : Commute x y := by
  obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hγ
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨b, hb, rfl⟩ := hy
  exact (hαc a ha b hb).conj g

theorem centSet_inter_eq_of_pCore_eq_bot (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (hP : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) {β : Set G} (hβ : β ∈ Dalpha D hC.alpha)
    {a b : G} (ha : a ∈ hC.alpha) (hb : b ∈ β) :
    {e | e ∈ D ∧ Commute e a ∧ Commute e b} = hC.alpha ∪ β := by
  obtain ⟨hαc, -, -⟩ := alpha_structure_of_pCore_eq_bot hC hH hP
  obtain ⟨hβc, hβD, -, hαβ⟩ := mem_Dalpha_iff.mp hβ
  ext e
  constructor
  · rintro ⟨he, hea, heb⟩
    rcases mem_block_or_DalphaStar_of_commute hC (mem_blockClass_self _) ha he hea.symm with
      heα | heE
    · exact Or.inl heα
    · by_cases heb' : e = b
      · exact Or.inr (heb' ▸ hb)
      · exact Or.inr (mem_block_of_commute hC hH hP hβc hb (subset_DalphaStar hβ hb) heE
          (Ne.symm heb') heb.symm)
  · rintro (heα | heβ)
    · exact ⟨hC.isBlock_alpha.subset heα, hαc e heα a ha, hαβ e heα b hb⟩
    · exact ⟨hβD heβ, (hαβ a ha e heβ).symm, commute_of_mem_blockClass hC hαc hβc heβ hb⟩

omit [Finite G] in
theorem exists_fixed_conj_of_mem_normalizer {γ : Set G} (hγf : γ.Finite) (hγ : Odd γ.ncard)
    {y : G} (hy2 : y * y = 1) (hyN : y ∈ Subgroup.normalizer γ) : ∃ r ∈ γ, y * r * y⁻¹ = r := by
  have : Finite γ := hγf.to_subtype
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy2
  let f : γ → γ := fun r => ⟨y * r * y⁻¹, (hyN r).mp r.2⟩
  have hf : Function.Involutive f := by
    intro r
    apply Subtype.ext
    change y * (y * r * y⁻¹) * y⁻¹ = r
    rw [hyi]
    calc y * (y * ↑r * y) * y = (y * y) * ↑r * (y * y) := by group
      _ = r := by rw [hy2, one_mul, mul_one]
  obtain ⟨r, hr⟩ := CFSG.GH74.Uniqueness.Bender.exists_fixed_of_odd_card f hf
    (by rwa [Nat.card_coe_set_eq])
  exact ⟨r, r.2, congrArg Subtype.val hr⟩

theorem centSet_inter_eq_conj (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (hP : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) (g : G) {σ : Set G}
    (hσ : σ ∈ Dalpha D ((fun x => g * x * g⁻¹) '' hC.alpha)) {r s : G}
    (hr : r ∈ (fun x => g * x * g⁻¹) '' hC.alpha) (hs : s ∈ σ) {e : G} (he : e ∈ D)
    (her : Commute e r) (hes : Commute e s) : e ∈ (fun x => g * x * g⁻¹) '' hC.alpha ∪ σ := by
  have hσ' := Dalpha.conj hC.setup.normal hσ g⁻¹
  simp only [inv_inv, Set.image_image,
    show ∀ x : G, g⁻¹ * (g * x * g⁻¹) * g = x from fun x => by group, Set.image_id'] at hσ'
  obtain ⟨r₀, hr₀, rfl⟩ := hr
  have hs' : g⁻¹ * s * g ∈ (fun x => g⁻¹ * x * g) '' σ := ⟨s, hs, rfl⟩
  have hconj : ∀ a b : G, Commute a b → Commute (g⁻¹ * a * g) (g⁻¹ * b * g) := fun a b h => by
    simpa using h.conj g⁻¹
  have hmem : g⁻¹ * e * g ∈ {e | e ∈ D ∧ Commute e r₀ ∧ Commute e (g⁻¹ * s * g)} := by
    refine ⟨by simpa using hC.setup.conj_mem g⁻¹ he, ?_, hconj e s hes⟩
    simpa [show g⁻¹ * (g * r₀ * g⁻¹) * g = r₀ by group] using hconj e _ her
  rw [centSet_inter_eq_of_pCore_eq_bot hC hH hP hσ' hr₀ hs'] at hmem
  rcases hmem with h | ⟨e₀, he₀, he₀e⟩
  · exact Or.inl ⟨_, h, by group⟩
  · right
    have : e = e₀ := by
      have h1 : g⁻¹ * e₀ * g = g⁻¹ * e * g := he₀e
      simpa using h1.symm
    rw [this]
    exact he₀

theorem block_eq_of_mem (hC : HypothesisC D) {γ γ' : Set G} (hγ : γ ∈ blockClass hC.alpha)
    (hγ' : γ' ∈ blockClass hC.alpha) {x : G} (hx : x ∈ γ) (hx' : x ∈ γ') : γ = γ' := by
  obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hγ
  obtain ⟨h, rfl⟩ := mem_blockClass_iff.mp hγ'
  have hγb : IsBlock D ((fun y => g * y * g⁻¹) '' hC.alpha) :=
    isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hγ
  have heq : (fun y => h * y * h⁻¹) '' hC.alpha =
      (fun y => (h * g⁻¹) * y * (h * g⁻¹)⁻¹) '' ((fun y => g * y * g⁻¹) '' hC.alpha) := by
    rw [Set.image_image]
    congr 1
    ext y
    group
  by_cases hc : h * g⁻¹ ∈ Subgroup.normalizer ((fun y => g * y * g⁻¹) '' hC.alpha)
  · rw [heq, conj_image_block_eq hc]
  · exfalso
    rw [heq] at hx'
    exact Set.disjoint_left.mp (hγb.disjoint_conj hc) hx hx'

section Main


theorem false_of_pCore_eq_bot (hC : HypothesisC D) (hH : Th91Hyp D hC)
    (hs : IsSimpleGroup (commutator G)) (hP : CFSG.pCore 2 (Halpha D hC.alpha) = ⊥) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hαc, hαm, k, hk2, hαcard⟩ := alpha_structure_of_pCore_eq_bot hC hH hP
  have hm3 : 3 ≤ 2 ^ k - 1 := by
    have : 4 ≤ 2 ^ k := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    omega
  have hmodd : Odd (2 ^ k - 1) := by
    have h2k : Even (2 ^ k) := (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    obtain ⟨r, hr⟩ := h2k
    exact ⟨r - 1, by omega⟩
  have hblk_card : ∀ γ ∈ blockClass hC.alpha, γ.ncard = 2 ^ k - 1 := by
    intro γ hγ
    obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hγ
    rw [Set.ncard_image_of_injective _ (fun a b h => by simpa using h), hαcard]
  have hblk_mul : ∀ γ ∈ blockClass hC.alpha, ∀ x ∈ γ, ∀ y ∈ γ, x ≠ y → x * y ∈ γ := by
    intro γ hγ x hx y hy hxy
    obtain ⟨g, rfl⟩ := mem_blockClass_iff.mp hγ
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    have hab : a ≠ b := fun h => hxy (by rw [h])
    exact ⟨a * b, hαm a ha b hb hab, by group⟩
  obtain ⟨β, hβ⟩ := exists_mem_Dalpha hC
  obtain ⟨hβc, hβD, hβα, hαβ⟩ := mem_Dalpha_iff.mp hβ
  have hαD : hC.alpha ⊆ D := hC.isBlock_alpha.subset
  have hdisj : Disjoint hC.alpha β := by
    obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hβc
    have hgN : g ∉ Subgroup.normalizer hC.alpha := fun hgN =>
      hβα (hg.trans (conj_image_block_eq hgN))
    exact hg ▸ hC.isBlock_alpha.disjoint_conj hgN
  obtain ⟨v, hv⟩ := blockClass_nonempty hC.isBlock_alpha.nonempty hβc
  set u := hC.d with hu
  have huα : u ∈ hC.alpha := hC.d_mem_alpha
  have hABc : (hC.alpha ∪ β).Pairwise Commute := by
    rintro x (hx | hx) y (hy | hy) -
    · exact hαc x hx y hy
    · exact hαβ x hx y hy
    · exact (hαβ y hy x hx).symm
    · exact commute_of_mem_blockClass hC hαc hβc hx hy
  set A := Subgroup.closure (hC.alpha ∪ β) with hA
  have hAc : IsMulCommutative A := Subgroup.isMulCommutative_closure hABc
  have hAsq : ∀ x ∈ A, x * x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with hy | hy
      · exact hC.setup.oddT.mul_self_eq_one (hαD hy)
      · exact hC.setup.oddT.mul_self_eq_one (hβD hy)
    | one => exact mul_one 1
    | mul a b ha hb iha ihb =>
      have hab : a * b = b * a := hAc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩ |> congrArg Subtype.val
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [hab]
        _ = 1 := by rw [← mul_assoc, iha, one_mul, ihb]
    | inv a ha iha => rw [← mul_inv_rev, iha, inv_one]
  have hA2 : IsPGroup 2 A := fun g => ⟨1, by
    rw [pow_one, pow_two]
    exact Subtype.ext (hAsq g g.2)⟩
  obtain ⟨S, hAS⟩ := hA2.exists_le_sylow
  have hαS : ∀ x ∈ hC.alpha, x ∈ (S : Subgroup G) := fun x hx =>
    hAS (Subgroup.subset_closure (Or.inl hx))
  have hβS : ∀ x ∈ β, x ∈ (S : Subgroup G) := fun x hx =>
    hAS (Subgroup.subset_closure (Or.inr hx))
  have hvD : v ∈ D := hβD hv
  have huv : u ≠ v := fun h => Set.disjoint_left.mp hdisj huα (h ▸ hv)
  have hSD : ∀ e ∈ (S : Subgroup G), e ∈ D → e ∈ hC.alpha ∪ β := by
    intro e heS heD
    have hcom : ∀ w ∈ (S : Subgroup G), w ∈ D → Commute e w := fun w hw hwD => by
      by_cases hew : e = w
      · rw [hew]
      · exact sylow_inter_commute_of_setup hC.setup S heS hw heD hwD hew
    rw [← centSet_inter_eq_of_pCore_eq_bot hC hH hP hβ huα hv]
    exact ⟨heD, hcom u (hαS u huα) (hαD huα), hcom v (hβS v hv) hvD⟩
  set P : Set G := {x | ∃ a ∈ hC.alpha, ∃ b ∈ β, x = a * b} with hPdef
  have hSconj : ∀ s ∈ (S : Subgroup G), ∀ x ∈ P, s * x * s⁻¹ ∈ P := by
    rintro s hs _ ⟨a, ha, b, hb, rfl⟩
    have hsa : s * a * s⁻¹ ∈ hC.alpha ∪ β := hSD _ ((S : Subgroup G).mul_mem
      ((S : Subgroup G).mul_mem hs (hαS a ha)) ((S : Subgroup G).inv_mem hs))
      (hC.setup.conj_mem s (hαD ha))
    have hsb : s * b * s⁻¹ ∈ hC.alpha ∪ β := hSD _ ((S : Subgroup G).mul_mem
      ((S : Subgroup G).mul_mem hs (hβS b hb)) ((S : Subgroup G).inv_mem hs))
      (hC.setup.conj_mem s (hβD hb))
    have hsplit : s * (a * b) * s⁻¹ = (s * a * s⁻¹) * (s * b * s⁻¹) := by group
    rw [hsplit]
    rcases hsa with hsa | hsa <;> rcases hsb with hsb | hsb
    · exfalso
      have hsN := mem_normalizer_block_of_conj_mem hC (mem_blockClass_self _) ha hsa
      exact Set.disjoint_left.mp hdisj ((hsN b).mpr hsb) hb
    · exact ⟨_, hsa, _, hsb, rfl⟩
    · exact ⟨_, hsb, _, hsa, (hαβ _ hsb _ hsa).symm.eq⟩
    · exfalso
      have hsN := mem_normalizer_block_of_conj_mem hC hβc hb hsb
      exact Set.disjoint_left.mp hdisj ha ((hsN a).mpr hsa)
  have hinjP : Set.InjOn (fun p : G × G => p.1 * p.2) (hC.alpha ×ˢ β) := by
    rintro ⟨a, b⟩ ⟨ha, hb⟩ ⟨a', b'⟩ ⟨ha', hb'⟩ hab
    simp only at hab
    have ha'2 := hC.setup.oddT.mul_self_eq_one (hαD ha')
    have hb2 := hC.setup.oddT.mul_self_eq_one (hβD hb)
    have hkey : a' * a = b' * b := by
      calc a' * a = a' * (a * b) * b := by simp only [mul_assoc, hb2, mul_one]
        _ = a' * (a' * b') * b := by rw [hab]
        _ = b' * b := by rw [← mul_assoc, ha'2, one_mul]
    by_cases haa : a = a'
    · subst haa
      have : b = b' := by
        have h1 : a * b = a * b' := hab
        exact mul_left_cancel h1
      rw [this]
    · exfalso
      have h1 : a' * a ∈ hC.alpha := hαm a' ha' a ha (Ne.symm haa)
      by_cases hbb : b' = b
      · subst hbb
        rw [hb2] at hkey
        exact haa (hC.setup.oddT.eq_of_mul_eq_one (hαD ha') hkey).symm
      · have h2 : b' * b ∈ β := hblk_mul β hβc b' hb' b hb hbb
        exact Set.disjoint_left.mp hdisj h1 (hkey ▸ h2)
  have hPimg : P = (fun p : G × G => p.1 * p.2) '' (hC.alpha ×ˢ β) := by
    ext x
    constructor
    · rintro ⟨a, ha, b, hb, rfl⟩
      exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
    · rintro ⟨⟨a, b⟩, ⟨ha, hb⟩, rfl⟩
      exact ⟨a, ha, b, hb, rfl⟩
  have hPcard : P.ncard = (2 ^ k - 1) * (2 ^ k - 1) := by
    rw [hPimg, hinjP.ncard_image, Set.ncard_prod, hαcard, hblk_card β hβc]
  have hPodd : ¬ 2 ∣ Nat.card P := by
    rw [Nat.card_coe_set_eq, hPcard]
    exact Nat.not_even_iff_odd.mpr (hmodd.mul hmodd) ∘ even_iff_two_dvd.mpr
  have : Finite P := (Set.toFinite P).to_subtype
  let act : MulAction (S : Subgroup G) P :=
    { smul := fun s x => ⟨s * x * s⁻¹, hSconj s s.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        change ((1 : (S : Subgroup G)) : G) * x * ((1 : (S : Subgroup G)) : G)⁻¹ = x
        simp)
      mul_smul := fun s t x => Subtype.ext (by
        change ((s * t : (S : Subgroup G)) : G) * x * ((s * t : (S : Subgroup G)) : G)⁻¹ =
          (s : G) * ((t : G) * x * (t : G)⁻¹) * (s : G)⁻¹
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group) }
  obtain ⟨⟨z, hzP⟩, hzfix⟩ :=
    (S.isPGroup').nonempty_fixed_point_of_prime_not_dvd_card P hPodd
  obtain ⟨a₀, ha₀, b₀, hb₀, rfl⟩ := hzP
  have hzc : ∀ x ∈ (S : Subgroup G), x * (a₀ * b₀) = (a₀ * b₀) * x := by
    intro x hx
    have h := congrArg Subtype.val (hzfix ⟨x, hx⟩)
    change x * (a₀ * b₀) * x⁻¹ = a₀ * b₀ at h
    calc x * (a₀ * b₀) = x * (a₀ * b₀) * x⁻¹ * x := by group
      _ = (a₀ * b₀) * x := by rw [h]
  have ha₀D := hαD ha₀
  have hb₀D := hβD hb₀
  have hab₀ : a₀ ≠ b₀ := fun h => Set.disjoint_left.mp hdisj ha₀ (h ▸ hb₀)
  have hcab : Commute a₀ b₀ := hαβ a₀ ha₀ b₀ hb₀
  have hzA : a₀ * b₀ ∈ A := A.mul_mem (Subgroup.subset_closure (Or.inl ha₀))
    (Subgroup.subset_closure (Or.inr hb₀))
  have hzS : a₀ * b₀ ∈ (S : Subgroup G) := hAS hzA
  have hz2 : a₀ * b₀ * (a₀ * b₀) = 1 := hAsq _ hzA
  have hz1 : a₀ * b₀ ≠ 1 := fun h => hab₀ (hC.setup.oddT.eq_of_mul_eq_one ha₀D h)
  have hzD : a₀ * b₀ ∉ D := fun h => Set.disjoint_left.mp hdisj
    (mem_block_of_mul_mem hC hH (mem_blockClass_self _) ha₀ ha₀D hb₀D hab₀ hcab h) hb₀
  have hzC : ∀ e ∈ D, Commute e (a₀ * b₀) ↔ e ∈ hC.alpha ∪ β := by
    intro e he
    rw [hC.setup.oddT.commute_mul_iff ha₀D hb₀D he hab₀ hcab,
      ← centSet_inter_eq_of_pCore_eq_bot hC hH hP hβ ha₀ hb₀]
    exact ⟨fun h => ⟨he, h⟩, fun h => h.2⟩
  have hzcomm : ∀ x ∈ A, Commute (a₀ * b₀) x := fun x hx =>
    congrArg Subtype.val (hAc.is_comm.comm ⟨a₀ * b₀, hzA⟩ ⟨x, hx⟩)
  have hzNα : a₀ * b₀ ∈ Subgroup.normalizer hC.alpha :=
    mem_normalizer_block_of_conj_mem hC (mem_blockClass_self _) huα (by
      rw [(hzcomm u (Subgroup.subset_closure (Or.inl huα))).eq, mul_inv_cancel_right]
      exact huα)
  have hwcl : CFSG.LargeExtraspecial.S11.wcl (a₀ * b₀) ≤ A := by
    rw [CFSG.LargeExtraspecial.S11.wcl, Subgroup.closure_le]
    rintro _ ⟨m, rfl, hyz⟩
    obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hβc
    have hρc : (fun x => m * x * m⁻¹) '' hC.alpha ∈ blockClass hC.alpha :=
      mem_blockClass_iff.mpr ⟨m, rfl⟩
    have hσc : (fun x => m * x * m⁻¹) '' β ∈ blockClass hC.alpha := by
      refine mem_blockClass_iff.mpr ⟨m * g, ?_⟩
      rw [hg, Set.image_image]
      congr 1
      ext x
      group
    have hσρ : (fun x => m * x * m⁻¹) '' β ∈ Dalpha D ((fun x => m * x * m⁻¹) '' hC.alpha) :=
      Dalpha.conj hC.setup.normal hβ m
    have hρσ : (fun x => m * x * m⁻¹) '' hC.alpha ≠ (fun x => m * x * m⁻¹) '' β :=
      fun h => (mem_Dalpha_iff.mp hσρ).2.2.1 h.symm
    have hρσcomm := (mem_Dalpha_iff.mp hσρ).2.2.2
    have hρD : (fun x => m * x * m⁻¹) '' hC.alpha ⊆ D := by
      rintro _ ⟨x, hx, rfl⟩
      exact hC.setup.conj_mem m (hαD hx)
    have hσD : (fun x => m * x * m⁻¹) '' β ⊆ D := by
      rintro _ ⟨x, hx, rfl⟩
      exact hC.setup.conj_mem m (hβD hx)
    have hCy : ∀ e ∈ D, Commute e (m * (a₀ * b₀) * m⁻¹) ↔
        e ∈ (fun x => m * x * m⁻¹) '' hC.alpha ∪ (fun x => m * x * m⁻¹) '' β := by
      intro e he
      have he' : m⁻¹ * e * m ∈ D := by simpa using hC.setup.conj_mem m⁻¹ he
      constructor
      · intro h
        have h' := h.conj m⁻¹
        rw [inv_inv, show m⁻¹ * (m * (a₀ * b₀) * m⁻¹) * m = a₀ * b₀ by group] at h'
        rcases (hzC _ he').mp h' with h1 | h1
        · exact Or.inl ⟨_, h1, by group⟩
        · exact Or.inr ⟨_, h1, by group⟩
      · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
        · exact ((hzC x (hαD hx)).mpr (Or.inl hx)).conj m
        · exact ((hzC x (hβD hx)).mpr (Or.inr hx)).conj m
    have hzy : (a₀ * b₀) * (m * (a₀ * b₀) * m⁻¹) * (a₀ * b₀)⁻¹ = m * (a₀ * b₀) * m⁻¹ := by
      rw [← hyz, mul_inv_cancel_right]
    have hpres : ∀ x ∈ (fun x => m * x * m⁻¹) '' hC.alpha ∪ (fun x => m * x * m⁻¹) '' β,
        (a₀ * b₀) * x * (a₀ * b₀)⁻¹ ∈
          (fun x => m * x * m⁻¹) '' hC.alpha ∪ (fun x => m * x * m⁻¹) '' β := by
      intro x hx
      have hxD : x ∈ D := hx.elim (fun h => hρD h) (fun h => hσD h)
      rw [← hCy _ (hC.setup.conj_mem _ hxD)]
      have h := ((hCy x hxD).mpr hx).conj (a₀ * b₀)
      rwa [hzy] at h
    have hm_a : m * a₀ * m⁻¹ ∈ (fun x => m * x * m⁻¹) '' hC.alpha := ⟨a₀, ha₀, rfl⟩
    have hm_b : m * b₀ * m⁻¹ ∈ (fun x => m * x * m⁻¹) '' β := ⟨b₀, hb₀, rfl⟩
    have hy_eq : m * (a₀ * b₀) * m⁻¹ = (m * a₀ * m⁻¹) * (m * b₀ * m⁻¹) := by group
    have hz_inv : (a₀ * b₀)⁻¹ = a₀ * b₀ := inv_eq_of_mul_eq_one_left hz2
    rcases hpres _ (Or.inl hm_a) with hzρ | hzσ
    ·
      have hzNρ := mem_normalizer_block_of_conj_mem hC hρc hm_a hzρ
      have hzNσ : a₀ * b₀ ∈ Subgroup.normalizer ((fun x => m * x * m⁻¹) '' β) := by
        rcases hpres _ (Or.inr hm_b) with h | h
        · exact absurd (block_eq_of_mem hC hρc hσc ((hzNρ _).mpr h) hm_b) hρσ
        · exact mem_normalizer_block_of_conj_mem hC hσc hm_b h
      have hfix : ∀ {γ : Set G}, γ ∈ blockClass hC.alpha →
          a₀ * b₀ ∈ Subgroup.normalizer γ → γ ⊆ hC.alpha ∪ β := by
        intro γ hγ hzN
        obtain ⟨r, hrγ, hr⟩ := exists_fixed_conj_of_mem_normalizer (Set.toFinite γ)
          (by rw [hblk_card γ hγ]; exact hmodd) hz2 hzN
        have hrD : r ∈ D := (isBlock_of_mem_blockClass hC.setup.normal hC.isBlock_alpha hγ).subset
          hrγ
        have hrz : Commute r (a₀ * b₀) := by
          change r * (a₀ * b₀) = (a₀ * b₀) * r
          calc r * (a₀ * b₀) = (a₀ * b₀) * r * (a₀ * b₀)⁻¹ * (a₀ * b₀) := by rw [hr]
            _ = (a₀ * b₀) * r := by group
        rcases (hzC r hrD).mp hrz with h | h
        · rw [block_eq_of_mem hC hγ (mem_blockClass_self _) hrγ h]
          exact Set.subset_union_left
        · rw [block_eq_of_mem hC hγ hβc hrγ h]
          exact Set.subset_union_right
      rw [hy_eq]
      exact A.mul_mem (Subgroup.subset_closure (hfix hρc hzNρ hm_a))
        (Subgroup.subset_closure (hfix hσc hzNσ hm_b))
    ·
      exfalso
      have hinvol : ∀ w, (a₀ * b₀) * ((a₀ * b₀) * w * (a₀ * b₀)⁻¹) * (a₀ * b₀)⁻¹ = w := by
        intro w
        rw [hz_inv]
        calc a₀ * b₀ * (a₀ * b₀ * w * (a₀ * b₀)) * (a₀ * b₀) =
            (a₀ * b₀ * (a₀ * b₀)) * w * (a₀ * b₀ * (a₀ * b₀)) := by group
          _ = w := by rw [hz2, one_mul, mul_one]
      have hzρc : (fun x => (a₀ * b₀) * x * (a₀ * b₀)⁻¹) '' ((fun x => m * x * m⁻¹) '' hC.alpha) ∈
          blockClass hC.alpha := by
        refine mem_blockClass_iff.mpr ⟨(a₀ * b₀) * m, ?_⟩
        rw [Set.image_image]
        congr 1
        ext x
        group
      have hzρσ : (fun x => (a₀ * b₀) * x * (a₀ * b₀)⁻¹) '' ((fun x => m * x * m⁻¹) '' hC.alpha) =
          (fun x => m * x * m⁻¹) '' β :=
        block_eq_of_mem hC hzρc hσc ⟨_, hm_a, rfl⟩ hzσ
      have hzmap : ∀ r ∈ (fun x => m * x * m⁻¹) '' hC.alpha,
          (a₀ * b₀) * r * (a₀ * b₀)⁻¹ ∈ (fun x => m * x * m⁻¹) '' β := fun r hr =>
        hzρσ ▸ ⟨r, hr, rfl⟩
      have hzσρ : (fun x => (a₀ * b₀) * x * (a₀ * b₀)⁻¹) '' ((fun x => m * x * m⁻¹) '' β) =
          (fun x => m * x * m⁻¹) '' hC.alpha := by
        rw [← hzρσ, Set.image_image]
        ext x
        constructor
        · rintro ⟨w, hw, rfl⟩
          change (a₀ * b₀) * ((a₀ * b₀) * w * (a₀ * b₀)⁻¹) * (a₀ * b₀)⁻¹ ∈ _
          rw [hinvol]
          exact hw
        · intro hx
          exact ⟨x, hx, hinvol x⟩
      have hyfz : ∀ r ∈ (fun x => m * x * m⁻¹) '' hC.alpha,
          Commute (r * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹)) (a₀ * b₀) := by
        intro r hr
        have hc := hρσcomm r hr _ (hzmap r hr)
        have key : (a₀ * b₀) * (r * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹)) * (a₀ * b₀)⁻¹ =
            r * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹) := by
          calc (a₀ * b₀) * (r * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹)) * (a₀ * b₀)⁻¹ =
              ((a₀ * b₀) * r * (a₀ * b₀)⁻¹) *
                ((a₀ * b₀) * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹) * (a₀ * b₀)⁻¹) := by group
            _ = ((a₀ * b₀) * r * (a₀ * b₀)⁻¹) * r := by rw [hinvol]
            _ = r * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹) := hc.eq.symm
        change r * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹) * (a₀ * b₀) =
          (a₀ * b₀) * (r * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹))
        calc r * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹) * (a₀ * b₀) =
            ((a₀ * b₀) * (r * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹)) * (a₀ * b₀)⁻¹) * (a₀ * b₀) := by
              rw [key]
          _ = (a₀ * b₀) * (r * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹)) := by group
      have hyN_or : ∀ r ∈ (fun x => m * x * m⁻¹) '' hC.alpha,
          r * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹) ∈ Subgroup.normalizer hC.alpha ∨
            (fun x => (r * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹)) * x *
              (r * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹))⁻¹) '' hC.alpha = β := by
        intro r hr
        set y := r * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹) with hy
        have hyu : y * u * y⁻¹ ∈ hC.alpha ∪ β := by
          rw [← hzC _ (hC.setup.conj_mem _ (hαD huα))]
          have h := ((hzC u (hαD huα)).mpr (Or.inl huα)).conj y
          rwa [show y * (a₀ * b₀) * y⁻¹ = a₀ * b₀ by
            rw [(hyfz r hr).eq, mul_inv_cancel_right]] at h
        rcases hyu with h | h
        · exact Or.inl (mem_normalizer_block_of_conj_mem hC (mem_blockClass_self _) huα h)
        · exact Or.inr (block_eq_of_mem hC (mem_blockClass_iff.mpr ⟨y, rfl⟩) hβc ⟨u, huα, rfl⟩ h)
      have hρcard : 1 < ((fun x => m * x * m⁻¹) '' hC.alpha).ncard := by
        rw [hblk_card _ hρc]
        omega
      obtain ⟨r₁, r₂, hr₁, hr₂, hr12⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp hρcard
      have hr3 : r₁ * r₂ ∈ (fun x => m * x * m⁻¹) '' hC.alpha := hblk_mul _ hρc r₁ hr₁ r₂ hr₂ hr12
      have hy3 : (r₁ * r₂) * ((a₀ * b₀) * (r₁ * r₂) * (a₀ * b₀)⁻¹) =
          (r₁ * ((a₀ * b₀) * r₁ * (a₀ * b₀)⁻¹)) * (r₂ * ((a₀ * b₀) * r₂ * (a₀ * b₀)⁻¹)) := by
        have hc := hρσcomm r₂ hr₂ _ (hzmap r₁ hr₁)
        calc (r₁ * r₂) * ((a₀ * b₀) * (r₁ * r₂) * (a₀ * b₀)⁻¹) =
            r₁ * (r₂ * ((a₀ * b₀) * r₁ * (a₀ * b₀)⁻¹)) * ((a₀ * b₀) * r₂ * (a₀ * b₀)⁻¹) := by group
          _ = r₁ * (((a₀ * b₀) * r₁ * (a₀ * b₀)⁻¹) * r₂) * ((a₀ * b₀) * r₂ * (a₀ * b₀)⁻¹) := by
            rw [hc.eq]
          _ = _ := by group
      have hswap : ∀ c : G, Commute c (a₀ * b₀) →
          (fun x => c * x * c⁻¹) '' hC.alpha = β → (fun x => c * x * c⁻¹) '' β = hC.alpha := by
        intro c hcz hcα
        have hcv : c * v * c⁻¹ ∈ hC.alpha ∪ β := by
          rw [← hzC _ (hC.setup.conj_mem _ hvD)]
          have h := ((hzC v hvD).mpr (Or.inr hv)).conj c
          rwa [show c * (a₀ * b₀) * c⁻¹ = a₀ * b₀ by rw [hcz.eq, mul_inv_cancel_right]] at h
        have hcβc : (fun x => c * x * c⁻¹) '' β ∈ blockClass hC.alpha := by
          obtain ⟨g, hg⟩ := mem_blockClass_iff.mp hβc
          refine mem_blockClass_iff.mpr ⟨c * g, ?_⟩
          rw [hg, Set.image_image]
          congr 1
          ext x
          group
        rcases hcv with h | h
        · exact block_eq_of_mem hC hcβc (mem_blockClass_self _) ⟨v, hv, rfl⟩ h
        · exfalso
          have h1 := block_eq_of_mem hC hcβc hβc ⟨v, hv, rfl⟩ h
          have h2 : (fun x => c * x * c⁻¹) '' β = (fun x => c * x * c⁻¹) '' hC.alpha :=
            h1.trans hcα.symm
          have hinj : Function.Injective fun x : G => c * x * c⁻¹ := fun a b h => by
            simpa using h
          exact hβα ((Set.image_injective.mpr hinj) h2)
      obtain ⟨r, hr, hrN⟩ : ∃ r ∈ (fun x => m * x * m⁻¹) '' hC.alpha,
          r * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹) ∈ Subgroup.normalizer hC.alpha := by
        rcases hyN_or r₁ hr₁ with h1 | h1
        · exact ⟨r₁, hr₁, h1⟩
        rcases hyN_or r₂ hr₂ with h2 | h2
        · exact ⟨r₂, hr₂, h2⟩
        refine ⟨r₁ * r₂, hr3, ?_⟩
        rw [hy3]
        refine mem_normalizer_block_of_conj_mem hC (mem_blockClass_self _) huα ?_
        have hu2 : (r₂ * ((a₀ * b₀) * r₂ * (a₀ * b₀)⁻¹)) * u *
            (r₂ * ((a₀ * b₀) * r₂ * (a₀ * b₀)⁻¹))⁻¹ ∈ β := h2 ▸ ⟨u, huα, rfl⟩
        have hβα' := hswap _ (hyfz r₁ hr₁) h1
        have hu3 : (r₁ * ((a₀ * b₀) * r₁ * (a₀ * b₀)⁻¹)) *
            ((r₂ * ((a₀ * b₀) * r₂ * (a₀ * b₀)⁻¹)) * u *
              (r₂ * ((a₀ * b₀) * r₂ * (a₀ * b₀)⁻¹))⁻¹) *
            (r₁ * ((a₀ * b₀) * r₁ * (a₀ * b₀)⁻¹))⁻¹ ∈ hC.alpha := hβα' ▸ ⟨_, hu2, rfl⟩
        convert hu3 using 1
        group
      have hrD : r ∈ D := hρD hr
      have hr'σ := hzmap r hr
      have hr'D : (a₀ * b₀) * r * (a₀ * b₀)⁻¹ ∈ D := hσD hr'σ
      have hcrr := hρσcomm r hr _ hr'σ
      have hrr' : r ≠ (a₀ * b₀) * r * (a₀ * b₀)⁻¹ := fun h =>
        hρσ (block_eq_of_mem hC hρc hσc hr (h ▸ hr'σ))
      have hy2' : ∀ r' : G, r * r' = r' * r → r' * r' = 1 → r * r' * (r * r') = 1 := by
        intro r' hc h2
        calc r * r' * (r * r') = r * (r' * r) * r' := by group
          _ = r * (r * r') * r' := by rw [← hc]
          _ = (r * r) * (r' * r') := by group
          _ = 1 := by rw [hC.setup.oddT.mul_self_eq_one hrD, h2, one_mul]
      have hy2 := hy2' _ hcrr.eq (hC.setup.oddT.mul_self_eq_one hr'D)
      obtain ⟨a', ha'α, ha'⟩ := exists_fixed_conj_of_mem_normalizer (Set.toFinite _)
        (by rw [hαcard]; exact hmodd) hy2 hrN
      have ha'D := hαD ha'α
      have ha'y : Commute a' (r * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹)) := by
        change a' * _ = _ * a'
        calc a' * (r * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹)) =
            ((r * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹)) * a' * (r * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹))⁻¹) *
              (r * ((a₀ * b₀) * r * (a₀ * b₀)⁻¹)) := by rw [ha']
          _ = _ := by group
      obtain ⟨ha'r, ha'r'⟩ := (hC.setup.oddT.commute_mul_iff hrD hr'D ha'D hrr' hcrr).mp ha'y
      have ha'ρσ := centSet_inter_eq_conj hC hH hP m hσρ hr hr'σ ha'D ha'r ha'r'
      have hzα := conj_image_block_eq hzNα
      rcases ha'ρσ with h | h
      · have hαρ := block_eq_of_mem hC (mem_blockClass_self _) hρc ha'α h
        apply hρσ
        rw [← hzρσ, ← hαρ, hzα]
      · have hασ := block_eq_of_mem hC (mem_blockClass_self _) hσc ha'α h
        apply hρσ
        rw [← hzσρ, ← hασ, hzα]
  obtain ⟨a₁, a₂, ha₁, ha₂, ha12⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp
    (show 1 < hC.alpha.ncard by rw [hαcard]; omega)
  have h12G : a₁ * a₂ ∈ commutator G := hC.setup.mul_mem_commutator (hαD ha₁) (hαD ha₂)
  have h12D : a₁ * a₂ ∈ D := hαD (hαm a₁ ha₁ a₂ ha₂ ha12)
  have hcomm_top : commutator G = ⊤ := by
    rw [eq_top_iff, ← hC.setup.gen, Subgroup.closure_le]
    intro d hd
    obtain ⟨c, rfl⟩ := isConj_iff.mp (hC.setup.isConj h12D hd)
    exact (inferInstance : (commutator G).Normal).conj_mem _ h12G c
  have hsimpleG : IsSimpleGroup G := by
    have h : IsSimpleGroup ↥(⊤ : Subgroup G) := hcomm_top ▸ hs
    exact (Subgroup.topEquiv (G := G)).symm.isSimpleGroup
  obtain ⟨x₁, hx₁, x₂, hx₂, hx12⟩ := exists_not_commute_DalphaStar hC hH
  have hnonab : ∃ a b : G, a * b ≠ b * a := ⟨x₁, x₂, hx12⟩
  have hPS : P ⊂ ((S : Subgroup G) : Set G) := by
    refine ⟨fun x hx => ?_, fun h => ?_⟩
    · obtain ⟨a, ha, b, hb, rfl⟩ := hx
      exact hAS (A.mul_mem (Subgroup.subset_closure (Or.inl ha))
        (Subgroup.subset_closure (Or.inr hb)))
    · obtain ⟨a, ha, b, hb, hab⟩ := h (S : Subgroup G).one_mem
      have hab' : a * b = 1 := hab.symm
      exact Set.disjoint_left.mp hdisj ha
        ((hC.setup.oddT.eq_of_mul_eq_one (hαD ha) hab') ▸ hb)
  have hScard : 16 ≤ Nat.card (S : Subgroup G) := by
    have hlt := Set.ncard_lt_ncard hPS (Set.toFinite _)
    rw [hPcard] at hlt
    have h9 : 9 ≤ (2 ^ k - 1) * (2 ^ k - 1) := Nat.mul_le_mul hm3 hm3
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    have hSn : ((S : Subgroup G) : Set G).ncard = 2 ^ n := by
      rw [← Nat.card_coe_set_eq]
      exact hn
    rw [hSn] at hlt
    rw [hn]
    by_contra h16
    have hn4 : n < 4 := by
      by_contra hn4
      exact h16 (by
        calc 16 = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega))
    interval_cases n <;> omega
  have hab : IsMulCommutative (CFSG.LargeExtraspecial.S11.wcl (a₀ * b₀)) :=
    ⟨⟨fun x y => Subtype.ext (show (x : G) * y = y * x from congrArg Subtype.val
      (hAc.is_comm.comm ⟨x, hwcl x.2⟩ ⟨y, hwcl y.2⟩))⟩⟩
  have hB := isBenderGroup_of_wcl_abelian hnonab S hzS hz1 hzc hab hScard
  have hzord : orderOf (a₀ * b₀) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1
  have hconj := IsBenderGroup.isConj_of_orderOf_eq_two hB
    (hC.setup.oddT.orderOf_eq_two (hαD huα)) hzord
  apply hzD
  rw [hC.setup.eq_setOf_isConj (hαD huα)]
  exact hconj

end Main

end CFSG.OddTranspositions.PartThree.Nine
