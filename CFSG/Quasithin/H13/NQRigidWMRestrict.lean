module

public import CFSG.Quasithin.Background.InternalSecB56
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.H13.NQRigidWMSetup

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Quasithin CFSG.Quasithin.InternalSec CFSG.QuasithinUnique
  CFSG.Assembly.LowTwoRank
open CFSG.Open (pCoreOf)
open scoped IsMulCommutative commutatorElement

section SQTKImage

@[expose] def IsSQTKImage (Y : Type) [Group Y] : Prop :=
  ∃ (X : Type) (_ : Group X) (_ : Finite X), SQTKGroup X ∧ ∃ f : X →* Y, Function.Surjective f

theorem isSQTKImage_of_b53Hyp {V : Type} [CommGroup V] [Finite V] {J : Subgroup (MulAut V)}
    (h : B53Hyp J) : IsSQTKImage ↥J := by
  obtain ⟨-, -, X, _, _, N, _, hS, ⟨e⟩⟩ := h
  exact ⟨X, inferInstance, inferInstance, hS, e.symm.toMonoidHom.comp (QuotientGroup.mk' N),
    e.symm.surjective.comp (QuotientGroup.mk'_surjective N)⟩

theorem IsSQTKImage.of_surjective {Y Z : Type} [Group Y] [Group Z] (h : IsSQTKImage Y)
    (g : Y →* Z) (hg : Function.Surjective g) : IsSQTKImage Z := by
  obtain ⟨X, _, _, hS, f, hf⟩ := h
  exact ⟨X, inferInstance, inferInstance, hS, g.comp f, hg.comp hf⟩

theorem IsSQTKImage.subgroup {Y : Type} [Group Y] (h : IsSQTKImage Y) (H : Subgroup Y) :
    IsSQTKImage ↥H := by
  obtain ⟨X, _, _, hS, f, hf⟩ := h
  refine ⟨↥(H.comap f), inferInstance, inferInstance, sqtkGroup_subgroup hS _,
    f.subgroupComap H, ?_⟩
  rintro ⟨y, hy⟩
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨⟨x, hy⟩, rfl⟩

theorem IsSQTKImage.b53 {Y : Type} [Group Y] (h : IsSQTKImage Y) :
    ∃ (X : Type) (_ : Group X) (_ : Finite X) (N : Subgroup X) (_ : N.Normal),
      SQTKGroup X ∧ Nonempty (Y ≃* X ⧸ N) := by
  obtain ⟨X, _, _, hS, f, hf⟩ := h
  exact ⟨X, inferInstance, inferInstance, f.ker, inferInstance, hS,
    ⟨(QuotientGroup.quotientKerEquivOfSurjective f hf).symm⟩⟩

end SQTKImage

section Centralizer

variable {Ω : Type*} [Group Ω]

theorem not_isPGroup_two_of_simple {K : Type*} [Group K] [Finite K] [IsSimpleGroup K]
    (hnab : ∃ a b : K, a * b ≠ b * a) : ¬ IsPGroup 2 K := by
  intro hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial K := IsSimpleGroup.toNontrivial
  have hc := hp.center_nontrivial
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center K) with h | h
  · rw [h] at hc
    obtain ⟨x, y, hxy⟩ := hc
    exact hxy (Subsingleton.elim x y)
  · obtain ⟨a, b, hab⟩ := hnab
    exact hab ((mem_center_iff.mp (h ▸ mem_top b)) a)

theorem pCoreOf_eq_bot_of_centralizer [Finite Ω] {J K : Subgroup Ω} (hKJ : K ≤ J)
    (hn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hKs : IsSimpleGroup ↥K)
    (hnab : ∃ a b : ↥K, a * b ≠ b * a)
    (hC : ∀ x ∈ J, (∀ k ∈ K, x * k = k * x) → x = 1) : pCoreOf 2 J = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pCoreOf, map_eq_bot_iff_of_injective _ J.subtype_injective, CFSG.pCore_eq_iSup]
  refine le_bot_iff.mp (iSup_le fun N => iSup_le fun hN => iSup_le fun hp => ?_)
  intro x hx
  rw [mem_bot]
  apply Subtype.ext
  apply hC x x.2
  intro k hk
  set P : Subgroup Ω := N.map J.subtype with hP
  have hPK : ∀ y ∈ P, y ∈ K → y = 1 := by
    intro y hyP hyK
    set Q : Subgroup ↥K := (P ⊓ K).subgroupOf K with hQ
    have hQn : Q.Normal := by
      refine ⟨fun q hq c => ?_⟩
      rw [hQ, mem_subgroupOf] at hq ⊢
      refine mem_inf.mpr ⟨?_, ?_⟩
      · obtain ⟨n, hn', hnq⟩ := (mem_inf.mp hq).1
        refine ⟨⟨c, hKJ c.2⟩ * n * ⟨c, hKJ c.2⟩⁻¹, hN.conj_mem n hn' _, ?_⟩
        simp only [coe_subtype, coe_mul, coe_inv] at hnq ⊢
        rw [hnq]
      · exact mul_mem (mul_mem c.2 (mem_inf.mp hq).2) (inv_mem c.2)
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Q with h | h
    · have : (⟨y, hyK⟩ : ↥K) ∈ Q := mem_subgroupOf.mpr (mem_inf.mpr ⟨hyP, hyK⟩)
      rw [h, mem_bot] at this
      exact congrArg Subtype.val this
    · exfalso
      apply not_isPGroup_two_of_simple hnab
      intro z
      have hz : z ∈ Q := by rw [h]; trivial
      have hzP : (z : Ω) ∈ P := (mem_inf.mp (mem_subgroupOf.mp hz)).1
      obtain ⟨n, hnN, hnz⟩ := hzP
      obtain ⟨e, he⟩ := hp ⟨n, hnN⟩
      refine ⟨e, Subtype.ext ?_⟩
      have h1 := congrArg (fun t : ↥N => ((t : ↥J) : Ω)) he
      simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
      rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← hnz]
      exact h1
  have hxk : ⁅(x : Ω), k⁆ = 1 := by
    apply hPK
    · refine ⟨x * ⟨k, hKJ hk⟩ * x⁻¹ * ⟨k, hKJ hk⟩⁻¹, ?_, ?_⟩
      · have h1 : (⟨k, hKJ hk⟩ : ↥J) * x⁻¹ * (⟨k, hKJ hk⟩ : ↥J)⁻¹ ∈ N :=
          hN.conj_mem _ (inv_mem hx) _
        have h2 : x * (⟨k, hKJ hk⟩ * x⁻¹ * (⟨k, hKJ hk⟩ : ↥J)⁻¹) ∈ N := mul_mem hx h1
        simpa [mul_assoc] using h2
      · simp [commutatorElement_def]
    · rw [commutatorElement_def]
      exact mul_mem (hn x x.2 k hk) (inv_mem hk)
  rw [commutatorElement_eq_one_iff_mul_comm] at hxk
  exact hxk

theorem ne_bot_of_one_lt_card {X : Subgroup Ω} (h : 1 < Nat.card ↥X) : X ≠ ⊥ := by
  intro h0
  rw [h0, card_bot] at h
  exact lt_irrefl 1 h

theorem ne_bot_of_b56FactorList {Ω : Type} [Group Ω] {X : Subgroup Ω} (h : B56FactorList ↥X) :
    X ≠ ⊥ := by
  apply ne_bot_of_one_lt_card
  rcases h with ⟨n, F, _, _, hn, hF, ⟨e⟩⟩ | he | ⟨m, F, _, _, hm, -, hF, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv, card_statedSL_two1527d, hF]
    have h2 : 2 ≤ 2 ^ n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    have h4 : 4 ≤ (2 ^ n) ^ 2 := by nlinarith
    have : 3 ≤ (2 ^ n) ^ 2 - 1 := by omega
    nlinarith
  · obtain ⟨e⟩ := he
    rw [Nat.card_congr e.toEquiv, Nat.card_perm, Nat.card_fin]
    decide
  · rw [Nat.card_congr e.toEquiv, card_statedSL_three1527d, hF]
    have h2 : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h4 : 4 ≤ (2 ^ m) ^ 2 := by nlinarith
    have h8 : 8 ≤ (2 ^ m) ^ 3 := by nlinarith
    have : 3 ≤ (2 ^ m) ^ 2 - 1 := by omega
    have : 7 ≤ (2 ^ m) ^ 3 - 1 := by omega
    have h5 : 1 ≤ ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1) := by nlinarith
    nlinarith

theorem one_lt_card_statedSL_three_two : 1 < Nat.card ↥(StatedSL 3 (ZMod 2)) := by
  rw [card_statedSL_three1527d, Nat.card_zmod]
  decide

end Centralizer

section Case1

variable {V : Type} [CommGroup V] [Finite V]

theorem b56Case1_of_centralizer {J K : Subgroup (MulAut V)} (hKJ : K ≤ J)
    (hn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hK : CFSG.IsQuasisimple ↥K)
    (hC : ∀ j ∈ J, (∀ k ∈ K, j * k = k * j) → j = 1)
    (hcases : B56Case1 J ∨ B56Case2 J ∨ B56Case3 J ∨ B56Case4 J ∨ B56Case5 J) : B56Case1 J := by
  have hfac : ∀ {G₁ G₂ : Subgroup (MulAut V)}, G₂ ≤ J → (∀ a ∈ G₁, ∀ b ∈ G₂, a * b = b * a) →
      K ≤ G₁ → G₂ = ⊥ := by
    intro G₁ G₂ hG₂ hc hK1
    rw [eq_bot_iff]
    intro b hb
    rw [mem_bot]
    exact hC b (hG₂ hb) fun k hk => (hc k (hK1 hk) b hb).symm
  rcases hcases with h1 | ⟨⟨e⟩, -⟩ | ⟨G₁, G₂, hsup, -, hc, hf₁, hf₂, -⟩ |
      ⟨G₁, G₂, t, hJt, -, hc, ⟨e₁⟩, hc₂, -, -, -, -, -, ht₁, ht₂, -⟩ |
      ⟨G₁, G₂, hsup, -, hc, -, ⟨e₁⟩, -, -, h₂⟩
  · exact h1
  · exact (not_le_perm_three hK hKJ e).elim
  · exfalso
    have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
    have h₁J : G₁ ≤ J := hsup ▸ le_sup_left
    have h₂J : G₂ ≤ J := hsup ▸ le_sup_right
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hK with h | h
    · exact ne_bot_of_b56FactorList hf₂ (hfac h₂J hc h)
    · exact ne_bot_of_b56FactorList hf₁ (hfac h₁J hc' h)
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h₂J : G₂ ≤ J := by rw [hJt]; exact le_sup_right.trans le_sup_left
    rcases le_or_le_of_sup_zpowers hJt hc ht₁ ht₂ hKJ hn hK with h | h
    · have h0 := hfac h₂J hc h
      rw [h0, card_bot] at hc₂
      omega
    · exact not_le_of_card_prime hK h hc₂
  · exfalso
    have hc' : ∀ a ∈ G₂, ∀ b ∈ G₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
    have h₁J : G₁ ≤ J := hsup ▸ le_sup_left
    have h₂J : G₂ ≤ J := hsup ▸ le_sup_right
    rcases le_or_le_of_sup_eq hsup hc hKJ hn hK with h | h
    · apply ne_bot_of_one_lt_card (X := G₂) _ (hfac h₂J hc h)
      rcases h₂ with ⟨⟨e₂⟩, -⟩ | ⟨n, F, _, _, hF, π, hπ⟩
      · rw [Nat.card_congr e₂.toEquiv]
        exact one_lt_card_statedSL_three_two
      · rw [card_eq_of_nat_realizes1527d hπ, card_statedSL_two1527d]
        have h2 : 2 ≤ Nat.card F := Finite.one_lt_card
        have h4 : 4 ≤ Nat.card F ^ 2 := by nlinarith
        have : 3 ≤ Nat.card F ^ 2 - 1 := by omega
        nlinarith
    · apply ne_bot_of_one_lt_card (X := G₁) _ (hfac h₁J hc' h)
      rw [Nat.card_congr e₁.toEquiv]
      exact one_lt_card_statedSL_three_two

end Case1

section Restrict

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem le_stabSub_fixV {J D : Subgroup (MulAut V)}
    (hDn : ∀ x ∈ J, ∀ d ∈ D, x * d * x⁻¹ ∈ D) : J ≤ stabSub (fixV D) := by
  have key : ∀ j ∈ J, ∀ v ∈ fixV D, j v ∈ fixV D := by
    intro j hj v hv d hd
    have h1 : j⁻¹ * d * j⁻¹⁻¹ ∈ D := hDn j⁻¹ (J.inv_mem hj) d hd
    have h2 := hv _ h1
    rw [inv_inv, MulAut.mul_apply, MulAut.mul_apply] at h2
    have h3 := congrArg j h2
    rwa [MulAut.inv_apply, MulEquiv.apply_symm_apply] at h3
  intro j hj v
  refine ⟨fun h => ?_, fun h => key j hj v h⟩
  have := key j⁻¹ (J.inv_mem hj) _ h
  rwa [MulAut.inv_apply, MulEquiv.symm_apply_apply] at this

theorem b51Conclusion_of_restrict (h56 : AsB56) (hV : ∀ v : V, v ^ 2 = 1)
    {J K A D X : Subgroup (MulAut V)} (hJ : B53Hyp J) (hKJ : K ≤ J)
    (hn : ∀ x ∈ J, ∀ k ∈ K, x * k * x⁻¹ ∈ K) (hKs : IsSimpleGroup ↥K)
    (hnab : ∃ a b : ↥K, a * b ≠ b * a) (hA : IsFFStarOffender X A) (hAJ : A ≤ J)
    (hKA : ⁅K, A⁆ = K) (hDn : ∀ x ∈ J, ∀ d ∈ D, x * d * x⁻¹ ∈ D)
    (hCD : ∀ j ∈ J, (∀ k ∈ K, j * k = k * j) → j ∈ D)
    (hfaith : ∀ k ∈ K, (∀ v ∈ fixV D, k v = v) → k = 1) :
    ∃ H : Subgroup (MulAut ↥(fixV D)), B51Conclusion H (autSub K (fixV D)) := by
  classical
  set V₀ := fixV D with hV₀
  have hJst : J ≤ stabSub V₀ := le_stabSub_fixV hDn
  have hKst : K ≤ stabSub V₀ := hKJ.trans hJst
  have hAst : A ≤ stabSub V₀ := hAJ.trans hJst
  set rK : ↥K →* MulAut ↥V₀ := (resHom V₀).comp (inclusion hKst) with hrKdef
  have hrK : Function.Injective rK := by
    rw [injective_iff_map_eq_one]
    intro k hk
    apply Subtype.ext
    apply hfaith k k.2
    intro v hv
    have := congrArg (fun φ : MulAut ↥V₀ => ((φ ⟨v, hv⟩ : V₀) : V)) hk
    exact this
  have hK₀ : autSub K V₀ = rK.range := B1Red.autSub_eq_range hKst
  let eK : ↥K ≃* ↥(autSub K V₀) :=
    (MonoidHom.ofInjective hrK).trans (MulEquiv.subgroupCongr hK₀.symm)
  have hK₀s : IsSimpleGroup ↥(autSub K V₀) := eK.symm.isSimpleGroup
  have hK₀nab : ∃ a b : ↥(autSub K V₀), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eK a, eK b, fun h => hab (eK.injective (by rw [map_mul, map_mul, h]))⟩
  have hK₀q : CFSG.IsQuasisimple ↥(autSub K V₀) := isQuasisimple_of_simple_nonab hK₀nab
  have hK₀H : autSub K V₀ ≤ autSub J V₀ := autSub_mono hKJ V₀
  have hA₀H : autSub A V₀ ≤ autSub J V₀ := autSub_mono hAJ V₀
  have hK₀n : ∀ x ∈ autSub J V₀, ∀ k ∈ autSub K V₀, x * k * x⁻¹ ∈ autSub K V₀ := by
    intro x hx k hk
    obtain ⟨g, hgJ, rfl⟩ := mem_autSub.1 hx
    obtain ⟨c, hcK, rfl⟩ := mem_autSub.1 hk
    refine mem_autSub.2 ⟨g * c * g⁻¹, hn _ hgJ _ hcK, ?_⟩
    rw [map_mul, map_mul, map_inv]
  have hCH : ∀ x ∈ autSub J V₀, (∀ k ∈ autSub K V₀, x * k = k * x) → x = 1 := by
    intro x hx hxc
    obtain ⟨g, hgJ, rfl⟩ := mem_autSub.1 hx
    have hgD : (g : MulAut V) ∈ D := by
      apply hCD g hgJ
      intro k hk
      have hgk : (g : MulAut V) * k * (g : MulAut V)⁻¹ ∈ K := hn g hgJ k hk
      have h1 : rK ⟨_, hgk⟩ = rK ⟨k, hk⟩ := by
        have e1 : rK ⟨_, hgk⟩ = resHom V₀ g * resHom V₀ ⟨k, hKst hk⟩ * (resHom V₀ g)⁻¹ := by
          rw [← map_inv, ← map_mul, ← map_mul]
          rfl
        rw [e1, hxc _ (mem_autSub.2 ⟨⟨k, hKst hk⟩, hk, rfl⟩), mul_inv_cancel_right]
        rfl
      have h2 : (g : MulAut V) * k * (g : MulAut V)⁻¹ = k := congrArg Subtype.val (hrK h1)
      calc (g : MulAut V) * k = ((g : MulAut V) * k * (g : MulAut V)⁻¹) * (g : MulAut V) := by
            group
        _ = k * g := by rw [h2]
    ext v
    rw [resHom_apply]
    exact v.2 g hgD
  have hAnt : ¬ A ≤ centSub V₀ := by
    intro hAc
    have hKc : K ≤ centSub V₀ := by
      rw [← hKA, commutator_le]
      intro k hk a ha v hv
      have hav : ∀ w ∈ V₀, a w = w := hAc ha
      have hkiv : k⁻¹ v ∈ V₀ := (hKst (K.inv_mem hk) v).2 hv
      have hai : a⁻¹ v = v := by
        have h1 := hav v hv
        calc a⁻¹ v = a⁻¹ (a v) := by rw [h1]
          _ = v := by rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
      show (k * a * k⁻¹ * a⁻¹) v = v
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, hai, hav _ hkiv,
        ← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
    obtain ⟨x, hx⟩ := exists_ne (1 : ↥K)
    exact hx (Subtype.ext (hfaith x x.2 (hKc x.2)))
  have hA₀ : IsFFStarOffender (autSub J V₀) (autSub A V₀) := by
    have h1 := B1Red.isFFStarOffender_autSub hA (fun a ha w hw => (hAst ha w).2 hw) hAnt
    exact ⟨hA₀H, h1.2⟩
  have hK₀A₀ : ⁅autSub K V₀, autSub A V₀⁆ = autSub K V₀ := by
    have hnorm : autSub A V₀ ≤ normalizer ((autSub K V₀ : Subgroup (MulAut ↥V₀)) : Set _) := by
      intro a ha
      rw [mem_normalizer_iff]
      intro k
      refine ⟨fun hk => hK₀n a (hA₀H ha) k hk, fun hk => ?_⟩
      have := hK₀n a⁻¹ (inv_mem (hA₀H ha)) _ hk
      simpa [mul_assoc] using this
    rcases commutator_eq_or_eq_bot_of_simple hK₀s hnorm with h | h
    · exact h
    · exfalso
      apply hA₀.2.1
      rw [eq_bot_iff]
      intro a ha
      rw [mem_bot]
      apply hCH a (hA₀H ha)
      intro k hk
      have hc := (commutator_eq_bot_iff_le_centralizer.mp h) hk
      exact (mem_centralizer_iff.mp hc) a ha
  set J₂ := ffJ (autSub J V₀) with hJ₂
  have hK₀J : autSub K V₀ ≤ J₂ := B1Red.K_le_ffJ hK₀H hA₀ hK₀A₀
  have hJ₂H : J₂ ≤ autSub J V₀ := B6.ffJ_le _
  have hJ₂n : ∀ x ∈ J₂, ∀ k ∈ autSub K V₀, x * k * x⁻¹ ∈ autSub K V₀ :=
    fun x hx k hk => hK₀n x (hJ₂H hx) k hk
  have hJ₂C : ∀ j ∈ J₂, (∀ k ∈ autSub K V₀, j * k = k * j) → j = 1 :=
    fun j hj hjc => hCH j (hJ₂H hj) hjc
  have hb53 : B53Hyp J₂ := by
    refine ⟨pCoreOf_eq_bot_of_centralizer hK₀J hJ₂n hK₀s hK₀nab hJ₂C, (ffJ_ffJ _).symm, ?_⟩
    have h1 : IsSQTKImage ↥J := isSQTKImage_of_b53Hyp hJ
    have hrJ : autSub J V₀ = ((resHom V₀).comp (inclusion hJst)).range :=
      B1Red.autSub_eq_range hJst
    let fJ : ↥J →* ↥(autSub J V₀) :=
      ((resHom V₀).comp (inclusion hJst)).codRestrict (autSub J V₀) fun j => by
        rw [hrJ]
        exact ⟨j, rfl⟩
    have hfJ : Function.Surjective fJ := by
      rintro ⟨y, hy⟩
      rw [hrJ] at hy
      obtain ⟨j, rfl⟩ := hy
      exact ⟨j, rfl⟩
    have h2 := (h1.of_surjective fJ hfJ).subgroup (J₂.subgroupOf (autSub J V₀))
    exact (h2.of_surjective (subgroupOfEquivOfLe hJ₂H).toMonoidHom
      (subgroupOfEquivOfLe hJ₂H).surjective).b53
  have hV₀2 : ∀ v : ↥V₀, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV v)
  have hJ₂ne : J₂ ≠ ⊥ := fun h0 => ne_bot_of_isSimpleGroup hK₀s (le_bot_iff.mp (h0 ▸ hK₀J))
  have hcases := h56 ↥V₀ hV₀2 J₂ hJ₂ne hb53
  have h1 := b56Case1_of_centralizer hK₀J hJ₂n hK₀q hJ₂C hcases
  have hF := eq_of_le_quasisimple hK₀J hJ₂n hK₀q h1.1
  exact ⟨J₂, hF ▸ h1.2.1⟩

end Restrict

end CFSG.Quasithin.H13.NQRigid
