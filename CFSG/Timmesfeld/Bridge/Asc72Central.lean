module

public import CFSG.Timmesfeld.Bridge.Asc72Bender
public import CFSG.Timmesfeld.Bridge.SchurNarrow
public import CFSG.Walter.W67.CentralExt
public import CFSG.Timmesfeld.Bridge.Asc72Basic

public section

namespace CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
open scoped commutatorElement

variable {G : Type} [Group G] {D : Set G}

namespace Setup

variable (hS : Setup G D)
include hS

theorem eq_of_mem_center {d : G} (hd : d ∈ D) (hdc : d ∈ Subgroup.center G) {e : G}
    (he : e ∈ D) : e = d := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp (hS.isConj hd he)
  rw [Subgroup.mem_center_iff.mp hdc c, mul_inv_cancel_right]

theorem false_of_mul_mem_center {d x : G} (hd : d ∈ D) (hdx : d * x ∈ D)
    (hxc : x ∈ Subgroup.center G) (hx1 : x ≠ 1) : False := by
  have hne : d ≠ d * x := fun h => hx1 (by simpa using h.symm)
  have hcomm : Commute d (d * x) := (Commute.refl d).mul_right (Subgroup.mem_center_iff.mp hxc d)
  have hdc : d ∈ Subgroup.center G := by
    have hall : ∀ w ∈ D, Commute w d := by
      intro w hw
      have h1 : Commute w (d * (d * x)) := by
        rw [← mul_assoc, hS.oddT.mul_self_eq_one hd, one_mul]
        exact Subgroup.mem_center_iff.mp hxc w
      exact ((hS.oddT.commute_mul_iff hd hdx hw hne hcomm).mp h1).1
    have hle : Subgroup.closure D ≤ Subgroup.centralizer {d} := by
      rw [Subgroup.closure_le]
      intro w hw
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hall w hw).eq
    rw [Subgroup.mem_center_iff]
    intro g
    have := hle (hS.gen ▸ Subgroup.mem_top g)
    exact Subgroup.mem_centralizer_singleton_iff.mp this
  exact hne (hS.eq_of_mem_center hd hdc hdx).symm

end Setup

theorem IsBenderGroup.commutator_eq_top {K : Type*} [Group K] [Finite K]
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) : commutator K = ⊤ := by
  have := IsBenderGroup.isSimpleGroup hK
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator K) with h | h
  · obtain ⟨a, b, hab⟩ := IsBenderGroup.exists_not_commute hK
    refine absurd ?_ hab
    rw [← commutatorElement_eq_one_iff_commute, ← Subgroup.mem_bot, ← h, commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  · exact h

private theorem map_commutator_eq_of_surjective {H : Type*} [Group H] {f : G →* H}
    (hf : Function.Surjective f) : (commutator G).map f = commutator H := by
  rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hf, commutator_def]

private theorem commutatorElement_mul_center_right {a b c : G} (hc : c ∈ Subgroup.center G) :
    ⁅a, b * c⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.mp hc
  rw [commutatorElement_def, commutatorElement_def]
  calc a * (b * c) * a⁻¹ * (b * c)⁻¹ = a * b * (c * a⁻¹) * c⁻¹ * b⁻¹ := by group
    _ = a * b * (a⁻¹ * c) * c⁻¹ * b⁻¹ := by rw [h a⁻¹]
    _ = a * b * a⁻¹ * b⁻¹ := by group

private theorem commutatorElement_mul_center_left {a b c : G} (hc : c ∈ Subgroup.center G) :
    ⁅a * c, b⁆ = ⁅a, b⁆ := by
  have h := Subgroup.mem_center_iff.mp hc
  rw [commutatorElement_def, commutatorElement_def]
  calc a * c * b * (a * c)⁻¹ * b⁻¹ = a * (c * b) * c⁻¹ * a⁻¹ * b⁻¹ := by group
    _ = a * (b * c) * c⁻¹ * a⁻¹ * b⁻¹ := by rw [h b]
    _ = a * b * a⁻¹ * b⁻¹ := by group

theorem sup_commutator_eq_top_of_commutator_eq_top {F : Subgroup G} [F.Normal]
    (h : commutator (G ⧸ F) = ⊤) : F ⊔ commutator G = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : (g : G ⧸ F) ∈ (commutator G).map (QuotientGroup.mk' F) := by
    rw [map_commutator_eq_of_surjective (QuotientGroup.mk'_surjective F), h]
    exact Subgroup.mem_top _
  obtain ⟨c, hc, hcg⟩ := hg
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hcg
  rw [sup_comm, ← mul_inv_cancel_left c g]
  exact Subgroup.mul_mem_sup hc hcg

namespace Setup

theorem not_mem_of_isBenderGroup [Finite G] (hS : Setup G D) {F : Subgroup G} [F.Normal]
    (hFc : F ≤ Subgroup.center G) (hB : CFSG.BenderSuzuki.IsBenderGroup (G ⧸ F)) {d : G}
    (hd : d ∈ D) : d ∉ F := by
  intro hdF
  have hdc := hFc hdF
  have hle : Subgroup.closure D ≤ Subgroup.center G := by
    rw [Subgroup.closure_le]
    intro e he
    rw [SetLike.mem_coe, hS.eq_of_mem_center hd hdc he]
    exact hdc
  obtain ⟨a, b, hab⟩ := IsBenderGroup.exists_not_commute hB
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  have ha : a ∈ Subgroup.center G := hle (hS.gen ▸ Subgroup.mem_top a)
  have hc : Commute a b := (Subgroup.mem_center_iff.mp ha b).symm
  exact hab (hc.map (QuotientGroup.mk' F))

theorem exists_inv_mul_mem_of_isBenderGroup [Finite G] (hS : Setup G D) {F : Subgroup G}
    [F.Normal] (hFc : F ≤ Subgroup.center G) (hB : CFSG.BenderSuzuki.IsBenderGroup (G ⧸ F))
    {s : G} (hs : s ∉ F) (hs2 : s * s ∈ F) : ∃ d ∈ D, d⁻¹ * s ∈ F := by
  obtain ⟨d₀, hd₀⟩ := hS.nonempty
  have h1 : orderOf (d₀ : G ⧸ F) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← QuotientGroup.mk_mul, hS.oddT.mul_self_eq_one hd₀, QuotientGroup.mk_one]
    · rw [Ne, QuotientGroup.eq_one_iff]
      exact hS.not_mem_of_isBenderGroup hFc hB hd₀
  have h2 : orderOf (s : G ⧸ F) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [pow_two, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
      exact hs2
    · rw [Ne, QuotientGroup.eq_one_iff]
      exact hs
  obtain ⟨c, hc⟩ := isConj_iff.mp (IsBenderGroup.isConj_of_orderOf_eq_two hB h1 h2)
  obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective c
  refine ⟨c * d₀ * c⁻¹, hS.conj_mem c hd₀, ?_⟩
  rw [← QuotientGroup.eq, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
  exact hc

theorem commute_of_mem_sylow_of_psl2 [Finite G] (hS : Setup G D) {F : Subgroup G} [F.Normal]
    (hFc : F ≤ Subgroup.center G) (hF2 : IsPGroup 2 F) {n : ℕ} (hn : 2 ≤ n)
    (e : (G ⧸ F) ≃* CFSG.Theory.Comparator.PSL2Model n) (S : Sylow 2 G) {a b : G} (ha : a ∈ S)
    (hb : b ∈ S) : Commute a b := by
  have hB : CFSG.BenderSuzuki.IsBenderGroup (G ⧸ F) := .isPSL2 n hn e
  have hFS : F ≤ S := hF2.le_sylow_of_normal S
  set Q : Sylow 2 (G ⧸ F) := S.mapSurjective (QuotientGroup.mk'_surjective F) with hQ
  have hQab := IsBenderGroup.commute_of_psl2 hn e Q
  have hz : ∀ {z : G}, z ∈ F → ∀ g : G, Commute g z := fun hz g =>
    Subgroup.mem_center_iff.mp (hFc hz) g
  have hdec : ∀ s ∈ S, s ∈ F ∨ ∃ d ∈ D, d ∈ S ∧ d⁻¹ * s ∈ F := by
    intro s hs
    by_cases hsF : s ∈ F
    · exact Or.inl hsF
    right
    have hsQ : (s : G ⧸ F) ∈ (Q : Subgroup (G ⧸ F)) := by
      rw [hQ, Sylow.coe_mapSurjective]
      exact Subgroup.mem_map_of_mem _ hs
    have hs2 : s * s ∈ F := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
      exact IsBenderGroup.mul_self_eq_one_of_commute hB Q hsQ (hQab _ hsQ)
    obtain ⟨d, hd, hdF⟩ := hS.exists_inv_mul_mem_of_isBenderGroup hFc hB hsF hs2
    refine ⟨d, hd, ?_, hdF⟩
    rw [show d = s * (d⁻¹ * s)⁻¹ by group]
    exact (S : Subgroup G).mul_mem hs ((S : Subgroup G).inv_mem (hFS hdF))
  rcases hdec a ha with haF | ⟨d, hd, hdS, hdF⟩
  · exact (hz haF b).symm
  rcases hdec b hb with hbF | ⟨d', hd', hd'S, hd'F⟩
  · exact hz hbF a
  have hdd' : Commute d d' := hS.oddT.commute_of_isPGroup S.isPGroup' hd hd' hdS hd'S
  rw [show a = d * (d⁻¹ * a) by group, show b = d' * (d'⁻¹ * b) by group]
  exact (hdd'.mul_right (hz hd'F d)).mul_left (hz hdF _).symm

theorem false_of_inf_commutator [Finite G] (hS : Setup G D) {F : Subgroup G} [F.Normal]
    (hFc : F ≤ Subgroup.center G) (hB : CFSG.BenderSuzuki.IsBenderGroup (G ⧸ F))
    (hSzU : (∃ f : ℕ, 2 ≤ f ∧ Nonempty ((G ⧸ F) ≃* PSU3 2 f)) ∨
      (∃ a : ℕ, 1 ≤ a ∧ Nonempty ((G ⧸ F) ≃* Sz a)))
    {x : G} (hxF : x ∈ F) (hxG : x ∈ commutator G) (hx1 : x ≠ 1) (hxx : x * x = 1)
    (hint : ∀ w ∈ F, w ∈ commutator G → w = 1 ∨ w = x) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G, K = commutator G := ⟨_, rfl⟩
  have hxc := hFc hxF
  have hdec : ∀ g : G, ∃ k ∈ K, ∃ f ∈ F, k * f = g := by
    intro g
    have hg : (g : G ⧸ F) ∈ (commutator G).map (QuotientGroup.mk' F) := by
      rw [map_commutator_eq_of_surjective (QuotientGroup.mk'_surjective F),
        IsBenderGroup.commutator_eq_top hB]
      exact Subgroup.mem_top _
    obtain ⟨k, hk, hkg⟩ := hg
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq] at hkg
    exact ⟨k, hK.ge hk, k⁻¹ * g, hkg, mul_inv_cancel_left k g⟩
  have hKK : K ≤ ⁅K, K⁆ := by
    have h : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ ⁅K, K⁆ := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      obtain ⟨k, hk, f, hf, rfl⟩ := hdec a
      obtain ⟨k', hk', f', hf', rfl⟩ := hdec b
      rw [commutatorElement_mul_center_right (hFc hf'), commutatorElement_mul_center_left (hFc hf)]
      exact Subgroup.commutator_mem_commutator hk hk'
    rwa [← commutator_def, ← hK] at h
  obtain ⟨x', rfl⟩ : ∃ x' : K, (x' : G) = x := ⟨⟨x, hK.ge hxG⟩, rfl⟩
  have hx'c : x' ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp hxc g)
  have hx'n : (Subgroup.zpowers x').Normal := zpowers_normal_of_mem_center hx'c
  have hx'2 : orderOf x' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [pow_two]; exact hxx) hx1
  have hx'K : x' ∈ commutator K := by
    have h : K.subtype x' ∈ (commutator K).map K.subtype := by
      rw [Subgroup.map_subtype_commutator]
      exact hKK x'.2
    exact (Subgroup.mem_map_iff_mem K.subtype_injective).mp h
  let φ : K →* G ⧸ F := (QuotientGroup.mk' F).comp K.subtype
  have hφ : ∀ k : K, φ k = ((k : G) : G ⧸ F) := fun k => rfl
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk, f, hf, rfl⟩ := hdec g
    refine ⟨⟨k, hk⟩, ?_⟩
    rw [hφ, QuotientGroup.eq, inv_mul_cancel_left]
    exact hf
  have hker : φ.ker = Subgroup.zpowers x' := by
    apply le_antisymm
    · intro k hk
      rw [MonoidHom.mem_ker, hφ, QuotientGroup.eq_one_iff] at hk
      rcases hint _ hk (hK.le k.2) with h | h
      · rw [show k = 1 from Subtype.ext h]
        exact Subgroup.one_mem _
      · rw [show k = x' from Subtype.ext h]
        exact Subgroup.mem_zpowers _
    · rw [Subgroup.zpowers_le, MonoidHom.mem_ker, hφ, QuotientGroup.eq_one_iff]
      exact hxF
  let σ : K ⧸ Subgroup.zpowers x' ≃* G ⧸ F :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  let τ : (⊤ : Subgroup (K ⧸ Subgroup.zpowers x')) ⧸
      (⊥ : Subgroup (K ⧸ Subgroup.zpowers x')).subgroupOf ⊤ ≃* G ⧸ F :=
    ((QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf _)).trans
      QuotientGroup.quotientBot).trans (Subgroup.topEquiv.trans σ)
  have hmodel : (∃ f : ℕ, 2 ≤ f ∧ Nonempty ((⊤ : Subgroup (K ⧸ Subgroup.zpowers x')) ⧸
        (⊥ : Subgroup (K ⧸ Subgroup.zpowers x')).subgroupOf ⊤ ≃* PSU3 2 f)) ∨
      (∃ a : ℕ, 1 ≤ a ∧ Nonempty ((⊤ : Subgroup (K ⧸ Subgroup.zpowers x')) ⧸
        (⊥ : Subgroup (K ⧸ Subgroup.zpowers x')).subgroupOf ⊤ ≃* Sz a)) := by
    rcases hSzU with ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · exact Or.inl ⟨f, hf, ⟨τ.trans e⟩⟩
    · exact Or.inr ⟨a, ha, ⟨τ.trans e⟩⟩
  obtain ⟨z, hz2, hzx, hzc⟩ := schurNarrowInput K x' hx'n hx'c hx'2 hx'K ⊥ ⊤ inferInstance
    inferInstance inferInstance bot_le (by rw [Subgroup.card_bot]; exact odd_one)
    (by rw [Subgroup.index_top]; exact odd_one) hmodel
  have hzz : (z : G) * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [hz2, pow_two] at h
    exact congrArg Subtype.val h
  have hzF : (z : G) ∉ F := by
    intro h
    apply hzx
    rw [← hker, MonoidHom.mem_ker, hφ, QuotientGroup.eq_one_iff]
    exact h
  obtain ⟨d, hd, hdz⟩ :=
    hS.exists_inv_mul_mem_of_isBenderGroup hFc hB hzF (hzz ▸ Subgroup.one_mem F)
  obtain ⟨f, hf, hzf⟩ : ∃ f ∈ F, (z : G) = d * f := ⟨d⁻¹ * z, hdz, by group⟩
  have hfc := Subgroup.mem_center_iff.mp (hFc hf)
  obtain ⟨c, hc⟩ := isConj_iff.mp (K.subtype.map_isConj hzc)
  rw [map_mul, Subgroup.coe_subtype, hzf] at hc
  have hdx : c * d * c⁻¹ = d * x' := by
    refine mul_right_cancel (b := f) ?_
    calc c * d * c⁻¹ * f = c * d * (c⁻¹ * f) := by group
      _ = c * d * (f * c⁻¹) := by rw [hfc c⁻¹]
      _ = c * (d * f) * c⁻¹ := by group
      _ = d * f * x' := hc
      _ = d * (f * x') := by group
      _ = d * (x' * f) := by rw [hfc x']
      _ = d * x' * f := by group
  exact hS.false_of_mul_mem_center hd (hdx ▸ hS.conj_mem c hd) hxc hx1

theorem inf_commutator_eq_bot_of_nonlinear [Finite G] (hS : Setup G D) {E : Subgroup G}
    (hEc : E ≤ Subgroup.center G) (hE2 : IsPGroup 2 E) [E.Normal]
    (hB : CFSG.BenderSuzuki.IsBenderGroup (G ⧸ E))
    (hSzU : (∃ f : ℕ, 2 ≤ f ∧ Nonempty ((G ⧸ E) ≃* PSU3 2 f)) ∨
      (∃ a : ℕ, 1 ≤ a ∧ Nonempty ((G ⧸ E) ≃* Sz a))) : E ⊓ commutator G = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  obtain ⟨L, hL⟩ : ∃ L : Subgroup (E ⊓ commutator G : Subgroup G), L.index = 2 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hE2.to_le inf_le_left :
      IsPGroup 2 (E ⊓ commutator G : Subgroup G))
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.eq_bot_of_card_eq _ (by rw [hk, pow_zero]))
    obtain ⟨L, hLc⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := k - 1)
      (by rw [hk]; exact pow_dvd_pow 2 (Nat.sub_le k 1))
    refine ⟨L, ?_⟩
    have h := L.card_mul_index
    rw [hLc, hk, show k = k - 1 + 1 by omega, pow_succ, Nat.add_sub_cancel] at h
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h
  obtain ⟨y, hy⟩ : ∃ y : (E ⊓ commutator G : Subgroup G), y ∉ L := by
    by_contra h
    push Not at h
    rw [show L = ⊤ from eq_top_iff.mpr fun y _ => h y, Subgroup.index_top] at hL
    exact absurd hL (by norm_num)
  set E₁ : Subgroup G := L.map (E ⊓ commutator G).subtype
  have hE₁E' : E₁ ≤ E ⊓ commutator G := Subgroup.map_subtype_le L
  have hE₁E : E₁ ≤ E := hE₁E'.trans inf_le_left
  have hE₁c : E₁ ≤ Subgroup.center G := hE₁E.trans hEc
  have : E₁.Normal := Subgroup.normal_of_le_center hE₁c
  have hmem : ∀ w : (E ⊓ commutator G : Subgroup G), (w : G) ∈ E₁ ↔ w ∈ L := fun w =>
    Subgroup.mem_map_iff_mem (E ⊓ commutator G).subtype_injective
  have hπs : Function.Surjective (QuotientGroup.mk' E₁) := QuotientGroup.mk'_surjective E₁
  have hS₁ : Setup (G ⧸ E₁) (QuotientGroup.mk' E₁ '' D) :=
    hS.map _ hπs fun d hd h1 => hS.not_mem_of_isBenderGroup hEc hB hd
      (hE₁E ((QuotientGroup.eq_one_iff d).mp h1))
  have hFc : E.map (QuotientGroup.mk' E₁) ≤ Subgroup.center (G ⧸ E₁) := by
    rintro _ ⟨e, he, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := hπs g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hEc he) g]
  let σ := QuotientGroup.quotientQuotientEquivQuotient E₁ E hE₁E
  have hB₁ : CFSG.BenderSuzuki.IsBenderGroup ((G ⧸ E₁) ⧸ E.map (QuotientGroup.mk' E₁)) := by
    rcases hB with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
    · exact .isPSL2 n hn (σ.trans e)
    · exact .isSuzuki n hn (σ.trans e)
    · exact .isPSU3 n hn (σ.trans e)
  have hSzU₁ : (∃ f : ℕ, 2 ≤ f ∧
        Nonempty (((G ⧸ E₁) ⧸ E.map (QuotientGroup.mk' E₁)) ≃* PSU3 2 f)) ∨
      (∃ a : ℕ, 1 ≤ a ∧ Nonempty (((G ⧸ E₁) ⧸ E.map (QuotientGroup.mk' E₁)) ≃* Sz a)) := by
    rcases hSzU with ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · exact Or.inl ⟨f, hf, ⟨σ.trans e⟩⟩
    · exact Or.inr ⟨a, ha, ⟨σ.trans e⟩⟩
  have hcomm : commutator (G ⧸ E₁) = (commutator G).map (QuotientGroup.mk' E₁) :=
    (map_commutator_eq_of_surjective hπs).symm
  refine hS₁.false_of_inf_commutator hFc hB₁ hSzU₁ (x := QuotientGroup.mk' E₁ y)
    (Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.mp y.2).1) ?_ ?_ ?_ ?_
  · rw [hcomm]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_inf.mp y.2).2
  · rw [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hmem]
    exact hy
  · rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← Subgroup.coe_mul, hmem,
      Subgroup.mul_mem_iff_of_index_two hL]
  · rintro w ⟨e, he, rfl⟩ hw
    rw [hcomm] at hw
    obtain ⟨c, hc, hce⟩ := hw
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hce
    have heG : e ∈ commutator G := by
      have h := (commutator G).mul_mem hc (Subgroup.mem_inf.mp (hE₁E' hce)).2
      rwa [mul_inv_cancel_left] at h
    obtain ⟨e', rfl⟩ : ∃ e' : (E ⊓ commutator G : Subgroup G), (e' : G) = e :=
      ⟨⟨e, Subgroup.mem_inf.mpr ⟨he, heG⟩⟩, rfl⟩
    by_cases heL : e' ∈ L
    · left
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hmem]
      exact heL
    · right
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ← Subgroup.coe_inv,
        ← Subgroup.coe_mul, hmem, Subgroup.mul_mem_iff_of_index_two hL, Subgroup.inv_mem_iff]
      exact iff_of_false heL hy

end Setup

theorem inf_commutator_eq_bot_of_isBenderGroup [Finite G] (hS : Setup G D) {E : Subgroup G}
    (hEc : E ≤ Subgroup.center G) (hE2 : IsPGroup 2 E) [E.Normal]
    (hB : CFSG.BenderSuzuki.IsBenderGroup (G ⧸ E)) : E ⊓ commutator G = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases id hB with ⟨n, hn, e⟩ | ⟨n, hn, e⟩ | ⟨n, hn, e⟩
  · obtain ⟨S⟩ : Nonempty (Sylow 2 G) := inferInstance
    have hP : IsMulCommutative (S : Subgroup G) :=
      ⟨⟨fun a b => Subtype.ext (hS.commute_of_mem_sylow_of_psl2 hEc hE2 hn e S a.2 b.2).eq⟩⟩
    exact CFSG.Walter.W67.inf_commutator_eq_bot_of_isPGroup S hP hEc hE2
  · have hmodel : CFSG.Theory.Comparator.SzModel n = Sz n := CFSG.Models.benderSzModel_eq_sz n
    exact hS.inf_commutator_eq_bot_of_nonlinear hEc hE2 hB
      (Or.inr ⟨n, hn, ⟨e.trans (MulEquiv.subgroupCongr hmodel)⟩⟩)
  · have hmodel : CFSG.Theory.Comparator.PSU3Model n = PSU3 2 n := CFSG.Models.benderPSU3Model_eq_psu3 n
    exact hS.inf_commutator_eq_bot_of_nonlinear hEc hE2 hB
      (Or.inl ⟨n, hn, ⟨e.trans (MulEquiv.subgroupCongr hmodel)⟩⟩)

theorem isCompl_commutator_of_isBenderGroup [Finite G] (hS : Setup G D) {E : Subgroup G}
    (hEc : E ≤ Subgroup.center G) (hE2 : IsPGroup 2 E) [E.Normal]
    (hB : CFSG.BenderSuzuki.IsBenderGroup (G ⧸ E)) : IsCompl E (commutator G) :=
  IsCompl.of_eq (inf_commutator_eq_bot_of_isBenderGroup hS hEc hE2 hB)
    (sup_commutator_eq_top_of_commutator_eq_top (IsBenderGroup.commutator_eq_top hB))

theorem card_le_two_of_isBenderGroup [Finite G] (hS : Setup G D) {E : Subgroup G}
    (hEc : E ≤ Subgroup.center G) (hE2 : IsPGroup 2 E) [E.Normal]
    (hB : CFSG.BenderSuzuki.IsBenderGroup (G ⧸ E)) : Nat.card E ≤ 2 := by
  have h := inf_commutator_eq_bot_of_isBenderGroup hS hEc hE2 hB
  have hinj : Function.Injective ((QuotientGroup.mk' (commutator G)).comp E.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have ha' : (a : G) ∈ E ⊓ commutator G :=
      Subgroup.mem_inf.mpr ⟨a.2, (QuotientGroup.eq_one_iff _).mp ha⟩
    rw [h, Subgroup.mem_bot] at ha'
    exact Subtype.ext ha'
  calc Nat.card E ≤ Nat.card (G ⧸ commutator G) := Nat.card_le_card_of_injective _ hinj
    _ ≤ 2 := hS.index_commutator_le_two

theorem sup_commutator_eq_top_of_isBenderGroup [Finite G] (hS : Setup G D) {E : Subgroup G}
    (hEc : E ≤ Subgroup.center G) (hE2 : IsPGroup 2 E) [E.Normal]
    (hB : CFSG.BenderSuzuki.IsBenderGroup (G ⧸ E)) : E ⊔ commutator G = ⊤ :=
  (isCompl_commutator_of_isBenderGroup hS hEc hE2 hB).sup_eq_top

end CFSG.Timmesfeld.Bridge.Asc72
