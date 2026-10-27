module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.Sporadic.ON
import CFSG.RankThree.PartTwo.Sec14.Ronan148JNA6
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.Sec4.Ronan148VL37

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree.PartTwo
open scoped commutatorElement

@[expose] def NoNormal3 (W : Type*) [Group W] : Prop :=
  ∀ N : Subgroup W, N.Normal → ¬ 3 ∣ Nat.card N → N = ⊥

theorem noNormal3_congr {W W' : Type*} [Group W] [Group W'] (e : W ≃* W') (h : NoNormal3 W) :
    NoNormal3 W' := by
  intro N hN h3
  have hN' : (N.map e.symm.toMonoidHom).Normal := hN.map _ e.symm.surjective
  have hc : Nat.card (N.map e.symm.toMonoidHom) = Nat.card N :=
    Subgroup.card_map_of_injective e.symm.injective
  have h0 := h _ hN' (by rwa [hc])
  exact (Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective).mp h0

theorem eq_one_of_pow_three_of_not_dvd {W : Type*} [Group W] [Finite W] {N : Subgroup W}
    (hN3 : ¬ 3 ∣ Nat.card N) {n : W} (hn : n ∈ N) (h3 : n ^ 3 = 1) : n = 1 := by
  have hd : orderOf n ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
  · exact orderOf_eq_one_iff.mp h
  · exfalso
    apply hN3
    have h1 : orderOf (⟨n, hn⟩ : ↥N) = 3 := by rw [Subgroup.orderOf_mk, h]
    rw [← h1]
    exact orderOf_dvd_natCard _

theorem card_normal_of_isTripleCover {W S : Type*} [Group W] [Group S] [Finite W]
    [IsSimpleGroup S] (h : Sec4.IsTripleCover W S) (N : Subgroup W) [hN : N.Normal] :
    Nat.card N ∣ 3 ∨ Nat.card S ∣ Nat.card N := by
  obtain ⟨hZ, ⟨e⟩⟩ := h
  set π := QuotientGroup.mk' (Subgroup.center W) with hπ
  have hM : ((N.map π).map e.toMonoidHom).Normal :=
    (hN.map π (QuotientGroup.mk'_surjective _)).map _ e.surjective
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.map π).map e.toMonoidHom) with h0 | h0
  · left
    have h1 : N.map π = ⊥ := (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp h0
    have hle : N ≤ Subgroup.center W := by
      have h2 := (Subgroup.map_eq_bot_iff N).mp h1
      rwa [hπ, QuotientGroup.ker_mk'] at h2
    rw [← hZ]
    exact Subgroup.card_dvd_of_le hle
  · right
    have h1 : Nat.card ((N.map π).map e.toMonoidHom) = Nat.card S := by
      rw [h0, Subgroup.card_top]
    rw [Subgroup.card_map_of_injective e.injective] at h1
    rw [← h1]
    exact Subgroup.card_map_dvd N π

theorem noNormal3_of_isTripleCover {W S : Type*} [Group W] [Group S] [Finite W] [IsSimpleGroup S]
    (hS3 : 3 ∣ Nat.card S) (h : Sec4.IsTripleCover W S) : NoNormal3 W := by
  intro N hN hN3
  rcases card_normal_of_isTripleCover h N with h1 | h1
  · rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h2 | h2
    · exact Subgroup.eq_bot_of_card_eq N h2
    · exact absurd (by rw [h2]) hN3
  · exact absurd (hS3.trans h1) hN3

theorem noNormal3_of_isSimpleGroup {W : Type*} [Group W] [IsSimpleGroup W]
    (h3 : 3 ∣ Nat.card W) : NoNormal3 W := by
  intro N hN hN3
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exact absurd (by rw [h, Subgroup.card_top]; exact h3) hN3

theorem noNormal3_of_commute_sup {W : Type*} [Group W] [Finite W] {K₁ K₂ : Subgroup W}
    (hK₁ : K₁.Normal) (hK₂ : K₂.Normal) (hsup : K₁ ⊔ K₂ = ⊤)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (h₁ : NoNormal3 ↥K₁) (h₂ : NoNormal3 ↥K₂)
    (hz₁ : ∀ z ∈ Subgroup.center ↥K₁, z ^ 3 = 1) (hz₂ : ∀ z ∈ Subgroup.center ↥K₂, z ^ 3 = 1) :
    NoNormal3 W := by
  intro N hN hN3
  have hc : ∀ {K : Subgroup W}, K.Normal → NoNormal3 ↥K → ∀ n ∈ N, ∀ k ∈ K, n * k = k * n := by
    intro K hK hKn n hn k hk
    have h0 : N.subgroupOf K = ⊥ := by
      refine hKn _ (hN.subgroupOf K) fun h3 => hN3 (h3.trans ?_)
      exact Subgroup.card_comap_dvd_of_injective N K.subtype K.subtype_injective
    have hdisj : N ⊓ K = ⊥ := by
      rw [Subgroup.subgroupOf_eq_bot] at h0
      exact disjoint_iff.mp h0
    have hmem : ⁅n, k⁆ ∈ N ⊓ K := Subgroup.commutator_le_inf N K
      (Subgroup.commutator_mem_commutator hn hk)
    rw [hdisj, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  have hn' : n ∈ ((K₁ ⊔ K₂ : Subgroup W) : Set W) := by rw [hsup]; trivial
  rw [Subgroup.mul_normal] at hn'
  obtain ⟨x, hx, y, hy, hxyn⟩ := hn'
  have hxyn' : x * y = n := hxyn
  rw [← hxyn'] at hn ⊢
  have hxy : x * y = y * x := hcomm x hx y hy
  have hxZ : (⟨x, hx⟩ : ↥K₁) ∈ Subgroup.center ↥K₁ := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h1 : x * y * g = g * (x * y) := hc hK₁ h₁ _ hn g g.2
    have h2 : y * g = g * y := (hcomm g g.2 y hy).symm
    change (g : W) * x = x * g
    calc (g : W) * x = g * (x * y) * y⁻¹ := by group
      _ = x * y * g * y⁻¹ := by rw [h1]
      _ = x * (y * g) * y⁻¹ := by group
      _ = x * (g * y) * y⁻¹ := by rw [h2]
      _ = x * g := by group
  have hyZ : (⟨y, hy⟩ : ↥K₂) ∈ Subgroup.center ↥K₂ := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    have h1 : x * y * g = g * (x * y) := hc hK₂ h₂ _ hn g g.2
    have h2 : x * g = g * x := hcomm x hx g g.2
    change (g : W) * y = y * g
    calc (g : W) * y = x⁻¹ * (x * g) * y := by group
      _ = x⁻¹ * (g * x) * y := by rw [h2]
      _ = x⁻¹ * (g * (x * y)) := by group
      _ = x⁻¹ * (x * y * g) := by rw [h1]
      _ = y * g := by group
  have hx3 : x ^ 3 = 1 := by simpa using congrArg Subtype.val (hz₁ _ hxZ)
  have hy3 : y ^ 3 = 1 := by simpa using congrArg Subtype.val (hz₂ _ hyZ)
  refine eq_one_of_pow_three_of_not_dvd hN3 hn ?_
  rw [(Commute.mul_pow hxy 3), hx3, hy3, one_mul]

theorem pow_three_eq_one_of_mem_center {W : Type*} [Group W]
    (hZ : Nat.card (Subgroup.center W) = 3) {z : W} (hz : z ∈ Subgroup.center W) : z ^ 3 = 1 := by
  have : Finite (Subgroup.center W) := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have h1 := orderOf_dvd_natCard (⟨z, hz⟩ : ↥(Subgroup.center W))
  rw [hZ] at h1
  have h2 := orderOf_dvd_iff_pow_eq_one.mp h1
  simpa using congrArg Subtype.val h2

theorem card_alternatingGroup_six : Nat.card (alternatingGroup (Fin 6)) = 360 := by
  rw [KFacts.KS14.card_alternatingGroup_fin (by norm_num)]
  decide

theorem noNormal3_of_isCentralProductA6Covers {W : Type*} [Group W] [Finite W]
    (h : IsCentralProductA6Covers W) : NoNormal3 W := by
  obtain ⟨U, V, hUn, hVn, hUV, hc, -, hU, hV⟩ := h
  have hcomm : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u := fun u hu v hv => by
    have := Subgroup.commutator_mem_commutator hu hv
    rw [hc, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have h3 : 3 ∣ Nat.card (alternatingGroup (Fin 6)) := by
    rw [card_alternatingGroup_six]; norm_num
  exact noNormal3_of_commute_sup hUn hVn hUV hcomm (noNormal3_of_isTripleCover h3 hU)
    (noNormal3_of_isTripleCover h3 hV) (fun z hz => pow_three_eq_one_of_mem_center hU.1 hz)
    (fun z hz => pow_three_eq_one_of_mem_center hV.1 hz)

theorem noNormal3_alternating_five_sq :
    NoNormal3 (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) := by
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 :=
    KFacts.KS14.card_alternatingGroup_five_seven_ten.1
  have hZ := Ronan148J.center_alternatingGroup_five_eq_bot
  intro N hN hN3
  have hslice : ∀ f : alternatingGroup (Fin 5) →* alternatingGroup (Fin 5) ×
      alternatingGroup (Fin 5), Function.Injective f → N.comap f = ⊥ := by
    intro f hf
    have := hN.comap f
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.comap f) with h | h
    · exact h
    · exfalso
      apply hN3
      have h1 := Subgroup.card_comap_dvd_of_injective N f hf
      rw [h, Subgroup.card_top, h60] at h1
      exact (show 3 ∣ 60 by norm_num).trans h1
  have h1 := hslice (MonoidHom.inl _ _) (fun a b h => by simpa using congrArg Prod.fst h)
  have h2 := hslice (MonoidHom.inr _ _) (fun a b h => by simpa using congrArg Prod.snd h)
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  have hcen : ∀ a : alternatingGroup (Fin 5), (∀ g, a * g = g * a) → a = 1 := by
    intro a ha
    have hmem : a ∈ Subgroup.center (alternatingGroup (Fin 5)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact (ha g).symm
    rw [hZ, Subgroup.mem_bot] at hmem
    exact hmem
  have hx1 : x.1 = 1 := by
    refine hcen _ fun g => ?_
    have hmem : x * (g, 1) * x⁻¹ * (g, 1)⁻¹ ∈ N := by
      have h' := N.mul_mem hx (hN.conj_mem x⁻¹ (N.inv_mem hx) (g, 1))
      simpa [mul_assoc] using h'
    have hmem' : x.1 * g * x.1⁻¹ * g⁻¹ ∈ N.comap (MonoidHom.inl _ _) := by
      show MonoidHom.inl _ _ (x.1 * g * x.1⁻¹ * g⁻¹) ∈ N
      have e : MonoidHom.inl (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))
          (x.1 * g * x.1⁻¹ * g⁻¹) = x * (g, 1) * x⁻¹ * (g, 1)⁻¹ := by
        ext <;> simp
      rw [e]
      exact hmem
    rw [h1, Subgroup.mem_bot] at hmem'
    calc x.1 * g = x.1 * g * x.1⁻¹ * g⁻¹ * (g * x.1) := by group
      _ = g * x.1 := by rw [hmem', one_mul]
  have hx2 : x.2 = 1 := by
    refine hcen _ fun g => ?_
    have hmem : x * (1, g) * x⁻¹ * (1, g)⁻¹ ∈ N := by
      have h' := N.mul_mem hx (hN.conj_mem x⁻¹ (N.inv_mem hx) (1, g))
      simpa [mul_assoc] using h'
    have hmem' : x.2 * g * x.2⁻¹ * g⁻¹ ∈ N.comap (MonoidHom.inr _ _) := by
      show MonoidHom.inr _ _ (x.2 * g * x.2⁻¹ * g⁻¹) ∈ N
      have e : MonoidHom.inr (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))
          (x.2 * g * x.2⁻¹ * g⁻¹) = x * (1, g) * x⁻¹ * (1, g)⁻¹ := by
        ext <;> simp
      rw [e]
      exact hmem
    rw [h2, Subgroup.mem_bot] at hmem'
    calc x.2 * g = x.2 * g * x.2⁻¹ * g⁻¹ * (g * x.2) := by group
      _ = g * x.2 := by rw [hmem', one_mul]
  exact Prod.ext hx1 hx2

theorem noNormal3_of_isTripleCover_ON {W : Type*} [Group W]
    [Finite W] (h : Sec4.IsTripleCover W CFSG.Blueprint.NativeSporadic.ON) : NoNormal3 W := by
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.ON := CFSG.Sporadic.ON.isSimpleGroup_ON
  refine noNormal3_of_isTripleCover ?_ h
  rw [CFSG.Sporadic.ON.card_ON]
  norm_num

theorem noNormal3_alternatingGroup_seven : NoNormal3 (alternatingGroup (Fin 7)) := by
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  refine noNormal3_of_isSimpleGroup ?_
  rw [KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1]
  norm_num

theorem noNormal3_projSL_three_seven [Fact (Nat.Prime 7)] :
    NoNormal3 (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) := by
  have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 7 1)
  refine noNormal3_of_isSimpleGroup ?_
  exact (show 3 ∣ 9 by norm_num).trans (Sec4.Ronan148V.noNine_projSL_three_seven).1

theorem center_eq_bot_of_isSimpleGroup_of_nine_dvd {W : Type*} [Group W] [Finite W]
    [IsSimpleGroup W] (h9 : 9 ∣ Nat.card W) : Subgroup.center W = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center W) with h | h
  · exact h
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 ((show 3 ∣ 9 by norm_num).trans h9)
    have hN : (Subgroup.zpowers x).Normal := by
      constructor
      intro n hnx g
      have hn : n ∈ Subgroup.center W := h ▸ Subgroup.mem_top n
      rw [Subgroup.mem_center_iff] at hn
      have e : g * n * g⁻¹ = n := by rw [hn g]; group
      rw [e]
      exact hnx
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers x) with h1 | h1
    · have hx1 : x = 1 := by
        have := Subgroup.mem_zpowers x
        rwa [h1, Subgroup.mem_bot] at this
      rw [hx1, orderOf_one] at hx
      norm_num at hx
    · have h2 : Nat.card (Subgroup.zpowers x) = Nat.card W := by rw [h1, Subgroup.card_top]
      rw [Nat.card_zpowers, hx] at h2
      rw [← h2] at h9
      norm_num at h9

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
