module

public import CFSG.Quasithin.Background.G117NoE9
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.FFC4Split

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Open

@[expose] def ThreeRank2 (X : Type*) [Group X] : Prop :=
  ∃ x y : X, x ≠ 1 ∧ x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ x * y = y * x ∧ y ∉ Subgroup.zpowers x

theorem ThreeRank2.of_injective {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (hf : Function.Injective f) (h : ThreeRank2 X) : ThreeRank2 Y := by
  obtain ⟨x, y, hx1, hx3, hy3, hxy, hy⟩ := h
  refine ⟨f x, f y, fun h1 => hx1 (hf (h1.trans f.map_one.symm)), by rw [← map_pow, hx3, map_one],
    by rw [← map_pow, hy3, map_one], by rw [← map_mul, ← map_mul, hxy], fun hmem => hy ?_⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
  refine Subgroup.mem_zpowers_iff.2 ⟨n, hf ?_⟩
  rw [map_zpow]
  exact hn

theorem ThreeRank2.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : ThreeRank2 X) :
    ThreeRank2 Y :=
  h.of_injective e.toMonoidHom e.injective

theorem ThreeRank2.of_le {Ω : Type*} [Group Ω] {H K : Subgroup Ω} (hHK : H ≤ K) (h : ThreeRank2 ↥H) :
    ThreeRank2 ↥K :=
  h.of_injective (Subgroup.inclusion hHK) (Subgroup.inclusion_injective hHK)

theorem ThreeRank2.of_commuting_subgroups {Ω : Type*} [Group Ω] {H₁ H₂ K : Subgroup Ω}
    (h1 : H₁ ≤ K) (h2 : H₂ ≤ K) (hinf : H₁ ⊓ H₂ = ⊥) (hcomm : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a)
    {x y : Ω} (hx : x ∈ H₁) (hy : y ∈ H₂) (hx1 : x ≠ 1) (hy1 : y ≠ 1) (hx3 : x ^ 3 = 1)
    (hy3 : y ^ 3 = 1) : ThreeRank2 ↥K := by
  refine ⟨⟨x, h1 hx⟩, ⟨y, h2 hy⟩, fun h => hx1 (congrArg Subtype.val h), Subtype.ext (by simpa using hx3),
    Subtype.ext (by simpa using hy3), Subtype.ext (hcomm x hx y hy), fun hmem => ?_⟩
  have hy' : y ∈ H₁ := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have : y = x ^ n := congrArg Subtype.val hn.symm
    rw [this]
    exact H₁.zpow_mem hx n
  have : y ∈ H₁ ⊓ H₂ := ⟨hy', hy⟩
  rw [hinf, Subgroup.mem_bot] at this
  exact hy1 this

theorem false_of_commuting_threes {Ω : Type*} [Group Ω] [Finite Ω] {Γ : Subgroup Ω}
    (hq : IsQuotientOfSQTKTauCeti ↥Γ) {t c x y : Ω} (ht : t ∈ Γ) (hc : c ∈ Γ) (hx : x ∈ Γ) (hy : y ∈ Γ)
    (ht2 : t * t = 1) (ht1 : t ≠ 1) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (htc : t * c * t⁻¹ = c⁻¹)
    (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x)
    (hyx : y ∉ Subgroup.zpowers x) (hxt : x * t = t * x) (hxc : x * c = c * x) (hyt : y * t = t * y)
    (hyc : y * c = c * y) : False := by
  set S : Set Ω := {x, y} with hS
  set E : Subgroup Ω := Subgroup.closure S with hE
  have hgenS : S ⊆ Subgroup.centralizer S := by
    intro a ha b hb
    rw [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact hxy.symm
    · exact hxy
    · rfl
  have hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
    have hNle : E ≤ Subgroup.centralizer S := (Subgroup.closure_le _).2 hgenS
    intro a ha b hb
    have h1 : b ∈ Subgroup.centralizer S := hNle hb
    have h2 : a ∈ Subgroup.centralizer (Subgroup.centralizer S : Set Ω) :=
      Subgroup.closure_le_centralizer_centralizer _ ha
    exact (Subgroup.mem_centralizer_iff.1 h2 b h1).symm
  have hE3 : ∀ e ∈ E, e ^ 3 = 1 := by
    intro e he
    induction he using Subgroup.closure_induction with
    | mem a ha =>
      rw [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact hx3
      · exact hy3
    | one => simp
    | mul a b ha hb h1 h2 =>
      have hcom : Commute a b := hEcomm a ha b hb
      rw [hcom.mul_pow, h1, h2, one_mul]
    | inv a _ h1 => rw [inv_pow, h1, inv_one]
  have hEΓ : E ≤ Γ := (Subgroup.closure_le _).2 (by
    intro a ha
    rw [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hx
    · exact hy)
  have hxE : x ∈ E := Subgroup.subset_closure (Or.inl rfl)
  have hyE : y ∈ E := Subgroup.subset_closure (Or.inr rfl)
  have hcentral : ∀ z : Ω, x * z = z * x → y * z = z * y → ∀ e ∈ E, e * z = z * e := by
    intro z hxz hyz e he
    have hle : E ≤ Subgroup.centralizer ({z} : Set Ω) := by
      rw [hE, Subgroup.closure_le]
      intro a ha w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      rw [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at ha
      rcases ha with rfl | rfl
      · exact hxz.symm
      · exact hyz.symm
    exact (Subgroup.mem_centralizer_iff.1 (hle he) z rfl).symm
  have hEnc : ¬ IsCyclic ↥E := by
    intro hcyc
    obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥E)
    have hg3 : g ^ 3 = 1 := Subtype.ext (hE3 g g.2)
    have h1 : Nat.card ↥E ∣ 3 := by
      rw [← hg]
      exact orderOf_dvd_of_pow_eq_one hg3
    have hle : Subgroup.zpowers x ≤ E := (Subgroup.zpowers_le).2 hxE
    have hord : orderOf x = 3 := orderOf_eq_prime hx3 hx1
    have h2 : Nat.card ↥(Subgroup.zpowers x) ≤ Nat.card ↥E := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers, hord] at h2
    have h3 : Nat.card ↥E ≤ 3 := Nat.le_of_dvd (by norm_num) h1
    have heq : Subgroup.zpowers x = E := by
      apply Subgroup.eq_of_le_of_card_ge hle
      rw [Nat.card_zpowers, hord]
      exact h3
    exact hyx (heq ▸ hyE)
  exact G11.G117.no_S3_noncyclic hq ht hc hEΓ ht2 ht1 hc3 hc1 htc hEcomm hE3 hEnc
    (fun e he => hcentral t hxt hyt e he) (fun e he => hcentral c hxc hyc e he)

section Split

variable {V : Type} [CommGroup V] [Finite V]

theorem B58Split.false_of_threeRank2 {G A G₁ G₂ F : Subgroup (MulAut V)} (h : B58Split G A G₁ G₂ F)
    (hq : IsQuotientOfSQTKTauCeti ↥G) (hX : ThreeRank2 ↥G₂) : False := by
  obtain ⟨x, y, hx1, hx3, hy3, hxy, hyx⟩ := hX
  obtain ⟨t, ht, ht1, ht2, -⟩ := h.s3.exists_inv_A
  obtain ⟨c, hc, hc1, hc3, -⟩ := h.s3.exists_gen_F
  have htc := h.s3.conj_eq_inv ht ht1 hc
  have htG₁ : t ∈ G₁ := h.A_le ht
  have hcG₁ : c ∈ G₁ := h.G₁_eq ▸ (le_sup_left : F ≤ F ⊔ A) hc
  have hxG : (x : MulAut V) ∈ G := h.G₂_le x.2
  have hyG : (y : MulAut V) ∈ G := h.G₂_le y.2
  refine false_of_commuting_threes hq (t := t) (c := c) (x := (x : MulAut V)) (y := (y : MulAut V))
    (h.G₁_le htG₁) (h.G₁_le hcG₁) hxG hyG (by simpa [pow_two] using ht2) ht1 hc3 hc1 htc
    (fun h' => hx1 (Subtype.ext h')) (by simpa using congrArg Subtype.val hx3)
    (by simpa using congrArg Subtype.val hy3) (by simpa using congrArg Subtype.val hxy) ?_
    ?_ ?_ ?_ ?_
  · intro hmem
    apply hyx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
    exact Subgroup.mem_zpowers_iff.2 ⟨n, Subtype.ext (by simpa using hn)⟩
  · exact (h.comm t htG₁ _ x.2).symm
  · exact (h.comm c hcG₁ _ x.2).symm
  · exact (h.comm t htG₁ _ y.2).symm
  · exact (h.comm c hcG₁ _ y.2).symm

end Split

end FFC

end CFSG.Quasithin
