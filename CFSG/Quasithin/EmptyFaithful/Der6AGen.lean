module

public import CFSG.Quasithin.Background.A4Four
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Der6A

variable {G : Type} [Group G]

theorem oTwoUpper_le_of_normal_sup [Finite G] {H N S : Subgroup G} (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hS : IsPGroup 2 S) (hSH : S ≤ H) (hH : H ≤ N ⊔ S) :
    oTwoUpper H ≤ N := by
  refine oTwoUpper_le_of_pow_mem fun x hx => ?_
  have hsup : N.subgroupOf H ⊔ S.subgroupOf H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNH hSH]
    exact Subgroup.subgroupOf_eq_top.mpr hH
  have hx' : (⟨x, hx⟩ : ↥H) ∈ N.subgroupOf H ⊔ S.subgroupOf H := by
    rw [hsup]
    exact Subgroup.mem_top _
  obtain ⟨n, hn, s, hs, hns⟩ := Subgroup.mem_sup_of_normal_left.mp hx'
  have hS' : IsPGroup 2 (S.subgroupOf H) := hS.of_equiv (Subgroup.subgroupOfEquivOfLe hSH).symm
  obtain ⟨k, hk⟩ := hS' ⟨s, hs⟩
  refine ⟨k, ?_⟩
  have hs1 : s ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : ↥H) : ↥H ⧸ N.subgroupOf H) = QuotientGroup.mk s := by
    rw [← hns, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, one_mul]
  have h2 : (QuotientGroup.mk ((⟨x, hx⟩ : ↥H) ^ 2 ^ k) : ↥H ⧸ N.subgroupOf H) = 1 := by
    rw [QuotientGroup.mk_pow, h1, ← QuotientGroup.mk_pow, hs1, QuotientGroup.mk_one]
  rw [QuotientGroup.eq_one_iff] at h2
  simpa using Subgroup.mem_subgroupOf.mp h2

theorem s3_conj_cover :
    ∀ s g : Equiv.Perm (Fin 3), s ≠ 1 → s * s = 1 →
      ∃ g₁ g₂ : Equiv.Perm (Fin 3), g = 1 ∨ g = g₁ * s * g₁⁻¹ ∨
        g = (g₁ * s * g₁⁻¹) * (g₂ * s * g₂⁻¹) := by
  decide

theorem s3_comm_sq :
    ∀ a b : Equiv.Perm (Fin 3), a * a = 1 → b * b = 1 → a * b = b * a →
      a = 1 ∨ b = 1 ∨ a = b := by
  decide

theorem eq_top_of_involution_mem (K : Subgroup (Equiv.Perm (Fin 3))) [K.Normal]
    {s : Equiv.Perm (Fin 3)} (hs : s ∈ K) (hs1 : s ≠ 1) (hs2 : s * s = 1) : K = ⊤ := by
  refine eq_top_iff.mpr fun g _ => ?_
  obtain ⟨g₁, g₂, h⟩ := s3_conj_cover s g hs1 hs2
  have c₁ : g₁ * s * g₁⁻¹ ∈ K := Subgroup.Normal.conj_mem inferInstance s hs g₁
  have c₂ : g₂ * s * g₂⁻¹ ∈ K := Subgroup.Normal.conj_mem inferInstance s hs g₂
  rcases h with rfl | rfl | rfl
  · exact K.one_mem
  · exact c₁
  · exact K.mul_mem c₁ c₂

variable {X : Subgroup G}

noncomputable def piS3 (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) : ↥X →* Equiv.Perm (Fin 3) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥X))

theorem piS3_surjective (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) :
    Function.Surjective (piS3 e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem piS3_eq_one_iff (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) {x : G} (hx : x ∈ X) :
    piS3 e ⟨x, hx⟩ = 1 ↔ x ∈ pCoreOf 2 X := by
  have h1 : piS3 e ⟨x, hx⟩ = 1 ↔ (QuotientGroup.mk (⟨x, hx⟩ : ↥X) : OTwoQuot X) = 1 :=
    e.map_eq_one_iff
  rw [h1, QuotientGroup.eq_one_iff]
  constructor
  · intro h
    exact ⟨⟨x, hx⟩, h, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    have : y = ⟨x, hx⟩ := Subtype.ext hyx
    rwa [this] at hy

theorem piS3_sq_eq_one (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) {a : G} (ha : a ∈ X)
    (ha2 : a ^ 2 = 1) : piS3 e ⟨a, ha⟩ * piS3 e ⟨a, ha⟩ = 1 := by
  rw [← map_mul]
  have : (⟨a, ha⟩ : ↥X) * ⟨a, ha⟩ = 1 := Subtype.ext (by simpa [pow_two] using ha2)
  rw [this, map_one]

theorem exists_mul_mem_pCoreOf_of_normal (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) {N : Subgroup G}
    (hN : (N.subgroupOf X).Normal) {a : G} (haX : a ∈ X) (haN : a ∈ N)
    (ha2 : a ^ 2 = 1) (haQ : a ∉ pCoreOf 2 X) :
    ∀ x ∈ X, ∃ n ∈ N, n⁻¹ * x ∈ pCoreOf 2 X := by
  intro x hx
  set K := (N.subgroupOf X).map (piS3 e) with hK
  have hKn : K.Normal := Subgroup.Normal.map hN _ (piS3_surjective e)
  have hs : piS3 e ⟨a, haX⟩ ∈ K := Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr haN)
  have hs1 : piS3 e ⟨a, haX⟩ ≠ 1 := fun h => haQ ((piS3_eq_one_iff e haX).mp h)
  have hKtop : K = ⊤ := eq_top_of_involution_mem K hs hs1 (piS3_sq_eq_one e haX ha2)
  have hxK : piS3 e ⟨x, hx⟩ ∈ K := by rw [hKtop]; exact Subgroup.mem_top _
  obtain ⟨n', hn', hnx⟩ := Subgroup.mem_map.mp hxK
  refine ⟨(n' : G), Subgroup.mem_subgroupOf.mp hn', ?_⟩
  rw [← piS3_eq_one_iff e (X.mul_mem (X.inv_mem n'.2) hx)]
  have : (⟨(n' : G)⁻¹ * x, X.mul_mem (X.inv_mem n'.2) hx⟩ : ↥X) = n'⁻¹ * ⟨x, hx⟩ := rfl
  rw [this, map_mul, map_inv, hnx, inv_mul_cancel]

theorem relIndex_inf_pCoreOf_eq_two (e : OTwoQuot X ≃* Equiv.Perm (Fin 3)) {A : Subgroup G}
    (hAX : A ≤ X) (hA : IsElemAbelian 2 A) (hAQ : ¬ A ≤ pCoreOf 2 X) :
    (A ⊓ pCoreOf 2 X).relIndex A = 2 := by
  have key : ∀ a ∈ A, ∀ b ∈ A, a ∉ pCoreOf 2 X → b ∉ pCoreOf 2 X → a⁻¹ * b ∈ pCoreOf 2 X := by
    intro a ha b hb haQ hbQ
    have ha1 : piS3 e ⟨a, hAX ha⟩ ≠ 1 := fun h => haQ ((piS3_eq_one_iff e _).mp h)
    have hb1 : piS3 e ⟨b, hAX hb⟩ ≠ 1 := fun h => hbQ ((piS3_eq_one_iff e _).mp h)
    have hcomm : piS3 e ⟨a, hAX ha⟩ * piS3 e ⟨b, hAX hb⟩ =
        piS3 e ⟨b, hAX hb⟩ * piS3 e ⟨a, hAX ha⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (B2F.isElemAbelian_comm hA ha hb)
    have heq := ((s3_comm_sq _ _ (piS3_sq_eq_one e _ (hA.2 a ha))
      (piS3_sq_eq_one e _ (hA.2 b hb)) hcomm).resolve_left ha1).resolve_left hb1
    rw [← piS3_eq_one_iff e (X.mul_mem (X.inv_mem (hAX ha)) (hAX hb))]
    have : (⟨a⁻¹ * b, X.mul_mem (X.inv_mem (hAX ha)) (hAX hb)⟩ : ↥X) =
        (⟨a, hAX ha⟩ : ↥X)⁻¹ * ⟨b, hAX hb⟩ := rfl
    rw [this, map_mul, map_inv, heq, inv_mul_cancel]
  obtain ⟨a₀, ha₀, ha₀Q⟩ := Set.not_subset.mp hAQ
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨a₀, ha₀, fun b hb => ?_⟩
  by_cases hbQ : b ∈ pCoreOf 2 X
  · refine Or.inr ⟨⟨hb, hbQ⟩, fun h => ha₀Q ?_⟩
    have h2 : b * a₀ ∈ pCoreOf 2 X := h.2
    have := (pCoreOf 2 X).mul_mem ((pCoreOf 2 X).inv_mem hbQ) h2
    simpa using this
  · refine Or.inl ⟨⟨A.mul_mem hb ha₀, ?_⟩, fun h => hbQ h.2⟩
    have hbinv : b⁻¹ ∉ pCoreOf 2 X := fun h => hbQ (by simpa using (pCoreOf 2 X).inv_mem h)
    simpa using key b⁻¹ (A.inv_mem hb) a₀ ha₀ hbinv ha₀Q

end Der6A

end CFSG.Quasithin
