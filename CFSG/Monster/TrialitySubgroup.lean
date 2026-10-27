module

public import CFSG.Monster.Triality

public section

namespace CFSG.Monster

variable {G : Type*} [Group G]

theorem coe_mem_zpowers_iff {K : Subgroup G} {z : G} (hz : z ∈ K) (q : K) :
    q ∈ Subgroup.zpowers (⟨z, hz⟩ : K) ↔ (q : G) ∈ Subgroup.zpowers z := by
  simp only [Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← hk, SubgroupClass.coe_zpow]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by rw [SubgroupClass.coe_zpow, hk])⟩

theorem isSimpleGroup_of_triality_subgroup {K : Subgroup G} [Finite K] {H Q : Subgroup G}
    (hHK : H ≤ K) (hQH : Q ≤ H) [hQnH : (Q.subgroupOf H).Normal]
    {z : G} (hzQ : z ∈ Q) (hz2 : orderOf z = 2)
    (hZ : ∀ q ∈ Q, (∀ x ∈ Q, x * q = q * x) ↔ q ∈ Subgroup.zpowers z)
    (hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ Subgroup.zpowers z)
    (hQz : ∃ q ∈ Q, q ∉ Subgroup.zpowers z) (hsimple : IsSimpleGroup (H ⧸ Q.subgroupOf H))
    (hfaith : ∀ h ∈ H, (∀ x ∈ Q, h * x * h⁻¹ * x⁻¹ ∈ Subgroup.zpowers z) → h ∈ Q)
    (hirr : ∀ R : Subgroup G, (∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) →
      Subgroup.zpowers z ≤ R → R ≤ Q → R = Subgroup.zpowers z ∨ R = Q)
    (hCz : K ⊓ Subgroup.centralizer {z} = H) {E : Subgroup G} (hEH : E ≤ H)
    (hE4 : Nat.card E = 4) (hEexp : ∀ e ∈ E, e * e = 1) (hzE : z ∈ E) {τ : G} (hτK : τ ∈ K)
    (hτE : ∀ e ∈ E, τ⁻¹ * e * τ ∈ E) (hτcyc : ∀ e ∈ E, e ≠ 1 → τ⁻¹ * e * τ ≠ e)
    (hgen : Subgroup.closure (insert τ (H : Set G)) = K) {u : G} (hu : u ∈ Q)
    (huH : τ⁻¹ * u * τ ∈ H) (huQ : τ⁻¹ * u * τ ∉ Q) {h : G} (hh : h ∈ H)
    (hhτ : τ⁻¹ * h * τ * h = τ) : Nontrivial K ∧ IsSimpleGroup K := by
  have hQK : Q ≤ K := hQH.trans hHK
  have hzK : z ∈ K := hQK hzQ
  have hQn : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q := fun h hh q hq =>
    hQnH.conj_mem ⟨q, hQH hq⟩ hq ⟨h, hh⟩
  have hQn' : ((Q.subgroupOf K).subgroupOf (H.subgroupOf K)).Normal :=
    ⟨fun n hn g => hQn _ g.2 _ hn⟩
  have hsimple' : IsSimpleGroup
      (H.subgroupOf K ⧸ (Q.subgroupOf K).subgroupOf (H.subgroupOf K)) := by
    have he : ((Q.subgroupOf K).subgroupOf (H.subgroupOf K)).map
        (Subgroup.subgroupOfEquivOfLe hHK).toMonoidHom = Q.subgroupOf H := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        refine ⟨(Subgroup.subgroupOfEquivOfLe hHK).symm x, ?_, ?_⟩
        · exact hx
        · exact (Subgroup.subgroupOfEquivOfLe hHK).apply_symm_apply x
    exact (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hHK) he).isSimpleGroup
  have hgen' : Subgroup.closure (insert (⟨τ, hτK⟩ : K) ((H.subgroupOf K : Subgroup K) : Set K)) =
      ⊤ := by
    have himg : (K.subtype '' ((H.subgroupOf K : Subgroup K) : Set K)) = (H : Set G) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hHK hx⟩, hx, rfl⟩
    apply Subgroup.map_injective (f := K.subtype) Subtype.coe_injective
    rw [MonoidHom.map_closure, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
      Set.image_insert_eq, himg]
    exact hgen
  refine isSimpleGroup_of_triality (G := K) (H := H.subgroupOf K) (Q := Q.subgroupOf K)
    (fun x hx => hQH hx) (z := ⟨z, hzK⟩) hzQ
    ((orderOf_injective K.subtype Subtype.coe_injective ⟨z, hzK⟩).symm.trans hz2) ?_ ?_ ?_ hsimple'
    ?_ ?_ ?_ (E := E.subgroupOf K) (fun x hx => hEH hx) ?_ (fun e he => Subtype.ext (hEexp _ he))
    hzE (τ := ⟨τ, hτK⟩) (fun e he => hτE _ he) ?_ hgen' (u := ⟨u, hQK hu⟩) hu huH huQ
    (h := ⟨h, hHK hh⟩) hh (Subtype.ext hhτ)
  ·
    intro q hq
    rw [coe_mem_zpowers_iff hzK, ← hZ (q : G) (Subgroup.mem_subgroupOf.1 hq)]
    constructor
    · intro hc x hx
      exact congrArg Subtype.val (hc ⟨x, hQK hx⟩ hx)
    · intro hc x hx
      exact Subtype.ext (hc _ hx)
  ·
    intro x hx y hy
    rw [coe_mem_zpowers_iff hzK]
    exact hcomm _ hx _ hy
  ·
    obtain ⟨q, hq, hqz⟩ := hQz
    exact ⟨⟨q, hQK hq⟩, hq, fun h' => hqz ((coe_mem_zpowers_iff hzK _).1 h')⟩
  ·
    intro g hg hc
    refine hfaith _ hg fun x hx => ?_
    exact (coe_mem_zpowers_iff hzK _).1 (hc ⟨x, hQK hx⟩ hx)
  ·
    intro R hR hzR hRQ
    have hR' := hirr (R.map K.subtype)
      (by
        rintro g hg _ ⟨r, hr, rfl⟩
        exact ⟨⟨g, hHK hg⟩ * r * ⟨g, hHK hg⟩⁻¹, hR ⟨g, hHK hg⟩ hg r hr, rfl⟩)
      (by
        intro y hy
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
        refine ⟨⟨z, hzK⟩ ^ k, hzR (Subgroup.zpow_mem_zpowers _ k), ?_⟩
        rw [Subgroup.coe_subtype, SubgroupClass.coe_zpow])
      (by
        rintro _ ⟨r, hr, rfl⟩
        exact hRQ hr)
    have hcomap : ∀ S : Subgroup G, R.map K.subtype = S → R = S.comap K.subtype := fun S hS => by
      rw [← hS, Subgroup.comap_map_eq_self_of_injective Subtype.coe_injective]
    rcases hR' with h1 | h1
    · left
      rw [hcomap _ h1]
      ext y
      exact (coe_mem_zpowers_iff hzK y).symm
    · right
      rw [hcomap _ h1]
      rfl
  ·
    ext y
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, ← hCz,
      Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      exact ⟨y.2, congrArg Subtype.val hy⟩
    · rintro ⟨-, hy⟩
      exact Subtype.ext hy
  ·
    rw [← hE4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hEH.trans hHK)).toEquiv
  ·
    intro e he hne heq
    exact hτcyc _ he (fun h1 => hne (Subtype.ext h1)) (congrArg Subtype.val heq)

end CFSG.Monster
