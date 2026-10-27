module

public import CFSG.Quasithin.Vol2.Ch11SecA15Aut
public import CFSG.Quasithin.Vol2.Ch11SecBK9B

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K9

variable {G : Type} [Group G]

theorem mem_normalizer_iff_map_conj {H : Subgroup G} {x : G} :
    x ∈ Subgroup.normalizer (H : Set G) ↔ H.map (MulAut.conj x).toMonoidHom = H := by
  refine ⟨map_conj_eq_of_mem_normalizer, fun h => ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    rw [← h]
    exact ⟨g, hg, rfl⟩
  · intro hg
    rw [← h] at hg
    obtain ⟨y, hy, hyg⟩ := hg
    have : y = g := by
      change x * y * x⁻¹ = x * g * x⁻¹ at hyg
      simpa using hyg
    rwa [← this]

theorem map_conj_le {V U : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hU : U ≤ V) : U.map (MulAut.conj x).toMonoidHom ≤ V := by
  rw [← map_conj_eq_of_mem_normalizer hx]
  exact Subgroup.map_mono hU

theorem subgroupOf_map_conj {V U : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) (hU : U ≤ V) :
    (U.map (MulAut.conj x).toMonoidHom).subgroupOf V =
      (U.subgroupOf V).map (SecA.conjV V x hx).toMonoidHom := by
  ext w
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨u, hu, hux⟩
    refine ⟨⟨u, hU hu⟩, hu, Subtype.ext ?_⟩
    rw [MulEquiv.coe_toMonoidHom, SecA.conjV_apply_coe]
    exact hux
  · rintro ⟨u, hu, rfl⟩
    refine ⟨u, hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, SecA.conjV_apply_coe, MulAut.conj_apply]

theorem mem_normalizer_iff_subgroupOf {V U : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) (hU : U ≤ V) :
    x ∈ Subgroup.normalizer (U : Set G) ↔
      (U.subgroupOf V).map (SecA.conjV V x hx).toMonoidHom = U.subgroupOf V := by
  rw [mem_normalizer_iff_map_conj, ← subgroupOf_map_conj hx hU, Subgroup.subgroupOf_inj,
    inf_of_le_left hU, inf_of_le_left (map_conj_le hx hU)]

theorem mem_normalizer_of_mem_centralizer {V U : Subgroup G} (hU : U ≤ V) {c : G}
    (hc : c ∈ Subgroup.centralizer (V : Set G)) : c ∈ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro u
  have key : ∀ w ∈ V, c * w * c⁻¹ = w := fun w hw => by
    rw [← Subgroup.mem_centralizer_iff.mp hc w hw, mul_inv_cancel_right]
  constructor
  · intro hu
    rwa [key u (hU hu)]
  · intro hu
    have h1 := key _ (hU hu)
    have e : u = c * u * c⁻¹ := by
      calc u = c⁻¹ * (c * u * c⁻¹) * c := by group
        _ = c⁻¹ * (c * (c * u * c⁻¹) * c⁻¹) * c := by rw [h1]
        _ = c * u * c⁻¹ := by group
    rwa [e]

variable {L V : Subgroup G} {Γ : Type*} [Group Γ]

@[expose] noncomputable def rhoL (hLV : L ≤ Subgroup.normalizer (V : Set G))
    {π : Γ →* ↥(autOn L V)} (hπ : Function.Bijective π) : ↥L →* Γ :=
  (MulEquiv.ofBijective π hπ).symm.toMonoidHom.comp (SecA.autOnHom' V L hLV)

theorem rhoL_spec (hLV : L ≤ Subgroup.normalizer (V : Set G)) {π : Γ →* ↥(autOn L V)}
    (hπ : Function.Bijective π) (l : ↥L) :
    ((π (rhoL hLV hπ l) : ↥(autOn L V)) : MulAut ↥V) = SecA.conjV V l (hLV l.2) := by
  have h : π (rhoL hLV hπ l) = SecA.autOnHom' V L hLV l :=
    (MulEquiv.ofBijective π hπ).apply_symm_apply _
  rw [h, SecA.autOnHom'_coe]

theorem rhoL_surjective (hLV : L ≤ Subgroup.normalizer (V : Set G)) {π : Γ →* ↥(autOn L V)}
    (hπ : Function.Bijective π) : Function.Surjective (rhoL hLV hπ) :=
  (MulEquiv.ofBijective π hπ).symm.surjective.comp (SecA.autOnHom'_surjective V L hLV)

theorem rhoL_eq_one_iff (hLV : L ≤ Subgroup.normalizer (V : Set G)) {π : Γ →* ↥(autOn L V)}
    (hπ : Function.Bijective π) (l : ↥L) :
    rhoL hLV hπ l = 1 ↔ (l : G) ∈ Subgroup.centralizer (V : Set G) := by
  have hspec := rhoL_spec hLV hπ l
  rw [Subgroup.mem_centralizer_iff]
  constructor
  · intro h v hv
    rw [h, map_one] at hspec
    have h2 := congrArg (fun φ : MulAut ↥V => ((φ ⟨v, hv⟩ : ↥V) : G)) hspec
    simp only [SecA.conjV_apply_coe] at h2
    change v = (l : G) * v * (l : G)⁻¹ at h2
    calc v * (l : G) = ((l : G) * v * (l : G)⁻¹) * l := by rw [← h2]
      _ = (l : G) * v := by group
  · intro h
    apply hπ.1
    rw [map_one]
    apply Subtype.ext
    rw [hspec]
    refine MulEquiv.ext fun w => Subtype.ext ?_
    show (SecA.conjV V l (hLV l.2) w : G) = w
    rw [SecA.conjV_apply_coe, ← h w w.2, mul_inv_cancel_right]

theorem card_eq_of_card_comap_eq {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {ρ : A →* B} (hρ : Function.Surjective ρ) {P P' : Subgroup B}
    (h : Nat.card (P.comap ρ) = Nat.card (P'.comap ρ)) : Nat.card P = Nat.card P' := by
  have h1 := (P.comap ρ).card_mul_index
  have h2 := (P'.comap ρ).card_mul_index
  rw [Subgroup.index_comap_of_surjective _ hρ] at h1 h2
  have hi : P.index = P'.index := by
    rw [h] at h1
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h1.trans h2.symm)
  have h3 := P.card_mul_index
  have h4 := P'.card_mul_index
  rw [hi] at h3
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
    (h3.trans h4.symm)

end CFSG.Quasithin.Vol2.Ch11.SecB.K9
