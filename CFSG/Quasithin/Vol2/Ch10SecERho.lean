module

public import CFSG.Quasithin.Vol2.Ch10SecEE3Data
public import CFSG.Quasithin.Vol2.Ch10SecECase1b

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecE

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique Equiv

@[expose] def rA : Perm (Fin 5) := swap 0 2 * swap 1 3

@[expose] def vFour : Finset (Perm (Fin 5)) := {1, sA * sB, rA, rA * (sA * sB)}

theorem mem_vFour_of_normalizes : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 →
    (∀ g ∈ eFour, σ * g * σ⁻¹ ∈ eFour) → σ ∈ vFour := by
  decide +kernel

theorem card_vFour : vFour.card = 4 := by decide

theorem rA_mem_vFour : rA ∈ vFour := by decide

theorem isSylowTwoOf_map_range'' {G W : Type*} [Group G] [Group W] {H S : Subgroup G}
    (hS : IsSylowTwoOf S H) (ρ : ↥H →* W) :
    IsSylowTwoOf ((S.subgroupOf H).map ρ) ρ.range := by
  have hS2 : IsPGroup 2 (S.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  refine ⟨Subgroup.map_le_range ρ _, hS2.map ρ, ?_⟩
  have h1 : ((S.subgroupOf H).map ρ).subgroupOf ρ.range =
      (S.subgroupOf H).map ρ.rangeRestrict := by
    ext x
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subtype.ext_iff]
  rw [h1]
  intro hd
  apply hS.2.2
  exact hd.trans (Subgroup.index_map_dvd _ ρ.rangeRestrict_surjective)

theorem mem_alternatingGroup_of_mem_oTwoUpper {W : Type*} [CommGroup W] {K : Subgroup (MulAut W)}
    (θ : ↥K ≃* Perm (Fin 5)) {x : MulAut W} (hx : x ∈ oTwoUpper K) :
    θ ⟨x, oTwoUpper_le K hx⟩ ∈ alternatingGroup (Fin 5) := by
  suffices key : ∀ y ∈ oTwoUpper K, ∀ hy : y ∈ K, θ ⟨y, hy⟩ ∈ alternatingGroup (Fin 5) from
    key x hx _
  intro y hy
  induction hy using Subgroup.closure_induction with
  | mem z hz =>
    intro hzK
    rw [Perm.mem_alternatingGroup]
    have ho : Odd (orderOf (θ ⟨z, hzK⟩)) := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact hz.2
    obtain ⟨k, hk⟩ := ho
    have h1 := congrArg Perm.sign (pow_orderOf_eq_one (θ ⟨z, hzK⟩))
    rw [map_pow, map_one, hk] at h1
    rcases Int.units_eq_one_or (Perm.sign (θ ⟨z, hzK⟩)) with h | h
    · exact h
    · rw [h, pow_succ, pow_mul] at h1
      simp at h1
  | one => intro h1; rw [show (⟨1, h1⟩ : ↥K) = 1 from rfl, map_one]; exact Subgroup.one_mem _
  | mul a b ha hb iha ihb =>
    intro hab
    have e : (⟨a * b, hab⟩ : ↥K) = ⟨a, oTwoUpper_le K ha⟩ * ⟨b, oTwoUpper_le K hb⟩ := rfl
    rw [e, map_mul]
    exact Subgroup.mul_mem _ (iha _) (ihb _)
  | inv a ha iha =>
    intro hai
    have e : (⟨a⁻¹, hai⟩ : ↥K) = (⟨a, oTwoUpper_le K ha⟩)⁻¹ := rfl
    rw [e, map_inv]
    exact Subgroup.inv_mem _ (iha _)

theorem card_alt_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem card_eq_four_of_sylow {X : Type*} [Group X] [Finite X] {P Q : Subgroup X}
    (hPQ : IsSylowTwoOf P Q) (hQ : Nat.card Q = 60) : Nat.card P = 4 := by
  obtain ⟨k, hk⟩ := hPQ.2.1.exists_card_eq
  have h1 := Subgroup.relIndex_mul_card P Q
  rw [inf_eq_left.mpr hPQ.1, hk, hQ] at h1
  have hodd : ¬ 2 ∣ P.relIndex Q := hPQ.2.2
  have hk5 : k < 6 := by
    by_contra hk6
    push Not at hk6
    have : 2 ^ 6 ∣ 2 ^ k := pow_dvd_pow 2 hk6
    have h2 : 2 ^ k ∣ 60 := Dvd.intro_left _ h1
    have := Nat.le_of_dvd (by norm_num) (this.trans h2)
    norm_num at this
  rw [hk]
  interval_cases k <;> omega

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem card_autI_inf_L
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : Ch10.TmpL6_3_2_2_two) (hyp : Hyp10 G T L I) (h2 : Ch10.Case10_1_1Two T L I) :
    Nat.card ↥(autI (SecA.isElemAbelian_fsuVM hyp) (T ⊓ L)) = 4 := by
  have hLN : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (SecA.le_fsuL0 T L).trans (SecA.fsuL0_le_normalizer_fsuVM T L I)
  set ρ : ↥L →* MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp)) :=
    (convI (SecA.isElemAbelian_fsuVM hyp)).comp (Subgroup.inclusion hLN)
  have e1 : ρ.range = autI (SecA.isElemAbelian_fsuVM hyp) L := by
    ext φ
    rw [MonoidHom.mem_range, mem_autI]
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨Subgroup.inclusion hLN l, l.2, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg⟩, rfl⟩
  have e2 : ((T ⊓ L).subgroupOf L).map ρ = autI (SecA.isElemAbelian_fsuVM hyp) (T ⊓ L) := by
    ext φ
    rw [Subgroup.mem_map, mem_autI]
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨Subgroup.inclusion hLN l, Subgroup.mem_subgroupOf.mp hl, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      exact ⟨⟨g, hg.2⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  have hsyl := isSylowTwoOf_map_range'' (SecA.isSylowTwoOf_inf hyp.fsu.maximal.1) ρ
  rw [e1, e2] at hsyl
  obtain ⟨⟨eA⟩, -⟩ := h2
  refine card_eq_four_of_sylow hsyl ?_
  rw [card_autI_L h37 h38 h322 hyp, Nat.card_congr eA.toEquiv, card_alt_five]

theorem conj_mem_autI_thompsonJ (hyp : Hyp10 G T L I)
    {g p : MulAut (IntMod (fsuVM T L I) (SecA.isElemAbelian_fsuVM hyp))}
    (hg : g ∈ autI (SecA.isElemAbelian_fsuVM hyp) T)
    (hp : p ∈ autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T)) :
    g * p * g⁻¹ ∈ autI (SecA.isElemAbelian_fsuVM hyp) (thompsonJ T) := by
  obtain ⟨s, hs, rfl⟩ := (mem_autI _).mp hg
  obtain ⟨j, hj, rfl⟩ := (mem_autI _).mp hp
  rw [mem_autI]
  refine ⟨s * j * s⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  exact (Subgroup.mem_normalizer_iff.mp
    ((Subgroup.le_normalizer.trans (normalizer_le_normalizer_thompsonJ T)) hs) j).mp hj

namespace Case2Data

variable {hyp : Hyp10 G T L I} {t : G} (D : Case2Data hyp t)

theorem autI_inf_L_le : autI (SecA.isElemAbelian_fsuVM hyp) (T ⊓ L) ≤ oTwoUpper D.K₁ :=
  D.oTwo₁ ▸ autI_mono _ inf_le_right

theorem mem_autI_inf_L_iff
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : Ch10.TmpL6_3_2_2_two) (h2 : Ch10.Case10_1_1Two T L I) :
    ∀ g (hg : g ∈ D.K₁), g ∈ autI (SecA.isElemAbelian_fsuVM hyp) (T ⊓ L) ↔
      D.θ₁ ⟨g, hg⟩ ∈ vFour := by
  set Q := autI (SecA.isElemAbelian_fsuVM hyp) (T ⊓ L)
  have hQK : Q ≤ D.K₁ := D.autI_inf_L_le.trans (oTwoUpper_le _)
  have himp : ∀ g (hg : g ∈ D.K₁), g ∈ Q → D.θ₁ ⟨g, hg⟩ ∈ vFour := by
    intro g hg hgQ
    have hA := mem_alternatingGroup_of_mem_oTwoUpper D.θ₁ (D.autI_inf_L_le hgQ)
    refine mem_vFour_of_normalizes _ (Perm.mem_alternatingGroup.mp hA) fun σ hσ => ?_
    set p : ↥D.K₁ := D.θ₁.symm σ
    have hpP : (p : MulAut _) ∈ D.P₁ := (D.memP₁ p p.2).mpr (by simpa [p] using hσ)
    have hgT : g ∈ autI (SecA.isElemAbelian_fsuVM hyp) T := autI_mono _ inf_le_left hgQ
    have h1 : g * p * g⁻¹ ∈ D.P₁ :=
      ⟨D.K₁.mul_mem (D.K₁.mul_mem hg p.2) (D.K₁.inv_mem hg),
        conj_mem_autI_thompsonJ hyp hgT hpP.2⟩
    have h2 := (D.memP₁ _ h1.1).mp h1
    have e : (⟨g * p * g⁻¹, h1.1⟩ : ↥D.K₁) = ⟨g, hg⟩ * p * (⟨g, hg⟩)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv] at h2
    simpa [p] using h2
  intro g hg
  refine ⟨himp g hg, fun hgV => ?_⟩
  classical
  set S := (Q.subgroupOf D.K₁).map D.θ₁.toMonoidHom
  have hS : ∀ σ ∈ S, σ ∈ vFour := by
    rintro σ ⟨q, hq, rfl⟩
    exact himp q q.2 (Subgroup.mem_subgroupOf.mp hq)
  have hcS : Nat.card S = 4 := by
    rw [← card_autI_inf_L h37 h38 h322 hyp h2]
    refine (Nat.card_congr (Subgroup.equivMapOfInjective _ _ D.θ₁.injective).toEquiv).symm.trans ?_
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv
  have hSeq : (S : Set (Perm (Fin 5))) = ↑vFour := by
    refine Set.eq_of_subset_of_ncard_le hS ?_ (Set.toFinite _)
    rw [Set.ncard_coe_finset, card_vFour, ← hcS, ← Nat.card_coe_set_eq]
    rfl
  have hmem : D.θ₁ ⟨g, hg⟩ ∈ S := by
    rw [← SetLike.mem_coe, hSeq]
    exact hgV
  obtain ⟨q, hq, hqg⟩ := hmem
  have h1 : (q : MulAut _) = g := congrArg Subtype.val (D.θ₁.injective hqg)
  rw [← h1]
  exact Subgroup.mem_subgroupOf.mp hq

theorem exists_rho
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : Ch10.TmpL6_3_2_2_two) (h2 : Ch10.Case10_1_1Two T L I) :
    ∃ g : Subgroup.normalizer (fsuVM T L I : Set G), (g : G) ∈ T ⊓ L ∧
      convI (SecA.isElemAbelian_fsuVM hyp) g = ((D.θ₁.symm rA : ↥D.K₁) : MulAut _) := by
  have h := (D.mem_autI_inf_L_iff h37 h38 h322 h2 _ (D.θ₁.symm rA).2).mpr
    (by simpa using rA_mem_vFour)
  exact (mem_autI _).mp h

end Case2Data

end CFSG.Quasithin.Vol2.Ch10.SecE
