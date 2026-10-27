module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModD
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.SecIrrHss15

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.Quasithin.F53.Stellmacher.S43
open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs Equiv

namespace F53.Stellmacher

namespace S35.B5

variable {G : Type} [Group G] [Finite G]

theorem hom_trivial_of_coprime_five {X : Subgroup G}
    (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5))) {F : Type} [Group F] [Finite F]
    (hF : Nat.Coprime 5 (Nat.card F)) (φ : ↥(oTwoRes X) →* F) : φ = 1 := by
  obtain ⟨θ, hs, hk⟩ := epi_of_otwo hq
  have hmem : ∀ l : ↥(oTwoRes X),
      θ (Subgroup.inclusion (oTwoRes_le X) l) ∈ alternatingGroup (Fin 5) := fun l => by
    rw [← map_oTwoRes_eq_alt hs]
    exact Subgroup.mem_map_of_mem θ (Subgroup.mem_subgroupOf.mpr l.2)
  let A : ↥(oTwoRes X) →* ↥(alternatingGroup (Fin 5)) :=
    (θ.comp (Subgroup.inclusion (oTwoRes_le X))).codRestrict _ hmem
  have hAs : Function.Surjective A := by
    intro a
    have ha : (a : Perm (Fin 5)) ∈ Subgroup.map θ ((oTwoRes X).subgroupOf X) := by
      rw [map_oTwoRes_eq_alt hs]
      exact a.2
    obtain ⟨x, hx, hxa⟩ := ha
    exact ⟨⟨x.1, Subgroup.mem_subgroupOf.mp hx⟩, Subtype.ext hxa⟩
  have : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have : (φ.ker.map A).Normal := Subgroup.Normal.map inferInstance A hAs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (φ.ker.map A) with h | h
  · exfalso
    have hle : φ.ker ≤ A.ker := fun k hk => by
      have : A k ∈ φ.ker.map A := ⟨k, hk, rfl⟩
      rw [h] at this
      exact this
    have h5 : 5 ∣ Nat.card F := by
      have h1 : A.ker.index ∣ φ.ker.index := Subgroup.index_dvd_of_le hle
      rw [Subgroup.index_ker, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hAs,
        Subgroup.card_top] at h1
      have h60 : Nat.card ↥(alternatingGroup (Fin 5)) = 60 := by
        rw [Nat.card_eq_fintype_card, card_alternatingGroup]
        decide
      rw [h60] at h1
      exact (show 5 ∣ 60 by norm_num).trans (h1.trans (Subgroup.card_subgroup_dvd_card _))
    exact absurd (Nat.Coprime.eq_one_of_dvd hF h5) (by norm_num)
  · have hodd : ∀ y : ↥(oTwoRes X), ∀ m : ℕ, Odd m → y ^ m = 1 → φ y = 1 := by
      intro y m hm hym
      have hy : A y ∈ φ.ker.map A := by rw [h]; trivial
      obtain ⟨k, hkK, hky⟩ := hy
      have hn : k⁻¹ * y ∈ A.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hky, inv_mul_cancel]
      have hnQ : ((k⁻¹ * y : ↥(oTwoRes X)) : G) ∈ pCoreOf 2 X := by
        have h1 : θ (Subgroup.inclusion (oTwoRes_le X) (k⁻¹ * y)) = 1 := by
          have := congrArg Subtype.val hn
          exact this
        have h2 : Subgroup.inclusion (oTwoRes_le X) (k⁻¹ * y) ∈ θ.ker := h1
        rw [hk, Subgroup.mem_subgroupOf] at h2
        exact h2
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp (pCoreOf_isPGroup 2 X))
        ⟨((k⁻¹ * y : ↥(oTwoRes X)) : G), hnQ⟩
      have hj' : orderOf (k⁻¹ * y) = 2 ^ j :=
        (Subgroup.orderOf_coe (k⁻¹ * y)).symm.trans
          ((Subgroup.orderOf_coe (⟨((k⁻¹ * y : ↥(oTwoRes X)) : G), hnQ⟩ :
            ↥(pCoreOf 2 X))).trans hj)
      have hφ : φ y = φ (k⁻¹ * y) := by
        rw [map_mul, map_inv, hkK, inv_one, one_mul]
      have d1 : orderOf (φ y) ∣ m := orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hym, map_one])
      have d2 : orderOf (φ y) ∣ 2 ^ j := by
        rw [hφ, ← hj']
        exact orderOf_map_dvd _ _
      have hcop : Nat.Coprime (2 ^ j) m :=
        Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hm)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd d2 d1))
    ext y
    have hy : (y : G) ∈ φ.ker.map (oTwoRes X).subtype := by
      have hle : oTwoRes X ≤ φ.ker.map (oTwoRes X).subtype := by
        refine (Subgroup.closure_le _).mpr fun x hx => ?_
        obtain ⟨hxX, m, hm, hxm⟩ := hx
        have hxL : x ∈ oTwoRes X := Subgroup.subset_closure ⟨hxX, m, hm, hxm⟩
        refine ⟨⟨x, hxL⟩, hodd ⟨x, hxL⟩ m hm (Subtype.ext hxm), rfl⟩
      exact hle y.2
    obtain ⟨z, hz, hzy⟩ := hy
    have : z = y := Subtype.ext hzy
    subst this
    simpa using hz

theorem oTwoRes_le_of_relIndex_le_four {X N : Subgroup G}
    (hq : Nonempty (OTwoQuot X ≃* Perm (Fin 5))) (_hN : N ≤ X) (hidx : N.relIndex X ≤ 4) :
    oTwoRes X ≤ N := by
  let N' : Subgroup ↥X := N.subgroupOf X
  let φ : ↥(oTwoRes X) →* Perm (↥X ⧸ N') :=
    (MulAction.toPermHom ↥X (↥X ⧸ N')).comp (Subgroup.inclusion (oTwoRes_le X))
  have hpos : 0 < N'.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have hle : N'.index ≤ 4 := hidx
  have hF : Nat.Coprime 5 (Nat.card (Perm (↥X ⧸ N'))) := by
    rw [Nat.card_perm]
    show Nat.Coprime 5 (N'.index).factorial
    interval_cases (N'.index) <;> decide
  have h1 := hom_trivial_of_coprime_five hq hF φ
  intro l hl
  have h2 : φ ⟨l, hl⟩ (((1 : ↥X) : ↥X ⧸ N')) = ((1 : ↥X) : ↥X ⧸ N') := by rw [h1]; rfl
  have h3 : ((⟨l, oTwoRes_le X hl⟩ * 1 : ↥X) : ↥X ⧸ N') = ((1 : ↥X) : ↥X ⧸ N') := h2
  have h4 : ((⟨l, oTwoRes_le X hl⟩ * 1 : ↥X))⁻¹ * 1 ∈ N' := QuotientGroup.eq.mp h3
  have h5 : (⟨l, oTwoRes_le X hl⟩ : ↥X) ∈ N' := by
    simpa using N'.inv_mem h4
  exact Subgroup.mem_subgroupOf.mp h5

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
