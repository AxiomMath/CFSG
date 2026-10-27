module

public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.EmptyFaithful.SBd13Main

public section

namespace CFSG.Quasithin.ModH

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.R3c14

@[expose] def SolvNine (X : Type) [Group X] : Prop :=
  ∀ P Y : Subgroup X, IsSylowTwoOf P ⊤ → P ≤ Subgroup.normalizer (Y : Set X) →
    Group.IsSolvable ↥Y → 9 ∣ Nat.card ↥Y → False

theorem SolvNine.of_equiv {X X' : Type} [Group X] [Group X'] (φ : X' ≃* X) (h : SolvNine X) :
    SolvNine X' := by
  intro P Y hP hN hs h9
  have hP' : IsSylowTwoOf (P.map φ.toMonoidHom) ⊤ := by
    obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hP
    refine K1.isSylowTwoOf_top_iff.mpr ⟨hp.map φ.toMonoidHom, ?_⟩
    rw [Subgroup.index_map_of_bijective (f := φ.toMonoidHom) φ.bijective]
    exact hi
  refine h (P.map φ.toMonoidHom) (Y.map φ.toMonoidHom) hP' ?_ ?_ ?_
  · intro t ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    exact (R3c11.mem_normalizer_map_equiv_iff φ Y t₀).mpr (hN ht₀)
  · have : Group.IsSolvable ↥Y := hs
    exact Group.isSolvable_of_surjective (f := (φ.toMonoidHom.subgroupMap Y))
      (φ.toMonoidHom.subgroupMap_surjective Y)
  · rw [Nat.card_congr (Y.equivMapOfInjective φ.toMonoidHom φ.injective).toEquiv.symm]
    exact h9

section Main

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_of_struct {H : Subgroup G}
    (hq : IsElemAbelianOfRank 3 2 (OTwoQuot H) ∨ IsPOnePlusTwo 3 (OTwoQuot H)) :
    Group.IsSolvable ↥H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h2 : IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥H) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have : Group.IsNilpotent ↥(CFSG.Open.pCore 2 ↥H) := h2.isNilpotent
  have : Group.IsSolvable ↥(CFSG.Open.pCore 2 ↥H) := inferInstance
  obtain ⟨b, k, -, hb, hcard⟩ := SBd11.card_form_of_struct hq
  have hQ3 : IsPGroup 3 (↥H ⧸ CFSG.Open.pCore 2 ↥H) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥H)
    rw [hcard, hb] at h1
    have hpos : 0 < 2 ^ b := Nat.two_pow_pos b
    have hc : Nat.card (↥H ⧸ CFSG.Open.pCore 2 ↥H) = 3 ^ k := by
      have : Nat.card (↥H ⧸ CFSG.Open.pCore 2 ↥H) * 2 ^ b = 3 ^ k * 2 ^ b := by
        rw [← h1]; ring
      exact Nat.eq_of_mul_eq_mul_right hpos this
    exact IsPGroup.of_card hc
  have : Group.IsNilpotent (↥H ⧸ CFSG.Open.pCore 2 ↥H) := hQ3.isNilpotent
  have : Group.IsSolvable (↥H ⧸ CFSG.Open.pCore 2 ↥H) := inferInstance
  exact Group.isSolvable_of_ker_le_range (CFSG.Open.pCore 2 ↥H).subtype
    (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) (by simp)

theorem false_of_solvNine {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hN : I ≤ Subgroup.normalizer (L : Set G)) (hYL : Yp ≤ L)
    {X : Type} [Group X] (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* X) (hX : SolvNine X) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hpc := SBd13.pCore_eq_center_of_center_eq hZ
  have hX' : SolvNine (↥L ⧸ Subgroup.center ↥L) :=
    SolvNine.of_equiv ((QuotientGroup.quotientMulEquivOfEq hpc.symm).trans e) hX
  have hLI : L ≤ I := le_of_mem_cComp c.c33.mem
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans c.hyp.hyp.T_le
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := fun s hs => hN (hSI hs)
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
      (le_inf hLI Subgroup.le_normalizer) inf_le_right
  set Q : Subgroup G := Sgp153 T V₁ ⊓ L with hQdef
  have hMIY : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := fun x hx => by
    have : x ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by rw [c.facts.norm_eq]; exact hx
    exact this.2
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := fun s hs => hMIY ⟨hSM hs, hSI hs⟩
  have hQS : Q ≤ Sgp153 T V₁ := inf_le_left
  obtain ⟨Tsyl, hT, -, -⟩ := R3c10.exists_quotSylow hZ hQsyl
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZdef
  set π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hπ
  have hTsyl : IsSylowTwoOf ((Q.subgroupOf L).map π) ⊤ := by
    rw [← hT]
    exact K1.isSylowTwoOf_top_iff.mpr ⟨Tsyl.isPGroup', Tsyl.not_dvd_index⟩
  have hnorm := quot_normalizes (L := L) (A := Q) hYL (fun q hq => hSN (hQS hq))
  obtain ⟨b, k, hk2, -, hcard⟩ := SBd11.card_form_of_struct c.facts11.struct_Yp
  have hsolvY : Group.IsSolvable ↥Yp := isSolvable_of_struct c.facts11.struct_Yp
  have hcen : IsPGroup 2 (Subgroup.center ↥L) := SBd11.isPGroup_center_of_center_eq hZ
  let ψ : ↥Yp →* ↥L ⧸ Z := π.comp (Subgroup.inclusion hYL)
  have hker : ∀ z : ↥Yp, z ∈ ψ.ker ↔ Subgroup.inclusion hYL z ∈ Z := fun z => by
    simp [ψ, hπ, MonoidHom.mem_ker, QuotientGroup.eq_one_iff]
  have hK2 : IsPGroup 2 ψ.ker := by
    intro z
    obtain ⟨m, hm⟩ := hcen ⟨_, (hker z.1).1 z.2⟩
    refine ⟨m, Subtype.ext ?_⟩
    have h1 := congrArg (fun w : ↥(Subgroup.center ↥L) => (w : ↥L)) hm
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h1
    apply Subgroup.inclusion_injective hYL
    simpa [map_pow] using h1
  have hrange : ψ.range = (Yp.subgroupOf L).map π := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Subgroup.inclusion hYL y, Subgroup.mem_subgroupOf.mpr y.2, rfl⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨⟨(l : G), Subgroup.mem_subgroupOf.mp hl⟩, rfl⟩
  have hsolv : Group.IsSolvable ↥((Yp.subgroupOf L).map π) := by
    rw [← hrange]
    exact Group.isSolvable_of_surjective ψ.rangeRestrict_surjective
  have hprod := Subgroup.card_ker_mul_card_range ψ
  obtain ⟨i, hi⟩ := (IsPGroup.iff_card).1 hK2
  have h3k : 3 ^ k ∣ Nat.card ψ.range := by
    have h1 : 3 ^ k ∣ Nat.card ψ.ker * Nat.card ψ.range := by
      rw [hprod, hcard]
      exact Dvd.intro_left _ rfl
    have hcop : Nat.Coprime (3 ^ k) (Nat.card ψ.ker) := by
      rw [hi]
      exact Nat.Coprime.pow k i (by norm_num)
    exact hcop.dvd_of_dvd_mul_left h1
  have h9 : 9 ∣ Nat.card ψ.range := (pow_dvd_pow 3 hk2).trans h3k
  exact hX' _ _ hTsyl hnorm hsolv (by rw [← hrange]; exact h9)

end Main

end CFSG.Quasithin.ModH
