module

public import CFSG.Quasithin.Vol2.Ch11SecE42S1b
public import CFSG.Quasithin.Vol2.Ch11SecE42S1a
public import CFSG.Quasithin.Vol2.Ch11SecE42Setup

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

variable {T L I : Subgroup G} {n : ℕ}

theorem le_centralizer_of_case21 (h3214 : TmpL6_3_2_14) (h : Hyp11 G T L I n) {z : G}
    (hz : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G)) {K Kp : Subgroup G}
    (hloc : quasithinIsLocal T Kp) (hKKp : K ≤ Kp)
    (hKz : K ≤ Subgroup.centralizer ({z} : Set G))
    (h21 : ⁅(CFSG.oddCore ↥(modO2Image (Kp ⊔ T) Kp)).map (modO2Image (Kp ⊔ T) Kp).subtype,
        modO2Image (Kp ⊔ T) Kp⁆ ≠ ⊥ ∧
      modO2Image (Kp ⊔ T) Kp = modO2Image (Kp ⊔ T) K ⊔
        (CFSG.oddCore ↥(modO2Image (Kp ⊔ T) Kp)).map (modO2Image (Kp ⊔ T) Kp).subtype) :
    Kp ≤ Subgroup.centralizer ({z} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKp : Kp ∈ cComp (Kp ⊔ T) := hloc.2.1
  have hR := h3214 G T Kp h.fsu.simple h.fsu.nonabelian h.fsu.qtke h.fsu.sylow hloc
    (not_isQuasisimple_of_case21 hKp h21.1)
  have hS := isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow (le_sup_right : T ≤ Kp ⊔ T)
  obtain ⟨S', hS'⟩ := exists_sylow_of_quasithinIsSylowTwo h.fsu.sylow
  have hchar : QuasithinUnique.CharTwo (Kp ⊔ T) :=
    charTwo_of_inH h.fsu.qtke.2.1 S' ⟨hS' ▸ le_sup_right, hloc.2.2.2⟩
  have hzT : z ∈ T := SecA.fsuV_le_T h hz.1
  have hz2 : z ^ 2 = 1 := (SecA.isElemAbelian_fsuV h).2 z hz.1
  have hzR := mem_reducedAggregate_of_mem hS hchar hzT hz.2 hz2
  have hsolz : solvRad Kp ≤ Subgroup.centralizer ({z} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr
      ((Subgroup.mem_centralizer_iff.mp (hR hy) z hzR).symm)
  set Lb := modO2Image (Kp ⊔ T) Kp with hLb
  set OL : Subgroup (↥(Kp ⊔ T) ⧸ CFSG.pCore 2 ↥(Kp ⊔ T)) := (CFSG.oddCore ↥Lb).map Lb.subtype
    with hOL
  have hOLLb : OL ≤ Lb := Subgroup.map_subtype_le _
  have hLbOL : Lb ≤ Subgroup.normalizer (OL : Set (↥(Kp ⊔ T) ⧸ CFSG.pCore 2 ↥(Kp ⊔ T))) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨o, ho, rfl⟩
      exact ⟨⟨x, hx⟩ * o * ⟨x, hx⟩⁻¹, (CFSG.oddCore_normal (G := ↥Lb)).conj_mem _ ho _, rfl⟩
    · intro hy
      obtain ⟨o, ho, ho'⟩ := hy
      have hyL : y ∈ Lb := by
        have h1 : x * y * x⁻¹ ∈ Lb := ho' ▸ o.2
        have h2 := Lb.mul_mem (Lb.mul_mem (Lb.inv_mem hx) h1) hx
        simpa [mul_assoc] using h2
      refine ⟨⟨y, hyL⟩, ?_, rfl⟩
      have h3 := (CFSG.oddCore_normal (G := ↥Lb)).conj_mem _ ho (⟨x, hx⟩⁻¹)
      have e : (⟨x, hx⟩⁻¹ * o * (⟨x, hx⟩⁻¹)⁻¹ : ↥Lb) = ⟨y, hyL⟩ := Subtype.ext (by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        rw [show (o : ↥(Kp ⊔ T) ⧸ CFSG.pCore 2 ↥(Kp ⊔ T)) = x * y * x⁻¹ from ho']
        group)
      rwa [e] at h3
  set f := (QuotientGroup.mk' (CFSG.pCore 2 ↥(Kp ⊔ T))).comp
    (Subgroup.inclusion (le_sup_left : Kp ≤ Kp ⊔ T)) with hf
  have hfLb : ∀ k : ↥Kp, f k ∈ Lb := fun k => ⟨Subgroup.inclusion le_sup_left k,
    Subgroup.mem_subgroupOf.mpr k.2, rfl⟩
  set A : Subgroup ↥Kp := OL.comap f with hA
  have hAn : A.Normal := ⟨fun a ha k => by
    show f (k * a * k⁻¹) ∈ OL
    rw [map_mul, map_mul, map_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hLbOL (hfLb k)) (f a)).mp ha⟩
  have hOLs : Group.IsSolvable ↥OL := by
    have hs : Group.IsSolvable ↥(CFSG.oddCore ↥Lb) :=
      CFSG.FeitThompson.isSolvable_of_odd_natCard _ (SecD.odd_card_oddCore _)
    exact Group.isSolvable_of_isSolvable_injective (f := (Subgroup.equivMapOfInjective
      (CFSG.oddCore ↥Lb) Lb.subtype Lb.subtype_injective).symm.toMonoidHom)
      (Subgroup.equivMapOfInjective _ _ Lb.subtype_injective).symm.injective
  have hAs : Group.IsSolvable ↥A := by
    set fA : ↥A →* ↥OL := (f.comp A.subtype).codRestrict OL (fun a => a.2) with hfA
    have hker : IsPGroup 2 ↥fA.ker := fun a => by
      have h0 : fA (a : ↥A) = 1 := a.2
      have h1 : f (a : ↥A) = 1 := congrArg Subtype.val h0
      have h2 : ((a : ↥A) : ↥Kp) ∈ (f.ker) := h1
      have h3 := (mem_ker_modO2_iff (le_sup_left : Kp ≤ Kp ⊔ T) ((a : ↥A) : ↥Kp)).mp h2
      obtain ⟨j, hj⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Kp ⊔ T)) ⟨_, h3⟩
      exact ⟨j, Subtype.ext (Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hj)))⟩
    have : Group.IsNilpotent ↥fA.ker := hker.isNilpotent
    exact Group.isSolvable_of_ker_le_range fA.ker.subtype fA (by rw [Subgroup.range_subtype])
  have hAsol : A.map Kp.subtype ≤ solvRad Kp := by
    refine le_solvRad (Subgroup.map_subtype_le _) ?_ ?_
    · rw [map_subtype_subgroupOf']
      exact hAn
    · exact Group.isSolvable_of_isSolvable_injective (f := (Subgroup.equivMapOfInjective A
        Kp.subtype Kp.subtype_injective).symm.toMonoidHom)
        (Subgroup.equivMapOfInjective _ _ Kp.subtype_injective).symm.injective
  have hAz : A.map Kp.subtype ≤ Subgroup.centralizer ({z} : Set G) := hAsol.trans hsolz
  have hKbO : modO2Image (Kp ⊔ T) K ≤
      Subgroup.normalizer (OL : Set (↥(Kp ⊔ T) ⧸ CFSG.pCore 2 ↥(Kp ⊔ T))) :=
    (Subgroup.map_mono (fun x hx => Subgroup.mem_subgroupOf.mpr
      (hKKp (Subgroup.mem_subgroupOf.mp hx)))).trans hLbOL
  have hO2z : pCoreOf 2 (Kp ⊔ T) ≤ Subgroup.centralizer ({z} : Set G) :=
    (pCoreOf_two_le_of_sylowIn hS.1 hS.2.1 hS.2.2).trans (le_centralizer_of_mem hz.2)
  intro k hk
  have hk' : f ⟨k, hk⟩ ∈ ((modO2Image (Kp ⊔ T) K ⊔ OL : Subgroup _) : Set _) := by
    rw [← h21.2]
    exact hfLb ⟨k, hk⟩
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hKbO] at hk'
  obtain ⟨kb, ⟨b, hb, rfl⟩, ol, hol, hbo⟩ := hk'
  obtain ⟨o', ho', rfl⟩ := hol
  obtain ⟨o, ho, ho'eq⟩ := o'.2
  have hbK : (b : G) ∈ K := Subgroup.mem_subgroupOf.mp hb
  have hoKp : (o : G) ∈ Kp := Subgroup.mem_subgroupOf.mp ho
  have hoA : (⟨o, hoKp⟩ : ↥Kp) ∈ A := by
    show f ⟨o, hoKp⟩ ∈ OL
    have : f ⟨o, hoKp⟩ = (o' : ↥(Kp ⊔ T) ⧸ CFSG.pCore 2 ↥(Kp ⊔ T)) := ho'eq
    rw [this]
    exact ⟨o', ho', rfl⟩
  have hoz : (o : G) ∈ Subgroup.centralizer ({z} : Set G) := hAz ⟨_, hoA, rfl⟩
  have hbz : (b : G) ∈ Subgroup.centralizer ({z} : Set G) := hKz hbK
  have heq : QuotientGroup.mk' (CFSG.pCore 2 ↥(Kp ⊔ T)) (b * o) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥(Kp ⊔ T)) ⟨k, Subgroup.mem_sup_left hk⟩ := by
    rw [map_mul, ho'eq]
    exact hbo
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at heq
  rw [← SecD.pCoreOf_subgroupOf, Subgroup.mem_subgroupOf] at heq
  have hq := hO2z heq
  have e : k = (b : G) * (o : G) *
      (((b * o)⁻¹ * ⟨k, Subgroup.mem_sup_left hk⟩ : ↥(Kp ⊔ T)) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hbz hoz) hq

end CFSG.Quasithin.Vol2.Ch11.SecE
