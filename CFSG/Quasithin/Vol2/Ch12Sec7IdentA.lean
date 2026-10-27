module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeldBridge
public import CFSG.LargeExtraspecial.Transport
public import CFSG.Quasithin.Vol2.Ch12Sec7IdentSL32

public section

namespace CFSG.Quasithin.H13.I1277

open CFSG.Open CFSG.LargeExtraspecial Subgroup

variable {G : Type} [Group G]

abbrev Gz (z : G) : Subgroup G := Subgroup.centralizer ({z} : Set G)

@[expose] def StructAt (G : Type) [Group G] [Finite G] (z : G) : Prop :=
  IsExtraspecialPGroup 2 ↥(pCoreOf 2 (Gz z)) ∧ Nat.card ↥(pCoreOf 2 (Gz z)) = 128 ∧
    Gz z ⊓ Subgroup.centralizer ((pCoreOf 2 (Gz z) : Subgroup G) : Set G) ≤ pCoreOf 2 (Gz z) ∧
    (∃ f : ↥(Gz z) →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), Function.Surjective f ∧
      f.ker = (pCoreOf 2 (Gz z)).subgroupOf (Gz z)) ∧
    ∃ A B : Subgroup G, IsElemAbelian 2 A ∧ IsElemAbelian 2 B ∧ Nat.card A = 16 ∧
      Nat.card B = 16 ∧ A ⊔ B = pCoreOf 2 (Gz z) ∧ A ⊓ B = Subgroup.zpowers z ∧
      Gz z ≤ Subgroup.normalizer (A : Set G) ∧ Gz z ≤ Subgroup.normalizer (B : Set G)

@[expose] noncomputable def settingOf {z : G} [Finite G] (hz : orderOf z = 2)
    (hext : IsExtraspecialPGroup 2 ↥(pCoreOf 2 (Gz z)))
    (hcent : Gz z ⊓ Subgroup.centralizer ((pCoreOf 2 (Gz z) : Subgroup G) : Set G) ≤
      pCoreOf 2 (Gz z)) : Setting G where
  z := z
  orderOf_z := hz
  Q := pCore 2 ↥(Gz z)
  normal := inferInstance
  extraspecial := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact isExtraspecialPGroup_of_mulEquiv
      (Subgroup.equivMapOfInjective (pCore 2 ↥(Gz z)) (Gz z).subtype Subtype.val_injective).symm
      hext
  centralizer_le := by
    intro x hx
    have hxC : (x : G) ∈ Subgroup.centralizer ((pCoreOf 2 (Gz z) : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hp
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx q hq)
    have hxP : (x : G) ∈ pCoreOf 2 (Gz z) := hcent ⟨x.2, hxC⟩
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxP
    have hyx' : y = x := Subtype.ext hyx
    rw [← hyx']
    exact hy
  le_of_normal := fun N hN hp => le_sSup ⟨hN, hp⟩


theorem card_pCore_centralizer {G : Type} [Group G] {z : G}
    (h128 : Nat.card ↥(pCoreOf 2 (Gz z)) = 128) :
    Nat.card ↥(pCore 2 ↥(Gz z)) = 128 := by
  rw [← h128]
  exact Nat.card_congr
    (Subgroup.equivMapOfInjective (pCore 2 ↥(Gz z)) (Gz z).subtype Subtype.val_injective).toEquiv

theorem card_pCore_inf_eq [Finite G] {z : G} {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hV64 : Nat.card V = 64) (hzV : z ∈ V) (hz2 : orderOf z = 2) (hS : StructAt G z) :
    Nat.card ↥(pCoreOf 2 (Gz z) ⊓ V) = 16 := by
  classical
  obtain ⟨hext, hP128, hcent, ⟨f, hfsurj, hfker⟩, -⟩ := hS
  have hVG : V ≤ Gz z := fun v hv => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hV.1.is_comm.comm ⟨v, hv⟩ ⟨z, hzV⟩)
  set S : Setting G := settingOf hz2 hext hcent with hSdef
  have hSQ : Nat.card S.Q = 128 := card_pCore_centralizer hP128
  have hwidth : S.width = 3 := S.width_eq (n := 3) (by rw [hSQ]; norm_num)
  have hQG : S.QG = pCoreOf 2 (Gz z) := rfl
  have hVQ_comm : ∀ x ∈ S.QG ⊓ V, ∀ y ∈ S.QG ⊓ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hV.1.is_comm.comm ⟨x, hx.2⟩ ⟨y, hy.2⟩)
  have hupper : Nat.card ↥(S.QG ⊓ V) ≤ 16 := by
    have h := S.card_le_of_commute (A := S.QG ⊓ V) inf_le_left hVQ_comm
    rw [hwidth] at h
    norm_num at h
    exact h
  have hker : (f.comp (Subgroup.inclusion hVG)).ker = (S.QG ⊓ V).subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : f (Subgroup.inclusion hVG v) = 1 ↔ (v : G) ∈ pCoreOf 2 (Gz z) := by
      rw [← MonoidHom.mem_ker, hfker, Subgroup.mem_subgroupOf]
      rfl
    rw [MonoidHom.comp_apply, h1, hQG]
    exact ⟨fun h => ⟨h, v.2⟩, fun h => h.1⟩
  have hkerCard : Nat.card (f.comp (Subgroup.inclusion hVG)).ker = Nat.card ↥(S.QG ⊓ V) := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : S.QG ⊓ V ≤ V)).toEquiv]
  have htot : Nat.card ↥V = Nat.card (f.comp (Subgroup.inclusion hVG)).range *
      Nat.card (f.comp (Subgroup.inclusion hVG)).ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (f.comp (Subgroup.inclusion hVG)).ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange
        (f.comp (Subgroup.inclusion hVG))).toEquiv]
  have hrc : ∀ x ∈ (f.comp (Subgroup.inclusion hVG)).range,
      ∀ y ∈ (f.comp (Subgroup.inclusion hVG)).range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact congrArg Subtype.val (hV.1.is_comm.comm a b)
  have hre : ∀ x ∈ (f.comp (Subgroup.inclusion hVG)).range, x ^ 2 = 1 := by
    rintro _ ⟨a, rfl⟩
    have ha2 : a ^ 2 = 1 := Subtype.ext (by simpa using hV.2 a a.2)
    rw [← map_pow, ha2, map_one]
  have hrange : IsElemAbelian 2 (f.comp (Subgroup.inclusion hVG)).range :=
    ⟨⟨⟨fun x y => Subtype.ext (hrc x x.2 y y.2)⟩⟩, fun x hx => hre x hx⟩
  have hR4 := sl32_card_le_four _ hrange
  have hlower : 16 ≤ Nat.card ↥(S.QG ⊓ V) := by
    by_contra hlt
    rw [not_le, ← hkerCard] at hlt
    have hk : Nat.card (f.comp (Subgroup.inclusion hVG)).ker ≤ 15 := by omega
    have hmul := Nat.mul_le_mul hR4 hk
    rw [← htot, hV64] at hmul
    omega
  rw [← hQG]
  exact le_antisymm hupper hlower

theorem centralizer_iso_transvection_of_structAt [Finite G] {z : G} {V : Subgroup G}
    (hV : IsElemAbelian 2 V) (hV64 : Nat.card V = 64) (hzV : z ∈ V) (hz1 : z ≠ 1)
    (hS : StructAt G z) :
    Nonempty (↥(Gz z) ≃* ↥(Subgroup.centralizer
      ({Quasithin.H13.transvection15} : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))))) := by
  classical
  have hS0 := hS
  obtain ⟨hext, hP128, hcent, ⟨f, hfsurj, hfker⟩, A, B, hA, hB, -, -, hAB, hAB', hCA, hCB⟩ := hS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : orderOf z = 2 := orderOf_eq_prime (by simpa using hV.2 z hzV) hz1
  have hVG : V ≤ Gz z := fun v hv => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hV.1.is_comm.comm ⟨v, hv⟩ ⟨z, hzV⟩)
  set S : Setting G := settingOf hz2 hext hcent with hSdef
  have hSQ : Nat.card S.Q = 128 := card_pCore_centralizer hP128
  have hwidth : S.width = 3 := S.width_eq (n := 3) (by rw [hSQ]; norm_num)
  have hQG : S.QG = pCoreOf 2 (Gz z) := rfl
  have hidx : Nat.card S.M = 168 * Nat.card S.Q := by
    have hPle : pCoreOf 2 (Gz z) ≤ Gz z := Subgroup.map_subtype_le _
    have hker : Nat.card f.ker = 128 := by
      rw [hfker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv, hP128]
    have hq : Nat.card (↥(Gz z) ⧸ f.ker) = 168 := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hfsurj).toEquiv, card_sl32]
    have hsplit := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    show Nat.card ↥(Gz z) = 168 * Nat.card S.Q
    rw [hsplit, hq, hker, hSQ]
  have hAQ : A ≤ S.QG := by
    rw [hQG, ← hAB]
    exact le_sup_left
  have hBQ : B ≤ S.QG := by
    rw [hQG, ← hAB]
    exact le_sup_right
  have hAB'' : A ⊔ B = S.QG := by
    rw [hQG]
    exact hAB
  have hEQ : Nat.card ↥(S.QG ⊓ V : Subgroup G) = 16 := by
    rw [hQG]
    exact card_pCore_inf_eq hV hV64 hzV hz2 hS0
  have hAS := CFSG.ComponentClassification.AS81.nonempty_centralizer_mulEquiv_sl5 S hwidth hAQ hBQ
    hA hB hAB' hAB'' hCA hCB hidx hVG hV hV64 hEQ
  rw [CFSG.ComponentClassification.AS81.transvection15_eq_cornerTransvection]
  exact hAS

end CFSG.Quasithin.H13.I1277
