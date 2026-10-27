module

public import CFSG.Quasithin.Vol2.Ch12Sec7Mod4E
public import CFSG.Quasithin.Vol2.Ch12Sec7ModV
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData2
import all CFSG.Quasithin.Vol2.Ch12Sec2Ident

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

abbrev OP5 : Type := {q : OP // q.1 ≠ 1}

theorem oPts5_facts : ∀ p ∈ oPts, p ≠ 1 → p ∈ [4, 16, 21, 57, 45] := by decide

theorem oPts5_facts' : ∀ p ∈ [4, 16, 21, 57, 45], p ∈ oPts ∧ p ≠ 1 := by decide

theorem one_mem_oPts : 1 ∈ oPts := by decide

theorem zs6_fix1 : ∀ z ∈ zs6, z.app 1 = 1 → z = B6.id := by decide

theorem card_OP5 : Nat.card OP5 = 5 := by
  have e : OP5 ≃ {p : ℕ // p ∈ [4, 16, 21, 57, 45]} :=
    { toFun := fun q => ⟨q.1.1, oPts5_facts _ q.1.2 q.2⟩
      invFun := fun p => ⟨⟨p.1, (oPts5_facts' _ p.2).1⟩, (oPts5_facts' _ p.2).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e]
  have e2 : {p : ℕ // p ∈ [4, 16, 21, 57, 45]} ≃ ↥([4, 16, 21, 57, 45] : List ℕ).toFinset :=
    Equiv.subtypeEquivRight fun p => by simp
  rw [Nat.card_congr e2, Nat.card_eq_finsetCard]
  rfl

instance : Finite OP5 := Subtype.finite

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem piPts_one
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V)) (m : ↥h.hyp.MVbar)
    (hm : (C.cB m).app 1 = 1) : piPts h hC m ⟨1, one_mem_oPts⟩ = ⟨1, one_mem_oPts⟩ := by
  apply Subtype.ext
  show pn ((C.cB m).app 1) = 1
  rw [hm]
  rfl

theorem piPts_ne_one
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V)) (m : ↥h.hyp.MVbar)
    (hm : (C.cB m).app 1 = 1) (x : OP) : (piPts h hC m x).1 ≠ 1 ↔ x.1 ≠ 1 := by
  constructor
  · intro hx hx1
    apply hx
    have : x = ⟨1, one_mem_oPts⟩ := Subtype.ext hx1
    rw [this, piPts_one h hC m hm]
  · intro hx hx1
    apply hx
    have e : piPts h hC m x = piPts h hC m ⟨1, one_mem_oPts⟩ := by
      rw [piPts_one h hC m hm]
      exact Subtype.ext hx1
    exact congrArg Subtype.val ((piPts h hC m).injective e)

@[expose] noncomputable def pi5
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V))
    {H : Subgroup (MulAut ↥V)} (hHM : H ≤ h.hyp.MVbar) (hH1 : ∀ a ∈ H, (C.cB a).app 1 = 1) :
    ↥H →* Equiv.Perm OP5 where
  toFun a := (piPts h hC ⟨a, hHM a.2⟩).subtypePerm fun x =>
    piPts_ne_one h hC ⟨a, hHM a.2⟩ (hH1 a a.2) x
  map_one' := by
    ext x
    show ((piPts h hC ⟨1, hHM (1 : ↥H).2⟩ x.1 : OP) : ℕ) = x.1.1
    rw [show (⟨1, hHM (1 : ↥H).2⟩ : ↥h.hyp.MVbar) = 1 from rfl, map_one]
    rfl
  map_mul' a b := by
    ext x
    show ((piPts h hC ⟨a * b, hHM (a * b).2⟩ x.1 : OP) : ℕ) =
      ((piPts h hC ⟨a, hHM a.2⟩ (piPts h hC ⟨b, hHM b.2⟩ x.1) : OP) : ℕ)
    rw [show (⟨a * b, hHM (a * b).2⟩ : ↥h.hyp.MVbar) = ⟨a, hHM a.2⟩ * ⟨b, hHM b.2⟩ from rfl,
      map_mul]
    rfl

theorem pi5_injective
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V))
    {H : Subgroup (MulAut ↥V)} (hHM : H ≤ h.hyp.MVbar) (hH1 : ∀ a ∈ H, (C.cB a).app 1 = 1) :
    Function.Injective (pi5 h hC hHM hH1) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hker : (⟨a, hHM a.2⟩ : ↥h.hyp.MVbar) ∈ (piPts h hC).ker := by
    rw [MonoidHom.mem_ker]
    ext x
    by_cases hx : x.1 = 1
    · have : x = ⟨1, one_mem_oPts⟩ := Subtype.ext hx
      rw [this, piPts_one h hC _ (hH1 a a.2)]
      rfl
    · have e := congrArg (fun σ : Equiv.Perm OP5 => ((σ ⟨x, hx⟩ : OP5) : OP)) ha
      exact congrArg Subtype.val e
  have hz := (mem_ker_piPts h hC _).1 hker
  have hid := zs6_fix1 _ hz (hH1 a a.2)
  exact Subtype.ext (C.cB_eq_one.1 hid)

theorem card_autOn_Lt
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V)) {t : G} (ht : t ∈ V)
    (h1 : C.cd ⟨t, ht⟩ = 1) :
    Nat.card ↥(autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))) V) = 60 := by
  classical
  set H := autOn (oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))) V with hHd
  have e : ↥H ≃ {B : B6 // B ∈ stab1} :=
    Equiv.ofBijective (fun a => ⟨C.cB a, (mem_autOn_Lt_iff h hC ht h1 a).1 a.2⟩)
      ⟨fun a b hab => Subtype.ext (C.cB_injective (congrArg Subtype.val hab)), fun B => by
        obtain ⟨a, ha⟩ := hC.2 B.1 (stab1_sub B.2).1
        exact ⟨⟨a, (mem_autOn_Lt_iff h hC ht h1 a).2 (ha ▸ B.2)⟩, Subtype.ext ha⟩⟩
  rw [Nat.card_congr e]
  have e2 : {B : B6 // B ∈ stab1} ≃ ↥stab1.toFinset := Equiv.subtypeEquivRight fun B => by simp
  rw [Nat.card_congr e2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup stab1_nodup,
    cert4_card_stab1]

theorem Lt_quot_equiv
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V}
    (hC : IdentL C (autOn L V)) {t : G} (ht : t ∈ V) (h1 : C.cd ⟨t, ht⟩ = 1) :
    Nonempty (↥(oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))) ⧸
        CFSG.pCore 2 ↥(oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G))) ≃*
      alternatingGroup (Fin 5)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Lt := oTwoUpper (L ⊓ Subgroup.centralizer ({t} : Set G)) with hLtd
  set H := autOn Lt V with hHd
  have hLtL : Lt ≤ L := (oTwoUpper_le' _).trans inf_le_left
  have hLtN : Lt ≤ Subgroup.normalizer (V : Set G) := hLtL.trans (L_le_normalizer h)
  have hHM : H ≤ h.hyp.MVbar := (A4.autOn_mono hLtL).trans (A4.autOn_mono (L_le_MV h))
  have hH1 : ∀ a ∈ H, (C.cB a).app 1 = 1 := fun a ha => by
    have := (mem_autOn_Lt_iff h hC ht h1 a).1 ha
    rw [stab1, List.mem_filter] at this
    simpa using this.2
  set e5 : OP5 ≃ Fin 5 := (Finite.equivFin OP5).trans (finCongr card_OP5) with he5
  set φ : ↥H →* Equiv.Perm (Fin 5) :=
    (Equiv.permCongrHom e5).toMonoidHom.comp (pi5 h hC hHM hH1) with hφ
  have hφinj : Function.Injective φ :=
    (Equiv.permCongrHom e5).injective.comp (pi5_injective h hC hHM hH1)
  have hrange : φ.range = alternatingGroup (Fin 5) := by
    apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
    have hc : Nat.card φ.range = 60 := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv, card_autOn_Lt h hC ht h1]
    have e := Subgroup.card_mul_index φ.range
    rw [hc, Nat.card_perm, Nat.card_fin] at e
    have h120 : Nat.factorial 5 = 120 := by decide
    omega
  set ψ : ↥Lt →* ↥(alternatingGroup (Fin 5)) :=
    (MulEquiv.subgroupCongr hrange).toMonoidHom.comp (φ.rangeRestrict.comp (autOnSurj hLtN))
    with hψ
  have hψsurj : Function.Surjective ψ :=
    (MulEquiv.subgroupCongr hrange).surjective.comp
      (φ.rangeRestrict_surjective.comp (autOnSurj_surjective hLtN))
  have hψker : ψ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf Lt := by
    rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.subgroupCongr hrange).injective,
      MonoidHom.ker_comp_of_injective _ _ (by
        intro a b hab
        exact hφinj (congrArg Subtype.val hab)), ker_autOnSurj]
  have hkerP : CFSG.pCore 2 ↥Lt = ψ.ker := by
    apply le_antisymm
    · have hN : ((CFSG.pCore 2 ↥Lt).map ψ).Normal :=
        (CFSG.pCore_normal (p := 2) (G := ↥Lt)).map ψ hψsurj
      have hP : IsPGroup 2 ((CFSG.pCore 2 ↥Lt).map ψ) := (CFSG.pCore_isPGroup (p := 2)).map ψ
      have hs : IsSimpleGroup ↥(alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup
        (by simp)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 ↥Lt).map ψ) with hb | ht'
      · intro x hx
        have : ψ x ∈ (CFSG.pCore 2 ↥Lt).map ψ := ⟨x, hx, rfl⟩
        rw [hb] at this
        exact this
      · exfalso
        rw [ht'] at hP
        obtain ⟨n, hn⟩ := IsPGroup.iff_card.1 hP
        rw [Subgroup.card_top, nat_card_alternatingGroup, Nat.card_fin] at hn
        have h60 : Nat.factorial 5 / 2 = 60 := by decide
        rw [h60] at hn
        have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 60)
        exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by decide)
    · rw [hψker]
      apply le_sSup
      refine ⟨?_, ?_⟩
      · rw [← hψker]
        exact MonoidHom.normal_ker ψ
      · have h2 := isPGroup_inf_centralizer h1222 h (K := Lt) hLtL
        intro x
        obtain ⟨k, hk⟩ := h2 ⟨((x : ↥Lt) : G), (x : ↥Lt).2, x.2⟩
        refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
        have := congrArg Subtype.val hk
        simpa using this
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerP).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj)⟩

end CFSG.Quasithin.H13.S127.Mod

end
