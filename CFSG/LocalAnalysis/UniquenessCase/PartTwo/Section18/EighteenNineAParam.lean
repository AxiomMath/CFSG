module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.L2SzAutRank
public import CFSG.Quasithin.Background.RonanE42SetS2
public import CFSG.Quasithin.Vol2.Ch10SecC9S5d
public import CFSG.Quasithin.Background.C126A5ExtractFam
public import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22g
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveOTwoBar
public import TauCeti.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18

open CFSG.Open Subgroup CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem aParam_autI_le_of_fixFree (hKL2 : Inputs1719.K_L2SzAutRank) {V T J X₁ U : Subgroup G}
    (hU : IsElemAbelian 2 U)
    (hUdef : U = CFSG.Quasithin.conjClosure (V ⊓ centralizer (T : Set G)) X₁)
    (hT : IsSylowIn 2 T X₁) (hJX : J ≤ X₁) (hXJ : X₁ ≤ normalizer (J : Set G))
    (hX₁ : X₁ = T ⊔ J) (hXU : X₁ ≤ normalizer (U : Set G))
    (hJC : J ⊓ centralizer (U : Set G) = pCoreOf 2 J)
    (hKT : X₁ ⊓ centralizer (U : Set G) ≤ T) {m : ℕ}
    (hL2 : IsL2 (Bar2 J) m) : E3.aParam (autI hU X₁) ≤ m := by
  classical
  have hJN : J ≤ Subgroup.normalizer (U : Set G) := hJX.trans hXU
  have hTN : T ≤ Subgroup.normalizer (U : Set G) := hT.le.trans hXU
  have hJA : autI hU J ≤ autI hU X₁ := autI_mono hU hJX
  have hTA : autI hU T ≤ autI hU X₁ := autI_mono hU hT.le
  set A : Subgroup (MulAut (IntMod U hU)) := autI hU X₁ with hA
  set L : Subgroup ↥A := (autI hU J).subgroupOf A with hL
  have hLnorm : L.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJA).mpr
      (CFSG.Quasithin.C126.A5.autI_le_normalizer_autI hU hXJ)
  obtain ⟨e₂⟩ := CFSG.Quasithin.Vol2.Ch10.SecC.nonempty_quotient_equiv (V := U) (J := J)
    hU hJN hJC (MulEquiv.refl ↥(autI hU J))
  have h2a : IsL2 ↥(autI hU J) m := CFSG.Blueprint.LieModel.of_mulEquiv e₂ hL2
  have h2L : IsL2 ↥L m :=
    CFSG.Blueprint.LieModel.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJA).symm h2a
  have hsimple : IsSimpleGroup ↥L :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h2L
  have hntriv : Nontrivial ↥L := hsimple.toNontrivial
  have hnab : ¬ IsMulCommutative ↥L := by
    intro hc
    have htop : Subgroup.center ↥L = ⊤ := Subgroup.center_eq_top_iff.mpr hc
    rw [uc22p22g_center_bot h2L] at htop
    have hbot : (⊤ : Subgroup ↥L) = ⊥ := htop.symm
    obtain ⟨a, b, hab⟩ := hntriv.exists_pair_ne
    have ha : a = 1 := by
      have h : a ∈ (⊤ : Subgroup ↥L) := Subgroup.mem_top a
      rw [hbot] at h
      exact Subgroup.mem_bot.mp h
    have hb : b = 1 := by
      have h : b ∈ (⊤ : Subgroup ↥L) := Subgroup.mem_top b
      rw [hbot] at h
      exact Subgroup.mem_bot.mp h
    exact hab (ha.trans hb.symm)
  have hTstarP : IsPGroup 2 ↥(autI hU T) := by
    let g : ↥T →* ↥(autI hU T) :=
      (convHom hU T hTN).codRestrict _
        (fun t => convI_mem_autI hU t.2 (hTN t.2))
    have hsurj : Function.Surjective g := by
      intro x
      have hx : (x : MulAut (IntMod U hU)) ∈ (convHom hU T hTN).range := by
        rw [range_convHom hU T hTN]
        exact x.2
      obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp hx
      exact ⟨t, Subtype.ext ht⟩
    exact IsPGroup.of_surjective hT.isPGroup g hsurj
  have hTsubP : IsPGroup 2 ↥((autI hU T).subgroupOf A) :=
    hTstarP.of_equiv (Subgroup.subgroupOfEquivOfLe hTA).symm
  have hquot2 : IsPGroup 2 (↥A ⧸ L) := by
    have hsup : (autI hU T).subgroupOf A ⊔ L = ⊤ := by
      rw [hL, ← Subgroup.subgroupOf_sup hTA hJA, ← autI_sup hU hTN hJN, ← hX₁]
      exact Subgroup.subgroupOf_self A
    have hmapTop : ((autI hU T).subgroupOf A).map (QuotientGroup.mk' L) = ⊤ := by
      have h1 : ((autI hU T).subgroupOf A ⊔ L).map (QuotientGroup.mk' L) = ⊤ := by
        rw [hsup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective L)]
      rwa [Subgroup.map_sup, QuotientGroup.map_mk'_self, sup_bot_eq] at h1
    have h := IsPGroup.map hTsubP (QuotientGroup.mk' L)
    rw [hmapTop] at h
    exact h.of_equiv Subgroup.topEquiv
  let fA : ↥X₁ →* ↥A :=
    (convHom hU X₁ hXU).codRestrict A (fun x => convI_mem_autI hU x.2 (hXU x.2))
  have hfAker : fA.ker = (X₁ ⊓ Subgroup.centralizer (U : Set G)).subgroupOf X₁ := by
    ext r
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h2 : convHom hU X₁ hXU r = 1 := congrArg Subtype.val h
      rw [← MonoidHom.mem_ker, ker_convHom hU X₁ hXU, Subgroup.mem_subgroupOf] at h2
      exact h2
    · intro h
      have h2 : r ∈ (convHom hU X₁ hXU).ker := by
        rw [ker_convHom hU X₁ hXU, Subgroup.mem_subgroupOf]
        exact h
      exact Subtype.ext (MonoidHom.mem_ker.mp h2)
  have hfArange : fA.range = ⊤ := by
    rw [eq_top_iff]
    rintro x -
    have hx : (x : MulAut (IntMod U hU)) ∈ (convHom hU X₁ hXU).range := by
      rw [range_convHom hU X₁ hXU]
      exact x.2
    obtain ⟨r, hr⟩ := MonoidHom.mem_range.mp hx
    exact ⟨r, Subtype.ext hr⟩
  set Cc : Subgroup ↥A := Subgroup.centralizer (L : Set ↥A) with hCc
  have hCcP : IsPGroup 2 ↥Cc := by
    have hCL : Cc ⊓ L = ⊥ := by
      rw [eq_bot_iff]
      rintro x ⟨hxc, hxL⟩
      have hmem : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxc (y : ↥A) y.2)
      rw [uc22p22g_center_bot h2L] at hmem
      have h1 : (⟨x, hxL⟩ : ↥L) = 1 := Subgroup.mem_bot.mp hmem
      simpa using congrArg Subtype.val h1
    let ψ : ↥Cc →* ↥A ⧸ L := (QuotientGroup.mk' L).comp Cc.subtype
    have hψker : ψ.ker = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxL : (x : ↥A) ∈ L := by
        refine (QuotientGroup.eq_one_iff (x : ↥A)).mp ?_
        exact MonoidHom.mem_ker.mp hx
      have hmem : (x : ↥A) ∈ Cc ⊓ L := ⟨x.2, hxL⟩
      rw [hCL] at hmem
      exact Subtype.ext (Subgroup.mem_bot.mp hmem)
    exact IsPGroup.of_injective hquot2 ψ ((MonoidHom.ker_eq_bot_iff ψ).mp hψker)
  set R : Subgroup ↥X₁ := Cc.comap fA with hR
  have hRnorm : R.Normal := Subgroup.Normal.comap (H := Cc) Subgroup.normal_centralizer fA
  have hRP : IsPGroup 2 ↥R := by
    let fR : ↥R →* ↥Cc :=
      { toFun := fun r => ⟨fA (r : ↥X₁), r.2⟩
        map_one' := Subtype.ext (map_one fA)
        map_mul' := fun a b =>
          Subtype.ext (map_mul fA (a : ↥X₁) (b : ↥X₁)) }
    have hsurjR : Function.Surjective fR := by
      intro c
      have hc : (c : ↥A) ∈ fA.range := by
        rw [hfArange]
        exact Subgroup.mem_top c
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hc
      have hxR : x ∈ R := by
        show fA x ∈ Cc
        rw [hx]
        exact c.2
      exact ⟨⟨x, hxR⟩, Subtype.ext hx⟩
    have hkerR : fR.ker = (fA.ker).subgroupOf R := by
      ext r
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    have hQuotP : IsPGroup 2 (↥R ⧸ fR.ker) := hCcP.of_equiv
      (QuotientGroup.quotientKerEquivOfSurjective fR hsurjR).symm
    have hkerP : IsPGroup 2 ↥fR.ker := by
      have hmemT : ∀ x : ↥fR.ker, ((x : ↥R) : ↥X₁).val ∈ T := by
        intro x
        have h2 : (x : ↥R) ∈ (fA.ker).subgroupOf R := hkerR ▸ x.2
        have h1 : ((x : ↥R) : ↥X₁) ∈ fA.ker := Subgroup.mem_subgroupOf.mp h2
        rw [hfAker, Subgroup.mem_subgroupOf] at h1
        exact hKT h1
      let φ : ↥fR.ker →* ↥T :=
        { toFun := fun x => ⟨((x : ↥R) : ↥X₁).val, hmemT x⟩
          map_one' := Subtype.ext rfl
          map_mul' := fun a b => Subtype.ext rfl }
      have hinj : Function.Injective φ := by
        intro a b hab
        have h1 : (((a : ↥R) : ↥X₁) : G) = (((b : ↥R) : ↥X₁) : G) := by
          simpa [φ] using congrArg (fun t : ↥T => (t : G)) hab
        exact Subtype.ext (Subtype.ext (Subtype.ext h1))
      exact IsPGroup.of_injective hT.isPGroup φ hinj
    exact IsPGroup.of_subgroup_of_quotient hkerP hQuotP
  let Rg : Subgroup G := R.map X₁.subtype
  have hRgsub : Rg.subgroupOf X₁ = R := by
    ext y
    constructor
    · intro hy
      obtain ⟨r, hr, hry⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hy)
      have hry' : r = y := Subtype.ext hry
      rwa [← hry']
    · intro hy
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem X₁.subtype hy)
  have hRgC : Rg ≤ Subgroup.centralizer (U : Set G) := by
    have hRg2 : IsPGroup 2 Rg := hRP.map X₁.subtype
    obtain ⟨a, ha⟩ := hRg2.exists_card_eq
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
      (ha ▸ Subgroup.relIndex_dvd_card (Subgroup.centralizer (U : Set G)) Rg)
    rw [hUdef] at hk ⊢
    exact CFSG.LocalAnalysis.WeakClosure81.le_centralizer_conjClosure_of_two_pow_relIndex hT
      inf_le_right (Subgroup.map_subtype_le R) (by rw [hRgsub]; exact hRnorm) ⟨k, hk⟩
  have hRleKer : R ≤ fA.ker := by
    intro r hr
    rw [hfAker, Subgroup.mem_subgroupOf]
    exact ⟨r.2, hRgC (Subgroup.mem_map_of_mem X₁.subtype hr)⟩
  have hCcbot : Cc = ⊥ := by
    have hmap : Cc = R.map fA := by
      have h1 : (Cc.comap fA).map fA = Cc := by
        refine Subgroup.map_comap_eq_self ?_
        rw [hfArange]
        exact le_top
      rw [hR]
      exact h1.symm
    rw [hmap, eq_bot_iff]
    rintro y hy
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_bot]
    exact MonoidHom.mem_ker.mp (hRleKer hr)
  have hrank : CFSG.Open.pRank 2 (⊤ : Subgroup ↥A) ≤ m :=
    hKL2 ↥A L m hsimple hnab hCcbot hquot2 (Or.inl h2L)
  have h7 : E3.aParam A ≤ CFSG.Open.pRank 2 (⊤ : Subgroup ↥A) := by
    have h := CFSG.Quasithin.RonanE42.Gen.aParam_le_pRank (V := IntMod U hU) (G := ↥A)
      (ρ := A.subtype) A.subtype_injective
    simpa [Subgroup.range_subtype] using h
  exact h7.trans hrank

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18
