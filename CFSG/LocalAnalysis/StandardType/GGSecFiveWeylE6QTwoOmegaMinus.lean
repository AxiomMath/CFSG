module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSInputs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaTorus
import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoUnitaryAux
import CFSG.LocalAnalysis.StandardType.GGHalfRowData
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.SixLieOutOrth
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoInnerQAux

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open FrameRoute

variable {G : Type} [Group G] [Finite G]

theorem E6QTwo.omegaMinusFive_of_marking
    {L : Subgroup G}
    (hlab : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 5 ∧ lab.n = 1)) :
    commutator ↥L = ⊤ ∧ Subgroup.center ↥L = ⊥ ∧ StatedClassicalModel ↥L .POmegaMinus 5 2 1 := by
  obtain ⟨hperf, lab, -, hraw⟩ := hlab
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨R₀, _, I₀, F₀, -, -, -, hlabS, hlabS'⟩ := largeEvenRawDatum_exists hraw
  obtain rfl := hlabS
  obtain ⟨rfl, rfl⟩ := hlabS'
  dsimp only [LargeEvenRawDatumLegacy, LargeEvenRecipeOmegaMinus] at hraw
  obtain ⟨K, hF, hfin, hK, bf, cf, hbc, hq⟩ := hraw
  letI : Field K := hF
  letI : Finite K := hfin
  obtain ⟨-, -, θ, hP, -⟩ := hq
  have hModelQuot : StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .POmegaMinus 5 2 1 :=
    statedClassicalModel_of_mulEquiv' θ.symm
      (statedClassicalModel_omegaMinus 5 1 hK bf cf hbc ⟨Nat.prime_two, le_rfl, by norm_num⟩)
  haveI : Group.IsPerfect ↥L := ⟨hperf⟩
  have hZ : Subgroup.center ↥L = ⊥ := HalfRowData.center_eq_bot_of_pomegaMinus_two hModelQuot
  have e : ↥L ⧸ Subgroup.center ↥L ≃* ↥L :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  exact ⟨hperf, hZ, statedClassicalModel_of_mulEquiv' e hModelQuot⟩

theorem GGSecFiveRestHyp.normal_of_twD5
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hlab : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 5 ∧ lab.n = 1)) :
    (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal := by
  have hS : LargeEvenSStar 3 B x L := hR.1.1.2.2.2.2.2.2.1
  have hModel : StatedClassicalModel ↥L .POmegaMinus 5 2 1 :=
    (E6QTwo.omegaMinusFive_of_marking hlab).2.2
  have hnc : ∃ S : Subgroup G, S ≤ L ∧ IsPGroup 3 S ∧ ¬ IsCyclic S := by
    obtain ⟨T, -, hT, hTcard⟩ := E6QTwo.exists_le_elemAbelian_card_of_pomegaMinus_five hModel
      (E := ⊥) (by
        constructor
        · exact IsMulCommutative.of_comm fun (a b : ↥(⊥ : Subgroup ↥L)) =>
            by rw [Subsingleton.elim a b]
        · intro x hx
          simp at hx
          simp [hx])
    have hTnc : ¬ IsCyclic ↥T := by
      intro hcyc
      haveI := hcyc
      have hdvd : Monoid.exponent ↥T ∣ 3 :=
        Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (hT.2 (↑g) g.2)
      rw [IsCyclic.exponent_eq_card, hTcard] at hdvd
      have hle : 3 ^ 5 ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
      norm_num at hle
    have hTmap : IsElemAbelian 3 (T.map L.subtype) := by
      constructor
      · haveI : IsMulCommutative ↥T := hT.1
        infer_instance
      · intro x hx
        obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
        simpa using congrArg (fun y : ↥L => (y : G)) (hT.2 t ht)
    refine ⟨T.map L.subtype, Subgroup.map_subtype_le T, CFSG.Open.IsElemAbelian.isPGroup hTmap, ?_⟩
    intro hcyc
    haveI : IsCyclic (T.map L.subtype) := hcyc
    exact hTnc (isCyclic_of_injective
      (Subgroup.equivMapOfInjective T L.subtype (Subgroup.subtype_injective L)).toMonoidHom
      (Subgroup.equivMapOfInjective T L.subtype (Subgroup.subtype_injective L)).injective)
  refine ⟨fun n hn g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  exact (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_sstar hS hnc g.2) n).mp hn

theorem GGSecFiveRestHyp.bstar_eq_sup_of_twD5
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hlab : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 5 ∧ lab.n = 1)) :
    x ∉ L ∧ Bs = Subgroup.zpowers x ⊔ (Bs ⊓ L) := by
  have hS : LargeEvenSStar 3 B x L := hR.1.1.2.2.2.2.2.2.1
  obtain ⟨-, hBs, hxB, hLx, -⟩ := hR.1.tableB_facts
  have hx1 : x ≠ 1 := hS.2.2.1
  have horderx : orderOf x = 3 := orderOf_eq_prime (hBs.2 x hxB) hx1
  have hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hR.1.2.1.2.2.2
  have hcyc : ∀ S : Subgroup G, IsPGroup 3 S → S ≤ Subgroup.centralizer (L : Set G) →
      IsCyclic S := fun S hSp hSL => hS.2.2.2.2 S hSL hSp
  have hZ := (E6QTwo.omegaMinusFive_of_marking hlab).2.1
  have hModel := (E6QTwo.omegaMinusFive_of_marking hlab).2.2
  have hZ2 : IsPGroup 2 (Subgroup.center ↥L) := by
    rw [hZ]
    exact IsPGroup.of_bot
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLx hl)
  have hxL : x ∉ L := E6QTwo.not_mem_of_isPGroup_two_center hZ2 horderx hxC
  refine ⟨hxL, ?_⟩
  have hBL : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian Nat.prime_three hBs hxB hx1 hLx
      (fun S hSL hSp => hcyc S hSp hSL)
  have hBsCx : Bs ≤ Subgroup.centralizer ({x} : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hBs.1.is_comm.comm ⟨b, hb⟩ ⟨x, hxB⟩)
  have hN : (L.subgroupOf (Subgroup.centralizer ({x} : Set G))).Normal :=
    GGSecFiveRestHyp.normal_of_twD5 hR hlab
  have hNle : Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLx).mp hN
  have hNL : Bs ≤ Subgroup.normalizer (L : Set G) := hBsCx.trans hNle
  have hAut := CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.autThreePowInner_pomegaMinus_two
    (by norm_num : 4 ≤ 5) hModel
  have hmem : ∀ b ∈ Bs, b ∈ Subgroup.zpowers x ⊔ (Bs ⊓ L) := by
    intro b hb
    let ψ := E6QTwo.e6QTwoBstarConjAction hNL ⟨b, hb⟩
    have hψ3 : ψ ^ 3 = 1 := by
      rw [← map_pow]
      have hb3 : (⟨b, hb⟩ : ↥Bs) ^ 3 = 1 := by
        ext
        exact hBs.2 b hb
      rw [hb3]
      simp
    obtain ⟨a, ha⟩ := hAut ψ 1 (by
      intro y
      rw [pow_one]
      have hiter : ψ^[3] y = (ψ ^ 3) y := rfl
      rw [hiter, hψ3]
      simp)
    have hψ_eq : ψ = MulAut.conj a := by
      ext y
      rw [ha y, MulAut.conj_apply]
    have hinj : Function.Injective (MulAut.conj : ↥L → MulAut ↥L) := by
      intro x y hxy
      have h : y⁻¹ * x ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro z
        have h1 := congrArg (fun f : MulAut ↥L => f z) hxy
        rw [MulAut.conj_apply, MulAut.conj_apply] at h1
        calc z * (y⁻¹ * x) = y⁻¹ * (y * z * y⁻¹) * x := by group
          _ = y⁻¹ * (x * z * x⁻¹) * x := by rw [← h1]
          _ = (y⁻¹ * x) * z := by group
      rw [hZ] at h
      rw [Subgroup.mem_bot] at h
      calc x = y * (y⁻¹ * x) := by group
        _ = y * 1 := by rw [h]
        _ = y := by group
    have haC : (a : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      let ψ_s := E6QTwo.e6QTwoBstarConjAction hNL ⟨s, hs⟩
      have hcomm : ψ * ψ_s = ψ_s * ψ := by
        rw [← map_mul, ← map_mul]
        congr 1
        exact hBs.1.is_comm.comm ⟨b, hb⟩ ⟨s, hs⟩
      have hcomm2 : MulAut.conj a * ψ_s = ψ_s * MulAut.conj a := by
        rw [← hψ_eq]
        exact hcomm
      have hconj_ψs : ψ_s * MulAut.conj a * ψ_s⁻¹ = MulAut.conj a := by
        rw [← hcomm2]
        group
      have hψs_a : ψ_s a = a := by
        have h_eq : ψ_s * MulAut.conj a * ψ_s⁻¹ = MulAut.conj (ψ_s a) := by
          ext x
          simp only [MulAut.mul_apply, MulAut.conj_apply]
          rw [map_mul, map_mul, map_inv]
          simp
        rw [h_eq] at hconj_ψs
        exact hinj hconj_ψs
      have h2 : ((ψ_s a : ↥L) : G) = s * (a : G) * s⁻¹ := by
        rw [E6QTwo.e6QTwoBstarConjAction_apply]
      have h1 : ((ψ_s a : ↥L) : G) = (a : G) := congrArg Subtype.val hψs_a
      rw [h2] at h1
      calc s * (a : G) = (s * (a : G) * s⁻¹) * s := by group
        _ = (a : G) * s := by rw [h1]
    have ha3 : (a : G) ^ 3 = 1 := by
      have h1 : MulAut.conj (a ^ 3) = 1 := by
        rw [map_pow, ← hψ_eq, hψ3]
      have h2 : a ^ 3 ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro z
        have h3 := congrArg (fun f : MulAut ↥L => f z) h1
        rw [MulAut.conj_apply, MulAut.one_apply] at h3
        calc z * a ^ 3 = (a ^ 3 * z * (a ^ 3)⁻¹) * a ^ 3 := by rw [h3]
          _ = a ^ 3 * z := by group
      rw [hZ] at h2
      rw [Subgroup.mem_bot] at h2
      exact congrArg Subtype.val h2
    have haBs : (a : G) ∈ Bs := hstar (a : G) haC ha3
    have hbma_mem : b * (a : G)⁻¹ ∈ Bs := Bs.mul_mem hb (Bs.inv_mem haBs)
    have hbma_cent : b * (a : G)⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
      have h_eq : (⟨b * (a : G)⁻¹, hbma_mem⟩ : ↥Bs) =
          ⟨b, hb⟩ * (⟨(a : G), haBs⟩ : ↥Bs)⁻¹ := by
        ext
        simp
      have hψ_a : E6QTwo.e6QTwoBstarConjAction hNL ⟨(a : G), haBs⟩ = MulAut.conj a := by
        ext x
        rw [E6QTwo.e6QTwoBstarConjAction_apply, MulAut.conj_apply]
        rfl
      have hψ_ba : E6QTwo.e6QTwoBstarConjAction hNL ⟨b * (a : G)⁻¹, hbma_mem⟩ = 1 := by
        rw [h_eq, map_mul, map_inv, hψ_a]
        change ψ * (MulAut.conj a)⁻¹ = 1
        rw [hψ_eq]
        simp
      exact (E6QTwo.e6QTwoBstarConjAction_eq_one_iff hNL ⟨b * (a : G)⁻¹, hbma_mem⟩).mp hψ_ba
    have hbma_zp : b * (a : G)⁻¹ ∈ Subgroup.zpowers x := by
      rw [← hBL]
      exact Subgroup.mem_inf.mpr ⟨hbma_mem, hbma_cent⟩
    have ha_inf : (a : G) ∈ Bs ⊓ L := Subgroup.mem_inf.mpr ⟨haBs, a.2⟩
    have hb_eq2 : b = (a : G) * (b * (a : G)⁻¹) := by
      calc b = b * (a : G) * (a : G)⁻¹ := by group
        _ = (a : G) * b * (a : G)⁻¹ := by rw [← haC b hb]
        _ = (a : G) * (b * (a : G)⁻¹) := by group
    rw [hb_eq2]
    exact (Subgroup.zpowers x ⊔ (Bs ⊓ L)).mul_mem
      (Subgroup.mem_sup_right ha_inf)
      (Subgroup.mem_sup_left hbma_zp)
  have hle1 : Bs ≤ Subgroup.zpowers x ⊔ (Bs ⊓ L) := fun b hb => hmem b hb
  have hle2 : Subgroup.zpowers x ⊔ (Bs ⊓ L) ≤ Bs := by
    apply sup_le
    · exact Subgroup.zpowers_le.mpr hxB
    · exact inf_le_left
  exact le_antisymm hle1 hle2

theorem GGSecFiveRestHyp.card_bstar_inf_of_twD5
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hR : GGSecFiveRestHyp 3 B Bs x L D J)
    (hlab : LargeEvenMarking L (fun lab _ _ _ _ _ => lab.tag = .twD ∧ lab.rank = 5 ∧ lab.n = 1)) :
    Nat.card ↥(Bs ⊓ L) = 3 ^ 5 := by
  have hS : LargeEvenSStar 3 B x L := hR.1.1.2.2.2.2.2.2.1
  obtain ⟨-, hBs, hxB, hLx, -⟩ := hR.1.tableB_facts
  have hx1 : x ≠ 1 := hS.2.2.1
  have horderx : orderOf x = 3 := orderOf_eq_prime (hBs.2 x hxB) hx1
  have hstar : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hR.1.2.1.2.2.2
  have hcyc : ∀ S : Subgroup G, IsPGroup 3 S → S ≤ Subgroup.centralizer (L : Set G) →
      IsCyclic S := fun S hSp hSL => hS.2.2.2.2 S hSL hSp
  have hModel := (E6QTwo.omegaMinusFive_of_marking hlab).2.2
  have hE : IsElemAbelian 3 ((Bs ⊓ L).subgroupOf L) := by
    rw [Subgroup.inf_subgroupOf_right]
    exact hBs.subgroupOf L
  obtain ⟨T, hTle, hTEA, hTcard⟩ :=
    E6QTwo.exists_le_elemAbelian_card_of_pomegaMinus_five hModel hE
  let T' := T.map L.subtype
  have hT'le : T' ≤ L := by
    intro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨t, ht, rfl⟩ := hg
    exact t.2
  have hT'card : Nat.card T' = 3 ^ 5 := by
    change Nat.card (T.map L.subtype) = 3 ^ 5
    rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective L)]
    exact hTcard
  have hT'EA : IsElemAbelian 3 T' := hTEA.map L.subtype
  have hT'C : T' ≤ Subgroup.centralizer (Bs : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hsup : Bs = Subgroup.zpowers x ⊔ (Bs ⊓ L) :=
      (GGSecFiveRestHyp.bstar_eq_sup_of_twD5 hR hlab).2
    have hb' : b ∈ Subgroup.zpowers x ⊔ (Bs ⊓ L) := by rw [← hsup]; exact hb
    have hb_closure : b ∈ Subgroup.closure (((Subgroup.zpowers x : Subgroup G) : Set G) ∪
        ((Bs ⊓ L : Subgroup G) : Set G)) := by
      rw [← Subgroup.sup_eq_closure]
      exact hb'
    have h_comm_closure :
        ∀ y ∈ Subgroup.closure ((Subgroup.zpowers x : Set G) ∪ (Bs ⊓ L : Set G)),
          t * y = y * t := by
      intro y hy
      refine Subgroup.closure_induction_left (p := fun z _ => t * z = z * t) ?_ ?_ ?_ hy
      · rw [mul_one, one_mul]
      · intro u hu v hv ih
        have hu_comm : t * u = u * t := by
          rcases hu with hu | hu
          ·
            have hxt : t * x = x * t := by
              have h : t ∈ Subgroup.centralizer ({x} : Set G) := hLx (hT'le ht)
              exact Subgroup.mem_centralizer_singleton_iff.mp h
            have hx_cent : x ∈ Subgroup.centralizer ({t} : Set G) := by
              rw [Subgroup.mem_centralizer_singleton_iff]
              exact hxt.symm
            have hu_cent : u ∈ Subgroup.centralizer ({t} : Set G) :=
              Subgroup.zpowers_le.mpr hx_cent hu
            have h := Subgroup.mem_centralizer_singleton_iff.mp hu_cent
            exact h.symm
          ·
            have hu' : u ∈ T' := by
              have huL : u ∈ L := (Subgroup.mem_inf.mp hu).2
              have hu'' : (⟨u, huL⟩ : ↥L) ∈ (Bs ⊓ L).subgroupOf L := by
                rw [Subgroup.mem_subgroupOf]
                exact hu
              have hTle' := hTle hu''
              exact Subgroup.mem_map.mpr ⟨⟨u, huL⟩, hTle', rfl⟩
            have hcomm := hT'EA.1.is_comm.comm ⟨u, hu'⟩ ⟨t, ht⟩
            exact congrArg Subtype.val hcomm |>.symm
        calc t * (u * v) = (t * u) * v := by rw [mul_assoc]
          _ = (u * t) * v := by rw [hu_comm]
          _ = u * (t * v) := by rw [mul_assoc]
          _ = u * (v * t) := by rw [ih]
          _ = (u * v) * t := by rw [mul_assoc]
      · intro u hu v hv ih
        have hu_comm : t * u = u * t := by
          rcases hu with hu | hu
          ·
            have hxt : t * x = x * t := by
              have h : t ∈ Subgroup.centralizer ({x} : Set G) := hLx (hT'le ht)
              exact Subgroup.mem_centralizer_singleton_iff.mp h
            have hx_cent : x ∈ Subgroup.centralizer ({t} : Set G) := by
              rw [Subgroup.mem_centralizer_singleton_iff]
              exact hxt.symm
            have hu_cent : u ∈ Subgroup.centralizer ({t} : Set G) :=
              Subgroup.zpowers_le.mpr hx_cent hu
            have h := Subgroup.mem_centralizer_singleton_iff.mp hu_cent
            exact h.symm
          ·
            have hu' : u ∈ T' := by
              have huL : u ∈ L := (Subgroup.mem_inf.mp hu).2
              have hu'' : (⟨u, huL⟩ : ↥L) ∈ (Bs ⊓ L).subgroupOf L := by
                rw [Subgroup.mem_subgroupOf]
                exact hu
              have hTle' := hTle hu''
              exact Subgroup.mem_map.mpr ⟨⟨u, huL⟩, hTle', rfl⟩
            have hcomm := hT'EA.1.is_comm.comm ⟨u, hu'⟩ ⟨t, ht⟩
            exact congrArg Subtype.val hcomm |>.symm
        have hu_inv_comm : t * u⁻¹ = u⁻¹ * t := by
          calc t * u⁻¹ = u⁻¹ * (u * t) * u⁻¹ := by group
            _ = u⁻¹ * (t * u) * u⁻¹ := by rw [hu_comm]
            _ = u⁻¹ * t := by group
        calc t * (u⁻¹ * v) = (t * u⁻¹) * v := by rw [mul_assoc]
          _ = (u⁻¹ * t) * v := by rw [hu_inv_comm]
          _ = u⁻¹ * (t * v) := by rw [mul_assoc]
          _ = u⁻¹ * (v * t) := by rw [ih]
          _ = (u⁻¹ * v) * t := by rw [mul_assoc]
    exact (h_comm_closure b hb_closure).symm
  have hT'Bs : T' ≤ Bs := by
    intro t ht
    exact hstar t (hT'C ht) (hT'EA.2 t ht)
  have hT'inf : T' ≤ Bs ⊓ L := by
    intro t ht
    exact Subgroup.mem_inf.mpr ⟨hT'Bs ht, hT'le ht⟩
  have hinf_le_T' : Bs ⊓ L ≤ T' := by
    intro g hg
    have hgBs : g ∈ Bs := (Subgroup.mem_inf.mp hg).1
    have hgL : g ∈ L := (Subgroup.mem_inf.mp hg).2
    have hg' : (⟨g, hgL⟩ : ↥L) ∈ (Bs ⊓ L).subgroupOf L := by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_inf.mpr ⟨hgBs, hgL⟩
    have hTle' := hTle hg'
    exact Subgroup.mem_map.mpr ⟨⟨g, hgL⟩, hTle', rfl⟩
  have heq : T' = Bs ⊓ L := le_antisymm hT'inf hinf_le_T'
  rw [← heq]
  exact hT'card

end CFSG.StandardType

end
