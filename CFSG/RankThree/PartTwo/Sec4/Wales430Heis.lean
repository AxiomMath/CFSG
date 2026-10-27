module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiOn
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec4.Proof430

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem false_of_isHeisCentral {A L : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (h27 : Nat.card A = 27)
    (hAmax : ∀ x : G, x ^ 3 = 1 → (∀ y ∈ A, x * y = y * x) → x ∈ A)
    (hLp : Group.IsPerfect L) {a c : G} (haA : a ∈ A) (hcA : c ∈ A)
    (hCA : A ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers a) (ha3 : orderOf a = 3)
    (hca : c ∉ Subgroup.zpowers a)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G))
    (hH : IsHeisCentral ↥(A ⊔ L) ↥L) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set X := A ⊔ L with hXdef
  have hXA : A ≤ X := le_sup_left
  have hXL : L ≤ X := le_sup_right
  obtain ⟨U, V, hsup, hUV, hU, -, h3⟩ := hH
  have hdec := KFacts.L34.exists_mul_eq_of_sup_eq_top hsup hUV
  set Z := U ⊓ V with hZdef
  have hZc : ∀ z ∈ Z, ∀ x : ↥X, z * x = x * z := by
    intro z hz x
    obtain ⟨u, hu, v, hv, rfl⟩ := hdec x
    have h1 : z * u = u * z := (hUV u hu z hz.2).symm
    have h2 : z * v = v * z := hUV z hz.1 v hv
    calc z * (u * v) = z * u * v := (mul_assoc _ _ _).symm
      _ = u * (z * v) := by rw [h1, mul_assoc]
      _ = u * v * z := by rw [h2, mul_assoc]
  have hU3 : ∀ u ∈ U, u ^ 3 = 1 := by
    intro u hu
    have h := Monoid.pow_exponent_eq_one (⟨u, hu⟩ : ↥U)
    rw [hU.2.2] at h
    simpa using congrArg Subtype.val h
  have hU3G : ∀ u ∈ U, ((u : G)) ^ 3 = 1 := fun u hu => by
    simpa using congrArg Subtype.val (hU3 u hu)
  have hZa : ∀ z ∈ Z, ((z : G)) ∈ Subgroup.zpowers a := by
    intro z hz
    rw [← hCA]
    refine ⟨hAmax _ (hU3G z hz.1) fun y hy => congrArg Subtype.val (hZc z hz ⟨y, hXA hy⟩),
      Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    exact (congrArg Subtype.val (hZc z hz ⟨l, hXL hl⟩)).symm
  have hZmap : Z.map X.subtype = Subgroup.zpowers a := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact hZa z hz
    · rw [Subgroup.card_map_of_injective X.subtype_injective, h3, Nat.card_zpowers, ha3]
  have haX : ∀ w ∈ Subgroup.zpowers a, ∀ x : ↥X, w * (x : G) = (x : G) * w := by
    intro w hw x
    rw [← hZmap] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    exact congrArg Subtype.val (hZc z hz x)
  have hZU : Z.subgroupOf U = Subgroup.center ↥U := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · intro w hw
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hUV (g : ↥X) g.2 (w : ↥X) (Subgroup.mem_subgroupOf.mp hw).2)
    · rw [hU.1.2.2.2, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : Z ≤ U)).toEquiv,
        h3]
  have hcomm : ∀ u ∈ U, ∀ u' ∈ U, u * u' * u⁻¹ * u'⁻¹ ∈ Z := by
    intro u hu u' hu'
    have hmem : ⁅(⟨u, hu⟩ : ↥U), (⟨u', hu'⟩ : ↥U)⁆ ∈ Subgroup.center ↥U := by
      rw [← hU.1.2.1]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [← hZU] at hmem
    simpa [commutatorElement_def] using Subgroup.mem_subgroupOf.mp hmem
  have hux : ∀ u ∈ U, ∀ x ∈ A, ((u : G)) * x * (u : G)⁻¹ * x⁻¹ ∈ Subgroup.zpowers a := by
    intro u hu x hx
    obtain ⟨u', hu', v', hv', hx'⟩ := hdec ⟨x, hXA hx⟩
    have h1 : v' * u⁻¹ = u⁻¹ * v' := (hUV u⁻¹ (U.inv_mem hu) v' hv').symm
    have key : u * (⟨x, hXA hx⟩ : ↥X) * u⁻¹ * (⟨x, hXA hx⟩ : ↥X)⁻¹ = u * u' * u⁻¹ * u'⁻¹ := by
      rw [← hx']
      calc u * (u' * v') * u⁻¹ * (u' * v')⁻¹ = u * u' * (v' * u⁻¹) * v'⁻¹ * u'⁻¹ := by group
        _ = u * u' * (u⁻¹ * v') * v'⁻¹ * u'⁻¹ := by rw [h1]
        _ = u * u' * u⁻¹ * u'⁻¹ := by group
    have h2 := hZa _ (hcomm u hu u' hu')
    rw [← key] at h2
    simpa using h2
  have hfwd : ∀ u ∈ U, ∀ x ∈ A, ((u : G)) * x * (u : G)⁻¹ ∈ A := by
    intro u hu x hx
    have h1 := hux u hu x hx
    have h2 : (u : G) * x * (u : G)⁻¹ = ((u : G) * x * (u : G)⁻¹ * x⁻¹) * x := by group
    rw [h2]
    exact A.mul_mem (Subgroup.zpowers_le.mpr haA h1) hx
  have hUN : ∀ u ∈ U, ((u : G)) ∈ Subgroup.normalizer (A : Set G) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hfwd u hu x, fun h => ?_⟩
    have h1 := hfwd u⁻¹ (U.inv_mem hu) _ h
    have h2 : ((u⁻¹ : ↥X) : G) * ((u : G) * x * (u : G)⁻¹) * ((u⁻¹ : ↥X) : G)⁻¹ = x := by
      simp only [InvMemClass.coe_inv, inv_inv]
      group
    rwa [h2] at h1
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  have huc : ∀ u ∈ U, ((u : G)) * c = c * u := by
    intro u hu
    have h1 : (u : G) * c * (u : G)⁻¹ ∈ Subgroup.zpowers c :=
      (Subgroup.mem_normalizer_iff.mp (hW (hUN u hu)) c).mp (Subgroup.mem_zpowers c)
    have h3' : (u : G) * c * (u : G)⁻¹ * c⁻¹ ∈ Subgroup.zpowers c :=
      Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ (Subgroup.mem_zpowers c))
    have h4 : (u : G) * c * (u : G)⁻¹ * c⁻¹ ∈ Subgroup.zpowers c ⊓ Subgroup.zpowers a :=
      ⟨h3', hux u hu c hcA⟩
    rw [Sec13.zpowers_inf_eq_bot hc3 hca, Subgroup.mem_bot] at h4
    calc (u : G) * c = ((u : G) * c * (u : G)⁻¹ * c⁻¹) * c * u := by group
      _ = c * u := by rw [h4, one_mul]
  have hXX : ∀ x x' : ↥X, x * x' * x⁻¹ * x'⁻¹ ∈ V := by
    intro x x'
    obtain ⟨u, hu, v, hv, rfl⟩ := hdec x
    obtain ⟨u', hu', v', hv', rfl⟩ := hdec x'
    have e1 : v * u' = u' * v := (hUV u' hu' v hv).symm
    have e2 : v * v' * v⁻¹ * u⁻¹ = u⁻¹ * (v * v' * v⁻¹) :=
      (hUV u⁻¹ (U.inv_mem hu) _ (V.mul_mem (V.mul_mem hv hv') (V.inv_mem hv))).symm
    have e3 : v * v' * v⁻¹ * v'⁻¹ * u'⁻¹ = u'⁻¹ * (v * v' * v⁻¹ * v'⁻¹) :=
      (hUV u'⁻¹ (U.inv_mem hu') _ (V.mul_mem (V.mul_mem (V.mul_mem hv hv') (V.inv_mem hv))
        (V.inv_mem hv'))).symm
    have key : u * v * (u' * v') * (u * v)⁻¹ * (u' * v')⁻¹ =
        (u * u' * u⁻¹ * u'⁻¹) * (v * v' * v⁻¹ * v'⁻¹) := by
      calc u * v * (u' * v') * (u * v)⁻¹ * (u' * v')⁻¹
          = u * (v * u') * v' * v⁻¹ * u⁻¹ * v'⁻¹ * u'⁻¹ := by group
        _ = u * u' * (v * v' * v⁻¹ * u⁻¹) * v'⁻¹ * u'⁻¹ := by rw [e1]; group
        _ = u * u' * u⁻¹ * (v * v' * v⁻¹ * v'⁻¹ * u'⁻¹) := by rw [e2]; group
        _ = (u * u' * u⁻¹ * u'⁻¹) * (v * v' * v⁻¹ * v'⁻¹) := by rw [e3]; group
    rw [key]
    exact V.mul_mem (hcomm u hu u' hu').2
      (V.mul_mem (V.mul_mem (V.mul_mem hv hv') (V.inv_mem hv)) (V.inv_mem hv'))
  have hLV : L ≤ V.map X.subtype := by
    have hperf : ⁅L, L⁆ = L := by
      rw [← Subgroup.map_subtype_commutator, hLp.commutator_eq_top, Subgroup.map_top,
        Subgroup.range_subtype]
    rw [← hperf, Subgroup.commutator_le]
    intro g hg h hh
    refine ⟨(⟨g, hXL hg⟩ : ↥X) * ⟨h, hXL hh⟩ * (⟨g, hXL hg⟩ : ↥X)⁻¹ * (⟨h, hXL hh⟩ : ↥X)⁻¹,
      hXX _ _, ?_⟩
    simp [commutatorElement_def]
  set D := Subgroup.zpowers c ⊔ Subgroup.zpowers a with hD
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha3
    omega
  have hc1 : c ≠ 1 := fun h => hca (h ▸ Subgroup.one_mem _)
  have hcomm' : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hDA : D ≤ A := sup_le (Subgroup.zpowers_le.mpr hcA) (Subgroup.zpowers_le.mpr haA)
  have hD9 : Nat.card D = 9 := by
    have hcommD : ∀ u ∈ Subgroup.zpowers c, ∀ v ∈ Subgroup.zpowers a, u * v = v * u :=
      fun u hu v hv => hcomm' u (Subgroup.zpowers_le.mpr hcA hu) v
        (Subgroup.zpowers_le.mpr haA hv)
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcommD
    rw [Sec13.zpowers_inf_eq_bot hc3 hca, Subgroup.card_bot, mul_one,
      Sec13.card_zpowers_of_pow_three hc3 hc1,
      Sec13.card_zpowers_of_pow_three (hA.2 a haA) ha1] at hcard
    exact hcard
  obtain ⟨y, hyA, hyD⟩ : ∃ y ∈ A, y ∉ D := by
    by_contra hcon
    push Not at hcon
    have := Subgroup.card_le_of_le (show A ≤ D from hcon)
    omega
  have hAy : A = Subgroup.zpowers y ⊔ D :=
    (Sec12.eq_of_card_nine_lt h27 (sup_le (Subgroup.zpowers_le.mpr hyA) hDA) le_sup_right hD9
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers y)) hyD).symm
  let f : ↥U →* ↥(Subgroup.zpowers a) :=
    { toFun := fun u => ⟨((u : ↥X) : G) * y * ((u : ↥X) : G)⁻¹ * y⁻¹, hux u u.2 y hyA⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro u₁ u₂
        apply Subtype.ext
        have hz := hux u₂ u₂.2 y hyA
        have hcz := haX _ hz (u₁ : ↥X)
        simp only [Subgroup.coe_mul, MulMemClass.coe_mul, mul_inv_rev]
        calc (u₁ : G) * u₂ * y * ((u₂ : G)⁻¹ * (u₁ : G)⁻¹) * y⁻¹
            = (u₁ : G) * ((u₂ : G) * y * (u₂ : G)⁻¹ * y⁻¹) * (y * (u₁ : G)⁻¹ * y⁻¹) := by
              group
          _ = ((u₂ : G) * y * (u₂ : G)⁻¹ * y⁻¹) * (u₁ : G) * (y * (u₁ : G)⁻¹ * y⁻¹) := by
              rw [← hcz]
          _ = ((u₁ : G) * y * (u₁ : G)⁻¹ * y⁻¹) * ((u₂ : G) * y * (u₂ : G)⁻¹ * y⁻¹) := by
              have hc2 := haX _ hz ((u₁ : ↥X) * ⟨y, hXA hyA⟩ * (u₁ : ↥X)⁻¹ * ⟨y, hXA hyA⟩⁻¹)
              simp only [Subgroup.coe_mul, InvMemClass.coe_inv] at hc2
              calc ((u₂ : G) * y * (u₂ : G)⁻¹ * y⁻¹) * (u₁ : G) * (y * (u₁ : G)⁻¹ * y⁻¹)
                  = ((u₂ : G) * y * (u₂ : G)⁻¹ * y⁻¹) * ((u₁ : G) * y * (u₁ : G)⁻¹ * y⁻¹) := by
                    group
                _ = _ := hc2 }
  have hker : 9 ≤ Nat.card f.ker := by
    have hcardU : Nat.card ↥U = 27 := hU.2.1
    have hrange : Nat.card f.range ≤ 3 := by
      calc Nat.card f.range ≤ Nat.card ↥(Subgroup.zpowers a) := Subgroup.card_le_card_group _
        _ = 3 := by rw [Nat.card_zpowers, ha3]
    have hiso := Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
    have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
    rw [hiso, hcardU] at hlag
    nlinarith [Nat.card_pos (α := ↥f.ker), Nat.card_pos (α := ↥f.range)]
  obtain ⟨u, huker, huZ⟩ : ∃ u ∈ f.ker, u ∉ Z.subgroupOf U := by
    by_contra hcon
    push Not at hcon
    have hle := Subgroup.card_le_of_le (show f.ker ≤ Z.subgroupOf U from hcon)
    rw [hZU, hU.1.2.2.2] at hle
    omega
  have huy : ((u : ↥X) : G) * y = y * u := by
    have h := congrArg Subtype.val (f.mem_ker.mp huker)
    simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, OneMemClass.coe_one] at h
    calc ((u : ↥X) : G) * y = ((u : G) * y * (u : G)⁻¹ * y⁻¹) * y * u := by group
      _ = y * u := by rw [h, one_mul]
  have hua : ((u : ↥X) : G) * a = a * u :=
    (haX a (Subgroup.mem_zpowers a) (u : ↥X)).symm
  have hAC : A ≤ Subgroup.centralizer ({((u : ↥X) : G)} : Set G) := by
    rw [hAy]
    refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr huy.symm))
      ?_
    rw [hD]
    exact sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      (huc u u.2).symm)) (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
      hua.symm))
  have huA : ∀ x ∈ A, ((u : ↥X) : G) * x = x * u := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hAC hx)).symm
  have huAm : ((u : ↥X) : G) ∈ A := hAmax _ (hU3G u u.2) huA
  have huL : ((u : ↥X) : G) ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    obtain ⟨v, hv, hvl⟩ := hLV hl
    rw [← hvl]
    exact (congrArg Subtype.val (hUV (u : ↥X) u.2 v hv)).symm
  have hua' : ((u : ↥X) : G) ∈ Z.map X.subtype := by
    rw [hZmap, ← hCA]
    exact ⟨huAm, huL⟩
  apply huZ
  obtain ⟨z, hz, hzu⟩ := hua'
  rw [Subgroup.mem_subgroupOf]
  have : z = (u : ↥X) := Subtype.ext hzu
  rw [← this]
  exact hz

end CFSG.RankThree.PartTwo.Sec4.Proof430
