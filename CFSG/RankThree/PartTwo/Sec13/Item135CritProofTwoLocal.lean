module

public import CFSG.RankThree.PartTwo.Sec13.Item135CritProofTrans
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofA7
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Equiv KFacts.KP2

namespace TwoLocalProof

theorem card_filter_centralizer_vOne : (Finset.univ.filter (fun x : Perm (Fin 7) =>
    x * vOneF 1 = vOneF 1 * x ∧ x * vOneF 2 = vOneF 2 * x ∧ Perm.sign x = 1 ∧
      x * cOne ≠ cOne * x)).card = 0 := by
  decide +kernel

theorem commute_cOne_of_commute_vOne {x : Perm (Fin 7)} (h1 : x * vOneF 1 = vOneF 1 * x)
    (h2 : x * vOneF 2 = vOneF 2 * x) (hs : Perm.sign x = 1) : x * cOne = cOne * x := by
  by_contra h
  exact forall_not_of_card_filter_eq_zero card_filter_centralizer_vOne x ⟨h1, h2, hs, h⟩

theorem cOne_ne_one : cOne ≠ 1 := by decide +kernel

theorem vOneF_one_ne_one : vOneF 1 ≠ 1 := by decide +kernel

end TwoLocalProof

open TwoLocalProof in
theorem ks135A7TwoLocal : KS135A7TwoLocal := by
  intro G _ _ A c L hD hA7 hcL h9
  obtain ⟨e⟩ := hA7
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 L with hθ
  set π := QuotientGroup.mk' θ with hπ
  set ε : L →* alternatingGroup (Fin 7) := e.toMonoidHom.comp π with hε
  have hεs : Function.Surjective ε := e.surjective.comp (QuotientGroup.mk'_surjective θ)
  have hεker : ∀ x : L, ε x = 1 ↔ x ∈ θ := by
    intro x
    rw [hε, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff, hπ,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set EL : Subgroup L := A.subgroupOf L with hELdef
  have hEL9 : Nat.card EL = 9 := by
    have h1 : A.subgroupOf L = (A ⊓ L).subgroupOf L := (Subgroup.inf_subgroupOf_right A L).symm
    rw [hELdef, h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, h9]
  have hEL3 : IsPGroup 3 EL := IsPGroup.of_card (n := 2) (by rw [hEL9]; norm_num)
  have hinjπ : Set.InjOn π (EL : Set L) := injOn_mk_of_isPGroup Nat.prime_three hEL3
  have hinjε : Set.InjOn ε (EL : Set L) := fun x hx y hy hxy => hinjπ hx hy (e.injective hxy)
  have hE9 : Nat.card (EL.map ε) = 9 := by rw [card_map_eq_of_injOn ε hinjε, hEL9]
  obtain ⟨g, hg⟩ := Sec4.Res423Two.exists_map_conj_eq_of_card_nine
    Sec4.Res423Two.factorization_card_alt7 Sec4.Res423Two.card_eNine7 hE9
  set c₁ : alternatingGroup (Fin 7) := ⟨cOne, eNine_le_alternatingGroup cOne_mem_eNine⟩
    with hc₁
  have hc₁E : c₁ ∈ Sec4.Res423Two.eNine7 := cOne_mem_eNine
  have hgc : g * c₁ * g⁻¹ ∈ EL.map ε := by
    rw [← hg]
    exact ⟨c₁, hc₁E, rfl⟩
  obtain ⟨bL, hbL, hbLε⟩ := hgc
  have hbLε' : ε bL = g * c₁ * g⁻¹ := hbLε
  set v₁ : alternatingGroup (Fin 7) := ⟨vOneF 1, (vOneF_spec 1).2⟩ with hv₁
  set v₂ : alternatingGroup (Fin 7) := ⟨vOneF 2, (vOneF_spec 2).2⟩ with hv₂
  have hvOne7 : vOne ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨m, rfl⟩
    exact (vOneF_spec m).2
  set V : Subgroup (alternatingGroup (Fin 7)) :=
    (vOne.subgroupOf (alternatingGroup (Fin 7))).map (MulAut.conj g).toMonoidHom with hVdef
  have hV2 : IsPGroup 2 V := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [hVdef, Subgroup.card_map_of_injective (MulAut.conj g).injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hvOne7).toEquiv, card_vOne]
    norm_num
  have hv₁V : g * v₁ * g⁻¹ ∈ V := ⟨v₁, ⟨1, rfl⟩, rfl⟩
  have hv₂V : g * v₂ * g⁻¹ ∈ V := ⟨v₂, ⟨2, rfl⟩, rfl⟩
  have hbL3 : IsPGroup 3 (Subgroup.zpowers bL) := hEL3.to_le (Subgroup.zpowers_le.mpr hbL)
  have hlift : ∀ v ∈ V, ∃ y : L, y ∈ Subgroup.centralizer {bL} ∧ ε y = v := by
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨m, hm⟩ : ∃ m, ((w : alternatingGroup (Fin 7)) : Perm (Fin 7)) = vOneF m := hw
    have hwc : w * c₁ = c₁ * w := Subtype.ext (by
      simp only [Subgroup.coe_mul]
      rw [hm]
      exact (vOneF_spec m).1)
    obtain ⟨x, hx⟩ := hεs ((MulAut.conj g).toMonoidHom w)
    have hcomm : π x * π bL = π bL * π x := by
      apply e.injective
      change ε (x * bL) = ε (bL * x)
      rw [map_mul, map_mul, hx, hbLε']
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g * w * g⁻¹ * (g * c₁ * g⁻¹) = g * (w * c₁) * g⁻¹ := by group
        _ = g * (c₁ * w) * g⁻¹ := by rw [hwc]
        _ = g * c₁ * g⁻¹ * (g * w * g⁻¹) := by group
    have hxN : π x ∈ Subgroup.normalizer
        (((Subgroup.zpowers bL).map π : Subgroup (L ⧸ θ)) : Set (L ⧸ θ)) := by
      rw [MonoidHom.map_zpowers]
      have hcz : π x ∈ Subgroup.centralizer (Subgroup.zpowers (π bL) : Set (L ⧸ θ)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        exact ((Commute.zpow_left (hcomm.symm : Commute (π bL) (π x)) k)).eq
      exact Subgroup.centralizer_le_normalizer _ hcz
    rw [normalizer_map_mk_eq hbL3] at hxN
    obtain ⟨y, hyN, hyx⟩ := hxN
    have h1 : y * bL * y⁻¹ ∈ Subgroup.zpowers bL :=
      (Subgroup.mem_normalizer_iff.mp hyN bL).mp (Subgroup.mem_zpowers bL)
    have h2 : π (y * bL * y⁻¹) = π bL := by
      rw [map_mul, map_mul, map_inv]
      change π y * π bL * (π y)⁻¹ = π bL
      rw [hyx, hcomm, mul_inv_cancel_right]
    have h3 : y * bL * y⁻¹ = bL :=
      injOn_mk_of_isPGroup Nat.prime_three hbL3 h1 (Subgroup.mem_zpowers bL) h2
    refine ⟨y, Subgroup.mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · calc y * bL = (y * bL * y⁻¹) * y := by group
        _ = bL * y := by rw [h3]
    · rw [← hx]
      change e (π y) = e (π x)
      rw [hyx]
  set Y : Subgroup L := V.comap ε ⊓ Subgroup.centralizer {bL} with hYdef
  set ψ : Y →* V := (ε.comp Y.subtype).codRestrict V (fun y => (Subgroup.mem_inf.mp y.2).1)
    with hψdef
  have hψs : Function.Surjective ψ := by
    rintro ⟨v, hv⟩
    obtain ⟨y, hyC, hyv⟩ := hlift v hv
    refine ⟨⟨y, Subgroup.mem_inf.mpr ⟨?_, hyC⟩⟩, Subtype.ext hyv⟩
    rw [Subgroup.mem_comap, hyv]
    exact hv
  obtain ⟨S₂⟩ : Nonempty (Sylow 2 Y) := inferInstance
  have hVtop : IsPGroup 2 (⊤ : Subgroup V) := hV2.of_equiv Subgroup.topEquiv.symm
  have htop := ((S₂.mapSurjective hψs).is_maximal' hVtop le_top).symm
  rw [Sylow.coe_mapSurjective] at htop
  set RL : Subgroup L := (S₂ : Subgroup Y).map Y.subtype with hRLdef
  have hRLmap : ∀ v ∈ V, ∃ r ∈ RL, ε r = v := by
    intro v hv
    have hmem : (⟨v, hv⟩ : V) ∈ (S₂ : Subgroup Y).map ψ := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨s, hs, hsv⟩ := hmem
    exact ⟨s, ⟨s, hs, rfl⟩, congrArg Subtype.val hsv⟩
  have hRLY : RL ≤ Y := Subgroup.map_subtype_le _
  have hRL2 : IsPGroup 2 RL := S₂.isPGroup'.map Y.subtype
  refine ⟨RL.map L.subtype, (bL : G), Subgroup.map_subtype_le _, hRL2.map L.subtype, ?_,
    ⟨Subgroup.mem_subgroupOf.mp hbL, bL.2⟩, ?_, ?_, ?_⟩
  ·
    intro hRθ
    obtain ⟨r, hr, hrv⟩ := hRLmap _ hv₁V
    have hrθ : r ∈ θ := by
      obtain ⟨r', hr', hr'r⟩ := hRθ ⟨r, hr, rfl⟩
      have : r' = r := Subtype.ext hr'r
      rw [← this]
      exact hr'
    rw [← hεker, hrv] at hrθ
    apply vOneF_one_ne_one
    have hv1 : v₁ = 1 := by
      calc v₁ = g⁻¹ * (g * v₁ * g⁻¹) * g := by group
        _ = 1 := by rw [hrθ]; group
    exact congrArg Subtype.val hv1
  ·
    intro hb1
    have hbL1 : bL = 1 := Subtype.ext hb1
    rw [hbL1, map_one] at hbLε'
    apply cOne_ne_one
    have hc : c₁ = 1 := by
      calc c₁ = g⁻¹ * (g * c₁ * g⁻¹) * g := by group
        _ = 1 := by rw [← hbLε']; group
    exact congrArg Subtype.val hc
  ·
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨r, hr, rfl⟩
    have h := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hRLY hr)).2
    exact congrArg Subtype.val h
  ·
    intro x hx
    set xL : L := ⟨x, (Subgroup.mem_inf.mp hx).1⟩ with hxL
    have hxr : ∀ r ∈ RL, ε xL * ε r = ε r * ε xL := by
      intro r hr
      have h := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 (r : G) ⟨r, hr, rfl⟩
      have h' : r * xL = xL * r := Subtype.ext h
      rw [← map_mul, ← map_mul, h']
    obtain ⟨r₁, hr₁, hr₁v⟩ := hRLmap _ hv₁V
    obtain ⟨r₂, hr₂, hr₂v⟩ := hRLmap _ hv₂V
    have hc1 := hxr r₁ hr₁
    rw [hr₁v] at hc1
    have hc2 := hxr r₂ hr₂
    rw [hr₂v] at hc2
    set z : alternatingGroup (Fin 7) := g⁻¹ * ε xL * g with hz
    have hz1 : z * v₁ = v₁ * z := by
      calc z * v₁ = g⁻¹ * (ε xL * (g * v₁ * g⁻¹)) * g := by rw [hz]; group
        _ = g⁻¹ * ((g * v₁ * g⁻¹) * ε xL) * g := by rw [hc1]
        _ = v₁ * z := by rw [hz]; group
    have hz2 : z * v₂ = v₂ * z := by
      calc z * v₂ = g⁻¹ * (ε xL * (g * v₂ * g⁻¹)) * g := by rw [hz]; group
        _ = g⁻¹ * ((g * v₂ * g⁻¹) * ε xL) * g := by rw [hc2]
        _ = v₂ * z := by rw [hz]; group
    have hzc : z * c₁ = c₁ * z := Subtype.ext (commute_cOne_of_commute_vOne
      (congrArg Subtype.val hz1) (congrArg Subtype.val hz2)
      (Equiv.Perm.mem_alternatingGroup.mp z.2))
    have hzx : ε xL = g * z * g⁻¹ := by rw [hz]; group
    have hxb : ε xL * ε bL = ε bL * ε xL := by
      rw [hbLε', hzx]
      calc g * z * g⁻¹ * (g * c₁ * g⁻¹) = g * (z * c₁) * g⁻¹ := by group
        _ = g * (c₁ * z) * g⁻¹ := by rw [hzc]
        _ = g * c₁ * g⁻¹ * (g * z * g⁻¹) := by group
    have hθm : xL * bL * xL⁻¹ * bL⁻¹ ∈ θ := by
      rw [← hεker, map_mul, map_mul, map_mul, map_inv, map_inv, hxb]
      group
    exact ⟨_, hθm, rfl⟩

theorem item135A7Three : Item135A7Three :=
  item135A7Three_of_twoLocal ks135A7TwoLocal

end CFSG.RankThree.PartTwo.Sec13
