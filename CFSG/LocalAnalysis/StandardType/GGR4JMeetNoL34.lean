module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetKGDefs
public import CFSG.LocalAnalysis.StandardType.GGE6TwoTorus
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetL34
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggR4Meet_noE6TwoL34
  {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hCfg : GGConfig 3 B Bs x L D J)
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G)) (hCard : Nat.card Bs = 3 ^ 5)
    (hperf : commutator ↥L = ⊤) (hZL : ∀ g ∈ Subgroup.center ↥L, Nat.Coprime 3 (orderOf g))
    (hL : GGHasLabel ⟨.E6, 0, 1⟩ (↥L ⧸ Subgroup.center ↥L))
    (hJ : GGHasLabel ⟨.A, 2, 2⟩
      (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L))) : False := by
  have hS : LargeEvenSStar 3 B x L := hCfg.1.2.2.2.2.2.2.1
  have hStd : LargeEvenStdSubPre 3 B x L D J := hCfg.2.2.1
  haveI : Group.IsPerfect ↥L := Group.isPerfect_def.mpr hperf
  obtain ⟨F, U, hFelem, hFcard, hUbot, hU2, hFU⟩ := ggE6TwoTwoLocalFour_holds ↥L hL
  have hFZ : F ⊓ Subgroup.center ↥L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    rw [Subgroup.mem_inf] at hg
    have hg3 : g ^ 3 = 1 := hFelem.2 g hg.1
    have hdvd : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
    have h1 : orderOf g = 1 :=
      Nat.eq_one_of_dvd_coprimes (hZL g hg.2) hdvd dvd_rfl
    exact orderOf_eq_one_iff.mp h1
  have hx3 : x ^ 3 = 1 := hCfg.2.1.2.1.2 x (hCfg.2.1.1 hS.2.1)
  have hrank : 5 ≤ LargeEvenTwoLocalRank 3 G :=
    five_le_twoLocalRank_of_normalizing hS.2.2.2.1.1 hS.2.2.1 hx3 hUbot hU2 hFU hFelem
      (Or.inr ⟨hFcard, hFZ⟩)
  have hBcard : Nat.card Bs ≤ Nat.card B := by
    rw [hS.1.2.1, hCard]
    exact Nat.pow_le_pow_right (by norm_num : 0 < 3) hrank
  have hB : B = Bs := Subgroup.eq_of_le_of_card_ge hCfg.2.1.1 hBcard
  have hD : D = Bs ⊓ Subgroup.centralizer (J : Set G) := by
    rw [← hB]
    exact hStd.2.2.2.2.2.2
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a :=
    fun a ha b hb => CFSG.Open.IsElemAbelian.comm hCfg.2.1.2.1 ha hb
  have hBsNJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hcomm hCfg.2.1.1 hStd hBsN
  let α : ↥Bs →* MulAut ↥J :=
    (Subgroup.normalizerMonoidHom (H := J)).comp (Subgroup.inclusion hBsNJ)
  have hαapply : ∀ (b : ↥Bs) (j : ↥J),
      ((α b) j : G) = (b : G) * (j : G) * (b : G)⁻¹ := by
    intro b j
    have hαb : α b = Subgroup.normalizerMonoidHom (H := J) ⟨(b : G), hBsNJ b.2⟩ := rfl
    rw [hαb, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hαeq : ∀ b : ↥Bs, α b = 1 ↔ (b : G) ∈ Subgroup.centralizer (J : Set G) := by
    intro b
    constructor
    · intro hb
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have h : (b : G) * (j : G) * (b : G)⁻¹ = (j : G) := by
        have h0 := congrArg (fun φ : MulAut ↥J => (((φ ⟨j, hj⟩ : ↥J) : G))) hb
        simpa only [MulAut.one_apply, hαapply, Subtype.coe_mk] using h0
      calc (j : G) * (b : G) = ((b : G) * (j : G) * (b : G)⁻¹) * (b : G) := by rw [h]
        _ = (b : G) * (j : G) := by group
    · intro hbC
      ext j
      rw [hαapply b j, MulAut.one_apply]
      have hcomm' := (Subgroup.mem_centralizer_iff.mp hbC) (j : G) j.2
      calc (b : G) * (j : G) * (b : G)⁻¹ = ((j : G) * (b : G)) * (b : G)⁻¹ := by
            rw [← hcomm']
        _ = (j : G) := by group
  have hker : α.ker = (Bs ⊓ Subgroup.centralizer (J : Set G)).subgroupOf Bs := by
    ext b
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => ⟨b.2, (hαeq b).mp h⟩, fun h => (hαeq b).mpr h.2⟩
  have hcardKer : Nat.card α.ker = 9 := by
    rw [hker]
    have hcardSub : Nat.card ↥((Bs ⊓ Subgroup.centralizer (J : Set G)).subgroupOf Bs) =
        Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (inf_le_left : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ Bs)).toEquiv
    rw [hcardSub, ← hD, hStd.2.2.1]
    norm_num
  have hcardW : Nat.card α.range = 27 := by
    have h := Subgroup.card_ker_mul_card_range α
    rw [hcardKer, hCard] at h
    have h27 : (9 : ℕ) * Nat.card α.range = 9 * 27 := by rw [h]; norm_num
    exact Nat.mul_left_cancel (by norm_num : 0 < 9) h27
  have hElemTop : IsElemAbelian 3 (⊤ : Subgroup ↥Bs) := by
    have htop : Subgroup.comap Bs.subtype Bs = (⊤ : Subgroup ↥Bs) := by
      ext g
      simp [Subgroup.mem_comap]
    rw [← htop]
    exact CFSG.Open.IsElemAbelian.comap hCfg.2.1.2.1 Bs.subtype_injective
  have hWelem : IsElemAbelian 3 α.range := by
    have h := CFSG.Open.IsElemAbelian.map hElemTop α
    rwa [Subgroup.map_top] at h
  have hJL : J ≤ L := by
    rw [hStd.2.2.2.2.1]
    exact sSup_le fun K hK => hK.1.trans inf_le_left
  let e : ↥(J.subgroupOf L) ≃* ↥J := Subgroup.subgroupOfEquivOfLe hJL
  haveI : Group.IsPerfect ↥J := Group.isPerfect_def.mpr hStd.2.2.2.2.2.1.2.2.1
  have hperfJ : commutator ↥(J.subgroupOf L) = ⊤ :=
    Group.isPerfect_def.mp
      (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective)
  have hW'elem : IsElemAbelian 3 ((α.range).map (MulAut.congr e.symm).toMonoidHom) :=
    CFSG.Open.IsElemAbelian.map hWelem (MulAut.congr e.symm).toMonoidHom
  have hW'card : Nat.card ((α.range).map (MulAut.congr e.symm).toMonoidHom) = 27 := by
    rw [Subgroup.card_map_of_injective (MulAut.congr e.symm).injective, hcardW]
  have hle9 : Nat.card ((α.range).map (MulAut.congr e.symm).toMonoidHom) ≤ 9 :=
    ggAut_L34_card_le_nine ↥(J.subgroupOf L) hperfJ hJ _ hW'elem
  omega

end CFSG.StandardType

end
