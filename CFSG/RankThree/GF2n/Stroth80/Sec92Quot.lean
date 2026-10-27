module

public import CFSG.RankThree.GF2n.Stroth80.Sec9Alg
public import CFSG.RankThree.GF2n.Stroth80.Sec92Basic
public import CFSG.RankThree.GF2n.Stroth80.Sec5Core
public import CFSG.Quasithin.H13.NQRigidWMGroups

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Sec9R0_conj_mem (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) {x ρ : G}
    (hρ : ρ ∈ Rt M (LB M Q B) t) {a : G} (ha : a ∈ Sec9R0 hc t x) :
    ρ * a * ρ⁻¹ ∈ Sec9R0 hc t x := by
  let f : G →* G := (MulAut.conj ρ).toMonoidHom
  have hle : Sec9R0 hc t x ≤ (Sec9R0 hc t x).comap f := by
    refine sup_le (fun s hs => ?_) (iSup₂_le fun ρ₁ hρ₁ => ?_)
    · exact CN_le_Sec9R0 hc t x (hc.CN_conj_mem ht hρ hs)
    · rw [Subgroup.zpowers_le]
      show ρ * (ρ₁ * x * ρ₁⁻¹) * ρ⁻¹ ∈ Sec9R0 hc t x
      have e : ρ * (ρ₁ * x * ρ₁⁻¹) * ρ⁻¹ = (ρ * ρ₁) * x * (ρ * ρ₁)⁻¹ := by group
      rw [e]
      refine Subgroup.mem_sup_right (Subgroup.mem_iSup_of_mem (ρ * ρ₁)
        (Subgroup.mem_iSup_of_mem ((Rt M (LB M Q B) t).mul_mem hρ hρ₁) ?_))
      exact Subgroup.mem_zpowers _
  exact hle ha

theorem sec9_nonabelian_of_commutator_eq_top {Y : Type} [Group Y] [Nontrivial Y]
    (h : commutator Y = ⊤) : ∃ a b : Y, a * b ≠ b * a := by
  by_contra hno
  push Not at hno
  have hbot : commutator Y = ⊥ := by
    rw [commutator_def, eq_bot_iff, Subgroup.commutator_le]
    intro a _ b _
    rw [Subgroup.mem_bot, commutatorElement_def, hno a b, mul_inv_cancel_right, mul_inv_cancel]
  obtain ⟨y, hy⟩ := exists_ne (1 : Y)
  have : y ∈ commutator Y := h ▸ Subgroup.mem_top y
  rw [hbot, Subgroup.mem_bot] at this
  exact hy this

theorem step92Quot : Step92QuotStatement := by
  intro G _ _ M Q Z B hc n t hs x hxL hxN hlt
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hxR : x ∈ Rt M (LB M Q B) t := (le_Rt (M := M) (LB M Q B) ht) hxL
  obtain ⟨K, fK, finK, hK, φ, hφr, hφk, -⟩ := hs.plus4
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hK.trans hZ2)
  have h4 : 4 ≤ Nat.card K := by rw [hK]; exact hc.hyp.q4
  obtain ⟨e⟩ := statedOmega_plus_four_nonempty_equiv K h4
  haveI hsimple : IsSimpleGroup ↥(StatedSL 2 K) :=
    CFSG.Quasithin.H13.NQRigid.isSimpleGroup_statedSL_two_charTwo h4
  have hnonab : ∃ a b : ↥(StatedSL 2 K), a * b ≠ b * a :=
    sec9_nonabelian_of_commutator_eq_top
      (statedSL_quasisimple_of_card 2 K le_rfl h4).1.commutator_eq_top
  let ψ : ↥(Rt M (LB M Q B) t) →* ↥(StatedSL 2 K) × ↥(StatedSL 2 K) :=
    e.toMonoidHom.comp ((MulEquiv.subgroupCongr hφr).toMonoidHom.comp φ.rangeRestrict)
  have hψsurj : Function.Surjective ψ := by
    refine e.surjective.comp ((MulEquiv.subgroupCongr hφr).surjective.comp
      (MonoidHom.rangeRestrict_surjective φ))
  have hψker : ψ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) := by
    rw [← hφk]
    ext g
    simp only [MonoidHom.mem_ker, ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    constructor
    · intro h
      have h1 := e.injective (h.trans (map_one e).symm)
      have h2 := (MulEquiv.subgroupCongr hφr).injective
        (h1.trans (map_one (MulEquiv.subgroupCongr hφr)).symm)
      have := congrArg Subtype.val h2
      simpa using this
    · intro h
      have h1 : (φ.rangeRestrict g) = 1 := Subtype.ext (by simpa using h)
      rw [h1]
      simp
  have hR₀R : Sec9R0 hc t x ≤ Rt M (LB M Q B) t := Sec9R0_le_Rt hc hxR
  have hNR₀ : hc.CN t ≤ Sec9R0 hc t x := CN_le_Sec9R0 hc t x
  haveI hnormR₀ : ((Sec9R0 hc t x).subgroupOf (Rt M (LB M Q B) t)).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact Sec9R0_conj_mem hc ht g.2 ha
  haveI hnormN : ((hc.CN t).subgroupOf (Sec9R0 hc t x)).Normal := by
    refine ⟨fun a ha g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact hc.CN_conj_mem ht (hR₀R g.2) ha
  set H := ((Sec9R0 hc t x).subgroupOf (Rt M (LB M Q B) t)).map ψ with hH
  haveI hHnormal : H.Normal := Subgroup.Normal.map hnormR₀ ψ hψsurj
  have hHbot : H ≠ ⊥ := by
    intro hbot
    have hmem : ψ ⟨x, hxR⟩ ∈ H :=
      ⟨⟨x, hxR⟩, Subgroup.mem_subgroupOf.mpr (mem_Sec9R0 hc t hxR), rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    have : (⟨x, hxR⟩ : ↥(Rt M (LB M Q B) t)) ∈ ψ.ker := hmem
    rw [hψker, Subgroup.mem_subgroupOf] at this
    exact hxN this
  have hHtop : H ≠ ⊤ := by
    intro htop
    apply hlt.ne
    refine le_antisymm hR₀R ?_
    intro g hg
    obtain ⟨a, ha, hag⟩ : ψ ⟨g, hg⟩ ∈ H := by rw [htop]; exact Subgroup.mem_top _
    have hker1 : (a⁻¹ * ⟨g, hg⟩ : ↥(Rt M (LB M Q B) t)) ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hag, inv_mul_cancel]
    rw [hψker, Subgroup.mem_subgroupOf] at hker1
    have haR₀ : (a : G) ∈ Sec9R0 hc t x := Subgroup.mem_subgroupOf.mp ha
    have hn : (a : G)⁻¹ * g ∈ Sec9R0 hc t x := hNR₀ hker1
    have e2 : g = (a : G) * ((a : G)⁻¹ * g) := by group
    rw [e2]
    exact (Sec9R0 hc t x).mul_mem haR₀ hn
  have hfac := sec9_normal_sub_prod hnonab hnonab H hHbot hHtop
  obtain ⟨eqv⟩ := sec9_quot_equiv_map hNR₀ hR₀R ψ hψker
  refine ⟨hnormN, K, fK, finK, hK, ?_⟩
  rcases hfac with h | h
  · obtain ⟨e₁⟩ := h
    exact ⟨eqv.trans e₁⟩
  · obtain ⟨e₂⟩ := h
    exact ⟨eqv.trans e₂⟩

end CFSG.RankThree.GF2n.Stroth80
