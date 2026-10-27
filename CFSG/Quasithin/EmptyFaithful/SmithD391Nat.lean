module

public import CFSG.Quasithin.EmptyFaithful.SmithD391Mult
public import CFSG.Quasithin.EmptyFaithful.SmithD391Q

public section

namespace CFSG.Quasithin.SmithD391

open CFSG.Quasithin.Z391 CFSG.Quasithin.F918X CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise

section Abstract

variable {X : Type} [CommGroup X] {Lb : Subgroup (MulAut X)} {Vb Vb' : Subgroup X}

theorem forall_aut_of_sumNatDual {n : ℕ} (hSND : SumNatDual Lb ⊤ n) (hV : XMod.IsIrr ↥Lb Vb)
    (hV' : XMod.IsIrr ↥Lb Vb') (hinf : Vb ⊓ Vb' = ⊥) (hnot : ¬ XMod.Iso ↥Lb Vb' Vb) :
    ∀ ψ : ↥Vb ≃* ↥Vb, ∃ g ∈ Lb, ∀ u : ↥Vb, g (u : X) = ((ψ u : ↥Vb) : X) := by
  obtain ⟨hn, π, U₁, U₂, hU, hR₁, hR₂⟩ := hSND
  have hd : 2 ≤ n := by rcases hn with rfl | rfl <;> norm_num
  have hirr₁ : ∀ J : Subgroup X, (∀ k ∈ Lb, ∀ w ∈ J, k w ∈ J) → J ≤ U₁ → J = ⊥ ∨ J = U₁ :=
    fun J hJ hJU => FFC.irr_of_binaryNatural hd
      (⟨ZMod 2, inferInstance, inferInstance, by simp, π, hR₁⟩ : BinaryNaturalSL Lb U₁ ⊥ n 1)
      J hJ bot_le hJU
  have hirr₂ := n6_irr_of_dualNat hd hR₂
  have hK₁ : ∀ k ∈ Lb, ∀ u ∈ U₁, k u ∈ U₁ := fun k hk u hu => hR₁.2.2.2.1 ⟨k, hk⟩ u hu
  have hK₂ : ∀ k ∈ Lb, ∀ u ∈ U₂, k u ∈ U₂ := fun k hk u hu => hR₂.2.2.2.1 ⟨k, hk⟩ u hu
  intro ψ
  rcases summands_eq hU.1 hU.2 hK₁ hK₂ hirr₁ hirr₂ hV hV' hinf hnot with ⟨h1, -⟩ | ⟨h1, -⟩
  · subst h1
    obtain ⟨g, hg⟩ := exists_eq_of_mulAut_nat hR₁ ψ
    exact ⟨_, (π g).2, hg⟩
  · subst h1
    obtain ⟨g, hg⟩ := exists_eq_of_mulAut_dual hR₂ ψ
    exact ⟨_, (π g).2, hg⟩

theorem exists_mulEquiv_of_sumNatDual {n : ℕ} (hSND : SumNatDual Lb ⊤ n) :
    Nonempty (↥(StatedSL n (ZMod 2)) ≃* ↥Lb) := by
  obtain ⟨-, π, U₁, U₂, -, hR₁, -⟩ := hSND
  exact ⟨MulEquiv.ofBijective π
    ⟨FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hR₁, hR₁.1⟩⟩

end Abstract

theorem eq_one_of_mem_center_of_equiv {G : Type} [Group G] {L : Subgroup G} {n : ℕ}
    (hn : 0 < n) (e : ↥(StatedSL n (ZMod 2)) ≃* ↥L) {g : G} (hg : g ∈ L)
    (hc : ∀ l ∈ L, g * l = l * g) : g = 1 := by
  have hZ : Subgroup.center ↥L = ⊥ :=
    AL2.center_eq_bot_of_mulEquiv e (center_statedSL_two_eq_bot hn)
  have hmem : (⟨g, hg⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (hc l l.2).symm
  rw [hZ, Subgroup.mem_bot] at hmem
  exact congrArg Subtype.val hmem

section Situation

variable {W : Type} [CommGroup W] [Finite W] {M T L : Subgroup (MulAut W)} {V : Subgroup W}

theorem d391_faithL (hD : D3Std M L T L V) (h5 : D35Five L V) :
    L ⊓ centSec (orbSup T V) (orbSup T V ⊓ fixV L) = ⊥ := by
  let _i := qAct hD.hyp.Mp_normal
  have hLM : L ≤ M := le_of_mem_cComp hD.hyp.comp
  have hinj := (injective_twoClass_tildeQ hD h5).1
  rw [eq_bot_iff]
  rintro l ⟨hlL, hlC⟩
  rw [Subgroup.mem_bot]
  have h1 : actAut (L.subgroupOf M) (tilde L ⊤ V) (isIrr_tildeQ hD).1
      ⟨⟨l, hLM hlL⟩, hlL⟩ = 1 := by
    refine MulEquiv.ext fun q => Subtype.ext ?_
    show (⟨l, hLM hlL⟩ : ↥M) • (q : W ⧸ modFix L (⊤ : Subgroup W)) = q
    obtain ⟨w, hw, hq⟩ := mem_tilde_iff.1 q.2
    rw [← hq]
    show (QuotientGroup.mk (l w) : W ⧸ modFix L (⊤ : Subgroup W)) = QuotientGroup.mk w
    rw [QuotientGroup.eq, modFix_top_eq]
    have h2 : l w * w⁻¹ ∈ fixV L := ((mem_centSec.1 hlC).2 w (le_orbSup T V hw)).2
    have h3 := (fixV L).inv_mem h2
    rwa [mul_inv_rev, inv_inv, mul_comm] at h3
  have h2 := hinj (h1.trans (map_one _).symm)
  exact congrArg (fun x : ↥(L.subgroupOf M) => ((x : ↥M) : MulAut W)) h2

theorem d391_mulEquiv (hD : D3Std M L T L V) (h5 : D35Five L V) {n : ℕ}
    (hSND : SumNatDual (autSec L (orbSup T V) (orbSup T V ⊓ fixV L)) ⊤ n) :
    Nonempty (↥(StatedSL n (ZMod 2)) ≃* ↥L) := by
  obtain ⟨e⟩ := exists_mulEquiv_of_sumNatDual hSND
  have hG := n1_sup_le_stabSub_sec hD.hyp
  have hLs : L ≤ stabSub (orbSup T V) := le_sup_left.trans (hG.trans inf_le_left)
  have hLc : L ≤ stabSub (orbSup T V ⊓ fixV L) := le_sup_left.trans (hG.trans inf_le_right)
  exact ⟨e.trans (B5.secEquiv L hLs hLc (d391_faithL hD h5)).symm⟩

theorem d391_inj (hD : D3Std M L T L V) (h5 : D35Five L V) :
    letI := qAct hD.hyp.Mp_normal
    ∀ l : ↥(L.subgroupOf M), (∀ v ∈ tilde L ⊤ V, (l : ↥M) • v = v) → l = 1 := by
  let _i := qAct hD.hyp.Mp_normal
  intro l hl
  apply (injective_twoClass_tildeQ hD h5).1
  rw [map_one]
  exact MulEquiv.ext fun v => Subtype.ext (by
    show (l : ↥M) • (v : W ⧸ modFix L (⊤ : Subgroup W)) = v
    exact hl v v.2)

theorem d391_center (hD : D3Std M L T L V) {n : ℕ} (hn : 0 < n)
    (e : ↥(StatedSL n (ZMod 2)) ≃* ↥L) :
    ∀ l : ↥(L.subgroupOf M), (∀ l' : ↥(L.subgroupOf M), l * l' = l' * l) → l = 1 := by
  have hLM : L ≤ M := le_of_mem_cComp hD.hyp.comp
  intro l hl
  have h1 := eq_one_of_mem_center_of_equiv hn e (g := ((l : ↥M) : MulAut W)) l.2
    (fun l'' hl'' => by
      have h2 := hl ⟨⟨l'', hLM hl''⟩, hl''⟩
      exact congrArg (fun x : ↥(L.subgroupOf M) => ((x : ↥M) : MulAut W)) h2)
  exact Subtype.ext (Subtype.ext h1)

theorem d391_aut (hD : D3Std M L T L V)
    (hAutX : ∀ ψ : ↥(sec35Img (orbSup T V) (orbSup T V ⊓ fixV L) V) ≃*
        ↥(sec35Img (orbSup T V) (orbSup T V ⊓ fixV L) V),
      ∃ g ∈ autSec L (orbSup T V) (orbSup T V ⊓ fixV L),
        ∀ u : ↥(sec35Img (orbSup T V) (orbSup T V ⊓ fixV L) V),
          g (u : Sec (orbSup T V) (orbSup T V ⊓ fixV L)) =
            ((ψ u : ↥(sec35Img (orbSup T V) (orbSup T V ⊓ fixV L) V)) :
              Sec (orbSup T V) (orbSup T V ⊓ fixV L))) :
    letI := qAct hD.hyp.Mp_normal
    ∀ ψ : ↥(tilde L ⊤ V) ≃* ↥(tilde L ⊤ V), ∃ l : ↥(L.subgroupOf M),
      ∀ v : ↥(tilde L ⊤ V), (l : ↥M) • (v : W ⧸ modFix L (⊤ : Subgroup W)) =
        ((ψ v : ↥(tilde L ⊤ V)) : W ⧸ modFix L (⊤ : Subgroup W)) := by
  let _i := qAct hD.hyp.Mp_normal
  intro ψ
  set VT := orbSup T V with hVT
  set C := VT ⊓ fixV L with hC
  set Vb := sec35Img VT C V with hVb
  have hLM : L ≤ M := le_of_mem_cComp hD.hyp.comp
  have hLG : L ≤ stabSub VT ⊓ stabSub C := le_sup_left.trans (n1_sup_le_stabSub_sec hD.hyp)
  have hmapV : Vb.map (iotaQ L VT) = tilde L ⊤ V := map_iotaQ_sec35Img L (le_orbSup T V)
  let j : ↥Vb ≃* ↥(tilde L ⊤ V) :=
    (Subgroup.equivMapOfInjective Vb (iotaQ L VT) (iotaQ_injective L VT)).trans
      (MulEquiv.subgroupCongr hmapV)
  have hj : ∀ u : ↥Vb, ((j u : ↥(tilde L ⊤ V)) : W ⧸ modFix L (⊤ : Subgroup W)) =
      iotaQ L VT (u : Sec VT C) := fun u => rfl
  obtain ⟨g, hgL, hg⟩ := hAutX (j.trans (ψ.trans j.symm))
  obtain ⟨g₀, hg₀L, rfl⟩ := (n2_mem_autSec hLG).1 hgL
  refine ⟨⟨⟨g₀, hLM hg₀L⟩, hg₀L⟩, fun v => ?_⟩
  have hv : (v : W ⧸ modFix L (⊤ : Subgroup W)) = iotaQ L VT ((j.symm v : ↥Vb) : Sec VT C) := by
    rw [← hj, MulEquiv.apply_symm_apply]
  have h2 := hg (j.symm v)
  have h3 : (((j.trans (ψ.trans j.symm)) (j.symm v) : ↥Vb) : Sec VT C) =
      ((j.symm (ψ v) : ↥Vb) : Sec VT C) := by
    simp
  calc (⟨g₀, hLM hg₀L⟩ : ↥M) • (v : W ⧸ modFix L (⊤ : Subgroup W))
      = (⟨g₀, hLM hg₀L⟩ : ↥M) • iotaQ L VT ((j.symm v : ↥Vb) : Sec VT C) := by rw [hv]
    _ = iotaQ L VT (n2Rho VT C g₀ ((j.symm v : ↥Vb) : Sec VT C)) :=
        (iotaQ_rho hD.hyp.Mp_normal g₀ (hLM hg₀L) _).symm
    _ = iotaQ L VT ((j.symm (ψ v) : ↥Vb) : Sec VT C) := by rw [h2, h3]
    _ = ((ψ v : ↥(tilde L ⊤ V)) : W ⧸ modFix L (⊤ : Subgroup W)) := by
        rw [← hj, MulEquiv.apply_symm_apply]

end Situation

end CFSG.Quasithin.SmithD391
