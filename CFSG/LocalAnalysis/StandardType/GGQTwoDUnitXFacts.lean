module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitXPair
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitOrthA3
public import CFSG.LocalAnalysis.StandardType.GGSkeleton
import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinHC

public section

namespace CFSG.StandardType.QTwo

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.PhanDn.QTwo
  CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {G : Type} [Group G] [Finite G]

variable {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
  {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {m : ℕ}
  {e' : Fin m ≃ ι} {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {ψ : Su F0 2 1 m →* G}
  {ε : Equiv.Perm (Fin m) ≃* ↥(ggAutomizer L Bs)} {βL : Additive ↥Bs ≃+ DVec m} {ω : F0ˣ}
  {a b c : Fin m} {α : MulAut ↥Bs} {g : G} {b' : ↥Bs}

private lemma qtwoDB22_dBasis_apply (m : ℕ) (i : Fin m) :
    dBasis m i = Pi.single i (1 : ZMod 3) :=
  Pi.basisFun_apply (ZMod 3) (Fin m) i

private lemma qtwoDB22_dPerm_inv (m : ℕ) (σ : Equiv.Perm (Fin m)) :
    dPerm m σ⁻¹ = (dPerm m σ)⁻¹ := by
  symm
  exact inv_eq_of_mul_eq_one_right (by rw [← dPerm_mul, mul_inv_cancel, dPerm_one])

private lemma qtwoDB22_oTwoPrime_mono {H K : Subgroup G} (h : H ≤ K) :
    ggOTwoPrime H ≤ ggOTwoPrime K :=
  Subgroup.closure_mono fun _ hy => ⟨h hy.1, hy.2⟩

theorem qtwoDB22_frame_of_weyl {X : Subgroup G}
    (hjoin : ∀ w ∈ dEven m, ∃ a ∈ ggAutomizerJoin L Bs 𝒦,
      ∀ s : ↥Bs, βL (Additive.ofMul (a s)) = w (βL (Additive.ofMul s)))
    (hnode : ∃ c₀ : Fin m, ∀ i : Fin m, (i : ℕ) ≠ 0 → ∃ (sgn : Bool) (a b : Fin m),
      a ≠ b ∧ a ≠ c₀ ∧ b ≠ c₀ ∧ ∀ s : ↥Bs,
        βL (Additive.ofMul ((((e (M.simple (e' i)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs))
          s)) = dTau m sgn a b (βL (Additive.ofMul s)))
    (hweyl : ∀ a' : MulAut ↥Bs, a' ∈ ggAutomizerJoin L Bs 𝒦 →
      ∀ w : DVec m ≃ₗ[ZMod 3] DVec m, w ∈ dEven m → w (Pi.single c 1) = Pi.single c 1 →
        (∀ s : ↥Bs, βL (Additive.ofMul (a' s)) = w (βL (Additive.ofMul s))) →
          a' ∈ ggAutomizer X Bs) :
    QTwoFrameAt Bs X M (ggAutomizerJoin L Bs 𝒦) e e' := by
  classical
  obtain ⟨c₀, hnode⟩ := hnode
  let σ : Equiv.Perm (Fin m) := Equiv.swap c₀ c
  have hσ : dPerm m σ ∈ dEven m := dPerm_mem_dEven m σ
  obtain ⟨a₀, ha₀J, ha₀w⟩ := hjoin (dPerm m σ) hσ
  let w₀ : M.Group := e.symm ⟨a₀, ha₀J⟩
  refine ⟨w₀, fun i hi => ?_⟩
  obtain ⟨sgn, a, b, hab, hac₀, hbc₀, hact⟩ := hnode i hi
  have hσac : σ a ≠ c := by
    intro h
    change Equiv.swap c₀ c a = c at h
    exact hac₀ ((Equiv.swap_apply_eq_iff.mp h).trans (Equiv.swap_apply_right c₀ c))
  have hσbc : σ b ≠ c := by
    intro h
    change Equiv.swap c₀ c b = c at h
    exact hbc₀ ((Equiv.swap_apply_eq_iff.mp h).trans (Equiv.swap_apply_right c₀ c))
  have hσab : σ a ≠ σ b := σ.injective.ne hab
  let a' : MulAut ↥Bs := a₀ *
    (((e (M.simple (e' i)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs)) * a₀⁻¹
  have ha'J : a' ∈ ggAutomizerJoin L Bs 𝒦 := by
    dsimp only [a']
    exact (ggAutomizerJoin L Bs 𝒦).mul_mem
      ((ggAutomizerJoin L Bs 𝒦).mul_mem ha₀J (e (M.simple (e' i))).2)
      ((ggAutomizerJoin L Bs 𝒦).inv_mem ha₀J)
  let w : DVec m ≃ₗ[ZMod 3] DVec m := dPerm m σ * dTau m sgn a b * (dPerm m σ)⁻¹
  have hw : w ∈ dEven m := by
    dsimp only [w]
    exact (dEven m).mul_mem ((dEven m).mul_mem (dPerm_mem_dEven m σ)
      (dTau_mem_dEven m sgn hab)) ((dEven m).inv_mem (dPerm_mem_dEven m σ))
  have hconj : w = dTau m sgn (σ a) (σ b) := by
    dsimp only [w]
    rw [dPerm_conj_dTau]
  have hwc : w (Pi.single c 1) = Pi.single c 1 := by
    rw [hconj, ← qtwoDB22_dBasis_apply m c]
    exact dTau_apply_of_ne m sgn (Ne.symm hσac) (Ne.symm hσbc)
  have hainv : ∀ s : ↥Bs, βL (Additive.ofMul (a₀⁻¹ s)) =
      dPerm m σ⁻¹ (βL (Additive.ofMul s)) := by
    intro s
    have h := ha₀w (a₀⁻¹ s)
    rw [MulAut.apply_inv_self] at h
    rw [h, ← LinearEquiv.mul_apply, show dPerm m σ⁻¹ * dPerm m σ = 1 from by
      rw [← dPerm_mul, inv_mul_cancel, dPerm_one]]
    rfl
  have ha'w : ∀ s : ↥Bs, βL (Additive.ofMul (a' s)) = w (βL (Additive.ofMul s)) := by
    intro s
    have h1 : βL (Additive.ofMul (a' s)) =
        dPerm m σ (dTau m sgn a b (dPerm m σ⁻¹ (βL (Additive.ofMul s)))) := by
      dsimp only [a']
      rw [MulAut.mul_apply, MulAut.mul_apply, ha₀w, hact, hainv s]
    have h2 : dPerm m σ (dTau m sgn a b (dPerm m σ⁻¹ (βL (Additive.ofMul s)))) =
        w (βL (Additive.ofMul s)) := by
      rw [show w = dPerm m σ * dTau m sgn a b * (dPerm m σ)⁻¹ from rfl,
        qtwoDB22_dPerm_inv, ← LinearEquiv.mul_apply, ← LinearEquiv.mul_apply]
    rw [h1, h2]
  have hgoal : ((e (w₀ * M.simple (e' i) * w₀⁻¹) :
      ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = a' := by
    dsimp only [w₀, a']
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
    rfl
  rw [hgoal]
  exact hweyl a' ha'J w hw hwc ha'w



theorem ggQTwoDUnit_X_frame (hm : 7 ≤ m) (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b') :
    QTwoFrameAt Bs (qtwoDelX ψ c g) M (ggAutomizerJoin L Bs 𝒦) e e' :=
  qtwoDB22_frame_of_weyl hcoords.join_onto hcoords.node fun _ ha'J _ hw hwc ha'w =>
    ggQTwoDUnit_weyl_X (by omega) hbase hcoords hdel.hab hdel.hca hdel.hcb hdel.sign hdel.norm
      hdel.conj ha'J hw hwc ha'w

theorem ggQTwoDUnit_X_adjA3 (hA3 : QTwoOrthAdjA3Stmt) (hEA : GGQTwoEdgeAmbientInput)
    (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hm : 7 ≤ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b')
    {Y : Subgroup G} (hXY : qtwoDelX ψ c g ≤ Y) (Φ : OrthTorus.OrthFrameCore 3 Bs Y)
    (hF : Nat.card Φ.F = 2) (hr : 5 ≤ Φ.r) (hZ : Subgroup.center ↥Y = ⊥) :
    ∀ r₁ ∈ ggAutomizer (qtwoDelX ψ c g) Bs, r₁ ∈ ggCoxRefl M e →
      ∀ r₂ ∈ ggAutomizer (qtwoDelX ψ c g) Bs, r₂ ∈ ggCoxRefl M e →
        ∀ r₃ ∈ ggAutomizer (qtwoDelX ψ c g) Bs, r₃ ∈ ggCoxRefl M e →
          r₁ * r₂ ≠ r₂ * r₁ → r₂ * r₃ ≠ r₃ * r₂ → r₁ * r₃ = r₃ * r₁ → r₁ ≠ r₃ →
            Nat.card ↥(ggRankOneIn (qtwoDelX ψ c g) Bs r₁) = 6 →
              ∃ θ : Su (GaloisField 2 2) 2 1 4 →* G,
                θ.range = ggRankTwoIn (qtwoDelX ψ c g) Bs r₁ r₂ ⊔
                  ggRankTwoIn (qtwoDelX ψ c g) Bs r₂ r₃ := by
  intro r₁ hr1A hr1C r₂ hr2A hr2C r₃ hr3A hr3C h12 h23 h13 hne _h6
  have hBsE : CFSG.Open.IsElemAbelian 3 Bs := by
    have h := hbase.hyp.bstar.2.1
    rwa [hbase.p_eq] at h
  have hr1refl : GGIsReflection 3 r₁ := by
    have h := ggCoxRefl_isReflection hcfg.2.2.2.1.2 hr1C
    rwa [hbase.p_eq] at h
  have hr2refl : GGIsReflection 3 r₂ := by
    have h := ggCoxRefl_isReflection hcfg.2.2.2.1.2 hr2C
    rwa [hbase.p_eq] at h
  have hr3refl : GGIsReflection 3 r₃ := by
    have h := ggCoxRefl_isReflection hcfg.2.2.2.1.2 hr3C
    rwa [hbase.p_eq] at h
  obtain ⟨θ, hθ⟩ := hA3 G Bs Y hBsE Φ hF hr hZ r₁ (ggAutomizer_mono Bs hXY hr1A) hr1refl
    r₂ (ggAutomizer_mono Bs hXY hr2A) hr2refl
    r₃ (ggAutomizer_mono Bs hXY hr3A) hr3refl h12 h23 h13 hne
  refine ⟨θ, ?_⟩
  have hp12 : ggRankTwoIn Y Bs r₁ r₂ = ggRankTwoIn (qtwoDelX ψ c g) Bs r₁ r₂ := by
    have hXeq := ggQTwoDUnit_X_rankTwo hEA hcfg hm hM hbase hcoords hdel r₁ hr1A hr1C
      r₂ hr2A hr2C h12
    have hmono : ggRankTwoIn (qtwoDelX ψ c g) Bs r₁ r₂ ≤ ggRankTwoIn Y Bs r₁ r₂ := by
      rw [ggRankTwoIn, ggRankTwoIn]
      exact qtwoDB22_oTwoPrime_mono (inf_le_inf hXY le_rfl)
    have hglob : ggRankTwoIn Y Bs r₁ r₂ ≤ ggRankTwo Bs r₁ r₂ := by
      rw [ggRankTwoIn, ggRankTwo]
      exact qtwoDB22_oTwoPrime_mono inf_le_right
    exact le_antisymm (hglob.trans_eq hXeq) hmono
  have hp23 : ggRankTwoIn Y Bs r₂ r₃ = ggRankTwoIn (qtwoDelX ψ c g) Bs r₂ r₃ := by
    have hXeq := ggQTwoDUnit_X_rankTwo hEA hcfg hm hM hbase hcoords hdel r₂ hr2A hr2C
      r₃ hr3A hr3C h23
    have hmono : ggRankTwoIn (qtwoDelX ψ c g) Bs r₂ r₃ ≤ ggRankTwoIn Y Bs r₂ r₃ := by
      rw [ggRankTwoIn, ggRankTwoIn]
      exact qtwoDB22_oTwoPrime_mono (inf_le_inf hXY le_rfl)
    have hglob : ggRankTwoIn Y Bs r₂ r₃ ≤ ggRankTwo Bs r₂ r₃ := by
      rw [ggRankTwoIn, ggRankTwo]
      exact qtwoDB22_oTwoPrime_mono inf_le_right
    exact le_antisymm (hglob.trans_eq hXeq) hmono
  rw [hθ, hp12, hp23]

theorem qtwoDB22_X_le_ggG0_of (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) {J₁ : Subgroup G}
    (hJ₁L : J₁ ≤ L) (hgJ : g ∈ L ⊔ ⨆ K ∈ 𝒦, K) :
    J₁ ⊔ J₁.map (MulAut.conj g).toMonoidHom ≤ ggG0 p B x L D J := by
  have hNbr : GGNbrSet p B x D J 𝒦 := hcfg.1.2.2.2.1
  have hjoin : L ⊔ ⨆ K ∈ 𝒦, K ≤ ggG0 p B x L D J := ggJoin_le_ggG0 (Bs := Bs) hNbr
  have hJ1 : J₁ ≤ ggG0 p B x L D J := hJ₁L.trans (le_ggG0_left p B x L D J)
  have hJ2 : J₁.map (MulAut.conj g).toMonoidHom ≤ ggG0 p B x L D J := by
    rintro z ⟨y, hy, rfl⟩
    have hgG0 : g ∈ ggG0 p B x L D J := hjoin hgJ
    exact (ggG0 p B x L D J).mul_mem
      ((ggG0 p B x L D J).mul_mem hgG0 (hJ1 hy))
      ((ggG0 p B x L D J).inv_mem hgG0)
  exact sup_le hJ1 hJ2

theorem ggQTwoDUnit_X_le_ggG0 (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (hbase : QTwoUnitBase p B Bs x L ψ ε) (hgJ : g ∈ L ⊔ ⨆ K ∈ 𝒦, K) :
    qtwoDelX ψ c g ≤ ggG0 p B x L D J := by
  have hJ1L : qtwoDelJ ψ c ≤ L := by
    rw [qtwoDelJ, ← hbase.range]
    exact Subgroup.map_le_range ψ _
  rw [qtwoDelX]
  exact qtwoDB22_X_le_ggG0_of hcfg hJ1L hgJ

theorem ggQTwoDUnit_X_facts (hA3 : QTwoOrthAdjA3Stmt) (hL1 : GGQTwoL1Input)
    (hEA : GGQTwoEdgeAmbientInput) (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e) (hm : 7 ≤ m)
    (hM : M = (ggCoxeterMatrixD m).reindex e') (hbase : QTwoUnitBase p B Bs x L ψ ε)
    (hcoords : QTwoUnitCoords Bs x L 𝒦 M e e' ψ ε βL ω) (hdel : QTwoUnitDel Bs βL a b c α g b')
    {Y : Subgroup G} (hXY : qtwoDelX ψ c g ≤ Y) (Φ : OrthTorus.OrthFrameCore 3 Bs Y)
    (hF : Nat.card Φ.F = 2) (hr : 5 ≤ Φ.r) (hZ : Subgroup.center ↥Y = ⊥) :
    QTwoMemberFacts Bs (qtwoDelX ψ c g) M (ggAutomizerJoin L Bs 𝒦) e :=
  ⟨ggQTwoDUnit_X_rankOne hL1 hcfg hm hM hbase hcoords hdel,
    ggQTwoDUnit_X_rankTwo hEA hcfg hm hM hbase hcoords hdel,
    ggQTwoDUnit_X_pair hL1 hEA hcfg hm hM hbase hcoords hdel,
    ggQTwoDUnit_X_adjA3 hA3 hEA hcfg hm hM hbase hcoords hdel hXY Φ hF hr hZ,
    ggQTwoDUnit_X_far2 hEA hcfg hm hM hbase hcoords hdel⟩

end CFSG.StandardType.QTwo

end
