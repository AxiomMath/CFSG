module

public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerSplitInst
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerPair
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerSplitUntwist
public import CFSG.RankThree.GF2n.Smith81.LinRank
public import CFSG.RankThree.GF2n.Smith81.Sec220Coprime
public import CFSG.RankThree.GF2n.Smith81.Sec220Defs
public import CFSG.RankThree.GF2n.Smith81.Sec220Local
public import CFSG.RankThree.GF2n.Smith81.Sec2Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec10Stmt
public import CFSG.RankThree.GF2n.Stroth80.Sec310Assembly
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClMain
public import CFSG.RankThree.GF2n.Stroth80.Sec310RootMain
public import CFSG.RankThree.GF2n.Stroth80.Sec311Torus
public import CFSG.RankThree.GF2n.Stroth80.Sec51Main
public import CFSG.RankThree.GF2n.Stroth80.Sec78NormZ0
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsE
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1015
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly69
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssemblyFixed
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarFrattini
public import CFSG.RankThree.GF2n.Stroth80.Sec8CentreModel
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

theorem vAct_irred (h34 : Stroth34Statement) (hS : IsTensorSetup hc n M₀ ρ b) {n' : ℕ} {t : G}
    (hs : Sec7Hyp hc n' t) (S : Submodule K ↥(hc.VtSub hS.model t))
    (hSinv : IsInvSub (vAct hS hs.toSec5.mem) S) : S = ⊥ ∨ S = ⊤ := by
  have h35 :=
    (stroth_3_5 h34 hc hs.toSec5.width hs.toSec5.n_gt hs.toSec5.noA2 hs.toSec5.gen).2.1
  have hinv : ∀ x ∈ bar M Q (Rt M (LB M Q B) t), ∀ v ∈ S.map (hc.VtSub hS.model t).subtype,
      (ρ x).toAdd v ∈ S.map (hc.VtSub hS.model t).subtype := by
    intro x hx v hv
    obtain ⟨s, hsS, rfl⟩ := Submodule.mem_map.mp hv
    exact Submodule.mem_map.mpr ⟨vAct hS hs.toSec5.mem ⟨x, hx⟩ s, hSinv _ s hsS, rfl⟩
  have hinj := Submodule.map_injective_of_injective (hc.VtSub hS.model t).injective_subtype
  rcases hc.irred_VtSub hS h35 hs.toSec5.mem _ (Submodule.map_subtype_le _ S) hinv with h | h
  · exact Or.inl (hinj (by rw [h, Submodule.map_bot]))
  · exact Or.inr (hinj (by rw [h, Submodule.map_subtype_top]))

theorem isPairing_layers (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (h52a : Stroth52aStatement) (hCV : Sec7CVStatement) (hS : IsTensorSetup hc n M₀ ρ b)
    {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r)
    (φ₈ : ↥(bar M Q (Rt M (LB M Q B) t)) →* GL (Fin 4 ⊕ Fin 4) K)
    (hφker : ∀ x, φ₈ x = 1 ↔ (x : Mbar M Q) ∈ bar M Q (hc.CN t))
    (e : ↥(hc.VtSub hS.model t) ≃ₗ[K] (Fin 4 ⊕ Fin 4 → K))
    (he : ∀ (x : ↥(bar M Q (Rt M (LB M Q B) t))) (w : ↥(hc.VtSub hS.model t)),
      e ⟨(ρ (x : Mbar M Q)).toAdd w, hc.act_mem_VtSub hS hs.toSec5.mem _ x.2 _ w.2⟩ =
        (φ₈ x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) K) *ᵥ e w) :
    IsPairing φ₈ (vAct hS hs.toSec5.mem) (wvAct hS hs.toSec5.mem) (deltaAct hS hs.toSec5.mem) e
      (betaQ h310chi h52a hS hs hr) where
  he x w := he x w
  irr := vAct_irred h34 hS hs
  kerM x hx := wvAct_of_mem_CN h310chi h52a hS hs hr x ((hφker x).mp hx)
  kerN x hx := deltaAct_of_mem_CN h310chi h52a hS hs hr x ((hφker x).mp hx)
  equiv := betaQ_equivariant h310chi h52a hS hs hr
  left _ hm := betaQ_eq_zero_left h310chi h52a hS hs hr hCV hm
  right _ hf := betaQ_eq_zero_right h310chi h52a hS hs hr hf

theorem sec715LayerSplit_of (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement) (hZc : Sec7ZCardStatement)
    (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement) (hCV : Sec7CVStatement)
    (hA : Sec7AExistsStatement) (hExt : Ext1VanishingD4Statement)
    (hRoot8 : Omega8LongRootRankStatement) (hWV : Sec7WVMinOrderStatement)
    (h79 : Sec79MinOrderStatement) : Sec715LayerSplitStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp hn Z0 hZ0 hZN K _ _ γ M₀ ρ b hS φ₈ hφ hφker e he
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  obtain ⟨k, -, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hS.card.trans hZ2)
  have hq : 4 ≤ Nat.card K := by
    rw [hS.card]
    exact hc.hyp.q4
  exact (isPairing_layers h34 h310chi h52a hCV hS hs hr φ₈ hφker e he).isLayerSplit hRoot8 hq hφ
    (minDim_wv hS h34 hWV hs hp) (finrank_wvQ hS h34 hs hp hn) (proj_wv hS h34 hExt hs hp hn hZ0 hZN)
    (minDim_delta hS h34 hRoot h310chi h51 h52a h52b hNO hZc hCRW hMp h79 hs hr hp hZ0 hZN)
    (finrank_deltaSub hS h34 hRoot h310chi h51 h52a h52b hNO hZc hCRW hMp hs hr hp hn hZ0 hZN)
    (proj_delta hS h34 hRoot h310chi h51 h52a h52b hNO hZc hCRW hMp hExt hs hr hp hn hZ0 hZN)

end CFSG.RankThree.GF2n.Stroth80.S715L
