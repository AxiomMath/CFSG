module

public import CFSG.RankThree.GF2n.Stroth80.Ext1D4Module
public import CFSG.RankThree.GF2n.Stroth80.Ext1D4Om8Borel
public import CFSG.RankThree.GF2n.Stroth80.Omega8SmallTransfer
public import CFSG.RankThree.GF2n.Stroth80.Sec715LayerSplitInst
public import CFSG.RankThree.GF2n.Stroth80.Sec41iiTensorSetupOfModel
public import CFSG.RankThree.GF2n.Stroth80.Sec7WVMinOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec79MinOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec715TriKegelA

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG.CGT.Timmesfeld75

variable {G : Type} [Group G] {K X Hb : Type} [Field K] [AddCommGroup X] [Module K X] [Group Hb]

namespace IsLayerBridge

variable {V W R : Subgroup G} {act : Hb →* (X ≃ₗ[K] X)} {f : G → X} {bar : ↥R → Hb}
  (hB : IsLayerBridge V W R act f bar)

include hB

@[expose] def preAdd (M : AddSubgroup X) : Subgroup G where
  carrier := {x | x ∈ W ∧ f x ∈ M}
  one_mem' := ⟨W.one_mem, by rw [hB.f_one]; exact M.zero_mem⟩
  mul_mem' := fun {x y} hx hy => ⟨W.mul_mem hx.1 hy.1, by
    rw [hB.f_mul x hx.1 y hy.1]; exact M.add_mem hx.2 hy.2⟩
  inv_mem' := fun {x} hx => ⟨W.inv_mem hx.1, by rw [hB.f_inv hx.1]; exact M.neg_mem hx.2⟩

@[expose] def imAdd (A : Subgroup G) (hAW : A ≤ W) : AddSubgroup X where
  carrier := {v | ∃ a ∈ A, f a = v}
  zero_mem' := ⟨1, A.one_mem, hB.f_one⟩
  add_mem' := by
    rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact ⟨a * b, A.mul_mem ha hb, hB.f_mul a (hAW ha) b (hAW hb)⟩
  neg_mem' := by
    rintro _ ⟨a, ha, rfl⟩
    exact ⟨a⁻¹, A.inv_mem ha, hB.f_inv (hAW ha)⟩

theorem conj_mem_of_conjSubgroup {A : Subgroup G} (hAR : ∀ r ∈ R, conjSubgroup r A = A)
    {r : G} (hr : r ∈ R) {a : G} (ha : a ∈ A) : r * a * r⁻¹ ∈ A := by
  rw [← hAR r hr]
  refine mem_conjSubgroup.mpr ?_
  simpa [mul_assoc] using ha

theorem exists_compl_of_addCompl (A : Subgroup G) (hVA : V ≤ A) (hAW : A ≤ W)
    (hAR : ∀ r ∈ R, conjSubgroup r A = A)
    (hX : ∀ M : AddSubgroup X, (∀ h, ∀ v ∈ M, act h v ∈ M) →
      ∃ M' : AddSubgroup X, IsCompl M M' ∧ ∀ h, ∀ v ∈ M', act h v ∈ M') :
    ∃ A' : Subgroup G, V ≤ A' ∧ A' ≤ W ∧ (∀ r ∈ R, conjSubgroup r A' = A') ∧
      A ⊔ A' = W ∧ A ⊓ A' = V := by
  have hMinv : ∀ h, ∀ v ∈ hB.imAdd A hAW, act h v ∈ hB.imAdd A hAW := by
    rintro h _ ⟨a, ha, rfl⟩
    obtain ⟨r, rfl⟩ := hB.bar_surj h
    rw [← hB.conj_f r a (hAW ha)]
    exact ⟨_, conj_mem_of_conjSubgroup hB hAR r.2 ha, rfl⟩
  obtain ⟨M', hMM', hM'⟩ := hX _ hMinv
  have hdisj : ∀ v, v ∈ hB.imAdd A hAW → v ∈ M' → v = 0 := fun v h1 h2 => by
    have : v ∈ hB.imAdd A hAW ⊓ M' := ⟨h1, h2⟩
    rwa [hMM'.inf_eq_bot, AddSubgroup.mem_bot] at this
  have hcod : ∀ v : X, ∃ a ∈ A, ∃ m ∈ M', f a + m = v := fun v => by
    have hv : v ∈ hB.imAdd A hAW ⊔ M' := by rw [hMM'.sup_eq_top]; trivial
    obtain ⟨_, ⟨a, ha, rfl⟩, m, hm, h⟩ := AddSubgroup.mem_sup.1 hv
    exact ⟨a, ha, m, hm, h⟩
  have hkey : ∀ s : ↥R, ∀ x ∈ hB.preAdd M', (s : G) * x * (s : G)⁻¹ ∈ hB.preAdd M' :=
    fun s x hx => ⟨hB.conj_W s x hx.1, by rw [hB.conj_f s x hx.1]; exact hM' _ _ hx.2⟩
  refine ⟨hB.preAdd M', fun x hx => ⟨hB.V_le_W hx, ?_⟩, fun x hx => hx.1, fun r hr => ?_, ?_, ?_⟩
  · rw [(hB.f_ker x (hB.V_le_W hx)).mpr hx]
    exact M'.zero_mem
  · ext x
    rw [mem_conjSubgroup]
    constructor
    · intro hx
      have := hkey ⟨r, hr⟩ _ hx
      simpa [mul_assoc] using this
    · intro hx
      have := hkey ⟨r⁻¹, R.inv_mem hr⟩ x hx
      simpa [mul_assoc] using this
  · refine le_antisymm (sup_le hAW fun x hx => hx.1) fun x hxW => ?_
    obtain ⟨a, ha, m, hm, hsum⟩ := hcod (f x)
    have hax : a⁻¹ * x ∈ hB.preAdd M' := by
      refine ⟨W.mul_mem (W.inv_mem (hAW ha)) hxW, ?_⟩
      rw [hB.f_mul _ (W.inv_mem (hAW ha)) x hxW, hB.f_inv (hAW ha), ← hsum]
      simpa using hm
    have := Subgroup.mul_mem_sup ha hax
    simpa using this
  · refine le_antisymm (fun x hx => ?_) (le_inf hVA fun x hx => ⟨hB.V_le_W hx, ?_⟩)
    · have h0 := hdisj (f x) ⟨x, hx.1, rfl⟩ hx.2.2
      exact (hB.f_ker x hx.2.1).mp h0
    · rw [(hB.f_ker x (hB.V_le_W hx)).mpr hx]
      exact M'.zero_mem

end IsLayerBridge

section Transfer

open CFSG.Open CFSG.LieType.D4Small CFSG.RankThree.GF2n.Stroth80.Ext1D4 Module

variable {K : Type} [Field K] [Finite K] [CharP K 2] {X : Type} [AddCommGroup X] [Module K X]
  {Hb : Type} [Group Hb]

theorem exists_addCompl_of_omega8 (hNF : Tri.SmallNFStatement) (hq : 4 ≤ Nat.card K)
    (act : Hb →* (X ≃ₗ[K] X)) (φ₈ : Hb →* GL (Fin 4 ⊕ Fin 4) K)
    (hφr : φ₈.range = StatedOmega (StatedQuadPlus 4 K)) (hker : ∀ h, φ₈ h = 1 → act h = 1)
    (hdim : finrank K X = 16)
    (hmin : ∀ U : Submodule K X, IsInvSub act U → U ≠ ⊥ → 8 ≤ finrank K U)
    (M : AddSubgroup X) (hM : ∀ h, ∀ v ∈ M, act h v ∈ M) :
    ∃ M' : AddSubgroup X, IsCompl M M' ∧ ∀ h, ∀ v ∈ M', act h v ∈ M' := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : FiniteDimensional K X := Module.finite_of_finrank_pos (by rw [hdim]; norm_num)
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hq' : 4 ≤ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  have hm : 2 * 2 ^ ((n : ℕ) - 1) = Fintype.card K := by
    rw [hn, ← pow_succ']
    congr 1
    have := n.pos
    omega
  obtain ⟨ρ', hρ'⟩ := exists_statedOmega_factor hφr hker
  set σ := repOm8 ρ' 1 with hσ
  have hσact : ∀ g v, ∃ h, σ g v = act h v := fun g v => by
    have hmem : ((conjOm8 1 g : StatedOmega (StatedQuadPlus 4 K)) : GL (Fin 4 ⊕ Fin 4) K) ∈
        φ₈.range := by
      rw [hφr]
      exact (conjOm8 1 g).2
    obtain ⟨h, hh⟩ := hmem
    have hh' : φ₈ h ∈ StatedOmega (StatedQuadPlus 4 K) := by rw [hh]; exact (conjOm8 1 g).2
    have he : conjOm8 1 g = ⟨φ₈ h, hh'⟩ := Subtype.ext hh.symm
    refine ⟨h, ?_⟩
    rw [hσ, repOm8_apply, he, hρ' h hh']
    rfl
  have hactσ : ∀ h v, ∃ g, act h v = σ g v := fun h v => by
    have hh : φ₈ h ∈ StatedOmega (StatedQuadPlus 4 K) := hφr ▸ ⟨h, rfl⟩
    refine ⟨(conjOm8 1).symm ⟨φ₈ h, hh⟩, ?_⟩
    rw [hσ, repOm8_apply, MulEquiv.apply_symm_apply, hρ' h hh]
    rfl
  have hminσ : ∀ U : Submodule K X, (∀ g, ∀ x ∈ U, σ g x ∈ U) → U ≠ ⊥ → 8 ≤ finrank K U :=
    fun U hU hU0 => hmin U (fun h x hx => by
      obtain ⟨g, hg⟩ := hactσ h x
      rw [hg]
      exact hU g x hx) hU0
  have hMσ : ∀ g, ∀ v ∈ M, σ g v ∈ M := fun g v hv => by
    obtain ⟨h, hh⟩ := hσact g v
    rw [hh]
    exact hM h v hv
  obtain ⟨M', hMM', hM'⟩ := exists_addCompl_of_minDim (om8Datum K) σ hNF hn hm hq'
    (borel_index_ne_zero K) hdim.le hminσ M hMσ
  refine ⟨M', hMM', fun h v hv => ?_⟩
  obtain ⟨g, hg⟩ := hactσ h v
  rw [hg]
  exact hM' g v hv

end Transfer

section Holds

open CFSG CFSG.Open CFSG.Assembly.LowTwoRank

theorem ext1VanishingD4_of_smallNF (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement) (hZc : Sec7ZCardStatement)
    (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (hNF : Tri.SmallNFStatement) :
    Ext1VanishingD4Statement := by
  intro G _ _ M Q Z B hc n t hs hp hn Z0 hZ0 hZN
  haveI : (Q.subgroupOf M).Normal := hc.normal_Q_in_M
  have h310chi := stroth310Chi_of_34 h34
  have hWV := sec7WVMinOrder_of hA hPts h52a h52b
  have h79 := sec79MinOrder_of h51 hA hPts
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  obtain ⟨m, γ, M₀, -, hM⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨ρ, b, hS⟩ := hc.exists_isTensorSetup h34 hs.toSec5.width hs.toSec5.n_gt
    hs.toSec5.noA2 hs.toSec5.gen hM
  obtain ⟨φ₈, -, hφr, hφk, -⟩ := exists_phi8 hS hs.toSec5.mem hp
  have h4 : 4 ≤ Nat.card (GaloisField 2 m) := hS.card ▸ hc.hyp.q4
  refine ⟨fun A hZA hAN hAR => ?_, fun A hVA hAW hAR => ?_⟩
  ·
    exact (isLayerBridge_delta hS h34 hRoot h310chi h51 h52a h52b hNO hZc hCRW hMp hs hr hZ0
      hZN).exists_compl_of_addCompl A hZA hAN hAR fun M' hM' =>
      exists_addCompl_of_omega8 hNF h4 (deltaAct hS hs.toSec5.mem) φ₈ hφr
        (fun h hh => deltaAct_of_mem_CN h310chi h52a hS hs hr h ((hφk h).mp hh))
        (finrank_deltaSub hS h34 hRoot h310chi h51 h52a h52b hNO hZc hCRW hMp hs hr hp hn hZ0
          hZN)
        (fun U hU hU0 => minDim_delta hS h34 hRoot h310chi h51 h52a h52b hNO hZc hCRW hMp h79 hs
          hr hp hZ0 hZN U hU hU0) M' hM'
  ·
    exact (isLayerBridge_wv hS h34 hs).exists_compl_of_addCompl A hVA hAW hAR fun M' hM' =>
      exists_addCompl_of_omega8 hNF h4 (wvAct hS hs.toSec5.mem) φ₈ hφr
        (fun h hh => wvAct_of_mem_CN h310chi h52a hS hs hr h ((hφk h).mp hh))
        (finrank_wvQ hS h34 hs hp hn) (fun U hU hU0 => minDim_wv hS h34 hWV hs hp U hU hU0) M' hM'

theorem ext1VanishingD4_of (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement) (hZc : Sec7ZCardStatement)
    (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) : Ext1VanishingD4Statement :=
  ext1VanishingD4_of_smallNF h34 hRoot h51 h52a h52b hNO hZc hCRW hMp hA hPts Tri.smallNF_holds

end Holds

end CFSG.RankThree.GF2n.Stroth80.S715L
