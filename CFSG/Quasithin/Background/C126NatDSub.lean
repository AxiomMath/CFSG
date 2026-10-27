module

public import CFSG.Quasithin.Background.C126NatDMin
public import CFSG.Quasithin.Background.C1PackSubnormal

public section

namespace CFSG.Quasithin.C126.Nat

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin B2F E2

variable {G : Type} [Group G] [Finite G]

section Residual

theorem mem_normalizer_twoResidual {W : Subgroup G} {x : G}
    (hx : x ∈ Subgroup.normalizer (W : Set G)) :
    x ∈ Subgroup.normalizer (twoResidual W : Set G) := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.2
  have h1 := E1.map_twoResidual (MulAut.conj x).toMonoidHom W
  have h2 := Subgroup.mem_normalizer_iff_map_conj_eq.1 hx
  exact h1.trans (congrArg twoResidual h2)

theorem twoResidual_twoResidual (W : Subgroup G) :
    twoResidual (twoResidual W) = twoResidual W := by
  apply le_antisymm (twoResidual_le _)
  have hBW : twoResidual W ≤ W := twoResidual_le W
  have hWn : W ≤ Subgroup.normalizer (twoResidual (twoResidual W) : Set G) := fun x hx =>
    mem_normalizer_twoResidual (le_normalizer_twoResidual W hx)
  have h2 : ∀ w ∈ W, ∃ k : ℕ, w ^ 2 ^ k ∈ twoResidual (twoResidual W) := by
    intro w hw
    obtain ⟨a, ha⟩ := twoResidual_isTwoQuotient W w hw
    obtain ⟨b, hb⟩ := twoResidual_isTwoQuotient (twoResidual W) _ ha
    exact ⟨a + b, by rw [pow_add, pow_mul]; exact hb⟩
  exact twoResidual_le_of_isTwoQuotient ((twoResidual_le _).trans hBW) hWn h2

theorem le_twoResidual_of_noTwoQuotient {X W : Subgroup G} (hXW : X ≤ W)
    (hX : ∀ (N : Subgroup ↥X) [N.Normal], IsPGroup 2 (↥X ⧸ N) → N = ⊤) :
    X ≤ twoResidual W := by
  set N : Subgroup ↥X := (twoResidual W).subgroupOf X with hN
  have hNn : N.Normal := by
    refine ⟨fun n hn g => ?_⟩
    show ((g : G) * n * (g : G)⁻¹) ∈ twoResidual W
    exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_twoResidual W (hXW g.2)) n).mp hn
  have hp : IsPGroup 2 (↥X ⧸ N) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H b =>
      obtain ⟨k, hk⟩ := twoResidual_isTwoQuotient W b (hXW b.2)
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hk
  have htop := hX N hp
  intro b hb
  have : (⟨b, hb⟩ : ↥X) ∈ N := htop ▸ Subgroup.mem_top _
  exact this

end Residual

namespace NatCtx

variable {H T M V : Subgroup G} {hV : IsElemAbelian 2 V}
  {I : Finset (Subgroup (MulAut (IntMod V hV)))} (c : NatCtx H T M V hV I)

include c in
theorem le_normalizer_KS :
    H ≤ Subgroup.normalizer ((twoResidual H ⊔ baum T : Subgroup G) : Set G) := by
  have hTbaum : T ≤ Subgroup.normalizer (baum T : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
  have hTn : T ≤ Subgroup.normalizer ((twoResidual H ⊔ baum T : Subgroup G) : Set G) :=
    fun t ht => C1.mem_normalizer_sup (le_normalizer_twoResidual H (c.min.isSylow.1 ht))
      (hTbaum ht)
  have hKn : twoResidual H ≤ Subgroup.normalizer ((twoResidual H ⊔ baum T : Subgroup G) : Set G) :=
    le_sup_left.trans Subgroup.le_normalizer
  exact (sup_twoResidual_eq c.min.isSylow).symm.le.trans (sup_le hTn hKn)

omit [Finite G] in
include c in
theorem KS_le_normalizer_K :
    twoResidual H ⊔ baum T ≤ Subgroup.normalizer (twoResidual H : Set G) :=
  sup_le Subgroup.le_normalizer fun _ hx =>
    le_normalizer_twoResidual H ((inf_le_left.trans c.min.isSylow.1) hx)

include c in
theorem twoResidual_le_K {W : Subgroup G} (hW : W ≤ twoResidual H ⊔ baum T) :
    twoResidual W ≤ twoResidual H := by
  have hKSnK := c.KS_le_normalizer_K
  have hN : W ≤ Subgroup.normalizer ((W ⊓ twoResidual H : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hKSnK (hW hx)⟩
  have h2 : ∀ y ∈ W, ∃ k : ℕ, y ^ 2 ^ k ∈ W ⊓ twoResidual H := fun y hy => by
    obtain ⟨k, hk⟩ := B6.isTwoQuotient_of_sup_eq c.syl.2.1 hKSnK (sup_comm _ _) y (hW hy)
    exact ⟨k, W.pow_mem hy _, hk⟩
  exact (twoResidual_le_of_isTwoQuotient inf_le_left hN h2).trans inf_le_right

include c in
theorem kerK_le_baum (hRF : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) :
    twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ baum T := by
  have hSH : baum T ≤ H := inf_le_left.trans c.min.isSylow.1
  have hKSH : twoResidual H ⊔ baum T ≤ H := sup_le (twoResidual_le H) hSH
  intro x hx
  have hxO : x ∈ pCoreOf 2 H := hRF hx
  have hxKS : x ∈ twoResidual H ⊔ baum T := Subgroup.mem_sup_left hx.1
  have hnorm : twoResidual H ⊔ baum T ≤
      Subgroup.normalizer ((pCoreOf 2 H ⊓ (twoResidual H ⊔ baum T) : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hKSH hg), Subgroup.le_normalizer hg⟩
  exact B6.pCoreOf_two_le_of_isSylowTwoOf c.syl
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left) ⟨hxO, hxKS⟩)

include c in
theorem isSubnormal_K1 (hRF : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H)
    {P : Subgroup G} (hSP : baum T ≤ P) (hPK : P ≤ twoResidual H ⊔ baum T)
    {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) (hρ : autI hV (twoResidual P) = L)
    (hshort : ∀ (N : Subgroup ↥(twoResidual P)) [N.Normal],
      IsPGroup 2 (↥(twoResidual P) ⧸ N) → N = ⊤) :
    ((twoResidual P).subgroupOf H).IsSubnormal := by
  have hHN := c.hHN
  have hSH : baum T ≤ H := inf_le_left.trans c.min.isSylow.1
  have hKSH : twoResidual H ⊔ baum T ≤ H := sup_le (twoResidual_le H) hSH
  have hKSN : twoResidual H ⊔ baum T ≤ Subgroup.normalizer (V : Set G) := hKSH.trans hHN
  have hρKS : autI hV (twoResidual H ⊔ baum T) ≤ Subgroup.normalizer (L : Set _) :=
    (c.rho_le le_rfl).trans (c.iSup_le_normalizer hL)
  set W : Subgroup G := preI hV (twoResidual H ⊔ baum T) hKSN L with hW
  have hWKS : W ≤ twoResidual H ⊔ baum T := preI_le hV
  have hKW : twoResidual P ≤ W := fun x hx => (mem_preI hV).2
    ⟨hPK (twoResidual_le P hx), hρ ▸ convI_mem_autI hV hx (hKSN (hPK (twoResidual_le P hx)))⟩
  have hWnorm : twoResidual H ⊔ baum T ≤ Subgroup.normalizer (W : Set G) := fun g hg => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => conj_mem_preI hV hKSN hρKS hg hy, fun hy => ?_⟩
    have := conj_mem_preI hV hKSN hρKS ((twoResidual H ⊔ baum T).inv_mem hg) hy
    simpa [mul_assoc] using this
  set B : Subgroup G := twoResidual W with hB
  have hKB : twoResidual P ≤ B := le_twoResidual_of_noTwoQuotient hKW hshort
  have hBK : B ≤ twoResidual H := c.twoResidual_le_K hWKS
  have hS2 : IsPGroup 2 ↥(baum T) := c.min.isSylow.2.1.to_le inf_le_left
  have hdec : ∀ b ∈ B, ∃ k ∈ twoResidual P, ∃ r ∈ baum T ⊓ B, b = k * r := by
    intro b hb
    obtain ⟨hbKS, hbL⟩ := (mem_preI hV).1 (twoResidual_le W hb)
    have hbL' : convI hV ⟨b, hKSN hbKS⟩ ∈ autI hV (twoResidual P) := by
      rw [hρ]
      exact hbL
    obtain ⟨k, hk, hkb⟩ := (mem_autI hV).1 hbL'
    have h1 : convI hV (k⁻¹ * ⟨b, hKSN hbKS⟩) = 1 := by
      rw [map_mul, map_inv, ← hkb, inv_mul_cancel]
    have h2 : (k : G)⁻¹ * b ∈ Subgroup.centralizer (V : Set G) := (convI_eq_one_iff hV _).1 h1
    have hrB : (k : G)⁻¹ * b ∈ B := B.mul_mem (B.inv_mem (hKB hk)) hb
    exact ⟨k, hk, (k : G)⁻¹ * b, ⟨c.kerK_le_baum hRF ⟨hBK hrB, h2⟩, hrB⟩, by group⟩
  have hBnorm : B ≤ Subgroup.normalizer (twoResidual P : Set G) := by
    intro b hb
    obtain ⟨k, hk, r, hr, rfl⟩ := hdec b hb
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hk)
      (le_normalizer_twoResidual P (hSP hr.1))
  have hsup : (baum T ⊓ B) ⊔ twoResidual P = B := by
    apply le_antisymm
    · exact sup_le inf_le_right hKB
    · intro b hb
      obtain ⟨k, hk, r, hr, rfl⟩ := hdec b hb
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hk) (Subgroup.mem_sup_left hr)
  have h2q := B6.isTwoQuotient_of_sup_eq (hS2.to_le (inf_le_left : baum T ⊓ B ≤ baum T))
    hBnorm hsup
  have hBleK : B ≤ twoResidual P := by
    have := twoResidual_le_of_isTwoQuotient hKB hBnorm h2q
    rwa [hB, twoResidual_twoResidual] at this
  have hBeq : B = twoResidual P := le_antisymm hBleK hKB
  have hBKS : B ≤ twoResidual H ⊔ baum T := hBK.trans le_sup_left
  have hBn : twoResidual H ⊔ baum T ≤ Subgroup.normalizer (B : Set G) := fun x hx =>
    mem_normalizer_twoResidual (hWnorm hx)
  have hBnormal : (B.subgroupOf (twoResidual H ⊔ baum T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBKS).2 hBn
  have hKSnormal : ((twoResidual H ⊔ baum T).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKSH).2 c.le_normalizer_KS
  rw [← hBeq]
  exact C1Pack.isSubnormal_subgroupOf_trans' hBKS hKSH hBnormal.isSubnormal
    hKSnormal.isSubnormal

end NatCtx

end CFSG.Quasithin.C126.Nat
