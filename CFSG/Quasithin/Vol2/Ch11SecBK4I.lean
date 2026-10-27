module

public import CFSG.Quasithin.Vol2.Ch11G2Q8LineGen
public import CFSG.Quasithin.Vol2.Ch11SecBK4C
public import CFSG.Quasithin.Vol2.Ch11SecBK4F

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Quasithin CFSG.Quasithin.JonesParshall
open CFSG.Open (quasithinG2 IsElemAbelian)
open scoped IsMulCommutative

namespace BK4

variable {G : Type} [Group G] {L V : Subgroup G} {n : ℕ} {K : Type} [Field K]

theorem rootInv_g2 [Finite G] [IsMulCommutative ↥V] [Finite K] [CharP K 2]
    (hV : IsElemAbelian 2 V) (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hVL : ⁅V, L⁆ = V)
    (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    {π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* ↥(autOn L V)} {f : ↥V → (Ix3 → K)}
    (hf : KGNat.IsCoord (G2Q8.lmG K) (autOn L V)
      ((Subgroup.centralizer (L : Set G)).subgroupOf V) π f)
    {T : Subgroup G} (hTS : QuasithinUnique.IsSylowTwoOf T (L ⊔ T))
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) {x : G}
    (hxV : x ∈ Subgroup.normalizer (V : Set G)) (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hx1 : x ∉ Subgroup.centralizer (V : Set G))
    (hx2 : SecA.conjV V x hxV * SecA.conjV V x hxV = 1)
    (hm : E3.mQuot V (V ⊓ Subgroup.centralizer ({x} : Set G)) = 2 * n) :
    ∃ W : Subgroup G, W ≤ V ⊓ Subgroup.centralizer ({x} : Set G) ∧ ∃ g ∈ L,
      V ⊓ Subgroup.centralizer (L : Set G) ≤ conjSubgroup W g ∧
      IsEndStable L V (V ⊓ Subgroup.centralizer (L : Set G)) (conjSubgroup W g) ∧
      (V ⊓ Subgroup.centralizer (L : Set G)).relIndex (conjSubgroup W g) = 2 ^ (n * 3) ∧
      T ⊓ L ≤ Subgroup.normalizer (conjSubgroup W g : Set G) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hsq : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hV.2 w w.2)
  obtain ⟨c₀, hc0, hc1⟩ := G2Q8.exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨c, γ, σ, hc, hact⟩ := G2Q8.exists_smul_frob_conjV
    (X := Subgroup.normalizer (L : Set G)) hf hc0 hc1 hK hn inf_le_left (e := x) ⟨hxL, hxV⟩
  let T' : (Ix3 → K) →+ (Ix3 → K) :=
    { toFun := fun y => c • g2Act γ (G2Q8.frobQ (σ : K →+* K) y)
      map_zero' := by
        have : G2Q8.frobQ (σ : K →+* K) 0 = 0 := funext fun j => map_zero σ
        rw [this, map_zero, smul_zero]
      map_add' := fun y y' => by
        have : G2Q8.frobQ (σ : K →+* K) (y + y') =
            G2Q8.frobQ (σ : K →+* K) y + G2Q8.frobQ (σ : K →+* K) y' :=
          funext fun j => map_add σ (y j) (y' j)
        simp only [this, map_add, smul_add] }
  have hT : ∀ w, f (SecA.conjV V x hxV w) = T' (f w) := hact
  have hsemi : ∀ (a : K) (y : Ix3 → K), T' (a • y) = (σ : K →+* K) a • T' y := by
    intro a y
    show c • g2Act γ (G2Q8.frobQ (σ : K →+* K) (a • y)) =
      (σ : K →+* K) a • (c • g2Act γ (G2Q8.frobQ (σ : K →+* K) y))
    rw [G2Q8.frobQ_smul, G2Q8.g2Act_smul, smul_comm]
  have hm' := hm
  rw [mQuot_inf_centralizer hxV] at hm'
  have hC : ∀ w ∈ fixV (Subgroup.zpowers (SecA.conjV V x hxV)), T' (f w) = f w :=
    fun w hw => by rw [← hT, mem_fixV_zpowers.mp hw]
  have hM := card_fun_six hK
  have hlow := two_pow_le_card_fix hV hf hC hM hm'
  have hlow' : 2 ^ (4 * n) ≤ Nat.card {z : Ix3 → K // T' z = z} := by
    rw [show 6 * n = 2 * n + 4 * n by ring, pow_add] at hlow
    exact Nat.le_of_mul_le_mul_left hlow (by positivity)
  have hσ : ∀ θ, σ θ = θ := by
    by_contra h
    simp only [not_forall] at h
    obtain ⟨θ, hθ⟩ := h
    have h1 := G2Q8.card_fix_sq_le T' (σ : K →+* K) hθ hsemi
    have h3 := (Nat.pow_le_pow_left hlow' 2).trans h1
    rw [hM, ← pow_mul] at h3
    have := (Nat.pow_le_pow_iff_right (by norm_num)).mp h3
    omega
  have hT' : ∀ y, T' y = c • g2Act γ y := fun y => by
    show c • g2Act γ (G2Q8.frobQ (σ : K →+* K) y) = _
    congr 2
    exact funext fun j => hσ (y j)
  have hsq' : ∀ y, c • g2Act γ (c • g2Act γ y) = y := by
    intro y
    obtain ⟨w, rfl⟩ := hf.surj y
    have h1 := congrArg (fun φ : MulAut ↥V => f (φ w)) hx2
    simp only [MulAut.mul_apply, MulAut.one_apply] at h1
    rwa [hT, hT, hT', hT'] at h1
  have hγγ : ∀ y, g2Act (γ * γ) y = (c * c)⁻¹ • y := by
    intro y
    have h1 := hsq' y
    rw [G2Q8.g2Act_smul, smul_smul, ← G2Q8.g2Act_mul_apply] at h1
    calc g2Act (γ * γ) y = (c * c)⁻¹ • ((c * c) • g2Act (γ * γ) y) := by
          rw [smul_smul, inv_mul_cancel₀ (mul_ne_zero hc hc), one_smul]
      _ = (c * c)⁻¹ • y := by rw [h1]
  have hcc : (c * c)⁻¹ = 1 := G2Q8.scalar_eq_one hγγ
  have hc1' : c = 1 := by
    have hcc' : c * c = 1 := by
      have := congrArg (·⁻¹) hcc
      simpa using this
    have h4 : (c + 1) * (c + 1) = 0 := by linear_combination hcc' + (1 + c) * h2
    have h5 := mul_self_eq_zero.mp h4
    linear_combination h5 - h2
  have hTγ : ∀ y, T' y = g2Act γ y := fun y => by rw [hT', hc1', one_smul]
  have hγ2 : γ * γ = 1 := G2Q8.cayley_eq_one fun y => by rw [hγγ, hcc, one_smul]
  have hγ1 : γ ≠ 1 := by
    rintro rfl
    refine hx1 (mem_centralizer_of_g2 hLV hVL hf hc0 hc1 hxV hxL fun v => ?_)
    rw [hT, hTγ, map_one]
    rfl
  have hfixγ : ∀ y, T' y = y ↔ y ∈ G2Q8.fixQ γ := fun y => by rw [G2Q8.mem_fixQ, hTγ]
  have hcardC : Nat.card {z : Ix3 → K // T' z = z} = Nat.card (G2Q8.fixQ γ) :=
    Nat.card_congr (Equiv.subtypeEquivRight hfixγ)
  have hup : Nat.card {z : Ix3 → K // T' z = z} ≤ 2 ^ (4 * n) := by
    rw [hcardC]
    have h1 := B42G2.card_fixQ_le hγ2 hγ1
    rwa [hK, ← pow_mul, mul_comm] at h1
  obtain ⟨h, rfl⟩ := G2Q8.eq_conj_tL_of_fix hγ2 hγ1 (by
    rw [← hcardC, hK, ← pow_mul, mul_comm]
    exact hlow')
  set S : Submodule K (Ix3 → K) := G2Q8.gmapG h (G2Q8.stdF K 3) with hS
  set W : Subgroup G := (hf.pre S.toAddSubgroup).map V.subtype with hW
  have hWV : W ≤ V := by
    rintro _ ⟨v, -, rfl⟩
    exact v.2
  have hWsub : W.subgroupOf V = hf.pre S.toAddSubgroup :=
    Subgroup.comap_map_eq_self_of_injective V.subtype_injective _
  have hfull : ∀ w : ↥V, T' (f w) = f w → w ∈ fixV (Subgroup.zpowers (SecA.conjV V x hxV)) :=
    fun w hw => mem_of_rkIdx_add_le hV hf hC hM hup (by omega) hw
  have hWx : W ≤ V ⊓ Subgroup.centralizer ({x} : Set G) := by
    rintro _ ⟨v, hv, rfl⟩
    have hv' : f v ∈ S := hv
    have h1 : v ∈ (V ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf V := by
      rw [inf_centralizer_subgroupOf hxV]
      refine hfull v ?_
      rw [hTγ, G2Q8.g2Act_mul_apply, G2Q8.g2Act_mul_apply]
      have h3 : g2Act h⁻¹ (f v) ∈ G2Q8.stdF K 3 := G2Q8.mem_gmapG.mp hv'
      obtain ⟨a1, a2, a3⟩ := G2Q8.mem_stdF_three.mp h3
      rw [G2Q8.g2Act_tL_of_inC 1 ⟨a2, a3⟩, G2Q8.g2Act_apply_inv]
    exact h1
  have hTL' : QuasithinUnique.IsSylowTwoOf (T ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hTS le_sup_left (sup_le Subgroup.le_normalizer hTL)
  obtain ⟨g₀, hg₀⟩ := G2Q8.exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1
    (SecA.isSylowTwoOf_autOn hLV hTL')
  obtain ⟨l, hl, hlV, hlA⟩ :=
    SecA.mem_autOn_iff.mp (G2Q8.rhoG hc0 hc1 π (h * g₀⁻¹)).2
  have hW'V : conjSubgroup W l ≤ V := G2Q8.conjSubgroup_le_of_le hWV hlV
  have hW' := G2Q8.subgroupOf_conjSubgroup_eq hf hc0 hc1 hWsub hlV hlA
  rw [show (h * g₀⁻¹)⁻¹ * h = g₀ by group] at hW'
  have hfl := G2Q8.isFlagW_preG hsq hf hc0 hc1 hg₀ (G2Q8.stdF_stable 3)
    (G2Q8.card_stdF (by norm_num : 3 ≤ 6))
  rw [← hW', hK] at hfl
  exact ⟨W, hWx, l, hl, flag_conclusions hLV hW'V hfl⟩

end BK4

end CFSG.Quasithin.Vol2.Ch11.SecB
