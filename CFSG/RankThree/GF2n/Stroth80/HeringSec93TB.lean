module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec91Pts
public import CFSG.RankThree.GF2n.Stroth80.HeringSec95CN6
public import CFSG.RankThree.GF2n.Stroth80.Sec101SLVec
public import CFSG.RankThree.GF2n.Stroth80.Sec79Split
public import CFSG.RankThree.GF2n.Stroth80.Sec123Order
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.RankThree.GF2n.Stroth80.HeringSec93TGrp

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
  CFSG.RankThree.GF2n.Smith81
open CFSG.Open.StatedAPI
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

namespace HS9

theorem sup_inf_sup_eq_of_not_le (hc : Ctx M Q Z B) {B' : Subgroup G} (hc' : Ctx M Q Z B')
    (h : ¬ B' ≤ B ⊔ Z) : (B ⊔ Z) ⊓ (B' ⊔ Z) = Z := by
  refine le_antisymm ?_ (le_inf le_sup_right le_sup_right)
  intro w hw
  by_contra hwZ
  have hw1 : w ≠ 1 := fun h1 => hwZ (h1 ▸ Z.one_mem)
  obtain ⟨p, hpQ, hwp⟩ := hc.exists_mem_conj_of_mem_sup hw.1 hwZ
  obtain ⟨p', hp'Q, hwp'⟩ := hc'.exists_mem_conj_of_mem_sup hw.2 hwZ
  obtain ⟨g, hg⟩ := hc.conj
  obtain ⟨g', hg'⟩ := hc'.conj
  have hX : IsZConjugate Z (conjSubgroup p B) := ⟨p * g, by rw [hg, conjSubgroup_mul]⟩
  have hY : IsZConjugate Z (conjSubgroup p' B') := ⟨p' * g', by rw [hg', conjSubgroup_mul]⟩
  have heq : conjSubgroup p B = conjSubgroup p' B' :=
    IsZConjugate.eq_of_mem hc.hyp hX hY hw1 hwp hwp'
  have hB'eq : B' = conjSubgroup (p'⁻¹ * p) B := by
    have h1 := congrArg (conjSubgroup p'⁻¹) heq
    simp only [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h1
    exact h1.symm
  have hQ : p'⁻¹ * p ∈ Q := Q.mul_mem (Q.inv_mem hp'Q) hpQ
  have hle : B' ≤ B ⊔ Z := by
    rw [hB'eq]
    calc conjSubgroup (p'⁻¹ * p) B ≤ conjSubgroup (p'⁻¹ * p) (B ⊔ Z) :=
          Subgroup.map_mono le_sup_left
      _ = B ⊔ Z := hc.conj_sup_Z_of_mem_Q hQ
  exact h hle

theorem not_le_sup_Z_of_ne (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M)
    (hne : LB M Q B ≠ conjSubgroup h (LB M Q B)) : ¬ conjSubgroup h B ≤ B ⊔ Z := by
  intro hle
  have hc' : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  obtain ⟨p, hpQ, hpB⟩ := hc.exists_conj_of_le_ZB hc' (by rw [sup_comm]; exact hle)
  have hpM : p ∈ M := hc.hyp.Q_normal.1 hpQ
  apply hne
  have h1 : conjSubgroup p (LB M Q B) = LB M Q B :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer (sec39_Q_le_LB hpQ))
  calc LB M Q B = conjSubgroup p (LB M Q B) := h1.symm
    _ = LB M Q (conjSubgroup p B) := (hc.LB_conj hpM).symm
    _ = LB M Q (conjSubgroup h B) := by rw [hpB]
    _ = conjSubgroup h (LB M Q B) := hc.LB_conj hh

theorem LB_le_normalizer_inf_CN (hc : Ctx M Q Z B) {t : G} (ht : t ∈ LB M Q B) :
    LB M Q B ≤ Subgroup.normalizer ((LB M Q B ⊓ hc.CN t : Subgroup G) : Set G) := by
  have key : ∀ z ∈ LB M Q B, ∀ y ∈ LB M Q B ⊓ hc.CN t,
      z * y * z⁻¹ ∈ LB M Q B ⊓ hc.CN t := by
    intro z hz y hy
    exact ⟨(LB M Q B).mul_mem ((LB M Q B).mul_mem hz hy.1) ((LB M Q B).inv_mem hz),
      hc.CN_conj_mem ht (le_Rt (M := M) (LB M Q B) ht hz) hy.2⟩
  intro x hxL
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key x hxL y, fun hy => ?_⟩
  have := key x⁻¹ ((LB M Q B).inv_mem hxL) _ hy
  rwa [show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y by group] at this

theorem exists_mem_inf_CN_not_mem_Q (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ}
    {t : G} (hs : Sec9Hyp hc n t) (hn5 : 5 ≤ n) {H' F : Subgroup G} (hHL : H' ≤ LB M Q B)
    (hFL : F.relIndex (LB M Q B) ≤ Nat.card Z) (hFH : F ⊓ LB M Q B ≤ H')
    (hH : H' ⊔ (LB M Q B ⊓ hc.CN t) = LB M Q B) : ∃ x ∈ H' ⊓ hc.CN t, x ∉ Q := by
  by_contra hcon
  push Not at hcon
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hLcard : Nat.card ↥(LB M Q B) = Nat.card ↥Q * Nat.card Z ^ (n - 1) :=
    (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.2.1
  have hrel : (hc.CN t).relIndex (LB M Q B) = Nat.card Z ^ 2 := relIndex_LB_CN h34 hs
  have h1 : (hc.CN t).relIndex (LB M Q B) * Nat.card ↥(hc.CN t ⊓ LB M Q B) =
      Nat.card ↥(LB M Q B) := Subgroup.relIndex_mul_card _ _
  rw [hrel, inf_comm] at h1
  have hHn : H' ≤ Subgroup.normalizer ((LB M Q B ⊓ hc.CN t : Subgroup G) : Set G) :=
    fun x hx => LB_le_normalizer_inf_CN hc ht (hHL hx)
  have hA := card_sup_mul_card_inf_of_le_normalizer hHn
  rw [hH] at hA
  have hesmall : Nat.card ↥(H' ⊓ (LB M Q B ⊓ hc.CN t)) ≤ Nat.card ↥Q := by
    apply Subgroup.card_le_of_le
    intro x hx
    exact hcon x ⟨hx.1, hx.2.2⟩
  have h2 : F.relIndex (LB M Q B) * Nat.card ↥(F ⊓ LB M Q B) = Nat.card ↥(LB M Q B) :=
    Subgroup.relIndex_mul_card F (LB M Q B)
  have h3 : Nat.card ↥(F ⊓ LB M Q B) ≤ Nat.card ↥H' := Subgroup.card_le_of_le hFH
  have hLle : Nat.card ↥(LB M Q B) ≤ Nat.card Z * Nat.card ↥H' := by
    rw [← h2]
    exact Nat.mul_le_mul hFL h3
  have hcpos : 0 < Nat.card ↥(LB M Q B ⊓ hc.CN t) := Nat.card_pos
  have hqpos : 0 < Nat.card Z := by omega
  have hQpos : 0 < Nat.card ↥Q := Nat.card_pos
  have hqe : Nat.card Z ^ 2 * Nat.card ↥(H' ⊓ (LB M Q B ⊓ hc.CN t)) = Nat.card ↥H' := by
    have : (Nat.card Z ^ 2 * Nat.card ↥(H' ⊓ (LB M Q B ⊓ hc.CN t))) *
        Nat.card ↥(LB M Q B ⊓ hc.CN t) = Nat.card ↥H' * Nat.card ↥(LB M Q B ⊓ hc.CN t) := by
      rw [← hA, ← h1]
      ring
    exact Nat.eq_of_mul_eq_mul_right hcpos this
  have hup : Nat.card ↥(LB M Q B) ≤ Nat.card Z ^ 3 * Nat.card ↥Q := by
    calc Nat.card ↥(LB M Q B) ≤ Nat.card Z * Nat.card ↥H' := hLle
      _ = Nat.card Z * (Nat.card Z ^ 2 *
            Nat.card ↥(H' ⊓ (LB M Q B ⊓ hc.CN t))) := by rw [hqe]
      _ ≤ Nat.card Z * (Nat.card Z ^ 2 * Nat.card ↥Q) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hesmall)
      _ = Nat.card Z ^ 3 * Nat.card ↥Q := by ring
  have hpow : Nat.card Z ^ 4 ≤ Nat.card Z ^ (n - 1) :=
    Nat.pow_le_pow_right hqpos (by omega)
  have hlow : Nat.card Z ^ 4 * Nat.card ↥Q ≤ Nat.card ↥(LB M Q B) := by
    rw [hLcard, mul_comm (Nat.card ↥Q)]
    exact Nat.mul_le_mul_right _ hpow
  have h3pos : 0 < Nat.card Z ^ 3 := pow_pos hqpos 3
  have h4 : Nat.card Z ^ 3 * Nat.card Z * Nat.card ↥Q ≤ Nat.card Z ^ 3 * 1 * Nat.card ↥Q := by
    calc Nat.card Z ^ 3 * Nat.card Z * Nat.card ↥Q = Nat.card Z ^ 4 * Nat.card ↥Q := by ring
      _ ≤ Nat.card ↥(LB M Q B) := hlow
      _ ≤ Nat.card Z ^ 3 * Nat.card ↥Q := hup
      _ = Nat.card Z ^ 3 * 1 * Nat.card ↥Q := by ring
  have h5 := Nat.le_of_mul_le_mul_right h4 hQpos
  have h6 := Nat.le_of_mul_le_mul_left h5 h3pos
  omega

theorem polar_mulVec_eq_zero_of_sub_mem {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι]
    [DecidableEq ι] {Q' : QuadraticForm K (ι → K)} {g : Matrix ι ι K}
    (hg : ∀ x, Q' (g *ᵥ x) = Q' x) {u : ι → K} (hu : Q' u = 0) {x : ι → K} (c : K)
    (hx : g *ᵥ x - x = c • u) : polar Q' x (g *ᵥ x) = 0 := by
  have e : g *ᵥ x = x + c • u := by
    rw [← hx]
    abel
  have h1 := hg x
  rw [e, QuadraticMap.map_add (⇑Q') x (c • u)] at h1
  have h2 : Q' (c • u) = 0 := by rw [QuadraticMap.map_smul, hu, smul_zero]
  have h3 : polar Q' x (c • u) = 0 := by
    rw [h2, add_zero] at h1
    exact add_eq_left.mp h1
  rw [e, QuadraticMap.polar_add_right Q' x x (c • u), h3, add_zero, QuadraticMap.polar_self,
    two_nsmul]
  exact CharTwo.add_self_eq_zero _

theorem exists_comm_not_mem_sup_Z (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) :
    ∃ y ∈ LB M Q B, ∃ v ∈ Vt M (LB M Q B) B Z t, ⁅y, v⁆ ∉ B ⊔ Z := by
  classical
  obtain ⟨K, fK, finK, hch, E, hn, φ, ψ, u, P⟩ := exists_pts91 h34 hs
  haveI := hn
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hQnd := nondegenerate_polarBilin_quadPlus 2 K
  have h4 : 4 ≤ Fintype.card (Fin 2 ⊕ Fin 2) := by
    rw [Fintype.card_sum, Fintype.card_fin]
  obtain ⟨u₁, hu₁⟩ : ∃ u₁ : Fin 2 ⊕ Fin 2 → K, polar (quadPlus 2 K) u₁ u ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact P.ne_zero (hQnd.2 u hcon)
  obtain ⟨y, hyL, x, hx⟩ := exists_nonA2_of_map_Lom E hQnd h4 φ P.sing hu₁ P.root
  have hyLB : (y : G) ∈ LB M Q B := Subgroup.mem_subgroupOf.mp hyL
  have hVR := hc.Rt_normalizes_Vt ht
  obtain ⟨vq, hvq⟩ := QuotientGroup.mk_surjective (ψ.symm (Multiplicative.ofAdd x))
  have hsv : secVec ψ vq = x := by
    unfold secVec
    rw [hvq]
    simp
  refine ⟨(y : G), hyLB, (vq : G), vq.2, fun hmem => ?_⟩
  have hw : (y : G) * (vq : G) * (y : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    (Subgroup.mem_normalizer_iff.mp (hVR y.2) (vq : G)).mp vq.2
  have hact := P.act y vq ⟨_, hw⟩ rfl
  have hcommE : ⁅(y : G), (vq : G)⁆ = ((y : G) * (vq : G) * (y : G)⁻¹) * (vq : G)⁻¹ := by
    rw [commutatorElement_def]
  have hcmV : ⁅(y : G), (vq : G)⁆ ∈ Vt M (LB M Q B) B Z t := by
    rw [hcommE]
    exact (Vt M (LB M Q B) B Z t).mul_mem hw ((Vt M (LB M Q B) B Z t).inv_mem vq.2)
  have hvec : secVec ψ (⟨_, hcmV⟩ : ↥(Vt M (LB M Q B) B Z t)) =
      (φ y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x - x := by
    have : (⟨_, hcmV⟩ : ↥(Vt M (LB M Q B) B Z t)) = ⟨_, hw⟩ * vq⁻¹ := by
      apply Subtype.ext
      exact hcommE
    rw [this, secVec_mul, secVec_inv, sub_eq_add_neg]
    have h1 : secVec ψ (⟨_, hw⟩ : ↥(Vt M (LB M Q B) B Z t)) =
        (φ y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ x := by
      unfold secVec at hsv ⊢
      rw [hact, hsv]
    rw [h1, hsv]
  have hBZ : B ≤ Subgroup.normalizer (Z : Set G) := fun b hb =>
    hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hc.le hb))
  obtain ⟨b, hb, z, hz, hbz⟩ := exists_mul_of_mem_sup_of_le_normalizer hBZ hmem
  have hbV : b ∈ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht hb
  have hzV : z ∈ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt hz
  have hvec2 : secVec ψ (⟨_, hcmV⟩ : ↥(Vt M (LB M Q B) B Z t)) = secVec ψ ⟨b, hbV⟩ := by
    have : (⟨_, hcmV⟩ : ↥(Vt M (LB M Q B) B Z t)) = ⟨b, hbV⟩ * ⟨z, hzV⟩ := by
      apply Subtype.ext
      exact hbz.symm
    rw [this, secVec_mul, (secVec_eq_zero_iff ψ ⟨z, hzV⟩).mpr hz, add_zero]
  obtain ⟨c, hc'⟩ := (P.point (secVec ψ ⟨b, hbV⟩)).mp ⟨⟨b, hbV⟩, hb, rfl⟩
  rw [hvec2, hc'] at hvec
  have hphi : (φ y : GL (Fin 2 ⊕ Fin 2) K) ∈ StatedOmega (StatedQuadPlus 2 K) :=
    P.range ▸ MonoidHom.mem_range.mpr ⟨y, rfl⟩
  have hiso : ∀ w, quadPlus 2 K ((φ y : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ w) =
      quadPlus 2 K w := fun w => E.quad_mulVec hphi w
  exact hx (polar_mulVec_eq_zero_of_sub_mem hiso P.sing c hvec.symm)

theorem comm_comm_mem_Z_of_inf (hc : Ctx M Q Z B) {h : G} (hh : h ∈ M)
    (hne : LB M Q B ≠ conjSubgroup h (LB M Q B)) {V : Subgroup G} (hVQ : V ≤ Q)
    (hVB : V ≤ Subgroup.centralizer (B : Set G))
    (hVB' : V ≤ Subgroup.centralizer (conjSubgroup h B : Set G)) {x y v : G}
    (hx : x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B))
    (hy : y ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B)) (hv : v ∈ V) : ⁅y, ⁅x, v⁆⁆ ∈ Z := by
  have hc' : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hLconj : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  have hxL' : x ∈ LB M Q (conjSubgroup h B) := hLconj ▸ hx.2
  have hyL' : y ∈ LB M Q (conjSubgroup h B) := hLconj ▸ hy.2
  have hu1 : ⁅x, v⁆ ∈ Q ⊓ QB B := hc.comm_LB_mem_inf hx.1 (hVQ hv) (hVB hv)
  have hu2 : ⁅x, v⁆ ∈ Q ⊓ QB (conjSubgroup h B) :=
    hc'.comm_LB_mem_inf hxL' (hVQ hv) (hVB' hv)
  have h1 : ⁅y, ⁅x, v⁆⁆ ∈ B ⊔ Z := comm_LB_inf_QB hc hy.1 hu1
  have h2 : ⁅y, ⁅x, v⁆⁆ ∈ conjSubgroup h B ⊔ Z := comm_LB_inf_QB hc' hyL' hu2
  have hinter := sup_inf_sup_eq_of_not_le hc hc' (not_le_sup_Z_of_ne hc hh hne)
  rw [← hinter]
  exact ⟨h1, h2⟩

theorem comm_comm_mem_Z_of_decomp {L H' N V : Subgroup G}
    (hHn : H' ≤ Subgroup.normalizer ((L ⊓ N : Subgroup G) : Set G)) (hH : H' ⊔ (L ⊓ N) = L)
    (hZc : ∀ l ∈ L, ∀ z ∈ Z, l * z * l⁻¹ = z) (hVL : ∀ l ∈ L, ∀ v ∈ V, l * v * l⁻¹ ∈ V)
    (hVN : ∀ m ∈ N, ∀ v ∈ V, ⁅m, v⁆ ∈ Z)
    (hE : ∀ x ∈ H', ∀ y ∈ H', ∀ v ∈ V, ⁅y, ⁅x, v⁆⁆ ∈ Z) :
    ∀ l₁ ∈ L, ∀ l₂ ∈ L, ∀ v ∈ V, ⁅l₂, ⁅l₁, v⁆⁆ ∈ Z := by
  have hdec : ∀ l ∈ L, ∃ a ∈ H', ∃ m ∈ L ⊓ N, l = a * m := by
    intro l hl
    rw [← hH] at hl
    obtain ⟨a, ha, m, hm, hlam⟩ := exists_mul_of_mem_sup_of_le_normalizer hHn hl
    exact ⟨a, ha, m, hm, hlam.symm⟩
  have hHL : H' ≤ L := hH ▸ le_sup_left
  intro l₁ hl₁ l₂ hl₂ v hv
  obtain ⟨a₁, ha₁, m₁, hm₁, rfl⟩ := hdec l₁ hl₁
  obtain ⟨a₂, ha₂, m₂, hm₂, rfl⟩ := hdec l₂ hl₂
  have ha₁L : a₁ ∈ L := hHL ha₁
  have ha₂L : a₂ ∈ L := hHL ha₂
  have hu₁ : ⁅a₁, v⁆ ∈ V := by
    have e : ⁅a₁, v⁆ = (a₁ * v * a₁⁻¹) * v⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact V.mul_mem (hVL a₁ ha₁L v hv) (V.inv_mem hv)
  have hz₁ : ⁅m₁, v⁆ ∈ Z := hVN m₁ hm₁.2 v hv
  have hz₂ : ⁅m₂, ⁅a₁, v⁆⁆ ∈ Z := hVN m₂ hm₂.2 _ hu₁
  have hz₃ : ⁅a₂, ⁅a₁, v⁆⁆ ∈ Z := hE a₁ ha₁ a₂ ha₂ v hv
  have h₂ : ⁅a₂ * m₂, ⁅a₁, v⁆⁆ ∈ Z := by
    have e : ⁅a₂ * m₂, ⁅a₁, v⁆⁆ = a₂ * ⁅m₂, ⁅a₁, v⁆⁆ * a₂⁻¹ * ⁅a₂, ⁅a₁, v⁆⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e, hZc a₂ ha₂L _ hz₂]
    exact Z.mul_mem hz₂ hz₃
  have e1 : ⁅a₁ * m₁, v⁆ = ⁅m₁, v⁆ * ⁅a₁, v⁆ := by
    have : ⁅a₁ * m₁, v⁆ = a₁ * ⁅m₁, v⁆ * a₁⁻¹ * ⁅a₁, v⁆ := by
      simp only [commutatorElement_def]
      group
    rw [this, hZc a₁ ha₁L _ hz₁]
  have e2 : ⁅a₂ * m₂, ⁅m₁, v⁆ * ⁅a₁, v⁆⁆ =
      ⁅a₂ * m₂, ⁅m₁, v⁆⁆ * (⁅m₁, v⁆ * ⁅a₂ * m₂, ⁅a₁, v⁆⁆ * ⁅m₁, v⁆⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e1, e2]
  have hl₂L : a₂ * m₂ ∈ L := L.mul_mem ha₂L hm₂.1
  have h0 : ⁅a₂ * m₂, ⁅m₁, v⁆⁆ = 1 := by
    rw [commutatorElement_def, hZc _ hl₂L _ hz₁]
    group
  rw [h0, one_mul]
  have hconj : ⁅m₁, v⁆ * ⁅a₂ * m₂, ⁅a₁, v⁆⁆ * ⁅m₁, v⁆⁻¹ ∈ Z :=
    Z.mul_mem (Z.mul_mem hz₁ h₂) (Z.inv_mem hz₁)
  exact hconj

theorem false_of_conjB_le_Wt (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t : G}
    (hs : Sec9Hyp hc n t) {h : G} (hh : h ∈ M)
    (hne : LB M Q B ≠ conjSubgroup h (LB M Q B))
    (hW : conjSubgroup h B ≤ Wt Q (Vt M (LB M Q B) B Z t))
    (hH : (LB M Q B ⊓ conjSubgroup h (LB M Q B)) ⊔ (LB M Q B ⊓ hc.CN t) = LB M Q B) :
    False := by
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have h35 := (stroth_3_5 h34 hc hs5.width hs5.n_gt hs5.noA2 hs5.gen).2.1
  have hVcomm := hc.Vt_comm (fun m hm => hc.CQt_conj hm h35) ht hs5.notQ
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hVB : Vt M (LB M Q B) B Z t ≤ Subgroup.centralizer (B : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact hVcomm b (hc.B_le_Vt ht hb) v hv
  have hVB' : Vt M (LB M Q B) B Z t ≤ Subgroup.centralizer (conjSubgroup h B : Set G) := by
    intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro c hcB
    exact (Subgroup.mem_centralizer_iff.mp (hW hcB).2 v hv).symm
  have hHL : LB M Q B ⊓ conjSubgroup h (LB M Q B) ≤ LB M Q B := inf_le_left
  have hE : ∀ x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B),
      ∀ y ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B), ∀ v ∈ Vt M (LB M Q B) B Z t,
        ⁅y, ⁅x, v⁆⁆ ∈ Z := fun x hx y hy v hv =>
    comm_comm_mem_Z_of_inf hc hh hne hVQ hVB hVB' hx hy hv
  have hZc : ∀ l ∈ LB M Q B, ∀ z ∈ Z, l * z * l⁻¹ = z := by
    intro l hl z hz
    have := Subgroup.mem_centralizer_iff.mp (hc.LB_le_H0 hl).2 z hz
    rw [← this, mul_inv_cancel_right]
  have hVL : ∀ l ∈ LB M Q B, ∀ v ∈ Vt M (LB M Q B) B Z t,
      l * v * l⁻¹ ∈ Vt M (LB M Q B) B Z t := fun l hl v hv =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht (le_Rt (M := M) (LB M Q B) ht hl)) v).mp
      hv
  have hVN : ∀ m ∈ hc.CN t, ∀ v ∈ Vt M (LB M Q B) B Z t, ⁅m, v⁆ ∈ Z := fun m hm v hv =>
    (Ctx.mem_CN.mp hm).2 v hv
  have hHn : LB M Q B ⊓ conjSubgroup h (LB M Q B) ≤
      Subgroup.normalizer ((LB M Q B ⊓ hc.CN t : Subgroup G) : Set G) :=
    fun x hx => LB_le_normalizer_inf_CN hc ht hx.1
  have h6 := comm_comm_mem_Z_of_decomp hHn hH hZc hVL hVN hE
  obtain ⟨y, hyL, v, hv, hyv⟩ := exists_comm_not_mem_sup_Z h34 hs
  have hu : ⁅y, v⁆ ∈ Q := (hc.comm_LB_mem_inf hyL (hVQ hv) (hVB hv)).1
  have hnot : ⁅y, v⁆ ∉ CQt Q Z (LB M Q B) := by
    rw [h35]
    exact hyv
  have : ¬ ∀ l ∈ LB M Q B, ⁅l, ⁅y, v⁆⁆ ∈ Z := fun hall => hnot ⟨hu, hall⟩
  push Not at this
  obtain ⟨l, hl, hlnot⟩ := this
  exact hlnot (h6 y hyL l hl v hv)

end HS9

end CFSG.RankThree.GF2n.Stroth80
