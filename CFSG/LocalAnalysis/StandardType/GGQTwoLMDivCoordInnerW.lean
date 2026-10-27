module

import CFSG.LocalAnalysis.StandardType.GGQTwoLMMod
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMDivCoordInnerLift
public import CFSG.LocalAnalysis.StandardType.GGQTwoLMPrimeCBase

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord
  CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary Matrix CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

private theorem qTwoLMDivCoordInner_w_center_centralizer {B Bs L : Subgroup G} {x : G}
    (hG : GGThmIHyp 3 B x L) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m : ℕ} (hm : 4 ≤ m)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
    {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ)
    {z : ↥L} (hzcenter : z ∈ Subgroup.center ↥L) (hz3 : z ^ 3 = 1) :
    (z : G) ∈ Subgroup.centralizer (Bs : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  by_cases hcase : 3 ∣ Nat.card (Subgroup.center ↥L)
  · have hker : π.ker = ⊥ :=
      (qTwoLMDivCoordInner_kerpi (qTwoLMFrameC_perfect hG) hN hm hU).1 hcase
    have hπinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hker
    have hcz : c z ∈ Subgroup.center L0 :=
      Subgroup.map_center_le_center hU.c_surj (Subgroup.mem_map_of_mem c hzcenter)
    obtain ⟨s0, hs0⟩ := hU.π_surj (c z)
    have hs0center : s0 ∈ Subgroup.center (Su F0 2 1 m) := by
      rw [Subgroup.mem_center_iff]
      intro s'
      apply hπinj
      calc π (s' * s0) = π s' * π s0 := map_mul π s' s0
        _ = π s' * c z := by rw [hs0]
        _ = c z * π s' := Subgroup.mem_center_iff.mp hcz (π s')
        _ = π s0 * π s' := by rw [hs0]
        _ = π (s0 * s') := (map_mul π s0 s').symm
    obtain ⟨c0, hc0⟩ := qTwoLMDivCoordInner_center_scalar hU.card hm hs0center
    let b1 : ↥Bs := ⟨b, hb⟩
    obtain ⟨g, -, hgact⟩ := hU.diag b1
    obtain ⟨u', hu'mat, hu'act⟩ := hgact s0
    have hconj_scalar : (g : GL (Fin m) F0) * (s0 : GL (Fin m) F0) * g⁻¹ = s0 := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_inv_eq_inv_val, hc0, ← Matrix.scalar_apply]
      rw [← Matrix.scalar_comm c0 (fun r => Commute.all c0 r) (g : Matrix (Fin m) (Fin m) F0)]
      rw [mul_assoc, ← Units.val_mul]
      simp
    have hu'GL : (u' : GL (Fin m) F0) = (s0 : GL (Fin m) F0) := by
      rw [hu'mat, hconj_scalar]
    have hu' : u' = s0 := Subtype.ext hu'GL
    have hρfix : ρ b1 (c z) = c z := by
      rw [← hs0, hu'act, hu']
    let w : ↥L := ⟨(b1 : G) * z * (b1 : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hN b1.2) z).mp z.2⟩
    have hcw : c w = c z := by
      have h := hU.induced b1 z
      rw [hρfix] at h
      exact h
    let z'' : ↥L := z⁻¹ * w
    have hz''ker : z'' ∈ c.ker := by
      rw [MonoidHom.mem_ker]
      show c (z⁻¹ * w) = 1
      rw [map_mul, map_inv, hcw]
      group
    have hw3 : w ^ 3 = 1 := by
      apply Subtype.ext
      have hz3G : (z : G) ^ 3 = 1 := by
        have := congrArg (fun t : ↥L => (t : G)) hz3
        simpa using this
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      change (((b1 : G) * (z : G) * (b1 : G)⁻¹) ^ 3) = 1
      rw [conj_pow, hz3G]
      group
    have hwcenter : w ∈ Subgroup.center ↥L := by
      have hmem : ggGamma L hN b1 z ∈
          Subgroup.map (ggGamma L hN b1 : ↥L →* ↥L) (Subgroup.center ↥L) :=
        Subgroup.mem_map_of_mem (ggGamma L hN b1 : ↥L →* ↥L) hzcenter
      have hcenter_map : Subgroup.map (ggGamma L hN b1 : ↥L →* ↥L)
          (Subgroup.center ↥L) = Subgroup.center ↥L := by
        simpa using Subgroup.map_center_eq (ggGamma L hN b1)
      rw [hcenter_map] at hmem
      have hw_eq : w = ggGamma L hN b1 z := Subtype.ext rfl
      rwa [hw_eq]
    have hz''3 : z'' ^ 3 = 1 := by
      have hz_inv_center : z⁻¹ ∈ Subgroup.center ↥L := Subgroup.inv_mem _ hzcenter
      have hcomm : Commute z⁻¹ w :=
        (Subgroup.mem_center_iff.mp hz_inv_center w).symm
      change (z⁻¹ * w) ^ 3 = 1
      rw [hcomm.mul_pow, hw3]
      rw [show z⁻¹ ^ 3 = 1 by rw [inv_pow, hz3, inv_one]]
      group
    have hz''1 : z'' = 1 := by
      obtain ⟨k, hk⟩ := hU.c_two.exists_pow_pow_eq_one ⟨z'', hz''ker⟩
      have h2 : z'' ^ 2 ^ k = 1 := by
        have := congrArg (fun t : ↥c.ker => (t : ↥L)) hk
        simpa using this
      have hdvd2 : orderOf z'' ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr h2
      have hdvd3 : orderOf z'' ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hz''3
      have hcop : Nat.Coprime (2 ^ k) 3 := (by norm_num : Nat.Coprime 2 3).pow_left k
      have hgcd : Nat.gcd (2 ^ k) 3 = 1 := Nat.coprime_iff_gcd_eq_one.mp hcop
      have hdvd1 : orderOf z'' ∣ 1 := by
        have := Nat.dvd_gcd hdvd2 hdvd3
        rwa [hgcd] at this
      exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
    have hwz : w = z := by
      have h : z * z'' = w := by simp [z'', mul_assoc]
      rw [hz''1, mul_one] at h
      exact h.symm
    have hbz : (b1 : G) * (z : G) * (b1 : G)⁻¹ = (z : G) := by
      have := congrArg (fun t : ↥L => (t : G)) hwz
      simpa [w] using this
    exact (mul_inv_eq_iff_eq_mul).mp hbz
  · have hdvd_center : orderOf z ∣ Nat.card (Subgroup.center ↥L) := by
      have h := orderOf_dvd_natCard (⟨z, hzcenter⟩ : Subgroup.center ↥L)
      have hx : orderOf (⟨z, hzcenter⟩ : Subgroup.center ↥L) = orderOf z :=
        (orderOf_injective (Subgroup.center ↥L).subtype Subtype.coe_injective
          (⟨z, hzcenter⟩ : Subgroup.center ↥L)).symm
      rwa [hx] at h
    have hdvd3 : orderOf z ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hz3
    have hone : orderOf z = 1 := by
      rcases (by norm_num : Nat.Prime 3).eq_one_or_self_of_dvd (orderOf z) hdvd3 with h1 | h3'
      · exact h1
      · exact absurd (h3' ▸ hdvd_center) hcase
    rw [orderOf_eq_one_iff.mp hone]
    simp

theorem qTwoLMDivCoordInner_wnorm {B Bs L : Subgroup G} {x : G} (hG : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) {m : ℕ} (hm : 4 ≤ m)
    {F0 : Type} [Field F0] [Finite F0] [CharP F0 2] {L0 : Type} [Group L0]
    {c : ↥L →* L0} {π : Su F0 2 1 m →* L0} {ρ : ↥Bs →* MulAut L0}
    (hU : QTwoDivInnerFrame m Bs L hN F0 L0 c π ρ)
    (hsplit : ∀ b ∈ Bs, ∃ t : ↥L, (t : G) ∈ Bs ∧ ∃ k : ℕ, b = (t : G) * x ^ k)
    (n : ↥L) (hn : MulAut.conj n ∈
      Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L))) :
    (n : G) ∈ Subgroup.normalizer (Bs : Set G) := by
  have hS : LargeEvenSStar 3 B x L := hG.2.2.2.2.2.2.1
  obtain ⟨⟨-, -, -⟩, hxB, hx1, -, -⟩ := hS
  have hxBs : x ∈ Bs := hBs.1 hxB
  have hforward : ∀ b ∈ Bs, (n : G) * b * (n : G)⁻¹ ∈ Bs := by
    intro b hb
    obtain ⟨t, htBs, k, hbk⟩ := hsplit b hb
    have hntn : (n : G) * (t : G) * (n : G)⁻¹ ∈ Bs := by
      let b_t : ↥Bs := ⟨(t : G), htBs⟩
      have hconj_t : MulAut.conj t = ggGamma L hN b_t := by
        apply MulEquiv.ext
        intro l
        apply Subtype.ext
        simp only [MulAut.conj_apply, ggGamma_coe, Subgroup.coe_mul, Subgroup.coe_inv]
        rfl
      let t0 : ↥L := MulAut.conj n t
      have ht0_eq : t0 = (n : ↥L) * t * (n : ↥L)⁻¹ := rfl
      have hconj_t0 : MulAut.conj t0 =
          MulAut.conj n * MulAut.conj t * (MulAut.conj n)⁻¹ := by
        rw [ht0_eq]
        simp only [map_mul, map_inv]
      have hW : MulAut.conj t0 ∈ (ggGamma L hN).range := by
        have hmem : ggGamma L hN b_t ∈ (ggGamma L hN).range :=
          MonoidHom.mem_range.mpr ⟨b_t, rfl⟩
        have h1 := (Subgroup.mem_normalizer_iff.mp hn (ggGamma L hN b_t)).mp hmem
        rwa [← hconj_t, ← hconj_t0] at h1
      obtain ⟨bW, hbW⟩ := MonoidHom.mem_range.mp hW
      obtain ⟨s, hsBs, k2, hbk2⟩ := hsplit bW bW.2
      have hconj_s : MulAut.conj s = ggGamma L hN bW := by
        apply MulEquiv.ext
        intro l
        apply Subtype.ext
        rw [MulAut.conj_apply, ggGamma_coe]
        have hxl : Commute x (l : G) :=
          Subgroup.mem_centralizer_iff.mp (qTwoLMFrameC_le_centralizer hG l.2) x
            (Set.mem_singleton x)
        have hxk : Commute (l : G) (x ^ k2) := hxl.symm.pow_right k2
        rw [hbk2]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        rw [show ((s : G) * x ^ k2) * (l : G) * ((s : G) * x ^ k2)⁻¹ =
            (s : G) * (l : G) * (s : G)⁻¹ by
          calc ((s : G) * x ^ k2) * (l : G) * ((s : G) * x ^ k2)⁻¹
              = (s : G) * (x ^ k2 * (l : G) * (x ^ k2)⁻¹) * (s : G)⁻¹ := by group
            _ = (s : G) * ((l : G) * x ^ k2 * (x ^ k2)⁻¹) * (s : G)⁻¹ := by
                rw [← hxk.eq]
            _ = (s : G) * (l : G) * (s : G)⁻¹ := by group]
      have ht0s : MulAut.conj t0 = MulAut.conj s := by
        rw [← hbW, hconj_s]
      let z : ↥L := s⁻¹ * t0
      have hzcenter : z ∈ Subgroup.center ↥L := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hconjz : MulAut.conj z = 1 := by
          show MulAut.conj (s⁻¹ * t0) = 1
          rw [map_mul, map_inv, ht0s]
          group
        have h := congrArg (fun a : MulAut ↥L => a g) hconjz
        simp only [MulAut.conj_apply, MulAut.one_apply] at h
        calc g * z = z * g * z⁻¹ * z := by rw [h]
          _ = z * g := by group
      have ht3 : t ^ 3 = 1 := by
        apply Subtype.ext
        simp [Subgroup.coe_pow, hBs.2.1.2 (t : G) htBs]
      have ht0_3 : t0 ^ 3 = 1 := by
        change (MulAut.conj n t) ^ 3 = 1
        rw [← map_pow (MulAut.conj n) t 3, ht3, map_one]
      have hs3 : s ^ 3 = 1 := by
        apply Subtype.ext
        simp [Subgroup.coe_pow, hBs.2.1.2 (s : G) hsBs]
      have hz3 : z ^ 3 = 1 := by
        have ht0z : t0 = s * z := by simp [z]
        have hcomm : Commute s z := Subgroup.mem_center_iff.mp hzcenter s
        rw [ht0z, hcomm.mul_pow, hs3, one_mul] at ht0_3
        exact ht0_3
      have hzcent_bs : (z : G) ∈ Subgroup.centralizer (Bs : Set G) :=
        qTwoLMDivCoordInner_w_center_centralizer hG hN hm hU hzcenter hz3
      have hz3G : (z : G) ^ 3 = 1 := by
        have := congrArg (fun t : ↥L => (t : G)) hz3
        simpa using this
      have hzBs : (z : G) ∈ Bs := hBs.2.2.2 (z : G) hzcent_bs hz3G
      have ht0_eq : t0 = s * z := by simp [z]
      have ht0G : (t0 : G) = (s : G) * (z : G) := by
        rw [ht0_eq, Subgroup.coe_mul]
      have hntn_eq : (n : G) * (t : G) * (n : G)⁻¹ = (t0 : G) := by
        rw [show t0 = (n : ↥L) * t * (n : ↥L)⁻¹ from rfl]
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hntn_eq, ht0G]
      exact Bs.mul_mem hsBs hzBs
    have hnx : (n : G) * x ^ k * (n : G)⁻¹ = x ^ k := by
      have hcomm : Commute x (n : G) :=
        Subgroup.mem_centralizer_iff.mp (qTwoLMFrameC_le_centralizer hG n.2) x
          (Set.mem_singleton x)
      have hnk : Commute (n : G) (x ^ k) := hcomm.symm.pow_right k
      calc (n : G) * x ^ k * (n : G)⁻¹ = x ^ k * (n : G) * (n : G)⁻¹ := by rw [hnk.eq]
        _ = x ^ k := by group
    rw [hbk]
    rw [show (n : G) * ((t : G) * x ^ k) * (n : G)⁻¹ =
        ((n : G) * (t : G) * (n : G)⁻¹) * ((n : G) * x ^ k * (n : G)⁻¹) by group]
    rw [hnx]
    exact Bs.mul_mem hntn (Subgroup.pow_mem Bs hxBs k)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rintro x ⟨b, hb, rfl⟩
    exact hforward b hb
  · rw [Subgroup.card_map_of_injective (K := Bs)
      (f := (MulAut.conj (n : G) : G →* G)) (MulAut.conj (n : G)).injective]


theorem qTwoLMDivCoordInner_permHm (m : ℕ) (h3 : 3 ∣ m) :
    ∃ ρ : Equiv.Perm (Fin m) →* MulAut (QTwoHm m h3), IsHmModel m h3 (QTwoHm m h3) ρ ∧
      ∀ σ (f : ↥(sumZero m 3)),
        ρ σ (QuotientGroup.mk f) = QuotientGroup.mk (permAutV σ f) := by
  let Z : Subgroup ↥(sumZero m 3) := Subgroup.zpowers (qTwoOneVec m h3)
  have hfix : ∀ σ : Equiv.Perm (Fin m), permAutV σ (qTwoOneVec m h3) = qTwoOneVec m h3 := by
    intro σ
    refine ext_crd fun k => ?_
    rw [crd_permAutV]
    show Multiplicative.toAdd ((qTwoOneVec m h3 : Fin m → Multiplicative (ZMod 3)) (σ⁻¹ k)) =
      Multiplicative.toAdd ((qTwoOneVec m h3 : Fin m → Multiplicative (ZMod 3)) k)
    rfl
  have hmap : ∀ σ : Equiv.Perm (Fin m),
      Z.map (permAutV (p := 3) σ : ↥(sumZero m 3) →* ↥(sumZero m 3)) = Z := by
    intro σ
    change (Subgroup.zpowers (qTwoOneVec m h3)).map
      (permAutV (p := 3) σ : ↥(sumZero m 3) →* ↥(sumZero m 3)) =
      Subgroup.zpowers (qTwoOneVec m h3)
    rw [MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers (hfix σ)
  let ρfun : Equiv.Perm (Fin m) → MulAut (QTwoHm m h3) := fun σ =>
    QuotientGroup.congr Z Z (permAutV (p := 3) σ) (hmap σ)
  have hρmul : ∀ σ τ : Equiv.Perm (Fin m), ρfun (σ * τ) = ρfun σ * ρfun τ := by
    intro σ τ
    apply MulEquiv.ext
    intro x
    refine QuotientGroup.induction_on x fun g => ?_
    show QuotientGroup.congr Z Z (permAutV (p := 3) (σ * τ)) (hmap (σ * τ)) (QuotientGroup.mk g) =
      (QuotientGroup.congr Z Z (permAutV (p := 3) σ) (hmap σ) *
        QuotientGroup.congr Z Z (permAutV (p := 3) τ) (hmap τ)) (QuotientGroup.mk g)
    rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
      permAutV_mul, MulAut.mul_apply]
  let ρ : Equiv.Perm (Fin m) →* MulAut (QTwoHm m h3) := MonoidHom.mk' ρfun hρmul
  have hρ : ∀ σ, ρ σ = ρfun σ := fun _ => rfl
  have hperm : ∀ σ (f : ↥(sumZero m 3)),
      ρ σ (QuotientGroup.mk f) = QuotientGroup.mk (permAutV σ f) := by
    intro σ f
    rw [hρ]
    show QuotientGroup.congr Z Z (permAutV (p := 3) σ) (hmap σ) (QuotientGroup.mk f) = _
    rw [QuotientGroup.congr_mk]
  refine ⟨ρ, ⟨QuotientGroup.mk' Z, QuotientGroup.mk'_surjective Z, ?_, ?_⟩, hperm⟩
  · intro v
    exact QuotientGroup.eq_one_iff (N := Z) v
  · intro σ v
    exact (hperm σ v).symm

end CFSG.StandardType.QTwo

end
