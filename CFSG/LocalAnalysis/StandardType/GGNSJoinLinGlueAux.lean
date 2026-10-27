module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyNbrFieldRows
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMember

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

namespace NSJoin

theorem nsLG_label_J_ennola (hKn : GGTCJEnnolaKnown) {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G}
    {K : Subgroup G} (hnb : GGNbr p B x D J y K)
    (hLrow : GGInnerDiagOnLabel ggRowP_Ennola p Bs L)
    (labJ₀ : LargeEvenLabel) (hΛ₀ : LargeEvenInLambda2 labJ₀)
    (hhas₀ : GGHasLabel labJ₀ (J ⧸ Subgroup.center J)) :
    ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
      GGHasLabel labJ (J ⧸ Subgroup.center J) ∧ p ∣ 2 ^ labJ.n + 1 ∧
      ¬ (labJ.tag = .twD ∧ labJ.rank = 2) := by
  have hT : GGThmIHyp p B x L := hcfg.1
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hT.2.2.2.2.2.1.2.1
  have hSS := hT.2.2.2.2.2.2.1
  have hBel : IsElemAbelian p B := hSS.1.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hSS.2.2.2.1.1
  have hy : y ∈ B := hnb.1.2.1
  have hyBs : y ∈ Bs := hcfg.2.1.1 hy
  have hLperf : commutator ↥L = ⊤ := hLrow.1
  have hM := ggMarking_and_labelAll_dep (fun lab hlab => hKn p hp hp2 lab hlab) hLrow
  obtain ⟨lab, -, -, R, _, I, F, θ, ⟨⟨hEnnola, hNL, hind⟩, hTC⟩⟩ :=
    largeEvenMarking_exists_hasLabel hM
  have hyN : y ∈ Subgroup.normalizer (L : Set G) := hNL hyBs
  have hy1 : y ^ p = 1 := hBel.2 y hy
  have hep : L.normalizerMonoidHom ⟨y, hyN⟩ ^ p = 1 := by
    rw [← map_pow]
    have h1 : (⟨y, hyN⟩ : ↥(Subgroup.normalizer (L : Set G))) ^ p = 1 :=
      Subtype.ext (by simpa using hy1)
    rw [h1, map_one]
  obtain ⟨φ, hφI, hφ⟩ := hind y⁻¹ (Bs.inv_mem hyBs)
  let ψ : ↥L →* R := (θ : L ⧸ Subgroup.center L →* R).comp (QuotientGroup.mk' (Subgroup.center L))
  have hψsurj : Function.Surjective ψ := fun r => by
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, rfl⟩
  have hψker : ψ.ker ≤ Subgroup.center ↥L := fun l hl => by
    have h0 : θ (QuotientGroup.mk l) = 1 := hl
    have h1 : (QuotientGroup.mk l : L ⧸ Subgroup.center L) = 1 := by
      simpa using θ.injective (h0.trans (map_one θ).symm)
    exact (QuotientGroup.eq_one_iff l).mp h1
  have hφe : ∃ φ ∈ I, ∀ l : ↥L, φ (ψ l) = ψ (L.normalizerMonoidHom ⟨y, hyN⟩ l) := by
    refine ⟨φ, hφI, fun l => hφ l (L.normalizerMonoidHom ⟨y, hyN⟩ l) ?_⟩
    show ((L.normalizerMonoidHom ⟨y, hyN⟩ l : ↥L) : G) = y⁻¹⁻¹ * (l : G) * y⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  have hDy : D = Subgroup.closure {x, y} := hnb.2.1
  have hcomp : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hcfg.2.2.1.2.2.2.2.2.1
  have hJL : J ≤ L := hcomp.1.trans inf_le_left
  rw [hDy, ggInf_centralizer_pair hLx] at hcomp
  have hJcomp := ggIsComponentOf_ggFixSub_normalizerMonoidHom hyN hcomp
  let eJ : ↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L) ≃*
      ↥J ⧸ Subgroup.center ↥J :=
    QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJL) (Subgroup.map_center_eq _)
  obtain ⟨labJ, hlabJ, hhasJ, hd, h2⟩ :=
    hTC hEnnola ↥L ψ hψsurj hψker hLperf _ hep hφe (J.subgroupOf L) hJcomp labJ₀ hΛ₀
      (ggHasLabel_of_mulEquiv eJ.symm hhas₀)
  exact ⟨labJ, hlabJ, ggHasLabel_of_mulEquiv eJ hhasJ, hd, h2⟩

theorem nsLG_odd_of_three_dvd_two_pow_add_one {n : ℕ} (h : 3 ∣ 2 ^ n + 1) : Odd n := by
  have key : ∀ k : ℕ, (2 ^ k + 1) % 3 = if k % 2 = 0 then 2 else 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      split_ifs at ih ⊢ with h1 h2 h2 <;> omega
  have h3 := key n
  have h0 : (2 ^ n + 1) % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
  rw [h3] at h0
  by_cases h4 : n % 2 = 0
  · rw [if_pos h4] at h0
    norm_num at h0
  · rw [if_neg h4] at h0
    rw [Nat.odd_iff]
    omega

theorem nsLG_common_label_J (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown) (hKn : GGTCJEnnolaKnown)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) {y : G} {K : Subgroup G} (hnb : GGNbr 3 B x D J y K)
    (hLrow : GGInnerDiagOnLabel ggRowP_Ennola 3 Bs L)
    (hQ4 : GGInnerDiagOnLabel GGLabQFour 3 Bs L) :
    ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
      GGHasLabel labJ (J ⧸ Subgroup.center J) ∧ 3 ≤ labJ.n := by
  obtain ⟨labL, labJ₂, -, hq4, -, hΛ₂, hdvd₂, hhas₂⟩ :=
    ggNbr_label_J_of_tcj_onLabel hTCJ hcfg hQ4 hnb
  obtain ⟨labJ₁, hΛ₁, hhas₁, hdvd₁, hnot₁⟩ :=
    nsLG_label_J_ennola hKn hcfg hnb hLrow labJ₂ hΛ₂ hhas₂
  have hodd : Odd labJ₁.n := nsLG_odd_of_three_dvd_two_pow_add_one hdvd₁
  have hJ₂ : 2 ≤ labJ₂.n := le_trans hq4 (Nat.le_of_dvd (by have := hΛ₂.1; omega) hdvd₂)
  have hiso : GGLabelIso labJ₁ labJ₂ :=
    hRig labJ₁ labJ₂ (J ⧸ Subgroup.center J) hΛ₁ hΛ₂ hhas₁ hhas₂
  rcases hiso.n_cases with h | h | h
  · have h2 : 2 ≤ labJ₁.n := by rw [h]; exact hJ₂
    obtain ⟨k, hk⟩ := hodd
    exact ⟨labJ₁, hΛ₁, hhas₁, by omega⟩
  · exact absurd h hnot₁
  · exfalso
    obtain ⟨k, hk⟩ := hodd
    omega

end NSJoin

end CFSG.StandardType

end
