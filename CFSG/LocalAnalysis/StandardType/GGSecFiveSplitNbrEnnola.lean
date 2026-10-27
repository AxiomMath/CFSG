module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1Defs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowDefs
public import CFSG.LocalAnalysis.StandardType.GGTPNNarrow
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyNbrFieldRows
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTier1OfPrim
public import CFSG.LocalAnalysis.StandardType.GGSecFivePrimDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRankOneCard
public import CFSG.LocalAnalysis.StandardType.GGNbrBalance
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.StandardType

open CFSG.Assembly
open scoped MatrixGroups

@[expose] def ggRowP_E (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ggRowP_ESU p lab ∨ ggRowP_EOmP p lab ∨ ggRowP_EOmM p lab ∨ ggRowP_ETwE6 p lab ∨
    ggRowP_EE7 p lab ∨ ggRowP_EE8 p lab

theorem ggRowP_E.dvd {p : ℕ} {lab : LargeEvenLabel} (h : ggRowP_E p lab) :
    p ∣ 2 ^ lab.n + 1 := by
  rcases h with ⟨-, h⟩ | ⟨-, -, -, h⟩ | ⟨-, -, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> exact h

theorem ggDvd_two_of_dvd_pow_sub_add {p m : ℕ} (h1 : p ∣ 2 ^ m - 1) (h2 : p ∣ 2 ^ m + 1) :
    p ∣ 2 := by
  have hm : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h := Nat.dvd_sub h2 h1
  have e : 2 ^ m + 1 - (2 ^ m - 1) = 2 := by omega
  rwa [e] at h

theorem three_dvd_two_pow_add_one_of_three_mul {m : ℕ} (h : 3 ∣ 2 ^ (3 * m) + 1) :
    3 ∣ 2 ^ m + 1 := by
  have key : ∀ k : ℕ, (2 ^ k + 1) % 3 = if k % 2 = 0 then 2 else 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      split_ifs at ih ⊢ with h1 h2 h2 <;> omega
  have h3 := key (3 * m)
  have hm := key m
  rw [Nat.dvd_iff_mod_eq_zero] at h ⊢
  split_ifs at h3 hm with h4 h5 h5 <;> omega

theorem GGLabelIso.n_cases {a b : LargeEvenLabel} (h : GGLabelIso a b) :
    a.n = b.n ∨ (a.tag = .twD ∧ a.rank = 2) ∨ a.n = 2 * b.n := by
  obtain ⟨ta, ra, na⟩ := a
  obtain ⟨tb, rb, nb⟩ := b
  simp only [GGLabelIso, LargeEvenLabel.mk.injEq] at h
  dsimp only
  rcases h with ⟨-, -, h⟩ | ⟨-, -, -, h⟩ | ⟨⟨-, -⟩, -, -, h⟩ | ⟨⟨-, -⟩, -, -, h⟩ |
    ⟨⟨-, -⟩, -, -, h⟩ | ⟨⟨-, -⟩, -, -, h⟩ | ⟨⟨h1, h2, -⟩, -⟩ | ⟨-, -, h⟩
  · exact Or.inl h
  · exact Or.inl h
  · exact Or.inl h.symm
  · exact Or.inl h.symm
  · exact Or.inl h.symm
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl ⟨h1, h2⟩)
  · exact Or.inr (Or.inr h.2)

theorem ggLabelIso_ennola_absurd {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {labK labL : LargeEvenLabel} (hiso : GGLabelIso labK labL) (hf : f ∣ labL.n)
    (hpf : p ∣ 2 ^ f - 1) (hK : p ∣ 2 ^ labK.n + 1)
    (hK2 : ¬ (labK.tag = .twD ∧ labK.rank = 2)) : False := by
  have hno : ∀ m, p ∣ 2 ^ m - 1 → p ∣ 2 ^ m + 1 → False := fun m h1 h2 => by
    have h := Nat.le_of_dvd (by norm_num) (ggDvd_two_of_dvd_pow_sub_add h1 h2)
    have := hp.two_le
    omega
  have hmul : ∀ k, f ∣ k → p ∣ 2 ^ k - 1 := fun k hk => by
    obtain ⟨c, rfl⟩ := hk
    have h1 : 1 ≡ 2 ^ f [MOD p] := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).2 hpf
    have h2 : 1 ≡ 2 ^ (f * c) [MOD p] := by simpa [pow_mul] using h1.pow c
    exact (Nat.modEq_iff_dvd' Nat.one_le_two_pow).1 h2
  rcases hiso.n_cases with h | h | h
  · exact hno _ (hmul _ (h ▸ hf)) hK
  · exact hK2 h
  · exact hno _ (hmul _ (h ▸ dvd_mul_of_dvd_right hf 2)) hK

@[expose] def ggRowP_Ennola (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ggRowP_E p lab ∨ (ggRowP_NF4 p lab ∧ p = 3 ∧ p ∣ 2 ^ lab.n + 1)

@[expose] def GGTCJEnnolaKnown : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab fun R _ I _ => ggRowP_Ennola p lab →
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ e : MulAut L', e ^ p = 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (e l)) →
          ∀ J : Subgroup L', CFSG.Assembly.IsComponentOf J (ggFixSub e) →
            ∀ labJ₀ : LargeEvenLabel, LargeEvenInLambda2 labJ₀ →
              GGHasLabel labJ₀ (J ⧸ Subgroup.center J) →
              ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
                GGHasLabel labJ (J ⧸ Subgroup.center J) ∧ p ∣ 2 ^ labJ.n + 1 ∧
                ¬ (labJ.tag = .twD ∧ labJ.rank = 2)

theorem ggIsComponentOf_inf_centralizer_nbr {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G}
    {K : Subgroup G} (hnb : GGNbr p B x D J y K) (hJK : J ≤ K) :
    IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) := by
  have hSS := hcfg.1.2.2.2.2.2.2.1
  have hst := hcfg.1.2.2.2.2.2.2.2
  have hJY := isComponentOf_inf_centralizer_of_stdSub hSS hcfg.2.2.1 hnb.2.1
  obtain ⟨hKc, -⟩ := isComponentOf_of_isNeighborOf hst (isNeighborOf_of_ggNbr hcfg.2.2 hnb)
  have hle : K ⊓ Subgroup.centralizer ({x} : Set G) ≤
      Subgroup.centralizer ({y} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :=
    inf_le_inf_right _ hKc.1
  have hJle : J ≤ K ⊓ Subgroup.centralizer ({x} : Set G) := le_inf hJK (hJY.1.trans inf_le_right)
  have hsub := CFSG.Assembly.IsSubnormal.inf_of_le hJY.2.1 hle
  rw [inf_eq_left.mpr hJle] at hsub
  exact ⟨hJle, hsub, hJY.2.2⟩

theorem ggNbr_label_J_ennola (hKn : GGTCJEnnolaKnown) (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) {y : G} {K : Subgroup G}
    (hK : GGInnerDiagOnLabel ggRowP_Ennola p Bs K) (hnb : GGNbr p B x D J y K)
    (labJ₀ : LargeEvenLabel) (hΛ₀ : LargeEvenInLambda2 labJ₀)
    (hhas₀ : GGHasLabel labJ₀ (J ⧸ Subgroup.center J)) :
    ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧ GGHasLabel labJ (J ⧸ Subgroup.center J) ∧
      p ∣ 2 ^ labJ.n + 1 ∧ ¬ (labJ.tag = .twD ∧ labJ.rank = 2) := by
  have hT : GGThmIHyp p B x L := hcfg.1
  have hp : p.Prime := hT.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hT.2.2.2.2.2.1.2.1
  have hSS := hT.2.2.2.2.2.2.1
  have hBel : IsElemAbelian p B := hSS.1.1
  have hxB : x ∈ B := hSS.2.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 hxB
  have hJK : J ≤ K := le_of_ggNbr hLB hT hcfg.2.2 (hP G p B x L D J hT hcfg.2.2) hnb
  have hcomp := ggIsComponentOf_inf_centralizer_nbr hcfg hnb hJK
  have hKperf : commutator ↥K = ⊤ := hK.1
  have hM := ggMarking_and_labelAll_dep (fun lab hlab => hKn p hp hp2 lab hlab) hK
  obtain ⟨lab, -, -, R, _, I, F, θ, ⟨⟨hS, hNK, hind⟩, hTC⟩⟩ :=
    largeEvenMarking_exists_hasLabel hM
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hNK hxBs
  have hx1 : x ^ p = 1 := hBel.2 x hxB
  have hep : K.normalizerMonoidHom ⟨x, hxN⟩ ^ p = 1 := by
    rw [← map_pow]
    have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ p = 1 :=
      Subtype.ext (by simpa using hx1)
    rw [h1, map_one]
  obtain ⟨φ, hφI, hφ⟩ := hind x⁻¹ (Bs.inv_mem hxBs)
  let ψ : ↥K →* R := (θ : K ⧸ Subgroup.center K →* R).comp (QuotientGroup.mk' (Subgroup.center K))
  have hψsurj : Function.Surjective ψ := fun r => by
    obtain ⟨q, rfl⟩ := θ.surjective r
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨l, rfl⟩
  have hψker : ψ.ker ≤ Subgroup.center ↥K := fun l hl => by
    have h0 : θ (QuotientGroup.mk l) = 1 := hl
    have h1 : (QuotientGroup.mk l : K ⧸ Subgroup.center K) = 1 := by
      simpa using θ.injective (h0.trans (map_one θ).symm)
    exact (QuotientGroup.eq_one_iff l).mp h1
  have hφe : ∃ φ ∈ I, ∀ l : ↥K, φ (ψ l) = ψ (K.normalizerMonoidHom ⟨x, hxN⟩ l) := by
    refine ⟨φ, hφI, fun l => hφ l (K.normalizerMonoidHom ⟨x, hxN⟩ l) ?_⟩
    show ((K.normalizerMonoidHom ⟨x, hxN⟩ l : ↥K) : G) = x⁻¹⁻¹ * (l : G) * x⁻¹
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, inv_inv]
  have hJcomp := ggIsComponentOf_ggFixSub_normalizerMonoidHom hxN hcomp
  let eJ : ↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K) ≃* ↥J ⧸ Subgroup.center ↥J :=
    QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJK) (Subgroup.map_center_eq _)
  obtain ⟨labJ, hlabJ, hhasJ, hd, h2⟩ :=
    hTC hS ↥K ψ hψsurj hψker hKperf _ hep hφe (J.subgroupOf K) hJcomp labJ₀ hΛ₀
      (ggHasLabel_of_mulEquiv eJ.symm hhas₀)
  exact ⟨labJ, hlabJ, ggHasLabel_of_mulEquiv eJ hhasJ, hd, h2⟩

section Split

@[expose] def GGSplitLieLabelInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (L : Subgroup G), p.Prime → p ≠ 2 →
    GGSplitLie p L → ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      GGHasLabel lab (L ⧸ Subgroup.center L) ∧ p ∣ 2 ^ lab.n - 1

theorem ggRowEnnola_absurd
    (hRig : GGLabelRigidInput) (hTCJ : GGTCJKnown)
    (hKn : GGTCJEnnolaKnown) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    (hBr : GGSplitLieLabelInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hL : GGSplitLie p L)
    {K : Subgroup G} (hK : K ∈ 𝒦) (hrow : GGInnerDiagOnLabel ggRowP_Ennola p Bs K) : False := by
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  obtain ⟨y, hnb⟩ := hcfg.2.2.2.1.2 K hK
  have hInnL : GGInnerDiagOn Bs L := hcfg.1.2.2.1.1
  obtain ⟨labL, hΛL, hhasL, hpL⟩ := hBr G p L hp hp2 hL
  have hLlab : GGInnerDiagOnLabel (fun p lab => p ∣ 2 ^ lab.n - 1) p Bs L :=
    largeEvenMarking_mono (fun lab _ _ _ _ _ ⟨he, hP⟩ => ⟨he ▸ hpL, hP⟩)
      (ggInnerDiagOn_relabel hRig hInnL hΛL hhasL)
  obtain ⟨lab, labJ, -, hS, -, hΛJ, hdvd, hhasJ⟩ :=
    ggNbr_label_J_of_tcj_onLabel hTCJ hcfg.1.1 hLlab hnb
  obtain ⟨labJ', hΛJ', hhasJ', hJ1, hJ2⟩ :=
    ggNbr_label_J_ennola hKn hLB hP hcfg.1.1 hrow hnb labJ hΛJ hhasJ
  exact ggLabelIso_ennola_absurd hp hp2 (hRig _ _ _ hΛJ' hΛJ hhasJ' hhasJ) hdvd hS hJ1 hJ2

end Split

end CFSG.StandardType

end
