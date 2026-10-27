module

public import CFSG.RankThree.PartOne.S9.Sylow.GlobalOddCore
public import CFSG.RankThree.PartTwo.ExponentPrimeSmallRank
public import CFSG.RankThree.CentralExtension.MinimalCoverFrattini
public import CFSG.RankThree.PartOne.FTL.Frattini
public import CFSG.RankThree.PartOne.SRC.RankOneAux
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.RankThree.PartOne.SRC

open Subgroup CFSG
open scoped commutatorElement

theorem card_quotient_commutator_le {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {W : Type*} [Group W] [Finite W]
    [Group.IsPerfect W] (C : Subgroup W) [C.Normal]
    (hmin : ∀ M : Subgroup W, M.map (QuotientGroup.mk' C) = ⊤ → M = ⊤)
    (D : Subgroup W) [D.Normal] (hDC : D ≤ C) (hDp : IsPGroup p D) (hexp : ∀ x : D, x ^ p = 1)
    (hclass : commutator ↥D ≤ center ↥D) (hrank : CFSG.pRank p ↥D ≤ 3) :
    Nat.card (↥D ⧸ commutator ↥D) ≤ p ^ 3 := by
  have : Fact p.Prime := ⟨hp⟩
  have hDq : IsPGroup p (↥D ⧸ commutator ↥D) := hDp.to_quotient _
  obtain ⟨k, hk⟩ := hDq.exists_card_eq
  obtain ⟨-, hprk⟩ := CFSG.RankThree.PartTwo.quotient_commutator_rank hp hexp hk
  obtain ⟨hb1, hb2, hb3⟩ := CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hDp hexp hclass
  have hk4 : k ≤ 4 := by
    have := hb3 hrank
    omega
  by_contra hlt
  have hk4' : k = 4 := by
    have : 3 < k := by
      by_contra h
      push Not at h
      exact hlt (by rw [hk]; exact Nat.pow_le_pow_right hp.pos h)
    omega
  have hr3 : CFSG.pRank p ↥D = 3 := by
    have h3 : ¬ CFSG.pRank p ↥D ≤ 2 := fun h => by
      have := hb1 h
      omega
    omega
  obtain ⟨i, hi, -⟩ := hb2 hr3
  fin_cases i
  · simp at hi
    omega
  · simp at hi
    obtain ⟨-, hcard, hZ, -⟩ := hi
    exact CFSG.RankThree.CentralExtension.perfect_minimal_cover_excludes_extraspecial_frattini_subgroup
      hp2 C hmin ⟨D, inferInstance, hDC, fun d hd => by simpa using hexp ⟨d, hd⟩, hZ.symm, hcard⟩
  · simp at hi
    omega

theorem isPGroup_quotient_of_map_eq_top {W Q : Type*} [Group W] [Group Q] (ρ : W →* Q) {p : ℕ}
    (hker : IsPGroup p ρ.ker) (N : Subgroup W) [N.Normal] (hN : N.map ρ = ⊤) :
    IsPGroup p (W ⧸ N) := by
  intro x
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x
  have hw : ρ w ∈ N.map ρ := hN ▸ Subgroup.mem_top _
  obtain ⟨n, hn, hnw⟩ := Subgroup.mem_map.mp hw
  have hc : n⁻¹ * w ∈ ρ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hnw, inv_mul_cancel]
  obtain ⟨k, hk⟩ := hker ⟨n⁻¹ * w, hc⟩
  refine ⟨k, ?_⟩
  have h1 : (n⁻¹ * w) ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have h2 : (QuotientGroup.mk w : W ⧸ N) = QuotientGroup.mk (n⁻¹ * w) := by
    rw [QuotientGroup.eq]
    have := (inferInstance : N.Normal).conj_mem n⁻¹ (N.inv_mem hn) w⁻¹
    simpa [mul_assoc] using this
  rw [h2, ← QuotientGroup.mk_pow, h1, QuotientGroup.mk_one]

theorem central_of_rank_le_three_gen {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {W Q : Type*} [Group W] [Finite W] [Group Q] [Finite Q] [hperf : Group.IsPerfect W]
    (ρ : W →* Q) (hρ : Function.Surjective ρ)
    (hker : IsPGroup p ρ.ker) (hmin : ∀ M : Subgroup W, M.map ρ = ⊤ → M = ⊤)
    (hbig : ∀ K₁ : Subgroup Q, K₁.Normal → ∀ n : ℕ, n ≤ 3 →
      Nat.card Q ∣ Nat.card K₁ * Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod p)) →
        K₁ = ⊤)
    (hgen : ∀ N : Subgroup Q, N.Normal → (∀ h : Q, Nat.Coprime (orderOf h) p → h ∈ N) →
      N = ⊤)
    (hrank : ∀ E : Subgroup W, IsElementaryAbelian p E → Nat.card E ≤ p ^ 3) :
    ρ.ker ≤ center W := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_contra hC
  have hC1 : ρ.ker ≠ ⊥ := fun h0 => hC (h0 ▸ bot_le)
  have hmin' : ∀ M : Subgroup W, M.map (QuotientGroup.mk' ρ.ker) = ⊤ → M = ⊤ := by
    intro M hM
    apply hmin
    have h1 : M.map ρ = (M.map (QuotientGroup.mk' ρ.ker)).map (QuotientGroup.kerLift ρ) := by
      rw [Subgroup.map_map]; rfl
    rw [h1, hM, Subgroup.map_top]
    refine MonoidHom.range_eq_top.mpr fun q => ?_
    obtain ⟨w, rfl⟩ := hρ q
    exact ⟨QuotientGroup.mk w, rfl⟩
  obtain ⟨D, hDC, hD1, hDnorm, hDexp, hDcomm, hDdet⟩ :=
    CFSG.RankThree.PartOne.Sec9B.exists_critical hp hp2 hker hC1
  have hDN : D.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    refine eq_top_iff.mpr fun g _ => hDnorm g ?_
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top g
  have hDp : IsPGroup p D := hker.to_le hDC
  have hexpD : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (hDexp x x.2)
  have hclass : commutator ↥D ≤ center ↥D := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have h1 := hDcomm (Subgroup.commutator_mem_commutator a.2 (hDC b.2))
    rw [Subgroup.mem_center_iff]
    intro c
    have h2 := Subgroup.mem_centralizer_iff.mp h1.2 (c : W) c.2
    exact Subtype.ext h2
  have hrankD : CFSG.pRank p ↥D ≤ 3 := by
    refine CFSG.RankThree.PartTwo.pRank_le_of_forall_isMulCommutative hp fun E hE => ?_
    have hEel : IsElementaryAbelian p (E.map D.subtype) := by
      refine { toIsMulCommutative := Subgroup.map_isMulCommutative E D.subtype, exponent_dvd_p := ?_ }
      refine Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun x => ?_
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp x.2
      apply Subtype.ext
      rw [Subgroup.coe_pow, ← hyx]
      simpa using hDexp y y.2
    have := hrank _ hEel
    rwa [Subgroup.card_map_of_injective D.subtype_injective] at this
  have hcardV := card_quotient_commutator_le hp hp2 ρ.ker hmin' D hDC hDp hexpD hclass hrankD
  have hfc : frattini ↥D = commutator ↥D :=
    CFSG.RankThree.PartTwo.frattini_eq_commutator hDp hexpD
  have hVp : IsPGroup p (↥D ⧸ frattini ↥D) := hDp.to_quotient _
  obtain ⟨n, hn⟩ := hVp.exists_card_eq
  have hVcard : Nat.card (↥D ⧸ frattini ↥D) = Nat.card (↥D ⧸ commutator ↥D) :=
    Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hfc).toEquiv
  have hn3 : n ≤ 3 := by
    have : p ^ n ≤ p ^ 3 := by rw [← hn, hVcard]; exact hcardV
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp this
  have hcomm : ∀ a b : ↥D ⧸ frattini ↥D, a * b = b * a := by
    intro a b
    have := CFSG.RankThree.PartTwo.isMulCommutative_quotient_commutator (P := ↥D)
    apply (QuotientGroup.quotientMulEquivOfEq hfc).injective
    rw [map_mul, map_mul]
    exact this.is_comm.comm _ _
  have hpow : ∀ a : ↥D ⧸ frattini ↥D, a ^ p = 1 :=
    CFSG.RankThree.PartTwo.quotient_pow_eq_one hexpD _
  obtain ⟨ecoord⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := p) hcomm hpow hn
  let ψ : W →* MulAut (↥D ⧸ frattini ↥D) :=
    (CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism (frattini ↥D)).comp
      MulAut.conjNormal
  have hψ1 : ψ.ker = ⊤ := by
    set K₁ : Subgroup Q := ψ.ker.map ρ with hK₁
    have hK₁n : K₁.Normal := Subgroup.Normal.map inferInstance ρ hρ
    have hcardQ := Subgroup.card_eq_card_quotient_mul_card_subgroup K₁
    let f : W ⧸ ψ.ker →* Q ⧸ K₁ :=
      QuotientGroup.map ψ.ker K₁ ρ (fun x hx => Subgroup.mem_map_of_mem ρ hx)
    have hfs : Function.Surjective f := by
      intro q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨w, rfl⟩ := hρ x
      exact ⟨QuotientGroup.mk w, rfl⟩
    have h2 : Nat.card (Q ⧸ K₁) ∣ Nat.card (W ⧸ ψ.ker) := Subgroup.card_dvd_of_surjective hfs
    have h3 : Nat.card (W ⧸ ψ.ker) ∣ Nat.card (MulAut (↥D ⧸ frattini ↥D)) := by
      rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv]
      exact Subgroup.card_subgroup_dvd_card _
    have h4 := CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL ecoord
    have hdvd : Nat.card Q ∣ Nat.card K₁ *
        Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod p)) := by
      rw [hcardQ, mul_comm]
      exact mul_dvd_mul_left _ (h2.trans (h3.trans (h4 ▸ dvd_rfl)))
    have htop : K₁ = ⊤ := hbig K₁ hK₁n n hn3 hdvd
    have hpg := isPGroup_quotient_of_map_eq_top (p := p) ρ hker ψ.ker htop
    exact eq_top_of_perfect_pgroup_quotient ψ.ker hpg
  have hψ : ∀ g : W, ψ g = 1 := fun g => MonoidHom.mem_ker.mp (hψ1 ▸ Subgroup.mem_top g)
  have hdet : ∀ g : W, Nat.Coprime (orderOf g) p → ∀ m ∈ ρ.ker, g * m * g⁻¹ = m := by
    intro g hg m hm
    refine hDdet g ?_ ?_ hg m hm
    · rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      exact Subgroup.mem_top g
    · have hω : (MulAut.conjNormal g : MulAut ↥D) ^ (orderOf g) = 1 := by
        rw [← map_pow, pow_orderOf_eq_one, map_one]
      have htriv : CFSG.OrderReductions.FrattiniAutomorphisms.quotientAutomorphism
          (frattini ↥D) (MulAut.conjNormal g) = 1 := hψ g
      have h1 := CFSG.RankThree.PartOne.FTL.eq_one_of_trivial_mod_frattini hDp hω hg htriv
      intro x hx
      have h2 := congrArg (fun τ : MulAut ↥D => ((τ ⟨x, hx⟩ : ↥D) : W)) h1
      simpa [MulAut.conjNormal_apply] using h2
  have hcentn : (Subgroup.centralizer (ρ.ker : Set W)).Normal := by
    refine ⟨fun x hx w => ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : w⁻¹ * y * w ∈ ρ.ker := by
      have := (inferInstance : ρ.ker.Normal).conj_mem y hy w⁻¹
      simpa using this
    have hx' := Subgroup.mem_centralizer_iff.mp hx _ hy'
    calc y * (w * x * w⁻¹) = w * ((w⁻¹ * y * w) * x) * w⁻¹ := by group
      _ = w * (x * (w⁻¹ * y * w)) * w⁻¹ := by rw [hx']
      _ = w * x * w⁻¹ * y := by group
  have hmapn : ((Subgroup.centralizer (ρ.ker : Set W)).map ρ).Normal :=
    Subgroup.Normal.map hcentn ρ hρ
  have htop : (Subgroup.centralizer (ρ.ker : Set W)).map ρ = ⊤ := by
    refine hgen _ hmapn fun h hh => ?_
    obtain ⟨g, hgρ, hgo⟩ := exists_lift_coprime ρ hρ hp hh
    refine ⟨g, ?_, hgρ⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    have := hdet g hgo y hy
    calc y * g = (g * y * g⁻¹) * g := by rw [this]
      _ = g * y := by group
  have hpg := isPGroup_quotient_of_map_eq_top (p := p) ρ hker _ htop
  have hall := eq_top_of_perfect_pgroup_quotient (Subgroup.centralizer (ρ.ker : Set W)) hpg
  apply hC
  intro c hc
  rw [Subgroup.mem_center_iff]
  intro w
  have hw : w ∈ Subgroup.centralizer (ρ.ker : Set W) := hall ▸ Subgroup.mem_top w
  exact (Subgroup.mem_centralizer_iff.mp hw c hc).symm

theorem central_of_rank_le_three {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he : 4 ≤ e)
    {W Q : Type*} [Group W] [Finite W] [Group Q] [Finite Q] [hperf : Group.IsPerfect W]
    (hQ : CFSG.IsQuasisimple Q) (ρ : W →* Q) (hρ : Function.Surjective ρ)
    (hker : IsPGroup p ρ.ker) (hmin : ∀ M : Subgroup W, M.map ρ = ⊤ → M = ⊤)
    (hQp : p ^ e ∣ Nat.card Q) (hZ : Nat.Coprime p (Nat.card (center Q)))
    (h : Q) (hhc : h ∉ center Q) (hho : Nat.Coprime (orderOf h) p)
    (hrank : ∀ E : Subgroup W, IsElementaryAbelian p E → Nat.card E ≤ p ^ 3) :
    ρ.ker ≤ center W := by
  have : Fact p.Prime := ⟨hp⟩
  refine central_of_rank_le_three_gen hp hp2 ρ hρ hker hmin ?_ ?_ hrank
  · intro K₁ hK₁ n hn hdvd
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hK₁ with htop | hle
    · exact htop
    · exfalso
      have hK₁c : Nat.card K₁ ∣ Nat.card (center Q) := Subgroup.card_dvd_of_le hle
      have hcop : Nat.Coprime (p ^ e) (Nat.card K₁) :=
        Nat.Coprime.pow_left e (Nat.Coprime.coprime_dvd_right hK₁c hZ)
      have h1 : p ^ e ∣ Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod p)) :=
        hcop.dvd_of_dvd_mul_left (hQp.trans hdvd)
      exact not_pow_four_dvd_card_GL hn ((pow_dvd_pow p he).trans h1)
  · intro N hN hall
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hN with htop | hle
    · exact htop
    · exact absurd (hle (hall h hho)) hhc

end CFSG.RankThree.PartOne.SRC
