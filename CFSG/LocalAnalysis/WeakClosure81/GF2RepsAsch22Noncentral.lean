module

import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319
import CFSG.RankThree.OddKernel.CompleteRankComparison
public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut
import CFSG.Monster.B.TwoA.Base.ElemAut

namespace CFSG.LocalAnalysis.WeakClosure81.Asch22

theorem conjNormal_ker_le_of_simple_quotient {Y : Type*} [Group Y] (P : Subgroup Y) [P.Normal]
    [IsSimpleGroup (Y ⧸ P)]
    (hmin : ∀ M : Subgroup Y, M.map (QuotientGroup.mk' P) = ⊤ → M = ⊤)
    (hnc : ¬ P ≤ Subgroup.center Y) :
    (MulAut.conjNormal (H := P)).ker ≤ P := by
  let C := (MulAut.conjNormal (H := P)).ker
  have hCn : C.Normal := MonoidHom.normal_ker _
  have hmapn : (C.map (QuotientGroup.mk' P)).Normal :=
    hCn.map (QuotientGroup.mk' P) (QuotientGroup.mk'_surjective P)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map (QuotientGroup.mk' P)) with hbot | htop
  · rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
  · exfalso
    have hCtop : C = ⊤ := hmin C htop
    apply hnc
    intro b hb
    rw [Subgroup.mem_center_iff]
    intro y
    have hyC : y ∈ C := by rw [hCtop]; exact Subgroup.mem_top y
    have hy1 : MulAut.conjNormal (H := P) y = 1 := MonoidHom.mem_ker.mp hyC
    have h1 := congrArg (fun f : MulAut ↥P => (f ⟨b, hb⟩ : ↥P)) hy1
    simp only [MulAut.one_apply] at h1
    have h2 : y * b * y⁻¹ = b := by
      simpa using congrArg (fun z : ↥P => (z : Y)) h1
    calc y * b = y * b * y⁻¹ * y := by group
      _ = b * y := by rw [h2]

theorem exists_frattini_quotient_card_eq_pow_le_three {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y] (P : Subgroup Y) [P.Normal]
    (hP : IsPGroup p P)
    (hmin : ∀ M : Subgroup Y, M.map (QuotientGroup.mk' P) = ⊤ → M = ⊤)
    (D : Subgroup P) [D.Characteristic] (hDne : D ≠ ⊥)
    (hexp : ∀ x ∈ D, x ^ p = 1)
    (hDZ : ⁅D, (⊤ : Subgroup P)⁆ ≤ D ⊓ Subgroup.centralizer (D : Set P))
    (hrk : CFSG.pRank p Y ≤ 3) :
    ∃ n : ℕ, Nat.card (D ⧸ frattini D) = p ^ n ∧ n ≤ 3 := by
  classical
  have hDp : IsPGroup p D := hP.to_subgroup D
  have hDexp : ∀ x : D, x ^ p = 1 := fun x => Subtype.ext (hexp x.1 x.2)
  have : Nontrivial ↥D := (Subgroup.nontrivial_iff_ne_bot D).mpr hDne
  have hexpD : Monoid.exponent ↥D = p := by
    refine (Monoid.exponent_eq_prime_iff (Fact.out : p.Prime)).mpr ?_
    intro x hx
    have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hDexp x)
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd with h1 | hp'
    · exact absurd (orderOf_eq_one_iff.mp h1) hx
    · exact hp'
  have hclass : _root_.commutator ↥D ≤ Subgroup.center ↥D := by
    rw [_root_.commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have h := hDZ (Subgroup.commutator_mem_commutator a.2 (Subgroup.mem_top (b : ↥P)))
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.1 h.2 (g : ↥P) g.2
  obtain ⟨n, hcard⟩ := (hDp.to_quotient (frattini ↥D)).exists_card_eq
  obtain ⟨-, hWc, hWp⟩ := CFSG.SectionRank.Ccomm.frattini_quotient_elementary hDp
  have hfr : frattini ↥D = _root_.commutator ↥D :=
    CFSG.RankThree.PartTwo.frattini_eq_commutator hDp hDexp
  have hWn : CFSG.pRank p (↥D ⧸ frattini ↥D) = n :=
    CFSG.RankThree.PartTwo.pRank_eq_of_isMulCommutative (Fact.out : p.Prime) hWp
      ⟨⟨hWc⟩⟩ hcard
  have hrk' : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 3 := by
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top p Y]
    exact hrk
  have hDrank : CFSG.pRank p ↥D ≤ 3 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top p ↥D]
    exact (CFSG.SectionRank.pRank_top_le_of_injective (Fact.out : p.Prime).one_lt
      (P.subtype.comp D.subtype)
      (P.subtype_injective.comp D.subtype_injective)).trans hrk'
  have hrankq : CFSG.pRank p (↥D ⧸ _root_.commutator ↥D) = n := by
    rw [← hWn, CFSG.SectionRank.pRank_eq_open_pRank_top,
      CFSG.SectionRank.pRank_eq_open_pRank_top]
    exact (CFSG.SectionRank.pRank_top_eq_of_mulEquiv (Fact.out : p.Prime).one_lt
      (QuotientGroup.quotientMulEquivOfEq hfr)).symm
  have hbounds := CFSG.RankThree.PartTwo.class_two_small_rank_order_bounds hDp hDexp hclass
  have hn4 : n ≤ 4 := hrankq ▸ hbounds.2.2 hDrank
  have hn4ne : n ≠ 4 := by
    intro h
    have h3 := CFSG.RankThree.OddKernel.frattini_dim_eq_three (n := 4) hp2 P hP hmin D
      hexpD hDZ hrk (Or.inr (Or.inl rfl))
      (show Nat.card (↥D ⧸ frattini ↥D) = p ^ 4 by rw [← h]; exact hcard)
    exact absurd h3 (by norm_num)
  exact ⟨n, hcard, by omega⟩

theorem pRank_quotient_le_two_of_frattiniConjAction {p n : ℕ} (hp : p.Prime)
    {Y : Type*} [Group Y] [Finite Y] (P : Subgroup Y) [P.Normal]
    (D : Subgroup P) [D.Characteristic]
    (R : Subgroup Y) [R.Normal]
    (hKR : (CFSG.RankThree.OddKernel.frattiniConjAction P D).ker ≤ R)
    (hRp : IsPGroup p (R.map (CFSG.RankThree.OddKernel.frattiniConjAction P D)))
    (e : D ⧸ frattini D ≃* Multiplicative (Fin n → ZMod p))
    (hn : n ≤ 3) :
    CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ R)) ≤ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let α := CFSG.RankThree.OddKernel.frattiniConjAction P D
  obtain ⟨ψ, hψsurj, hψker, -⟩ :=
    CFSG.RankThree.OddKernel.exists_range_hom_quotient α hKR
  have hBp : IsPGroup p ψ.ker := by
    rw [hψker]
    have hmap : (R.map α.rangeRestrict).map α.range.subtype = R.map α := by
      rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]
    exact hRp.of_equiv (hmap ▸ (Subgroup.equivMapOfInjective (R.map α.rangeRestrict)
      α.range.subtype Subtype.val_injective).symm)
  let ι : α.range →* GL (Fin n) (ZMod p) :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp α.range.subtype
  have hιinj : Function.Injective ι :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).injective.comp Subtype.val_injective
  refine CFSG.SectionRank.pRank_le hp.one_lt ?_
  intro E _ hE
  have hEp : IsPGroup p E := CFSG.Open.IsElemAbelian.isPGroup hE
  obtain ⟨k, hk⟩ := hEp.exists_card_eq
  let F : Subgroup α.range := E.comap ψ
  have hFp : IsPGroup p F := IsPGroup.comap_of_ker_isPGroup hEp ψ hBp
  have hQp : IsPGroup p (F.map ι) := hFp.map ι
  have hQle : Nat.card (F.map ι) ≤
      p ^ CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input319.Nexp n :=
    CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input319.gl_pSub_card_le p n hQp
  have hQcard : Nat.card (F.map ι) = Nat.card F := Subgroup.card_map_of_injective hιinj
  let φ : F →* E := (ψ.comp F.subtype).codRestrict E fun y => Subgroup.mem_comap.mp y.2
  have hφsurj : Function.Surjective φ := by
    intro x
    obtain ⟨y, hy⟩ := hψsurj (x : Y ⧸ R)
    refine ⟨⟨y, ?_⟩, ?_⟩
    · rw [Subgroup.mem_comap, hy]; exact x.2
    · apply Subtype.ext; exact hy
  have hcardF : Nat.card F = Nat.card E * Nat.card (MonoidHom.ker φ) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (MonoidHom.ker φ)
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).toEquiv] at h
    exact h
  have hEdiv : Nat.card E ∣ Nat.card F := ⟨Nat.card (MonoidHom.ker φ), hcardF⟩
  have hLE : Nat.card E ≤ Nat.card F :=
    Nat.le_of_dvd (Nat.card_pos (α := ↥F)) hEdiv
  have hk_le : k ≤ CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input319.Nexp n := by
    have hpow : p ^ k ≤
        p ^ CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input319.Nexp n := by
      rw [← hk]
      exact hLE.trans (hQcard ▸ hQle)
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hpow
  have hNexp3 : CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input319.Nexp 3 = 3 := by
    have h := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input319.Nexp_mul_two 3
    norm_num at h
    omega
  have hNexp2 : CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input319.Nexp 2 = 1 := by
    have h := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input319.Nexp_mul_two 2
    norm_num at h
    omega
  have hk2 : k ≤ 2 := by
    by_contra hk2
    have hk3 : 3 ≤ k := by omega
    have hNle3 : 3 ≤ CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input319.Nexp n :=
      hk3.trans hk_le
    have hn3 : n = 3 := by
      rcases lt_or_ge n 3 with hlt | hge
      · have hn2 : n ≤ 2 := by omega
        have hmono := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input319.Nexp_mono hn2
        omega
      · omega
    have hNn : CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input319.Nexp n = 3 := by
      rw [hn3, hNexp3]
    have hk3' : k = 3 := by omega
    have hcardE3 : Nat.card E = p ^ 3 := by rw [hk, hk3']
    have hFcardle : Nat.card F ≤ p ^ 3 := by
      have h := hQle
      rw [hQcard, hNn] at h
      exact h
    have hker1 : Nat.card (MonoidHom.ker φ) = 1 := by
      have hle : p ^ 3 * Nat.card (MonoidHom.ker φ) ≤ p ^ 3 * 1 := by
        rw [mul_one]
        calc p ^ 3 * Nat.card (MonoidHom.ker φ)
            = Nat.card E * Nat.card (MonoidHom.ker φ) := by rw [hcardE3]
          _ = Nat.card F := hcardF.symm
          _ ≤ p ^ 3 := hFcardle
      have hmle : Nat.card (MonoidHom.ker φ) ≤ 1 :=
        Nat.le_of_mul_le_mul_left hle (pow_pos hp.pos 3)
      have hmpos : 0 < Nat.card (MonoidHom.ker φ) := Nat.card_pos
      omega
    have hφinj : Function.Injective φ :=
      (MonoidHom.ker_eq_bot_iff φ).mp (Subgroup.card_eq_one.mp hker1)
    have hElemab : CFSG.Open.IsElemAbelian p F := by
      have hinj : Function.Injective (E.subtype.comp φ) :=
        E.subtype_injective.comp hφinj
      have hcomap := CFSG.Open.IsElemAbelian.comap (E := E)
        (f := E.subtype.comp φ) hE hinj
      have htop : E.comap (E.subtype.comp φ) = ⊤ := by
        ext x
        simp only [Subgroup.mem_comap, Subgroup.mem_top, iff_true]
        exact (φ x).2
      have hmapF : (⊤ : Subgroup F).map F.subtype = F := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [htop] at hcomap
      exact hmapF ▸ CFSG.SectionRank.isElemAbelian_map hcomap F.subtype
    have hQel : CFSG.Open.IsElemAbelian p (F.map ι) :=
      CFSG.SectionRank.isElemAbelian_map hElemab ι
    have hbound := CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input319.gl_elemAb_card_le
      p n (by omega) (Q := F.map ι) hQel
    have hcardMap : Nat.card (F.map ι) = p ^ 3 := by
      rw [hQcard, hcardF, hcardE3, hker1, mul_one]
    rw [hcardMap, hNn] at hbound
    have : 3 ≤ 3 - 1 := (Nat.pow_le_pow_iff_right hp.one_lt).mp hbound
    omega
  rw [hk]
  exact Nat.pow_le_pow_right hp.pos hk2

end CFSG.LocalAnalysis.WeakClosure81.Asch22

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch22

theorem pRank_quotient_centralizer_sup_le_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y] (Q : Subgroup Y) [Q.Normal]
    (hQ : IsPGroup p Q)
    (hmin : ∀ M : Subgroup Y, M.map (QuotientGroup.mk' Q) = ⊤ → M = ⊤)
    (hperf : ∀ N : Subgroup (Y ⧸ Q), N.Normal → ⁅N, N⁆ = N)
    (hrk : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 3)
    (R : Subgroup Y) [R.Normal] (hR : R = Subgroup.centralizer (Q : Set Y) ⊔ Q) :
    CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ R)) ≤ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  let C : Subgroup Y := Subgroup.centralizer (Q : Set Y)
  by_cases hQbot : Q = ⊥
  · have hCtop : Subgroup.centralizer (Q : Set Y) = ⊤ := by
      rw [hQbot]
      ext x
      rw [Subgroup.mem_centralizer_iff]
      simp
    have hRtop : R = ⊤ := by rw [hR, hCtop, hQbot, sup_bot_eq]
    have hsub : Subsingleton (Y ⧸ R) := QuotientGroup.subsingleton_iff.mpr hRtop
    refine CFSG.SectionRank.pRank_le hp.one_lt (fun E _ _ => ?_)
    have hEbot : E = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x _
      exact hsub.allEq x 1
    rw [hEbot, Subgroup.card_bot]
    have hpos : 0 < p ^ 2 := pow_pos hp.pos 2
    omega
  · have hnt : Nontrivial ↥Q := (Subgroup.nontrivial_iff_ne_bot Q).mpr hQbot
    obtain ⟨D, hDc, hDne, hDexp, hDZ, -, hkerD⟩ :=
      CFSG.SectionRank.Ccomm.supercritical_witness (p := p) hp2 (Q := ↥Q) hQ
    let : D.Characteristic := hDc
    let α := CFSG.RankThree.OddKernel.frattiniConjAction Q D
    have hCker : C ≤ α.ker := by
      intro x hx
      rw [MonoidHom.mem_ker]
      have hconj : MulAut.conjNormal (H := Q) x = 1 := by
        refine MulEquiv.ext fun q => Subtype.ext ?_
        rw [MulAut.conjNormal_apply, MulAut.one_apply,
          ← Subgroup.mem_centralizer_iff.mp hx q q.2, mul_inv_cancel_right]
      simp [α, CFSG.RankThree.OddKernel.frattiniConjAction, hconj]
    have hC_le_R : C ≤ R := by rw [hR]; exact le_sup_left
    have hQ_le_R : Q ≤ R := by rw [hR]; exact le_sup_right
    have hCmap : C.map α = ⊥ :=
      (Subgroup.map_eq_bot_iff (H := C) (f := α)).mpr hCker
    have hRp : IsPGroup p (R.map α) := by
      rw [hR, Subgroup.map_sup, hCmap, bot_sup_eq]
      exact hQ.map α
    have hKR : α.ker ≤ R := by
      let N₀ : Subgroup Y := α.ker
      have hN₀normal : N₀.Normal := MonoidHom.normal_ker α
      let q : Y ⧸ Q →* Y ⧸ R := QuotientGroup.map Q R (MonoidHom.id Y) hQ_le_R
      have hq_comp : q.comp (QuotientGroup.mk' Q) = QuotientGroup.mk' R := by
        ext y
        exact QuotientGroup.map_mk (N := Q) (M := R) (f := MonoidHom.id Y)
          (h := hQ_le_R) y
      let X : Subgroup (Y ⧸ Q) := (N₀ ⊔ R).map (QuotientGroup.mk' Q)
      have hsupN : (N₀ ⊔ R).Normal := inferInstance
      have hXnormal : X.Normal := hsupN.map _ (QuotientGroup.mk'_surjective Q)
      have hXperfect : Group.IsPerfect ↥X :=
        Subgroup.isPerfect_iff.mpr (hperf X hXnormal)
      let f : N₀ →* Y ⧸ R := (QuotientGroup.mk' R).comp N₀.subtype
      have hfker : f.ker = (N₀ ⊓ R).subgroupOf N₀ := by
        ext x
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
          QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
      have htop : (⊤ : Subgroup N₀).map N₀.subtype = N₀ := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      have hfrange : f.range = N₀.map (QuotientGroup.mk' R) := by
        rw [show f = (QuotientGroup.mk' R).comp N₀.subtype from rfl,
          MonoidHom.range_eq_map, ← Subgroup.map_map, htop]
      have hRmap : R.map (QuotientGroup.mk' R) = ⊥ := by
        rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      have hXq : X.map q = f.range := by
        rw [show X = (N₀ ⊔ R).map (QuotientGroup.mk' Q) from rfl,
          Subgroup.map_map, hq_comp, Subgroup.map_sup, hRmap, sup_bot_eq, hfrange]
      let β : N₀ →* MulAut Q := (MulAut.conjNormal (H := Q)).comp N₀.subtype
      have hconjker : (MulAut.conjNormal (H := Q)).ker = C := by
        ext x
        rw [MonoidHom.mem_ker, Subgroup.mem_centralizer_iff]
        constructor
        · intro h q hq
          have h1 := congrArg (fun φ : MulAut Q => ((φ ⟨q, hq⟩ : Q) : Y)) h
          simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
          calc q * x = x * q * x⁻¹ * x := by rw [h1]
            _ = x * q := by group
        · intro h
          refine MulEquiv.ext fun q => Subtype.ext ?_
          rw [MulAut.conjNormal_apply, MulAut.one_apply, ← h q q.2, mul_inv_cancel_right]
      have hβker : β.ker = (N₀ ⊓ C).subgroupOf N₀ := by
        have hcomp : β.ker =
            ((MulAut.conjNormal (H := Q)).ker).comap N₀.subtype := by
          rw [show β = (MulAut.conjNormal (H := Q)).comp N₀.subtype from rfl,
            ← MonoidHom.comap_ker]
        rw [hcomp, hconjker]
        ext x
        rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨fun h => ⟨x.2, h⟩, fun h => h.2⟩
      have hβrange : β.range ≤ (CFSG.SectionRank.Ccomm.frattiniAction D).ker := by
        rintro _ ⟨y, rfl⟩
        simpa [β, α, CFSG.RankThree.OddKernel.frattiniConjAction] using
          MonoidHom.mem_ker.mp y.2
      have hβrangeP : IsPGroup p β.range :=
        IsPGroup.of_injective hkerD (Subgroup.inclusion hβrange)
          (Subgroup.inclusion_injective hβrange)
      have hpC : IsPGroup p (N₀ ⧸ (N₀ ⊓ C).subgroupOf N₀) :=
        (hβrangeP.of_equiv (QuotientGroup.quotientKerEquivRange β).symm).of_equiv
          (QuotientGroup.quotientMulEquivOfEq hβker)
      have hle : (N₀ ⊓ C).subgroupOf N₀ ≤ (N₀ ⊓ R).subgroupOf N₀ :=
        Subgroup.subgroupOf_mono N₀ (inf_le_inf_left N₀ hC_le_R)
      have hpR : IsPGroup p (N₀ ⧸ (N₀ ⊓ R).subgroupOf N₀) := by
        let qq : N₀ ⧸ (N₀ ⊓ C).subgroupOf N₀ →* N₀ ⧸ (N₀ ⊓ R).subgroupOf N₀ :=
          QuotientGroup.map _ _ (MonoidHom.id N₀) hle
        have hqq : Function.Surjective qq :=
          QuotientGroup.map_surjective_of_surjective _ _ (MonoidHom.id N₀)
            (QuotientGroup.mk'_surjective _) hle
        exact hpC.of_surjective qq hqq
      have hpR' : IsPGroup p (N₀ ⧸ f.ker) :=
        hpR.of_equiv (QuotientGroup.quotientMulEquivOfEq hfker).symm
      have hfrangep : IsPGroup p f.range :=
        hpR'.of_equiv (QuotientGroup.quotientKerEquivRange f)
      have hfrangperfect : Group.IsPerfect ↥f.range := by
        have hmap := Group.IsPerfect.map (H := X) q
        rwa [hXq] at hmap
      have hfrbot : f.range = ⊥ := by
        by_contra hne
        have hntR : Nontrivial ↥f.range := (Subgroup.nontrivial_iff_ne_bot f.range).mpr hne
        have hperfR : Group.IsPerfect ↥f.range := hfrangperfect
        exact Group.IsPerfect.not_isNilpotent ↥f.range hfrangep.isNilpotent
      intro x hx
      have hx1 : QuotientGroup.mk' R x = 1 := by
        have hmem : QuotientGroup.mk' R x ∈ f.range :=
          MonoidHom.mem_range.mpr ⟨⟨x, hx⟩, rfl⟩
        rw [hfrbot] at hmem
        exact Subgroup.mem_bot.mp hmem
      exact (QuotientGroup.eq_one_iff x).mp hx1
    have hrk' : CFSG.pRank p Y ≤ 3 := by
      rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
      exact hrk
    obtain ⟨n, hcard, hn3⟩ :=
      exists_frattini_quotient_card_eq_pow_le_three hp2 Q hQ hmin D hDne hDexp hDZ hrk'
    have hDp : IsPGroup p D := hQ.to_subgroup D
    obtain ⟨-, hWc, hWp⟩ := CFSG.SectionRank.Ccomm.frattini_quotient_elementary hDp
    obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary hWc hWp hcard
    exact pRank_quotient_le_two_of_frattiniConjAction hp Q D R hKR hRp e hn3

theorem pRank_quotient_le_two_of_not_le_center {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y] (P : Subgroup Y) [P.Normal]
    (hP : IsPGroup p P) (hS : IsSimpleGroup (Y ⧸ P))
    (hmin : ∀ M : Subgroup Y, M.map (QuotientGroup.mk' P) = ⊤ → M = ⊤)
    (hnc : ¬ P ≤ Subgroup.center Y) (hrk : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 3) :
    CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ P)) ≤ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsSimpleGroup (Y ⧸ P) := hS
  let C : Subgroup Y := Subgroup.centralizer (P : Set Y)
  have hCker : C ≤ (MulAut.conjNormal (H := P)).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    refine MulEquiv.ext fun q => Subtype.ext ?_
    rw [MulAut.conjNormal_apply, MulAut.one_apply,
      ← Subgroup.mem_centralizer_iff.mp hx q q.2, mul_inv_cancel_right]
  have hCP : C ≤ P := hCker.trans (conjNormal_ker_le_of_simple_quotient P hmin hnc)
  have hR : P = Subgroup.centralizer (P : Set Y) ⊔ P := (sup_eq_right.mpr hCP).symm
  have hQperf : Group.IsPerfect (Y ⧸ P) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective P)
  have hperf : ∀ N : Subgroup (Y ⧸ P), N.Normal → ⁅N, N⁆ = N := by
    intro N hN
    have hNnormal : N.Normal := hN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
    · rw [hbot, Subgroup.commutator_bot_left]
    · rw [htop]
      exact hQperf.commutator_eq_top
  exact pRank_quotient_centralizer_sup_le_two hp hp2 P hP hmin hperf hrk P hR

theorem pRank_quotient_le_three_of_not_le_center {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Y : Type*} [Group Y] [Finite Y] [Group.IsPerfect Y] (P : Subgroup Y) [P.Normal]
    (hP : IsPGroup p P) (hS : IsSimpleGroup (Y ⧸ P))
    (hmin : ∀ M : Subgroup Y, M.map (QuotientGroup.mk' P) = ⊤ → M = ⊤)
    (hnc : ¬ P ≤ Subgroup.center Y) (hrk : CFSG.Open.pRank p (⊤ : Subgroup Y) ≤ 3) :
    CFSG.Open.pRank p (⊤ : Subgroup (Y ⧸ P)) ≤ 3 := by
  exact (pRank_quotient_le_two_of_not_le_center hp hp2 P hP hS hmin hnc hrk).trans
    (by norm_num : 2 ≤ 3)

end CFSG.LocalAnalysis.WeakClosure81.Asch22
