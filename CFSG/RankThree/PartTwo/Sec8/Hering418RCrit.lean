module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF418.Rows
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.KF418.Type418
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.RankThree.PartTwo.Sec6.Item65One
public import CFSG.RankThree.PartTwo.Sec8.Hering418Model

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering418

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.AGLEmbeddingD2.Wilson.Coordinator.KF418

@[expose] def NoCommute37 (S : Type*) [Group S] : Prop :=
  ∀ y z : S, orderOf y = 3 → orderOf z = 7 → y * z ≠ z * y

@[expose] def NoNineDvd (S : Type*) [Group S] : Prop :=
  ∀ x : S, ¬ 9 ∣ orderOf x

@[expose] def HasNineQuot (X : Type*) [Group X] : Prop :=
  ∃ y : X, y ^ 9 ∈ Subgroup.center X ∧ y ^ 3 ∉ Subgroup.center X

section Criteria


theorem kF418ModelOn_of_noCommute37 {P : ∀ (X : Type) [Group X], Prop}
    (hinner : ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → P X →
      ∀ σ : MulAut X, σ ^ 3 = 1 → σ ∈ (MulAut.conj : X →* MulAut X).range)
    (hexcl : ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → P X →
      NoCommute37 (X ⧸ Subgroup.center X)) : KF418ModelOn P := by
  intro G _ _ L hL hl a b ha3 hb3 hab hb1 habz haN hbN hbC haC K hK n hn htype hKa
  exfalso
  have c := Cfg.of_model hK ha3 hb3 hab haN hbN hbC haC hKa
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hT := type418Arith_of hn hKq htype
  have hq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) := hL.2.2
  have hαI : c.alpha ∈ innBar L := hinner _ hq hl _ c.alpha_pow_three
  have hβI : c.beta ∈ innBar L := hinner _ hq hl _ c.beta_pow_three
  obtain ⟨hβo, -, h7⟩ := exists_centralizer_of_inner c.hKL c.hKb c.ha3 c.hb3 c.hab c.haL c.hbL
    c.hβ1 c.haK c.hout hT hαI hβI
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  haveI : Finite (MulAut (L ⧸ aschbacherSolvableCore 3 L)) :=
    Finite.of_injective (fun α : MulAut (L ⧸ aschbacherSolvableCore 3 L) => (α : _ → _))
      fun _ _ h => MulEquiv.ext (congrFun h)
  obtain ⟨w, hw7⟩ := exists_prime_orderOf_dvd_card' (G := ↥(innBar L ⊓
    Subgroup.centralizer {rho L ⟨b, c.hbL⟩})) 7 h7
  have hwI : (w : MulAut (L ⧸ aschbacherSolvableCore 3 L)) ∈ innBar L := w.2.1
  have hwc : (w : MulAut (L ⧸ aschbacherSolvableCore 3 L)) * c.beta =
      c.beta * (w : MulAut (L ⧸ aschbacherSolvableCore 3 L)) :=
    Subgroup.mem_centralizer_singleton_iff.mp w.2.2
  let e := quotCenterEquivInn (L ⧸ aschbacherSolvableCore 3 L)
  let z0 : (MulAut.conj : (L ⧸ aschbacherSolvableCore 3 L) →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).range := ⟨w, hwI⟩
  let y0 : (MulAut.conj : (L ⧸ aschbacherSolvableCore 3 L) →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).range := ⟨c.beta, hβI⟩
  refine hexcl _ hq hl (e.symm y0) (e.symm z0) ?_ ?_ ?_
  · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hβo
  · rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, Subgroup.orderOf_coe]
    exact hw7
  · rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hwc.symm

theorem ker_rhoK_le {G : Type} [Group G] [Finite G] {L K : Subgroup G} (hKL : K ≤ L) :
    (rhoK hKL).ker ≤ (Subgroup.center (K ⧸ aschbacherSolvableCore 3 K)).comap
      (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) := by
  intro k hk
  rw [Subgroup.mem_comap]
  have h1 : rho L ⟨k, L.le_normalizer (hKL k.2)⟩ = 1 := hk
  have h2 := thetaQuot_eq_one_of_rho_eq_one hKL (L.le_normalizer (hKL k.2))
    (K.le_normalizer k.2) h1
  rw [thetaQuot_eq_conj K k.2] at h2
  exact mem_center_of_conj_eq_one h2

theorem Cfg.exists_nine_dvd_orderOf_rhoK {G : Type} [Group G] [Finite G] {L K : Subgroup G}
    {a b : G} (c : Cfg L K a b) (h : HasNineQuot (K ⧸ aschbacherSolvableCore 3 K)) :
    ∃ k : K, 9 ∣ orderOf (rhoK c.hKL k) := by
  obtain ⟨y, hy9, hy3⟩ := h
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective y
  set x : MulAut (L ⧸ aschbacherSolvableCore 3 L) := rhoK c.hKL k with hx
  refine ⟨k, ?_⟩
  show 9 ∣ orderOf x
  set Z := Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) with hZ
  set yb : (K ⧸ aschbacherSolvableCore 3 K) ⧸ Z := QuotientGroup.mk (QuotientGroup.mk k) with hyb
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h9 : yb ^ 9 = 1 := by
    rw [hyb, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, ← QuotientGroup.mk_pow]
    exact hy9
  have h3 : ¬ yb ^ (3 ^ 1) = 1 := by
    rw [pow_one, hyb, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, ← QuotientGroup.mk_pow]
    exact hy3
  have hord : orderOf yb = 3 ^ 2 := orderOf_eq_prime_pow (n := 1) h3 (by simpa using h9)
  have hxm : yb ^ orderOf x = 1 := by
    have hk1 : k ^ orderOf x ∈ (rhoK c.hKL).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact pow_orderOf_eq_one x
    have := ker_rhoK_le c.hKL hk1
    rw [Subgroup.mem_comap] at this
    rw [hyb, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    simpa using this
  have := orderOf_dvd_of_pow_eq_one hxm
  rw [hord] at this
  simpa using this

theorem Cfg.exists_nine_dvd_orderOf {G : Type} [Group G] [Finite G] {L K : Subgroup G} {a b : G}
    (c : Cfg L K a b) (h : HasNineQuot (K ⧸ aschbacherSolvableCore 3 K)) :
    ∃ x : MulAut (L ⧸ aschbacherSolvableCore 3 L), x ∈ innBar L ∧ 9 ∣ orderOf x := by
  obtain ⟨k, hk⟩ := c.exists_nine_dvd_orderOf_rhoK h
  exact ⟨rhoK c.hKL k, rho_mem_innBar L (c.hKL k.2), hk⟩

theorem kF418ModelOn_of_no_nine {P : ∀ (X : Type) [Group X], Prop}
    (hnine : ∀ (X : Type) [Group X] (n : ℕ), 1 ≤ n → IsQuasisimple X → IsType418 X n →
      HasNineQuot X)
    (hno : ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → P X →
      NoNineDvd (X ⧸ Subgroup.center X)) : KF418ModelOn P := by
  intro G _ _ L hL hl a b ha3 hb3 hab hb1 habz haN hbN hbC haC K hK n hn htype hKa
  exfalso
  have c := Cfg.of_model hK ha3 hb3 hab haN hbN hbC haC hKa
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsIn hK
  have hq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) := hL.2.2
  obtain ⟨x, hxI, hx9⟩ := c.exists_nine_dvd_orderOf (hnine _ n hn hKq htype)
  haveI : Finite (MulAut (L ⧸ aschbacherSolvableCore 3 L)) :=
    Finite.of_injective (fun α : MulAut (L ⧸ aschbacherSolvableCore 3 L) => (α : _ → _))
      fun _ _ h => MulEquiv.ext (congrFun h)
  let e := quotCenterEquivInn (L ⧸ aschbacherSolvableCore 3 L)
  let x0 : (MulAut.conj : (L ⧸ aschbacherSolvableCore 3 L) →*
      MulAut (L ⧸ aschbacherSolvableCore 3 L)).range := ⟨x, hxI⟩
  refine hno _ hq hl (e.symm x0) ?_
  rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
  exact hx9

end Criteria

end CFSG.RankThree.PartTwo.Sec8.Hering418
