module

public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6K318Red
public import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.SectionRank CFSG.SectionRank.Ccomm
open CFSG.LocalAnalysis.UniquenessCase.UC6.K318 (le_or_eq_top_of_normal pRank_le_of_le
  le_four_of_card_frattini)
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

@[expose] def CriticalSection206 {H K : Type} [Group H] [Group K] (κ : K →* H) (Y : Subgroup K)
    (p : ℕ) (Q : Subgroup H) (r : ℕ) : Prop :=
  ∃ R : Subgroup Q, ∃ _ : R.Characteristic, R ≠ ⊥ ∧ (∀ x ∈ R, x ^ p = 1) ∧
    ⁅R, (⊤ : Subgroup Q)⁆ ≤ R ⊓ centralizer (R : Set Q) ∧
    (∀ x ∈ centralizer (R : Set Q), orderOf x = p → x ∈ R) ∧
    IsPGroup p (frattiniAction R).ker ∧ commutator R ≤ center R ∧
    ∃ d : ℕ, Nat.card (R ⧸ frattini R) = p ^ d ∧ (r ≤ 3 → d ≤ 4) ∧
      ∃ e : R ⧸ frattini R ≃* Multiplicative (Fin d → ZMod p),
      ∃ φ : H →* GL (Fin d) (ZMod p), (φ.comp κ).ker ≤ Y ∧
        ∀ (g : H) (x y : R), ((y : Q) : H) = g * ((x : Q) : H) * g⁻¹ →
          (φ g : Matrix (Fin d) (Fin d) (ZMod p)) *ᵥ
              Multiplicative.toAdd (e (x : R ⧸ frattini R)) =
            Multiplicative.toAdd (e (y : R ⧸ frattini R))

theorem uc22s206c_range_le_centralizer {H K : Type} [Group H] [Group K] [Finite K]
    [Group.IsPerfect K] (κ : K →* H) {p : ℕ} [Fact p.Prime] {Q : Subgroup H} [Q.Normal]
    (h : IsPGroup p ((MulAut.conjNormal (H := Q)).comp κ).range) :
    κ.range ≤ centralizer (Q : Set H) := by
  set c : K →* MulAut Q := (MulAut.conjNormal (H := Q)).comp κ with hc
  haveI : Group.IsPerfect c.range := Group.IsPerfect.range c
  haveI : Finite c.range := Finite.of_surjective _ c.rangeRestrict_surjective
  have hc1 : c.range = ⊥ := by
    by_contra hne
    haveI : Nontrivial c.range := (nontrivial_iff_ne_bot _).2 hne
    exact Group.IsPerfect.not_isNilpotent c.range h.isNilpotent
  rintro _ ⟨k, rfl⟩
  rw [mem_centralizer_iff]
  intro x hx
  have hck : c k = 1 := by
    have hmem : c k ∈ c.range := ⟨k, rfl⟩
    rw [hc1, mem_bot] at hmem
    exact hmem
  have h2 := congrArg (fun σ : MulAut Q => ((σ ⟨x, hx⟩ : Q) : H)) hck
  simp only [hc, MonoidHom.comp_apply, MulAut.conjNormal_apply, MulAut.one_apply] at h2
  calc x * κ k = κ k * x * (κ k)⁻¹ * κ k := by rw [h2]
    _ = κ k * x := by group

theorem uc22s206c_ker_le {H K : Type} [Group H] [Group K] [Finite K] [Group.IsPerfect K]
    {Y : Subgroup K} [Y.Normal] (hYs : Group.IsSolvable Y) (hs : IsSimpleGroup (K ⧸ Y))
    (κ : K →* H) {p : ℕ} [Fact p.Prime] {Q : Subgroup H} [Q.Normal] (R : Subgroup Q)
    [R.Characteristic] (hker : IsPGroup p (frattiniAction R).ker)
    (hnc : ¬ κ.range ≤ centralizer (Q : Set H)) :
    (((frattiniAction R).comp (MulAut.conjNormal (H := Q))).comp κ).ker ≤ Y := by
  rcases le_or_eq_top_of_normal hYs hs
      (((frattiniAction R).comp (MulAut.conjNormal (H := Q))).comp κ).ker with h | h
  · exact h
  · exfalso
    apply hnc
    apply uc22s206c_range_le_centralizer κ (p := p)
    refine hker.to_le ?_
    rintro _ ⟨k, rfl⟩
    have hk : k ∈ (((frattiniAction R).comp (MulAut.conjNormal (H := Q))).comp κ).ker :=
      h ▸ mem_top k
    exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hk)

theorem uc22s206c_exists {H K : Type} [Group H] [Finite H] [Group K] [Finite K]
    [Group.IsPerfect K] {Y : Subgroup K} [Y.Normal] (hYs : Group.IsSolvable Y)
    (hs : IsSimpleGroup (K ⧸ Y)) (κ : K →* H) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Q : Subgroup H) [Q.Normal] (hQ : IsPGroup p Q)
    (hnc : ¬ κ.range ≤ centralizer (Q : Set H)) :
    CriticalSection206 κ Y p Q (CFSG.Open.pRank p (⊤ : Subgroup H)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI hQnt : Nontrivial Q := by
    rw [nontrivial_iff_ne_bot]
    intro hbot
    apply hnc
    rintro _ ⟨k, rfl⟩
    rw [mem_centralizer_iff]
    intro x hx
    have hx' : x ∈ Q := hx
    rw [hbot, mem_bot] at hx'
    rw [hx', one_mul, mul_one]
  obtain ⟨R, hRc, hRne, hRp, hRZ, hRΩ, hker⟩ := supercritical_witness hp2 hQ
  set α : H →* MulAut (R ⧸ frattini R) :=
    (frattiniAction R).comp (MulAut.conjNormal (H := Q)) with hα
  have hαK : (α.comp κ).ker ≤ Y := uc22s206c_ker_le hYs hs κ R hker hnc
  have hRq : IsPGroup p R := hQ.to_subgroup R
  obtain ⟨-, hWcomm, hWpow⟩ := frattini_quotient_elementary hRq
  obtain ⟨d, hd⟩ := (hRq.to_quotient (frattini R)).exists_card_eq
  have hexp : ∀ x : R, x ^ p = 1 := fun x => Subtype.ext (by simpa using hRp x x.2)
  have hclass : commutator R ≤ center R := by
    rw [_root_.commutator_def, commutator_le]
    intro a _ b _
    rw [mem_center_iff]
    intro z
    have hab : ⁅(a : Q), (b : Q)⁆ ∈ centralizer (R : Set Q) :=
      (hRZ (commutator_mem_commutator a.2 (mem_top (b : Q)))).2
    apply Subtype.ext
    have h1 := mem_centralizer_iff.1 hab (z : Q) z.2
    simpa [commutatorElement_def] using h1
  obtain ⟨e⟩ := nonempty_mulEquiv_of_elementary hWcomm hWpow hd
  unfold CriticalSection206
  refine ⟨R, hRc, hRne, hRp, hRZ, hRΩ, hker, hclass, d, hd, fun hr =>
    le_four_of_card_frattini hRq hexp hclass ((pRank_le_of_le hp.one_lt le_top R).trans hr) hd,
    e, (elemAutEquivGL e).toMonoidHom.comp α, ?_, ?_⟩
  · intro k hk
    apply hαK
    rw [MonoidHom.mem_ker] at hk ⊢
    apply (elemAutEquivGL e).injective
    rw [map_one]
    exact hk
  · intro g x y hxy
    have h1 := elemAutEquivGL_mulVec e (α g) (x : R ⧸ frattini R)
    rw [hα, MonoidHom.comp_apply, frattiniAction_mk] at h1
    have hy : (⟨MulAut.conjNormal g (x : Q),
        (MulAut.characteristic R (MulAut.conjNormal g) x).2⟩ : R) = y :=
      Subtype.ext (Subtype.ext (by rw [MulAut.conjNormal_apply]; exact hxy.symm))
    rw [hy] at h1
    exact h1

theorem uc22s206c_exists_prime [Finite G] {M : Subgroup G} {X : Subgroup (Bar2 M)}
    (hF : ⁅X, CFSG.fittingSubgroup (Bar2 M)⁆ ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧ ¬ X ≤ centralizer (CFSG.pCore p (Bar2 M) : Set (Bar2 M)) := by
  by_contra hall
  push Not at hall
  apply hF
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, CFSG.fitting_eq_sup_pCore]
  apply CFSG.subgroup_le_centralizer_iSup_of_le_centralizer
  intro q
  have hq : q.1.1.Prime := Nat.prime_of_mem_primeFactors q.1.2
  by_cases hq2 : q.1.1 = 2
  · have h2 : CFSG.pCore 2 (Bar2 M) = ⊥ :=
      CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot (H := ↥M) (p := 2)
    rw [hq2, h2]
    intro x _
    rw [mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, mem_bot] at hy
    rw [hy, one_mul, mul_one]
  · exact hall q.1.1 hq hq2

theorem uc22s206c_pRank_le [Finite G] (M : Subgroup G) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (Bar2 M)) ≤ CFSG.Open.pRank p M := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : ¬ p ∣ Nat.card (CFSG.pCore 2 ↥M) := by
    intro hdvd
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥M))
    rw [hn] at hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow hdvd))
  rw [CFSG.SectionRank.pRank_quotient_eq (CFSG.pCore 2 ↥M) hN]
  have h := CFSG.SectionRank.pRank_le_map hp.one_lt M.subtype M.subtype_injective ⊤
  rwa [Subgroup.map_top, Subgroup.range_subtype] at h

theorem uc22s206c_critical [Finite G] {M K : Subgroup G} (hKM : K ≤ M) (hKp : ⁅K, K⁆ = K)
    (h8 : IsAlt (Bar2 K) 8)
    (hF : ⁅(K.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)),
      CFSG.fittingSubgroup (Bar2 M)⁆ ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
      ¬ (K.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ≤
        centralizer (CFSG.pCore p (Bar2 M) : Set (Bar2 M)) ∧
      CriticalSection206 ((QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hKM))
        (CFSG.pCore 2 ↥K) p (CFSG.pCore p (Bar2 M)) (CFSG.Open.pRank p M) := by
  obtain ⟨p, hp, hp2, hnc⟩ := uc22s206c_exists_prime hF
  refine ⟨p, hp, hp2, hnc, ?_⟩
  set κ : ↥K →* Bar2 M := (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hKM)
    with hκ
  have hrange : κ.range = (K.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) := by
    rw [hκ, MonoidHom.range_comp, Subgroup.inclusion_range]
  haveI : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.2 hKp
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e8⟩ := h8
  haveI : IsSimpleGroup (alternatingGroup (Fin 8)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; norm_num)
  have hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := e8.isSimpleGroup
  have hYs : Group.IsSolvable ↥(CFSG.pCore 2 ↥K) := by
    have := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).isNilpotent
    infer_instance
  have h := uc22s206c_exists hYs hs κ hp hp2 (CFSG.pCore p (Bar2 M)) CFSG.pCore_isPGroup
    (by rw [hrange]; exact hnc)
  have hr := uc22s206c_pRank_le M hp hp2
  unfold CriticalSection206 at h ⊢
  obtain ⟨R, hRc, h1, h2, h3, h4, h5, h6, d, hd, hd4, rest⟩ := h
  exact ⟨R, hRc, h1, h2, h3, h4, h5, h6, d, hd, fun h => hd4 (hr.trans h), rest⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
