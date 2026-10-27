module

public import CFSG.Quasithin.Vol2.KGFactJ4BlockB
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4B
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentCEQuasisimple
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4ThreeClass

public section

namespace CFSG.Quasithin.H13.Ch4.J4Blk

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.KGC31 CFSG.Quasithin.KGC31.J4M4
open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

@[expose] def BlockConcl {K : Type} [Group K] (B : Subgroup K) : Prop :=
  Subgroup.normalizer (B : Set K) = B ∧
    Subgroup.centralizer (pCoreOf 2 B : Set K) = pCoreOf 2 B ∧
    (∀ W : Subgroup K, W ≤ pCoreOf 2 B → B ≤ Subgroup.normalizer (W : Set K) →
      W = ⊥ ∨ W = pCoreOf 2 B) ∧
    ∃ x : K, x ∈ B ∧ orderOf x = 3 ∧
      pCoreOf 2 B ⊓ Subgroup.centralizer ({x} : Set K) ≠ ⊥ ∧
      CFSG.IsQuasisimple ↥(perfectCore (Subgroup.centralizer ({x} : Set K))) ∧
      Nat.card ↥(Subgroup.center ↥(perfectCore (Subgroup.centralizer ({x} : Set K)))) = 6 ∧
      IsSporadic .M22 (↥(perfectCore (Subgroup.centralizer ({x} : Set K))) ⧸
        Subgroup.center ↥(perfectCore (Subgroup.centralizer ({x} : Set K)))) ∧
      ¬ pCoreOf 2 B ⊓ Subgroup.centralizer ({x} : Set K) ≤
        Subgroup.centralizer (perfectCore (Subgroup.centralizer ({x} : Set K)) : Set K)

section Transport

variable {K K' : Type} [Group K] [Group K']

theorem map_centralizer_mulEquiv (f : K ≃* K') (s : Set K) :
    (Subgroup.centralizer s).map f.toMonoidHom = Subgroup.centralizer (f '' s) := by
  ext y
  rw [Subgroup.mem_map_equiv, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · rintro h _ ⟨b, hb, rfl⟩
    apply f.symm.injective
    rw [map_mul, map_mul, MulEquiv.symm_apply_apply, h b hb]
  · intro h b hb
    have h1 := congrArg f.symm (h (f b) ⟨b, hb, rfl⟩)
    rwa [map_mul, map_mul, MulEquiv.symm_apply_apply] at h1

theorem map_centralizer_subgroup (f : K ≃* K') (Q : Subgroup K) :
    (Subgroup.centralizer (Q : Set K)).map f.toMonoidHom =
      Subgroup.centralizer ((Q.map f.toMonoidHom : Subgroup K') : Set K') := by
  rw [map_centralizer_mulEquiv, Subgroup.coe_map, MulEquiv.coe_toMonoidHom]

theorem map_centralizer_singleton (f : K ≃* K') (x : K) :
    (Subgroup.centralizer ({x} : Set K)).map f.toMonoidHom =
      Subgroup.centralizer ({f.toMonoidHom x} : Set K') := by
  have h := map_centralizer_mulEquiv f {x}
  rw [Set.image_singleton] at h
  exact h

theorem blockConcl_of_map (f : K ≃* K') {B : Subgroup K} (h : BlockConcl (B.map f.toMonoidHom)) :
    BlockConcl B := by
  obtain ⟨hN, hC, hirr, x', hx'B, hx3, hne, hq, hz, hM, hnot⟩ := h
  have hQ : (pCoreOf 2 B).map f.toMonoidHom = pCoreOf 2 (B.map f.toMonoidHom) :=
    NoJ4.blockQ_map f.toMonoidHom f.injective B
  obtain ⟨x, hxB, rfl⟩ := hx'B
  have hPC : (perfectCore (Subgroup.centralizer ({x} : Set K))).map f.toMonoidHom =
      perfectCore (Subgroup.centralizer ({f.toMonoidHom x} : Set K')) := by
    rw [NoJ4.perfectCore_map f.toMonoidHom f.injective, map_centralizer_singleton]
  have eP : ↥(perfectCore (Subgroup.centralizer ({x} : Set K))) ≃*
      ↥(perfectCore (Subgroup.centralizer ({f.toMonoidHom x} : Set K'))) :=
    ((perfectCore (Subgroup.centralizer ({x} : Set K))).equivMapOfInjective f.toMonoidHom
      f.injective).trans (MulEquiv.subgroupCongr hPC)
  refine ⟨?_, ?_, ?_, x, hxB, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
    rw [Subgroup.map_equiv_normalizer_eq, hN]
  ·
    apply Subgroup.map_injective (f := f.toMonoidHom) f.injective
    rw [map_centralizer_subgroup, hQ, hC]
  ·
    intro W hWQ hBW
    have h1 : W.map f.toMonoidHom ≤ pCoreOf 2 (B.map f.toMonoidHom) :=
      (Subgroup.map_mono hWQ).trans hQ.le
    have h2 : B.map f.toMonoidHom ≤
        Subgroup.normalizer ((W.map f.toMonoidHom : Subgroup K') : Set K') := by
      rw [← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono hBW
    rcases hirr _ h1 h2 with h3 | h3
    · exact Or.inl ((Subgroup.map_eq_bot_iff_of_injective W f.injective).mp h3)
    · refine Or.inr (Subgroup.map_injective (f := f.toMonoidHom) f.injective ?_)
      rw [h3, hQ]
  ·
    rw [← hx3]
    exact (MulEquiv.orderOf_eq f x).symm
  ·
    intro hb
    apply hne
    rw [← hQ, ← map_centralizer_singleton, ← Subgroup.map_inf_eq _ _ f.toMonoidHom f.injective,
      hb, Subgroup.map_bot]
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv eP.symm hq
  · rw [← NoJ4.center_map_mulEquiv eP.symm, Subgroup.card_map_of_injective eP.symm.injective]
    exact hz
  · exact NoJ4.isSporadic_of_mulEquiv .M22 _ _
      (QuotientGroup.congr _ _ eP.symm (NoJ4.center_map_mulEquiv eP.symm)) hM
  · intro hle
    apply hnot
    have h1 := Subgroup.map_mono (f := f.toMonoidHom) hle
    rwa [Subgroup.map_inf_eq _ _ f.toMonoidHom f.injective, hQ, map_centralizer_singleton,
      map_centralizer_subgroup, hPC] at h1

theorem blockConcl_of_bijective (f : K →* K') (hf : Function.Bijective f) {B : Subgroup K}
    (h : BlockConcl (B.map f)) : BlockConcl B := by
  have he : (MulEquiv.ofBijective f hf).toMonoidHom = f := MonoidHom.ext fun _ => rfl
  refine blockConcl_of_map (MulEquiv.ofBijective f hf) ?_
  rw [he]
  exact h

theorem centralizer_facts_of_conj {b c g : K} (hg : g * b * g⁻¹ = c)
    (hq : CFSG.IsQuasisimple ↥(Subgroup.centralizer ({c} : Set K)))
    (hc : Nat.card ↥(Subgroup.center ↥(Subgroup.centralizer ({c} : Set K))) = 6)
    (hm : Nonempty (↥(Subgroup.centralizer ({c} : Set K)) ⧸
      Subgroup.center ↥(Subgroup.centralizer ({c} : Set K)) ≃*
        ↥CFSG.Blueprint.NativeSporadic.M22)) :
    CFSG.IsQuasisimple ↥(Subgroup.centralizer ({b} : Set K)) ∧
      Nat.card ↥(Subgroup.center ↥(Subgroup.centralizer ({b} : Set K))) = 6 ∧
      IsSporadic .M22 (↥(Subgroup.centralizer ({b} : Set K)) ⧸
        Subgroup.center ↥(Subgroup.centralizer ({b} : Set K))) := by
  have hC : (Subgroup.centralizer ({b} : Set K)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({c} : Set K) := by
    have h1 := map_centralizer_singleton (MulAut.conj g) b
    have h2 : (MulAut.conj g).toMonoidHom b = c := hg
    rw [h2] at h1
    exact h1
  have e := ((Subgroup.centralizer ({b} : Set K)).equivMapOfInjective
    (MulAut.conj g).toMonoidHom (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hC)
  obtain ⟨hm⟩ := hm
  refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq, ?_, ?_⟩
  · rw [← NoJ4.center_map_mulEquiv e.symm, Subgroup.card_map_of_injective e.symm.injective]
    exact hc
  · exact ⟨(QuotientGroup.congr _ _ e (NoJ4.center_map_mulEquiv e)).trans hm⟩

end Transport

attribute [local instance] finite_J

theorem centralizer_of_orderOf_three
    {b : J} (hb : orderOf b = 3) :
    CFSG.IsQuasisimple ↥(Subgroup.centralizer ({b} : Set J)) ∧
      Nat.card ↥(Subgroup.center ↥(Subgroup.centralizer ({b} : Set J))) = 6 ∧
      IsSporadic .M22 (↥(Subgroup.centralizer ({b} : Set J)) ⧸
        Subgroup.center ↥(Subgroup.centralizer ({b} : Set J))) := by
  have hb3 : b ^ 3 = 1 := by rw [← hb, pow_orderOf_eq_one]
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hb
    norm_num at hb
  obtain ⟨g, hg⟩ :=
    CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.exists_conj_cE_of_orderThree b hb3 hb1
  obtain ⟨hq, hc, hm⟩ :=
    CFSG.AGLEmbeddingD2.Wilson.NormalizerAction.centralizer_cE_quasisimple j4Facts
  exact centralizer_facts_of_conj hg hq hc hm

theorem x_facts
    {E : Subgroup J} (hE : IsPGroup 2 ↥E) {x : J}
    (hx : orderOf x = 3) (h4 : 4 ≤ Nat.card ↥(E ⊓ Subgroup.centralizer ({x} : Set J))) :
    E ⊓ Subgroup.centralizer ({x} : Set J) ≠ ⊥ ∧
      CFSG.IsQuasisimple ↥(perfectCore (Subgroup.centralizer ({x} : Set J))) ∧
      Nat.card ↥(Subgroup.center ↥(perfectCore (Subgroup.centralizer ({x} : Set J)))) = 6 ∧
      IsSporadic .M22 (↥(perfectCore (Subgroup.centralizer ({x} : Set J))) ⧸
        Subgroup.center ↥(perfectCore (Subgroup.centralizer ({x} : Set J)))) ∧
      ¬ E ⊓ Subgroup.centralizer ({x} : Set J) ≤
        Subgroup.centralizer (perfectCore (Subgroup.centralizer ({x} : Set J)) : Set J) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hq, hc, hm⟩ := centralizer_of_orderOf_three hx
  have hP : perfectCore (Subgroup.centralizer ({x} : Set J)) =
      Subgroup.centralizer ({x} : Set J) :=
    perfectCore_eq_self_of_perfect (Subgroup.isPerfect_iff.mp hq.1)
  rw [hP]
  refine ⟨fun h => ?_, hq, hc, hm, fun hle => ?_⟩
  · rw [h, Subgroup.card_bot] at h4
    norm_num at h4
  · set C := Subgroup.centralizer ({x} : Set J) with hCdef
    set D := E ⊓ C with hD
    have hDC : D ≤ C := inf_le_right
    have hDZ : D.subgroupOf C ≤ Subgroup.center ↥C := by
      intro d hd
      rw [Subgroup.mem_subgroupOf] at hd
      rw [Subgroup.mem_center_iff]
      intro c
      apply Subtype.ext
      have h1 := Subgroup.mem_centralizer_iff.mp (hle hd) c c.2
      simpa using h1
    have hdvd : Nat.card D ∣ 6 := by
      rw [← hc, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv]
      exact Subgroup.card_dvd_of_le hDZ
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hE.to_le (inf_le_left : D ≤ E))
    rw [hn] at h4 hdvd
    have hco : Nat.Coprime (2 ^ n) 3 := Nat.Coprime.pow_left n (by norm_num)
    have h2 : 2 ^ n ∣ 2 := hco.dvd_of_dvd_mul_right (show 2 ^ n ∣ 2 * 3 from hdvd)
    have := Nat.le_of_dvd (by norm_num) h2
    omega

theorem blockConcl_Hj :
    BlockConcl Hj := by
  obtain ⟨x, hxH, hx3, h4⟩ := exists_orderOf_three_Hj
  obtain ⟨h1, h2, h3, h5, h6⟩ := x_facts (isPGroup_Eg (elem_uJ j4Facts.mat)) hx3 h4
  refine ⟨normalizer_Hj, ?_, ?_, x, hxH, hx3, ?_⟩
  · rw [pCoreOf_Hj]
    exact centralizer_Eg
  · rw [pCoreOf_Hj]
    exact fun W hW hHW => minimal_Eg W hW hHW
  · rw [pCoreOf_Hj]
    exact ⟨h1, h2, h3, h5, h6⟩

end CFSG.Quasithin.H13.Ch4.J4Blk
