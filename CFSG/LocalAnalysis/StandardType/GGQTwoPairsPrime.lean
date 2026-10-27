module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAbsorbPrime
public import CFSG.LocalAnalysis.StandardType.GGQTwoPairsLK

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

open scoped commutatorElement

private theorem ggQ2nP_automizer_ne_bot {G : Type} [Group G] {Bs J : Subgroup G}
    (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) : ggAutomizer J Bs ≠ ⊥ := by
  intro hbot
  rw [hbot, Subgroup.card_bot] at hCav
  exact absurd hCav (by norm_num)

private theorem ggQ2nP_conjAut_conj_apply {G : Type} [Group G] {Bs : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) (t : MulAut ↥Bs) (b : ↥Bs) :
    (((ggConjAut Bs hg * t * (ggConjAut Bs hg)⁻¹) b : ↥Bs) : G) =
      g * (t ⟨g⁻¹ * b * g, ((ggConjAut Bs hg)⁻¹ b).2⟩ : G) * g⁻¹ := by
  rw [MulAut.mul_apply, MulAut.mul_apply, ggConjAut_apply]
  rfl

private theorem ggQ2nP_mem_ggInduced_map_conj {G : Type} [Group G] {Bs X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) {t : MulAut ↥Bs} (ht : t ∈ ggInduced X Bs) :
    ggConjAut Bs hg * t * (ggConjAut Bs hg)⁻¹ ∈
      ggInduced (X.map (MulAut.conj g).toMonoidHom) Bs := by
  obtain ⟨k, hkX, hkN, hk⟩ := ht
  refine ⟨g * k * g⁻¹, ⟨k, hkX, rfl⟩, ?_, fun b => ?_⟩
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hkN) (Subgroup.inv_mem _ hg)
  · rw [ggQ2nP_conjAut_conj_apply hg, hk]
    simp only
    group

private theorem ggQ2nP_commutator_conj_iff_aux {G : Type} [Group G] [Finite G] (p : ℕ)
    (X : Subgroup G) (g b : G) :
    (⁅X.map (MulAut.conj g).toMonoidHom, Subgroup.zpowers b⁆ : Subgroup G) ≤
        LargeEvenPPrimeCoreOf p (X.map (MulAut.conj g).toMonoidHom) ↔
      (⁅X, Subgroup.zpowers (g⁻¹ * b * g)⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p X := by
  have heq : (⁅X.map (MulAut.conj g).toMonoidHom, Subgroup.zpowers b⁆ : Subgroup G) =
      (⁅X, Subgroup.zpowers (g⁻¹ * b * g)⁆ : Subgroup G).map
        (MulAut.conj g).toMonoidHom := by
    rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
    congr 1
    congr 1
    simp [MulAut.conj_apply]
    group
  rw [heq, largeEvenPPrimeCoreOf_map_conj]
  exact map_conj_le_map_conj_iff g

private theorem ggQ2nP_commutator_zpowers_le {G : Type} [Group G] {X P : Subgroup G} {c : G}
    (hcP : c ∈ Subgroup.normalizer (P : Set G))
    (h : ∀ x ∈ X, ⁅x, c⁆ ∈ P) :
    ⁅X, Subgroup.zpowers c⁆ ≤ P := by
  rw [Subgroup.commutator_le]
  intro x hx z hz
  have hT : ∀ z ∈ Subgroup.zpowers c, ⁅x, z⁆ ∈ P := by
    let T : Subgroup G :=
      { carrier := {z : G | z ∈ Subgroup.normalizer (P : Set G) ∧ ⁅x, z⁆ ∈ P}
        one_mem' := ⟨Subgroup.one_mem _, by simp⟩
        mul_mem' := by
          intro y z hy hz
          obtain ⟨hyN, hyP⟩ := hy
          obtain ⟨hzN, hzP⟩ := hz
          refine ⟨Subgroup.mul_mem _ hyN hzN, ?_⟩
          have h1 : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
            rw [commutatorElement_def, commutatorElement_def]
            group
          rw [h1]
          exact P.mul_mem hyP ((Subgroup.mem_normalizer_iff.mp hyN _).mp hzP)
        inv_mem' := by
          intro y hy
          obtain ⟨hyN, hyP⟩ := hy
          refine ⟨Subgroup.inv_mem _ hyN, ?_⟩
          have h1 : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y := by
            rw [commutatorElement_def, commutatorElement_def]
            group
          have h2 : y⁻¹ * ⁅x, y⁆ * y ∈ P := by
            have h3 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) _).mp hyP
            simpa only [inv_inv] using h3
          rw [h1]
          simpa only [mul_inv_rev, inv_inv, mul_assoc] using Subgroup.inv_mem _ h2 }
    have hcT : c ∈ T := ⟨hcP, h x hx⟩
    intro z hz
    exact (Subgroup.zpowers_le.mpr hcT hz).2
  exact hT z hz

private theorem ggQ2nP_nbr_basic {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnbr : GGNbr p B x D J y K) :
    y ∈ Bs ∧ y ≠ 1 ∧ LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K ∧
      Bs ≤ Subgroup.normalizer (K : Set G) := by
  obtain ⟨hcfg, -, hIDAll, -, -⟩ := hHyp
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hBsabel : IsElemAbelian p Bs := hBstar.2.1
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hI hStdSub
  have hJq : CFSG.Assembly.IsQuasisimple ↥J := hStdSub.1.2.2.2.2.2.1.2.2
  have hJJ : ⁅J, J⁆ = J := commutator_self_eq_of_isQuasisimple hJq
  have hBsL : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hIDAll.1
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBsabel.1.is_comm.comm (⟨a, ha⟩ : ↥Bs) ⟨b, hb⟩)
  have hBsJ : Bs ≤ Subgroup.normalizer (J : Set G) :=
    GGDichotomy.le_normalizer_stdSub hcomm hBstar.1 hStdSub.1 hBsL
  have hyB : y ∈ B := hnbr.1.2.1
  have hy1 : y ≠ 1 := hnbr.1.2.2.1
  have hyBs : y ∈ Bs := hBstar.1 hyB
  have hKpc : LargeEvenPComponent p (Subgroup.centralizer ({y} : Set G)) K :=
    hnbr.1.2.2.2.2.1
  have hJK : J ≤ K := le_of_ggNbr hLB hI hStdSub hpJ hnbr
  have hBsy : Bs ≤ Subgroup.centralizer ({y} : Set G) :=
    (GGBstar.le_centralizer hBstar).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hyB))
  have hBsK : Bs ≤ Subgroup.normalizer (K : Set G) :=
    GGDichotomy.le_normalizer_of_pComponent hBsy hKpc hJK hJJ hpJ hBsJ
  exact ⟨hyBs, hy1, hKpc, hBsK⟩

private theorem ggQ2nP_nbr_Z_aux {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnbr : GGNbr p B x D J y K) :
    ∀ b ∈ B, ⁅K, Subgroup.zpowers b⁆ ≤ LargeEvenPPrimeCoreOf p K → b ∈ Subgroup.zpowers y := by
  intro b hb hcomm
  have hBsK : Bs ≤ Subgroup.normalizer (K : Set G) :=
    (ggQ2nP_nbr_basic hLB hP hHyp hnbr).2.2.2
  obtain ⟨hcfg, -, -, -, -⟩ := hHyp
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  exact (hnbr.1.2.2.2.2.2 b).mp ⟨hb, hBsK (hBstar.1 hb), hcomm⟩

theorem ggStdPair'_L {G : Type} [Group G] [Finite G] (hP : GGStdSubPrimeInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) :
    GGStdPair' p Bs x L := by
  have hAJ : ggAutomizer J Bs ≠ ⊥ := ggQ2nP_automizer_ne_bot hCav
  have hP' : GGStdPair p Bs x L := ggStdPair_L hP hHyp hAJ
  obtain ⟨hcfg, -, -, -, -⟩ := hHyp
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hI hStdSub
  obtain ⟨hJL, -, -⟩ := eq_of_le_of_stdSub hI hStdSub hpJ
  have hxp : x ^ p = 1 := hBstar.2.1.2 x hP'.1
  have hx1 : x ≠ 1 := hP'.2.1
  have hcard_le : Nat.card {b : ↥Bs // (⁅L, Subgroup.zpowers (b : G)⁆ : Subgroup G) ≤
      LargeEvenPPrimeCoreOf p L} ≤ p ^ 2 := by
    let f : {b : ↥Bs // (⁅L, Subgroup.zpowers (b : G)⁆ : Subgroup G) ≤
        LargeEvenPPrimeCoreOf p L} → ↥(Subgroup.zpowers x) :=
      fun t => ⟨(t.1 : G), (hP'.2.2.2.2.1 t.1 t.1.2).mp t.2⟩
    have hf : Function.Injective f := by
      intro t s hts
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun u : ↥(Subgroup.zpowers x) => (u : G)) hts
    have hle := Nat.card_le_card_of_injective f hf
    rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1] at hle
    refine hle.trans ?_
    have hp1 : 1 ≤ p := hp.one_lt.le
    calc p = p * 1 := (mul_one p).symm
      _ ≤ p * p := Nat.mul_le_mul_left p hp1
      _ = p ^ 2 := by ring
  refine ⟨hP'.1, hP'.2.1, hP'.2.2.1, hP'.2.2.2.1, hcard_le, ?_⟩
  have hmono : ggAutomizer J Bs ≤ ggAutomizer L Bs := by
    rw [ggAutomizer, ggAutomizer]
    exact Subgroup.closure_mono fun φ hφ => by
      obtain ⟨g, hgJ, hgN, hgφ⟩ := hφ
      exact ⟨g, hJL hgJ, hgN, hgφ⟩
  exact hCav.trans (Subgroup.card_dvd_of_le hmono)

theorem ggStdPair'_L_Z {G : Type} [Group G] [Finite G] (hP : GGStdSubPrimeInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs)) :
    ∀ b ∈ Bs, ⁅L, Subgroup.zpowers b⁆ ≤ LargeEvenPPrimeCoreOf p L → b ∈ Subgroup.zpowers x := by
  have hAJ : ggAutomizer J Bs ≠ ⊥ := ggQ2nP_automizer_ne_bot hCav
  exact fun b hb => ((ggStdPair_L hP hHyp hAJ).2.2.2.2.1 b hb).1

theorem ggStdPair'_nbr {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hCav : 4 ∣ Nat.card ↥(ggAutomizer J Bs))
    {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K) : GGStdPair' p Bs y K := by
  obtain ⟨hyBs, hy1, hKpc, hBsK⟩ := ggQ2nP_nbr_basic hLB hP hHyp hnbr
  have hHyp' : GGCorFiveTwentyHyp p B Bs x L D J := hHyp
  obtain ⟨hcfg, -, -, -, -⟩ := hHyp
  obtain ⟨hI, hBstar, hStdSub⟩ := hcfg
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  haveI : Fact p.Prime := ⟨hp⟩
  have hpJ : p ∣ Nat.card J := hP G p B x L D J hI hStdSub
  let O : Subgroup G := LargeEvenPPrimeCoreOf p K
  let Z : Subgroup G :=
    { carrier := {c : G | c ∈ Bs ∧ ∀ x ∈ K, ⁅x, c⁆ ∈ O}
      one_mem' := by
        refine ⟨Bs.one_mem, ?_⟩
        intro x hx
        simpa using O.one_mem
      mul_mem' := by
        rintro a b ⟨haBs, ha⟩ ⟨hbBs, hb⟩
        refine ⟨Bs.mul_mem haBs hbBs, ?_⟩
        intro x hx
        have haN : a ∈ Subgroup.normalizer (O : Set G) :=
          mem_normalizer_largeEvenPPrimeCoreOf (hBsK haBs)
        have h1 : ⁅x, a * b⁆ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) := by
          rw [commutatorElement_def, commutatorElement_def]
          group
        rw [h1]
        exact O.mul_mem (ha x hx) ((Subgroup.mem_normalizer_iff.mp haN _).mp (hb x hx))
      inv_mem' := by
        rintro a ⟨haBs, ha⟩
        refine ⟨Bs.inv_mem haBs, ?_⟩
        intro x hx
        have haN : a ∈ Subgroup.normalizer (O : Set G) :=
          mem_normalizer_largeEvenPPrimeCoreOf (hBsK haBs)
        have h1 : ⁅x, a⁻¹⁆ = a⁻¹ * ⁅x, a⁆⁻¹ * a := by
          rw [commutatorElement_def, commutatorElement_def]
          group
        have h2 : a⁻¹ * ⁅x, a⁆ * a ∈ O := by
          have h3 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haN) _).mp (ha x hx)
          simpa only [inv_inv] using h3
        rw [h1]
        simpa only [mul_inv_rev, inv_inv, mul_assoc] using O.inv_mem h2 }
  have hZmem : ∀ c : G, c ∈ Z ↔ c ∈ Bs ∧ (⁅K, Subgroup.zpowers c⁆ : Subgroup G) ≤ O := by
    intro c
    constructor
    · intro hc
      exact ⟨hc.1, ggQ2nP_commutator_zpowers_le
        (mem_normalizer_largeEvenPPrimeCoreOf (hBsK hc.1)) hc.2⟩
    · rintro ⟨hcBs, hcomm⟩
      exact ⟨hcBs, fun x hx => (Subgroup.commutator_le.mp hcomm) x hx c (Subgroup.mem_zpowers c)⟩
  have hZleBs : Z ≤ Bs := fun c hc => ((hZmem c).mp hc).1
  have hZB : Z ⊓ B ≤ Subgroup.zpowers y := by
    intro z hz
    obtain ⟨hzZ, hzB⟩ := hz
    have hcomm : (⁅K, Subgroup.zpowers z⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf p K :=
      ((hZmem z).mp hzZ).2
    exact ggQ2nP_nbr_Z_aux hLB hP hHyp' hnbr z hzB hcomm
  have hcard : Nat.card {b : ↥Bs // (⁅K, Subgroup.zpowers (b : G)⁆ : Subgroup G) ≤
      LargeEvenPPrimeCoreOf p K} = Nat.card ↥Z :=
    Nat.card_congr
      { toFun := fun t => ⟨(t.1 : G), (hZmem (t.1 : G)).mpr ⟨t.1.2, t.2⟩⟩
        invFun := fun z => ⟨⟨z.1, ((hZmem z.1).mp z.2).1⟩, ((hZmem z.1).mp z.2).2⟩
        left_inv := by
          intro t
          apply Subtype.ext
          apply Subtype.ext
          rfl
        right_inv := by
          intro z
          apply Subtype.ext
          rfl }
  haveI : Nonempty ↥B := ⟨1⟩
  have hyB : y ∈ B := hnbr.1.2.1
  have hyBs' : y ∈ Bs := hBstar.1 hyB
  have hyp : y ^ p = 1 := hBstar.2.1.2 y hyBs'
  have hzy : Nat.card ↥(Subgroup.zpowers y) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hyp hy1]
  have hZinf_le : Nat.card ↥(B ⊓ Z) ≤ p := by
    have hle : B ⊓ Z ≤ Subgroup.zpowers y := fun z hz => hZB ⟨hz.2, hz.1⟩
    have h := Subgroup.card_le_of_le hle
    rwa [hzy] at h
  have hrelBs : B.relIndex Bs * Nat.card ↥B = Nat.card ↥Bs := by
    have h := Subgroup.relIndex_mul_card (H := B) (K := Bs)
    have hinf : B ⊓ Bs = B := le_antisymm inf_le_left (fun z hz => ⟨hz, hBstar.1 hz⟩)
    rwa [hinf] at h
  haveI : Nonempty ↥Bs := ⟨1⟩
  have hrelB_ne : B.relIndex Bs ≠ 0 := by
    intro h0
    rw [h0, Nat.zero_mul] at hrelBs
    exact (ne_of_gt (Nat.card_pos : 0 < Nat.card ↥Bs)) hrelBs.symm
  have hrelBs_le : B.relIndex Bs ≤ p := by
    have h := hBstar.2.2.1
    rw [← hrelBs] at h
    exact Nat.le_of_mul_le_mul_right h (Nat.card_pos : 0 < Nat.card ↥B)
  have hrelZ_le : B.relIndex Z ≤ p :=
    (Subgroup.relIndex_le_of_le_right hZleBs hrelB_ne).trans hrelBs_le
  have hZcard : Nat.card ↥Z = B.relIndex Z * Nat.card ↥(B ⊓ Z) :=
    (Subgroup.relIndex_mul_card (H := B) (K := Z)).symm
  have hZ_le : Nat.card ↥Z ≤ p * p := by
    rw [hZcard]
    exact Nat.mul_le_mul hrelZ_le hZinf_le
  have hgoal : Nat.card {b : ↥Bs // (⁅K, Subgroup.zpowers (b : G)⁆ : Subgroup G) ≤
      LargeEvenPPrimeCoreOf p K} ≤ p ^ 2 := by
    rw [hcard]
    calc Nat.card ↥Z ≤ p * p := hZ_le
      _ = p ^ 2 := by ring
  have hJK : J ≤ K := le_of_ggNbr hLB hI hStdSub hpJ hnbr
  have hmono : ggAutomizer J Bs ≤ ggAutomizer K Bs := by
    rw [ggAutomizer, ggAutomizer]
    exact Subgroup.closure_mono fun φ hφ => by
      obtain ⟨g, hgJ, hgN, hgφ⟩ := hφ
      exact ⟨g, hJK hgJ, hgN, hgφ⟩
  exact ⟨hyBs, hy1, hKpc, hBsK, hgoal, hCav.trans (Subgroup.card_dvd_of_le hmono)⟩

theorem ggStdPair'_nbr_Z {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput)
    (hP : GGStdSubPrimeInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) {y : G} {K : Subgroup G}
    (hnbr : GGNbr p B x D J y K) :
    ∀ b ∈ B, ⁅K, Subgroup.zpowers b⁆ ≤ LargeEvenPPrimeCoreOf p K → b ∈ Subgroup.zpowers y :=
  ggQ2nP_nbr_Z_aux hLB hP hHyp hnbr

theorem ggStdPair'_conj {G : Type} [Group G] [Finite G] {p : ℕ} {Bs X : Subgroup G} {w g : G}
    (hg : g ∈ Subgroup.normalizer (Bs : Set G)) (h : GGStdPair' p Bs w X) :
    GGStdPair' p Bs (g * w * g⁻¹) (X.map (MulAut.conj g).toMonoidHom) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hm := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom h.1
    rw [map_conj_eq_of_mem_normalizer hg] at hm
    simpa [MulAut.conj_apply] using hm
  · intro h1
    have h2 : g⁻¹ * (g * w * g⁻¹) * g = g⁻¹ * 1 * g :=
      congrArg (fun z => g⁻¹ * z * g) h1
    have h3 : g⁻¹ * (g * w * g⁻¹) * g = w := by group
    have h4 : g⁻¹ * 1 * g = 1 := by group
    exact h.2.1 (by rwa [h3, h4] at h2)
  · rw [← CFSG.LocalAnalysis.ComponentInitial.map_conj_centralizer_singleton g w]
    exact largeEvenPComponent_map_conj' h.2.2.1 g
  · intro b hb
    rw [mem_normalizer_iff_map_conj]
    have hbg : g⁻¹ * b * g ∈ Bs := by
      have hm := Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom hb
      rw [map_conj_eq_of_mem_normalizer (Subgroup.inv_mem _ hg)] at hm
      simpa [MulAut.conj_apply] using hm
    rw [map_conj_map_conj]
    rw [show b * g = g * (g⁻¹ * b * g) by group, ← map_conj_map_conj,
      map_conj_eq_of_mem_normalizer (h.2.2.2.1 hbg)]
  · let e : ↥Bs ≃ ↥Bs := ggConjAut Bs (Subgroup.inv_mem _ hg)
    have he : ∀ b : ↥Bs, ((e b : ↥Bs) : G) = g⁻¹ * b * g := by
      intro b
      change ((ggConjAut Bs (Subgroup.inv_mem _ hg) b : ↥Bs) : G) = g⁻¹ * b * g
      rw [ggConjAut_apply]
      group
    have hiff : ∀ b : ↥Bs,
        ((⁅X.map (MulAut.conj g).toMonoidHom, Subgroup.zpowers (b : G)⁆ : Subgroup G) ≤
          LargeEvenPPrimeCoreOf p (X.map (MulAut.conj g).toMonoidHom)) ↔
        ((⁅X, Subgroup.zpowers ((e b : ↥Bs) : G)⁆ : Subgroup G) ≤
          LargeEvenPPrimeCoreOf p X) := by
      intro b
      rw [he b]
      exact ggQ2nP_commutator_conj_iff_aux p X g (b : G)
    have hcard : Nat.card {b : ↥Bs // (⁅X.map (MulAut.conj g).toMonoidHom,
        Subgroup.zpowers (b : G)⁆ : Subgroup G) ≤
          LargeEvenPPrimeCoreOf p (X.map (MulAut.conj g).toMonoidHom)} =
        Nat.card {b : ↥Bs // (⁅X, Subgroup.zpowers (b : G)⁆ : Subgroup G) ≤
          LargeEvenPPrimeCoreOf p X} :=
      Nat.card_congr (Equiv.subtypeEquiv e hiff)
    exact hcard.trans_le h.2.2.2.2.1
  · have hle : (ggAutomizer X Bs).map (MulAut.conj (ggConjAut Bs hg)).toMonoidHom ≤
        ggAutomizer (X.map (MulAut.conj g).toMonoidHom) Bs := by
      rw [ggAutomizer_eq X Bs, ggAutomizer_eq (X.map (MulAut.conj g).toMonoidHom) Bs]
      rintro _ ⟨t, ht, rfl⟩
      exact ggQ2nP_mem_ggInduced_map_conj hg ht
    have hdvd : Nat.card ↥(ggAutomizer X Bs) ∣
        Nat.card ↥(ggAutomizer (X.map (MulAut.conj g).toMonoidHom) Bs) := by
      calc Nat.card ↥(ggAutomizer X Bs)
          = Nat.card ↥((ggAutomizer X Bs).map
              (MulAut.conj (ggConjAut Bs hg)).toMonoidHom) := by
            rw [Subgroup.card_map_of_injective (MulAut.conj (ggConjAut Bs hg)).injective]
        _ ∣ Nat.card ↥(ggAutomizer (X.map (MulAut.conj g).toMonoidHom) Bs) :=
            Subgroup.card_dvd_of_le hle
    exact h.2.2.2.2.2.trans hdvd

theorem ggStdPair'_commutator_conj_iff {G : Type} [Group G] [Finite G] (p : ℕ) (X : Subgroup G)
    (g b : G) :
    ⁅X.map (MulAut.conj g).toMonoidHom, Subgroup.zpowers b⁆ ≤
        LargeEvenPPrimeCoreOf p (X.map (MulAut.conj g).toMonoidHom) ↔
      ⁅X, Subgroup.zpowers (g⁻¹ * b * g)⁆ ≤ LargeEvenPPrimeCoreOf p X := by
  exact ggQ2nP_commutator_conj_iff_aux p X g b

theorem ggStdPair'_unique {G : Type} [Group G] [Finite G] (hLB : GGLBalanceInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hHyp : GGCorFiveTwentyHyp p B Bs x L D J) (hp : p = 3) {w : G} {X₁ X₂ : Subgroup G}
    (h₁ : GGStdPair' p Bs w X₁) (h₂ : GGStdPair' p Bs w X₂) : X₁ = X₂ := by
  have hcent : Subgroup.centralizer (Subgroup.zpowers w : Set G) =
      Subgroup.centralizer ({w} : Set G) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hQ : LargeEvenPComponent p (Subgroup.centralizer (Subgroup.zpowers w : Set G)) X₂ :=
    hcent.symm ▸ h₂.2.2.1
  have hX2leX1 : X₂ ≤ X₁ :=
    ggQ2n_absorb hLB hHyp hp (Subgroup.zpowers_le.mpr h₁.1) (Subgroup.mem_zpowers w)
      h₁ hQ h₂.2.2.2.2.2
  exact (ggF2 h₂.2.2.1 h₁.2.2.1 hX2leX1).symm

end CFSG.StandardType

end
