module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortPump
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortKernel
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP8
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiag
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTransport
import CFSG.LocalAnalysis.StandardType.GGCorFourTwo
import CFSG.LocalAnalysis.StandardType.GGHalfFiveInnAll
import CFSG.GroupTheory.ElementaryAbelianTransport
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly

@[expose] def GGOuterThreeRank (R : Type) [Group R] : Prop :=
  ∀ A : Subgroup (MulAut R), IsElemAbelian 3 A →
    A ⊓ (MulAut.conj : R →* MulAut R).range = ⊥ → Nat.card A ≤ 9

@[expose] def GGOuterThreeRankInput : Prop :=
  ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab →
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ _ _ => GGOuterThreeRank R)

variable {G : Type} [Group G] [Finite G]

theorem nbr_of_p5Out (hPU : GGPumpupInput) {B Bs : Subgroup G} {x z : G}
    {L D₁ J₁ : Subgroup G} (h : P5Out B Bs x z L D₁ J₁)
    (hirr : ∀ V : Subgroup G, V ≤ Bs → z ∈ V →
      (∀ g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        ∀ v ∈ V, g * v * g⁻¹ ∈ V) → V = Subgroup.zpowers z ∨ V = Bs) :
    GGNbr 3 B x D₁ J₁ z (ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J₁) ∧
      LargeEvenIsNeighborOf 3 B x L z
        (ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J₁) := by
  have hI : GGThmIHyp 3 B x L := h.cfg.1
  have hS : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hDJ : LargeEvenStdSub 3 B x L D₁ J₁ := h.cfg.2.2
  set K : Subgroup G := ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J₁ with hK
  have hKdata : LargeEvenPComponent 3 (Subgroup.centralizer ({z} : Set G)) K ∧
      J₁ ≤ K ∧ x ∈ Subgroup.normalizer (K : Set G) ∧
      (GGNbr 3 B x D₁ J₁ z K ∨
        (⁅K, Subgroup.zpowers x⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf 3 K) :=
    pumpup_of_stdSub hPU hI hDJ h.three_dvd h.plane
  obtain ⟨hKc, hJK, hxNK, hcase⟩ := hKdata
  rcases hcase with hnbr | hcomm
  · exact ⟨hnbr, isNeighborOf_of_ggNbr hDJ hnbr⟩
  · exfalso
    have hF10 := F10_normalizer_invariance hPU h
    have hBsK : Bs ≤ Subgroup.normalizer (K : Set G) := hF10.2.2.1
    have hNK : Subgroup.normalizer (Bs : Set G) ⊓
        Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (K : Set G) := hF10.2.2.2
    have hxBs : x ∈ Bs := h.cfg.2.1.1 hS.2.1
    have hxF11 : x ∈ Subgroup.zpowers z :=
      (F11_kernel_eq_zpowers h hKc hJK hBsK hNK hirr x).mp ⟨hxBs, hxNK, hcomm⟩
    obtain ⟨-, -, hz1, hz3⟩ := facts_of_closure_pair hI hDJ h.plane
    have hDle : D₁ ≤ Subgroup.zpowers z := by
      rw [h.plane]
      refine (Subgroup.closure_le _).mpr ?_
      rintro y (rfl | rfl)
      · exact hxF11
      · exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    have hle : Nat.card D₁ ≤ 3 := by
      have hcard := Nat.card_le_card_of_injective (Subgroup.inclusion hDle)
        (Subgroup.inclusion_injective hDle)
      rw [Nat.card_zpowers, orderOf_eq_prime hz3 hz1] at hcard
      rw [hDJ.1.2.2.1] at hcard ⊢
      omega
    have hle2 : 3 ^ 2 ≤ 3 := hDJ.1.2.2.1 ▸ hle
    norm_num at hle2

theorem component_of_p5Out (hPU : GGPumpupInput) {B Bs : Subgroup G} {x z : G}
    {L D₁ J₁ K : Subgroup G} (h : P5Out B Bs x z L D₁ J₁)
    (hK : K = ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J₁)
    (hirr : ∀ V : Subgroup G, V ≤ Bs → z ∈ V →
      (∀ g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        ∀ v ∈ V, g * v * g⁻¹ ∈ V) → V = Subgroup.zpowers z ∨ V = Bs) :
    CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({z} : Set G)) ∧
      LargeEvenIsNeighborOf 3 B x L z K ∧ J₁ ≤ K ∧
      CFSG.Assembly.IsComponentOf J₁ (K ⊓ Subgroup.centralizer ({x} : Set G)) ∧
      Bs ≤ Subgroup.normalizer (K : Set G) ∧
      Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
        Subgroup.normalizer (K : Set G) ∧
      Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z ∧
      LargeEvenMarking K (fun _ _ _ _ _ _ => True) := by
  subst hK
  have hI : GGThmIHyp 3 B x L := h.cfg.1
  have hS : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  have hDJ : LargeEvenStdSub 3 B x L D₁ J₁ := h.cfg.2.2
  have hst : LargeEvenStandardType 3 B x L := hI.2.2.2.2.2.2.2
  have hF10 := F10_normalizer_invariance hPU h
  have hKc : LargeEvenPComponent 3 (Subgroup.centralizer ({z} : Set G))
      (ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J₁) := hF10.1
  have hJK : J₁ ≤ ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J₁ := hF10.2.1
  have hBsK : Bs ≤ Subgroup.normalizer
      ((ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J₁ : Subgroup G) : Set G) :=
    hF10.2.2.1
  have hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer
        ((ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J₁ : Subgroup G) : Set G) :=
    hF10.2.2.2
  have h1 := nbr_of_p5Out hPU h hirr
  have hnbr : GGNbr 3 B x D₁ J₁ z
      (ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J₁) := h1.1
  have hnb : LargeEvenIsNeighborOf 3 B x L z
      (ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J₁) := h1.2
  have hcomp := isComponentOf_of_isNeighborOf hst hnb
  have hJ1comp := isComponentOf_inf_centralizer_of_ggNbr hS hDJ hnbr hJK
  have hmark : LargeEvenMarking
      (ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J₁)
      (fun lab _ _ I F θ =>
        LargeEvenHalfSplit 3 lab
            (Subgroup.center (ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J₁) = ⊥) ∨
          LargeEvenPrimeField 3 lab I F
            (LargeEvenInduces θ fun j j' => (j' : G) = x⁻¹ * j * x)) :=
    (hst.2.2.1 z _ hnb).2
  refine ⟨hcomp.1, hnb, hJK, hJ1comp, hBsK, hNK, ?_,
    largeEvenMarking_mono (fun _ _ _ _ _ _ _ => trivial) hmark⟩
  apply le_antisymm
  · intro b hb
    rw [Subgroup.mem_inf] at hb
    refine (F11_kernel_eq_zpowers h hKc hJK hBsK hNK hirr b).mp ⟨hb.1, ?_, ?_⟩
    · exact Subgroup.centralizer_le_normalizer
        (ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J₁ : Set G) hb.2
    · have hle : Subgroup.zpowers b ≤
          Subgroup.centralizer
            ((ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J₁ : Subgroup G) : Set G) :=
        Subgroup.zpowers_le.mpr hb.2
      have hbot : (⁅ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J₁,
          Subgroup.zpowers b⁆ : Subgroup G) = ⊥ :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
          (Subgroup.le_centralizer_iff.mpr hle)
      rw [hbot]
      exact bot_le
  · rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · obtain ⟨hzB, -, -, -⟩ := facts_of_closure_pair hI hDJ h.plane
      exact h.cfg.2.1.1 hzB
    · rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact Subgroup.mem_centralizer_singleton_iff.mp (hKc.1 hk)

private theorem glue1Aux_le_sup {Bs K : Subgroup G} {z : G} {n : ℕ}
    {R : Type} [Group R] (θ : K ⧸ Subgroup.center K ≃* R) (hperf : commutator K = ⊤)
    (hOrank : GGOuterThreeRank R)
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hn : 4 ≤ n) (hz : z ∈ Bs)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hirr : ∀ V : Subgroup G, V ≤ Bs → z ∈ V →
      (∀ g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        ∀ v ∈ V, g * v * g⁻¹ ∈ V) → V = Subgroup.zpowers z ∨ V = Bs) :
    Bs ≤ K ⊔ Subgroup.centralizer (K : Set G) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (K : Set G)
  have hzC : z ∈ C := by
    have h : z ∈ Bs ⊓ C :=
      hker.symm ▸ Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩
    exact h.2
  have hVz : z ∈ Bs ⊓ (K ⊔ C) :=
    Subgroup.mem_inf.mpr ⟨hz, Subgroup.mem_sup_right hzC⟩
  have hVinv : ∀ g ∈ Subgroup.normalizer (Bs : Set G) ⊓
      Subgroup.centralizer ({z} : Set G), ∀ v ∈ Bs ⊓ (K ⊔ C),
      g * v * g⁻¹ ∈ Bs ⊓ (K ⊔ C) := by
    intro g hg v hv
    have hgNBs : g ∈ Subgroup.normalizer (Bs : Set G) := hg.1
    have hgNK : g ∈ Subgroup.normalizer (K : Set G) := hNK hg
    have hKmap : K.map (MulAut.conj g).toMonoidHom = K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgNK
    have hCmap : C.map (MulAut.conj g).toMonoidHom = C := by
      apply le_antisymm
      · intro c hc
        rw [Subgroup.mem_map] at hc
        obtain ⟨c0, hc0, rfl⟩ := hc
        rw [Subgroup.mem_centralizer_iff] at hc0 ⊢
        intro k hk
        have hk' : g⁻¹ * k * g ∈ K :=
          (Subgroup.mem_normalizer_iff.mp hgNK (g⁻¹ * k * g)).mpr
            (by simpa [mul_assoc] using hk)
        calc k * (g * c0 * g⁻¹) = g * ((g⁻¹ * k * g) * c0) * g⁻¹ := by group
          _ = g * (c0 * (g⁻¹ * k * g)) * g⁻¹ := by rw [hc0 _ hk']
          _ = g * c0 * g⁻¹ * k := by group
      · intro c hc
        have hc' : g⁻¹ * c * g ∈ C := by
          rw [Subgroup.mem_centralizer_iff] at hc ⊢
          intro k hk
          have hk' : g * k * g⁻¹ ∈ K :=
            (Subgroup.mem_normalizer_iff.mp hgNK k).mp hk
          calc k * (g⁻¹ * c * g) = g⁻¹ * ((g * k * g⁻¹) * c) * g := by group
            _ = g⁻¹ * (c * (g * k * g⁻¹)) * g := by rw [hc _ hk']
            _ = g⁻¹ * c * g * k := by group
        refine Subgroup.mem_map.mpr ⟨g⁻¹ * c * g, hc', ?_⟩
        show g * (g⁻¹ * c * g) * g⁻¹ = c
        group
    have hsup : (K ⊔ C).map (MulAut.conj g).toMonoidHom ≤ K ⊔ C := by
      rw [Subgroup.map_sup, hKmap, hCmap]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hgNBs v).mp hv.1
    · exact hsup (by
        simpa [MulAut.conj_apply] using
          Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hv.2)
  rcases hirr (Bs ⊓ (K ⊔ C)) inf_le_left hVz hVinv with hVz' | hVBs
  · exfalso
    let N : Subgroup G := Subgroup.normalizer (K : Set G)
    let D : Subgroup ↥N := Bs.subgroupOf N
    let f : ↥D →* MulAut R := (ggLAut K θ).comp D.subtype
    let A : Subgroup (MulAut R) := D.map (ggLAut K θ)
    have hcardD : Nat.card ↥D = 3 ^ n := by
      rw [show Nat.card ↥D = Nat.card Bs from
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv, hcard]
    have hrange : f.range = A := by
      ext x
      constructor
      · rintro ⟨y, rfl⟩
        exact Subgroup.mem_map_of_mem (ggLAut K θ) y.2
      · intro hx
        rw [Subgroup.mem_map] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        exact ⟨⟨y, hy⟩, rfl⟩
    have hker_le : ∀ x : ↥D, f x = 1 → ((x : ↥N) : G) ∈ Subgroup.zpowers z := by
      intro x hx
      have hxC : ((x : ↥N) : G) ∈ C :=
        mem_centralizer_of_ggLAut_eq_one K θ hperf hx
      have hxBs : ((x : ↥N) : G) ∈ Bs := Subgroup.mem_subgroupOf.mp x.2
      have hxinf : ((x : ↥N) : G) ∈ Bs ⊓ C := ⟨hxBs, hxC⟩
      rwa [hker] at hxinf
    have hkercard : Nat.card f.ker ≤ 3 := by
      let ψ : f.ker → ↥(Subgroup.zpowers z) := fun x =>
        ⟨(((x.1 : ↥D) : ↥N) : G), hker_le x.1 x.2⟩
      have hinj : Function.Injective ψ := by
        intro x y hxy
        have h1 : ((x.1 : ↥D) : ↥N) = ((y.1 : ↥D) : ↥N) := by
          apply Subtype.ext
          exact congrArg (fun t : ↥(Subgroup.zpowers z) => (t : G)) hxy
        exact Subtype.ext (Subtype.ext h1)
      have h := Nat.card_le_card_of_injective ψ hinj
      rw [Nat.card_zpowers] at h
      have hz3 : z ^ 3 = 1 := hBs.2 z hz
      exact le_trans h (Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hz3))
    have hAel : IsElemAbelian 3 A :=
      IsElemAbelian.map (IsElemAbelian.subgroupOf hBs N) (ggLAut K θ)
    have hAdisj : A ⊓ (MulAut.conj : R →* MulAut R).range = ⊥ := by
      apply le_antisymm _ bot_le
      intro a ha
      rw [Subgroup.mem_inf] at ha
      obtain ⟨haA, haInn⟩ := ha
      rw [Subgroup.mem_map] at haA
      obtain ⟨b, hbD, hbmap⟩ := haA
      obtain ⟨r, hr⟩ := haInn
      have hbinn : ggLAut K θ b ∈ (MulAut.conj : R →* MulAut R).range :=
        ⟨r, hr.trans hbmap.symm⟩
      have hbsup : ((b : ↥N) : G) ∈ K ⊔ C :=
        mem_sup_centralizer_of_ggLAut_mem K θ hperf hbinn
      have hbV : ((b : ↥N) : G) ∈ Bs ⊓ (K ⊔ C) :=
        Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hbD, hbsup⟩
      rw [hVz'] at hbV
      have hbC : ((b : ↥N) : G) ∈ C := (hker.symm ▸ hbV).2
      have hb1 : ggLAut K θ b = 1 := ggLAut_eq_one_of_mem_centralizer K θ hbC
      rw [hbmap] at hb1
      exact Subgroup.mem_bot.mpr hb1
    have hcardA : Nat.card A * Nat.card f.ker = 3 ^ n := by
      have h1 : Nat.card f.ker * Nat.card f.range = Nat.card ↥D :=
        Subgroup.card_ker_mul_card_range f
      rw [hrange, hcardD] at h1
      calc Nat.card A * Nat.card f.ker = Nat.card f.ker * Nat.card A := Nat.mul_comm _ _
        _ = 3 ^ n := h1
    have hn1 : 1 ≤ n := by omega
    have h3n : 3 ^ n = 3 ^ (n - 1) * 3 := by
      calc 3 ^ n = 3 ^ (n - 1 + 1) := by rw [Nat.sub_add_cancel hn1]
        _ = 3 ^ (n - 1) * 3 := pow_succ _ _
    have hleA : 3 ^ (n - 1) ≤ Nat.card A := by
      have hmul : Nat.card A * Nat.card f.ker ≤ Nat.card A * 3 :=
        Nat.mul_le_mul_left _ hkercard
      have hmain : 3 ^ (n - 1) * 3 ≤ Nat.card A * 3 := by
        calc 3 ^ (n - 1) * 3 = 3 ^ n := h3n.symm
          _ = Nat.card A * Nat.card f.ker := hcardA.symm
          _ ≤ Nat.card A * 3 := hmul
      exact Nat.le_of_mul_le_mul_right hmain (by norm_num)
    have h27 : 27 ≤ Nat.card A := by
      have h3le : 3 ≤ n - 1 := by omega
      have hpow : 3 ^ 3 ≤ 3 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) h3le
      norm_num at hpow
      omega
    have h9 := hOrank A hAel hAdisj
    omega
  · rw [← hVBs]
    exact inf_le_right

theorem innerDiagOn_of_irreducible (hO : GGOuterThreeRankInput) {Bs K : Subgroup G} {z : G}
    {n : ℕ} (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ n) (hn : 4 ≤ n) (hz : z ∈ Bs)
    (hM : LargeEvenMarking K (fun _ _ _ _ _ _ => True))
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z)
    (hirr : ∀ V : Subgroup G, V ≤ Bs → z ∈ V →
      (∀ g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        ∀ v ∈ V, g * v * g⁻¹ ∈ V) → V = Subgroup.zpowers z ∨ V = Bs) :
    GGInnerDiagOnLabel (fun _ _ => True) 3 Bs K := by
  have hM1 : LargeEvenMarking K (fun lab R _ I F θ => True ∧ GGOuterThreeRank R) :=
    largeEvenMarking_and_labelAll_simple (P := fun _ _ _ _ _ _ => True)
      (S := fun _ => True) (P' := fun R _ _ _ => GGOuterThreeRank R)
      (hall := fun lab hlab _ => hO lab hlab)
      (hS := fun _ _ _ _ _ _ _ => trivial) hM
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM1
  have hraw2 := largeEvenRawDatum_inn_all hraw
  have hM2 : LargeEvenMarking K (fun lab R _ I F θ =>
      GGOuterThreeRank R ∧ LargeEvenInnSet R ⊆ I) := by
    refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw2⟩
    rintro R _ I F ⟨⟨hs, hna, θ, -, hOrank⟩, hInn⟩
    exact ⟨hs, hna, θ, hOrank, hInn⟩
  refine largeEvenMarking_mono ?_ hM2
  intro lab R _ I F θ hP
  obtain ⟨hOrank, hInn⟩ := hP
  refine ⟨trivial, hN, fun b hb => ?_⟩
  have hsup := glue1Aux_le_sup θ hperf hOrank hBs hcard hn hz hN hNK hker hirr
  have hbN : b⁻¹ ∈ Subgroup.normalizer (K : Set G) := hN (inv_mem hb)
  have hbpre : b⁻¹ ∈ ggInndiagPre K θ (∅ : Set (MulAut R)) :=
    sup_centralizer_le_ggInndiagPre K θ ∅ (hsup (inv_mem hb))
  obtain ⟨hgN, hgI⟩ := mem_ggInndiagPre_iff.mp hbpre
  have hIeq : ggInndiag R (∅ : Set (MulAut R)) = (MulAut.conj : R →* MulAut R).range := by
    simp [ggInndiag]
  have hφI : ggLAut K θ ⟨b⁻¹, hbN⟩ ∈ I := by
    apply hInn
    show ggLAut K θ ⟨b⁻¹, hbN⟩ ∈ LargeEvenInnSet R
    have hmem : ggLAut K θ ⟨b⁻¹, hgN⟩ ∈ (MulAut.conj : R →* MulAut R).range :=
      hIeq ▸ hgI
    simpa [LargeEvenInnSet] using hmem
  exact ⟨ggLAut K θ ⟨b⁻¹, hbN⟩, hφI, largeEvenInduces_ggLAut_inv K θ hbN⟩

theorem glueOne (hPU : GGPumpupInput) (hO : GGOuterThreeRankInput) (hTCJ : GGTCJKnown)
    (hRigid : GGLabelRigidInput) {B Bs : Subgroup G} {x z : G} {L D₁ J₁ : Subgroup G} {n : ℕ}
    (h : P5Out B Bs x z L D₁ J₁) (hcard : Nat.card Bs = 3 ^ n) (hn : 4 ≤ n)
    (hirr : ∀ V : Subgroup G, V ≤ Bs → z ∈ V →
      (∀ g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        ∀ v ∈ V, g * v * g⁻¹ ∈ V) → V = Subgroup.zpowers z ∨ V = Bs)
    (hJlab : ∃ j, GGFrameJTag j ∧ GGHasLabel j (J₁ ⧸ Subgroup.center J₁)) :
    ∃ K : Subgroup G, CFSG.Assembly.IsComponentOf K (Subgroup.centralizer ({z} : Set G)) ∧
      LargeEvenIsNeighborOf 3 B x L z K ∧ J₁ ≤ K ∧ Bs ≤ Subgroup.normalizer (K : Set G) ∧
      Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
        Subgroup.normalizer (K : Set G) ∧
      Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers z ∧
      GGInnerDiagOnLabel (fun _ lab => lab.n = 1) 3 Bs K := by
  let K : Subgroup G := ggLayerClosure 3 (Subgroup.centralizer ({z} : Set G)) J₁
  have hcomp := component_of_p5Out (K := K) hPU h rfl hirr
  obtain ⟨hIsComp, hNbr, hJK, hJ1comp, hBsN, hNK, hker, hM⟩ := hcomp
  have hI : GGThmIHyp 3 B x L := h.cfg.1
  have hS : LargeEvenSStar 3 B x L := hI.2.2.2.2.2.2.1
  obtain ⟨hzB, -, -, -⟩ := facts_of_closure_pair hI h.cfg.2.2 h.plane
  have hzBs : z ∈ Bs := h.cfg.2.1.1 hzB
  have hxBs : x ∈ Bs := h.cfg.2.1.1 hS.2.1
  have hx3 : x ^ 3 = 1 := hS.1.1.2 x hS.2.1
  have hBs : IsElemAbelian 3 Bs := h.cfg.2.1.2.1
  have hid := innerDiagOn_of_irreducible hO hBs hcard hn hzBs hM hBsN hNK hker hirr
  have hfield := P8c_innerDiag_fieldOne hTCJ hRigid (S := fun _ _ => True)
    hxBs hx3 hid hJK hJ1comp hJlab
  refine ⟨K, hIsComp, hNbr, hJK, hBsN, hNK, hker, ?_⟩
  refine largeEvenMarking_mono ?_ hfield
  intro lab R _ I F θ h
  exact ⟨h.1.2, h.2.1, h.2.2⟩

end CFSG.StandardType.FrameRoute
