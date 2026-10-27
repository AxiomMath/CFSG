module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortDefs
import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem F11_kernel_eq_zpowers {B Bs : Subgroup G} {x z : G} {L D₁ J₁ K : Subgroup G}
    (h : P5Out B Bs x z L D₁ J₁)
    (hK : LargeEvenPComponent 3 (Subgroup.centralizer ({z} : Set G)) K) (hJK : J₁ ≤ K)
    (hBsK : Bs ≤ Subgroup.normalizer (K : Set G))
    (hNK : Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.normalizer (K : Set G))
    (hirr : ∀ V : Subgroup G, V ≤ Bs → z ∈ V →
      (∀ g ∈ Subgroup.normalizer (Bs : Set G) ⊓ Subgroup.centralizer ({z} : Set G),
        ∀ v ∈ V, g * v * g⁻¹ ∈ V) → V = Subgroup.zpowers z ∨ V = Bs) :
    ∀ b : G, (b ∈ Bs ∧ b ∈ Subgroup.normalizer (K : Set G) ∧
        (⁅K, Subgroup.zpowers b⁆ : Subgroup G) ≤ LargeEvenPPrimeCoreOf 3 K) ↔
      b ∈ Subgroup.zpowers z := by
  classical
  obtain ⟨hcfg, hplane, hnormL, hthree, hA1, -⟩ := h
  obtain ⟨-, hBstar, hstd⟩ := hcfg
  obtain ⟨hBBs, hBsEA, -, -⟩ := hBstar
  obtain ⟨hD₁B, -, -, -, -, hJ₁comp, -⟩ := hstd.1
  have hzD₁ : z ∈ D₁ := by
    rw [hplane]
    exact Subgroup.subset_closure (by simp)
  have hzBs : z ∈ Bs := hBBs (hD₁B hzD₁)
  have hKz : K ≤ Subgroup.centralizer ({z} : Set G) := hK.1
  have hzKC : z ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hKz hk)
  have hzNK : z ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.centralizer_le_normalizer (K : Set G) hzKC
  have hcomm : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBsEA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hBsJ : Bs ≤ Subgroup.normalizer (J₁ : Set G) :=
    GGDichotomy.le_normalizer_stdSub hcomm hBBs hstd.1 hnormL
  set O : Subgroup G := LargeEvenPPrimeCoreOf 3 K with hOdef
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcopO : Nat.Coprime 3 (Nat.card O) := by
    have hOeq : O = (CFSG.pPrimeCore 3 ↥K).map K.subtype := rfl
    rw [hOeq, Subgroup.card_map_of_injective K.subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  have hJ₁N : J₁ ≤ Subgroup.normalizer (O : Set G) := by
    intro j hj
    exact mem_normalizer_largeEvenPPrimeCoreOf (A := K) (p := 3)
      ((Subgroup.le_normalizer (H := K)) (hJK hj))
  let S : Set G := {b : G | b ∈ Bs ∧ (⁅K, Subgroup.zpowers b⁆ : Subgroup G) ≤ O}
  set V : Subgroup G := Subgroup.closure S with hVdef
  have hS_cent : ∀ b ∈ S, b ∈ Subgroup.centralizer (J₁ : Set G) := by
    intro b hb
    have hbNJ : b ∈ Subgroup.normalizer (J₁ : Set G) := hBsJ hb.1
    have hcommJ : (⁅J₁, Subgroup.zpowers b⁆ : Subgroup G) ≤ O :=
      (Subgroup.commutator_mono hJK le_rfl).trans hb.2
    exact mem_centralizer_of_commutator_le_coprime (p := 3) (by norm_num)
      hJ₁comp.2.2 hthree hcopO hJ₁N hbNJ hcommJ
  have hV_le_cent : V ≤ Subgroup.centralizer (J₁ : Set G) := by
    rw [hVdef]
    exact (Subgroup.closure_le _).mpr fun x hx => hS_cent x hx
  have hzS : z ∈ S := by
    refine ⟨hzBs, ?_⟩
    have hKleCz : K ≤ Subgroup.centralizer (Subgroup.zpowers z : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
      exact hKz
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKleCz]
    exact bot_le
  have hSinv : ∀ g ∈ Subgroup.normalizer (Bs : Set G) ⊓
      Subgroup.centralizer ({z} : Set G), ∀ s ∈ S, g * s * g⁻¹ ∈ S := by
    intro g hg s hs
    have hgNBs : g ∈ Subgroup.normalizer (Bs : Set G) := hg.1
    have hgNK : g ∈ Subgroup.normalizer (K : Set G) := hNK hg
    refine ⟨(Subgroup.mem_normalizer_iff.mp hgNBs s).mp hs.1, ?_⟩
    have hKmap : K.map (MulAut.conj g).toMonoidHom = K :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hgNK
    have hOmap : O.map (MulAut.conj g).toMonoidHom = O :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (mem_normalizer_largeEvenPPrimeCoreOf (A := K) (p := 3) hgNK)
    have hzpow : Subgroup.zpowers (g * s * g⁻¹) =
        (Subgroup.zpowers s).map (MulAut.conj g).toMonoidHom := by
      rw [MonoidHom.map_zpowers]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hzpow, ← hKmap, ← Subgroup.map_commutator]
    simpa only [hOmap] using
      Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hs.2
  have hVinv : ∀ g ∈ Subgroup.normalizer (Bs : Set G) ⊓
      Subgroup.centralizer ({z} : Set G), ∀ v ∈ V, g * v * g⁻¹ ∈ V := by
    intro g hg v hv
    have hmap : V.map (MulAut.conj g).toMonoidHom ≤ V := by
      rw [hVdef, MonoidHom.map_closure]
      exact (Subgroup.closure_le _).mpr (by
        rintro _ ⟨s, hs, rfl⟩
        simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
          Subgroup.subset_closure (hSinv g hg s hs))
    have hmem := hmap (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hv)
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using hmem
  have hVleBs : V ≤ Bs := by
    rw [hVdef]
    exact (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hzV : z ∈ V := Subgroup.subset_closure hzS
  have hVcase : V = Subgroup.zpowers z ∨ V = Bs := hirr V hVleBs hzV hVinv
  have hnotBs : V ≠ Bs := fun hVB => hA1 (hVB ▸ hV_le_cent)
  intro b
  constructor
  · rintro ⟨hbBs, -, hbO⟩
    have hbV : b ∈ V := Subgroup.subset_closure (show b ∈ S from ⟨hbBs, hbO⟩)
    rcases hVcase with hVz | hVBs
    · rwa [hVz] at hbV
    · exact absurd hVBs hnotBs
  · intro hbz
    have hbBs : b ∈ Bs := (Subgroup.zpowers_le.mpr hzBs) hbz
    have hbNK : b ∈ Subgroup.normalizer (K : Set G) :=
      (Subgroup.zpowers_le.mpr hzNK) hbz
    have hbC : b ∈ Subgroup.centralizer (K : Set G) :=
      (Subgroup.zpowers_le.mpr hzKC) hbz
    have hKleCb : K ≤ Subgroup.centralizer (Subgroup.zpowers b : Set G) :=
      Subgroup.le_centralizer_iff.mpr (Subgroup.zpowers_le.mpr hbC)
    have hcommb : (⁅K, Subgroup.zpowers b⁆ : Subgroup G) = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hKleCb
    exact ⟨hbBs, hbNK, by rw [hcommb]; exact bot_le⟩

end CFSG.StandardType.FrameRoute

end
