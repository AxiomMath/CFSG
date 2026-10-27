module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveL1OddLeaves
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E4Inner
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.SectionRank.SectionAssembly
public import CFSG.Quasithin.Background.A1cModuleCoprime
public import CFSG.Quasithin.Background.A3Structure312Facts
public import CFSG.Quasithin.Vol2.Ch4Sec4L443E3Conj
public import CFSG.Quasithin.Vol2.Ch4Sec4L443EIn
public import CFSG.Quasithin.Vol2.Ch4Sec4W446
public import Certificates.Certificate8026Base

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

@[expose] def GGSecFiveCentDNormInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ X : Subgroup G, (X = L ∨ ∃ y : G, GGNbr p B x D J y X) →
        Subgroup.centralizer (D : Set G) ≤ Subgroup.normalizer (X : Set G)

@[expose] def GGSecFiveReflToJInput :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (𝒦 : Finset (Subgroup G)), GGSecFiveRouteCfg p B Bs x L D J 𝒦 → GGSplitLie p L →
      ∀ (ι : Type) (M : CoxeterMatrix ι) (e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)),
        GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e → (∀ i j : ι, i ≠ j → M.M i j ≤ 3) →
        ∀ X : Subgroup G, (X = L ∨ X ∈ 𝒦) → GGSplitLie p X →
          ∀ r ∈ ggAutomizer X Bs, r ∈ ggCoxRefl M e →
            ∃ n ∈ X, n ∈ Subgroup.normalizer (Bs : Set G) ∧
              D ≤ (ggHyperplane Bs r).map (MulAut.conj n).toMonoidHom

theorem SecFiveL1Pi.centralizer_le_normalizer_of_conj {G : Type} [Group G]
    {D H X : Subgroup G} {n : G}
    (hnX : n ∈ X) (hD : D ≤ H.map (MulAut.conj n).toMonoidHom)
    (hN : Subgroup.centralizer (D : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    Subgroup.centralizer (H : Set G) ≤ Subgroup.normalizer (X : Set G) := by
  intro c hc
  have hc' : n * c * n⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    obtain ⟨h, hh, rfl⟩ := hD hd
    have hch : h * c = c * h := (Subgroup.mem_centralizer_iff.mp hc) h hh
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc n * h * n⁻¹ * (n * c * n⁻¹) = n * (h * c) * n⁻¹ := by group
      _ = n * (c * h) * n⁻¹ := by rw [hch]
      _ = n * c * n⁻¹ * (n * h * n⁻¹) := by group
  have hnN : n ∈ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer hnX
  have h1 := hN hc'
  have e : c = n⁻¹ * (n * c * n⁻¹) * n := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hnN) h1) hnN

theorem ggCentHyp_le_normalizer
    (hN : GGSecFiveCentDNormInput) (h22 : GGSecFiveReflToJInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hsplit : GGSplitLie p L)
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e) (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3)
    {X : Subgroup G} (hX : X = L ∨ X ∈ 𝒦) (hXs : GGSplitLie p X) {r : MulAut ↥Bs}
    (hrX : r ∈ ggAutomizer X Bs) (hrC : r ∈ ggCoxRefl M e) :
    Subgroup.centralizer (ggHyperplane Bs r : Set G) ≤ Subgroup.normalizer (X : Set G) := by
  obtain ⟨n, hnX, -, hD⟩ := h22 G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX hXs r hrX hrC
  have hXN : X = L ∨ ∃ y : G, GGNbr p B x D J y X := by
    rcases hX with h | h
    · exact Or.inl h
    · exact Or.inr (hcfg.2.2.2.1.2 X h)
  exact SecFiveL1Pi.centralizer_le_normalizer_of_conj hnX hD
    (hN G p B Bs x L D J 𝒦 hcfg hsplit X hXN)

theorem ggSecFiveL1PiInput_of_pieces
    (hN : GGSecFiveCentDNormInput) (h22 : GGSecFiveReflToJInput)
    (hOut : GGSplitLieOutInput) (hC : GGSecFiveRk1CentInput) : GGSecFiveL1PiInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX hXs r hrX hrC
  set P := ggRankOnePerf Bs r with hP
  have hPle : P ≤ Subgroup.centralizer (ggHyperplane Bs r : Set G) :=
    CFSG.Quasithin.perfectCore_le _
  have hPperf : ⁅P, P⁆ = P := CFSG.Quasithin.perfectCore_perfect _
  have hPN : P ≤ Subgroup.normalizer (X : Set G) :=
    hPle.trans (ggCentHyp_le_normalizer hN h22 hcfg hsplit hpres hle3 hX hXs hrX hrC)
  have hPXC : P ≤ X ⊔ Subgroup.centralizer (X : Set G) :=
    CFSG.Quasithin.H13.Ch4.E443.le_sup_centralizer_of_outSolvable (hOut G p X hXs) hPN hPperf
  exact hC G p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX hXs r hrX hrC P hPle hPperf hPXC

theorem ggSecFiveCentDNormInput_of_leaves
    (ha₀ : GGLNoncyclicInput) (hJR : GGSecFiveJReflInput)
    (hL : GGLBalanceInput) : GGSecFiveCentDNormInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit X hX
  obtain ⟨r, hr, hrefl⟩ := hJR G p B Bs x L D J 𝒦 hcfg hsplit
  have hpJ : p ∣ Nat.card J := SecFiveL1Odd.p_dvd_card_J ha₀ hcfg hr hrefl
  rcases hX with rfl | ⟨y, hy⟩
  · exact SecFiveL1Odd.centralizer_le_normalizer_L ha₀ hcfg
  · exact SecFiveL1Odd.centralizer_le_normalizer_nbr ha₀ hL hcfg hpJ hy

theorem ggSecFiveReflToJInput_of_leaves
    (ha₀ : GGLNoncyclicInput) (hKGp : GGSecFiveKGPosInput)
    (hJR : GGSecFiveJReflInput) (hL : GGLBalanceInput) : GGSecFiveReflToJInput := by
  intro G _ _ p B Bs x L D J 𝒦 hcfg hsplit ι M e hpres hle3 X hX hXs r hrX hrC
  exact SecFiveL1Odd.exists_conj_le_ggHyperplane ha₀ hKGp hJR hL hcfg hsplit hpres hle3 hX hXs
    hrX hrC

theorem ggSecFiveL1PiInput_of_leaves
    (ha₀ : GGLNoncyclicInput) (hKGp : GGSecFiveKGPosInput)
    (hJR : GGSecFiveJReflInput) (hL : GGLBalanceInput) (hOut : GGSplitLieOutInput)
    (hC : GGSecFiveRk1CentInput) : GGSecFiveL1PiInput :=
  ggSecFiveL1PiInput_of_pieces (ggSecFiveCentDNormInput_of_leaves ha₀ hJR hL)
    (ggSecFiveReflToJInput_of_leaves ha₀ hKGp hJR hL) hOut hC


end CFSG.StandardType
