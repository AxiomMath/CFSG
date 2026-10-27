module

public import CFSG.LieType.SeitzGeneration.ExcPlanePair
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5Unitary
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5UnitaryFrameCoord
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5UnitaryFramePlane
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U3
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9Wa
public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortSU

public section

namespace CFSG.StandardType.FrameRoute.UnitaryModel

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU

private abbrev P5Setup (G : Type) [Group G] (F : Type) [Field F] (m n : ℕ)
    (Bs L : Subgroup G) (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (x : G)
    (φ : ↥(unitarySU 2 1 F m) →* ↥L) (ζ : Fˣ) : Prop :=
  ∃ (u : G → Fin m → ZMod 3) (ι : ↥(ggGamma L hN).range →* UTorus.Proj F m),
    (∀ b ∈ Bs, ∀ s s' : ↥(unitarySU 2 1 F m),
      (s' : GL (Fin m) F) = TauCeti.diagGL (fun i => ζ ^ (u b i).val) * s *
        (TauCeti.diagGL (fun i => ζ ^ (u b i).val))⁻¹ →
      ((φ s' : ↥L) : G) = b⁻¹ * φ s * b) ∧
    (∀ b ∈ Bs, ∀ b' ∈ Bs, ∃ c : ZMod 3, ∀ i, u (b * b') i = u b i + u b' i + c) ∧
    (∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔ b ∈ Subgroup.zpowers x) ∧
    Function.Injective ι ∧ UTorus.inner F m ≤ ι.range ∧
    (∀ b ∈ Bs, (QuotientGroup.mk (fun i => ζ ^ (u b i).val) : UTorus.Proj F m) ∈ ι.range) ∧
    (∀ v : Fin m → ZMod 3,
      (QuotientGroup.mk (fun i => ζ ^ (v i).val) : UTorus.Proj F m) ∈ ι.range →
        ∃ b ∈ Bs, ∃ c : ZMod 3, ∀ i, u b i = v i + c) ∧
    Nat.card (ggGamma L hN).range = 3 ^ (n - 1)

private theorem p5Setup {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} (hThm : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) {m n : ℕ} (hm : 3 ≤ m)
    (hcard : Nat.card Bs = 3 ^ n) {φ : ↥(unitarySU 2 1 F m) →* ↥L}
    (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → ∃ c : F,
      ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = Matrix.diagonal fun _ => c)
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin m → F, ActsDiagU φ a t)
    (hSC : GGTorusSelfCent 3 (ggGamma L hN).range) {ζ : Fˣ} (hζ : orderOf ζ = 3) :
    P5Setup G F m n Bs L hN x φ ζ := by
  have hS : LargeEvenSStar 3 B x L := hThm.2.2.2.2.2.2.1
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F :=
    ⟨Nat.prime_two, le_rfl, by rw [hF]; norm_num⟩
  obtain ⟨ι, hιinj, hι⟩ := P9_U6a_exists_coord h hm hφs hφker hdiag
  have hinner : UTorus.inner F m ≤ ι.range := P9_U6a_inner_le_range h hdiag hSC ι hι
  obtain ⟨u, hw, hmul, hconst', hmem, hsurj⟩ :=
    exists_unitaryCoord hN hF hζ hdiag ι hιinj hι
  have hconst : ∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔ b ∈ Subgroup.zpowers x := by
    intro b hb
    refine (hconst' b hb).trans ?_
    rw [← hker]
    exact ⟨fun hc => ⟨hb, hc⟩, fun hc => hc.2⟩
  have hcardA : Nat.card (ggGamma L hN).range = 3 ^ (n - 1) :=
    P9_Wa_card_range hBs.2.1 hcard (hBs.1 hS.2.1) hS.2.2.1 hN hker
  exact ⟨u, ι, hw, hmul, hconst, hιinj, hinner, hmem, hsurj, hcardA⟩

private abbrev P5CoordProp (G : Type) [Group G] (F : Type) [Field F] (m : ℕ)
    (Bs L : Subgroup G) (x : G) (φ : ↥(unitarySU 2 1 F m) →* ↥L) (ζ : Fˣ) : Prop :=
  ∃ u : G → Fin m → ZMod 3,
    (∀ b ∈ Bs, ∀ s s' : ↥(unitarySU 2 1 F m),
      (s' : GL (Fin m) F) = TauCeti.diagGL (fun i => ζ ^ (u b i).val) * s *
        (TauCeti.diagGL (fun i => ζ ^ (u b i).val))⁻¹ →
      ((φ s' : ↥L) : G) = b⁻¹ * φ s * b) ∧
    (∀ b ∈ Bs, ∀ b' ∈ Bs, ∃ c : ZMod 3, ∀ i, u (b * b') i = u b i + u b' i + c) ∧
    (∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔ b ∈ Subgroup.zpowers x) ∧
    (m = 7 → ∀ v : Fin m → ZMod 3, ∃ b ∈ Bs, ∃ c : ZMod 3, ∀ i, u b i = v i + c) ∧
    (m = 9 → (∀ b ∈ Bs, ∑ i, u b i = 0) ∧
      ∀ v : Fin m → ZMod 3, ∑ i, v i = 0 →
        ∃ b ∈ Bs, ∃ c : ZMod 3, ∀ i, u b i = v i + c)

private theorem p5CoordOfSetup {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} {F : Type} [Field F] [Finite F] {m n : ℕ}
    {hN : Bs ≤ Subgroup.normalizer (L : Set G)} (hF : Nat.card F = 4)
    {φ : ↥(unitarySU 2 1 F m) →* ↥L} {ζ : Fˣ} (hζ : orderOf ζ = 3)
    (h : P5Setup G F m n Bs L hN x φ ζ)
    (hmn : (m = 7 ∧ n = 7 ∧ B ≠ Bs) ∨ (m = 9 ∧ n = 8)) :
    P5CoordProp G F m Bs L x φ ζ := by
  obtain ⟨u, ι, hw, hmul, hconst, hιinj, hinner, hmem, hsurj, hcardA⟩ := h
  have hιcard : Nat.card ι.range = Nat.card (ggGamma L hN).range :=
    (Nat.card_congr (MonoidHom.ofInjective hιinj).toEquiv).symm
  refine ⟨u, hw, hmul, hconst, ?_, ?_⟩
  · intro hm7
    have hn7 : n = 7 := by rcases hmn with h | h <;> omega
    have htop : ι.range = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [hιcard, hcardA, UTorus.card_proj hF (by omega : 1 ≤ m),
        show m - 1 = 6 by omega, show n - 1 = 6 by omega]
    intro v
    exact hsurj v (by rw [htop]; exact Subgroup.mem_top _)
  · intro hm9
    have hn8 : n = 8 := by rcases hmn with h | h <;> omega
    have hAr : Nat.card (ggGamma L hN).range = 3 ^ 7 := by
      rw [hcardA, show n - 1 = 7 by omega]
    have hrange : ι.range = UTorus.inner F m := by
      rcases UTorus.eq_inner_or_eq_top hF (by omega : 1 ≤ m) hinner with h | h
      · exact h
      · exfalso
        have h1 : Nat.card (UTorus.Proj F m) = 3 ^ 7 := by
          have htopcard : Nat.card (UTorus.Proj F m) = Nat.card ι.range := by
            rw [h, Subgroup.card_top]
          rw [htopcard, hιcard, hAr]
        have h2 : Nat.card (UTorus.Proj F m) = 3 ^ 8 := by
          rw [UTorus.card_proj hF (by omega : 1 ≤ m), show m - 1 = 8 by omega]
        exact (by norm_num : (3 : ℕ) ^ 7 ≠ 3 ^ 8) (h1.symm.trans h2)
    constructor
    · intro b hb
      have hb' : (QuotientGroup.mk (fun i => ζ ^ (u b i).val) : UTorus.Proj F m) ∈
          UTorus.inner F m := by
        rw [← hrange]
        exact hmem b hb
      exact (mk_pow_mem_inner_iff hF hζ (by omega : 3 ∣ m) (u b)).mp hb'
    · intro v hv
      have hv' : (QuotientGroup.mk (fun i => ζ ^ (v i).val) : UTorus.Proj F m) ∈
          UTorus.inner F m :=
        (mk_pow_mem_inner_iff hF hζ (by omega : 3 ∣ m) v).mpr hv
      refine hsurj v ?_
      rwa [hrange]

private theorem exists_p5Coord {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} (hThm : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) {m n : ℕ}
    (hmn : (m = 7 ∧ n = 7 ∧ B ≠ Bs) ∨ (m = 9 ∧ n = 8)) (hcard : Nat.card Bs = 3 ^ n)
    {φ : ↥(unitarySU 2 1 F m) →* ↥L} (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → ∃ c : F,
      ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = Matrix.diagonal fun _ => c)
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin m → F, ActsDiagU φ a t)
    (hSC : GGTorusSelfCent 3 (ggGamma L hN).range) {ζ : Fˣ} (hζ : orderOf ζ = 3) :
    P5CoordProp G F m Bs L x φ ζ :=
  have hm : 3 ≤ m := by rcases hmn with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> norm_num
  p5CoordOfSetup hF hζ (p5Setup hThm hBs hN hker hF hm hcard hφs hφker hdiag hSC hζ) hmn

private theorem assemble
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x z : G}
    {L : Subgroup G} (hThm : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) {m : ℕ}
    {φ : ↥(unitarySU 2 1 F m) →* ↥L} {ζ : Fˣ} {u : G → Fin m → ZMod 3}
    (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → ∃ c : F,
      ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = Matrix.diagonal fun _ => c)
    (hζ : orderOf ζ = 3)
    (hw : ∀ b ∈ Bs, ∀ s s' : ↥(unitarySU 2 1 F m),
      (s' : GL (Fin m) F) = TauCeti.diagGL (fun i => ζ ^ (u b i).val) * s *
        (TauCeti.diagGL (fun i => ζ ^ (u b i).val))⁻¹ →
      ((φ s' : ↥L) : G) = b⁻¹ * φ s * b)
    {I : Finset (Fin m)} {t : ZMod 3} (hI : ∀ i, i ∈ I ↔ u z i = t)
    (h5 : 5 ≤ I.card) (hId : I.card < m) (hdI : m ≤ I.card + 2)
    (hzB : z ∈ B) (hznot : z ∉ Subgroup.zpowers x) (hB9 : 9 < Nat.card B)
    (hBF : ∀ b ∈ B, (∀ i ∈ I, ∀ j ∈ I, u b i = u b j) ↔ b ∈ Subgroup.closure {x, z})
    {r : ℕ} (hr : Rank3Witness (unitarySU 2 1 F I.card) r)
    (hm : LargeEvenTwoLocalRank 3 G < 2 * r + 1) :
    ∃ J₁ : Subgroup G, P5Out B Bs x z L (Subgroup.closure {x, z}) J₁ ∧
      J₁ = LargeEvenLayer (L ⊓ Subgroup.centralizer (Subgroup.closure {x, z} : Set G)) ∧
      LargeEvenMarking ↥J₁ (fun lab _ _ _ _ _ => lab = ⟨.twA, I.card - 1, 1⟩) ∧
      Nonempty (↥J₁ ≃* unitarySU 2 1 F (I.card - 1 + 1)) := by
  have hS : LargeEvenSStar 3 B x L := hThm.2.2.2.2.2.2.1
  obtain ⟨hDB, hDe, hDc, hDB'⟩ :=
    closure_pair_facts hS.1.1 hS.2.1 hS.2.2.1 hzB hznot hB9
  have hx : x ∈ Subgroup.centralizer (L : Set G) := by
    have hmem : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
      rw [hker]
      exact Subgroup.mem_zpowers x
    exact hmem.2
  obtain ⟨J₁, hP5, hlay, hmark, -, hSU⟩ :=
    exists_p5Out_of_unitaryCover hThm hBs hN hF hφs hφker hζ hw hI h5 hId hdI hx hDB hDB'
      hDe hDc hBF hr hm
  have hk : I.card - 1 + 1 = I.card := by omega
  exact ⟨J₁, hP5, hlay, hmark, by rwa [hk]⟩

private abbrev P5UnitaryOut (G : Type) [Group G] [Finite G] (B Bs L : Subgroup G) (x : G)
    (F : Type) [Field F] (m : ℕ) (φ : ↥(unitarySU 2 1 F m) →* ↥L) (ζ : Fˣ) : Prop :=
  ∃ (u : G → Fin m → ZMod 3) (z : G) (J₁ : Subgroup G) (k : ℕ),
    (∀ b ∈ Bs, ∀ s s' : ↥(unitarySU 2 1 F m),
      (s' : GL (Fin m) F) = TauCeti.diagGL (fun i => ζ ^ (u b i).val) * s *
        (TauCeti.diagGL (fun i => ζ ^ (u b i).val))⁻¹ →
      ((φ s' : ↥L) : G) = b⁻¹ * φ s * b) ∧
    (∀ b ∈ Bs, ∀ b' ∈ Bs, ∃ c : ZMod 3, ∀ i, u (b * b') i = u b i + u b' i + c) ∧
    (∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔ b ∈ Subgroup.zpowers x) ∧
    (m = 7 → ∀ v : Fin m → ZMod 3, ∃ b ∈ Bs, ∃ c : ZMod 3, ∀ i, u b i = v i + c) ∧
    (m = 9 → (∀ b ∈ Bs, ∑ i, u b i = 0) ∧
      ∀ v : Fin m → ZMod 3, ∑ i, v i = 0 → ∃ b ∈ Bs, ∃ c : ZMod 3, ∀ i, u b i = v i + c) ∧
    z ∈ B ∧
    ((m = 7 ∧ k = 5 ∧ ∃ j : Fin m, ∃ c : ZMod 3, ∀ i,
        u z i = (Pi.single j 1 : Fin m → ZMod 3) i + c) ∨
      (((m = 7 ∧ k = 4) ∨ (m = 9 ∧ k = 6)) ∧ ∃ j j' : Fin m, j ≠ j' ∧ ∃ c : ZMod 3, ∀ i,
        u z i = (Pi.single j 1 - Pi.single j' 1 : Fin m → ZMod 3) i + c)) ∧
    P5Out B Bs x z L (Subgroup.closure {x, z}) J₁ ∧
    J₁ = LargeEvenLayer (L ⊓ Subgroup.centralizer (Subgroup.closure {x, z} : Set G)) ∧
    LargeEvenMarking ↥J₁ (fun lab _ _ _ _ _ => lab = ⟨.twA, k, 1⟩) ∧
    Nonempty (↥J₁ ≃* unitarySU 2 1 F (k + 1))

private theorem seven_case
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} (hThm : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) (hBne : B ≠ Bs)
    (hcard : Nat.card Bs = 3 ^ 7) {φ : ↥(unitarySU 2 1 F 7) →* ↥L}
    (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → ∃ c : F,
      ((g : GL (Fin 7) F) : Matrix (Fin 7) (Fin 7) F) = Matrix.diagonal fun _ => c)
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin 7 → F, ActsDiagU φ a t)
    (hSC : GGTorusSelfCent 3 (ggGamma L hN).range) {ζ : Fˣ} (hζ : orderOf ζ = 3) :
    P5UnitaryOut G B Bs L x F 7 φ ζ := by
  have hS : LargeEvenSStar 3 B x L := hThm.2.2.2.2.2.2.1
  obtain ⟨u, hw, hmul, hconst, hsurj, h9⟩ :=
    exists_p5Coord hThm hBs hN hker hF (Or.inl ⟨rfl, rfl, hBne⟩) hcard hφs hφker hdiag hSC hζ
  obtain ⟨z, hzB, I, t, hI, hznot, hBF, hshape⟩ :=
    exists_goodPlane_seven hBs.1 hBs.2.2.1 hS.2.1 hmul hconst (hsurj rfl)
  have hIc : I.card = 5 ∨ I.card = 6 := by
    rcases hshape with ⟨h, -⟩ | ⟨h, -⟩
    exacts [Or.inr h, Or.inl h]
  have hd : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F :=
    ⟨Nat.prime_two, le_rfl, by rw [hF]; norm_num⟩
  have hr : Rank3Witness (unitarySU 2 1 F I.card) 3 := by
    rcases hIc with h | h
    · rw [h]
      exact rank3Witness_unitarySU_two hd (k := 3) (n := 5) (by norm_num) (by norm_num)
        (Or.inr (by norm_num))
    · rw [h]
      exact rank3Witness_unitarySU_two hd (k := 3) (n := 6) (by norm_num) (by norm_num)
        (Or.inl (by norm_num))
  obtain ⟨hBge, -, htlr6⟩ :=
    ggBstar_card_bounds hThm hBs (n := 6) (by simpa using hcard)
  have htlr : LargeEvenTwoLocalRank 3 G < 7 := by
    have := htlr6 hBne
    omega
  have hB9 : 9 < Nat.card B := by
    have : (9 : ℕ) < 3 ^ 6 := by norm_num
    omega
  obtain ⟨J₁, hP5, hlay, hmark, hSU⟩ := assemble hThm hBs hN hker hF hφs hφker hζ hw hI
    (by omega) (by omega) (by omega) hzB hznot hB9 hBF hr (by omega)
  refine ⟨u, z, J₁, I.card - 1, hw, hmul, hconst, hsurj, h9, hzB, ?_, hP5, hlay, hmark, hSU⟩
  rcases hshape with ⟨h, hA⟩ | ⟨h, hB⟩
  · exact Or.inl ⟨rfl, by omega, hA⟩
  · exact Or.inr ⟨Or.inl ⟨rfl, by omega⟩, hB⟩

private theorem nine_case
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L : Subgroup G} (hThm : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4)
    (hcard : Nat.card Bs = 3 ^ 8) {φ : ↥(unitarySU 2 1 F 9) →* ↥L}
    (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → ∃ c : F,
      ((g : GL (Fin 9) F) : Matrix (Fin 9) (Fin 9) F) = Matrix.diagonal fun _ => c)
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin 9 → F, ActsDiagU φ a t)
    (hSC : GGTorusSelfCent 3 (ggGamma L hN).range) {ζ : Fˣ} (hζ : orderOf ζ = 3) :
    P5UnitaryOut G B Bs L x F 9 φ ζ := by
  have hS : LargeEvenSStar 3 B x L := hThm.2.2.2.2.2.2.1
  obtain ⟨u, hw, hmul, hconst, h7, h9⟩ :=
    exists_p5Coord hThm hBs hN hker hF (Or.inr ⟨rfl, rfl⟩) hcard hφs hφker hdiag hSC hζ
  obtain ⟨hsum, hsurj⟩ := h9 rfl
  obtain ⟨z, hzB, I, t, hI, hIc, hznot, hBF, hshape⟩ :=
    exists_goodPlane_nine hBs.1 hBs.2.2.1 hS.2.1 hmul hconst hsum hsurj
  have hd : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 F :=
    ⟨Nat.prime_two, le_rfl, by rw [hF]; norm_num⟩
  have hr : Rank3Witness (unitarySU 2 1 F I.card) 5 := by
    rw [hIc]
    exact rank3Witness_unitarySU_two hd (k := 5) (n := 7) (by norm_num) (by norm_num)
      (Or.inr (by norm_num))
  obtain ⟨hBge, htlr8, -⟩ :=
    ggBstar_card_bounds hThm hBs (n := 7) (by simpa using hcard)
  have htlr : LargeEvenTwoLocalRank 3 G < 11 := by omega
  have hB9 : 9 < Nat.card B := by
    have : (9 : ℕ) < 3 ^ 7 := by norm_num
    omega
  obtain ⟨J₁, hP5, hlay, hmark, hSU⟩ := assemble hThm hBs hN hker hF hφs hφker hζ hw hI
    (by omega) (by omega) (by omega) hzB hznot hB9 hBF hr (by omega)
  exact ⟨u, z, J₁, I.card - 1, hw, hmul, hconst, h7, h9, hzB,
    Or.inr ⟨Or.inr ⟨rfl, by omega⟩, hshape⟩, hP5, hlay, hmark, hSU⟩

theorem exists_p5Out_of_unitaryModel
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L : Subgroup G} (hThm : GGThmIHyp 3 B x L)
    (hBs : GGBstar 3 B Bs) (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 4) {m n : ℕ}
    (hmn : (m = 7 ∧ n = 7 ∧ B ≠ Bs) ∨ (m = 9 ∧ n = 8)) (hcard : Nat.card Bs = 3 ^ n)
    {φ : ↥(unitarySU 2 1 F m) →* ↥L} (hφs : Function.Surjective φ)
    (hφker : ∀ g, φ g = 1 → ∃ c : F,
      ((g : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = Matrix.diagonal fun _ => c)
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin m → F, ActsDiagU φ a t)
    (hSC : GGTorusSelfCent 3 (ggGamma L hN).range) {ζ : Fˣ} (hζ : orderOf ζ = 3) :
    ∃ (u : G → Fin m → ZMod 3) (z : G) (J₁ : Subgroup G) (k : ℕ),
      (∀ b ∈ Bs, ∀ s s' : ↥(unitarySU 2 1 F m),
        (s' : GL (Fin m) F) = TauCeti.diagGL (fun i => ζ ^ (u b i).val) * s *
          (TauCeti.diagGL (fun i => ζ ^ (u b i).val))⁻¹ →
        ((φ s' : ↥L) : G) = b⁻¹ * φ s * b) ∧
      (∀ b ∈ Bs, ∀ b' ∈ Bs, ∃ c : ZMod 3, ∀ i, u (b * b') i = u b i + u b' i + c) ∧
      (∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔ b ∈ Subgroup.zpowers x) ∧
      (m = 7 → ∀ v : Fin m → ZMod 3, ∃ b ∈ Bs, ∃ c : ZMod 3, ∀ i, u b i = v i + c) ∧
      (m = 9 → (∀ b ∈ Bs, ∑ i, u b i = 0) ∧
        ∀ v : Fin m → ZMod 3, ∑ i, v i = 0 → ∃ b ∈ Bs, ∃ c : ZMod 3, ∀ i, u b i = v i + c) ∧
      z ∈ B ∧
      ((m = 7 ∧ k = 5 ∧ ∃ j : Fin m, ∃ c : ZMod 3, ∀ i,
          u z i = (Pi.single j 1 : Fin m → ZMod 3) i + c) ∨
        (((m = 7 ∧ k = 4) ∨ (m = 9 ∧ k = 6)) ∧ ∃ j j' : Fin m, j ≠ j' ∧ ∃ c : ZMod 3, ∀ i,
          u z i = (Pi.single j 1 - Pi.single j' 1 : Fin m → ZMod 3) i + c)) ∧
      P5Out B Bs x z L (Subgroup.closure {x, z}) J₁ ∧
      J₁ = LargeEvenLayer (L ⊓ Subgroup.centralizer (Subgroup.closure {x, z} : Set G)) ∧
      LargeEvenMarking ↥J₁ (fun lab _ _ _ _ _ => lab = ⟨.twA, k, 1⟩) ∧
      Nonempty (↥J₁ ≃* unitarySU 2 1 F (k + 1)) := by
  rcases hmn with ⟨rfl, rfl, hBne⟩ | ⟨rfl, rfl⟩
  · exact seven_case hThm hBs hN hker hF hBne hcard hφs hφker hdiag hSC hζ
  · exact nine_case hThm hBs hN hker hF hcard hφs hφker hdiag hSC hζ

end CFSG.StandardType.FrameRoute.UnitaryModel
