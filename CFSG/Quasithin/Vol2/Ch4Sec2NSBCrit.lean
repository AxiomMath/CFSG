module

public import CFSG.Quasithin.Background.C48PfA
public import CFSG.Quasithin.Vol2.Ch4Sec2NSBKer

public section

namespace CFSG.Quasithin.H13.Ch4.NSB

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4 CFSG.Quasithin.H13.Ch4 CFSG.Quasithin.CosetGraph
open scoped commutatorElement Pointwise

private theorem rPlus_eq_pCoreOf' {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G}
    {m k : ℕ} (hd : NoSumBigData G T M L Mm I H K m k) : rPlus T M L = pCoreOf 2 (L ⊔ T) := by
  rw [hd.1.pCoreOf_sup_eq_inf, hd.2.2.1.conjClosure_eq]

private theorem mem_normalizer_centralizerSection_nsb {G : Type} [Group G] [Finite G]
    {M L : Subgroup G} {g : G} (hM : g ∈ M) (hL : g ∈ Subgroup.normalizer (L : Set G)) :
    g ∈ Subgroup.normalizer (centralizerSection M L (pCoreOf 2 L) : Set G) := by
  have key : ∀ {g : G}, g ∈ M → g ∈ Subgroup.normalizer (L : Set G) →
      ∀ x ∈ centralizerSection M L (pCoreOf 2 L), g * x * g⁻¹ ∈ centralizerSection M L (pCoreOf 2 L) := by
    intro g hM hL x hx
    obtain ⟨hxM, hxL, hxO, hxc⟩ := hx
    have hgO : g ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) := normalizer_le_normalizer_pCoreOf 2 L hL
    refine ⟨M.mul_mem (M.mul_mem hM hxM) (M.inv_mem hM),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hL hxL) (Subgroup.inv_mem _ hL),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgO hxO) (Subgroup.inv_mem _ hgO), fun l hl => ?_⟩
    have hl' : g⁻¹ * l * g ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hL) l).mp hl
      simpa using this
    have h1 := hxc _ hl'
    have e : l * (g * x * g⁻¹) * l⁻¹ * (g * x * g⁻¹)⁻¹ =
        g * ((g⁻¹ * l * g) * x * (g⁻¹ * l * g)⁻¹ * x⁻¹) * g⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp hgO _).mp h1
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key hM hL x hx, fun hx => ?_⟩
  have := key (M.inv_mem hM) (Subgroup.inv_mem _ hL) _ hx
  simpa [mul_assoc] using this

private theorem mem_normalizer_centralizer_nsb {G : Type} [Group G] {V : Subgroup G} {g : G}
    (hV : g ∈ Subgroup.normalizer (V : Set G)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := by
  have key : ∀ {g : G}, g ∈ Subgroup.normalizer (V : Set G) →
      ∀ c ∈ Subgroup.centralizer (V : Set G), g * c * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    intro g hg c hc
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : g⁻¹ * v * g ∈ V := (Subgroup.mem_normalizer_iff''.mp hg v).mp hv
    have h1 := (Subgroup.mem_centralizer_iff.mp hc) _ hv'
    calc v * (g * c * g⁻¹) = g * ((g⁻¹ * v * g) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * v := by group
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key hV c hc, fun hc => ?_⟩
  have := key (Subgroup.inv_mem _ hV) _ hc
  simpa [mul_assoc] using this

theorem amalgamData_of (h31 : Lemma31) (h32 : Lemma32) (hK : KRInfGammaZero) : AmalgamData := by
  intro G _ _ T M L Mm I H K m k hch hIV
  have hd : NoSumBigData G T M L Mm I H K m k := hch.1
  have hcf : Conf4212 G T M L I H K := hd.2.2.1
  obtain ⟨hRlt, hRC⟩ := h31 G T M L Mm I H K m k hd
  have hrP : rPlus T M L = pCoreOf 2 (L ⊔ T) := rPlus_eq_pCoreOf' hd
  refine ⟨hK G T M L Mm I H K m k hch hIV, ?_, ?_, ?_⟩
  ·
    obtain ⟨s, hsP, hsN, hsR⟩ := exists_mem_normalizer_not_mem (P := rPlus T M L)
      (hrP ▸ pCoreOf_isPGroup 2 (L ⊔ T)) hRlt
    have hmem : ∀ x ∈ rPlus T M L, x ∈ Subgroup.normalizer ((pCoreOf 2 I : Subgroup G) : Set G) →
        x ∈ gammaZero T M L I := fun x hx hxN => ⟨⟨hx.2, hxN⟩, hRC hx⟩
    refine lt_of_le_of_ne (fun r hr => hmem r (hRlt.le hr) (Subgroup.le_normalizer hr)) fun h => hsR ?_
    rw [h]
    exact hmem s hsP hsN
  ·
    intro i hi
    have hiM : i ∈ M := hcf.I_le hi
    have hiL : i ∈ Subgroup.normalizer (L : Set G) := hcf.normal hiM
    have hiR : i ∈ Subgroup.normalizer ((pCoreOf 2 I : Subgroup G) : Set G) :=
      le_normalizer_pCoreOf 2 I hi
    have hiC : i ∈ Subgroup.normalizer (centralizerSection M L (pCoreOf 2 L) : Set G) :=
      mem_normalizer_centralizerSection_nsb hiM hiL
    have hiV : i ∈ Subgroup.normalizer ((vV T L : Subgroup G) : Set G) := hIV hi
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.inf_normalizer_le_normalizer_inf ⟨hiC, Subgroup.le_normalizer hiR⟩,
        mem_normalizer_centralizer_nsb hiV⟩
  ·
    have hΩ : K ≤ Subgroup.normalizer
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 I)) : Set G) :=
      (le_sup_left.trans (le_normalizer_pCoreOf 2 (K ⊔ pCoreOf 2 I))).trans
        (normalizer_le_normalizer_omegaOneCenterOf _)
    exact (commutator_le_left_of_le_normalizer hΩ).trans (omegaOneCenterOf_le _)

private theorem mem_normalizer_commutator_nsb {G : Type} [Group G] {X Y : Subgroup G} {g : G}
    (hX : g ∈ Subgroup.normalizer (X : Set G)) (hY : g ∈ Subgroup.normalizer (Y : Set G)) :
    g ∈ Subgroup.normalizer ((⁅X, Y⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hX hY ⊢
  rw [Subgroup.map_commutator, hX, hY]

theorem le_normalizer_uZero {G : Type} [Group G] [Finite G] {I H K : Subgroup G}
    (hIH : I ≤ H) (hHK : H ≤ Subgroup.normalizer (K : Set G)) :
    K ⊔ pCoreOf 2 I ≤ Subgroup.normalizer (uZero I K : Set G) := by
  have hRK : pCoreOf 2 I ≤ Subgroup.normalizer (K : Set G) :=
    (pCoreOf_le 2 I).trans (hIH.trans hHK)
  have hAK : K ⊔ pCoreOf 2 I ≤ Subgroup.normalizer (K : Set G) :=
    _root_.sup_le Subgroup.le_normalizer hRK
  have hAΩ : K ⊔ pCoreOf 2 I ≤ Subgroup.normalizer
      (omegaOneCenterOf (pCoreOf 2 (K ⊔ pCoreOf 2 I)) : Set G) :=
    (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_omegaOneCenterOf _)
  intro a ha
  exact mem_normalizer_commutator_nsb (hAΩ ha) (hAK ha)

theorem uZero_le_kerA {G : Type} [Group G] [Finite G] {I K B : Subgroup G}
    (hUO : uZero I K ≤ pCoreOf 2 (K ⊔ pCoreOf 2 I)) (hOR : pCoreOf 2 (K ⊔ pCoreOf 2 I) ≤ pCoreOf 2 I)
    (hRB : pCoreOf 2 I ≤ B) : uZero I K ≤ kerA (K ⊔ pCoreOf 2 I) B := by
  intro u hu
  have huO := hUO hu
  refine ⟨pCoreOf_le 2 _ huO, fun a ha => ?_⟩
  have h1 : a⁻¹ * u * a ∈ pCoreOf 2 (K ⊔ pCoreOf 2 I) := by
    have := (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_pCoreOf 2 _ ((K ⊔ pCoreOf 2 I).inv_mem ha)) u).mp huO
    simpa using this
  exact hRB (hOR h1)

theorem notCriticalPair_of (h22 : ∀ (G : Type) [Group G] [Finite G], ASC22Three G)
    (h31 : Lemma31) (h32 : Lemma32) (hAm : AmalgamData) (hLF : LocalFlip) :
    NotCriticalPair := by
  intro G _ _ T M L Mm I H K m k hch hIV δ ε hc
  have hd : NoSumBigData G T M L Mm I H K m k := hch.1
  have hcf : Conf4212 G T M L I H K := hd.2.2.1
  obtain ⟨hAB, hRG, hIB, hUO⟩ := hAm G T M L Mm I H K m k hch hIV
  obtain ⟨hHK, -⟩ := h32 G T M L Mm I H K m k hd
  have hIH : I ≤ H := hd.2.1.2
  have hRI : pCoreOf 2 I ≤ I := pCoreOf_le 2 I
  have hRK : pCoreOf 2 I ≤ Subgroup.normalizer (K : Set G) := hRI.trans (hIH.trans hHK)
  have hOR : pCoreOf 2 (K ⊔ pCoreOf 2 I) ≤ pCoreOf 2 I :=
    C48Pf.pCoreOf_sup_le (h22 G) hcf.hypC28 hcf.K_mem hRK
  have hRB : pCoreOf 2 I ≤ gammaZero T M L I := hRG.le
  have hBR : gammaZero T M L I ≤
      Subgroup.normalizer (((K ⊔ pCoreOf 2 I) ⊓ gammaZero T M L I : Subgroup G) : Set G) := by
    rw [hAB]
    intro b hb
    exact hb.1.2
  obtain ⟨g, hg, h1, h2, u, hu, hnot⟩ := exists_conj_of_isCriticalPair hBR
    (le_normalizer_uZero hIH hHK) (uZero_le_kerA hUO hOR hRB) hc
  rw [hAB] at h1 h2
  exact hLF G T M L Mm I H K m k hch hIV g hg h1 h2 ⟨u, hu, hnot⟩

end CFSG.Quasithin.H13.Ch4.NSB
