module

public import CFSG.Quasithin.Vol2.Ch11SecE42S2e
public import CFSG.Quasithin.Vol2.Ch11SecEFacts6
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecE42S2a

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem mem_lFamily_iff' {B S : Subgroup G} : B ∈ lFamily S ↔ B ∈ cComp (B ⊔ S) := Iff.rfl

theorem pCoreOf_lOf_le_rOf (h : Hyp11 G T L I n) {V₁ : Subgroup G} (hV₁ : IsVi T L I n 1 V₁) :
    pCoreOf 2 (LOf L V₁) ≤ ROf T L V₁ :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans le_sup_left)
    ((sup_le Subgroup.le_normalizer
      (SecA.T_le_normalizer_lOf h.normal (SecA.IsVi.le_normalizer hV₁))).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

theorem thetaKJ_surjective (h : Hyp11 G T L I n) {V₁ K : Subgroup G} (hLK : LOf L V₁ ≤ K)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (φ : ↥K →* SL(2, ZMod p)) (hφs : Function.Surjective φ)
    (hφk : ∀ k : ↥K, φ k = 1 ↔ (k : G) ∈ oTwoTwoPrime K)
    (hRK : ⁅ROf T L V₁, K⁆ ≤ oTwoTwoPrime K) : Function.Surjective (thetaKJ T L V₁ φ) := by
  intro s
  obtain ⟨s', rfl⟩ := Dickson.pslMap_surjective s
  obtain ⟨k, hk, hφk'⟩ := exists_kJ_preimage h hLK hTK hp5 φ hφs hφk hRK s'
  refine ⟨⟨k, hk⟩, ?_⟩
  show Dickson.pslMap p (φ (Subgroup.inclusion _ ⟨k, hk⟩)) = Dickson.pslMap p s'
  rw [← hφk']
  rfl

theorem cartan_le_normalizer_kJ (hF : Facts42) (hN : SecA.NatFacts) (hPar : ParInFacts)
    (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat)
    (h312 : QuasithinUnique.Vol2Native.A312ForSQTKCat) (h1102 : Stmt11_0_2)
    (h1110 : Stmt11_1_0) (h : Hyp11 G T L I n)
    (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) {V₁ K X : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hX : IsCartanX T L X) (hn : n = 2)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hLK : LOf L V₁ ≤ K) {p : ℕ} [Fact p.Prime]
    (h11 : 11 ≤ p) (φ : ↥K →* SL(2, ZMod p)) (hθs : Function.Surjective (thetaKJ T L V₁ φ))
    (hθR : ∀ k : ↥(kJ T L V₁ K), thetaKJ T L V₁ φ k = 1 → (k : G) ∈ ROf T L V₁)
    {r : G} (hrR : r ∈ ROf T L V₁) (hr1 : r ≠ 1) :
    X ≤ Subgroup.normalizer (kJ T L V₁ K : Set G) := by
  have := h.fsu.simple
  have hp5 : 5 ≤ p := by omega
  set N := Subgroup.normalizer (ROf T L V₁ : Set G) with hNdef
  have hRN : ROf T L V₁ ≤ pCoreOf 2 N :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hNne : pCoreOf 2 N ≠ ⊥ := fun h0 => hr1 (Subgroup.mem_bot.mp (h0 ▸ hRN hrR))
  have hTN : T ≤ N := T_le_normalizer_rOf T L V₁
  have hS := isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTN
  have hKJN : kJ T L V₁ K ≤ N := (kJ_le T L V₁ K).trans inf_le_right
  have hKJl : kJ T L V₁ K ∈ lFamily T := mem_lFamily_iff'.mpr (kJ_mem_cComp hTK hp5 φ hθs hθR)
  have hTKJ := T_le_normalizer_kJ (L := L) (V₁ := V₁) hTK
  have hLocal := (QuasithinUnique.qtkeCore_of_cat h.fsu.nonabelian h.fsu.qtke).1
  obtain ⟨K₀, hK₀, hKJK₀⟩ :=
    QuasithinUnique.Vol2Native.lemma_1_2_4_exists hLocal h37 h39 hNne hS hKJN hKJl
  have hK₀n := QuasithinUnique.Vol2Native.lemma_1_2_4_normal hLocal h37 h38 hNne hS hKJl hKJK₀
    hK₀ hTKJ
  have hXN : X ≤ N := cartan_le_normalizer_rOf hN hPar h1102 h hcV hV₁ hX
  have hXK₀ : X ≤ Subgroup.normalizer (K₀ : Set G) :=
    hXN.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hK₀)).mp hK₀n)
  have hkey : ¬ (A312Case (modO2Image N (kJ T L V₁ K)) (modO2Image N K₀) ∨
      A312Nonquasi (modO2Image N (kJ T L V₁ K)) (modO2Image N K₀)) := by
    intro hc
    obtain ⟨e⟩ := modO2Image_kJ_iso T L V₁ hp5 φ hθs hθR hKJN hRN
    have hL2 := hF.l2p _ _ _ p Fact.out h11 ⟨e⟩ hc
    have hL₁N : LOf L V₁ ≤ N := lOf_le_normalizer_rOf T L V₁
    have hL₁l : LOf L V₁ ∈ lFamily T := SecA.lOf_mem_lFamily hN h1102 h hV₁ (Or.inl rfl) le_rfl
    have hL₁K₀ := (lOf_le_kJ (T := T) hLK).trans hKJK₀
    obtain ⟨F, _, _, hF4, ⟨e₁⟩⟩ := exists_lOf_iso h1110 h hV₁ hn
    obtain ⟨φ', hφ's, hφ'k⟩ := exists_modO2Image_lOf_map hL₁N e₁
    have hlist := QuasithinUnique.Vol2Native.lemma_1_2_4_list hLocal h312 hNne hS hL₁N hL₁l hK₀
      hL₁K₀
    exact (hF.a5 _ _ _ F hF4 ⟨φ', hφ's, hφ'k⟩ hlist p Fact.out (by omega)).1 hL2
  have hKJeq : kJ T L V₁ K = K₀ := by
    rcases QuasithinUnique.Vol2Native.lemma_1_2_4_list hLocal h312 hNne hS hKJN hKJl hK₀ hKJK₀
      with heq | hc | hc
    · exact SecA.eq_of_modO2Image_eq hS (le_of_mem_cComp hK₀) hKJK₀ (perfect_of_mem_cComp hK₀)
        hTKJ heq
    · exact absurd (Or.inl hc) hkey
    · exact absurd (Or.inr hc) hkey
  rw [hKJeq]
  exact hXK₀

theorem le_centralizer_of_sl2pE
    (hF : Facts42) (hSig : SL2pSignalizerFact) (hN : SecA.NatFacts)
    (hPar : ParInFacts) (hP : SecB.PointFacts) (h37 : QuasithinUnique.Vol2Native.A37ForSQTKCat)
    (h38 : QuasithinUnique.Vol2Native.A38ForSQTKCat)
    (h39 : QuasithinUnique.Vol2Native.A39ForSQTKCat)
    (h312 : QuasithinUnique.Vol2Native.A312ForSQTKCat) (h3214 : TmpL6_3_2_14)
    (h1102 : Stmt11_0_2) (h1110 : Stmt11_1_0) (h1141 : Stmt11_4_1) (h : Hyp11 G T L I n)
    (hcV : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) {V₁ K : Subgroup G}
    (hV₁ : IsVi T L I n 1 V₁) (hn : n = 2) (hloc : quasithinIsLocal T K)
    (hTK : T ≤ Subgroup.normalizer (K : Set G)) (hLK : LOf L V₁ ≤ K) {z : G} (hzV₁ : z ∈ V₁)
    (hz1 : z ≠ 1) (hKz : K ≤ Subgroup.centralizer ({z} : Set G))
    (hE : IsSL2pE (↥K ⧸ CFSG.pCore 2 ↥K)) : K ≤ Subgroup.centralizer (V₁ : Set G) := by
  obtain ⟨p, _, φ, h11, hφs, hφk, hinv⟩ := exists_sl2_map_of_sl2pE hE
  have hp5 : 5 ≤ p := by omega
  have hO := oTwoTwoPrime_le_centralizer h3214 hP h1102 h hV₁ hloc hTK hLK
    (not_isQuasisimple_of_sl2pE hE)
  have hRK := commutator_rOf_le_oTwoTwoPrime hSig h1110 h hV₁ hn hLK hTK h11 φ hφs hφk
  obtain ⟨r, hrL, hrK, hφr⟩ := exists_neg_one_mem_pCoreOf h1110 h hV₁ hn hLK h11 φ hφk
  have hrR : r ∈ ROf T L V₁ := pCoreOf_lOf_le_rOf h hV₁ hrL
  have hθs := thetaKJ_surjective h hLK hTK hp5 φ hφs hφk hRK
  have hθR : ∀ k : ↥(kJ T L V₁ K), thetaKJ T L V₁ φ k = 1 → (k : G) ∈ ROf T L V₁ := by
    intro k hk
    exact mem_rOf_of_theta h hLK hTK φ hφk hinv hrR hrK hφr _ k.2 (Dickson.mem_ker_pslMap.mp hk)
  have hr1 : r ≠ 1 := by
    rintro rfl
    have h1 : φ ⟨1, hrK⟩ = 1 := map_one φ
    rw [h1] at hφr
    exact A1c.sl2NegOne_ne_one (by omega) hφr.symm
  obtain ⟨X, hX⟩ := SecD.exists_isCartanX h
  have hXKJ := cartan_le_normalizer_kJ hF hN hPar h37 h38 h39 h312 h1102 h1110 h hcV hV₁ hX hn hTK
    hLK h11 φ hθs hθR hrR hr1
  have hKJz : kJ T L V₁ K ≤ Subgroup.centralizer ({z} : Set G) :=
    ((kJ_le T L V₁ K).trans inf_le_left).trans hKz
  have hnat := SecD.natSetting11_of h1102 h1141 h hV₁
  have hKJV : kJ T L V₁ K ≤ Subgroup.centralizer (V₁ : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1, one_mul, mul_one]
    obtain ⟨x, hx, hxw⟩ := hF.cartan G T L I n V₁ X hnat hV₁ hX z hzV₁ hz1 w hw hw1
    have hk' : x⁻¹ * k * x ∈ kJ T L V₁ K := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hXKJ hx)) k).mp hk
      simpa using this
    have hc := Subgroup.mem_centralizer_singleton_iff.mp (hKJz hk')
    rw [← hxw]
    calc x * z * x⁻¹ * k = x * (z * (x⁻¹ * k * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * k * x) * z) * x⁻¹ := by rw [hc]
      _ = k * (x * z * x⁻¹) := by group
  exact le_centralizer_of_kJ h hLK hTK hp5 φ hφs hφk hRK hO hKJV

end CFSG.Quasithin.Vol2.Ch11.SecE
