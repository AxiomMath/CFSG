module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2KTC
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2Fx
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2E6

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.CosetGeom CFSG.ASVolI.ChF
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped IsMulCommutative commutatorElement

section NormalizerCentralizerMod

variable {G : Type} [Group G]

theorem le_normalizer_centralizerMod_nfa2 {V₁ X U S : Subgroup G} (hSX : S ≤ X)
    (hSU : S ≤ Subgroup.normalizer (U : Set G)) (hSV : S ≤ Subgroup.centralizer (V₁ : Set G)) :
    S ≤ Subgroup.normalizer ((centralizerMod V₁ X U : Subgroup G) : Set G) := by
  apply le_normalizer_of_conj_mem'
  intro s hs c hc
  obtain ⟨hcX, hcN, hcU⟩ := mem_centralizerMod.mp hc
  have hsN : s ∈ Subgroup.normalizer (V₁ : Set G) := Subgroup.centralizer_le_normalizer _ (hSV hs)
  refine mem_centralizerMod.mpr ⟨X.mul_mem (X.mul_mem (hSX hs) hcX) (X.inv_mem (hSX hs)),
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hsN hcN) (Subgroup.inv_mem _ hsN), fun u hu => ?_⟩
  have hu' : s⁻¹ * u * s ∈ U := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hSU (Subgroup.inv_mem S hs)) u).mp hu
    rwa [inv_inv] at h1
  have h2 := (Subgroup.mem_normalizer_iff.mp hsN _).mp (hcU _ hu')
  have e : s * c * s⁻¹ * u * (s * c * s⁻¹)⁻¹ * u⁻¹ =
      s * (c * (s⁻¹ * u * s) * c⁻¹ * (s⁻¹ * u * s)⁻¹) * s⁻¹ := by
    group
  rw [e]
  exact h2

end NormalizerCentralizerMod

section LeTCNormal

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem A2Cfg.le_TC_of_normal (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (c : A2Cfg G T M L D H K q) {C : Subgroup G} (hCG : C ≤ a2G2 K T)
    (hCn : a2G2 K T ≤ Subgroup.normalizer (C : Set G)) (hKC : ¬ K ≤ C) : C ≤ a2TC K T := by
  obtain ⟨t₀, ht₀T, ht₀K, hK'c, hKK, -⟩ := c.kstruct h37 h38
  have hK : K ∈ cComp (H ⊔ D) := c.nf.K_comp
  have hKN' : K ≤ Subgroup.normalizer ((K.map (MulAut.conj t₀).toMonoidHom : Subgroup G) : Set G) :=
    le_normalizer_of_mem_cComp hK'c hK
  have hK'N : K.map (MulAut.conj t₀).toMonoidHom ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_mem_cComp hK hK'c
  have hKG : K ≤ a2G2 K T := (le_conjClosure K T).trans le_sup_left
  have hK'K₀ : K.map (MulAut.conj t₀).toMonoidHom ≤ conjClosure K T := by
    rw [hKK]
    exact le_sup_right
  have hK'G : K.map (MulAut.conj t₀).toMonoidHom ≤ a2G2 K T := hK'K₀.trans le_sup_left
  have hK0N : conjClosure K T ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKK]
    exact sup_le (fun k hk => Subgroup.le_normalizer hk) hK'N
  have hK0N' : conjClosure K T ≤
      Subgroup.normalizer ((K.map (MulAut.conj t₀).toMonoidHom : Subgroup G) : Set G) := by
    rw [hKK]
    exact sup_le hKN' (fun k hk => Subgroup.le_normalizer hk)
  have hG2N₀ : a2G2 K T ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    sup_le (fun k hk => Subgroup.le_normalizer hk) (le_normalizer_conjClosure K T)
  have hNN : a2G2 K T ≤ Subgroup.normalizer ((C ⊓ conjClosure K T : Subgroup G) : Set G) := by
    apply le_normalizer_of_conj_mem'
    intro s hs x hx
    obtain ⟨hxC, hxK₀⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hCn hs) x).mp hxC,
      (Subgroup.mem_normalizer_iff.mp (hG2N₀ hs) x).mp hxK₀⟩
  have hA : (C ⊓ conjClosure K T) ⊓ K ≤ pCoreOf 2 K := by
    have hKN_X : K ≤ Subgroup.normalizer (((C ⊓ conjClosure K T) ⊓ K : Subgroup G) : Set G) := by
      apply le_normalizer_of_conj_mem'
      intro k hk x hx
      obtain ⟨hxN, hxK⟩ := Subgroup.mem_inf.mp hx
      exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hNN (hKG hk)) x).mp hxN,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hk hxK) (Subgroup.inv_mem _ hk)⟩
    have hXn : (((C ⊓ conjClosure K T) ⊓ K).subgroupOf K).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hKN_X
    have hXmap := hXn.map (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (QuotientGroup.mk'_surjective _)
    rcases CFSG.LocalCores.quasisimple_normal_subgroups c.nf.Kq hXmap with h | h
    · exfalso
      have hKX : K ≤ (C ⊓ conjClosure K T) ⊓ K :=
        CFSG.Quasithin.EmptyFaithfulMultiple.L15420.le_of_map_eq_top inf_le_right hXn
          (perfect_of_mem_cComp c.nf.K_comp) h
      exact hKC ((hKX.trans inf_le_left).trans inf_le_left)
    · rw [center_quot_of_cfg c, le_bot_iff] at h
      exact CFSG.Quasithin.EmptyFaithfulMultiple.L15420.le_pCoreOf_of_map_eq_bot inf_le_right h
  have hB : (C ⊓ conjClosure K T) ⊓ K.map (MulAut.conj t₀).toMonoidHom ≤
      pCoreOf 2 (K.map (MulAut.conj t₀).toMonoidHom) := by
    intro x hx
    obtain ⟨hxN, hxK'⟩ := Subgroup.mem_inf.mp hx
    have ht₀G : t₀⁻¹ ∈ a2G2 K T := (a2G2 K T).inv_mem (Subgroup.mem_sup_right ht₀T)
    have hconjN : t₀⁻¹ * x * t₀ ∈ C ⊓ conjClosure K T := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (hNN ht₀G) x).mp hxN
      rwa [inv_inv] at h1
    have hconjK : t₀⁻¹ * x * t₀ ∈ K := (mem_map_conj_iff' K t₀ x).mp hxK'
    have hconjP : t₀⁻¹ * x * t₀ ∈ pCoreOf 2 K := hA (Subgroup.mem_inf.mpr ⟨hconjN, hconjK⟩)
    rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj t₀) K]
    exact (mem_map_conj_iff' _ t₀ x).mpr hconjP
  have hCK : C ⊓ conjClosure K T ≤
      kerAct K ⊓ kerAct (K.map (MulAut.conj t₀).toMonoidHom) := by
    intro g hg
    have hgK₀ : g ∈ conjClosure K T := (Subgroup.mem_inf.mp hg).2
    refine Subgroup.mem_inf.mpr ⟨mem_kerAct.mpr ⟨hK0N hgK₀, fun k hk => ?_⟩,
      mem_kerAct.mpr ⟨hK0N' hgK₀, fun k' hk' => ?_⟩⟩
    · have e : g * k * g⁻¹ * k⁻¹ = g * (k * g⁻¹ * k⁻¹) := by group
      have hkN : k * g⁻¹ * k⁻¹ ∈ C ⊓ conjClosure K T :=
        (Subgroup.mem_normalizer_iff.mp (hNN (hKG hk)) g⁻¹).mp (Subgroup.inv_mem _ hg)
      have hgK : g * k * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hK0N hgK₀) k).mp hk
      have hmem : g * (k * g⁻¹ * k⁻¹) ∈ (C ⊓ conjClosure K T) ⊓ K := by
        refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ hg hkN, ?_⟩
        rw [← e]
        exact Subgroup.mul_mem _ hgK (Subgroup.inv_mem _ hk)
      rw [e]
      exact hA hmem
    · have e : g * k' * g⁻¹ * k'⁻¹ = g * (k' * g⁻¹ * k'⁻¹) := by group
      have hkN : k' * g⁻¹ * k'⁻¹ ∈ C ⊓ conjClosure K T :=
        (Subgroup.mem_normalizer_iff.mp (hNN (hK'G hk')) g⁻¹).mp (Subgroup.inv_mem _ hg)
      have hgK' : g * k' * g⁻¹ ∈ K.map (MulAut.conj t₀).toMonoidHom :=
        (Subgroup.mem_normalizer_iff.mp (hK0N' hgK₀) k').mp hk'
      have hmem : g * (k' * g⁻¹ * k'⁻¹) ∈
          (C ⊓ conjClosure K T) ⊓ K.map (MulAut.conj t₀).toMonoidHom := by
        refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ hg hkN, ?_⟩
        rw [← e]
        exact Subgroup.mul_mem _ hgK' (Subgroup.inv_mem _ hk')
      rw [e]
      exact hB hmem
  have hNG : C ⊓ conjClosure K T ≤ a2G2 K T := inf_le_right.trans le_sup_left
  have hNTC : C ⊓ conjClosure K T ≤ a2TC K T := by
    intro g hg
    exact c.le_TC_of_acts_trivially h37 h38 ht₀T ht₀K (Subgroup.mem_inf.mpr ⟨hNG hg, hCK hg⟩)
  have hN2 : IsPGroup 2 ↥(C ⊓ conjClosure K T) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (a2G2 K T)).to_le hNTC
  have hC2 : IsPGroup 2 ↥C :=
    isPGroup_two_of_le_sup c.nf.hyp.sylow.1 (le_normalizer_conjClosure K T) hCG hN2
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hCG hCn hC2

theorem A2Cfg.not_K_le_H (h5 : Stmt3_3_5) (h7 : Stmt3_3_7)
    (h9 : Stmt3_3_9) (h128 : Lemma128Two) (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (h39 : A39ForSQTKCat) (c : A2Cfg G T M L D H K q) : ¬ K ≤ H := by
  intro hKH
  obtain ⟨t₀, ht₀T, -, -, hKK, -⟩ := c.kstruct h37 h38
  have ht₀H : t₀ ∈ H := c.nf.inH.1 ht₀T
  have hK'H : K.map (MulAut.conj t₀).toMonoidHom ≤ H := by
    rintro _ ⟨k, hk, rfl⟩
    exact H.mul_mem (H.mul_mem ht₀H (hKH hk)) (H.inv_mem ht₀H)
  have hK0H : conjClosure K T ≤ H := by
    rw [hKK]
    exact sup_le hKH hK'H
  have hK0M : conjClosure K T ≤ M :=
    hK0H.trans ((CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H).trans (c.normalizer_le_M h5 h7 h9))
  exact c.not_K0_le_M h128 h37 h38 h39 hK0M

end LeTCNormal

theorem leaf_E1b_of (hLS1 : Leaf_LS1)
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) :
    ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ),
      A2Cfg G T M L D H K q → coreIn (a2G1 L T ⊓ a2G2 K T) (a2G2 K T) ≤ a2TC K T := by
  intro G _ _ T M L D H K q c
  rw [hLS1 G T M L D H K q c]
  have hKC : ¬ K ≤ coreIn H (a2G2 K T) := fun hKC =>
    c.not_K_le_H h5 h7 h9 h128 h37 h38 h39 (hKC.trans (coreIn_le_right H (a2G2 K T)))
  exact c.le_TC_of_normal h37 h38 (coreIn_le_left H (a2G2 K T))
    (le_normalizer_coreIn H (a2G2 K T)) hKC

theorem leaf_E5b_of (h36 : A36ForSQTK) (hLSCV : Leaf_LSCV)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) :
    ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ),
      A2Cfg G T M L D H K q → E5aConcl L K T H →
        centralizerMod (a2Z T) (a2G2 K T) (a2UH L T H K) ≤ a2TC K T := by
  intro G _ _ T M L D H K q c _
  have hG2Z : a2G2 K T ≤ Subgroup.centralizer (a2Z T : Set G) := c.G2_le_centralizer_Z h36
  have hCG : centralizerMod (a2Z T) (a2G2 K T) (a2UH L T H K) ≤ a2G2 K T :=
    centralizerMod_le_left _ _ _
  have hCn : a2G2 K T ≤
      Subgroup.normalizer ((centralizerMod (a2Z T) (a2G2 K T) (a2UH L T H K) : Subgroup G) : Set G) :=
    le_normalizer_centralizerMod_nfa2 le_rfl
      (le_normalizer_conjClosure (⁅vPlus L T, oTwoUpper H⁆) (conjClosure K T ⊔ T)) hG2Z
  have hKC : ¬ K ≤ centralizerMod (a2Z T) (a2G2 K T) (a2UH L T H K) := by
    intro hKC
    obtain ⟨x, hxY, hxK, hx3⟩ := c.exists_x h37 h38
    have hxC := hKC hxK
    have hbC : Subgroup.zpowers x ≤ centralizerMod (a2Z T) (a2G2 K T) (a2UH L T H K) :=
      Subgroup.zpowers_le.mpr hxC
    have key : ∀ b ∈ centralizerMod (a2Z T) (a2G2 K T) (a2UH L T H K), ∀ a ∈ a2UH L T H K,
        ⁅a, b⁆ ∈ a2Z T := by
      intro b hb a ha
      have h1 := (mem_centralizerMod.mp hb).2.2 a ha
      have e : ⁅a, b⁆ = (b * a * b⁻¹ * a⁻¹)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [e]
      exact (a2Z T).inv_mem h1
    apply c.not_comm_le_Z hLSCV hxY hx3
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact key b (hbC hb) a (le_conjClosure (⁅vPlus L T, oTwoUpper H⁆) (conjClosure K T ⊔ T) ha)
  exact c.le_TC_of_normal h37 h38 hCG hCn hKC

end CFSG.Quasithin.H13.NFa2
