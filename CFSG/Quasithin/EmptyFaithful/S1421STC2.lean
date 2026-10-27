module

public import CFSG.Quasithin.EmptyFaithful.S1421STC
public import CFSG.Quasithin.Vol2.Ch1Comm
public import CFSG.Quasithin.EmptyFaithful.S1421Hyp111
public import CFSG.Quasithin.EmptyFaithful.S1421Inputs
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.Vol2.Ch12Sec8Three

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem K1_le_mcOf (st : Setting1427 T M H K1) : K1 ≤ mcOf T :=
  st.notation_.le_K.trans ((oTwoUpper_le H).trans
    (st.hyp.isUniqueM_centralizer st.hStar.1 st.hStar.2.1).1.2)

theorem not_le_mcOf_of_normal (st : Setting1427 T M H K1) {G0 L : Subgroup G}
    (hYG0 : yOfL22 T M ≤ G0) (hLG0 : L ≤ G0) (hLn : (L.subgroupOf G0).Normal) (hKL : K1 ≤ L) :
    ¬ L ≤ mcOf T := by
  intro hLc
  have h1281 := lemma_14_2_4 st.hyp st.facts
  have hGN : G0 ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLG0).mp hLn
  obtain ⟨hVred, -⟩ := h1281.isTwoReducedIn
  obtain ⟨z, hzZ, hz1⟩ : ∃ z ∈ quasithinOmegaOneCenter T, z ≠ 1 := by
    by_contra hall
    push Not at hall
    exact h1281.omegaOneCenter_ne_bot (by
      rw [eq_bot_iff]
      intro w hw
      rw [Subgroup.mem_bot]
      exact hall w hw)
  have hzV : z ∈ VZ T M := le_conjClosure _ _ hzZ
  have hLV : L ≤ Subgroup.centralizer (VZ T M : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    by_cases hv1 : v = 1
    · rw [hv1, mul_one, one_mul]
    obtain ⟨y, hy, hyz⟩ := h1281.exists_conj_eq hzV hv hz1 hv1
    have hy' : y⁻¹ * l * y ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hGN (inv_mem (hYG0 hy))) l).mp hl
      simpa using this
    have hc : (y⁻¹ * l * y) * z = z * (y⁻¹ * l * y) :=
      ((Subgroup.mem_centralizer_iff.mp (hLc hy') z hzZ)).symm
    have hlv : l * v * l⁻¹ = v := by
      rw [← hyz]
      calc l * (y * z * y⁻¹) * l⁻¹ = y * ((y⁻¹ * l * y) * z * (y⁻¹ * l * y)⁻¹) * y⁻¹ := by group
        _ = y * z * y⁻¹ := by rw [hc]; group
    calc v * l = (l * v * l⁻¹) * l := by rw [hlv]
      _ = l * v := by group
  have hLM : L ≤ M := by
    have := hLV.trans (Subgroup.centralizer_le_normalizer (s := ((VZ T M : Subgroup G) : Set G)))
    rwa [h1281.normalizer_VZ] at this
  exact st.notation_.not_le (hKL.trans hLM)

theorem exists_cComp_normal_of_syl (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (st : Setting1427 T M H K1) {G0 : Subgroup G} (hne : pCoreOf 2 G0 ≠ ⊥)
    (hS : IsSylowTwoOf (sOf T K1) G0) (hK1 : K1 ≤ G0) :
    ∃ L ∈ cComp G0, K1 ≤ L ∧ (L.subgroupOf G0).Normal := by
  have hB : K1 ∈ lFamily (sOf T K1) := st.notation_.cComp_mem
  obtain ⟨L, hL, hKL⟩ := lemma_1_2_4_exists st.hyp.qtke st.hyp.simple st.hyp.nonabelian h37 h39 hne
    hS hK1 hB
  exact ⟨L, hL, hKL, lemma_1_2_4_normal st.hyp.qtke st.hyp.simple st.hyp.nonabelian h37 h38 hne hS hB
    hKL hL inf_le_right⟩

end S1421

@[expose] def Lemma14215Step2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    S1421.sOf T K1 < T → pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1 →
    ∀ M₁ : Subgroup G,
      InM (K1 ⊔ S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1) M₁ → ¬ T ≤ M₁ →
        IsSylowTwoOf (S1421.sOf T K1) M₁

@[expose] def Lemma14215Core3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M H K1 : Subgroup G), Setting1427 T M H K1 →
    S1421.sOf T K1 < T → pCoreOf 2 (yOfL22 T M) ≤ S1421.sOf T K1 →
    pCoreOf 2 (K1 ⊔ S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1) ≠ ⊥ →
    ∀ M₁ : Subgroup G,
      InM (K1 ⊔ S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1) M₁ → ¬ T ≤ M₁ →
      IsSylowTwoOf (S1421.sOf T K1) M₁ →
      ∀ L : Subgroup G,
        L ∈ cComp (K1 ⊔ S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1) → K1 < L →
        (L.subgroupOf (K1 ⊔ S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1)).Normal →
        K1 ⊔ S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1 = L ⊔ yOfL22 T M ⊔ S1421.sOf T K1 →
        ¬ L ≤ mcOf T → False

theorem lemma14215_of_step2_core3 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h2 : Lemma14215Step2) (h3 : Lemma14215Core3) : Lemma14215 := by
  intro G _ _ T M H K1 st hlt h13
  by_contra hne
  obtain ⟨M₁, hM₁⟩ := exists_inM_of_pCoreOf_ne_bot hne
  have hT : ¬ T ≤ M₁ := S1421.not_le_of_inM_G0 st hM₁
  have hS : IsSylowTwoOf (S1421.sOf T K1) M₁ := h2 G T M H K1 st hlt h13 M₁ hM₁ hT
  have hS2S : S1421.s2Of T H (yOfL22 T M) ≤ S1421.sOf T K1 := S1421.s2_le_sOf st.notation_ h13
  have hSG0 : S1421.sOf T K1 ≤ K1 ⊔ S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1 := le_sup_right
  have hK1G0 : K1 ≤ K1 ⊔ S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1 := le_sup_left.trans le_sup_left
  have hYG0 : yOfL22 T M ≤ K1 ⊔ S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1 :=
    (le_sup_left : yOfL22 T M ≤ S1421.l2Of T H (yOfL22 T M)).trans (le_sup_right.trans le_sup_left)
  have hSylG0 : IsSylowTwoOf (S1421.sOf T K1) (K1 ⊔ S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1) :=
    A4.isSylowTwoOf_mono hS hSG0 hM₁.2
  obtain ⟨L, hL, hKL, hLn⟩ := S1421.exists_cComp_normal_of_syl h37 h38 h39 st hne hSylG0 hK1G0
  have hLG0 : L ≤ K1 ⊔ S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1 := le_of_mem_cComp hL
  have hLc : ¬ L ≤ mcOf T := S1421.not_le_mcOf_of_normal st hYG0 hLG0 hLn hKL
  have hlt' : K1 < L := lt_of_le_of_ne hKL fun h => hLc (h ▸ S1421.K1_le_mcOf st)
  have hGeq : K1 ⊔ S1421.l2Of T H (yOfL22 T M) ⊔ S1421.sOf T K1 =
      L ⊔ yOfL22 T M ⊔ S1421.sOf T K1 := by
    refine le_antisymm (sup_le (sup_le (hKL.trans (le_sup_left.trans le_sup_left)) ?_) le_sup_right)
      (sup_le (sup_le hLG0 hYG0) hSG0)
    exact sup_le (le_sup_right.trans le_sup_left) (hS2S.trans le_sup_right)
  exact h3 G T M H K1 st hlt h13 hne M₁ hM₁ hT hS L hL hlt' hLn hGeq hLc

end CFSG.Quasithin
