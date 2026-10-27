module

public import CFSG.Quasithin.EmptyFaithful.S1421STC3Defs
public import CFSG.Quasithin.EmptyFaithful.S1416
public import CFSG.Quasithin.Vol2.Ch1Unique4
public import CFSG.Quasithin.EmptyFaithful.S1421L11
public import CFSG.Quasithin.EmptyFaithful.S1421STC2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S1421

variable {G : Type} [Group G] [Finite G] {T M H K1 : Subgroup G}

theorem exists_pow_mem_inf_centralizer_VZ (st : Setting1427 T M H K1) {x : G}
    (hx : x ∈ M ⊓ mcOf T) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ M ⊓ Subgroup.centralizer (VZ T M : Set G) := by
  have hMV : M ≤ Subgroup.normalizer (VZ T M : Set G) :=
    ((lemma_14_2_4 st.hyp st.facts).isTwoReducedIn).1.2.1
  have hDM : M ≤ Subgroup.normalizer ((M ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) :
      Set G) := le_normalizer_inf_centralizer hMV
  have hmmc := st.facts.mmc_eq
  have hxDR : x ∈ (M ⊓ Subgroup.centralizer (VZ T M : Set G)) ⊔ pCoreOf 2 (M ⊓ mcOf T) := by
    rw [← hmmc]
    exact hx
  have hDW : (M ⊓ Subgroup.centralizer (VZ T M : Set G)) ≤
      Subgroup.normalizer (pCoreOf 2 (M ⊓ mcOf T) : Set G) := by
    refine le_trans ?_ (le_normalizer_pCoreOf 2 (M ⊓ mcOf T))
    rw [hmmc]
    exact le_sup_left
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hDW] at hxDR
  obtain ⟨c, hc, r, hr, hxcr⟩ := hxDR
  have hr2 : IsPGroup 2 (pCoreOf 2 (M ⊓ mcOf T)) := pCoreOf_isPGroup 2 _
  obtain ⟨k, hk⟩ := hr2 ⟨r, hr⟩
  have hrk : r ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hrM : r ∈ M := ((pCoreOf_le 2 _) hr).1
  obtain ⟨x', hx', hpow⟩ := A4.exists_pow_mul_eq hc (hDM hrM) (2 ^ k)
  refine ⟨k, ?_⟩
  rw [← hxcr, hpow, hrk, mul_one]
  exact hx'

theorem false_of_pRank_conj (st : Setting1427 T M H K1) {g : G} (hg : g ∈ mcOf T)
    {T1 : Subgroup G} (hT1 : T1 ≤ mcOf T) (hK1 : K1 = oTwoUpper K1)
    (hP : ∀ x ∈ K1 ⊔ T1, g⁻¹ * x * g ∈ M)
    (hrank : 2 ≤ CFSG.Open.pRank 3 (conjClosure K1 T1)) : False := by
  set P : Subgroup G := K1 ⊔ T1 with hPdef
  set C : Subgroup G := M ⊓ Subgroup.centralizer (VZ T M : Set G) with hC
  set ψ : G →* G := (MulAut.conj g⁻¹).toMonoidHom with hψ
  have hψapp : ∀ x, ψ x = g⁻¹ * x * g := fun x => by
    rw [hψ]
    simp
  have hK1Mc : K1 ≤ mcOf T := K1_le_mcOf st
  have hPMc : P ≤ mcOf T := sup_le hK1Mc hT1
  have hPN : ∀ x ∈ P, ∃ k : ℕ, x ^ 2 ^ k ∈ C.comap ψ := by
    intro x hx
    have hy : g⁻¹ * x * g ∈ M ⊓ mcOf T :=
      ⟨hP x hx, (mcOf T).mul_mem ((mcOf T).mul_mem ((mcOf T).inv_mem hg) (hPMc hx)) hg⟩
    obtain ⟨k, hk⟩ := exists_pow_mem_inf_centralizer_VZ st hy
    refine ⟨k, ?_⟩
    rw [Subgroup.mem_comap, map_pow, hψapp]
    exact hk
  have hON : oTwoUpper P ≤ C.comap ψ := oTwoUpper_le_of_pow_mem hPN
  have hK1P : K1 ≤ oTwoUpper P :=
    calc K1 = oTwoUpper K1 := hK1
      _ ≤ oTwoUpper P := oTwoUpper_mono le_sup_left
  have hXO : conjClosure K1 T1 ≤ oTwoUpper P := by
    refine conjClosure_le fun h hh z hz => ?_
    exact (Subgroup.mem_normalizer_iff.mp
      (le_normalizer_oTwoUpper P ((le_sup_right : T1 ≤ K1 ⊔ T1) hh)) z).mp (hK1P hz)
  have hXC : (conjClosure K1 T1).map ψ ≤ C :=
    Subgroup.map_le_iff_le_comap.mpr (hXO.trans hON)
  have h1 : 2 ≤ CFSG.Open.pRank 3 C :=
    calc 2 ≤ CFSG.Open.pRank 3 (conjClosure K1 T1) := hrank
      _ ≤ CFSG.Open.pRank 3 ((conjClosure K1 T1).map ψ) :=
        CFSG.SectionRank.pRank_le_map (by norm_num) ψ (MulAut.conj g⁻¹).injective _
      _ ≤ CFSG.Open.pRank 3 C := CFSG.SectionRank.pRank_mono (by norm_num) hXC
  have h2 : CFSG.Open.pRank 3 C ≤ 1 := st.facts.m3_le
  omega

end S1421

theorem lemma14210_of_14209 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h209 : Lemma14209Used) : Lemma14210 := by
  intro G _ _ T M H K1 st hlt T1 hT1 hST1
  have hyp := st.hyp
  have N := st.notation_
  obtain ⟨-, -, hUniq, -⟩ := stageLemma1416_of_a3 h37 h38 h39 G T (mcOf T) hyp.toQTFE14
  obtain ⟨Kc, hKc, hK1Kc, -, hdisj⟩ := h209 G T M H K1 st hlt
  have hKcMc : Kc ≤ mcOf T := le_of_mem_cComp hKc
  have hTMc : IsSylowTwoOf T (mcOf T) :=
    isSylowTwoOf_of_isSylowTwo hyp.sylow hyp.toQTFE14.t_le_mc
  obtain ⟨g, hg, hgT⟩ := A4.exists_conj_of_isSylowTwoOf hTMc hT1
  have hK1perf : K1 = oTwoUpper K1 :=
    eq_oTwoUpper_of_perfect (perfect_of_mem_cComp N.cComp_mem)
  refine ⟨⟨hyp.mc_max, sup_le (hK1Kc.trans hKcMc) hT1.1⟩, fun M' hM' => ?_⟩
  set M'' : Subgroup G := M'.map (MulAut.conj g⁻¹).toMonoidHom with hM''
  have hmem : ∀ x, x ∈ M'' ↔ g * x * g⁻¹ ∈ M' := by
    intro x
    rw [hM'', A38.mem_map_conj]
    simp
  have hTM'' : T ≤ M'' := by
    intro t ht
    rw [hmem]
    refine hM'.2 ((le_sup_right : T1 ≤ K1 ⊔ T1) ((hgT _).mpr ?_))
    rw [show g⁻¹ * (g * t * g⁻¹) * g = t by group]
    exact ht
  rcases hyp.inM_iff.mp ⟨quasithinIsMaxTwoLocal_map_conj hM'.1 g⁻¹, hTM''⟩ with hM''M | hM''Mc
  ·
    exfalso
    have hP : ∀ x ∈ K1 ⊔ T1, g⁻¹ * x * g ∈ M := by
      intro x hx
      rw [← hM''M, hmem]
      simpa [mul_assoc] using hM'.2 hx
    rcases hdisj T1 hT1 hST1 with hle | hrank
    ·
      have hK' : Kc.map (MulAut.conj g⁻¹).toMonoidHom ∈ cComp (mcOf T) :=
        map_conj_mem_cComp hKc ((mcOf T).inv_mem hg)
      have hK'M : Kc.map (MulAut.conj g⁻¹).toMonoidHom ≤ M := by
        intro y hy
        rw [A38.mem_map_conj, inv_inv] at hy
        have := hP _ (hle hy)
        simpa [mul_assoc] using this
      have hMuniq := (hUniq _ hK').2 M ⟨hyp.m_max.1.1, sup_le hK'M hyp.m_max.1.2⟩
      exact hyp.ne_centralizer hMuniq
    · exact S1421.false_of_pRank_conj st hg hT1.1 hK1perf hP hrank
  ·
    ext x
    have h1 : x ∈ M' ↔ g⁻¹ * x * g ∈ M'' := by
      rw [hmem]
      simp [mul_assoc]
    have hM''Mc' : M'' = mcOf T := hM''Mc
    rw [h1, hM''Mc']
    constructor
    · intro hx
      have := (mcOf T).mul_mem ((mcOf T).mul_mem hg hx) ((mcOf T).inv_mem hg)
      simpa [mul_assoc] using this
    · intro hx
      exact (mcOf T).mul_mem ((mcOf T).mul_mem ((mcOf T).inv_mem hg) hx) hg

end CFSG.Quasithin
