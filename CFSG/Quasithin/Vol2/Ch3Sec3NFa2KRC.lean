module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2KTC
public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2KAct

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.CosetGeom CFSG.ASVolI.ChF
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped MatrixGroups commutatorElement

section Commutators

variable {G : Type} [Group G]

theorem le_kerAct_of_comm_le_pCoreOf {K K' : Subgroup G}
    (hK'N : K' ≤ Subgroup.normalizer (K : Set G)) (hcomm : ⁅K, K'⁆ ≤ pCoreOf 2 K) :
    K' ≤ kerAct K := by
  have h2 : ⁅K', K⁆ ≤ pCoreOf 2 K := by
    rw [Subgroup.commutator_comm]
    exact hcomm
  intro k' hk'
  refine mem_kerAct.mpr ⟨hK'N hk', fun x hx => ?_⟩
  have h3 := h2 (Subgroup.commutator_mem_commutator hk' hx)
  rwa [commutatorElement_def] at h3

theorem comm_le_pCoreOf_of_normalizes [Finite G] {K K' : Subgroup G}
    (hK'N : K' ≤ Subgroup.normalizer (K : Set G)) (hKN' : K ≤ Subgroup.normalizer (K' : Set G))
    (hcomm : ⁅K, K'⁆ ≤ pCoreOf 2 K) : ⁅K, K'⁆ ≤ pCoreOf 2 K' := by
  have hKK'comm : ⁅K, K'⁆ ≤ K' := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    exact K'.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKN' hg) h).mp hh) (K'.inv_mem hh)
  have hK'N2 : K' ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    fun k hk => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K (hK'N hk)
  have hXN : K' ≤ Subgroup.normalizer ((pCoreOf 2 K ⊓ K' : Subgroup G) : Set G) :=
    F7.le_normalizer_inf hK'N2 Subgroup.le_normalizer
  have hXle : pCoreOf 2 K ⊓ K' ≤ pCoreOf 2 K' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hXN
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le inf_le_left)
  exact (le_inf hcomm hKK'comm).trans hXle

theorem inv_mul_mem_kerAct_of_second {K : Subgroup G} {a r : G} (ha : a ∈ K)
    (hrN : r ∈ Subgroup.normalizer (K : Set G))
    (h : ∀ k ∈ K, r * k * r⁻¹ * (a * k * a⁻¹)⁻¹ ∈ pCoreOf 2 K) : a⁻¹ * r ∈ kerAct K := by
  have haN : a⁻¹ ∈ Subgroup.normalizer (K : Set G) :=
    Subgroup.inv_mem _ (Subgroup.le_normalizer ha)
  refine mem_kerAct.mpr ⟨Subgroup.mul_mem _ haN hrN, fun k hk => ?_⟩
  have h1 := conj_mem_pCoreOf_of_mem_normalizer haN (h k hk)
  rw [inv_inv] at h1
  have e : a⁻¹ * r * k * (a⁻¹ * r)⁻¹ * k⁻¹ = a⁻¹ * (r * k * r⁻¹ * (a * k * a⁻¹)⁻¹) * a := by
    group
  rw [e]
  exact h1

theorem exists_mem_outside_pair {V A B : Subgroup G} {v₀ v₁ : G} (hv₀V : v₀ ∈ V) (hv₁V : v₁ ∈ V)
    (hv₀ : ¬ (v₀ ∈ A ∧ v₀ ∈ B)) (h1 : v₁ ∈ A ↔ v₀ ∈ B) (h2 : v₁ ∈ B ↔ v₀ ∈ A) :
    ∃ v ∈ V, v ∉ A ∧ v ∉ B := by
  by_cases hA : v₀ ∈ A
  · have hB : v₀ ∉ B := fun hB => hv₀ ⟨hA, hB⟩
    have hv₁B : v₁ ∈ B := h2.mpr hA
    have hv₁A : v₁ ∉ A := fun h => hB (h1.mp h)
    refine ⟨v₀ * v₁, V.mul_mem hv₀V hv₁V, fun h => hv₁A ?_, fun h => hB ?_⟩
    · have h' := A.mul_mem (A.inv_mem hA) h
      simpa using h'
    · have h' := B.mul_mem h (B.inv_mem hv₁B)
      simpa using h'
  · by_cases hB : v₀ ∈ B
    · have hv₁A : v₁ ∈ A := h1.mpr hB
      have hv₁B : v₁ ∉ B := fun h => hA (h2.mp h)
      refine ⟨v₀ * v₁, V.mul_mem hv₀V hv₁V, fun h => hA ?_, fun h => hv₁B ?_⟩
      · have h' := A.mul_mem h (A.inv_mem hv₁A)
        simpa using h'
      · have h' := B.mul_mem (B.inv_mem hB) h
        simpa using h'
    · exact ⟨v₀, hv₀V, hA, hB⟩

theorem relIndex_le_two_of_dichotomy {K R : Subgroup G} {a : G} (ha : a ∈ K)
    (hdich : ∀ r ∈ R, r ∈ kerAct K ∨ a⁻¹ * r ∈ kerAct K) :
    (R ⊓ kerAct K).relIndex R ≤ 2 := by
  have hdvd : (R ⊓ kerAct K).relIndex R ∣ 2 := by
    rw [Subgroup.relIndex_dvd_two_iff]
    by_cases h : ∃ r₀ ∈ R, r₀ ∉ kerAct K
    · obtain ⟨r₀, hr₀R, hr₀⟩ := h
      refine ⟨r₀⁻¹, R.inv_mem hr₀R, fun b hbR => ?_⟩
      by_cases hb : b ∈ kerAct K
      · exact Or.inr (Subgroup.mem_inf.mpr ⟨hbR, hb⟩)
      · left
        have hb2 : a⁻¹ * b ∈ kerAct K := (hdich b hbR).resolve_left hb
        have hr2 : a⁻¹ * r₀ ∈ kerAct K := (hdich r₀ hr₀R).resolve_left hr₀
        have e : b * r₀⁻¹ = a * ((a⁻¹ * b) * (a⁻¹ * r₀)⁻¹) * a⁻¹ := by group
        rw [Subgroup.mem_inf]
        refine ⟨R.mul_mem hbR (R.inv_mem hr₀R), ?_⟩
        rw [e]
        exact conj_mem_kerAct_of_mem_normalizer (Subgroup.le_normalizer ha)
          ((kerAct K).mul_mem hb2 ((kerAct K).inv_mem hr2))
    · push Not at h
      exact ⟨1, R.one_mem, fun b hbR => Or.inr (Subgroup.mem_inf.mpr ⟨hbR, h b hbR⟩)⟩
  exact Nat.le_of_dvd (by norm_num) hdvd

end Commutators

section CentreAndConj

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem A2Cfg.conj_le_kerAct (c : A2Cfg G T M L D H K q) {t : G} (ht : t ∈ T)
    (htK : t ∉ Subgroup.normalizer (K : Set G)) :
    K.map (MulAut.conj t).toMonoidHom ≤ kerAct K := by
  have htH₀ : t ∈ H ⊔ D := Subgroup.mem_sup_left (c.nf.inH.1 ht)
  have hK : K ∈ cComp (H ⊔ D) := c.nf.K_comp
  set K' := K.map (MulAut.conj t).toMonoidHom with hK'def
  have hK' : K' ∈ cComp (H ⊔ D) := CFSG.Quasithin.map_conj_mem_cComp hK htH₀
  have hKK' : K ≠ K' := fun h => htK (A38.map_conj_eq_iff.mp h.symm)
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_mem_cComp hK hK'
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := center_quot_of_cfg c
  have hcomm : ⁅K, K'⁆ ≤ pCoreOf 2 K :=
    CFSG.Quasithin.EmptyFaithfulMultiple.L15420.commutator_le_pCoreOf_of_ne hK hK' hKK' c.nf.Kq hZ
  exact le_kerAct_of_comm_le_pCoreOf hK'N hcomm

theorem A2Cfg.le_kerAct_conj (c : A2Cfg G T M L D H K q) {t : G} (ht : t ∈ T)
    (htK : t ∉ Subgroup.normalizer (K : Set G)) :
    K ≤ kerAct (K.map (MulAut.conj t).toMonoidHom) := by
  have htH₀ : t ∈ H ⊔ D := Subgroup.mem_sup_left (c.nf.inH.1 ht)
  have hK : K ∈ cComp (H ⊔ D) := c.nf.K_comp
  set K' := K.map (MulAut.conj t).toMonoidHom with hK'def
  have hK' : K' ∈ cComp (H ⊔ D) := CFSG.Quasithin.map_conj_mem_cComp hK htH₀
  have hKK' : K ≠ K' := fun h => htK (A38.map_conj_eq_iff.mp h.symm)
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_mem_cComp hK hK'
  have hKN' : K ≤ Subgroup.normalizer (K' : Set G) := le_normalizer_of_mem_cComp hK' hK
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := center_quot_of_cfg c
  have hcomm : ⁅K, K'⁆ ≤ pCoreOf 2 K :=
    CFSG.Quasithin.EmptyFaithfulMultiple.L15420.commutator_le_pCoreOf_of_ne hK hK' hKK' c.nf.Kq hZ
  have hcomm' : ⁅K, K'⁆ ≤ pCoreOf 2 K' := comm_le_pCoreOf_of_normalizes hK'N hKN' hcomm
  exact le_kerAct_of_comm_le_pCoreOf (K := K') (K' := K) hKN'
    (by rw [Subgroup.commutator_comm]; exact hcomm')

theorem A2Cfg.mem_TC_iff (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (c : A2Cfg G T M L D H K q) {t : G} (ht : t ∈ T) (htK : t ∉ Subgroup.normalizer (K : Set G))
    (x : G) :
    x ∈ a2TC K T ↔
      x ∈ pCoreOf 2 H ∧ x ∈ kerAct K ∧ x ∈ kerAct (K.map (MulAut.conj t).toMonoidHom) := by
  constructor
  · intro hx
    have hA := c.TC_acts_trivially h37 h38 ht htK hx
    exact ⟨c.TC_le_R hx, (Subgroup.mem_inf.mp hA).1, (Subgroup.mem_inf.mp hA).2⟩
  · rintro ⟨hxR, hxK, hxK'⟩
    have hG2 : x ∈ a2G2 K T := c.H_le_G2 (CFSG.LieType.BorelTits.pCoreOf_le 2 H hxR)
    have hmem : x ∈ a2G2 K T ⊓ (kerAct K ⊓ kerAct (K.map (MulAut.conj t).toMonoidHom)) :=
      Subgroup.mem_inf.mpr ⟨hG2, Subgroup.mem_inf.mpr ⟨hxK, hxK'⟩⟩
    rw [c.TC_eq h37 h38 ht htK]
    exact hmem

end CentreAndConj

section Leaves

variable {G : Type} [Group G] [Finite G]

theorem leaf_SLRTC_of (h5 : Stmt3_3_5)
    (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (h128 : Lemma128Two) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) :
    ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ),
      A2Cfg G T M L D H K q → mIdx (a2R H) (a2TC K T) ≤ 2 := by
  intro G _ _ T M L D H K q c
  obtain ⟨t₀, ht₀T, ht₀N, -, -, -⟩ := c.kstruct h37 h38
  obtain ⟨x, hxY, hxK, hx3⟩ := c.exists_x h37 h38
  obtain ⟨a, haK, -, -, -, hdich⟩ :=
    c.exists_involution h5 h7 h9 h128 h37 h38 h39 hxY hxK hx3
  have hRp : IsPGroup 2 ↥(pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hRN : pCoreOf 2 H ≤ Subgroup.normalizer (K : Set G) := c.R_le_normalizer_K h37 h38
  have hdich' : ∀ r ∈ pCoreOf 2 H, r ∈ kerAct K ∨ a⁻¹ * r ∈ kerAct K := by
    intro r hr
    rcases hdich r hr with h1 | h2
    · exact Or.inl (mem_kerAct.mpr ⟨hRN hr, h1⟩)
    · exact Or.inr (inv_mul_mem_kerAct_of_second haK (hRN hr) h2)
  have h1 : (pCoreOf 2 H ⊓ kerAct K).relIndex (pCoreOf 2 H) ≤ 2 :=
    relIndex_le_two_of_dichotomy haK hdich'
  have hRc : (pCoreOf 2 H).map (MulAut.conj t₀).toMonoidHom = pCoreOf 2 H :=
    A38.map_conj_eq_iff.mpr (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (c.sylow_H.1 ht₀T))
  have hinj : Function.Injective (MulAut.conj t₀).toMonoidHom := (MulAut.conj t₀).injective
  have hR2 : pCoreOf 2 H ⊓ kerAct (K.map (MulAut.conj t₀).toMonoidHom) =
      (pCoreOf 2 H ⊓ kerAct K).map (MulAut.conj t₀).toMonoidHom := by
    rw [kerAct_map_conj, Subgroup.map_inf_eq _ _ _ hinj, hRc]
  have h2 : (pCoreOf 2 H ⊓ kerAct (K.map (MulAut.conj t₀).toMonoidHom)).relIndex (pCoreOf 2 H) ≤ 2 := by
    have hmap := Subgroup.relIndex_map_map_of_injective (pCoreOf 2 H ⊓ kerAct K) (pCoreOf 2 H) hinj
    rw [hRc] at hmap
    rw [hR2, hmap]
    exact h1
  have hTC : a2TC K T = (pCoreOf 2 H ⊓ kerAct K) ⊓
      (pCoreOf 2 H ⊓ kerAct (K.map (MulAut.conj t₀).toMonoidHom)) := by
    apply Subgroup.ext
    intro x
    rw [c.mem_TC_iff h37 h38 ht₀T ht₀N x]
    simp only [Subgroup.mem_inf]
    tauto
  have hle4 : (a2TC K T).relIndex (a2R H) ≤ 4 := by
    rw [hTC]
    exact le_trans Subgroup.relIndex_inf_le (le_trans (Nat.mul_le_mul h1 h2) (by norm_num))
  have hpow : (a2TC K T).relIndex (a2R H) = 2 ^ mIdx (a2R H) (a2TC K T) :=
    HypF98.relIndex_eq_two_pow_mIdx hRp
  rw [hpow] at hle4
  by_contra hc
  have hc3 : 3 ≤ mIdx (a2R H) (a2TC K T) := by omega
  have h8 := Nat.pow_le_pow_right (by norm_num : (0 : ℕ) < 2) hc3
  exact absurd (h8.trans hle4) (by norm_num)

theorem leaf_C3s_of (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) :
    ∀ (G : Type) [Group G] [Finite G] (T M L D H K : Subgroup G) (q : ℕ),
      A2Cfg G T M L D H K q → ¬ a2V L T ≤ a2TC K T →
        ∀ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) →
          ∃ v ∈ a2V L T, v ∉ a2TC K T ⊔ K ∧ v ∉ a2TC K T ⊔ conjSub t K := by
  intro G _ _ T M L D H K q c hV t ht htK
  obtain ⟨t₀, -, -, -, -, hs⟩ := c.kstruct h37 h38
  have hKtt : (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = K := by
    rw [map_conj_map_conj]
    rcases hs (t * t) (T.mul_mem ht ht) with h1 | h1
    · exact h1
    · exfalso
      have hKt : K.map (MulAut.conj t).toMonoidHom = K.map (MulAut.conj t₀).toMonoidHom := by
        rcases hs t ht with h2 | h2
        · exact absurd (A38.map_conj_eq_iff.mp h2) htK
        · exact h2
      exact htK (A38.map_conj_eq_iff.mp (map_conj_eq_of_map_conj_eq K (hKt.trans h1.symm)))
  have hK'to : ∀ y : G, y ∈ kerAct (K.map (MulAut.conj t).toMonoidHom) ↔
      t⁻¹ * y * t ∈ kerAct K :=
    fun y => mem_kerAct_map_conj_iff t y K
  have hKto : ∀ y : G, y ∈ kerAct K ↔
      t⁻¹ * y * t ∈ kerAct (K.map (MulAut.conj t).toMonoidHom) := by
    intro y
    have h := mem_kerAct_map_conj_iff t y (K.map (MulAut.conj t).toMonoidHom)
    rw [hKtt] at h
    exact h
  have hVN : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) :=
    (Hyp331.vPlus_reduced c.nf.hyp.toSetup331).2.2.2.1
  have htV : t ∈ Subgroup.normalizer (vPlus L T : Set G) := hVN (Subgroup.mem_sup_right ht)
  have hVG2 : a2V L T ≤ a2G2 K T :=
    c.V_le_R.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans c.H_le_G2)
  obtain ⟨v₀, hv₀V, hv₀⟩ : ∃ v₀ ∈ a2V L T,
      ¬ (v₀ ∈ kerAct K ∧ v₀ ∈ kerAct (K.map (MulAut.conj t).toMonoidHom)) := by
    by_contra hcon
    push Not at hcon
    apply hV
    intro v hv
    rw [c.TC_eq h37 h38 ht htK]
    exact Subgroup.mem_inf.mpr ⟨hVG2 hv, Subgroup.mem_inf.mpr (hcon v hv)⟩
  have hv₁V : t * v₀ * t⁻¹ ∈ a2V L T := (Subgroup.mem_normalizer_iff.mp htV v₀).mp hv₀V
  have hconj : ∀ v : G, t⁻¹ * (t * v * t⁻¹) * t = v := fun v => by group
  have h1 : t * v₀ * t⁻¹ ∈ kerAct K ↔ v₀ ∈ kerAct (K.map (MulAut.conj t).toMonoidHom) := by
    rw [hKto, hconj]
  have h2 : t * v₀ * t⁻¹ ∈ kerAct (K.map (MulAut.conj t).toMonoidHom) ↔ v₀ ∈ kerAct K := by
    rw [hK'to, hconj]
  obtain ⟨v, hvV, hvK, hvK'⟩ := exists_mem_outside_pair hv₀V hv₁V hv₀ h1 h2
  refine ⟨v, hvV, ?_, ?_⟩
  · intro hmem
    apply hvK'
    have hle : a2TC K T ⊔ K ≤ kerAct (K.map (MulAut.conj t).toMonoidHom) :=
      sup_le ((c.TC_acts_trivially h37 h38 ht htK).trans inf_le_right) (c.le_kerAct_conj ht htK)
    exact hle hmem
  · intro hmem
    apply hvK
    have hle : a2TC K T ⊔ conjSub t K ≤ kerAct K :=
      sup_le ((c.TC_acts_trivially h37 h38 ht htK).trans inf_le_left) (c.conj_le_kerAct ht htK)
    exact hle hmem

end Leaves

end CFSG.Quasithin.H13.NFa2
