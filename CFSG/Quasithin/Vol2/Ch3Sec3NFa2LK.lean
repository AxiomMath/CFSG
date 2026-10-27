module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFa2KRC

public section

namespace CFSG.Quasithin.H13.NFa2

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

section Generic

variable {G : Type} [Group G]

theorem pCoreOf_le_kerAct (K : Subgroup G) : pCoreOf 2 K ≤ kerAct K := by
  intro o ho
  refine mem_kerAct.mpr ⟨Subgroup.le_normalizer (CFSG.LieType.BorelTits.pCoreOf_le 2 K ho),
    fun k hk => ?_⟩
  have e : o * k * o⁻¹ * k⁻¹ = o * (k * o⁻¹ * k⁻¹) := by group
  rw [e]
  exact Subgroup.mul_mem _ ho
    (conj_mem_pCoreOf_of_mem_normalizer (Subgroup.le_normalizer hk) ((pCoreOf 2 K).inv_mem ho))

theorem Ykill [Finite G] {K R : Subgroup G} {a r₁ y : G}
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) (ha : a ∈ K)
    (hdich : ∀ r ∈ R, r ∈ kerAct K ∨ a⁻¹ * r ∈ kerAct K)
    (hr₁ : r₁ ∈ R) (hr₁K : r₁ ∉ kerAct K)
    (hyN : y ∈ Subgroup.normalizer (K : Set G)) (hyR : y ∈ Subgroup.normalizer (R : Set G)) :
    y * a * y⁻¹ * a⁻¹ ∈ pCoreOf 2 K ∧ ∀ r ∈ R, y * r * y⁻¹ * r⁻¹ ∈ kerAct K := by
  have haN : a ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer ha
  have h1 : a⁻¹ * r₁ ∈ kerAct K := (hdich r₁ hr₁).resolve_left hr₁K
  have hyr₁ : y * r₁ * y⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hyR r₁).mp hr₁
  have h2 : a⁻¹ * (y * r₁ * y⁻¹) ∈ kerAct K := by
    refine (hdich _ hyr₁).resolve_left fun hk => hr₁K ?_
    have := conj_mem_kerAct_of_mem_normalizer (Subgroup.inv_mem _ hyN) hk
    simpa [mul_assoc] using this
  have h3 : y * (a⁻¹ * r₁) * y⁻¹ ∈ kerAct K := conj_mem_kerAct_of_mem_normalizer hyN h1
  have h4 : a⁻¹ * y * a * y⁻¹ ∈ kerAct K := by
    have := (kerAct K).mul_mem h2 ((kerAct K).inv_mem h3)
    have e : a⁻¹ * (y * r₁ * y⁻¹) * (y * (a⁻¹ * r₁) * y⁻¹)⁻¹ = a⁻¹ * y * a * y⁻¹ := by group
    rwa [e] at this
  have h5 : a⁻¹ * y * a * y⁻¹ ∈ K := by
    have hya : y * a * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hyN a).mp ha
    have e : a⁻¹ * y * a * y⁻¹ = a⁻¹ * (y * a * y⁻¹) := by group
    rw [e]
    exact K.mul_mem (K.inv_mem ha) hya
  have h6 : a⁻¹ * y * a * y⁻¹ ∈ pCoreOf 2 K :=
    mem_pCoreOf_of_central hZ h5 (fun x hx => (mem_kerAct.mp h4).2 x hx)
  have h7 : y * a * y⁻¹ * a⁻¹ ∈ pCoreOf 2 K := by
    have := conj_mem_pCoreOf_of_mem_normalizer haN h6
    have e : a * (a⁻¹ * y * a * y⁻¹) * a⁻¹ = y * a * y⁻¹ * a⁻¹ := by group
    rwa [e] at this
  refine ⟨h7, fun r hr => ?_⟩
  rcases hdich r hr with hrk | hrk
  · have := conj_mem_kerAct_of_mem_normalizer hyN hrk
    exact (kerAct K).mul_mem this ((kerAct K).inv_mem hrk)
  ·
    set r₂ := a⁻¹ * r with hr₂
    have hy2 : y * r₂ * y⁻¹ * r₂⁻¹ ∈ kerAct K := by
      have := conj_mem_kerAct_of_mem_normalizer hyN hrk
      exact (kerAct K).mul_mem this ((kerAct K).inv_mem hrk)
    have hy3 : a * (y * r₂ * y⁻¹ * r₂⁻¹) * a⁻¹ ∈ kerAct K :=
      conj_mem_kerAct_of_mem_normalizer haN hy2
    have e : y * r * y⁻¹ * r⁻¹ =
        (y * a * y⁻¹ * a⁻¹) * (a * (y * r₂ * y⁻¹ * r₂⁻¹) * a⁻¹) := by
      rw [hr₂]; group
    rw [e]
    exact (kerAct K).mul_mem (pCoreOf_le_kerAct K h7) hy3

end Generic

section Cfg

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

structure AData (c : A2Cfg G T M L D H K q) (t a : G) : Prop where
  aK : a ∈ K
  a_not : a ∉ pCoreOf 2 K
  a_sq : a ^ 2 ∈ pCoreOf 2 K
  dich : ∀ r ∈ pCoreOf 2 H, r ∈ kerAct K ∨ a⁻¹ * r ∈ kerAct K
  dich' : ∀ r ∈ pCoreOf 2 H, r ∈ kerAct (K.map (MulAut.conj t).toMonoidHom) ∨
    (t * a * t⁻¹)⁻¹ * r ∈ kerAct (K.map (MulAut.conj t).toMonoidHom)
  nontriv : ∃ r ∈ pCoreOf 2 H, r ∉ kerAct K

theorem A2Cfg.conj_inv_mem_R (c : A2Cfg G T M L D H K q) {t : G} (ht : t ∈ T) {r : G}
    (hr : r ∈ pCoreOf 2 H) : t⁻¹ * r * t ∈ pCoreOf 2 H := by
  have hRc : (pCoreOf 2 H).map (MulAut.conj t).toMonoidHom = pCoreOf 2 H :=
    A38.map_conj_eq_iff.mpr (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (c.sylow_H.1 ht))
  rw [← hRc] at hr
  exact (mem_map_conj_iff' _ t r).mp hr

theorem A2Cfg.conj_mem_R (c : A2Cfg G T M L D H K q) {t : G} (ht : t ∈ T) {r : G}
    (hr : r ∈ pCoreOf 2 H) : t * r * t⁻¹ ∈ pCoreOf 2 H := by
  have := c.conj_inv_mem_R (T.inv_mem ht) hr
  simpa using this

theorem A2Cfg.exists_AData_of_x
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (c : A2Cfg G T M L D H K q) {t : G} (ht : t ∈ T) {x : G} (hxY : x ∈ oTwoUpper H)
    (hxK : x ∈ K) (hx3 : orderOf x = 3) :
    ∃ a, AData c t a ∧ ⁅x, a⁆ ∈ pCoreOf 2 K := by
  obtain ⟨a, haK, haO, ha2, hxa, hdich⟩ :=
    c.exists_involution h5 h7 h9 h128 h37 h38 h39 hxY hxK hx3
  have hRN : pCoreOf 2 H ≤ Subgroup.normalizer (K : Set G) := c.R_le_normalizer_K h37 h38
  have dich : ∀ r ∈ pCoreOf 2 H, r ∈ kerAct K ∨ a⁻¹ * r ∈ kerAct K := by
    intro r hr
    rcases hdich r hr with h1 | h2
    · exact Or.inl (mem_kerAct.mpr ⟨hRN hr, h1⟩)
    · exact Or.inr (inv_mul_mem_kerAct_of_second haK (hRN hr) h2)
  refine ⟨a, ⟨haK, haO, ha2, dich, fun r hr => ?_, ?_⟩, hxa⟩
  ·
    have hr' := c.conj_inv_mem_R ht hr
    rcases dich _ hr' with h1 | h2
    · exact Or.inl ((mem_kerAct_map_conj_iff t r K).mpr h1)
    · refine Or.inr ((mem_kerAct_map_conj_iff t _ K).mpr ?_)
      have e : t⁻¹ * ((t * a * t⁻¹)⁻¹ * r) * t = a⁻¹ * (t⁻¹ * r * t) := by group
      rw [e]
      exact h2
  ·
    by_contra hcon
    push Not at hcon
    obtain ⟨t₀, ht₀T, -, -, hKK, -⟩ := c.kstruct h37 h38
    have hact : ∀ r ∈ pCoreOf 2 H, ∀ k ∈ K, r * k * r⁻¹ * k⁻¹ ∈ pCoreOf 2 K :=
      fun r hr k hk => (mem_kerAct.mp (hcon r hr)).2 k hk
    have hKR : K ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      KAct.le_normalizer_of_act_trivial (c.pCoreOf_K_le_R h37 h38) hact
    have hKM : K ≤ M := fun k hk => c.normalizer_le_M h5 h7 h9 (hKR hk)
    have ht₀M : t₀ ∈ M := c.nf.hyp.TM ht₀T
    have hK'M : K.map (MulAut.conj t₀).toMonoidHom ≤ M := by
      rintro _ ⟨k, hk, rfl⟩
      exact M.mul_mem (M.mul_mem ht₀M (hKM hk)) (M.inv_mem ht₀M)
    apply c.not_K0_le_M h128 h37 h38 h39
    rw [hKK]
    exact sup_le hKM hK'M

theorem A2Cfg.exists_AData
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (c : A2Cfg G T M L D H K q) {t : G} (ht : t ∈ T) :
    ∃ a, AData c t a := by
  obtain ⟨x, hxY, hxK, hx3⟩ := c.exists_x h37 h38
  obtain ⟨a, hd, -⟩ := c.exists_AData_of_x h5 h7 h9 h128 h37 h38 h39 ht hxY hxK hx3
  exact ⟨a, hd⟩

end Cfg

section Cases

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem A2Cfg.mem_TC_iff' (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (c : A2Cfg G T M L D H K q) {t : G} (ht : t ∈ T) (htK : t ∉ Subgroup.normalizer (K : Set G))
    {x : G} :
    x ∈ a2TC K T ↔ x ∈ a2G2 K T ∧ x ∈ kerAct K ∧
      x ∈ kerAct (K.map (MulAut.conj t).toMonoidHom) := by
  rw [c.TC_eq h37 h38 ht htK, Subgroup.mem_inf, Subgroup.mem_inf]

theorem AData.R_cases (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    {c : A2Cfg G T M L D H K q} {t a : G} (ht : t ∈ T)
    (htK : t ∉ Subgroup.normalizer (K : Set G)) (hd : AData c t a) {r : G}
    (hr : r ∈ pCoreOf 2 H) :
    r ∈ a2TC K T ∨ a⁻¹ * r ∈ a2TC K T ∨ (t * a * t⁻¹)⁻¹ * r ∈ a2TC K T ∨
      (t * a * t⁻¹)⁻¹ * (a⁻¹ * r) ∈ a2TC K T := by
  set K' := K.map (MulAut.conj t).toMonoidHom with hK'
  set a' := t * a * t⁻¹ with ha'
  have haK' : a' ∈ K' := ⟨a, hd.aK, by simp [ha', MulAut.conj_apply]⟩
  have hG2 : ∀ x ∈ K, x ∈ a2G2 K T := fun x hx => (le_conjClosure K T).trans le_sup_left hx
  have hTG : t ∈ a2G2 K T := Subgroup.mem_sup_right ht
  have ha'G : a' ∈ a2G2 K T :=
    (a2G2 K T).mul_mem ((a2G2 K T).mul_mem hTG (hG2 a hd.aK)) ((a2G2 K T).inv_mem hTG)
  have haG : a ∈ a2G2 K T := hG2 a hd.aK
  have hrG : r ∈ a2G2 K T := c.H_le_G2 (CFSG.LieType.BorelTits.pCoreOf_le 2 H hr)
  have hK'ker : K' ≤ kerAct K := c.conj_le_kerAct ht htK
  have hKker' : K ≤ kerAct K' := c.le_kerAct_conj ht htK
  have hK'N : K' ≤ Subgroup.normalizer (K' : Set G) := fun x hx => Subgroup.le_normalizer hx
  have mk : ∀ x, x ∈ a2G2 K T → x ∈ kerAct K → x ∈ kerAct K' → x ∈ a2TC K T :=
    fun x h1 h2 h3 => (c.mem_TC_iff' h37 h38 ht htK).mpr ⟨h1, h2, h3⟩
  have haker' : a⁻¹ ∈ kerAct K' := (kerAct K').inv_mem (hKker' hd.aK)
  have ha'ker : a'⁻¹ ∈ kerAct K := (kerAct K).inv_mem (hK'ker haK')
  rcases hd.dich r hr with h1 | h1 <;> rcases hd.dich' r hr with h2 | h2
  · exact Or.inl (mk r hrG h1 h2)
  ·
    refine Or.inr (Or.inr (Or.inl (mk _ ((a2G2 K T).mul_mem ((a2G2 K T).inv_mem ha'G) hrG)
      ((kerAct K).mul_mem ha'ker h1) h2)))
  ·
    refine Or.inr (Or.inl (mk _ ((a2G2 K T).mul_mem ((a2G2 K T).inv_mem haG) hrG) h1
      ((kerAct K').mul_mem haker' h2)))
  ·
    refine Or.inr (Or.inr (Or.inr (mk _ ?_ ?_ ?_)))
    · exact (a2G2 K T).mul_mem ((a2G2 K T).inv_mem ha'G)
        ((a2G2 K T).mul_mem ((a2G2 K T).inv_mem haG) hrG)
    · exact (kerAct K).mul_mem ha'ker h1
    · have h3 := conj_mem_kerAct_of_mem_normalizer
        (Subgroup.inv_mem _ (Subgroup.le_normalizer haK')) haker'
      have h4 := (kerAct K').mul_mem h3 h2
      have e : a'⁻¹ * a⁻¹ * (a'⁻¹)⁻¹ * (a'⁻¹ * r) = a'⁻¹ * (a⁻¹ * r) := by group
      rwa [e] at h4

theorem A2Cfg.R_comm_le_TC
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (c : A2Cfg G T M L D H K q) {y : G} (hyK0 : y ∈ conjClosure K T)
    (hyR : y ∈ Subgroup.normalizer (pCoreOf 2 H : Set G)) :
    ∀ r ∈ pCoreOf 2 H, y * r * y⁻¹ * r⁻¹ ∈ a2TC K T := by
  have hex : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push Not at hcon
    exact c.nf.TK hcon
  obtain ⟨t, ht, htK⟩ := hex
  obtain ⟨a, hd⟩ := c.exists_AData h5 h7 h9 h128 h37 h38 h39 ht
  set K' := K.map (MulAut.conj t).toMonoidHom with hK'
  have hK : K ∈ cComp (H ⊔ D) := c.nf.K_comp
  have htH₀ : t ∈ H ⊔ D := Subgroup.mem_sup_left (c.nf.inH.1 ht)
  have hK'c : K' ∈ cComp (H ⊔ D) := CFSG.Quasithin.map_conj_mem_cComp hK htH₀
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_mem_cComp hK hK'c
  have hKN' : K ≤ Subgroup.normalizer (K' : Set G) := le_normalizer_of_mem_cComp hK'c hK
  obtain ⟨t₀, -, -, -, hKK₀, hs⟩ := c.kstruct h37 h38
  have hKt : K' = K.map (MulAut.conj t₀).toMonoidHom := by
    rcases hs t ht with h | h
    · exact absurd (A38.map_conj_eq_iff.mp h) htK
    · exact h
  have hK0 : conjClosure K T = K ⊔ K' := hKK₀.trans (by rw [← hKt])
  have hyN : y ∈ Subgroup.normalizer (K : Set G) := by
    have : conjClosure K T ≤ Subgroup.normalizer (K : Set G) := by
      rw [hK0]; exact sup_le Subgroup.le_normalizer hK'N
    exact this hyK0
  have hyN' : y ∈ Subgroup.normalizer (K' : Set G) := by
    have : conjClosure K T ≤ Subgroup.normalizer (K' : Set G) := by
      rw [hK0]; exact sup_le hKN' Subgroup.le_normalizer
    exact this hyK0
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := center_quot_of_cfg c
  have hZ' : Subgroup.center (↥K' ⧸ CFSG.pCore 2 ↥K') = ⊥ := center_quot_map_conj K t hZ
  obtain ⟨r₁, hr₁R, hr₁K⟩ := hd.nontriv
  intro r hr
  have hyrG : y * r * y⁻¹ * r⁻¹ ∈ a2G2 K T := by
    have hyr : y * r * y⁻¹ ∈ pCoreOf 2 H := (Subgroup.mem_normalizer_iff.mp hyR r).mp hr
    exact c.H_le_G2 (CFSG.LieType.BorelTits.pCoreOf_le 2 H
      ((pCoreOf 2 H).mul_mem hyr ((pCoreOf 2 H).inv_mem hr)))
  refine (c.mem_TC_iff' h37 h38 ht htK).mpr ⟨hyrG, ?_, ?_⟩
  · exact (Ykill hZ hd.aK hd.dich hr₁R hr₁K hyN hyR).2 r hr
  ·
    have hr₁' : t * r₁ * t⁻¹ ∈ pCoreOf 2 H := c.conj_mem_R ht hr₁R
    have hr₁'K : t * r₁ * t⁻¹ ∉ kerAct K' := by
      intro h
      apply hr₁K
      have := (mem_kerAct_map_conj_iff t _ K).mp h
      simpa [mul_assoc] using this
    have haK' : t * a * t⁻¹ ∈ K' := ⟨a, hd.aK, by simp [MulAut.conj_apply]⟩
    exact (Ykill hZ' haK' hd.dich' hr₁' hr₁'K hyN' hyR).2 r hr

theorem A2Cfg.UH_le_TC
    (h5 : Stmt3_3_5) (h7 : Stmt3_3_7) (h9 : Stmt3_3_9) (h128 : Lemma128Two)
    (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (c : A2Cfg G T M L D H K q) : a2UH L T H K ≤ a2TC K T := by
  have hVY : ⁅vPlus L T, oTwoUpper H⁆ ≤ a2TC K T := by
    refine Subgroup.commutator_le.mpr fun v hv y hy => ?_
    have hyK0 : y ∈ conjClosure K T := c.nf.YK hy
    have hyH : y ∈ H := CFSG.Quasithin.oTwoUpper_le H hy
    have hyR : y ∈ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H hyH
    have hvR : v ∈ pCoreOf 2 H := c.V_le_R hv
    have h1 := c.R_comm_le_TC h5 h7 h9 h128 h37 h38 h39 hyK0 hyR v hvR
    have := (a2TC K T).inv_mem h1
    have e : (y * v * y⁻¹ * v⁻¹)⁻¹ = v * y * v⁻¹ * y⁻¹ := by group
    rw [e] at this
    exact this
  refine conjClosure_le fun g hg x hx => ?_
  have hgN : g ∈ Subgroup.normalizer (a2TC K T : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (a2G2 K T) hg
  exact (Subgroup.mem_normalizer_iff.mp hgN x).mp (hVY hx)

end Cases

section TypeTwo

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem AData.mem_of_not_sup (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) {c : A2Cfg G T M L D H K q} {t a : G} (ht : t ∈ T)
    (htK : t ∉ Subgroup.normalizer (K : Set G)) (hd : AData c t a) {r : G}
    (hr : r ∈ pCoreOf 2 H) (h1 : r ∉ a2TC K T ⊔ K)
    (h2 : r ∉ a2TC K T ⊔ K.map (MulAut.conj t).toMonoidHom) :
    (t * a * t⁻¹)⁻¹ * (a⁻¹ * r) ∈ a2TC K T := by
  set K' := K.map (MulAut.conj t).toMonoidHom with hK'
  have haK' : t * a * t⁻¹ ∈ K' := ⟨a, hd.aK, by simp [MulAut.conj_apply]⟩
  rcases hd.R_cases h37 h38 ht htK hr with h | h | h | h
  · exact absurd (Subgroup.mem_sup_left h) h1
  · refine absurd ?_ h1
    have e : r = a * (a⁻¹ * r) := by group
    rw [e]
    exact (a2TC K T ⊔ K).mul_mem (Subgroup.mem_sup_right hd.aK) (Subgroup.mem_sup_left h)
  · refine absurd ?_ h2
    have e : r = (t * a * t⁻¹) * ((t * a * t⁻¹)⁻¹ * r) := by group
    rw [e]
    exact (a2TC K T ⊔ K').mul_mem (Subgroup.mem_sup_right haK') (Subgroup.mem_sup_left h)
  · exact h

theorem AData.not_mem_sup_of (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) {c : A2Cfg G T M L D H K q} {t a : G} (ht : t ∈ T)
    (htK : t ∉ Subgroup.normalizer (K : Set G)) (hd : AData c t a) {r : G}
    (hu : (t * a * t⁻¹)⁻¹ * (a⁻¹ * r) ∈ a2TC K T) :
    r ∉ a2TC K T ⊔ K ∧ r ∉ a2TC K T ⊔ K.map (MulAut.conj t).toMonoidHom := by
  set K' := K.map (MulAut.conj t).toMonoidHom with hK'
  set a' := t * a * t⁻¹ with ha'
  have haK' : a' ∈ K' := ⟨a, hd.aK, by simp [ha', MulAut.conj_apply]⟩
  have hK'ker : K' ≤ kerAct K := c.conj_le_kerAct ht htK
  have hKker' : K ≤ kerAct K' := c.le_kerAct_conj ht htK
  have hTCK : a2TC K T ≤ kerAct K := (c.TC_acts_trivially h37 h38 ht htK).trans inf_le_left
  have hTCK' : a2TC K T ≤ kerAct K' := (c.TC_acts_trivially h37 h38 ht htK).trans inf_le_right
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := center_quot_of_cfg c
  have hZ' : Subgroup.center (↥K' ⧸ CFSG.pCore 2 ↥K') = ⊥ := center_quot_map_conj K t hZ
  constructor
  · intro hmem
    have hc' : r ∈ kerAct K' := (sup_le hTCK' hKker') hmem
    have h1 : a⁻¹ * r ∈ kerAct K' := (kerAct K').mul_mem ((kerAct K').inv_mem (hKker' hd.aK)) hc'
    have h2 : a'⁻¹ ∈ kerAct K' :=
      have := (kerAct K').mul_mem (hTCK' hu) ((kerAct K').inv_mem h1)
      by
        have e : (a'⁻¹ * (a⁻¹ * r)) * (a⁻¹ * r)⁻¹ = a'⁻¹ := by group
        rwa [e] at this
    have h3 : a' ∈ kerAct K' := by simpa using (kerAct K').inv_mem h2
    have h4 : a' ∈ pCoreOf 2 K' :=
      mem_pCoreOf_of_central hZ' haK' (fun x hx => (mem_kerAct.mp h3).2 x hx)
    apply hd.a_not
    rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 (MulAut.conj t) K] at h4
    have := (mem_map_conj_iff' _ t a').mp h4
    simpa [ha', mul_assoc] using this
  · intro hmem
    have hc : r ∈ kerAct K := (sup_le hTCK hK'ker) hmem
    have h1 : a⁻¹ * r ∈ kerAct K := by
      have := (kerAct K).mul_mem (hK'ker haK') (hTCK hu)
      have e : a' * (a'⁻¹ * (a⁻¹ * r)) = a⁻¹ * r := by group
      rwa [e] at this
    have h2 : a ∈ kerAct K := by
      have := (kerAct K).mul_mem h1 ((kerAct K).inv_mem hc)
      have e : a⁻¹ * r * r⁻¹ = a⁻¹ := by group
      rw [e] at this
      simpa using (kerAct K).inv_mem this
    exact hd.a_not (mem_pCoreOf_of_central hZ hd.aK (fun x hx => (mem_kerAct.mp h2).2 x hx))

theorem AData.exists_type_two (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) {c : A2Cfg G T M L D H K q} {t a : G} (ht : t ∈ T)
    (htK : t ∉ Subgroup.normalizer (K : Set G)) (hd : AData c t a) :
    ∃ c₀ ∈ pCoreOf 2 H, c₀ ∉ a2TC K T ⊔ K ∧
      c₀ ∉ a2TC K T ⊔ K.map (MulAut.conj t).toMonoidHom := by
  set K' := K.map (MulAut.conj t).toMonoidHom with hK'
  set a' := t * a * t⁻¹ with ha'
  have haK' : a' ∈ K' := ⟨a, hd.aK, by simp [ha', MulAut.conj_apply]⟩
  have hK'ker : K' ≤ kerAct K := c.conj_le_kerAct ht htK
  have hTCK : a2TC K T ≤ kerAct K := (c.TC_acts_trivially h37 h38 ht htK).trans inf_le_left
  have hG2 : ∀ x ∈ K, x ∈ a2G2 K T := fun x hx => (le_conjClosure K T).trans le_sup_left hx
  have hTG : t ∈ a2G2 K T := Subgroup.mem_sup_right ht
  have ha'G : a' ∈ a2G2 K T :=
    (a2G2 K T).mul_mem ((a2G2 K T).mul_mem hTG (hG2 a hd.aK)) ((a2G2 K T).inv_mem hTG)
  have hTCn : a2G2 K T ≤ Subgroup.normalizer (a2TC K T : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (a2G2 K T)
  obtain ⟨r₁, hr₁R, hr₁K⟩ := hd.nontriv
  have key : ∀ r ∈ pCoreOf 2 H, (t * a * t⁻¹)⁻¹ * (a⁻¹ * r) ∈ a2TC K T →
      r ∉ a2TC K T ⊔ K ∧ r ∉ a2TC K T ⊔ K' := fun r _ hu =>
    hd.not_mem_sup_of h37 h38 ht htK hu
  rcases hd.R_cases h37 h38 ht htK hr₁R with h | h | h | h
  · exact absurd (hTCK h) hr₁K
  ·
    have hr₂ : t * r₁ * t⁻¹ ∈ pCoreOf 2 H := c.conj_mem_R ht hr₁R
    refine ⟨r₁ * (t * r₁ * t⁻¹), (pCoreOf 2 H).mul_mem hr₁R hr₂, key _
      ((pCoreOf 2 H).mul_mem hr₁R hr₂) ?_⟩
    have h1 : a'⁻¹ * (a⁻¹ * r₁) * (a'⁻¹)⁻¹ ∈ a2TC K T :=
      (Subgroup.mem_normalizer_iff.mp (hTCn ((a2G2 K T).inv_mem ha'G)) _).mp h
    have h2 : t * (a⁻¹ * r₁) * t⁻¹ ∈ a2TC K T :=
      (Subgroup.mem_normalizer_iff.mp (hTCn hTG) _).mp h
    have h3 := (a2TC K T).mul_mem h1 h2
    have e : a'⁻¹ * (a⁻¹ * r₁) * (a'⁻¹)⁻¹ * (t * (a⁻¹ * r₁) * t⁻¹) =
        a'⁻¹ * (a⁻¹ * (r₁ * (t * r₁ * t⁻¹))) := by
      rw [ha']; group
    rwa [e] at h3
  ·
    exfalso
    apply hr₁K
    have := (kerAct K).mul_mem (hK'ker haK') (hTCK h)
    have e : a' * (a'⁻¹ * r₁) = r₁ := by group
    rwa [e] at this
  · exact ⟨r₁, hr₁R, key r₁ hr₁R h⟩

end TypeTwo

section KCtx

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G} {q : ℕ}

theorem A2Cfg.pCoreOf_K_le_TC (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat)
    (c : A2Cfg G T M L D H K q) : pCoreOf 2 K ≤ a2TC K T := by
  obtain ⟨t₀, -, -, hK', hKK, -⟩ := c.kstruct h37 h38
  have hK'N : K.map (MulAut.conj t₀).toMonoidHom ≤ Subgroup.normalizer (K : Set G) :=
    le_normalizer_of_mem_cComp c.nf.K_comp hK'
  have h1 : pCoreOf 2 K ≤ pCoreOf 2 (conjClosure K T) := by
    rw [hKK]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans le_sup_left) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
    exact sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
      (hK'N.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
  exact h1.trans c.N0_le_TC

structure KCtx (c : A2Cfg G T M L D H K q) (t : G) : Prop where
  tT : t ∈ T
  tK : t ∉ Subgroup.normalizer (K : Set G)
  K0 : conjClosure K T = K ⊔ K.map (MulAut.conj t).toMonoidHom
  K'N : K.map (MulAut.conj t).toMonoidHom ≤ Subgroup.normalizer (K : Set G)
  KN' : K ≤ Subgroup.normalizer ((K.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G)
  comm : ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ ≤ pCoreOf 2 K
  perm : ∀ s ∈ T,
    (K.map (MulAut.conj s).toMonoidHom = K ∧
      (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom =
        K.map (MulAut.conj t).toMonoidHom) ∨
    (K.map (MulAut.conj s).toMonoidHom = K.map (MulAut.conj t).toMonoidHom ∧
      (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj s).toMonoidHom = K)

theorem A2Cfg.kctx (h37 : A37ForSQTKCat) (h38 : A38ForSQTKCat) (c : A2Cfg G T M L D H K q)
    {t : G} (ht : t ∈ T) (htK : t ∉ Subgroup.normalizer (K : Set G)) : KCtx c t := by
  have htH₀ : t ∈ H ⊔ D := Subgroup.mem_sup_left (c.nf.inH.1 ht)
  have hK : K ∈ cComp (H ⊔ D) := c.nf.K_comp
  set K' := K.map (MulAut.conj t).toMonoidHom with hK'def
  have hK' : K' ∈ cComp (H ⊔ D) := CFSG.Quasithin.map_conj_mem_cComp hK htH₀
  have hKK' : K ≠ K' := fun h => htK (A38.map_conj_eq_iff.mp h.symm)
  have hKN' : K ≤ Subgroup.normalizer (K' : Set G) := le_normalizer_of_mem_cComp hK' hK
  have hK'N : K' ≤ Subgroup.normalizer (K : Set G) := le_normalizer_of_mem_cComp hK hK'
  obtain ⟨t₀, -, -, -, hKK₀, hs⟩ := c.kstruct h37 h38
  have hKt : K' = K.map (MulAut.conj t₀).toMonoidHom := by
    rcases hs t ht with h | h
    · exact absurd (A38.map_conj_eq_iff.mp h) htK
    · exact h
  have hKK₀' : conjClosure K T = K ⊔ K' := hKK₀.trans (by rw [← hKt])
  have hs' : ∀ s ∈ T, K.map (MulAut.conj s).toMonoidHom = K ∨
      K.map (MulAut.conj s).toMonoidHom = K' := by
    intro s hs_
    rcases hs s hs_ with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hKt.symm)
  have hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ := center_quot_of_cfg c
  have hcomm : ⁅K, K'⁆ ≤ pCoreOf 2 K :=
    CFSG.Quasithin.EmptyFaithfulMultiple.L15420.commutator_le_pCoreOf_of_ne hK hK' hKK' c.nf.Kq hZ
  refine ⟨ht, htK, hKK₀', hK'N, hKN', hcomm, fun s hsT => ?_⟩
  have hp := perm_conj htK (hs' (s * t) (T.mul_mem hsT ht))
  rcases hs' s hsT with h | h
  · exact Or.inl ⟨h, hp.1 h⟩
  · exact Or.inr ⟨h, hp.2 h⟩

end KCtx

end CFSG.Quasithin.H13.NFa2
