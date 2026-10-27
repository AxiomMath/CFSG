module

public import CFSG.Quasithin.EmptyFaithful.SzF53BasD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S152X CFSG.Quasithin.F7

namespace F53

variable {G : Type} [Group G] [Finite G]

open CosetGeom

variable {H M S : Subgroup G}

theorem crit_bAt_eq (hA : F53Amalgam H M S) {δ δ' : Geo H M} (h : IsCritPair₁ δ δ')
    (hc : ⁅Zv δ, Zv δ'⁆ ≠ ⊥) : bAt δ = bMin H M ∧ bAt δ' = bMin H M := by
  have h1 : bAt δ = bMin H M :=
    le_antisymm (h.2 ▸ Nat.sInf_le ⟨δ', rfl, h.1⟩) (bMin_le_bAt δ)
  refine ⟨h1, ?_⟩
  have hn : ¬ Zv δ' ≤ Qv δ := by
    intro hle
    apply hc
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact fun x hx => Subgroup.centralizer_le hle ((Zv_le_centerOf_Qv hA δ hx).2)
  refine le_antisymm ?_ (bMin_le_bAt δ')
  have := (Nat.sInf_le ⟨δ, rfl, hn⟩ : bAt δ' ≤ dist δ' δ)
  rw [CosetGeom.dist_comm] at this
  rw [h.2] at this
  exact this

theorem hss113_d (hA : F53Amalgam H M S) {α β α' : Geo H M} (hc : IsCritData α β α')
    (h : ⁅Zv α, Zv α'⁆ ≠ ⊥) (hb : bMin H M < bAt β) : Even (bMin H M) := by
  have h' : IsCritPair₁ α α' := ⟨hc.not_le, hc.dist_eq⟩
  obtain ⟨-, hα'⟩ := crit_bAt_eq hA h' h
  have hne : vtype α' ≠ vtype β := by
    intro hv
    have := bAt_eq_of_vtype_eq hv
    omega
  have hαβ : vtype α ≠ vtype β := vtype_ne_of_adj hc.adj
  have hαα' : vtype α = vtype α' := by
    cases h1 : vtype α <;> cases h2 : vtype α' <;> cases h3 : vtype β <;> simp_all
  have := (vtype_eq_iff_even_dist hA.amalgam.gen α α').mp hαα'
  rwa [hc.dist_eq] at this

theorem hss114_ab (hA : F53Amalgam H M S) {α β α' : Geo H M} (hc : IsCritData α β α')
    (h1 : ⁅Zv α, Zv α'⁆ = ⊥) (_hb : 1 < bMin H M) :
    Zv α' = quasithinOmegaOneCenter (stab α') ∧ Odd (bMin H M) ∧ vtype α' = vtype β := by
  have hle : Zv α ≤ stab α' :=
    Zv_le_stab_of_dist_le hA (by rw [hc.dist_eq, hc.bAt_eq])
  have hZ : Zv α' = quasithinOmegaOneCenter (stab α') := by
    rcases centralizer_Zv_dichotomy hA α' with hQ | hZ
    · exfalso
      apply hc.not_le
      rw [← hQ]
      exact le_inf hle (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1)
    · exact hZ
  have hodd : Odd (bMin H M) := by
    by_contra hodd
    have heven : Even (bMin H M) := Nat.not_odd_iff_even.mp hodd
    have hv : vtype α = vtype α' := by
      rw [vtype_eq_iff_even_dist hA.amalgam.gen, hc.dist_eq]; exact heven
    have hb' : bAt α' = bMin H M := by
      rw [← bAt_eq_of_vtype_eq hv]; exact hc.bAt_eq
    have h12 := centralizer_Zv_eq_Qv_of_bAt hA hb'
    have hcen : stab α' ≤ Subgroup.centralizer (Zv α' : Set G) := by
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hz' : z ∈ centerOf (stab α') := omegaOneCenter_le_centerOf_self _ (hZ ▸ hz)
      exact ((Subgroup.mem_centralizer_iff.mp hz'.2) x hx).symm
    have : stab α' ⊓ Subgroup.centralizer (Zv α' : Set G) = stab α' := inf_eq_left.mpr hcen
    rw [this] at h12
    exact pCoreOf_ne_stab hA α' h12.symm
  refine ⟨hZ, hodd, ?_⟩
  have hαβ : vtype α ≠ vtype β := vtype_ne_of_adj hc.adj
  have hne : vtype α ≠ vtype α' := by
    intro hv
    have := (vtype_eq_iff_even_dist hA.amalgam.gen α α').mp hv
    rw [hc.dist_eq] at this
    exact (Nat.not_even_iff_odd.mpr hodd) this
  cases h1 : vtype α <;> cases h2 : vtype α' <;> cases h3 : vtype β <;> simp_all

omit [Finite G] in
theorem stab_le_normalizer_Vn (δ : Geo H M) : stab δ ≤ Subgroup.normalizer (Vn δ : Set G) := by
  intro x hx
  obtain ⟨hmem, hfix⟩ := mem_stab.mp hx
  apply mem_normalizer_of_conjSub_eq
  have := Vn_smul (⟨x, hmem⟩ : ↥(H ⊔ M)) δ
  rw [hfix] at this
  exact this.symm

theorem isElemAbelian_Vn (hA : F53Amalgam H M S) (hb : 3 ≤ bMin H M) (δ : Geo H M) :
    IsElemAbelian 2 (Vn δ) := by
  have e : Vn δ = ⨆ μ : {μ : Geo H M // μ ∈ nbrs δ}, Zv μ.1 := by
    unfold Vn; exact iSup_subtype'
  rw [e]
  refine isElemAbelian_iSup _ (fun μ => isElemAbelian_Zv hA μ.1) (fun μ μ' x hx y hy => ?_)
  have h1 : dist δ μ.1 = 1 := dist_eq_one_iff_adj.mpr μ.2
  have h2 : dist δ μ'.1 = 1 := dist_eq_one_iff_adj.mpr μ'.2
  have h3 := dist_triangle hA.amalgam.gen μ.1 δ μ'.1
  rw [CosetGeom.dist_comm μ.1 δ] at h3
  have h4 := bMin_le_bAt (H := H) (M := M) μ.1
  have hd : dist μ.1 μ'.1 < bAt μ.1 := by omega
  have hxQ : x ∈ Qv μ'.1 := Zv_le_Qv_of_dist_lt hd hx
  exact (Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA μ'.1 hy).2 x hxQ)

theorem Vn_le_stab (hA : F53Amalgam H M S) (_hb : 3 ≤ bMin H M) {δ δ' : Geo H M}
    (h : dist δ δ' + 1 = bMin H M) : Vn δ ≤ stab δ' := by
  refine iSup₂_le fun l hl => ?_
  apply Zv_le_stab_of_dist_le hA
  have h1 : dist δ l = 1 := dist_eq_one_iff_adj.mpr hl
  have h3 := dist_triangle hA.amalgam.gen l δ δ'
  rw [CosetGeom.dist_comm l δ] at h3
  have h4 := bMin_le_bAt (H := H) (M := M) l
  omega

theorem hss114_d (hA : F53Amalgam H M S) (hb : 3 ≤ bMin H M) {δ δ' : Geo H M}
    (h : dist δ δ' + 1 = bMin H M) :
    Vn δ ≤ stab δ' ∧ Vn δ' ≤ stab δ ∧ ⁅⁅Vn δ', Vn δ⁆, Vn δ⁆ = ⊥ ∧
      ⁅⁅Vn δ, Vn δ'⁆, Vn δ'⁆ = ⊥ := by
  have h' : dist δ' δ + 1 = bMin H M := by rw [CosetGeom.dist_comm]; exact h
  have hl1 := Vn_le_stab hA hb h
  have hl2 := Vn_le_stab hA hb h'
  have hn1 : Vn δ ≤ Subgroup.normalizer (Vn δ' : Set G) := hl1.trans (stab_le_normalizer_Vn δ')
  have hn2 : Vn δ' ≤ Subgroup.normalizer (Vn δ : Set G) := hl2.trans (stab_le_normalizer_Vn δ)
  have hc := commutator_le_inf_of_normalizes hn2 hn1
  refine ⟨hl1, hl2, ?_, ?_⟩
  · refine le_bot_iff.mp ((Subgroup.commutator_mono (hc.trans inf_le_right) le_rfl).trans ?_)
    rw [commutator_self_eq_bot (isElemAbelian_Vn hA hb δ)]
  · have hc' : ⁅Vn δ, Vn δ'⁆ ≤ Vn δ' := by
      rw [Subgroup.commutator_comm]; exact hc.trans inf_le_left
    refine le_bot_iff.mp ((Subgroup.commutator_mono hc' le_rfl).trans ?_)
    rw [commutator_self_eq_bot (isElemAbelian_Vn hA hb δ')]

@[expose] def kerMod (X V Z : Subgroup G) (hZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hV : X ≤ Subgroup.normalizer (V : Set G)) : Subgroup G where
  carrier := {x | x ∈ X ∧ ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ Z}
  one_mem' := ⟨X.one_mem, fun v _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨X.mul_mem ha hb, fun v hv => ?_⟩
    have h1 := hb' v hv
    have h2 : a * (b * v * b⁻¹ * v⁻¹) * a⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hZ ha) _).mp h1
    have h3 := ha' v hv
    have e : a * b * v * (a * b)⁻¹ * v⁻¹ =
        (a * (b * v * b⁻¹ * v⁻¹) * a⁻¹) * (a * v * a⁻¹ * v⁻¹) := by group
    rw [e]; exact Z.mul_mem h2 h3
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨X.inv_mem ha, fun v hv => ?_⟩
    have hw : a⁻¹ * v * a ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hV (X.inv_mem ha)) v).mp hv
      simpa using this
    have h1 := ha' _ hw
    have e : a⁻¹ * v * (a⁻¹)⁻¹ * v⁻¹ = (a * (a⁻¹ * v * a) * a⁻¹ * (a⁻¹ * v * a)⁻¹)⁻¹ := by group
    rw [e]; exact Z.inv_mem h1

omit [Finite G] in
theorem kerMod_normal (X V Z : Subgroup G) (hZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hV : X ≤ Subgroup.normalizer (V : Set G)) :
    X ≤ Subgroup.normalizer (kerMod X V Z hZ hV : Set G) := by
  have key : ∀ g ∈ X, ∀ c ∈ kerMod X V Z hZ hV, g * c * g⁻¹ ∈ kerMod X V Z hZ hV := by
    intro g hg c ⟨hc, hc'⟩
    refine ⟨X.mul_mem (X.mul_mem hg hc) (X.inv_mem hg), fun v hv => ?_⟩
    have hw : g⁻¹ * v * g ∈ V := by
      have := (Subgroup.mem_normalizer_iff.mp (hV (X.inv_mem hg)) v).mp hv
      simpa using this
    have h1 := hc' _ hw
    have h2 : g * (c * (g⁻¹ * v * g) * c⁻¹ * (g⁻¹ * v * g)⁻¹) * g⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hZ hg) _).mp h1
    have e : g * c * g⁻¹ * v * (g * c * g⁻¹)⁻¹ * v⁻¹ =
        g * (c * (g⁻¹ * v * g) * c⁻¹ * (g⁻¹ * v * g)⁻¹) * g⁻¹ := by group
    rw [e]; exact h2
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => key g hg c hc, fun hc => ?_⟩
  have := key g⁻¹ (X.inv_mem hg) _ hc
  simpa [mul_assoc] using this

theorem hss114_e (hA : F53Amalgam H M S) {δ' : Geo H M}
    (hz : Zv δ' = quasithinOmegaOneCenter (stab δ')) :
    ∀ x ∈ stab δ', (∀ v ∈ Vn δ', x * v * x⁻¹ * v⁻¹ ∈ Zv δ') → x ∈ Qv δ' := by
  intro x hx hxC
  by_contra hxQ
  have hZn := stab_le_normalizer_Zv hA δ'
  have hVn := stab_le_normalizer_Vn (H := H) (M := M) δ'
  set C := kerMod (stab δ') (Vn δ') (Zv δ') hZn hVn with hCdef
  have hCX : C ≤ stab δ' := fun y hy => hy.1
  have hCn := kerMod_normal (stab δ') (Vn δ') (Zv δ') hZn hVn
  have hCQ : ¬ C ≤ pCoreOf 2 (stab δ') := fun hle => hxQ (hle ⟨hx, hxC⟩)
  obtain ⟨μ, hμ⟩ := exists_adj δ'
  have hm : μ ∈ nbrs δ' := hμ
  have hm' : δ' ∈ nbrs μ := SimpleGraph.Adj.symm hμ
  have hUB : Zv μ ≤ stab δ' ⊓ stab μ :=
    le_inf ((Zv_le_Qv hA μ).trans (Qv_le_stab_of_mem_nbrs hA hm'))
      ((Zv_le_Qv hA μ).trans (pCoreOf_le 2 _))
  have hZle : Zv δ' ≤ Zv μ := by
    rw [hz]
    exact (omegaOneCenter_le_Zv hA hm).1.trans (omegaOneCenter_le_Zv hA hm).2.2
  have hkey : ∀ c ∈ C, conjSub c (Zv μ) ≤ Zv μ := by
    intro c hc z hz'
    have hw : c⁻¹ * z * c ∈ Zv μ := mem_conjSub.mp hz'
    have hwV : c⁻¹ * z * c ∈ Vn δ' :=
      (le_iSup₂_of_le (f := fun (μ : Geo H M) (_ : μ ∈ nbrs δ') => Zv μ) μ hm le_rfl) hw
    have h1 : c * (c⁻¹ * z * c) * c⁻¹ * (c⁻¹ * z * c)⁻¹ ∈ Zv δ' := hc.2 _ hwV
    have h2 := Zv μ |>.mul_mem (hZle h1) hw
    have e : c * (c⁻¹ * z * c) * c⁻¹ * (c⁻¹ * z * c)⁻¹ * (c⁻¹ * z * c) = z := by group
    rwa [e] at h2
  have hCμ : ∀ c ∈ C, c ∈ Subgroup.normalizer (Zv μ : Set G) := fun c hc =>
    mem_normalizer_of_conj_le (hkey c hc) (hkey c⁻¹ (C.inv_mem hc))
  have hα : ∀ ε ∈ nbrs δ', ∀ ε' ∈ nbrs δ', ∃ x : ↥(H ⊔ M),
      (x : G) ∈ Subgroup.normalizer (Zv μ : Set G) ∧ x • δ' = δ' ∧ x • ε = ε' := by
    intro ε hε ε' hε'
    obtain ⟨c, hcC, hcε⟩ := exists_smul_eq_of_normal_not_le hA hε hε' hCX hCn hCQ
    exact ⟨c, hCμ _ hcC, smul_eq_of_mem_stab (hCX hcC), hcε⟩
  have hβ : ∀ ε ∈ nbrs μ, ∀ ε' ∈ nbrs μ, ∃ x : ↥(H ⊔ M),
      (x : G) ∈ Subgroup.normalizer (Zv μ : Set G) ∧ x • μ = μ ∧ x • ε = ε' := by
    intro ε hε ε' hε'
    obtain ⟨g, hg, hgε⟩ := stab_transitive_on_nbrs hε hε'
    exact ⟨g, stab_le_normalizer_Zv hA μ hg, smul_eq_of_mem_stab hg, hgε⟩
  exact Zv_ne_bot hA μ (eq_bot_of_normalizer_transitive_vertex hA
    (show (graph (H ⊔ M) H M).Adj δ' μ from hμ) hUB hα hβ)

omit [Finite G] in
theorem bAt_eq_of_crit {δ δ' : Geo H M} (h : IsCritPair₁ δ δ') : bAt δ = bMin H M :=
  le_antisymm (h.2 ▸ Nat.sInf_le ⟨δ', rfl, h.1⟩) (bMin_le_bAt δ)

omit [Finite G] in
theorem exists_smul_of_vtype_eq {δ δ' : Geo H M} (h : vtype δ = vtype δ') :
    ∃ g : ↥(H ⊔ M), δ' = g • δ := by
  cases hv : vtype δ with
  | false =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₀ hv
    obtain ⟨g', hg'⟩ := exists_smul_eq_γ₀ (h ▸ hv)
    exact ⟨g' * g⁻¹, by rw [hg, hg', mul_smul, inv_smul_smul]⟩
  | true =>
    obtain ⟨g, hg⟩ := exists_smul_eq_γ₁ hv
    obtain ⟨g', hg'⟩ := exists_smul_eq_γ₁ (h ▸ hv)
    exact ⟨g' * g⁻¹, by rw [hg, hg', mul_smul, inv_smul_smul]⟩

omit [Finite G] in
theorem Zv_central_smul (g : ↥(H ⊔ M)) (δ : Geo H M)
    (hz : Zv δ = quasithinOmegaOneCenter (stab δ)) :
    Zv (g • δ) = quasithinOmegaOneCenter (stab (g • δ)) := by
  rw [Zv_smul, stab_smul, ← conjSub_omegaOneCenter, hz]

theorem Zv_central_of_conj (_hA : F53Amalgam H M S) {δ δ' : Geo H M} (h : vtype δ = vtype δ')
    (hz : Zv δ = quasithinOmegaOneCenter (stab δ)) :
    Zv δ' = quasithinOmegaOneCenter (stab δ') := by
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq h
  exact Zv_central_smul g δ hz

end F53

end CFSG.Quasithin
