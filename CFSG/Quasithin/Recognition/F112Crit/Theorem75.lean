module

public import CFSG.Quasithin.Recognition.F112Crit.Lemma73
public import CFSG.Quasithin.Recognition.F112Crit.Lemma72
public import CFSG.Quasithin.Recognition.F112Crit.ConjAut

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open scoped Pointwise

universe u

variable {G : Type u} [Group G]

open CosetGeom (graph stab ballStab nbrs sphere vtype γ₀ γ₁ Vv)

variable {G₀ G₁ G₂ T Z : Subgroup G} [Finite G]

theorem vtype_eq_of_dist (hc : CritAmalgam G₀ G₁ G₂ T Z) {γ : CosetGeom G₀ G₁ G₂}
    (hγ : vtype γ = false) :
    ∀ (d : ℕ) (μ : CosetGeom G₀ G₁ G₂), CosetGeom.dist γ μ = d → vtype μ = decide (Odd d) := by
  intro d
  induction d with
  | zero =>
    intro μ hμ
    obtain rfl := (CosetGeom.dist_eq_zero_iff hc.amalgam.gen).mp hμ
    simpa using hγ
  | succ d ih =>
    intro μ hμ
    obtain ⟨μ', hadj, hμ'⟩ := CosetGeom.exists_adj_dist_eq hc.amalgam.gen hμ
    have h1 := ih μ' hμ'
    have h2 := CosetGeom.vtype_ne_of_adj hadj
    rw [h1] at h2
    by_cases hd : Odd d
    · have h3 : ¬ Odd (d + 1) := by rw [Nat.odd_add_one]; exact not_not.mpr hd
      simp only [hd, decide_true] at h2
      simp only [h3, decide_false]
      cases h : vtype μ <;> simp_all
    · have h3 : Odd (d + 1) := by rw [Nat.odd_add_one]; exact hd
      simp only [hd, decide_false] at h2
      simp only [h3, decide_true]
      cases h : vtype μ <;> simp_all

structure CritConfig (Z : Subgroup G) (α α₁ α' α₂ α₃ : CosetGeom G₀ G₁ G₂) : Prop where
  vα : vtype α = false
  vα₁ : vtype α₁ = true
  vα' : vtype α' = true
  adj₁ : α ∈ nbrs α₁
  adj₂ : α₂ ∈ nbrs α₁
  adj₃ : α₃ ∈ nbrs α'
  not_le : ¬ Vv Z α ≤ ballStab 1 α'
  push₂ : Vv Z α' ≤ pCoreOf 2 (stab α₂)
  push₃ : Vv Z α₁ ≤ pCoreOf 2 (stab α₃)

theorem exists_critConfig (hc : CritAmalgam G₀ G₁ G₂ T Z) (hb : Odd (critB G₀ G₁ G₂ Z)) :
    ∃ α α₁ α' α₂ α₃ : CosetGeom G₀ G₁ G₂, CritConfig Z α α₁ α' α₂ α₃ := by
  have hG := hc.amalgam.gen
  have hb2 := two_le_critB hc
  obtain ⟨α', hdist, hnZ⟩ := exists_dist_eq_critB hc
  obtain ⟨k, hk⟩ : ∃ k, critB G₀ G₁ G₂ Z = k + 2 := ⟨critB G₀ G₁ G₂ Z - 2, by omega⟩
  rw [hk] at hdist hb
  have hα : vtype (γ₀ G₀ G₁ G₂) = false := CosetGeom.vtype_γ₀
  have hα'v : vtype α' = true := by
    rw [vtype_eq_of_dist hc hα _ α' hdist]; exact decide_eq_true hb
  have hd1 : CosetGeom.dist α' (γ₀ G₀ G₁ G₂) = (k + 1) + 1 := by
    rw [CosetGeom.dist_comm]; exact hdist
  obtain ⟨α₁, hadj₁, hd₁⟩ := CosetGeom.exists_adj_dist_eq hG hd1
  have hα₁v : vtype α₁ = true := vtype_eq_true_of_mem_nbrs hα hadj₁
  have hd2 : CosetGeom.dist α₁ α' = k + 1 := by rw [CosetGeom.dist_comm]; exact hd₁
  obtain ⟨α₃, hadj₃, hd₃⟩ := CosetGeom.exists_adj_dist_eq hG hd2
  obtain ⟨α₂, hadj₂, hd₄⟩ := CosetGeom.exists_adj_dist_eq hG hd₁
  refine ⟨γ₀ G₀ G₁ G₂, α₁, α', α₂, α₃, ⟨hα, hα₁v, hα'v, CosetGeom.mem_nbrs_symm hadj₁, hadj₂,
    hadj₃, ?_, ?_, ?_⟩⟩
  · rw [CosetGeom.Vv_γ₀ hc.normalizes]; exact hnZ
  · exact lemma72_small hc hα'v (by rw [hk, hd₄])
  · exact lemma72_small hc hα₁v (by rw [hk, hd₃])

theorem CritConfig.smul (hc : CritAmalgam G₀ G₁ G₂ T Z) {α α₁ α' α₂ α₃ : CosetGeom G₀ G₁ G₂}
    (h : CritConfig Z α α₁ α' α₂ α₃) (g : ↥G₀) :
    CritConfig Z (g • α) (g • α₁) (g • α') (g • α₂) (g • α₃) where
  vα := by rw [CosetGeom.vtype_smul]; exact h.vα
  vα₁ := by rw [CosetGeom.vtype_smul]; exact h.vα₁
  vα' := by rw [CosetGeom.vtype_smul]; exact h.vα'
  adj₁ := (CosetGeom.smul_adj g).mpr h.adj₁
  adj₂ := (CosetGeom.smul_adj g).mpr h.adj₂
  adj₃ := (CosetGeom.smul_adj g).mpr h.adj₃
  not_le := by
    rw [CosetGeom.Vv_smul hc.normalizes, CosetGeom.ballStab_smul, conjSub_le_conjSub_iff]
    exact h.not_le
  push₂ := by
    rw [CosetGeom.Vv_smul hc.normalizes, CosetGeom.stab_smul, pCoreOf_conjSub]
    exact conjSub_mono _ h.push₂
  push₃ := by
    rw [CosetGeom.Vv_smul hc.normalizes, CosetGeom.stab_smul, pCoreOf_conjSub]
    exact conjSub_mono _ h.push₃

theorem conj_eq_of_mem_centralizer {V : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.centralizer (V : Set G)) {a : G} (ha : a ∈ V) : g * a * g⁻¹ = a := by
  rw [mul_inv_eq_iff_eq_mul]
  exact ((Subgroup.mem_centralizer_iff.mp hg) a ha).symm

theorem conj_inv_action {V : Subgroup G} {s x : G} (hs : s ∈ Subgroup.normalizer (V : Set G))
    (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hn : s * x * s⁻¹ * x ∈ Subgroup.centralizer (V : Set G)) :
    ∀ a ∈ V, s * (x * a * x⁻¹) * s⁻¹ = x⁻¹ * (s * a * s⁻¹) * x := by
  intro a ha
  have hb : x⁻¹ * (s * a * s⁻¹) * x ∈ V :=
    ConjAut.conj_inv_mem V hx (ConjAut.conj_mem V hs ha)
  have h1 := conj_eq_of_mem_centralizer hn hb
  calc s * (x * a * x⁻¹) * s⁻¹
      = (s * x * s⁻¹ * x) * (x⁻¹ * (s * a * s⁻¹) * x) * (s * x * s⁻¹ * x)⁻¹ := by group
    _ = x⁻¹ * (s * a * s⁻¹) * x := h1

theorem sq_action {V : Subgroup G} {t : G} (htt : t * t ∈ Subgroup.centralizer (V : Set G)) :
    ∀ a ∈ V, t * (t * a * t⁻¹) * t⁻¹ = a := by
  intro a ha
  have h1 := conj_eq_of_mem_centralizer htt ha
  calc t * (t * a * t⁻¹) * t⁻¹ = (t * t) * a * (t * t)⁻¹ := by group
    _ = a := h1

variable {α α₁ α' α₂ α₃ : CosetGeom G₀ G₁ G₂}

theorem CritConfig.vOne_le (hc : CritAmalgam G₀ G₁ G₂ T Z)
    (h : CritConfig Z α α₁ α' α₂ α₃) : Vv Z α₁ ≤ stab α' ⊓ stab α₃ := by
  have hα₃ : vtype α₃ = false := vtype_eq_false_of_mem_nbrs h.vα' h.adj₃
  refine h.push₃.trans (le_inf ?_ (pCoreOf_le 2 _))
  exact (lemma63_1 hc hα₃).2.trans
    (IsLocalReg.ker_le_stab_of_mem_nbrs (CosetGeom.mem_nbrs_symm h.adj₃))

theorem CritConfig.vTwo_le (hc : CritAmalgam G₀ G₁ G₂ T Z)
    (h : CritConfig Z α α₁ α' α₂ α₃) : Vv Z α' ≤ stab α₁ ⊓ stab α₂ := by
  have hα₂ : vtype α₂ = false := vtype_eq_false_of_mem_nbrs h.vα₁ h.adj₂
  refine h.push₂.trans (le_inf ?_ (pCoreOf_le 2 _))
  exact (lemma63_1 hc hα₂).2.trans
    (IsLocalReg.ker_le_stab_of_mem_nbrs (CosetGeom.mem_nbrs_symm h.adj₂))

open scoped IsMulCommutative

theorem crit_card_comm (hc : CritAmalgam G₀ G₁ G₂ T Z) (hconf : CritConfig Z α α₁ α' α₂ α₃)
    {p : ℕ} {X' X₁ : Subgroup G} (h' : IsLocalReg α' p X') (h₁ : IsLocalReg α₁ p X₁) {x : G}
    (hx : x ∈ X') (hxN : x ∉ ballStab 1 α') :
    p = 3 ∧ Nat.card (ConjAut.commSubgroup (Vv Z α') x) = 4 := by
  have hG := hc.amalgam.gen
  have hel := lemma63_2' hc hconf.vα'
  haveI : IsMulCommutative ↥(Vv Z α') := hel.1.1
  have h2 : ∀ v ∈ Vv Z α', v * v = 1 := fun v hv => by
    rw [← pow_two]; exact hel.1.2 v hv
  have hnorm : stab α' ≤ Subgroup.normalizer (Vv Z α' : Set G) := hel.2.2.2.2
  have hxst : x ∈ stab α' := h'.le_stab hx
  have hxs : x ∈ Subgroup.normalizer (Vv Z α' : Set G) := hnorm hxst
  have hcentN : ballStab 1 α' ≤ Subgroup.centralizer (Vv Z α' : Set G) :=
    ballStab_le_centralizer_Vv hc hconf.vα'
  obtain ⟨v₀, hv₀Z, hv₀N⟩ := SetLike.not_le_iff_exists.mp hconf.not_le
  have hv₀V₁ : v₀ ∈ Vv Z α₁ := Vv_le_Vv_of_mem_nbrs hconf.vα₁ hconf.adj₁ hv₀Z
  have hel₁ := lemma63_2' hc hconf.vα₁
  have hv₀sq : v₀ * v₀ = 1 := by rw [← pow_two]; exact hel₁.1.2 v₀ hv₀V₁
  have hv₀st : v₀ ∈ stab α' ⊓ stab α₃ := hconf.vOne_le hc hv₀V₁
  have hts : v₀ ∈ Subgroup.normalizer (Vv Z α' : Set G) := hnorm hv₀st.1
  have hinv : ∀ y ∈ X', v₀ * y * v₀⁻¹ * y ∈ ballStab 1 α' :=
    (h'.mem_ker_or_inv hG hconf.adj₃ hv₀st
      (by rw [hv₀sq]; exact Subgroup.one_mem _)).resolve_left hv₀N
  have hxp : ∀ a ∈ Vv Z α', x ^ p * a * (x ^ p)⁻¹ = a := fun a ha =>
    conj_eq_of_mem_centralizer (hcentN (h'.pow_mem_ker hx)) ha
  have htt : ∀ a ∈ Vv Z α', v₀ * (v₀ * a * v₀⁻¹) * v₀⁻¹ = a :=
    sq_action (by rw [hv₀sq]; exact Subgroup.one_mem _)
  have htx := conj_inv_action hts hxs (hcentN (hinv x hx))
  have hne : ∃ a ∈ Vv Z α', x * a * x⁻¹ ≠ a := by
    by_contra hcon
    push Not at hcon
    apply hxN
    rw [← lemma73_1 hc hconf.vα']
    refine ⟨hxst, ?_⟩
    show x ∈ Subgroup.centralizer (Vv Z α' : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have := hcon a ha
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this.symm
  have hN₁C : ballStab 1 α₁ ≤ Subgroup.centralizer ({v₀} : Set G) :=
    (ballStab_le_centralizer_Vv hc hconf.vα₁).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hv₀V₁))
  have hidx : (Subgroup.centralizer ({v₀} : Set G)).relIndex (Vv Z α') ≤ 2 := by
    refine relIndex_le_two_of_forall fun a ha b hb haC hbC => ?_
    have hst := hconf.vTwo_le hc
    have haN : a ∉ ballStab 1 α₁ := fun hh => haC (hN₁C hh)
    have hbN : b ∉ ballStab 1 α₁ := fun hh => hbC (hN₁C hh)
    have hsq : ∀ c ∈ Vv Z α', c * c ∈ ballStab 1 α₁ := fun c hc' => by
      rw [h2 c hc']; exact Subgroup.one_mem _
    exact hN₁C (h₁.mul_mem_ker hG hconf.adj₂ (hst hb) (hst ha) (hsq b hb) (hsq a ha) hbN haN)
  have hp2 : p % 2 = 1 := h'.prime.eq_two_or_odd.resolve_left h'.ne_two
  obtain ⟨hp3, h4⟩ :=
    ConjAut.lemma74_group (Vv Z α') h2 h'.prime hp2 hxs hts hxp htt htx hne hidx
  exact ⟨hp3, by rw [ConjAut.card_commSubgroup (Vv Z α') x hxs]; exact h4⟩

theorem crit_card_Z_le (hc : CritAmalgam G₀ G₁ G₂ T Z) (hconf : CritConfig Z α α₁ α' α₂ α₃)
    {p : ℕ} {X' X₁ : Subgroup G} (h' : IsLocalReg α' p X') (h₁ : IsLocalReg α₁ p X₁) {x : G}
    (hx : x ∈ X') (hxN : x ∉ ballStab 1 α') {γ : CosetGeom G₀ G₁ G₂} (hγ : γ ∈ nbrs α') :
    Nat.card (Vv Z γ) ≤ 2 := by
  have hG := hc.amalgam.gen
  obtain ⟨hp3, h4⟩ := crit_card_comm hc hconf h' h₁ hx hxN
  have hel := lemma63_2' hc hconf.vα'
  haveI : IsMulCommutative ↥(Vv Z α') := hel.1.1
  have h2 : ∀ v ∈ Vv Z α', v * v = 1 := fun v hv => by
    rw [← pow_two]; exact hel.1.2 v hv
  have hnorm : stab α' ≤ Subgroup.normalizer (Vv Z α' : Set G) := hel.2.2.2.2
  have hxst : x ∈ stab α' := h'.le_stab hx
  have hxs : x ∈ Subgroup.normalizer (Vv Z α' : Set G) := hnorm hxst
  have hcentN : ballStab 1 α' ≤ Subgroup.centralizer (Vv Z α' : Set G) :=
    ballStab_le_centralizer_Vv hc hconf.vα'
  have hW4 : Nat.card (GaloisDescent.commSub (ConjAut.conjAut (Vv Z α') x hxs)) = 4 := by
    rw [← ConjAut.card_commSubgroup (Vv Z α') x hxs]; exact h4
  have hγt : vtype γ = false := vtype_eq_false_of_mem_nbrs hconf.vα' hγ
  obtain ⟨t, ht, htN⟩ := h'.exists_mem γ hγ
  have htt' : t * t ∈ ballStab 1 α' := by
    have := h'.pow_pred_mem hG hγ ht
    rwa [hp3, show 3 - 1 = 2 from rfl, pow_two] at this
  have hinv : ∀ y ∈ X', t * y * t⁻¹ * y ∈ ballStab 1 α' :=
    (h'.mem_ker_or_inv hG hγ ht htt').resolve_left htN
  have hts : t ∈ Subgroup.normalizer (Vv Z α' : Set G) := hnorm ht.1
  have hxp : ∀ a ∈ Vv Z α', x ^ p * a * (x ^ p)⁻¹ = a := fun a ha =>
    conj_eq_of_mem_centralizer (hcentN (h'.pow_mem_ker hx)) ha
  have htt : ∀ a ∈ Vv Z α', t * (t * a * t⁻¹) * t⁻¹ = a := sq_action (hcentN htt')
  have htx := conj_inv_action hts hxs (hcentN (hinv x hx))
  have hp2 : p % 2 = 1 := h'.prime.eq_two_or_odd.resolve_left h'.ne_two
  refine ConjAut.card_le_two_group (Vv Z α') h2 hp2 hxs hts hxp htt htx hW4
    (Vv_le_Vv_of_mem_nbrs hconf.vα' hγ) (fun a ha => ?_) (fun a ha hax => ?_)
  · exact conj_eq_of_mem_centralizer (stab_le_centralizer_Vv hc hγt ht.2) ha
  · refine lemma73_3 hc hconf.vα' h' hγ hx hxN ha ?_
    rw [mul_inv_eq_iff_eq_mul] at hax
    exact hax

theorem Vv_eq_sup_conj (hc : CritAmalgam G₀ G₁ G₂ T Z) {δ : CosetGeom G₀ G₁ G₂}
    (hδ : vtype δ = true) {X : Subgroup G} (h : IsLocalReg δ 3 X) {γ : CosetGeom G₀ G₁ G₂}
    (hγ : γ ∈ nbrs δ) {x : G} (hx : x ∈ X) (hxN : x ∉ ballStab 1 δ) :
    Vv Z δ = Vv Z γ ⊔ conjSub x (Vv Z γ) ⊔ conjSub (x ^ 2) (Vv Z γ) := by
  have hxst : x ∈ stab δ := h.le_stab hx
  have hxr : ∀ r : ℕ, x ^ r ∈ G₀ := fun r => G₀.pow_mem (CosetGeom.stab_le δ hxst) r
  have hconj : ∀ r : ℕ, conjSub (x ^ r) (Vv Z γ) = Vv Z ((⟨x ^ r, hxr r⟩ : ↥G₀) • γ) :=
    fun r => (CosetGeom.Vv_smul hc.normalizes (⟨x ^ r, hxr r⟩ : ↥G₀) γ).symm
  have hle : ∀ r : ℕ, conjSub (x ^ r) (Vv Z γ) ≤ Vv Z δ := fun r => by
    rw [hconj r]
    exact Vv_le_Vv_of_mem_nbrs hδ (IsLocalReg.smul_mem_nbrs hγ ((stab δ).pow_mem hxst r))
  apply le_antisymm
  · refine Vv_le_of_forall_mem_nbrs hδ fun μ hμ => ?_
    obtain ⟨r, hr, g, hg, rfl⟩ := h.exists_pow_smul_eq hγ hμ hx hxN
    rw [CosetGeom.Vv_smul hc.normalizes, hg]
    interval_cases r
    · rw [pow_zero, conjSub_one]; exact le_sup_left.trans le_sup_left
    · rw [pow_one]; exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  · refine sup_le (sup_le (Vv_le_Vv_of_mem_nbrs hδ hγ) ?_) (hle 2)
    simpa using hle 1

theorem le_normalizer_of_le_comm {V H K : Subgroup G} [IsMulCommutative ↥V] (hH : H ≤ V)
    (hK : K ≤ V) : H ≤ Subgroup.normalizer (K : Set G) := by
  refine le_trans ?_ (Subgroup.centralizer_le_normalizer (K : Set G))
  intro h hh
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  exact congrArg Subtype.val (mul_comm (⟨k, hK hk⟩ : ↥V) ⟨h, hH hh⟩)

theorem crit_card_V_le (hc : CritAmalgam G₀ G₁ G₂ T Z) (hconf : CritConfig Z α α₁ α' α₂ α₃)
    {p : ℕ} {X' X₁ : Subgroup G} (h' : IsLocalReg α' p X') (h₁ : IsLocalReg α₁ p X₁) :
    Nat.card (Vv Z α') ≤ 8 := by
  obtain ⟨x, hx, hxN⟩ := h'.exists_not_mem
  have hp3 := (crit_card_comm hc hconf h' h₁ hx hxN).1
  subst hp3
  have hel := lemma63_2' hc hconf.vα'
  haveI : IsMulCommutative ↥(Vv Z α') := hel.1.1
  have hγ := hconf.adj₃
  have hE := Vv_eq_sup_conj hc hconf.vα' h' hγ hx hxN
  have hA : Vv Z α₃ ≤ Vv Z α' := Vv_le_Vv_of_mem_nbrs hconf.vα' hγ
  have hB : conjSub x (Vv Z α₃) ≤ Vv Z α' := by rw [hE]; exact le_sup_right.trans le_sup_left
  have hC : conjSub (x ^ 2) (Vv Z α₃) ≤ Vv Z α' := by rw [hE]; exact le_sup_right
  have hZ2 := crit_card_Z_le hc hconf h' h₁ hx hxN hγ
  calc Nat.card (Vv Z α')
      = Nat.card ↥(Vv Z α₃ ⊔ conjSub x (Vv Z α₃) ⊔ conjSub (x ^ 2) (Vv Z α₃)) := by rw [← hE]
    _ ≤ Nat.card ↥(Vv Z α₃ ⊔ conjSub x (Vv Z α₃)) * Nat.card ↥(conjSub (x ^ 2) (Vv Z α₃)) :=
        card_sup_le_of_le_normalizer (le_normalizer_of_le_comm (sup_le hA hB) hC)
    _ ≤ (Nat.card ↥(Vv Z α₃) * Nat.card ↥(conjSub x (Vv Z α₃))) *
          Nat.card ↥(conjSub (x ^ 2) (Vv Z α₃)) :=
        Nat.mul_le_mul_right _ (card_sup_le_of_le_normalizer (le_normalizer_of_le_comm hA hB))
    _ ≤ (2 * 2) * 2 := by
        rw [IsLocalReg.card_conjSub_eq, IsLocalReg.card_conjSub_eq]
        exact Nat.mul_le_mul (Nat.mul_le_mul hZ2 hZ2) hZ2

theorem exists_critConfig_at (hc : CritAmalgam G₀ G₁ G₂ T Z) (hb : Odd (critB G₀ G₁ G₂ Z))
    {δ : CosetGeom G₀ G₁ G₂} (hδ : vtype δ = true) :
    ∃ α α₁ α₂ α₃ : CosetGeom G₀ G₁ G₂, CritConfig Z α α₁ δ α₂ α₃ := by
  obtain ⟨α, α₁, α', α₂, α₃, hconf⟩ := exists_critConfig hc hb
  obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₁ hδ
  obtain ⟨g', hg'⟩ := CosetGeom.exists_smul_eq_γ₁ hconf.vα'
  refine ⟨(g * g'⁻¹) • α, (g * g'⁻¹) • α₁, (g * g'⁻¹) • α₂, (g * g'⁻¹) • α₃, ?_⟩
  have h1 : (g * g'⁻¹) • α' = δ := by
    rw [hg', ← mul_smul, mul_assoc, inv_mul_cancel, mul_one, hg]
  have := hconf.smul hc (g * g'⁻¹)
  rwa [h1] at this

theorem theorem75 (hc : CritAmalgam G₀ G₁ G₂ T Z) (hb : Odd (critB G₀ G₁ G₂ Z)) {p : ℕ}
    {X₀ : Subgroup G} (hbase : IsLocalReg (γ₁ G₀ G₁ G₂) p X₀) :
    p = 3 ∧ Nat.card Z = 2 ∧
      ∀ δ : CosetGeom G₀ G₁ G₂, vtype δ = true →
        Nat.card (Vv Z δ) ≤ 8 ∧
        ∀ X : Subgroup G, IsLocalReg δ p X → ∀ x ∈ X, x ∉ ballStab 1 δ →
          Nat.card (ConjAut.commSubgroup (Vv Z δ) x) = 4 := by
  obtain ⟨α, α₁, α', α₂, α₃, hconf⟩ := exists_critConfig hc hb
  obtain ⟨X', hX'⟩ := exists_isLocalReg_of_vtype hbase hconf.vα'
  obtain ⟨X₁, hX₁⟩ := exists_isLocalReg_of_vtype hbase hconf.vα₁
  obtain ⟨x, hx, hxN⟩ := hX'.exists_not_mem
  have hp3 := (crit_card_comm hc hconf hX' hX₁ hx hxN).1
  refine ⟨hp3, ?_, fun δ hδ => ?_⟩
  · have hα₃ : vtype α₃ = false := vtype_eq_false_of_mem_nbrs hconf.vα' hconf.adj₃
    obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₀ hα₃
    have h1 : Nat.card Z ≤ 2 := by
      have := crit_card_Z_le hc hconf hX' hX₁ hx hxN hconf.adj₃
      rwa [hg, Zv_smul_γ₀ hc, IsLocalReg.card_conjSub_eq] at this
    have h2 : 0 < Nat.card Z := Nat.card_pos
    have h3 : Nat.card Z ≠ 1 := fun h => hc.ne_bot (Subgroup.card_eq_one.mp h)
    omega
  · obtain ⟨β, β₁, β₂, β₃, hconfδ⟩ := exists_critConfig_at hc hb hδ
    obtain ⟨X₁', hX₁'⟩ := exists_isLocalReg_of_vtype hbase hconfδ.vα₁
    refine ⟨?_, fun X hX y hy hyN => (crit_card_comm hc hconfδ hX hX₁' hy hyN).2⟩
    obtain ⟨X'', hX''⟩ := exists_isLocalReg_of_vtype hbase hδ
    exact crit_card_V_le hc hconfδ hX'' hX₁'

theorem corollary76 (hc : CritAmalgam G₀ G₁ G₂ T Z) {p : ℕ} {X₀ : Subgroup G}
    (hbase : IsLocalReg (γ₁ G₀ G₁ G₂) p X₀) (hp : p ≠ 3) : ¬ Odd (critB G₀ G₁ G₂ Z) :=
  fun hb => hp (theorem75 hc hb hbase).1

theorem exists_zpowers_of_card_two {H : Subgroup G} (h : Nat.card H = 2) :
    ∃ z : G, H = Subgroup.zpowers z ∧ orderOf z = 2 := by
  have hne : H ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.card_bot] at h
    omega
  obtain ⟨⟨z, hzH⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hz1' : z ≠ 1 := fun h' => hz1 (Subtype.ext h')
  have hzle : Subgroup.zpowers z ≤ H := (Subgroup.zpowers_le).mpr hzH
  have hord : orderOf z ∣ 2 := by
    rw [← h, ← Nat.card_zpowers]; exact Subgroup.card_dvd_of_le hzle
  have hord2 : orderOf z = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp hord).resolve_left (by simpa [orderOf_eq_one_iff] using hz1')
  refine ⟨z, (Subgroup.eq_of_le_of_card_ge hzle ?_).symm, hord2⟩
  rw [Nat.card_zpowers, hord2, h]

theorem conjSub_zpowers (g z : G) :
    conjSub g (Subgroup.zpowers z) = Subgroup.zpowers (g * z * g⁻¹) := by
  unfold conjSub
  rw [MonoidHom.map_zpowers]
  rfl

theorem corollary77 (hc : CritAmalgam G₀ G₁ G₂ T Z) (hb : Odd (critB G₀ G₁ G₂ Z)) {p : ℕ}
    {X₀ : Subgroup G} (hbase : IsLocalReg (γ₁ G₀ G₁ G₂) p X₀) :
    p = 3 ∧
    (∀ γ : CosetGeom G₀ G₁ G₂, vtype γ = false →
      ∃ z : G, Vv Z γ = Subgroup.zpowers z ∧ orderOf z = 2 ∧ ∀ g ∈ stab γ, g * z = z * g) ∧
    ∀ δ : CosetGeom G₀ G₁ G₂, vtype δ = true → ∀ X : Subgroup G, IsLocalReg δ p X →
      ∀ γ ∈ nbrs δ, ∀ x ∈ X, x ∉ ballStab 1 δ → ∀ z : G, Vv Z γ = Subgroup.zpowers z →
        Vv Z δ = Subgroup.zpowers z ⊔ Subgroup.zpowers (x * z * x⁻¹) ⊔
          Subgroup.zpowers (x ^ 2 * z * (x ^ 2)⁻¹) := by
  obtain ⟨hp3, hZ, -⟩ := theorem75 hc hb hbase
  subst hp3
  refine ⟨rfl, fun γ hγ => ?_, fun δ hδ X hX γ hγ x hx hxN z hz => ?_⟩
  · obtain ⟨g, hg⟩ := CosetGeom.exists_smul_eq_γ₀ hγ
    have hcard : Nat.card (Vv Z γ) = 2 := by
      rw [hg, Zv_smul_γ₀ hc, IsLocalReg.card_conjSub_eq]; exact hZ
    obtain ⟨z, hz, hord⟩ := exists_zpowers_of_card_two hcard
    refine ⟨z, hz, hord, fun g hg' => ?_⟩
    have hzV : z ∈ Vv Z γ := hz ▸ Subgroup.mem_zpowers z
    exact ((Subgroup.mem_centralizer_iff.mp (stab_le_centralizer_Vv hc hγ hg')) z hzV).symm
  · rw [Vv_eq_sup_conj hc hδ hX hγ hx hxN, hz, conjSub_zpowers, conjSub_zpowers]

end CFSG.Quasithin.F112Crit
