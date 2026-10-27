module

public import CFSG.Quasithin.Background.FLc3Set
public import CFSG.Quasithin.Background.FLc3Mod
public import CFSG.Quasithin.Background.FLcNat
public import CFSG.Quasithin.Background.FLc3Rad

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.FLc

open CFSG.Open CFSG.Quasithin Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem card_le_of_offender {V : Type} [CommGroup V] {X A : Subgroup (MulAut V)}
    (h : IsFFStarOffender X A) : Nat.card V ≤ Nat.card A * Nat.card (fixV A) := by
  have hbot := h.2.2.2 ⊥ bot_le
  have hfixbot : fixV (⊥ : Subgroup (MulAut V)) = ⊤ := by
    ext v
    simp [mem_fixV]
  rw [hfixbot, Subgroup.card_bot, Subgroup.card_top, one_mul] at hbot
  exact hbot

theorem QI_le_of_reflections {n : ℕ} {H : Subgroup (SLt n)} (hU : Ut n ≤ H) {c : ℕ}
    (hr : ∀ i, ∀ hi : IsNode n i, i ≠ c → reflection n (ZMod 2) i hi.1 hi.2 ∈ H) :
    QI n {c} ≤ H := by
  have hH := eq_QI_cuts hU
  have hsub : cuts H ⊆ {c} := by
    intro i hi
    have hin := isNode_of_mem_cuts hi
    by_contra hic
    obtain ⟨h1, h2, hnot⟩ := hi
    exact hnot (hr i ⟨h1, h2⟩ hic)
  rw [hH]
  exact (QI_le_QI_iff fun j hj => isNode_of_mem_cuts hj).2 hsub

section

variable {V : Type} [CommGroup V]

theorem fixQ_of_model {n : ℕ} {ρ : SLt n →* MulAut V} {U' Z' : Subgroup V} {X : Type} [CommGroup X]
    {act : SLt n → X → X} (D : VModel n ρ U' Z' X act) (hV2 : ∀ w : V, w ^ 2 = 1) (hn : 1 ≤ n) {c : ℕ}
    (hFix : ∀ a : X, (∀ g ∈ Ut n, act g a = a) → ∀ i, ∀ hi : IsNode n i, i ≠ c →
      act (reflection n (ZMod 2) i hi.1 hi.2) a = a)
    {v : V} (hv : v ∈ U') (hvf : ∀ s ∈ Ut n, (ρ s) v = v) : ∀ x ∈ QI n {c}, (ρ x) v = v := by
  let H : Subgroup (SLt n) := (MulAction.stabilizer (MulAut V) v).comap ρ
  have hUH : Ut n ≤ H := fun s hs => hvf s hs
  have hrH : ∀ i, ∀ hi : IsNode n i, i ≠ c → reflection n (ZMod 2) i hi.1 hi.2 ∈ H := by
    intro i hi hic
    have h1 := D.fix_reflection_conj hV2 hn hFix 1 hv (by simpa using hvf) hi hic
    have h2 : (ρ (reflection n (ZMod 2) i hi.1 hi.2)) v = v := by simpa using h1
    exact h2
  intro x hx
  exact QI_le_of_reflections hUH hrH hx

end

theorem dual_fix_last {n : ℕ} (hn : 1 ≤ n) {g : SLt n} (hg : g ∈ QI n {n - 1}) {w : Vt n}
    (hw : ∀ b : Fin n, (b : ℕ) < n - 1 → w b = 0) : (mat g⁻¹)ᵀ *ᵥ w = w := by
  set z : Fin n := ⟨n - 1, by omega⟩ with hz
  set h : SLt n := g⁻¹ with hh
  have hhg : h ∈ QI n {n - 1} := (QI n {n - 1}).inv_mem hg
  have hstab : h ∈ stabilizer (flagSpace n (ZMod 2) (n - 1)) := by
    have := (mem_flagStabilizer).1 hhg (n - 1) rfl
    exact this
  have hpres := (mem_stabilizer_iff).1 hstab
  have hrow0 : ∀ j : Fin n, j ≠ z → mat h z j = 0 := by
    intro j hjz
    have hej : (Pi.single j (1 : ZMod 2) : Vt n) ∈ flagSpace n (ZMod 2) (n - 1) := by
      rw [mem_flagSpace]
      intro k hk
      have hkz : k = z := Fin.ext (by simp [hz]; omega)
      rw [hkz]
      exact Pi.single_eq_of_ne (Ne.symm hjz) _
    have := (hpres _).1 hej
    rw [mem_flagSpace] at this
    have h2 := this z (by simp [hz])
    simpa [Matrix.mulVec_single_one] using h2
  have hrow1 : mat h z z = 1 := by
    have e := congrFun (congrFun (mat_mul_inv h) z) z
    rw [Matrix.mul_apply, Finset.sum_eq_single z] at e
    · rw [Matrix.one_apply_eq] at e
      exact zmod_two_eq_one_of_mul_eq_one e
    · intro j _ hjz
      rw [hrow0 j hjz, zero_mul]
    · intro hz'
      exact absurd (Finset.mem_univ z) hz'
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  rw [Finset.sum_eq_single z]
  · by_cases hjz : j = z
    · rw [hjz, hrow1, one_mul]
    · rw [hrow0 j hjz, zero_mul]
      have hwj : w j = 0 := hw j (by
        have : (j : ℕ) ≠ n - 1 := fun h' => hjz (Fin.ext (by simp [hz]; exact h'))
        have := j.2
        omega)
      rw [hwj]
  · intro k _ hkz
    rw [hw k (by have := k.2; have : (k : ℕ) ≠ n - 1 := fun h' => hkz (Fin.ext (by simp [hz]; exact h'))
                 omega), mul_zero]
  · intro hz'
    exact absurd (Finset.mem_univ z) hz'

theorem fix_dual_support {n : ℕ} (a : Multiplicative (Vt n)) (ha : ∀ g ∈ Ut n, actDl g a = a) :
    ∀ b : Fin n, (b : ℕ) < n - 1 → Multiplicative.toAdd a b = 0 := by
  intro b hb
  have hb1 : (b : ℕ) + 1 < n := by omega
  set b' : Fin n := ⟨(b : ℕ) + 1, hb1⟩ with hb'
  have hlt : b < b' := by
    rw [Fin.lt_def]
    show (b : ℕ) < (b : ℕ) + 1
    omega
  have hg : (tv b b' hlt)⁻¹ ∈ Ut n := (Ut n).inv_mem (tv_mem_Ut hlt)
  have h1 := congrArg Multiplicative.toAdd (ha _ hg)
  rw [toAdd_actDl, inv_inv] at h1
  have hco : mat (tv b b' hlt) = 1 + Matrix.single b b' (1 : ZMod 2) :=
    SpecialLinearGroup.transvection_coe hlt.ne 1
  rw [hco, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single] at h1
  have h2 := congrFun h1 b'
  rw [mat_transv_mulVec_apply hlt.ne'] at h2
  simp only [ite_true] at h2
  have h3 : Multiplicative.toAdd a b' + Multiplicative.toAdd a b = Multiplicative.toAdd a b' := h2
  have h4 : Multiplicative.toAdd a b = 0 := by
    have := congrArg (fun x => x - Multiplicative.toAdd a b') h3
    simpa using this
  exact h4

theorem fix_dual {n : ℕ} (hn : 1 ≤ n) (a : Multiplicative (Vt n)) (ha : ∀ g ∈ Ut n, actDl g a = a) :
    ∀ i, ∀ hi : IsNode n i, i ≠ n - 1 →
      actDl (reflection n (ZMod 2) i hi.1 hi.2) a = a := by
  intro i hi hin
  have hr : reflection n (ZMod 2) i hi.1 hi.2 ∈ QI n {n - 1} :=
    (reflection_mem_QI hi).2 (by simpa using hin)
  apply Multiplicative.toAdd.injective
  rw [toAdd_actDl]
  exact dual_fix_last hn hr (fix_dual_support a ha)

section

variable {G : Type} [Group G] [Finite G]

theorem exists_sylow_autOn {U L SL : Subgroup G} {n : ℕ} {ρ : SLt n →* MulAut ↥U}
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (hSyl : CFSG.QuasithinUnique.IsSylowTwoOf SL L)
    (hrange : ∀ k ∈ autOn L U, ∃ g, ρ g = k) (hrange' : ∀ g, ρ g ∈ autOn L U) :
    ∃ P : Sylow 2 ↥ρ.range, (P : Subgroup ↥ρ.range) = (autOn SL U).subgroupOf ρ.range := by
  obtain ⟨P, hP⟩ := exists_sylow_of_isSylowTwoOf hSyl
  have hmem : ∀ l : ↥L, ((conjAct U).comp (Subgroup.inclusion hLU)) l ∈ ρ.range := fun l => by
    obtain ⟨g, hg⟩ := hrange _ (mem_autOn_iff.2 ⟨l, hLU l.2, l.2, rfl⟩)
    exact ⟨g, hg⟩
  let f : ↥L →* ↥ρ.range := ((conjAct U).comp (Subgroup.inclusion hLU)).codRestrict ρ.range hmem
  have hfs : Function.Surjective f := fun k => by
    obtain ⟨g, hg⟩ := k.2
    obtain ⟨x, hx, hxL, hρ⟩ := mem_autOn_iff.1 (hrange' g)
    refine ⟨⟨x, hxL⟩, Subtype.ext ?_⟩
    show conjAct U ⟨x, hLU hxL⟩ = k
    rw [← hg, ← hρ]
  refine ⟨Sylow.mapSurjective hfs P, ?_⟩
  rw [Sylow.coe_mapSurjective hfs P, hP]
  ext ⟨k, hk⟩
  constructor
  · rintro ⟨l, hl, hlk⟩
    have : conjAct U ⟨l, hLU l.2⟩ = k := congrArg Subtype.val hlk
    exact mem_autOn_iff.2 ⟨l, hLU l.2, hl, this⟩
  · intro h
    obtain ⟨x, hx, hxS, hxk⟩ := mem_autOn_iff.1 h
    exact ⟨⟨x, hSyl.1 hxS⟩, hxS, Subtype.ext hxk⟩

omit [Finite G] in
theorem normQ_of_ctx {U L Q M : Subgroup G} {n : ℕ} (ρ : SLt n →* MulAut ↥U)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (hMQ : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q)
    (hML : M ≤ L) {J : Set ℕ} (hQJ : ∀ x ∈ QI n J, ρ x ∈ autOn M U) :
    ∀ x ∈ QI n J, ∀ a ∈ autOn Q U, ρ x * a * (ρ x)⁻¹ ∈ autOn Q U := by
  intro x hx a ha
  obtain ⟨m, hm, hmM, hρm⟩ := mem_autOn_iff.1 (hQJ x hx)
  obtain ⟨q, hq, hqQ, rfl⟩ := mem_autOn_iff.1 ha
  have hc : m * q * m⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normalizer (U : Set G)).mul_mem
      ((Subgroup.normalizer (U : Set G)).mul_mem (hLU (hML hmM)) hq)
      ((Subgroup.normalizer (U : Set G)).inv_mem (hLU (hML hmM)))
  rw [← hρm, conjAct_conj hm hq hc]
  exact mem_autOn_iff.2 ⟨_, hc, hMQ m hmM q hqQ, rfl⟩

omit [Finite G] in
theorem core_not_ff {U L Q M : Subgroup G} (hU : IsElemAbelian 2 U) {n : ℕ}
    (ρ : SLt n →* MulAut ↥U) (hρinj : Function.Injective ρ)
    (hLU : L ≤ Subgroup.normalizer (U : Set G))
    (hMQ : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q) (hML : M ≤ L) {I : Set ℕ}
    (hQI : ∀ x ∈ QI n I, ρ x ∈ autOn M U) (hQU : autOn Q U ≤ (Ut n).map ρ)
    (hmod : ∀ A'' : Subgroup (SLt n), A'' ≤ Ut n →
      (∀ y ∈ A'', ∀ i j : Fin n, i < j → (∀ d ∈ I, (i : ℕ) < d → (j : ℕ) < d) → mat y i j = 0) →
      A'' ≠ ⊥ → Nat.card (A''.map ρ) * Nat.card (@fixV ↥U (commGroupOfElemAbelian hU) (A''.map ρ)) <
        Nat.card ↥U)
    {A : Subgroup (MulAut ↥U)} (hAQ : A ≤ autOn Q U) (hA : A ≠ ⊥) :
    Nat.card A * Nat.card (@fixV ↥U (commGroupOfElemAbelian hU) A) < Nat.card ↥U := by
  let _ : CommGroup ↥U := commGroupOfElemAbelian hU
  exact not_ff_of_radical hρinj hQU (normQ_of_ctx ρ hLU hMQ hML hQI) hmod hAQ hA

omit [Finite G] in
theorem core_not_ff_asym {U L S Z₂ Q M : Subgroup G} (hU : IsElemAbelian 2 U) {n : ℕ} (hn : 3 ≤ n)
    (ρ : SLt n →* MulAut ↥U) (hρinj : Function.Injective ρ)
    (hLU : L ≤ Subgroup.normalizer (U : Set G)) (hSL : ∀ s ∈ S, ∀ l ∈ L, s * l * s⁻¹ ∈ L)
    (hgen : U ≤ conjClosure Z₂ L) (hZ₂ : Z₂ ≤ U) (hSZ : ∀ s ∈ S, ∀ z ∈ Z₂, s * z * s⁻¹ = z)
    (hS2 : IsPGroup 2 S) (hQS : Q ≤ S) (hMQ : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q) (hML : M ≤ L)
    (hrange : ∀ k ∈ autOn L U, ∃ g, ρ g = k) (hrange' : ∀ g, ρ g ∈ autOn L U)
    (hT : ∀ u ∈ Ut n, ρ u ∈ autOn (S ⊓ L) U) {I I' : Set ℕ} (hII' : I ⊆ I')
    (hI' : ∀ i ∈ I', IsNode n i) (hasym : ∃ i ∈ I', n - i ∉ I')
    (hQI : ∀ x ∈ QI n I, ρ x ∈ autOn M U)
    (hmod : ∀ A'' : Subgroup (SLt n), A'' ≤ Ut n →
      (∀ y ∈ A'', ∀ i j : Fin n, i < j → (∀ d ∈ I, (i : ℕ) < d → (j : ℕ) < d) → mat y i j = 0) →
      A'' ≠ ⊥ → Nat.card (A''.map ρ) * Nat.card (@fixV ↥U (commGroupOfElemAbelian hU) (A''.map ρ)) <
        Nat.card ↥U)
    {A : Subgroup (MulAut ↥U)} (hAQ : A ≤ autOn Q U) (hA : A ≠ ⊥) :
    Nat.card A * Nat.card (@fixV ↥U (commGroupOfElemAbelian hU) A) < Nat.card ↥U := by
  let _ : CommGroup ↥U := commGroupOfElemAbelian hU
  have hst := stSetting_ctx hU ρ hρinj hLU hSL hgen hZ₂ hSZ hS2 hrange hrange'
    (fun u hu => autOn_mono' (inf_le_left : S ⊓ L ≤ S) (hT u hu))
  have hQI' : ∀ x ∈ QI n I', ρ x ∈ autOn M U := fun x hx =>
    hQI x (((QI_le_QI_iff (fun j hj => hI' j (hII' hj))).2 hII') hx)
  have hQU : autOn Q U ≤ (Ut n).map ρ :=
    StSetting.Q_le_rhoUt hst hn (autOn_mono' hQS) hI' hasym (normQ_of_ctx ρ hLU hMQ hML hQI')
  exact core_not_ff hU ρ hρinj hLU hMQ hML hQI hQU hmod hAQ hA

end

end CFSG.Quasithin.FLc
