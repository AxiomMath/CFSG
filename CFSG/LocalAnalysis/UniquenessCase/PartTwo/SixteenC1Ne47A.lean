module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Bot47HvA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_inCalV0_of_sect16 {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hne : V₀ ≠ ⊥) : InCalV0 D.M V₀ V := by
  rcases hS.setting.hyp151.hyp125.1 with ⟨-, hbot⟩ | h2
  · exact absurd hbot hne
  · exact h2.1

theorem s16c1_ti_V₀ {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hne : V₀ ≠ ⊥) :
    ∀ y : G, V₀ ⊓ conjSubgroup V₀ y ≠ ⊥ → conjSubgroup V₀ y = V₀ := by
  have h0 := s16c1_inCalV0_of_sect16 hS hne
  intro y hy
  rcases h0.2.2.2.1 y⁻¹ with h1 | h1
  · exact absurd h1 hy
  · have h2 : V₀ ≤ conjSubgroup V₀ y := by
      intro x hx
      have hx1 : x ∈ V₀ ⊓ CFSG.CGT.Timmesfeld75.conjSubgroup y⁻¹ V₀ := by
        rw [h1]
        exact hx
      have hx2 : x ∈ CFSG.CGT.Timmesfeld75.conjSubgroup y⁻¹ V₀ := hx1.2
      have hx3 : x ∈ V₀.map (MulAut.conj (y⁻¹)).toMonoidHom := by
        simpa [CFSG.CGT.Timmesfeld75.conjSubgroup] using hx2
      simpa [CFSG.Quasithin.conjSubgroup] using hx3
    have hcard : Nat.card ↥(conjSubgroup V₀ y) = Nat.card ↥V₀ := by
      rw [CFSG.Quasithin.conjSubgroup]
      exact Subgroup.card_map_of_injective (MulAut.conj y⁻¹).injective
    exact (Subgroup.eq_of_le_of_card_ge h2 hcard.le).symm

theorem s16c1_card_V_eq_two_mul_uOne {V : Subgroup G} {z : G} (hV : IsElemAbelian 2 V)
    (hz : z ∈ V) (h47 : Concl1647 V z) : Nat.card ↥V = 2 * Nat.card ↥(uOne V z) := by
  have h := s16c1_card_starImg_mul_card_uOne hV hz
  rw [h47.1] at h
  omega

theorem s16c1_hConjClosure_le_pCoreOf {z : G} {A : Subgroup G}
    (hA : A ≤ pCoreOf 2 (centralizer ({z} : Set G))) :
    hConjClosure z A ≤ pCoreOf 2 (centralizer ({z} : Set G)) := by
  rw [hConjClosure]
  apply iSup_le
  intro h
  calc conjSubgroup A (h : G)
      ≤ conjSubgroup (pCoreOf 2 (centralizer ({z} : Set G))) (h : G) := Subgroup.map_mono hA
    _ = pCoreOf 2 (centralizer ({z} : Set G)) :=
        s16c1_conjSubgroup_pCoreOf_self (centralizer ({z} : Set G)) h.2

theorem s16c1_hConjClosure_le_centralizer {z : G} {A Q : Subgroup G}
    (hQ : ∀ h ∈ centralizer ({z} : Set G), conjSubgroup Q h = Q)
    (hA : A ≤ centralizer (Q : Set G)) :
    hConjClosure z A ≤ centralizer (Q : Set G) := by
  rw [hConjClosure]
  apply iSup_le
  intro h
  calc conjSubgroup A (h : G)
      ≤ conjSubgroup (centralizer (Q : Set G)) (h : G) := Subgroup.map_mono hA
    _ = centralizer (conjSubgroup Q (h : G) : Set G) := E3.conjSubgroup_centralizer Q (h : G)
    _ = centralizer (Q : Set G) := by rw [hQ h h.2]

theorem s16c1_eTwo_le_pCoreOf (D : Data G) {V₀ : Subgroup G} {z : G}
    (hC : V₀ ⊓ centralizer ((D.T ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) ≤
      pCoreOf 2 (centralizer ({z} : Set G))) :
    eTwo D V₀ z ≤ pCoreOf 2 (centralizer ({z} : Set G)) :=
  s16c1_hConjClosure_le_pCoreOf hC

theorem s16c1_eTwo_le_centralizer (D : Data G) {V₀ : Subgroup G} {z : G}
    (hSyl : IsSylowIn 2 (D.T ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G))) :
    eTwo D V₀ z ≤ centralizer (pCoreOf 2 (centralizer ({z} : Set G)) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQS : pCoreOf 2 (centralizer ({z} : Set G)) ≤ D.T ⊓ centralizer ({z} : Set G) :=
    CFSG.Quasithin.pCoreOf_le_of_isSylowIn hSyl
  refine s16c1_hConjClosure_le_centralizer
    (fun h hh => s16c1_conjSubgroup_pCoreOf_self _ hh) ?_
  exact inf_le_right.trans (Subgroup.centralizer_le hQS)

theorem s16c1_phi_eTwo (D : Data G) {V₀ : Subgroup G} (hV₀ : IsElemAbelian 2 V₀) {z : G}
    (hSyl : IsSylowIn 2 (D.T ⊓ centralizer ({z} : Set G)) (centralizer ({z} : Set G)))
    (hC : V₀ ⊓ centralizer ((D.T ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G) ≤
      pCoreOf 2 (centralizer ({z} : Set G))) :
    ⁅eTwo D V₀ z, eTwo D V₀ z⁆ = ⊥ ∧ ∀ e ∈ eTwo D V₀ z, e ^ 2 = 1 := by
  let H := centralizer ({z} : Set G)
  let C : Subgroup G := V₀ ⊓ centralizer ((D.T ⊓ H : Subgroup G) : Set G)
  let T : Set G := ⋃ h : ↥H, (conjSubgroup C h : Set G)
  have hE_Q : eTwo D V₀ z ≤ pCoreOf 2 H := s16c1_eTwo_le_pCoreOf D hC
  have hE_cent : eTwo D V₀ z ≤ centralizer (pCoreOf 2 H : Set G) :=
    s16c1_eTwo_le_centralizer D hSyl
  have hcommE : ⁅eTwo D V₀ z, eTwo D V₀ z⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (hE_cent.trans (Subgroup.centralizer_le hE_Q))
  have hX : Subgroup.closure T = eTwo D V₀ z := by
    show Subgroup.closure (⋃ h : ↥H, (conjSubgroup C h : Set G)) = eTwo D V₀ z
    rw [eTwo, hConjClosure]
    exact (Subgroup.iSup_eq_closure (fun h : ↥H => conjSubgroup C h)).symm
  have hTE : T ⊆ (eTwo D V₀ z : Set G) := by rw [← hX]; exact Subgroup.subset_closure
  have hZ : ∀ c ∈ (⊥ : Subgroup G), ∀ x ∈ eTwo D V₀ z, c * x = x * c :=
    fun c hc x _ => by rw [Subgroup.mem_bot] at hc; rw [hc, one_mul, mul_one]
  have hcomm : ∀ a ∈ T, ∀ b ∈ T, ⁅a, b⁆ ∈ (⊥ : Subgroup G) := by
    intro a ha b hb
    rw [← hcommE]
    exact Subgroup.commutator_mem_commutator (hTE ha) (hTE hb)
  have hsq : ∀ a ∈ T, a ^ 2 ∈ (⊥ : Subgroup G) := by
    intro a ha
    rw [Set.mem_iUnion] at ha
    obtain ⟨h, hh⟩ := ha
    have hhaV : (h : G) * a * (h : G)⁻¹ ∈ V₀ := (mem_conjSubgroup_iff.mp hh).1
    have hsq1 : ((h : G) * a * (h : G)⁻¹) ^ 2 = 1 := hV₀.2 _ hhaV
    have hconj : ((h : G) * a * (h : G)⁻¹) ^ 2 = (h : G) * a ^ 2 * (h : G)⁻¹ := by
      rw [show (h : G) * a * (h : G)⁻¹ = MulAut.conj (h : G) a by
        simp [MulAut.conj_apply]]
      rw [← map_pow (MulAut.conj (h : G)) a 2]
      simp [MulAut.conj_apply]
    rw [Subgroup.mem_bot]
    rw [show a ^ 2 = (h : G)⁻¹ * ((h : G) * a * (h : G)⁻¹) ^ 2 * (h : G) by
      rw [hconj]; group, hsq1]
    simp
  obtain ⟨hcomm_bot, hsq_bot⟩ :=
    s16c1_closure_comm_sq (X := eTwo D V₀ z) (Z := ⊥) (T := T) hX hZ hcomm hsq
  exact ⟨le_bot_iff.mp hcomm_bot, fun e he => Subgroup.mem_bot.mp (hsq_bot e he)⟩

theorem s16c1_ti_uTwo (D : Data G) {V₀ : Subgroup G} {z : G}
    (hTI : ∀ y : G, V₀ ⊓ conjSubgroup V₀ y ≠ ⊥ → conjSubgroup V₀ y = V₀) :
    ∀ h ∈ centralizer ({z} : Set G),
      conjSubgroup (uTwo D V₀ z) h = uTwo D V₀ z ∨
        uTwo D V₀ z ⊓ conjSubgroup (uTwo D V₀ z) h = ⊥ := by
  intro h hh
  by_cases hbot : uTwo D V₀ z ⊓ conjSubgroup (uTwo D V₀ z) h = ⊥
  · exact Or.inr hbot
  · left
    have hU_le : uTwo D V₀ z ≤ V₀ := inf_le_left
    have hle : uTwo D V₀ z ⊓ conjSubgroup (uTwo D V₀ z) h ≤ V₀ ⊓ conjSubgroup V₀ h :=
      le_inf (inf_le_left.trans hU_le) (inf_le_right.trans (E3.conjSubgroup_mono_left h hU_le))
    have hV₀ne : V₀ ⊓ conjSubgroup V₀ h ≠ ⊥ := by
      intro hzero
      exact hbot (le_bot_iff.mp (hle.trans (le_of_eq hzero)))
    have hV₀eq : conjSubgroup V₀ h = V₀ := hTI h hV₀ne
    have hEeq : conjSubgroup (eTwo D V₀ z) h = eTwo D V₀ z := by
      simpa only [eTwo] using
        (s16c1_conjSubgroup_hConjClosure (z := z)
          (A := V₀ ⊓ centralizer ((D.T ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G)) hh)
    rw [uTwo, E3.conjSubgroup_inf, hV₀eq, hEeq]

theorem s16c1_comm_V_eTwo_le_uTwo (D : Data G) {V₀ V : Subgroup G} {z : G}
    (hV : IsElemAbelian 2 V) (hz : z ∈ V) (hM : D.M ≤ normalizer (V : Set G))
    (hM₀ : D.M ≤ normalizer (V₀ : Set G))
    (hEC : eTwo D V₀ z ≤ F11.CTilde D.M V₀ V) :
    ⁅V, eTwo D V₀ z⁆ ≤ uTwo D V₀ z := by
  rw [Subgroup.commutator_le]
  intro v hv e he
  have hvH : v ∈ centralizer ({z} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hz)
      ((Subgroup.le_centralizer_iff_isMulCommutative.mpr hV.1) hv)
  have hEeq : conjSubgroup (eTwo D V₀ z) v = eTwo D V₀ z := by
    simpa only [eTwo] using
      (s16c1_conjSubgroup_hConjClosure (z := z)
        (A := V₀ ⊓ centralizer ((D.T ⊓ centralizer ({z} : Set G) : Subgroup G) : Set G)) hvH)
  rw [uTwo, Subgroup.mem_inf]
  constructor
  · have hcmod : CentralizesMod V₀ V e :=
      CFSG.LocalAnalysis.WeakClosure81.centralizesMod_of_mem_cTilde hV hM hM₀ (hEC he)
    have hmem : e * v * e⁻¹ * v⁻¹ ∈ V₀ := hcmod v hv
    have hcomm : ⁅v, e⁆ = (e * v * e⁻¹ * v⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [hcomm]
    exact V₀.inv_mem hmem
  · have hve : v * e * v⁻¹ ∈ eTwo D V₀ z := by
      have : e ∈ conjSubgroup (eTwo D V₀ z) v := by rw [hEeq]; exact he
      exact mem_conjSubgroup_iff.mp this
    have hcomm : ⁅v, e⁆ = (v * e * v⁻¹) * e⁻¹ := by rw [commutatorElement_def]
    rw [hcomm]
    exact (eTwo D V₀ z).mul_mem hve ((eTwo D V₀ z).inv_mem he)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
