module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4V1Cex

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary (SUid)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s16c4v1_r2_eq_r1_inv (V : Subgroup G) (g : G) :
    s16c4v1_r2 V g = s16c4v1_r1 V g⁻¹ := by
  unfold s16c4v1_r2 s16c4v1_r1
  rw [← E3.mQuot_conjSubgroup V (Subgroup.centralizer (conjSubgroup V g⁻¹ : Set G)) g]
  congr 1
  rw [E3.conjSubgroup_centralizer, E3.conjSubgroup_inv_conj]

theorem s16c4v1_card_comm_inv (V : Subgroup G) (g : G) :
    Nat.card (⁅V, conjSubgroup V g⁻¹⁆ : Subgroup G) =
      Nat.card (⁅V, conjSubgroup V g⁆ : Subgroup G) := by
  have h : (⁅V, conjSubgroup V g⁻¹⁆ : Subgroup G) =
      conjSubgroup (⁅V, conjSubgroup V g⁆ : Subgroup G) g⁻¹ := by
    rw [E3.conjSubgroup_commutator, E3.conjSubgroup_conj_inv]
    exact Subgroup.commutator_comm V (conjSubgroup V g⁻¹)
  rw [h, E3.card_conjSubgroup]

private theorem s16c4v1_shp_inv_mul_mem_of_relIndex_le_two {H K : Subgroup G}
    (hle : H.relIndex K ≤ 2) {x y : G} (hx : x ∈ K) (hy : y ∈ K)
    (hxH : x ∉ H) (hyH : y ∉ H) : x⁻¹ * y ∈ H := by
  have h0 : H.relIndex K ≠ 0 := E3.relIndex_ne_zero' K H
  have hne : H.relIndex K ≠ 1 := fun h1 => hxH (Subgroup.relIndex_eq_one.1 h1 hx)
  have h2 : H.relIndex K = 2 := by omega
  obtain ⟨a, haK, haH, ha⟩ := Subgroup.relIndex_eq_two_iff_exists_notMem_and'.1 h2
  rcases ha x hx with h | h
  · rcases ha y hy with h' | h'
    · have hmem : (a * x)⁻¹ * (a * y) ∈ H := H.mul_mem (H.inv_mem h) h'
      simpa [mul_assoc] using hmem
    · exact absurd h' hyH
  · exact absurd h hxH

private theorem s16c4v1_shp_comm_eq_of_relIndex {V A : Subgroup G}
    (hV : IsElemAbelian 2 V) (hA : IsElemAbelian 2 A)
    (hVA : ⁅V, A⁆ ≤ V ⊓ A)
    (h1 : E3.mQuot V (Subgroup.centralizer (A : Set G)) ≤ 1)
    (h2 : E3.mQuot A (Subgroup.centralizer (V : Set G)) ≤ 1)
    {v v₀ a a₀ : G} (hv : v ∈ V) (hv₀ : v₀ ∈ V) (ha : a ∈ A) (ha₀ : a₀ ∈ A)
    (hne : ⁅v, a⁆ ≠ 1) (hne₀ : ⁅v₀, a₀⁆ ≠ 1) :
    ⁅v, a⁆ = ⁅v₀, a₀⁆ := by
  set CV : Subgroup G := V ⊓ Subgroup.centralizer (A : Set G) with hCV
  set CA : Subgroup G := A ⊓ Subgroup.centralizer (V : Set G) with hCA
  have hCVrel : CV.relIndex V ≤ 2 := by
    have hrel := E3.relIndex_eq_two_pow hV.isPGroup (Subgroup.centralizer (A : Set G))
    have hle : (Subgroup.centralizer (A : Set G)).relIndex V ≤ 2 := by
      rw [hrel]
      calc 2 ^ E3.mQuot V (Subgroup.centralizer (A : Set G)) ≤ 2 ^ 1 :=
            Nat.pow_le_pow_right (by norm_num) h1
        _ = 2 := by norm_num
    rw [hCV, Subgroup.inf_relIndex_left]
    exact hle
  have hCArel : CA.relIndex A ≤ 2 := by
    have hrel := E3.relIndex_eq_two_pow hA.isPGroup (Subgroup.centralizer (V : Set G))
    have hle : (Subgroup.centralizer (V : Set G)).relIndex A ≤ 2 := by
      rw [hrel]
      calc 2 ^ E3.mQuot A (Subgroup.centralizer (V : Set G)) ≤ 2 ^ 1 :=
            Nat.pow_le_pow_right (by norm_num) h2
        _ = 2 := by norm_num
    rw [hCA, Subgroup.inf_relIndex_left]
    exact hle
  have hvCV : v ∉ CV := by
    intro hmem
    rw [hCV] at hmem
    obtain ⟨-, hcent⟩ := Subgroup.mem_inf.1 hmem
    exact hne (by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.1 hcent a ha).symm)
  have hv₀CV : v₀ ∉ CV := by
    intro hmem
    rw [hCV] at hmem
    obtain ⟨-, hcent⟩ := Subgroup.mem_inf.1 hmem
    exact hne₀ (by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_centralizer_iff.1 hcent a₀ ha₀).symm)
  have haCA : a ∉ CA := by
    intro hmem
    rw [hCA] at hmem
    obtain ⟨-, hcent⟩ := Subgroup.mem_inf.1 hmem
    exact hne (by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_iff.1 hcent v hv)
  have ha₀CA : a₀ ∉ CA := by
    intro hmem
    rw [hCA] at hmem
    obtain ⟨-, hcent⟩ := Subgroup.mem_inf.1 hmem
    exact hne₀ (by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact Subgroup.mem_centralizer_iff.1 hcent v₀ hv₀)
  have hcV : v⁻¹ * v₀ ∈ CV :=
    s16c4v1_shp_inv_mul_mem_of_relIndex_le_two hCVrel hv hv₀ hvCV hv₀CV
  have hcA : a⁻¹ * a₀ ∈ CA :=
    s16c4v1_shp_inv_mul_mem_of_relIndex_le_two hCArel ha ha₀ haCA ha₀CA
  obtain ⟨-, hcVcent⟩ := Subgroup.mem_inf.1 hcV
  obtain ⟨hcAc, hcAcent⟩ := Subgroup.mem_inf.1 hcA
  have hccomm : ⁅v⁻¹ * v₀, a * (a⁻¹ * a₀)⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    have h1 : Commute (v⁻¹ * v₀) a := (Subgroup.mem_centralizer_iff.1 hcVcent a ha).symm
    have h2 : Commute (v⁻¹ * v₀) (a⁻¹ * a₀) :=
      (Subgroup.mem_centralizer_iff.1 hcVcent (a⁻¹ * a₀) hcAc).symm
    exact (h1.mul_right h2).eq
  have hvc' : ⁅v, a⁻¹ * a₀⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subgroup.mem_centralizer_iff.1 hcAcent v hv
  have hmain : ⁅v * (v⁻¹ * v₀), a * (a⁻¹ * a₀)⁆ = ⁅v, a⁆ := by
    rw [commutatorElement_mul_left_eq_conj_mul, hccomm]
    rw [commutatorElement_mul_right_eq_mul_conj, hvc']
    group
  have hv₀eq : v₀ = v * (v⁻¹ * v₀) := by group
  have ha₀eq : a₀ = a * (a⁻¹ * a₀) := by group
  rw [hv₀eq, ha₀eq]
  exact hmain.symm

private theorem s16c4v1_shp_comm_const {V A : Subgroup G}
    (hV : IsElemAbelian 2 V) (hA : IsElemAbelian 2 A)
    (hVA : ⁅V, A⁆ ≤ V ⊓ A)
    (h1 : E3.mQuot V (Subgroup.centralizer (A : Set G)) ≤ 1)
    (h2 : E3.mQuot A (Subgroup.centralizer (V : Set G)) ≤ 1) :
    ∃ e : G, e ^ 2 = 1 ∧ ⁅V, A⁆ ≤ Subgroup.zpowers e := by
  by_cases hbot : ⁅V, A⁆ = ⊥
  · exact ⟨1, one_pow 2, by rw [hbot]; exact bot_le⟩
  · have hgen : ∃ v ∈ V, ∃ a ∈ A, ⁅v, a⁆ ≠ 1 := by
      by_contra hcon
      have h : ∀ v ∈ V, ∀ a ∈ A, ⁅v, a⁆ = 1 := by
        intro v hv a ha
        by_contra hne
        exact hcon ⟨v, hv, a, ha, hne⟩
      apply hbot
      rw [Subgroup.commutator_def]
      refine le_antisymm ?_ bot_le
      rw [Subgroup.closure_le]
      rintro g ⟨v, hv, a, ha, rfl⟩
      simpa using h v hv a ha
    obtain ⟨v₀, hv₀, a₀, ha₀, hne₀⟩ := hgen
    refine ⟨⁅v₀, a₀⁆, ?_, ?_⟩
    · have heV : ⁅v₀, a₀⁆ ∈ V :=
        (Subgroup.mem_inf.1 (hVA (Subgroup.commutator_mem_commutator hv₀ ha₀))).1
      simpa using hV.2 ⁅v₀, a₀⁆ heV
    · refine Subgroup.commutator_le.mpr ?_
      intro v hv a ha
      by_cases hva : ⁅v, a⁆ = 1
      · rw [hva]
        exact Subgroup.one_mem (Subgroup.zpowers ⁅v₀, a₀⁆)
      · rw [s16c4v1_shp_comm_eq_of_relIndex hV hA hVA h1 h2 hv hv₀ ha ha₀ hva hne₀]
        exact Subgroup.mem_zpowers ⁅v₀, a₀⁆

theorem s16c4v1_pairing_le {V A : Subgroup G} (hV : IsElemAbelian 2 V) (hA : IsElemAbelian 2 A)
    (hVA : ⁅V, A⁆ ≤ V ⊓ A) (h1 : E3.mQuot V (Subgroup.centralizer (A : Set G)) ≤ 1)
    (h2 : E3.mQuot A (Subgroup.centralizer (V : Set G)) ≤ 1) :
    Nat.card (⁅V, A⁆ : Subgroup G) ≤ 2 := by
  obtain ⟨e, he2, hle⟩ := s16c4v1_shp_comm_const hV hA hVA h1 h2
  calc Nat.card (⁅V, A⁆ : Subgroup G) ≤ Nat.card (Subgroup.zpowers e) :=
        Subgroup.card_le_of_le hle
    _ = orderOf e := Nat.card_zpowers e
    _ ≤ 2 := Nat.le_of_dvd (by norm_num) (orderOf_dvd_iff_pow_eq_one.mpr he2)


private theorem s16c4v1_shp_vec_inv (S : s16c4v1_Sit D V L hV) {v : G} (hv : v ∈ V) :
    s16c4v1_vec S v⁻¹ = - s16c4v1_vec S v := by
  have h := s16c4v1_vec_mul S hv (V.inv_mem hv)
  rw [mul_inv_cancel, s16c4v1_vec_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

private theorem s16c4v1_shp_vec_comm (S : s16c4v1_Sit D V L hV) {g : G}
    (hg : s16c4v1_Cex D V g) (φ : ↥(conjSubgroup V g) →* ↥(SUid S.F.σ 4))
    (hφ : ∀ a : ↥(conjSubgroup V g), s16c4v1_Induces S (a : G) (φ a))
    (a : ↥(conjSubgroup V g)) {v : G} (hv : v ∈ V) :
    s16c4v1_vec S ((a : G) * v * (a : G)⁻¹ * v⁻¹) =
      (φ a) • s16c4v1_vec S v - s16c4v1_vec S v := by
  have haM : (a : G) ∈ D.M := hg.1 a.2
  have hav : (a : G) * v * (a : G)⁻¹ ∈ V := s16c4v1_conj_mem S haM hv
  rw [s16c4v1_vec_mul S hav (V.inv_mem hv), hφ a v hv,
    s16c4v1_shp_vec_inv S hv, sub_eq_add_neg]

private theorem s16c4v1_shp_sub_mem (S : s16c4v1_Sit D V L hV) {g : G}
    (hg : s16c4v1_Cex D V g) (P : Submodule S.F.K (Fin 4 → S.F.K))
    (hPD : ∀ d ∈ ⁅V, conjSubgroup V g⁆, s16c4v1_vec S d ∈ P)
    (φ : ↥(conjSubgroup V g) →* ↥(SUid S.F.σ 4))
    (hφ : ∀ a : ↥(conjSubgroup V g), s16c4v1_Induces S (a : G) (φ a)) :
    ∀ a : ↥(conjSubgroup V g), ∀ x : Fin 4 → S.F.K,
      (φ a) • x - x ∈ P := by
  intro a x
  obtain ⟨v, hv, rfl⟩ := s16c4v1_exists_vec S x
  have hd : (a : G) * v * (a : G)⁻¹ * v⁻¹ ∈ ⁅V, conjSubgroup V g⁆ := by
    have hmem : (a : G) * v * (a : G)⁻¹ * v⁻¹ ∈ ⁅conjSubgroup V g, V⁆ :=
      Subgroup.commutator_mem_commutator a.2 hv
    rwa [Subgroup.commutator_comm] at hmem
  rw [← s16c4v1_shp_vec_comm S hg φ hφ a hv]
  exact hPD _ hd

private theorem s16c4v1_shp_fix_P (S : s16c4v1_Sit D V L hV) {g : G}
    (hg : s16c4v1_Cex D V g) (P : Submodule S.F.K (Fin 4 → S.F.K))
    (hPD : ∀ d ∈ ⁅V, conjSubgroup V g⁆, s16c4v1_vec S d ∈ P)
    (hPtot : ∀ x ∈ P, ∀ y ∈ P, herm S.F.σ x y = 0)
    (φ : ↥(conjSubgroup V g) →* ↥(SUid S.F.σ 4))
    (hφ : ∀ a : ↥(conjSubgroup V g), s16c4v1_Induces S (a : G) (φ a))
    (a : ↥(conjSubgroup V g)) {x : Fin 4 → S.F.K} (hx : x ∈ P) :
    (φ a) • x = x := by
  have hzero : ∀ y : Fin 4 → S.F.K, herm S.F.σ y ((φ a) • x - x) = 0 := by
    intro y
    set q : Fin 4 → S.F.K := (φ a) • y - y with hqdef
    set p : Fin 4 → S.F.K := (φ a) • x - x with hpdef
    have hq : q ∈ P := by rw [hqdef]; exact s16c4v1_shp_sub_mem S hg P hPD φ hφ a y
    have hp : p ∈ P := by rw [hpdef]; exact s16c4v1_shp_sub_mem S hg P hPD φ hφ a x
    have h1 := herm_smul_smul S.F.σ (φ a) y x
    have hy : (φ a) • y = y + q := by rw [hqdef]; abel
    have hxp : (φ a) • x = x + p := by rw [hpdef]; abel
    rw [hy, hxp] at h1
    simp only [herm_add_left, herm_add_right, hPtot q hq x hx, hPtot q hq p hp,
      add_zero, zero_add] at h1
    have hA : herm S.F.σ y x + herm S.F.σ y p = herm S.F.σ y x + 0 := by
      rw [add_zero]; exact h1
    have hz := add_left_cancel hA
    rw [hpdef] at hz
    exact hz
  ext i
  have hi := hzero (Pi.single i 1)
  rw [herm_single_left] at hi
  have hpi : ((φ a) • x - x) i = 0 := by simpa using hi
  simpa [Pi.sub_apply, sub_eq_zero] using hpi

private theorem s16c4v1_shp_cent_of_mem_P (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D)
    {g : G} (hg : s16c4v1_Cex D V g) (hg' : s16c4v1_Cex D V g⁻¹)
    (P : Submodule S.F.K (Fin 4 → S.F.K))
    (hPD : ∀ d ∈ ⁅V, conjSubgroup V g⁆, s16c4v1_vec S d ∈ P)
    (hPtot : ∀ x ∈ P, ∀ y ∈ P, herm S.F.σ x y = 0)
    (φ : ↥(conjSubgroup V g) →* ↥(SUid S.F.σ 4))
    (hφ : ∀ a : ↥(conjSubgroup V g), s16c4v1_Induces S (a : G) (φ a))
    {v : G} (hv : v ∈ V) (hxv : s16c4v1_vec S v ∈ P) :
    ∀ a ∈ conjSubgroup V g, a * v * a⁻¹ = v := by
  intro a ha
  let aa : ↥(conjSubgroup V g) := ⟨a, ha⟩
  have hfix : (φ aa) • s16c4v1_vec S v = s16c4v1_vec S v :=
    s16c4v1_shp_fix_P S hg P hPD hPtot φ hφ aa hxv
  have hd : a * v * a⁻¹ * v⁻¹ ∈ ⁅V, conjSubgroup V g⁆ := by
    have hmem : a * v * a⁻¹ * v⁻¹ ∈ ⁅conjSubgroup V g, V⁆ :=
      Subgroup.commutator_mem_commutator ha hv
    rwa [Subgroup.commutator_comm] at hmem
  have hvec : s16c4v1_vec S (a * v * a⁻¹ * v⁻¹) = 0 := by
    rw [s16c4v1_shp_vec_comm S hg φ hφ aa hv, hfix, sub_self]
  have hd1 : a * v * a⁻¹ * v⁻¹ = 1 := by
    by_contra hne
    exact (s16c4v1_cex_D_sing S hstd hg hg' _ hd hne).1 hvec
  exact mul_inv_eq_one.1 hd1

private theorem s16c4v1_shp_mem_P_of_cent (S : s16c4v1_Sit D V L hV) {g : G}
    (hg : s16c4v1_Cex D V g) (hg' : s16c4v1_Cex D V g⁻¹)
    (P : Submodule S.F.K (Fin 4 → S.F.K))
    (hPD : ∀ d ∈ ⁅V, conjSubgroup V g⁆, s16c4v1_vec S d ∈ P)
    (hPsurj : ∀ x ∈ P, ∃ d ∈ ⁅V, conjSubgroup V g⁆, s16c4v1_vec S d = x)
    (hPtot : ∀ x ∈ P, ∀ y ∈ P, herm S.F.σ x y = 0)
    (hP2 : Module.finrank S.F.K P = 2)
    (φ : ↥(conjSubgroup V g) →* ↥(SUid S.F.σ 4))
    (hφ : ∀ a : ↥(conjSubgroup V g), s16c4v1_Induces S (a : G) (φ a))
    {v : G} (hv : v ∈ V) (hcent : ∀ a ∈ conjSubgroup V g, a * v * a⁻¹ = v) :
    s16c4v1_vec S v ∈ P := by
  have hfix : ∀ a : ↥(conjSubgroup V g), (φ a) • s16c4v1_vec S v = s16c4v1_vec S v := by
    intro a
    have h := hφ a v hv
    rw [hcent (a : G) a.2] at h
    exact h.symm
  have hVA : ⁅V, conjSubgroup V g⁆ ≤ V ⊓ conjSubgroup V g :=
    s16c4v1_cex_comm_le S.sect.setting.hyp16.hyp125.pairFacts.le_normalizer hg.1 hg'.1
  let Z : Subgroup ↥V :=
    { carrier := {w : ↥V | herm S.F.σ (s16c4v1_vec S (w : G)) (s16c4v1_vec S v) = 0}
      one_mem' := by
        show herm S.F.σ (s16c4v1_vec S ((1 : ↥V) : G)) (s16c4v1_vec S v) = 0
        rw [show ((1 : ↥V) : G) = (1 : G) from rfl, s16c4v1_vec_one, herm_zero_left]
      mul_mem' := by
        intro x y hx hy
        show herm S.F.σ (s16c4v1_vec S ((x * y : ↥V) : G)) (s16c4v1_vec S v) = 0
        rw [show ((x * y : ↥V) : G) = (x : G) * (y : G) from rfl,
          s16c4v1_vec_mul S x.2 y.2, herm_add_left, hx, hy, add_zero]
      inv_mem' := by
        intro x hx
        show herm S.F.σ (s16c4v1_vec S ((x⁻¹ : ↥V) : G)) (s16c4v1_vec S v) = 0
        rw [show ((x⁻¹ : ↥V) : G) = (x : G)⁻¹ from rfl,
          s16c4v1_shp_vec_inv S x.2, herm_neg_left, hx, neg_zero] }
  have hZA : ⁅conjSubgroup V g, V⁆ ≤ Z.map V.subtype := by
    refine Subgroup.commutator_le.mpr ?_
    intro a ha w hw
    have hcomV : ⁅a, w⁆ ∈ V := by
      rw [← commutatorElement_inv]
      exact V.inv_mem (Subgroup.mem_inf.1
        (hVA (Subgroup.commutator_mem_commutator hw ha))).1
    refine Subgroup.mem_map.mpr ⟨⟨⁅a, w⁆, hcomV⟩, ?_, rfl⟩
    have hvec : s16c4v1_vec S ⁅a, w⁆ =
        (φ ⟨a, ha⟩) • s16c4v1_vec S w - s16c4v1_vec S w :=
      s16c4v1_shp_vec_comm S hg φ hφ ⟨a, ha⟩ hw
    show herm S.F.σ (s16c4v1_vec S ⁅a, w⁆) (s16c4v1_vec S v) = 0
    have h1 : herm S.F.σ ((φ ⟨a, ha⟩) • s16c4v1_vec S w) (s16c4v1_vec S v) =
        herm S.F.σ (s16c4v1_vec S w) (s16c4v1_vec S v) := by
      calc herm S.F.σ ((φ ⟨a, ha⟩) • s16c4v1_vec S w) (s16c4v1_vec S v)
          = herm S.F.σ ((φ ⟨a, ha⟩) • s16c4v1_vec S w)
              ((φ ⟨a, ha⟩) • s16c4v1_vec S v) := by rw [hfix]
        _ = herm S.F.σ (s16c4v1_vec S w) (s16c4v1_vec S v) :=
              herm_smul_smul S.F.σ (φ ⟨a, ha⟩) (s16c4v1_vec S w) (s16c4v1_vec S v)
    rw [hvec, herm_sub_left, h1, sub_self]
  have hZA' : ⁅V, conjSubgroup V g⁆ ≤ Z.map V.subtype := by
    rw [Subgroup.commutator_comm]
    exact hZA
  have horth : ∀ y ∈ P, herm S.F.σ y (s16c4v1_vec S v) = 0 := by
    intro y hy
    obtain ⟨d, hd, hdy⟩ := hPsurj y hy
    obtain ⟨d', hd'Z, hd'eq⟩ := Subgroup.mem_map.mp (hZA' hd)
    have h1 : herm S.F.σ (s16c4v1_vec S (d' : G)) (s16c4v1_vec S v) = 0 := hd'Z
    rw [show (d' : G) = d from hd'eq, hdy] at h1
    exact h1
  exact s16c4v1_perp_self S.F.σ S.F.card_K S.F.isUnitary P hPtot hP2
    (s16c4v1_vec S v) horth

private theorem s16c4v1_shp_card_subgroupOf {H K : Subgroup G} (hHK : H ≤ K) :
    Nat.card (H.subgroupOf K) = Nat.card H := by
  refine Nat.card_congr ?_
  refine
    { toFun := fun x => ⟨(x : K), x.2⟩
      invFun := fun y => ⟨⟨(y : G), hHK y.2⟩, y.2⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun y => by ext; rfl }


theorem s16c4v1_shape_two (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D) {z : G}
    {ω : S.F.K} (hz : s16c4v1_ScalarOf S z ω) {g : G} (hg : s16c4v1_Cex D V g)
    (hg' : s16c4v1_Cex D V g⁻¹)
    (h4 : Nat.card (⁅V, conjSubgroup V g⁆ : Subgroup G) = 4) : s16c4v1_r2 V g ≤ 1 := by
  have haM : conjSubgroup V g ≤ D.M := hg.1
  have ha2 : IsPGroup 2 (conjSubgroup V g) := (E3.isElemAbelian_conjSubgroup hV g).isPGroup
  have ha1 : ∀ a ∈ conjSubgroup V g, ∀ x ∈ v1Sub D.M ⊥ V hV L, a * x * a⁻¹ = x :=
    s16c4v1_cex_cent_V1 S hstd hg hg'
  obtain ⟨φ, hφ, hker⟩ := s16c4v1_two_hom S hstd.r1217 hz haM ha2 ha1
  obtain ⟨P, hPD, hPsurj, hPsing, hPcard⟩ := s16c4v1_cex_D_subspace S hstd hz hg hg'
  have hPcard4 : Nat.card P = 4 := by rw [← hPcard]; exact h4
  have hpow : Nat.card P = 4 ^ Module.finrank S.F.K P := by
    rw [Module.natCard_eq_pow_finrank (K := S.F.K), S.F.card_K]
  have hP1 : Module.finrank S.F.K P = 1 := by
    have h : 4 ^ Module.finrank S.F.K P = 4 ^ 1 := by
      rw [← hpow, hPcard4]; norm_num
    exact Nat.pow_right_injective (by norm_num) h
  have hX : ∀ γ ∈ φ.range, ∀ x : Fin 4 → S.F.K, γ • x - x ∈ P := by
    rintro γ ⟨a, rfl⟩ x
    exact s16c4v1_shp_sub_mem S hg P hPD φ hφ a x
  have hcardX : Nat.card φ.range ≤ 2 :=
    s16c4v1_root_card S.F.σ S.F.card_K S.F.isUnitary P hP1 hPsing φ.range hX
  have hker_eq : φ.ker =
      (Subgroup.centralizer (V : Set G)).subgroupOf (conjSubgroup V g) := by
    ext a
    rw [MonoidHom.mem_ker, hker a, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h v hv
      exact (mul_inv_eq_iff_eq_mul.mp (h v hv)).symm
    · intro h v hv
      rw [← h v hv]
      group
  have hrel : (Subgroup.centralizer (V : Set G)).relIndex (conjSubgroup V g) =
      Nat.card φ.range := by
    show ((Subgroup.centralizer (V : Set G)).subgroupOf (conjSubgroup V g)).index =
      Nat.card φ.range
    rw [← hker_eq, Subgroup.index_ker]
  have hle2 : (Subgroup.centralizer (V : Set G)).relIndex (conjSubgroup V g) ≤ 2 := by
    rw [hrel]; exact hcardX
  have hpow2 := E3.relIndex_eq_two_pow ha2 (Subgroup.centralizer (V : Set G))
  have hpowle : 2 ^ E3.mQuot (conjSubgroup V g) (Subgroup.centralizer (V : Set G)) ≤ 2 := by
    rw [← hpow2]; exact hle2
  have hfin : E3.mQuot (conjSubgroup V g) (Subgroup.centralizer (V : Set G)) ≤ 1 :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).1 (by simpa using hpowle)
  unfold s16c4v1_r2
  exact hfin


theorem s16c4v1_shape_four (S : s16c4v1_Sit D V L hV) (hstd : s16c4v1_Std D) {z : G}
    {ω : S.F.K} (hz : s16c4v1_ScalarOf S z ω) {g : G} (hg : s16c4v1_Cex D V g)
    (hg' : s16c4v1_Cex D V g⁻¹)
    (h16 : Nat.card (⁅V, conjSubgroup V g⁆ : Subgroup G) = 16) : s16c4v1_r1 V g = 4 := by
  obtain ⟨φ, hφ, hker⟩ :=
    s16c4v1_two_hom S hstd.r1217 hz hg.1
      (E3.isElemAbelian_conjSubgroup hV g).isPGroup (s16c4v1_cex_cent_V1 S hstd hg hg')
  obtain ⟨P, hPD, hPsurj, hPsing, hPcard⟩ := s16c4v1_cex_D_subspace S hstd hz hg hg'
  have hP16 : Nat.card P = 16 := by rw [← hPcard]; exact h16
  have hpow : Nat.card P = 4 ^ Module.finrank S.F.K P := by
    rw [Module.natCard_eq_pow_finrank (K := S.F.K), S.F.card_K]
  have hP2 : Module.finrank S.F.K P = 2 := by
    have h : 4 ^ Module.finrank S.F.K P = 4 ^ 2 := by
      rw [← hpow, hP16]; norm_num
    exact Nat.pow_right_injective (by norm_num) h
  have hPtot : ∀ x ∈ P, ∀ y ∈ P, herm S.F.σ x y = 0 :=
    (s16c4v1_isotropic S.F.σ S.F.card_K S.F.isUnitary P hPsing).1
  let W : Subgroup G := V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G)
  have hWV : W ≤ V := inf_le_left
  have hcentP : ∀ v ∈ V, s16c4v1_vec S v ∈ P → v ∈ W := by
    intro v hv hvP
    refine Subgroup.mem_inf.mpr ⟨hv, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact mul_inv_eq_iff_eq_mul.mp
      (s16c4v1_shp_cent_of_mem_P S hstd hg hg' P hPD hPtot φ hφ hv hvP a ha)
  have hPcent : ∀ v ∈ V, v ∈ W → s16c4v1_vec S v ∈ P := by
    intro v hv hvW
    exact s16c4v1_shp_mem_P_of_cent S hg hg' P hPD hPsurj hPtot hP2 φ hφ hv
      (fun a ha => by
        rw [Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hvW).2 a ha]
        group)
  have hWP : ∀ v ∈ V, (v ∈ W ↔ s16c4v1_vec S v ∈ P) :=
    fun v hv => ⟨hPcent v hv, hcentP v hv⟩
  have hVA : ⁅V, conjSubgroup V g⁆ ≤ V ⊓ conjSubgroup V g :=
    s16c4v1_cex_comm_le S.sect.setting.hyp16.hyp125.pairFacts.le_normalizer hg.1 hg'.1
  let ψ : ↥V →* Multiplicative (Fin 4 → S.F.K) :=
    { toFun := fun w => Multiplicative.ofAdd (s16c4v1_vec S (w : G))
      map_one' := by
        show Multiplicative.ofAdd (s16c4v1_vec S ((1 : ↥V) : G)) = 1
        rw [show ((1 : ↥V) : G) = (1 : G) from rfl, s16c4v1_vec_one]
        rfl
      map_mul' := by
        intro x y
        show Multiplicative.ofAdd (s16c4v1_vec S ((x * y : ↥V) : G)) =
          Multiplicative.ofAdd (s16c4v1_vec S (x : G)) *
            Multiplicative.ofAdd (s16c4v1_vec S (y : G))
        rw [show ((x * y : ↥V) : G) = (x : G) * (y : G) from rfl,
          s16c4v1_vec_mul S x.2 y.2]
        rfl }
  have hkerψ : ψ.ker = (v1Sub D.M ⊥ V hV L).subgroupOf V := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd (s16c4v1_vec S (w : G)) = 1 ↔
      (w : G) ∈ v1Sub D.M ⊥ V hV L
    rw [ofAdd_eq_one]
    exact s16c4v1_vec_eq_zero_iff S w.2
  let ψW : ↥W →* Multiplicative (Fin 4 → S.F.K) := ψ.comp (Subgroup.inclusion hWV)
  have hkerW : ψW.ker = (v1Sub D.M ⊥ V hV L).subgroupOf W := by
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd (s16c4v1_vec S (w : G)) = 1 ↔
      (w : G) ∈ v1Sub D.M ⊥ V hV L
    rw [ofAdd_eq_one]
    exact s16c4v1_vec_eq_zero_iff S (hWV w.2)
  have hrange_eq : (ψW.range : Set (Multiplicative (Fin 4 → S.F.K))) =
      Multiplicative.ofAdd '' (P : Set (Fin 4 → S.F.K)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨w, rfl⟩ := hz
      exact ⟨s16c4v1_vec S (w : G), (hWP (w : G) (hWV w.2)).1 w.2, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨d, hd, hdy⟩ := hPsurj y hy
      have hdV : d ∈ V := (Subgroup.mem_inf.1 (hVA hd)).1
      have hdW : d ∈ W := (hWP d hdV).2 (by rw [hdy]; exact hy)
      refine MonoidHom.mem_range.mpr ⟨⟨d, hdW⟩, ?_⟩
      show Multiplicative.ofAdd (s16c4v1_vec S d) = Multiplicative.ofAdd y
      rw [hdy]
  have hcard_range : Nat.card ψW.range = Nat.card P := by
    change Nat.card (ψW.range : Set (Multiplicative (Fin 4 → S.F.K))) = Nat.card P
    rw [hrange_eq]
    exact Nat.card_image_of_injective Multiplicative.ofAdd.injective
      (P : Set (Fin 4 → S.F.K))
  have hV1W : v1Sub D.M ⊥ V hV L ≤ W := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨s16c4v1_v1_le S hx, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact mul_inv_eq_iff_eq_mul.mp
      (s16c4v1_cex_cent_V1 S hstd hg hg' a ha x hx)
  have hWcard : Nat.card W = Nat.card (v1Sub D.M ⊥ V hV L) * Nat.card P := by
    have h := Subgroup.card_ker_mul_card_range ψW
    rw [hkerW, s16c4v1_shp_card_subgroupOf hV1W, hcard_range] at h
    exact h.symm
  have hV1pos : 0 < Nat.card (v1Sub D.M ⊥ V hV L) := by
    haveI : Nonempty ↥(v1Sub D.M ⊥ V hV L) :=
      ⟨⟨1, (v1Sub D.M ⊥ V hV L).one_mem⟩⟩
    exact Nat.card_pos
  have hV1relV : (v1Sub D.M ⊥ V hV L).relIndex V = 2 ^ 8 := by
    have hmul := Subgroup.relIndex_mul_card (H := v1Sub D.M ⊥ V hV L) (K := V)
    rw [inf_eq_left.mpr (s16c4v1_v1_le S), s16c4v1_card_V S] at hmul
    exact Nat.eq_of_mul_eq_mul_right hV1pos hmul
  have hV1relW : (v1Sub D.M ⊥ V hV L).relIndex W = Nat.card P := by
    have hmul := Subgroup.relIndex_mul_card (H := v1Sub D.M ⊥ V hV L) (K := W)
    rw [inf_eq_left.mpr hV1W, hWcard,
      mul_comm (Nat.card (v1Sub D.M ⊥ V hV L)) (Nat.card P)] at hmul
    exact Nat.eq_of_mul_eq_mul_right hV1pos hmul
  have hWrel : W.relIndex V = 16 := by
    have hmul := Subgroup.relIndex_mul_relIndex (v1Sub D.M ⊥ V hV L) W V hV1W hWV
    rw [hV1relW, hV1relV, hP16] at hmul
    omega
  have hcent_relIndex : (Subgroup.centralizer (conjSubgroup V g : Set G)).relIndex V = 16 := by
    have h1 : (Subgroup.centralizer (conjSubgroup V g : Set G)).relIndex V = W.relIndex V := by
      rw [show W = V ⊓ Subgroup.centralizer (conjSubgroup V g : Set G) from rfl,
        Subgroup.inf_relIndex_left]
    rw [h1, hWrel]
  unfold s16c4v1_r1 E3.mQuot
  rw [hcent_relIndex, show (16 : ℕ) = 2 ^ 4 by norm_num, padicValNat.prime_pow]


end CFSG.LocalAnalysis.UniquenessCase.PartTwo
