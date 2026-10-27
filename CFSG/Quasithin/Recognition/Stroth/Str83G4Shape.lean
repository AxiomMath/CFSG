module

public import CFSG.Quasithin.Recognition.Stroth.Str83G4Sec5M4
public import CFSG.Quasithin.Recognition.Stroth.Str83G4CP

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def str83X1 (L1 L2 S : Subgroup G) : Subgroup G :=
  centralizerMod (Z1 L1 L2 S) (str83X L1 L2 S) (L1 ⊔ S)

theorem str83X1_def (L1 L2 S : Subgroup G) :
    str83X1 L1 L2 S = centralizerMod (Z1 L1 L2 S) (str83X L1 L2 S) (L1 ⊔ S) := rfl

theorem mem_str83X1 {L1 L2 S : Subgroup G} {x : G} :
    x ∈ str83X1 L1 L2 S ↔ x ∈ str83X L1 L2 S ∧
      x ∈ Subgroup.normalizer (Z1 L1 L2 S : Set G) ∧
      ∀ u ∈ L1 ⊔ S, x * u * x⁻¹ * u⁻¹ ∈ Z1 L1 L2 S :=
  Iff.rfl

theorem str83G4_sup_le_centralizer_z1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    L1 ⊔ S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) := by
  obtain ⟨hF, hB, ha, hSz, hL2, hZI⟩ := hfr
  obtain ⟨hZ1eq, -⟩ := str83_caseI_basics hF hB ha hSz hL2 hZI
  refine sup_le (le_sup_left.trans hZI) ?_
  rw [hZ1eq]
  intro s hs
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact (Subgroup.mem_centralizer_iff.mp
    (A4.centerOf_le_centralizer S (A4.omegaOneCenterOf_le_centerOf S hz)) s hs).symm

theorem str83G4_z1_le_x
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    Z1 L1 L2 S ≤ str83X L1 L2 S :=
  (str83G4_z1_le_center_x hfr).trans inf_le_left

theorem str83G4_x_le_sup
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    str83X L1 L2 S ≤ L1 ⊔ S :=
  (str83X_le_q1 hfr).trans ((str83G4_q1_le_s hfr).trans le_sup_right)

theorem str83G4_sup_le_normalizer_x
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    L1 ⊔ S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G) :=
  (sup_left_le_p1 L1 L2 S).trans (le_normalizer_str83X L1 L2 S)

theorem str83G4_sup_le_normalizer_z1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
  (sup_left_le_p1 L1 L2 S).trans (SmithC27.le_normalizer_omegaOneCenterOf_pCoreOf
    (P1 L1 L2 S))

private theorem le_normalizer_centralizerMod_of_le {Z X U Y : Subgroup G}
    (hZ : Y ≤ Subgroup.normalizer (Z : Set G)) (hX : Y ≤ Subgroup.normalizer (X : Set G))
    (hU : Y ≤ Subgroup.normalizer (U : Set G)) :
    Y ≤ Subgroup.normalizer (centralizerMod Z X U : Set G) := by
  have key : ∀ h ∈ Y, ∀ c ∈ centralizerMod Z X U, h * c * h⁻¹ ∈ centralizerMod Z X U := by
    intro h hh c hc
    obtain ⟨hcX, hcN, hcc⟩ := hc
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hX hh) c).mp hcX,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hZ hh) hcN) (Subgroup.inv_mem _ (hZ hh)),
      fun u hu => ?_⟩
    have hu' : h⁻¹ * u * h⁻¹⁻¹ ∈ U :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hU hh)) u).mp hu
    have h1 := hcc _ hu'
    have h2 := (Subgroup.mem_normalizer_iff.mp (hZ hh) _).mp h1
    rwa [show h * (c * (h⁻¹ * u * h⁻¹⁻¹) * c⁻¹ * (h⁻¹ * u * h⁻¹⁻¹)⁻¹) * h⁻¹ =
      h * c * h⁻¹ * u * (h * c * h⁻¹)⁻¹ * u⁻¹ by group] at h2
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨key h hh c, fun hc => ?_⟩
  have := key h⁻¹ (Y.inv_mem hh) _ hc
  rwa [show h⁻¹ * (h * c * h⁻¹) * h⁻¹⁻¹ = c by group] at this

theorem str83G4_z1_le_x1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    Z1 L1 L2 S ≤ str83X1 L1 L2 S := by
  intro z hz
  refine mem_centralizerMod.mpr ⟨str83G4_z1_le_x hfr hz, Subgroup.le_normalizer hz, ?_⟩
  intro u hu
  have hc := Subgroup.mem_centralizer_iff.mp (str83G4_sup_le_centralizer_z1 hfr hu) z hz
  rw [show z * u * z⁻¹ * u⁻¹ = 1 by
    rw [hc]; group]
  exact (Z1 L1 L2 S).one_mem

theorem str83G4_x1_le_x (L1 L2 S : Subgroup G) :
    str83X1 L1 L2 S ≤ str83X L1 L2 S :=
  centralizerMod_le_left _ _ _

theorem str83G4_x1_normal
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    IsNormalIn (L1 ⊔ S) (str83X L1 L2 S)
      (str83X1 L1 L2 S) := by
  refine ⟨str83G4_x1_le_x L1 L2 S, fun g hg x hx => ?_⟩
  have hN := le_normalizer_centralizerMod_of_le (Z := Z1 L1 L2 S) (X := str83X L1 L2 S)
    (U := L1 ⊔ S) (Y := L1 ⊔ S) (str83G4_sup_le_normalizer_z1 hfr)
    (str83G4_sup_le_normalizer_x hfr) Subgroup.le_normalizer
  exact (Subgroup.mem_normalizer_iff.mp (hN hg) x).mp hx

theorem str83G4_x_normal
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    IsNormalIn (L1 ⊔ S) (str83X L1 L2 S) (str83X L1 L2 S) := by
  refine ⟨le_rfl, fun g hg x hx => ?_⟩
  exact (Subgroup.mem_normalizer_iff.mp (str83G4_sup_le_normalizer_x hfr hg) x).mp hx

theorem str83G4_z1_normal
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    IsNormalIn (L1 ⊔ S) (str83X L1 L2 S) (Z1 L1 L2 S) := by
  refine ⟨str83G4_z1_le_x hfr, fun g hg x hx => ?_⟩
  exact (Subgroup.mem_normalizer_iff.mp (str83G4_sup_le_normalizer_z1 hfr hg) x).mp hx

theorem str83G4_commutator_z1_oTwo_eq_bot
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    ⁅Z1 L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ = ⊥ := by
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact (oTwoUpper_le (L1 ⊔ S)).trans (str83G4_sup_le_centralizer_z1 hfr)

theorem str83G4_commutator_x1_oTwo_eq_bot
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (hX : IsElemAbelian 2 (str83X L1 L2 S)) :
    ⁅str83X1 L1 L2 S,
      oTwoUpper (L1 ⊔ S)⁆ = ⊥ := by
  have hle : ⁅str83X1 L1 L2 S,
      oTwoUpper (L1 ⊔ S)⁆ ≤ Z1 L1 L2 S :=
    Subgroup.commutator_le.mpr fun x hx u hu => hx.2.2 u ((oTwoUpper_le (L1 ⊔ S)) hu)
  have hW : IsPGroup 2 (str83X1 L1 L2 S) :=
    (B2F.isPGroup_of_isElemAbelian hX).to_le (str83G4_x1_le_x L1 L2 S)
  have hWle : str83X1 L1 L2 S ≤ L1 ⊔ S :=
    (str83G4_x1_le_x L1 L2 S).trans (str83G4_x_le_sup hfr)
  have hNW : L1 ⊔ S ≤ Subgroup.normalizer
      (str83X1 L1 L2 S : Set G) :=
    (D14.le_normalizer_of_isNormalIn (str83G4_x1_normal hfr))
  have hstep := D14.commutator_le_commutator_commutator (H := L1 ⊔ S)
    (W := str83X1 L1 L2 S) hW hWle hNW
  have hbot : ⁅⁅str83X1 L1 L2 S,
      oTwoUpper (L1 ⊔ S)⁆, oTwoUpper (L1 ⊔ S)⁆ = ⊥ := by
    refine le_bot_iff.mp ((Subgroup.commutator_mono hle le_rfl).trans ?_)
    rw [str83G4_commutator_z1_oTwo_eq_bot hfr]
  exact le_bot_iff.mp (hstep.trans (le_of_eq hbot))

theorem str83G4_eta_x_eq_one
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    F112W.eta (L1 ⊔ S) (str83X L1 L2 S) (str83X L1 L2 S) = 1 := by
  have hser := F112W.isChiefSeriesFrom_eta (str83G4_x_le_sup hfr) (str83G4_x_normal hfr)
  exact str83G4_chiefSeries_x_eq_one hfr d hX hB hser

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits CFSG.Quasithin.H13
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem str83G4_centralizerMod_sup_eq_oTwoUpper
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) {L N : Subgroup G}
    (hLN : L ≤ N) (hNX : N ≤ str83X L1 L2 S) (hZ1L : Z1 L1 L2 S ≤ L)
    (hHL : L1 ⊔ S ≤ Subgroup.normalizer (L : Set G)) :
    centralizerMod L N (L1 ⊔ S) = centralizerMod L N (oTwoUpper (L1 ⊔ S)) := by
  have hH : L1 ⊔ S = oTwoUpper (L1 ⊔ S) ⊔ Q1 L1 L2 S :=
    (str83G4_oTwoUpper_sup_left hfr d).symm
  have hQ1N : Q1 L1 L2 S ≤ Subgroup.normalizer (oTwoUpper (L1 ⊔ S) : Set G) :=
    (str83G4_q1_le_s hfr).trans ((le_sup_right : S ≤ L1 ⊔ S).trans
      (CFSG.Quasithin.le_normalizer_oTwoUpper (L1 ⊔ S)))
  refine le_antisymm ?_ ?_
  · intro x hx
    exact ⟨hx.1, hx.2.1, fun u hu => hx.2.2 u ((oTwoUpper_le (L1 ⊔ S)) hu)⟩
  · intro x hx
    refine ⟨hx.1, hx.2.1, ?_⟩
    intro h hh
    have hmem : h ∈ oTwoUpper (L1 ⊔ S) ⊔ Q1 L1 L2 S := by rw [← hH]; exact hh
    obtain ⟨g, hg, q, hq, rfl⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hQ1N).mp hmem
    have h1 : x * g * x⁻¹ * g⁻¹ ∈ L := hx.2.2 g hg
    have h2 : x * q * x⁻¹ * q⁻¹ ∈ L := by
      have hmem2 : ⁅x, q⁆ ∈ ⁅str83X L1 L2 S, Q1 L1 L2 S⁆ :=
        Subgroup.commutator_mem_commutator (hNX hx.1) hq
      exact hZ1L (str83G4_commutator_x_q1_le hfr hmem2)
    have hgH : g ∈ L1 ⊔ S := (oTwoUpper_le (L1 ⊔ S)) hg
    have h3 : g * (x * q * x⁻¹ * q⁻¹) * g⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hHL hgH) _).mp h2
    have h4 : x * (g * q) * x⁻¹ * (g * q)⁻¹ =
        (x * g * x⁻¹ * g⁻¹) * (g * (x * q * x⁻¹ * q⁻¹) * g⁻¹) := by group
    rw [h4]
    exact L.mul_mem h1 h3

theorem str83G4_x1_eq_centralizerMod_oTwoUpper
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) :
    str83X1 L1 L2 S = centralizerMod (Z1 L1 L2 S) (str83X L1 L2 S)
      (oTwoUpper (L1 ⊔ S)) := by
  rw [str83X1_def]
  exact str83G4_centralizerMod_sup_eq_oTwoUpper hfr d
    (str83G4_z1_le_x hfr) le_rfl le_rfl (str83G4_sup_le_normalizer_z1 hfr)

abbrev str83N (L1 L2 S : Subgroup G) : Subgroup G :=
  ⁅str83X L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ ⊔ Z1 L1 L2 S

abbrev str83N1 (L1 L2 S : Subgroup G) : Subgroup G :=
  str83N L1 L2 S ⊓ str83X1 L1 L2 S

theorem str83N_le_x
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    str83N L1 L2 S ≤ str83X L1 L2 S :=
  sup_le (F112W.commutator_le_self_of_le_normalizer
      ((oTwoUpper_le (L1 ⊔ S)).trans (str83G4_sup_le_normalizer_x hfr)))
    (str83G4_z1_le_x hfr)

theorem str83Z1_le_n (L1 L2 S : Subgroup G) : Z1 L1 L2 S ≤ str83N L1 L2 S := le_sup_right

theorem str83Z1_le_n1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    Z1 L1 L2 S ≤ str83N1 L1 L2 S :=
  le_inf (str83Z1_le_n L1 L2 S) (str83G4_z1_le_x1 hfr)

theorem str83N1_le_n (L1 L2 S : Subgroup G) : str83N1 L1 L2 S ≤ str83N L1 L2 S := inf_le_left

theorem str83N1_le_x1 (L1 L2 S : Subgroup G) : str83N1 L1 L2 S ≤ str83X1 L1 L2 S := inf_le_right

theorem str83N_normal
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    IsNormalIn (L1 ⊔ S) (str83X L1 L2 S) (str83N L1 L2 S) := by
  have hHX : L1 ⊔ S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G) :=
    str83G4_sup_le_normalizer_x hfr
  have hHO : L1 ⊔ S ≤ Subgroup.normalizer (oTwoUpper (L1 ⊔ S) : Set G) :=
    CFSG.Quasithin.le_normalizer_oTwoUpper (L1 ⊔ S)
  have hHZ : L1 ⊔ S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    str83G4_sup_le_normalizer_z1 hfr
  have hHcomm : L1 ⊔ S ≤
      Subgroup.normalizer ((⁅str83X L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ : Subgroup G) : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHX hh),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHO hh)]
  exact F112W.isNormalIn_of_le_normalizer
    (sup_le (F112W.commutator_le_self_of_le_normalizer ((oTwoUpper_le (L1 ⊔ S)).trans hHX))
      (str83G4_z1_le_x hfr))
    (D14.le_normalizer_sup hHcomm hHZ)

theorem str83N1_normal
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a) :
    IsNormalIn (L1 ⊔ S) (str83X L1 L2 S) (str83N1 L1 L2 S) :=
  F112W.isNormalIn_inf (str83N_normal hfr) (str83G4_x1_normal hfr)

private theorem isChiefStep_of_isNormalIn_le {H U N' L M : Subgroup G}
    (hM : M ≤ N') (hN' : N' ≤ U) (h : IsChiefStep H N' L M) : IsChiefStep H U L M := by
  obtain ⟨hMn, hLn, hlt, hmax⟩ := h
  exact ⟨⟨hMn.1.trans hN', hMn.2⟩, ⟨hLn.1.trans hN', hLn.2⟩, hlt,
    fun K hK hLK hKM => hmax K ⟨hKM.trans hM, hK.2⟩ hLK hKM⟩

theorem str83N1_lt_n
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (hX : IsElemAbelian 2 (str83X L1 L2 S)) :
    str83N1 L1 L2 S < str83N L1 L2 S := by
  have hle : str83N1 L1 L2 S ≤ str83N L1 L2 S := str83N1_le_n L1 L2 S
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hNle : str83N L1 L2 S ≤ str83X1 L1 L2 S :=
    heq.ge.trans (str83N1_le_x1 L1 L2 S)
  have hXO2 : ⁅str83X L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ ≤ str83X1 L1 L2 S :=
    (show ⁅str83X L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ ≤ str83N L1 L2 S from le_sup_left).trans hNle
  have hWp : IsPGroup 2 (str83X L1 L2 S) := B2F.isPGroup_of_isElemAbelian hX
  have hWH : str83X L1 L2 S ≤ L1 ⊔ S := str83G4_x_le_sup hfr
  have hHW : L1 ⊔ S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G) :=
    str83G4_sup_le_normalizer_x hfr
  have hstep := D14.commutator_le_commutator_commutator (H := L1 ⊔ S)
    (W := str83X L1 L2 S) hWp hWH hHW
  have hbot : ⁅⁅str83X L1 L2 S, oTwoUpper (L1 ⊔ S)⁆, oTwoUpper (L1 ⊔ S)⁆ = ⊥ := by
    refine le_bot_iff.mp ((Subgroup.commutator_mono hXO2 le_rfl).trans ?_)
    exact le_of_eq (str83G4_commutator_x1_oTwo_eq_bot hfr hX)
  have hcomm : ⁅str83X L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ = ⊥ :=
    le_bot_iff.mp (hstep.trans (le_of_eq hbot))
  obtain ⟨L, N', hchief, hZ1L, hnc⟩ := str83G4_exists_chiefStep hfr
  apply hnc
  rw [F6.twoResidual_eq_oTwoUpper]
  intro u hu
  refine ⟨(oTwoUpper_le (L1 ⊔ S)) hu,
    (D14.le_normalizer_of_isNormalIn hchief.2.1) ((oTwoUpper_le (L1 ⊔ S)) hu), ?_⟩
  intro n hn
  have hmem : ⁅n, u⁆ ∈ ⁅str83X L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ :=
    Subgroup.commutator_mem_commutator (hchief.1.1 hn) hu
  rw [hcomm, Subgroup.mem_bot] at hmem
  have hinv : ⁅u, n⁆ = ⁅n, u⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  change ⁅u, n⁆ ∈ L
  rw [hinv, hmem, inv_one]
  exact L.one_mem

theorem str83G4_commutator_x_oTwo_le_n (L1 L2 S : Subgroup G) :
    ⁅str83X L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ ≤ str83N L1 L2 S :=
  le_sup_left

theorem str83G4_commutator_x_oTwo_eq_commutator_n_oTwo
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (hX : IsElemAbelian 2 (str83X L1 L2 S)) :
    ⁅str83X L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ =
      ⁅str83N L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ := by
  refine le_antisymm ?_ (Subgroup.commutator_mono (str83N_le_x hfr) le_rfl)
  have hWp : IsPGroup 2 (str83X L1 L2 S) := B2F.isPGroup_of_isElemAbelian hX
  have hWH : str83X L1 L2 S ≤ L1 ⊔ S := str83G4_x_le_sup hfr
  have hHW : L1 ⊔ S ≤ Subgroup.normalizer (str83X L1 L2 S : Set G) :=
    str83G4_sup_le_normalizer_x hfr
  have hstep := D14.commutator_le_commutator_commutator (H := L1 ⊔ S)
    (W := str83X L1 L2 S) hWp hWH hHW
  exact hstep.trans (Subgroup.commutator_mono
    (str83G4_commutator_x_oTwo_le_n L1 L2 S) le_rfl)

theorem str83G4_isChiefStep_n_n1
    {L1 L2 S : Subgroup G} {a : ℕ} (hfr : Str83G4Frame L1 L2 S a)
    (d : Str83G4Data L1 L2 S) (hX : IsElemAbelian 2 (str83X L1 L2 S))
    (hB : ¬ CFSG.conjugate (str83X L1 L2 S) d.w ≤ Q1 L1 L2 S) :
    IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (str83N1 L1 L2 S) (str83N L1 L2 S) ∧
      ¬ IsCentralStep (L1 ⊔ S) (str83N1 L1 L2 S) (str83N L1 L2 S) := by
  have hXH : str83X L1 L2 S ≤ L1 ⊔ S := str83G4_x_le_sup hfr
  have hXQ : str83X L1 L2 S ≤ pCoreOf 2 (L1 ⊔ S) := by
    rw [str83G4_pCoreOf_sup_left hfr]
    exact str83X_le_q1 hfr
  have hZn : IsNormalIn (L1 ⊔ S) (str83X L1 L2 S) (Z1 L1 L2 S) := str83G4_z1_normal hfr
  have hXn : IsNormalIn (L1 ⊔ S) (str83X L1 L2 S) (str83X L1 L2 S) :=
    F112W.isNormalIn_of_le_normalizer le_rfl (str83G4_sup_le_normalizer_x hfr)
  have hNn : IsNormalIn (L1 ⊔ S) (str83X L1 L2 S) (str83N L1 L2 S) := str83N_normal hfr
  have hN1n : IsNormalIn (L1 ⊔ S) (str83X L1 L2 S) (str83N1 L1 L2 S) := str83N1_normal hfr
  have hlt : str83N1 L1 L2 S < str83N L1 L2 S := str83N1_lt_n hfr hX
  obtain ⟨M, hMmin⟩ := exists_minimal_of_wellFoundedLT
    (fun M : Subgroup G =>
      IsNormalIn (L1 ⊔ S) (str83N L1 L2 S) M ∧ str83N1 L1 L2 S < M)
    ⟨str83N L1 L2 S, F112W.isNormalIn_of_le_normalizer le_rfl
      (D14.le_normalizer_of_isNormalIn (str83N_normal hfr)), hlt⟩
  have hMn : IsNormalIn (L1 ⊔ S) (str83N L1 L2 S) M := hMmin.1.1
  have hN1M : str83N1 L1 L2 S < M := hMmin.1.2
  have hMN : M ≤ str83N L1 L2 S := hMn.1
  have hMX : M ≤ str83X L1 L2 S := hMN.trans (str83N_le_x hfr)
  have hN1nN : IsNormalIn (L1 ⊔ S) (str83N L1 L2 S) (str83N1 L1 L2 S) :=
    F112W.isNormalIn_of_le_normalizer (str83N1_le_n L1 L2 S)
      (D14.le_normalizer_of_isNormalIn hN1n)
  have hstepN : IsChiefStep (L1 ⊔ S) (str83N L1 L2 S) (str83N1 L1 L2 S) M := by
    refine ⟨hMn, hN1nN, hN1M, ?_⟩
    intro K hK hN1K hKM
    by_cases hK1 : K = str83N1 L1 L2 S
    · exact Or.inl hK1
    · refine Or.inr (le_antisymm hKM ?_)
      exact hMmin.2 ⟨hK, lt_of_le_of_ne hN1K (fun h => hK1 h.symm)⟩ hKM
  have hstepX : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (str83N1 L1 L2 S) M :=
    isChiefStep_of_isNormalIn_le hMN (str83N_le_x hfr) hstepN
  have hN1O : ⁅str83N1 L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ = ⊥ := by
    refine le_bot_iff.mp ((Subgroup.commutator_mono (str83N1_le_x1 L1 L2 S) le_rfl).trans ?_)
    exact le_of_eq (str83G4_commutator_x1_oTwo_eq_bot hfr hX)
  have hncM : ¬ IsCentralStep (L1 ⊔ S) (str83N1 L1 L2 S) M := by
    intro hc
    have hMO : ⁅M, oTwoUpper (L1 ⊔ S)⁆ ≤ str83N1 L1 L2 S := by
      refine Subgroup.commutator_le.mpr fun m hm u hu => ?_
      have h1 : u * m * u⁻¹ * m⁻¹ ∈ str83N1 L1 L2 S :=
        hc u ((oTwoUpper_le (L1 ⊔ S)) hu) m hm
      have h2 := (str83N1 L1 L2 S).inv_mem h1
      rwa [show (u * m * u⁻¹ * m⁻¹)⁻¹ = ⁅m, u⁆ by
        simp only [commutatorElement_def]; group] at h2
    have hMp : IsPGroup 2 M := (B2F.isPGroup_of_isElemAbelian hX).to_le hMX
    have hHM : L1 ⊔ S ≤ Subgroup.normalizer (M : Set G) :=
      D14.le_normalizer_of_isNormalIn hMn
    have hstepM := D14.commutator_le_commutator_commutator (H := L1 ⊔ S)
      (W := M) hMp (hMX.trans hXH) hHM
    have hbot : ⁅⁅M, oTwoUpper (L1 ⊔ S)⁆, oTwoUpper (L1 ⊔ S)⁆ = ⊥ := by
      refine le_bot_iff.mp ((Subgroup.commutator_mono hMO le_rfl).trans ?_)
      exact (Subgroup.commutator_mono (str83N1_le_x1 L1 L2 S) le_rfl).trans
        (le_of_eq (str83G4_commutator_x1_oTwo_eq_bot hfr hX))
    have hMObot : ⁅M, oTwoUpper (L1 ⊔ S)⁆ = ⊥ :=
      le_bot_iff.mp (hstepM.trans (le_of_eq hbot))
    have hMle : M ≤ str83N1 L1 L2 S := by
      intro x hx
      refine ⟨hMN hx, ?_⟩
      rw [str83G4_x1_eq_centralizerMod_oTwoUpper hfr d]
      refine ⟨hMX hx, (str83G4_sup_le_normalizer_z1 hfr) (hXH (hMX hx)), ?_⟩
      intro u hu
      have hmem : ⁅x, u⁆ ∈ ⁅M, oTwoUpper (L1 ⊔ S)⁆ :=
        Subgroup.commutator_mem_commutator hx hu
      rw [hMObot, Subgroup.mem_bot] at hmem
      change ⁅x, u⁆ ∈ Z1 L1 L2 S
      rw [hmem]
      exact (Z1 L1 L2 S).one_mem
    exact (not_le_of_gt hN1M) hMle
  have hetaN1 : F112W.eta (L1 ⊔ S) (str83X L1 L2 S) (str83N1 L1 L2 S) = 0 := by
    refine (F112W.eta_eq_zero_iff hXH hXQ hN1n).mpr ?_
    exact le_bot_iff.mp ((Subgroup.commutator_mono (str83N1_le_x1 L1 L2 S) le_rfl).trans
      (le_of_eq (str83G4_commutator_x1_oTwo_eq_bot hfr hX)))
  have hetaX : F112W.eta (L1 ⊔ S) (str83X L1 L2 S) (str83X L1 L2 S) = 1 :=
    str83G4_eta_x_eq_one hfr d hX hB
  obtain ⟨a3, hser3⟩ := F112W.exists_isChiefSeriesBetween (H := L1 ⊔ S) (U := str83X L1 L2 S)
    hNn (str83X L1 L2 S) hXn (str83N_le_x hfr)
  have h3 : F112W.eta (L1 ⊔ S) (str83X L1 L2 S) (str83X L1 L2 S) =
      F112W.eta (L1 ⊔ S) (str83X L1 L2 S) (str83N L1 L2 S) + a3 :=
    F112W.eta_eq_add hXH hNn hser3
  have ha3 : a3 = 0 := by
    have hzero : F112W.IsChiefSeriesBetween (L1 ⊔ S) (str83X L1 L2 S) (str83N L1 L2 S)
        (str83X L1 L2 S) 0 :=
      (F112W.isChiefSeriesBetween_zero_iff hXH hXQ hNn hXn (str83N_le_x hfr)).mpr
        (str83G4_commutator_x_oTwo_le_n L1 L2 S)
    exact F112W.isChiefSeriesBetween_unique hXH hNn hser3 hzero
  have hetaN : F112W.eta (L1 ⊔ S) (str83X L1 L2 S) (str83N L1 L2 S) = 1 := by
    rw [hetaX, ha3, add_zero] at h3
    exact h3.symm
  obtain ⟨a2, hser2⟩ := F112W.exists_isChiefSeriesBetween (H := L1 ⊔ S) (U := str83X L1 L2 S)
    hN1n (str83N L1 L2 S) hNn (str83N1_le_n L1 L2 S)
  have h2 : F112W.eta (L1 ⊔ S) (str83X L1 L2 S) (str83N L1 L2 S) =
      F112W.eta (L1 ⊔ S) (str83X L1 L2 S) (str83N1 L1 L2 S) + a2 :=
    F112W.eta_eq_add hXH hN1n hser2
  have ha2 : a2 = 1 := by
    rw [hetaN, hetaN1, zero_add] at h2
    exact h2.symm
  have hserM : F112W.IsChiefSeriesBetween (L1 ⊔ S) (str83X L1 L2 S) (str83N1 L1 L2 S) M 1 :=
    F112W.IsChiefSeriesBetween.noncentral hstepX hncM F112W.IsChiefSeriesBetween.refl
  have hetaM : F112W.eta (L1 ⊔ S) (str83X L1 L2 S) M = 1 := by
    have hM1 := F112W.eta_eq_add hXH hN1n hserM
    rw [hetaN1, zero_add] at hM1
    exact hM1
  obtain ⟨a4, hser4⟩ := F112W.exists_isChiefSeriesBetween (H := L1 ⊔ S) (U := str83X L1 L2 S)
    (F112W.isNormalIn_of_le_normalizer hMX (D14.le_normalizer_of_isNormalIn hMn))
    (str83N L1 L2 S) hNn hMN
  have h4 : F112W.eta (L1 ⊔ S) (str83X L1 L2 S) (str83N L1 L2 S) =
      F112W.eta (L1 ⊔ S) (str83X L1 L2 S) M + a4 :=
    F112W.eta_eq_add hXH (F112W.isNormalIn_of_le_normalizer hMX
      (D14.le_normalizer_of_isNormalIn hMn)) hser4
  have ha4 : a4 = 0 := by
    rw [hetaN, hetaM] at h4
    omega
  have hNOM : ⁅str83N L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ ≤ M :=
    (F112W.isChiefSeriesBetween_zero_iff hXH hXQ
      (F112W.isNormalIn_of_le_normalizer hMX (D14.le_normalizer_of_isNormalIn hMn))
      hNn hMN).mp (ha4 ▸ hser4)
  have hNleM : str83N L1 L2 S ≤ M := by
    have hZleM : Z1 L1 L2 S ≤ M := (str83Z1_le_n1 hfr).trans hN1M.le
    calc str83N L1 L2 S = ⁅str83X L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ ⊔ Z1 L1 L2 S := rfl
      _ = ⁅str83N L1 L2 S, oTwoUpper (L1 ⊔ S)⁆ ⊔ Z1 L1 L2 S := by
        rw [str83G4_commutator_x_oTwo_eq_commutator_n_oTwo hfr hX]
      _ ≤ M := sup_le hNOM hZleM
  have hMeqN : M = str83N L1 L2 S := le_antisymm hMN hNleM
  have hstepN' : IsChiefStep (L1 ⊔ S) (str83N L1 L2 S) (str83N1 L1 L2 S)
      (str83N L1 L2 S) := hMeqN ▸ hstepN
  have hstepNX : IsChiefStep (L1 ⊔ S) (str83X L1 L2 S) (str83N1 L1 L2 S)
      (str83N L1 L2 S) :=
    isChiefStep_of_isNormalIn_le le_rfl (str83N_le_x hfr) hstepN'
  exact ⟨hstepNX, hMeqN ▸ hncM⟩

end CFSG.Quasithin.Stroth

end
