module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829CS5In
public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213Typ
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem11
public import CFSG.Quasithin.Vol2.Ch7E61
public import CFSG.Quasithin.Background.HMathieuO2Data
public import CFSG.Quasithin.Background.InternalSecISec

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

private theorem c6Odd829_mem_conj {G : Type} [Group G] {H : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  unfold CFSG.conjugate
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have e : g * x * g⁻¹ = y := by
      rw [← hyx]
      show g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y
      group
    rw [e]
    exact hy
  · intro hx
    refine ⟨g * x * g⁻¹, hx, ?_⟩
    show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x
    group

theorem c6Odd829_psl2_card_ne_m24 {n : ℕ} (hn : 2 ≤ n) :
    2 ^ n * (4 ^ n - 1) ≠ 244823040 := by
  rcases Nat.lt_or_ge n 28 with h | h
  · interval_cases n <;> norm_num
  · intro heq
    have h1 : 2 ^ 28 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h
    have h4n : 4 ≤ 4 ^ n := by
      calc 4 = 4 ^ 1 := by norm_num
        _ ≤ 4 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h4 : 0 < 4 ^ n - 1 := by omega
    have h3 : 2 ^ n ≤ 2 ^ n * (4 ^ n - 1) := Nat.le_mul_of_pos_right _ h4
    have h5 : 2 ^ 28 ≤ 244823040 := h1.trans (h3.trans heq.le)
    norm_num at h5

theorem c6Odd829_of
    (h443o : Stmt4_4_3Orbit') (h711n : Stmt7_1_1_normal) (h3228 : Stmt3_2_2_eight)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) : C6Odd829 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro G _ _ T L I hyp _ _ hc _ hcoc B hBM hB1 hBc hBo hBV
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := by
    refine h711n G T L I hyp hc ?_
    iterate 10 right
    exact Or.inl hcoc
  have hL0 : conjClosure L T = L := conjClosure_eq_self hTL
  have hL0' : fsuL0 T L = L := hL0
  have hMN : fsuM T L = Subgroup.normalizer (L : Set G) := by
    show Subgroup.normalizer (fsuL0 T L : Set G) = _
    rw [hL0']
  have hMmax : quasithinIsMaxTwoLocal (fsuM T L) :=
    (lemma_1_2_7_three hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian h37 h38 h39
      hyp.fsu.sylow hyp.fsu.maximal).1.1
  have hTM : T ≤ fsuM T L := by
    rw [hMN]
    exact hTL
  have hLM : L ≤ fsuM T L := by
    rw [hMN]
    exact Subgroup.le_normalizer
  have hLN₀ : fsuM T L ≤ Subgroup.normalizer (L : Set G) := hMN.le
  obtain ⟨hVX, hRed0, -⟩ := h3228 G T L I hyp.fsu
  have hVLT : fsuV T I ≤ L ⊔ T := by
    rw [hL0] at hVX
    exact hVX
  have hRed : IsPrimeReduced 2 ((fsuV T I).subgroupOf (L ⊔ T)) := by
    rw [hL0] at hRed0
    exact hRed0
  obtain ⟨-, hVN0⟩ := (stmtFSUModule_of_eight h3228) G T L I hyp.fsu
  have hLTN : L ⊔ T ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    rw [hL0'] at hVN0
    exact hVN0
  have hLN : L ≤ Subgroup.normalizer (fsuV T I : Set G) := le_sup_left.trans hLTN
  have hV1 : fsuV T I ≠ ⊥ := fsuV_ne_bot hyp.fsu
  have hIL : ⁅I, L⁆ = I := by
    have h := hyp.fsu.irrPlus.2.2.2.1
    rw [hL0] at h
    exact h
  have hLconj : ∀ t ∈ T, CFSG.conjugate L t = L := fun t ht =>
    conjugate_eq_self_of_normalizes (hTL ht)
  have hconjI : ∀ t ∈ T, CFSG.conjugate I t ≤ fsuV T I := by
    intro t ht x hx
    rw [c6Odd829_mem_conj] at hx
    have h1 := mem_conjClosure (T.inv_mem ht) hx
    have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
    rw [e] at h1
    exact h1
  have hsub : ∀ t ∈ T, CFSG.conjugate I t ≤ ⁅fsuV T I, L⁆ := by
    intro t ht
    calc CFSG.conjugate I t = CFSG.conjugate ⁅I, L⁆ t := by rw [hIL]
      _ = ⁅CFSG.conjugate I t, CFSG.conjugate L t⁆ := by
          unfold CFSG.conjugate
          exact Subgroup.map_commutator _ _ _
      _ = ⁅CFSG.conjugate I t, L⁆ := by rw [hLconj t ht]
      _ ≤ ⁅fsuV T I, L⁆ := Subgroup.commutator_mono (hconjI t ht) le_rfl
  have hVL : fsuV T I = ⁅fsuV T I, L⁆ := by
    refine le_antisymm (conjClosure_le fun t ht z hz => ?_) ?_
    · have hx : t * z * t⁻¹ ∈ CFSG.conjugate I t⁻¹ := by
        rw [c6Odd829_mem_conj]
        have e : t⁻¹ * (t * z * t⁻¹) * t⁻¹⁻¹ = z := by group
        rw [e]
        exact hz
      exact hsub t⁻¹ (T.inv_mem ht) hx
    · rw [Subgroup.commutator_le]
      intro v hv l hl
      have hlv : l * v⁻¹ * l⁻¹ ∈ fsuV T I :=
        (Subgroup.mem_normalizer_iff.mp (hLN hl) _).mp ((fsuV T I).inv_mem hv)
      have e : v * l * v⁻¹ * l⁻¹ = v * (l * v⁻¹ * l⁻¹) := by group
      rw [commutatorElement_def, e]
      exact (fsuV T I).mul_mem hv hlv
  have hH := remark_4_4_2 (M := fsuM T L) hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
    hyp.fsu.sylow hMmax hTM hyp.fsu.maximal hyp.fsu.faithful hLM hyp.fsu.quasisimple
    hLN₀ hVLT hRed hVL hV1 hBM hBV hB1 hBc hBo
  rcases stmt4_4_3Orbit_iff'.mp h443o G T (fsuM T L) L B ⊥ (fsuV T I) hH with
    hBN | ⟨-, hlist, -⟩
  · exact hBN
  exfalso
  have hcocL : MathieuCocode24 (V := ↥(fsuV T I)) (autOn L (fsuV T I)) ⊤ ⊥ := by
    have h := hcoc
    unfold Row711M24Cocode at h
    rw [hL0'] at h
    exact h
  have hcard : Nat.card ↥(autOn L (fsuV T I)) = 244823040 :=
    (CFSG.Quasithin.H.Mathieu.card_of_cocode24 hcocL).2
  haveI : Finite ↥(autOn L (fsuV T I)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hPL : pCoreOf 2 L ≤ Subgroup.centralizer (fsuV T I : Set G) := by
    have hQL : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ T) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
        (sup_le (le_normalizer_pCoreOf 2 L) (hTL.trans (normalizer_le_normalizer_pCoreOf 2 L)))
        (pCoreOf_isPGroup 2 L)
    exact hQL.trans (le_omegaOneCenter_of_isPrimeReduced hVLT hRed).2
  have hker : CFSG.pCore 2 ↥L ≤ (CFSG.Quasithin.InternalSec.autOnHom hLN).ker := by
    intro x hx
    exact (CFSG.Quasithin.InternalSec.mem_ker_autOnHom hLN x).2
      (hPL (show (x : G) ∈ pCoreOf 2 L from ⟨x, hx, rfl⟩))
  obtain ⟨χ, hχ⟩ : ∃ χ : (↥L ⧸ CFSG.pCore 2 ↥L) →* ↥(autOn L (fsuV T I)),
      ∀ l : ↥L, χ (l : ↥L ⧸ CFSG.pCore 2 ↥L) = CFSG.Quasithin.InternalSec.autOnHom hLN l :=
    ⟨QuotientGroup.lift _ (CFSG.Quasithin.InternalSec.autOnHom hLN) hker, fun l => rfl⟩
  have hχs : Function.Surjective χ := by
    intro y
    obtain ⟨l, rfl⟩ := CFSG.Quasithin.InternalSec.autOnHom_surjective hLN y
    exact ⟨(l : ↥L ⧸ CFSG.pCore 2 ↥L), hχ l⟩
  have hle : Nat.card ↥(autOn L (fsuV T I)) ≤ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) :=
    Nat.card_le_card_of_surjective χ hχs
  rw [hcard] at hle
  rcases hlist with ⟨n, hn, hpsl⟩ | hL32 | hL42 | ⟨e6⟩ | ⟨e7⟩ | ⟨hperf, hz3, e6'⟩ | hU33
  ·
    have hs : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) :=
      CFSG.Quasithin.H13.isSimpleGroup_of_lieModel_PSL2 hpsl
    have hQc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 2 ^ n * (4 ^ n - 1) :=
      CFSG.Quasithin.H13.Lem11.card_of_lieModel_psl_two hpsl
    rcases hs.eq_bot_or_eq_top_of_normal χ.ker with hk | hk
    · have hinj : Function.Injective χ := (MonoidHom.ker_eq_bot_iff χ).1 hk
      have hle' : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ≤ 244823040 := by
        rw [← hcard]
        exact Nat.card_le_card_of_injective χ hinj
      have heq : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 244823040 := le_antisymm hle' hle
      exact c6Odd829_psl2_card_ne_m24 hn (hQc.symm.trans heq)
    · have hsub1 : ∀ y : ↥(autOn L (fsuV T I)), y = 1 := by
        intro y
        obtain ⟨q, rfl⟩ := hχs y
        have hq : q ∈ χ.ker := by
          rw [hk]
          exact Subgroup.mem_top q
        exact MonoidHom.mem_ker.1 hq
      haveI : Subsingleton ↥(autOn L (fsuV T I)) :=
        ⟨fun a b => (hsub1 a).trans (hsub1 b).symm⟩
      have h1 := Nat.card_of_subsingleton (1 : ↥(autOn L (fsuV T I)))
      omega
  · have h := CFSG.Quasithin.H13.Ch4.T4213.card_of_lieModel_psl32 hL32
    omega
  · have h := CFSG.Quasithin.H13.Ch4.T4213.card_of_lieModel_psl42 hL42
    omega
  · obtain ⟨e⟩ := e6
    have h := Nat.card_congr e.toEquiv
    have h6 := CFSG.Quasithin.H13.Ch4.C489.card_alt6
    omega
  · obtain ⟨e⟩ := e7
    have h := Nat.card_congr e.toEquiv
    have h7 := CFSG.Quasithin.H13.Ch4.C489.card_alt7
    omega
  · have h := CFSG.Quasithin.H13.Ch4.T4213.card_of_hatA6 ⟨hperf, hz3, e6'⟩
    omega
  · have h := CFSG.Quasithin.H13.Ch4.T4213.card_of_lieModel_psu331 hU33
    omega

end CFSG.Quasithin.H13
