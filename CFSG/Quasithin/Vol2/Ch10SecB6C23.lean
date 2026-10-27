module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs5
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Vol2.Ch10SecA1012SixE23
public import CFSG.Quasithin.Vol2.Ch10SecB6Odd
public import CFSG.Quasithin.Vol2.Ch10SecB6Two

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem map_conj_mem_cComp' {X L : Subgroup G} (hL : L ∈ cComp X) {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    L.map (MulAut.conj g).toMonoidHom ∈ cComp X := by
  have h := cComp_map_mulEquiv (MulAut.conj g) hL
  rwa [A38.map_conj_eq_iff.mpr hg] at h

omit [Finite G] in
theorem modO2Image_map_conj_eq {X Y : Subgroup G} {r : G} (hrX : r ∈ X)
    (hr : (⟨r, hrX⟩ : ↥X) ∈ CFSG.pCore 2 ↥X) (hY : Y ≤ X) :
    modO2Image X (Y.map (MulAut.conj r).toMonoidHom) = modO2Image X Y := by
  have hnX : (CFSG.pCore 2 ↥X).Normal := CFSG.pCore_normal
  have hr1 : QuotientGroup.mk' (CFSG.pCore 2 ↥X) (⟨r, hrX⟩ : ↥X) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hr
  ext q
  constructor
  · intro hq
    obtain ⟨⟨y, hyX⟩, hy, rfl⟩ := Subgroup.mem_map.mp hq
    obtain ⟨l, hl, hly⟩ := Subgroup.mem_map.mp (show y ∈ Y.map (MulAut.conj r).toMonoidHom from hy)
    refine Subgroup.mem_map.mpr ⟨⟨l, hY hl⟩, show l ∈ Y from hl, ?_⟩
    have e : (⟨y, hyX⟩ : ↥X) = ⟨r, hrX⟩ * ⟨l, hY hl⟩ * (⟨r, hrX⟩ : ↥X)⁻¹ := by
      apply Subtype.ext
      show y = r * l * r⁻¹
      rw [← hly]
      simp
    rw [e, map_mul, map_mul, map_inv, hr1, one_mul, inv_one, mul_one]
  · intro hq
    obtain ⟨⟨l, hlX⟩, hl, rfl⟩ := Subgroup.mem_map.mp hq
    refine Subgroup.mem_map.mpr ⟨⟨r, hrX⟩ * ⟨l, hlX⟩ * (⟨r, hrX⟩ : ↥X)⁻¹, ?_, ?_⟩
    · show r * l * r⁻¹ ∈ Y.map (MulAut.conj r).toMonoidHom
      exact Subgroup.mem_map.mpr ⟨l, hl, by simp⟩
    · rw [map_mul, map_mul, map_inv, hr1, one_mul, inv_one, mul_one]

theorem pCoreOf_L0T_le_T1 (hyp : Hyp10 G T L I) : pCoreOf 2 (fsuL0 T L ⊔ T) ≤ T1 T L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hloc := hyp.fsu.maximal.1
  have hX : fsuL0 T L ⊔ T ≤ fsuM T L := sup_le (SecA.fsuL0_le_fsuM T L) (le_fsuM T L)
  have hLX : L ∈ cComp (fsuL0 T L ⊔ T) :=
    cComp_mem_of_le (SecA.mem_cComp_fsuM hloc) ((SecA.le_fsuL0 T L).trans le_sup_left) hX
  have hTX : IsSylowTwoOf T (fsuL0 T L ⊔ T) :=
    ⟨le_sup_right, hyp.fsu.sylow.1, SecA.not_two_dvd_index_of_le hyp.fsu.sylow le_sup_right⟩
  intro r hr
  refine ⟨CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTX hr, ?_⟩
  have hrX : r ∈ fsuL0 T L ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hr
  have hLr := map_conj_mem_cComp' hLX (Subgroup.le_normalizer hrX)
  have hr' : (⟨r, hrX⟩ : ↥(fsuL0 T L ⊔ T)) ∈ CFSG.pCore 2 ↥(fsuL0 T L ⊔ T) := by
    obtain ⟨y, hy, hyr⟩ := hr
    have : y = ⟨r, hrX⟩ := Subtype.ext hyr
    rw [← this]
    exact hy
  have heq : L.map (MulAut.conj r).toMonoidHom = L :=
    modO2Image_injOn _ hLr hLX (modO2Image_map_conj_eq hrX hr' (le_of_mem_cComp hLX))
  exact (Subgroup.mem_normalizer_iff_map_conj_eq).mpr heq

theorem le_fsuM_of_L0T (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I) {Y : Subgroup G}
    (hY : fsuL0 T L ⊔ T ≤ Y) (hY2 : pCoreOf 2 Y ≠ ⊥) : Y ≤ fsuM T L := by
  obtain ⟨M', hM'⟩ := exists_inM_of_pCoreOf_ne_bot hY2
  have h := (isUniqueM_L0T h331 hyp).2 M' ⟨hM'.1, hY.trans hM'.2⟩
  rw [← h]
  exact hM'.2

theorem normalizer_le_fsuM_of_L0T (h331 : Stmt3_3_1) (hyp : Hyp10 G T L I) {R : Subgroup G}
    (hRp : IsPGroup 2 R) (hR1 : R ≠ ⊥) (hRN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (R : Set G)) :
    Subgroup.normalizer (R : Set G) ≤ fsuM T L :=
  le_fsuM_of_L0T h331 hyp hRN (pCoreOf_normalizer_ne_bot' hRp hR1)

theorem hypC23Cat_of_inM (hK : LocalSQTK G) (h331 : Stmt3_3_1) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (hyp : Hyp10 G T L I) {H : Subgroup G}
    (hH : InM (fsuL0 T L ⊔ T1 T L) H) (hS : IsSylowTwoOf (T1 T L) H) :
    EmptyFaithfulMultiple.HypC23Cat H (pCoreOf 2 (fsuL0 T L ⊔ T)) (fsuM T L ⊓ H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 (fsuL0 T L ⊔ T) with hRdef
  have hRp : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hR1 : R ≠ ⊥ := SecA.pCoreOf_L0T_ne_bot hyp
  have hRT1 : R ≤ T1 T L := pCoreOf_L0T_le_T1 hyp
  have hT1H : T1 T L ≤ H := le_sup_right.trans hH.2
  have hL0H : fsuL0 T L ≤ H := le_sup_left.trans hH.2
  have hL0TN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hNR := normalizer_le_fsuM_of_L0T h331 hyp hRp hR1 hL0TN
  refine ⟨hK H (inH_of_inM hH).2, ⟨hRT1.trans hT1H, hR1, ?_⟩, inf_le_right, ?_, ?_⟩
  ·
    refine le_antisymm (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (le_inf (hRT1.trans hT1H) Subgroup.le_normalizer) inf_le_right hRp) ?_
    have hT1N : T1 T L ≤ H ⊓ Subgroup.normalizer (R : Set G) :=
      le_inf hT1H ((inf_le_left.trans le_sup_right).trans hL0TN)
    have hS' : IsSylowTwoOf (T1 T L) (H ⊓ Subgroup.normalizer (R : Set G)) :=
      B6.isSylowTwoOf_mono hS hT1N inf_le_left
    have hP1 := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hS'
    have hLN : fsuL0 T L ⊔ T1 T L ≤ H ⊓ Subgroup.normalizer (R : Set G) :=
      sup_le (le_inf hL0H (le_sup_left.trans hL0TN)) hT1N
    have hP2 : pCoreOf 2 (H ⊓ Subgroup.normalizer (R : Set G)) ≤ pCoreOf 2 (fsuL0 T L ⊔ T1 T L) :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hP1.trans le_sup_right)
        (hLN.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    refine hP2.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans (sup_le_sup_left inf_le_left _)) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _))
    refine le_trans ?_ (SecA.normalizer_le_normalizer_pCoreOf (fsuL0 T L ⊔ T1 T L))
    refine sup_le (le_sup_left.trans Subgroup.le_normalizer) fun s hs => ?_
    have h1 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (le_fsuM T L hs)
    have h2 := Subgroup.mem_normalizer_iff_map_conj_eq.mp (T1_normal h37 h38 hyp hs)
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, h1, h2]
  ·
    refine iSup₂_le fun C hCR => iSup₂_le fun hC1 hCc => ?_
    have hCN : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (C : Set G) := by
      have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (H := R) (C.subgroupOf R)
      rwa [Subgroup.map_subgroupOf_eq_of_le hCR] at h
    exact le_inf (inf_le_right.trans (normalizer_le_fsuM_of_L0T h331 hyp (hRp.to_le hCR) hC1
      (hL0TN.trans hCN))) inf_le_left
  ·
    have hT : IsSylowTwoOf T (fsuM T L) :=
      isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow (le_fsuM T L)
    have h427 := (a4_2_7 (eq_oTwoUpper_of_perfect (fsuL0_perfect' h37 h38 hyp))
      (SecA.fsuL0_le_fsuM T L) (Subgroup.normal_subgroupOf_of_le_normalizer le_rfl) hT rfl
      hNR).2.2.2.2.2
    exact B6.isSylowTwoOf_mono h427 (le_conjClosure R _) (conjClosure_mono le_rfl inf_le_left)

theorem not_le_fsuM (hyp : Hyp10 G T L I) {t : G} (ht : t ∈ T) {X H K : Subgroup G}
    (hX : X = L ∨ X = CFSG.conjugate L t) (hKc : K ∈ cComp H) (hXK : X < K) :
    ¬ K ≤ fsuM T L := by
  intro hKM
  have hloc := hyp.fsu.maximal.1
  have hXL0 : X ≤ fsuL0 T L := by
    rcases hX with rfl | rfl
    · exact SecA.le_fsuL0 T X
    · exact SecA.conjugate_le_fsuL0 ht
  have hXn : ((X.subgroupOf (fsuL0 T L))).Normal := by
    rcases hX with rfl | rfl
    · exact SecA.normal_fsuL0 hloc
    · exact SecA.normal_fsuL0_conjugate hloc ht
  have hXc : X ∈ cComp (fsuM T L) := by
    rcases hX with rfl | rfl
    · exact SecA.mem_cComp_fsuM hloc
    · exact SecA.conjugate_mem_cComp_fsuM hloc (le_fsuM T L ht)
  have hn : ((K ⊓ fsuL0 T L).subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left]
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have h1 := Subgroup.mem_normalizer_iff.mp (hKM hk) h
    have h2 : h ∈ K ↔ k * h * k⁻¹ ∈ K := by
      constructor
      · intro hh
        exact K.mul_mem (K.mul_mem hk hh) (K.inv_mem hk)
      · intro hh
        have := K.mul_mem (K.mul_mem (K.inv_mem hk) hh) hk
        simpa [mul_assoc] using this
    simp only [Subgroup.mem_inf]
    rw [h1, h2]
  have hKL0 : K ≤ fsuL0 T L := by
    rcases normal_eq_top_or_map_le_solvRad hKc ((K ⊓ fsuL0 T L).subgroupOf K) with h | h
    · intro k hk
      have : (⟨k, hk⟩ : ↥K) ∈ (K ⊓ fsuL0 T L).subgroupOf K := by rw [h]; trivial
      exact this.2
    · exfalso
      rw [Subgroup.map_subgroupOf_eq_of_le inf_le_left] at h
      have hXs : X ≤ solvRad K := (le_inf hXK.le hXL0).trans h
      have hsol := solvRad_isSolvable K
      exact not_isSolvable_of_mem_cComp hXc
        (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hXs))
  have hXnK : (X.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hXK.le]
    exact hKL0.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hXL0).mp hXn)
  have hsub : IsSubnormal X H :=
    A4.subnormal_trans (A4.subnormal_of_normal hXK.le hXnK) (subnormal_of_mem_cComp hKc)
  exact not_subnormal_of_mem_cComp hKc hXK (ne_bot_of_mem_cComp hXc) (perfect_of_mem_cComp hXc)
    hsub

end CFSG.Quasithin.Vol2.Ch10.SecB
