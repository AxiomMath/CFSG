module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem21Hyp
public import CFSG.Quasithin.Background.G13Wrap
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19W
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem20Four

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp6116

theorem T_le_normalizer_U (h : Hyp6116 G T M L V n) :
    T ≤ Subgroup.normalizer
      ((conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) : Subgroup G) : Set G) :=
  le_normalizer_conjClosure_of_normalizes h.toHyp611.T_le_normalizer
    (h.toHyp611Nat.T_le_normalizer_ZS.trans (F7.normalizer_le_normalizer_centralizer _))

theorem U_le_T (h432 : Stmt4_3_2) (h : Hyp6116 G T M L V n) :
    conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ≤ T :=
  (h.conjClosure_le_S h432).trans inf_le_left

theorem pCoreOf_L1_eq (h432 : Stmt4_3_2) (h : Hyp6116 G T M L V n) :
    pCoreOf 2 (L ⊔ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) =
      (L ⊔ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) ⊓ pCoreOf 2 (L ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) with hU
  have hUT := h.U_le_T h432
  have hL1 : L ⊔ U ≤ L ⊔ T := sup_le_sup_left hUT L
  have hN : L ⊔ T ≤ Subgroup.normalizer ((L ⊔ U : Subgroup G) : Set G) := by
    refine sup_le (fun x hx => ?_) (fun t ht => ?_)
    · exact Subgroup.le_normalizer (Subgroup.mem_sup_left hx)
    · refine mem_normalizer_of_conjSub_le' ?_
      unfold conjSub
      rw [Subgroup.map_sup]
      exact sup_le_sup (conjSub_eq_of_mem_normalizer'
          (h.toHyp611Nat.T_le_normalizer_L ht)).le
        (conjSub_eq_of_mem_normalizer' (h.T_le_normalizer_U ht)).le
  apply le_antisymm
  · refine le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 _) ?_
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hL1)
      (hN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
  · exact (F7.pCoreOf_inf_le hL1).trans' (by rw [inf_comm])

theorem inf_pCoreOf_L1_eq (h432 : Stmt4_3_2) (h : Hyp6116 G T M L V n) :
    conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
        pCoreOf 2 (L ⊔ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) =
      conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
        Subgroup.centralizer (V : Set G) := by
  rw [h.pCoreOf_L1_eq h432, ← h.toHyp611.centralizer_eq]
  have hUT := h.U_le_T h432
  ext x
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hx, -, -, hc⟩
    exact ⟨hx, hc⟩
  · rintro ⟨hx, hc⟩
    exact ⟨hx, Subgroup.mem_sup_right hx, hUT hx, hc⟩

theorem exists_mem_L_conjSub_ZS (h : Hyp6116 G T M L V n) {m : G} (hm : m ∈ ch6MV M V) :
    ∃ l' ∈ L, conjSub m (ch6ZS T L V) = conjSub l' (ch6ZS T L V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL := h.toHyp611.isSylowIn_TL
  have hmL : m ∈ Subgroup.normalizer (L : Set G) := h.normal hm.1
  have hmL' : conjSub m L = L := conjSub_eq_of_mem_normalizer' hmL
  have hmV : conjSub m V = V := conjSub_eq_of_mem_normalizer' hm.2
  have hle : conjSub m (T ⊓ L) ≤ L := by
    have := conjSub_mono m (inf_le_right : T ⊓ L ≤ L)
    rwa [hmL'] at this
  have h2 : IsPGroup 2 (conjSub m (T ⊓ L)) := (h.sylow.1.to_le inf_le_left).map _
  obtain ⟨l', hl', hl'le⟩ := F7.isSylowTwoOf_exists_conj_le hTL hle h2
  have heq : conjSub m (T ⊓ L) = conjSub l' (T ⊓ L) :=
    Subgroup.eq_of_le_of_card_ge hl'le (by rw [card_conjSub', card_conjSub'])
  refine ⟨l', hl', ?_⟩
  have hl'V : conjSub l' V = V :=
    conjSub_eq_of_mem_normalizer' (h.toHyp611.L_le_normalizer hl')
  show conjSub m (V ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)) =
    conjSub l' (V ⊓ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G))
  rw [conjSub_inf, conjSub_inf, hmV, hl'V, conjSub_centralizer', conjSub_centralizer', heq]

omit [Finite G] in
theorem map_conjClosure_eq' (f : G →* G) (Z H : Subgroup G) :
    (conjClosure Z H).map f = conjClosure (Z.map f) (H.map f) := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine CFSG.Quasithin.conjClosure_le fun x hx z hz => ?_
    show f (x * z * x⁻¹) ∈ conjClosure (Z.map f) (H.map f)
    rw [map_mul, map_mul, map_inv]
    exact mem_conjClosure (Subgroup.mem_map_of_mem f hx) (Subgroup.mem_map_of_mem f hz)
  · refine CFSG.Quasithin.conjClosure_le fun x' hx' z' hz' => ?_
    obtain ⟨x, hx, rfl⟩ := hx'
    obtain ⟨z, hz, rfl⟩ := hz'
    exact ⟨x * z * x⁻¹, mem_conjClosure hx hz, by simp⟩

omit [Finite G] in
theorem conjSub_conjClosure' (g : G) (Z H : Subgroup G) :
    conjSub g (conjClosure Z H) = conjClosure (conjSub g Z) (conjSub g H) :=
  map_conjClosure_eq' _ Z H

theorem conjSub_U_eq (h : Hyp6116 G T M L V n) {m : G} (hm : m ∈ ch6MV M V) :
    ∃ l' ∈ L, conjSub m (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) =
      conjSub l' (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) := by
  obtain ⟨l', hl', hml⟩ := h.exists_mem_L_conjSub_ZS hm
  refine ⟨l', hl', ?_⟩
  rw [conjSub_conjClosure', conjSub_conjClosure', conjSub_centralizer', conjSub_centralizer', hml,
    conjSub_eq_of_mem_normalizer' hm.2,
    conjSub_eq_of_mem_normalizer' (h.toHyp611.L_le_normalizer hl')]

theorem normalizer_le_normalizer_L1 (h : Hyp6116 G T M L V n) :
    ch6MV M V ≤ Subgroup.normalizer
      ((L ⊔ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) : Subgroup G) :
        Set G) := by
  intro m hm
  obtain ⟨l', hl', hml⟩ := h.conjSub_U_eq hm
  refine mem_normalizer_of_conjSub_le' ?_
  unfold conjSub
  rw [Subgroup.map_sup]
  change conjSub m L ⊔ conjSub m (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) ≤ _
  rw [conjSub_eq_of_mem_normalizer' (h.normal hm.1), hml]
  refine sup_le le_sup_left ?_
  have := conjSub_mono l' (le_sup_right :
    conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ≤
      L ⊔ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)))
  rwa [conjSub_eq_of_mem_normalizer' (Subgroup.le_normalizer (Subgroup.mem_sup_left hl'))] at this

theorem normalizer_ZS_le_normalizer_U (_h : Hyp6116 G T M L V n) :
    ch6MV M V ⊓ Subgroup.normalizer (ch6ZS T L V : Set G) ≤ Subgroup.normalizer
      ((conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) : Subgroup G) : Set G) :=
  le_normalizer_conjClosure_of_normalizes (inf_le_left.trans inf_le_right)
    (inf_le_right.trans (F7.normalizer_le_normalizer_centralizer _))

theorem exists_mul_eq_of_mem_MV (h : Hyp6116 G T M L V n) {m : G} (hm : m ∈ ch6MV M V) :
    ∃ l' ∈ L, l'⁻¹ * m ∈ ch6MV M V ⊓ Subgroup.normalizer (ch6ZS T L V : Set G) := by
  obtain ⟨l', hl', hml⟩ := h.exists_mem_L_conjSub_ZS hm
  have hl'MV : l' ∈ ch6MV M V := ⟨h.L_le hl', h.toHyp611.L_le_normalizer hl'⟩
  refine ⟨l', hl', Subgroup.mul_mem _ (Subgroup.inv_mem _ hl'MV) hm, ?_⟩
  refine mem_normalizer_of_conjSub_le' ?_
  rw [conjSub_mul, hml, ← conjSub_mul, inv_mul_cancel, conjSub_one]

omit [Finite G] in
theorem secImg_sup_eq {A B X : Subgroup G} [(B.subgroupOf A).Normal] (hXA : X ≤ A)
    (hBA : B ≤ A) (hXB : X ≤ Subgroup.normalizer (B : Set G)) :
    secImg A B (X ⊔ B) = secImg A B X := by
  refine le_antisymm ?_ (secImg_mono le_sup_left)
  rw [secImg_le_iff]
  intro x hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hXB] at hx
  obtain ⟨a, ha, b, hb, hab⟩ := hx
  have hx' : x = ⟨a, hXA ha⟩ * ⟨b, hBA hb⟩ := Subtype.ext hab.symm
  have hb1 : secMk A B ⟨b, hBA hb⟩ = 1 := secMk_eq_one_iff.mpr hb
  rw [hx', map_mul, hb1, mul_one]
  exact secMk_mem_secImg ha

theorem isSylowTwoOf_sup_pCoreOf_L1 (h432 : Stmt4_3_2) (h6111 : Stmt6_1_11)
    (h6119 : Stmt6_1_19) (h : Hyp6116 G T M L V n) :
    IsSylowTwoOf (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊔
        pCoreOf 2 (L ⊔ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))))
      (L ⊔ conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) with hU
  set O := pCoreOf 2 (L ⊔ T) with hO
  have hyp := h.almostSpecialL2Hyp h432 h6111 h6119
  have hS := hyp.G23_one.2
  rw [h.conjClosure_normalizer_eq h432] at hS
  have hUT := h.U_le_T h432
  have hUA : U ≤ L ⊔ T := hUT.trans le_sup_right
  have hL1A : L ⊔ U ≤ L ⊔ T := sup_le le_sup_left hUA
  have hOA : O ≤ L ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hAO : L ⊔ T ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hS0 : IsSylowTwoOf (secImg (L ⊔ T) O U) (secImg (L ⊔ T) O (L ⊔ U)) := hS
  rw [← secImg_sup_eq hUA hOA (hUA.trans hAO), ← secImg_sup_eq hL1A hOA (hL1A.trans hAO)] at hS0
  have hle : U ⊔ O ≤ L ⊔ U ⊔ O := sup_le_sup_right le_sup_right O
  have hidx := relIndex_secImg (A := L ⊔ T) (B := O) le_sup_right hle (sup_le hL1A hOA)
  have hS' : IsSylowTwoOf (U ⊔ O) (L ⊔ U ⊔ O) := by
    refine ⟨hle, IsPGroup.to_sup_of_normal_right' (h.sylow.1.to_le hUT)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) (hUA.trans hAO), ?_⟩
    change ¬ 2 ∣ (U ⊔ O).relIndex (L ⊔ U ⊔ O)
    rw [← hidx]
    exact hS0.2.2
  have hN : U ⊔ O ≤ Subgroup.normalizer ((L ⊔ U : Subgroup G) : Set G) := by
    have hN' : L ⊔ T ≤ Subgroup.normalizer ((L ⊔ U : Subgroup G) : Set G) := by
      refine sup_le (fun x hx => Subgroup.le_normalizer (Subgroup.mem_sup_left hx))
        (fun t ht => ?_)
      refine mem_normalizer_of_conjSub_le' ?_
      unfold conjSub
      rw [Subgroup.map_sup]
      exact sup_le_sup (conjSub_eq_of_mem_normalizer'
          (h.toHyp611Nat.T_le_normalizer_L ht)).le
        (conjSub_eq_of_mem_normalizer' (h.T_le_normalizer_U ht)).le
    exact (sup_le hUA hOA).trans hN'
  have hS'' := F7.isSylowTwoOf_inf_normal hS' le_sup_left hN
  have heq : (U ⊔ O) ⊓ (L ⊔ U) = U ⊔ pCoreOf 2 (L ⊔ U) := by
    rw [h.pCoreOf_L1_eq h432]
    apply le_antisymm
    · rintro x ⟨hx0, hxL⟩
      have hx : x ∈ U ⊔ O := hx0
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
        (hUA.trans hAO)] at hx
      obtain ⟨u, hu, o, ho, rfl⟩ := hx
      have hoL : o ∈ L ⊔ U := by
        have e : o = u⁻¹ * (u * o) := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_right hu)) hxL
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hu) (Subgroup.mem_sup_right ⟨hoL, ho⟩)
    · exact sup_le (le_inf le_sup_left le_sup_right)
        (le_inf (inf_le_right.trans le_sup_right) inf_le_left)
  rwa [heq] at hS''

theorem inf_conjSubgroup_eq_kerIn (h432 : Stmt4_3_2) (h6111 : Stmt6_1_11) (h6119 : Stmt6_1_19)
    (h : Hyp6116 G T M L V n) {l : G} (hl : l ∈ L)
    (hlN : l ∉ Subgroup.normalizer (ch6ZS T L V : Set G)) :
    conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) ⊓
        conjSubgroup (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) l =
      kerIn (conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))) (ch6MV M V) := by
  set U := conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) with hU
  have hyp := h.almostSpecialL2Hyp h432 h6111 h6119
  have h4 := hyp.G23_four hl hlN
  rw [h.conjClosure_normalizer_eq h432] at h4
  have hE1 : U ⊔ rconj U l ≤ Subgroup.normalizer ((U ⊓ rconj U l : Subgroup G) : Set G) :=
    h4.2.2.2.2.1
  have h2 := hyp.G23_two hl hlN
  rw [h.conjClosure_normalizer_eq h432] at h2
  rw [h2] at hE1
  apply le_antisymm
  · intro x hx m hm
    obtain ⟨l', hl', hn⟩ := h.exists_mul_eq_of_mem_MV (Subgroup.inv_mem _ hm)
    have hl'x : l'⁻¹ * x * l'⁻¹⁻¹ ∈ U ⊓ rconj U l :=
      (Subgroup.mem_normalizer_iff.mp
        (hE1 (Subgroup.mem_sup_left (Subgroup.inv_mem _ hl'))) x).mp hx
    have hnU := h.normalizer_ZS_le_normalizer_U (Subgroup.inv_mem _ hn)
    have h1 := (Subgroup.mem_normalizer_iff.mp hnU _).mp hl'x.1
    have e : m * x * m⁻¹ = (l'⁻¹ * m⁻¹)⁻¹ * (l'⁻¹ * x * l'⁻¹⁻¹) * (l'⁻¹ * m⁻¹)⁻¹⁻¹ := by group
    rw [e]
    exact h1
  · intro x hx
    have hlMV : l ∈ ch6MV M V := ⟨h.L_le hl, h.toHyp611.L_le_normalizer hl⟩
    have h1 := hx 1 (Subgroup.one_mem _)
    rw [one_mul, inv_one, mul_one] at h1
    exact ⟨h1, mem_rconj.mpr (hx l hlMV)⟩

end Hyp6116

theorem stmt6_1_21 (h432 : Stmt4_3_2) (h6111 : Stmt6_1_11) (h6119 : Stmt6_1_19) :
    ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ), Hyp6116 G T M L V n →
      ∀ l ∈ L, l ∉ Subgroup.normalizer (ch6ZS T L V : Set G) →
        let U := conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G))
        let L₁ := U ⊔ conjSubgroup U l
        let R := pCoreOf 2 L₁
        let E := U ⊓ conjSubgroup U l
        (L₁ = conjClosure U (ch6MV M V) ∧ ch6MV M V ≤ Subgroup.normalizer (L₁ : Set G) ∧
          L₁ = L ⊔ U) ∧
        (R = (U ⊓ Subgroup.centralizer (V : Set G)) ⊔
            (conjSubgroup U l ⊓ Subgroup.centralizer (V : Set G)) ∧
          IsSylowIn 2 (U ⊔ R) L₁) ∧
        (IsElemAbelian 2 E ∧ ⁅E, L₁⁆ ≤ V ∧ E = kerIn U (ch6MV M V) ∧
          ch6MV M V ≤ Subgroup.normalizer (E : Set G)) ∧
        (IsElemAbelianMod R E ∧
          (U ⊓ Subgroup.centralizer (V : Set G)) ⊓
              (conjSubgroup U l ⊓ Subgroup.centralizer (V : Set G)) = E ∧
          U ⊓ Subgroup.centralizer (V : Set G) = centralizerMod E R U) ∧
        (ch6MV M V ≤ Subgroup.normalizer (R : Set G) ∧ R ≤ pCoreOf 2 (ch6MV M V)) := by
  intro G _ _ T M L V n h l hl hlN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  dsimp only
  set U := conjClosure V (Subgroup.centralizer (ch6ZS T L V : Set G)) with hU
  have hyp := h.almostSpecialL2Hyp h432 h6111 h6119
  have hUeq := h.conjClosure_normalizer_eq h432
  have hrc : ∀ X : Subgroup G, rconj X l = conjSubgroup X l := fun X => rfl
  have h2 := hyp.G23_two hl hlN
  have h4 := hyp.G23_four hl hlN
  have h5 := hyp.G23_five hl hlN
  rw [hUeq, hrc] at h2 h4 h5
  have hL1 : U ⊔ conjSubgroup U l = L ⊔ U := h2
  have h3 := hyp.G23_three (U := conjClosure V (Subgroup.normalizer (ch6ZS T L V : Set G)))
    rfl hl hlN rfl rfl rfl
  have h6 := hyp.G23_six' (U := conjClosure V (Subgroup.normalizer (ch6ZS T L V : Set G)))
    rfl hl hlN rfl rfl rfl
  rw [hUeq, hrc, hL1] at h3 h6
  rw [hrc] at h3 h6
  have hW : U ⊓ pCoreOf 2 (L ⊔ U) = U ⊓ Subgroup.centralizer (V : Set G) :=
    h.inf_pCoreOf_L1_eq h432
  have hlV : l⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.inv_mem _ (h.toHyp611.L_le_normalizer hl)
  have hWl : conjSubgroup (U ⊓ pCoreOf 2 (L ⊔ U)) l =
      conjSubgroup U l ⊓ Subgroup.centralizer (V : Set G) := by
    rw [hW]
    show conjSub l⁻¹ (U ⊓ Subgroup.centralizer (V : Set G)) =
      conjSub l⁻¹ U ⊓ Subgroup.centralizer (V : Set G)
    rw [conjSub_inf, conjSub_centralizer', conjSub_eq_of_mem_normalizer' hlV]
  have hMVL1 := h.normalizer_le_normalizer_L1
  have hlMV : l ∈ ch6MV M V := ⟨h.L_le hl, h.toHyp611.L_le_normalizer hl⟩
  have hUMV : U ≤ ch6MV M V :=
    le_inf ((h.U_le_T h432).trans h.T_le) ((h.conjClosure_le_S h432).trans
      (inf_le_left.trans h.toHyp611.T_le_normalizer))
  have hL1MV : L ⊔ U ≤ ch6MV M V :=
    sup_le (le_inf h.L_le h.toHyp611.L_le_normalizer) hUMV
  have hE := h.inf_conjSubgroup_eq_kerIn h432 h6111 h6119 hl hlN
  rw [hL1] at h5 ⊢
  refine ⟨⟨?_, hMVL1, rfl⟩, ⟨?_, h.isSylowTwoOf_sup_pCoreOf_L1 h432 h6111 h6119⟩,
    ⟨h5.2, h5.1, hE, ?_⟩, ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  ·
    apply le_antisymm
    · rw [← hL1]
      refine sup_le (le_conjClosure U _) ?_
      exact Hyp6116.conjSub_le_conjClosure (Subgroup.inv_mem _ hlMV)
    · refine CFSG.Quasithin.conjClosure_le fun m hm u hu => ?_
      exact (Subgroup.mem_normalizer_iff.mp (hMVL1 hm) u).mp (Subgroup.mem_sup_right hu)
  ·
    rw [h3.1, hWl, hW]
  ·
    rw [hE]
    intro m hm
    refine mem_normalizer_of_forall_conj_mem_of_le fun x hx b hb => ?_
    have := hx (b * m) (Subgroup.mul_mem _ hb hm)
    have e : b * (m * x * m⁻¹) * b⁻¹ = b * m * x * (b * m)⁻¹ := by group
    rw [e]
    exact this
  ·
    obtain ⟨s, β, φ, -, -, hφs, hφk, -⟩ := h6.1
    intro u hu v hv
    have hcomm : φ (⟨u, hu⟩ * ⟨v, hv⟩ * ⟨u, hu⟩⁻¹ * ⟨v, hv⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (φ ⟨u, hu⟩) (φ ⟨v, hv⟩)]
      group
    have hsq : φ (⟨u, hu⟩ ^ 2) = 1 := by
      rw [map_pow, pow_two]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_one]
      funext j i
      simp only [Pi.add_apply, Pi.zero_apply]
      exact CharTwo.add_self_eq_zero _
    exact ⟨(hφk _).mp hcomm, (hφk _).mp hsq⟩
  ·
    rw [← hWl, ← hW]
    exact h6.2.1
  ·
    rw [← hW]
    ext x
    rw [mem_centralizerMod]
    constructor
    · intro hx
      have hN4 : L ⊔ U ≤ Subgroup.normalizer
          ((U ⊓ conjSubgroup U l : Subgroup G) : Set G) := hL1 ▸ h4.2.2.2.2.1
      refine ⟨hx.2, hN4 (CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx.2), fun u hu => ?_⟩
      have := ((h6.2.2.2 x hx.2).mp hx) u hu
      have e : x * u * x⁻¹ * u⁻¹ = ⁅u, x⁆⁻¹ := by rw [commutatorElement_def]; group
      rw [e]
      exact Subgroup.inv_mem _ this
    · rintro ⟨hxR, -, hxu⟩
      refine (h6.2.2.2 x hxR).mpr fun u hu => ?_
      have := Subgroup.inv_mem _ (hxu u hu)
      have e : (x * u * x⁻¹ * u⁻¹)⁻¹ = ⁅u, x⁆ := by rw [commutatorElement_def]; group
      rwa [e] at this
  ·
    exact hMVL1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  ·
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hL1MV)
      (hMVL1.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)

end CFSG.Quasithin.H13
