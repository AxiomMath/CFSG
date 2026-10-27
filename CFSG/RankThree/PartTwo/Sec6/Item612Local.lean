module

public import CFSG.RankThree.PartTwo.Sec6.Item612Basic
public import CFSG.RankThree.PartTwo.Sec21.PairExistence
public import CFSG.RankThree.PartTwo.Sec4.Statements
import CFSG.GroupTheory.LocalCores.Components
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylow
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylowContainment

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem le_sylow_sup_of_forall_pow_mem [Finite G] {p : ℕ} [Fact p.Prime] {Y N : Subgroup G}
    (hNY : N ≤ Y) (hYN : Y ≤ Subgroup.normalizer (N : Set G))
    (h : ∀ y ∈ Y, ∃ k : ℕ, y ^ (p ^ k) ∈ N) (P : Sylow p Y) :
    Y ≤ (P : Subgroup Y).map Y.subtype ⊔ N := by
  have hn : (N.subgroupOf Y).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNY).mpr hYN
  set π := QuotientGroup.mk' (N.subgroupOf Y)
  have hpg : IsPGroup p (Y ⧸ N.subgroupOf Y) := by
    intro q
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf Y) q
    obtain ⟨k, hk⟩ := h y y.2
    refine ⟨k, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr (by simpa using hk)
  set P' := Sylow.mapSurjective (QuotientGroup.mk'_surjective (N.subgroupOf Y)) P
  have htop : (P' : Subgroup (Y ⧸ N.subgroupOf Y)) = ⊤ :=
    P'.is_maximal' (hpg.to_subgroup ⊤) le_top |>.symm
  intro y hy
  have hmem : π ⟨y, hy⟩ ∈ (P : Subgroup Y).map π := by
    rw [← Sylow.coe_mapSurjective (QuotientGroup.mk'_surjective (N.subgroupOf Y)) P]
    change π ⟨y, hy⟩ ∈ (P' : Subgroup (Y ⧸ N.subgroupOf Y))
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨r, hr, hry⟩ := hmem
  have hrn : r⁻¹ * ⟨y, hy⟩ ∈ N.subgroupOf Y := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hry
    exact hry
  have hy' : y = (r : G) * ((r⁻¹ * ⟨y, hy⟩ : Y) : G) := by simp
  rw [hy']
  exact Subgroup.mul_mem_sup ⟨r, hr, rfl⟩ (Subgroup.mem_subgroupOf.mp hrn)

theorem exists_le_conj_sylow [Finite G] {p : ℕ} [Fact p.Prime] {Y Q : Subgroup G}
    (P : Sylow p Y) (hQY : Q ≤ Y) (hQ : IsPGroup p Q) :
    ∃ y ∈ Y, Q ≤ ((P : Subgroup Y).map Y.subtype).map (MulAut.conj y).toMonoidHom := by
  have hT : IsPGroup p (Q.subgroupOf Y) := hQ.comap_of_injective Y.subtype Y.subtype_injective
  obtain ⟨R, hTR⟩ := IsPGroup.exists_le_sylow hT
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq Y P R
  have hR : ((R : Subgroup Y).map Y.subtype) =
      ((P : Subgroup Y).map Y.subtype).map (MulAut.conj (y : G)).toMonoidHom := by
    rw [← hy, Sylow.coe_subgroup_smul]
    ext z
    simp only [Subgroup.mem_map, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨w, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨b, ⟨b, hb, rfl⟩, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    · rintro ⟨_, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨_, ⟨b, hb, rfl⟩, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
  refine ⟨y, y.2, ?_⟩
  rw [← hR]
  intro z hz
  exact ⟨⟨z, hQY hz⟩, hTR (Subgroup.mem_subgroupOf.mpr hz), rfl⟩

theorem exists_invariant_two_subgroup_not_le_theta [Finite G] {L E V : Subgroup G}
    (hE3 : IsPGroup 3 E) (hEL : E ≤ Subgroup.normalizer (L : Set G)) (hV2 : IsPGroup 2 V)
    (hEV : E ≤ Subgroup.normalizer (V : Set G)) (hVL : V ≤ Subgroup.normalizer (L : Set G))
    (hVLC : V ≤ L ⊔ thetaQuotCentralizer L) (hVE : V ≤ ⁅V, E⁆)
    (hVC : ¬ V ≤ thetaQuotCentralizer L) :
    ∃ U ∈ invariantPiSubgroups L E (piOf 2),
      ¬ ⁅U, E⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set C := thetaQuotCentralizer L with hC
  have hθN := normalizer_le_normalizer_theta L
  have hCN := normalizer_le_normalizer_thetaQuotCentralizer L
  have hθC := theta_le_thetaQuotCentralizer L
  have hLN : L ≤ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer
  set Y := (V ⊔ C) ⊓ L with hY
  set Z := C ⊓ L with hZ
  have hZY : Z ≤ Y := inf_le_inf_right L le_sup_right
  have hYL : Y ≤ L := inf_le_right
  have hYZ : Y ≤ Subgroup.normalizer (Z : Set G) :=
    (le_inf (hYL.trans (hLN.trans hCN)) (hYL.trans hLN)).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hYpow : ∀ y ∈ Y, ∃ k : ℕ, y ^ (2 ^ k) ∈ Z := by
    intro y hy
    obtain ⟨k, hk⟩ := exists_pow_mem_of_mem_sup hV2 (hVL.trans hCN) hy.1
    exact ⟨k, hk, L.pow_mem hy.2 _⟩
  obtain ⟨R⟩ : Nonempty (Sylow 2 Y) := inferInstance
  set RG := (R : Subgroup Y).map Y.subtype with hRG
  have hRGY : RG ≤ Y := Subgroup.map_subtype_le _
  have hRG2 : IsPGroup 2 RG := R.isPGroup'.map Y.subtype
  have hYRZ : Y ≤ RG ⊔ Z := le_sylow_sup_of_forall_pow_mem hZY hYZ hYpow R
  set W := RG ⊔ θL with hW
  have hWL : W ≤ L := sup_le (hRGY.trans hYL) (theta_le L)
  have hRGW : RG ≤ Subgroup.normalizer (W : Set G) := by
    apply le_normalizer_sup_of_conj
    · intro r hr x hx
      exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hr) x).mp
        hx)
    · intro r hr x hx
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
        (le_normalizer_theta L (hYL (hRGY hr))) x).mp hx)
  have hZW : Z ≤ Subgroup.normalizer (W : Set G) := by
    apply le_normalizer_sup_of_conj
    · intro z hz x hx
      have hxL : x ∈ L := hYL (hRGY hx)
      have h1 := (mem_thetaQuotCentralizer_iff.mp hz.1).2 x hxL
      rw [show z * x * z⁻¹ = x * (x⁻¹ * (z * x * z⁻¹)) by group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right h1)
    · intro z hz x hx
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (le_normalizer_theta L hz.2)
        x).mp hx)
  have hYW : Y ≤ Subgroup.normalizer (W : Set G) := hYRZ.trans (sup_le hRGW hZW)
  have hEC : E ≤ Subgroup.normalizer (C : Set G) := hEL.trans hCN
  have hEY : E ≤ Subgroup.normalizer (Y : Set G) := by
    have h1 : E ≤ Subgroup.normalizer ((V ⊔ C : Subgroup G) : Set G) := by
      apply le_normalizer_sup_of_conj
      · intro e he x hx
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hEV he) x).mp hx)
      · intro e he x hx
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hEC he) x).mp hx)
    exact (le_inf h1 hEL).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hEW : E ≤ Subgroup.normalizer (W : Set G) := by
    apply le_normalizer_sup_of_conj
    · intro e he x hx
      set Re := RG.map (MulAut.conj e).toMonoidHom
      have hReY : Re ≤ Y := by
        rintro _ ⟨w, hw, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp (hEY he) w).mp (hRGY hw)
      obtain ⟨y, hyY, hle⟩ := exists_le_conj_sylow R hReY (hRG2.map _)
      have h1 : e * x * e⁻¹ ∈ RG.map (MulAut.conj y).toMonoidHom := hle ⟨x, hx, rfl⟩
      obtain ⟨w, hw, hwx⟩ := h1
      have h2 : y * w * y⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hYW hyY) w).mp (Subgroup.mem_sup_left hw)
      change y * w * y⁻¹ = e * x * e⁻¹ at hwx
      rw [← hwx]
      exact h2
    · intro e he x hx
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hθN (hEL he)) x).mp hx)
  have hW3 : ¬ 3 ∣ Nat.card W := not_dvd_card_sup_of_isPGroup Nat.prime_three (by norm_num) hRG2
    ((hRGY.trans hYL).trans (le_normalizer_theta L)) (theta_solvable_and_not_dvd L).2
  obtain ⟨Q, hEQ⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_in_prime_complement_subgroup
      3 Nat.prime_three E W hE3 hW3 hEW 2 Nat.prime_two
  set U := (Q : Subgroup W).map W.subtype with hU
  have hUW : U ≤ W := Subgroup.map_subtype_le _
  have hU2 : IsPGroup 2 U := Q.isPGroup'.map W.subtype
  refine ⟨U, (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨hUW.trans hWL, hU2, hEQ⟩,
    fun hUE => hVC ?_⟩
  have hWpow : ∀ w ∈ W, ∃ k : ℕ, w ^ (2 ^ k) ∈ θL := fun w hw =>
    exists_pow_mem_of_mem_sup hRG2 ((hRGY.trans hYL).trans (le_normalizer_theta L)) hw
  have hWU : W ≤ U ⊔ θL := le_sylow_sup_of_forall_pow_mem le_sup_right
    (sup_le ((hRGY.trans hYL).trans (le_normalizer_theta L)) Subgroup.le_normalizer) hWpow Q
  have hVYC : V ≤ Y ⊔ C := by
    intro v hv
    have hv' : v ∈ (L : Set G) * (C : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right L C (hLN.trans hCN)]
      exact hVLC hv
    obtain ⟨l, hl, z, hz, rfl⟩ := hv'
    have hlY : l ∈ Y :=
      ⟨by rw [show l = (l * z) * z⁻¹ by group]
          exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right (inv_mem hz)),
        hl⟩
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hlY) (Subgroup.mem_sup_right hz)
  have hVUC : V ≤ U ⊔ C := by
    refine hVYC.trans (sup_le (hYRZ.trans (sup_le ?_ ?_)) le_sup_right)
    · exact (le_sup_left.trans hWU).trans (sup_le le_sup_left (hθC.trans le_sup_right))
    · exact inf_le_left.trans le_sup_right
  have hUCN : U ≤ Subgroup.normalizer (C : Set G) :=
    ((hUW.trans hWL).trans hLN).trans hCN
  calc V ≤ ⁅V, E⁆ := hVE
    _ ≤ ⁅U ⊔ C, E⁆ := Subgroup.commutator_mono hVUC le_rfl
    _ ≤ ⁅U, E⁆ ⊔ C := commutator_sup_le_of_le_normalizer hUCN hEC
    _ ≤ C := sup_le (hUE.trans hθC) le_rfl


theorem inf_thetaQuotCentralizer_le_of_invariant [Finite G] (he : CFSG.Assembly.evenRank G = 3)
    {L A E U : Subgroup G} (hA : CFSG.Assembly.IsElemAbelian 3 A) (hEA : E ≤ A)
    (hE : Nat.card E = 27) (hEL : E ≤ Subgroup.normalizer (L : Set G))
    (hU : U ∈ invariantPiSubgroups L E (piOf 2))
    (hUE : ¬ ⁅U, E⁆ ≤ inSubgroup (aschbacherSolvableCore 3) L) :
    A ⊓ thetaQuotCentralizer L ≤ E := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hUL, hU2, hEU⟩ := (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mp hU
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set C := thetaQuotCentralizer L with hC
  have hθN := normalizer_le_normalizer_theta L
  set F := E ⊔ (A ⊓ C) with hF
  have hFA : F ≤ A := sup_le hEA inf_le_left
  have hFab : CFSG.Assembly.IsElemAbelian 3 F := Sec5.isElemAbelian_of_le hA hFA
  have hF3 : IsPGroup 3 F := Sec5.isPGroup_of_isElemAbelian hFab
  set M := U ⊔ θL with hM
  have hFM : F ≤ Subgroup.normalizer (M : Set G) := by
    apply sup_le
    · apply le_normalizer_sup_of_conj
      · intro e he x hx
        exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hEU he) x).mp hx)
      · intro e he x hx
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hθN (hEL he)) x).mp hx)
    · apply le_normalizer_sup_of_conj
      · intro d hd x hx
        have h1 := (mem_thetaQuotCentralizer_iff.mp hd.2).2 x (hUL hx)
        rw [show d * x * d⁻¹ = x * (x⁻¹ * (d * x * d⁻¹)) by group]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hx) (Subgroup.mem_sup_right h1)
      · intro d hd x hx
        exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp
          (hθN (thetaQuotCentralizer_le_normalizer L hd.2)) x).mp hx)
  have hM3 : ¬ 3 ∣ Nat.card M := not_dvd_card_sup_of_isPGroup Nat.prime_three (by norm_num) hU2
    (hUL.trans (le_normalizer_theta L)) (theta_solvable_and_not_dvd L).2
  obtain ⟨R, hFR⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_in_prime_complement_subgroup
      3 Nat.prime_three F M hF3 hM3 hFM 2 Nat.prime_two
  set RG := (R : Subgroup M).map M.subtype with hRG
  have hRG2 : IsPGroup 2 RG := R.isPGroup'.map M.subtype
  have hRG1 : RG ≠ ⊥ := by
    intro hbot
    obtain ⟨y, -, hle⟩ := exists_le_conj_sylow R (le_sup_left : U ≤ M) hU2
    rw [← hRG, hbot, Subgroup.map_bot] at hle
    apply hUE
    rw [le_bot_iff.mp hle, Subgroup.commutator_bot_left]
    exact bot_le
  have hcard : Nat.card F ≤ 27 := Sec5.card_le_of_le_normalizer he hRG1 hRG2 hFab hFR
  have hEF : E = F := Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hE]; exact hcard)
  rw [hEF]
  exact le_sup_right

theorem map_inSubgroup_theta_of_injective {X Y : Type*} [Group X] [Group Y] [Finite X]
    (f : X →* Y) (hf : Function.Injective f) (L : Subgroup X) :
    (inSubgroup (aschbacherSolvableCore 3) L).map f =
      inSubgroup (aschbacherSolvableCore 3) (L.map f) := by
  rw [inSubgroup, inSubgroup,
    ← aschbacherSolvableCore_map_mulEquiv Nat.prime_three (L.equivMapOfInjective f hf),
    Subgroup.map_map, Subgroup.map_map]
  rfl

theorem le_centralizer_of_mem_thetaComponentsAt {c : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c) : L ≤ Subgroup.centralizer ({c} : Set G) :=
  le_of_mem_thetaComponentsIn hL

theorem isPerfect_of_mem_thetaComponentsAt {c : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c) : Group.IsPerfect L :=
  isPerfect_of_mem_thetaComponentsIn hL

theorem isQuasisimple_of_mem_thetaComponentsAt [Finite G] {c : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c) : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) := by
  obtain ⟨hLC, hL'⟩ := mem_thetaComponentsIn_iff.mp hL
  set e := Subgroup.subgroupOfEquivOfLe hLC
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.congr _ _ e (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)) hL'.2.2

theorem theta_eq_inf_of_mem_thetaComponentsAt [Finite G] {c : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c) :
    inSubgroup (aschbacherSolvableCore 3) L =
      L ⊓ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) := by
  obtain ⟨hLC, hL'⟩ := mem_thetaComponentsIn_iff.mp hL
  set H := Subgroup.centralizer ({c} : Set G)
  have h1 := solvable_prime_complement_core_subnormal_intersection Nat.prime_three hL'.2.1
  have h2 := congrArg (Subgroup.map H.subtype) h1
  have e1 := map_inSubgroup_theta_of_injective H.subtype H.subtype_injective (L.subgroupOf H)
  rw [Subgroup.map_subgroupOf_eq_of_le hLC] at e1
  rw [e1, Subgroup.map_inf_eq _ _ H.subtype H.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hLC] at h2
  exact h2


theorem commutator_le_normalizer_of_mem_thetaComponentsAt [Finite G] {X F L : Subgroup G} {c : G}
    (hXc : X ≤ Subgroup.centralizer ({c} : Set G))
    (hF : ∀ L' ∈ thetaComponentsAt 3 c, F ≤ Subgroup.normalizer (L' : Set G))
    (hL : L ∈ thetaComponentsAt 3 c) : ⁅X, F⁆ ≤ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.commutator_le]
  intro v hv b hb
  have hvc : v ∈ Subgroup.centralizer ({c} : Set G) := hXc hv
  have hcv : (MulAut.conj v⁻¹) c = c := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hvc
    rw [MulAut.conj_apply, inv_inv, mul_assoc, ← hvc, ← mul_assoc, inv_mul_cancel, one_mul]
  have hL' : L.map (MulAut.conj v⁻¹).toMonoidHom ∈ thetaComponentsAt 3 c := by
    have h := map_mem_thetaComponentsAt (MulAut.conj v⁻¹) hL
    rwa [hcv] at h
  have e1 : L.map (MulAut.conj b⁻¹).toMonoidHom = L :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hF L hL (F.inv_mem hb))
  have e2 : (L.map (MulAut.conj v⁻¹).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      L.map (MulAut.conj v⁻¹).toMonoidHom :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hF _ hL' hb)
  have e3 : (L.map (MulAut.conj v⁻¹).toMonoidHom).map (MulAut.conj v).toMonoidHom = L := by
    rw [Subgroup.map_map]
    conv_rhs => rw [← Subgroup.map_id L]
    congr 1
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have e0 : L.map (MulAut.conj ⁅v, b⁆).toMonoidHom =
      (((L.map (MulAut.conj b⁻¹).toMonoidHom).map (MulAut.conj v⁻¹).toMonoidHom).map
        (MulAut.conj b).toMonoidHom).map (MulAut.conj v).toMonoidHom := by
    simp only [Subgroup.map_map]
    congr 1
    ext x
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      commutatorElement_def]
    group
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change L.map (MulAut.conj ⁅v, b⁆).toMonoidHom = L
  rw [e0, e1, e2, e3]

theorem item45_of_item4_5 (h45 : Sec4.Item4_5) : Sec21.Item45 := by
  intro X _ _ hX A hA hor L hL
  refine h45 X hX A hA ?_ L hL
  rcases hor with h | ⟨hab, h27⟩
  · exact Or.inl h
  · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hA
    have h27' : 3 ^ 3 ∣ 3 ^ n := by rw [← hn]; simpa using h27
    exact Or.inr ⟨hab, n, (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h27', hn⟩

theorem le_normalizer_of_mem_thetaComponentsAt {G' : Type} [Group G'] [Finite G']
    (h45 : Sec4.Item4_5) (hG : TheoremFourHyp G') {A : Subgroup G'}
    (hA3 : CFSG.Assembly.IsElemAbelian 3 A) {c : G'} (hcA : c ∈ A) (hc1 : c ≠ 1) :
    ∀ L ∈ thetaComponentsAt 3 c, A ≤ Subgroup.normalizer (L : Set G') :=
  Sec21.le_normalizer_of_item45 (item45_of_item4_5 h45) hG hA3 hcA hc1

theorem commutator_eq_bot_of_mem_partTwoS [Finite G] {A : Subgroup G} (hA : A ∈ partTwoS G)
    {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) {E T : Subgroup G} (hEA : E ≤ A)
    (hT : T ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)))
    (hT2 : IsPGroup 2 T) (hET : E ≤ Subgroup.normalizer (T : Set G)) : ⁅T, E⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd := hA.2.1 a haA ha1
  have hle1 : ⁅T, E⁆ ≤ T := Subgroup.le_normalizer_iff_commutator_le_left.mp hET
  have hle2 : ⁅T, E⁆ ≤ ⁅inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({a} : Set G)), A⁆ := Subgroup.commutator_mono hT hEA
  have h2 : IsPGroup 2 (⁅T, E⁆ : Subgroup G) := hT2.to_le hle1
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  have hdvd := Subgroup.card_dvd_of_le hle2
  rw [hk] at hdvd
  have hk0 : k = 0 := by
    by_contra hk0
    have h2dvd : 2 ∣ 2 ^ k := dvd_pow_self 2 hk0
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2dvd.trans hdvd))
  rw [hk0, pow_zero] at hk
  exact Subgroup.eq_bot_of_card_eq _ hk


theorem isPerfect_inSubgroup_perfectResidual [Finite G] (X : Subgroup G) :
    Group.IsPerfect (inSubgroup perfectResidual X) := by
  obtain ⟨-, -, hperf, -⟩ := perfect_residual_characterization (G := X)
  exact Group.IsPerfect.map X.subtype

theorem theta_ne_of_mem_thetaComponentsAt [Finite G] {c : G} {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt 3 c) : inSubgroup (aschbacherSolvableCore 3) L ≠ L := by
  intro h
  obtain ⟨-, -, a, b, hab⟩ := isQuasisimple_of_mem_thetaComponentsAt hL
  have htop : aschbacherSolvableCore 3 L = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact h
  have : Subsingleton (L ⧸ aschbacherSolvableCore 3 L) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  exact hab (Subsingleton.elim _ _)

theorem mem_lStar_of_inf_le_zpowers [Finite G] {A L : Subgroup G} {c : G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hcA : c ∈ A) (hc1 : c ≠ 1)
    (hL : L ∈ thetaComponentsAt 3 c) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hD : A ⊓ thetaQuotCentralizer L ≤ Subgroup.zpowers c) : L ∈ lStar A := by
  refine ⟨mem_thetaComponentFamily_iff.mpr ⟨c, hcA, hc1, hL⟩, fun K hK hLK => ?_⟩
  obtain ⟨b, hbA, hb1, hKb⟩ := mem_thetaComponentFamily_iff.mp hK
  set θL := inSubgroup (aschbacherSolvableCore 3) L with hθL
  set J := inSubgroup perfectResidual (L ⊓ K) with hJ
  have hLJ : L = J ⊔ θL := hLK
  have hJLK : J ≤ L ⊓ K := Subgroup.map_subtype_le _
  have hKb' : K ≤ Subgroup.centralizer ({b} : Set G) := le_centralizer_of_mem_thetaComponentsAt hKb
  have hbC : b ∈ thetaQuotCentralizer L := by
    refine mem_thetaQuotCentralizer_iff.mpr ⟨hAL hbA, fun l hl => ?_⟩
    have hJθ : J ≤ Subgroup.normalizer (θL : Set G) :=
      (hJLK.trans inf_le_left).trans (le_normalizer_theta L)
    have hl' : l ∈ (J : Set G) * (θL : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right J θL hJθ, ← hLJ]
      exact hl
    obtain ⟨j, hj, t, ht, rfl⟩ := hl'
    have hjb : j * b = b * j := Subgroup.mem_centralizer_singleton_iff.mp (hKb' (hJLK hj).2)
    have htb : b * t * b⁻¹ ∈ θL :=
      (Subgroup.mem_normalizer_iff.mp (normalizer_le_normalizer_theta L (hAL hbA)) t).mp ht
    rw [show (j * t)⁻¹ * (b * (j * t) * b⁻¹) = t⁻¹ * (b * t * b⁻¹) by
      calc (j * t)⁻¹ * (b * (j * t) * b⁻¹) = t⁻¹ * j⁻¹ * ((b * j) * t * b⁻¹) := by group
        _ = t⁻¹ * j⁻¹ * ((j * b) * t * b⁻¹) := by rw [hjb]
        _ = t⁻¹ * (b * t * b⁻¹) := by group]
    exact θL.mul_mem (inv_mem ht) htb
  have hbc : b ∈ Subgroup.zpowers c := hD ⟨hbA, hbC⟩
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hA.2 c hcA) hc1
  have hb3 : orderOf b = 3 := orderOf_eq_prime (hA.2 b hbA) hb1
  have hzb : Subgroup.zpowers b = Subgroup.zpowers c :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hbc)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hb3, hc3])
  have hCbc : Subgroup.centralizer ({b} : Set G) = Subgroup.centralizer ({c} : Set G) := by
    rw [← Subgroup.centralizer_closure, ← Subgroup.zpowers_eq_closure, hzb,
      Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have hKc : K ∈ thetaComponentsAt 3 c := by
    rw [thetaComponentsAt_eq_thetaComponentsIn] at hKb ⊢
    rwa [hCbc] at hKb
  set H := Subgroup.centralizer ({c} : Set G) with hH
  obtain ⟨hLH, hL'⟩ := mem_thetaComponentsIn_iff.mp hL
  obtain ⟨hKH, hK'⟩ := mem_thetaComponentsIn_iff.mp hKc
  have hJH : J ≤ H := (hJLK.trans inf_le_left).trans hLH
  have hJ1 : J.subgroupOf H ≠ ⊥ := by
    intro hbot
    have hJbot : J = ⊥ := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hJH, hbot, Subgroup.map_bot]
    have h1 := hLJ
    rw [hJbot, bot_sup_eq] at h1
    exact theta_ne_of_mem_thetaComponentsAt hL h1.symm
  have hJp : Group.IsPerfect (J.subgroupOf H) := by
    have := isPerfect_inSubgroup_perfectResidual (L ⊓ K)
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hJH).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have heq : L.subgroupOf H = K.subgroupOf H :=
    theta_component_eq_of_perfect_le Nat.prime_three hL' hK' hJ1 hJp
      (fun x hx => Subgroup.mem_subgroupOf.mpr (hJLK (Subgroup.mem_subgroupOf.mp hx)).1)
      (fun x hx => Subgroup.mem_subgroupOf.mpr (hJLK (Subgroup.mem_subgroupOf.mp hx)).2)
  have hLK' : L = K := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hLH, ← Subgroup.map_subgroupOf_eq_of_le hKH, heq]
  rw [← hLK']
  exact llRel_self_of_mem_thetaComponentFamily (mem_thetaComponentFamily_iff.mpr
    ⟨c, hcA, hc1, hL⟩)

end CFSG.RankThree.PartTwo.Sec6
