module

public import CFSG.RankThree.PartTwo.Sec18.Item186a
import CFSG.RankThree.PartTwo.Sec18.Claim184LcProof
import CFSG.RankThree.PartTwo.Sec18.Item183KSylow
import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.RankThree.PartTwo.Sec18.Item183KStatements

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

namespace Item183NMProof

theorem commute_of_commutator_commute {X : Type*} [Group X] {P : Subgroup X} (hP : ⁅P, P⁆ = P)
    {x : X} (hxP : ∀ l ∈ P, x * l * x⁻¹ ∈ P)
    (hz : ∀ l ∈ P, ∀ m ∈ P, x * l * x⁻¹ * l⁻¹ * m = m * (x * l * x⁻¹ * l⁻¹)) {l : X}
    (hl : l ∈ P) : x * l = l * x := by
  let f : P →* Subgroup.center P :=
    { toFun := fun l => ⟨⟨x * l * x⁻¹ * l⁻¹, P.mul_mem (hxP l l.2) (P.inv_mem l.2)⟩,
        Subgroup.mem_center_iff.mpr fun m => Subtype.ext (hz l l.2 m m.2).symm⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        show x * 1 * x⁻¹ * 1⁻¹ = 1
        group
      map_mul' := fun l m => by
        apply Subtype.ext
        apply Subtype.ext
        show x * ((l : X) * m) * x⁻¹ * ((l : X) * m)⁻¹ =
          x * l * x⁻¹ * (l : X)⁻¹ * (x * m * x⁻¹ * (m : X)⁻¹)
        have h1 := hz m m.2 (l : X)⁻¹ (P.inv_mem l.2)
        calc x * ((l : X) * m) * x⁻¹ * ((l : X) * m)⁻¹
            = (x * l * x⁻¹) * (x * m * x⁻¹ * (m : X)⁻¹ * (l : X)⁻¹) := by group
          _ = (x * l * x⁻¹) * ((l : X)⁻¹ * (x * m * x⁻¹ * (m : X)⁻¹)) := by rw [h1]
          _ = x * l * x⁻¹ * (l : X)⁻¹ * (x * m * x⁻¹ * (m : X)⁻¹) := by group }
  have : Group.IsPerfect P := (Subgroup.isPerfect_iff).mpr hP
  have hker : commutator P ≤ f.ker := Abelianization.commutator_subset_ker f
  have h1 : f ⟨l, hl⟩ = 1 := by
    have hmem : (⟨l, hl⟩ : P) ∈ commutator P := by
      rw [Group.IsPerfect.commutator_eq_top]
      trivial
    exact hker hmem
  have h2 : x * l * x⁻¹ * l⁻¹ = 1 := congrArg (fun z : Subgroup.center P => ((z : P) : X)) h1
  calc x * l = x * l * x⁻¹ * l⁻¹ * (l * x) := by group
    _ = l * x := by rw [h2, one_mul]

variable {G : Type} [Group G] [Finite G]

theorem le_of_forall_commutator_mem {H Y W : Subgroup G} (hYH : Y ≤ H) (hYp : ⁅Y, Y⁆ = Y)
    (hYimg : (Y.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 H)) =
      (perfectResidual H).map (QuotientGroup.mk' (CFSG.pCore 2 H)))
    (hq : CFSG.IsQuasisimple ((perfectResidual H).map (QuotientGroup.mk' (CFSG.pCore 2 H))))
    {d : G} (hdH : d ∈ H)
    (hd : QuotientGroup.mk' (CFSG.pCore 2 H) ⟨d, hdH⟩ ∉ Subgroup.centralizer
      (((perfectResidual H).map (QuotientGroup.mk' (CFSG.pCore 2 H)) : Subgroup _) : Set _))
    (hWY : W ≤ Y) (hWn : ∀ y ∈ Y, ∀ w ∈ W, y * w * y⁻¹ ∈ W)
    (hWd : ∀ y ∈ Y, d * y * d⁻¹ * y⁻¹ ∈ W) : Y ≤ W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.pCore 2 H with hQ
  set π : H →* H ⧸ Q := QuotientGroup.mk' Q with hπ
  set Lb := (perfectResidual H).map π with hLb
  set Wb := (W.subgroupOf H).map π with hWb
  have hYL : ∀ l ∈ Lb, ∃ y : H, (y : G) ∈ Y ∧ π y = l := by
    intro l hl
    rw [← hYimg] at hl
    obtain ⟨y, hy, rfl⟩ := hl
    exact ⟨y, Subgroup.mem_subgroupOf.mp hy, rfl⟩
  have hYL' : ∀ y : H, (y : G) ∈ Y → π y ∈ Lb := by
    intro y hy
    rw [← hYimg]
    exact ⟨y, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hWbL : Wb ≤ Lb := by
    rintro _ ⟨w, hw, rfl⟩
    rw [← hYimg]
    exact ⟨w, Subgroup.mem_subgroupOf.mpr (hWY (Subgroup.mem_subgroupOf.mp hw)), rfl⟩
  have hWbn : (Wb.subgroupOf Lb).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨w, hw, hwn⟩ := hn
    obtain ⟨y, hy, hyg⟩ := hYL g g.2
    refine ⟨y * w * y⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (hWn y hy w (Subgroup.mem_subgroupOf.mp hw))
    · rw [map_mul, map_mul, map_inv, hyg, hwn]
      rfl
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq hWbn with
    htop | hcen
  ·
    have hLW : Lb ≤ Wb := (Subgroup.subgroupOf_eq_top).mp htop
    have hN : (W.subgroupOf Y).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact hWn g g.2 n hn
    have h2 : IsPGroup 2 (Y ⧸ W.subgroupOf Y) := by
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨w, hw, hwy⟩ := hLW (hYL' ⟨y, hYH y.2⟩ y.2)
      have hwW : (w : G) ∈ W := Subgroup.mem_subgroupOf.mp hw
      have hwY : (w : G) ∈ Y := hWY hwW
      have hr : w⁻¹ * ⟨y, hYH y.2⟩ ∈ Q := by
        rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_inv, hwy,
          inv_mul_cancel]
      rw [mem_pCore_iff_mem_pCoreOf] at hr
      obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H ⟨_, hr⟩
      have hrY : (w : G)⁻¹ * y ∈ Y := Y.mul_mem (Y.inv_mem hwY) y.2
      refine ⟨k, ?_⟩
      have hyeq : y = ⟨w, hwY⟩ * ⟨(w : G)⁻¹ * y, hrY⟩ := Subtype.ext (by simp)
      have hmkw : (QuotientGroup.mk (⟨w, hwY⟩ : Y) : Y ⧸ W.subgroupOf Y) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hwW)
      have hpow : (⟨(w : G)⁻¹ * y, hrY⟩ : Y) ^ (2 ^ k) = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hk)
      rw [hyeq, QuotientGroup.mk_mul, hmkw, one_mul, ← QuotientGroup.mk_pow, hpow,
        QuotientGroup.mk_one]
    have hs : Group.IsSolvable (Y ⧸ W.subgroupOf Y) := by
      have := h2.isNilpotent
      infer_instance
    exact (le_inSubgroup_perfectResidual hYp le_rfl).trans
      (inSubgroup_perfectResidual_le_of_isSolvable hWY hs)
  ·
    exfalso
    apply hd
    have hLp : ⁅Lb, Lb⁆ = Lb := (Subgroup.isPerfect_iff).mp hq.1
    have hcomm : ∀ y : H, (y : G) ∈ Y →
        π ⟨d, hdH⟩ * π y * (π ⟨d, hdH⟩)⁻¹ * (π y)⁻¹ ∈ Wb := by
      intro y hy
      refine ⟨⟨d, hdH⟩ * y * ⟨d, hdH⟩⁻¹ * y⁻¹, Subgroup.mem_subgroupOf.mpr (hWd y hy), ?_⟩
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    have hxP : ∀ l ∈ Lb, π ⟨d, hdH⟩ * l * (π ⟨d, hdH⟩)⁻¹ ∈ Lb := by
      intro l hl
      obtain ⟨y, hy, rfl⟩ := hYL l hl
      have hdy : ((⟨d, hdH⟩ * y * ⟨d, hdH⟩⁻¹ : H) : G) ∈ Y := by
        have e : ((⟨d, hdH⟩ * y * ⟨d, hdH⟩⁻¹ : H) : G) = (d * y * d⁻¹ * (y : G)⁻¹) * y := by
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          group
        rw [e]
        exact Y.mul_mem (hWY (hWd y hy)) hy
      have h1 := hYL' _ hdy
      rwa [map_mul, map_mul, map_inv] at h1
    have hz : ∀ l ∈ Lb, ∀ m ∈ Lb, π ⟨d, hdH⟩ * l * (π ⟨d, hdH⟩)⁻¹ * l⁻¹ * m =
        m * (π ⟨d, hdH⟩ * l * (π ⟨d, hdH⟩)⁻¹ * l⁻¹) := by
      intro l hl m hm
      obtain ⟨y, hy, rfl⟩ := hYL l hl
      have hmem : (⟨_, hWbL (hcomm y hy)⟩ : Lb) ∈ Wb.subgroupOf Lb :=
        Subgroup.mem_subgroupOf.mpr (hcomm y hy)
      have h1 := Subgroup.mem_center_iff.mp (hcen hmem) ⟨m, hm⟩
      exact (congrArg Subtype.val h1).symm
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (commute_of_commutator_commute hLp hxP hz hl).symm

omit [Finite G] in
theorem le_map_of_isSubnormal {C : Subgroup G} {K' : Subgroup C} (hK : K'.IsSubnormal)
    {Y D : Subgroup G} (hYC : Y ≤ C) (hDK : D ≤ K'.map C.subtype)
    (hDY : ∀ d ∈ D, ∀ y ∈ Y, d * y * d⁻¹ ∈ Y)
    (hW : ∀ W : Subgroup G, W ≤ Y → (∀ y ∈ Y, ∀ w ∈ W, y * w * y⁻¹ ∈ W) →
      (∀ y ∈ Y, ∀ d ∈ D, d * y * d⁻¹ * y⁻¹ ∈ W) → Y ≤ W) :
    Y ≤ K'.map C.subtype := by
  have claim : ∀ U : Subgroup C, U.IsSubnormal → D ≤ U.map C.subtype → Y ≤ U.map C.subtype := by
    intro U hU
    induction hU with
    | top =>
      intro _
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      exact hYC
    | step U V hUV hV hN ih =>
      intro hDU
      have hYV : Y ≤ V.map C.subtype := ih (hDU.trans (Subgroup.map_mono hUV))
      have hconj : ∀ v ∈ V.map C.subtype, ∀ u ∈ U.map C.subtype,
          v * u * v⁻¹ ∈ U.map C.subtype := by
        rintro _ ⟨v, hv, rfl⟩ _ ⟨u, hu, rfl⟩
        have h1 := hN.conj_mem ⟨u, hUV hu⟩ (Subgroup.mem_subgroupOf.mpr hu) ⟨v, hv⟩
        rw [Subgroup.mem_subgroupOf] at h1
        exact ⟨_, h1, by simp⟩
      have hle := hW (Y ⊓ U.map C.subtype) inf_le_left
        (fun y hy w hw => ⟨Y.mul_mem (Y.mul_mem hy hw.1) (Y.inv_mem hy),
          hconj y (hYV hy) w hw.2⟩)
        (fun y hy d hd => by
          refine ⟨Y.mul_mem (hDY d hd y hy) (Y.inv_mem hy), ?_⟩
          have e : d * y * d⁻¹ * y⁻¹ = d * (y * d⁻¹ * y⁻¹) := by group
          rw [e]
          exact (U.map C.subtype).mul_mem (hDU hd)
            (hconj y (hYV hy) d⁻¹ ((U.map C.subtype).inv_mem (hDU hd))))
      exact hle.trans inf_le_right
  exact claim K' hK hDK

theorem forall_mem_pCoreOf_iff {H : Subgroup G} {a : G} (ha : a ∈ H) :
    (∀ x ∈ inSubgroup perfectResidual H,
        a * x * a⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H)) ↔
      QuotientGroup.mk' (CFSG.pCore 2 H) ⟨a, ha⟩ ∈ Subgroup.centralizer
        (((perfectResidual H).map (QuotientGroup.mk' (CFSG.pCore 2 H)) : Subgroup _) : Set _) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : H →* H ⧸ CFSG.pCore 2 H := QuotientGroup.mk' (CFSG.pCore 2 H) with hπ
  set R := CFSG.Open.pCoreOf 2 H with hRdef
  set L := inSubgroup perfectResidual H with hLdef
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  have hmemR : ∀ x : H, π x = 1 ↔ (x : G) ∈ R := by
    intro x
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_pCore_iff_mem_pCoreOf]
  have hRL : R ⊓ L ≤ CFSG.Open.pCoreOf 2 L :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hLH hx), Subgroup.le_normalizer hx⟩)
      (hR2.to_le inf_le_left)
  have hO : CFSG.Open.pCoreOf 2 L ≤ R :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLH)
      ((le_normalizer_inSubgroup_perfectResidual H).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨x, hx, rfl⟩
    have hxL : (x : G) ∈ L := ⟨x, hx, rfl⟩
    have h1 := (hmemR (⟨a, ha⟩ * x * ⟨a, ha⟩⁻¹ * x⁻¹)).mpr (hO (hc _ hxL))
    simp only [map_mul, map_inv] at h1
    calc π x * π ⟨a, ha⟩ =
        π ⟨a, ha⟩ * π x * (π ⟨a, ha⟩)⁻¹ * (π x)⁻¹ * (π x * π ⟨a, ha⟩) := by
          rw [h1, one_mul]
      _ = π ⟨a, ha⟩ * π x := by group
  · intro hc x hxL
    obtain ⟨x', hx', rfl⟩ := hxL
    have h1 := Subgroup.mem_centralizer_iff.mp hc (π x') ⟨x', hx', rfl⟩
    have h2 : π (⟨a, ha⟩ * x' * ⟨a, ha⟩⁻¹ * x'⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [← h1]
      group
    have h3 := (hmemR _).mp h2
    refine hRL ⟨h3, ?_⟩
    have hxLG : (x' : G) ∈ L := ⟨x', hx', rfl⟩
    have haN : a ∈ Subgroup.normalizer (L : Set G) :=
      le_normalizer_inSubgroup_perfectResidual H ha
    show a * (x' : G) * a⁻¹ * (x' : G)⁻¹ ∈ L
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp haN _).mp hxLG) (L.inv_mem hxLG)

theorem isQuasisimple_map_perfectResidual {H : Subgroup G}
    (hL : inSubgroup perfectResidual H ∈ oTwoComponentsIn H) :
    CFSG.IsQuasisimple ((perfectResidual H).map (QuotientGroup.mk' (CFSG.pCore 2 H))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := inSubgroup perfectResidual H with hLdef
  have hLH : L ≤ H := Subgroup.map_subtype_le _
  have hLO : CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hLH)
      ((le_normalizer_inSubgroup_perfectResidual H).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
  obtain ⟨eL⟩ := Claim184LcProof.quotient_mulEquiv_map hLH hLO
  have hLimg : (L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 H)) =
      (perfectResidual H).map (QuotientGroup.mk' (CFSG.pCore 2 H)) := by
    have : L.subgroupOf H = perfectResidual H :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
    rw [this]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (eL.trans (MulEquiv.subgroupCongr hLimg))
    (isQuasisimple_of_mem_oTwoComponentsIn hL)

theorem generalizedFitting_eq_of_pCoreOf_le (hchar : CFSG.Assembly.IsCharTwoType G)
    {N H : Subgroup G} (hN : CFSG.Assembly.IsTwoLocal N) (hHN : H ≤ N)
    (hOH : CFSG.Open.pCoreOf 2 N ≤ H) : CFSG.generalizedFitting H = CFSG.pCore 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCoreOf 2 H with hQdef
  set R := CFSG.Open.pCoreOf 2 N with hRdef
  have hRQ : R ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hOH
    (hHN.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 N))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
  have hcen : H ⊓ Subgroup.centralizer (Q : Set G) ≤ Q := by
    intro x hx
    have hxN : x ∈ N ⊓ Subgroup.centralizer (CFSG.Assembly.pCoreOf 2 N : Set G) :=
      ⟨hHN hx.1, Subgroup.centralizer_le hRQ hx.2⟩
    exact hRQ (hchar N hN hxN)
  have hP : CFSG.IsCharacteristicP 2 H := by
    change Subgroup.centralizer (CFSG.pCore 2 H : Set H) ≤ CFSG.pCore 2 H
    intro x hx
    have hxQ : (x : G) ∈ Q := by
      refine hcen ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
      obtain ⟨q', hq', rfl⟩ := hq
      have hq'' : q' ∈ CFSG.pCore 2 H := by exact hq'
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx q' hq'')
    exact (mem_pCore_iff_mem_pCoreOf x).mpr hxQ
  exact (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore H 2).mp hP

end Item183NMProof

variable {G : Type} [Group G] [Finite G] {A M K E : Subgroup G} {c : G}

theorem Diag183.le_of_mem_scriptM (hD : Diag183 G A M c K E) {N : Subgroup G}
    (hN : N ∈ scriptM (gamma 2 E : Set G)) : K ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : IsE27 E := isE27_of_mem_partTwoE hD.E_mem_partTwoE
  have hΓ : gamma 2 E ≤ N := fun x hx => hN.2 hx
  have hEK : E ≤ Subgroup.normalizer (K : Set G) :=
    hD.E_le.trans (inf_le_left.trans hD.toHyp183.sup_le_normalizer)
  set R := CFSG.Open.pCoreOf 2 K with hRdef
  have hR2 : IsPGroup 2 R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hER : E ≤ Subgroup.normalizer (R : Set G) :=
    hEK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hKR : K ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  obtain ⟨B, hB⟩ := exists_subgroup_eq_sectionCentralizer hEK
  have hmem : ∀ x ∈ B, x ∈ E ∧ ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ R := fun x hx => by
    have hx' : x ∈ (B : Set G) := hx
    rwa [hB] at hx'
  have hBE : B ≤ E := fun x hx => (hmem x hx).1
  have hB9 : 9 ≤ Nat.card B :=
    nine_le_card_of_not_subset_zpowers (fun x hx => hE.1.2 x (hBE hx))
      (by rw [hB]; exact hD.sectionCentralizer_noncyclic)
  have hB2 : 2 ≤ CFSG.Open.pRank 3 B :=
    two_le_pRank_of_elemAbelian (isElemAbelian_of_le hE.1 hBE) hB9
  have hcomm : ∀ k ∈ K, ∀ b ∈ B, k * b * k⁻¹ * b⁻¹ ∈ R := by
    intro k hk b hb
    have h1 := R.inv_mem ((hmem b hb).2 k hk)
    have e : (b * k * b⁻¹ * k⁻¹)⁻¹ = k * b * k⁻¹ * b⁻¹ := by group
    rwa [e] at h1
  exact le_of_commutator_le_of_gamma_le hE hΓ hBE hB2 hR2 hER hKR hcomm

end CFSG.RankThree.PartTwo.Sec18
