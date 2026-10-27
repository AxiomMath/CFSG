module

public import CFSG.Quasithin.Background.RonanE611Torus
public import CFSG.Quasithin.Background.ONanE68Lin3
public import CFSG.Quasithin.Background.ONanE68RankOneCore
public import CFSG.Quasithin.Background.ONanE68Sp4
public import CFSG.Quasithin.Background.ONanE68LieBar
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Background.ONanE68RankOneModel

public section

namespace CFSG.Quasithin.RonanE611

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.E6.E68Proof CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Types

variable {A : Type} [Group A] [Finite A]

theorem card_center_sylow_modelOf {q k : ℕ} (h : ModelOf A q k) {P : Subgroup A}
    (hP : IsSylowTwoOf P ⊤) : Nat.card (Subgroup.center ↥P) = q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hP2, hPidx⟩ := isPGroup_and_not_dvd_index hP
  have hB := h.fusionBenderBorel (hP2.toSylow hPidx)
  exact hB.2.2.2.1

theorem exists_unitriangular_iso {n : ℕ} (hA : StatedClassicalModel A .PSL 3 2 n)
    {P : Subgroup A} (hP : IsSylowTwoOf P ⊤) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (φ : A ≃* projectiveSL 3 K),
      Nat.card K = 2 ^ n ∧ P.map φ.toMonoidHom = projUnitriangular 3 K := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  let e₁ : A ≃* projectiveSL 3 K :=
    (e.trans (projectiveSpecialLinearGroupEquivStatedProj 3 K).symm).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL 3 K)
  obtain ⟨hP2, hPidx⟩ := isPGroup_and_not_dvd_index hP
  obtain ⟨φ, hφ⟩ := Lin3.exists_mulEquiv_map_eq_projUnitriangular e₁ hP2 hPidx
  exact ⟨K, inferInstance, inferInstance, inferInstance, φ, hK, hφ⟩

theorem card_center_sylow_le_lin3 {n : ℕ} (hn : 2 ≤ n)
    (hA : StatedClassicalModel A .PSL 3 2 n) {P : Subgroup A} (hP : IsSylowTwoOf P ⊤) :
    Nat.card (Subgroup.center ↥P) ≤ 2 ^ n := by
  classical
  have hdata := e68Lin3Data_holds A n hn hA P hP
  have hsq : ∀ z ∈ Subgroup.center ↥P, z ^ 2 = 1 := by
    obtain ⟨K, _, _, _, φ, -, hφ⟩ := exists_unitriangular_iso hA hP
    intro z hz
    have hzP : (z : A) ∈ P := z.2
    have h1 : φ (z : A) ∈ projUnitriangular 3 K := by
      rw [← hφ]
      exact Subgroup.mem_map_of_mem _ hzP
    have h2 : ∀ y ∈ projUnitriangular 3 K, φ (z : A) * y = y * φ (z : A) := by
      intro y hy
      rw [← hφ] at hy
      obtain ⟨y', hy', rfl⟩ := hy
      change φ (z : A) * φ y' = φ y' * φ (z : A)
      rw [← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨y', hy'⟩).symm
    have h3 := sq_eq_one_of_central_projUnitriangular h1 h2
    have h4 : φ ((z : A) * (z : A)) = 1 := by rw [map_mul]; exact h3
    have h5 : (z : A) * (z : A) = 1 := φ.injective (by rw [h4, map_one])
    exact Subtype.ext (by simpa [pow_two] using h5)
  rw [← hdata.card_root,
    RankOne.omegaCenter_eq_map_center hsq,
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]

end Types

section Sup

variable {G : Type} [Group G] [Finite G] {L S W : Subgroup G} {n : ℕ}

theorem card_map_of_injOn {G' N : Type*} [Group G'] [Group N] (f : G' →* N) (H : Subgroup G')
    (hinj : ∀ x ∈ H, ∀ y ∈ H, f x = f y → x = y) : Nat.card (H.map f) = Nat.card H := by
  symm
  refine Nat.card_congr (Equiv.ofBijective (f.subgroupMap H)
    ⟨fun a b hab => ?_, f.subgroupMap_surjective H⟩)
  exact Subtype.ext (hinj a a.2 b b.2 (congrArg Subtype.val hab))

theorem mem_centerOf_iff_center {x : G} :
    x ∈ centerOf L ↔ ∃ z ∈ Subgroup.center ↥L, (z : G) = x := by
  constructor
  · rintro ⟨hxL, hxc⟩
    refine ⟨⟨x, hxL⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxc g g.2)
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨g, hg⟩)

theorem center_le_of_isSylowTwoOf (hS : IsSylowTwoOf S L) (hZ : IsPGroup 2 (Subgroup.center ↥L)) :
    ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ S := by
  intro z hz
  have hzp : z ∈ CFSG.Open.pCore 2 ↥L :=
    CFSG.LieType.BorelTits.le_pCore 2 inferInstance hZ hz
  have h1 : (z : G) ∈ pCoreOf 2 L := ⟨z, hzp, rfl⟩
  exact EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS h1

theorem centerOf_sylow_eq_sup (hS : IsSylowTwoOf S L) (hZ : IsPGroup 2 (Subgroup.center ↥L))
    (hbar : ∀ P : Subgroup (↥L ⧸ Subgroup.center ↥L), IsSylowTwoOf P ⊤ →
      Nat.card (Subgroup.center ↥P) ≤ 2 ^ n)
    (hWS : W ≤ S) (hWc : ∀ w ∈ W, ∀ s ∈ S, w * s = s * w) (hWcard : Nat.card W = 2 ^ n)
    (hWZ : ∀ w ∈ W, w ∈ centerOf L → w = 1) :
    centerOf S = centerOf L ⊔ W := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSL : S ≤ L := hS.1
  have hZS := center_le_of_isSylowTwoOf hS hZ
  have hWL : W ≤ L := hWS.trans hSL
  have hWcS : W ≤ centerOf S := fun w hw =>
    ⟨hWS hw, Subgroup.mem_centralizer_iff.2 fun s hs => (hWc w hw s hs).symm⟩
  set π : ↥L →* ↥L ⧸ Subgroup.center ↥L := piBar L with hπ
  have hSbar : IsSylowTwoOf ((S.subgroupOf L).map π) ⊤ := isSylowTwoOf_map_piBar hS hZS
  have hcardbar := hbar _ hSbar
  set Sb : Subgroup (↥L ⧸ Subgroup.center ↥L) := (S.subgroupOf L).map π with hSb
  set Cb : Subgroup (↥L ⧸ Subgroup.center ↥L) := ((centerOf S).subgroupOf L).map π with hCb
  set Wb : Subgroup (↥L ⧸ Subgroup.center ↥L) := (W.subgroupOf L).map π with hWb
  have hWC : Wb ≤ Cb := Subgroup.map_mono fun x hx => hWcS hx
  have hinj : ∀ x ∈ W.subgroupOf L, ∀ y ∈ W.subgroupOf L, π x = π y → x = y := by
    intro x hx y hy hxy
    have h1 : x⁻¹ * y ∈ Subgroup.center ↥L := by
      rw [← ker_piBar, MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
    have h2 : ((x⁻¹ * y : ↥L) : G) ∈ centerOf L := mem_centerOf_iff_center.2 ⟨_, h1, rfl⟩
    have h3 : ((x⁻¹ * y : ↥L) : G) ∈ W := by
      have hx' : (x : G) ∈ W := hx
      have hy' : (y : G) ∈ W := hy
      simpa using W.mul_mem (W.inv_mem hx') hy'
    exact inv_mul_eq_one.1 (Subtype.ext (hWZ _ h3 h2))
  have hWbcard : Nat.card Wb = 2 ^ n := by
    rw [hWb, card_map_of_injOn π (W.subgroupOf L) hinj, ← hWcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWL).toEquiv
  have hCcard : Nat.card Cb ≤ 2 ^ n := by
    refine le_trans ?_ hcardbar
    have hle : Cb ≤ (Subgroup.center ↥Sb).map Sb.subtype := by
      rintro _ ⟨u, hu, rfl⟩
      have hu' : (u : G) ∈ centerOf S := hu
      have huS : u ∈ S.subgroupOf L := hu'.1
      have hmem : π u ∈ Sb := ⟨u, huS, rfl⟩
      refine ⟨⟨π u, hmem⟩, Subgroup.mem_center_iff.2 fun g => ?_, rfl⟩
      obtain ⟨y, hy⟩ := g
      obtain ⟨s, hs, rfl⟩ := hy
      have hsu : (s : G) * (u : G) = (u : G) * (s : G) :=
        Subgroup.mem_centralizer_iff.1 hu'.2 (s : G) hs
      refine Subtype.ext ?_
      show π s * π u = π u * π s
      rw [← map_mul, ← map_mul]
      exact congrArg π (Subtype.ext hsu)
    have := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective (Subgroup.subtype_injective _)] at this
  have hCW : Wb = Cb := Subgroup.eq_of_le_of_card_ge hWC (by rw [hWbcard]; exact hCcard)
  apply le_antisymm
  · intro z hz
    have hzL : z ∈ L := hSL hz.1
    have hzC : π ⟨z, hzL⟩ ∈ Cb := ⟨⟨z, hzL⟩, hz, rfl⟩
    rw [← hCW] at hzC
    obtain ⟨w, hw, hwz⟩ := hzC
    have h1 : (⟨z, hzL⟩ : ↥L) * w⁻¹ ∈ Subgroup.center ↥L := by
      rw [← ker_piBar, MonoidHom.mem_ker, map_mul, map_inv, ← hwz, mul_inv_cancel]
    have h2 : z * (w : G)⁻¹ ∈ centerOf L := mem_centerOf_iff_center.2 ⟨_, h1, rfl⟩
    have h3 : z = (z * (w : G)⁻¹) * (w : G) := by group
    rw [h3]
    exact Subgroup.mul_mem_sup h2 hw
  · refine sup_le (fun x hx => ?_) hWcS
    obtain ⟨c, hc, rfl⟩ := mem_centerOf_iff_center.1 hx
    refine ⟨hZS c hc, Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hc ⟨s, hSL hs⟩)

end Sup

end CFSG.Quasithin.RonanE611
