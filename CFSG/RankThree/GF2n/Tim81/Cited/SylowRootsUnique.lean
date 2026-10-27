module

public import CFSG.Timmesfeld.Transvection.ModelSULowSpan
import CFSG.Timmesfeld.Transvection.ModelSULowRadAction
import CFSG.Timmesfeld.Transvection.ModelSUInvolution
import CFSG.GroupTheory.OddKernelImage
import CFSG.LocalAnalysis.StandardType.SUCenterOdd
import CFSG.Quasithin.Background.AutOnCard
import CFSG.Quasithin.Background.AutOnFixV
import CFSG.Quasithin.Background.AutOnElemAb
import CFSG.Timmesfeld.LieEmbed.UnitarySeven
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CGT.Timmesfeld75.CentralQuotient
public import CFSG.Quasithin.Background.AutOnBasics
public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.GF2n.Tim81.SUTrans

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Universal.Unitary.SUExtras CFSG.Timmesfeld.ARS CFSG.Timmesfeld.LieEmbed
  CFSG.Timmesfeld.Transvection CFSG.Timmesfeld.Transvection.ModelRank CFSG.LinearAlgebra
  CFSG.Quasithin CFSG.Quasithin.AutOn CFSG.Open CFSG.CGT.Timmesfeld75
open scoped commutatorElement IsMulCommutative

variable {F : Type} [Field F] {σ : F ≃+* F} {N : ℕ} {K : Type} [Group K]

private theorem lift_le_normalizer [Finite (SU σ N)] [CharP F 2] {Φ : SU σ N →* K}
    (hker : Φ.ker ≤ Subgroup.center (SU σ N)) (hodd : Odd (Nat.card Φ.ker))
    {Ê : Subgroup (SU σ N)}
    (hE : Ê.map Φ ≤ Subgroup.normalizer ((lowRad σ N).map Φ : Set K)) :
    Ê ≤ Subgroup.normalizer (lowRad σ N : Set (SU σ N)) := by
  intro ê hê
  have hΦ : Φ ê ∈ Subgroup.normalizer ((lowRad σ N).map Φ : Set K) :=
    hE (Subgroup.mem_map.mpr ⟨ê, hê, rfl⟩)
  have hconj : CFSG.CGT.Timmesfeld75.conjSubgroup (Φ ê) ((lowRad σ N).map Φ) =
      (lowRad σ N).map Φ :=
    CFSG.CGT.Timmesfeld75.mem_normalizer_iff_conjSubgroup_eq.mp hΦ
  have hmap : (CFSG.CGT.Timmesfeld75.conjSubgroup ê (lowRad σ N)).map Φ =
      (lowRad σ N).map Φ := by
    rw [CFSG.CGT.Timmesfeld75.map_conjSubgroup, hconj]
  have hP : IsPGroup 2 (CFSG.CGT.Timmesfeld75.conjSubgroup ê (lowRad σ N)) :=
    (isPGroup_lowRad (σ := σ) (m := N)).map (MulAut.conj ê).toMonoidHom
  have h1 : CFSG.CGT.Timmesfeld75.conjSubgroup ê (lowRad σ N) ≤ lowRad σ N :=
    CFSG.GroupTheory.le_of_map_le_map_of_odd hker hodd hP (le_of_eq hmap)
  have h2 : lowRad σ N ≤ CFSG.CGT.Timmesfeld75.conjSubgroup ê (lowRad σ N) :=
    CFSG.GroupTheory.le_of_map_le_map_of_odd hker hodd
      (isPGroup_lowRad (σ := σ) (m := N)) (le_of_eq hmap.symm)
  exact CFSG.CGT.Timmesfeld75.mem_normalizer_iff_conjSubgroup_eq.mpr (le_antisymm h1 h2)

private theorem inf_centralizer_le [CharP F 2] (hσ : ∀ c, σ (σ c) = c)
    {Ê : Subgroup (SU σ N)} (hÊcomm : ∀ x ∈ Ê, ∀ y ∈ Ê, x * y = y * x)
    (hÊsq : ∀ x ∈ Ê, x * x = 1) :
    Ê ⊓ Subgroup.centralizer (lowRad σ N : Set (SU σ N)) ≤
      lowRad σ N ⊓ Subgroup.centralizer (Ê : Set (SU σ N)) := by
  rintro x ⟨hxÊ, hxQ⟩
  refine ⟨mem_lowRad_of_mem_centralizer (σ := σ) (m := N) hσ (hÊsq x hxÊ)
    (fun w hw => ?_), ?_⟩
  · exact (Subgroup.mem_centralizer_iff.mp hxQ w hw).symm
  · exact Subgroup.mem_centralizer_iff.mpr (fun y hy => hÊcomm y hy x hxÊ)

private theorem card_le_autOn_mul_fixV [Finite (SU σ N)] [CharP F 2]
    (hσ : ∀ c, σ (σ c) = c)
    {Ê : Subgroup (SU σ N)}
    (hÊN : Ê ≤ Subgroup.normalizer (lowRad σ N : Set (SU σ N)))
    (hÊcomm : ∀ x ∈ Ê, ∀ y ∈ Ê, x * y = y * x)
    (hÊsq : ∀ x ∈ Ê, x * x = 1)
    (hcard : Nat.card ↥(lowRad σ N) ≤ Nat.card ↥Ê) :
    Nat.card ↥(lowRad σ N) ≤
      Nat.card (autOn Ê (lowRad σ N)) * Nat.card (fixV (autOn Ê (lowRad σ N))) := by
  classical
  have h1 := card_autOn_mul (K := Ê) (V := lowRad σ N) hÊN
  have h2 := card_fixV_autOn_eq (A := Ê) (W := lowRad σ N) hÊN
  have hle := inf_centralizer_le (σ := σ) (N := N) hσ hÊcomm hÊsq
  calc Nat.card ↥(lowRad σ N)
      ≤ Nat.card ↥Ê := hcard
    _ = Nat.card (autOn Ê (lowRad σ N)) *
          Nat.card ↥(Ê ⊓ Subgroup.centralizer (lowRad σ N : Set (SU σ N))) := h1.symm
    _ ≤ Nat.card (autOn Ê (lowRad σ N)) *
          Nat.card ↥(lowRad σ N ⊓ Subgroup.centralizer (Ê : Set (SU σ N))) :=
        Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hle)
    _ = Nat.card (autOn Ê (lowRad σ N)) *
          Nat.card (fixV (autOn Ê (lowRad σ N))) := by rw [h2]

private theorem exists_minimal_offender {V : Type*} [CommGroup V] [Finite V]
    {X : Subgroup (MulAut V)} (hX : IsA2 X X)
    (h : Nat.card V ≤ Nat.card X * Nat.card (fixV X)) :
    ∃ A : Subgroup (MulAut V), A ≤ X ∧ IsFFStarOffender X A ∧
      ∀ B : Subgroup (MulAut V), IsFFStarOffender X B → B ≤ A → B = A := by
  classical
  obtain ⟨B₀, hB₀X, hB₀off, -⟩ :=
    CFSG.Quasithin.B1.exists_offender_below hX 0 (by simpa using h)
  let S : Set (Subgroup (MulAut V)) := {B | B ≤ B₀ ∧ IsFFStarOffender X B}
  have hSne : S.Nonempty := ⟨B₀, le_rfl, hB₀off⟩
  obtain ⟨A, hA, hmin⟩ :=
    Set.exists_min_image S (fun B => Nat.card B) (Set.toFinite S) hSne
  exact ⟨A, hA.1.trans hB₀X, hA.2, fun B hBoff hBA => by
    have hBS : B ∈ S := ⟨hBA.trans hA.1, hBoff⟩
    exact Subgroup.eq_of_le_of_card_ge hBA (hmin B hBS)⟩

private theorem exists_lift [Finite (SU σ N)] [CharP F 2] {Φ : SU σ N →* K}
    (hker : Φ.ker ≤ Subgroup.center (SU σ N)) (hodd : Odd (Nat.card Φ.ker))
    {E : Subgroup K}
    (hE : E ≤ Φ.range ⊓ Subgroup.normalizer ((lowRad σ N).map Φ : Set K))
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : ∀ x ∈ E, x * x = 1)
    (hcard : Nat.card ↥((lowRad σ N).map Φ) ≤ Nat.card ↥E) :
    ∃ Ê : Subgroup (SU σ N), Ê.map Φ = E ∧ IsElemAbelian 2 Ê ∧
      Ê ≤ Subgroup.normalizer (lowRad σ N : Set (SU σ N)) ∧
      Nat.card ↥(lowRad σ N) ≤ Nat.card ↥Ê := by
  classical
  have hQ2 : IsPGroup 2 (lowRad σ N) := isPGroup_lowRad (σ := σ) (m := N)
  have hEpg : IsPGroup 2 E := by
    intro x
    refine ⟨1, ?_⟩
    rw [pow_one, pow_two]
    exact Subtype.ext (hE2 x x.2)
  obtain ⟨Ê, hÊ2, hÊmap, hÊinj⟩ :=
    CFSG.GroupTheory.exists_isPGroup_map_eq_of_odd (Φ := Φ) hodd (hE.trans inf_le_left) hEpg
  have hÊcard : Nat.card ↥Ê = Nat.card ↥E := by
    rw [← hÊmap]
    exact (CFSG.GroupTheory.natCard_map_of_isPGroup_of_odd (Φ := Φ) hodd hÊ2).symm
  have hQbar : Nat.card ↥((lowRad σ N).map Φ) = Nat.card ↥(lowRad σ N) :=
    CFSG.GroupTheory.natCard_map_of_isPGroup_of_odd (Φ := Φ) hodd hQ2
  have hcardÊ : Nat.card ↥(lowRad σ N) ≤ Nat.card ↥Ê := by
    rw [hÊcard, ← hQbar]
    exact hcard
  have hmemE : ∀ x ∈ Ê, Φ x ∈ E := by
    intro x hx
    rw [← hÊmap]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hÊcomm : ∀ x ∈ Ê, ∀ y ∈ Ê, x * y = y * x := by
    intro x hx y hy
    have h : (⟨x * y, Ê.mul_mem hx hy⟩ : ↥Ê) = ⟨y * x, Ê.mul_mem hy hx⟩ := by
      apply hÊinj
      show Φ (x * y) = Φ (y * x)
      rw [map_mul, map_mul]
      exact hEc (Φ x) (hmemE x hx) (Φ y) (hmemE y hy)
    exact congrArg Subtype.val h
  have hÊsq : ∀ x ∈ Ê, x * x = 1 := by
    intro x hx
    have h : (⟨x * x, Ê.mul_mem hx hx⟩ : ↥Ê) = ⟨1, Ê.one_mem⟩ := by
      apply hÊinj
      show Φ (x * x) = Φ 1
      rw [map_mul, map_one]
      exact hE2 (Φ x) (hmemE x hx)
    exact congrArg Subtype.val h
  have hEN : Ê.map Φ ≤ Subgroup.normalizer ((lowRad σ N).map Φ : Set K) := by
    intro y hy
    rw [hÊmap] at hy
    exact (hE hy).2
  have hÊN : Ê ≤ Subgroup.normalizer (lowRad σ N : Set (SU σ N)) :=
    lift_le_normalizer (σ := σ) (N := N) hker hodd hEN
  refine ⟨Ê, hÊmap, ?_, hÊN, hcardÊ⟩
  exact ⟨IsMulCommutative.of_comm (fun x y => Subtype.ext (hÊcomm x.1 x.2 y.1 y.2)),
    fun x hx => by rw [pow_two]; exact hÊsq x hx⟩

private theorem card_fixV_le [Finite F] [Finite (SU σ N)] [CharP F 2]
    (hσ : ∀ c, σ (σ c) = c) (hm : 3 ≤ N / 2) {Ê : Subgroup (SU σ N)}
    (hÊsq : ∀ x ∈ Ê, x * x = 1)
    {A : Subgroup (MulAut ↥(lowRad σ N))}
    {a₀ : MulAut ↥(lowRad σ N)} (ha₀A : a₀ ∈ A)
    {ĝ₀ : SU σ N} (hĝ₀Ê : ĝ₀ ∈ Ê)
    (hĝ₀N : ĝ₀ ∈ Subgroup.normalizer (lowRad σ N : Set (SU σ N)))
    (hĝ₀a : conjAct (lowRad σ N) ⟨ĝ₀, hĝ₀N⟩ = a₀)
    (hne : ∃ w ∈ lowRad σ N, ĝ₀ * w * ĝ₀⁻¹ ≠ w) :
    Nat.card (fixV A) * Nat.card F ≤ Nat.card ↥(lowRad σ N) := by
  classical
  have hmap_le : (fixV A).map (lowRad σ N).subtype ≤
      lowRad σ N ⊓ Subgroup.centralizer ({ĝ₀} : Set (SU σ N)) := by
    rintro y ⟨q, hq, rfl⟩
    refine ⟨q.2, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      have hval : ((conjAct (lowRad σ N) ⟨ĝ₀, hĝ₀N⟩) q : SU σ N) = (q : SU σ N) := by
        rw [hĝ₀a]
        exact congrArg Subtype.val (show a₀ q = q from hq a₀ ha₀A)
      rw [coe_conjAct_apply] at hval
      simp only [Subgroup.coe_mk] at hval
      calc ĝ₀ * (q : SU σ N)
          = (ĝ₀ * (q : SU σ N) * ĝ₀⁻¹) * ĝ₀ := by group
        _ = (q : SU σ N) * ĝ₀ := by rw [hval])
  have hfix_le : Nat.card (fixV A) ≤
      Nat.card ↥(lowRad σ N ⊓ Subgroup.centralizer ({ĝ₀} : Set (SU σ N))) := by
    rw [← Subgroup.card_subtype (lowRad σ N) (fixV A)]
    exact Subgroup.card_le_of_le hmap_le
  have hcentral := card_inf_centralizer_mul_card_le (σ := σ) (m := N) hσ hm hĝ₀N
    (hÊsq ĝ₀ hĝ₀Ê) hne
  calc Nat.card (fixV A) * Nat.card F
      ≤ Nat.card ↥(lowRad σ N ⊓ Subgroup.centralizer ({ĝ₀} : Set (SU σ N))) *
          Nat.card F := Nat.mul_le_mul_right _ hfix_le
    _ ≤ Nat.card ↥(lowRad σ N) := hcentral

private theorem card_offender_le [Finite F] [CharP F 2] {f : ℕ}
    (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) (htrace : Nat.card ↥(traceZero σ) = 2 ^ f)
    {Ê : Subgroup (SU σ N)}
    (hÊN : Ê ≤ Subgroup.normalizer (lowRad σ N : Set (SU σ N)))
    (hÊcomm : ∀ x ∈ Ê, ∀ y ∈ Ê, x * y = y * x)
    (hÊsq : ∀ x ∈ Ê, x * x = 1)
    {A : Subgroup (MulAut ↥(lowRad σ N))}
    (hA : A ≤ autOn Ê (lowRad σ N)) (hAq : IsQuadratic A)
    {a₀ : MulAut ↥(lowRad σ N)} (ha₀A : a₀ ∈ A)
    {ĝ₀ : SU σ N} (hĝ₀Ê : ĝ₀ ∈ Ê)
    (hĝ₀N : ĝ₀ ∈ Subgroup.normalizer (lowRad σ N : Set (SU σ N)))
    (hĝ₀a : conjAct (lowRad σ N) ⟨ĝ₀, hĝ₀N⟩ = a₀)
    (hne : ∃ w ∈ lowRad σ N, ĝ₀ * w * ĝ₀⁻¹ ≠ w) :
    Nat.card A ≤ 2 ^ f := by
  classical
  have hlift : ∀ a : ↥A, ∃ (x : SU σ N)
      (hx : x ∈ Subgroup.normalizer (lowRad σ N : Set (SU σ N))),
      x ∈ Ê ∧ conjAct (lowRad σ N) ⟨x, hx⟩ = (a : MulAut ↥(lowRad σ N)) :=
    fun a => mem_autOn_iff_exists.mp (hA a.2)
  choose x hxN hxÊ hxA using hlift
  have hex : ∀ a : ↥A, ∃ c : F, c + σ c = 0 ∧
      lowPart σ N (x a) - 1 = c • (lowPart σ N ĝ₀ - 1) := by
    intro a
    have hqq : ∀ w ∈ lowRad σ N,
        x a * (ĝ₀ * w * ĝ₀⁻¹ * w⁻¹) * (x a)⁻¹ = ĝ₀ * w * ĝ₀⁻¹ * w⁻¹ := by
      intro w hw
      have hw' : ĝ₀ * w * ĝ₀⁻¹ ∈ lowRad σ N :=
        (Subgroup.mem_normalizer_iff.mp hĝ₀N w).1 hw
      have hzwQ : ĝ₀ * w * ĝ₀⁻¹ * w⁻¹ ∈ lowRad σ N :=
        (lowRad σ N).mul_mem hw' ((lowRad σ N).inv_mem hw)
      let w₀ : ↥(lowRad σ N) := ⟨w, hw⟩
      let zw : ↥(lowRad σ N) := ⟨ĝ₀ * w * ĝ₀⁻¹ * w⁻¹, hzwQ⟩
      have hzw : a₀ w₀ * w₀⁻¹ = zw := by
        apply Subtype.ext
        have h1 : ((a₀ w₀ : ↥(lowRad σ N)) : SU σ N) = ĝ₀ * w * ĝ₀⁻¹ := by
          rw [← hĝ₀a]
          simpa using coe_conjAct_apply (lowRad σ N) ⟨ĝ₀, hĝ₀N⟩ w₀
        rw [Subgroup.coe_mul, Subgroup.coe_inv, h1]
      have hmem : zw ∈ commV A := by
        rw [← hzw]
        exact Subgroup.subset_closure ⟨a₀, ha₀A, w₀, rfl⟩
      have hfix : zw ∈ fixV A := hAq hmem
      have hact : (a : MulAut ↥(lowRad σ N)) zw = zw := hfix (a : MulAut ↥(lowRad σ N)) a.2
      rw [← hxA a] at hact
      have hcoe := congrArg (Subtype.val : ↥(lowRad σ N) → SU σ N) hact
      rw [coe_conjAct_apply] at hcoe
      simpa [zw] using hcoe
    exact exists_lowPart_sub_one_eq_smul (σ := σ) (m := N) hσ htr hĝ₀N (hÊN (hxÊ a))
      (hÊsq ĝ₀ hĝ₀Ê) (hÊsq (x a) (hxÊ a))
      (hÊcomm (x a) (hxÊ a) ĝ₀ hĝ₀Ê) hne hqq
  choose c hc hceq using hex
  let φ : ↥A → ↥(traceZero σ) := fun a => ⟨c a, hc a⟩
  have hφinj : Function.Injective φ := by
    intro a a' heq
    have hcc : c a = c a' := congrArg Subtype.val heq
    have hlp : lowPart σ N (x a) = lowPart σ N (x a') := by
      have h1 : lowPart σ N (x a) - 1 = lowPart σ N (x a') - 1 := by
        rw [hceq a, hceq a', hcc]
      exact sub_left_inj.mp h1
    have hact : ∀ w ∈ lowRad σ N, x a * w * (x a)⁻¹ = x a' * w * (x a')⁻¹ :=
      fun w hw => conj_eq_conj_of_lowPart_eq (hÊN (hxÊ a)) (hÊN (hxÊ a')) hlp hw
    apply Subtype.ext
    rw [← hxA a, ← hxA a']
    refine MulEquiv.ext fun w => ?_
    apply Subtype.ext
    rw [coe_conjAct_apply, coe_conjAct_apply]
    simp only [Subgroup.coe_mk]
    exact hact (w : SU σ N) w.2
  have := Nat.card_le_card_of_injective φ hφinj
  rwa [htrace] at this

private theorem lt_irrefl_of_card {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f)
    {n : ℕ} (hn : 0 < n) (h : n * Nat.card F ≤ 2 ^ f * n) : False := by
  have h2 : n * ((2 ^ f) * (2 ^ f)) ≤ n * (2 ^ f) := by
    calc n * ((2 ^ f) * (2 ^ f)) = n * Nat.card F := by rw [hF, pow_two]
      _ ≤ 2 ^ f * n := h
      _ = n * (2 ^ f) := Nat.mul_comm _ _
  have h3 : (2 ^ f) * (2 ^ f) ≤ (2 ^ f) := Nat.le_of_mul_le_mul_left h2 hn
  have h4 : (2 ^ f) ≤ 1 := by
    have h3' : (2 ^ f) * (2 ^ f) ≤ (2 ^ f) * 1 := by simpa using h3
    exact Nat.le_of_mul_le_mul_left h3' (Nat.two_pow_pos f)
  have hf0 : f ≠ 0 := by
    have := hf
    omega
  have h5 : 1 < 2 ^ f := one_lt_pow' (by norm_num) hf0
  omega

private theorem eq_of_le_centralizer [CharP F 2] {Φ : SU σ N →* K} {E : Subgroup K}
    {Ê : Subgroup (SU σ N)} (hÊmap : Ê.map Φ = E) (hσ : ∀ c, σ (σ c) = c)
    (hÊsq : ∀ x ∈ Ê, x * x = 1)
    (hcent : Ê ≤ Subgroup.centralizer (lowRad σ N : Set (SU σ N)))
    (hcard : Nat.card ↥((lowRad σ N).map Φ) ≤ Nat.card ↥E)
    [Finite ↥((lowRad σ N).map Φ)] :
    E = (lowRad σ N).map Φ := by
  have hÊQ : Ê ≤ lowRad σ N := by
    intro x hx
    exact mem_lowRad_of_mem_centralizer (σ := σ) (m := N) hσ (hÊsq x hx)
      (fun w hw => (Subgroup.mem_centralizer_iff.mp (hcent hx) w hw).symm)
  have hle : E ≤ (lowRad σ N).map Φ := by
    rw [← hÊmap]
    exact Subgroup.map_mono hÊQ
  exact Subgroup.eq_of_le_of_card_ge hle hcard

private theorem false_of_not_le_centralizer [Finite F] [Finite (SU σ N)] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hσ : ∀ c, σ (σ c) = c)
    (htr : ∀ a, σ a = a → ∃ c, c + σ c = a) (htrace : Nat.card ↥(traceZero σ) = 2 ^ f)
    (hm : 3 ≤ N / 2)
    {Ê : Subgroup (SU σ N)} (hÊel : IsElemAbelian 2 Ê)
    (hÊN : Ê ≤ Subgroup.normalizer (lowRad σ N : Set (SU σ N)))
    (hcardÊ : Nat.card ↥(lowRad σ N) ≤ Nat.card ↥Ê)
    (hcent : ¬ Ê ≤ Subgroup.centralizer (lowRad σ N : Set (SU σ N))) :
    False := by
  classical
  have hÊcomm : ∀ x ∈ Ê, ∀ y ∈ Ê, x * y = y * x :=
    fun x hx y hy => congrArg Subtype.val (hÊel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hÊsq : ∀ x ∈ Ê, x * x = 1 := by
    intro x hx
    have h := hÊel.2 x hx
    rwa [pow_two] at h
  have hXab : IsElemAbelian2 (autOn Ê (lowRad σ N)) := isElemAbelian2_autOn hÊel
  have hXne : autOn Ê (lowRad σ N) ≠ ⊥ :=
    CFSG.Quasithin.AutOn.autOn_ne_bot_of_not_le_centralizer hÊN hcent
  have hcardX := card_le_autOn_mul_fixV (σ := σ) (N := N) hσ hÊN hÊcomm hÊsq hcardÊ
  obtain ⟨A₁, hA₁X, hA₁off, hA₁min⟩ :=
    exists_minimal_offender (V := ↥(lowRad σ N))
      (X := autOn Ê (lowRad σ N)) ⟨le_rfl, hXne, hXab⟩ hcardX
  have hA₁q : IsQuadratic A₁ :=
    CFSG.Quasithin.B1_4_3_of_minimal (V := ↥(lowRad σ N))
      (X := autOn Ê (lowRad σ N)) (A := A₁)
      (fun v => by rw [pow_two]; exact Subtype.ext (mul_self_eq_one_of_mem_lowRad v.2))
      hA₁off hA₁min
  have hA₁ne : A₁ ≠ ⊥ := hA₁off.2.1
  have hA₁card : Nat.card ↥(lowRad σ N) ≤ Nat.card A₁ * Nat.card (fixV A₁) := by
    have h := hA₁off.card_le (B := ⊥) bot_le
    rwa [CFSG.Quasithin.B1.card_bot_mul_card_fixV] at h
  obtain ⟨a₀, ha₀ne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA₁ne
  have ha₀A : (a₀ : MulAut ↥(lowRad σ N)) ∈ A₁ := a₀.2
  have ha₀ne' : (a₀ : MulAut ↥(lowRad σ N)) ≠ 1 := fun h => ha₀ne (Subtype.ext h)
  obtain ⟨ĝ₀, hĝ₀N, hĝ₀Ê, hĝ₀a⟩ := mem_autOn_iff_exists.mp (hA₁X ha₀A)
  have hne : ∃ w ∈ lowRad σ N, ĝ₀ * w * ĝ₀⁻¹ ≠ w := by
    by_contra h
    push Not at h
    apply ha₀ne'
    have hone : conjAct (lowRad σ N) ⟨ĝ₀, hĝ₀N⟩ = 1 := by
      refine MulEquiv.ext fun w => ?_
      apply Subtype.ext
      rw [coe_conjAct_apply]
      simpa [Subgroup.coe_mk] using h w.1 w.2
    rw [← hĝ₀a]
    exact hone
  have hfixle := card_fixV_le (σ := σ) (N := N) hσ hm hÊsq ha₀A hĝ₀Ê hĝ₀N hĝ₀a hne
  have hAle := card_offender_le (σ := σ) (N := N) hσ htr htrace
    hÊN hÊcomm hÊsq hA₁X hA₁q ha₀A hĝ₀Ê hĝ₀N hĝ₀a hne
  have hmain : Nat.card ↥(lowRad σ N) * Nat.card F ≤ 2 ^ f * Nat.card ↥(lowRad σ N) := by
    calc Nat.card ↥(lowRad σ N) * Nat.card F
        ≤ (Nat.card A₁ * Nat.card (fixV A₁)) * Nat.card F :=
            Nat.mul_le_mul_right _ hA₁card
      _ = Nat.card A₁ * (Nat.card (fixV A₁) * Nat.card F) := by ring
      _ ≤ Nat.card A₁ * Nat.card ↥(lowRad σ N) := Nat.mul_le_mul_left _ hfixle
      _ ≤ 2 ^ f * Nat.card ↥(lowRad σ N) := Nat.mul_le_mul_right _ hAle
  haveI : Nonempty ↥(lowRad σ N) := ⟨⟨1, (lowRad σ N).one_mem⟩⟩
  exact lt_irrefl_of_card (F := F) hF hf Nat.card_pos hmain

theorem eq_map_lowRad_of_le_normalizer [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 1 ≤ f) (hN : 6 ≤ N)
    {Φ : SU (unitaryInvolution F 2 f) N →* K}
    (hker : Φ.ker ≤ Subgroup.center (SU (unitaryInvolution F 2 f) N)) {E : Subgroup K}
    (hE : E ≤ Φ.range ⊓ Subgroup.normalizer
      (((lowRad (unitaryInvolution F 2 f) N).map Φ : Subgroup K) : Set K))
    (hEc : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hE2 : ∀ x ∈ E, x * x = 1)
    (hcard : Nat.card ↥((lowRad (unitaryInvolution F 2 f) N).map Φ) ≤ Nat.card ↥E) :
    E = (lowRad (unitaryInvolution F 2 f) N).map Φ := by
  classical
  let σ := unitaryInvolution F 2 f
  have hσ : ∀ c, σ (σ c) = c := unitaryInvolution_involutive hF
  have htr : ∀ a, σ a = a → ∃ c, c + σ c = a := fun _ ha => exists_add_unitaryInvolution_eq hF ha
  haveI : Finite (SU σ N) :=
    Finite.of_injective (mat σ N) (mat_injective (σ := σ) (n := N))
  have hodd : Odd (Nat.card Φ.ker) :=
    CFSG.StandardType.odd_natCard_of_le_center_SU σ hker
  obtain ⟨Ê, hÊmap, hÊel, hÊN, hcardÊ⟩ :=
    exists_lift (σ := σ) (N := N) (Φ := Φ) hker hodd hE hEc hE2 hcard
  haveI : Finite ↥((lowRad σ N).map Φ) :=
    Finite.of_surjective
      (fun q : ↥(lowRad σ N) =>
        (⟨Φ q, Subgroup.mem_map.mpr ⟨q, q.2, rfl⟩⟩ : ↥((lowRad σ N).map Φ)))
      (by
        rintro ⟨y, hy⟩
        obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.mp hy
        exact ⟨⟨q, hq⟩, rfl⟩)
  have hm : 3 ≤ N / 2 := by
    have := hN
    omega
  by_cases hcent : Ê ≤ Subgroup.centralizer (lowRad σ N : Set (SU σ N))
  · refine eq_of_le_centralizer (σ := σ) (N := N) hÊmap hσ (fun x hx => ?_) hcent hcard
    have h := hÊel.2 x hx
    rwa [pow_two] at h
  · exact (false_of_not_le_centralizer (σ := σ) (N := N) (f := f) hF hf hσ htr
      (card_traceZero hF) hm hÊel hÊN hcardÊ hcent).elim

end CFSG.RankThree.GF2n.Tim81.SUTrans
