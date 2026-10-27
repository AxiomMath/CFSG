module

public import CFSG.Quasithin.H13.L32A76S2f
public import CFSG.Quasithin.H13.L32A76S2Aut
public import CFSG.Quasithin.Vol2.Ch1Chief
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.Setting

public section

namespace CFSG.Quasithin.H13.L32A.S2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.A4

theorem aut_eq_one_of_quasisimple {X : Type*} [Group X] (hX : CFSG.IsQuasisimple X)
    {N : Subgroup X} (hN : N.Normal) (hne : N ≠ ⊤) (α : MulAut X)
    (hα : ∀ x : X, α x * x⁻¹ ∈ N) : α = 1 := by
  have hZ : N ≤ Subgroup.center X := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hX hN with h | h
    · exact absurd h hne
    · exact h
  have hc : ∀ x : X, α x * x⁻¹ ∈ Subgroup.center X := fun x => hZ (hα x)
  let δ : X →* ↥(Subgroup.center X) :=
    { toFun := fun x => ⟨α x * x⁻¹, hc x⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        show α (x * y) * (x * y)⁻¹ = (α x * x⁻¹) * (α y * y⁻¹)
        have h1 := Subgroup.mem_center_iff.mp (hc y) (x⁻¹)
        calc α (x * y) * (x * y)⁻¹ = α x * ((α y * y⁻¹) * x⁻¹) := by rw [map_mul]; group
          _ = α x * (x⁻¹ * (α y * y⁻¹)) := by rw [h1]
          _ = (α x * x⁻¹) * (α y * y⁻¹) := by group) }
  have hker : commutator X ≤ δ.ker := Abelianization.commutator_subset_ker δ
  have hperf : commutator X = ⊤ := Group.isPerfect_def.mp hX.1
  refine MulEquiv.ext fun x => ?_
  have hx : x ∈ δ.ker := hker (hperf ▸ Subgroup.mem_top x)
  have h1 : α x * x⁻¹ = 1 := congrArg Subtype.val hx
  rw [MulAut.one_apply]
  exact mul_inv_eq_one.mp h1

theorem false_of_case4 {X : Type} [Group X] [Finite X] (h4 : A36Case4 X) (N : Subgroup X)
    [N.Normal] (hs : IsSimpleGroup (X ⧸ N)) (h168 : Nat.card (X ⧸ N) = 168) : False := by
  have := hs
  obtain ⟨-, hnil, ⟨e⟩, -⟩ := h4
  have hFN : CFSG.fittingSubgroup X ≤ N := le_of_nilpotent_of_card hnil h168
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hdvd : N.index ∣ (CFSG.fittingSubgroup X).index := Subgroup.index_dvd_of_le hFN
  rw [Subgroup.index_eq_card, Subgroup.index_eq_card, h168, Nat.card_congr e.toEquiv,
    card_SL_two_zmod] at hdvd
  norm_num at hdvd

variable {G : Type} [Group G] [Finite G]

theorem comm_mem_pCoreOf_LA (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h36 : A36ForSQTK) {A LA : Subgroup G}
    (hA : IsElemAbelian 2 A) (h8 : Nat.card A = 8)
    (hLA : LA ∈ cComp (Subgroup.normalizer (A : Set G))) (htop : autOn LA A = ⊤) :
    ∀ x ∈ Subgroup.normalizer (LA : Set G), x ∈ Subgroup.centralizer (A : Set G) →
      x ^ 5 = 1 → ∀ l ∈ LA, l * x * l⁻¹ * x⁻¹ ∈ pCoreOf 2 LA := by
  classical
  intro x hxL hxC hx5 l hl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (A : Set G) with hNdef
  have hA2 : IsPGroup 2 A := fun x => ⟨1, Subtype.ext (by simpa using hA.2 x x.2)⟩
  have hAO : A ≤ pCoreOf 2 N := le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hA2
  have hA1 : A ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at h8
    norm_num at h8
  have hO : pCoreOf 2 N ≠ ⊥ := fun h => hA1 (le_bot_iff.mp (h ▸ hAO))
  have hLN : LA ≤ N := le_of_mem_cComp hLA
  have hGL : autOn N A = ⊤ := by
    rw [eq_top_iff, ← htop]
    rintro _ ⟨y, -, rfl⟩
    exact Subgroup.mem_map.mpr ⟨y, Subgroup.mem_subgroupOf.mpr y.2, rfl⟩
  have hxN : x ∈ N := by
    refine Subgroup.mem_normalizer_fintype fun a ha => ?_
    have h1 : a * x = x * a := Subgroup.mem_centralizer_iff.mp hxC a ha
    rw [← h1, mul_inv_cancel_right]
    exact ha
  have hlN : l ∈ N := hLN hl
  have hQeq : CFSG.pCore 2 ↥N = CFSG.Open.pCore 2 ↥N := A3.pCore_eq_openCore 2 ↥N
  have hQn : (CFSG.pCore 2 ↥N).Normal := CFSG.pCore_normal
  have hO2 := autOn_pCoreOf_eq_bot hA h8 hGL
  have hQker : CFSG.pCore 2 ↥N ≤ (conjAct A).ker := by
    intro q hq
    have hq' : (q : G) ∈ pCoreOf 2 N := ⟨q, hq, rfl⟩
    have h1 : conjAct A q ∈ autOn (pCoreOf 2 N) A :=
      Subgroup.mem_map.mpr ⟨q, Subgroup.mem_subgroupOf.mpr hq', rfl⟩
    rw [hO2, Subgroup.mem_bot] at h1
    exact h1
  let fb : (↥N ⧸ CFSG.pCore 2 ↥N) →* MulAut ↥A := QuotientGroup.lift _ (conjAct A) hQker
  set Lb := modO2Image N LA with hLbdef
  let φ : ↥Lb →* MulAut ↥A := fb.comp Lb.subtype
  have hφs : Function.Surjective φ := by
    rw [← MonoidHom.range_eq_top, MonoidHom.range_comp, Subgroup.range_subtype]
    show ((LA.subgroupOf N).map (QuotientGroup.mk' (CFSG.pCore 2 ↥N))).map fb = ⊤
    rw [Subgroup.map_map]
    have e1 : fb.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥N)) = conjAct A :=
      MonoidHom.ext fun _ => rfl
    rw [e1]
    exact htop
  have hsimpA := E8.isSimpleGroup_mulAut hA h8
  let e := QuotientGroup.quotientKerEquivOfSurjective φ hφs
  have hsimpQ : IsSimpleGroup (↥Lb ⧸ φ.ker) := e.isSimpleGroup
  have hcardQ : Nat.card (↥Lb ⧸ φ.ker) = 168 := by
    rw [Nat.card_congr e.toEquiv, E8.card_mulAut hA h8]
  have hne : φ.ker ≠ ⊤ := by
    intro h
    have h1 : φ.ker.index = 1 := Subgroup.index_eq_one.mpr h
    rw [Subgroup.index_eq_card, hcardQ] at h1
    norm_num at h1
  set xb : ↥N ⧸ CFSG.pCore 2 ↥N := QuotientGroup.mk' _ ⟨x, hxN⟩ with hxbdef
  have hxbn : xb ∈ Subgroup.normalizer (Lb : Set (↥N ⧸ CFSG.pCore 2 ↥N)) := by
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨⟨x, hxN⟩ * z * ⟨x, hxN⟩⁻¹, ?_, by
      rw [map_mul, map_mul, map_inv]⟩
    rw [Subgroup.mem_subgroupOf]
    exact (Subgroup.mem_normalizer_iff.mp hxL (z : G)).mp (Subgroup.mem_subgroupOf.mp hz)
  let α : MulAut ↥Lb := conjAct Lb ⟨xb, hxbn⟩
  have hα5 : α ^ 5 = 1 := by
    have h1 : (⟨xb, hxbn⟩ : ↥(Subgroup.normalizer (Lb : Set (↥N ⧸ CFSG.pCore 2 ↥N)))) ^ 5 = 1 := by
      apply Subtype.ext
      show xb ^ 5 = 1
      rw [hxbdef, ← map_pow]
      have h2 : (⟨x, hxN⟩ : ↥N) ^ 5 = 1 := Subtype.ext (by simpa using hx5)
      rw [h2, map_one]
    show conjAct Lb ⟨xb, hxbn⟩ ^ 5 = 1
    rw [← map_pow, h1, map_one]
  have hfx : fb xb = 1 := CFSG.Quasithin.A4.conjAct_eq_one_iff.mpr hxC
  have hα : ∀ y : ↥Lb, α y * y⁻¹ ∈ φ.ker := by
    intro y
    rw [MonoidHom.mem_ker]
    have hy : ((α y : ↥Lb) : ↥N ⧸ CFSG.pCore 2 ↥N) = xb * y * xb⁻¹ :=
      conjAct_apply_coe' Lb ⟨xb, hxbn⟩ y
    show fb (((α y * y⁻¹ : ↥Lb)) : ↥N ⧸ CFSG.pCore 2 ↥N) = 1
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hy, map_mul, map_inv, map_mul, map_mul, map_inv, hfx]
    group
  have hα1 : α = 1 := by
    obtain ⟨hc, -, -⟩ := lemma_1_2_1_four_strong hK hs hnab h36 hO hLA
    rcases hc with ⟨hcomp, -, -⟩ | ⟨hcomp, -, -⟩ | h3 | h4
    · exact aut_eq_one_of_quasisimple hcomp.1 (MonoidHom.normal_ker φ) hne α hα
    · exact aut_eq_one_of_quasisimple hcomp.1 (MonoidHom.normal_ker φ) hne α hα
    · exact aut_eq_one_of_case3 h3 φ.ker hsimpQ hcardQ α hα5 hα
    · exact (false_of_case4 h4 φ.ker hsimpQ hcardQ).elim
  set lb : ↥N ⧸ CFSG.pCore 2 ↥N := QuotientGroup.mk' _ ⟨l, hlN⟩ with hlbdef
  have hlb : lb ∈ Lb := Subgroup.mem_map.mpr ⟨⟨l, hlN⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  have h1 : xb * lb * xb⁻¹ = lb := by
    have h2 : ((α ⟨lb, hlb⟩ : ↥Lb) : ↥N ⧸ CFSG.pCore 2 ↥N) = lb := by rw [hα1]; rfl
    exact (conjAct_apply_coe' Lb ⟨xb, hxbn⟩ ⟨lb, hlb⟩).symm.trans h2
  have h2 : QuotientGroup.mk' (CFSG.pCore 2 ↥N)
      (⟨l, hlN⟩ * ⟨x, hxN⟩ * (⟨l, hlN⟩ : ↥N)⁻¹ * (⟨x, hxN⟩ : ↥N)⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    calc lb * xb * lb⁻¹ * xb⁻¹ = (xb * lb * xb⁻¹) * xb * lb⁻¹ * xb⁻¹ := by rw [h1]
      _ = 1 := by group
  have h3 := (QuotientGroup.eq_one_iff _).mp h2
  have h4 : l * x * l⁻¹ * x⁻¹ ∈ pCoreOf 2 N := ⟨_, h3, rfl⟩
  have h5 : l * x * l⁻¹ * x⁻¹ ∈ LA := by
    have h6 : x * l⁻¹ * x⁻¹ ∈ LA := (Subgroup.mem_normalizer_iff.mp hxL _).mp (LA.inv_mem hl)
    have e2 : l * x * l⁻¹ * x⁻¹ = l * (x * l⁻¹ * x⁻¹) := by group
    rw [e2]
    exact LA.mul_mem hl h6
  have hint : LA ⊓ pCoreOf 2 N ≤ pCoreOf 2 LA :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hk, le_normalizer_pCoreOf 2 N (hLN hk)⟩)
      ((pCoreOf_isPGroup 2 N).to_le inf_le_right)
  exact hint ⟨h5, h4⟩

end CFSG.Quasithin.H13.L32A.S2

end
