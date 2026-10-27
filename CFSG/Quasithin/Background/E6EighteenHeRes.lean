module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Background.GoldschmidtTDE68Bar

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open
open scoped commutatorElement

@[expose] def FactHeInvPerfect : Prop :=
  ∀ (S : Type) [Group S], Nonempty (S ≃* Blueprint.NativeSporadic.Carrier .He) →
    ∀ x : S, orderOf x = 2 → ∃ D : Subgroup S, D ≤ Subgroup.centralizer ({x} : Set S) ∧
      ⁅D, D⁆ = D ∧ 64 ∣ Nat.card D

namespace Bar

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}

theorem exists_lift_comm_of_perfect (r : ↥(Subgroup.normalizer (L : Set Y)))
    {D : Subgroup (Qbar L)} (hD : ⁅D, D⁆ = D) (hfix : ∀ d ∈ D, barHom L r d = d) :
    ∃ E : Subgroup ↥L, ⁅E, E⁆ = E ∧ E.map (QuotientGroup.mk' (Subgroup.center ↥L)) = D ∧
      ∀ e ∈ E, (r : Y) * (e : Y) = e * r := by
  set π := QuotientGroup.mk' (Subgroup.center ↥L) with hπ
  set D₀ := D.comap π with hD₀
  have hc : ∀ a : ↥D₀, (a : ↥L)⁻¹ * conjL L r a ∈ Subgroup.center ↥L := by
    intro a
    have h2 : barAut r (QuotientGroup.mk (a : ↥L) : Qbar L) = QuotientGroup.mk (a : ↥L) :=
      hfix _ a.2
    rw [barAut_mk] at h2
    exact QuotientGroup.eq.1 h2.symm
  let f : ↥D₀ →* ↥(Subgroup.center ↥L) :=
    { toFun := fun a => ⟨(a : ↥L)⁻¹ * conjL L r a, hc a⟩
      map_one' := by ext; simp
      map_mul' := fun a b => by
        have hz := Subgroup.mem_center_iff.1 (hc a) ((b : ↥L)⁻¹)
        apply Subtype.ext
        change ((a : ↥L) * b)⁻¹ * conjL L r ((a : ↥L) * b) =
          ((a : ↥L)⁻¹ * conjL L r a) * ((b : ↥L)⁻¹ * conjL L r b)
        rw [map_mul]
        calc ((a : ↥L) * b)⁻¹ * (conjL L r a * conjL L r b)
            = (b : ↥L)⁻¹ * ((a : ↥L)⁻¹ * conjL L r a) * conjL L r b := by group
          _ = ((a : ↥L)⁻¹ * conjL L r a) * (b : ↥L)⁻¹ * conjL L r b := by rw [hz]
          _ = ((a : ↥L)⁻¹ * conjL L r a) * ((b : ↥L)⁻¹ * conjL L r b) := by group }
  have hker : commutator ↥D₀ ≤ f.ker := Abelianization.commutator_subset_ker f
  set F : Subgroup ↥L := (Subgroup.centralizer ({(r : Y)} : Set Y)).comap L.subtype with hF
  have hDF : ⁅D₀, D₀⁆ ≤ F := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have hm : ⁅(⟨a, ha⟩ : ↥D₀), (⟨b, hb⟩ : ↥D₀)⁆ ∈ f.ker :=
      hker (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
    have h1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hm)
    change (⁅a, b⁆ : ↥L)⁻¹ * conjL L r ⁅a, b⁆ = 1 at h1
    have h3 := congrArg Subtype.val (inv_mul_eq_one.1 h1).symm
    rw [conjL_apply] at h3
    rw [Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.mem_centralizer_singleton_iff]
    exact (mul_inv_eq_iff_eq_mul.1 h3).symm
  refine ⟨perfectCore D₀, perfectCore_perfect D₀, ?_, fun e he => ?_⟩
  · rw [map_perfectCore, Subgroup.map_comap_eq_self_of_surjective
      (QuotientGroup.mk'_surjective _)]
    exact perfectCore_eq_self_of_perfect hD
  · have he' : e ∈ F := hDF ((perfectCore_le_derivedSeriesOf D₀ 1) he)
    rw [hF, Subgroup.mem_comap, Subgroup.coe_subtype,
      Subgroup.mem_centralizer_singleton_iff] at he'
    exact he'.symm

end Bar

theorem le_centralizer_of_perfect_of_card_le_four' {G : Type} [Group G] [Finite G]
    {X Z : Subgroup G} (hX : ⁅X, X⁆ = X) (hXZ : X ≤ Subgroup.normalizer (Z : Set G))
    (hZ : Nat.card Z ≤ 4) : X ≤ Subgroup.centralizer (Z : Set G) := by
  classical
  set N := Subgroup.normalizer (Z : Set G) with hNdef
  let ρ : N →* Equiv.Perm Z := (MulAut.toPerm Z).comp Z.normalizerMonoidHom
  set X' : Subgroup N := X.subgroupOf N with hX'def
  have hX'map : X'.map N.subtype = X := by
    rw [hX'def, Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 hXZ
  have hX' : ⁅X', X'⁆ = X' := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_commutator, hX'map, hX]
  set H := X'.map ρ with hHdef
  have hH : ⁅H, H⁆ = H := by rw [hHdef, ← Subgroup.map_commutator, hX']
  obtain ⟨n, hn⟩ := (Equiv.Perm.isSolvable (α := Z) hZ).solvable
  have hle : ∀ k, H ≤ derivedSeries (Equiv.Perm Z) k := by
    intro k
    induction k with
    | zero => exact le_top
    | succ k ih =>
      rw [derivedSeries_succ, ← hH]
      exact Subgroup.commutator_mono ih ih
  have hbot : H = ⊥ := eq_bot_iff.2 (hn ▸ hle n)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hρ : ρ ⟨x, hXZ hx⟩ = 1 := by
    have h : ρ ⟨x, hXZ hx⟩ ∈ H := ⟨⟨x, hXZ hx⟩, hx, rfl⟩
    rw [hbot] at h
    exact h
  have h1 : ρ ⟨x, hXZ hx⟩ ⟨z, hz⟩ = ⟨z, hz⟩ := by rw [hρ]; rfl
  have h2 : x * z * x⁻¹ = z := by
    have h3 : ((Z.normalizerMonoidHom ⟨x, hXZ hx⟩ ⟨z, hz⟩ : Z) : G) = z := congrArg Subtype.val h1
    rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at h3
  calc z * x = x * z * x⁻¹ * x := by rw [h2]
    _ = x * z := by group

theorem le_centralizer_of_perfect_of_index_le_two {G : Type} [Group G] [Finite G]
    {V U X : Subgroup G} (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hUV : U ≤ V)
    (hU4 : Nat.card U ≤ 4) (hidx : U.relIndex V ≤ 2) (hX : ⁅X, X⁆ = X)
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (hXU : X ≤ Subgroup.normalizer (U : Set G)) :
    X ≤ Subgroup.centralizer (V : Set G) := by
  have hC := le_centralizer_of_perfect_of_card_le_four' hX hXU hU4
  have hcos : ∀ y ∈ X, ∀ v ∈ V, y * v * y⁻¹ * v⁻¹ ∈ U := by
    intro y hy v hv
    have hyv : y * v * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hXV hy) v).1 hv
    by_cases hvU : v ∈ U
    · exact U.mul_mem ((Subgroup.mem_normalizer_iff.1 (hXU hy) v).1 hvU) (U.inv_mem hvU)
    · have hyvU : y * v * y⁻¹ ∉ U := fun h => hvU ((Subgroup.mem_normalizer_iff.1 (hXU hy) v).2 h)
      have hne1 : (U.subgroupOf V).index ≠ 1 := fun h => hvU (by
        have h1 := Subgroup.index_eq_one.1 h
        have h2 : (⟨v, hv⟩ : ↥V) ∈ U.subgroupOf V := h1 ▸ Subgroup.mem_top _
        exact h2)
      have h0 : (U.subgroupOf V).index ≠ 0 := Subgroup.index_ne_zero_of_finite
      have hi2 : (U.subgroupOf V).index = 2 := by
        have : (U.subgroupOf V).index ≤ 2 := hidx
        omega
      have hm := (Subgroup.mul_mem_iff_of_index_two hi2 (a := (⟨y * v * y⁻¹, hyv⟩ : ↥V))
        (b := (⟨v, hv⟩ : ↥V)⁻¹)).2 ⟨fun h => absurd h hyvU,
          fun h => absurd (show v ∈ U by
            simpa [Subgroup.mem_subgroupOf] using (U.subgroupOf V).inv_mem h) hvU⟩
      exact hm
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  let φ : ↥X →* ↥U :=
    { toFun := fun y => ⟨(y : G) * v * (y : G)⁻¹ * v⁻¹, hcos y y.2 v hv⟩
      map_one' := by ext; simp
      map_mul' := fun y z => by
        apply Subtype.ext
        have hz := hcos z z.2 v hv
        have hcz := Subgroup.mem_centralizer_iff.1 (hC y.2) _ hz
        have hyU := hcos y y.2 v hv
        change (y : G) * z * v * ((y : G) * z)⁻¹ * v⁻¹ =
          ((y : G) * v * (y : G)⁻¹ * v⁻¹) * ((z : G) * v * (z : G)⁻¹ * v⁻¹)
        rw [hVab _ (hUV hyU) _ (hUV hz)]
        calc (y : G) * z * v * ((y : G) * z)⁻¹ * v⁻¹ =
            (y : G) * ((z : G) * v * (z : G)⁻¹ * v⁻¹) * (y : G)⁻¹ *
              ((y : G) * v * (y : G)⁻¹ * v⁻¹) := by group
          _ = ((z : G) * v * (z : G)⁻¹ * v⁻¹) * (y : G) * (y : G)⁻¹ *
              ((y : G) * v * (y : G)⁻¹ * v⁻¹) := by rw [← hcz]
          _ = _ := by group }
  have hle : ⁅X, X⁆ ≤ φ.ker.map X.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    refine ⟨⁅(⟨a, ha⟩ : ↥X), ⟨b, hb⟩⁆, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (hVab _ (hUV (φ ⟨a, ha⟩).2) _ (hUV (φ ⟨b, hb⟩).2))
  obtain ⟨y, hy, hyx⟩ := hle (hX.symm ▸ hx)
  have h1 := congrArg Subtype.val (MonoidHom.mem_ker.1 hy)
  change (y : G) * v * (y : G)⁻¹ * v⁻¹ = 1 at h1
  have hyx' : (y : G) = x := hyx
  rw [hyx'] at h1
  have h2 : x * v = v * x := by
    calc x * v = x * v * x⁻¹ * v⁻¹ * (v * x) := by group
      _ = v * x := by rw [h1, one_mul]
  exact h2.symm

end E6

end CFSG.Quasithin
