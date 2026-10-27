module

public import CFSG.Quasithin.MS93.S36Ext3

public section

namespace CFSG.Quasithin.MS93.S36

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Vol2
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

variable {G : Type} [Group G]

theorem frattiniIn_eq_bot_of_elem [Finite G] {V : Subgroup G}
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hV2 : ∀ x ∈ V, x ^ 2 = 1) : frattiniIn V = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 ↥V := fun v => ⟨1, Subtype.ext (by simpa using hV2 v v.2)⟩
  have : Fact (IsPGroup 2 ↥V) := ⟨hP⟩
  have hE : CFSG.IsElementaryAbelian 2 ↥V :=
    { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (hVc x x.2 y y.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun v =>
        Subtype.ext (by simpa using hV2 v v.2) }
  have := (CFSG.frattini_eq_bot_iff_isElementaryAbelian (R := ↥V) (p := 2)).mpr hE
  rw [frattiniIn, this, Subgroup.map_bot]

section Natural

variable [Finite G] {M T L : Subgroup G} (h : PUHyp M T L) {F : Type} [Field F] [Fintype F]
  {a : ↥L →* ↥(StatedSL 3 F)}

include h in
theorem natural_of_elem (ha : Function.Surjective a)
    (hU : IsSumOfNaturalModulesVia L (Uq M T L) ⊥ a false 1) (hVU : Vq M L ≠ Uq M T L)
    (hXL : ⁅Xq M, L⁆ ≤ Uq M T L) (hVc : ∀ x ∈ Vq M L, ∀ y ∈ Vq M L, x * y = y * x)
    (hV2 : ∀ x ∈ Vq M L, x ^ 2 = 1)
    (hVcard : Nat.card ↥(Vq M L) ≤ Fintype.card F ^ 3 * Nat.card ↥(Uq M T L))
    (hVQ : ⁅Vq M L, pCoreOf 2 M⁆ ≤ Uq M T L) :
    IsSumOfNaturalModulesVia L (Vq M L) (Uq M T L) a false 1 := by
  set N := NatSec.ofIsSum hU
  have hUV := Uq_le_Vq h
  have hVQ' : Vq M L ≤ pCoreOf 2 M := Vq_le_pCoreOf h.L_le
  have hUn := le_normalizer_Uq (T := T) h.le_normalizer
  have hVn := le_normalizer_Vq (M := M) h.le_normalizer
  obtain ⟨x, hxQ, v₀, hv₀, hv₀x⟩ : ∃ x ∈ pCoreOf 2 M, ∃ v ∈ Vq M L, ⁅v, x⁆ ≠ 1 := by
    by_contra hall
    push Not at hall
    apply hVU
    have hVX : Vq M L ≤ Xq M := by
      intro v hv
      refine Subgroup.subset_closure ⟨⟨hVQ' hv, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩,
        hV2 v hv⟩
      exact ((commutatorElement_eq_one_iff_mul_comm).mp (hall y hy v hv)).symm
    have hVeq : Vq M L = ⁅Vq M L, L⁆ :=
      commutator_eq_commutator_commutator (pCoreOf_le' M) h.L_le (le_normalizer_pCoreOf M)
        h.le_normalizer h.perfect
    refine le_antisymm ?_ hUV
    rw [hVeq]
    exact (Subgroup.commutator_mono hVX le_rfl).trans hXL
  have hfmem : ∀ v ∈ Vq M L, ⁅v, x⁆ ∈ Uq M T L := fun v hv =>
    hVQ (Subgroup.commutator_mem_commutator hv hxQ)
  have hUcomm : ∀ u ∈ Uq M T L, ∀ v ∈ Vq M L, u * v = v * u := fun u hu v hv =>
    (commute_of_mem_pCoreOf_Xq (hVQ' hv) (h.Uq_le_Xq hu)).symm
  let f : ↥(Vq M L) →* ↥(Uq M T L) :=
    { toFun := fun v => ⟨⁅(v : G), x⁆, hfmem v v.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun v w => Subtype.ext (by
        simp only [Subgroup.coe_mul]
        have h1 := hUcomm _ (hfmem w w.2) v v.2
        calc ⁅(v : G) * w, x⁆ = (v : G) * ⁅(w : G), x⁆ * (v : G)⁻¹ * ⁅(v : G), x⁆ := by
              simp only [commutatorElement_def]; group
          _ = ⁅(w : G), x⁆ * ⁅(v : G), x⁆ := by rw [← h1]; group
          _ = ⁅(v : G), x⁆ * ⁅(w : G), x⁆ :=
              uq_comm h _ (hfmem w w.2) _ (hfmem v v.2)) }
  have hf : ∀ v : ↥(Vq M L), ((f v : ↥(Uq M T L)) : G) = ⁅(v : G), x⁆ := fun _ => rfl
  have hfeq : ∀ (l : ↥L) (v : ↥(Vq M L)),
      ⁅(l : G) * v * (l : G)⁻¹, x⁆ = (l : G) * ⁅(v : G), x⁆ * (l : G)⁻¹ := by
    intro l v
    set c := x⁻¹ * ((l : G)⁻¹ * x * (l : G)) with hcdef
    have hc : c ∈ Vq M L := by
      have := Subgroup.commutator_mem_commutator ((pCoreOf 2 M).inv_mem hxQ) (L.inv_mem l.2)
      rw [hcdef]
      simpa [commutatorElement_def, mul_assoc] using this
    have hcv : c * (v : G)⁻¹ = (v : G)⁻¹ * c := hVc _ hc _ ((Vq M L).inv_mem v.2)
    have h1 : ⁅(v : G), x * c⁆ = ⁅(v : G), x⁆ := by
      simp only [commutatorElement_def]
      calc (v : G) * (x * c) * (v : G)⁻¹ * (x * c)⁻¹ =
          (v : G) * x * (c * (v : G)⁻¹) * c⁻¹ * x⁻¹ := by group
        _ = (v : G) * x * ((v : G)⁻¹ * c) * c⁻¹ * x⁻¹ := by rw [hcv]
        _ = (v : G) * x * (v : G)⁻¹ * x⁻¹ := by group
    calc ⁅(l : G) * v * (l : G)⁻¹, x⁆ = (l : G) * ⁅(v : G), x * c⁆ * (l : G)⁻¹ := by
          rw [show x * c = (l : G)⁻¹ * x * (l : G) by rw [hcdef]; group]
          simp only [commutatorElement_def]
          group
      _ = (l : G) * ⁅(v : G), x⁆ * (l : G)⁻¹ := by rw [h1]
  have hrange : ∀ u ∈ Uq M T L, ∃ v ∈ Vq M L, ⁅v, x⁆ = u := by
    set I := (f.range).map (Uq M T L).subtype with hI
    have hIL : ∀ l : ↥L, ∀ y ∈ I, (l : G) * y * (l : G)⁻¹ ∈ I := by
      rintro l _ ⟨_, ⟨v, rfl⟩, rfl⟩
      have hv' : (l : G) * v * (l : G)⁻¹ ∈ Vq M L :=
        (Subgroup.mem_normalizer_iff.mp (hVn (h.L_le l.2)) v).mp v.2
      refine ⟨f ⟨_, hv'⟩, ⟨⟨_, hv'⟩, rfl⟩, ?_⟩
      simp only [Subgroup.coe_subtype, hf]
      exact hfeq l v
    have hUI : Uq M T L ≤ I := N.le_of_invariant ha hIL
      (⟨f ⟨v₀, hv₀⟩, ⟨⟨v₀, hv₀⟩, rfl⟩, rfl⟩ : ⁅v₀, x⁆ ∈ I) (hfmem v₀ hv₀) hv₀x
    intro u hu
    obtain ⟨_, ⟨v, rfl⟩, hvu⟩ := hUI hu
    exact ⟨v, v.2, hvu⟩
  have hsurj : Function.Surjective f := fun u => by
    obtain ⟨v, hv, hvu⟩ := hrange u u.2
    exact ⟨⟨v, hv⟩, Subtype.ext hvu⟩
  have hUker : (Uq M T L).subgroupOf (Vq M L) ≤ f.ker := by
    intro v hv
    rw [MonoidHom.mem_ker]
    refine Subtype.ext ?_
    rw [hf, OneMemClass.coe_one, commutatorElement_eq_one_iff_mul_comm]
    exact (commute_of_mem_pCoreOf_Xq hxQ (h.Uq_le_Xq hv)).symm
  have hker : f.ker = (Uq M T L).subgroupOf (Vq M L) := by
    have h1 := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top] at h1
    have hUc := N.card_eq
    rw [Nat.card_eq_fintype_card (α := F)] at hUc
    have hcU' : Nat.card ↥((Uq M T L).subgroupOf (Vq M L)) = Nat.card ↥(Uq M T L) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv
    refine (Subgroup.eq_of_le_of_card_ge hUker ?_).symm
    rw [hcU']
    have hUpos : 0 < Nat.card ↥(Uq M T L) := Nat.card_pos
    have h2 : Nat.card ↥f.ker * Nat.card ↥(Uq M T L) ≤
        Nat.card ↥(Uq M T L) * Nat.card ↥(Uq M T L) := by
      rw [h1]
      calc Nat.card ↥(Vq M L) ≤ Fintype.card F ^ 3 * Nat.card ↥(Uq M T L) := hVcard
        _ = Nat.card ↥(Uq M T L) * Nat.card ↥(Uq M T L) := by rw [← hUc]
    exact Nat.le_of_mul_le_mul_right h2 hUpos
  obtain ⟨-, -, β, hβs, hβk, hβe⟩ := hU
  refine ⟨hVn.trans' h.L_le, hUV, β.comp f, hβs.comp hsurj, ?_, ?_⟩
  · ext v
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf,
      Subgroup.mem_bot, ← hker, MonoidHom.mem_ker]
    exact ⟨fun h' => Subtype.ext h', fun h' => congrArg Subtype.val h'⟩
  · intro l u v huv i
    refine hβe l (f u) (f v) ?_ i
    rw [hf, hf, huv]
    exact hfeq l u

end Natural

theorem s36SL3Ext_holds :
    ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L),
      critDist (puAmalgam h.le) = 2 → Vq M L ≠ Uq M T L → ⁅Xq M, L⁆ ≤ Uq M T L →
      (∀ α' : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) (baseA _) α' →
        S33i h α' (Qv (puAmalgam h.le) (baseA _))) →
      IsDoubleSL3Ext M T L := by
  intro G _ _ M T L h hb hVU hXL hS
  obtain ⟨ψ, hψ⟩ := exists_critical_inr h hb
  obtain ⟨n, F, _, _, a, hq, ha, hU, hXZU, -, hR, hH⟩ :=
    s33i_data h ψ (hS _ ((isCritical_inr_iff h hb ψ).mpr hψ))
  have hψ' := not_le_tImage_inv h hb hψ
  obtain ⟨n', F', _, _, a', hq', -, hU', -, -, hR', -⟩ :=
    s33i_data h ψ⁻¹ (hS _ ((isCritical_inr_iff h hb ψ⁻¹).mpr hψ'))
  have hqq : 2 ^ n' = 2 ^ n := by
    have h1 := (NatSec.ofIsSum hU).card_eq
    have h2 := (NatSec.ofIsSum hU').card_eq
    rw [h1, Nat.card_eq_fintype_card, hq, Nat.card_eq_fintype_card, hq'] at h2
    exact (Nat.pow_left_injective (by norm_num : (3 : ℕ) ≠ 0) h2).symm
  have : CharP F 2 := FFC.charP_two_of_card_pow (n := n) (by rw [Nat.card_eq_fintype_card, hq])
  set N := NatSec.ofIsSum hU with hN
  have hRq : Nat.card ↥⁅Z0q M T, tImage ψ (Z0q M T)⁆ = Fintype.card F := by rw [hR, hq]
  have hR'q : Nat.card ↥⁅Z0q M T, tImage ψ⁻¹ (Z0q M T)⁆ = Fintype.card F := by
    rw [hR', hqq, hq]
  have hHq : Nat.card ↥⁅pCoreOf 2 M, tImage ψ (Z0q M T)⁆ = Fintype.card F * Fintype.card F := by
    rw [hH, hq]
  have hHQ := commutator_H_le h N ha hb hψ hR'q hHq
  have hVQ := commutator_Vq_le h hb hψ hHQ
  obtain ⟨hRF, t₀, ht₀L, ht₀R, ht₀1, ht₀2, ht₀C, ht₀V⟩ := exists_t0 h N ha hRq hVQ
  have hZT : Z0q M T ≤ T := Z0q_le_T h
  have hZψT : tImage ψ (Z0q M T) ≤ T := tImage_le _ _
  have hRU : ⁅Z0q M T, tImage ψ (Z0q M T)⁆ ≤ Uq M T L := by
    rw [S33.commutator_Z0q_eq h hZψT]
    exact commutator_le_left_of_le_normalizer (hZψT.trans (T_le_normalizer_Uq h))
  have hRH : ⁅Z0q M T, tImage ψ (Z0q M T)⁆ ≤ ⁅pCoreOf 2 M, tImage ψ (Z0q M T)⁆ :=
    Subgroup.commutator_mono h.Z0q_le_pCoreOf le_rfl
  have hHQ' : ⁅pCoreOf 2 M, tImage ψ (Z0q M T)⁆ ≤ pCoreOf 2 M :=
    commutator_le_left_of_le_normalizer ((hZψT.trans h.le).trans (le_normalizer_pCoreOf M))
  have hHZ : ⁅pCoreOf 2 M, tImage ψ (Z0q M T)⁆ ≤ tImage ψ (Z0q M T) := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_left_of_le_normalizer (h.pCore_le.trans
      (le_normalizer_tImage (h.le.trans (le_normalizer_Z0q M T)) ψ))
  have hZab := h.isElemAbelian_Z0q
  have hZcomm : ∀ x ∈ Z0q M T, ∀ y ∈ Z0q M T, x * y = y * x :=
    fun x hx y hy => commute_of_mem_pCoreOf_Xq (h.Z0q_le_pCoreOf hx) (h.Z0q_le_Xq hy)
  have hHab : ∀ x ∈ ⁅pCoreOf 2 M, tImage ψ (Z0q M T)⁆, ∀ y ∈ ⁅pCoreOf 2 M, tImage ψ (Z0q M T)⁆,
      x * y = y * x := fun x hx y hy => commute_of_mem_tImage hZcomm (hHZ hx) (hHZ hy)
  have hH2 : ∀ x ∈ ⁅pCoreOf 2 M, tImage ψ (Z0q M T)⁆, x ^ 2 = 1 := fun x hx =>
    sq_eq_one_of_mem_tImage hZab.2 (hHZ hx)
  obtain ⟨hVc, hV2, hVcard⟩ := elem_and_card h N ha hU hRU hRH hRq hRF hHQ' hHq hHab hH2 hHQ
    hVQ ht₀L ht₀R ht₀1 ht₀2 ht₀C ht₀V
  exact ⟨frattiniIn_eq_bot_of_elem hVc hV2, hXZU, n, F, inferInstance, inferInstance, a, hq, ha,
    hU, natural_of_elem h ha hU hVU hXL hVc hV2 hVcard hVQ⟩

end CFSG.Quasithin.MS93.S36
