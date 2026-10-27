module

public import CFSG.Quasithin.Vol2.Ch3Sec1Lem319Defs
public import CFSG.Quasithin.Background.A4Aut

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section Q

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def qMin (M V : Subgroup G) (hV : IsElemAbelian 2 V) : ℕ :=
  sInf ((fun D : Subgroup (MulAut ↥V) => rk ↥D) ''
    @Qset ↥V (commGroupOfElemAbelian hV) (autOn M V))

omit [Finite G] in
theorem map_subtype_commSub_le {V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hA : A ≤ Subgroup.normalizer (V : Set G)) (W : Subgroup ↥V) :
    (@commSub ↥V (commGroupOfElemAbelian hV) W (autOn A V)).map V.subtype ≤
      ⁅W.map V.subtype, A⁆ := by
  rw [Subgroup.map_le_iff_le_comap]
  unfold commSub
  rw [Subgroup.closure_le]
  rintro _ ⟨x, hx, w, hw, rfl⟩
  obtain ⟨a, rfl⟩ := (A4.mem_autOn_iff hA).mp hx
  show (((A4.actionOn V A hA a) w * w⁻¹ : ↥V) : G) ∈ ⁅W.map V.subtype, A⁆
  rw [← Subgroup.commutator_comm]
  have h1 : (((A4.actionOn V A hA a) w * w⁻¹ : ↥V) : G) = ⁅(a : G), (w : G)⁆ := by
    rw [Subgroup.coe_mul, A4.actionOn_apply_coe, commutatorElement_def]
    simp
  rw [h1]
  exact Subgroup.commutator_mem_commutator a.2 (Subgroup.mem_map.mpr ⟨w, hw, rfl⟩)

omit [Finite G] in
theorem commSeries_two_autOn_eq_bot {V A : Subgroup G} (hV : IsElemAbelian 2 V)
    (hA : A ≤ Subgroup.normalizer (V : Set G)) (h : ⁅⁅V, A⁆, A⁆ = ⊥) :
    @commSeries ↥V (commGroupOfElemAbelian hV) (autOn A V) 2 = ⊥ := by
  have h1 := map_subtype_commSub_le hV hA (⊤ : Subgroup ↥V)
  rw [Subgroup.map_top, Subgroup.range_subtype] at h1
  have h2 := map_subtype_commSub_le hV hA
    (@commSub ↥V (commGroupOfElemAbelian hV) ⊤ (autOn A V))
  have h3 : ⁅(@commSub ↥V (commGroupOfElemAbelian hV) ⊤ (autOn A V)).map V.subtype, A⁆ ≤ ⊥ :=
    h ▸ Subgroup.commutator_mono h1 le_rfl
  have h4 := h2.trans h3
  exact (Subgroup.map_eq_bot_iff_of_injective _ V.subtype_injective).mp (le_bot_iff.mp h4)

theorem mem_Qset_autOn {M V B' : Subgroup G} (hV : IsElemAbelian 2 V) (hB'M : B' ≤ M)
    (hB'N : B' ≤ Subgroup.normalizer (V : Set G)) (hB'el : IsElemAbelian 2 B')
    (hnc : ¬ B' ≤ Subgroup.centralizer (V : Set G)) (hq : ⁅⁅V, B'⁆, B'⁆ = ⊥)
    (hr : secRank V (V ⊓ Subgroup.centralizer (B' : Set G)) =
      2 * secRank B' (B' ⊓ Subgroup.centralizer (V : Set G))) :
    autOn B' V ∈ @Qset ↥V (commGroupOfElemAbelian hV) (autOn M V) ∧
      rk ↥(autOn B' V) = secRank B' (B' ⊓ Subgroup.centralizer (V : Set G)) := by
  have hA2 : @IsA2 ↥V (commGroupOfElemAbelian hV) (autOn M V) (autOn B' V) :=
    ⟨autOn_le_autOn V hB'M, autOn_ne_bot_of_not_le_centralizer hB'N hnc,
      isElemAbelian2_autOn hV hB'el hB'N⟩
  have hrk : rk ↥(autOn B' V) = secRank B' (B' ⊓ Subgroup.centralizer (V : Set G)) := by
    unfold rk secRank rkIdx
    rw [card_autOn_eq_relIndex hB'N]
    rfl
  have hidx : @rkIdx ↥V _ (@fixV ↥V (commGroupOfElemAbelian hV) (autOn B' V)) =
      secRank V (V ⊓ Subgroup.centralizer (B' : Set G)) := by
    have e1 := Subgroup.card_mul_index (@fixV ↥V (commGroupOfElemAbelian hV) (autOn B' V))
    have e2 := Subgroup.card_mul_index
      ((V ⊓ Subgroup.centralizer (B' : Set G)).subgroupOf V)
    have hc : Nat.card (@fixV ↥V (commGroupOfElemAbelian hV) (autOn B' V)) =
        Nat.card ((V ⊓ Subgroup.centralizer (B' : Set G)).subgroupOf V) := by
      rw [card_fixV_autOn_eq hV hB'N]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
    have hpos : 0 < Nat.card (@fixV ↥V (commGroupOfElemAbelian hV) (autOn B' V)) :=
      Nat.card_pos
    have hind : (@fixV ↥V (commGroupOfElemAbelian hV) (autOn B' V)).index =
        ((V ⊓ Subgroup.centralizer (B' : Set G)).subgroupOf V).index := by
      refine Nat.eq_of_mul_eq_mul_left hpos ?_
      calc _ = Nat.card ↥V := e1
        _ = Nat.card ((V ⊓ Subgroup.centralizer (B' : Set G)).subgroupOf V) *
              ((V ⊓ Subgroup.centralizer (B' : Set G)).subgroupOf V).index := e2.symm
        _ = _ := by rw [← hc]
    unfold secRank rkIdx
    rw [hind]
  have hpos : 0 < rk ↥(autOn B' V) := @IsA2.rk_pos ↥V (commGroupOfElemAbelian hV) _ _ _ hA2
  have hrAV : @rAV ↥V (commGroupOfElemAbelian hV) (autOn B' V) = 2 := by
    unfold rAV
    rw [hidx, hr, ← hrk]
    have : (rk ↥(autOn B' V) : ℚ) ≠ 0 := by exact_mod_cast hpos.ne'
    push_cast
    field_simp
  exact ⟨⟨⟨hA2, hrAV.le⟩, commSeries_two_autOn_eq_bot hV hB'N hq⟩, hrk⟩

end Q

section Conj

variable {G : Type} [Group G]

theorem relIndex_conjSub (g : G) (N L : Subgroup G) :
    (B6.conjSub g L).relIndex (B6.conjSub g N) = L.relIndex N :=
  Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) L N
    (MulAut.conj g).injective

theorem secRank_conjSub (g : G) (N L : Subgroup G) :
    secRank (B6.conjSub g N) (B6.conjSub g L) = secRank N L :=
  congrArg (padicValNat 2) (relIndex_conjSub g N L)

theorem B6conjSub_centralizer (g : G) (S : Subgroup G) :
    B6.conjSub g (Subgroup.centralizer (S : Set G)) =
      Subgroup.centralizer ((B6.conjSub g S : Subgroup G) : Set G) := by
  ext x
  rw [B6.mem_conjSub, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h t ht
    have ht' : t ∈ B6.conjSub g S := ht
    rw [B6.mem_conjSub] at ht'
    have := h _ ht'
    calc t * x = g * ((g⁻¹ * t * g) * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * (g⁻¹ * t * g)) * g⁻¹ := by rw [this]
      _ = x * t := by group
  · intro h s hs
    have hs' : g * s * g⁻¹ ∈ B6.conjSub g S := by
      rw [B6.mem_conjSub]
      simpa [mul_assoc] using hs
    have := h (g * s * g⁻¹) hs'
    calc s * (g⁻¹ * x * g) = g⁻¹ * ((g * s * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * s * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * x * g * s := by group

theorem B6conjSub_commutator (g : G) (X Y : Subgroup G) :
    B6.conjSub g ⁅X, Y⁆ = ⁅B6.conjSub g X, B6.conjSub g Y⁆ :=
  Subgroup.map_commutator (f := (MulAut.conj g).toMonoidHom) (H₁ := X) (H₂ := Y)

theorem conjSub_conjSubgroup (g : G) (V : Subgroup G) :
    B6.conjSub g (conjSubgroup V g) = V := by
  ext x
  rw [B6.mem_conjSub, mem_conjSubgroup_iff]
  have : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rw [this]

end Conj

end CFSG.Quasithin
