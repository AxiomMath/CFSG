module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FD
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5FC

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits
open scoped commutatorElement

section Generic

variable {Γ : Type*} [Group Γ] [Finite Γ]

theorem mem_commV_of_conj_ch615 {V : Type*} [CommGroup V] {X : Subgroup (MulAut V)}
    {t : MulAut V} (ht : ∀ x ∈ X, t * x * t⁻¹ ∈ X) {w : V} (hw : w ∈ commV X) :
    t w ∈ commV X :=
  CFSG.Quasithin.commV_apply_mem_of_normalizes ht hw

theorem exists_fix_ch615 {V : Type*} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {P : Subgroup (MulAut V)} (hP : IsPGroup 2 P) {W : Subgroup V} (hW : W ≠ ⊥)
    (hPW : ∀ p ∈ P, ∀ w ∈ W, p w ∈ W) : ∃ w ∈ W, w ≠ 1 ∧ ∀ p ∈ P, p w = w := by
  classical
  let _ : MulAction ↥P ↥W :=
    { smul := fun p w => ⟨(p : MulAut V) w, hPW p p.2 w w.2⟩
      one_smul := fun w => Subtype.ext rfl
      mul_smul := fun p q w => Subtype.ext rfl }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hP.card_modEq_card_fixedPoints ↥W
  have hW2 : IsPGroup 2 ↥W := fun w => ⟨1, Subtype.ext (by simpa using hV w)⟩
  obtain ⟨n, hn⟩ := hW2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero, Subgroup.card_eq_one] at hn
    exact hW hn
  have heven : Nat.card ↥W % 2 = 0 := by
    rw [hn]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hn0)
  by_contra hno
  have hfix : Nat.card (MulAction.fixedPoints ↥P ↥W) = 1 := by
    rw [Nat.card_eq_one_iff_exists]
    refine ⟨⟨1, fun p => Subtype.ext (map_one _)⟩, fun ⟨w, hw⟩ => Subtype.ext ?_⟩
    by_contra hw1
    exact hno ⟨w, w.2, fun h => hw1 (Subtype.ext h), fun p hp =>
      congrArg Subtype.val (hw ⟨p, hp⟩)⟩
  rw [hfix] at hmod
  unfold Nat.ModEq at hmod
  omega

end Generic

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ}

omit [Finite G] in
theorem autI_commutator_ch615 {V : Subgroup G} (hV : IsElemAbelian 2 V) {A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (V : Set G)) (hB : B ≤ Subgroup.normalizer (V : Set G)) :
    autI hV ⁅A, B⁆ = ⁅autI hV A, autI hV B⁆ := by
  have hAB : ⁅A, B⁆ ≤ Subgroup.normalizer (V : Set G) :=
    Subgroup.commutator_le.2 fun a ha b hb => by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hA ha) (hB hb))
        (Subgroup.inv_mem _ (hA ha))) (Subgroup.inv_mem _ (hB hb))
  unfold autI
  rw [← Subgroup.map_commutator]
  congr 1
  apply Subgroup.map_injective (Subgroup.normalizer (V : Set G)).subtype_injective
  rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hA,
    Subgroup.map_subgroupOf_eq_of_le hB, Subgroup.map_subgroupOf_eq_of_le hAB]

namespace Cx615C

theorem isSylowTwoOf_autI_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H)) :
    IsSylowTwoOf (autI hU T) (autI hU (borelL T L ⊔ H)) := by
  have hTX : T ≤ borelL T L ⊔ H := c.hH.1.1.trans le_sup_right
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hsyl : IsSylowTwoOf T (borelL T L ⊔ H) := c.hyp.toHyp5_0_1.isSylowTwoOf hTX
  have := Setup.Wreath.isSylowTwoOf_map_hom hsyl (convHom hU _ hXN)
  rwa [range_convHom, ← autI_eq_map_convHom hU hXN hTX] at this

theorem isPGroup_autI_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H)) :
    IsPGroup 2 ↥(autI hU T) :=
  (c.isSylowTwoOf_autI_ch615 hU).isPGroup

theorem le_commutator_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H)) :
    autI hU (oTwoUpper H) ≤ ⁅autI hU (oTwoUpper H), autI hU (thompsonJ T)⁆ := by
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hKN : oTwoUpper H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    ((oTwoUpper_le H).trans le_sup_right).trans hXN
  have hJN : thompsonJ T ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    ((thompsonJ_le_self T).trans (c.hH.1.1.trans le_sup_right)).trans hXN
  rw [← autI_commutator_ch615 hU hKN hJN, c.JK]

theorem isSolvable_autI_ch615 (c : Cx615C G T M L V H n) (hU : IsElemAbelian 2 (UX615 T L H)) :
    Group.IsSolvable ↥(autI hU (borelL T L ⊔ T)) := by
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hBTN : borelL T L ⊔ T ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    (sup_le le_sup_left (c.hH.1.1.trans le_sup_right)).trans hXN
  have := c.isSolvable_borelL_sup_ch615
  rw [← range_convHom hU _ hBTN]
  exact Group.isSolvable_of_surjective (convHom hU _ hBTN).rangeRestrict_surjective

theorem autI_le_normalizer_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H)) :
    autI hU T ≤ Subgroup.normalizer (autI hU (borelL T L) : Set (MulAut _)) := by
  have hTB : T ≤ Subgroup.normalizer (borelL T L : Set G) := c.hyp.toHyp5_0_1.T_le_normalizer_borel
  intro y hy
  refine Subgroup.mem_normalizer_iff.mpr fun a => ⟨fun ha => C124.autI_conj_mem hU hTB y hy a ha,
    fun ha => ?_⟩
  have := C124.autI_conj_mem hU hTB y⁻¹ ((autI hU T).inv_mem hy) _ ha
  simpa [mul_assoc] using this

theorem mem_autI_borelL_of_odd_ch615 (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H)) {y : MulAut (IntMod (UX615 T L H) hU)}
    (hy : y ∈ autI hU (borelL T L ⊔ T)) (hodd : Odd (orderOf y)) : y ∈ autI hU (borelL T L) := by
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hBN : borelL T L ≤ Subgroup.normalizer (UX615 T L H : Set G) := le_sup_left.trans hXN
  have hTN : T ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    (c.hH.1.1.trans le_sup_right).trans hXN
  rw [autI_sup hU hBN hTN] at hy
  exact mem_of_odd_of_mem_sup_ch615 (c.isPGroup_autI_ch615 hU) (c.autI_le_normalizer_ch615 hU) hy
    hodd

theorem le_or_le_ch615 (h331 : Stmt3_3_1) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H)) {A B : Subgroup (MulAut (IntMod (UX615 T L H) hU))}
    (hA : A ≤ autI hU (oTwoUpper H)) (hB : B ≤ autI hU (oTwoUpper H))
    (hTA : autI hU T ≤ Subgroup.normalizer (A : Set (MulAut (IntMod (UX615 T L H) hU))))
    (hTB : autI hU T ≤ Subgroup.normalizer (B : Set (MulAut (IntMod (UX615 T L H) hU))))
    (hK : ∀ k ∈ autI hU (oTwoUpper H), ∃ a ∈ A, ∃ b ∈ B, a * b = k) :
    autI hU (oTwoUpper H) ≤ A ∨ autI hU (oTwoUpper H) ≤ B := by
  classical
  have hmp := c.toCx615.minParabolic h331
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hHN : H ≤ Subgroup.normalizer (UX615 T L H : Set G) := le_sup_right.trans hXN
  have hTH : T ≤ H := c.hH.1.1
  have hT2 := c.isPGroup_autI_ch615 hU
  have key : ∀ C : Subgroup (MulAut (IntMod (UX615 T L H) hU)),
      autI hU T ≤ Subgroup.normalizer (C : Set (MulAut _)) →
      H ≤ preI615 hU (C ⊔ autI hU T) → autI hU (oTwoUpper H) ≤ C := by
    intro C hTC hHC
    refine autI_le_of_le_preI615 ((Subgroup.closure_le _).mpr ?_)
    rintro x ⟨hxH, hxodd⟩
    have hxN := hHN hxH
    obtain ⟨y, hy, hyx⟩ := hHC hxH
    have hy' : y = ⟨x, hxN⟩ := Subtype.ext hyx
    rw [hy'] at hy
    refine mem_preI615 hxN (mem_of_odd_of_mem_sup_ch615 hT2 hTC hy ?_)
    have := orderOf_map_dvd (convI hU) ⟨x, hxN⟩
    rw [Subgroup.orderOf_mk] at this
    exact Odd.of_dvd_nat hxodd this
  by_contra hno
  obtain ⟨hnA, hnB⟩ := not_or.mp hno
  have hT_le : ∀ C : Subgroup (MulAut (IntMod (UX615 T L H) hU)),
      T ≤ H ⊓ preI615 hU (C ⊔ autI hU T) := fun C t ht =>
    ⟨hTH ht, mem_preI615 (hHN (hTH ht))
      (Subgroup.mem_sup_right (convI_mem_autI hU ht (hHN (hTH ht))))⟩
  have hle_M : ∀ C : Subgroup (MulAut (IntMod (UX615 T L H) hU)),
      autI hU T ≤ Subgroup.normalizer (C : Set (MulAut _)) → ¬ autI hU (oTwoUpper H) ≤ C →
      H ⊓ preI615 hU (C ⊔ autI hU T) ≤ H ⊓ M := by
    intro C hTC hnC
    have hlt : H ⊓ preI615 hU (C ⊔ autI hU T) < H := by
      exact lt_of_le_of_ne inf_le_left fun h => hnC (key C hTC fun x hx => (h.ge hx).2)
    obtain ⟨N, hN, hYN⟩ := exists_isMaxSubgroupIn hlt
    rw [← hmp.eq_of_maximal hN ((hT_le C).trans hYN)]
    exact hYN
  have hYA := hle_M A hTA hnA
  have hYB := hle_M B hTB hnB
  have hHle : H ≤ (H ⊓ preI615 hU (A ⊔ autI hU T)) ⊔ (H ⊓ preI615 hU (B ⊔ autI hU T)) := by
    have hsup : T ⊔ twoResidual H = H := sup_twoResidual_eq c.toCx615.isSylowTwoOf
    rw [twoResidual_eq_oTwoUpper'] at hsup
    intro x hx
    have hx' : x ∈ T ⊔ oTwoUpper H := by rw [hsup]; exact hx
    refine (sup_le ((hT_le A).trans le_sup_left) fun k hk => ?_) hx'
    have hkH : k ∈ H := oTwoUpper_le H hk
    have hkN := hHN hkH
    obtain ⟨a, ha, b, hb, hab⟩ := hK _ (convI_mem_autI hU hk hkN)
    obtain ⟨ka, hka, hkae⟩ := (mem_autI hU).mp (hA ha)
    obtain ⟨kb, hkb, hkbe⟩ := (mem_autI hU).mp (hB hb)
    have hkaA : convI hU ka ∈ A ⊔ autI hU T := by rw [hkae]; exact Subgroup.mem_sup_left ha
    have hkbB : convI hU kb ∈ B ⊔ autI hU T := by rw [hkbe]; exact Subgroup.mem_sup_left hb
    have hkaY : (ka : G) ∈ H ⊓ preI615 hU (A ⊔ autI hU T) :=
      ⟨oTwoUpper_le H hka, mem_preI615 ka.2 hkaA⟩
    have hkbY : (kb : G) ∈ H ⊓ preI615 hU (B ⊔ autI hU T) :=
      ⟨oTwoUpper_le H hkb, mem_preI615 kb.2 hkbB⟩
    set r : ↥(Subgroup.normalizer (UX615 T L H : Set G)) := ⟨k, hkN⟩ * (ka * kb)⁻¹ with hr
    have hr1 : convI hU r = 1 := by
      rw [hr, map_mul, map_inv, map_mul, hkae, hkbe, hab, mul_inv_cancel]
    have hrA : convI hU r ∈ A ⊔ autI hU T := by rw [hr1]; exact Subgroup.one_mem _
    have hrH : (r : G) ∈ H :=
      H.mul_mem hkH (H.inv_mem (H.mul_mem (oTwoUpper_le H hka) (oTwoUpper_le H hkb)))
    have hrY : (r : G) ∈ H ⊓ preI615 hU (A ⊔ autI hU T) := ⟨hrH, mem_preI615 r.2 hrA⟩
    have e : k = (r : G) * ka * kb := by
      rw [hr]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hrY)
      (Subgroup.mem_sup_left hkaY)) (Subgroup.mem_sup_right hkbY)
  exact c.hH.2.1 ((hHle.trans (sup_le hYA hYB)).trans inf_le_right)

theorem false_of_fix_ch615 (h432 : Stmt4_3_2) (c : Cx615C G T M L V H n)
    (hU : IsElemAbelian 2 (UX615 T L H)) {D : Subgroup G}
    (hD : Lin2.IsHallTwoPrimeOf D (borelL T L)) {w : IntMod (UX615 T L H) hU} (hw1 : w ≠ 1)
    (hwT : ∀ t ∈ autI hU T, t w = w) (hwK : ∀ k ∈ autI hU (oTwoUpper H), k w = w)
    {δ : MulAut (IntMod (UX615 T L H) hU)} (hδ : δ ∈ autI hU D) (hδ1 : δ ≠ 1)
    (hδw : δ w = w) : False := by
  have hTX : T ≤ borelL T L ⊔ H := c.hH.1.1.trans le_sup_right
  have hXN : borelL T L ⊔ H ≤ Subgroup.normalizer (UX615 T L H : Set G) :=
    le_normalizer_conjClosure _ _
  have hUT : UX615 T L H ≤ T :=
    c.U_red_ch615.1.trans (F7.isSylowTwoOf_pCoreOf_le (c.hyp.toHyp5_0_1.isSylowTwoOf hTX))
  set z := w.val with hz
  have hzU : z ∈ UX615 T L H := w.val_mem
  have hfix : ∀ g (hg : g ∈ Subgroup.normalizer (UX615 T L H : Set G)),
      convI hU ⟨g, hg⟩ w = w → g * z * g⁻¹ = z := fun g hg h => by
    have := congrArg IntMod.val h
    rwa [convI_apply_val] at this
  have hzC : z ∈ Subgroup.centralizer (T : Set G) := Subgroup.mem_centralizer_iff.mpr fun t ht => by
    have htN := hXN (hTX ht)
    have h1 := hfix t htN (hwT _ (convI_mem_autI hU ht htN))
    calc t * z = t * z * t⁻¹ * t := by group
      _ = z * t := by rw [h1]
  have hz2 : z ^ 2 = 1 := by simpa [pow_two] using hU.2 z hzU
  have hzZ : z ∈ quasithinOmegaOneCenter T :=
    mem_quasithinOmegaOneCenter_iff.mpr ⟨hUT hzU, hzC, hz2⟩
  have hz1 : z ≠ 1 := fun h => hw1 (IntMod.val_injective (by rw [← hz, h, IntMod.val_one]))
  have hKz : oTwoUpper H ≤ Subgroup.centralizer ({z} : Set G) := fun k hk => by
    have hkN := hXN (Subgroup.mem_sup_right (oTwoUpper_le H hk))
    have h1 := hfix k hkN (hwK _ (convI_mem_autI hU hk hkN))
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    calc z * k = k * z * k⁻¹ * k := by rw [h1]
      _ = k * z := by group
  obtain ⟨⟨d, hdN⟩, hdD, rfl⟩ := (mem_autI hU).mp hδ
  have hd1 : d ≠ 1 := fun h => hδ1 (by
    have : (⟨d, hdN⟩ : ↥(Subgroup.normalizer (UX615 T L H : Set G))) = 1 := Subtype.ext h
    rw [this, map_one])
  have hdodd : Odd (orderOf d) := Odd.of_dvd_nat hD.2.1 (Subgroup.orderOf_dvd_natCard D hdD)
  exact false_of_centralizes_ch615 h432 c hzZ hz1 hKz (hD.1 hdD) hdodd hd1 (hfix d hdN hδw)

end Cx615C

end CFSG.Quasithin.H13
