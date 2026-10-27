module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSAReciprocalFusion
public import CFSG.Quasithin.Vol2.Ch11SecU1Defs
public import CFSG.Quasithin.Vol2.Ch11SecU1Dih
public import CFSG.Quasithin.Vol2.Ch11SecU1In1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2KleinFourSelfCentralizer

public section

namespace CFSG.Quasithin.RonanE114.L2

open CFSG.GorensteinWalter CFSG.Quasithin.Vol2.Ch11.SecU1

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K] [Finite K] {p f : ℕ}
  [Fact p.Prime]

theorem inner_conj_gen (e : L ≃* PSL2 K) (hK : Nat.card K = p ^ f) (hp : Odd p) (hf : 0 < f)
    {x y : G} (hxL : x ∈ L) (hyL : y ∈ L) (hx : orderOf x = 2) (hy : orderOf y = 2) :
    ∃ g ∈ L, g * x * g⁻¹ = y := by
  have hord : ∀ (z : G) (hz : z ∈ L), orderOf z = 2 → orderOf (e ⟨z, hz⟩) = 2 := fun z hz h =>
    by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, h]
  obtain ⟨c, hc⟩ := isConj_iff.mp (CFSG.Walter.psl2_isConj_of_orderOf_eq_two K hK hp hf
    (hord x hxL hx) (hord y hyL hy))
  refine ⟨embL e c, embL_mem e c, ?_⟩
  have h1 : x = embL e (e ⟨x, hxL⟩) := (embL_apply e hxL).symm
  rw [h1, ← map_inv, ← map_mul, ← map_mul, hc, embL_apply]

theorem inner_dihedral_gen (e : L ≃* PSL2 K) (hK : Nat.card K = p ^ f) (hp : Odd p) (hf : 0 < f)
    (h7 : 7 ≤ p ^ f) {x : G} (hxL : x ∈ L) (hx : orderOf x = 2) :
    ∃ n : ℕ, 4 ≤ n ∧ Even n ∧ Nonempty (↥(L ⊓ Subgroup.centralizer {x}) ≃* DihedralGroup n) ∧
      ((p ^ f % 4 = 1 ∧ 2 * n = p ^ f - 1) ∨ (p ^ f % 4 = 3 ∧ 2 * n = p ^ f + 1)) := by
  have hex : orderOf (e ⟨x, hxL⟩) = 2 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx]
  obtain ⟨h1, h3⟩ := CFSG.Walter.psl2_centralizer_involution K hK hp hf hex
  obtain ⟨n, hn4, hneven, hcard, ⟨d⟩⟩ :=
    CFSG.Walter.psl2_centralizer_involution_dihedral K hK hp hf h7 hex
  have hq4 : p ^ f % 4 = 1 ∨ p ^ f % 4 = 3 := by
    have := Nat.odd_iff.mp (hp.pow (n := f))
    omega
  refine ⟨n, hn4, hneven, ?_, ?_⟩
  · rw [inf_centralizer_eq_map e hxL]
    exact ⟨((Subgroup.centralizer {e ⟨x, hxL⟩}).equivMapOfInjective _
      (embL_injective e)).symm.trans d⟩
  · rcases hq4 with hq4 | hq4
    · exact Or.inl ⟨hq4, by have := (h1 hq4).1; omega⟩
    · exact Or.inr ⟨hq4, by have := (h3 hq4).1; omega⟩

theorem inner_solvable_gen (e : L ≃* PSL2 K) (hK : Nat.card K = p ^ f) (hp : Odd p)
    (hf : 0 < f) (h7 : 7 ≤ p ^ f) {x : G} (hxL : x ∈ L) (hx : orderOf x = 2) :
    Group.IsSolvable ↥(L ⊓ Subgroup.centralizer {x}) := by
  obtain ⟨n, hn, -, ⟨d⟩, -⟩ := inner_dihedral_gen e hK hp hf h7 hxL hx
  have : NeZero n := ⟨by omega⟩
  have := CFSG.Walter.isSolvable_dihedralGroup' n
  exact Group.isSolvable_of_isSolvable_injective (f := d.toMonoidHom) d.injective

theorem inner_max_gen (e : L ≃* PSL2 K)
    (hco : ∀ t : PSL2 K, orderOf t = 2 → IsCoatom (Subgroup.centralizer ({t} : Set (PSL2 K))))
    {x : G} (hxL : x ∈ L) (hx : orderOf x = 2) (H : Subgroup G)
    (hlt : L ⊓ Subgroup.centralizer {x} < H) (hHL : H ≤ L) : H = L := by
  have hex : orderOf (e ⟨x, hxL⟩) = 2 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx]
  have hmap : (H.comap (embL e)).map (embL e) = H := by
    rw [Subgroup.map_comap_eq, range_embL, inf_eq_right.mpr hHL]
  rw [inf_centralizer_eq_map e hxL] at hlt
  have hle : Subgroup.centralizer {e ⟨x, hxL⟩} ≤ H.comap (embL e) :=
    (Subgroup.map_le_iff_le_comap).mp hlt.le
  have hne : Subgroup.centralizer {e ⟨x, hxL⟩} ≠ H.comap (embL e) := fun h =>
    hlt.ne (by rw [h, hmap])
  rw [← hmap, (hco _ hex).2 _ (lt_of_le_of_ne hle hne), ← MonoidHom.range_eq_map, range_embL]

theorem inner_center_gen (e : L ≃* PSL2 K) (hK : Nat.card K = p ^ f) (hp : Odd p) (hf : 0 < f)
    (h7 : 7 ≤ p ^ f) {x : G} (hxL : x ∈ L) (hx : orderOf x = 2) {y : G}
    (hy : y ∈ L ⊓ Subgroup.centralizer {x})
    (hcen : ∀ w ∈ L ⊓ Subgroup.centralizer {x}, y * w = w * y) : y ∈ Subgroup.zpowers x := by
  have hex : orderOf (e ⟨x, hxL⟩) = 2 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx]
  set C := Subgroup.centralizer ({e ⟨x, hxL⟩} : Set (PSL2 K)) with hC
  have hZ := CFSG.Walter.psl2_center_centralizer_involution K hK hp hf h7 hex
  rw [inf_centralizer_eq_map e hxL] at hy hcen
  obtain ⟨c, hcC, rfl⟩ := hy
  have hcZ : (⟨c, hcC⟩ : C) ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    apply embL_injective e
    have := hcen (embL e w) ⟨w, w.2, rfl⟩
    simpa [map_mul] using this.symm
  have hcz : c ∈ Subgroup.zpowers (e ⟨x, hxL⟩) := by
    rw [← hZ]
    exact ⟨⟨c, hcC⟩, hcZ, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcz
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← hk, map_zpow, embL_apply]

theorem inner_torus_gen
    (e : L ≃* PSL2 K) (hLn : L.Normal) (hK : Nat.card K = p ^ f)
    (hp : Odd p) (hf : 0 < f) (h7 : 7 ≤ p ^ f) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrq : (p ^ f % 4 = 1 → r ∣ p ^ f - 1) ∧ (p ^ f % 4 = 3 → r ∣ p ^ f + 1))
    {x : G} (hxL : x ∈ L) (hx : orderOf x = 2) : OddTorus L x := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨n, hn4, hneven, ⟨d⟩, hcases⟩ := inner_dihedral_gen e hK hp hf h7 hxL hx
  have : NeZero n := ⟨by omega⟩
  set t := e ⟨x, hxL⟩ with ht
  have htx : x = embL e t := (embL_apply e hxL).symm
  have ht2 : orderOf t = 2 := by rw [ht, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx]
  set C := Subgroup.centralizer ({t} : Set (PSL2 K)) with hC
  set X := L ⊓ Subgroup.centralizer ({x} : Set G) with hX
  have hXmap : X = C.map (embL e) := inf_centralizer_eq_map e hxL
  have hcardX : Nat.card X = 2 * n := by
    rw [Nat.card_congr d.toEquiv, DihedralGroup.nat_card]
  have hcardC : Nat.card C = Nat.card X := by
    rw [hXmap]
    exact (Subgroup.card_map_of_injective (embL_injective e)).symm
  have hrcard : r ∣ Nat.card C := by
    rw [hcardC, hcardX]
    rcases hcases with ⟨h4, h2n⟩ | ⟨h4, h2n⟩
    · rw [h2n]; exact hrq.1 h4
    · rw [h2n]; exact hrq.2 h4
  obtain ⟨y₀, hy₀⟩ := exists_prime_orderOf_dvd_card' (G := C) r hrcard
  set A₀ : Subgroup (PSL2 K) := Subgroup.zpowers (y₀ : PSL2 K) with hA₀
  have hA₀C : A₀ ≤ C := Subgroup.zpowers_le.mpr y₀.2
  have hA₀card : Nat.card A₀ = r := by
    rw [hA₀, Nat.card_zpowers, Subgroup.orderOf_coe, hy₀]
  have hrodd : Odd r := hr.odd_of_ne_two hr2
  set P := A₀.map (embL e) with hP
  have hPcard : Nat.card P = r := by
    rw [hP, Subgroup.card_map_of_injective (embL_injective e), hA₀card]
  have hPX : P ≤ X := by rw [hXmap]; exact Subgroup.map_mono hA₀C
  refine ⟨P, hPX, by rw [hPcard]; exact hr, by rw [hPcard]; exact hr2, ?_, ?_⟩
  ·
    intro c hc
    have hcP : A1b.conjSub c P ≤ X := by
      intro w hw
      rw [A1b.mem_conjSub_iff] at hw
      have hw' := hPX hw
      refine Subgroup.mem_inf.mpr ⟨by simpa [mul_assoc] using hLn.conj_mem _ hw'.1 c, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hw'.2
      calc w * x = c * (c⁻¹ * w * c * (c⁻¹ * x * c)) * c⁻¹ := by group
        _ = c * (c⁻¹ * w * c * x) * c⁻¹ := by
          rw [show c⁻¹ * x * c = x by
            calc c⁻¹ * x * c = c⁻¹ * (c * x) := by rw [hc]; group
              _ = x := by group]
        _ = c * (x * (c⁻¹ * w * c)) * c⁻¹ := by rw [h1]
        _ = x * w := by
          rw [show c * (x * (c⁻¹ * w * c)) * c⁻¹ = (c * x * c⁻¹) * w by group]
          rw [show c * x * c⁻¹ = x by rw [hc]; group]
    have hcard' : Nat.card (A1b.conjSub c P) = Nat.card P :=
      Nat.card_congr (P.equivMapOfInjective _ (MulAut.conj c).injective).toEquiv.symm
    have hsub : (A1b.conjSub c P).subgroupOf X = P.subgroupOf X := by
      refine eq_of_odd_of_mulEquiv d ?_ ?_
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcP).toEquiv, hcard', hPcard]
        exact hrodd
      · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcP).toEquiv,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPX).toEquiv, hcard']
    rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hcP, inf_eq_left.mpr hPX] at hsub
    rw [Subgroup.mem_normalizer_iff]
    intro w
    constructor
    · intro hw
      rw [← hsub]
      exact ⟨w, hw, rfl⟩
    · intro hw
      rw [← hsub, A1b.mem_conjSub_iff] at hw
      simpa [mul_assoc] using hw
  ·
    intro y hy hy2 hyx hPy
    have hy' : y ∈ C.map (embL e) := by
      have h1 : y ∈ X := hy
      rw [hXmap] at h1
      exact h1
    obtain ⟨s, hsC, rfl⟩ := hy'
    have hs2 : orderOf s = 2 := (orderOf_injective _ (embL_injective e) s).symm.trans hy2
    have hst : s ≠ t := fun h => hyx (by rw [h, htx])
    have hcomm : s * t = t * s := Subgroup.mem_centralizer_singleton_iff.mp hsC
    have hV := CFSG.ComponentClassification.UnbalancedGS.ReciprocalFusion.isKleinFour_closure_pair
      hs2 ht2 hcomm hst
    refine psl2_no_kleinFour_centralizes_odd_cyclic K ⟨p, f, Fact.out, hp, hf, hK⟩ A₀ _
      inferInstance (fun h => by simp [h] at hA₀card; exact hr.one_lt.ne hA₀card)
      (by rw [hA₀card]; exact hrodd) hV ?_
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro a ha
      apply embL_injective e
      have := Subgroup.mem_centralizer_singleton_iff.mp (hPy ⟨a, ha, rfl⟩)
      simpa [map_mul] using this
    · rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro a ha
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hA₀C ha))

end CFSG.Quasithin.RonanE114.L2
