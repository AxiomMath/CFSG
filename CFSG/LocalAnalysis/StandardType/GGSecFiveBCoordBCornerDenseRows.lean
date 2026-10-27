module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBDenseDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpPlaneFrameDefs
import CFSG.ClassicalGroups.Symplectic.ComponentCartanRank
import CFSG.LocalAnalysis.StandardType.GGRowKFrame
import CFSG.LocalAnalysis.StandardType.GGSecFiveBCoordBCornerSign
import CFSG.LocalAnalysis.StandardType.GGSignedCoordFix
import CFSG.LocalAnalysis.StandardType.GGSignedCoordRefl
import CFSG.ClassicalGroups.Symplectic.DiagonalTorusRank
import CFSG.SignalizerFunctorTheorem.NonLocal.Cross
import CFSG.SignalizerFunctorTheorem.NonLocal.SpData

public section

namespace CFSG.StandardType

open CFSG.Open GGQ2Frame

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

theorem GGSecFiveBCoordBDenseNbr.eq_one_of_apply_eq_one [Finite G] {p : ℕ} {Bs : Subgroup G}
    {𝒦 : Finset (Subgroup G)} {n : ℕ} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {K : Subgroup G} (hK : GGSecFiveBCoordBDenseNbr p Bs 𝒦 n eta K) {y : G} (hy : y ∈ Bs)
    (hKy : K ≤ Subgroup.centralizer ({y} : Set G)) {i : Fin n} (hi : eta ⟨y, hy⟩ i = 1) :
    y = 1 := by
  obtain ⟨-, δ, hδ, hAK⟩ := hK
  have hfix : ∀ u ∈ (aPermutationFull n p).map (MulAut.conj δ).toMonoidHom,
      u (eta ⟨y, hy⟩) = eta ⟨y, hy⟩ := by
    intro u hu
    rw [← hAK] at hu
    obtain ⟨ψ, hψ, rfl⟩ := Subgroup.mem_map.mp hu
    change eta (ψ (eta.symm (eta ⟨y, hy⟩))) = eta ⟨y, hy⟩
    rw [MulEquiv.symm_apply_apply, ggRC_automizer_fixes_y hy hKy ψ hψ]
  obtain ⟨c, hc⟩ := exists_const_of_forall_map_conj_aPermutationFull_fix δ hfix
  rw [bSignedFull_eq_signedPermSubgroup] at hδ
  obtain ⟨π, ε, hε, hπ⟩ := (hδ : SpCoord.IsSignedPerm ⇑δ)
  have hcoord : ∀ j, Multiplicative.toAdd (eta ⟨y, hy⟩ (π j)) = ε j * c := by
    intro j
    rw [hc, hπ]
    rfl
  have hc0 : c = 0 := by
    have hunit : IsUnit (ε (π.symm i)) := by
      rcases hε (π.symm i) with h | h <;> rw [h]
      · exact isUnit_one
      · exact isUnit_one.neg
    have h := hcoord (π.symm i)
    rw [Equiv.apply_symm_apply, hi, toAdd_one] at h
    exact hunit.mul_right_eq_zero.mp h.symm
  have hall : eta ⟨y, hy⟩ = 1 := by
    funext j
    obtain ⟨j', rfl⟩ := π.surjective j
    apply Multiplicative.toAdd.injective
    rw [hcoord, hc0, mul_zero]
    rfl
  have h1 : (⟨y, hy⟩ : ↥Bs) = 1 := eta.injective (by rw [hall, map_one])
  simpa using congrArg Subtype.val h1

private theorem eta_apply_eq_one_of_coord_eq_zero {Bs L : Subgroup G} {n r : ℕ}
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic r))
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {ι : Fin r → Fin n}
    (hι : Function.Injective ι)
    (hframe : ∀ (a : ↥(Bs.subgroupOf L)) (k : Fin r) (s : ZMod 3),
      (R.coord (Additive.ofMul a) : PlaneRaw.V r) = Pi.single k s →
      ∃ t : ZMod 3, (s ≠ 0 → t ≠ 0) ∧
        eta ⟨((a : ↥L) : G), Subgroup.mem_subgroupOf.mp a.2⟩ =
          Pi.mulSingle (ι k) (Multiplicative.ofAdd t))
    (a : ↥(Bs.subgroupOf L)) {k : Fin r}
    (hk : (R.coord (Additive.ofMul a) : PlaneRaw.V r) k = 0) :
    eta ⟨((a : ↥L) : G), Subgroup.mem_subgroupOf.mp a.2⟩ (ι k) = 1 := by
  classical
  let T : Subgroup ↥(Bs.subgroupOf L) :=
    ((ggBsCoordZero Bs eta (ι k)).subgroupOf L).subgroupOf (Bs.subgroupOf L)
  have hT : ∀ b : ↥(Bs.subgroupOf L), b ∈ T ↔
      eta ⟨((b : ↥L) : G), Subgroup.mem_subgroupOf.mp b.2⟩ (ι k) = 1 := by
    intro b
    simp only [T, Subgroup.mem_subgroupOf, mem_ggBsCoordZero]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨_, h⟩⟩
  let S := (Subgroup.toAddSubgroup T).comap R.coord.symm.toAddMonoidHom
  have hS : ∀ b : ↥(Bs.subgroupOf L), R.coord (Additive.ofMul b) ∈ S ↔ b ∈ T := by
    intro b
    change Additive.toMul (R.coord.symm (R.coord (Additive.ofMul b))) ∈ T ↔ b ∈ T
    rw [AddEquiv.symm_apply_apply, toMul_ofMul]
  have hsingle : ∀ m, m ≠ k → ∀ s : ZMod 3, (Pi.single m s : PlaneRaw.V r) ∈ S := by
    intro m hm s
    obtain ⟨b, hb⟩ : ∃ b : ↥(Bs.subgroupOf L),
        (R.coord (Additive.ofMul b) : PlaneRaw.V r) = Pi.single m s :=
      ⟨Additive.toMul (R.coord.symm (Pi.single m s : PlaneRaw.V r)), by
        rw [ofMul_toMul]
        exact R.coord.apply_symm_apply _⟩
    obtain ⟨t, -, ht⟩ := hframe b m s hb
    have h := (hS b).mpr ((hT b).mpr (by
      rw [ht]
      exact Pi.mulSingle_eq_of_ne (hι.ne (Ne.symm hm)) _))
    rw [hb] at h
    exact h
  have hv : R.coord (Additive.ofMul a) ∈ S := by
    rw [← Finset.univ_sum_single (R.coord (Additive.ofMul a) : PlaneRaw.V r)]
    refine AddSubgroup.sum_mem S fun m _ => ?_
    by_cases hm : m = k
    · rw [hm, hk, Pi.single_zero]
      exact S.zero_mem
    · exact hsingle m hm _
  exact (hT a).mp ((hS a).mp hv)

private theorem exists_zpow_eq_of_mem_centralizer {Bs L : Subgroup G} {x c : G} {n : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    (hxBs : x ∈ Bs) (hx1 : x ≠ 1) (hxL : x ∈ Subgroup.centralizer (L : Set G))
    (hcBs : c ∈ Bs) (hcL : c ∈ Subgroup.centralizer (L : Set G)) : ∃ k : ℤ, x ^ k = c := by
  have hxax := eta_eq_mulSingle_of_mem_centralizer eta hb (b := ⟨x, hxBs⟩) hxL
  have hcax := eta_eq_mulSingle_of_mem_centralizer eta hb (b := ⟨c, hcBs⟩) hcL
  have hx0 : eta ⟨x, hxBs⟩ i0 ≠ 1 := by
    intro h
    apply hx1
    have h' : eta ⟨x, hxBs⟩ = eta 1 := by rw [hxax, h, Pi.mulSingle_one, map_one]
    simpa using congrArg Subtype.val (eta.injective h')
  have hcard : Nat.card (Multiplicative (ZMod 3)) = 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card]
  have hmem : eta ⟨c, hcBs⟩ i0 ∈ Subgroup.zpowers (eta ⟨x, hxBs⟩ i0) := by
    rw [zpowers_eq_top_of_prime_card (p := 3) hcard hx0]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ : ∃ k : ℤ, eta ⟨x, hxBs⟩ i0 ^ k = eta ⟨c, hcBs⟩ i0 :=
    Subgroup.mem_zpowers_iff.mp hmem
  refine ⟨k, ?_⟩
  have h' : eta (⟨x, hxBs⟩ ^ k) = eta ⟨c, hcBs⟩ := by
    rw [map_zpow, hxax, hcax, ← hk]
    funext j
    by_cases hj : j = i0
    · subst hj
      simp
    · simp [Pi.mulSingle_eq_of_ne hj]
  simpa using congrArg Subtype.val (eta.injective h')

theorem GGConfig.cornerSplit_of_planeFrame [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hC : GGConfig 3 B Bs x L D J) {n r : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    {π : Fin (r + 2) ≃ Fin n} {κ : StatedSp (r + 1) (GaloisField 2 1) →* G}
    {ζ : Multiplicative (ZMod 3) →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1)}
    (hF : GGSecFiveBPermSpPlaneFrame Bs L eta π κ ζ) :
    Subgroup.zpowers x ⊓ L = ⊥ ∧ ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k := by
  obtain ⟨-, hxB, hx1, hcomp, -⟩ := hC.1.2.2.2.2.2.2.1
  obtain ⟨hκ, hκL, -, hact⟩ := hF
  have hxBs : x ∈ Bs := hC.2.1.1 hxB
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact ((Subgroup.mem_centralizer_iff.mp (hcomp.1 hl)) x (Set.mem_singleton x)).symm
  have hZ : Subgroup.center ↥L = ⊥ := by
    let ψ : StatedSp (r + 1) (GaloisField 2 1) →* ↥L :=
      κ.codRestrict L fun g => hκL ▸ (κ.mem_range).2 ⟨g, rfl⟩
    have hψ : Function.Bijective ψ := by
      refine ⟨fun a b hab => hκ (by simpa [ψ] using congrArg Subtype.val hab), fun y => ?_⟩
      have hy : (y : G) ∈ κ.range := by rw [hκL]; exact y.2
      obtain ⟨g, hg⟩ := (κ.mem_range).1 hy
      exact ⟨g, Subtype.ext hg⟩
    have h := Subgroup.map_center_eq (MulEquiv.ofBijective ψ hψ)
    rw [CFSG.ClassicalGroups.Symplectic.center_statedSp_eq_bot_of_charP_two (m := r + 1)
      (by omega), Subgroup.map_bot] at h
    exact h.symm
  refine ⟨?_, ?_⟩
  · rw [inf_comm, eq_bot_iff]
    rintro y ⟨hyL, hyx⟩
    rw [Subgroup.mem_bot]
    have hyc : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply Subtype.ext
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hyx
      have hcomm : Commute x (l : G) :=
        (Subgroup.mem_centralizer_iff.mp hxL (l : G) l.2).symm
      have hyl : y * (l : G) = (l : G) * y := by
        rw [← hk]
        exact (hcomm.zpow_left k).eq
      simpa using hyl.symm
    rw [hZ] at hyc
    simpa using congrArg Subtype.val (Subgroup.mem_bot.mp hyc)
  · intro b hbBs
    have hcomm : ∀ v w : Fin (r + 1) → Multiplicative (ZMod 3),
        SpJoin.spPlaneTorus (r + 1) ζ v * SpJoin.spPlaneTorus (r + 1) ζ w *
          (SpJoin.spPlaneTorus (r + 1) ζ v)⁻¹ = SpJoin.spPlaneTorus (r + 1) ζ w := by
      intro v w
      rw [← map_mul, mul_comm v w, map_mul, mul_inv_cancel_right]
    obtain ⟨v, hv⟩ : ∃ v : Fin (r + 1) → Multiplicative (ZMod 3),
        v = fun m => eta ⟨b, hbBs⟩ (π m.succ) := ⟨_, rfl⟩
    have haL : κ (SpJoin.spPlaneTorus (r + 1) ζ v) ∈ L := by
      rw [← hκL]
      exact (κ.mem_range).2 ⟨_, rfl⟩
    have hacent : κ (SpJoin.spPlaneTorus (r + 1) ζ v) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hconj := hact ⟨h, hh⟩ (SpJoin.spPlaneTorus (r + 1) ζ v)
      change h * _ * h⁻¹ = _ at hconj
      rw [hcomm] at hconj
      calc h * κ (SpJoin.spPlaneTorus (r + 1) ζ v)
          = h * κ (SpJoin.spPlaneTorus (r + 1) ζ v) * h⁻¹ * h := by group
        _ = κ (SpJoin.spPlaneTorus (r + 1) ζ v) * h := by rw [hconj]
    have h3 : ∀ w : Multiplicative (ZMod 3), w ^ 3 = 1 := fun w => by
      have h := pow_card_eq_one' (x := w)
      rwa [Nat.card_eq_fintype_card, Fintype.card_multiplicative, ZMod.card] at h
    have ha3 : κ (SpJoin.spPlaneTorus (r + 1) ζ v) ^ 3 = 1 := by
      have hv3 : v ^ 3 = 1 := funext fun m => h3 (v m)
      rw [← map_pow, ← map_pow, hv3, map_one, map_one]
    have haBs : κ (SpJoin.spPlaneTorus (r + 1) ζ v) ∈ Bs := hC.2.1.2.2.2 _ hacent ha3
    have hcL : (κ (SpJoin.spPlaneTorus (r + 1) ζ v))⁻¹ * b ∈
        Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' : l ∈ κ.range := by rw [hκL]; exact hl
      obtain ⟨s, rfl⟩ := (κ.mem_range).1 hl'
      have h1 := hact ⟨b, hbBs⟩ s
      change b * κ s * b⁻¹ = _ at h1
      rw [← hv, map_mul, map_mul, map_inv] at h1
      calc κ s * ((κ (SpJoin.spPlaneTorus (r + 1) ζ v))⁻¹ * b)
          = (κ (SpJoin.spPlaneTorus (r + 1) ζ v))⁻¹ * (κ (SpJoin.spPlaneTorus (r + 1) ζ v) *
              κ s * (κ (SpJoin.spPlaneTorus (r + 1) ζ v))⁻¹) * b := by group
        _ = (κ (SpJoin.spPlaneTorus (r + 1) ζ v))⁻¹ * (b * κ s * b⁻¹) * b := by rw [h1]
        _ = (κ (SpJoin.spPlaneTorus (r + 1) ζ v))⁻¹ * b * κ s := by group
    obtain ⟨k, hk⟩ := exists_zpow_eq_of_mem_centralizer eta hb hxBs hx1 hxL
      (Bs.mul_mem (Bs.inv_mem haBs) hbBs) hcL
    exact ⟨_, ⟨haBs, haL⟩, k, by rw [hk, mul_inv_cancel_left]⟩

theorem GGSecFiveRouteCfg.not_denseNbr_of_cornerCoord_eq_zero [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {n : ℕ} (hn : 4 ≤ n)
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))) {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    (hxL' : Subgroup.zpowers x ⊓ L = ⊥)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k)
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1)))
    (z : ↥(Bs.subgroupOf L)) (hD : D = Subgroup.zpowers x ⊔ Subgroup.zpowers ((z : ↥L) : G))
    {k : Fin (n - 1)} (hk : (R.coord (Additive.ofMul z) : PlaneRaw.V (n - 1)) k = 0)
    {K : Subgroup G} (hK : GGSecFiveBCoordBDenseNbr 3 Bs 𝒦 n eta K) : False := by
  obtain ⟨-, hxB, -, hcomp, -⟩ := hR.1.1.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hR.1.1.2.1.1 hxB
  have hxL : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact ((Subgroup.mem_centralizer_iff.mp (hcomp.1 hl)) x (Set.mem_singleton x)).symm
  obtain ⟨ι, hι, hιne, -, hframe, -⟩ :=
    exists_eta_frame_of_realization hn hR.1.1.2.1.2.1 hxBs hxL hxL' hsplit R eta hb
  have hxj : x ∈ ggBsCoordZero Bs eta (ι k) := by
    refine mem_ggBsCoordZero.mpr ⟨hxBs, ?_⟩
    rw [eta_eq_mulSingle_of_mem_centralizer eta hb (b := ⟨x, hxBs⟩) hxL]
    exact Pi.mulSingle_eq_of_ne (hιne k) _
  have hzj : ((z : ↥L) : G) ∈ ggBsCoordZero Bs eta (ι k) :=
    mem_ggBsCoordZero.mpr ⟨_, eta_apply_eq_one_of_coord_eq_zero R eta hι hframe z hk⟩
  obtain ⟨y, hnb⟩ := hR.2.2.2.1.2 K hK.1
  have hyD : y ∈ D := by
    rw [hnb.2.1]
    exact Subgroup.subset_closure (by simp)
  have hDle : D ≤ ggBsCoordZero Bs eta (ι k) := by
    rw [hD]
    exact sup_le (Subgroup.zpowers_le.mpr hxj) (Subgroup.zpowers_le.mpr hzj)
  obtain ⟨hyBs, hyj⟩ := mem_ggBsCoordZero.mp (hDle hyD)
  exact hnb.1.2.2.1 (hK.eq_one_of_apply_eq_one hyBs hnb.1.2.2.2.1 hyj)

theorem GGSecFiveRouteCfg.cornerRowRest_rowThree_of_denseNbr [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hR : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦) {n : ℕ} (hn : 4 ≤ n)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod 3))} {i0 : Fin n}
    (hb : (ggAutomizer L Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n 3 i0)
    (hxL' : Subgroup.zpowers x ⊓ L = ⊥)
    (hsplit : ∀ b ∈ Bs, ∃ a ∈ Bs ⊓ L, ∃ k : ℤ, b = a * x ^ k)
    (R : Realization (⊤ : Subgroup ↥L) (Bs.subgroupOf L) (planeEntry .symplectic (n - 1)))
    (z : ↥(Bs.subgroupOf L)) {c : PlaneRaw.Code (n - 1)}
    (hD : D = Subgroup.zpowers x ⊔ Subgroup.zpowers ((z : ↥L) : G))
    (hrow : PlaneRaw.CornerRowRest (ggLinImage (p := 3) R.coord (B.subgroupOf L))
      (R.coord (Additive.ofMul z)) c)
    {K : Subgroup G} (hK : GGSecFiveBCoordBDenseNbr 3 Bs 𝒦 n eta K) :
    ∃ k l, k ≠ l ∧ ∃ s : PlaneRaw.F, s ≠ 0 ∧
      (∀ v, v ∈ ggLinImage (p := 3) R.coord (B.subgroupOf L) ↔ v k = s * v l) ∧
      (∀ i, (R.coord (Additive.ofMul z) : PlaneRaw.V (n - 1)) i ≠ 0) ∧
      (c = .extension (R.coord (Additive.ofMul z)) ∨
        c = .extension (-(R.coord (Additive.ofMul z) : PlaneRaw.V (n - 1)))) ∧
      5 ≤ n - 1 := by
  rcases hrow with ⟨k, l, -, -, -, -, hu, -, h5⟩ | h3 | ⟨k, -, hu, -, -⟩
  · exfalso
    obtain ⟨m, hm⟩ : ∃ m : Fin (n - 1), m ∉ ({k, l} : Finset (Fin (n - 1))) := by
      by_contra h
      push Not at h
      have hle := Finset.card_le_card (fun m (_ : m ∈ Finset.univ) => h m)
      rw [Finset.card_univ, Fintype.card_fin] at hle
      have h2 := Finset.card_le_two (a := k) (b := l)
      omega
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    have hm0 : (R.coord (Additive.ofMul z) : PlaneRaw.V (n - 1)) m = 0 := by
      by_contra h
      rcases (hu m).mp h with h' | h'
      · exact hm.1 h'
      · exact hm.2 h'
    exact hR.not_denseNbr_of_cornerCoord_eq_zero hn eta hb hxL' hsplit R z hD hm0 hK
  · exact h3
  · exact (hR.not_denseNbr_of_cornerCoord_eq_zero hn eta hb hxL' hsplit R z hD
      ((hu k).mpr rfl) hK).elim

end CFSG.StandardType

end
