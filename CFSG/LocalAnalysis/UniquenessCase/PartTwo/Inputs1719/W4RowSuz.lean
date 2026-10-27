module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowGen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1RowHalf
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps13AltContext
public import CFSG.Quasithin.Background.Asc81cPfQuot
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.Suz

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

namespace W4Row

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
theorem quoAct_injective_of_o2Trivial (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hO2 : O2Trivial L) : Function.Injective (Asc81c.Pf.quoAct L) := by
  set K : Subgroup (MulAut W) := (Asc81c.Pf.quoAct L).ker.map L.subtype with hK
  have hKL : K ≤ L := by
    rintro _ ⟨g, -, rfl⟩
    exact g.2
  have hKn : (K.subgroupOf L).Normal := by
    have hKL' : K.subgroupOf L = (Asc81c.Pf.quoAct L).ker :=
      Subgroup.comap_map_eq_self_of_injective L.subtype_injective _
    rw [hKL']
    exact MonoidHom.normal_ker _
  have hK2 : IsPGroup 2 K := by
    rintro ⟨_, g, hg, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    have h := Asc81c.Pf.mul_self_eq_one_of_quoAct hW (MonoidHom.mem_ker.1 hg)
    simpa [sq] using h
  have hbot := hO2 K hKL hKn hK2
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgK : (g : MulAut W) ∈ K := ⟨g, hg, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hgK
  exact Subtype.ext hgK

theorem two_pow_22_le_index_fixV_of_cover (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)}
    (hO2 : O2Trivial L) {S : Type} [Group S] (e : CQ L ≃* S)
    (hZ : Nat.card (center ↥L) = 1 ∨ Nat.card (center ↥L) = 3)
    {A : Subgroup S} (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAp : ∀ a ∈ A, a ^ 3 = 1)
    (hAcard : Nat.card A = 243) {g : S} (hgA : ∀ a ∈ A, g * a * g⁻¹ ∈ A) (hg11 : g ^ 11 = 1)
    (hgnc : ∃ a ∈ A, g * a * g⁻¹ ≠ a) : 2 ^ 22 ≤ (fixV L).index := by
  have hρ := quoAct_injective_of_o2Trivial hW hO2
  set L' : Subgroup (MulAut (W ⧸ fixV L)) := (Asc81c.Pf.quoAct L).range with hL'
  let φ : ↥L ≃* ↥L' := MonoidHom.ofInjective hρ
  have hcen : (center ↥L).map (φ : ↥L →* ↥L') = center ↥L' := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine Subgroup.mem_center_iff.2 fun z => ?_
      obtain ⟨z', rfl⟩ := φ.surjective z
      change φ z' * φ x = φ x * φ z'
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx z']
    · intro hy
      refine ⟨φ.symm y, Subgroup.mem_center_iff.2 fun z => ?_, φ.apply_symm_apply y⟩
      apply φ.injective
      rw [map_mul, map_mul, φ.apply_symm_apply, Subgroup.mem_center_iff.1 hy]
  let e' : CQ L' ≃* S := (QuotientGroup.congr (center ↥L) (center ↥L') φ hcen).symm.trans e
  have hZ' : Nat.card (center ↥L') = Nat.card (center ↥L) := by
    rw [← hcen]
    exact Subgroup.card_map_of_injective (f := (φ : ↥L →* ↥L')) φ.injective
  have hW' : ∀ w : W ⧸ fixV L, w * w = 1 := by
    intro w
    induction w using QuotientGroup.induction_on with
    | H w => rw [← QuotientGroup.mk_mul, ← sq, hW, QuotientGroup.mk_one]
  rw [← hZ'] at hZ
  exact CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.two_pow_22_le_card_of_cover hW' e'
    hZ hAc hAp hAcard hgA hg11 hgnc

theorem index_fixV_le_pow_of_actS_gen {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y)
    (hF : Fstar Y = L) (hperf : Group.IsPerfect ↥L)
    (hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W))) {S : Type} [Group S] (e : CQ L ≃* S)
    {b : MulAut W} (hbY : b ∈ Y) (cs : List S)
    (hgen : (MulAut.conj : S →* MulAut S).range ≤ Subgroup.closure
      {x : MulAut S | ∃ c ∈ cs, x = MulAut.conj c * actS hY e ⟨b, Subgroup.mem_sup_right hbY⟩ *
        (MulAut.conj c)⁻¹}) :
    (fixV L).index ≤ (fixV (Subgroup.zpowers b)).index ^ cs.length := by
  classical
  obtain ⟨ls, hls⟩ := (List.map_surjective_iff.2 (redHom_surjective L e)) cs
  have hlen : ls.length = cs.length := by rw [← hls, List.length_map]
  set bG : ↥(L ⊔ Y) := ⟨b, Subgroup.mem_sup_right hbY⟩ with hbG
  let cG : ↥L → ↥(L ⊔ Y) := fun l => ⟨(l : MulAut W), Subgroup.mem_sup_left l.2⟩
  have hcG : ∀ l, actS hY e (cG l) = MulAut.conj (redHom L e l) := fun l => actS_of_mem hY e l
  set K' : Subgroup ↥(L ⊔ Y) :=
    Subgroup.closure {x | ∃ l ∈ ls, x = cG l * bG * (cG l)⁻¹} with hK'
  have hρK : (MulAut.conj : S →* MulAut S).range ≤ K'.map (actS hY e) := by
    refine hgen.trans ?_
    rw [Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    rw [← hls] at hc
    obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hc
    refine ⟨cG l * bG * (cG l)⁻¹, Subgroup.subset_closure ⟨l, hl, rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_inv, hcG]
  have hcent : ∀ x : ↥(L ⊔ Y), actS hY e x = 1 →
      (x : MulAut W) ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
    intro x hx
    have h1 : actionOnCQ (le_sup_left : L ≤ L ⊔ Y) (normal_sup_of_le_normalizer hY) x = 1 := by
      rw [actS_apply] at hx
      exact (MulAut.congr e).injective (by rw [hx, map_one])
    exact (actionOnCQ_eq_one_iff (le_sup_left : L ≤ L ⊔ Y) (normal_sup_of_le_normalizer hY)
      hperf x).1 h1
  set J : Subgroup ↥L := (K'.map (L ⊔ Y).subtype).comap L.subtype with hJ
  have hJtop : J = ⊤ := by
    refine eq_top_of_sup_center_eq_top hperf (eq_top_iff.2 fun z _ => ?_)
    obtain ⟨x, hxK, hxs⟩ := hρK ⟨redHom L e z, rfl⟩
    have hxY : (x : MulAut W) ∈ Y := (sup_eq_right.2 hLY).le x.2
    have hxL : (x : MulAut W) ∈ L :=
      mem_of_actS_inner_of_fstar hLY hF hperf hY e hxY ⟨redHom L e z, hxs.symm⟩
    set xL : ↥L := ⟨x, hxL⟩ with hxL'
    have hxJ : xL ∈ J := ⟨x, hxK, rfl⟩
    have hc : z⁻¹ * xL ∈ center ↥L := by
      have hx' : actS hY e (cG xL) = MulAut.conj (redHom L e z) := hxs
      have h1 : actS hY e (cG (z⁻¹ * xL)) = 1 := by
        rw [hcG, map_mul, map_inv, map_mul, map_inv, ← hcG xL, hx', inv_mul_cancel]
      have h2 := hcent _ h1
      exact Subgroup.mem_center_iff.2 fun w =>
        Subtype.ext (Subgroup.mem_centralizer_iff.1 h2 w w.2)
    have hz : z = xL * (z⁻¹ * xL)⁻¹ := by group
    rw [hz]
    exact Subgroup.mul_mem_sup hxJ (Subgroup.inv_mem _ hc)
  set bs : List (MulAut W) := ls.map (fun c : ↥L => (c : MulAut W) * b * (c : MulAut W)⁻¹)
    with hbs
  have hLK : L ≤ Subgroup.closure {x : MulAut W | x ∈ bs} := by
    intro x hx
    have hxJ : (⟨x, hx⟩ : ↥L) ∈ J := by rw [hJtop]; trivial
    obtain ⟨z, hz, hzx⟩ := hxJ
    have hzx' : (z : MulAut W) = x := hzx
    rw [← hzx']
    have hmap : K'.map (L ⊔ Y).subtype ≤ Subgroup.closure {x : MulAut W | x ∈ bs} := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨t, ⟨l, hl, rfl⟩, rfl⟩
      exact Subgroup.subset_closure (List.mem_map.2 ⟨l, hl, rfl⟩)
    exact hmap ⟨z, hz, rfl⟩
  refine (Subgroup.index_antitone (X1.fixV_anti hLK)).trans
    ((X1.index_fixV_closure_le bs).trans ?_)
  have hrep : bs.map (fun x => (fixV (Subgroup.zpowers x)).index) =
      List.replicate cs.length (fixV (Subgroup.zpowers b)).index := by
    rw [hbs, List.map_map, ← hlen, List.map_eq_replicate_iff]
    intro x _
    exact X1.index_fixV_conj (x : MulAut W) b
  rw [hrep, List.prod_replicate]

end W4Row

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Setup.Family
open CFSG.Blueprint CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
  CFSG.Sporadic.SuzOddCore CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

theorem w4Thm11_1RowM_Suz_holds :
    W4Thm11_1RowM .Suz := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e⟩ := hs
  show 8 ≤ E3.mParam Y
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  have : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  have hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).1 hLn
  have hperf : Group.IsPerfect ↥L := hq.1
  set e₁ : CQ L ≃* ↥suzM := e.trans suzEquivM with he₁
  have hmult := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq e
  rw [nativeRow_Suz] at hmult
  have hZ : Nat.card (center ↥L) = 1 ∨ Nat.card (center ↥L) = 3 :=
    eq_one_or_three_of_odd_dvd_six'
      (CFSG.LocalAnalysis.WeakClosure81.GF2Reps13Alt.odd_card_center_of_o2Trivial hO2 le_rfl
        fun y hy l hl => L.mul_mem (L.mul_mem hy hl) (L.inv_mem hy))
      (hmult.trans (by decide))
  obtain ⟨A, g, hAc, hAp, hAcard, hgA, hg11, hgnc⟩ := suzAG_facts
  have h22 : 2 ^ 22 ≤ (fixV L).index :=
    W4Row.two_pow_22_le_index_fixV_of_cover hW hO2 e₁ hZ hAc hAp hAcard hgA hg11 hgnc
  have key : ∀ t ∈ Y, orderOf t = 2 → 8 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
    intro t htY hto
    have ht2 : t * t = 1 := by
      rw [← sq, ← hto]
      exact pow_orderOf_eq_one t
    set t' : ↥(L ⊔ Y) := ⟨t, Subgroup.mem_sup_right htY⟩ with ht'
    have hψ2 : actS hY e₁ t' * actS hY e₁ t' = 1 := by
      rw [← map_mul, show t' * t' = 1 from Subtype.ext ht2, map_one]
    have hψ1 : actS hY e₁ t' ≠ 1 := by
      intro h1
      have h2 : actionOnCQ (le_sup_left : L ≤ L ⊔ Y) (normal_sup_of_le_normalizer hY) t' = 1 := by
        rw [actS_apply] at h1
        exact (MulAut.congr e₁).injective (by rw [h1, map_one])
      have h3 := (actionOnCQ_eq_one_iff (le_sup_left : L ≤ L ⊔ Y)
        (normal_sup_of_le_normalizer hY) hperf t').1 h2
      have htL : t ∈ L := W4Row.mem_of_mem_centralizer_of_fstar_eq hLY hF htY h3
      apply W4Row.redHom_ne_one_of_o2Trivial hO2 e₁ htL hto
      rw [redHom_eq_one_iff]
      exact Subgroup.mem_center_iff.2 fun z =>
        Subtype.ext (Subgroup.mem_centralizer_iff.1 h3 z z.2)
    obtain ⟨cs, hcs, hgen⟩ := suzAut_gen _ hψ2 hψ1
    have h3 := W4Row.index_fixV_le_pow_of_actS_gen hLY hF hperf hY e₁ htY cs hgen
    rw [hcs] at h3
    obtain ⟨m, hm⟩ := index_fixV_eq_two_pow hW' (Subgroup.zpowers t)
    rw [hm, ← pow_mul] at h3
    have h4 : 22 ≤ m * 3 := (Nat.pow_le_pow_iff_right (by norm_num)).1 (h22.trans h3)
    rw [rkIdx, hm, padicValNat.prime_pow]
    omega
  unfold E3.mParam
  by_cases hEven : Even (Nat.card Y)
  · rw [if_pos hEven]
    refine le_csInf ?_ ?_
    · obtain ⟨t, hto⟩ :=
        exists_prime_orderOf_dvd_card' (G := ↥Y) 2 (even_iff_two_dvd.1 hEven)
      exact ⟨_, (t : MulAut W), t.2, by rwa [Subgroup.orderOf_coe], rfl⟩
    · rintro n ⟨t, htY, hto, rfl⟩
      exact key t htY hto
  · rw [if_neg hEven]
    have hcard : Nat.card W = 2 ^ rk W :=
      card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hW)
    have h := h22.trans (index_fixV_le_card L)
    rw [hcard] at h
    have := (Nat.pow_le_pow_iff_right (by norm_num)).1 h
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
