module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmFrame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentFrame

public section

namespace CFSG.StandardType.SevOm

open Module Multiplicative CFSG.LocalAnalysis.GLTheoremA.S172C.Cent CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal

section Prod

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {p k : ℕ} {U : Fin k → Submodule K V} {e : Fin k → ↥(orthDerived Q)}
  {Bb : Subgroup ↥(orthDerived Q)}

private theorem p9Frame_mem {E : Subgroup (V ≃ₗ[K] V)}
    (hF : IsPlaneFrame Q p U e (E.subgroupOf (orthDerived Q))) (j : Fin k) :
    (e j : V ≃ₗ[K] V) ∈ E := by
  have h : e j ∈ E.subgroupOf (orthDerived Q) := by
    rw [← hF.closure_eq]
    exact Subgroup.subset_closure (Set.mem_range_self j)
  exact Subgroup.mem_subgroupOf.mp h

private theorem p9Frame_commute {E : Subgroup (V ≃ₗ[K] V)} (hEΩ : E ≤ orthDerived Q)
    (hF : IsPlaneFrame Q p U e (E.subgroupOf (orthDerived Q))) {a b : V ≃ₗ[K] V} (ha : a ∈ E)
    (hb : b ∈ E) : Commute a b :=
  congrArg (fun z : E.subgroupOf (orthDerived Q) => ((z : orthDerived Q) : V ≃ₗ[K] V))
    (hF.isElemAbelian.1.is_comm.comm ⟨⟨a, hEΩ ha⟩, Subgroup.mem_subgroupOf.mpr ha⟩
      ⟨⟨b, hEΩ hb⟩, Subgroup.mem_subgroupOf.mpr hb⟩)

private theorem p9Frame_pow_eq_one (hF : IsPlaneFrame Q p U e Bb) (j : Fin k) :
    (e j : V ≃ₗ[K] V) ^ p = 1 := by
  have h := pow_orderOf_eq_one (e j)
  rw [hF.orderOf_eq j] at h
  simpa using congrArg Subtype.val h

private theorem p9Frame_pairwise (e : Fin k → ↥(orthDerived Q))
    (hc : ∀ i j, Commute (e i : V ≃ₗ[K] V) (e j : V ≃ₗ[K] V)) (s : Fin k → ZMod p) :
    ((Finset.univ : Finset (Fin k)) : Set (Fin k)).Pairwise
      (Function.onFun Commute fun j => (e j : V ≃ₗ[K] V) ^ (s j).val) :=
  fun i _ j _ _ => (hc i j).pow_pow _ _

private noncomputable def p9Frame_prod (e : Fin k → ↥(orthDerived Q))
    (hc : ∀ i j, Commute (e i : V ≃ₗ[K] V) (e j : V ≃ₗ[K] V)) (s : Fin k → ZMod p) :
    V ≃ₗ[K] V :=
  Finset.univ.noncommProd (fun j => (e j : V ≃ₗ[K] V) ^ (s j).val) (p9Frame_pairwise e hc s)

private theorem p9Frame_prod_add (hp : p.Prime) (hF : IsPlaneFrame Q p U e Bb)
    (hc : ∀ i j, Commute (e i : V ≃ₗ[K] V) (e j : V ≃ₗ[K] V)) (s t : Fin k → ZMod p) :
    p9Frame_prod e hc (s + t) = p9Frame_prod e hc s * p9Frame_prod e hc t := by
  have : NeZero p := ⟨hp.ne_zero⟩
  unfold p9Frame_prod
  rw [← Finset.noncommProd_mul_distrib]
  · refine Finset.noncommProd_congr rfl (fun j _ => ?_) _
    simp only [Pi.add_apply, Pi.mul_apply]
    rw [ZMod.val_add, ← pow_eq_pow_mod _ (p9Frame_pow_eq_one hF j), pow_add]
  · exact fun i _ j _ _ => (hc i j).pow_pow _ _

private theorem p9Frame_pow_apply_of_perp (hF : IsPlaneFrame Q p U e Bb) (i : Fin k) (n : ℕ)
    {x : V} (hx : x ∈ polarPerp Q (U i)) : ((e i : V ≃ₗ[K] V) ^ n) x = x := by
  induction n with
  | zero => rw [pow_zero, LinearEquiv.coe_one, id_eq]
  | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, hF.apply_of_perp i x hx, ih]

private theorem p9Frame_pow_mem (hF : IsPlaneFrame Q p U e Bb) (j : Fin k) (n : ℕ) {x : V}
    (hx : x ∈ U j) : ((e j : V ≃ₗ[K] V) ^ n) x ∈ U j := by
  induction n with
  | zero =>
    rw [pow_zero, LinearEquiv.coe_one, id_eq]
    exact hx
  | succ n ih =>
    rw [pow_succ', LinearEquiv.mul_apply]
    exact hF.maps_to j _ ih

private theorem p9Frame_prod_apply_of_mem (hF : IsPlaneFrame Q p U e Bb)
    (hc : ∀ i j, Commute (e i : V ≃ₗ[K] V) (e j : V ≃ₗ[K] V)) (s : Fin k → ZMod p) (j : Fin k)
    {x : V} (hx : x ∈ U j) : p9Frame_prod e hc s x = ((e j : V ≃ₗ[K] V) ^ (s j).val) x := by
  unfold p9Frame_prod
  rw [← Finset.noncommProd_erase_mul _ (Finset.mem_univ j), LinearEquiv.mul_apply]
  refine Finset.noncommProd_induction _ _ _ (fun g : V ≃ₗ[K] V => ∀ y ∈ U j, g y = y)
    (fun a b ha hb y hy => ?_) (fun _ _ => rfl) (fun i hi y hy => ?_) _
    (p9Frame_pow_mem hF j _ hx)
  · rw [LinearEquiv.mul_apply, hb y hy, ha y hy]
  · exact p9Frame_pow_apply_of_perp hF i _ (mem_polarPerp_iff.2 fun z hz =>
      hF.perp i j (Finset.ne_of_mem_erase hi) z hz y hy)

private theorem p9Frame_prod_apply_of_perp (hF : IsPlaneFrame Q p U e Bb)
    (hc : ∀ i j, Commute (e i : V ≃ₗ[K] V) (e j : V ≃ₗ[K] V)) (s : Fin k → ZMod p) {v : V}
    (hv : ∀ j, s j ≠ 0 → v ∈ polarPerp Q (U j)) : p9Frame_prod e hc s v = v := by
  unfold p9Frame_prod
  refine Finset.noncommProd_induction _ _ _ (fun g : V ≃ₗ[K] V => g v = v)
    (fun a b (ha : a v = v) (hb : b v = v) => ?_) rfl (fun j _ => ?_)
  · rw [LinearEquiv.mul_apply, hb, ha]
  · by_cases hs : s j = 0
    · rw [hs, ZMod.val_zero, pow_zero, LinearEquiv.coe_one, id_eq]
    · exact p9Frame_pow_apply_of_perp hF j _ (hv j hs)

private noncomputable def p9Frame_iota (hp : p.Prime) (hF : IsPlaneFrame Q p U e Bb)
    (hc : ∀ i j, Commute (e i : V ≃ₗ[K] V) (e j : V ≃ₗ[K] V)) :
    Multiplicative (Fin k → ZMod p) →* (V ≃ₗ[K] V) where
  toFun s := p9Frame_prod e hc (toAdd s)
  map_one' := by
    unfold p9Frame_prod
    refine (Finset.noncommProd_eq_pow_card _ _ _ 1 fun j _ => ?_).trans (one_pow _)
    simp
  map_mul' s t := p9Frame_prod_add hp hF hc (toAdd s) (toAdd t)

private theorem p9Frame_iota_apply (hp : p.Prime) (hF : IsPlaneFrame Q p U e Bb)
    (hc : ∀ i j, Commute (e i : V ≃ₗ[K] V) (e j : V ≃ₗ[K] V))
    (s : Multiplicative (Fin k → ZMod p)) :
    p9Frame_iota hp hF hc s = p9Frame_prod e hc (toAdd s) :=
  rfl

private theorem p9Frame_iota_single (hp : p.Prime) (hF : IsPlaneFrame Q p U e Bb)
    (hc : ∀ i j, Commute (e i : V ≃ₗ[K] V) (e j : V ≃ₗ[K] V)) (j : Fin k) :
    p9Frame_iota hp hF hc (ofAdd (Pi.single j 1)) = e j := by
  have : Fact (1 < p) := ⟨hp.one_lt⟩
  have h1 : ∀ i ∈ Finset.univ.erase j,
      (e i : V ≃ₗ[K] V) ^ (toAdd (ofAdd (Pi.single j 1 : Fin k → ZMod p)) i).val = 1 :=
    fun i hi => by simp [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hi)]
  rw [p9Frame_iota_apply]
  unfold p9Frame_prod
  rw [← Finset.noncommProd_erase_mul _ (Finset.mem_univ j)]
  refine (congrArg (· * _) ((Finset.noncommProd_eq_pow_card _ _ _ 1 h1).trans
    (one_pow _))).trans ?_
  simp [ZMod.val_one]

private theorem p9Frame_ne_bot (hF : IsPlaneFrame Q p U e Bb) (j : Fin k) : U j ≠ ⊥ := by
  intro h
  have h2 := hF.finrank_eq j
  rw [h, finrank_bot] at h2
  exact absurd h2 (by norm_num)

private theorem p9Frame_range (hp : p.Prime) {E : Subgroup (V ≃ₗ[K] V)}
    (hEΩ : E ≤ orthDerived Q) (hF : IsPlaneFrame Q p U e (E.subgroupOf (orthDerived Q)))
    (hc : ∀ i j, Commute (e i : V ≃ₗ[K] V) (e j : V ≃ₗ[K] V)) :
    (p9Frame_iota hp hF hc).range = E := by
  refine le_antisymm (fun d hd => ?_) fun d hd => ?_
  · obtain ⟨s, rfl⟩ := MonoidHom.mem_range.1 hd
    rw [p9Frame_iota_apply]
    unfold p9Frame_prod
    exact Subgroup.noncommProd_mem _ _ fun j _ => pow_mem (p9Frame_mem hF j) _
  · have key : ∀ x ∈ Subgroup.closure (Set.range e),
        (x : V ≃ₗ[K] V) ∈ (p9Frame_iota hp hF hc).range := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨j, rfl⟩ := hx
        exact MonoidHom.mem_range.2 ⟨_, p9Frame_iota_single hp hF hc j⟩
      | one => exact one_mem _
      | mul x y _ _ hx hy =>
        rw [Subgroup.coe_mul]
        exact mul_mem hx hy
      | inv x _ hx =>
        rw [Subgroup.coe_inv]
        exact inv_mem hx
    refine key ⟨d, hEΩ hd⟩ ?_
    rw [hF.closure_eq]
    exact Subgroup.mem_subgroupOf.mpr hd

end Prod

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p k : ℕ} {U : Fin k → Submodule K V}
  {e : Fin k → ↥(orthDerived Q)} {Bb : Subgroup ↥(orthDerived Q)}

private theorem p9Frame_pow_eq_zero (hp : p.Prime) (hF : IsPlaneFrame Q p U e Bb) (j : Fin k)
    {n : ℕ} (hn : ¬ p ∣ n) {x : V} (hx : x ∈ U j) (hfix : ((e j : V ≃ₗ[K] V) ^ n) x = x) :
    x = 0 := by
  have hord : orderOf (e j : V ≃ₗ[K] V) = p := by rw [Subgroup.orderOf_coe, hF.orderOf_eq j]
  have hne : (e j : V ≃ₗ[K] V) ^ n ≠ 1 := fun h => hn (hord ▸ orderOf_dvd_of_pow_eq_one h)
  have hx' : x ∈ fixedSpace ((e j : V ≃ₗ[K] V) ^ n) := mem_fixedSpace.2 hfix
  rw [fixedSpace_eq_of_mem_zpowers hp hord (Subgroup.npow_mem_zpowers _ n) hne] at hx'
  exact hF.eq_zero_of_apply_eq j x hx (mem_fixedSpace.1 hx')

private theorem p9Frame_prod_eq_zero (hp : p.Prime) (hF : IsPlaneFrame Q p U e Bb)
    (hc : ∀ i j, Commute (e i : V ≃ₗ[K] V) (e j : V ≃ₗ[K] V)) (s : Fin k → ZMod p) (j : Fin k)
    (hs : s j ≠ 0) {x : V} (hx : x ∈ U j) (hfix : p9Frame_prod e hc s x = x) : x = 0 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hn : ¬ p ∣ (s j).val := fun h =>
    hs ((ZMod.val_eq_zero (s j)).1 (Nat.eq_zero_of_dvd_of_lt h (ZMod.val_lt (s j))))
  exact p9Frame_pow_eq_zero hp hF j hn hx
    ((p9Frame_prod_apply_of_mem hF hc s j hx).symm.trans hfix)

private theorem p9Frame_mem_polarPerp (hp : p.Prime) (hF : IsPlaneFrame Q p U e Bb)
    (hc : ∀ i j, Commute (e i : V ≃ₗ[K] V) (e j : V ≃ₗ[K] V)) (s : Fin k → ZMod p) {v : V}
    (hv : p9Frame_prod e hc s v = v) (j : Fin k) (hs : s j ≠ 0) : v ∈ polarPerp Q (U j) := by
  have hcompl := isCompl_polarPerp (hF.nondeg j)
  have hv' : v ∈ U j ⊔ polarPerp Q (U j) := by
    rw [hcompl.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hv'
  have hda : p9Frame_prod e hc s a ∈ U j := by
    rw [p9Frame_prod_apply_of_mem hF hc s j ha]
    exact p9Frame_pow_mem hF j _ ha
  have hdb : p9Frame_prod e hc s b ∈ polarPerp Q (U j) := by
    have hcomm : Commute (e j : V ≃ₗ[K] V) (p9Frame_prod e hc s) :=
      Finset.noncommProd_commute _ _ _ _ fun i _ => (hc j i).pow_right _
    have hb' := hb
    rw [← hF.fixedSpace_eq_polarPerp j, mem_fixedSpace] at hb' ⊢
    rw [← LinearEquiv.mul_apply, hcomm.eq, LinearEquiv.mul_apply, hb']
  have hab : p9Frame_prod e hc s a - a = b - p9Frame_prod e hc s b := by
    rw [sub_eq_sub_iff_add_eq_add, ← map_add, hv, add_comm]
  have h0 : p9Frame_prod e hc s a - a = 0 :=
    (Submodule.disjoint_def.1 hcompl.disjoint) _ (sub_mem hda ha) (hab ▸ sub_mem hb hdb)
  rw [p9Frame_prod_eq_zero hp hF hc s j hs ha (sub_eq_zero.1 h0), zero_add]
  exact hb

private theorem p9Frame_injective (hp : p.Prime) (hF : IsPlaneFrame Q p U e Bb)
    (hc : ∀ i j, Commute (e i : V ≃ₗ[K] V) (e j : V ≃ₗ[K] V)) :
    Function.Injective (p9Frame_iota hp hF hc) := by
  refine (injective_iff_map_eq_one _).2 fun s hs => ?_
  have h0 : ∀ j, toAdd s j = 0 := fun j => by
    by_contra hne
    obtain ⟨x, hxU, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (p9Frame_ne_bot hF j)
    exact hx0 (p9Frame_prod_eq_zero hp hF hc _ j hne hxU
      (congrArg (fun g : V ≃ₗ[K] V => g x) hs))
  have h0' : toAdd s = 0 := funext h0
  rw [← ofAdd_toAdd s, h0', ofAdd_zero]

theorem exists_frame_of_isPlaneFrame {Q : QuadraticForm K V} {p : ℕ} (hp : p.Prime) {k : ℕ}
    {U : Fin k → Submodule K V} {e : Fin k → ↥(CFSG.RankThree.Classical2.orthDerived Q)}
    {E : Subgroup (V ≃ₗ[K] V)} (hEΩ : E ≤ CFSG.RankThree.Classical2.orthDerived Q)
    (hF : IsPlaneFrame Q p U e (E.subgroupOf (CFSG.RankThree.Classical2.orthDerived Q))) :
    ∃ F : Frame Q p E k, F.U = U := by
  have hc : ∀ i j, Commute (e i : V ≃ₗ[K] V) (e j : V ≃ₗ[K] V) := fun i j =>
    p9Frame_commute hEΩ hF (p9Frame_mem hF i) (p9Frame_mem hF j)
  refine ⟨{ ι := p9Frame_iota hp hF hc
            U := U
            inj := p9Frame_injective hp hF hc
            range := p9Frame_range hp hEΩ hF hc
            ne_bot := p9Frame_ne_bot hF
            nondeg := fun i u hu h => (Submodule.disjoint_def.1
              (isCompl_polarPerp (hF.nondeg i)).disjoint) u hu (mem_polarPerp_iff.2 h)
            orth := hF.perp
            mapsTo := fun s j u hu => by
              rw [p9Frame_iota_apply, p9Frame_prod_apply_of_mem hF hc _ j hu]
              exact p9Frame_pow_mem hF j _ hu
            triv := fun s j hs u hu => by
              rw [p9Frame_iota_apply, p9Frame_prod_apply_of_mem hF hc _ j hu, hs, ZMod.val_zero,
                pow_zero, LinearEquiv.coe_one, id_eq]
            fpf := fun s j hs u hu h => p9Frame_prod_eq_zero hp hF hc _ j hs hu h
            fix := fun s v => ⟨fun h j hs u hu =>
                mem_polarPerp_iff.1 (p9Frame_mem_polarPerp hp hF hc _ h j hs) u hu,
              fun h => p9Frame_prod_apply_of_perp hF hc _ fun j hs =>
                mem_polarPerp_iff.2 (h j hs)⟩ },
    rfl⟩

end Frame

end CFSG.StandardType.SevOm
