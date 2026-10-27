module

public import CFSG.Quasithin.Vol2.Ch10SecKL7b
public import CFSG.Quasithin.Background.B5Statement
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.KL7

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix

variable {W : Type} [CommGroup W]

theorem mem_fixV_zp {x : MulAut W} {w : W} : w ∈ fixV (Subgroup.zpowers x) ↔ x w = w :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

@[expose] noncomputable def topQuot : ↥(⊤ : Subgroup M3) ⧸ (⊥ : Subgroup M3).subgroupOf ⊤ ≃* M3 :=
  (QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf ⊤)).trans
    (QuotientGroup.quotientBot.trans Subgroup.topEquiv)

theorem topQuot_mk (m : ↥(⊤ : Subgroup M3)) : topQuot (QuotientGroup.mk m) = (m : M3) := rfl

theorem exists_equiv_of_realizesVia {L : Subgroup (MulAut W)} {I : Subgroup W} {π : SL32 →* ↥L}
    (h : (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia L I ⊥ π) :
    ∃ e : ↥I ≃* M3, ∀ (γ : SL32) (u : ↥I),
      e ⟨((π γ : ↥L) : MulAut W) u, h.2.2.2.1 (π γ) u u.2⟩ = act γ (e u) := by
  obtain ⟨β, hβs, hβk, hβe⟩ := h.2.2.2.2.2.2.2
  let β' : ↥I →* ↥(⊤ : Subgroup M3) ⧸ (⊥ : Subgroup M3).subgroupOf ⊤ := β
  have hβe' : ∀ (γ : SL32) (u : ↥I) (m : ↥(⊤ : Subgroup M3))
      (hu : ((π γ : ↥L) : MulAut W) u ∈ I), β' u = QuotientGroup.mk m →
      β' ⟨_, hu⟩ = QuotientGroup.mk
        (⟨natAct (StatedSL 3 (ZMod 2)) γ m, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup M3)) :=
    fun γ u m hu hm => hβe γ u m hu (Subgroup.mem_top _) hm
  have hβi : Function.Injective β' := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu))
  let e : ↥I ≃* M3 := (MulEquiv.ofBijective β' ⟨hβi, hβs⟩).trans topQuot
  refine ⟨e, fun γ u => ?_⟩
  have hu : β' u = QuotientGroup.mk (⟨e u, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup M3)) := by
    apply topQuot.injective
    rw [topQuot_mk]
    rfl
  have h2 := hβe' γ u _ (h.2.2.2.1 (π γ) u u.2) hu
  show topQuot (β' _) = _
  rw [h2, topQuot_mk]
  rfl

structure Coord (L : Subgroup (MulAut W)) (U : Subgroup W) where
  π : SL32 ≃* ↥L
  Ψ : (Fin 4 → M3) ≃* ↥U
  equivar : ∀ (γ : SL32) (v : Fin 4 → M3),
    ((π γ : ↥L) : MulAut W) (Ψ v : W) = (Ψ (actN 4 γ v) : W)

theorem actN_mulSingle (n : ℕ) (γ : SL32) (i : Fin n) (x : M3) :
    actN n γ (Pi.mulSingle i x) = Pi.mulSingle i (act γ x) := by
  funext j
  rw [actN_apply]
  by_cases hj : j = i
  · subst hj
    simp
  · rw [Pi.mulSingle_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj, map_one]

theorem nonempty_coord {L : Subgroup (MulAut W)} {U : Subgroup W}
    (h : DirectSumOfCopies L U ⊥ (FFModel.nat (StatedSL 3 (ZMod 2))) 4) : Nonempty (Coord L U) := by
  obtain ⟨I, π₁, -, hind, hsup, hreal₁⟩ := h
  let π : SL32 →* ↥L := π₁
  have hreal : ∀ i, (FFModel.nat (StatedSL 3 (ZMod 2))).RealizesVia L (I i) ⊥ π := hreal₁
  choose e he using fun i => exists_equiv_of_realizesVia (hreal i)
  have hπi : Function.Injective π := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    apply eq_one_of_act
    intro x
    have h1 := he 0 γ ((e 0).symm x)
    have h2 : (⟨((π γ : ↥L) : MulAut W) ((e 0).symm x : W), (hreal 0).2.2.2.1 (π γ) _
        ((e 0).symm x).2⟩ : ↥(I 0)) = (e 0).symm x := by
      apply Subtype.ext
      rw [hγ]
      rfl
    rw [h2, MulEquiv.apply_symm_apply] at h1
    exact h1.symm
  let ϕ : Fin 4 → (M3 →* W) := fun i => (I i).subtype.comp (e i).symm.toMonoidHom
  have hcomm : Pairwise fun i j => ∀ (x : M3) (y : M3), Commute (ϕ i x) (ϕ j y) :=
    fun _ _ _ _ _ => Commute.all _ _
  let ψ : (Fin 4 → M3) →* W := MonoidHom.noncommPiCoprod ϕ hcomm
  have hrange : ∀ i, (ϕ i).range = I i := fun i => by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (e i).symm.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hψr : ψ.range = U := by
    show (MonoidHom.noncommPiCoprod ϕ hcomm).range = U
    rw [MonoidHom.noncommPiCoprod_range]
    simp only [hrange]
    rw [← hsup, bot_sup_eq]
  have hψi : Function.Injective ψ := by
    refine MonoidHom.injective_noncommPiCoprod_of_iSupIndep ϕ ?_ fun i =>
      Subtype.val_injective.comp (e i).symm.injective
    rw [show (fun i => (ϕ i).range) = I from funext hrange, iSupIndep_def]
    intro i
    rw [disjoint_iff, ← hind i, bot_sup_eq]
  let Ψ : (Fin 4 → M3) ≃* ↥U := (MonoidHom.ofInjective hψi).trans (MulEquiv.subgroupCongr hψr)
  refine ⟨⟨MulEquiv.ofBijective π ⟨hπi, (hreal 0).1⟩, Ψ, fun γ v => ?_⟩⟩
  have key : ((π γ : MulAut W).toMonoidHom).comp ψ = ψ.comp (actN 4 γ) := by
    refine MonoidHom.functions_ext W _ _ fun i x => ?_
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, actN_mulSingle, MulEquiv.coe_toMonoidHom]
    show ((π γ : ↥L) : MulAut W) (MonoidHom.noncommPiCoprod ϕ hcomm (Pi.mulSingle i x)) =
      MonoidHom.noncommPiCoprod ϕ hcomm (Pi.mulSingle i (act γ x))
    rw [MonoidHom.noncommPiCoprod_mulSingle, MonoidHom.noncommPiCoprod_mulSingle]
    have h1 := congrArg (fun y => ((e i).symm y : W)) (he i γ ((e i).symm x))
    simp only [MulEquiv.symm_apply_apply, MulEquiv.apply_symm_apply] at h1
    exact h1
  exact congrArg (fun f => f v) key

namespace Coord

variable {L : Subgroup (MulAut W)} {U : Subgroup W} (c : Coord L U)

include c in
theorem card_U : Nat.card U = 2 ^ 12 := by
  rw [← Nat.card_congr c.Ψ.toEquiv, Nat.card_fun, card_M3, Nat.card_fin]
  norm_num

theorem exists_Ψ {w : W} (hw : w ∈ U) : ∃ v, (c.Ψ v : W) = w :=
  ⟨c.Ψ.symm ⟨w, hw⟩, by rw [MulEquiv.apply_symm_apply]⟩

theorem coe_π_of_eq {γ : SL32} {l : MulAut W} {hl : l ∈ L} (h : c.π γ = ⟨l, hl⟩) :
    ((c.π γ : ↥L) : MulAut W) = l := by
  rw [h]

include c in
theorem map_mem {l : MulAut W} (hl : l ∈ L) {w : W} (hw : w ∈ U) : l w ∈ U := by
  obtain ⟨γ, hγ⟩ := c.π.surjective ⟨l, hl⟩
  obtain ⟨v, rfl⟩ := c.exists_Ψ hw
  rw [← c.coe_π_of_eq hγ, c.equivar]
  exact (c.Ψ _).2

theorem fix_iff (γ : SL32) (v : Fin 4 → M3) :
    ((c.π γ : ↥L) : MulAut W) (c.Ψ v : W) = (c.Ψ v : W) ↔ ∀ i, act γ (v i) = v i := by
  rw [c.equivar, Subtype.coe_inj, c.Ψ.injective.eq_iff, funext_iff]
  simp only [actN_apply]

include c in
theorem fix_eq_one {w : W} (hw : w ∈ U) (h : ∀ l ∈ L, l w = w) : w = 1 := by
  obtain ⟨v, rfl⟩ := c.exists_Ψ hw
  have hv : v = 1 := funext fun i => eq_one_of_forall_act (v i) fun γ =>
    (c.fix_iff γ v).1 (h _ (c.π γ).2) i
  rw [hv, map_one]
  rfl

theorem card_fix (γ : SL32) :
    Nat.card ↥(fixV (Subgroup.zpowers ((c.π γ : ↥L) : MulAut W)) ⊓ U) =
      Nat.card (fixM γ) ^ 4 := by
  rw [show Nat.card (fixM γ) ^ 4 = Nat.card (Fin 4 → ↥(fixM γ)) by
    rw [Nat.card_fun, Nat.card_fin]]
  refine Nat.card_congr
    { toFun := fun w i => ⟨(c.Ψ.symm ⟨w, w.2.2⟩) i, ?_⟩
      invFun := fun f => ⟨c.Ψ (fun i => (f i : M3)), ?_, (c.Ψ _).2⟩
      left_inv := fun w => ?_
      right_inv := fun f => ?_ }
  · have hw := mem_fixV_zp.1 w.2.1
    have h1 : (c.Ψ (c.Ψ.symm ⟨w, w.2.2⟩) : W) = w := by rw [MulEquiv.apply_symm_apply]
    exact (c.fix_iff γ _).1 (by rw [h1]; exact hw) i
  · exact mem_fixV_zp.2 ((c.fix_iff γ _).2 fun i => (f i).2)
  · apply Subtype.ext
    show (c.Ψ (fun i => (c.Ψ.symm ⟨w, w.2.2⟩) i) : W) = w
    rw [show (fun i => (c.Ψ.symm ⟨w, w.2.2⟩) i) = c.Ψ.symm ⟨w, w.2.2⟩ from rfl,
      MulEquiv.apply_symm_apply]
  · funext i
    apply Subtype.ext
    show (c.Ψ.symm ⟨c.Ψ (fun i => (f i : M3)), _⟩) i = (f i : M3)
    rw [Subtype.coe_eta, MulEquiv.symm_apply_apply]

theorem mQuot_fix (γ : SL32) :
    E3.mQuot U (fixV (Subgroup.zpowers ((c.π γ : ↥L) : MulAut W))) = 4 * cdM γ := by
  have h1 := Subgroup.relIndex_mul_card (fixV (Subgroup.zpowers ((c.π γ : ↥L) : MulAut W))) U
  rw [c.card_fix, c.card_U] at h1
  have h3 : Nat.card (fixM γ) ^ 4 * 2 ^ (4 * cdM γ) = 2 ^ 12 := by
    calc Nat.card (fixM γ) ^ 4 * 2 ^ (4 * cdM γ)
        = (Nat.card (fixM γ) * 2 ^ cdM γ) ^ 4 := by rw [mul_pow, ← pow_mul, mul_comm (cdM γ) 4]
      _ = 2 ^ 12 := by rw [card_fixM_mul]; norm_num
  have hpos : 0 < Nat.card (fixM γ) ^ 4 := pow_pos Nat.card_pos 4
  have h4 : (fixV (Subgroup.zpowers ((c.π γ : ↥L) : MulAut W))).relIndex U =
      2 ^ (4 * cdM γ) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, mul_comm, h3]
  rw [E3.mQuot, h4, padicValNat.prime_pow]

include c in
theorem card_invariant {V : Subgroup W} (hVU : V ≤ U) (hV : ∀ l ∈ L, ∀ v ∈ V, l v ∈ V) :
    ∃ k, Nat.card V = 8 ^ k := by
  let V' : Subgroup (Fin 4 → M3) := (V.subgroupOf U).comap c.Ψ.toMonoidHom
  obtain ⟨k, hk⟩ := KL7.card_invariant 4 V' fun γ v hv => by
    show ((c.Ψ (actN 4 γ v) : ↥U) : W) ∈ V
    rw [← c.equivar]
    exact hV _ (c.π γ).2 _ hv
  refine ⟨k, ?_⟩
  rw [← hk, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVU).toEquiv]
  exact Nat.card_congr (c.Ψ.toEquiv.subtypeEquiv fun _ => Iff.rfl).symm

end Coord

end CFSG.Quasithin.Vol2.Ch10.SecB.KL7
