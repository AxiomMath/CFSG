module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrame
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs
import CFSG.LocalAnalysis.StandardType.GGE6DepZLTv
import CFSG.LocalAnalysis.StandardType.GGTDAutomizer

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord

section Frame

variable {G : Type} [Group G] {Bs L : Subgroup G} {x : G}
  {m : ℕ} {V VT : Type} [Group V] [Group VT]

private noncomputable def qTwoLMFrameB_phi (F : QTwoFrame m V VT Bs L x) : ↥Bs →* V :=
  F.theta.symm.toMonoidHom.comp (ggGamma L F.hN).rangeRestrict

private theorem qTwoLMFrameB_phi_apply (F : QTwoFrame m V VT Bs L x) (b : ↥Bs) :
    qTwoLMFrameB_phi F b =
      F.theta.symm ((ggGamma L F.hN).rangeRestrict b) := rfl

private theorem qTwoLMFrameB_phi_surjective (F : QTwoFrame m V VT Bs L x) :
    Function.Surjective (qTwoLMFrameB_phi F) :=
  F.theta.symm.surjective.comp (ggGamma L F.hN).rangeRestrict_surjective

private def qTwoLMFrameB_Acts (F : QTwoFrame m V VT Bs L x) (a : MulAut ↥Bs)
    (π : Equiv.Perm (Fin m)) : Prop :=
  ∀ b : ↥Bs, qTwoLMFrameB_phi F (a b) = F.permV π (qTwoLMFrameB_phi F b)

private theorem qTwoLMFrameB_acts_mul (F : QTwoFrame m V VT Bs L x)
    {a a' : MulAut ↥Bs} {π π' : Equiv.Perm (Fin m)}
    (h : qTwoLMFrameB_Acts F a π) (h' : qTwoLMFrameB_Acts F a' π') :
    qTwoLMFrameB_Acts F (a * a') (π * π') := by
  intro b
  calc qTwoLMFrameB_phi F ((a * a') b)
      = qTwoLMFrameB_phi F (a (a' b)) := rfl
    _ = F.permV π (qTwoLMFrameB_phi F (a' b)) := h (a' b)
    _ = F.permV π (F.permV π' (qTwoLMFrameB_phi F b)) := by rw [h' b]
    _ = F.permV (π * π') (qTwoLMFrameB_phi F b) := by rw [map_mul, MulAut.mul_apply]

private theorem qTwoLMFrameB_conj_mem_range (F : QTwoFrame m V VT Bs L x) (n : ↥L)
    (hn : (n : G) ∈ Subgroup.normalizer (Bs : Set G)) (b : ↥Bs) :
    MulAut.conj n * ggGamma L F.hN b * (MulAut.conj n)⁻¹ ∈
      (ggGamma L F.hN).range :=
  MonoidHom.mem_range.mpr
    ⟨_, ggGamma_conj L F.hN n b ((Subgroup.mem_normalizer_iff.mp hn b).mp b.2)⟩

private theorem qTwoLMFrameB_congr_val (F : QTwoFrame m V VT Bs L x) {n : ↥L}
    (hn : MulAut.conj n ∈
      Subgroup.normalizer ((ggGamma L F.hN).range : Set (MulAut ↥L)))
    (π : Equiv.Perm (Fin m))
    (hπ : ggConjAut (ggGamma L F.hN).range hn = MulAut.congr F.theta (F.permV π))
    (b : ↥Bs) :
    MulAut.conj n * ggGamma L F.hN b * (MulAut.conj n)⁻¹ =
      F.theta (F.permV π (F.theta.symm ((ggGamma L F.hN).rangeRestrict b))) := by
  have happ := congrArg
    (fun f : MulAut ↥((ggGamma L F.hN).range) =>
      ((f ((ggGamma L F.hN).rangeRestrict b) : ↥((ggGamma L F.hN).range)) :
        MulAut ↥L)) hπ
  simpa only [ggConjAut_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MonoidHom.coe_rangeRestrict] using happ

private theorem qTwoLMFrameB_phi_eq_one_iff (F : QTwoFrame m V VT Bs L x) (b : ↥Bs) :
    qTwoLMFrameB_phi F b = 1 ↔ (b : G) ∈ Subgroup.zpowers x := by
  rw [qTwoLMFrameB_phi_apply, F.theta.symm.map_eq_one_iff, Subtype.ext_iff]
  exact F.ker b

private theorem qTwoLMFrameB_exists_perm (F : QTwoFrame m V VT Bs L x) :
    ∀ a ∈ ggAutomizer L Bs, ∃ π : Equiv.Perm (Fin m), qTwoLMFrameB_Acts F a π := by
  intro a ha
  obtain ⟨g, hgL, hgN, hg⟩ := mem_ggAutomizer_iff.mp ha
  let n : ↥L := ⟨g, hgL⟩
  have hnW := conj_mem_normalizer_range_ggGamma F.hN hgL hgN
  obtain ⟨π, hπ⟩ := F.norm_perm n hnW
  refine ⟨π, fun b => ?_⟩
  have hb : a b = ⟨g * (b : G) * g⁻¹,
      (Subgroup.mem_normalizer_iff.mp hgN b).mp b.2⟩ := Subtype.ext (hg b)
  have hval := qTwoLMFrameB_congr_val F hnW π hπ b
  calc qTwoLMFrameB_phi F (a b)
      = F.theta.symm ((ggGamma L F.hN).rangeRestrict (a b)) := rfl
    _ = F.theta.symm ((ggGamma L F.hN).rangeRestrict ⟨g * (b : G) * g⁻¹,
          (Subgroup.mem_normalizer_iff.mp hgN b).mp b.2⟩) := by rw [hb]
    _ = F.theta.symm ⟨MulAut.conj n * ggGamma L F.hN b * (MulAut.conj n)⁻¹,
          qTwoLMFrameB_conj_mem_range F n hgN b⟩ := by
          congr 1
          exact Subtype.ext (ggGamma_conj L F.hN n b _)
    _ = F.theta.symm (F.theta (F.permV π
          (F.theta.symm ((ggGamma L F.hN).rangeRestrict b)))) := by
          congr 1
          exact Subtype.ext hval
    _ = F.permV π (F.theta.symm ((ggGamma L F.hN).rangeRestrict b)) := by
          rw [MulEquiv.symm_apply_apply]
    _ = F.permV π (qTwoLMFrameB_phi F b) := rfl

private theorem qTwoLMFrameB_acts_unique (F : QTwoFrame m V VT Bs L x)
    (hfaith : ∀ σ : Equiv.Perm (Fin m), (∀ v, F.permV σ v = v) → σ = 1)
    {a : MulAut ↥Bs} {π π' : Equiv.Perm (Fin m)}
    (h : qTwoLMFrameB_Acts F a π) (h' : qTwoLMFrameB_Acts F a π') : π = π' := by
  have hperm : F.permV π = F.permV π' := by
    ext v
    obtain ⟨b, rfl⟩ := qTwoLMFrameB_phi_surjective F v
    rw [← h b, ← h' b]
  have h1 : F.permV (π'⁻¹ * π) = 1 := by
    rw [map_mul, map_inv, hperm, inv_mul_cancel]
  have h2 : π'⁻¹ * π = 1 := hfaith _ (fun v => by rw [h1]; rfl)
  exact (inv_mul_eq_one.mp h2).symm

private noncomputable def qTwoLMFrameB_rho (F : QTwoFrame m V VT Bs L x)
    (hfaith : ∀ σ : Equiv.Perm (Fin m), (∀ v, F.permV σ v = v) → σ = 1) :
    ↥(ggAutomizer L Bs) →* Equiv.Perm (Fin m) :=
  MonoidHom.mk' (fun a => Classical.choose (qTwoLMFrameB_exists_perm F a a.2))
    (fun a a' => qTwoLMFrameB_acts_unique F hfaith
      (Classical.choose_spec (qTwoLMFrameB_exists_perm F (a * a') (a * a').2))
      (by
        have h1 := Classical.choose_spec (qTwoLMFrameB_exists_perm F a a.2)
        have h2 := Classical.choose_spec (qTwoLMFrameB_exists_perm F a' a'.2)
        simpa only [Subgroup.coe_mul] using qTwoLMFrameB_acts_mul F h1 h2))

private theorem qTwoLMFrameB_rho_spec (F : QTwoFrame m V VT Bs L x)
    (hfaith : ∀ σ : Equiv.Perm (Fin m), (∀ v, F.permV σ v = v) → σ = 1)
    (a : ↥(ggAutomizer L Bs)) :
    qTwoLMFrameB_Acts F (a : MulAut ↥Bs) (qTwoLMFrameB_rho F hfaith a) :=
  Classical.choose_spec (qTwoLMFrameB_exists_perm F a a.2)

private theorem qTwoLMFrameB_rho_eq_one [Finite G] (F : QTwoFrame m V VT Bs L x)
    (hnt : GGNoTransvection 3 Bs)
    (hfix : ∀ a ∈ ggAutomizer L Bs, a ⟨x, F.hx⟩ = ⟨x, F.hx⟩)
    (hfaith : ∀ σ : Equiv.Perm (Fin m), (∀ v, F.permV σ v = v) → σ = 1)
    (a : ↥(ggAutomizer L Bs)) (ha : qTwoLMFrameB_rho F hfaith a = 1) : a = 1 := by
  have hacts : qTwoLMFrameB_Acts F (a : MulAut ↥Bs) 1 := by
    rw [← ha]
    exact qTwoLMFrameB_rho_spec F hfaith a
  have hψ : ∀ b : ↥Bs,
      ((b⁻¹ * (a : MulAut ↥Bs) b : ↥Bs) : G) ∈ Subgroup.zpowers x := by
    intro b
    refine (qTwoLMFrameB_phi_eq_one_iff F (b⁻¹ * (a : MulAut ↥Bs) b)).mp ?_
    have hb1 : qTwoLMFrameB_phi F ((a : MulAut ↥Bs) b) = qTwoLMFrameB_phi F b := by
      simpa using hacts b
    rw [map_mul, map_inv, hb1, inv_mul_cancel]
  have hx1 : x ≠ 1 := by
    intro h
    have hord := F.hord
    rw [h] at hord
    simp at hord
  have h3 := CFSG.StandardType.E6Dep.ZL.ggAut_eq_one_or_isTransvection F.hx hx1 F.elemAb
    (hfix (a : MulAut ↥Bs) a.2) hψ
  rcases h3 with h1 | htr
  · exact Subtype.ext h1
  · exfalso
    have hind : (a : MulAut ↥Bs) ∈ ggInduced ⊤ Bs := by
      have htop := ggAutomizer_mono Bs (le_top : L ≤ ⊤) a.2
      rwa [ggAutomizer_eq] at htop
    exact hnt _ hind htr

private theorem qTwoLMFrameB_rho_injective [Finite G] (F : QTwoFrame m V VT Bs L x)
    (hnt : GGNoTransvection 3 Bs)
    (hfix : ∀ a ∈ ggAutomizer L Bs, a ⟨x, F.hx⟩ = ⟨x, F.hx⟩)
    (hfaith : ∀ σ : Equiv.Perm (Fin m), (∀ v, F.permV σ v = v) → σ = 1) :
    Function.Injective (qTwoLMFrameB_rho F hfaith) := by
  intro a a' h
  have h1 : qTwoLMFrameB_rho F hfaith (a * a'⁻¹) = 1 := by
    rw [map_mul, map_inv, h, mul_inv_cancel]
  exact mul_inv_eq_one.mp
    (qTwoLMFrameB_rho_eq_one F hnt hfix hfaith (a * a'⁻¹) h1)

private theorem qTwoLMFrameB_act_of_conjAut (F : QTwoFrame m V VT Bs L x)
    {σ : Equiv.Perm (Fin m)}
    (h : ∃ (n : ↥L) (hn : MulAut.conj n ∈
      Subgroup.normalizer ((ggGamma L F.hN).range : Set (MulAut ↥L))),
      ggConjAut (ggGamma L F.hN).range hn = MulAut.congr F.theta (F.permV σ)) :
    ∃ a ∈ ggAutomizer L Bs, qTwoLMFrameB_Acts F a σ := by
  obtain ⟨n, hn, hπ⟩ := h
  obtain ⟨n', hn', hconj⟩ := F.link n hn
  refine ⟨ggConjAut Bs hn', ggConjAut_mem_ggAutomizer n'.2 hn', fun b => ?_⟩
  have hb : ggConjAut Bs hn' b = ⟨(n' : G) * (b : G) * (n' : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp hn' b).mp b.2⟩ :=
    Subtype.ext (ggConjAut_apply Bs hn' b)
  have hval := qTwoLMFrameB_congr_val F hn σ hπ b
  have hmemn : MulAut.conj n * ggGamma L F.hN b * (MulAut.conj n)⁻¹ ∈
      (ggGamma L F.hN).range := by
    rw [← hconj]
    exact qTwoLMFrameB_conj_mem_range F n' hn' b
  calc qTwoLMFrameB_phi F (ggConjAut Bs hn' b)
      = F.theta.symm ((ggGamma L F.hN).rangeRestrict (ggConjAut Bs hn' b)) := rfl
    _ = F.theta.symm ⟨MulAut.conj n' * ggGamma L F.hN b * (MulAut.conj n')⁻¹,
          qTwoLMFrameB_conj_mem_range F n' hn' b⟩ := by
          congr 1
          exact Subtype.ext (ggGamma_conj L F.hN n' b _)
    _ = F.theta.symm ⟨MulAut.conj n * ggGamma L F.hN b * (MulAut.conj n)⁻¹,
          hmemn⟩ := by
          congr 1
          apply Subtype.ext
          show MulAut.conj n' * ggGamma L F.hN b * (MulAut.conj n')⁻¹ =
            MulAut.conj n * ggGamma L F.hN b * (MulAut.conj n)⁻¹
          rw [hconj]
    _ = F.theta.symm (F.theta (F.permV σ
          (F.theta.symm ((ggGamma L F.hN).rangeRestrict b)))) := by
          congr 1
          exact Subtype.ext hval
    _ = F.permV σ (F.theta.symm ((ggGamma L F.hN).rangeRestrict b)) := by
          rw [MulEquiv.symm_apply_apply]
    _ = F.permV σ (qTwoLMFrameB_phi F b) := rfl

private theorem qTwoLMFrameB_exists_act (F : QTwoFrame m V VT Bs L x)
    (σ : Equiv.Perm (Fin m)) :
    ∃ a ∈ ggAutomizer L Bs, qTwoLMFrameB_Acts F a σ :=
  qTwoLMFrameB_act_of_conjAut F (F.perm_ind σ)

private theorem qTwoLMFrameB_rho_surjective (F : QTwoFrame m V VT Bs L x)
    (hfaith : ∀ σ : Equiv.Perm (Fin m), (∀ v, F.permV σ v = v) → σ = 1) :
    Function.Surjective (qTwoLMFrameB_rho F hfaith) := by
  intro σ
  obtain ⟨a, haMem, hacts⟩ := qTwoLMFrameB_exists_act F σ
  refine ⟨⟨a, haMem⟩, ?_⟩
  exact qTwoLMFrameB_acts_unique F hfaith
    (qTwoLMFrameB_rho_spec F hfaith ⟨a, haMem⟩) hacts

private theorem qTwoLMFrameB_apply_eq_of_mul_self {H : Type} [Group H]
    (hH3 : ∀ y : H, y ^ 3 = 1) {σ : MulAut H} (hσ : σ * σ = 1)
    {N : Subgroup H} (hN : ∀ n ∈ N, σ n = n) {y : H} (hy : y⁻¹ * σ y ∈ N) : σ y = y := by
  set n := y⁻¹ * σ y with hn
  have e1 : σ y = y * n := by rw [hn]; group
  have e2 : σ (σ y) = y := by rw [← MulAut.mul_apply, hσ, MulAut.one_apply]
  rw [e1, map_mul, e1, hN n hy] at e2
  have hn2 : n * n = 1 := by
    have h := congrArg (fun z => y⁻¹ * z) e2
    simp only [inv_mul_cancel] at h
    rw [← h]
    group
  have hn1 : n = 1 := by
    calc n = n ^ 3 * (n * n)⁻¹ := by group
      _ = 1 := by rw [hH3 n, hn2]; group
  rw [e1, hn1, mul_one]

private theorem qTwoLMFrameB_fix_iff (F : QTwoFrame m V VT Bs L x)
    (hfix : ∀ a ∈ ggAutomizer L Bs, a ⟨x, F.hx⟩ = ⟨x, F.hx⟩)
    {τ : Equiv.Perm (Fin m)} {a : ↥(ggAutomizer L Bs)}
    (ha : qTwoLMFrameB_Acts F (a : MulAut ↥Bs) τ)
    (hmul : (a : MulAut ↥Bs) * (a : MulAut ↥Bs) = 1) (b : ↥Bs) :
    (a : MulAut ↥Bs) b = b ↔
      F.permV τ (qTwoLMFrameB_phi F b) = qTwoLMFrameB_phi F b := by
  constructor
  · intro hb
    rw [← ha b, hb]
  · intro hb
    have h1 : qTwoLMFrameB_phi F (b⁻¹ * (a : MulAut ↥Bs) b) = 1 := by
      rw [map_mul, map_inv, ha b, hb, inv_mul_cancel]
    have hmem : b⁻¹ * (a : MulAut ↥Bs) b ∈ (Subgroup.zpowers x).comap Bs.subtype :=
      (qTwoLMFrameB_phi_eq_one_iff F _).mp h1
    have hNfix : ∀ n ∈ (Subgroup.zpowers x).comap Bs.subtype,
        (a : MulAut ↥Bs) n = n := by
      intro n hn
      rw [Subgroup.mem_comap] at hn
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
      have hnk : n = (⟨x, F.hx⟩ : ↥Bs) ^ k := by
        apply Subtype.ext
        rw [Subgroup.coe_zpow]
        exact hk.symm
      rw [hnk, map_zpow, hfix (a : MulAut ↥Bs) a.2]
    exact qTwoLMFrameB_apply_eq_of_mul_self (H := ↥Bs)
      (fun y => Subtype.ext (by simpa using F.elemAb.2 (y : G) y.2)) hmul hNfix hmem

private theorem qTwoLMFrameB_card_fix [Finite G] (F : QTwoFrame m V VT Bs L x)
    (hfix : ∀ a ∈ ggAutomizer L Bs, a ⟨x, F.hx⟩ = ⟨x, F.hx⟩)
    (hfaith : ∀ σ : Equiv.Perm (Fin m), (∀ v, F.permV σ v = v) → σ = 1)
    {τ : Equiv.Perm (Fin m)} {a : ↥(ggAutomizer L Bs)}
    (ha : qTwoLMFrameB_rho F hfaith a = τ)
    (hmul : (a : MulAut ↥Bs) * (a : MulAut ↥Bs) = 1)
    (hτ : Nat.card {v : V // F.permV τ v = v} * 3 = Nat.card V) :
    Nat.card {b : ↥Bs // (a : MulAut ↥Bs) b = b} * 3 = Nat.card ↥Bs := by
  haveI : Finite ↥Bs := Subtype.finite
  haveI : Finite ↥((ggGamma L F.hN).range) :=
    Finite.of_surjective ((ggGamma L F.hN).rangeRestrict)
      (ggGamma L F.hN).rangeRestrict_surjective
  haveI : Finite V := Finite.of_injective F.theta F.theta.injective
  have hacts : qTwoLMFrameB_Acts F (a : MulAut ↥Bs) τ := by
    rw [← ha]
    exact qTwoLMFrameB_rho_spec F hfaith a
  let C : Subgroup V := (F.permV τ).toMonoidHom.eqLocus (MonoidHom.id V)
  let H : Subgroup ↥Bs := C.comap (qTwoLMFrameB_phi F)
  have hHfix : ∀ b : ↥Bs, b ∈ H ↔ (a : MulAut ↥Bs) b = b := by
    intro b
    rw [Subgroup.mem_comap]
    exact (qTwoLMFrameB_fix_iff F hfix hacts hmul b).symm
  have hCcard : Nat.card C = Nat.card {v : V // F.permV τ v = v} := rfl
  have hHidx : H.index = 3 := by
    change (C.comap (qTwoLMFrameB_phi F)).index = 3
    rw [Subgroup.index_comap_of_surjective C (qTwoLMFrameB_phi_surjective F)]
    refine Nat.mul_left_cancel (Nat.card_pos (α := ↥C)) ?_
    rw [Subgroup.card_mul_index, hCcard, hτ]
  have hcardH : Nat.card H * 3 = Nat.card ↥Bs := by
    rw [← hHidx, Subgroup.card_mul_index]
  have hcardEq : Nat.card {b : ↥Bs // (a : MulAut ↥Bs) b = b} = Nat.card H :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun b => (hHfix b).symm))
  rw [hcardEq, hcardH]

private theorem qTwoLMFrameB_isReflection [Finite G] (F : QTwoFrame m V VT Bs L x)
    (hnt : GGNoTransvection 3 Bs)
    (hfix : ∀ a ∈ ggAutomizer L Bs, a ⟨x, F.hx⟩ = ⟨x, F.hx⟩)
    (hfaith : ∀ σ : Equiv.Perm (Fin m), (∀ v, F.permV σ v = v) → σ = 1)
    {τ : Equiv.Perm (Fin m)} {a : ↥(ggAutomizer L Bs)}
    (ha : qTwoLMFrameB_rho F hfaith a = τ)
    (hτ2 : τ ^ 2 = 1)
    (hτ : Nat.card {v : V // F.permV τ v = v} * 3 = Nat.card V) :
    GGIsReflection 3 (a : MulAut ↥Bs) := by
  have ha2sub : a ^ 2 = 1 := by
    apply qTwoLMFrameB_rho_injective F hnt hfix hfaith
    rw [map_pow, ha, hτ2, map_one]
  have ha2 : (a : MulAut ↥Bs) ^ 2 = 1 := by
    rw [← Subgroup.coe_pow, ha2sub, Subgroup.coe_one]
  have hmul : (a : MulAut ↥Bs) * (a : MulAut ↥Bs) = 1 := by
    rw [← pow_two, ha2]
  exact ⟨ha2, qTwoLMFrameB_card_fix F hfix hfaith ha hmul hτ⟩

end Frame

theorem qTwoLMSkel_frame_weyl {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {x : G}
    {m : ℕ} {V VT : Type} [Group V] [Group VT] (F : QTwoFrame m V VT Bs L x) (hm : 3 ≤ m)
    (hnt : GGNoTransvection 3 Bs)
    (hfix : ∀ a ∈ ggAutomizer L Bs, a ⟨x, F.hx⟩ = ⟨x, F.hx⟩)
    (hfaith : ∀ σ, (∀ v, F.permV σ v = v) → σ = 1)
    (hrefl : ∀ a b : Fin m, a ≠ b → F.permV (Equiv.swap a b) ^ 2 = 1 ∧
      Nat.card {v : V // F.permV (Equiv.swap a b) v = v} * 3 = Nat.card V) :
    GGWeylOfType 3 (CoxeterMatrix.A (m - 1)) (ggAutomizer L Bs) := by
  classical
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hρinj := qTwoLMFrameB_rho_injective F hnt hfix hfaith
  have hρsurj := qTwoLMFrameB_rho_surjective F hfaith
  let ρe : ↥(ggAutomizer L Bs) ≃* Equiv.Perm (Fin (k + 1)) :=
    MulEquiv.ofBijective (qTwoLMFrameB_rho F hfaith) ⟨hρinj, hρsurj⟩
  obtain ⟨e0, he0⟩ := ggCoxeterA_mulEquivPerm k
  refine ⟨e0.trans ρe.symm, fun i => ?_⟩
  have hne : i.castSucc ≠ i.succ := ne_of_lt i.castSucc_lt_succ
  set τ : Equiv.Perm (Fin (k + 1)) := Equiv.swap i.castSucc i.succ with hτ
  have hρa : qTwoLMFrameB_rho F hfaith
      ((e0.trans ρe.symm) ((CoxeterMatrix.A k).simple i)) = τ := by
    rw [MulEquiv.trans_apply, he0]
    change ρe (ρe.symm τ) = τ
    exact MulEquiv.apply_symm_apply ρe τ
  have hτ2 : τ ^ 2 = 1 := by
    rw [hτ, pow_two, Equiv.swap_mul_self]
  have hτcard : Nat.card {v : V // F.permV τ v = v} * 3 = Nat.card V := by
    rw [hτ]
    exact (hrefl i.castSucc i.succ hne).2
  exact qTwoLMFrameB_isReflection F hnt hfix hfaith hρa hτ2 hτcard

end CFSG.StandardType.QTwo

end
