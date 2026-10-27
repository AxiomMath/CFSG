module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.Base8Nat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.ModuleSec
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

open CFSG.Quasithin CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive Equiv
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (IsIrrOn StableUnder)

variable {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ} {ψ : ↥H →* Perm (Fin n)}

@[expose] noncomputable def secIdx (Y₀ Y₁ : Subgroup V) (x : MulAut V) : ℕ :=
  (fixV (autSec (Subgroup.zpowers x) Y₁ Y₀)).index

theorem secIdx_le [Finite V] {Y₀ Y₁ : Subgroup V} (h01 : Y₀ ≤ Y₁) {x : MulAut V}
    (hx₁ : x ∈ stabSub Y₁) : secIdx Y₀ Y₁ x ≤ (fixV (Subgroup.zpowers x)).index := by
  unfold secIdx
  have h1 := index_fixV_autSec_mul_relIndex_le h01 (Subgroup.zpowers_le.2 hx₁)
  have h2 : 0 < (fixV (Subgroup.zpowers x)).relIndex Y₀ := relIndex_pos_of_finite _ _
  calc (fixV (autSec (Subgroup.zpowers x) Y₁ Y₀)).index
      ≤ (fixV (autSec (Subgroup.zpowers x) Y₁ Y₀)).index *
          (fixV (Subgroup.zpowers x)).relIndex Y₀ := Nat.le_mul_of_pos_right _ h2
    _ ≤ (fixV (Subgroup.zpowers x)).relIndex Y₁ := h1
    _ ≤ (fixV (Subgroup.zpowers x)).index := relIndex_fixV_le_index _ Y₁

theorem secIdx_mul_secIdx_le [Finite V] {Y₀ Y₁ Y₂ Y₃ : Subgroup V} (h01 : Y₀ ≤ Y₁)
    (h12 : Y₁ ≤ Y₂) (h23 : Y₂ ≤ Y₃) {x : MulAut V} (hx₁ : x ∈ stabSub Y₁)
    (hx₃ : x ∈ stabSub Y₃) :
    secIdx Y₀ Y₁ x * secIdx Y₂ Y₃ x ≤ (fixV (Subgroup.zpowers x)).index := by
  unfold secIdx
  have e1 := index_fixV_autSec_mul_relIndex_le h01 (Subgroup.zpowers_le.2 hx₁)
  have e3 := index_fixV_autSec_mul_relIndex_le h23 (Subgroup.zpowers_le.2 hx₃)
  have e2 := relIndex_fixV_mono (Subgroup.zpowers x) h12
  have h0 : 0 < (fixV (Subgroup.zpowers x)).relIndex Y₀ := relIndex_pos_of_finite _ _
  calc (fixV (autSec (Subgroup.zpowers x) Y₁ Y₀)).index *
        (fixV (autSec (Subgroup.zpowers x) Y₃ Y₂)).index
      ≤ (fixV (autSec (Subgroup.zpowers x) Y₃ Y₂)).index *
          ((fixV (autSec (Subgroup.zpowers x) Y₁ Y₀)).index *
            (fixV (Subgroup.zpowers x)).relIndex Y₀) := by
        rw [mul_comm]
        exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ h0)
    _ ≤ (fixV (autSec (Subgroup.zpowers x) Y₃ Y₂)).index *
          (fixV (Subgroup.zpowers x)).relIndex Y₂ := Nat.mul_le_mul_left _ (e1.trans e2)
    _ ≤ (fixV (Subgroup.zpowers x)).relIndex Y₃ := e3
    _ ≤ (fixV (Subgroup.zpowers x)).index := relIndex_fixV_le_index _ Y₃

section Transport

variable {Y₀ Y₁ : Subgroup V}

private theorem autSec_zpowers {K : Subgroup (MulAut V)} (h₀ : K ≤ stabSub Y₀)
    (h₁ : K ≤ stabSub Y₁) (k : ↥K) :
    autSec (Subgroup.zpowers (k : MulAut V)) Y₁ Y₀ = Subgroup.zpowers (secHom h₀ h₁ k) := by
  have hle : Subgroup.zpowers (k : MulAut V) ≤ K := Subgroup.zpowers_le.2 k.2
  have hof : (Subgroup.zpowers (k : MulAut V)).subgroupOf K = Subgroup.zpowers k := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨m, hm⟩
      exact ⟨m, Subtype.ext (by rw [Subgroup.coe_zpow]; exact hm)⟩
    · rintro ⟨m, rfl⟩
      exact ⟨m, by rw [Subgroup.coe_zpow]⟩
  rw [← map_secHom h₀ h₁ hle, hof, MonoidHom.map_zpowers]

private theorem isIrrOn_autSec (hY : IsChiefFac H Y₀ Y₁) : IsIrrOn (autSec H Y₁ Y₀) ⊤ ⊥ := by
  have h := isIrrSec_autSec hY.stab₀ hY.stab₁ hY.lt fun J hJ h₀ h₁ =>
    hY.eq_or_eq_of_invariant hJ h₀ h₁
  refine ⟨h.1, fun _ _ _ _ => Subgroup.mem_top _, fun x _ u hu => ?_, fun J hJ h₀ h₁ => ?_⟩
  · rw [Subgroup.mem_bot.1 hu, map_one]
    exact Subgroup.one_mem _
  · exact h.2 J (fun a l hl => hJ a a.2 l hl) h₀ h₁

private theorem natSec_of_natVia_top (hH₀ : H ≤ stabSub Y₀) (hH₁ : H ≤ stabSub Y₁)
    (e : ↥H ≃* ↥(autSec H Y₁ Y₀))
    (he : ∀ h, ((e h : ↥(autSec H Y₁ Y₀)) : MulAut (Sec Y₁ Y₀)) = secHom hH₀ hH₁ h)
    (φ : ↥(autSec H Y₁ Y₀) →* Perm (Fin n)) (hφe : ∀ h, φ (e h) = ψ h)
    (hfix : fixV (altPre φ) = ⊥) (hN : NatVia φ ⊤) : NatSec ψ Y₀ Y₁ := by
  obtain ⟨π, hπs, hker, heq⟩ := hN
  let ι : ↥Y₁ →* ↥(⊤ : Subgroup (Sec Y₁ Y₀)) :=
    Subgroup.topEquiv.symm.toMonoidHom.comp (QuotientGroup.mk' (Y₀.subgroupOf Y₁))
  have hι : ∀ u : ↥Y₁, ((ι u : ↥(⊤ : Subgroup (Sec Y₁ Y₀))) : Sec Y₁ Y₀) = QuotientGroup.mk u :=
    fun _ => rfl
  refine ⟨π.comp ι, ?_, ?_, fun h u v huv => ?_⟩
  · refine hπs.comp fun x => ?_
    obtain ⟨u, hu⟩ := QuotientGroup.mk_surjective (x : Sec Y₁ Y₀)
    exact ⟨u, Subtype.ext (by rw [hι, hu])⟩
  · ext u
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker, hfix,
      Subgroup.mem_subgroupOf, top_inf_eq, Subgroup.mem_bot, hι, QuotientGroup.eq_one_iff]
  · have hmk : ((ι v : ↥(⊤ : Subgroup (Sec Y₁ Y₀))) : Sec Y₁ Y₀) =
        ((e h : ↥(autSec H Y₁ Y₀)) : MulAut (Sec Y₁ Y₀))
          ((ι u : ↥(⊤ : Subgroup (Sec Y₁ Y₀))) : Sec Y₁ Y₀) := by
      rw [he, hι, hι, secHom_mk]
      congr 1
      exact Subtype.ext huv
    have h1 := heq (e h) (ι u) (ι v) hmk
    rw [hφe] at h1
    exact h1

theorem exists_secTransport (hn : 5 ≤ n) (hψ : Function.Injective ψ)
    (hA : alternatingGroup (Fin n) ≤ ψ.range) (hY : IsChiefFac H Y₀ Y₁)
    (hYL : ¬ IsCentralSec (altPre ψ) Y₀ Y₁) :
    ∃ (e : ↥H ≃* ↥(autSec H Y₁ Y₀)) (φ : ↥(autSec H Y₁ Y₀) →* Perm (Fin n)),
      (∀ h, φ (e h) = ψ h) ∧ Function.Injective φ ∧ φ.range = ψ.range ∧
      IsIrrOn (autSec H Y₁ Y₀) ⊤ ⊥ ∧ fixV (altPre φ) = ⊥ ∧
      (∀ h : ↥H,
        (fixV (Subgroup.zpowers ((e h : ↥(autSec H Y₁ Y₀)) : MulAut (Sec Y₁ Y₀)))).index =
          secIdx Y₀ Y₁ h) ∧
      (NatVia φ ⊤ → NatSec ψ Y₀ Y₁) := by
  have hH₀ : H ≤ stabSub Y₀ := hY.stab₀
  have hH₁ : H ≤ stabSub Y₁ := hY.stab₁
  have hσinj : Function.Injective (secHom hH₀ hH₁) :=
    secHom_injective hH₀ hH₁ (inf_centSec_eq_bot hn hψ hA hH₀ hH₁ hYL)
  have hrange : (secHom hH₀ hH₁).range = autSec H Y₁ Y₀ := range_secHom hH₀ hH₁
  let e₀ : ↥H →* ↥(autSec H Y₁ Y₀) :=
    (secHom hH₀ hH₁).codRestrict (autSec H Y₁ Y₀) fun h => hrange ▸ ⟨h, rfl⟩
  have heinj : Function.Injective e₀ := fun a b hab => hσinj (congrArg Subtype.val hab)
  have hesurj : Function.Surjective e₀ := by
    rintro ⟨g, hg⟩
    rw [← hrange] at hg
    obtain ⟨h, rfl⟩ := hg
    exact ⟨h, rfl⟩
  let e : ↥H ≃* ↥(autSec H Y₁ Y₀) := MulEquiv.ofBijective e₀ ⟨heinj, hesurj⟩
  have he : ∀ h, ((e h : ↥(autSec H Y₁ Y₀)) : MulAut (Sec Y₁ Y₀)) = secHom hH₀ hH₁ h :=
    fun _ => rfl
  let φ : ↥(autSec H Y₁ Y₀) →* Perm (Fin n) := ψ.comp e.symm.toMonoidHom
  have hφe : ∀ h, φ (e h) = ψ h := fun h => by
    change ψ (e.symm (e h)) = ψ h
    rw [MulEquiv.symm_apply_apply]
  have hirr : IsIrrOn (autSec H Y₁ Y₀) ⊤ ⊥ := isIrrOn_autSec hY
  have hfix : fixV (altPre φ) = ⊥ := by
    have hst : StableUnder (autSec H Y₁ Y₀) (fixV (altPre φ)) := fun x hx u hu =>
      (le_stabSub_fixV le_normalizer_altPre hx u).2 hu
    rcases hirr.2.2.2 _ hst bot_le le_top with h | h
    · exact h
    · exfalso
      refine hYL fun l hl y hy => ?_
      have hlH : l ∈ H := altPre_le hl
      have hmem : ((e ⟨l, hlH⟩ : ↥(autSec H Y₁ Y₀)) : MulAut (Sec Y₁ Y₀)) ∈ altPre φ :=
        coe_mem_altPre_iff.2 (by
          rw [hφe]
          exact (coe_mem_altPre_iff (x := ⟨l, hlH⟩)).1 hl)
      have hmk : (QuotientGroup.mk ⟨y, hy⟩ : Sec Y₁ Y₀) ∈ fixV (altPre φ) := by
        rw [h]
        exact Subgroup.mem_top _
      have h1 := mem_fixV.1 hmk _ hmem
      rw [he, secHom_mk] at h1
      exact (mk_eq_mk_sec_iff _ _).1 h1
  refine ⟨e, φ, hφe, hψ.comp e.symm.injective, ?_, hirr, hfix, fun h => ?_,
    natSec_of_natVia_top hH₀ hH₁ e he φ hφe hfix⟩
  · ext σ
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨e.symm x, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨e h, hφe h⟩
  · rw [secIdx, autSec_zpowers hH₀ hH₁ h, he]

end Transport

theorem commV_eq_top_of_fixV_eq_bot {W : Type*} [CommGroup W] {G L : Subgroup (MulAut W)}
    (hirr : IsIrrOn G ⊤ ⊥) (hLG : L ≤ G) (hfix : fixV L = ⊥) : commV G = ⊤ := by
  have hst : StableUnder G (commV G) := fun x hx u hu =>
    commV_apply_mem_of_mem_normalizer (Subgroup.le_normalizer hx) hu
  rcases hirr.2.2.2 _ hst bot_le le_top with h | h
  · exfalso
    have hGfix : fixV G = ⊤ := by
      rw [eq_top_iff]
      intro w _ g hg
      have h1 : g w * w⁻¹ ∈ commV G := Subgroup.subset_closure ⟨g, hg, w, rfl⟩
      rw [h, Subgroup.mem_bot, mul_inv_eq_one] at h1
      exact h1
    have h1 : fixV G ≤ fixV L := fun w hw g hg => hw g (hLG hg)
    rw [hGfix, hfix] at h1
    exact hirr.1.ne (top_le_iff.1 h1)
  · exact h

end CFSG.LocalAnalysis.WeakClosure81.GF2Reps86

end
