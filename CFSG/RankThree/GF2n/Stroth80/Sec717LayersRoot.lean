module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveRep
import CFSG.RankThree.GF2n.Stroth80.Sec717QLayersW1
import CFSG.RankThree.GF2n.Stroth80.Sec52bProof
import CFSG.RankThree.GF2n.Stroth80.HeringSec6Split
public import CFSG.RankThree.GF2n.Stroth80.Sec311Main

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Transport

variable {K : Type*} [Field K] {K' : Type} [Field K'] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem exists_smul_of_commute_of_addEquiv [Finite K] [Finite K'] [Nonempty ι] {T : Type*}
    [AddCommGroup T] [Module K T] {Ω : Subgroup (GL ι K')} (hΩ : AddCommutantScalar Ω)
    (hKK : Nat.card K = Nat.card K') (e : (ι → K') ≃+ T) {S : Set (T →ₗ[K] T)}
    (he : ∀ A ∈ Ω, ∃ s ∈ S, ∀ u, e ((A : Matrix ι ι K') *ᵥ u) = s (e u)) (h : T →+ T)
    (hh : ∀ s ∈ S, ∀ w, h (s w) = s (h w)) : ∃ c : K, ∀ w, h w = c • w := by
  have key : ∀ g : T →+ T, (∀ s ∈ S, ∀ w, g (s w) = s (g w)) →
      ∃ κ : K', ∀ u, g (e u) = e (κ • u) := by
    intro g hg
    obtain ⟨κ, hκ⟩ := hΩ ((e.symm.toAddMonoidHom.comp g).comp e.toAddMonoidHom) fun A hA u => by
      obtain ⟨s, hs, hse⟩ := he A hA
      apply e.injective
      show e (e.symm (g (e ((A : Matrix ι ι K') *ᵥ u)))) =
        e ((A : Matrix ι ι K') *ᵥ e.symm (g (e u)))
      rw [AddEquiv.apply_symm_apply, hse, hse, AddEquiv.apply_symm_apply, hg s hs]
    refine ⟨κ, fun u => ?_⟩
    have h1 := congrArg e (hκ u)
    simpa using h1
  have hsc : ∀ c : K, ∃ κ : K', ∀ u, c • e u = e (κ • u) := fun c =>
    key (AddMonoidHom.mk' (fun w => c • w) (smul_add c)) fun s _ w => (map_smul s c w).symm
  choose σ hσ using hsc
  obtain ⟨i⟩ := ‹Nonempty ι›
  have he0 : e (Pi.single i 1) ≠ 0 := by
    rw [ne_eq, AddEquivClass.map_eq_zero_iff]
    simp
  have hσinj : Function.Injective σ := fun c₁ c₂ h12 =>
    smul_left_injective K he0 (show c₁ • e (Pi.single i 1) = c₂ • e (Pi.single i 1) by
      rw [hσ, hσ, h12])
  obtain ⟨κ, hκ⟩ := key h hh
  obtain ⟨c, rfl⟩ := (hσinj.bijective_of_nat_card_le hKK.ge).2 κ
  refine ⟨c, fun w => ?_⟩
  obtain ⟨u, rfl⟩ := e.surjective w
  rw [hκ, hσ]

theorem opm_eq_smul_of_transport [Finite K] [Finite K'] [Nonempty ι] {E X : Type*}
    [AddCommGroup E] [Module K E] [Group X] {Ω : Subgroup (GL ι K')} (hΩ : AddCommutantScalar Ω)
    (hKK : Nat.card K = Nat.card K') (φ : X →* (E ≃ₗ[K] E)) {V Rb : Subgroup X}
    {T P : Submodule K E} (hcent : ∀ r ∈ Rb, ∀ a ∈ V, r * a = a * r)
    (hrange : ∀ a ∈ V, a ≠ 1 → LinearMap.range (opm (φ a)) = T)
    (hker : ∀ a ∈ V, a ≠ 1 → LinearMap.ker (opm (φ a)) = P) (e : (ι → K') ≃+ T)
    (he : ∀ A ∈ Ω, ∃ r ∈ Rb, ∀ u, (e ((A : Matrix ι ι K') *ᵥ u) : E) = φ r (e u))
    (hV : Nat.card V = Nat.card K) {a₀ : X} (ha₀ : a₀ ∈ V) (ha₀1 : a₀ ≠ 1) :
    (∀ a ∈ V, ∃ c : K, opm (φ a) = c • opm (φ a₀)) ∧
      ∀ c : K, ∃ a ∈ V, opm (φ a) = c • opm (φ a₀) := by
  classical
  have hcomm : ∀ r ∈ Rb, ∀ a ∈ V, ∀ x, φ r (opm (φ a) x) = opm (φ a) (φ r x) := by
    intro r hr a ha x
    have h := DFunLike.congr_fun (congrArg φ (hcent r hr a ha)) x
    rw [map_mul, map_mul, LinearEquiv.mul_apply, LinearEquiv.mul_apply] at h
    rw [opm_apply, opm_apply, map_sub, h]
  have hD₀T : ∀ x, opm (φ a₀) x ∈ T := fun x => by
    rw [← hrange a₀ ha₀ ha₀1]
    exact LinearMap.mem_range_self _ x
  have hRT : ∀ r ∈ Rb, ∀ w ∈ T, φ r w ∈ T := by
    intro r hr w hw
    rw [← hrange a₀ ha₀ ha₀1] at hw
    obtain ⟨x, rfl⟩ := hw
    rw [hcomm r hr a₀ ha₀]
    exact hD₀T _
  set S : Set (T →ₗ[K] T) := {s | ∃ r ∈ Rb, ∀ w : T, (s w : E) = φ r w} with hS
  have heS : ∀ A ∈ Ω, ∃ s ∈ S, ∀ u, e ((A : Matrix ι ι K') *ᵥ u) = s (e u) := by
    intro A hA
    obtain ⟨r, hr, hre⟩ := he A hA
    exact ⟨(φ r : E →ₗ[K] E).restrict (hRT r hr), ⟨r, hr, fun w => rfl⟩,
      fun u => Subtype.ext (hre u)⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  have hT0 : ((e (Pi.single i 1) : T) : E) ≠ 0 := by
    rw [ne_eq, Submodule.coe_eq_zero, AddEquivClass.map_eq_zero_iff]
    simp
  have hmul : ∀ a ∈ V, ∃ c : K, opm (φ a) = c • opm (φ a₀) := by
    intro a ha
    by_cases ha1 : a = 1
    · exact ⟨0, LinearMap.ext fun x => by simp [ha1, opm_apply]⟩
    have hpre : ∀ w : T, ∃ x, opm (φ a₀) x = w := fun w => by
      have hw : (w : E) ∈ LinearMap.range (opm (φ a₀)) := by
        rw [hrange a₀ ha₀ ha₀1]
        exact w.2
      exact hw
    choose pre hpre using hpre
    have hwd : ∀ x y, opm (φ a₀) x = opm (φ a₀) y → opm (φ a) x = opm (φ a) y := by
      intro x y hxy
      have hk : x - y ∈ LinearMap.ker (opm (φ a₀)) := by
        rw [LinearMap.mem_ker, map_sub, hxy, sub_self]
      rw [hker a₀ ha₀ ha₀1, ← hker a ha ha1, LinearMap.mem_ker, map_sub, sub_eq_zero] at hk
      exact hk
    have hDT : ∀ x, opm (φ a) x ∈ T := fun x => by
      rw [← hrange a ha ha1]
      exact LinearMap.mem_range_self _ x
    let g : T →+ T :=
      { toFun := fun w => ⟨opm (φ a) (pre w), hDT _⟩
        map_zero' := Subtype.ext ((hwd _ 0 (by rw [hpre, map_zero]; rfl)).trans (map_zero _))
        map_add' := fun w₁ w₂ => Subtype.ext (by
          show opm (φ a) (pre (w₁ + w₂)) = opm (φ a) (pre w₁) + opm (φ a) (pre w₂)
          rw [← map_add]
          exact hwd _ _ (by rw [hpre, map_add, hpre, hpre]; rfl)) }
    have hgS : ∀ s ∈ S, ∀ w, g (s w) = s (g w) := by
      rintro s ⟨r, hr, hs⟩ w
      apply Subtype.ext
      rw [hs]
      show opm (φ a) (pre (s w)) = φ r (opm (φ a) (pre w))
      rw [hcomm r hr a ha]
      exact hwd _ _ (by rw [hpre, hs, ← hcomm r hr a₀ ha₀, hpre])
    obtain ⟨c, hc⟩ := exists_smul_of_commute_of_addEquiv hΩ hKK e heS g hgS
    refine ⟨c, LinearMap.ext fun x => ?_⟩
    have h := congrArg Subtype.val (hc ⟨_, hD₀T x⟩)
    have h' : opm (φ a) (pre ⟨_, hD₀T x⟩) = opm (φ a) x := hwd _ _ (hpre _)
    rw [LinearMap.smul_apply, ← h']
    exact h
  choose F hF using hmul
  have hFinj : Function.Injective fun a : V => F a a.2 := by
    intro a b hab
    have hab' : F a a.2 = F b b.2 := hab
    have h2 : opm (φ (a : X)) = opm (φ b) := by rw [hF a a.2, hF b b.2, hab']
    have h1 : φ (a : X) = φ b := LinearEquiv.ext fun x => by
      have h := LinearMap.congr_fun h2 x
      rwa [opm_apply, opm_apply, sub_left_inj] at h
    by_contra hne
    have hab1 : (a : X)⁻¹ * b ≠ 1 := fun h => hne (Subtype.ext (inv_mul_eq_one.mp h))
    have hr := hrange _ (V.mul_mem (V.inv_mem a.2) b.2) hab1
    have h0 : opm (φ ((a : X)⁻¹ * b)) = 0 := by
      rw [map_mul, map_inv, h1, inv_mul_cancel]
      exact LinearMap.ext fun x => by simp [opm_apply]
    rw [h0, LinearMap.range_zero] at hr
    exact hT0 ((Submodule.eq_bot_iff T).mp hr.symm _ (e (Pi.single i 1)).2)
  refine ⟨fun a ha => ⟨F a ha, hF a ha⟩, fun c => ?_⟩
  obtain ⟨a, hac⟩ := (hFinj.bijective_of_nat_card_le hV.ge).2 c
  have hac' : F a a.2 = c := hac
  exact ⟨a, a.2, by rw [hF a a.2, hac']⟩

end Transport

section Stroth

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.sec717_T_eq_image (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {K : Type} [Field K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x))
    (T : Submodule K M₀.E)
    (hT : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.range (opm (φ a)) = T) :
    (T : Set M₀.E) = M₀.π '' (Vt M (LB M Q B) B Z t : Set G) := by
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  obtain ⟨s, hsZ0, hsQ⟩ := sec7_exists_Z0_not_Q hZcard hc hs hZ0
  have hsM : s ∈ M := hc.centre_le_M t hZ0 hsZ0
  have hsbar : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ ∈ bar M Q Z0 :=
    (mk_mem_bar_iff_sec4 hQZ0 _).mpr hsZ0
  have hsH : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ ∈ bar M Q (H0 M Z) :=
    (mk_mem_bar_iff_sec4 hQH _).mpr ((hc.Rt_le_H0 t) (hZ0.le hsZ0))
  have ha₀V : (⟨_, hsH⟩ : ↥(bar M Q (H0 M Z))) ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) :=
    Subgroup.mem_subgroupOf.mpr hsbar
  have ha₀1 : (⟨_, hsH⟩ : ↥(bar M Q (H0 M Z))) ≠ 1 := fun h => hsQ (Subgroup.mem_subgroupOf.mp
    ((QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)))
  have hs2 : s ^ 2 ∈ Q := by
    have h := sq_eq_one_bar hc hs hZc hZ0 (QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩) hsbar
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    exact Subgroup.mem_subgroupOf.mp h
  rw [← hT _ ha₀V ha₀1, range_opm_eq_image M₀ s (φ _) hc.hyp.Z_normal.1
    (fun x hx => (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hsM) x).mp hx)
    (fun x hx => hφπ ⟨s, hsM⟩ hsH x hx) hs2, hZV G M Q Z B hc n t hs Z0 hZ0 s hsZ0 hsQ]

theorem Ctx.sec717_exists_transport (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hp3 : OmegaPlusNat hc t 3) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {K : Type} [Field K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (hM : GlobalModelData M Q Z γ M₀) (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x))
    (T : Submodule K M₀.E)
    (hT : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.range (opm (φ a)) = T) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K'), Nat.card K' = Nat.card K ∧
      ∃ e : (Fin 3 ⊕ Fin 3 → K') ≃+ ↥T,
        (∀ A ∈ StatedOmega (StatedQuadPlus 3 K'),
          ∃ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)), ∀ u,
            (e ((A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *ᵥ u) : M₀.E) = φ r (e u)) ∧
        ∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
          ∃ A ∈ StatedOmega (StatedQuadPlus 3 K'), ∀ u,
            (e ((A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *ᵥ u) : M₀.E) = φ r (e u) := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hVtQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hTset := hc.sec717_T_eq_image hZcard hZc hZV hs hZ0 M₀ φ hφπ T hT
  have hπVt : ∀ v ∈ Vt M (LB M Q B) B Z t, M₀.π v ∈ T := fun v hv => by
    have : M₀.π v ∈ (T : Set M₀.E) := by
      rw [hTset]
      exact ⟨v, hv, rfl⟩
    exact this
  obtain ⟨K', fK', finK', hK'Z, ρ, hρ, -, hnorm, hn, ψ, hψ⟩ := hp3
  refine ⟨K', fK', finK', hK'Z.trans hM.card.symm, ?_⟩
  let f : ↥(Vt M (LB M Q B) B Z t) →* Multiplicative ↥T :=
    MonoidHom.mk' (fun v => Multiplicative.ofAdd ⟨M₀.π v, hπVt v v.2⟩) fun v w => by
      apply Multiplicative.toAdd.injective
      exact Subtype.ext (M₀.π_mul _ (hVtQ v.2) _ (hVtQ w.2))
  have hfZ : Z.subgroupOf (Vt M (LB M Q B) B Z t) ≤ f.ker := fun v hv => by
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    exact Subtype.ext ((M₀.π_ker _ (hVtQ v.2)).mpr (Subgroup.mem_subgroupOf.mp hv))
  let Λ := QuotientGroup.lift (Z.subgroupOf (Vt M (LB M Q B) B Z t)) f hfZ
  have hΛ : ∀ v : ↥(Vt M (LB M Q B) B Z t), Λ (QuotientGroup.mk v) = f v := fun v => rfl
  have hΛinj : Function.Injective Λ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    rw [hΛ] at hq
    have h0 : M₀.π v = 0 := congrArg Subtype.val (congrArg Multiplicative.toAdd hq)
    exact (QuotientGroup.eq_one_iff v).mpr
      (Subgroup.mem_subgroupOf.mpr ((M₀.π_ker _ (hVtQ v.2)).mp h0))
  have hΛsurj : Function.Surjective Λ := by
    intro y
    have hy : ((Multiplicative.toAdd y : ↥T) : M₀.E) ∈ (T : Set M₀.E) := (Multiplicative.toAdd y).2
    rw [hTset] at hy
    obtain ⟨v, hv, hvy⟩ := hy
    refine ⟨QuotientGroup.mk ⟨v, hv⟩, ?_⟩
    rw [hΛ]
    apply Multiplicative.toAdd.injective
    exact Subtype.ext hvy
  let E' : Multiplicative (Fin 3 ⊕ Fin 3 → K') ≃* Multiplicative ↥T :=
    ψ.symm.trans (MulEquiv.ofBijective Λ ⟨hΛinj, hΛsurj⟩)
  let e : (Fin 3 ⊕ Fin 3 → K') ≃+ ↥T := AddEquiv.toMultiplicative.symm E'
  have he_rep : ∀ (v : ↥(Vt M (LB M Q B) B Z t)) (u : Fin 3 ⊕ Fin 3 → K'),
      Multiplicative.toAdd (ψ (QuotientGroup.mk v)) = u → (e u : M₀.E) = M₀.π v := by
    intro v u hvu
    have hq : ψ.symm (Multiplicative.ofAdd u) = QuotientGroup.mk v := by
      rw [MulEquiv.symm_apply_eq, ← hvu]
      rfl
    show ((Multiplicative.toAdd (Λ (ψ.symm (Multiplicative.ofAdd u))) : ↥T) : M₀.E) = M₀.π v
    rw [hq, hΛ]
    rfl
  have hequiv : ∀ (x : ↥(Rt M (LB M Q B) t))
      (hx : QuotientGroup.mk' (Q.subgroupOf M) ⟨(x : G), hc.Rt_le_M t x.2⟩ ∈ bar M Q (H0 M Z))
      (u : Fin 3 ⊕ Fin 3 → K'),
      (e ((ρ x : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K') *ᵥ u) : M₀.E) = φ ⟨_, hx⟩ (e u) := by
    intro x hx u
    obtain ⟨v, hv⟩ := QuotientGroup.mk_surjective (ψ.symm (Multiplicative.ofAdd u))
    have hvu : Multiplicative.toAdd (ψ (QuotientGroup.mk v)) = u := by
      rw [hv, MulEquiv.apply_symm_apply]
      rfl
    have hxv : (x : G) * v * (x : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
      (Subgroup.mem_normalizer_iff.mp (hnorm x.2) v).mp v.2
    have h1 := hψ x v ⟨_, hxv⟩ rfl
    beta_reduce at h1
    rw [hvu] at h1
    rw [he_rep ⟨_, hxv⟩ _ h1, he_rep v u hvu]
    exact hφπ ⟨(x : G), hc.Rt_le_M t x.2⟩ hx v (hVtQ v.2)
  refine ⟨e, fun A hA => ?_, fun r hr => ?_⟩
  · obtain ⟨x, hx⟩ : A ∈ ρ.range := by
      rw [hρ]
      exact hA
    have hxH : QuotientGroup.mk' (Q.subgroupOf M) ⟨(x : G), hc.Rt_le_M t x.2⟩ ∈
        bar M Q (H0 M Z) := (mk_mem_bar_iff_sec4 hQH _).mpr (hc.Rt_le_H0 t x.2)
    refine ⟨⟨_, hxH⟩, Subgroup.mem_subgroupOf.mpr ((mk_mem_bar_iff_sec4 hQR _).mpr x.2),
      fun u => ?_⟩
    rw [← hx]
    exact hequiv x hxH u
  · obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (r : Mbar M Q)
    have hyR : (y : G) ∈ Rt M (LB M Q B) t :=
      (mk_mem_bar_iff_sec4 hQR y).mp (hy ▸ Subgroup.mem_subgroupOf.mp hr)
    have hyH : QuotientGroup.mk' (Q.subgroupOf M) ⟨((⟨(y : G), hyR⟩ : ↥(Rt M (LB M Q B) t)) : G),
        hc.Rt_le_M t hyR⟩ ∈ bar M Q (H0 M Z) := hy ▸ r.2
    have hr' : r = ⟨_, hyH⟩ := Subtype.ext hy.symm
    refine ⟨ρ ⟨(y : G), hyR⟩, ?_, fun u => ?_⟩
    · rw [← hρ]
      exact ⟨_, rfl⟩
    · rw [hr']
      exact hequiv ⟨(y : G), hyR⟩ hyH u

theorem Ctx.sec717_rootGroup (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hp3 : OmegaPlusNat hc t 3) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {K : Type} [Field K] [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (hM : GlobalModelData M Q Z γ M₀) (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x))
    (T : Submodule K M₀.E)
    (hT : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.range (opm (φ a)) = T) :
    ∀ a₀ ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a₀ ≠ 1 →
      (∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), ∃ c : K, opm (φ a) = c • opm (φ a₀)) ∧
        ∀ c : K, ∃ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)),
          opm (φ a) = c • opm (φ a₀) := by
  intro a₀ ha₀ ha₀1
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  obtain ⟨K', _, _, hKK, e, he, -⟩ :=
    hc.sec717_exists_transport hZcard hZc hZV hs hp3 hZ0 M₀ hM φ hφπ T hT
  obtain ⟨hnd, hrefl, hisom⟩ := quadModel_form_facts M₀
  have hiso : ∀ x u v, M₀.B (φ x u) (φ x v) = M₀.B u v := fun x =>
    hisom (φ x) (hc.phi_Qf_eq M₀ φ hφπ x)
  have hcent : ∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
      ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), r * a = a * r := by
    intro r hr a ha
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (r : Mbar M Q)
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (a : Mbar M Q)
    have hxR : (x : G) ∈ Rt M (LB M Q B) t :=
      (mk_mem_bar_iff_sec4 hQR x).mp (hx ▸ Subgroup.mem_subgroupOf.mp hr)
    have hyZ : (y : G) ∈ Z0 :=
      (mk_mem_bar_iff_sec4 hQZ0 y).mp (hy ▸ Subgroup.mem_subgroupOf.mp ha)
    have hyx : ⁅(y : G), (x : G)⁆ ∈ Q := ((hZ0 y).mp hyZ).2 x hxR
    have hq : ⁅y, x⁆ ∈ Q.subgroupOf M := by
      rw [Subgroup.mem_subgroupOf]
      have e : (((⁅y, x⁆ : ↥M)) : G) = ⁅(y : G), (x : G)⁆ := by
        simp [commutatorElement_def]
      rw [e]
      exact hyx
    have h1 : ⁅QuotientGroup.mk' (Q.subgroupOf M) y, QuotientGroup.mk' (Q.subgroupOf M) x⁆ = 1 := by
      rw [← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hq
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy]
    exact h1.symm
  have hVcard : Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) = Nat.card K := by
    have hle : bar M Q Z0 ≤ bar M Q (H0 M Z) := bar_mono' (hZ0.le.trans (hc.Rt_le_H0 t))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hM.card]
    have h := bar_card_mul_card_of_le (M := M) (S := Z0) hQZ0 (hc.centre_le_M t hZ0)
    rw [hZcard G M Q Z B hc n t hs Z0 hZ0, Nat.mul_comm (Nat.card Q) (Nat.card Z)] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  exact opm_eq_smul_of_transport (addCommutantScalar_statedOmegaPlus le_rfl) hKK.symm φ hcent hT
    (fun a ha ha1 => by
      rw [ker_opm_eq_orthogonal_range M₀.B hnd hrefl (φ a) (hiso a), hT a ha ha1])
    e he hVcard ha₀ ha₀1

theorem Ctx.sec717_fixed_P_mod_T (h34 : Stroth34Statement) (hZcard : Sec7ZCardStatement)
    (hZc : Sec7CentreMpStatement) (hZV : Sec7ZVStatement) (h52a : Stroth52aStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) (hp3 : OmegaPlusNat hc t 3)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {K : Type} [Field K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) (hM : GlobalModelData M Q Z γ M₀)
    (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x))
    (T : Submodule K M₀.E)
    (hT : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.range (opm (φ a)) = T) :
    ∀ w ∈ M₀.B.orthogonal T,
      (∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)), opm (φ r) w ∈ T) →
        w ∈ T := by
  intro w hw hfix
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hVtQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hZVt : Z ≤ Vt M (LB M Q B) B Z t := le_sup_left
  have hQM : ∀ y ∈ M, ∀ x ∈ Q, y * x * y⁻¹ ∈ Q := fun y hy x hx =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hy) x).mp hx
  have hTset := hc.sec717_T_eq_image hZcard hZc hZV hs hZ0 M₀ φ hφπ T hT
  have hπVt : ∀ v ∈ Vt M (LB M Q B) B Z t, M₀.π v ∈ T := fun v hv => by
    have : M₀.π v ∈ (T : Set M₀.E) := by
      rw [hTset]
      exact ⟨v, hv, rfl⟩
    exact this
  have hmemV : ∀ x ∈ Q, M₀.π x ∈ T → x ∈ Vt M (LB M Q B) B Z t := by
    intro x hx hxT
    have hxT' : M₀.π x ∈ (T : Set M₀.E) := hxT
    rw [hTset] at hxT'
    obtain ⟨v, hv, hvx⟩ := hxT'
    have hvQ := hVtQ hv
    have h0 : M₀.π (v⁻¹ * x) = 0 := by
      rw [M₀.π_mul _ (Q.inv_mem hvQ) _ hx, ← hvx, ← M₀.π_mul _ (Q.inv_mem hvQ) _ hvQ,
        inv_mul_cancel]
      exact (M₀.π_ker 1 Q.one_mem).mpr Z.one_mem
    have hz : v⁻¹ * x ∈ Z := (M₀.π_ker _ (Q.mul_mem (Q.inv_mem hvQ) hx)).mp h0
    have e1 : x = v * (v⁻¹ * x) := by group
    rw [e1]
    exact Subgroup.mul_mem _ hv (hZVt hz)
  obtain ⟨x, hxQ, rfl⟩ := M₀.π_surj w
  have hxW : x ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
    refine Subgroup.mem_inf.mpr ⟨hxQ, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hvQ : v ∈ Q := hVtQ hv
    have hB : M₀.B (M₀.π v) (M₀.π x) = 0 :=
      (LinearMap.BilinForm.mem_orthogonal_iff.mp hw) _ (hπVt v hv)
    rw [← M₀.comm_eq v hvQ x hxQ] at hB
    have h1 : ⁅v, x⁆ = 1 := hM.reg.inj _ (M₀.comm_mem v hvQ x hxQ) hB
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hcomm : ∀ l ∈ Rt M (LB M Q B) t, ⁅l, x⁆ ∈ Vt M (LB M Q B) B Z t := by
    intro l hl
    have hlM : l ∈ M := hc.Rt_le_M t hl
    have hlH : QuotientGroup.mk' (Q.subgroupOf M) ⟨l, hlM⟩ ∈ bar M Q (H0 M Z) :=
      (mk_mem_bar_iff_sec4 hQH _).mpr (hc.Rt_le_H0 t hl)
    have h := hfix ⟨_, hlH⟩ (Subgroup.mem_subgroupOf.mpr ((mk_mem_bar_iff_sec4 hQR _).mpr hl))
    rw [opm_apply, ← hφπ ⟨l, hlM⟩ hlH x hxQ] at h
    have hlx : l * x * l⁻¹ ∈ Q := hQM l hlM x hxQ
    have hcQ : ⁅l, x⁆ ∈ Q := by
      rw [commutatorElement_def]
      exact Q.mul_mem hlx (Q.inv_mem hxQ)
    have e1 : ((⟨l, hlM⟩ : ↥M) : G) * x * ((⟨l, hlM⟩ : ↥M) : G)⁻¹ = ⁅l, x⁆ * x := by
      show l * x * l⁻¹ = ⁅l, x⁆ * x
      rw [commutatorElement_def]
      group
    rw [e1, M₀.π_mul _ hcQ _ hxQ, add_sub_cancel_right] at h
    exact hmemV _ hcQ h
  have hRoot := stroth310Root_of_34 h34
  obtain ⟨-, r, hr, hplane⟩ := HS6.exists_hypPlane_omegaPlus h34 hRoot hc hs.toSec5 le_rfl hp3
  have homega : OmegaNat hc t := by
    obtain ⟨K', fK', finK', hK', hnat⟩ := hp3
    exact ⟨K', fK', finK', hK', Or.inl ⟨3, le_rfl, hnat⟩⟩
  obtain ⟨-, -, -, -, -, hinf, -, -, hA₁, hA₂⟩ :=
    stroth52b_of_c2 h52a h34 hRoot (sec52b_hC2 h34 hRoot) G M Q Z B hc n t hs.toSec5 homega r hr
      hplane _ _ _ _ _ rfl rfl rfl rfl rfl
  have hx₁ := (hA₁ x hxW).mpr fun l hl => hcomm l (le_Rt (M := M) (LB M Q B) ht hl)
  have hx₂ := (hA₂ x hxW).mpr fun l hl => hcomm l (by
    rw [hc.LB_conj (hc.Rt_le_M t hr)] at hl
    exact hc.conj_LB_le_Rt ht hr hl)
  have hxV : x ∈ Vt M (LB M Q B) B Z t := by
    rw [← hinf]
    exact Subgroup.mem_inf.mpr ⟨hx₁, hx₂⟩
  exact hπVt x hxV

end Stroth

end CFSG.RankThree.GF2n.Stroth80
