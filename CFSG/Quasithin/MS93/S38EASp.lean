module

public import CFSG.Quasithin.MS93.S38EAMap
public import CFSG.Quasithin.MS93.S310Mod
public import CFSG.Quasithin.MS93.S36SpECrd
public import CFSG.Quasithin.H13.L1332Inputs

public section

namespace CFSG.Quasithin.MS93.S38EA

open CFSG.Quasithin CFSG.Quasithin.MS93.S38E CFSG.Quasithin.MS93.MSP
open CFSG.Assembly.LowTwoRank Matrix
open scoped commutatorElement

variable {U₀ : Type} [Group U₀] {V G₀ Lt Tb Qa E : Subgroup U₀} {e : ℕ}
  (hS : EndSetup V G₀ Lt Tb Qa E e) (lam : ↥⁅V, V⁆ →* ℂˣ)
  (hlam1 : ∀ c : ↥⁅V, V⁆, (c : U₀) ∈ ⁅⁅V, V⁆, Tb⁆ → lam c = 1)

theorem range_le_normalizer_kS :
    (hS.secRho lam hlam1).range ≤
      Subgroup.normalizer (hS.kS lam hlam1 : Set (MulAut (hS.SM lam hlam1))) := by
  rintro _ ⟨g, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g : ↥G₀, ∀ k ∈ hS.kS lam hlam1,
      hS.secRho lam hlam1 g * k * (hS.secRho lam hlam1 g)⁻¹ ∈ hS.kS lam hlam1 := by
    rintro g _ ⟨l, hl, rfl⟩
    refine ⟨g * l * g⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hl ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hS.nLt g.2) l).mp hl
  intro k
  refine ⟨key g k, fun hk => ?_⟩
  have := key g⁻¹ _ hk
  simpa [mul_assoc] using this

include hS in
theorem fix_of_mem_bSub (v : ↥V) (hv : (v : U₀) ∈ bSub V Lt) :
    (QuotientGroup.mk v : hS.YM lam) ∈ fixV (hS.kY lam hlam1) := by
  rintro _ ⟨l, hl, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hl
  rw [hS.rho_mk lam hlam1, QuotientGroup.eq]
  apply zc_le_zLam hS.cls2 lam
  rw [mem_zc]
  intro w
  have hc := hv.2 _ hl
  have e : (((conjV hS.nV l v)⁻¹ * v : ↥V) : U₀) = ⁅(v : U₀), (l : U₀)⁆ := by
    have hvc : (v : U₀) * ⁅(v : U₀), (l : U₀)⁆ = ⁅(v : U₀), (l : U₀)⁆ * v :=
      Subgroup.mem_centralizer_iff.mp hc v v.2
    have e1 : (((conjV hS.nV l v)⁻¹ * v : ↥V) : U₀) =
        (v : U₀)⁻¹ * ⁅(v : U₀), (l : U₀)⁆ * v := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjV_apply_coe, commutatorElement_def]
      group
    rw [e1, mul_assoc, ← hvc, inv_mul_cancel_left]
  apply Subtype.ext
  show (w : U₀) * (((conjV hS.nV l v)⁻¹ * v : ↥V) : U₀) =
    (((conjV hS.nV l v)⁻¹ * v : ↥V) : U₀) * w
  rw [e]
  exact Subgroup.mem_centralizer_iff.mp hc w w.2

theorem card_kS (hK : AlternatingNatural (hS.kS lam hlam1) ⊤ ⊥ 6) :
    Nat.card ↥(hS.kS lam hlam1) = 360 := by
  obtain ⟨π₀, hR⟩ := hK
  let π : ↥(alternatingGroup (Fin 6)) →* ↥(hS.kS lam hlam1) := π₀
  have hπs : Function.Surjective π := hR.1
  obtain ⟨θ, hθ⟩ := S36E.exists_heartCoord (π := π) hR
  have hπi : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ
    rw [Subgroup.mem_bot]
    have hmat : ∀ v : V4 (ZMod 2), mat (S6B.thetaTwo (σ : Equiv.Perm (Fin 6))) *ᵥ v = v := by
      intro v
      obtain ⟨s, hs⟩ := θ.surjective (Multiplicative.ofAdd v)
      have h1 := hθ σ s
      rw [hσ, Subgroup.coe_one, MulAut.one_apply, hs, toAdd_ofAdd] at h1
      exact h1.symm
    have h2 : ((S6B.thetaTwo (σ : Equiv.Perm (Fin 6)) : ↥(StatedSp 2 (ZMod 2))) :
        GL (Fin 2 ⊕ Fin 2) (ZMod 2)) = 1 :=
      S6B.gl_ext fun v => by rw [hmat v]; simp
    have h3 : S6B.thetaTwo (σ : Equiv.Perm (Fin 6)) = 1 := Subtype.ext h2
    have h4 : (σ : Equiv.Perm (Fin 6)) = 1 := by
      rw [← map_one S6B.thetaTwo] at h3
      exact S6B.thetaTwo.injective h3
    exact Subtype.ext h4
  rw [← Nat.card_congr (MulEquiv.ofBijective π ⟨hπi, hπs⟩).toEquiv,
    H13.card_alternatingGroup_fin 6 (by norm_num)]
  rfl

theorem card_sp4_two : Nat.card (Sp4 (ZMod 2)) = 720 := by
  rw [Nat.card_congr Sp4Inf.iotaSp.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  rfl

include hS in
theorem card_comm_v0_le
    (hK : AlternatingNatural (hS.kS lam hlam1) ⊤ ⊥ 6) (he : 2 ≤ e ∧ e ≤ 4)
    (h4 : (fixV (hS.eS lam hlam1)).index = 4) :
    Nat.card ↥⁅⁅V, Lt⁆, ⁅V, Lt⁆⁆ ≤ 2 := by
  classical
  have hcard := card_kS hS lam hlam1 hK
  obtain ⟨π, hR⟩ := hK
  obtain ⟨φ, θ, hθ⟩ := S36E.coord_of_altDn hR (range_le_normalizer_kS hS lam hlam1)
  let a : ↥G₀ →* Sp4 (ZMod 2) := φ.comp (hS.secRho lam hlam1).rangeRestrict
  have ha : ∀ (g : ↥G₀) (s : hS.SM lam hlam1),
      Multiplicative.toAdd (θ (hS.secRho lam hlam1 g s)) =
        mat (a g) *ᵥ Multiplicative.toAdd (θ s) :=
    fun g s => hθ ((hS.secRho lam hlam1).rangeRestrict g) s
  have hφi : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    ext s
    apply θ.injective
    apply Multiplicative.toAdd.injective
    have h1 := hθ x s
    rw [hx, mat_one, Matrix.one_mulVec] at h1
    rw [h1]
    rfl
  let D : Subgroup (Sp4 (ZMod 2)) :=
    ((hS.kS lam hlam1).subgroupOf (hS.secRho lam hlam1).range).map φ
  have hDc : Nat.card D = 360 := by
    rw [Subgroup.card_map_of_injective hφi,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Subgroup.map_le_range _ _)).toEquiv, hcard]
  have hDi : D.index = 2 := by
    have := D.index_mul_card
    rw [hDc, card_sp4_two] at this
    omega
  have hord3 : ∀ g : Sp4 (ZMod 2), g ^ 3 = 1 → ∃ l : ↥G₀, (l : U₀) ∈ Lt ∧ a l = g := by
    intro g hg
    have hg4 : g = (g ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by rfl, pow_succ, hg, one_mul]
    have hmem : g ∈ D := by
      rw [hg4]
      exact Subgroup.sq_mem_of_index_two hDi _
    obtain ⟨k, hk, hkg⟩ := hmem
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hk
    obtain ⟨l, hl, hlk⟩ := hk
    refine ⟨l, Subgroup.mem_subgroupOf.mp hl, ?_⟩
    rw [← hkg]
    show φ ((hS.secRho lam hlam1).rangeRestrict l) = φ k
    congr 1
    exact Subtype.ext hlk
  let βv : U₀ → V4 (ZMod 2) := fun x =>
    if hx : x ∈ ⁅V, Lt⁆ then Multiplicative.toAdd (θ (sMap hS lam hlam1 ⟨x, hx⟩)) else 0
  have hβv : ∀ x (hx : x ∈ ⁅V, Lt⁆),
      βv x = Multiplicative.toAdd (θ (sMap hS lam hlam1 ⟨x, hx⟩)) := fun x hx => dite_eq_left hx
  have hs : S310.Setup G₀ Lt ⁅V, Lt⁆ (⁅V, Lt⁆ ⊓ bSub V Lt) a βv :=
    { lt_le := hS.lt_le
      le_normalizer_lt := hS.nLt
      le_normalizer_v := le_normalizer_v0 hS
      bk_le := inf_le_left
      map_mul := fun x hx y hy => by
        rw [hβv _ ((⁅V, Lt⁆).mul_mem hx hy), hβv x hx, hβv y hy]
        have e : (⟨x * y, (⁅V, Lt⁆).mul_mem hx hy⟩ : ↥⁅V, Lt⁆) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
        rw [e, map_mul, map_mul, toAdd_mul]
      surj := fun w => by
        obtain ⟨s, hs⟩ := θ.surjective (Multiplicative.ofAdd w)
        obtain ⟨x, rfl⟩ := sMap_surjective hS lam hlam1 s
        exact ⟨x, x.2, by rw [hβv _ x.2, Subtype.coe_eta, hs, toAdd_ofAdd]⟩
      ker := fun x hx => by
        rw [hβv x hx]
        constructor
        · intro h0
          have h1 : θ (sMap hS lam hlam1 ⟨x, hx⟩) = 1 :=
            Multiplicative.toAdd.injective (by rw [h0]; rfl)
          have h2 : sMap hS lam hlam1 ⟨x, hx⟩ = 1 := θ.injective (h1.trans (map_one θ).symm)
          exact ⟨hx, mem_bSub_of_fix hS lam hlam1 he h4 _
            ((sMap_eq_one_iff hS lam hlam1 _).mp h2)⟩
        · rintro ⟨-, hxB⟩
          have h2 : sMap hS lam hlam1 ⟨x, hx⟩ = 1 :=
            (sMap_eq_one_iff hS lam hlam1 _).mpr (fix_of_mem_bSub hS lam hlam1 _ hxB)
          rw [h2, map_one]
          rfl
      equiv := fun g x hx => by
        rw [hβv _ (conj_mem_of_le_normalizer (le_normalizer_v0 hS) g.2 hx), hβv x hx,
          sMap_conj hS lam hlam1 g ⟨x, hx⟩, ha]
      ord3 := hord3 }
  have hcomm : ⁅⁅⁅V, Lt⁆, Lt⁆, ⁅V, Lt⁆ ⊓ bSub V Lt⁆ = ⊥ := by
    rw [commutator_v0_lt hS, eq_bot_iff, ← commutator_v0_bSub hS]
    exact Subgroup.commutator_mono le_rfl inf_le_right
  have hD : ⁅⁅⁅V, Lt⁆, Lt⁆, ⁅⁅V, Lt⁆, Lt⁆⁆ ≤ Subgroup.centralizer (Lt : Set U₀) := by
    rw [commutator_v0_lt hS]
    exact (Subgroup.commutator_mono hS.commV_le hS.commV_le).trans
      (Subgroup.le_centralizer_iff.mp hS.ltC)
  have hV₀ : ⁅⁅⁅V, Lt⁆, Lt⁆, Lt⁆ = ⁅⁅V, Lt⁆, Lt⁆ := by
    rw [commutator_v0_lt hS, commutator_v0_lt hS]
  have h := S310.Setup.card_comm_le hs hcomm hD hV₀
  rw [commutator_v0_lt hS] at h
  simpa using h

end CFSG.Quasithin.MS93.S38EA
