module

public import CFSG.Quasithin.Background.FLcP0Main

public section

namespace CFSG.Quasithin.FLc

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LieType.BorelTits CFSG.Open

@[expose] def actHom (n : ℕ) : SLt n →* MulAut (Multiplicative (Vt n)) where
  toFun := actM
  map_one' := by
    refine MulEquiv.ext fun x => ?_
    apply Multiplicative.toAdd.injective
    rw [toAdd_actM, mat_one, one_mulVec]
    rfl
  map_mul' g h := by
    refine MulEquiv.ext fun x => ?_
    apply Multiplicative.toAdd.injective
    rw [MulAut.mul_apply, toAdd_actM, toAdd_actM, toAdd_actM, mat_mul, mulVec_mulVec]

theorem toAdd_actHom {n : ℕ} (g : SLt n) (x : Multiplicative (Vt n)) :
    Multiplicative.toAdd (actHom n g x) = mat g *ᵥ Multiplicative.toAdd x := rfl

theorem actHom_injective (n : ℕ) : Function.Injective (actHom n) := by
  intro g h hgh
  have h1 : ∀ v : Vt n, mat g *ᵥ v = mat h *ᵥ v := by
    intro v
    have := congrArg (fun φ : MulAut (Multiplicative (Vt n)) =>
      Multiplicative.toAdd (φ (Multiplicative.ofAdd v))) hgh
    simpa [toAdd_actHom] using this
  exact Subtype.ext (Matrix.ext_iff_mulVec.mpr h1)

theorem actHom_surjective (n : ℕ) : Function.Surjective (actHom n) := by
  intro φ
  obtain ⟨g, hg⟩ := exists_mat_of_mulEquiv φ
  refine ⟨g, MulEquiv.ext fun x => ?_⟩
  apply Multiplicative.toAdd.injective
  rw [toAdd_actHom, ← ofAdd_toAdd x]
  have := hg (Multiplicative.toAdd x)
  rw [toAdd_ofAdd]
  exact this.symm

@[expose] noncomputable def actEquiv (n : ℕ) : SLt n ≃* MulAut (Multiplicative (Vt n)) :=
  MulEquiv.ofBijective (actHom n) ⟨actHom_injective n, actHom_surjective n⟩


namespace P0Setup

variable {G : Type} [Group G] {L S UL : Subgroup G} {n : ℕ} {W : ℕ → Subgroup G}
  (D : P0Setup L S UL n W)

include D

theorem LS_le_normalizer : L ⊔ S ≤ Subgroup.normalizer (UL : Set G) := sup_le D.L_le D.S_le

@[expose] noncomputable def rho : ↥(L ⊔ S) →* SLt n :=
  (actEquiv n).symm.toMonoidHom.comp
    ((MulAut.congr D.β).toMonoidHom.comp
      (UL.normalizerMonoidHom.comp (Subgroup.inclusion D.LS_le_normalizer)))

theorem rho_spec (x : ↥(L ⊔ S)) (u v : ↥UL) (huv : (v : G) = (x : G) * (u : G) * (x : G)⁻¹) :
    Multiplicative.toAdd (D.β v) = mat (D.rho x) *ᵥ Multiplicative.toAdd (D.β u) := by
  have hN : (x : G) ∈ Subgroup.normalizer (UL : Set G) := D.LS_le_normalizer x.2
  have e : actEquiv n (D.rho x) =
      MulAut.congr D.β (UL.normalizerMonoidHom ⟨(x : G), hN⟩) :=
    (actEquiv n).apply_symm_apply _
  have h2 : (actEquiv n (D.rho x)) (D.β u) = D.β v := by
    rw [e, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    congr 1
    apply Subtype.ext
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact huv.symm
  rw [← h2]
  rfl

theorem rho_apply_L (l : ↥L) : D.rho ⟨(l : G), Subgroup.mem_sup_left l.2⟩ = D.α l := by
  apply actHom_injective n
  refine MulEquiv.ext fun y => ?_
  obtain ⟨u, rfl⟩ := D.β.surjective y
  have hmem : (l : G) * (u : G) * (l : G)⁻¹ ∈ UL :=
    (Subgroup.mem_normalizer_iff.1 (D.L_le l.2) (u : G)).1 u.2
  apply Multiplicative.toAdd.injective
  rw [toAdd_actHom, toAdd_actHom,
    ← D.rho_spec ⟨(l : G), Subgroup.mem_sup_left l.2⟩ u ⟨_, hmem⟩ rfl,
    ← D.rel l u ⟨_, hmem⟩ rfl]

theorem rho_eq_one_iff (x : ↥(L ⊔ S)) :
    D.rho x = 1 ↔ (x : G) ∈ Subgroup.centralizer (UL : Set G) := by
  have hN : (x : G) ∈ Subgroup.normalizer (UL : Set G) := D.LS_le_normalizer x.2
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hmem : (x : G) * u * (x : G)⁻¹ ∈ UL := (Subgroup.mem_normalizer_iff.1 hN u).1 hu
    have h1 := D.rho_spec x ⟨u, hu⟩ ⟨_, hmem⟩ rfl
    rw [h, mat_one, one_mulVec] at h1
    have h2 : D.β ⟨(x : G) * u * (x : G)⁻¹, hmem⟩ = D.β ⟨u, hu⟩ := Multiplicative.toAdd.injective h1
    have h3 : (x : G) * u * (x : G)⁻¹ = u := congrArg Subtype.val (D.β.injective h2)
    calc u * (x : G) = ((x : G) * u * (x : G)⁻¹) * (x : G) := by rw [h3]
      _ = (x : G) * u := by group
  · intro h
    apply actHom_injective n
    refine MulEquiv.ext fun y => ?_
    obtain ⟨u, rfl⟩ := D.β.surjective y
    have hmem : (x : G) * (u : G) * (x : G)⁻¹ ∈ UL := (Subgroup.mem_normalizer_iff.1 hN u).1 u.2
    have hxu : (x : G) * (u : G) * (x : G)⁻¹ = (u : G) := by
      have := Subgroup.mem_centralizer_iff.1 h (u : G) u.2
      calc (x : G) * (u : G) * (x : G)⁻¹ = ((u : G) * (x : G)) * (x : G)⁻¹ := by rw [this]
        _ = (u : G) := by group
    apply Multiplicative.toAdd.injective
    rw [toAdd_actHom, ← D.rho_spec x u ⟨_, hmem⟩ rfl, map_one]
    have : (⟨(x : G) * (u : G) * (x : G)⁻¹, hmem⟩ : ↥UL) = u := Subtype.ext hxu
    rw [this]
    rfl

theorem rho_surjective : Function.Surjective D.rho := by
  intro g
  obtain ⟨l, rfl⟩ := D.surj g
  exact ⟨⟨(l : G), Subgroup.mem_sup_left l.2⟩, D.rho_apply_L l⟩

theorem mem_normalizer_W_iff {k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) (x : ↥(L ⊔ S)) :
    (x : G) ∈ Subgroup.normalizer (W k : Set G) ↔
      D.rho x ∈ stabilizer (flagSpace n (ZMod 2) k) := by
  obtain ⟨l, c, hc, hxlc⟩ := D.decomp x.2
  have hrho : D.rho x = D.α l := by
    have hx : x = ⟨(l : G), Subgroup.mem_sup_left l.2⟩ * ⟨c, hc.2⟩ := Subtype.ext hxlc
    rw [hx, map_mul, D.rho_apply_L, (D.rho_eq_one_iff ⟨c, hc.2⟩).2 hc.1, mul_one]
  rw [hrho, ← D.mem_normalizer_W hk1 hkn l]
  have hcN : c ∈ Subgroup.normalizer (W k : Set G) :=
    Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 (D.W_le k hk1 hkn)) hc.1)
  constructor
  · intro hx
    have hl : (l : G) = (x : G) * c⁻¹ := by rw [hxlc]; group
    rw [hl]
    exact (Subgroup.normalizer (W k : Set G)).mul_mem hx
      ((Subgroup.normalizer (W k : Set G)).inv_mem hcN)
  · intro hl
    rw [hxlc]
    exact (Subgroup.normalizer (W k : Set G)).mul_mem hl hcN

theorem ker_le_S [Finite G] {x : ↥(L ⊔ S)} (hx : D.rho x = 1) : (x : G) ∈ S := by
  obtain ⟨hK2, hKn⟩ := kc_facts D.S_norm D.S2 D.L_le D.S_le D.K2
  have hnorm : ((Subgroup.centralizer (UL : Set G) ⊓ (L ⊔ S)).subgroupOf (L ⊔ S)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact hKn y hy k hk
    · intro hk
      have := hKn y⁻¹ ((L ⊔ S).inv_mem hy) _ hk
      simpa [mul_assoc] using this
  have hle := A4.le_of_normal_of_isSylowTwoOf D.syl inf_le_right hnorm hK2
  exact hle ⟨(D.rho_eq_one_iff x).1 hx, x.2⟩

theorem rho_S_le_Ut {s : G} (hs : s ∈ S) : D.rho ⟨s, Subgroup.mem_sup_right hs⟩ ∈ Ut n := by
  rw [Ut_eq_QI, mem_flagStabilizer]
  intro j hj
  exact (D.mem_normalizer_W_iff hj.1 hj.2 _).1 (D.W_norm j hj.1 hj.2 hs)

@[expose] noncomputable def Theta (H : Subgroup G) : Subgroup (SLt n) := (H.subgroupOf (L ⊔ S)).map D.rho

theorem Theta_mem_iff [Finite G] {H : Subgroup G} (hSH : S ≤ H) (x : ↥(L ⊔ S)) :
    D.rho x ∈ D.Theta H ↔ (x : G) ∈ H := by
  constructor
  · rintro ⟨h, hh, hhx⟩
    have hker : D.rho (h⁻¹ * x) = 1 := by rw [map_mul, map_inv, hhx, inv_mul_cancel]
    have hS : ((h⁻¹ * x : ↥(L ⊔ S)) : G) ∈ S := D.ker_le_S hker
    have hxh : (x : G) = (h : G) * ((h⁻¹ * x : ↥(L ⊔ S)) : G) := by simp
    rw [hxh]
    exact H.mul_mem hh (hSH hS)
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem Theta_S [Finite G] : D.Theta S = Ut n := by
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact D.rho_S_le_Ut hh
  · intro hg
    rw [← D.norm] at hg
    obtain ⟨b, hb, rfl⟩ := hg
    have hbS : (b : G) ∈ S := (Subgroup.mem_subgroupOf.1 hb).1
    exact ⟨⟨(b : G), Subgroup.mem_sup_left b.2⟩, hbS, D.rho_apply_L b⟩

theorem Theta_mono {H H' : Subgroup G} (h : H ≤ H') : D.Theta H ≤ D.Theta H' := by
  rintro g ⟨x, hx, rfl⟩
  exact ⟨x, h hx, rfl⟩

theorem Ut_le_Theta [Finite G] {H : Subgroup G} (hSH : S ≤ H) : Ut n ≤ D.Theta H := by
  rw [← D.Theta_S]
  exact D.Theta_mono hSH

theorem le_of_Theta_le [Finite G] {H H' : Subgroup G} (hSH' : S ≤ H') (hHX : H ≤ L ⊔ S)
    (h : D.Theta H ≤ D.Theta H') : H ≤ H' := by
  intro x hx
  have hxX : x ∈ L ⊔ S := hHX hx
  have h1 : D.rho ⟨x, hxX⟩ ∈ D.Theta H := ⟨⟨x, hxX⟩, hx, rfl⟩
  exact (D.Theta_mem_iff hSH' ⟨x, hxX⟩).1 (h h1)

theorem eq_of_Theta_eq [Finite G] {H H' : Subgroup G} (hSH : S ≤ H) (hSH' : S ≤ H')
    (hHX : H ≤ L ⊔ S) (hH'X : H' ≤ L ⊔ S) (h : D.Theta H = D.Theta H') : H = H' :=
  le_antisymm (D.le_of_Theta_le hSH' hHX h.le) (D.le_of_Theta_le hSH hH'X h.ge)

theorem exists_Theta_eq [Finite G] {J : Subgroup (SLt n)} (hJ : Ut n ≤ J) :
    ∃ H : Subgroup G, S ≤ H ∧ H ≤ L ⊔ S ∧ D.Theta H = J := by
  refine ⟨(J.comap D.rho).map (L ⊔ S).subtype, ?_, ?_, ?_⟩
  · intro s hs
    exact ⟨⟨s, Subgroup.mem_sup_right hs⟩, hJ (D.rho_S_le_Ut hs), rfl⟩
  · rintro _ ⟨x, _, rfl⟩
    exact x.2
  · ext g
    constructor
    · rintro ⟨x, ⟨y, hy, hyx⟩, rfl⟩
      have : y = x := Subtype.ext hyx
      subst this
      exact hy
    · intro hg
      obtain ⟨x, rfl⟩ := D.rho_surjective g
      exact ⟨x, ⟨x, hg, rfl⟩, rfl⟩

theorem Theta_parab [Finite G] (i : ℕ) :
    D.Theta (parab (L ⊔ S) n W i) = QI n {j | 1 ≤ j ∧ j < n ∧ j ≠ i} := by
  ext g
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [mem_flagStabilizer]
    intro j hj
    exact (D.mem_normalizer_W_iff hj.1 hj.2.1 x).1 ((mem_parab.1 hx).2 j hj.1 hj.2.1 hj.2.2)
  · intro hg
    obtain ⟨x, rfl⟩ := D.rho_surjective g
    rw [mem_flagStabilizer] at hg
    refine ⟨x, mem_parab.2 ⟨x.2, fun j h1 h2 h3 => ?_⟩, rfl⟩
    exact (D.mem_normalizer_W_iff h1 h2 x).2 (hg j ⟨h1, h2, h3⟩)

end P0Setup

end CFSG.Quasithin.FLc
