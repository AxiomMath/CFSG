module

public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAShape

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank S714 Module
open scoped Matrix commutatorElement

section Iso

variable {K L : Type*} [Field K] [AddCommGroup L] [Module K L]

theorem formT_pureT_pureT (P : L →ₗ[K] L →ₗ[K] K) (ψ : Matrix (Fin 2) (Fin 2) K)
    (g g' : Fin 2 → K) (m m' : L) :
    formT P ψ (pureT g m) (pureT g' m') = (g ⬝ᵥ (ψ *ᵥ g')) * P m m' := by
  simp only [formT_apply, pureT_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
    Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  ring

theorem two_mul_finrank_le_of_isotropic_of_ker [FiniteDimensional K L]
    (b : LinearMap.BilinForm K L) (hb : LinearMap.ker b = ⊥) {T : Submodule K L}
    (hT : ∀ x ∈ T, ∀ y ∈ T, b x y = 0) : 2 * finrank K T ≤ finrank K L := by
  have h := two_mul_finrank_le_add_inf_ker_of_isotropic b hT
  rw [hb, inf_bot_eq, finrank_bot, add_zero] at h
  exact h

theorem two_mul_finrank_le_of_isotropic_pureT [FiniteDimensional K L]
    {P : L →ₗ[K] L →ₗ[K] K} (hP : LinearMap.ker P = ⊥) (ψ : Matrix (Fin 2) (Fin 2) K)
    {g₁ : Fin 2 → K} (hg₁ : g₁ ⬝ᵥ (ψ *ᵥ g₁) ≠ 0) {Y T : Submodule K (Fin 2 → L)}
    (hY : finrank K Y ≤ finrank K L + 1) (hgY : ∀ m, pureT g₁ m ∈ Y) (hTY : T ≤ Y)
    (hT : ∀ x ∈ T, ∀ x' ∈ T, formT P ψ x x' = 0) : 2 * finrank K T ≤ finrank K L + 2 := by
  have hg0 : g₁ ≠ 0 := by
    rintro rfl
    simp at hg₁
  set X₁ : Submodule K (Fin 2 → L) := LinearMap.range (pureT g₁) with hX₁
  have hX₁Y : X₁ ≤ Y := by
    rintro _ ⟨m, rfl⟩
    exact hgY m
  have hX₁dim : finrank K X₁ = finrank K L := by
    rw [hX₁, LinearMap.finrank_range_of_inj (pureT_injective hg0)]
  set S : Submodule K L := Submodule.comap (pureT g₁) T with hS
  have hSiso : ∀ m ∈ S, ∀ m' ∈ S, P m m' = 0 := by
    intro m hm m' hm'
    have h1 := hT _ hm _ hm'
    rw [formT_pureT_pureT] at h1
    exact (mul_eq_zero.mp h1).resolve_left hg₁
  have hS2 : 2 * finrank K S ≤ finrank K L := two_mul_finrank_le_of_isotropic_of_ker P hP hSiso
  have hTX : finrank K ↥(T ⊓ X₁) ≤ finrank K S := by
    have hle : T ⊓ X₁ ≤ S.map (pureT g₁) := by
      rintro x ⟨hxT, m, rfl⟩
      exact ⟨m, hxT, rfl⟩
    calc finrank K ↥(T ⊓ X₁) ≤ finrank K ↥(S.map (pureT g₁)) := Submodule.finrank_mono hle
      _ ≤ finrank K S := Submodule.finrank_map_le _ _
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq T X₁
  have hsup : finrank K ↥(T ⊔ X₁) ≤ finrank K Y := Submodule.finrank_mono (sup_le hTY hX₁Y)
  omega

end Iso

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal] {hc : Ctx M Q Z B} {n : ℕ} {K : Type} [Field K] [Finite K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)}
  {b : M₀.E}

@[expose] def fixSub (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (S : Set M₀.E) :
    Subgroup (Mbar M Q) where
  carrier := {x | ∀ e ∈ S, (ρ x).toAdd e = e}
  mul_mem' {x y} hx hy e he := by
    show (ρ (x * y)).toAdd e = e
    rw [act_mul_apply, hy e he, hx e he]
  one_mem' e _ := act_one_apply e
  inv_mem' {x} hx e he := by
    show (ρ x⁻¹).toAdd e = e
    conv_lhs => rw [← hx e he]
    rw [← act_mul_apply, inv_mul_cancel]
    exact act_one_apply e

theorem mem_fixSub {S : Set M₀.E} {x : Mbar M Q} :
    x ∈ fixSub ρ S ↔ ∀ e ∈ S, (ρ x).toAdd e = e := Iff.rfl

theorem card_eq_of_conj {X : Type*} [Group X] {H H' : Subgroup X} (a : X)
    (h : ∀ x, x ∈ H ↔ a * x * a⁻¹ ∈ H') : Nat.card H = Nat.card H' :=
  Nat.card_congr
    { toFun := fun x => ⟨a * x * a⁻¹, (h x).mp x.2⟩
      invFun := fun y => ⟨a⁻¹ * y * a, (h _).mpr (by
        rw [show a * (a⁻¹ * (y : X) * a) * a⁻¹ = y by group]
        exact y.2)⟩
      left_inv := fun x => Subtype.ext (by simp only; group)
      right_inv := fun y => Subtype.ext (by simp only; group) }

theorem mem_bar_conjSubgroup_iff {g : G} (hgM : g ∈ M) {S : Subgroup G} (hQS : Q ≤ S)
    (hQM : ∀ y ∈ M, ∀ x ∈ Q, y * x * y⁻¹ ∈ Q) (x : Mbar M Q) :
    x ∈ bar M Q (conjSubgroup g S) ↔
      (QuotientGroup.mk (⟨g, hgM⟩ : ↥M) : Mbar M Q)⁻¹ * x * QuotientGroup.mk (⟨g, hgM⟩ : ↥M) ∈
        bar M Q S := by
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
  have hQS' : Q ≤ conjSubgroup g S := fun q hq => mem_conjSubgroup.mpr
    (hQS (by simpa using hQM g⁻¹ (M.inv_mem hgM) q hq))
  have e1 : (QuotientGroup.mk (⟨g, hgM⟩ : ↥M) : Mbar M Q)⁻¹ * QuotientGroup.mk m *
      QuotientGroup.mk (⟨g, hgM⟩ : ↥M) = QuotientGroup.mk ((⟨g, hgM⟩ : ↥M)⁻¹ * m * ⟨g, hgM⟩) :=
    rfl
  rw [e1]
  rw [show (QuotientGroup.mk m : Mbar M Q) = QuotientGroup.mk' (Q.subgroupOf M) m from rfl,
    show (QuotientGroup.mk ((⟨g, hgM⟩ : ↥M)⁻¹ * m * ⟨g, hgM⟩) : Mbar M Q) =
      QuotientGroup.mk' (Q.subgroupOf M) ((⟨g, hgM⟩ : ↥M)⁻¹ * m * ⟨g, hgM⟩) from rfl,
    mk_mem_bar_iff_sec4 hQS', mk_mem_bar_iff_sec4 hQS, mem_conjSubgroup]
  rfl

section Coord

variable {hS : IsTensorSetup hc n M₀ ρ b} {t : G} {L₃ L₄ : Type}
  [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄] [Module K L₄]
  {ρ₃ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₃ ≃ₗ[K] L₃)}
  {ρ₄ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₄ ≃ₗ[K] L₄)}
  {eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)} {eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄)}
  {μ : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t)} {q₃ : QuadraticForm K L₃}
  {q₄ : QuadraticForm K L₄} {φ ψ : Matrix (Fin 2) (Fin 2) K} {κ : K}

theorem ConfigAData.mem_fixSub_range_iff (h310chi : Stroth310ChiStatement)
    (h52a : Stroth52aStatement) {n' : ℕ} {r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r)
    (D : ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ) (T : TrialityFacts q₃ q₄ μ)
    {v : Mbar M Q} (hv : v ∈ bar M Q (hc.CN t)) {f : Fin 2 → K} {y : L₄} (hf : f ≠ 0)
    (hy : y ≠ 0) (hqy : q₄ y = 0)
    (hx : eN ⟨delta hS t v (mem_bar_H0_of_CN hv), delta_mem_deltaSub hS hv⟩ = pureT f y)
    {x : Mbar M Q} (hxN : x ∈ bar M Q (hc.CN t)) :
    x ∈ fixSub ρ (LinearMap.range (dlin hS v (mem_bar_H0_of_CN hv)) : Set M₀.E) ↔
      contr (ψ *ᵥ f) (eN ⟨delta hS t x (mem_bar_H0_of_CN hxN), delta_mem_deltaSub hS hxN⟩) ∈
        K ∙ y := by
  haveI : FiniteDimensional K L₃ := Module.finite_of_finrank_pos (by rw [D.finrank₃]; norm_num)
  have hvH := mem_bar_H0_of_CN hv
  obtain ⟨hxV, -, -⟩ := dmap_CN_facts h310chi h52a hS hs hr hxN
  obtain ⟨-, -, hvE⟩ := dmap_CN_facts h310chi h52a hS hs hr hv
  rw [← T.forall_betaMu_pureT_eq_zero_iff' D.finrank₃ hy hqy, mem_fixSub]
  constructor
  · intro hfix k hk
    obtain ⟨w, hw⟩ := exists_eM_eq eM (pureT (ψ *ᵥ f) k)
    have hmem : (w : M₀.E) ∈ LinearMap.range (dlin hS v hvH) ⊔ hc.VtSub hS.model t :=
      (D.mem_range_sup_iff h310chi h52a hs hr T hv hf hy hqy hx w).mpr
        (by rw [hw]; exact ⟨k, hk, rfl⟩)
    obtain ⟨e₁, he₁, u, hu, hsum⟩ := Submodule.mem_sup.mp hmem
    have h1 := D.delta_eq_betaMu hxN w
    rw [delta_apply, ← hsum, dmap_add, hxV u hu, add_zero, hw] at h1
    have h2 : dmap ρ x e₁ = 0 := by
      rw [dmap, hfix e₁ he₁, sub_self]
    rw [h2] at h1
    exact Submodule.coe_eq_zero.mp h1.symm
  · intro h e he
    obtain ⟨e₀, rfl⟩ := LinearMap.mem_range.mp he
    have hw : dlin hS v hvH e₀ ∈ wsub hS t := by
      rw [dlin_apply]
      exact hvE e₀
    obtain ⟨k, hk, hkw⟩ := (D.mem_range_sup_iff h310chi h52a hs hr T hv hf hy hqy hx ⟨_, hw⟩).mp
      (Submodule.mem_sup_left (LinearMap.mem_range_self _ e₀))
    have h1 := D.delta_eq_betaMu hxN ⟨_, hw⟩
    rw [← hkw, h k hk, Submodule.coe_zero, delta_apply] at h1
    have h3 : dmap ρ x (dlin hS v hvH e₀) = 0 := h1
    rw [act_eq_add_dmap, h3, add_zero]

end Coord

theorem exists_addSubgroup_card_eq (h310chi : Stroth310ChiStatement) (h52a : Stroth52aStatement)
    (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement) (hS : IsTensorSetup hc n M₀ ρ b)
    {n' : ℕ} {t r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r) {Z0 : Subgroup G}
    (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {L₄ : Type} [AddCommGroup L₄] [Module K L₄]
    (eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄)) {S : Subgroup (Mbar M Q)}
    (hZS : bar M Q Z0 ≤ S) (hSN : S ≤ bar M Q (hc.CN t)) :
    ∃ A : AddSubgroup (Fin 2 → L₄),
      (∀ X, X ∈ A ↔ ∃ x, ∃ hx : x ∈ S,
        X = eN ⟨delta hS t x (mem_bar_H0_of_CN (hSN hx)), delta_mem_deltaSub hS (hSN hx)⟩) ∧
      Nat.card S = Nat.card (bar M Q Z0) * Nat.card A := by
  classical
  have hdmul : ∀ (x y : ↥S), delta hS t ((x * y : ↥S) : Mbar M Q)
      (mem_bar_H0_of_CN (hSN (x * y).2)) =
        delta hS t (x : Mbar M Q) (mem_bar_H0_of_CN (hSN x.2)) +
          delta hS t (y : Mbar M Q) (mem_bar_H0_of_CN (hSN y.2)) := by
    intro x y
    rw [delta_congr hS t (Subgroup.coe_mul S x y) _
      (Subgroup.mul_mem _ (mem_bar_H0_of_CN (hSN x.2)) (mem_bar_H0_of_CN (hSN y.2)))]
    exact delta_mul h310chi h52a hS hs hr (hSN x.2) (hSN y.2)
  have hd1 : delta hS t ((1 : ↥S) : Mbar M Q) (mem_bar_H0_of_CN (hSN (1 : ↥S).2)) = 0 :=
    LinearMap.ext fun w => by rw [delta_apply, Subgroup.coe_one, dmap_one, LinearMap.zero_apply]
  set F : ↥S → Fin 2 → L₄ := fun x => eN ⟨delta hS t (x : Mbar M Q)
    (mem_bar_H0_of_CN (hSN x.2)), delta_mem_deltaSub hS (hSN x.2)⟩ with hF
  have hF1 : F 1 = 0 := by
    rw [hF]
    simp only
    rw [show (⟨delta hS t ((1 : ↥S) : Mbar M Q) (mem_bar_H0_of_CN (hSN (1 : ↥S).2)),
      delta_mem_deltaSub hS (hSN (1 : ↥S).2)⟩ : ↥(deltaSub hS t)) = 0 from Subtype.ext hd1,
      map_zero]
  have hFmul : ∀ x y, F (x * y) = F x + F y := by
    intro x y
    rw [hF]
    simp only
    rw [← map_add]
    congr 1
    exact Subtype.ext (hdmul x y)
  let φS : ↥S →* Multiplicative (Fin 2 → L₄) :=
    { toFun := fun x => Multiplicative.ofAdd (F x)
      map_one' := by rw [hF1]; rfl
      map_mul' := fun x y => by rw [hFmul]; rfl }
  refine ⟨Subgroup.toAddSubgroup' φS.range, fun X => ?_, ?_⟩
  · rw [Subgroup.mem_toAddSubgroup', MonoidHom.mem_range]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨x, x.2, (congrArg Multiplicative.toAdd hx).symm⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  · have h1 := Subgroup.card_ker_mul_card_range φS
    have hker : φS.ker = (bar M Q Z0).subgroupOf S := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      have hR : (x : Mbar M Q) ∈ bar M Q (Rt M (LB M Q B) t) :=
        bar_mono' (fun y hy => (Ctx.mem_CN.mp hy).1) (hSN x.2)
      rw [← delta_eq_zero_iff hCRW hMp hS hs hZ0 hR]
      constructor
      · intro h
        have h2 : F x = 0 := congrArg Multiplicative.toAdd h
        have h3 := eN.map_eq_zero_iff.mp h2
        exact congrArg Subtype.val h3
      · intro h
        show Multiplicative.ofAdd (F x) = 1
        have h2 : F x = 0 := by
          rw [hF]
          simp only
          rw [show (⟨delta hS t (x : Mbar M Q) (mem_bar_H0_of_CN (hSN x.2)),
            delta_mem_deltaSub hS (hSN x.2)⟩ : ↥(deltaSub hS t)) = 0 from Subtype.ext h,
            map_zero]
        rw [h2]
        rfl
    have e1 : Nat.card φS.ker = Nat.card (bar M Q Z0) := by
      rw [hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZS).toEquiv
    have e2 : Nat.card (Subgroup.toAddSubgroup' φS.range) = Nat.card φS.range :=
      Nat.card_congr
        { toFun := fun a => ⟨Multiplicative.ofAdd a.1, (Subgroup.mem_toAddSubgroup' _ _).mp a.2⟩
          invFun := fun a => ⟨Multiplicative.toAdd a.1, (Subgroup.mem_toAddSubgroup' _ _).mpr a.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [e1, ← e2] at h1
    exact h1.symm

section Card

variable {hS : IsTensorSetup hc n M₀ ρ b} {t : G} {L₃ L₄ : Type}
  [AddCommGroup L₃] [Module K L₃] [AddCommGroup L₄] [Module K L₄]
  {ρ₃ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₃ ≃ₗ[K] L₃)}
  {ρ₄ : ↥(bar M Q (Rt M (LB M Q B) t)) →* (L₄ ≃ₗ[K] L₄)}
  {eM : wvQ hS t ≃ₗ[K] (Fin 2 → L₃)} {eN : ↥(deltaSub hS t) ≃ₗ[K] (Fin 2 → L₄)}
  {μ : L₃ →ₗ[K] L₄ →ₗ[K] ↥(hc.VtSub hS.model t)} {q₃ : QuadraticForm K L₃}
  {q₄ : QuadraticForm K L₄} {φ ψ : Matrix (Fin 2) (Fin 2) K} {κ : K}

theorem ConfigAData.card_fixSub_range (h310chi : Stroth310ChiStatement)
    (h52a : Stroth52aStatement) (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement)
    {n' : ℕ} {r : G} (hs : Sec7Hyp hc n' t) (hr : Sec7A hc t r)
    (D : ConfigAData hS hs.toSec5.mem ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ) (T : TrialityFacts q₃ q₄ μ)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hSΔ : ∀ F ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      F = delta hS t g (mem_bar_H0_of_CN hg))
    {v : Mbar M Q} (hv : v ∈ bar M Q (hc.CN t)) {f : Fin 2 → K} {y : L₄} (hf : f ≠ 0)
    (hy : y ≠ 0) (hqy : q₄ y = 0)
    (hx : eN ⟨delta hS t v (mem_bar_H0_of_CN hv), delta_mem_deltaSub hS hv⟩ = pureT f y) :
    Nat.card ↥(bar M Q (hc.CN t) ⊓
      fixSub ρ (LinearMap.range (dlin hS v (mem_bar_H0_of_CN hv)) : Set M₀.E)) =
        Nat.card (bar M Q Z0) * Nat.card K ^ 9 := by
  classical
  haveI : FiniteDimensional K L₄ := Module.finite_of_finrank_pos (by rw [D.finrank₄]; norm_num)
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hZN : bar M Q Z0 ≤ bar M Q (hc.CN t) := bar_mono' (sec7ctr_Z0_le_CN hc hs hZ0)
  set S := bar M Q (hc.CN t) ⊓
    fixSub ρ (LinearMap.range (dlin hS v (mem_bar_H0_of_CN hv)) : Set M₀.E) with hSdef
  have hfix : ∀ x (hxN : x ∈ bar M Q (hc.CN t)), x ∈ S ↔
      contr (ψ *ᵥ f) (eN ⟨delta hS t x (mem_bar_H0_of_CN hxN), delta_mem_deltaSub hS hxN⟩) ∈
        K ∙ y := fun x hxN => by
    rw [hSdef, Subgroup.mem_inf, D.mem_fixSub_range_iff h310chi h52a hs hr T hv hf hy hqy hx hxN]
    exact ⟨fun h => h.2, fun h => ⟨hxN, h⟩⟩
  have hZS : bar M Q Z0 ≤ S := by
    intro a ha
    have haN := hZN ha
    refine (hfix a haN).mpr ?_
    have hR : a ∈ bar M Q (Rt M (LB M Q B) t) := bar_mono' (fun y hy => (Ctx.mem_CN.mp hy).1) haN
    have h0 := (delta_eq_zero_iff hCRW hMp hS hs hZ0 hR).mpr ha
    rw [show (⟨delta hS t a (mem_bar_H0_of_CN haN), delta_mem_deltaSub hS haN⟩ :
      ↥(deltaSub hS t)) = 0 from Subtype.ext h0, map_zero, map_zero]
    exact Submodule.zero_mem _
  have hSN' : S ≤ bar M Q (hc.CN t) := inf_le_left
  obtain ⟨A, hA, hcard⟩ := exists_addSubgroup_card_eq h310chi h52a hCRW hMp hS hs hr hZ0 eN hZS
    hSN'
  rw [hcard]
  congr 1
  set P : Submodule K (Fin 2 → L₄) := Submodule.comap (contr (ψ *ᵥ f)) (K ∙ y) with hP
  have hAP : (A : Set (Fin 2 → L₄)) = (P : Set (Fin 2 → L₄)) := by
    ext X
    rw [SetLike.mem_coe, SetLike.mem_coe, hA, hP, Submodule.mem_comap]
    constructor
    · rintro ⟨x, hxS, rfl⟩
      exact (hfix x (hSN' hxS)).mp hxS
    · intro hX
      obtain ⟨g, hg, hgF⟩ := hSΔ _ (eN.symm X).2
      have hgX : eN ⟨delta hS t g (mem_bar_H0_of_CN hg), delta_mem_deltaSub hS hg⟩ = X := by
        rw [show (⟨delta hS t g (mem_bar_H0_of_CN hg), delta_mem_deltaSub hS hg⟩ :
          ↥(deltaSub hS t)) = eN.symm X from Subtype.ext hgF.symm, LinearEquiv.apply_symm_apply]
      refine ⟨g, (hfix g hg).mpr (by rw [hgX]; exact hX), hgX.symm⟩
  have hd : ψ *ᵥ f ≠ 0 := by
    intro h0
    apply hf
    rw [← Matrix.one_mulVec f, ← D.φψ, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]
  have e : Nat.card ↥A = Nat.card ↥P := Nat.card_congr
    (Equiv.subtypeEquivRight fun X => by rw [← SetLike.mem_coe, hAP, SetLike.mem_coe])
  rw [e, Module.natCard_eq_pow_finrank (K := K), finrank_comap_contr_span hd hy, D.finrank₄]

end Card

end CFSG.RankThree.GF2n.Stroth80.S715L
