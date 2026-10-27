module

public import CFSG.RankThree.GF2n.Stroth80.Sec7Step77TameFalse
public import CFSG.RankThree.GF2n.Stroth80.Sec7SingularVectors

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix


theorem sec7_tame_comm_of_normalizer (h34 : Stroth34Statement) (h310chi : Stroth310ChiStatement)
    (hZc : Sec7CentreMpStatement) (hK : Sec7CRWStatement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (h71 : Stroth71Statement) (h73a : Stroth73aStatement)
    (hZV : Sec7ZVStatement) (hStr : Stroth73cOm4Statement) :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
      Sec7Hyp hc n t → ¬ Conc71abcd hc n t → OmegaMinusNat hc t 2 →
      ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
      ∀ g ∈ M, ∀ s : G, s * (g * t * g⁻¹)⁻¹ ∈ Q → ⁅s, t⁆ ∈ Q → s ∉ Z0 →
      (∀ w ∈ Wt Q (Vt M (LB M Q B) B Z t), ⁅s, w⁆ ∈ Vt M (LB M Q B) B Z t) →
      ∀ r₀ ∈ Rt M (LB M Q B) t,
      (∀ k ∈ hc.CN t,
        k ∈ Subgroup.normalizer ((LB M Q (conjSubgroup (g * r₀) B) : Subgroup G) : Set G)) →
      ∀ y ∈ hc.CN t, ⁅y, s⁆ ∈ Q := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 htame r₀ hr₀ hnorm y hy
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hguM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM htM) (M.inv_mem hgM)
  have hsM : s ∈ M := by
    have h1 : s = (s * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹) := by group
    rw [h1]
    exact M.mul_mem (hc.hyp.Q_normal.1 hs1) hguM
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
  have hZ0L : Z0 ≤ LB M Q B := fun x hx => (hZc G M Q Z B hc n t hs Z0 hZ0 x hx).1
  have hvan := sec7_pair_vanish h71 hc hs hno hgM hs1 hs2
  have hr₀M : r₀ ∈ M := hc.Rt_le_M t hr₀
  have hhM : g * r₀ ∈ M := M.mul_mem hgM hr₀M
  have hyM : y ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hy).1
  have hRnorm : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ * y * ρ⁻¹ ∈ Q := fun ρ hρ y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ)) y).mp hy
  have h1 : ⁅y, s⁆ ∈ Z0 :=
    comm_N_of_vanish h34 h310chi hK h52a hA hc hs hZ0 hsM hs2 hvan htame y hy
  have hsh : (g * r₀)⁻¹ * s * (g * r₀) ∈ Z0 := by
    have h1' : g⁻¹ * s * g ∈ Z0 := by
      have e : g⁻¹ * s * g = (g⁻¹ * (s * (g * t * g⁻¹)⁻¹) * (g⁻¹)⁻¹) * t := by group
      rw [e]
      exact Z0.mul_mem (hQZ0 ((hc.conj_mem_Q_of_mem_M (M.inv_mem hgM)).1 _ hs1)) htZ0
    have hN := IsCentrePre.mem_normalizer hZ0 hRnorm ((Rt M (LB M Q B) t).inv_mem hr₀)
    have h2 := (Subgroup.mem_normalizer_iff.mp hN _).mp h1'
    have e : (g * r₀)⁻¹ * s * (g * r₀) = r₀⁻¹ * (g⁻¹ * s * g) * (r₀⁻¹)⁻¹ := by group
    rw [e]
    exact h2
  have hSC : StronglyClosedMod M Z0 (LB M Q B) := (hStr G M Q Z B hc n t hs hno hom Z0 hZ0).2
  have hsL : s ∈ LB M Q (conjSubgroup (g * r₀) B) := by
    rw [hc.LB_conj hhM]
    exact mem_conjSubgroup.mpr (hZ0L hsh)
  have hysL : y * s * y⁻¹ ∈ LB M Q (conjSubgroup (g * r₀) B) :=
    (Subgroup.mem_normalizer_iff.mp (hnorm y hy) s).mp hsL
  have hconj : ((g * r₀)⁻¹ * y * (g * r₀)) * ((g * r₀)⁻¹ * s * (g * r₀)) *
      ((g * r₀)⁻¹ * y * (g * r₀))⁻¹ = (g * r₀)⁻¹ * (y * s * y⁻¹) * (g * r₀) := by group
  have h2 : (g * r₀)⁻¹ * (y * s * y⁻¹) * (g * r₀) ∈ Z0 := by
    have hz := hSC _ hsh ((g * r₀)⁻¹ * y * (g * r₀))
      (M.mul_mem (M.mul_mem (M.inv_mem hhM) hyM) hhM) (by
        rw [hconj]
        have := hysL
        rw [hc.LB_conj hhM] at this
        exact mem_conjSubgroup.mp this)
    rwa [hconj] at hz
  have h3 : (g * r₀)⁻¹ * ⁅y, s⁆ * (g * r₀) ∈ Z0 := by
    have e : (g * r₀)⁻¹ * ⁅y, s⁆ * (g * r₀) =
        ((g * r₀)⁻¹ * (y * s * y⁻¹) * (g * r₀)) * ((g * r₀)⁻¹ * s * (g * r₀))⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Z0.mul_mem h2 (Z0.inv_mem hsh)
  by_contra hyQ
  have hu₀Q : (g * r₀)⁻¹ * ⁅y, s⁆ * (g * r₀) ∉ Q := by
    intro hq
    apply hyQ
    have := (hc.conj_mem_Q_of_mem_M hhM).1 _ hq
    have e : g * r₀ * ((g * r₀)⁻¹ * ⁅y, s⁆ * (g * r₀)) * (g * r₀)⁻¹ = ⁅y, s⁆ := by group
    rwa [e] at this
  have hN := Z0_normalizes_of_ZV h73a hZV G M Q Z B hc n t hs hno Z0 hZ0 (g * r₀) hhM _ h3 hu₀Q (by
    have e : g * r₀ * ((g * r₀)⁻¹ * ⁅y, s⁆ * (g * r₀)) * (g * r₀)⁻¹ = ⁅y, s⁆ := by group
    rw [e]
    exact h1)
  apply hs3
  have h4 : g * r₀ * ((g * r₀)⁻¹ * s * (g * r₀)) * (g * r₀)⁻¹ ∈ Z0 :=
    (Subgroup.mem_normalizer_iff.mp hN _).mp hsh
  have e : g * r₀ * ((g * r₀)⁻¹ * s * (g * r₀)) * (g * r₀)⁻¹ = s := by group
  rwa [e] at h4

theorem sec7_CN_normalizes_LB_conj {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
    [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    {K : Type} [Field K] [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E) (hS : IsTensorSetup hc n M₀ ρ b)
    {h : G} (hhM : h ∈ M)
    (hbU : (ρ (QuotientGroup.mk (⟨h, hhM⟩ : ↥M))).toAdd b ∈ hc.VtSub hS.model t) :
    ∀ k ∈ hc.CN t,
      k ∈ Subgroup.normalizer ((LB M Q (conjSubgroup h B) : Subgroup G) : Set G) := by
  classical
  intro k hk
  have hkM : k ∈ M := hc.Rt_le_M t (Ctx.mem_CN.mp hk).1
  have hh'M : h⁻¹ * k * h ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hhM) hkM) hhM
  have hkU : ∀ u ∈ hc.VtSub hS.model t,
      (ρ (QuotientGroup.mk (⟨k, hkM⟩ : ↥M))).toAdd u = u := by
    intro u hu
    obtain ⟨v, hvV, hvQ, rfl⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp hu)
    have h1 := sec7_act_sub_comm hc M₀ ρ b hS hkM hvQ
    have h2 : M₀.π ⁅k, v⁆ = 0 :=
      (M₀.π_ker _ (sec7_comm_mem_Q hc hkM hvQ)).mpr ((Ctx.mem_CN.mp hk).2 v hvV)
    rw [h2] at h1
    exact sub_eq_zero.mp h1
  have hfix : (ρ (QuotientGroup.mk (⟨h⁻¹ * k * h, hh'M⟩ : ↥M))).toAdd b = b := by
    have e : (QuotientGroup.mk (⟨h⁻¹ * k * h, hh'M⟩ : ↥M) : Mbar M Q) =
        QuotientGroup.mk (⟨h⁻¹, M.inv_mem hhM⟩ : ↥M) * QuotientGroup.mk (⟨k, hkM⟩ : ↥M) *
          QuotientGroup.mk (⟨h, hhM⟩ : ↥M) := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      rfl
    have e2 : (QuotientGroup.mk (⟨h⁻¹, M.inv_mem hhM⟩ : ↥M) : Mbar M Q) *
        QuotientGroup.mk (⟨h, hhM⟩ : ↥M) = 1 := by
      rw [← QuotientGroup.mk_mul]
      have : (⟨h⁻¹, M.inv_mem hhM⟩ * ⟨h, hhM⟩ : ↥M) = 1 := Subtype.ext (inv_mul_cancel h)
      rw [this]
      rfl
    rw [e, act_mul_apply, act_mul_apply, hkU _ hbU, ← act_mul_apply, e2, map_one]
    rfl
  have hN := hS.stab (QuotientGroup.mk (⟨h⁻¹ * k * h, hh'M⟩ : ↥M))
    ⟨1, by rw [one_smul]; exact hfix⟩
  have hN' : h⁻¹ * k * h ∈ Subgroup.normalizer ((LB M Q B : Subgroup G) : Set G) :=
    mem_normalizer_of_mk_mem_normalizer_bar sec39_Q_le_LB hc.LB_le_M ⟨h⁻¹ * k * h, hh'M⟩ hN
  rw [hc.LB_conj hhM]
  refine conjSubgroup_eq_self_iff.mp ?_
  have e : conjSubgroup k (conjSubgroup h (LB M Q B)) = conjSubgroup h (LB M Q B) := by
    rw [← conjSubgroup_mul]
    have e1 : k * h = h * (h⁻¹ * k * h) := by group
    rw [e1, conjSubgroup_mul, conjSubgroup_eq_self_iff.mpr hN']
  exact e

theorem sec7_exists_point_reverse (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) (hom : OmegaMinusNat hc t 2)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    {K : Type} [Field K] [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (ρ : Mbar M Q →* Multiplicative (AddAut M₀.E)) (b : M₀.E) (hS : IsTensorSetup hc n M₀ ρ b)
    (ψ : M₀.E →ₗ[K] M₀.E)
    (hψ : ∀ e, ψ e = (ρ (QuotientGroup.mk (⟨t, hc.LB_le_M hs.toSec5.mem⟩ : ↥M))).toAdd e - e)
    (hrange : ∀ e, e ∈ LinearMap.range ψ ↔ e ∈ M₀.img (Vt M (LB M Q B) B Z t))
    (hW : ∀ x ∈ Q, x ∈ Wt Q (Vt M (LB M Q B) B Z t) ↔ ψ (M₀.π x) = 0)
    {g : G} (hgM : g ∈ M) (Ru : Submodule K M₀.E)
    (hRu : ∀ e, e ∈ Ru ↔ e ∈ M₀.img (conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t)))
    (hD : Module.finrank K ↥(hc.VtSub hS.model t ⊓ Ru) = 3 ∨
      (Module.finrank K ↥(hc.VtSub hS.model t ⊓ Ru) = 2 ∧
        ∀ c₁ ∈ hc.VtSub hS.model t ⊓ Ru, ∀ c₂ ∈ hc.VtSub hS.model t ⊓ Ru, ∀ a₂ : M₀.E,
          ψ a₂ = c₂ → M₀.B c₁ a₂ = 0)) :
    ∃ r₀ ∈ Rt M (LB M Q B) t, ∃ hh : g * r₀ ∈ M,
      (ρ (QuotientGroup.mk (⟨g * r₀, hh⟩ : ↥M))).toAdd b ∈ hc.VtSub hS.model t := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hg'M : g⁻¹ ∈ M := M.inv_mem hgM
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  obtain ⟨K', fK', finK', hchar', b', c', hirr, φ, θ, Ψ, hKK, hφ, hΨc, hΨr, e₀, he₀U, he₀0, hline,
    hΨe₀0, hQΨe₀, hHperp⟩ := sec7_om4_setup h34 hRoot hc hs hom M₀ ρ b hS
  let D : Submodule K M₀.E := hc.VtSub hS.model t ⊓ Ru
  have hDU : D ≤ hc.VtSub hS.model t := inf_le_left
  let Dsub : Submodule K ↥(hc.VtSub hS.model t) := D.comap (hc.VtSub hS.model t).subtype
  have hfD : Module.finrank K Dsub = Module.finrank K D :=
    (LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hDU))
  let Pi3 : Submodule K' (Sec7Om4Idx → K') := Submodule.map (sec7_two_semi θ Ψ hΨc) Dsub
  have hfPi : Module.finrank K' Pi3 = Module.finrank K D := by
    rw [sec7_two_finrank_map_semi θ (sec7_two_semi θ Ψ hΨc) Ψ.injective Dsub]
    exact hfD
  obtain ⟨y₀, hy₀P, hy₀0, hy₀Q⟩ : ∃ y₀ ∈ Pi3, y₀ ≠ 0 ∧ quadMinus 2 K' b' c' y₀ = 0 := by
    rcases hD with h3 | ⟨h2, hiso2⟩
    · exact sec7_exists_singular_of_finrank_three (quadMinus 2 K' b' c') Pi3 (hfPi.trans h3)
    · refine sec7_exists_singular_of_polar_zero (quadMinus 2 K' b' c') Pi3 (hfPi.trans h2) ?_
      obtain ⟨hf, hr⟩ := sec7_model_form M₀
      have hr1 : LinearMap.range ψ = hc.VtSub hS.model t := Submodule.ext fun e => hrange e
      have hk1 := sec7_ker_psi_eq_orth hc M₀ ρ b hS ψ hW
      obtain ⟨β₁, h₁, hβ₁⟩ := sec7_induced_form M₀.B hf hr (hc.VtSub hS.model t) ψ hr1 hk1
      have hbarR : ∀ r : ↥(Rt M (LB M Q B) t),
          (QuotientGroup.mk ⟨(r : G), hRM r.2⟩ : Mbar M Q) ∈ bar M Q (Rt M (LB M Q B) t) := fun r =>
        Subgroup.mem_map.mpr ⟨⟨(r : G), hRM r.2⟩, Subgroup.mem_subgroupOf.mpr r.2, rfl⟩
      have hbarH : ∀ r : ↥(Rt M (LB M Q B) t),
          (QuotientGroup.mk ⟨(r : G), hRM r.2⟩ : Mbar M Q) ∈ bar M Q (H0 M Z) := fun r =>
        Subgroup.mem_map.mpr ⟨⟨(r : G), hRM r.2⟩,
          Subgroup.mem_subgroupOf.mpr (hc.Rt_le_H0 t r.2), rfl⟩
      have hactmem : ∀ (r : ↥(Rt M (LB M Q B) t)) (w : M₀.E), w ∈ hc.VtSub hS.model t →
          (ρ (QuotientGroup.mk ⟨(r : G), hRM r.2⟩)).toAdd w ∈ hc.VtSub hS.model t :=
        fun r w hw => hc.act_mem_VtSub hS ht _ (hbarR r) w hw
      let act : ↥(Rt M (LB M Q B) t) → ↥(hc.VtSub hS.model t) → ↥(hc.VtSub hS.model t) :=
        fun r w => ⟨(ρ (QuotientGroup.mk ⟨(r : G), hRM r.2⟩)).toAdd (w : M₀.E), hactmem r w w.2⟩
      have hactΨ : ∀ (r : ↥(Rt M (LB M Q B) t)) (u : ↥(hc.VtSub hS.model t)),
          Ψ (act r u) = ((φ r : GL Sec7Om4Idx K') : Matrix Sec7Om4Idx Sec7Om4Idx K') *ᵥ Ψ u :=
        fun r u => hΨr r u (hactmem r u u.2)
      have htZ0 : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) ht hZ0
      have hcomm_act : ∀ a b : Mbar M Q, a * b = b * a → ∀ e,
          (ρ a).toAdd ((ρ b).toAdd e) = (ρ b).toAdd ((ρ a).toAdd e) := by
        intro a b hab e
        rw [← act_mul_apply ρ a b e, ← act_mul_apply ρ b a e, hab]
      have hψS : ∀ (r : ↥(Rt M (LB M Q B) t)) (e : M₀.E),
          ψ ((ρ (QuotientGroup.mk ⟨(r : G), hRM r.2⟩)).toAdd e) =
            (ρ (QuotientGroup.mk ⟨(r : G), hRM r.2⟩)).toAdd (ψ e) := by
        intro r e
        rw [hψ, hψ, map_sub,
          hcomm_act _ _ (endg_comm_centre hZ0 hRM (z := ⟨t, htM⟩) htZ0 (hbarR r)) e]
      have hinvβ : ∀ (r : ↥(Rt M (LB M Q B) t)) (x y : ↥(hc.VtSub hS.model t)),
          β₁ (act r x) (act r y) = β₁ x y := by
        intro r x y
        obtain ⟨c, hc'⟩ : ∃ c, ψ c = (y : M₀.E) := by
          have : (y : M₀.E) ∈ LinearMap.range ψ := by rw [hr1]; exact y.2
          exact LinearMap.mem_range.mp this
        have h1 : ψ ((ρ (QuotientGroup.mk ⟨(r : G), hRM r.2⟩)).toAdd c) =
            ((act r y : ↥(hc.VtSub hS.model t)) : M₀.E) := by
          rw [hψS, hc']
        rw [hβ₁ (act r x) (act r y) _ h1, hβ₁ x y c hc']
        exact hS.iso _ (hbarH r) _ _
      obtain ⟨κ, hκ⟩ := sec7_form_scalar_of_invariant hirr θ Ψ hΨc β₁ φ hφ act hactΨ hinvβ
      have hκ0 : κ ≠ 0 := by
        intro h0
        have hz : ∀ x y : ↥(hc.VtSub hS.model t), β₁ x y = 0 := fun x y => by
          have := hκ x y
          rw [h0, zero_mul] at this
          exact θ.map_eq_zero_iff.mp this
        have := h₁.1 ⟨e₀, he₀U⟩ (fun y => hz _ y)
        exact he₀0 (congrArg Subtype.val this)
      intro x hx y hy
      obtain ⟨w₁, hw₁, rfl⟩ := Submodule.mem_map.mp hx
      obtain ⟨w₂, hw₂, rfl⟩ := Submodule.mem_map.mp hy
      obtain ⟨a₂, ha₂⟩ : ∃ a₂, ψ a₂ = (w₂ : M₀.E) := by
        have : (w₂ : M₀.E) ∈ LinearMap.range ψ := by rw [hr1]; exact w₂.2
        exact LinearMap.mem_range.mp this
      have hz : β₁ w₁ w₂ = 0 := by
        rw [hβ₁ w₁ w₂ a₂ ha₂]
        exact hiso2 _ hw₁ _ hw₂ a₂ ha₂
      have := hκ w₁ w₂
      rw [hz, map_zero] at this
      exact (mul_eq_zero.mp this.symm).resolve_left hκ0
  obtain ⟨A, hA, hAx⟩ := omegaMinusFourSingularTrans_holds K' b' c' hirr (Ψ ⟨e₀, he₀U⟩) y₀
    hΨe₀0 hy₀0 hQΨe₀ hy₀Q
  have hAφ : A ∈ φ.range := by
    rw [hφ]
    exact hA
  obtain ⟨r₀, rfl⟩ := hAφ
  have hr₀R : (r₀ : G) ∈ Rt M (LB M Q B) t := r₀.2
  have hr₀M : (r₀ : G) ∈ M := hc.Rt_le_M t hr₀R
  have hbarR : (QuotientGroup.mk (⟨(r₀ : G), hr₀M⟩ : ↥M) : Mbar M Q) ∈
      bar M Q (Rt M (LB M Q B) t) :=
    Subgroup.mem_map.mpr ⟨⟨(r₀ : G), hr₀M⟩, Subgroup.mem_subgroupOf.mpr hr₀R, rfl⟩
  have hmemV : (ρ (QuotientGroup.mk (⟨(r₀ : G), hr₀M⟩ : ↥M))).toAdd e₀ ∈
      hc.VtSub hS.model t := hc.act_mem_VtSub hS ht _ hbarR e₀ he₀U
  have hΨ1 := hΨr r₀ ⟨e₀, he₀U⟩ hmemV
  obtain ⟨w, hwD, hwΨ⟩ := Submodule.mem_map.mp hy₀P
  have hwΨ' : Ψ w = y₀ := hwΨ
  have hwe : (⟨(ρ (QuotientGroup.mk (⟨(r₀ : G), hr₀M⟩ : ↥M))).toAdd e₀, hmemV⟩ :
      ↥(hc.VtSub hS.model t)) = w := Ψ.injective (by rw [hΨ1, hAx, hwΨ'])
  have hNe₀ : (ρ (QuotientGroup.mk (⟨(r₀ : G), hr₀M⟩ : ↥M))).toAdd e₀ ∈ D := by
    have := hwD
    rw [← hwe] at this
    exact this
  obtain ⟨c, hcb⟩ := (hline b).mp hS.b_img
  have hr₀H : (r₀ : G) ∈ H0 M Z := hc.Rt_le_H0 t hr₀R
  have hr₀bar : (QuotientGroup.mk (⟨(r₀ : G), hr₀M⟩ : ↥M) : Mbar M Q) ∈ bar M Q (H0 M Z) :=
    Subgroup.mem_map.mpr ⟨⟨(r₀ : G), hr₀M⟩, Subgroup.mem_subgroupOf.mpr hr₀H, rfl⟩
  have hNb : (ρ (QuotientGroup.mk (⟨(r₀ : G), hr₀M⟩ : ↥M))).toAdd b ∈ D := by
    rw [hcb, hS.lin _ hr₀bar]
    exact D.smul_mem c hNe₀
  have hZV' : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hZS : Z ≤ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) := hc.Z_le_conjSubgroup hZV' hg'M
  have hmem' : (ρ (QuotientGroup.mk (⟨(r₀ : G), hr₀M⟩ : ↥M))).toAdd b ∈
      M₀.img (conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t)) := (hRu _).mp hNb.2
  have hconj : conjSubgroup g (conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t)) =
      Vt M (LB M Q B) B Z t := by
    rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
  have hfin := (sec7_img_conj_iff hc M₀ ρ b hS hgM hZS _).mpr hmem'
  rw [hconj] at hfin
  refine ⟨(r₀ : G), hr₀R, M.mul_mem hgM hr₀M, ?_⟩
  have e : (QuotientGroup.mk (⟨g * (r₀ : G), M.mul_mem hgM hr₀M⟩ : ↥M) : Mbar M Q) =
      QuotientGroup.mk (⟨g, hgM⟩ : ↥M) * QuotientGroup.mk (⟨(r₀ : G), hr₀M⟩ : ↥M) := by
    rw [← QuotientGroup.mk_mul]
    rfl
  rw [e, act_mul_apply]
  exact (hc.mem_VtSub hS.model t).mpr hfin

theorem sec7_tame_comm_d3 (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h71 : Stroth71Statement) (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hK : Sec7CRWStatement) (h73a : Stroth73aStatement)
    (hStr : Stroth73cOm4Statement) : Step77TameCommNStatement 3 := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 htame hcardV
  classical
  haveI := hc.normal_Q_in_M
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS, ψ, hψ, hrange, hW, hinj, hA5, hA6⟩ :=
    sec7_A0 h34 h310chi hZc hZV hZcard hc hs hZ0
  have hg'M : g⁻¹ ∈ M := M.inv_mem hgM
  have hZK : Nat.card Z = Nat.card K := hS.card.symm
  have hVinter : Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) =
      conjSubgroup g⁻¹ (conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Vt M (LB M Q B) B Z t) := by
    rw [conjSubgroup_inf, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one, inf_comm]
  have hd3 : Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t)) =
      Nat.card K ^ (1 + 3) := by
    rw [hVinter, card_conjSubgroup, inf_comm, hcardV, hZK]
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hS.card.trans he)
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hu : g⁻¹ * t * (g⁻¹)⁻¹ ∈ M := M.mul_mem (M.mul_mem hg'M htM) (M.inv_mem hg'M)
  have hs1' : (g⁻¹ * t * (g⁻¹)⁻¹) * (g⁻¹ * t * (g⁻¹)⁻¹)⁻¹ ∈ Q := by
    rw [mul_inv_cancel]
    exact Q.one_mem
  obtain ⟨ψu, hψu, hrsu, hkeru⟩ := sec7_pair_psi hc M₀ ρ b hS ht ψ hψ hrange hg'M hu hs1'
  obtain ⟨hHcard, hUcard⟩ := sec7_Hset_card h34 hRoot hc hs hom M₀ ρ b hS
  obtain ⟨hc1, hd4, hdV⟩ := sec7_pair_card_meet hc M₀ ρ b hS hg'M ψu hrsu hUcard
  have hdim : Module.finrank K ↥(hc.VtSub hS.model t ⊓ LinearMap.range ψu) = 3 := by
    rw [hd3] at hc1
    have h1 := Nat.pow_right_injective hK2 hc1
    omega
  obtain ⟨r₀, hr₀, hh, hbU⟩ := sec7_exists_point_reverse h34 hRoot hc hs hom hZ0 M₀ ρ b hS ψ hψ
    hrange hW hgM (LinearMap.range ψu) hrsu (Or.inl hdim)
  have hnorm := sec7_CN_normalizes_LB_conj hc hs M₀ ρ b hS hh hbU
  exact sec7_tame_comm_of_normalizer h34 h310chi hZc hK h52a hA h71 h73a hZV hStr G M Q Z B hc n t
    hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 htame r₀ hr₀ hnorm

theorem sec7_tame_comm_d2 (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h71 : Stroth71Statement) (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hK : Sec7CRWStatement) (h73a : Stroth73aStatement)
    (hStr : Stroth73cOm4Statement) : Step77TameCommNStatement 2 := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 htame hcardV
  classical
  haveI := hc.normal_Q_in_M
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hguM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM htM) (M.inv_mem hgM)
  have hsM : s ∈ M := by
    have h1 : s = (s * (g * t * g⁻¹)⁻¹) * (g * t * g⁻¹) := by group
    rw [h1]
    exact M.mul_mem (hc.hyp.Q_normal.1 hs1) hguM
  have hg'M : g⁻¹ ∈ M := M.inv_mem hgM
  have hZV' : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  obtain ⟨K, fK, finK, γ, M₀, ρ, b, hS, ψ, hψ, hrange, hW, hinj, hA5, hA6⟩ :=
    sec7_A0 h34 h310chi hZc hZV hZcard hc hs hZ0
  haveI : CharP K 2 := by
    obtain ⟨e, -, he, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hS.card.trans he)
  haveI : Finite M₀.E := Module.finite_of_finite K
  have hK2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have hZK : Nat.card Z = Nat.card K := hS.card.symm
  obtain ⟨ψs, hψs, hrs, hker⟩ := sec7_pair_psi hc M₀ ρ b hS ht ψ hψ hrange hgM hsM hs1
  obtain ⟨hHcard, hUcard⟩ := sec7_Hset_card h34 hRoot hc hs hom M₀ ρ b hS
  obtain ⟨hc1, hd4, hdV⟩ := sec7_pair_card_meet hc M₀ ρ b hS hgM ψs hrs hUcard
  obtain ⟨hf, hr⟩ := sec7_model_form M₀
  have hk1 := sec7_ker_psi_eq_orth hc M₀ ρ b hS ψ hW
  have hvan := sec7_pair_vanish h71 hc hs hno hgM hs1 hs2
  have hddim : Module.finrank K ↥(hc.VtSub hS.model t ⊓ LinearMap.range ψs) = 2 := by
    rw [hcardV, hZK] at hc1
    have h1 : 1 + 2 = 1 + Module.finrank K ↥(hc.VtSub hS.model t ⊓ LinearMap.range ψs) :=
      Nat.pow_right_injective hK2 hc1
    omega
  have hfR : Module.finrank K (LinearMap.range ψs) = 4 := by
    have hcard : Nat.card (LinearMap.range ψs) = Nat.card K ^ 4 := by
      have h1 : Nat.card (LinearMap.range ψs) = Nat.card (M₀.img (conjSubgroup g
          (Vt M (LB M Q B) B Z t))) :=
        Nat.card_congr (Equiv.subtypeEquivRight hrs)
      rw [h1, sec7_card_img_conj hc M₀ ρ b hS hgM hZV']
      have h2 : Nat.card (M₀.img (Vt M (LB M Q B) B Z t)) =
          Nat.card (hc.VtSub hS.model t) := rfl
      rw [h2, hUcard]
    have h := Module.natCard_eq_pow_finrank (K := K) (V := LinearMap.range ψs)
    rw [hcard] at h
    exact (Nat.pow_right_injective hK2 h).symm
  have hmap := sec7_finrank_map_orthogonal M₀.B hf hr ψs hker (hc.VtSub hS.model t)
  rw [hddim, hfR] at hmap
  have hAle : (M₀.B.orthogonal (hc.VtSub hS.model t)).map ψs ≤
      hc.VtSub hS.model t ⊓ LinearMap.range ψs := by
    rintro _ ⟨e₀, he₀, rfl⟩
    refine ⟨?_, LinearMap.mem_range_self ψs _⟩
    obtain ⟨w, hwQ, rfl⟩ := M₀.π_surj e₀
    have hwW : w ∈ Wt Q (Vt M (LB M Q B) B Z t) := by
      refine (hW w hwQ).mpr ?_
      rw [← hk1] at he₀
      exact LinearMap.mem_ker.mp he₀
    rw [sec7_psi_apply_comm hc M₀ ρ b hS hsM ψs hψs hwQ]
    exact (hc.mem_VtSub hS.model t).mpr
      (M₀.pi_mem_img (htame w hwW) (sec7_comm_mem_Q hc hsM hwQ))
  have hAeq : (M₀.B.orthogonal (hc.VtSub hS.model t)).map ψs =
      hc.VtSub hS.model t ⊓ LinearMap.range ψs :=
    Submodule.eq_of_le_of_finrank_eq hAle (by rw [hmap, hddim])
  have hu : g⁻¹ * t * (g⁻¹)⁻¹ ∈ M := M.mul_mem (M.mul_mem hg'M htM) (M.inv_mem hg'M)
  have hs1' : (g⁻¹ * t * (g⁻¹)⁻¹) * (g⁻¹ * t * (g⁻¹)⁻¹)⁻¹ ∈ Q := by
    rw [mul_inv_cancel]
    exact Q.one_mem
  obtain ⟨ψu, hψu, hrsu, hkeru⟩ := sec7_pair_psi hc M₀ ρ b hS ht ψ hψ hrange hg'M hu hs1'
  obtain ⟨hc1u, hd4u, hdVu⟩ := sec7_pair_card_meet hc M₀ ρ b hS hg'M ψu hrsu hUcard
  have hVinter : Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) =
      conjSubgroup g⁻¹ (conjSubgroup g (Vt M (LB M Q B) B Z t) ⊓ Vt M (LB M Q B) B Z t) := by
    rw [conjSubgroup_inf, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one, inf_comm]
  have hd2 : Nat.card ↥(Vt M (LB M Q B) B Z t ⊓ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t)) =
      Nat.card K ^ (1 + 2) := by
    rw [hVinter, card_conjSubgroup, inf_comm, hcardV, hZK]
  have hdimu : Module.finrank K ↥(hc.VtSub hS.model t ⊓ LinearMap.range ψu) = 2 := by
    rw [hd2] at hc1u
    have h1 := Nat.pow_right_injective hK2 hc1u
    omega
  have hZS : Z ≤ conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t) := hc.Z_le_conjSubgroup hZV' hg'M
  have hconj : conjSubgroup g (conjSubgroup g⁻¹ (Vt M (LB M Q B) B Z t)) =
      Vt M (LB M Q B) B Z t := by
    rw [← conjSubgroup_mul, mul_inv_cancel, conjSubgroup_one]
  have hiso : ∀ c₁ ∈ hc.VtSub hS.model t ⊓ LinearMap.range ψu,
      ∀ c₂ ∈ hc.VtSub hS.model t ⊓ LinearMap.range ψu, ∀ a₂ : M₀.E,
        ψ a₂ = c₂ → M₀.B c₁ a₂ = 0 := by
    intro c₁ hc₁ c₂ hc₂ a₂ ha₂
    obtain ⟨σ, a, ha0, hsemi, hsim⟩ := sec7_nu_data hc M₀ ρ b hS hgM
    have hNmem : ∀ c ∈ hc.VtSub hS.model t ⊓ LinearMap.range ψu,
        (ρ (QuotientGroup.mk (⟨g, hgM⟩ : ↥M))).toAdd c ∈
          hc.VtSub hS.model t ⊓ LinearMap.range ψs := by
      intro c hc'
      refine ⟨?_, ?_⟩
      · have h1 := (hrsu c).mp hc'.2
        have h2 := (sec7_img_conj_iff hc M₀ ρ b hS hgM hZS c).mpr h1
        rw [hconj] at h2
        exact (hc.mem_VtSub hS.model t).mpr h2
      · have h1 := (hc.mem_VtSub hS.model t).mp hc'.1
        exact (hrs _).mpr ((sec7_img_conj_iff hc M₀ ρ b hS hgM hZV' c).mpr h1)
    have hmk : (QuotientGroup.mk (⟨g, hgM⟩ : ↥M) : Mbar M Q) *
        QuotientGroup.mk (⟨t, htM⟩ : ↥M) =
        QuotientGroup.mk (⟨s, hsM⟩ : ↥M) * QuotientGroup.mk (⟨g, hgM⟩ : ↥M) := by
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      refine QuotientGroup.eq.mpr (Subgroup.mem_subgroupOf.mpr ?_)
      have hq := (hc.conj_mem_Q_of_mem_M (M.inv_mem (M.mul_mem hgM htM))).1 _ hs1
      have e' : (⟨g, hgM⟩ * ⟨t, htM⟩ : ↥M)⁻¹ * (⟨s, hsM⟩ * ⟨g, hgM⟩ : ↥M) =
          ⟨(g * t)⁻¹ * (s * (g * t * g⁻¹)⁻¹) * ((g * t)⁻¹)⁻¹, M.mul_mem (M.mul_mem
            (M.inv_mem (M.mul_mem hgM htM)) (M.mul_mem hsM (M.inv_mem hguM)))
            (M.inv_mem (M.inv_mem (M.mul_mem hgM htM)))⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [e']
      exact hq
    have hNψ : ∀ e, (ρ (QuotientGroup.mk (⟨g, hgM⟩ : ↥M))).toAdd (ψ e) =
        ψs ((ρ (QuotientGroup.mk (⟨g, hgM⟩ : ↥M))).toAdd e) := by
      intro e
      have h1 : (ρ (QuotientGroup.mk (⟨g, hgM⟩ : ↥M))).toAdd
          ((ρ (QuotientGroup.mk (⟨t, htM⟩ : ↥M))).toAdd e) =
          (ρ (QuotientGroup.mk (⟨g, hgM⟩ : ↥M) * QuotientGroup.mk (⟨t, htM⟩ : ↥M))).toAdd e :=
        (act_mul_apply ρ _ _ e).symm
      have h2 : (ρ (QuotientGroup.mk (⟨s, hsM⟩ : ↥M))).toAdd
          ((ρ (QuotientGroup.mk (⟨g, hgM⟩ : ↥M))).toAdd e) =
          (ρ (QuotientGroup.mk (⟨s, hsM⟩ : ↥M) * QuotientGroup.mk (⟨g, hgM⟩ : ↥M))).toAdd e :=
        (act_mul_apply ρ _ _ e).symm
      rw [hψ e, hψs, map_sub, h1, h2, hmk]
    have hsH : s ∈ H0 M Z :=
      sec7_mem_H0_of_mul_Q hc (sec7_conj_mem_H0 hc hgM (hc.LB_le_H0 ht)) hs1
    have hsbar : (QuotientGroup.mk (⟨s, hsM⟩ : ↥M) : Mbar M Q) ∈ bar M Q (H0 M Z) :=
      Subgroup.mem_map.mpr ⟨⟨s, hsM⟩, Subgroup.mem_subgroupOf.mpr hsH, rfl⟩
    let Ss : M₀.E ≃ₗ[K] M₀.E :=
      AddEquiv.toLinearEquiv (ρ (QuotientGroup.mk (⟨s, hsM⟩ : ↥M))).toAdd (hS.lin _ hsbar)
    have hSsiso : ∀ x y, M₀.B (Ss x) (Ss y) = M₀.B x y := fun x y => hS.iso _ hsbar x y
    have hSsU : ∀ u ∈ hc.VtSub hS.model t, Ss u = u := by
      intro u hu
      obtain ⟨v, hvV, hvQ, rfl⟩ := M₀.mem_img.mp ((hc.mem_VtSub hS.model t).mp hu)
      have h1 := sec7_act_sub_comm hc M₀ ρ b hS hsM hvQ
      have h2 : M₀.π ⁅s, v⁆ = 0 :=
        (M₀.π_ker _ (sec7_comm_mem_Q hc hsM hvQ)).mpr (hvan v hvV)
      rw [h2] at h1
      exact sub_eq_zero.mp h1
    have hNc₁ := hNmem c₁ hc₁
    rw [← hAeq] at hNc₁
    obtain ⟨w₁, hw₁, hw₁e⟩ := Submodule.mem_map.mp hNc₁
    have hNc₂ := hNmem c₂ hc₂
    have hy : Ss ((ρ (QuotientGroup.mk (⟨g, hgM⟩ : ↥M))).toAdd a₂) -
        (ρ (QuotientGroup.mk (⟨g, hgM⟩ : ↥M))).toAdd a₂ ∈ hc.VtSub hS.model t := by
      have h1 : Ss ((ρ (QuotientGroup.mk (⟨g, hgM⟩ : ↥M))).toAdd a₂) -
          (ρ (QuotientGroup.mk (⟨g, hgM⟩ : ↥M))).toAdd a₂ =
          ψs ((ρ (QuotientGroup.mk (⟨g, hgM⟩ : ↥M))).toAdd a₂) := (hψs _).symm
      rw [h1, ← hNψ, ha₂]
      exact hNc₂.1
    have hw₁' : ∀ u ∈ hc.VtSub hS.model t, M₀.B u w₁ = 0 := fun u hu =>
      LinearMap.BilinForm.isOrtho_def.mp (LinearMap.BilinForm.mem_orthogonal_iff.mp hw₁ u hu)
    have key : M₀.B ((ρ (QuotientGroup.mk (⟨g, hgM⟩ : ↥M))).toAdd c₁)
        ((ρ (QuotientGroup.mk (⟨g, hgM⟩ : ↥M))).toAdd a₂) = 0 := by
      have h0 : (ρ (QuotientGroup.mk (⟨g, hgM⟩ : ↥M))).toAdd c₁ = Ss w₁ - w₁ := by
        rw [← hw₁e, hψs]
        rfl
      rw [h0]
      exact sec7_adjoint_zero M₀.B hr (hc.VtSub hS.model t) Ss hSsiso hSsU w₁ _ hw₁' hy
    have := hsim c₁ a₂
    rw [key] at this
    have h3 : σ (M₀.B c₁ a₂) = 0 := (mul_eq_zero.mp this.symm).resolve_left ha0
    exact σ.map_eq_zero_iff.mp h3
  obtain ⟨r₀, hr₀, hh, hbU⟩ := sec7_exists_point_reverse h34 hRoot hc hs hom hZ0 M₀ ρ b hS ψ hψ
    hrange hW hgM (LinearMap.range ψu) hrsu (Or.inr ⟨hdimu, hiso⟩)
  have hnorm := sec7_CN_normalizes_LB_conj hc hs M₀ ρ b hS hh hbU
  exact sec7_tame_comm_of_normalizer h34 h310chi hZc hK h52a hA h71 h73a hZV hStr G M Q Z B hc n t
    hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 htame r₀ hr₀ hnorm

theorem step77OneTameD2_of_inputs (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h71 : Stroth71Statement) (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hK : Sec7CRWStatement) (h73a : Stroth73aStatement)
    (hStr : Stroth73cOm4Statement) (hCV : Sec7CVStatement) (hIrr : Sec7VtIrredStatement) :
    Step77OneTameD2Statement := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 htame hcard
  exact sec7_tame_false_of_comm h34 hRoot h71 h310chi hZc hZV hZcard hCV hIrr 2 le_rfl
    (by norm_num) (sec7_tame_comm_d2 h34 hRoot h71 h310chi hZc hZV hZcard h52a hA hK h73a hStr)
    G M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 htame hcard

theorem step77OneTameD3_of_inputs (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h71 : Stroth71Statement) (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hK : Sec7CRWStatement) (h73a : Stroth73aStatement)
    (hStr : Stroth73cOm4Statement) (hCV : Sec7CVStatement) (hIrr : Sec7VtIrredStatement) :
    Step77OneTameD3Statement := by
  intro G _ _ M Q Z B hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 htame hcard
  exact sec7_tame_false_of_comm h34 hRoot h71 h310chi hZc hZV hZcard hCV hIrr 3 (by norm_num)
    le_rfl (sec7_tame_comm_d3 h34 hRoot h71 h310chi hZc hZV hZcard h52a hA hK h73a hStr) G M Q Z B
    hc n t hs hno hom Z0 hZ0 g hgM s hs1 hs2 hs3 htame hcard

theorem step77OneNotNorm_of_inputs (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h71 : Stroth71Statement) (h310chi : Stroth310ChiStatement) (hZc : Sec7CentreMpStatement)
    (hZV : Sec7ZVStatement) (hZcard : Sec7ZCardStatement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hSec : Sec7WVSecCardStatement) (hK : Sec7CRWStatement)
    (h73a : Stroth73aStatement) (hStr : Stroth73cOm4Statement) (hCV : Sec7CVStatement)
    (hIrr : Sec7VtIrredStatement) : Step77OneNotNormStatement :=
  step77OneNotNorm_of_cases h34 hRoot h310chi hZc hZV hZcard
    (step77OneWildCase_of_inputs h34 hRoot h71 h310chi hZc hZV hZcard h52a hA hSec)
    (step77OneTameD2_of_inputs h34 hRoot h71 h310chi hZc hZV hZcard h52a hA hK h73a hStr hCV hIrr)
    (step77OneTameD3_of_inputs h34 hRoot h71 h310chi hZc hZV hZcard h52a hA hK h73a hStr hCV hIrr)

end CFSG.RankThree.GF2n.Stroth80
