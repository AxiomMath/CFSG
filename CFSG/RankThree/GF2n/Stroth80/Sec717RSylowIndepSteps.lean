module

public import CFSG.RankThree.GF2n.Stroth80.Sec717Layers
public import CFSG.RankThree.GF2n.Stroth80.Sec713O2Split
import CFSG.RankThree.GF2n.Stroth80.Sec7TailCaseOneBar

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

section Flag

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] {T P : Submodule K E}

theorem IsLayerLowering.pow_four_eq_one [CharP K 2] {a : E ≃ₗ[K] E}
    (ha : IsLayerLowering T P (opm a)) : a ^ 4 = 1 := by
  have h2 : ∀ v : E, v + v = 0 := fun v => by
    rw [← two_smul K v, CharTwo.two_eq_zero, zero_smul]
  have hsq : ∀ (b : E ≃ₗ[K] E) (x : E), opm (b * b) x = opm b (opm b x) := fun b x => by
    rw [opm_mul_apply_layer, h2, zero_add]
  have e : a ^ 4 = (a * a) * (a * a) := by
    rw [show a ^ 4 = (a ^ 2) ^ 2 by rw [← pow_mul], sq, sq]
  apply eq_one_of_opm_eq_zero
  intro x
  rw [e, hsq, hsq, hsq]
  exact ha.comp_comp ha ha _

theorem mem_pCore_two_of_isLayerLowering [CharP K 2] {X : Type*} [Group X]
    (φ : X →* (E ≃ₗ[K] E)) (hinj : Function.Injective φ) (hTP : T ≤ P) {Kb : Subgroup X}
    (hKT : ∀ k ∈ Kb, ∀ w ∈ T, φ k w ∈ T) (hKP : ∀ k ∈ Kb, ∀ w ∈ P, φ k w ∈ P)
    {x : X} (hx : x ∈ Kb) (hlow : IsLayerLowering T P (opm (φ x))) :
    (⟨x, hx⟩ : ↥Kb) ∈ pCore 2 ↥Kb := by
  have hone : IsLayerLowering T P (opm (φ 1)) := by
    rw [map_one]
    exact ⟨fun e => by simp [opm_apply], fun e _ => by simp [opm_apply],
      fun e _ => by simp [opm_apply]⟩
  let U : Subgroup ↥Kb :=
    { carrier := {y | IsLayerLowering T P (opm (φ (y : X)))}
      mul_mem' := fun {a b} ha hb => by
        show IsLayerLowering T P (opm (φ ((a : X) * (b : X))))
        rw [map_mul]
        exact IsLayerLowering.opm_mul hTP ha hb
      one_mem' := hone
      inv_mem' := fun {a} ha => by
        show IsLayerLowering T P (opm (φ ((a : X))⁻¹))
        rw [map_inv]
        exact IsLayerLowering.opm_inv hTP ha }
  have hUn : U.Normal := by
    refine ⟨fun y hy k => ?_⟩
    show IsLayerLowering T P (opm (φ ((k : X) * (y : X) * (k : X)⁻¹)))
    rw [map_mul, map_mul, map_inv]
    refine IsLayerLowering.conj (hKT k k.2) (hKP k k.2) (fun w hw => ?_) (fun w hw => ?_) hy
    · rw [← map_inv]
      exact hKT _ (Kb.inv_mem k.2) w hw
    · rw [← map_inv]
      exact hKP _ (Kb.inv_mem k.2) w hw
  have hU2 : IsPGroup 2 ↥U := by
    intro y
    have hy : IsLayerLowering T P (opm (φ ((y : ↥Kb) : X))) := y.2
    have h4 : φ (((y : ↥Kb) : X) ^ 4) = φ 1 := by
      rw [map_pow, map_one]
      exact hy.pow_four_eq_one
    refine ⟨2, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    simpa using hinj h4
  have hle : U ≤ pCore 2 ↥Kb := by
    unfold pCore
    exact le_sSup ⟨hUn, hU2⟩
  exact hle (show (⟨x, hx⟩ : ↥Kb) ∈ U from hlow)

end Flag

section Sylow

variable {X K E : Type*} [Group X] [Field K] [AddCommGroup E] [Module K E]

theorem mem_of_isPGroup_of_agree (φ : X →* (E ≃ₗ[K] E)) (T : Submodule K E)
    {Nb Rb Kb : Subgroup X} (hNR : Nb ≤ Rb) (hN2 : IsPGroup 2 ↥Nb) (hRK : Rb ≤ Kb)
    (hKR : ∀ k ∈ Kb, k ∈ Subgroup.normalizer (Rb : Set X))
    (hfix : ∀ r ∈ Rb, (∀ w ∈ T, φ r w = w) → r ∈ Nb)
    (h4 : ∀ c ∈ Kb, IsPGroup 2 ↥(Subgroup.zpowers c) → (∀ w ∈ T, φ c w = w) → c ∈ Nb)
    {s : X} (hsK : s ∈ Kb) (hs2 : IsPGroup 2 ↥(Subgroup.zpowers s)) {r : X} (hr : r ∈ Rb)
    (hsr : ∀ w ∈ T, φ s w = φ r w) : s ∈ Rb := by
  obtain ⟨c, rfl⟩ : ∃ c, s = r * c := ⟨r⁻¹ * s, (mul_inv_cancel_left r s).symm⟩
  have hcK : c ∈ Kb := by
    have h := Kb.mul_mem (Kb.inv_mem (hRK hr)) hsK
    rwa [inv_mul_cancel_left] at h
  have hcT : ∀ w ∈ T, φ c w = w := fun w hw => by
    have h := hsr w hw
    rw [map_mul, LinearEquiv.mul_apply] at h
    exact (φ r).injective h
  have hcTpow : ∀ (k : ℕ), ∀ w ∈ T, φ (c ^ k) w = w := by
    intro k
    induction k with
    | zero => intro w _; simp
    | succ k ih =>
      intro w hw
      rw [pow_succ, map_mul, LinearEquiv.mul_apply, hcT w hw, ih w hw]
  have hpow : ∀ k : ℕ, ∃ ρ ∈ Rb, (r * c) ^ k = ρ * c ^ k := by
    intro k
    induction k with
    | zero => exact ⟨1, Rb.one_mem, by simp⟩
    | succ k ih =>
      obtain ⟨ρ, hρ, hk⟩ := ih
      have hconj : c ^ k * r * (c ^ k)⁻¹ ∈ Rb :=
        (Subgroup.mem_normalizer_iff.mp (hKR _ (Kb.pow_mem hcK k)) r).mp hr
      refine ⟨ρ * (c ^ k * r * (c ^ k)⁻¹), Rb.mul_mem hρ hconj, ?_⟩
      rw [pow_succ, hk, pow_succ]
      group
  obtain ⟨a, ha⟩ := hs2 ⟨r * c, Subgroup.mem_zpowers _⟩
  have hsa : (r * c) ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  obtain ⟨ρ, hρ, hk⟩ := hpow (2 ^ a)
  rw [hsa] at hk
  have hcR : c ^ 2 ^ a ∈ Rb := by
    rw [eq_inv_of_mul_eq_one_right hk.symm]
    exact Rb.inv_mem hρ
  have hcN : c ^ 2 ^ a ∈ Nb := hfix _ hcR (hcTpow _)
  obtain ⟨b, hb⟩ := hN2 ⟨_, hcN⟩
  have hcb : (c ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
  have hcab : c ^ 2 ^ (a + b) = 1 := by rw [pow_add, pow_mul, hcb]
  have hc2 : IsPGroup 2 ↥(Subgroup.zpowers c) := by
    rintro ⟨y, hy⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨a + b, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcab, one_zpow]
  exact Rb.mul_mem hr (hNR (h4 c hcK hc2 hcT))

end Sylow

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

theorem Ctx.rSylow_of_layerSteps (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (h78 : Stroth78Statement) (hZV : Sec7ZVStatement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hCent : Sec715CentStatement) (hHard : Step713O2HardStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t)
    (hp3 : OmegaPlusNat hc t 3) {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q)
    (hZNc : IsCentrePre Z0 (hc.CN t) Q)
    (hTI : ∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G))
    {L : Subgroup G} (hL : Sec717L hc t Z0 L) (hLn : ∀ k ∈ NormH0 M Z Z0, conjSubgroup k L = L)
    {K : Type} [Field K] [Finite K] {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ)
    (hM : GlobalModelData M Q Z γ M₀) (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x))
    (T : Submodule K M₀.E)
    (hT : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.range (opm (φ a)) = T)
    (h2 : ∀ s ∈ (bar M Q (NormH0 M Z Z0)).subgroupOf (bar M Q (H0 M Z)),
      IsPGroup 2 ↥(Subgroup.zpowers s) →
        ∃ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
          ∀ w ∈ T, φ s w = φ r w)
    (h4mid : ∀ c ∈ (bar M Q (NormH0 M Z Z0)).subgroupOf (bar M Q (H0 M Z)),
      IsPGroup 2 ↥(Subgroup.zpowers c) → (∀ w ∈ T, φ c w = w) →
        ∀ w ∈ M₀.B.orthogonal T, opm (φ c) w ∈ T) :
    ∃ S : Sylow 2 ↥(bar M Q (H0 M Z)),
      (S : Subgroup ↥(bar M Q (H0 M Z))) ≤
        (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)) := by
  have LD := hc.sec717LayerData h34 h311a hZt hZcard hZc h78 hZV h52a hA hs hp3 hZ0 hZNc hTI hL
    hLn M₀ hM φ hφπ T hT
  have Bs := Ctx.yBase h34 h311a hZt hZcard hZc h78 hc hs hp3 hZ0 hZNc hTI hL hLn
  have hn4 : ¬ OmegaPlusNat hc t 4 := fun h => by have := hp3.eq_of_plus h; omega
  have hC : CentTwoInV hc t Z0 := fun k _ hk2 hkc =>
    hCent G M Q Z B hc n t hs (Or.inl hp3) Z0 hZ0 hZNc k hk2 hkc
  obtain ⟨S, hS⟩ := hc.ySylow hs hZ0 hZt hZcard (sec7_CN_pgroup_bar h34 h311a hc hs) hTI hC
  obtain ⟨e', -, he, -⟩ := hc.hyp.cp
  haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hM.card.trans he)
  obtain ⟨a₀, ha₀V, ha₀1⟩ := LD.V_ne
  have hKT : ∀ k ∈ (bar M Q (NormH0 M Z Z0)).subgroupOf (bar M Q (H0 M Z)),
      ∀ w ∈ T, φ k w ∈ T := by
    intro k hk w hw
    have hkV : k * a₀ * k⁻¹ ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := by
      have hkN := hk
      rw [Bs.K_eq] at hkN
      exact (Subgroup.mem_normalizer_iff.mp hkN a₀).mp ha₀V
    have hka1 : k * a₀ * k⁻¹ ≠ 1 := fun h => ha₀1 (by
      have e : a₀ = k⁻¹ * (k * a₀ * k⁻¹) * k := by group
      rw [e, h]
      group)
    rw [← LD.range_V a₀ ha₀V ha₀1] at hw
    obtain ⟨e, rfl⟩ := hw
    rw [← LD.range_V _ hkV hka1]
    refine ⟨φ k e, ?_⟩
    rw [opm_conj, phi_inv_apply_phi]
  have hKP : ∀ k ∈ (bar M Q (NormH0 M Z Z0)).subgroupOf (bar M Q (H0 M Z)),
      ∀ w ∈ M₀.B.orthogonal T, φ k w ∈ M₀.B.orthogonal T := by
    intro k hk w hw
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have hu' : φ k⁻¹ u ∈ T := hKT k⁻¹ (Subgroup.inv_mem _ hk) u hu
    have e : u = φ k (φ k⁻¹ u) := (phi_apply_inv_apply φ k u).symm
    rw [e, LD.isom]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hw) _ hu'
  have h4 : ∀ c ∈ (bar M Q (NormH0 M Z Z0)).subgroupOf (bar M Q (H0 M Z)),
      IsPGroup 2 ↥(Subgroup.zpowers c) → (∀ w ∈ T, φ c w = w) →
        c ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) := by
    intro c hcK hc2 hcT
    have hlow : IsLayerLowering T (M₀.B.orthogonal T) (opm (φ c)) :=
      ⟨fun e => by
          rw [opm_apply]
          exact sub_mem_orthogonal_of_fixes M₀.B (φ c) (LD.isom c) T hcT e,
        h4mid c hcK hc2 hcT, fun w hw => by rw [opm_apply, hcT w hw, sub_self]⟩
    have hpc := mem_pCore_two_of_isLayerLowering φ LD.inj LD.T_le hKT hKP hcK hlow
    exact Subgroup.mem_subgroupOf.mp (hHard G M Q Z B hc n t hs hn4 Z0 hZ0 hpc)
  refine ⟨S, fun s hsS => ?_⟩
  have hsK := hS hsS
  have hs2 : IsPGroup 2 ↥(Subgroup.zpowers s) :=
    S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hsS)
  obtain ⟨r, hr, hsr⟩ := h2 s hsK hs2
  exact mem_of_isPGroup_of_agree φ T Bs.NR Bs.N2 Bs.RK Bs.Rn LD.Rb_fix h4 hsK hs2 hr hsr

end CFSG.RankThree.GF2n.Stroth80
