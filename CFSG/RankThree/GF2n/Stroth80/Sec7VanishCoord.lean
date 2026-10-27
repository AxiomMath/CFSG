module

public import CFSG.RankThree.GF2n.Stroth80.Sec7VanishLinAlg
public import CFSG.RankThree.GF2n.Stroth80.Sec7VanishHypPlane
public import CFSG.RankThree.GF2n.Stroth80.Sec7VanishIsom
public import CFSG.RankThree.GF2n.Stroth80.Sec7EndBridge
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaPoints
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaSingular

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank QuadraticMap
open CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem vanishPair_Fx_eq {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    (u w : ι → K) (Fx : (ι → K) →ₗ[K] (ι → K))
    (Ah Ar : Matrix ι ι K) (hAh : Ah *ᵥ u = w) (hAr : Ar *ᵥ w = Fx w) (c : K) :
    Fx (Ah *ᵥ (c • u)) = Ar *ᵥ (Ah *ᵥ (c • u)) := by
  rw [Matrix.mulVec_smul, hAh, map_smul, Matrix.mulVec_smul, hAr]


theorem vanishPair_coord (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (hnat : SpNat hc t ∨ OmegaNat hc t)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = Nat.card Z)
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι] {Q' : QuadraticForm K (ι → K)}
    {X : Subgroup (GL ι K)} (E : ElemMatrixIso Q' X) (hQ : (polarBilin Q').Nondegenerate)
    (h4 : 4 ≤ Module.finrank K (ι → K)) (hX : AddCommutantScalar X)
    (φ : ↥(Rt M (LB M Q B) t) →* GL ι K) (hφ : φ.range = X)
    (hker : φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t))
    [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (ι → K))
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
          (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    (hW : ∀ x y : ι → K, x ≠ 0 → y ≠ 0 → Q' x = 0 → Q' y = 0 →
      ∃ A ∈ X, (A : Matrix ι ι K) *ᵥ x = y)
    (hN : ∀ A : GL ι K, (∀ g ∈ X, A * g * A⁻¹ ∈ X) →
      ∃ c : K, c ≠ 0 ∧ ∀ v, Q' (c • ((A : Matrix ι ι K) *ᵥ v)) = Q' v)
    {x : G} (hxM : x ∈ M) (hxt : ⁅x, t⁆ ∈ Q) (hx2 : x ^ 2 ∈ Q)
    (Fx : (ι → K) →ₗ[K] (ι → K))
    (hFx : ∀ k k' : ↥(Vt M (LB M Q B) B Z t), (k' : G) = x * k * x⁻¹ →
      Fx (secVec ψ k) = secVec ψ k')
    (hG : ∃ k : G, k ∈ Vt M (LB M Q B) B Z t ∧ ∀ r ∈ Rt M (LB M Q B) t,
      ⁅x, k⁆ ∉ conjSubgroup r B ⊔ Z) :
    ∃ h ∈ Rt M (LB M Q B) t, ∃ r ∈ Rt M (LB M Q B) t,
      HypPlane Q Z (conjSubgroup h B) (conjSubgroup r (conjSubgroup h B)) t ∧
        conjSubgroup x (conjSubgroup h B) ⊔ Z = conjSubgroup r (conjSubgroup h B) ⊔ Z := by
  classical
  have ht : t ∈ LB M Q B := hs.mem
  have htM : t ∈ M := hc.LB_le_M ht
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hVR : ∀ y ∈ Rt M (LB M Q B) t, ∀ v ∈ Vt M (LB M Q B) B Z t,
      y * v * y⁻¹ ∈ Vt M (LB M Q B) B Z t := fun y hy v hv =>
    (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hy) v).mp hv
  have hxV : ∀ v ∈ Vt M (LB M Q B) B Z t, x * v * x⁻¹ ∈ Vt M (LB M Q B) B Z t := fun v hv =>
    (Subgroup.mem_normalizer_iff.mp
      (conjSubgroup_eq_self_iff.mp (endg_F0_Vt hc hxM hxt)) v).mp hv
  have hxR : ∀ y ∈ Rt M (LB M Q B) t, x * y * x⁻¹ ∈ Rt M (LB M Q B) t := fun y hy =>
    (Subgroup.mem_normalizer_iff.mp
      (conjSubgroup_eq_self_iff.mp (endg_F0_Rt hc hxM hxt)) y).mp hy
  have hRM : ∀ y ∈ Rt M (LB M Q B) t, y ∈ M := fun y hy => hc.Rt_le_M t hy
  have hVM : ∀ v ∈ Vt M (LB M Q B) B Z t, v ∈ Q := fun v hv => hVQ hv
  have hcommQV : ∀ v ∈ Vt M (LB M Q B) B Z t, ∀ q ∈ Q, ⁅q, v⁆ ∈ Z := fun v hv q hq =>
    Smith81.comm_mem_Z hc.hyp hq (hVM v hv)
  have hFFx : ∀ w, Fx (Fx w) = w := by
    intro w
    obtain ⟨k, rfl⟩ := exists_secVec_eq ψ w
    set k₁ : ↥(Vt M (LB M Q B) B Z t) := ⟨x * k * x⁻¹, hxV k k.2⟩ with hk₁
    set k₂ : ↥(Vt M (LB M Q B) B Z t) := ⟨x * k₁ * x⁻¹, hxV k₁ k₁.2⟩ with hk₂
    have e1 : Fx (secVec ψ k) = secVec ψ k₁ := hFx k k₁ rfl
    have e2 : Fx (secVec ψ k₁) = secVec ψ k₂ := hFx k₁ k₂ rfl
    rw [e1, e2, secVec_eq_iff]
    have e3 : (k₂ : G) * (k : G)⁻¹ = ⁅x ^ 2, (k : G)⁆ := by
      rw [hk₂, hk₁]
      simp only [commutatorElement_def, pow_two]
      group
    rw [e3]
    exact Smith81.comm_mem_Z hc.hyp hx2 (hVM k k.2)
  have hcompat : ∀ g ∈ X, ∃ g' ∈ X,
      ∀ w, Fx ((g : Matrix ι ι K) *ᵥ Fx w) = (g' : Matrix ι ι K) *ᵥ w := by
    intro g hg
    have hgR : g ∈ φ.range := by rw [hφ]; exact hg
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hgR
    have ha' : x * (a : G) * x⁻¹ ∈ Rt M (LB M Q B) t := hxR a a.2
    have ha'M : x * (a : G) * x⁻¹ ∈ M :=
      M.mul_mem (M.mul_mem hxM (hRM a a.2)) (M.inv_mem hxM)
    refine ⟨φ ⟨x * (a : G) * x⁻¹, ha'⟩, ?_, ?_⟩
    · rw [← hφ]
      exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    intro w
    obtain ⟨k, rfl⟩ := exists_secVec_eq ψ w
    have eL : Fx ((φ a : Matrix ι ι K) *ᵥ Fx (secVec ψ k)) =
        secVec ψ ⟨x * ((a : G) * (x * k * x⁻¹) * (a : G)⁻¹) * x⁻¹,
          hxV _ (hVR a a.2 _ (hxV k k.2))⟩ := by
      have e1 : Fx (secVec ψ k) = secVec ψ ⟨x * k * x⁻¹, hxV k k.2⟩ :=
        hFx k ⟨x * k * x⁻¹, hxV k k.2⟩ rfl
      rw [e1]
      have e2 : (φ a : Matrix ι ι K) *ᵥ secVec ψ ⟨x * k * x⁻¹, hxV k k.2⟩ =
          secVec ψ ⟨(a : G) * (x * k * x⁻¹) * (a : G)⁻¹, hVR a a.2 _ (hxV k k.2)⟩ :=
        (hψ a ⟨x * k * x⁻¹, hxV k k.2⟩ _ rfl).symm
      rw [e2]
      exact hFx _ _ rfl
    have eR : (φ ⟨x * (a : G) * x⁻¹, ha'⟩ : Matrix ι ι K) *ᵥ secVec ψ k =
        secVec ψ ⟨x * (a : G) * x⁻¹ * k * (x * (a : G) * x⁻¹)⁻¹, hVR _ ha' k k.2⟩ :=
      (hψ ⟨x * (a : G) * x⁻¹, ha'⟩ k _ rfl).symm
    rw [eL, eR, secVec_eq_iff]
    have hz : x * (a : G) * x⁻¹ * ⁅x ^ 2, (k : G)⁆ * (x * (a : G) * x⁻¹)⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 ha'M) _).mp
        (Smith81.comm_mem_Z hc.hyp hx2 (hVM k k.2))
    convert hz using 1
    simp only [commutatorElement_def, pow_two, Subgroup.coe_mk]
    group
  have iso : ∀ v, Q' (Fx v) = Q' v := vanishGeom_isometry_of_normalizer hQ hN Fx hFFx hcompat
  have hmemX : ∀ s : ↥(Rt M (LB M Q B) t), (φ s : GL ι K) ∈ X := fun s => by
    rw [← hφ]
    exact MonoidHom.mem_range.mpr ⟨s, rfl⟩
  have hisoφ : ∀ s : ↥(Rt M (LB M Q B) t), ∀ v,
      Q' ((φ s : Matrix ι ι K) *ᵥ v) = Q' v := fun s v => vanishGeom_isometry_of_mem E (hmemX s) v
  have hpolφ : ∀ s : ↥(Rt M (LB M Q B) t), ∀ v y,
      polar Q' ((φ s : Matrix ι ι K) *ᵥ v) ((φ s : Matrix ι ι K) *ᵥ y) = polar Q' v y := by
    intro s v y
    unfold QuadraticMap.polar
    rw [← Matrix.mulVec_add, hisoφ, hisoφ, hisoφ]
  have h3 : 3 ≤ Module.finrank K (ι → K) := by omega
  have hsing := hc.omega_singular h34 hRoot hs hnat hK E hQ h3 hX φ hφ ψ hψ
  obtain ⟨u, hQu, hu0, hBiff, -, -, hHyp⟩ :=
    hc.omega_points_core h34 hRoot hs hnat hK E hQ h3 hX φ hφ hker ψ hψ hsing
  have hu_vec : ∀ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B → ∃ c : K, secVec ψ b = c • u :=
    fun b hb => (hBiff (secVec ψ b)).mp ⟨b, hb, rfl⟩
  have hu_back : ∀ c : K, ∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = c • u :=
    fun c => (hBiff (c • u)).mpr ⟨c, rfl⟩
  set T : (ι → K) →ₗ[K] (ι → K) := Fx - LinearMap.id with hT
  have h2v : ∀ v : ι → K, v + v = 0 := fun v => by
    ext i
    simp [CharTwo.add_self_eq_zero]
  have hTw : ∀ w, T w = Fx w - w := fun w => rfl
  have hT2 : ∀ w, T (T w) = 0 := by
    intro w
    have e : T (T w) = Fx (Fx w - w) - (Fx w - w) := by rw [hTw, hTw]
    rw [e, map_sub, hFFx]
    rw [show w - Fx w - (Fx w - w) = (w + w) - (Fx w + Fx w) by abel, h2v, h2v, sub_self]
  have hTiso : ∀ w, Q' (w + T w) = Q' w := by
    intro w
    rw [hTw, show w + (Fx w - w) = Fx w by abel, iso]
  have hnzT : ∃ v, Q' (T v) ≠ 0 := by
    obtain ⟨k, hkV, hkG⟩ := hG
    have hk1 : x * k * x⁻¹ ∈ Vt M (LB M Q B) B Z t := hxV k hkV
    let kV : ↥(Vt M (LB M Q B) B Z t) := ⟨k, hkV⟩
    let k₁ : ↥(Vt M (LB M Q B) B Z t) := ⟨x * k * x⁻¹, hk1⟩
    let cV : ↥(Vt M (LB M Q B) B Z t) :=
      ⟨x * k * x⁻¹ * k⁻¹, (Vt M (LB M Q B) B Z t).mul_mem hk1
        ((Vt M (LB M Q B) B Z t).inv_mem hkV)⟩
    have hTc : T (secVec ψ kV) = secVec ψ cV := by
      have e : cV = k₁ * kV⁻¹ := Subtype.ext (by simp [cV, k₁, kV, mul_assoc])
      rw [e, secVec_mul, secVec_inv, hTw, hFx kV k₁ rfl, sub_eq_add_neg]
    refine ⟨secVec ψ kV, ?_⟩
    rw [hTc]
    intro h0
    by_cases hcz : secVec ψ cV = 0
    · have hz : (cV : G) ∈ Z := (secVec_eq_zero_iff ψ cV).mp hcz
      apply hkG 1 (Subgroup.one_mem _)
      rw [commutatorElement_def]
      exact Subgroup.mem_sup_right hz
    · obtain ⟨A, hAX, hAu⟩ := hW u (secVec ψ cV) hu0 hcz hQu h0
      have hAφ : A ∈ φ.range := by rw [hφ]; exact hAX
      obtain ⟨r₀, hr₀⟩ := MonoidHom.mem_range.mp hAφ
      obtain ⟨b₀, hb₀, hb₀v⟩ := hu_back 1
      have hdV : (r₀ : G) * (b₀ : G) * (r₀ : G)⁻¹ ∈ Vt M (LB M Q B) B Z t :=
        hVR r₀ r₀.2 b₀ (hBV hb₀)
      let dV : ↥(Vt M (LB M Q B) B Z t) := ⟨(r₀ : G) * b₀ * (r₀ : G)⁻¹, hdV⟩
      have hd : secVec ψ dV = (φ r₀ : Matrix ι ι K) *ᵥ secVec ψ b₀ := hψ r₀ b₀ dV rfl
      have hdvec : secVec ψ dV = secVec ψ cV := by
        rw [hd, hb₀v, one_smul, hr₀, hAu]
      have hz : (cV : G) * (dV : G)⁻¹ ∈ Z := (secVec_eq_iff ψ cV dV).mp hdvec.symm
      have hdB : (dV : G) ∈ conjSubgroup (r₀ : G) B := by
        rw [mem_conjSubgroup]
        have e2 : (r₀ : G)⁻¹ * (dV : G) * (r₀ : G) = b₀ := by
          simp only [dV]
          group
        rw [e2]
        exact hb₀
      have e3 : ⁅x, k⁆ = ((cV : G) * (dV : G)⁻¹) * (dV : G) := by
        simp only [cV, dV, commutatorElement_def]
        group
      apply hkG r₀ r₀.2
      rw [e3]
      exact (conjSubgroup (r₀ : G) B ⊔ Z).mul_mem (Subgroup.mem_sup_right hz)
        (Subgroup.mem_sup_left hdB)
  obtain ⟨w, hwQ, hwpol⟩ := vanishLA_exists_singular_polar hQ h4 hT2 hTiso hnzT
  have hw0 : w ≠ 0 := by
    rintro rfl
    apply hwpol
    rw [map_zero, polar_zero_right]
  obtain ⟨Ah, hAhX, hAhu⟩ := hW u w hu0 hw0 hQu hwQ
  have hAhφ : Ah ∈ φ.range := by rw [hφ]; exact hAhX
  obtain ⟨h₁, hh₁⟩ := MonoidHom.mem_range.mp hAhφ
  have hh₁u : (φ h₁ : Matrix ι ι K) *ᵥ u = w := by rw [hh₁]; exact hAhu
  have hFw0 : Fx w ≠ 0 := fun h0 => hw0 (by rw [← hFFx w, h0, map_zero])
  obtain ⟨Ar, hArX, hArw⟩ := hW w (Fx w) hw0 hFw0 hwQ (by rw [iso w, hwQ])
  have hArφ : Ar ∈ φ.range := by rw [hφ]; exact hArX
  obtain ⟨r₁, hr₁⟩ := MonoidHom.mem_range.mp hArφ
  have hr₁w : (φ r₁ : Matrix ι ι K) *ᵥ w = Fx w := by rw [hr₁]; exact hArw
  have hps : polar Q' w w = 0 := by rw [polar_self, CharTwo.two_nsmul]
  have hhbV : ∀ b ∈ B, (h₁ : G) * b * (h₁ : G)⁻¹ ∈ Vt M (LB M Q B) B Z t := fun b hb =>
    hVR h₁ h₁.2 b (hBV hb)
  have hxhbV : ∀ b ∈ B, x * ((h₁ : G) * b * (h₁ : G)⁻¹) * x⁻¹ ∈ Vt M (LB M Q B) B Z t :=
    fun b hb => hxV _ (hhbV b hb)
  have hrhbV : ∀ b ∈ B, (r₁ : G) * ((h₁ : G) * b * (h₁ : G)⁻¹) * (r₁ : G)⁻¹ ∈
      Vt M (LB M Q B) B Z t := fun b hb => hVR r₁ r₁.2 _ (hhbV b hb)
  have hkey : ∀ (b : G) (hb : b ∈ B), secVec ψ ⟨x * ((h₁ : G) * b * (h₁ : G)⁻¹) * x⁻¹,
      hxhbV b hb⟩ = secVec ψ ⟨(r₁ : G) * ((h₁ : G) * b * (h₁ : G)⁻¹) * (r₁ : G)⁻¹,
      hrhbV b hb⟩ := by
    intro b hb
    obtain ⟨c, hc'⟩ := hu_vec ⟨b, hBV hb⟩ hb
    have e1 : secVec ψ ⟨x * ((h₁ : G) * b * (h₁ : G)⁻¹) * x⁻¹, hxhbV b hb⟩ =
        Fx (secVec ψ ⟨(h₁ : G) * b * (h₁ : G)⁻¹, hhbV b hb⟩) :=
      (hFx ⟨(h₁ : G) * b * (h₁ : G)⁻¹, hhbV b hb⟩ ⟨x * ((h₁ : G) * b * (h₁ : G)⁻¹) * x⁻¹,
        hxhbV b hb⟩ rfl).symm
    have e2 : secVec ψ ⟨(h₁ : G) * b * (h₁ : G)⁻¹, hhbV b hb⟩ =
        (φ h₁ : Matrix ι ι K) *ᵥ secVec ψ ⟨b, hBV hb⟩ :=
      hψ h₁ ⟨b, hBV hb⟩ ⟨(h₁ : G) * b * (h₁ : G)⁻¹, hhbV b hb⟩ rfl
    have e3 : secVec ψ ⟨(r₁ : G) * ((h₁ : G) * b * (h₁ : G)⁻¹) * (r₁ : G)⁻¹, hrhbV b hb⟩ =
        (φ r₁ : Matrix ι ι K) *ᵥ secVec ψ ⟨(h₁ : G) * b * (h₁ : G)⁻¹, hhbV b hb⟩ :=
      hψ r₁ ⟨(h₁ : G) * b * (h₁ : G)⁻¹, hhbV b hb⟩ ⟨(r₁ : G) * ((h₁ : G) * b * (h₁ : G)⁻¹) *
        (r₁ : G)⁻¹, hrhbV b hb⟩ rfl
    rw [e1, e3, e2, hc']
    exact vanishPair_Fx_eq u w Fx _ _ hh₁u hr₁w c
  have hsecond : conjSubgroup x (conjSubgroup (h₁ : G) B) ⊔ Z =
      conjSubgroup (r₁ : G) (conjSubgroup (h₁ : G) B) ⊔ Z := by
    apply le_antisymm
    · apply sup_le
      · intro c hcmem
        obtain ⟨b, hbB, rfl⟩ : ∃ b, b ∈ B ∧
            c = x * ((h₁ : G) * b * (h₁ : G)⁻¹) * x⁻¹ :=
          ⟨(h₁ : G)⁻¹ * (x⁻¹ * c * x) * (h₁ : G),
            mem_conjSubgroup.mp (mem_conjSubgroup.mp hcmem), by group⟩
        have hk := hkey b hbB
        have hb2 : (h₁ : G)⁻¹ * ((r₁ : G)⁻¹ * ((r₁ : G) * ((h₁ : G) * b * (h₁ : G)⁻¹) *
            (r₁ : G)⁻¹) * (r₁ : G)) * (h₁ : G) ∈ B := by
          have e : (h₁ : G)⁻¹ * ((r₁ : G)⁻¹ * ((r₁ : G) * ((h₁ : G) * b * (h₁ : G)⁻¹) *
              (r₁ : G)⁻¹) * (r₁ : G)) * (h₁ : G) = b := by group
          rw [e]
          exact hbB
        have hw : (r₁ : G) * ((h₁ : G) * b * (h₁ : G)⁻¹) * (r₁ : G)⁻¹ ∈
            conjSubgroup (r₁ : G) (conjSubgroup (h₁ : G) B) ⊔ Z :=
          Subgroup.mem_sup_left (mem_conjSubgroup.mpr (mem_conjSubgroup.mpr hb2))
        exact mem_of_secVec_eq le_sup_right ψ hw hk.symm
      · exact le_sup_right
    · apply sup_le
      · intro d hdmem
        obtain ⟨b, hbB, rfl⟩ : ∃ b, b ∈ B ∧
            d = (r₁ : G) * ((h₁ : G) * b * (h₁ : G)⁻¹) * (r₁ : G)⁻¹ :=
          ⟨(h₁ : G)⁻¹ * ((r₁ : G)⁻¹ * d * (r₁ : G)) * (h₁ : G),
            mem_conjSubgroup.mp (mem_conjSubgroup.mp hdmem), by group⟩
        have hk := hkey b hbB
        have hb2 : (h₁ : G)⁻¹ * (x⁻¹ * (x * ((h₁ : G) * b * (h₁ : G)⁻¹) * x⁻¹) * x) *
            (h₁ : G) ∈ B := by
          have e : (h₁ : G)⁻¹ * (x⁻¹ * (x * ((h₁ : G) * b * (h₁ : G)⁻¹) * x⁻¹) * x) *
              (h₁ : G) = b := by group
          rw [e]
          exact hbB
        have hw : x * ((h₁ : G) * b * (h₁ : G)⁻¹) * x⁻¹ ∈
            conjSubgroup x (conjSubgroup (h₁ : G) B) ⊔ Z :=
          Subgroup.mem_sup_left (mem_conjSubgroup.mpr (mem_conjSubgroup.mpr hb2))
        exact mem_of_secVec_eq le_sup_right ψ hw hk
      · exact le_sup_right
  have hHyp1 : HypPlane Q Z (conjSubgroup (h₁ : G) B)
      (conjSubgroup (r₁ : G) (conjSubgroup (h₁ : G) B)) t := by
    rw [← conjSubgroup_mul, hypPlane_conj_R hc ht h₁.2 r₁.2]
    let k₁ : ↥(Rt M (LB M Q B) t) := h₁⁻¹ * r₁ * h₁
    refine (hHyp k₁).1.mpr ?_
    have hφk : (φ k₁ : Matrix ι ι K) *ᵥ u = (((φ h₁)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ Fx w := by
      have e : (φ k₁ : GL ι K) = (φ h₁)⁻¹ * (φ r₁ * φ h₁) := by
        simp only [k₁, map_mul, map_inv, mul_assoc]
      rw [e, Units.val_mul, ← Matrix.mulVec_mulVec, Units.val_mul, ← Matrix.mulVec_mulVec,
        hh₁u, hr₁w]
    have hinv : ∀ z : ι → K,
        (φ h₁ : Matrix ι ι K) *ᵥ (((φ h₁)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ z = z := by
      intro z
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
        Matrix.one_mulVec]
    have key : polar Q' u ((((φ h₁)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ Fx w) = polar Q' w (T w) := by
      calc polar Q' u ((((φ h₁)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ Fx w)
          = polar Q' ((φ h₁ : Matrix ι ι K) *ᵥ u)
              ((φ h₁ : Matrix ι ι K) *ᵥ ((((φ h₁)⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ Fx w)) :=
            (hpolφ h₁ u _).symm
        _ = polar Q' w (Fx w) := by rw [hh₁u, hinv]
        _ = polar Q' w (T w) := by
          rw [show Fx w = T w + w by rw [hTw]; abel, polar_add_right, hps, add_zero]
    rw [hφk, key]
    exact hwpol
  exact ⟨(h₁ : G), h₁.2, (r₁ : G), r₁.2, hHyp1, hsecond⟩

end CFSG.RankThree.GF2n.Stroth80
