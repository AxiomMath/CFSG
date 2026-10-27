module

public import CFSG.Quasithin.Vol2.Ch11G2Q8LeviG2

public section

namespace CFSG.Quasithin.Vol2.Ch11.G2Q8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.KGNat Matrix

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem norm_add_smul_one {x : quasithinZorn F} (hx : cayleyTr x = 0) (r : F) :
    cayleyNorm (x + r • cayleyOne F) = cayleyNorm x + r * r := by
  rw [zorn_eta x] at hx ⊢
  rw [cayleyOne_eq, zmk_smul, zmk_add, cayleyNorm_zmk, cayleyNorm_zmk]
  rw [cayleyTr_zmk] at hx
  linear_combination r * hx

omit [CharP F 2] in
theorem norm_zI_F3 {w : Ix3 → F} (hw : w ∈ stdF F 3) : cayleyNorm (zI w) = 0 := by
  obtain ⟨h1, h2, h3⟩ := mem_stdF_three.mp hw
  rw [q6_eta w, zI_q6, cayleyNorm_zmk, h1, h2, h3]
  ring

theorem cgE_zI_of_norm {g : ↥(cayleyGroup F)} {w : Ix3 → F} (hw : cayleyNorm (zI w) = 0)
    (hgw : cayleyNorm (zI (g2Act g w)) = 0) : cgE g (zI w) = zI (g2Act g w) := by
  have h1 := g2_zI_eq g w
  have hn := cg_norm g (zI w)
  rw [h1, norm_add_smul_one (cayleyTr_zI _), hgw, hw, zero_add] at hn
  have hr : (cgE g (zI w)).1 = 0 := mul_self_eq_zero.mp hn
  rw [h1, hr, zero_smul, add_zero]

omit [CharP F 2] in
theorem mul_zI_F3 (a e f a' e' f' : F) :
    cayleyMul (zI (q6 a 0 0 0 e f)) (zI (q6 a' 0 0 0 e' f')) = (e * f' - f * e') • zU0 F := by
  rw [zI_q6, zI_q6, cayleyMul_zmk, zU0, zmk_smul]
  apply zmk_congr <;> ring

omit [CharP F 2] in
theorem mul_zU0_zI (w : Ix3 → F) :
    cayleyMul (zU0 F) (zI w) = zmk (w (.inr 0)) 0 0 0 0 (-(w (.inl 2))) (w (.inl 1)) 0 := by
  conv_lhs => rw [q6_eta w]
  rw [zI_q6, mul_zU0_left]

omit [CharP F 2] in
theorem mul_smul_zU0 (c r : F) (w : Ix3 → F) :
    cayleyMul (c • zU0 F) (zI w + r • cayleyOne F) =
      zmk (c * w (.inr 0)) (r * c) 0 0 0 (-(c * w (.inl 2))) (c * w (.inl 1)) 0 := by
  conv_lhs => rw [q6_eta w]
  rw [zI_q6, zU0, cayleyOne_eq, zmk_smul, zmk_smul, zmk_add, cayleyMul_zmk]
  apply zmk_congr <;> ring

omit [CharP F 2] in
theorem zI_eu : zI (eu 0 (1 : F)) = zU0 F := by
  rw [eu_eq_q6, zI_q6]
  rfl

omit [CharP F 2] in
theorem zP_zU0 : zP (zU0 F) = eu 0 (1 : F) := by
  rw [zU0, zP_zmk, eu_eq_q6]

theorem stabQ_three_le_one : stabQ (stdF F 3) ≤ stabQ (stdF F 1) := by
  have key : ∀ g ∈ stabQ (stdF F 3), g2Act g (eu 0 1) ∈ stdF F 1 := by
    intro g hg
    have hv1 : q6 (0 : F) 0 0 0 1 0 ∈ stdF F 3 := mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩
    have hv2 : q6 (0 : F) 0 0 0 0 1 ∈ stdF F 3 := mem_stdF_three.mpr ⟨rfl, rfl, rfl⟩
    have ha := (mem_stabQ.mp hg _).mp hv1
    have hb := (mem_stabQ.mp hg _).mp hv2
    have hza := cgE_zI_of_norm (norm_zI_F3 hv1) (norm_zI_F3 ha)
    have hzb := cgE_zI_of_norm (norm_zI_F3 hv2) (norm_zI_F3 hb)
    have h1 : zU0 F = cayleyMul (zI (q6 0 0 0 0 1 0)) (zI (q6 0 0 0 0 0 1)) := by
      rw [mul_zI_F3]
      simp
    have h2 : cgE g (zU0 F) = cayleyMul (zI (g2Act g (q6 0 0 0 0 1 0)))
        (zI (g2Act g (q6 0 0 0 0 0 1))) := by
      rw [h1, cg_mul, hza, hzb]
    obtain ⟨a1, a2, a3⟩ := mem_stdF_three.mp ha
    obtain ⟨b1, b2, b3⟩ := mem_stdF_three.mp hb
    rw [q6_eta (g2Act g (q6 0 0 0 0 1 0)), q6_eta (g2Act g (q6 0 0 0 0 0 1)), a1, a2, a3, b1,
      b2, b3, mul_zI_F3] at h2
    rw [g2Act_apply, zI_eu, h2, zP_smul, zP_zU0]
    exact (stdF F 1).smul_mem _ (mem_stdF_one_iff.mpr ⟨1, (one_smul _ _).symm⟩)
  intro g hg
  refine mem_stabQ.mpr fun w => ⟨fun hw => ?_, fun hw => ?_⟩
  · obtain ⟨t, rfl⟩ := mem_stdF_one_iff.mp hw
    rw [g2Act_smul]
    exact (stdF F 1).smul_mem t (key g hg)
  · obtain ⟨t, ht⟩ := mem_stdF_one_iff.mp hw
    rw [← g2Act_inv_apply g w, ht, g2Act_smul]
    exact (stdF F 1).smul_mem t (key g⁻¹ ((stabQ (stdF F 3)).inv_mem hg))

theorem stabQ_one_le_three : stabQ (stdF F 1) ≤ stabQ (stdF F 3) := by
  have key : ∀ g ∈ stabQ (stdF F 1), ∀ w ∈ stdF F 3, g2Act g w ∈ stdF F 3 := by
    intro g hg w hw
    obtain ⟨c, hc0, hc⟩ := exists_smul_of_mem_stabQ_one hg
    have hN0 : cayleyNorm (zU0 F) = 0 := by
      rw [zU0, cayleyNorm_zmk]
      ring
    have hgz : cgE g (zU0 F) = c • zU0 F := by
      have h := cgE_zI_of_norm (g := g) (w := eu 0 1) (by rw [zI_eu, hN0]) (by
        rw [hc, zI_smul, zI_eu, zU0, zmk_smul, cayleyNorm_zmk]
        ring)
      rw [zI_eu, hc, zI_smul, zI_eu] at h
      exact h
    have h0 : cayleyMul (zU0 F) (zI w) = 0 := by
      obtain ⟨h1, h2, h3⟩ := mem_stdF_three.mp hw
      rw [mul_zU0_zI, h1, h2, h3, neg_zero, ← zmk_zero]
    have h1 := congrArg (cgE g) h0
    rw [cg_mul, map_zero, hgz, g2_zI_eq g w, mul_smul_zU0, ← zmk_zero] at h1
    obtain ⟨e1, -, -, -, -, e6, e7, -⟩ := zmk_inj h1
    refine mem_stdF_three.mpr ⟨?_, ?_, ?_⟩
    · exact (mul_eq_zero.mp e7).resolve_left hc0
    · exact (mul_eq_zero.mp (neg_eq_zero.mp e6)).resolve_left hc0
    · exact (mul_eq_zero.mp e1).resolve_left hc0
  intro g hg
  refine mem_stabQ.mpr fun w => ⟨key g hg w, fun hw => ?_⟩
  have h1 := key g⁻¹ ((stabQ (stdF F 1)).inv_mem hg) _ hw
  rwa [g2Act_inv_apply] at h1

theorem stabQ_one_eq_three : stabQ (stdF F 1) = stabQ (stdF F 3) :=
  le_antisymm stabQ_one_le_three stabQ_three_le_one

section Map

variable {W : Type*} [CommGroup W]

theorem inv_conj_mem_of_conj_mem' {G : Type*} [Group G] {H : Subgroup G} [Finite H] {τ : G}
    (hτ : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H) : ∀ h ∈ H, τ⁻¹ * h * τ ∈ H := by
  let φ : ↥H → ↥H := fun h => ⟨τ * h * τ⁻¹, hτ h h.2⟩
  have hφ : Function.Injective φ := fun a b hab => Subtype.ext (by
    have h1 : τ * (a : G) * τ⁻¹ = τ * b * τ⁻¹ := congrArg Subtype.val hab
    exact mul_left_cancel (mul_right_cancel h1))
  intro h hh
  obtain ⟨h', hh'⟩ := Finite.surjective_of_injective hφ ⟨h, hh⟩
  have h1 : τ * (h' : G) * τ⁻¹ = h := congrArg Subtype.val hh'
  rw [← h1, show τ⁻¹ * (τ * (h' : G) * τ⁻¹) * τ = h' by group]
  exact h'.2

theorem isFlagW_map {H P : Subgroup (MulAut W)} {Z U : Subgroup W} {q i : ℕ}
    (hU : Ch11.SecA.IsFlagW H P Z q i U) {τ : MulAut W} (hτZ : τ ∈ Ch11.SecA.stabW Z)
    (hτH : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H) (hP : ∀ p ∈ P, τ⁻¹ * p * τ ∈ Ch11.SecA.stabW U) :
    Ch11.SecA.IsFlagW H P Z q i (U.map τ.toMonoidHom) := by
  obtain ⟨hZU, hst, hidx, -⟩ := hU
  have hτZ' : ∀ z, z ∈ Z ↔ τ z ∈ Z := Ch11.SecA.mem_stabW.mp hτZ
  have hτiZ : ∀ z, z ∈ Z ↔ τ⁻¹ z ∈ Z :=
    Ch11.SecA.mem_stabW.mp ((Ch11.SecA.stabW Z).inv_mem hτZ)
  refine ⟨fun z hz => ⟨τ⁻¹ z, hZU ((hτiZ z).mp hz), by simp⟩, ?_, ?_, fun p hp => ?_⟩
  · intro φ hφZ hφH u hu
    obtain ⟨u', hu', rfl⟩ := hu
    let φ' : W →* W := (τ⁻¹ : MulAut W).toMonoidHom.comp (φ.comp τ.toMonoidHom)
    have hφ'Z : ∀ z ∈ Z, φ' z ∈ Z := fun z hz =>
      (hτiZ _).mp (hφZ _ ((hτZ' z).mp hz))
    have hφ'H : ∀ h ∈ H, ∀ w : W, φ' (h w) * (h (φ' w))⁻¹ ∈ Z := by
      intro h hh w
      have h1 := hφH (τ * h * τ⁻¹) (hτH h hh) (τ w)
      have e : φ' (h w) * (h (φ' w))⁻¹ = τ⁻¹ (φ ((τ * h * τ⁻¹) (τ w)) *
          ((τ * h * τ⁻¹) (φ (τ w)))⁻¹) := by
        simp [φ', MulAut.mul_apply]
      rw [e]
      exact (hτiZ _).mp h1
    refine ⟨φ' u', hst φ' hφ'Z hφ'H u' hu', ?_⟩
    simp [φ']
  · rw [← hidx]
    have hZ : Z.map τ.toMonoidHom = Z := by
      ext z
      constructor
      · rintro ⟨z', hz', rfl⟩
        exact (hτZ' z').mp hz'
      · intro hz
        exact ⟨τ⁻¹ z, (hτiZ z).mp hz, by simp⟩
    conv_lhs => rw [← hZ]
    exact Subgroup.relIndex_map_map_of_injective Z U τ.injective
  · have hmem : ∀ w, w ∈ U.map τ.toMonoidHom ↔ τ⁻¹ w ∈ U := fun w => by
      constructor
      · rintro ⟨u, hu, rfl⟩
        simpa using hu
      · intro h
        exact ⟨τ⁻¹ w, h, by simp⟩
    rw [Ch11.SecA.mem_stabW]
    intro w
    rw [hmem, hmem, Ch11.SecA.mem_stabW.mp (hP p hp) (τ⁻¹ w)]
    simp [MulAut.mul_apply]

theorem stabW_of_map_eq {U : Subgroup W} {τ : MulAut W} (h : U.map τ.toMonoidHom = U) :
    τ ∈ Ch11.SecA.stabW U := by
  rw [Ch11.SecA.mem_stabW]
  intro u
  constructor
  · intro hu
    rw [← h]
    exact ⟨u, hu, rfl⟩
  · intro hu
    rw [← h] at hu
    obtain ⟨u', hu', e⟩ := hu
    have : u' = u := τ.injective e
    rwa [← this]

end Map

theorem factN13G2_holds : Ch11.SecA.FactN13G2 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U₁ U₃ hU₁ hU₃ τ hτZ hτH
  have : CharP K 2 := KGNat.charP_two_of_card (by omega) hK
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  obtain ⟨c₀, hc0, hc1⟩ := exists_ne_zero_ne_one_of_card hn hK
  obtain ⟨f, hf⟩ := exists_isCoord (lmG K) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_U0 hK (by omega) hf hc0 hc1 hP
  have hU₁' : Ch11.SecA.IsFlagW H P Z (Nat.card K) 1 U₁ := by rw [hK]; exact hU₁
  have hU₃' : Ch11.SecA.IsFlagW H P Z (Nat.card K) 3 U₃ := by rw [hK]; exact hU₃
  have huniq : ∀ {i : ℕ} {U V : Subgroup W}, Ch11.SecA.IsFlagW H P Z (Nat.card K) i U →
      Ch11.SecA.IsFlagW H P Z (Nat.card K) i V → U = V := by
    intro i U V hU hV
    obtain ⟨S, hS, hc, rfl⟩ := exists_eq_preG_of_isFlagW hW hf hc0 hc1 hg hU
    obtain ⟨S', hS', hc', rfl⟩ := exists_eq_preG_of_isFlagW hW hf hc0 hc1 hg hV
    rw [eq_stdF_of_card hS hc, eq_stdF_of_card hS' hc']
  have hH13 : H ⊓ Ch11.SecA.stabW U₁ = H ⊓ Ch11.SecA.stabW U₃ := by
    obtain ⟨S, hS, hc, rfl⟩ := exists_eq_preG_of_isFlagW hW hf hc0 hc1 hg hU₁'
    obtain ⟨S', hS', hc', rfl⟩ := exists_eq_preG_of_isFlagW hW hf hc0 hc1 hg hU₃'
    rw [eq_stdF_of_card hS hc, eq_stdF_of_card hS' hc', ← map_stabQ_eq hf hc0 hc1 g,
      ← map_stabQ_eq hf hc0 hc1 g, stabQ_one_eq_three]
  have hτH' := inv_conj_mem_of_conj_mem' hτH
  have hP₁ : P ≤ Ch11.SecA.stabW U₁ := hU₁.2.2.2
  have hP₃ : P ≤ Ch11.SecA.stabW U₃ := hU₃.2.2.2
  have hPH : P ≤ H := hP.1
  constructor
  · intro hτ
    have hP' : ∀ p ∈ P, τ⁻¹ * p * τ ∈ Ch11.SecA.stabW U₃ := by
      intro p hp
      have h1 : τ⁻¹ * p * τ ∈ H ⊓ Ch11.SecA.stabW U₁ :=
        ⟨hτH' p (hPH hp), (Ch11.SecA.stabW U₁).mul_mem ((Ch11.SecA.stabW U₁).mul_mem
          ((Ch11.SecA.stabW U₁).inv_mem hτ) (hP₁ hp)) hτ⟩
      rw [hH13] at h1
      exact h1.2
    exact stabW_of_map_eq (huniq (isFlagW_map hU₃' hτZ hτH hP') hU₃')
  · intro hτ
    have hP' : ∀ p ∈ P, τ⁻¹ * p * τ ∈ Ch11.SecA.stabW U₁ := by
      intro p hp
      have h1 : τ⁻¹ * p * τ ∈ H ⊓ Ch11.SecA.stabW U₃ :=
        ⟨hτH' p (hPH hp), (Ch11.SecA.stabW U₃).mul_mem ((Ch11.SecA.stabW U₃).mul_mem
          ((Ch11.SecA.stabW U₃).inv_mem hτ) (hP₃ hp)) hτ⟩
      rw [← hH13] at h1
      exact h1.2
    exact stabW_of_map_eq (huniq (isFlagW_map hU₁' hτZ hτH hP') hU₁')

end CFSG.Quasithin.Vol2.Ch11.G2Q8
