module

public import CFSG.Milestones.ASVolI.F411.aSwL3
public import CFSG.Milestones.ASVolI.F411.aSwL3BTri
public import CFSG.Milestones.ASVolI.F411.aSwL3BField
public import CFSG.Milestones.ASVolI.F411.L3Rad
public import CFSG.Milestones.ASVolI.F411.aSwL3BModel

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.Quasithin CFSG.ASVolI.ChF
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem burnsideF411a_map_pCore_of_range {E : Type} [Group E] {M M' : Subgroup E} (p : ℕ)
    (χ : ↥M →* E) (hχ : Function.Injective χ) (hr : χ.range = M') :
    (pCore p ↥M).map χ = pCoreOf p M' := by
  let φ : ↥M ≃* ↥M' := (MonoidHom.ofInjective hχ).trans (MulEquiv.subgroupCongr hr)
  have h1 := CFSG.LieType.BorelTits.map_pCore_mulEquiv p φ
  have h2 : M'.subtype.comp φ.toMonoidHom = χ := MonoidHom.ext fun _ => rfl
  unfold pCoreOf
  rw [← h1, Subgroup.map_map, h2]

theorem burnsideF411a_pCoreOf_map' {G E : Type} [Group G] [Group E] {f : G →* E}
    (hf : Function.Injective f) (p : ℕ) (X : Subgroup G) :
    pCoreOf p (X.map f) = (pCoreOf p X).map f := by
  let e : ↥X ≃* ↥(X.map f) := X.equivMapOfInjective f hf
  have h1 := CFSG.LieType.BorelTits.map_pCore_mulEquiv p e
  unfold pCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

section Radicals

variable {K : Type} [Field K]

theorem burnsideF411a_mem_l3R1 {g : SpecialLinearGroup (Fin 3) K} :
    g ∈ burnsideF411_l3R1 K ↔ ∃ a b : K, g = burnsideF411a_u a b 0 := by
  constructor
  · intro hg
    have r : ∀ i j : Fin 3, i ≠ 0 →
        (g : Matrix (Fin 3) (Fin 3) K) i j = (1 : Matrix (Fin 3) (Fin 3) K) i j := hg
    have h10 := r 1 0 (by decide)
    have h11 := r 1 1 (by decide)
    have h12 := r 1 2 (by decide)
    have h20 := r 2 0 (by decide)
    have h21 := r 2 1 (by decide)
    have h22 := r 2 2 (by decide)
    simp at h10 h11 h12 h20 h21 h22
    have hdet := g.2
    rw [Matrix.det_fin_three, h10, h11, h12, h20, h21, h22] at hdet
    simp at hdet
    refine ⟨(g : Matrix (Fin 3) (Fin 3) K) 0 1, (g : Matrix (Fin 3) (Fin 3) K) 0 2, ?_⟩
    ext i j
    rw [burnsideF411a_coe_u]
    fin_cases i <;> fin_cases j <;> simp [h10, h11, h12, h20, h21, h22, hdet]
  · rintro ⟨a, b, rfl⟩ i j hi
    rw [burnsideF411a_coe_u]
    fin_cases i
    · exact absurd rfl hi
    all_goals fin_cases j <;> simp

theorem burnsideF411a_mem_l3R2 {g : SpecialLinearGroup (Fin 3) K} :
    g ∈ burnsideF411_l3R2 K ↔ ∃ b c : K, g = burnsideF411a_u 0 b c := by
  constructor
  · intro hg
    have r : ∀ i j : Fin 3, j ≠ 2 →
        (g : Matrix (Fin 3) (Fin 3) K) i j = (1 : Matrix (Fin 3) (Fin 3) K) i j := hg
    have h00 := r 0 0 (by decide)
    have h10 := r 1 0 (by decide)
    have h20 := r 2 0 (by decide)
    have h01 := r 0 1 (by decide)
    have h11 := r 1 1 (by decide)
    have h21 := r 2 1 (by decide)
    simp at h00 h10 h20 h01 h11 h21
    have hdet := g.2
    rw [Matrix.det_fin_three, h00, h10, h20, h01, h11, h21] at hdet
    simp at hdet
    refine ⟨(g : Matrix (Fin 3) (Fin 3) K) 0 2, (g : Matrix (Fin 3) (Fin 3) K) 1 2, ?_⟩
    ext i j
    rw [burnsideF411a_coe_u]
    fin_cases i <;> fin_cases j <;> simp [h00, h10, h20, h01, h11, h21, hdet]
  · rintro ⟨b, c, rfl⟩ i j hj
    rw [burnsideF411a_coe_u]
    fin_cases j
    all_goals first
      | exact absurd rfl hj
      | fin_cases i <;> simp

end Radicals

theorem burnsideF411a_L3_one_norm {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 p f Gp M₁ M₂) (hp : p % 3 = 1)
    (hR1 : pCoreOf p M₁ = pCoreOf p (Gp ⊓ M₁)) (hR2 : pCoreOf p M₂ = pCoreOf p (Gp ⊓ M₂))
    (χ₁ : ↥M₁ →* E) (χ₂ : ↥M₂ →* E) (hχ₁ : Function.Injective χ₁)
    (hχ₂ : Function.Injective χ₂) (hr₁ : χ₁.range = M₂) (hr₂ : χ₂.range = M₁)
    (hagree : ∀ x : ↥(M₁ ⊓ M₂),
      χ₁ (Subgroup.inclusion inf_le_left x) = χ₂ (Subgroup.inclusion inf_le_right x))
    (K : Type) [Field K] [Finite K] [Fact p.Prime] [CharP K p] (e : projectiveSL 3 K ≃* ↥Gp)
    (hP1 : Gp ⊓ M₁ = (projStabilizer (flagSpace 3 K 1)).map (Gp.subtype.comp e.toMonoidHom))
    (hP2 : Gp ⊓ M₂ = (projStabilizer (flagSpace 3 K 2)).map (Gp.subtype.comp e.toMonoidHom))
    (x : E) :
    ∃ x' : E, @MulAut.conjNormal E _ Gp hyp.normal x' =
      MulAut.congr e (burnsideF411a_L3zeta K (frobeniusEquiv K p)) *
        @MulAut.conjNormal E _ Gp hyp.normal x *
          (MulAut.congr e (burnsideF411a_L3zeta K (frobeniusEquiv K p)))⁻¹ := by
  classical
  haveI : Finite E := hyp.finite
  haveI hN : Gp.Normal := hyp.normal
  set ι : projectiveSL 3 K →* E := Gp.subtype.comp e.toMonoidHom with hιdef
  have hι : Function.Injective ι := Gp.subtype_injective.comp e.injective
  set uE : K → K → K → E := fun a b c => ι (burnsideF411a_pu a b c) with huEdef
  have uE_mul : ∀ a b c a' b' c', uE a b c * uE a' b' c' =
      uE (a + a') (b + b' + a * c') (c + c') := fun a b c a' b' c' => by
    simp only [huEdef, ← map_mul, burnsideF411a_pu_mul]
  have uE_inv : ∀ a b c, (uE a b c)⁻¹ = uE (-a) (a * c - b) (-c) := fun a b c => by
    simp only [huEdef, ← map_inv, burnsideF411a_pu_inv]
  have uE_inj : ∀ {a b c a' b' c' : K}, uE a b c = uE a' b' c' → a = a' ∧ b = b' ∧ c = c' :=
    fun h => burnsideF411a_pu_injective (hι h)
  have uE_congr : ∀ {a b c a' b' c' : K}, a = a' → b = b' → c = c' →
      uE a b c = uE a' b' c' := by
    rintro a b c a' b' c' rfl rfl rfl
    rfl
  have hB1 : ∀ a b c, uE a b c ∈ M₁ := fun a b c => by
    have : uE a b c ∈ Gp ⊓ M₁ := by
      rw [hP1]
      exact ⟨_, burnsideF411a_pu_mem_projStabilizer a b c 1, rfl⟩
    exact this.2
  have hB2 : ∀ a b c, uE a b c ∈ M₂ := fun a b c => by
    have : uE a b c ∈ Gp ⊓ M₂ := by
      rw [hP2]
      exact ⟨_, burnsideF411a_pu_mem_projStabilizer a b c 2, rfl⟩
    exact this.2
  set vE : K → K → K → ↥M₁ := fun a b c => ⟨uE a b c, hB1 a b c⟩ with hvEdef
  have vE_mul : ∀ a b c a' b' c', vE a b c * vE a' b' c' =
      vE (a + a') (b + b' + a * c') (c + c') := fun a b c a' b' c' =>
    Subtype.ext (uE_mul a b c a' b' c')
  have vE_inv : ∀ a b c, (vE a b c)⁻¹ = vE (-a) (a * c - b) (-c) := fun a b c =>
    Subtype.ext (uE_inv a b c)
  have vE_congr : ∀ {a b c a' b' c' : K}, a = a' → b = b' → c = c' →
      vE a b c = vE a' b' c' := by
    rintro a b c a' b' c' rfl rfl rfl
    rfl
  have hQ1 : ∀ y, y ∈ pCoreOf p (Gp ⊓ M₁) ↔ ∃ a b, y = uE a b 0 := by
    intro y
    rw [hP1, burnsideF411a_pCoreOf_map' hι, burnsideF411_l3_pCoreOf_point (K := K) p,
      Subgroup.map_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨a, b, rfl⟩ := burnsideF411a_mem_l3R1.1 hg
      exact ⟨a, b, rfl⟩
    · rintro ⟨a, b, rfl⟩
      exact ⟨burnsideF411a_u a b 0, burnsideF411a_mem_l3R1.2 ⟨a, b, rfl⟩, rfl⟩
  have hQ2 : ∀ y, y ∈ pCoreOf p (Gp ⊓ M₂) ↔ ∃ b c, y = uE 0 b c := by
    intro y
    rw [hP2, burnsideF411a_pCoreOf_map' hι, burnsideF411_l3_pCoreOf_line (K := K) p,
      Subgroup.map_map]
    constructor
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨b, c, rfl⟩ := burnsideF411a_mem_l3R2.1 hg
      exact ⟨b, c, rfl⟩
    · rintro ⟨b, c, rfl⟩
      exact ⟨burnsideF411a_u 0 b c, burnsideF411a_mem_l3R2.2 ⟨b, c, rfl⟩, rfl⟩
  have hχQ1 : ∀ a b, ∃ b' c', χ₁ (vE a b 0) = uE 0 b' c' := by
    intro a b
    have hy : uE a b 0 ∈ pCoreOf p M₁ := by
      rw [hR1, hQ1]
      exact ⟨a, b, rfl⟩
    obtain ⟨w, hw, hwy⟩ := hy
    have hwv : w = vE a b 0 := Subtype.ext hwy
    have hmem : χ₁ w ∈ pCoreOf p (Gp ⊓ M₂) := by
      rw [← hR2, ← burnsideF411a_map_pCore_of_range p χ₁ hχ₁ hr₁]
      exact ⟨w, hw, rfl⟩
    rw [hwv] at hmem
    exact (hQ2 _).1 hmem
  have hχQ2 : ∀ b c, ∃ a' b', χ₁ (vE 0 b c) = uE a' b' 0 := by
    intro b c
    have hy : uE 0 b c ∈ pCoreOf p M₂ := by
      rw [hR2, hQ2]
      exact ⟨b, c, rfl⟩
    obtain ⟨w, hw, hwy⟩ := hy
    have hag := hagree ⟨uE 0 b c, ⟨hB1 0 b c, hB2 0 b c⟩⟩
    have e1 : (Subgroup.inclusion inf_le_left ⟨uE 0 b c, ⟨hB1 0 b c, hB2 0 b c⟩⟩ : ↥M₁) =
        vE 0 b c := rfl
    have e2 : (Subgroup.inclusion inf_le_right ⟨uE 0 b c, ⟨hB1 0 b c, hB2 0 b c⟩⟩ : ↥M₂) = w :=
      Subtype.ext hwy.symm
    rw [e1, e2] at hag
    have hmem : χ₂ w ∈ pCoreOf p (Gp ⊓ M₁) := by
      rw [← hR1, ← burnsideF411a_map_pCore_of_range p χ₂ hχ₂ hr₂]
      exact ⟨w, hw, rfl⟩
    rw [← hag] at hmem
    exact (hQ1 _).1 hmem
  choose β₁ s₁ hs₁ using fun a => hχQ1 a 0
  choose s₂ β₂ hs₂ using fun c => hχQ2 0 c
  have hχZ : ∀ b, ∃ b', χ₁ (vE 0 b 0) = uE 0 b' 0 := by
    intro b
    obtain ⟨b₁', c₁', h₁⟩ := hχQ1 0 b
    obtain ⟨a₂', b₂', h₂⟩ := hχQ2 b 0
    rw [h₁] at h₂
    obtain ⟨-, -, hc⟩ := uE_inj h₂
    exact ⟨b₁', by rw [h₁, hc]⟩
  choose sZ hsZ using hχZ
  have hs₁add : ∀ a a', s₁ (a + a') = s₁ a + s₁ a' := by
    intro a a'
    have h := congrArg χ₁ (vE_mul a 0 0 a' 0 0)
    rw [map_mul, hs₁, hs₁, uE_mul, vE_congr rfl (by ring : (0 : K) + 0 + a * 0 = 0)
      (by ring : (0 : K) + 0 = 0), hs₁] at h
    exact (uE_inj h.symm).2.2
  have hpair : ∀ a c, sZ (a * c) = -(s₂ c * s₁ a) := by
    intro a c
    have hcomm : vE a 0 0 * vE 0 0 c * (vE a 0 0)⁻¹ * (vE 0 0 c)⁻¹ = vE 0 (a * c) 0 := by
      rw [vE_inv, vE_inv, vE_mul, vE_mul, vE_mul]
      exact vE_congr (by ring) (by ring) (by ring)
    have h := congrArg χ₁ hcomm
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hs₁, hs₂, hsZ, uE_inv, uE_inv, uE_mul,
      uE_mul, uE_mul] at h
    have := (uE_inj h).2.1
    linear_combination -this
  have hsZinj : Function.Injective sZ := by
    intro b b' hbb
    have h1 := hsZ b
    have h2 := hsZ b'
    rw [hbb, ← h2] at h1
    have := congrArg Subtype.val (hχ₁ h1)
    exact (uE_inj this).2.1
  have hsZsurj : Function.Surjective sZ := Finite.injective_iff_surjective.mp hsZinj
  have hs₁1 : s₁ 1 ≠ 0 := by
    intro h0
    obtain ⟨b, hb⟩ := hsZsurj (β₁ 1)
    have h1 := hs₁ 1
    rw [h0, ← hb, ← hsZ] at h1
    have := congrArg Subtype.val (hχ₁ h1)
    exact one_ne_zero (uE_inj this).1
  have hs₂1 : s₂ 1 ≠ 0 := by
    intro h0
    obtain ⟨b, hb⟩ := hsZsurj (β₂ 1)
    have h1 := hs₂ 1
    rw [h0, ← hb, ← hsZ] at h1
    have := congrArg Subtype.val (hχ₁ h1)
    exact one_ne_zero (uE_inj this).2.2
  obtain ⟨τ, hτ₁, hτ₂⟩ := burnsideF411a_semilinear hs₁add hpair hs₁1 hs₂1
  have hβ : ∀ (h : E) (y : projectiveSL 3 K),
      ι ((MulAut.congr e).symm (MulAut.conjNormal h) y) = h * ι y * h⁻¹ := by
    intro h y
    simp only [hιdef, MonoidHom.comp_apply, MulAut.congr_symm_apply, MulEquiv.trans_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply, Subgroup.coe_subtype,
      MulAut.conjNormal_apply]
  have hmapβ : ∀ (h : E) (X : Subgroup (projectiveSL 3 K)),
      h ∈ Subgroup.normalizer ((X.map ι : Subgroup E) : Set E) →
        X.map ((MulAut.congr e).symm (MulAut.conjNormal h)).toMonoidHom = X := by
    intro h X hX
    apply Subgroup.map_injective hι
    ext z
    rw [Subgroup.map_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hβ]
      exact (Subgroup.mem_normalizer_iff.mp hX _).mp ⟨y, hy, rfl⟩
    · intro hz
      have hz' : h⁻¹ * z * h⁻¹⁻¹ ∈ X.map ι :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hX) z).mp hz
      obtain ⟨y, hy, hyz⟩ := hz'
      refine ⟨y, hy, ?_⟩
      rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hβ, hyz]
      group
  have hborel : ∀ h ∈ M₁ ⊓ M₂, ∃ (A : GL (Fin 3) K) (σ : K ≃+* K),
      (∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) K) i j = 0) ∧
        (MulAut.congr e).symm (MulAut.conjNormal h) = conjAut 3 K A * fieldAut 3 K σ := by
    intro h hh
    refine burnsideF411a_borel_aut _ (hmapβ h _ ?_) (hmapβ h _ ?_)
    · rw [← hP1, inf_comm]
      exact burnsideF411_le_normalizer_inf hN M₁ hh.1
    · rw [← hP2, inf_comm]
      exact burnsideF411_le_normalizer_inf hN M₂ hh.2
  have hact : ∀ (h : E) (A : GL (Fin 3) K) (σ : K ≃+* K),
      (∀ i j : Fin 3, j < i → (A : Matrix (Fin 3) (Fin 3) K) i j = 0) →
        (MulAut.congr e).symm (MulAut.conjNormal h) = conjAut 3 K A * fieldAut 3 K σ →
          ∀ a b c, ∃ b', h * uE a b c * h⁻¹ =
            uE ((A : Matrix (Fin 3) (Fin 3) K) 0 0 / (A : Matrix (Fin 3) (Fin 3) K) 1 1 * σ a) b'
              ((A : Matrix (Fin 3) (Fin 3) K) 1 1 / (A : Matrix (Fin 3) (Fin 3) K) 2 2 * σ c) := by
    intro h A σ hA hβA a b c
    obtain ⟨b', hb'⟩ := burnsideF411a_borel_act A hA σ a b c
    refine ⟨b', ?_⟩
    rw [← hβ, hβA, hb']
  obtain ⟨n, hn, h, hh, rfl⟩ := hyp.split x
  obtain ⟨A, σ, hA, hβA⟩ := hborel h hh
  set hM : ↥M₁ := ⟨h, hh.1⟩ with hhM
  have hh' : χ₁ hM ∈ M₁ ⊓ M₂ := by
    refine ⟨?_, ?_⟩
    · have hag := hagree ⟨h, hh⟩
      have e1 : (Subgroup.inclusion inf_le_left ⟨h, hh⟩ : ↥M₁) = hM := rfl
      rw [e1] at hag
      rw [hag]
      have hmem : χ₂ (Subgroup.inclusion inf_le_right ⟨h, hh⟩) ∈ χ₂.range := ⟨_, rfl⟩
      rwa [hr₂] at hmem
    · rw [← hr₁]
      exact ⟨_, rfl⟩
  obtain ⟨A₂, σ₂, hA₂, hβA₂⟩ := hborel (χ₁ hM) hh'
  have hE1 : ∀ a, (A₂ : Matrix (Fin 3) (Fin 3) K) 1 1 / (A₂ : Matrix (Fin 3) (Fin 3) K) 2 2 *
      σ₂ (s₁ a) = s₁ ((A : Matrix (Fin 3) (Fin 3) K) 0 0 /
        (A : Matrix (Fin 3) (Fin 3) K) 1 1 * σ a) := by
    intro a
    obtain ⟨b', hb'⟩ := hact h A σ hA hβA a 0 0
    have hv : hM * vE a 0 0 * hM⁻¹ = vE ((A : Matrix (Fin 3) (Fin 3) K) 0 0 /
        (A : Matrix (Fin 3) (Fin 3) K) 1 1 * σ a) 0 0 * vE 0 b' 0 := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      change h * uE a 0 0 * h⁻¹ = uE _ 0 0 * uE 0 b' 0
      rw [hb', uE_mul]
      exact uE_congr (by ring) (by ring) (by rw [map_zero]; ring)
    have hχ := congrArg χ₁ hv
    rw [map_mul, map_mul, map_inv, map_mul, hs₁, hs₁, hsZ, uE_mul] at hχ
    obtain ⟨b'', hb''⟩ := hact (χ₁ hM) A₂ σ₂ hA₂ hβA₂ 0 (β₁ a) (s₁ a)
    rw [hb''] at hχ
    have := (uE_inj hχ).2.2
    linear_combination this
  have hE2 : ∀ c, (A₂ : Matrix (Fin 3) (Fin 3) K) 0 0 / (A₂ : Matrix (Fin 3) (Fin 3) K) 1 1 *
      σ₂ (s₂ c) = s₂ ((A : Matrix (Fin 3) (Fin 3) K) 1 1 /
        (A : Matrix (Fin 3) (Fin 3) K) 2 2 * σ c) := by
    intro c
    obtain ⟨b', hb'⟩ := hact h A σ hA hβA 0 0 c
    have hv : hM * vE 0 0 c * hM⁻¹ = vE 0 b' 0 * vE 0 0 ((A : Matrix (Fin 3) (Fin 3) K) 1 1 /
        (A : Matrix (Fin 3) (Fin 3) K) 2 2 * σ c) := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      change h * uE 0 0 c * h⁻¹ = uE 0 b' 0 * uE 0 0 _
      rw [hb', uE_mul]
      exact uE_congr (by rw [map_zero]; ring) (by ring) (by ring)
    have hχ := congrArg χ₁ hv
    rw [map_mul, map_mul, map_inv, map_mul, hs₂, hs₂, hsZ, uE_mul] at hχ
    obtain ⟨b'', hb''⟩ := hact (χ₁ hM) A₂ σ₂ hA₂ hβA₂ (s₂ c) (β₂ c) 0
    rw [hb''] at hχ
    have := (uE_inj hχ).1
    linear_combination this
  have hx0 := burnsideF411a_diag_ne_zero A hA 0
  have hx1 := burnsideF411a_diag_ne_zero A hA 1
  have hx2 := burnsideF411a_diag_ne_zero A hA 2
  have hy0 := burnsideF411a_diag_ne_zero A₂ hA₂ 0
  have hy1 := burnsideF411a_diag_ne_zero A₂ hA₂ 1
  have hy2 := burnsideF411a_diag_ne_zero A₂ hA₂ 2
  have hE1' : ∀ a, (A₂ : Matrix (Fin 3) (Fin 3) K) 1 1 / (A₂ : Matrix (Fin 3) (Fin 3) K) 2 2 *
      σ₂ (s₁ 1) * σ₂ (τ a) = s₁ 1 * τ ((A : Matrix (Fin 3) (Fin 3) K) 0 0 /
        (A : Matrix (Fin 3) (Fin 3) K) 1 1) * τ (σ a) := by
    intro a
    have := hE1 a
    rw [hτ₁ a, hτ₁ ((A : Matrix (Fin 3) (Fin 3) K) 0 0 / (A : Matrix (Fin 3) (Fin 3) K) 1 1 * σ a),
      map_mul, map_mul] at this
    linear_combination this
  have hE1_1 := hE1' 1
  simp only [map_one, mul_one] at hE1_1
  have hσ₂ : σ₂ = σ := by
    have hστ : ∀ a, σ₂ (τ a) = τ (σ a) := by
      intro a
      have h1 := hE1' a
      rw [hE1_1] at h1
      have hne : s₁ 1 * τ ((A : Matrix (Fin 3) (Fin 3) K) 0 0 /
          (A : Matrix (Fin 3) (Fin 3) K) 1 1) ≠ 0 :=
        mul_ne_zero hs₁1 ((map_ne_zero τ).mpr (div_ne_zero hx0 hx1))
      exact mul_left_cancel₀ hne h1
    refine RingEquiv.ext fun y => ?_
    obtain ⟨a, rfl⟩ := τ.surjective y
    rw [hστ, burnsideF411a_aut_comm (p := p) σ τ a]
  rw [hσ₂] at hE1_1 hβA₂
  have hE2_1 : (A₂ : Matrix (Fin 3) (Fin 3) K) 0 0 / (A₂ : Matrix (Fin 3) (Fin 3) K) 1 1 *
      σ (s₂ 1) = s₂ 1 * τ ((A : Matrix (Fin 3) (Fin 3) K) 1 1 /
        (A : Matrix (Fin 3) (Fin 3) K) 2 2) := by
    have := hE2 1
    rw [hσ₂, map_one, mul_one, hτ₂ ((A : Matrix (Fin 3) (Fin 3) K) 1 1 /
      (A : Matrix (Fin 3) (Fin 3) K) 2 2)] at this
    exact this
  obtain ⟨m, hm⟩ := burnsideF411a_class_cube hp σ τ (frobeniusEquiv K p) hx0 hx1 hx2 hy1 hy2 hs₁1
    hs₂1 hE1_1 hE2_1
  have hdet0 : (frobeniusEquiv K p) (((GeneralLinearGroup.det A : Kˣ) : K)) *
      ((GeneralLinearGroup.det A₂ : Kˣ) : K) = m ^ 3 := by
    rw [burnsideF411a_det_upper A hA, burnsideF411a_det_upper A₂ hA₂]
    exact hm
  have hm0 : m ≠ 0 := by
    intro h0
    rw [h0, zero_pow (by norm_num)] at hdet0
    exact mul_ne_zero ((map_ne_zero _).mpr (GeneralLinearGroup.det A).ne_zero)
      (GeneralLinearGroup.det A₂).ne_zero hdet0
  set A'' := burnsideF411a_w0 K * GeneralLinearGroup.inverseTranspose
      (GeneralLinearGroup.map ((frobeniusEquiv K p : K ≃+* K) : K →+* K) A) *
        (burnsideF411a_w0 K)⁻¹ with hA''
  have hdet : GeneralLinearGroup.det (A'' * A₂⁻¹) = (Units.mk0 m hm0)⁻¹ ^ 3 := by
    rw [map_mul, map_inv, hA'', burnsideF411a_det_L3zeta]
    apply Units.ext
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, Units.coe_map,
      Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Units.val_mk0, inv_pow, ← hdet0]
    exact (mul_inv _ _).symm
  obtain ⟨g, hg⟩ := conjAut_mem_range_conj_of_det_eq_pow hdet
  set ζ₀ := burnsideF411a_L3zeta K (frobeniusEquiv K p) with hζ₀
  have hζβ : ζ₀ * (MulAut.congr e).symm (MulAut.conjNormal h) * ζ₀⁻¹ =
      MulAut.conj g * (MulAut.congr e).symm (MulAut.conjNormal (χ₁ hM)) := by
    rw [hβA, hβA₂, hg]
    have h1 := burnsideF411a_L3zeta_conj_conjAut (frobeniusEquiv K p) A
    have h2 := burnsideF411a_L3zeta_conj_fieldAut (frobeniusEquiv K p) σ
      (burnsideF411a_frob_comm σ)
    rw [← hζ₀] at h1 h2
    calc ζ₀ * (conjAut 3 K A * fieldAut 3 K σ) * ζ₀⁻¹
        = (ζ₀ * conjAut 3 K A * ζ₀⁻¹) * (ζ₀ * fieldAut 3 K σ * ζ₀⁻¹) := by group
      _ = conjAut 3 K A'' * fieldAut 3 K σ := by rw [h1, h2]
      _ = conjAut 3 K (A'' * A₂⁻¹) * (conjAut 3 K A₂ * fieldAut 3 K σ) := by
          rw [map_mul (conjAut 3 K) A'' A₂⁻¹, map_inv (conjAut 3 K) A₂]
          group
  refine ⟨((MulAut.congr e ζ₀) ⟨n, hn⟩ : E) * (((e g : ↥Gp) : E) * χ₁ hM), ?_⟩
  have hconj : ∀ y : ↥Gp, (MulAut.conjNormal (y : E) : MulAut ↥Gp) = MulAut.conj y := fun y =>
    MulAut.conjNormal_val
  rw [map_mul, map_mul, map_mul, hconj, hconj, hconj ⟨n, hn⟩]
  have hζn := burnsideF411a_mul_conj_mul_inv (MulAut.congr e ζ₀) ⟨n, hn⟩
  have hζh : MulAut.congr e ζ₀ * MulAut.conjNormal h * (MulAut.congr e ζ₀)⁻¹ =
      MulAut.conj (e g) * MulAut.conjNormal (χ₁ hM) := by
    have h1 := congrArg (MulAut.congr e) hζβ
    rw [map_mul, map_mul, map_inv, map_mul, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply] at h1
    rw [h1]
    congr 1
    ext y
    simp [MulAut.congr_apply, MulAut.conj_apply]
  calc MulAut.conj ((MulAut.congr e ζ₀) ⟨n, hn⟩) * (MulAut.conj (e g) * MulAut.conjNormal (χ₁ hM))
      = (MulAut.congr e ζ₀ * MulAut.conj ⟨n, hn⟩ * (MulAut.congr e ζ₀)⁻¹) *
          (MulAut.congr e ζ₀ * MulAut.conjNormal h * (MulAut.congr e ζ₀)⁻¹) := by
        rw [hζn, hζh]
    _ = MulAut.congr e ζ₀ * (MulAut.conj ⟨n, hn⟩ * MulAut.conjNormal h) *
          (MulAut.congr e ζ₀)⁻¹ := by group

theorem burnsideF411a_swap_L3_one {p f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .L3 p f Gp M₁ M₂) (hp : p % 3 = 1)
    (hR1 : pCoreOf p M₁ = pCoreOf p (Gp ⊓ M₁)) (hR2 : pCoreOf p M₂ = pCoreOf p (Gp ⊓ M₂)) :
    burnsideF411_Swap M₁ M₂ := by
  intro χ₁ χ₂ hχ₁ hχ₂ hr₁ hr₂ hagree
  exact burnsideF411a_swap_L3_of_normalizes hyp
    (fun K _ _ _ _ e hP1 hP2 x => burnsideF411a_L3_one_norm hyp hp hR1 hR2 χ₁ χ₂ hχ₁ hχ₂ hr₁ hr₂
      hagree K e hP1 hP2 x) χ₁ χ₂ hχ₁ hχ₂ hr₁ hr₂ hagree

end CFSG.ASVolI
