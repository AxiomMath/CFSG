module

public import CFSG.Quasithin.Background.G10FourSetup
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem g10Four_zmod_two_add_self (x : ZMod 2) : x + x = 0 := by
  revert x
  decide

theorem g10Four_zmod_two_add_eq_zero {x y : ZMod 2} (h : x + y = 0) : x = y := by
  revert x y
  decide

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ : Subgroup (GLV V)}

theorem G101Hyp.B_comm (hyp : G101Hyp B Γ v₁ W X X₀) (x y : V) : B x y = B y x := by
  have h := hyp.alt (x + y)
  simp only [map_add, LinearMap.add_apply, hyp.alt] at h
  have : B x y + B y x = 0 := by linear_combination h
  exact g10Four_zmod_two_add_eq_zero this

theorem isotropic_of_hfull (hyp : G101Hyp B Γ v₁ W X X₀) (K : Subgroup (GLV V)) (hKΓ : K ≤ Γ)
    (hXK : X ≤ K) (U : Submodule (ZMod 2) V) (hirr : IsIrr K U) (h1 : v₁ ∉ U)
    (h2 : ∃ u ∈ U, B v₁ u ≠ 0) (hn3 : 3 ≤ Module.finrank (ZMod 2) U) : Isotropic B U := by
  have hUX : Invariant X U := fun x hx u hu => hirr.1 x (hXK hx) u hu
  obtain ⟨-, -, -, hfull, hker⟩ := hyp.counting U hUX h1 h2
  obtain ⟨u₀, hu₀, hB₀⟩ := G101Hyp.exists_one U h2
  have hJinv : Invariant K (U ⊓ B.orthogonal U) := by
    intro k hk j hj
    refine ⟨hirr.1 k hk j hj.1, ?_⟩
    show k j ∈ B.orthogonal U
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    have hkinv : k⁻¹ ∈ K := K.inv_mem hk
    have h3 := hyp.isometry k (hKΓ hk) ((k⁻¹ : GLV V) w) j
    have h4 : k ((k⁻¹ : GLV V) w) = w := by simp
    rw [h4] at h3
    rw [h3]
    exact (LinearMap.BilinForm.mem_orthogonal_iff.1 hj.2) _ (hirr.1 _ hkinv w hw)
  have hJ : U ⊓ B.orthogonal U = ⊥ ∨ U ⊓ B.orthogonal U = U :=
    hirr.2.2 _ hJinv bot_le inf_le_left
  rcases hJ with hJ0 | hJU
  · exfalso
    have hrad : ∀ a : V, a ∈ U → (∀ w ∈ U, B w a = 0) → a = 0 := by
      intro a haU ha
      have : a ∈ U ⊓ B.orthogonal U := ⟨haU, ha⟩
      rw [hJ0, Submodule.mem_bot] at this
      exact this
    have key : ∀ a : U, B v₁ a = 0 → (a : V) ≠ 0 → ∀ w : U, B (w : V) (a : V) = B v₁ w := by
      intro a ha ha0
      obtain ⟨x, hx, hxa⟩ := hfull a ha
      have hiso := fun (u w : U) => hyp.isometry x (hyp.X_le hx) (u : V) (w : V)
      have hform : ∀ w : U, B (w : V) (a : V) + B v₁ w * B u₀ (a : V) = 0 := by
        intro w
        have h5 := hiso ⟨u₀, hu₀⟩ w
        rw [hxa ⟨u₀, hu₀⟩, hxa w] at h5
        simp only [hB₀, one_smul, map_add, LinearMap.add_apply, map_smul,
          smul_eq_mul, hyp.alt] at h5
        have hc := hyp.B_comm (a : V) (w : V)
        linear_combination h5 - hc
      intro w
      rcases g10Four_zmod_two_cases (B u₀ (a : V)) with hc | hc
      · exfalso
        apply ha0
        apply hrad (a : V) a.2
        intro w' hw'
        have := hform ⟨w', hw'⟩
        rw [hc, mul_zero, add_zero] at this
        exact this
      · have := hform w
        rw [hc, mul_one] at this
        exact g10Four_zmod_two_add_eq_zero this
    have hk2 : 2 ≤ Module.finrank (ZMod 2) ↥(LinearMap.ker ((B v₁).domRestrict U)) := by omega
    obtain ⟨a, ha, b, hb, ha0, hb0, hab⟩ := g10Four_exists_two_ne_zero (V := ↥U) _ hk2
    have haα : B v₁ (a : V) = 0 := by simpa using ha
    have hbα : B v₁ (b : V) = 0 := by simpa using hb
    have ha1 : (a : V) ≠ 0 := fun h => ha0 (Subtype.ext h)
    have hb1 : (b : V) ≠ 0 := fun h => hb0 (Subtype.ext h)
    have hsum : (a : V) + (b : V) = 0 := by
      apply hrad _ (U.add_mem a.2 b.2)
      intro w' hw'
      rw [map_add, key a haα ha1 ⟨w', hw'⟩, key b hbα hb1 ⟨w', hw'⟩]
      exact g10Four_zmod_two_add_self _
    apply hab
    have h6 : (a : V) = (b : V) :=
      (eq_neg_of_add_eq_zero_left hsum).trans (neg_eq_of_add_eq_zero_right (g10Four_add_self _))
    exact Subtype.ext h6
  · intro u hu u' hu'
    have : u' ∈ U ⊓ B.orthogonal U := by
      rw [hJU]
      exact hu'
    exact (LinearMap.BilinForm.mem_orthogonal_iff.1 this.2) u hu

theorem G101Hyp.two_mul_finrank_le (hyp : G101Hyp B Γ v₁ W X X₀) {U : Submodule (ZMod 2) V}
    (hiso : Isotropic B U) : 2 * Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) V := by
  have hU : U ≤ B.orthogonal U := fun u hu => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    exact fun n hn => hiso n hn u hu
  have h1 := Submodule.finrank_mono hU
  have h2 := LinearMap.BilinForm.finrank_orthogonal hyp.nondegenerate' U
  have h3 : Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) V := Submodule.finrank_le U
  omega

theorem G101Hyp.orthogonal_eq (hyp : G101Hyp B Γ v₁ W X X₀) {U : Submodule (ZMod 2) V}
    (hiso : Isotropic B U) (hdim : 2 * Module.finrank (ZMod 2) U = Module.finrank (ZMod 2) V) :
    B.orthogonal U = U := by
  have hU : U ≤ B.orthogonal U := fun u hu => by
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    exact fun n hn => hiso n hn u hu
  have h2 := LinearMap.BilinForm.finrank_orthogonal hyp.nondegenerate' U
  symm
  apply Submodule.eq_of_le_of_finrank_le hU
  omega

omit [Finite V] in
theorem g10Four_le_normalizer_centralizerOn (H : Subgroup (GLV V)) (U : Submodule (ZMod 2) V)
    (hUH : Invariant H U) : H ≤ Subgroup.normalizer (centralizerOn H U : Set (GLV V)) := by
  have hconj : ∀ h ∈ H, ∀ n ∈ centralizerOn H U, h * n * h⁻¹ ∈ centralizerOn H U := by
    intro h hh n hn
    refine ⟨H.mul_mem (H.mul_mem hh hn.1) (H.inv_mem hh), fun u hu => ?_⟩
    have h1 : (h⁻¹ : GLV V) u ∈ U := hUH _ (H.inv_mem hh) u hu
    have h2 : n ((h⁻¹ : GLV V) u) = (h⁻¹ : GLV V) u := hn.2 _ h1
    show h (n ((h⁻¹ : GLV V) u)) = u
    rw [h2]
    simp
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro n
  constructor
  · exact fun hn => hconj h hh n hn
  · intro hn
    have := hconj h⁻¹ (H.inv_mem hh) _ hn
    simpa [mul_assoc] using this

theorem centralizerOn_eq_bot_of_pCore (hyp : G101Hyp B Γ v₁ W X X₀) (h3 : pCoreOf 2 Γ = ⊥)
    (H : Subgroup (GLV V)) (hHΓ : H ≤ Γ) (hHn : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H)
    (U : Submodule (ZMod 2) V) (hUH : Invariant H U) (hperp : B.orthogonal U = U) :
    centralizerOn H U = ⊥ := by
  have hNH : centralizerOn H U ≤ H := fun n hn => hn.1
  have hsq : ∀ n ∈ centralizerOn H U, n * n = 1 := by
    intro n hn
    ext v
    have hU : n v - v ∈ U := by
      rw [← hperp, LinearMap.BilinForm.mem_orthogonal_iff]
      intro u hu
      have := hyp.isometry n (hHΓ hn.1) u v
      rw [hn.2 u hu] at this
      rw [map_sub, this]
      exact sub_self _
    have h1 : n (n v - v) = n v - v := hn.2 _ hU
    rw [map_sub] at h1
    show n (n v) = v
    have h2 : n (n v) = n v - v + n v := by
      rw [← h1]
      abel
    rw [h2]
    have h4 := g10Four_add_self (n v)
    calc n v - v + n v = (n v + n v) - v := by abel
      _ = 0 - v := by rw [h4]
      _ = v := by
        rw [zero_sub]
        exact neg_eq_of_add_eq_zero_right (g10Four_add_self v)
  have hp : IsPGroup 2 (centralizerOn H U) := by
    intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    simpa [pow_two] using hsq g.1 g.2
  have hN2 : centralizerOn H U ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hNH
      (g10Four_le_normalizer_centralizerOn H U hUH) hp
  have hΓnorm : Γ ≤ Subgroup.normalizer (H : Set (GLV V)) := by
    intro γ hγ
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · exact fun hh => hHn γ hγ h hh
    · intro hh
      have := hHn γ⁻¹ (Γ.inv_mem hγ) _ hh
      simpa [mul_assoc] using this
  have hPΓ : pCoreOf 2 H ≤ pCoreOf 2 Γ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hHΓ)
      (hΓnorm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H)
  rw [h3] at hPΓ
  exact le_bot_iff.1 (hN2.trans hPΓ)

theorem g10Four_transvection_mem (hyp : G101Hyp B Γ v₁ W X X₀) (U : Submodule (ZMod 2) V)
    (hperp : B.orthogonal U = U) (h : GLV V) (hhΓ : h ∈ Γ) (c : U) (f : U →ₗ[ZMod 2] ZMod 2)
    (hfc : f c = 0) (hact : ∀ u : U, h (u : V) = (u : V) + f u • (c : V)) (y : V)
    (hy : B (c : V) y = 0) : h y - y ∈ U := by
  have hinv : ∀ u : U, (h⁻¹ : GLV V) (u : V) = (u : V) + f u • (c : V) := by
    intro u
    have hmem : (u : V) + f u • (c : V) ∈ U := U.add_mem u.2 (U.smul_mem _ c.2)
    have h1 := hact ⟨(u : V) + f u • (c : V), hmem⟩
    have h2 : f ⟨(u : V) + f u • (c : V), hmem⟩ = f u := by
      have : (⟨(u : V) + f u • (c : V), hmem⟩ : U) = u + f u • c := rfl
      rw [this, map_add, map_smul, hfc, smul_eq_mul, mul_zero, add_zero]
    rw [h2] at h1
    have h3 : h ((u : V) + f u • (c : V)) = (u : V) := by
      simp only at h1
      rw [h1]
      have : f u • (c : V) + f u • (c : V) = 0 := by
        rw [← add_smul, g10Four_zmod_two_add_self, zero_smul]
      rw [add_assoc, this, add_zero]
    calc (h⁻¹ : GLV V) (u : V) = (h⁻¹ : GLV V) (h ((u : V) + f u • (c : V))) := by rw [h3]
      _ = (u : V) + f u • (c : V) := by simp
  rw [← hperp, LinearMap.BilinForm.mem_orthogonal_iff]
  intro u hu
  have h1 := hyp.isometry h hhΓ ((h⁻¹ : GLV V) u) y
  have h4 : h ((h⁻¹ : GLV V) u) = u := by simp
  rw [h4] at h1
  rw [map_sub, h1, hinv ⟨u, hu⟩]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, hy, smul_eq_mul,
    mul_zero, add_zero]
  exact sub_self _

theorem centralizerOn_eq_bot (hyp : G101Hyp B Γ v₁ W X X₀) (K H : Subgroup (GLV V))
    (hKΓ : K ≤ Γ) (hHK : H ≤ K) (hHnK : ∀ k ∈ K, ∀ h ∈ H, k * h * k⁻¹ ∈ H)
    (U : Submodule (ZMod 2) V) (hUH : Invariant H U) (hperp : B.orthogonal U = U)
    (hn3 : 3 ≤ Module.finrank (ZMod 2) U) (hfaithH : centralizerOn H U = ⊥) (hall : AutAll H U) :
    centralizerOn K U = ⊥ := by
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  have hrU : ∀ u ∈ U, r u = u := hr.2
  have hrinv : ∀ u ∈ U, (r⁻¹ : GLV V) u = u := by
    intro u hu
    have := congrArg (r⁻¹ : GLV V) (hrU u hu)
    simpa using this.symm
  have hS : ∀ v, r v - v ∈ U := by
    intro v
    rw [← hperp, LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have := hyp.isometry r (hKΓ hr.1) u v
    rw [hrU u hu] at this
    rw [map_sub, this]
    exact sub_self _
  have hcomm : ∀ h ∈ H, r * h = h * r := by
    intro h hh
    have hc : r * h * r⁻¹ * h⁻¹ ∈ centralizerOn H U := by
      refine ⟨H.mul_mem (hHnK r hr.1 h hh) (H.inv_mem hh), fun u hu => ?_⟩
      have h1 : (h⁻¹ : GLV V) u ∈ U := hUH _ (H.inv_mem hh) u hu
      show r (h ((r⁻¹ : GLV V) ((h⁻¹ : GLV V) u))) = u
      rw [hrinv _ h1]
      simp [hrU u hu]
    rw [hfaithH, Subgroup.mem_bot] at hc
    calc r * h = (r * h * r⁻¹ * h⁻¹) * (h * r) := by group
      _ = h * r := by rw [hc, one_mul]
  have hkey : ∀ y : V, r y - y = 0 := by
    intro y
    let s : U := ⟨r y - y, hS y⟩
    have hspan : ∀ c : U, (c : V) ≠ 0 → B (c : V) y = 0 → s ∈ Submodule.span (ZMod 2) {c} := by
      intro c hc0 hBc
      by_contra hns
      obtain ⟨f, hfc, hfs⟩ := g10Four_exists_dual U c s hns
      obtain ⟨h, hh, hact⟩ := hall (LinearEquiv.transvection hfc)
      have hact' : ∀ u : U, h (u : V) = (u : V) + f u • (c : V) := by
        intro u
        rw [hact u]
        rfl
      have hhΓ : h ∈ Γ := hKΓ (hHK hh)
      have hz := g10Four_transvection_mem hyp U hperp h hhΓ c f hfc hact' y hBc
      have hrz : r (h y - y) = h y - y := hrU _ hz
      have hrh : r (h y) = h (r y) := congrArg (fun g : GLV V => g y) (hcomm h hh)
      have hry : r (h y) = r y + (h y - y) := by
        have e1 : h y = y + (h y - y) := by abel
        calc r (h y) = r (y + (h y - y)) := congrArg r e1
          _ = r y + (h y - y) := by rw [map_add, hrz]
      have hs' : h (r y - y) = r y - y := by
        rw [map_sub, ← hrh, hry]
        abel
      have h5 := hact' s
      have h6 : f s • (c : V) = 0 := by
        have : (s : V) = r y - y := rfl
        rw [this, hs'] at h5
        have h7 : (r y - y) + f s • (c : V) = (r y - y) + 0 := by rw [← h5, add_zero]
        exact add_left_cancel h7
      rcases smul_eq_zero.1 h6 with h8 | h8
      · rw [hfs] at h8
        exact one_ne_zero h8
      · exact hc0 h8
    let g : U →ₗ[ZMod 2] ZMod 2 := (LinearMap.flip B y).domRestrict U
    have hker := g10Four_finrank_ker_ge (↥U) g
    obtain ⟨c, hc, c', hc', hc0, hc'0, hcc'⟩ :=
      g10Four_exists_two_ne_zero (V := ↥U) (LinearMap.ker g) (by omega)
    have hcB : B (c : V) y = 0 := by simpa [g] using hc
    have hc'B : B (c' : V) y = 0 := by simpa [g] using hc'
    have hs1 := hspan c (fun h => hc0 (Subtype.ext h)) hcB
    have hs2 := hspan c' (fun h => hc'0 (Subtype.ext h)) hc'B
    have hs0 : s = 0 := by
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hs1
      obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 hs2
      rcases g10Four_zmod_two_cases a with rfl | rfl
      · rw [← ha, zero_smul]
      · rcases g10Four_zmod_two_cases b with rfl | rfl
        · rw [← hb, zero_smul]
        · exfalso
          apply hcc'
          rw [one_smul] at ha hb
          rw [ha, hb]
    have : (s : V) = 0 := by rw [hs0]; rfl
    exact this
  ext y
  exact sub_eq_zero.1 (hkey y)

omit [Finite V] in
theorem le_of_centralizerOn_eq_bot (K H X : Subgroup (GLV V)) (hHK : H ≤ K) (hXK : X ≤ K)
    (U : Submodule (ZMod 2) V) (hUK : Invariant K U) (hall : AutAll H U)
    (hfaith : centralizerOn K U = ⊥) : X ≤ H := by
  intro x hx
  obtain ⟨h, hh, hact⟩ := hall (g10FourRestrict K U hUK ⟨x, hXK hx⟩)
  have hmem : x⁻¹ * h ∈ centralizerOn K U := by
    refine ⟨K.mul_mem (K.inv_mem (hXK hx)) (hHK hh), fun u hu => ?_⟩
    have h1 : h u = x u := by
      have := hact ⟨u, hu⟩
      simpa using this
    show (x⁻¹ : GLV V) (h u) = u
    rw [h1]
    simp
  rw [hfaith, Subgroup.mem_bot] at hmem
  have : x = h := by
    have h2 : h = x := by
      calc h = x * (x⁻¹ * h) := by group
        _ = x := by rw [hmem, mul_one]
    exact h2.symm
  rw [this]
  exact hh

end CFSG.Quasithin
