module

public import CFSG.Quasithin.Vol2.Ch1ModO2
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise

namespace Stellmacher.L3YC

section Theta

variable {G : Type} [Group G] [Finite G]

@[expose] def O2sub (H : Subgroup G) : Subgroup G := (CFSG.pCore 2 ↥H).map H.subtype

@[expose] def preImage (H : Subgroup G) (K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : Subgroup G :=
  (K.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H))).map H.subtype

@[expose] def theta (H₁ V : Subgroup G) : Subgroup G := ⨆ h ∈ H₁, B6.conjSub h V

omit [Finite G] in
theorem mem_O2sub_iff {H : Subgroup G} (x : ↥H) : (x : G) ∈ O2sub H ↔ x ∈ CFSG.pCore 2 ↥H :=
  Subgroup.mem_map_iff_mem H.subtype_injective

omit [Finite G] in
theorem conj_mem_O2sub {H : Subgroup G} {h r : G} (hh : h ∈ H) (hr : r ∈ O2sub H) :
    h * r * h⁻¹ ∈ O2sub H := by
  obtain ⟨r', hr', rfl⟩ := hr
  have : (CFSG.pCore 2 ↥H).Normal := CFSG.pCore_normal
  exact ⟨⟨h, hh⟩ * r' * ⟨h, hh⟩⁻¹, this.conj_mem r' hr' ⟨h, hh⟩, by simp⟩

omit [Finite G] in
theorem mem_preImage_iff {H : Subgroup G} {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (x : ↥H) :
    (x : G) ∈ preImage H K ↔ QuotientGroup.mk' (CFSG.pCore 2 ↥H) x ∈ K :=
  (Subgroup.mem_map_iff_mem H.subtype_injective).trans Subgroup.mem_comap

omit [Finite G] in
theorem preImage_le (H : Subgroup G) (K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) : preImage H K ≤ H := by
  rintro _ ⟨x, -, rfl⟩
  exact x.2

omit [Finite G] in
theorem conj_mem_preImage {H : Subgroup G} {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hK : K.Normal)
    {g h : G} (hg : g ∈ H) (hh : h ∈ preImage H K) : g * h * g⁻¹ ∈ preImage H K := by
  obtain ⟨h', hh', rfl⟩ := hh
  have : (g * (h' : G) * g⁻¹) = ((⟨g, hg⟩ * h' * ⟨g, hg⟩⁻¹ : ↥H) : G) := by simp
  show g * (h' : G) * g⁻¹ ∈ _
  rw [this, mem_preImage_iff]
  rw [map_mul, map_mul]
  have := hK.conj_mem _ (Subgroup.mem_comap.mp hh') (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨g, hg⟩)
  simpa using this

omit [Finite G] in
theorem conjSub_le_theta {H₁ V : Subgroup G} {h : G} (hh : h ∈ H₁) :
    B6.conjSub h V ≤ theta H₁ V :=
  le_iSup₂_of_le h hh le_rfl

omit [Finite G] in
theorem theta_le {H₁ V X : Subgroup G} (h : ∀ g ∈ H₁, B6.conjSub g V ≤ X) : theta H₁ V ≤ X :=
  iSup₂_le h

omit [Finite G] in
theorem le_theta {H₁ V : Subgroup G} : V ≤ theta H₁ V := by
  have := conjSub_le_theta (V := V) (Subgroup.one_mem H₁)
  rwa [B6.conjSub_one] at this

omit [Finite G] in
theorem normalizer_theta_of {H₁ V X : Subgroup G}
    (hX : ∀ g ∈ X, ∀ h ∈ H₁, ∃ h' ∈ H₁, B6.conjSub h V ≤ B6.conjSub g (B6.conjSub h' V)) :
    X ≤ Subgroup.normalizer (theta H₁ V : Set G) := by
  have key : ∀ g ∈ X, theta H₁ V ≤ B6.conjSub g (theta H₁ V) := by
    intro g hg
    refine theta_le fun h hh => ?_
    obtain ⟨h', hh', hle⟩ := hX g hg h hh
    exact hle.trans ((B6.conjSub g).monotone (conjSub_le_theta hh'))
  intro g hg
  have h1 := key g hg
  have h2 := key g⁻¹ (X.inv_mem hg)
  refine B6.mem_normalizer_of_conjSub_le ?_ ?_
  · have := (B6.conjSub g).monotone h2
    rwa [← B6.conjSub_mul, mul_inv_cancel, B6.conjSub_one] at this
  · have := (B6.conjSub g⁻¹).monotone h1
    rwa [← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one] at this

omit [Finite G] in
theorem le_normalizer_theta_self (H₁ V : Subgroup G) :
    H₁ ≤ Subgroup.normalizer (theta H₁ V : Set G) := by
  refine normalizer_theta_of fun g hg h hh => ⟨g⁻¹ * h, H₁.mul_mem (H₁.inv_mem hg) hh, ?_⟩
  rw [← B6.conjSub_mul, mul_inv_cancel_left]

omit [Finite G] in
theorem inf_normalizer_le_normalizer_theta {H H₁ V : Subgroup G}
    (hH₁ : ∀ g ∈ H, ∀ h ∈ H₁, g⁻¹ * h * g ∈ H₁) :
    H ⊓ Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (theta H₁ V : Set G) := by
  refine normalizer_theta_of fun g hg h hh => ⟨g⁻¹ * h * g, hH₁ g hg.1 h hh, ?_⟩
  have e : g * (g⁻¹ * h * g) = h * g := by group
  rw [← B6.conjSub_mul, e, B6.conjSub_mul, B6.conjSub_eq_self hg.2]

omit [Finite G] in
theorem theta_le_O2sub {H H₁ V : Subgroup G} (hH₁ : H₁ ≤ H) (hV : V ≤ O2sub H) :
    theta H₁ V ≤ O2sub H := by
  refine theta_le fun g hg x hx => ?_
  rw [B6.mem_conjSub] at hx
  have := conj_mem_O2sub (H := H) (hH₁ hg) (hV hx)
  simpa [mul_assoc] using this

omit [Finite G] in
theorem O2sub_le_of_isSylow {H S : Subgroup G} (hS : IsSylowTwoOf S H) : O2sub H ≤ S := by
  rintro _ ⟨x, hx, rfl⟩
  exact Subgroup.mem_subgroupOf.mp (pCore_two_le_subgroupOf hS hx)

omit [Finite G] in
theorem exists_lift {H L₀ : Subgroup G} {g : ↥H}
    (hg : QuotientGroup.mk' (CFSG.pCore 2 ↥H) g ∈ modO2Image H L₀) :
    ∃ l ∈ L₀, ∃ r ∈ O2sub H, (g : G) = l * r := by
  obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hg
  have h1 : y⁻¹ * g ∈ CFSG.pCore 2 ↥H := QuotientGroup.eq.mp hyg
  refine ⟨y, Subgroup.mem_subgroupOf.mp hy, ((y⁻¹ * g : ↥H) : G), ⟨_, h1, rfl⟩, ?_⟩
  simp

omit [Finite G] in
theorem orbit_lemma {H L₀ : Subgroup G} {K₁ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} {V : Subgroup G}
    {x₂ : G} (hLN : L₀ ≤ Subgroup.normalizer (V : Set G))
    (hRN : O2sub H ≤ Subgroup.normalizer (V : Set G)) (hx₂H : x₂ ∈ H)
    (hx₂N : x₂ ∉ Subgroup.normalizer (V : Set G))
    (hx₂K : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x₂, hx₂H⟩ ∈ K₁)
    (h2t : ∀ g ∈ K₁, g ∉ modO2Image H L₀ → ∀ h ∈ K₁,
      h ∈ modO2Image H L₀ ∨ ∃ a ∈ modO2Image H L₀, ∃ b ∈ modO2Image H L₀, h = a * g * b) :
    ∀ h ∈ preImage H K₁, B6.conjSub h V = V ∨
      ∃ a ∈ L₀, B6.conjSub h V = B6.conjSub a (B6.conjSub x₂ V) := by
  intro h hh
  obtain ⟨y, hy, rfl⟩ := hh
  have hyK : QuotientGroup.mk' (CFSG.pCore 2 ↥H) y ∈ K₁ := hy
  have hxL : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x₂, hx₂H⟩ ∉ modO2Image H L₀ := by
    intro hmem
    obtain ⟨l, hl, r, hr, hlr⟩ := exists_lift hmem
    apply hx₂N
    have : x₂ = l * r := hlr
    rw [this]
    exact Subgroup.mul_mem _ (hLN hl) (hRN hr)
  rcases h2t _ hx₂K hxL _ hyK with hmem | ⟨a, ha, b, hb, hab⟩
  · left
    obtain ⟨l, hl, r, hr, hlr⟩ := exists_lift hmem
    show B6.conjSub (y : G) V = V
    rw [hlr, B6.conjSub_mul, B6.conjSub_eq_self (hRN hr), B6.conjSub_eq_self (hLN hl)]
  · right
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
    set r : ↥H := (a₀ * ⟨x₂, hx₂H⟩ * b₀)⁻¹ * y with hrdef
    have h0 : QuotientGroup.mk' (CFSG.pCore 2 ↥H) (a₀ * ⟨x₂, hx₂H⟩ * b₀) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥H) y := by
      rw [map_mul, map_mul]
      exact hab.symm
    have h1 : r ∈ CFSG.pCore 2 ↥H := QuotientGroup.eq.mp h0
    have hr : (r : G) ∈ O2sub H := ⟨_, h1, rfl⟩
    refine ⟨a₀, Subgroup.mem_subgroupOf.mp ha₀, ?_⟩
    have e0 : a₀ * ⟨x₂, hx₂H⟩ * b₀ * r = y := by rw [hrdef]; exact mul_inv_cancel_left _ _
    have e := congrArg Subtype.val e0
    simp only [Subgroup.coe_mul] at e
    show B6.conjSub (y : G) V = _
    rw [← e]
    simp only [B6.conjSub_mul]
    rw [B6.conjSub_eq_self (hRN hr), B6.conjSub_eq_self (hLN (Subgroup.mem_subgroupOf.mp hb₀))]

omit [Finite G] in
theorem card_conjSub (g : G) (A : Subgroup G) : Nat.card ↥(B6.conjSub g A) = Nat.card ↥A :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

omit [Finite G] in
theorem conjSub_eq_self_iff {g : G} {A : Subgroup G} :
    B6.conjSub g A = A ↔ g ∈ Subgroup.normalizer (A : Set G) :=
  ⟨fun h => Subgroup.mem_normalizer_iff_map_conj_eq.mpr h, B6.conjSub_eq_self⟩

theorem U_le_theta {H₁ V U₀ : Subgroup G} {x₂ : G} (hV : Nat.card ↥V = 4)
    (hU : Nat.card ↥U₀ = 8) (hVU : V ≤ U₀) (hxU : x₂ ∈ Subgroup.normalizer (U₀ : Set G))
    (hxV : x₂ ∉ Subgroup.normalizer (V : Set G)) (hxH : x₂ ∈ H₁) : U₀ ≤ theta H₁ V := by
  have hc : B6.conjSub x₂ V ≤ U₀ := by
    have := (B6.conjSub x₂).monotone hVU
    rwa [B6.conjSub_eq_self hxU] at this
  have hne : ¬ B6.conjSub x₂ V ≤ V := fun hle => hxV (conjSub_eq_self_iff.mp
    (Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub, hV])))
  have hsupU : V ⊔ B6.conjSub x₂ V ≤ U₀ := sup_le hVU hc
  have hdvd : Nat.card ↥(V ⊔ B6.conjSub x₂ V) ∣ 8 := by
    have := Subgroup.card_dvd_of_le hsupU
    rwa [hU] at this
  have hdvd4 : 4 ∣ Nat.card ↥(V ⊔ B6.conjSub x₂ V) := by
    have := Subgroup.card_dvd_of_le (le_sup_left : V ≤ V ⊔ B6.conjSub x₂ V)
    rwa [hV] at this
  have h8 : Nat.card ↥(V ⊔ B6.conjSub x₂ V) = 8 := by
    obtain ⟨k, hk⟩ := hdvd4
    have hk' : k ∣ 2 := by
      rw [hk] at hdvd
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num : 0 < 4) (by simpa using hdvd)
    rcases (Nat.dvd_prime Nat.prime_two).mp hk' with h | h
    · exfalso
      apply hne
      have hc4 : Nat.card ↥(V ⊔ B6.conjSub x₂ V) = 4 := by rw [hk, h]
      have hVeq : V = V ⊔ B6.conjSub x₂ V :=
        Subgroup.eq_of_le_of_card_ge (le_sup_left : V ≤ V ⊔ B6.conjSub x₂ V)
          (by rw [hc4, hV])
      calc B6.conjSub x₂ V ≤ V ⊔ B6.conjSub x₂ V := le_sup_right
        _ = V := hVeq.symm
    · rw [hk, h]
  have heq : V ⊔ B6.conjSub x₂ V = U₀ := Subgroup.eq_of_le_of_card_ge hsupU (by rw [h8, hU])
  rw [← heq]
  exact sup_le le_theta (conjSub_le_theta hxH)

omit [Finite G] in
theorem normalizer_theta_of_acts {H₁ V U₀ L₀ : Subgroup G} {x₂ y : G}
    (hVU : V ≤ U₀) (hxU : B6.conjSub x₂ V ≤ U₀) (hUθ : U₀ ≤ theta H₁ V)
    (horb : ∀ h ∈ H₁, B6.conjSub h V = V ∨
      ∃ a ∈ L₀, B6.conjSub h V = B6.conjSub a (B6.conjSub x₂ V))
    (hL : L₀ ≤ Subgroup.centralizer (V : Set G))
    (hC : Subgroup.centralizer (V : Set G) ≤ Subgroup.normalizer (theta H₁ V : Set G))
    (hyV : y ∈ Subgroup.normalizer (V : Set G)) (hyU : y ∈ Subgroup.normalizer (U₀ : Set G)) :
    y ∈ Subgroup.normalizer (theta H₁ V : Set G) := by
  have key : ∀ z : G, z ∈ Subgroup.normalizer (V : Set G) → z ∈ Subgroup.normalizer (U₀ : Set G) →
      theta H₁ V ≤ B6.conjSub z (theta H₁ V) := by
    intro z hzV hzU
    have hU : U₀ ≤ B6.conjSub z (theta H₁ V) := by
      have := (B6.conjSub z).monotone hUθ
      rwa [B6.conjSub_eq_self hzU] at this
    refine theta_le fun h hh => ?_
    rcases horb h hh with h1 | ⟨a, ha, h1⟩
    · rw [h1]; exact hVU.trans hU
    · rw [h1]
      have hz : z⁻¹ * a * z ∈ Subgroup.centralizer (V : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have hzv : z * v * z⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hzV v).mp hv
        have := Subgroup.mem_centralizer_iff.mp (hL ha) (z * v * z⁻¹) hzv
        calc v * (z⁻¹ * a * z) = z⁻¹ * ((z * v * z⁻¹) * a) * z := by group
          _ = z⁻¹ * (a * (z * v * z⁻¹)) * z := by rw [this]
          _ = z⁻¹ * a * z * v := by group
      have hN : B6.conjSub (z⁻¹ * a * z) (theta H₁ V) = theta H₁ V :=
        B6.conjSub_eq_self (hC hz)
      have hcomm : B6.conjSub a (B6.conjSub z (theta H₁ V)) = B6.conjSub z (theta H₁ V) := by
        rw [← B6.conjSub_mul]
        have e : a * z = z * (z⁻¹ * a * z) := by group
        rw [e, B6.conjSub_mul, hN]
      calc B6.conjSub a (B6.conjSub x₂ V) ≤ B6.conjSub a (B6.conjSub z (theta H₁ V)) :=
            (B6.conjSub a).monotone (hxU.trans hU)
        _ = B6.conjSub z (theta H₁ V) := hcomm
  have h1 := key y hyV hyU
  have h2 := key y⁻¹ ((Subgroup.normalizer (V : Set G)).inv_mem hyV)
    ((Subgroup.normalizer (U₀ : Set G)).inv_mem hyU)
  refine B6.mem_normalizer_of_conjSub_le ?_ ?_
  · have := (B6.conjSub y).monotone h2
    rwa [← B6.conjSub_mul, mul_inv_cancel, B6.conjSub_one] at this
  · have := (B6.conjSub y⁻¹).monotone h1
    rwa [← B6.conjSub_mul, inv_mul_cancel, B6.conjSub_one] at this

end Theta

end Stellmacher.L3YC

end CFSG.Quasithin
