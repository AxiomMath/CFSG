module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.Order.Atoms.Finite
public import CFSG.Open.LocalVocabulary
public import CFSG.Assembly.InCatalog
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxAssemblyAux
public import CFSG.LocalAnalysis.StandardType.GGTorusMaxNormalP

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open

theorem tmAsm_eq_one_of_two_group_of_cube {G : Type*} [Group G] (P : Subgroup G)
    (hP2 : IsPGroup 2 P) {c : G} (hcP : c ∈ P) (h3 : c ^ 3 = 1) : c = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hP2) ⟨c, hcP⟩
  have hk' : orderOf c = 2 ^ k := by
    rw [← hk]
    exact (Subgroup.orderOf_mk c hcP).symm
  have h1 : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  have h2 : orderOf c ∣ 2 ^ k := hk' ▸ dvd_refl _
  have h4 : orderOf c ∣ Nat.gcd 3 (2 ^ k) := Nat.dvd_gcd h1 h2
  have h5 : Nat.gcd 3 (2 ^ k) = 1 := by
    have : Nat.Coprime 3 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
    exact this
  rw [h5] at h4
  exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)

theorem tmAsm_inf_eq_bot_of_two_group {G : Type*} [Group G] (E P H : Subgroup G)
    (hE3 : ∀ a ∈ E, a ^ 3 = 1) (hEH : Subgroup.normalizer (E : Set G) ≤ H) (hPH : P ≤ H)
    (hPn : (P.subgroupOf H).Normal) (hP2 : IsPGroup 2 P)
    (hcent : ∀ g ∈ Subgroup.normalizer (E : Set G), (∀ e ∈ E, g * e = e * g) → g ∈ E) :
    Subgroup.normalizer (E : Set G) ⊓ P = ⊥ := by
  rw [eq_bot_iff]
  rintro r ⟨hrM, hrP⟩
  have hEP : ∀ c ∈ E, c ∈ P → c = 1 := fun c hcE hcP =>
    tmAsm_eq_one_of_two_group_of_cube P hP2 hcP (hE3 c hcE)
  have hcomm : ∀ e ∈ E, r * e = e * r := by
    intro e he
    have heM : e ∈ Subgroup.normalizer (E : Set G) := Subgroup.le_normalizer he
    have hc1 : r * e * r⁻¹ * e⁻¹ ∈ E := by
      have h1 : r * e * r⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.1 hrM e).1 he
      exact E.mul_mem h1 (E.inv_mem he)
    have hc2 : r * e * r⁻¹ * e⁻¹ ∈ P := by
      have h1 : e * r⁻¹ * e⁻¹ ∈ P := by
        have := hPn.conj_mem (⟨r⁻¹, hPH (P.inv_mem hrP)⟩ : H)
          (by simpa [Subgroup.mem_subgroupOf] using P.inv_mem hrP) ⟨e, hEH heM⟩
        simpa [Subgroup.mem_subgroupOf, mul_assoc] using this
      have : r * (e * r⁻¹ * e⁻¹) ∈ P := P.mul_mem hrP h1
      simpa [mul_assoc] using this
    have h1 : r * e * r⁻¹ * e⁻¹ = 1 := hEP _ hc1 hc2
    calc r * e = (r * e * r⁻¹ * e⁻¹) * e * r := by group
      _ = e * r := by rw [h1, one_mul]
  have hrE : r ∈ E := hcent r hrM (fun e he => hcomm e he)
  exact Subgroup.mem_bot.2 (hEP r hrE hrP)

theorem tmAsm_normalizer_ne_top {G : Type*} [Group G] [Finite G] [IsSimpleGroup G] (E : Subgroup G)
    (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) {m : ℕ} (hm : 2 ≤ m) (hcard : Nat.card E = 3 ^ m) :
    Subgroup.normalizer (E : Set G) ≠ ⊤ := by
  intro htop
  haveI hn : E.Normal := Subgroup.normalizer_eq_top_iff.1 htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal E with h | h
  · have h1 : Nat.card E = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hcard] at h1
    have : 1 < 3 ^ m := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  · have hab : ∀ a b : G, a * b = b * a := by
      intro a b
      have ha : a ∈ E := h ▸ Subgroup.mem_top a
      have hb : b ∈ E := h ▸ Subgroup.mem_top b
      exact hE a ha b hb
    have hp : (Nat.card G).Prime := by
      letI : CommGroup G := { ‹Group G› with mul_comm := hab }
      exact IsSimpleGroup.prime_card
    have hG : Nat.card G = 3 ^ m := by
      rw [← hcard, h, Subgroup.card_top]
    rw [hG] at hp
    have h3 : 3 ∣ 3 ^ m := dvd_pow_self 3 (by omega)
    rcases hp.eq_one_or_self_of_dvd 3 h3 with h | h
    · omega
    · have : 3 ^ 2 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
      omega

theorem tmAsm_isCoatom_of_coatom_overgroups {G : Type*} [Group G] [Finite G] (M : Subgroup G)
    (hne : M ≠ ⊤) (h : ∀ H : Subgroup G, IsCoatom H → M < H → False) : IsCoatom M := by
  refine ⟨hne, fun H hH => ?_⟩
  rcases IsCoatomic.eq_top_or_exists_le_coatom H with hT | ⟨H', hH', hHH'⟩
  · exact hT
  · exact (h H' hH' (lt_of_lt_of_le hH hHH')).elim


theorem tmAsm_case_parabolic {G : Type*} [Group G] [Finite G] (E P H : Subgroup G) (c : ℕ)
    (hE3 : ∀ a ∈ E, a ^ 3 = 1) (hEH : Subgroup.normalizer (E : Set G) ≤ H) (hPH : P ≤ H)
    (hPn : (P.subgroupOf H).Normal) (hP2 : IsPGroup 2 P)
    (hcent : ∀ g ∈ Subgroup.normalizer (E : Set G), (∀ e ∈ E, g * e = e * g) → g ∈ E)
    (hdvd : 3 ^ (c + 1) ∣ Nat.card (Subgroup.normalizer (E : Set G)))
    (hv : padicValNat 3 (Nat.card (H ⧸ P.subgroupOf H)) ≤ c) : False := by
  have hinf := tmAsm_inf_eq_bot_of_two_group E P H hE3 hEH hPH hPn hP2 hcent
  have h1 := tmAsm_card_dvd_of_inf_eq_bot _ H P hEH hPH hPn hinf
  have h2 : 3 ^ (c + 1) ∣ Nat.card (H ⧸ P.subgroupOf H) := hdvd.trans h1
  have hpos : Nat.card (H ⧸ P.subgroupOf H) ≠ 0 := Nat.card_pos.ne'
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3 := (padicValNat_dvd_iff_le (p := 3) hpos).1 h2
  omega

theorem tmAsm_case_normal_three {G : Type*} [Group G] [Finite G] (E H Q : Subgroup G)
    (hE3 : IsPGroup 3 E) (hE0 : E ≠ ⊥) (hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hcent : ∀ g ∈ Subgroup.normalizer (E : Set G), (∀ e ∈ E, g * e = e * g) → g ∈ E)
    (hirr : ∀ F : Subgroup G, F ≤ E →
      (∀ g ∈ Subgroup.normalizer (E : Set G), ∀ f ∈ F, g * f * g⁻¹ ∈ F) → F = ⊥ ∨ F = E)
    (hsyl : ∃ P : Sylow 3 G, (P : Subgroup G) ≤ Subgroup.normalizer (E : Set G))
    (hMH : Subgroup.normalizer (E : Set G) < H) (hQH : Q ≤ H) (hQn : (Q.subgroupOf H).Normal)
    (hQ3 : Nat.card Q = 3) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQp : IsPGroup 3 Q := IsPGroup.of_card (n := 1) (by simpa using hQ3)
  have hQ0 : Q ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hQ3
    omega
  have hQc : ∀ h ∈ H, ∀ q ∈ Q, h * q * h⁻¹ ∈ Q := by
    intro h hh q hq
    have := hQn.conj_mem ⟨q, hQH hq⟩ (by simpa [Subgroup.mem_subgroupOf] using hq) ⟨h, hh⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have :=
    tmNormP_overgroup_le_normalizer 3 E hE3 hE0 hEab hcent hirr hsyl H Q hMH.le hQH hQc hQp hQ0
  exact absurd hMH (not_lt_of_ge this)

def tmAsm_conj {G : Type*} [Group G] (H J : Subgroup G) (hJH : J ≤ H)
    (hJn : (J.subgroupOf H).Normal) : H →* MulAut J where
  toFun h :=
    { toFun := fun j =>
        ⟨(h : G) * j * (h : G)⁻¹, by
          have := hJn.conj_mem ⟨j, hJH j.2⟩ (by simpa [Subgroup.mem_subgroupOf] using j.2) h
          simpa [Subgroup.mem_subgroupOf] using this⟩
      invFun := fun j =>
        ⟨(h : G)⁻¹ * j * (h : G), by
          have := hJn.conj_mem ⟨j, hJH j.2⟩ (by simpa [Subgroup.mem_subgroupOf] using j.2) h⁻¹
          simpa [Subgroup.mem_subgroupOf] using this⟩
      left_inv := fun j => by ext; simp [mul_assoc]
      right_inv := fun j => by ext; simp [mul_assoc]
      map_mul' := fun a b => by ext; simp [mul_assoc] }
  map_one' := by ext; simp
  map_mul' := fun a b => by ext; simp [mul_assoc]

theorem tmAsm_conj_injective {G : Type*} [Group G] (H J : Subgroup G) (hJH : J ≤ H)
    (hJn : (J.subgroupOf H).Normal) (hC : ∀ h ∈ H, (∀ j ∈ J, h * j = j * h) → h = 1) :
    Function.Injective (tmAsm_conj H J hJH hJn) := by
  rw [injective_iff_map_eq_one]
  intro h hh
  apply Subtype.ext
  apply hC h.1 h.2
  intro j hj
  have := congrArg (fun a : MulAut J => (a ⟨j, hj⟩ : G)) hh
  simp only [tmAsm_conj, MonoidHom.coe_mk, OneHom.coe_mk, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    MulAut.one_apply] at this
  calc (h : G) * j = ((h : G) * j * (h : G)⁻¹) * h := by group
    _ = j * h := by rw [this]

theorem tmAsm_inCatalog_of_kProper {G : Type} [Group G]
    (hK : CFSG.Assembly.KProper CFSG.Assembly.InCatalog G)
    (J : Subgroup G) (hJ : J ≠ ⊤) [IsSimpleGroup J] (hnonab : ∃ a b : J, a * b ≠ b * a) :
    CFSG.Assembly.InCatalog J :=
  CFSG.KCore.KProperNonab.catalogue_of_surjective CFSG.Assembly.inCatalog_isoInvariant hK J hJ
    hnonab (MonoidHom.id J) Function.surjective_id

end CFSG.StandardType.FrameRoute

end
