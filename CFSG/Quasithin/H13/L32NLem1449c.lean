module

public import CFSG.Quasithin.H13.L32NLem1449b
public import CFSG.Quasithin.H13.L32N1449Model

public section

namespace CFSG.Quasithin.H13.L1449

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L14411 L144B L1442M Mat8Cert
  O3Cert Q1447Cert Q1449Cert L1447

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)}

structure Good (G : Type) [Group G] [Finite G] (T L V V₂ : Subgroup G) (g : G)
    (D : HatModelU (fsuU T V)) (e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)) (c : ℕ)
    (x₀ : GL (Fin 8) (ZMod 2)) (i : G) : Prop extends Inv G T L V V₂ g D e x₀ i where
  hc : c < 2
  hx₀ : colsOf (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)) = xsS c
  imgH : img8 D e (l32nH T V) = gam c
  hU : fsuU T V = pCoreOf 2 (l32nH T V)

section Star

variable {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}

omit [Finite G] in
theorem star8_mul {a b : G} (ha : a ∈ l32nH T V) (hb : b ∈ l32nH T V) :
    matOf e (D.ρ ⟨a * b, HN ((l32nH T V).mul_mem ha hb)⟩) =
      matOf e (D.ρ ⟨a, HN ha⟩) * matOf e (D.ρ ⟨b, HN hb⟩) := by
  have e1 : (⟨a * b, HN ((l32nH T V).mul_mem ha hb)⟩ :
      ↥(Subgroup.normalizer (fsuU T V : Set G))) = ⟨a, HN ha⟩ * ⟨b, HN hb⟩ := rfl
  rw [e1, map_mul, map_mul]

omit [Finite G] in
theorem star8_inv {a : G} (ha : a ∈ l32nH T V) :
    matOf e (D.ρ ⟨a⁻¹, HN ((l32nH T V).inv_mem ha)⟩) = (matOf e (D.ρ ⟨a, HN ha⟩))⁻¹ := by
  have e1 : (⟨a⁻¹, HN ((l32nH T V).inv_mem ha)⟩ :
      ↥(Subgroup.normalizer (fsuU T V : Set G))) = (⟨a, HN ha⟩)⁻¹ := rfl
  rw [e1, map_inv, map_inv]

omit [Finite G] in
theorem star8_pow {a : G} (ha : a ∈ l32nH T V) (n : ℕ) :
    matOf e (D.ρ ⟨a ^ n, HN ((l32nH T V).pow_mem ha n)⟩) = matOf e (D.ρ ⟨a, HN ha⟩) ^ n := by
  have e1 : (⟨a ^ n, HN ((l32nH T V).pow_mem ha n)⟩ :
      ↥(Subgroup.normalizer (fsuU T V : Set G))) = ⟨a, HN ha⟩ ^ n := by
    apply Subtype.ext
    simp
  rw [e1, map_pow, map_pow]

end Star

namespace Good

section Basic

variable {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {c : ℕ} {x₀ : GL (Fin 8) (ZMod 2)} {i : G}
  (C : Good G T L V V₂ g D e c x₀ i)
include C

theorem UH : fsuU T V ≤ l32nH T V := by
  rw [C.hU]
  exact CFSG.LieType.BorelTits.pCoreOf_le 2 _

theorem U_two : IsPGroup 2 ↥(fsuU T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [C.hU]
  exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _

theorem star_U {u : G} (hu : u ∈ fsuU T V) : matOf e (D.ρ ⟨u, HN (C.UH hu)⟩) = 1 := by
  rw [L128A.HatU.rho_eq_one_of_mem D C.base.comm_center hu, map_one]

theorem mem_U_of_star {h : G} (hh : h ∈ l32nH T V) (h1 : matOf e (D.ρ ⟨h, HN hh⟩) = 1) :
    h ∈ fsuU T V := by
  have h2 : D.ρ ⟨h, HN hh⟩ = 1 := matOf_injective e (h1.trans (map_one _).symm)
  rw [C.hU, ← C.base.cHat]
  exact (L14332.rho_eq_one_iff_mem hh (HN hh)).mp h2

theorem pow_mem_U {h : G} (hh : h ∈ l32nH T V) {n : ℕ}
    (hn : matOf e (D.ρ ⟨h, HN hh⟩) ^ n = 1) : h ^ n ∈ fsuU T V := by
  refine C.mem_U_of_star ((l32nH T V).pow_mem hh n) ?_
  have e1 : (⟨h ^ n, HN ((l32nH T V).pow_mem hh n)⟩ :
      ↥(Subgroup.normalizer (fsuU T V : Set G))) = ⟨h, HN hh⟩ ^ n := by
    apply Subtype.ext
    simp
  rw [e1, map_pow, map_pow, hn]

theorem exists_conj_of_invol {j : G} (hjU : j * i⁻¹ ∈ fsuU T V) (hjj : j * j = 1) :
    ∃ u ∈ fsuU T V, ∃ ζ ∈ fsuV1 T V, j = u * (i * ζ) * u⁻¹ := by
  set w' := j * i⁻¹ with hw'
  have hj : j = w' * i := by rw [hw']; group
  have h1 : i * w' * i⁻¹ = w'⁻¹ := by
    have h2 : w' * i * (w' * i) = 1 := by rw [← hj]; exact hjj
    calc i * w' * i⁻¹ = w'⁻¹ * (w' * i * (w' * i)) * (i⁻¹ * i⁻¹) := by group
      _ = w'⁻¹ * (i⁻¹ * i⁻¹) := by rw [h2, mul_one]
      _ = w'⁻¹ := by rw [C.y_inv, C.yy, mul_one]
  have hfix : (x₀ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e (D.π w')) = e (D.π w') := by
    rw [← C.e_rho, D.ρ_π _ w' hjU]
    show e (D.π (i * w' * i⁻¹)) = _
    rw [h1, L128A.HatU.π_inv D hjU, map_neg]
    funext k
    exact CharTwo.neg_eq _
  obtain ⟨u₀, hu₀, ζ, hζ, hw0⟩ := C.exists_comm_of_fix hjU hfix
  refine ⟨u₀, hu₀, ζ, hζ, ?_⟩
  have hζc : ζ ∈ centerOf (fsuU T V) := by rw [C.base.zU]; exact hζ
  have hζu : u₀ * ζ = ζ * u₀ := Subgroup.mem_centralizer_iff.mp hζc.2 u₀ hu₀
  have hζu' : u₀⁻¹ * ζ = ζ * u₀⁻¹ := by
    calc u₀⁻¹ * ζ = u₀⁻¹ * (ζ * u₀) * u₀⁻¹ := by group
      _ = u₀⁻¹ * (u₀ * ζ) * u₀⁻¹ := by rw [hζu]
      _ = ζ * u₀⁻¹ := by group
  have hζi : i * ζ = ζ * i := C.comm_V1 C.yH hζ
  rw [hj, hw0]
  calc u₀ * i * u₀⁻¹ * i⁻¹ * ζ * i = u₀ * i * u₀⁻¹ * (i⁻¹ * (ζ * i)) := by group
    _ = u₀ * i * u₀⁻¹ * (i⁻¹ * (i * ζ)) := by rw [hζi]
    _ = u₀ * i * (u₀⁻¹ * ζ) := by group
    _ = u₀ * i * (ζ * u₀⁻¹) := by rw [hζu']
    _ = u₀ * (i * ζ) * u₀⁻¹ := by group

theorem exists_lift {h : G} (hh : h ∈ l32nH T V)
    (hcomm : matOf e (D.ρ ⟨h, HN hh⟩) * x₀ = x₀ * matOf e (D.ρ ⟨h, HN hh⟩))
    (h15 : matOf e (D.ρ ⟨h, HN hh⟩) ^ 15 = 1) :
    ∃ u ∈ fsuU T V, (u⁻¹ * h) * i = i * (u⁻¹ * h) := by
  obtain ⟨_, S⟩ := C.base.set14
  obtain ⟨z, -, -, hz, hz1, -⟩ := S.exists_basis
  have hiN := C.yN
  have hjH : h * i * h⁻¹ * i⁻¹ ∈ l32nH T V :=
    (l32nH T V).mul_mem ((l32nH T V).mul_mem ((l32nH T V).mul_mem hh C.yH)
      ((l32nH T V).inv_mem hh)) ((l32nH T V).inv_mem C.yH)
  have hjU : h * i * h⁻¹ * i⁻¹ ∈ fsuU T V := by
    refine C.mem_U_of_star hjH ?_
    have e1 : (⟨h * i * h⁻¹ * i⁻¹, HN hjH⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) =
        ⟨h, HN hh⟩ * ⟨i, hiN⟩ * ⟨h, HN hh⟩⁻¹ * ⟨i, hiN⟩⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv, map_mul, map_mul, map_mul, map_inv,
      map_inv, C.yStar, hcomm]
    group
  have hjj : (h * i * h⁻¹) * (h * i * h⁻¹) = 1 := by
    calc (h * i * h⁻¹) * (h * i * h⁻¹) = h * (i * i) * h⁻¹ := by group
      _ = 1 := by rw [C.yy]; group
  obtain ⟨u₀, hu₀, ζ, hζ, hj⟩ := C.exists_conj_of_invol hjU hjj
  rcases S.eq_of_mem_V1 hz hz1 hζ with rfl | rfl
  · refine ⟨u₀, hu₀, ?_⟩
    have h1 : h * i * h⁻¹ = u₀ * i * u₀⁻¹ := by rw [hj, mul_one]
    calc u₀⁻¹ * h * i = u₀⁻¹ * (h * i * h⁻¹) * h := by group
      _ = u₀⁻¹ * (u₀ * i * u₀⁻¹) * h := by rw [h1]
      _ = i * (u₀⁻¹ * h) := by group
  · by_cases hiz : ∃ u₁ ∈ fsuU T V, u₁ * i * u₁⁻¹ = i * ζ
    · obtain ⟨u₁, hu₁, h1⟩ := hiz
      refine ⟨u₀ * u₁, (fsuU T V).mul_mem hu₀ hu₁, ?_⟩
      have h2 : h * i * h⁻¹ = (u₀ * u₁) * i * (u₀ * u₁)⁻¹ := by
        rw [hj, ← h1]
        group
      calc (u₀ * u₁)⁻¹ * h * i = (u₀ * u₁)⁻¹ * (h * i * h⁻¹) * h := by group
        _ = (u₀ * u₁)⁻¹ * ((u₀ * u₁) * i * (u₀ * u₁)⁻¹) * h := by rw [h2]
        _ = i * ((u₀ * u₁)⁻¹ * h) := by group
    · exfalso
      push Not at hiz
      have hζc : ζ ∈ centerOf (fsuU T V) := by rw [C.base.zU]; exact hζ
      have hzh : ∀ m : ℕ, h * ζ ^ m * h⁻¹ = ζ ^ m := fun m => by
        have h1 : ζ ^ m ∈ fsuV1 T V := (fsuV1 T V).pow_mem hζ m
        rw [C.comm_V1 hh h1]
        group
      have hzu : ∀ m : ℕ, u₀⁻¹ * ζ ^ m = ζ ^ m * u₀⁻¹ := fun m => by
        have h1 : ζ ^ m ∈ centerOf (fsuU T V) := (centerOf (fsuU T V)).pow_mem hζc m
        have h2 := Subgroup.mem_centralizer_iff.mp h1.2 u₀⁻¹ ((fsuU T V).inv_mem hu₀)
        exact h2
      have key : ∀ n : ℕ, ∃ u ∈ fsuU T V, h ^ n * i * (h ^ n)⁻¹ = u * (i * ζ ^ n) * u⁻¹ := by
        intro n
        induction n with
        | zero => exact ⟨1, one_mem _, by simp⟩
        | succ n ih =>
          obtain ⟨u, hu, hun⟩ := ih
          refine ⟨h * u * h⁻¹ * u₀,
            (fsuU T V).mul_mem (L128A.HatU.conj_mem (HN hh) hu) hu₀, ?_⟩
          have hj' : h * i * h⁻¹ = u₀ * (i * ζ) * u₀⁻¹ := hj
          calc h ^ (n + 1) * i * (h ^ (n + 1))⁻¹ = h * (h ^ n * i * (h ^ n)⁻¹) * h⁻¹ := by
                rw [pow_succ']
                group
            _ = h * (u * (i * ζ ^ n) * u⁻¹) * h⁻¹ := by rw [hun]
            _ = (h * u * h⁻¹) * (h * i * h⁻¹) * (h * ζ ^ n * h⁻¹) * (h * u * h⁻¹)⁻¹ := by
                group
            _ = (h * u * h⁻¹) * (u₀ * (i * ζ) * u₀⁻¹) * ζ ^ n * (h * u * h⁻¹)⁻¹ := by
                rw [hj', hzh]
            _ = (h * u * h⁻¹) * u₀ * (i * ζ) * (u₀⁻¹ * ζ ^ n) * (h * u * h⁻¹)⁻¹ := by group
            _ = (h * u * h⁻¹) * u₀ * (i * ζ) * (ζ ^ n * u₀⁻¹) * (h * u * h⁻¹)⁻¹ := by
                rw [hzu]
            _ = (h * u * h⁻¹ * u₀) * (i * ζ ^ (n + 1)) * (h * u * h⁻¹ * u₀)⁻¹ := by
                rw [pow_succ']
                group
      obtain ⟨u, hu, hu15⟩ := key 15
      have h15U := C.pow_mem_U hh h15
      have hζ2 : ζ * ζ = 1 := S.mul_self_V (Subgroup.mem_inf.mp hζ).1
      have hζ15 : ζ ^ 15 = ζ := by
        rw [show 15 = 2 * 7 + 1 by rfl, pow_succ, pow_mul, sq, hζ2, one_pow, one_mul]
      apply hiz (u⁻¹ * h ^ 15) ((fsuU T V).mul_mem ((fsuU T V).inv_mem hu) h15U)
      calc u⁻¹ * h ^ 15 * i * (u⁻¹ * h ^ 15)⁻¹ = u⁻¹ * (h ^ 15 * i * (h ^ 15)⁻¹) * u := by group
        _ = u⁻¹ * (u * (i * ζ ^ 15) * u⁻¹) * u := by rw [hu15]
        _ = i * ζ := by rw [hζ15]; group

theorem conj_mem_dI {h : G} (hh : h ∈ l32nH T V)
    (hcomm : matOf e (D.ρ ⟨h, HN hh⟩) * x₀ = x₀ * matOf e (D.ρ ⟨h, HN hh⟩)) {d : G}
    (hd : d ∈ dI T V i) : h * d * h⁻¹ ∈ dI T V i := by
  have hrI : ∀ r ∈ rI T V i, h * r * h⁻¹ ∈ rI T V i := by
    intro r hr
    have hrU := hr.1
    have h1 : h * r * h⁻¹ ∈ fsuU T V := L128A.HatU.conj_mem (HN hh) hrU
    refine (C.mem_rI_iff h1).mpr ?_
    have h2 : e (D.π (h * r * h⁻¹)) =
        (matOf e (D.ρ ⟨h, HN hh⟩) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e (D.π r)) := by
      rw [matOf_mulVec, D.ρ_π _ r hrU]
    rw [h2, Matrix.mulVec_mulVec, ← Units.val_mul, ← hcomm, Units.val_mul, ← Matrix.mulVec_mulVec,
      (C.mem_rI_iff hrU).mp hr]
  have hi : h * i * h⁻¹ ∈ dI T V i := by
    have hjH : h * i * h⁻¹ * i⁻¹ ∈ l32nH T V :=
      (l32nH T V).mul_mem ((l32nH T V).mul_mem ((l32nH T V).mul_mem hh C.yH)
        ((l32nH T V).inv_mem hh)) ((l32nH T V).inv_mem C.yH)
    have hjU : h * i * h⁻¹ * i⁻¹ ∈ fsuU T V := by
      refine C.mem_U_of_star hjH ?_
      rw [star8_mul ((l32nH T V).mul_mem ((l32nH T V).mul_mem hh C.yH) ((l32nH T V).inv_mem hh))
        ((l32nH T V).inv_mem C.yH), star8_mul ((l32nH T V).mul_mem hh C.yH)
        ((l32nH T V).inv_mem hh), star8_mul hh C.yH, star8_inv hh, star8_inv C.yH, C.yStar,
        hcomm]
      group
    have hjj : (h * i * h⁻¹) * (h * i * h⁻¹) = 1 := by
      calc (h * i * h⁻¹) * (h * i * h⁻¹) = h * (i * i) * h⁻¹ := by group
        _ = 1 := by rw [C.yy]; group
    obtain ⟨u, hu, ζ, hζ, hj⟩ := C.exists_conj_of_invol hjU hjj
    refine C.mem_dI_iff.mpr (Or.inr ?_)
    have hw : u * i * u⁻¹ * i⁻¹ ∈ rI T V i :=
      ⟨C.comm_mem hu, Subgroup.mem_centralizer_singleton_iff.mpr (C.comm_comm hu)⟩
    have hζc : ζ ∈ centerOf (fsuU T V) := by rw [C.base.zU]; exact hζ
    have hζu : u⁻¹ * ζ = ζ * u⁻¹ :=
      Subgroup.mem_centralizer_iff.mp hζc.2 u⁻¹ ((fsuU T V).inv_mem hu)
    have hζi : i * ζ = ζ * i := C.comm_V1 C.yH hζ
    have e1 : h * i * h⁻¹ * i = (u * i * u⁻¹ * i⁻¹) * ζ := by
      rw [hj]
      calc u * (i * ζ) * u⁻¹ * i = u * i * (ζ * u⁻¹) * i := by group
        _ = u * i * (u⁻¹ * ζ) * i := by rw [hζu]
        _ = u * i * u⁻¹ * (ζ * i) := by group
        _ = u * i * u⁻¹ * (i * ζ) := by rw [hζi]
        _ = u * i * u⁻¹ * i * ζ := by group
        _ = (u * i * u⁻¹ * i⁻¹) * ζ := by rw [C.y_inv]
    rw [e1]
    exact (rI T V i).mul_mem hw (C.V1_le_rI hζ)
  rcases C.mem_dI_iff.mp hd with hd' | hd'
  · exact rI_le_dI (hrI d hd')
  · have e1 : h * d * h⁻¹ = (h * (d * i) * h⁻¹) * (h * i * h⁻¹)⁻¹ := by group
    rw [e1]
    exact (dI T V i).mul_mem (rI_le_dI (hrI _ hd')) ((dI T V i).inv_mem hi)

end Basic

section Cert

variable
  {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {c : ℕ} {x₀ : GL (Fin 8) (ZMod 2)} {i : G}
  (C : Good G T L V V₂ g D e c x₀ i)
include C

theorem mem_dI_of_two {y : G} (hyH : y ∈ l32nH T V) (hyi : y * i = i * y) {k : ℕ}
    (hy2 : y ^ 2 ^ k = 1)
    (hcl : ∀ h ∈ l32nH T V, h * i = i * h → ∃ m : ℕ, (y⁻¹ * h⁻¹ * y * h) ^ 2 ^ m = 1) :
    y ∈ dI T V i := by
  set Y := matOf e (D.ρ ⟨y, HN hyH⟩) with hY
  have hYx : Y * x₀ = x₀ * Y := by
    have h1 := star8_mul (e := e) hyH C.yH
    have h2 := star8_mul (e := e) C.yH hyH
    have e2 : matOf e (D.ρ ⟨y * i, HN ((l32nH T V).mul_mem hyH C.yH)⟩) =
        matOf e (D.ρ ⟨i * y, HN ((l32nH T V).mul_mem C.yH hyH)⟩) := by
      congr 2
      exact Subtype.ext hyi
    rw [h1, h2, C.yStar] at e2
    exact e2
  have hYΓ : Y ∈ gam c := by
    rw [← C.imgH]
    exact (mem_img8 D e).mpr ⟨y, hyH, HN hyH, rfl⟩
  have hY16 : Y ^ 16 = 1 := by
    have h240 := cen_pow C.hc C.hx₀ hYΓ hYx
    have h2k : Y ^ 2 ^ k = 1 := by
      rw [hY, ← star8_pow hyH]
      have e1 : (⟨y ^ 2 ^ k, HN ((l32nH T V).pow_mem hyH _)⟩ :
          ↥(Subgroup.normalizer (fsuU T V : Set G))) = 1 := Subtype.ext hy2
      rw [e1, map_one, map_one]
    obtain ⟨j, hj, hjY⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h2k)
    have h2 : 2 ^ j ∣ 240 := hjY ▸ orderOf_dvd_of_pow_eq_one h240
    have hj4 : j ≤ 4 := by
      by_contra hj4
      have h5 : 2 ^ 5 ∣ 240 := (Nat.pow_dvd_pow 2 (by omega)).trans h2
      norm_num at h5
    rw [← orderOf_dvd_iff_pow_eq_one, hjY]
    exact Nat.pow_dvd_pow 2 hj4
  by_cases hY1 : Y = 1
  · exact rI_le_dI ⟨C.mem_U_of_star hyH hY1,
      Subgroup.mem_centralizer_singleton_iff.mpr hyi⟩
  by_cases hYx₀ : Y = x₀
  · refine C.mem_dI_iff.mpr (Or.inr ⟨?_, ?_⟩)
    · refine C.mem_U_of_star ((l32nH T V).mul_mem hyH C.yH) ?_
      rw [star8_mul hyH C.yH, ← hY, hYx₀, C.yStar, x0_sq C.hc C.hx₀]
    · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc y * i * i = i * y * i := by rw [hyi]
        _ = i * (y * i) := by group
  exfalso
  obtain ⟨a, haΓ, hax, ha15, hc15, hc1⟩ := cen_spec C.hc (x0_mem C.hc C.hx₀).1
    (x0_not_mem_omega3 C.hc C.hx₀) hYΓ hYx hY16 hY1 hYx₀
  rw [← C.imgH] at haΓ
  obtain ⟨h, hh, hhN, rfl⟩ := (mem_img8 D e).mp haΓ
  obtain ⟨u, hu, hui⟩ := C.exists_lift hh hax ha15
  have hh'H : u⁻¹ * h ∈ l32nH T V := (l32nH T V).mul_mem ((l32nH T V).inv_mem (C.UH hu)) hh
  have hh'star : matOf e (D.ρ ⟨u⁻¹ * h, HN hh'H⟩) = matOf e (D.ρ ⟨h, hhN⟩) := by
    rw [star8_mul ((l32nH T V).inv_mem (C.UH hu)) hh, star8_inv (C.UH hu), C.star_U hu, inv_one,
      one_mul]
  obtain ⟨m, hm⟩ := hcl _ hh'H hui
  have hwH : y⁻¹ * (u⁻¹ * h)⁻¹ * y * (u⁻¹ * h) ∈ l32nH T V :=
    (l32nH T V).mul_mem ((l32nH T V).mul_mem ((l32nH T V).mul_mem ((l32nH T V).inv_mem hyH)
      ((l32nH T V).inv_mem hh'H)) hyH) hh'H
  have m1 : y⁻¹ * (u⁻¹ * h)⁻¹ ∈ l32nH T V :=
    (l32nH T V).mul_mem ((l32nH T V).inv_mem hyH) ((l32nH T V).inv_mem hh'H)
  have m2 : y⁻¹ * (u⁻¹ * h)⁻¹ * y ∈ l32nH T V := (l32nH T V).mul_mem m1 hyH
  have hwstar : matOf e (D.ρ ⟨_, HN hwH⟩) =
      Y⁻¹ * (matOf e (D.ρ ⟨h, hhN⟩))⁻¹ * (Y * matOf e (D.ρ ⟨h, hhN⟩)) := by
    rw [star8_mul m2 hh'H, star8_mul m1 hyH, star8_mul ((l32nH T V).inv_mem hyH)
      ((l32nH T V).inv_mem hh'H), star8_inv hyH, star8_inv hh'H, hh'star, ← hY]
    group
  have hc2 : (Y⁻¹ * (matOf e (D.ρ ⟨h, hhN⟩))⁻¹ * (Y * matOf e (D.ρ ⟨h, hhN⟩))) ^ 2 ^ m = 1 := by
    rw [← hwstar, ← star8_pow hwH]
    have e1 : (⟨(y⁻¹ * (u⁻¹ * h)⁻¹ * y * (u⁻¹ * h)) ^ 2 ^ m, HN ((l32nH T V).pow_mem hwH _)⟩ :
        ↥(Subgroup.normalizer (fsuU T V : Set G))) = 1 := Subtype.ext hm
    rw [e1, map_one, map_one]
  apply hc1
  obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hc2)
  have h15 := orderOf_dvd_of_pow_eq_one hc15
  rw [hjc] at h15
  cases j with
  | zero => rwa [pow_zero, orderOf_eq_one_iff] at hjc
  | succ j =>
    have h2 : 2 ∣ 15 := (dvd_pow_self 2 (Nat.succ_ne_zero j)).trans h15
    norm_num at h2

theorem le_dI_of_normal {O : Subgroup G} (hO : IsPGroup 2 ↥O) (hOH : O ≤ l32nH T V)
    (hOi : ∀ y ∈ O, y * i = i * y)
    (hON : ∀ h ∈ l32nH T V, h * i = i * h → ∀ y ∈ O, h⁻¹ * y * h ∈ O) : O ≤ dI T V i := by
  intro y hy
  obtain ⟨k, hk⟩ := hO ⟨y, hy⟩
  refine C.mem_dI_of_two (hOH hy) (hOi y hy) (k := k) (by simpa using congrArg Subtype.val hk)
    fun h hh hhi => ?_
  have hmem : y⁻¹ * h⁻¹ * y * h ∈ O := by
    have := O.mul_mem (O.inv_mem hy) (hON h hh hhi y hy)
    simpa [mul_assoc] using this
  obtain ⟨m, hm⟩ := hO ⟨_, hmem⟩
  exact ⟨m, by simpa using congrArg Subtype.val hm⟩

end Cert

end Good

end CFSG.Quasithin.H13.L1449
