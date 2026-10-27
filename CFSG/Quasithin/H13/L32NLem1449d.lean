module

public import CFSG.Quasithin.H13.L32NLem1449c

public section

namespace CFSG.Quasithin.H13.L1449

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin L14411 L144B L1442M Mat8Cert
  O3Cert Q1447Cert Q1449Cert L1447

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}
  {D : HatModelU (fsuU T V)}

namespace Good

section Basic

variable {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {c : ℕ} {x₀ : GL (Fin 8) (ZMod 2)} {i : G}
  (C : Good G T L V V₂ g D e c x₀ i)
include C

theorem card_fix_le {y : G} (hy : y ∈ l32nH T V) :
    Nat.card {w : Fin 8 → ZMod 2 //
      (matOf e (D.ρ ⟨y, HN hy⟩) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w = w} ≤
      Nat.card (rI T V y) := by
  classical
  obtain ⟨_, S⟩ := C.base.set14
  have hUH := C.UH
  have hcen : ∀ ζ ∈ fsuV1 T V, ∀ h ∈ l32nH T V, h * ζ = ζ * h := fun ζ hζ h hh =>
    C.comm_V1 hh hζ
  obtain ⟨F, hF⟩ : ∃ F : Subgroup G,
      ∀ u, u ∈ F ↔ u ∈ fsuU T V ∧ y * u * y⁻¹ * u⁻¹ ∈ fsuV1 T V := by
    refine ⟨{ carrier := {u | u ∈ fsuU T V ∧ y * u * y⁻¹ * u⁻¹ ∈ fsuV1 T V}
              one_mem' := ⟨one_mem _, by simp⟩
              mul_mem' := ?_
              inv_mem' := ?_ }, fun u => Iff.rfl⟩
    · rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
      refine ⟨mul_mem ha hb, ?_⟩
      have hc := hcen _ hb' (y * a * y⁻¹) (hUH (L128A.HatU.conj_mem (HN hy) ha))
      have e1 : y * (a * b) * y⁻¹ * (a * b)⁻¹ =
          (y * b * y⁻¹ * b⁻¹) * (y * a * y⁻¹ * a⁻¹) := by
        calc y * (a * b) * y⁻¹ * (a * b)⁻¹ =
            (y * a * y⁻¹) * (y * b * y⁻¹ * b⁻¹) * a⁻¹ := by group
          _ = (y * b * y⁻¹ * b⁻¹) * (y * a * y⁻¹) * a⁻¹ := by rw [hc]
          _ = _ := by group
      rw [e1]
      exact mul_mem hb' ha'
    · rintro a ⟨ha, ha'⟩
      refine ⟨inv_mem ha, ?_⟩
      have hc := hcen _ (inv_mem ha') a (hUH ha)
      have e1 : y * a⁻¹ * y⁻¹ * a⁻¹⁻¹ = (y * a * y⁻¹ * a⁻¹)⁻¹ := by
        calc y * a⁻¹ * y⁻¹ * a⁻¹⁻¹ = a⁻¹ * ((y * a * y⁻¹ * a⁻¹)⁻¹ * a) := by group
          _ = a⁻¹ * (a * (y * a * y⁻¹ * a⁻¹)⁻¹) := by rw [hc]
          _ = (y * a * y⁻¹ * a⁻¹)⁻¹ := by group
      rw [e1]
      exact inv_mem ha'
  have hFU : F ≤ fsuU T V := fun u hu => ((hF u).mp hu).1
  have hZF : centerOf (fsuU T V) ≤ F := by
    rw [C.base.zU]
    intro ζ hζ
    refine (hF ζ).mpr ⟨V_le_U (C.base.plane.1.1 (C.base.plane.2 hζ)), ?_⟩
    rw [hcen ζ hζ y hy, mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have h1 := card_eq_mul_card_range D hFU hZF
  have hZ2 : Nat.card (centerOf (fsuU T V)) = 2 := by
    rw [l32n_card_centerOf]
    exact C.base.ext.2.2.2
  set Y := matOf e (D.ρ ⟨y, HN hy⟩) with hY
  have hfix : ∀ u ∈ fsuU T V, (Y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e (D.π u)) =
      e (D.π u) ↔ u ∈ F := by
    intro u hu
    have hyu : y * u * y⁻¹ ∈ fsuU T V := L128A.HatU.conj_mem (HN hy) hu
    rw [hY, matOf_mulVec, D.ρ_π _ u hu, hF]
    constructor
    · intro h
      refine ⟨hu, ?_⟩
      have h2 := (D.π_eq_iff _ hyu _ hu).mp (e.injective h)
      rw [C.base.zU] at h2
      have h3 := (fsuV1 T V).inv_mem h2
      have h4 : y * u * y⁻¹ * u⁻¹ = u * ((y * u * y⁻¹)⁻¹ * u)⁻¹ * u⁻¹ := by group
      rw [h4, hcen _ h3 u (hUH hu), mul_inv_cancel_right]
      exact h3
    · rintro ⟨-, h⟩
      congr 1
      have h2 : y * u * y⁻¹ = (y * u * y⁻¹ * u⁻¹) * u := by group
      rw [h2, D.π_mul _ (V_le_U (C.base.plane.1.1 (C.base.plane.2 h))) _ hu,
        (L128A.HatU.π_eq_zero_iff D (V_le_U (C.base.plane.1.1 (C.base.plane.2 h)))).mpr
          (by rw [C.base.zU]; exact h), zero_add]
  have h2 : Nat.card ((piHom D).comp (Subgroup.inclusion hFU)).range =
      Nat.card {w : Fin 8 → ZMod 2 // (Y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w = w} := by
    refine Nat.card_congr
      { toFun := fun m => ⟨e (Multiplicative.toAdd (m : Multiplicative D.V)), ?_⟩
        invFun := fun w => ⟨Multiplicative.ofAdd (e.symm w), ?_⟩
        left_inv := fun m => by ext; simp
        right_inv := fun w => by ext; simp }
    · obtain ⟨x, hx, hxv⟩ := (mem_range_piHom D hFU _).mp
        (show Multiplicative.ofAdd (Multiplicative.toAdd (m : Multiplicative D.V)) ∈ _ from m.2)
      rw [← hxv]
      exact (hfix x (hFU hx)).mpr hx
    · obtain ⟨u, hu, hue⟩ := D.π_surj (e.symm (w : Fin 8 → ZMod 2))
      have hw : (Y : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e (D.π u)) = e (D.π u) := by
        rw [hue, LinearEquiv.apply_symm_apply]
        exact w.2
      exact (mem_range_piHom D hFU _).mpr ⟨u, (hfix u hu).mp hw, hue⟩
  let f : ↥F →* G :=
    { toFun := fun u => y * (u : G) * y⁻¹ * (u : G)⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        have haU := ((hF a).mp a.2).1
        have hb := ((hF b).mp b.2).2
        have hc := hcen _ hb (y * (a : G) * y⁻¹) (hUH (L128A.HatU.conj_mem (HN hy) haU))
        have hζa : y * (a : G) * y⁻¹ * (a : G)⁻¹ ∈ l32nH T V :=
          (l32nH T V).mul_mem ((l32nH T V).mul_mem ((l32nH T V).mul_mem hy (hUH haU))
            ((l32nH T V).inv_mem hy)) ((l32nH T V).inv_mem (hUH haU))
        show y * ((a : G) * b) * y⁻¹ * ((a : G) * b)⁻¹ =
          (y * (a : G) * y⁻¹ * (a : G)⁻¹) * (y * (b : G) * y⁻¹ * (b : G)⁻¹)
        calc y * ((a : G) * b) * y⁻¹ * ((a : G) * b)⁻¹ =
            (y * (a : G) * y⁻¹) * (y * (b : G) * y⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ := by group
          _ = (y * (b : G) * y⁻¹ * (b : G)⁻¹) * (y * (a : G) * y⁻¹) * (a : G)⁻¹ := by rw [hc]
          _ = (y * (b : G) * y⁻¹ * (b : G)⁻¹) * (y * (a : G) * y⁻¹ * (a : G)⁻¹) := by group
          _ = (y * (a : G) * y⁻¹ * (a : G)⁻¹) * (y * (b : G) * y⁻¹ * (b : G)⁻¹) :=
            (hcen _ hb _ hζa).symm }
  have hfr : f.range ≤ fsuV1 T V := by
    rintro _ ⟨u, rfl⟩
    exact ((hF u).mp u.2).2
  have hfk : Nat.card f.ker ≤ Nat.card (rI T V y) := by
    refine Nat.card_le_card_of_injective
      (fun x => ⟨((x : ↥F) : G), hFU (x : ↥F).2, ?_⟩) ?_
    · have hx : y * ((x : ↥F) : G) * y⁻¹ * ((x : ↥F) : G)⁻¹ = 1 := x.2
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      calc ((x : ↥F) : G) * y = (y * ((x : ↥F) : G) * y⁻¹ * ((x : ↥F) : G)⁻¹)⁻¹ *
          (y * (x : ↥F)) := by group
        _ = y * ((x : ↥F) : G) := by rw [hx, inv_one, one_mul]
    · intro a b hab
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (Subtype.val : ↥(rI T V y) → G) hab
  have h3 := Subgroup.card_mul_index f.ker
  rw [Subgroup.index_ker] at h3
  have h4 : Nat.card f.range ≤ 2 := (Subgroup.card_le_of_le hfr).trans S.card_V1.le
  have h5 : Nat.card F ≤ Nat.card (rI T V y) * 2 := by
    rw [← h3]
    exact Nat.mul_le_mul hfk h4
  rw [h1, hZ2, h2] at h5
  omega

end Basic

section Cert

variable
  {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)} {c : ℕ} {x₀ : GL (Fin 8) (ZMod 2)} {i : G}
  (C : Good G T L V V₂ g D e c x₀ i)
include C

theorem exists_out {z x : G} (hz : z ∈ fsuV1 T V) (hz1 : z ≠ 1) (hx : x⁻¹ * z * x = i) :
    (∀ u ∈ fsuU T V, x⁻¹ * u * x ∈ Subgroup.normalizer (dI T V i : Set G)) ∧
      ∃ u ∈ fsuU T V, x⁻¹ * u * x ∉ l32nH T V := by
  classical
  obtain ⟨_, S⟩ := C.base.set14
  have hUH := C.UH
  have hU2 := C.U_two
  set z' := x * z * x⁻¹ with hz'
  have hzx : z = x * i * x⁻¹ := by rw [← hx]; group
  have hmemH : ∀ w, w * z = z * w → w ∈ l32nH T V := fun w hw =>
    S.mem_g1 hz hz1 (by rw [hw]; group)
  have hHz : ∀ w ∈ l32nH T V, w * z = z * w := fun w hw => C.comm_V1 hw hz
  have hz'H : z' ∈ l32nH T V := by
    refine hmemH z' ?_
    have h1 := hHz i C.yH
    rw [← hx] at h1
    calc x * z * x⁻¹ * z = x * (z * (x⁻¹ * z * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * z * x) * z) * x⁻¹ := by rw [← h1]
      _ = z * (x * z * x⁻¹) := by group
  have hconj : ∀ w ∈ l32nH T V, w * i = i * w →
      x * w * x⁻¹ ∈ l32nH T V ∧ (x * w * x⁻¹) * z' = z' * (x * w * x⁻¹) := by
    intro w hw hwi
    refine ⟨hmemH _ ?_, ?_⟩
    · rw [hzx]
      calc x * w * x⁻¹ * (x * i * x⁻¹) = x * (w * i) * x⁻¹ := by group
        _ = x * (i * w) * x⁻¹ := by rw [hwi]
        _ = x * i * x⁻¹ * (x * w * x⁻¹) := by group
    · rw [hz']
      calc x * w * x⁻¹ * (x * z * x⁻¹) = x * (w * z) * x⁻¹ := by group
        _ = x * (z * w) * x⁻¹ := by rw [hHz w hw]
        _ = x * z * x⁻¹ * (x * w * x⁻¹) := by group
  have hconj' : ∀ w ∈ l32nH T V, w * z' = z' * w →
      x⁻¹ * w * x ∈ l32nH T V ∧ (x⁻¹ * w * x) * i = i * (x⁻¹ * w * x) := by
    intro w hw hwz
    refine ⟨hmemH _ ?_, ?_⟩
    · calc x⁻¹ * w * x * z = x⁻¹ * (w * (x * z * x⁻¹)) * x := by group
        _ = x⁻¹ * ((x * z * x⁻¹) * w) * x := by rw [← hz', hwz]
        _ = z * (x⁻¹ * w * x) := by group
    · rw [← hx]
      calc x⁻¹ * w * x * (x⁻¹ * z * x) = x⁻¹ * (w * z) * x := by group
        _ = x⁻¹ * (z * w) * x := by rw [hHz w hw]
        _ = x⁻¹ * z * x * (x⁻¹ * w * x) := by group
  have hmapmem : ∀ (K : Subgroup G) (w : G),
      w ∈ K.map (MulAut.conj x⁻¹).toMonoidHom ↔ x * w * x⁻¹ ∈ K := by
    intro K w
    constructor
    · rintro ⟨k, hk, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hk
    · intro hw
      exact ⟨x * w * x⁻¹, hw, by simp [mul_assoc]⟩
  have hmir : ∀ K : Subgroup G, IsPGroup 2 ↥K → K ≤ l32nH T V → (∀ k ∈ K, k * z' = z' * k) →
      (∀ w ∈ l32nH T V, w * z' = z' * w → ∀ k ∈ K, w * k * w⁻¹ ∈ K) →
      K.map (MulAut.conj x⁻¹).toMonoidHom ≤ dI T V i := by
    intro K hK2 hKH hKz hKN
    refine C.le_dI_of_normal (hK2.map _) ?_ ?_ ?_
    · intro w hw
      have hk := (hmapmem K w).mp hw
      have := (hconj' _ (hKH hk) (hKz _ hk)).1
      simpa [mul_assoc] using this
    · intro w hw
      have hk := (hmapmem K w).mp hw
      have := (hconj' _ (hKH hk) (hKz _ hk)).2
      simpa [mul_assoc] using this
    · intro h hh hhi w hw
      have hk := (hmapmem K w).mp hw
      obtain ⟨h1, h2⟩ := hconj h hh hhi
      have h2' : (x * h * x⁻¹)⁻¹ * z' = z' * (x * h * x⁻¹)⁻¹ := by
        calc (x * h * x⁻¹)⁻¹ * z' = (x * h * x⁻¹)⁻¹ * (z' * (x * h * x⁻¹)) *
            (x * h * x⁻¹)⁻¹ := by group
          _ = (x * h * x⁻¹)⁻¹ * ((x * h * x⁻¹) * z') * (x * h * x⁻¹)⁻¹ := by rw [h2]
          _ = z' * (x * h * x⁻¹)⁻¹ := by group
      have h3 := hKN _ ((l32nH T V).inv_mem h1) h2' _ hk
      refine (hmapmem K _).mpr ?_
      have e1 : x * (h⁻¹ * w * h) * x⁻¹ =
          (x * h * x⁻¹)⁻¹ * (x * w * x⁻¹) * (x * h * x⁻¹)⁻¹⁻¹ := by group
      rw [e1]
      exact h3
  have hinvc : ∀ w : G, w * z' = z' * w → w⁻¹ * z' = z' * w⁻¹ := by
    intro w hw
    calc w⁻¹ * z' = w⁻¹ * (z' * w) * w⁻¹ := by group
      _ = w⁻¹ * (w * z') * w⁻¹ := by rw [hw]
      _ = z' * w⁻¹ := by group
  have hcc : ∀ w k : G, w * z' = z' * w → k * z' = z' * k →
      (w * k * w⁻¹) * z' = z' * (w * k * w⁻¹) := by
    intro w k hw hk
    calc w * k * w⁻¹ * z' = w * k * (w⁻¹ * z') := by group
      _ = w * k * (z' * w⁻¹) := by rw [hinvc w hw]
      _ = w * (k * z') * w⁻¹ := by group
      _ = w * (z' * k) * w⁻¹ := by rw [hk]
      _ = (w * z') * k * w⁻¹ := by group
      _ = (z' * w) * k * w⁻¹ := by rw [hw]
      _ = z' * (w * k * w⁻¹) := by group
  have hwr : ∀ w ∈ l32nH T V, w * z' = z' * w → ∀ r ∈ rI T V z', w * r * w⁻¹ ∈ rI T V z' :=
    fun w hw hwz r hr => ⟨L128A.HatU.conj_mem (HN hw) hr.1,
      Subgroup.mem_centralizer_singleton_iff.mpr
        (hcc w r hwz (Subgroup.mem_centralizer_singleton_iff.mp hr.2))⟩
  have hrz2 : IsPGroup 2 ↥(rI T V z') := hU2.to_le inf_le_left
  have hO₁ := hmir (rI T V z') hrz2 (inf_le_left.trans hUH)
    (fun k hk => Subgroup.mem_centralizer_singleton_iff.mp hk.2) hwr
  have hcardO₁ : Nat.card (rI T V z') ≤ 64 := by
    have := Subgroup.card_le_of_le hO₁
    rwa [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, C.card_dI] at this
  have hz'U : z' ∉ fsuU T V := by
    intro hz'U
    have h1 := C.card_fix_le hz'H
    have hρ : D.ρ ⟨z', HN hz'H⟩ = 1 :=
      L128A.HatU.rho_eq_one_of_mem D C.base.comm_center hz'U (HN hz'H)
    rw [hρ, map_one] at h1
    have hall : ∀ w : Fin 8 → ZMod 2,
        ((1 : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w = w := fun w => by
      rw [Units.val_one, Matrix.one_mulVec]
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), Nat.card_fun, Nat.card_zmod,
      Nat.card_fin] at h1
    norm_num at h1
    omega
  set Y' := matOf e (D.ρ ⟨z', HN hz'H⟩) with hY'
  have hY'Γ : Y' ∈ gam c := by
    rw [← C.imgH]
    exact (mem_img8 D e).mpr ⟨z', hz'H, HN hz'H, rfl⟩
  have hY'1 : Y' ≠ 1 := fun h => hz'U (C.mem_U_of_star hz'H h)
  have hzz : z * z = 1 := S.mul_self_V (Subgroup.mem_inf.mp hz).1
  have hz'z' : z' * z' = 1 := by
    rw [hz']
    calc x * z * x⁻¹ * (x * z * x⁻¹) = x * (z * z) * x⁻¹ := by group
      _ = 1 := by rw [hzz]; group
  have hY'Y' : Y' * Y' = 1 := by
    rw [hY', ← star8_mul hz'H hz'H]
    have e1 : (⟨z' * z', HN ((l32nH T V).mul_mem hz'H hz'H)⟩ :
        ↥(Subgroup.normalizer (fsuU T V : Set G))) = 1 := Subtype.ext hz'z'
    rw [e1, map_one, map_one]
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨a₅, ha₅⟩ := exists_prime_orderOf_dvd_card' (G := ↥(cenA c x₀)) 5
    (by rw [card_cenA_x0 C.hc C.hx₀]; norm_num)
  have ha₅Γ : (a₅ : GL (Fin 8) (ZMod 2)) ∈ gam c := (cenA_le C.hc x₀ a₅.2).1
  have ha₅x : (a₅ : GL (Fin 8) (ZMod 2)) * x₀ = x₀ * a₅ := comm_of_mem_cenA C.hc a₅.2
  have ha₅5 : (a₅ : GL (Fin 8) (ZMod 2)) ^ 5 = 1 := by
    have h1 := pow_orderOf_eq_one a₅
    rw [ha₅] at h1
    simpa using congrArg Subtype.val h1
  have ha₅15 : (a₅ : GL (Fin 8) (ZMod 2)) ^ 15 = 1 := by
    rw [show 15 = 5 * 3 by rfl, pow_mul, ha₅5, one_pow]
  rw [← C.imgH] at ha₅Γ
  obtain ⟨h, hh, hhN, hhstar⟩ := (mem_img8 D e).mp ha₅Γ
  obtain ⟨u, hu, hui⟩ := C.exists_lift hh (by rw [hhstar]; exact ha₅x)
    (by rw [hhstar]; exact ha₅15)
  have hu'H : u⁻¹ * h ∈ l32nH T V := (l32nH T V).mul_mem ((l32nH T V).inv_mem (hUH hu)) hh
  have hstar' : matOf e (D.ρ ⟨u⁻¹ * h, HN hu'H⟩) = a₅ := by
    rw [star8_mul ((l32nH T V).inv_mem (hUH hu)) hh, star8_inv (hUH hu), C.star_U hu, inv_one,
      one_mul, ← hhstar]
  have hu5U : (u⁻¹ * h) ^ 5 ∈ fsuU T V := C.pow_mem_U hu'H (by rw [hstar']; exact ha₅5)
  obtain ⟨k, hk⟩ := hU2 ⟨_, hu5U⟩
  have hk' : ((u⁻¹ * h) ^ 5) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  set a' := (u⁻¹ * h) ^ 2 ^ k with ha'
  have ha'H : a' ∈ l32nH T V := (l32nH T V).pow_mem hu'H _
  have ha'5 : a' ^ 5 = 1 := by
    rw [ha', ← pow_mul, mul_comm, pow_mul]
    exact hk'
  have ha'i : a' * i = i * a' := ((Commute.pow_left hui (2 ^ k))).eq
  have ha'star1 : matOf e (D.ρ ⟨a', HN ha'H⟩) ≠ 1 := by
    rw [star8_pow hu'H, hstar']
    intro h1
    have h2 : orderOf a₅ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using h1))
    rw [ha₅] at h2
    have h3 := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow (by norm_num) h2)
    norm_num at h3
  obtain ⟨hbH, hbz'⟩ := hconj a' ha'H ha'i
  set b := x * a' * x⁻¹ with hb
  set Bm := matOf e (D.ρ ⟨b, HN hbH⟩) with hBm
  have hb5 : b ^ 5 = 1 := by rw [hb, conj_pow, ha'5]; group
  have hBm5 : Bm ^ 5 = 1 := by
    rw [hBm, ← star8_pow hbH]
    have e1 : (⟨b ^ 5, HN ((l32nH T V).pow_mem hbH 5)⟩ :
        ↥(Subgroup.normalizer (fsuU T V : Set G))) = 1 := Subtype.ext hb5
    rw [e1, map_one, map_one]
  have hBm1 : Bm ≠ 1 := by
    intro h1
    have hbU := C.mem_U_of_star hbH h1
    obtain ⟨m, hm⟩ := hU2 ⟨b, hbU⟩
    have hm' : b ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hcop : Nat.Coprime 5 (2 ^ m) := Nat.Coprime.pow_right m (by norm_num)
    have hb1 : orderOf b = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hb5) hcop)
        (orderOf_dvd_of_pow_eq_one hm')
    rw [orderOf_eq_one_iff] at hb1
    have ha'1 : a' = 1 := by
      have := congrArg (fun t => x⁻¹ * t * x) hb1
      simpa [hb, mul_assoc] using this
    apply ha'star1
    have e1 : (⟨a', HN ha'H⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) = 1 := Subtype.ext ha'1
    rw [e1, map_one, map_one]
  have hBmΓ : Bm ∈ gam c := by
    rw [← C.imgH]
    exact (mem_img8 D e).mpr ⟨b, hbH, HN hbH, rfl⟩
  have hBmY : Bm * Y' = Y' * Bm := by
    rw [hBm, hY', ← star8_mul hbH hz'H, ← star8_mul hz'H hbH]
    congr 2
    exact Subtype.ext hbz'
  rcases invol_cases C.hc hY'Γ hY'1 hY'Y' hBmΓ hBm5 hBm1 hBmY with h64 | ⟨hfull, halt⟩
  · exfalso
    have h1 := C.card_fix_le hz'H
    rw [← hY'] at h1
    have h64' : 64 ≤ Nat.card {w : Fin 8 → ZMod 2 //
        (Y' : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec w = w} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      convert h64 using 2
    have hcard : Nat.card ((rI T V z').map (MulAut.conj x⁻¹).toMonoidHom) =
        Nat.card (dI T V i) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, C.card_dI]
      omega
    have heq := Subgroup.eq_of_le_of_card_ge hO₁ hcard.ge
    have hzD : z ∈ (rI T V z').map (MulAut.conj x⁻¹).toMonoidHom := by
      rw [heq]
      exact rI_le_dI (C.V1_le_rI hz)
    exact hz'U ((hmapmem _ z).mp hzD).1
  ·
    have C' : Inv G T L V V₂ g D e Y' z' :=
      ⟨C.base, C.form, hz'H, hz'z', rfl, hfull, halt⟩
    have hD'2 : IsPGroup 2 ↥(dI T V z') := fun d => ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, pow_two, Subgroup.coe_one]
      exact C'.dI_sq d.2)⟩
    have hD'H : dI T V z' ≤ l32nH T V :=
      sup_le (inf_le_left.trans hUH) ((Subgroup.zpowers_le).mpr hz'H)
    have hO₂ := hmir (dI T V z') hD'2 hD'H (fun d hd => C'.dI_comm hd y_mem_dI)
      (fun w hw hwz d hd => by
        rcases C'.mem_dI_iff.mp hd with hd' | hd'
        · exact rI_le_dI (hwr w hw hwz d hd')
        · refine C'.mem_dI_iff.mpr (Or.inr ?_)
          have e1 : w * d * w⁻¹ * z' = w * (d * z') * w⁻¹ := by
            calc w * d * w⁻¹ * z' = w * d * (w⁻¹ * z') := by group
              _ = w * d * (z' * w⁻¹) := by rw [hinvc w hwz]
              _ = w * (d * z') * w⁻¹ := by group
          rw [e1]
          exact hwr w hw hwz _ hd')
    have hcard : Nat.card ((dI T V z').map (MulAut.conj x⁻¹).toMonoidHom) =
        Nat.card (dI T V i) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, C'.card_dI, C.card_dI]
    have heq := Subgroup.eq_of_le_of_card_ge hO₂ hcard.ge
    refine ⟨fun u hu => ?_, ?_⟩
    · refine Subgroup.mem_normalizer_fintype fun d hd => ?_
      rw [← heq] at hd ⊢
      have hd' := (hmapmem _ d).mp hd
      refine (hmapmem _ _).mpr ?_
      have hun := C'.U_le_normalizer_dI hu
      have e1 : x * (x⁻¹ * u * x * d * (x⁻¹ * u * x)⁻¹) * x⁻¹ = u * (x * d * x⁻¹) * u⁻¹ := by
        group
      rw [e1]
      exact (Subgroup.mem_normalizer_iff.mp hun _).mp hd'
    · by_contra hall
      push Not at hall
      apply hz'U
      refine C.mem_U_of_star hz'H ?_
      rw [(L128A.HatU.rho_eq_one_iff D ⟨z', HN hz'H⟩).mpr fun v hv => ?_, map_one]
      have h1 := hHz _ (hall v hv)
      have h2 : v * z' = z' * v := by
        calc v * z' = x * ((x⁻¹ * v * x) * z) * x⁻¹ := by rw [hz']; group
          _ = x * (z * (x⁻¹ * v * x)) * x⁻¹ := by rw [h1]
          _ = z' * v := by rw [hz']; group
      have h3 : z' * v * z'⁻¹ * v⁻¹ = 1 := by
        rw [← h2]
        group
      rw [h3]
      exact one_mem _

end Cert

end Good

end CFSG.Quasithin.H13.L1449
