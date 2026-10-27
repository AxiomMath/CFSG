module

public import CFSG.Quasithin.H13.L32NLem14323b
public import CFSG.Quasithin.H13.L32NThm1443
public import CFSG.Quasithin.H13.L32NSp4Main

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin

namespace L14323

variable {G : Type} [Group G]

section Img

variable {U : Subgroup G} (D : HatModelU U)

theorem img_le_of_le_map {K : Subgroup G} {X : Subgroup (D.V ≃ₗ[ZMod 2] D.V)}
    (h : K ≤ (X.comap D.ρ).map (Subgroup.normalizer (U : Set G)).subtype) : D.img K ≤ X := by
  intro γ hγ
  obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
  obtain ⟨n, hn, hnk⟩ := h hk
  have e : n = ⟨k, hkN⟩ := Subtype.ext hnk
  rw [← e]
  exact hn

theorem rho_mem_normalizer {K : Subgroup G} {x : G} (hxN : x ∈ Subgroup.normalizer (U : Set G))
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) :
    D.ρ ⟨x, hxN⟩ ∈ Subgroup.normalizer (D.img K : Set (D.V ≃ₗ[ZMod 2] D.V)) := by
  have key : ∀ (y : G) (hy : y ∈ Subgroup.normalizer (U : Set G)),
      y ∈ Subgroup.normalizer (K : Set G) → ∀ δ ∈ D.img K,
        D.ρ ⟨y, hy⟩ * δ * (D.ρ ⟨y, hy⟩)⁻¹ ∈ D.img K := by
    intro y hy hyK δ hδ
    obtain ⟨k, hk, hkN, rfl⟩ := (L128A.HatU.mem_img D).mp hδ
    have hmem : y * k * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hyK k).mp hk
    have hN : y * k * y⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hkN) (Subgroup.inv_mem _ hy)
    have e : D.ρ ⟨y, hy⟩ * D.ρ ⟨k, hkN⟩ * (D.ρ ⟨y, hy⟩)⁻¹ = D.ρ ⟨y * k * y⁻¹, hN⟩ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [e]
    exact L128A.HatU.rho_mem_img D hmem hN
  rw [Subgroup.mem_normalizer_iff]
  intro δ
  refine ⟨key x hxN hxK δ, fun hδ => ?_⟩
  have h1 := key x⁻¹ (Subgroup.inv_mem _ hxN) (Subgroup.inv_mem _ hxK) _ hδ
  have e : D.ρ ⟨x⁻¹, Subgroup.inv_mem _ hxN⟩ = (D.ρ ⟨x, hxN⟩)⁻¹ := by
    rw [← map_inv]
    rfl
  rw [e, inv_inv] at h1
  rwa [show (D.ρ ⟨x, hxN⟩)⁻¹ * (D.ρ ⟨x, hxN⟩ * δ * (D.ρ ⟨x, hxN⟩)⁻¹) * D.ρ ⟨x, hxN⟩ = δ by
    group] at h1

theorem img_conjClosure_le {Z H : Subgroup G} (hH : H ≤ Subgroup.normalizer (U : Set G))
    (hZH : Z ≤ H) {X : Subgroup (D.V ≃ₗ[ZMod 2] D.V)} (hZX : D.img Z ≤ X)
    (hHX : D.img H ≤ Subgroup.normalizer (X : Set (D.V ≃ₗ[ZMod 2] D.V))) :
    D.img (conjClosure Z H) ≤ X := by
  refine img_le_of_le_map D (conjClosure_le fun h hh z hz => ?_)
  have hhN := hH hh
  have hzN := hH (hZH hz)
  have hN : h * z * h⁻¹ ∈ Subgroup.normalizer (U : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hhN hzN) (Subgroup.inv_mem _ hhN)
  refine ⟨⟨h * z * h⁻¹, hN⟩, ?_, rfl⟩
  show D.ρ ⟨h * z * h⁻¹, hN⟩ ∈ X
  have e : D.ρ ⟨h * z * h⁻¹, hN⟩ = D.ρ ⟨h, hhN⟩ * D.ρ ⟨z, hzN⟩ * (D.ρ ⟨h, hhN⟩)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e]
  have hzX : D.ρ ⟨z, hzN⟩ ∈ X := hZX (L128A.HatU.rho_mem_img D hz hzN)
  exact (Subgroup.mem_normalizer_iff.mp (hHX (L128A.HatU.rho_mem_img D hh hhN)) _).mp hzX

end Img

namespace Ctx

variable [Finite G] {T L V V₂ : Subgroup G} {g a c : G} {D : HatModelU (fsuU T V)}
variable (C : Ctx G T L V V₂ g a c D)
include C

theorem card_T_of {n e : ℕ} (hΓ : Nat.card ↥(D.img (l32nH T V)) = n)
    (he : Nat.gcd n 16 = 2 ^ e) (hn : ¬ 2 ^ (e + 1) ∣ n) : Nat.card ↥(D.img T) = 2 ^ e := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := L14332.finite_linearEquiv D
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp C.isPGroup_imgT
  have h1 : 2 ^ e ∣ 2 ^ k := by rw [← he, ← hΓ, ← hk]; exact C.gcd_dvd
  have h2 : 2 ^ k ∣ n := by rw [← hΓ, ← hk]; exact Subgroup.card_dvd_of_le C.imgT_le
  have hek : e ≤ k := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h1
  have hke : k ≤ e := by
    by_contra hc
    exact hn ((Nat.pow_dvd_pow 2 (by omega : e + 1 ≤ k)).trans h2)
  rw [hk, le_antisymm hke hek]

theorem sup_T_eq {P : Subgroup (D.V ≃ₗ[ZMod 2] D.V)} (hPΓ : P ≤ D.img (l32nH T V))
    (hP9 : Nat.card P = 9) (hcard : Nat.card ↥(D.img (l32nH T V)) = 9 * Nat.card ↥(D.img T)) :
    P ⊔ D.img T = D.img (l32nH T V) := by
  have := L14332.finite_linearEquiv D
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp C.isPGroup_imgT
  refine Subgroup.eq_of_le_of_card_ge (sup_le hPΓ C.imgT_le) ?_
  have h1 : 9 ∣ Nat.card ↥(P ⊔ D.img T) := by
    rw [← hP9]
    exact Subgroup.card_dvd_of_le le_sup_left
  have h2 : Nat.card ↥(D.img T) ∣ Nat.card ↥(P ⊔ D.img T) := Subgroup.card_dvd_of_le le_sup_right
  have hcop : Nat.Coprime 9 (Nat.card ↥(D.img T)) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  rw [hcard]
  exact Nat.le_of_dvd Nat.card_pos (Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h1 h2)

theorem T_le_normalizer_lOne : T ≤ Subgroup.normalizer (lOne L (fsuV1 T V) : Set G) := by
  have key : ∀ t ∈ T, ∀ x ∈ lOne L (fsuV1 T V), t * x * t⁻¹ ∈ lOne L (fsuV1 T V) := by
    intro t ht x hx
    have hx' : x ∈ Subgroup.closure
        {y | y ∈ L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) ∧ Odd (orderOf y)} := hx
    have hle : Subgroup.closure
        {y | y ∈ L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) ∧ Odd (orderOf y)} ≤
          (lOne L (fsuV1 T V)).comap (MulAut.conj t).toMonoidHom := by
      rw [Subgroup.closure_le]
      rintro y ⟨⟨hyL, hyH⟩, hyo⟩
      show t * y * t⁻¹ ∈ lOne L (fsuV1 T V)
      have hsc : SemiconjBy t y (t * y * t⁻¹) := by
        show t * y = t * y * t⁻¹ * t
        group
      have htH := C.TH ht
      refine mem_oTwoUpper_of_odd ⟨(Subgroup.mem_normalizer_iff.mp (C.TL ht) y).mp hyL, ?_⟩
        (by rw [← SemiconjBy.orderOf_eq t hsc]; exact hyo)
      exact (l32nH T V).mul_mem ((l32nH T V).mul_mem htH hyH) ((l32nH T V).inv_mem htH)
    exact hle hx'
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key t ht x, fun hx => ?_⟩
  have h1 := key t⁻¹ (T.inv_mem ht) _ hx
  rwa [show t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x by group] at h1

omit [Finite G] C in
theorem lOne_le {P : Subgroup (D.V ≃ₗ[ZMod 2] D.V)}
    (hP : ∀ y ∈ D.img (l32nH T V), y ^ 9 = 1 → y ∈ P)
    (h36 : Nat.card ↥(D.img (l32nH T V)) ∣ 36) : D.img (lOne L (fsuV1 T V)) ≤ P := by
  have hHN := L14332.l32nH_le_normalizer_fsuU T V
  refine img_le_of_le_map D ((Subgroup.closure_le _).mpr ?_)
  rintro x ⟨⟨hxL, hxH⟩, hxo⟩
  have hxN := hHN hxH
  refine ⟨⟨x, hxN⟩, ?_, rfl⟩
  show D.ρ ⟨x, hxN⟩ ∈ P
  have hmem := L128A.HatU.rho_mem_img D hxH hxN
  refine hP _ hmem ?_
  have hodd : Odd (orderOf (D.ρ ⟨x, hxN⟩)) := by
    refine Odd.of_dvd_nat hxo ((orderOf_map_dvd D.ρ _).trans ?_)
    rw [← Subgroup.orderOf_coe]
  have hdvd : orderOf (D.ρ ⟨x, hxN⟩) ∣ 36 :=
    (Subgroup.orderOf_dvd_natCard _ hmem).trans h36
  have h9 : orderOf (D.ρ ⟨x, hxN⟩) ∣ 9 := by
    have hcop : Nat.Coprime (orderOf (D.ρ ⟨x, hxN⟩)) 4 := by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num]
      exact (Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)).symm
    exact hcop.dvd_of_dvd_mul_left (by simpa using hdvd)
  exact orderOf_dvd_iff_pow_eq_one.mp h9

theorem l1_normal_of {P : Subgroup (D.V ≃ₗ[ZMod 2] D.V)} (hPΓ : P ≤ D.img (l32nH T V))
    (hP9 : Nat.card P = 9) (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hP : ∀ y ∈ D.img (l32nH T V), y ^ 9 = 1 → y ∈ P)
    (h36 : Nat.card ↥(D.img (l32nH T V)) ∣ 36)
    (hcard : Nat.card ↥(D.img (l32nH T V)) = 9 * Nat.card ↥(D.img T)) :
    D.img (l32nH T V) ≤
      Subgroup.normalizer (D.img (lOne L (fsuV1 T V)) : Set (D.V ≃ₗ[ZMod 2] D.V)) := by
  have hL1P : D.img (lOne L (fsuV1 T V)) ≤ P := lOne_le hP h36
  have hPn : P ≤ Subgroup.normalizer (D.img (lOne L (fsuV1 T V)) : Set _) := by
    intro π hπ
    rw [Subgroup.mem_normalizer_iff]
    intro δ
    have hcomm : ∀ δ ∈ P, π * δ * π⁻¹ = δ := fun δ hδ => by
      rw [hPc π hπ δ hδ, mul_inv_cancel_right]
    refine ⟨fun hδ => by rw [hcomm δ (hL1P hδ)]; exact hδ, fun hδ => ?_⟩
    have hδP : δ ∈ P := by
      have h1 := hL1P hδ
      have h2 : π⁻¹ * (π * δ * π⁻¹) * π = δ := by group
      rw [← h2]
      exact P.mul_mem (P.mul_mem (P.inv_mem hπ) h1) hπ
    rwa [hcomm δ hδP] at hδ
  have hTn : D.img T ≤ Subgroup.normalizer (D.img (lOne L (fsuV1 T V)) : Set _) := by
    intro γ hγ
    obtain ⟨t, ht, htN, rfl⟩ := (L128A.HatU.mem_img D).mp hγ
    exact rho_mem_normalizer D htN (C.T_le_normalizer_lOne ht)
  rw [← C.sup_T_eq hPΓ hP9 hcard]
  exact sup_le hPn hTn

theorem lt_zU (hq : Sp4Cert.QuadMoved D.B (D.img (l32nH T V)) (D.π a) (D.π c)) :
    fsuV1 T V < centerOf (fsuU T V) := by
  have hle : fsuV1 T V ≤ centerOf (fsuU T V) := C.VZ.symm.le.trans inf_le_right
  refine lt_of_le_of_ne hle fun heq => ?_
  obtain ⟨q, hq1, hpol, hinv⟩ := C.quad heq.symm
  have hqa : q (D.π a) = 0 := (hq1 a C.aU).mpr (by rw [pow_two]; exact C.V_sq a C.aV)
  have hqc : q (D.π c) = 0 := (hq1 c C.cU).mpr (by rw [pow_two]; exact C.V_sq c C.cV)
  have hac : a * c ∈ V := V.mul_mem C.aV C.cV
  have hqac : q (D.π a + D.π c) = 0 := by
    rw [← D.π_mul a C.aU c C.cU]
    exact (hq1 _ (C.V_U hac)).mpr (by rw [pow_two]; exact C.V_sq _ hac)
  obtain ⟨γ, hγ, v, hv⟩ := hq q hpol hqa hqc hqac
  exact hv (hinv γ hγ v)

theorem zU_ne_bot (hq : Sp4Cert.QuadMoved D.B (D.img (l32nH T V)) (D.π a) (D.π c)) :
    D.img (CFSG.conjugate (centerOf (fsuU T V)) g) ≠ ⊥ :=
  C.zU_ne (C.lt_zU hq)

omit [Finite G] C in
theorem one_lt_card_zU (hne : D.img (CFSG.conjugate (centerOf (fsuU T V)) g) ≠ ⊥) :
    1 < Nat.card ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)) := by
  have := L14332.finite_linearEquiv D
  exact (Subgroup.one_lt_card_iff_ne_bot _).mpr hne

theorem card_X_le_two (h18 : Nat.card ↥(D.img (l32nH T V)) = 18) :
    Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) ≤ 2 := by
  have := L14332.finite_linearEquiv D
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX2 : IsPGroup 2 ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) := fun x =>
    ⟨1, Subtype.ext (by
      rw [Subgroup.coe_pow, pow_one, pow_two, Subgroup.coe_one]
      exact C.g101.X_sq x.1 x.2)⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hX2
  have hdvd := Subgroup.card_dvd_of_le C.X_le
  rw [hm, h18] at hdvd
  rw [hm]
  rcases m with _ | _ | m
  · norm_num
  · norm_num
  · exfalso
    have h4 : 2 ^ 2 ∣ 18 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at h4

theorem case_iv (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h14312 : Lemma14312One)
    (h18 : Nat.card ↥(D.img (l32nH T V)) = 18) (hE : Sp4Cert.HasE9 (D.img (l32nH T V))) :
    Case14323iv T L V D := by
  have := L14332.finite_linearEquiv D
  obtain ⟨P, hPΓ, hP9, hnorm, hPc, hP3, hP⟩ := hE
  have hT2 : Nat.card ↥(D.img T) = 2 := by
    have := C.card_T_of (e := 1) h18 (by norm_num) (by norm_num)
    simpa using this
  refine ⟨⟨P.subgroupOf (D.img (l32nH T V)), ?_, ⟨?_, ?_⟩, ?_, ?_⟩,
    C.l1_normal_of hPΓ hP9 hPc hP (by rw [h18]; norm_num) (by rw [h18, hT2]), ?_⟩
  · exact ⟨fun n hn k => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hnorm k.2) n).mp hn⟩
  · exact ⟨⟨fun x y => Subtype.ext (Subtype.ext (hPc _ x.2 _ y.2))⟩⟩
  · intro x hx
    exact Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hP3 _ (Subgroup.mem_subgroupOf.mp hx))
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPΓ).toEquiv, hP9]
  · have h1 := (P.subgroupOf (D.img (l32nH T V))).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPΓ).toEquiv, hP9, h18] at h1
    omega
  ·
    have hle : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) ≤
        2 ^ (Module.finrank (ZMod 2) D.V / 2 - 1) := by
      rw [C.d4]
      exact (C.card_X_le_two h18).trans (by norm_num)
    obtain ⟨-, -, ⟨hZ, hext, -⟩, -⟩ := h14312 G T L V C.hyp V₂ g C.plane C.gP C.gN D hle
    have h32 : Nat.card ↥(fsuU T V) = 2 ^ 5 := by
      rw [D.card_U, hZ, C.card_V1, C.card_V]
      norm_num
    exact isQ8Sq_of_isQ8CentralPow_two
      (lemma1442Q8Four_of_inputs (stmtL32NModule_of_inputs h1332 h1334) C.hyp hext h32)

theorem case_i
    (hiso : Nonempty (↥(D.img (l32nH T V)) ≃* Equiv.Perm (Fin 3) × Equiv.Perm (Fin 3)))
    (hE : Sp4Cert.HasE9 (D.img (l32nH T V)))
    (hF2 : Nat.card ↥(D.img (l32nH T V) ⊓ Sp4Cert.fixW (D.hat V)) = 2)
    {X : Subgroup (D.V ≃ₗ[ZMod 2] D.V)} (hXΓ : X ≤ D.img (l32nH T V)) (hX6 : Nat.card X = 6)
    (hXnc : ∃ α ∈ X, ∃ β ∈ X, α * β ≠ β * α)
    (hXn : D.img (l32nH T V) ≤ Subgroup.normalizer (X : Set (D.V ≃ₗ[ZMod 2] D.V)))
    (hFX : D.img (l32nH T V) ⊓ Sp4Cert.fixW (D.hat V) ≤ X)
    (hXy : ∀ y ∈ D.img (l32nH T V), y ∈ Sp4Cert.stabW (D.hat V) → y ∈ X → y ≠ 1 →
      y ^ 3 = 1 → ∀ x ∈ D.hat V, y x = x) :
    Case14323i T L V g D := by
  have := L14332.finite_linearEquiv D
  have hHN := L14332.l32nH_le_normalizer_fsuU T V
  obtain ⟨P, hPΓ, hP9, -, hPc, -, hP⟩ := hE
  obtain ⟨e⟩ := hiso
  have h36 : Nat.card ↥(D.img (l32nH T V)) = 36 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_fin]
    rfl
  have hT4 : Nat.card ↥(D.img T) = 4 := by
    have := C.card_T_of (e := 2) h36 (by norm_num) (by norm_num)
    simpa using this
  have hcard : Nat.card ↥(D.img (l32nH T V)) = 9 * Nat.card ↥(D.img T) := by omega
  refine ⟨⟨e⟩, C.l1_normal_of hPΓ hP9 hPc hP (dvd_of_eq h36) hcard, fun hne => ?_⟩
  have h1 := one_lt_card_zU hne
  have hle := C.zU_le_fix
  set Z := D.img (CFSG.conjugate (centerOf (fsuU T V)) g) with hZdef
  set K := conjClosure (CFSG.conjugate (centerOf (fsuU T V)) g) (l32nH T V) with hKdef
  have hZF : Z = D.img (l32nH T V) ⊓ Sp4Cert.fixW (D.hat V) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hF2]; omega)
  have hZ2 : Nat.card Z = 2 := by rw [hZF, hF2]
  have hKH : K ≤ l32nH T V := conjClosure_le fun h hh z hz =>
    (l32nH T V).mul_mem ((l32nH T V).mul_mem hh (C.zUg_le hz)) ((l32nH T V).inv_mem hh)
  have hKX : D.img K ≤ X := img_conjClosure_le D hHN C.zUg_le (hZF.le.trans hFX) hXn
  have hKn : X ≤ Subgroup.normalizer (D.img K : Set (D.V ≃ₗ[ZMod 2] D.V)) := by
    intro γ hγ
    obtain ⟨h, hh, hhN, rfl⟩ := (L128A.HatU.mem_img D).mp (hXΓ hγ)
    exact rho_mem_normalizer D hhN (le_normalizer_conjClosure _ _ hh)
  obtain ⟨⟨z, hzZ⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  have hz1' : z ≠ 1 := fun h0 => hz1 (Subtype.ext h0)
  have hz2 : z ^ 2 = 1 := by
    have h := Subgroup.orderOf_dvd_natCard Z hzZ
    rw [hZ2] at h
    exact orderOf_dvd_iff_pow_eq_one.mp h
  have hzK : z ∈ D.img K := img_mono D (le_conjClosure _ _) hzZ
  have hKeq : D.img K = X := Sp4Cert.eq_of_le_card_six hX6 hXnc hKX hKn hzK hz1' hz2
  have hK6 : Nat.card ↥(D.img K) = 6 := by rw [hKeq, hX6]
  have hJeq : D.img K ⊔ D.img (lOne L (fsuV1 T V)) ⊔ D.img T = D.img (l32nH T V) := by
    have hle : D.img K ⊔ D.img (lOne L (fsuV1 T V)) ⊔ D.img T ≤ D.img (l32nH T V) :=
      sup_le (sup_le (img_mono D hKH) (img_mono D L14332.lOne_le_l32nH)) C.imgT_le
    refine le_antisymm hle ?_
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨x₃, hx₃⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) 3 (by rw [hX6]; norm_num)
    have hx3 : orderOf (x₃ : D.V ≃ₗ[ZMod 2] D.V) = 3 := by rw [Subgroup.orderOf_coe]; exact hx₃
    have hx3P : (x₃ : D.V ≃ₗ[ZMod 2] D.V) ∈ P :=
      hP _ (hXΓ x₃.2) (orderOf_dvd_iff_pow_eq_one.mp (by rw [hx3]; norm_num))
    obtain ⟨y, hyL, hyH, hyS, hy3, hya⟩ := C.exists_y
    have hmove : y (D.π a) ≠ D.π a := fun h => C.pi_a_ne_c (hya.symm.trans h).symm
    have hy1 : y ≠ 1 := fun h1 => hmove (by subst h1; rfl)
    have hyX : y ∉ X := fun hyX => hmove (hXy y hyH hyS hyX hy1 hy3 (D.π a) C.pi_a_mem)
    have hyP : y ∈ P :=
      hP _ hyH (by rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, hy3, one_pow])
    set J := Subgroup.zpowers (x₃ : D.V ≃ₗ[ZMod 2] D.V) ⊔ Subgroup.zpowers y with hJdef
    have hsub : J ≤ P := sup_le (Subgroup.zpowers_le.mpr hx3P) (Subgroup.zpowers_le.mpr hyP)
    have hlt : Subgroup.zpowers (x₃ : D.V ≃ₗ[ZMod 2] D.V) < J := by
      refine lt_of_le_of_ne le_sup_left fun he => hyX ?_
      have hy' : y ∈ Subgroup.zpowers (x₃ : D.V ≃ₗ[ZMod 2] D.V) := by
        rw [he]
        exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
      exact (Subgroup.zpowers_le.mpr x₃.2) hy'
    have hcardlt := Subgroup.card_lt_of_lt hlt
    rw [Nat.card_zpowers, hx3] at hcardlt
    have hdvd9 : Nat.card J ∣ 9 := by
      rw [← hP9]
      exact Subgroup.card_dvd_of_le hsub
    have hP' : J = P := by
      refine Subgroup.eq_of_le_of_card_ge hsub ?_
      obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
        (show Nat.card J ∣ 3 ^ 2 from hdvd9)
      interval_cases i
      · rw [pow_zero] at hci
        omega
      · rw [pow_one] at hci
        omega
      · have h9 : Nat.card J = 9 := hci.trans (by norm_num)
        omega
    have hPJ : P ≤ D.img K ⊔ D.img (lOne L (fsuV1 T V)) := by
      rw [← hP']
      refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · exact Subgroup.mem_sup_left (by rw [hKeq]; exact x₃.2)
      · exact Subgroup.mem_sup_right hyL
    rw [← C.sup_T_eq hPΓ hP9 hcard]
    exact sup_le (hPJ.trans le_sup_left) le_sup_right
  refine ⟨hZF, hZ2, ?_, hJeq, ?_⟩
  · refine SBd.nonempty_mulEquiv_perm_three_of_card_six hK6 ?_
    obtain ⟨α, hα, β, hβ, hne'⟩ := hXnc
    rw [← hKeq] at hα hβ
    exact ⟨⟨α, hα⟩, ⟨β, hβ⟩, fun h => hne' (congrArg Subtype.val h)⟩
  ·
    intro hKM
    have hL1M : lOne L (fsuV1 T V) ≤ Subgroup.normalizer (L : Set G) :=
      (oTwoUpper_le _).trans (inf_le_left.trans Subgroup.le_normalizer)
    have hJ : D.img (l32nH T V) ≤ D.img (l32nH T V ⊓ Subgroup.normalizer (L : Set G)) := by
      rw [← hJeq]
      exact sup_le (sup_le (img_mono D (le_inf hKH hKM))
        (img_mono D (le_inf L14332.lOne_le_l32nH hL1M))) (img_mono D (le_inf C.TH C.TL))
    have hle : l32nH T V ≤ (l32nH T V ⊓ Subgroup.normalizer (L : Set G)) ⊔ l32nCHat T V := by
      intro h hh
      have hhN := hHN hh
      obtain ⟨m, hm, hmN, hmh⟩ :=
        (L128A.HatU.mem_img D).mp (hJ (L128A.HatU.rho_mem_img D hh hhN))
      have hmH : m ∈ l32nH T V := hm.1
      have hmi : m⁻¹ * h ∈ l32nH T V := (l32nH T V).mul_mem ((l32nH T V).inv_mem hmH) hh
      have hmiN := hHN hmi
      have h1 : D.ρ ⟨m⁻¹ * h, hmiN⟩ = 1 := by
        have e : (⟨m⁻¹ * h, hmiN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G))) =
            (⟨m, hmN⟩ : ↥(Subgroup.normalizer (fsuU T V : Set G)))⁻¹ * ⟨h, hhN⟩ := rfl
        rw [e, map_mul, map_inv, hmh, inv_mul_cancel]
      have hC : m⁻¹ * h ∈ l32nCHat T V := (L14332.rho_eq_one_iff_mem hmi hmiN).mp h1
      rw [show h = m * (m⁻¹ * h) by group]
      exact Subgroup.mul_mem_sup hm hC
    exact lt_irrefl _ (C.lt_H.trans_le hle)

theorem case_ii (hiso : Nonempty (↥(D.img (l32nH T V)) ≃* Equiv.Perm (Fin 5)))
    (hnat : ∃ (φ : ↥(D.img (l32nH T V)) ≃* RuType.SigmaL2F4) (ψ : D.V ≃+ (Fin 2 → RuType.F4)),
      ∀ (γ : ↥(D.img (l32nH T V))) (v : D.V),
        ψ ((γ : D.V ≃ₗ[ZMod 2] D.V) v) = RuType.sigmaAct (φ γ) (ψ v))
    (hlay : ∀ γ ∈ D.img (l32nH T V) ⊓ Sp4Cert.fixW (D.hat V),
      γ ∈ (CFSG.Open.genFittingLayer ↥(D.img (l32nH T V))).map (D.img (l32nH T V)).subtype)
    (hcen : ∀ t ∈ D.img (l32nH T V), t ∈ Sp4Cert.stabW (D.hat V) → t ≠ 1 → t ^ 2 = 1 →
      (∃ x ∈ D.hat V, t x ≠ x) →
        Nat.card ↥(D.img (l32nH T V) ⊓ (Sp4Cert.fixW (D.hat V) ⊓ Subgroup.centralizer {t})) = 2)
    (hq : Sp4Cert.QuadMoved D.B (D.img (l32nH T V)) (D.π a) (D.π c)) :
    Case14323ii T V g D := by
  have := L14332.finite_linearEquiv D
  refine ⟨hiso, hnat, ?_, fun γ hγ => hlay γ (C.zU_le_fix hγ)⟩
  obtain ⟨t, htX, htc, htV⟩ := C.exists_t
  have hmove : t (D.π c) ≠ D.π c := by
    rw [htc]
    intro h
    exact C.pi_a_ne (by simpa using h)
  have h2 := hcen t (C.X_le htX) (Sp4Cert.mem_stabW.mpr htV) (fun h1 => hmove (by subst h1; rfl))
    (by rw [pow_two]; exact C.g101.X_sq t htX) ⟨D.π c, C.pi_c_mem, hmove⟩
  have hle : D.img (CFSG.conjugate (centerOf (fsuU T V)) g) ≤
      D.img (l32nH T V) ⊓ (Sp4Cert.fixW (D.hat V) ⊓ Subgroup.centralizer {t}) := by
    intro z hz
    have hz' := C.zU_le_fix hz
    refine ⟨hz'.1, hz'.2, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
    rw [Set.mem_singleton_iff.mp hs]
    exact (zU_comm_X hz htX).symm
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [h2] at hdvd
  have h1 := one_lt_card_zU (C.zU_ne_bot hq)
  have h3 := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem case_iii
    (hiii : (Nonempty (↥(D.img (l32nH T V)) ≃* ↥(alternatingGroup (Fin 6))) ∧
        Nat.card ↥(D.img (l32nH T V) ⊓ Sp4Cert.fixW (D.hat V)) = 4) ∨
      (Nonempty (↥(D.img (l32nH T V)) ≃* Equiv.Perm (Fin 6)) ∧
        Nat.card ↥(D.img (l32nH T V) ⊓ Sp4Cert.fixW (D.hat V)) = 8 ∧
        ∀ γ ∈ D.img (l32nH T V), (∀ f ∈ D.img (l32nH T V) ⊓ Sp4Cert.fixW (D.hat V),
          f * γ = γ * f) → γ ∈ Sp4Cert.fixW (D.hat V)))
    (hq : Sp4Cert.QuadMoved D.B (D.img (l32nH T V)) (D.π a) (D.π c)) :
    Case14323iii T V g D := by
  have := L14332.finite_linearEquiv D
  have h1 := one_lt_card_zU (C.zU_ne_bot hq)
  have hdvd := Subgroup.card_dvd_of_le C.zU_le_fix
  rcases hiii with ⟨hiso, hF4⟩ | ⟨hiso, hF8, hC⟩
  · refine ⟨Or.inl hiso, ?_⟩
    rw [hF4] at hdvd
    obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show _ ∣ 2 ^ 2 from hdvd)
    interval_cases i
    · rw [pow_zero] at hci
      omega
    · exact Or.inl (hci.trans (by norm_num))
    · exact Or.inr (hci.trans (by norm_num))
  · refine ⟨Or.inr hiso, ?_⟩
    rw [hF8] at hdvd
    obtain ⟨i, hi, hci⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show _ ∣ 2 ^ 3 from hdvd)
    interval_cases i
    · rw [pow_zero] at hci
      omega
    · exact Or.inl (hci.trans (by norm_num))
    · exact Or.inr (hci.trans (by norm_num))
    · exfalso
      have h8 : Nat.card ↥(D.img (CFSG.conjugate (centerOf (fsuU T V)) g)) = 8 :=
        hci.trans (by norm_num)
      have hZF : D.img (CFSG.conjugate (centerOf (fsuU T V)) g) =
          D.img (l32nH T V) ⊓ Sp4Cert.fixW (D.hat V) :=
        Subgroup.eq_of_le_of_card_ge C.zU_le_fix (by omega)
      obtain ⟨t, htX, htc, -⟩ := C.exists_t
      have htF := hC t (C.X_le htX) fun f hf => by
        rw [← hZF] at hf
        exact zU_comm_X hf htX
      have hfix := Sp4Cert.mem_fixingSubgroup_iff'.mp htF (D.π c) C.pi_c_mem
      rw [htc] at hfix
      exact C.pi_a_ne (by simpa using hfix)

end Ctx

end L14323

theorem lemma14323Two_of_inputs (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2) (h12213 : Stmt12_2_13)
    (h1288 : Lemma12_8_8_two) (h12811 : Lemma12_8_11) (h12811h : Lemma12_8_11_hat)
    (h12813 : Lemma12_8_13) (h14312 : Lemma14312One) (hG112 : G11.TheoremG112Fix) :
    Lemma14323Two := by
  intro G _ _ T L V h V₂ g hV₂ hgP hgN D hd
  obtain ⟨a, c, C⟩ := L14323.exists_ctx h1332 h1334 h1222 h12213 h1288 h12811 h12811h h12813
    hG112 h hV₂ hgP hgN D hd
  rcases Sp4Cert.sp4_classify (L128A.HatU.B_isAlt D) D.nondegenerate C.d4
      (L14323.img_le_sp D _) C.dvd_card C.hatV_eq C.pi_a_mem C.pi_c_mem C.pi_a_ne C.pi_c_ne
      C.pi_a_ne_c C.B_ac C.hT C.h3 C.hne C.h2 with
    ⟨h18, hE⟩ | ⟨hiso, hE, hF2, X, hXΓ, hX6, hXnc, hXn, hFX, hXy⟩ |
      ⟨hiso, hnat, hlay, hcen, hq⟩ | ⟨hiii, hq⟩
  · exact Or.inr (Or.inr (Or.inr (C.case_iv h1332 h1334 h14312 h18 hE)))
  · exact Or.inl (C.case_i hiso hE hF2 hXΓ hX6 hXnc hXn hFX hXy)
  · exact Or.inr (Or.inl (C.case_ii hiso hnat hlay hcen hq))
  · exact Or.inr (Or.inr (Or.inl (C.case_iii hiii hq)))

end CFSG.Quasithin.H13
