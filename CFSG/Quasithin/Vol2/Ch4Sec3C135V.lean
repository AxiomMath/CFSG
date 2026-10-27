module

public import CFSG.Quasithin.Vol2.Ch4Sec3C135W

public section

namespace CFSG.Quasithin.H13.Ch4.C135

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.Ch4 Matrix
open scoped commutatorElement

variable {G : Type} [Group G] {F : Type} [Field F]

theorem mem_centralizer_of_trivOn {U X : Subgroup G}
    (hUab : ∀ u ∈ U, ∀ u' ∈ U, u * u' = u' * u) {y z : G}
    (hyN : y ∈ Subgroup.normalizer (X : Set G)) (hzN : z ∈ Subgroup.normalizer (X : Set G))
    (hy : ∀ x ∈ X, x⁻¹ * (y * x * y⁻¹) ∈ U) (hz : ∀ x ∈ X, x⁻¹ * (z * x * z⁻¹) ∈ U)
    (hyU : ∀ u ∈ U, y * u = u * y) (hzU : ∀ u ∈ U, z * u = u * z) :
    y * z * y⁻¹ * z⁻¹ ∈ Subgroup.centralizer (X : Set G) := by
  have hcomm : ∀ x ∈ X, (y * z) * x * (y * z)⁻¹ = (z * y) * x * (z * y)⁻¹ := by
    intro x hx
    obtain ⟨e₁, he₁, h₁⟩ : ∃ e ∈ U, y * x * y⁻¹ = x * e := ⟨_, hy x hx, by group⟩
    obtain ⟨e₂, he₂, h₂⟩ : ∃ e ∈ U, z * x * z⁻¹ = x * e := ⟨_, hz x hx, by group⟩
    have hye : y * e₂ * y⁻¹ = e₂ := by rw [hyU e₂ he₂]; group
    have hze : z * e₁ * z⁻¹ = e₁ := by rw [hzU e₁ he₁]; group
    calc (y * z) * x * (y * z)⁻¹ = y * (z * x * z⁻¹) * y⁻¹ := by group
      _ = y * (x * e₂) * y⁻¹ := by rw [h₂]
      _ = (y * x * y⁻¹) * (y * e₂ * y⁻¹) := by group
      _ = x * e₁ * e₂ := by rw [h₁, hye]
      _ = x * e₂ * e₁ := by rw [mul_assoc, hUab e₁ he₁ e₂ he₂, ← mul_assoc]
      _ = (z * x * z⁻¹) * (z * e₁ * z⁻¹) := by rw [h₂, hze]
      _ = z * (x * e₁) * z⁻¹ := by group
      _ = z * (y * x * y⁻¹) * z⁻¹ := by rw [h₁]
      _ = (z * y) * x * (z * y)⁻¹ := by group
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  have hx' : (z * y)⁻¹ * x * (z * y) ∈ X := by
    have := (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.normalizer (X : Set G)).inv_mem
        ((Subgroup.normalizer (X : Set G)).mul_mem hzN hyN)) x).mp hx
    simpa using this
  have h1 := hcomm _ hx'
  have h2 : (y * z * y⁻¹ * z⁻¹) * x * (y * z * y⁻¹ * z⁻¹)⁻¹ = x := by
    have e : (y * z * y⁻¹ * z⁻¹) * x * (y * z * y⁻¹ * z⁻¹)⁻¹ =
        y * z * ((z * y)⁻¹ * x * (z * y)) * (y * z)⁻¹ := by group
    rw [e, h1]
    group
  calc x * (y * z * y⁻¹ * z⁻¹) =
        ((y * z * y⁻¹ * z⁻¹) * x * (y * z * y⁻¹ * z⁻¹)⁻¹) * (y * z * y⁻¹ * z⁻¹) := by rw [h2]
    _ = (y * z * y⁻¹ * z⁻¹) * x := by group

theorem le_normalizer_of_conj_mem {X K : Subgroup G} (h : ∀ g ∈ K, ∀ x ∈ X, g * x * g⁻¹ ∈ X) :
    K ≤ Subgroup.normalizer (X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h g hg x, fun hx => ?_⟩
  have := h g⁻¹ (K.inv_mem hg) _ hx
  simpa [mul_assoc] using this

namespace Hyp135

variable {G₀ L : Subgroup G} {α : ↥L →* ↥(StatedSL 3 F)} {H : Hyp135 G₀ L α}

namespace Adapted

variable (C : H.Adapted)

abbrev W : Subgroup G := C.Wμ (e₀ F)

abbrev V : Subgroup G := pCoreOf 2 G₀ ⊓ Subgroup.centralizer (C.W : Set G)

theorem centerOf_le_centralizer : centerOf (c134Q G₀ L) ≤
    Subgroup.centralizer (c134Q G₀ L : Set G) := fun _ hu => hu.2

theorem mul_comm_U' {u v : G} (hu : u ∈ centerOf (c134Q G₀ L))
    (hv : v ∈ centerOf (c134Q G₀ L)) : u * v = v * u := mul_comm_U hu hv

theorem le_normalizer_W : L ≤ Subgroup.normalizer (C.W : Set G) := by
  refine le_normalizer_of_conj_mem fun a ha x hx => ?_
  have hxQ := C.Wμ_le _ hx
  have h1 := C.e_cnj_one ⟨a, ha⟩ ⟨x, hxQ⟩
  rw [(C.mem_W_iff ⟨x, hxQ⟩).mp hx, mulVec_zero] at h1
  exact (C.mem_W_iff (cnj _ ⟨x, hxQ⟩)).mpr h1

theorem e_cnj_of_mem_W [Finite G] {t : G} (ht : t ∈ pCoreOf 2 G₀) {w : ↥(c134Q G₀ L)}
    (hw : (w : G) ∈ C.W) : C.e (cnj (H.pCoreOf_le_normalizer_Q ht) w) = C.e w := by
  obtain ⟨s, hs⟩ := C.conjT t ht
  have h1 := (C.mem_W_iff w).mp hw
  funext i
  fin_cases i
  · show C.e (cnj (H.pCoreOf_le_normalizer_Q ht) w) 0 = C.e w 0
    rw [(hs w).1, h1, smul_zero, add_zero]
  · exact (hs w).2

theorem pCoreOf_le_normalizer_W [Finite G] : pCoreOf 2 G₀ ≤ Subgroup.normalizer (C.W : Set G) := by
  refine le_normalizer_of_conj_mem fun t ht x hx => ?_
  have hxQ := C.Wμ_le _ hx
  have h1 := C.e_cnj_of_mem_W ht (w := ⟨x, hxQ⟩) hx
  have h2 : C.e (cnj (H.pCoreOf_le_normalizer_Q ht) ⟨x, hxQ⟩) 1 = 0 := by
    rw [h1]; exact (C.mem_W_iff _).mp hx
  exact (C.mem_W_iff (cnj _ ⟨x, hxQ⟩)).mpr h2

theorem e_one : C.e 1 = 0 := (C.ker 1).mpr (centerOf (c134Q G₀ L)).one_mem

theorem e_cnj_Q (c q : ↥(c134Q G₀ L)) {hc : (c : G) ∈ Subgroup.normalizer (c134Q G₀ L : Set G)} :
    C.e (cnj hc q) = C.e q := by
  have e : cnj hc q = c * q * c⁻¹ := Subtype.ext (by simp [coe_cnj])
  rw [e, C.mul, C.mul, C.e_inv]
  abel

@[expose] def triv₁ : Subgroup G where
  carrier := {x | ∃ hx : x ∈ Subgroup.normalizer (c134Q G₀ L : Set G),
    x ∈ Subgroup.normalizer (centerOf (c134Q G₀ L) : Set G) ∧ ∀ q, C.e (cnj hx q) 1 = C.e q 1}
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, fun q => by
    congr 2
    exact Subtype.ext (by simp [coe_cnj])⟩
  mul_mem' := by
    rintro x y ⟨hx, hxU, hx'⟩ ⟨hy, hyU, hy'⟩
    refine ⟨Subgroup.mul_mem _ hx hy, Subgroup.mul_mem _ hxU hyU, fun q => ?_⟩
    rw [cnj_mul_left hx hy, hx', hy']
  inv_mem' := by
    rintro x ⟨hx, hxU, hx'⟩
    refine ⟨Subgroup.inv_mem _ hx, Subgroup.inv_mem _ hxU, fun q => ?_⟩
    have e : q = cnj hx (cnj (Subgroup.inv_mem _ hx) q) :=
      Subtype.ext (by simp only [coe_cnj]; group)
    conv_rhs => rw [e]
    rw [hx']

theorem e_cnj_triv₁ {x : G} (hx : x ∈ C.triv₁) (hxN : x ∈ Subgroup.normalizer (c134Q G₀ L : Set G))
    (q : ↥(c134Q G₀ L)) : C.e (cnj hxN q) 1 = C.e q 1 := by
  obtain ⟨hx', -, h⟩ := hx
  exact h q

theorem pCoreOf_le_triv₁ [Finite G] : pCoreOf 2 G₀ ≤ C.triv₁ := fun t ht =>
  ⟨H.pCoreOf_le_normalizer_Q ht, H.le_normalizer_U (pCoreOf_le 2 G₀ ht), fun q => by
    obtain ⟨s, hs⟩ := C.conjT t ht
    exact (hs q).2⟩

theorem mem_triv₁_of_ker {a : ↥L} (ha : α a = 1) : (a : G) ∈ C.triv₁ :=
  ⟨H.le_normalizer_Q (H.le a.2), H.le_normalizer_U (H.le a.2), fun q => by
    rw [C.e_cnj_one, H.ρd_eq_one ha]
    exact one_mulVec _⟩

theorem e_cm_mul {t : G} (ht : t ∈ pCoreOf 2 G₀) (y y' : ↥L) :
    C.e (cm ht (y * y')) 1 = C.e (cm ht y) 1 +
      ((H.ρd y : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        C.e (cm ht y') 1 := by
  have hyN := H.le_normalizer_Q (H.le y.2)
  have e : cm ht (y * y') = cm ht y * cnj hyN (cm ht y') := by
    apply Subtype.ext
    simp only [coe_cm, Subgroup.coe_mul, coe_cnj]
    group
  rw [e, C.mul, Pi.add_apply, C.e_cnj_one]

theorem e_cm_ker [Finite G] {t : G} (ht : t ∈ pCoreOf 2 G₀) {a : ↥L} (ha : α a = 1) :
    C.e (cm ht a) 1 = 0 := by
  classical
  set w := cm ht a with hw
  have haT := H.mem_pCoreOf_of_ker ha
  have htr := C.pCoreOf_le_triv₁ ht
  have h₁ : t⁻¹ * a ∈ C.triv₁ := C.triv₁.mul_mem (C.triv₁.inv_mem htr) (C.mem_triv₁_of_ker ha)
  have h₂ : t⁻¹ * a * t ∈ C.triv₁ := C.triv₁.mul_mem h₁ htr
  have hfix : ∀ γ : SpecialLinearGroup (Fin 3) F,
      (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ C.e w 1 = C.e w 1 := by
    intro γ
    obtain ⟨g, hg⟩ := H.ρd_surjective γ
    set c : ↥(c134Q G₀ L) := cm ht g with hc
    set q : ↥(c134Q G₀ L) := cm haT g with hq
    have hN₁ : t⁻¹ * a ∈ Subgroup.normalizer (c134Q G₀ L : Set G) := h₁.1
    have hN₂ : t⁻¹ * a * t ∈ Subgroup.normalizer (c134Q G₀ L : Set G) := h₂.1
    have hgN : (g : G) ∈ Subgroup.normalizer (c134Q G₀ L : Set G) := H.le_normalizer_Q (H.le g.2)
    have e : cnj hgN w = c⁻¹ * cnj hN₁ q * cnj hN₂ c * cnj hN₂ q⁻¹ * w := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_cnj, hw, hc, hq, coe_cm]
      group
    have h3 := C.e_cnj_one g w
    rw [e, C.mul, C.mul, C.mul, C.mul] at h3
    simp only [Pi.add_apply] at h3
    rw [C.e_cnj_triv₁ h₁, C.e_cnj_triv₁ h₂, C.e_cnj_triv₁ h₂, C.e_inv, C.e_inv] at h3
    simp only [Pi.neg_apply] at h3
    rw [← hg, ← h3]
    abel
  have h0 := eq_zero_of_fixed (k := 1) (x := fun _ => C.e w 1) (fun γ => by
    funext i
    exact hfix γ)
  exact congrFun h0 0

theorem W_le_Q : C.W ≤ c134Q G₀ L := C.Wμ_le _

@[expose] def wQ (w : ↥C.W) : ↥(c134Q G₀ L) := ⟨w, C.W_le_Q w.2⟩

theorem wQ_mul (w w' : ↥C.W) : C.wQ (w * w') = C.wQ w * C.wQ w' := rfl

@[expose] def eW (w : ↥C.W) : Fin 3 → F := C.e (C.wQ w) 0

theorem eW_mul (w w' : ↥C.W) : C.eW (w * w') = C.eW w + C.eW w' := by
  rw [eW, wQ_mul, C.mul]
  rfl

theorem eW_one : C.eW 1 = 0 := by
  rw [eW, show C.wQ 1 = 1 from rfl, C.e_one]
  rfl

theorem eW_inv (w : ↥C.W) : C.eW w⁻¹ = -C.eW w := by
  have h2 := C.eW_mul w w⁻¹
  rw [mul_inv_cancel, C.eW_one] at h2
  exact eq_neg_of_add_eq_zero_right h2.symm

theorem eW_surj (y : Fin 3 → F) : ∃ w : ↥C.W, C.eW w = y := by
  obtain ⟨q, hq⟩ := C.surj (fun i => if i = 0 then y else 0)
  have hqW : (q : G) ∈ C.W := (C.mem_W_iff q).mpr (by rw [hq]; simp)
  refine ⟨⟨q, hqW⟩, ?_⟩
  rw [eW, show C.wQ ⟨q, hqW⟩ = q from rfl, hq]
  simp

theorem mem_U_of_eW {w : ↥C.W} (h : C.eW w = 0) : (w : G) ∈ centerOf (c134Q G₀ L) := by
  have h1 := (C.mem_W_iff (C.wQ w)).mp w.2
  rw [show (w : G) = (C.wQ w : G) from rfl, ← C.ker]
  funext i
  fin_cases i
  · exact h
  · exact h1

theorem eW_cnj (g : ↥L) (w : ↥C.W) :
    C.eW (cnj (C.le_normalizer_W g.2) w) =
      ((H.ρd g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ C.eW w := by
  rw [eW, show C.wQ (cnj (C.le_normalizer_W g.2) w) =
    cnj (H.le_normalizer_Q (H.le g.2)) (C.wQ w) from rfl, C.e_cnj_zero]
  rfl

theorem eq_one_of_equivariant_W (δ : ↥C.W → ↥(centerOf (c134Q G₀ L)))
    (hmul : ∀ w w', δ (w * w') = δ w * δ w')
    (hU1 : ∀ w : ↥C.W, (w : G) ∈ centerOf (c134Q G₀ L) → δ w = 1)
    (hequiv : ∀ (g : ↥L) (w : ↥C.W),
      δ (cnj (C.le_normalizer_W g.2) w) = cnj (H.le_normalizer_U (H.le g.2)) (δ w))
    (w : ↥C.W) : δ w = 1 := by
  classical
  have hwd : ∀ w w' : ↥C.W, C.eW w = C.eW w' → δ w = δ w' := by
    intro w w' h
    have h1 : C.eW (w⁻¹ * w') = 0 := by rw [C.eW_mul, C.eW_inv, h, neg_add_cancel]
    have e : w' = w * (w⁻¹ * w') := by group
    rw [e, hmul, hU1 _ (C.mem_U_of_eW h1), mul_one]
  choose sec hsec using C.eW_surj
  let φ : (Fin 3 → F) → (Fin 3 → F) := fun y => crd H.nat (δ (sec y)) 0
  have hφ : ∀ y, φ y = 0 := by
    intro y
    refine eq_zero_of_dual_equivariant φ (fun γ y => ?_) y
    obtain ⟨g, hg⟩ := H.ρd_surjective (dualHom γ)
    have hnat : slNat α g = γ := by
      rw [← dualHom_dualHom (slNat α g)]
      show dualHom (H.ρd g) = γ
      rw [hg, dualHom_dualHom]
    have h1 : C.eW (cnj (C.le_normalizer_W g.2) (sec y)) =
        ((dualHom γ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ y := by
      rw [C.eW_cnj, hg, hsec]
    show crd H.nat (δ (sec _)) 0 = _
    rw [hwd _ (cnj (C.le_normalizer_W g.2) (sec y)) ((hsec _).trans h1.symm), hequiv,
      crd_conj_false H.nat g (δ (sec y)) _ rfl, hnat]
    rfl
  have h0 : crd H.nat (δ w) = 0 := by
    funext i
    rw [Subsingleton.elim i 0, ← hwd (sec (C.eW w)) w (hsec _)]
    exact hφ _
  rw [crd_eq_zero_iff, Subgroup.mem_bot] at h0
  exact Subtype.ext h0

theorem mul_comm_W [Finite G] [CharP F 2] {x y : G} (hx : x ∈ C.W) (hy : y ∈ C.W) :
    x * y = y * x := C.mul_comm_of_mem_Wμ e₀_ne_zero hx hy

theorem exists_mul_mem_V [Finite G] [CharP F 2] {t : G} (ht : t ∈ pCoreOf 2 G₀) :
    ∃ q₀ : ↥(c134Q G₀ L), t * (q₀ : G)⁻¹ ∈ C.V := by
  obtain ⟨c, hc0, hc1, hcc⟩ := H.scalar
  obtain ⟨m, hm⟩ := exists_coboundary (k := 1) (f := fun g _ => C.e (cm ht g) 1) hc0 hc1 hcc
    H.ρd_surjective (fun g g' => by
      funext i
      simp only [Pi.add_apply]
      rw [C.e_cm_mul]
      rfl)
    (fun a ha => by
      funext i
      exact C.e_cm_ker ht (H.slNat_eq_one_of_ρd ha))
  set m₀ := m 0 with hm₀
  have hm' : ∀ g : ↥L, C.e (cm ht g) 1 =
      ((H.ρd g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ m₀ - m₀ :=
    fun g => congrFun (hm g) 0
  obtain ⟨q₀, hq₀⟩ := C.surj (fun i => if i = 0 then 0 else m₀)
  have hq₀P : (q₀ : G) ∈ pCoreOf 2 G₀ := H.c134Q_le_pCoreOf q₀.2
  refine ⟨q₀, ?_⟩
  set t₁ := t * (q₀ : G)⁻¹ with ht₁def
  have ht₁ : t₁ ∈ pCoreOf 2 G₀ := (pCoreOf 2 G₀).mul_mem ht ((pCoreOf 2 G₀).inv_mem hq₀P)
  have ht₁U : ∀ u ∈ centerOf (c134Q G₀ L), t₁ * u = u * t₁ := fun u hu =>
    commute_of_mem_pCoreOf H.surj H.le H.norm H.nat ht₁ hu
  have hs : ∀ y : ↥L, (cm ht₁ y : G) ∈ C.W := by
    intro y
    have hyN : (y : G) ∈ Subgroup.normalizer (c134Q G₀ L : Set G) := H.le_normalizer_Q (H.le y.2)
    have e : cm ht₁ y = q₀ * cm ht y * cnj hyN q₀⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_cnj, coe_cm, ht₁def]
      group
    rw [C.mem_W_iff, e, C.mul, C.mul, Pi.add_apply, Pi.add_apply, C.e_cnj_one, C.e_inv, hm', hq₀]
    simp only [Pi.neg_apply, mulVec_neg]
    simp
  have ht₁N := C.pCoreOf_le_normalizer_W ht₁
  have hδmem : ∀ w : ↥C.W, t₁ * w * t₁⁻¹ * (w : G)⁻¹ ∈ centerOf (c134Q G₀ L) := by
    intro w
    have h1 := C.e_cnj_of_mem_W ht₁ (w := C.wQ w) w.2
    have h2 := (C.e_eq_iff (C.wQ w) (cnj (H.pCoreOf_le_normalizer_Q ht₁) (C.wQ w))).mp h1.symm
    have h3 := conj_mem_centerOf (H.le_normalizer_Q (pCoreOf_le 2 G₀
      (H.c134Q_le_pCoreOf (C.W_le_Q w.2)))) h2
    convert h3 using 1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_cnj, wQ]
    group
  let δ : ↥C.W → ↥(centerOf (c134Q G₀ L)) := fun w => ⟨_, hδmem w⟩
  have hδ : ∀ w, ((δ w : ↥(centerOf (c134Q G₀ L))) : G) = t₁ * w * t₁⁻¹ * (w : G)⁻¹ :=
    fun w => rfl
  have hδ1 := C.eq_one_of_equivariant_W δ
    (fun w w' => by
      apply Subtype.ext
      simp only [hδ, Subgroup.coe_mul]
      have hc := Subgroup.mem_centralizer_iff.mp (hδmem w').2 _
        ((c134Q G₀ L).inv_mem (C.W_le_Q w.2))
      calc t₁ * (↑w * ↑w') * t₁⁻¹ * (↑w * ↑w')⁻¹ =
            t₁ * ↑w * t₁⁻¹ * ((t₁ * ↑w' * t₁⁻¹ * (↑w')⁻¹) * (↑w)⁻¹) := by group
        _ = t₁ * ↑w * t₁⁻¹ * ((↑w)⁻¹ * (t₁ * ↑w' * t₁⁻¹ * (↑w')⁻¹)) := by rw [hc]
        _ = t₁ * ↑w * t₁⁻¹ * (↑w)⁻¹ * (t₁ * ↑w' * t₁⁻¹ * (↑w')⁻¹) := by group)
    (fun w hw => by
      apply Subtype.ext
      simp only [hδ, OneMemClass.coe_one]
      rw [ht₁U w hw]
      group)
    (fun g w => by
      apply Subtype.ext
      simp only [hδ, coe_cnj]
      have hsg := hs g
      rw [coe_cm] at hsg
      have hgw : (g : G) * w * (g : G)⁻¹ ∈ C.W :=
        (Subgroup.mem_normalizer_iff.mp (C.le_normalizer_W g.2) w).mp w.2
      have hc := C.mul_comm_W hsg hgw
      calc t₁ * (↑g * ↑w * (↑g)⁻¹) * t₁⁻¹ * (↑g * ↑w * (↑g)⁻¹)⁻¹ =
            t₁ * ((t₁⁻¹ * ↑g * t₁ * (↑g)⁻¹) * (↑g * ↑w * (↑g)⁻¹) *
              (t₁⁻¹ * ↑g * t₁ * (↑g)⁻¹)⁻¹) * t₁⁻¹ * (↑g * ↑w * (↑g)⁻¹)⁻¹ := by
            rw [hc]; group
        _ = ↑g * (t₁ * ↑w * t₁⁻¹ * (↑w)⁻¹) * (↑g)⁻¹ := by group)
  refine ⟨ht₁, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
  have h1 := congrArg Subtype.val (hδ1 ⟨w, hw⟩)
  simp only [hδ, OneMemClass.coe_one] at h1
  calc w * t₁ = (t₁ * w * t₁⁻¹ * w⁻¹)⁻¹ * (t₁ * w) := by group
    _ = t₁ * w := by rw [h1, inv_one, one_mul]

@[expose] noncomputable def lam [Finite G] {t : G} (ht : t ∈ pCoreOf 2 G₀) : F :=
  Classical.choose (C.conjT t ht)

theorem lam_spec [Finite G] {t : G} (ht : t ∈ pCoreOf 2 G₀) (q : ↥(c134Q G₀ L)) :
    C.e (cnj (H.pCoreOf_le_normalizer_Q ht) q) 0 = C.e q 0 + C.lam ht • C.e q 1 ∧
      C.e (cnj (H.pCoreOf_le_normalizer_Q ht) q) 1 = C.e q 1 :=
  Classical.choose_spec (C.conjT t ht) q

theorem exists_e1_ne_zero : ∃ q : ↥(c134Q G₀ L), C.e q 1 = Pi.single 0 1 := by
  obtain ⟨q, hq⟩ := C.surj (fun i => if i = 0 then 0 else Pi.single 0 1)
  exact ⟨q, by rw [hq]; simp⟩

theorem lam_mul [Finite G] {t t' : G} (ht : t ∈ pCoreOf 2 G₀) (ht' : t' ∈ pCoreOf 2 G₀) :
    C.lam ((pCoreOf 2 G₀).mul_mem ht ht') = C.lam ht + C.lam ht' := by
  obtain ⟨q, hq⟩ := C.exists_e1_ne_zero
  have h1 := (C.lam_spec ((pCoreOf 2 G₀).mul_mem ht ht') q).1
  rw [cnj_mul_left (H.pCoreOf_le_normalizer_Q ht) (H.pCoreOf_le_normalizer_Q ht')] at h1
  rw [(C.lam_spec ht _).1, (C.lam_spec ht' q).1, (C.lam_spec ht' q).2, hq] at h1
  have h2 := congrFun h1 0
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h2
  linear_combination -h2

theorem lam_congr [Finite G] {t t' : G} (ht : t ∈ pCoreOf 2 G₀) (ht' : t' ∈ pCoreOf 2 G₀)
    (h : t = t') : C.lam ht = C.lam ht' := by
  subst h
  rfl

theorem lam_one [Finite G] : C.lam (pCoreOf 2 G₀).one_mem = 0 := by
  have h := C.lam_mul (pCoreOf 2 G₀).one_mem (pCoreOf 2 G₀).one_mem
  rw [C.lam_congr _ (pCoreOf 2 G₀).one_mem (mul_one 1)] at h
  linear_combination -h

theorem lam_inv [Finite G] {t : G} (ht : t ∈ pCoreOf 2 G₀) :
    C.lam ((pCoreOf 2 G₀).inv_mem ht) = -C.lam ht := by
  have h := C.lam_mul ht ((pCoreOf 2 G₀).inv_mem ht)
  rw [C.lam_congr _ (pCoreOf 2 G₀).one_mem (mul_inv_cancel t), C.lam_one] at h
  linear_combination -h

theorem mem_Q_of_lam [Finite G] [CharP F 2] {t : G} (ht : t ∈ pCoreOf 2 G₀)
    (h : C.lam ht = 0) : t ∈ c134Q G₀ L := by
  refine H.mem_c134Q_of_triv ht ⟨H.pCoreOf_le_normalizer_Q ht, fun q => ?_⟩
  rw [crd_eq_iff, ← C.ker, C.mul, C.e_inv, neg_add_eq_zero]
  funext i
  fin_cases i
  · show C.e (cnj (H.pCoreOf_le_normalizer_Q ht) q) 0 = C.e q 0
    rw [(C.lam_spec ht q).1, h, zero_smul, add_zero]
  · exact (C.lam_spec ht q).2

theorem W_le_V [Finite G] [CharP F 2] : C.W ≤ C.V := fun _ hw =>
  ⟨H.c134Q_le_pCoreOf (C.W_le_Q hw), Subgroup.mem_centralizer_iff.mpr fun _ hw' =>
    C.mul_comm_W hw' hw⟩

theorem mem_W_of_mem_V_Q [Finite G] [CharP F 2] {v : G} (hv : v ∈ C.V) (hvQ : v ∈ c134Q G₀ L) :
    v ∈ C.W :=
  C.mem_W_of_commute ⟨v, hvQ⟩ fun w hw => (Subgroup.mem_centralizer_iff.mp hv.2 w hw).symm

theorem mem_W_of_commute_V [Finite G] [CharP F 2] {v : G} (hv : v ∈ C.V) (hvW : v ∉ C.W)
    {q : ↥(c134Q G₀ L)} (hq : (q : G) * v = v * q) : (q : G) ∈ C.W := by
  have hlam : C.lam hv.1 ≠ 0 := fun h => hvW (C.mem_W_of_mem_V_Q hv (C.mem_Q_of_lam hv.1 h))
  have h1 : cnj (H.pCoreOf_le_normalizer_Q hv.1) q = q :=
    Subtype.ext (by simp only [coe_cnj]; rw [← hq]; group)
  have h2 := (C.lam_spec hv.1 q).1
  rw [h1] at h2
  have h3 : C.lam hv.1 • C.e q 1 = 0 := by
    have := congrArg (fun x => x - C.e q 0) h2
    simpa using this.symm
  rw [C.mem_W_iff]
  exact (smul_eq_zero.mp h3).resolve_left hlam

end Adapted

end Hyp135

end CFSG.Quasithin.H13.Ch4.C135

end
