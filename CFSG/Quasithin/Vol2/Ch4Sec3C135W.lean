module

public import CFSG.Quasithin.Vol2.Ch4Sec3C135Lin

public section

namespace CFSG.Quasithin.H13.Ch4.C135

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.Ch4 Matrix
open scoped commutatorElement

variable {G : Type} [Group G] {F : Type} [Field F]

theorem coe_sl_mul (γ δ : SpecialLinearGroup (Fin 3) F) :
    ((γ * δ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      (γ : Matrix (Fin 3) (Fin 3) F) * (δ : Matrix (Fin 3) (Fin 3) F) := rfl

theorem coe_sl_mul_inv (γ : SpecialLinearGroup (Fin 3) F) :
    (γ : Matrix (Fin 3) (Fin 3) F) * ((γ⁻¹ : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [← coe_sl_mul, mul_inv_cancel]
  rfl

theorem coe_sl_inv_mul (γ : SpecialLinearGroup (Fin 3) F) :
    ((γ⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (γ : Matrix (Fin 3) (Fin 3) F) = 1 := by
  rw [← coe_sl_mul, inv_mul_cancel]
  rfl

namespace Hyp135

variable {G₀ L : Subgroup G} {α : ↥L →* ↥(StatedSL 3 F)} {H : Hyp135 G₀ L α}

namespace Adapted

variable (C : H.Adapted)

@[expose] def tns (μ : Fin 2 → F) (y : Fin 3 → F) : Fin 2 → Fin 3 → F := fun i => μ i • y

@[expose] def Wμ (μ : Fin 2 → F) : Subgroup G where
  carrier := {x | ∃ hx : x ∈ c134Q G₀ L, ∃ y, C.e ⟨x, hx⟩ = tns μ y}
  one_mem' := ⟨(c134Q G₀ L).one_mem, 0, by
    rw [show (⟨1, _⟩ : ↥(c134Q G₀ L)) = 1 from rfl, (C.ker 1).mpr (centerOf (c134Q G₀ L)).one_mem]
    funext i
    simp [tns]⟩
  mul_mem' := by
    rintro x x' ⟨hx, y, hy⟩ ⟨hx', y', hy'⟩
    refine ⟨(c134Q G₀ L).mul_mem hx hx', y + y', ?_⟩
    rw [show (⟨x * x', _⟩ : ↥(c134Q G₀ L)) = ⟨x, hx⟩ * ⟨x', hx'⟩ from rfl, C.mul, hy, hy']
    funext i
    simp [tns, smul_add]
  inv_mem' := by
    rintro x ⟨hx, y, hy⟩
    refine ⟨(c134Q G₀ L).inv_mem hx, -y, ?_⟩
    have h1 := C.mul ⟨x, hx⟩ ⟨x, hx⟩⁻¹
    rw [mul_inv_cancel, (C.ker 1).mpr (centerOf (c134Q G₀ L)).one_mem, hy] at h1
    rw [show (⟨x⁻¹, _⟩ : ↥(c134Q G₀ L)) = ⟨x, hx⟩⁻¹ from rfl, eq_neg_of_add_eq_zero_right h1.symm]
    funext i
    simp [tns]

theorem Wμ_le (μ : Fin 2 → F) : C.Wμ μ ≤ c134Q G₀ L := fun _ hx => hx.1

theorem centerOf_le_Wμ (μ : Fin 2 → F) : centerOf (c134Q G₀ L) ≤ C.Wμ μ := fun x hx =>
  ⟨hx.1, 0, by
    rw [(C.ker ⟨x, hx.1⟩).mpr hx]
    funext i
    simp [tns]⟩

theorem mem_Wμ_iff {μ : Fin 2 → F} (q : ↥(c134Q G₀ L)) :
    (q : G) ∈ C.Wμ μ ↔ ∃ y, C.e q = tns μ y :=
  ⟨fun ⟨_, y, hy⟩ => ⟨y, hy⟩, fun ⟨y, hy⟩ => ⟨q.2, y, hy⟩⟩

theorem e_inv (q : ↥(c134Q G₀ L)) : C.e q⁻¹ = -C.e q := by
  have h1 := C.mul q q⁻¹
  rw [mul_inv_cancel, (C.ker 1).mpr (centerOf (c134Q G₀ L)).one_mem] at h1
  exact eq_neg_of_add_eq_zero_right h1.symm

theorem e_eq_iff (q q' : ↥(c134Q G₀ L)) :
    C.e q = C.e q' ↔ ((q⁻¹ * q' : ↥(c134Q G₀ L)) : G) ∈ centerOf (c134Q G₀ L) := by
  rw [← C.ker, C.mul, C.e_inv, neg_add_eq_zero]

theorem e_pow_two [CharP F 2] (q : ↥(c134Q G₀ L)) : C.e (q ^ 2) = 0 := by
  rw [sq, C.mul]
  funext i j
  exact CharTwo.add_self_eq_zero _

theorem sq_eq_one_of_mem_Wμ [Finite G] [CharP F 2] {μ : Fin 2 → F} (hμ : μ ≠ 0) {x : G}
    (hx : x ∈ C.Wμ μ) : x ^ 2 = 1 := by
  classical
  obtain ⟨i₀, hi₀⟩ : ∃ i, μ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hμ (funext h)
  have hsqU : ∀ q : ↥(c134Q G₀ L), ((q ^ 2 : ↥(c134Q G₀ L)) : G) ∈ centerOf (c134Q G₀ L) :=
    fun q => (C.ker _).mp (C.e_pow_two q)
  have hUsq : ∀ u : ↥(centerOf (c134Q G₀ L)), u ^ 2 = 1 := by
    intro u
    apply crd_injective H.nat
    rw [sq, crd_mul, crd_one]
    funext i j
    exact CharTwo.add_self_eq_zero _
  choose sec hsec using C.surj
  let sq' : (Fin 3 → F) → ↥(centerOf (c134Q G₀ L)) := fun y =>
    ⟨_, hsqU (sec (tns μ y))⟩
  have hwd : ∀ q q' : ↥(c134Q G₀ L), C.e q = C.e q' → q ^ 2 = q' ^ 2 := by
    intro q q' h
    have h1 := (C.e_eq_iff q q').mp h
    set u := q⁻¹ * q' with hu
    have hqu : q' = q * u := by rw [hu]; group
    have hc : (q : G) * u = u * q := Subgroup.mem_centralizer_iff.mp h1.2 q q.2
    have hu2 : ((u : G)) ^ 2 = 1 := by
      have := congrArg Subtype.val (hUsq ⟨u, h1⟩)
      simpa using this
    apply Subtype.ext
    rw [hqu]
    simp only [sq, Subgroup.coe_mul] at hu2 ⊢
    calc (q : G) * q = q * q * (u * u) := by rw [hu2, mul_one]
      _ = q * (q * u) * u := by group
      _ = q * (u * q) * u := by rw [hc]
      _ = q * u * (q * u) := by group
  let φ : (Fin 3 → F) → (Fin 3 → F) := fun y => crd H.nat (sq' y) 0
  have hφ : φ = fun _ => 0 := by
    funext y
    refine eq_zero_of_dual_equivariant φ (fun γ y => ?_) y
    obtain ⟨g, hg⟩ := H.ρd_surjective (dualHom γ)
    have hgN := H.le_normalizer_Q (H.le g.2)
    have hgU := H.le_normalizer_U (H.le g.2)
    have hnat : slNat α g = γ := by
      rw [← dualHom_dualHom (slNat α g)]
      show dualHom (H.ρd g) = γ
      rw [hg, dualHom_dualHom]
    have h1 : C.e (cnj hgN (sec (tns μ y))) =
        tns μ ((dualHom γ : SpecialLinearGroup (Fin 3) F) *ᵥ y) := by
      rw [C.conjL, hsec, hg]
      funext i
      simp [tns, dact, mulVec_smul]
    have h2 : sec (tns μ ((dualHom γ : SpecialLinearGroup (Fin 3) F) *ᵥ y)) ^ 2 =
        cnj hgN (sec (tns μ y)) ^ 2 := hwd _ _ (by rw [hsec, h1])
    have h3 : (sq' ((dualHom γ : SpecialLinearGroup (Fin 3) F) *ᵥ y)) =
        cnj hgU (sq' y) := by
      apply Subtype.ext
      have h4 := congrArg Subtype.val h2
      simp only [SubgroupClass.coe_pow, coe_cnj] at h4
      show ((sec (tns μ ((dualHom γ : SpecialLinearGroup (Fin 3) F) *ᵥ y)) ^ 2 :
        ↥(c134Q G₀ L)) : G) = g * ((sec (tns μ y) ^ 2 : ↥(c134Q G₀ L)) : G) * (g : G)⁻¹
      simp only [SubgroupClass.coe_pow]
      rw [h4, sq, sq]
      group
    show crd H.nat _ 0 = _
    rw [h3, crd_conj_false H.nat g (sq' y) _ rfl, hnat]
    rfl
  obtain ⟨hxQ, y, hy⟩ := hx
  have h0 : crd H.nat (sq' y) = 0 := by
    funext i
    rw [Subsingleton.elim i 0]
    exact congrFun hφ y
  have h1 : sq' y = 1 := crd_injective H.nat (h0.trans (crd_one H.nat).symm)
  have h2 : (⟨x, hxQ⟩ : ↥(c134Q G₀ L)) ^ 2 = sec (tns μ y) ^ 2 := hwd _ _ (by rw [hsec, hy])
  have h3 := congrArg Subtype.val h2
  have h4 := congrArg Subtype.val h1
  simp only [SubgroupClass.coe_pow] at h3
  rw [h3]
  exact h4

theorem mul_comm_of_mem_Wμ [Finite G] [CharP F 2] {μ : Fin 2 → F} (hμ : μ ≠ 0) {x y : G}
    (hx : x ∈ C.Wμ μ) (hy : y ∈ C.Wμ μ) : x * y = y * x := by
  have h1 := C.sq_eq_one_of_mem_Wμ hμ ((C.Wμ μ).mul_mem hx hy)
  have h2 := C.sq_eq_one_of_mem_Wμ hμ hx
  have h3 := C.sq_eq_one_of_mem_Wμ hμ hy
  rw [sq] at h1 h2 h3
  calc x * y = x * (x * y * (x * y)) * y := by rw [h1, mul_one]
    _ = (x * x) * y * x * (y * y) := by group
    _ = y * x := by rw [h2, h3]; group

abbrev e₀ (F : Type) [Field F] : Fin 2 → F := ![1, 0]

theorem e₀_ne_zero : e₀ F ≠ 0 := fun h => by simpa using congrFun h 0

theorem mem_W_iff (q : ↥(c134Q G₀ L)) : (q : G) ∈ C.Wμ (e₀ F) ↔ C.e q 1 = 0 := by
  rw [mem_Wμ_iff]
  constructor
  · rintro ⟨y, hy⟩
    rw [hy]
    simp [tns]
  · intro h
    refine ⟨C.e q 0, funext fun i => ?_⟩
    fin_cases i
    · simp [tns]
    · simp [tns, h]

theorem e_cnj_one (a : ↥L) (q : ↥(c134Q G₀ L)) :
    C.e (cnj (H.le_normalizer_Q (H.le a.2)) q) 1 =
      ((H.ρd a : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ C.e q 1 := by
  rw [C.conjL]
  rfl

theorem e_cnj_zero (a : ↥L) (q : ↥(c134Q G₀ L)) :
    C.e (cnj (H.le_normalizer_Q (H.le a.2)) q) 0 =
      ((H.ρd a : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ C.e q 0 := by
  rw [C.conjL]
  rfl

theorem eq_top_of_sl_invariant (K : AddSubgroup (Fin 3 → F))
    (hK : ∀ (γ : SpecialLinearGroup (Fin 3) F) (z : Fin 3 → F), z ∈ K →
      (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ z ∈ K) {z : Fin 3 → F} (hz : z ∈ K) (hz0 : z ≠ 0) :
    K = ⊤ :=
  eq_top_of_transvection_invariant K (fun _ _ _ _ v hv => hK _ v hv) hz hz0

theorem mem_W_of_commute [Finite G] [CharP F 2] (q : ↥(c134Q G₀ L))
    (hq : ∀ w ∈ C.Wμ (e₀ F), (q : G) * w = w * q) : (q : G) ∈ C.Wμ (e₀ F) := by
  classical
  by_contra hqW
  rw [C.mem_W_iff] at hqW
  let K : AddSubgroup (Fin 3 → F) :=
    { carrier := {z | ∃ q' : ↥(c134Q G₀ L), (∀ w ∈ C.Wμ (e₀ F), (q' : G) * w = w * q') ∧
        C.e q' 1 = z}
      add_mem' := by
        rintro _ _ ⟨q₁, h₁, rfl⟩ ⟨q₂, h₂, rfl⟩
        refine ⟨q₁ * q₂, fun w hw => ?_, by rw [C.mul]; rfl⟩
        simp only [Subgroup.coe_mul]
        rw [mul_assoc, h₂ w hw, ← mul_assoc, h₁ w hw, mul_assoc]
      zero_mem' := ⟨1, fun w _ => by simp, by
        rw [(C.ker 1).mpr (centerOf (c134Q G₀ L)).one_mem]; rfl⟩
      neg_mem' := by
        rintro _ ⟨q₁, h₁, rfl⟩
        refine ⟨q₁⁻¹, fun w hw => ?_, by rw [C.e_inv]; rfl⟩
        have := h₁ w hw
        simp only [Subgroup.coe_inv]
        calc (q₁ : G)⁻¹ * w = (q₁ : G)⁻¹ * (w * q₁) * (q₁ : G)⁻¹ := by group
          _ = (q₁ : G)⁻¹ * (q₁ * w) * (q₁ : G)⁻¹ := by rw [this]
          _ = w * (q₁ : G)⁻¹ := by group }
  have hKtop : K = ⊤ := by
    refine eq_top_of_sl_invariant K (fun γ z hz => ?_) ⟨q, hq, rfl⟩ hqW
    obtain ⟨q₁, h₁, rfl⟩ := hz
    obtain ⟨a, ha⟩ := H.ρd_surjective γ
    have haN := H.le_normalizer_Q (H.le a.2)
    refine ⟨cnj haN q₁, fun w hw => ?_, by rw [C.e_cnj_one, ha]⟩
    have haN' := H.le_normalizer_Q (H.le (L.inv_mem a.2))
    have hw' : (a : G)⁻¹ * w * a ∈ C.Wμ (e₀ F) := by
      have hwQ := C.Wμ_le (e₀ F) hw
      have h2 : C.e (cnj haN' ⟨w, hwQ⟩) 1 = 0 := by
        have h3 := C.e_cnj_one ⟨_, L.inv_mem a.2⟩ ⟨w, hwQ⟩
        rw [(C.mem_W_iff ⟨w, hwQ⟩).mp hw, mulVec_zero] at h3
        exact h3
      have h4 := (C.mem_W_iff (cnj haN' ⟨w, hwQ⟩)).mpr h2
      simpa [coe_cnj] using h4
    have h5 := h₁ _ hw'
    simp only [coe_cnj]
    calc (a : G) * q₁ * (a : G)⁻¹ * w = a * (q₁ * ((a : G)⁻¹ * w * a)) * (a : G)⁻¹ := by group
      _ = a * (((a : G)⁻¹ * w * a) * q₁) * (a : G)⁻¹ := by rw [h5]
      _ = w * (a * q₁ * (a : G)⁻¹) := by group
  obtain ⟨y, hy0⟩ : ∃ y : Fin 3 → F, y ≠ 0 := ⟨Pi.single 0 1, by simp⟩
  obtain ⟨w, hw⟩ := C.surj (fun i => if i = 0 then y else 0)
  have hwW : (w : G) ∈ C.Wμ (e₀ F) := (C.mem_W_iff w).mpr (by rw [hw]; simp)
  have hwU : (w : G) ∈ centerOf (c134Q G₀ L) := by
    refine ⟨w.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hx1 : C.e ⟨x, hx⟩ 1 ∈ K := by rw [hKtop]; trivial
    obtain ⟨q₁, h₁, he⟩ := hx1
    have hd : (((q₁⁻¹ * ⟨x, hx⟩ : ↥(c134Q G₀ L))) : G) ∈ C.Wμ (e₀ F) := by
      rw [C.mem_W_iff, C.mul, C.e_inv]
      simp [he]
    have hc1 := h₁ w hwW
    have hc2 := C.mul_comm_of_mem_Wμ e₀_ne_zero hd hwW
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc2
    calc x * w = q₁ * ((q₁ : G)⁻¹ * x) * w := by group
      _ = q₁ * (w * ((q₁ : G)⁻¹ * x)) := by rw [mul_assoc, hc2]
      _ = w * q₁ * ((q₁ : G)⁻¹ * x) := by rw [← mul_assoc, hc1]
      _ = w * x := by group
  have h0 := (C.ker w).mpr hwU
  rw [hw] at h0
  exact hy0 (by simpa using congrFun h0 0)

theorem commute_of_sq {x y : G} (hx : x ^ 2 = 1) (hy : y ^ 2 = 1) (hxy : (x * y) ^ 2 = 1) :
    x * y = y * x := by
  rw [sq] at hx hy hxy
  calc x * y = x * (x * y * (x * y)) * y := by rw [hxy, mul_one]
    _ = (x * x) * y * x * (y * y) := by group
    _ = y * x := by rw [hx, hy]; group

theorem eq_top_of_stab_invariant (K : AddSubgroup (Fin 3 → F))
    (hK : ∀ (γ : SpecialLinearGroup (Fin 3) F), (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ ![1, 0, 0] =
      ![1, 0, 0] → ∀ z ∈ K, (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ z ∈ K)
    (h0 : ∀ b : F, b • (![1, 0, 0] : Fin 3 → F) ∈ K) {z : Fin 3 → F} (hz : z ∈ K)
    (hz1 : z 1 ≠ 0 ∨ z 2 ≠ 0) : K = ⊤ := by
  classical
  have hfix : ∀ (i j : Fin 3) (hij : i ≠ j), j ≠ 0 → ∀ (b : F) (v : Fin 3 → F), v ∈ K →
      Pi.single i (b * v j) ∈ K := by
    intro i j hij hj b v hv
    have hj0 : (![1, 0, 0] : Fin 3 → F) j = 0 := by fin_cases j <;> simp_all
    have h1 := hK (SpecialLinearGroup.transvection hij b) (by
      rw [transvection_mulVec, hj0, mul_zero, Pi.single_zero, add_zero]) v hv
    rw [transvection_mulVec] at h1
    have h2 := K.sub_mem h1 hv
    rwa [add_sub_cancel_left] at h2
  have hsingle : ∀ (i : Fin 3) (b : F), Pi.single i b ∈ K := by
    have h12 : ∀ b : F, Pi.single 2 b ∈ K ∧ Pi.single 1 b ∈ K := by
      rcases hz1 with h | h
      · have e2 : ∀ b : F, Pi.single 2 b ∈ K := fun b => by
          have := hfix 2 1 (by decide) (by decide) (b / z 1) z hz
          rwa [div_mul_cancel₀ b h] at this
        refine fun b => ⟨e2 b, ?_⟩
        have := hfix 1 2 (by decide) (by decide) b (Pi.single 2 1) (e2 1)
        simpa using this
      · have e1 : ∀ b : F, Pi.single 1 b ∈ K := fun b => by
          have := hfix 1 2 (by decide) (by decide) (b / z 2) z hz
          rwa [div_mul_cancel₀ b h] at this
        refine fun b => ⟨?_, e1 b⟩
        have := hfix 2 1 (by decide) (by decide) b (Pi.single 1 1) (e1 1)
        simpa using this
    intro i b
    fin_cases i
    · have := h0 b
      convert this using 1
      funext l
      fin_cases l <;> simp
    · exact (h12 b).2
    · exact (h12 b).1
  refine eq_top_iff.mpr fun v _ => ?_
  have hv : v = Pi.single 0 (v 0) + Pi.single 1 (v 1) + Pi.single 2 (v 2) := by
    funext l
    fin_cases l <;> simp
  rw [hv]
  exact K.add_mem (K.add_mem (hsingle 0 _) (hsingle 1 _)) (hsingle 2 _)

theorem mem_span_of_commute [Finite G] [CharP F 2] {w : ↥(c134Q G₀ L)} (hw1 : C.e w 1 = 0)
    (hw0 : C.e w 0 ≠ 0) {q : ↥(c134Q G₀ L)} (hq : (q : G) * w = w * q) :
    ∃ b : F, C.e q 1 = b • C.e w 0 := by
  classical
  set y := C.e w 0 with hy
  have hwW : (w : G) ∈ C.Wμ (e₀ F) := (C.mem_W_iff w).mpr hw1
  let K : AddSubgroup (Fin 3 → F) :=
    { carrier := {z | ∃ q' : ↥(c134Q G₀ L), (q' : G) * w = w * q' ∧ C.e q' 1 = z}
      add_mem' := by
        rintro _ _ ⟨q₁, h₁, rfl⟩ ⟨q₂, h₂, rfl⟩
        refine ⟨q₁ * q₂, ?_, by rw [C.mul]; rfl⟩
        simp only [Subgroup.coe_mul]
        rw [mul_assoc, h₂, ← mul_assoc, h₁, mul_assoc]
      zero_mem' := ⟨1, by simp, by rw [(C.ker 1).mpr (centerOf (c134Q G₀ L)).one_mem]; rfl⟩
      neg_mem' := by
        rintro _ ⟨q₁, h₁, rfl⟩
        refine ⟨q₁⁻¹, ?_, by rw [C.e_inv]; rfl⟩
        simp only [Subgroup.coe_inv]
        calc (q₁ : G)⁻¹ * w = (q₁ : G)⁻¹ * (w * q₁) * (q₁ : G)⁻¹ := by group
          _ = (q₁ : G)⁻¹ * (q₁ * w) * (q₁ : G)⁻¹ := by rw [h₁]
          _ = w * (q₁ : G)⁻¹ := by group }
  have hspan : ∀ b : F, b • y ∈ K := by
    intro b
    obtain ⟨q₂, hq₂⟩ := C.surj (fun i => if i = 0 then 0 else b • y)
    refine ⟨q₂, ?_, by rw [hq₂]; simp⟩
    have h1 : (q₂ : G) ∈ C.Wμ ![0, 1] := (C.mem_Wμ_iff q₂).mpr ⟨b • y, by
      rw [hq₂]
      funext i
      fin_cases i <;> simp [tns]⟩
    have h2 : ((w * q₂ : ↥(c134Q G₀ L)) : G) ∈ C.Wμ ![1, b] := (C.mem_Wμ_iff _).mpr ⟨y, by
      rw [C.mul, hq₂]
      funext i
      fin_cases i
      · simp [tns, hy]
      · simp [tns, hw1]⟩
    have hne01 : (![0, 1] : Fin 2 → F) ≠ 0 := fun h => by simpa using congrFun h 1
    have hne1b : (![1, b] : Fin 2 → F) ≠ 0 := fun h => by simpa using congrFun h 0
    exact (commute_of_sq (C.sq_eq_one_of_mem_Wμ hne01 h1)
      (C.sq_eq_one_of_mem_Wμ e₀_ne_zero hwW) (by
        have := C.sq_eq_one_of_mem_Wμ hne1b h2
        simp only [Subgroup.coe_mul] at this
        calc ((q₂ : G) * w) ^ 2 = (w : G)⁻¹ * ((w * q₂) ^ 2) * w := by rw [sq, sq]; group
          _ = 1 := by rw [this]; group))
  have hstab : ∀ (γ : SpecialLinearGroup (Fin 3) F), (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ y = y →
      ∀ z ∈ K, (γ : Matrix (Fin 3) (Fin 3) F) *ᵥ z ∈ K := by
    rintro γ hγ _ ⟨q₁, h₁, rfl⟩
    obtain ⟨a, ha⟩ := H.ρd_surjective γ
    have haN := H.le_normalizer_Q (H.le a.2)
    refine ⟨cnj haN q₁, ?_, by rw [C.e_cnj_one, ha]⟩
    have hw' : C.e (cnj haN w) = C.e w := by
      funext i
      fin_cases i
      · show C.e (cnj haN w) 0 = C.e w 0
        rw [C.e_cnj_zero, ha, ← hy, hγ]
      · show C.e (cnj haN w) 1 = C.e w 1
        rw [C.e_cnj_one, hw1, mulVec_zero]
    have hu := (C.e_eq_iff w (cnj haN w)).mp hw'.symm
    set u := w⁻¹ * cnj haN w with hudef
    have hwu : ((cnj haN w : ↥(c134Q G₀ L)) : G) = w * u := by rw [hudef]; simp
    have hcu : ((cnj haN q₁ : ↥(c134Q G₀ L)) : G) * u = u * cnj haN q₁ :=
      (Subgroup.mem_centralizer_iff.mp hu.2 _ (cnj haN q₁).2)
    have h2 : ((cnj haN q₁ : ↥(c134Q G₀ L)) : G) * (cnj haN w : ↥(c134Q G₀ L)) =
        (cnj haN w : ↥(c134Q G₀ L)) * cnj haN q₁ := by
      simp only [coe_cnj]
      calc (a : G) * q₁ * (a : G)⁻¹ * (a * w * (a : G)⁻¹) = a * (q₁ * w) * (a : G)⁻¹ := by group
        _ = a * (w * q₁) * (a : G)⁻¹ := by rw [h₁]
        _ = a * w * (a : G)⁻¹ * (a * q₁ * (a : G)⁻¹) := by group
    rw [hwu] at h2
    calc ((cnj haN q₁ : ↥(c134Q G₀ L)) : G) * w =
          ((cnj haN q₁ : ↥(c134Q G₀ L)) : G) * (w * u) * (u : G)⁻¹ := by group
      _ = (w * u) * cnj haN q₁ * (u : G)⁻¹ := by rw [h2]
      _ = w * (u * cnj haN q₁) * (u : G)⁻¹ := by group
      _ = w * (cnj haN q₁ * u) * (u : G)⁻¹ := by rw [hcu]
      _ = w * cnj haN q₁ := by group
  by_contra hnot
  push Not at hnot
  obtain ⟨γ₁, hγ₁⟩ := SL3Pt.exists_mulVec_e0 hw0
  let K' : AddSubgroup (Fin 3 → F) := K.comap
    (Matrix.mulVecLin ((γ₁ : Matrix (Fin 3) (Fin 3) F))).toAddMonoidHom
  have hmemK' : ∀ v, v ∈ K' ↔ (γ₁ : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ K := fun v => Iff.rfl
  have hK'top : K' = ⊤ := by
    have hinv1 := coe_sl_mul_inv γ₁
    have hz : (γ₁⁻¹ : SpecialLinearGroup (Fin 3) F) *ᵥ C.e q 1 ∈ K' := by
      rw [hmemK', mulVec_mulVec, hinv1, one_mulVec]
      exact ⟨q, hq, rfl⟩
    refine eq_top_of_stab_invariant K' (fun γ hγ z hz' => ?_) (fun b => ?_) hz ?_
    · rw [hmemK'] at hz' ⊢
      have h1 : (γ₁ * γ * γ₁⁻¹ : SpecialLinearGroup (Fin 3) F) *ᵥ y = y := by
        rw [← hγ₁, coe_sl_mul, coe_sl_mul, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
          coe_sl_inv_mul, Matrix.mul_one, ← mulVec_mulVec, hγ]
      have h2 := hstab _ h1 _ hz'
      rwa [coe_sl_mul, coe_sl_mul, mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc,
        coe_sl_inv_mul, Matrix.mul_one, ← mulVec_mulVec] at h2
    · rw [hmemK', mulVec_smul, hγ₁]
      exact hspan b
    · by_contra hzz
      push Not at hzz
      apply hnot ((((γ₁⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        C.e q 1) 0)
      have h3 : ((γ₁⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ C.e q 1 =
          ((((γ₁⁻¹ : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ C.e q 1) 0) •
            ![1, 0, 0] := by
        funext l
        fin_cases l
        · simp
        · exact hzz.1.trans (by simp)
        · exact hzz.2.trans (by simp)
      have h4 := congrArg (fun v => (γ₁ : Matrix (Fin 3) (Fin 3) F) *ᵥ v) h3
      rwa [mulVec_mulVec, coe_sl_mul_inv, one_mulVec, mulVec_smul, hγ₁] at h4
  have hwU : (w : G) ∈ centerOf (c134Q G₀ L) := by
    refine ⟨w.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hx1 : (γ₁⁻¹ : SpecialLinearGroup (Fin 3) F) *ᵥ C.e ⟨x, hx⟩ 1 ∈ K' := by
      rw [hK'top]; trivial
    rw [hmemK', mulVec_mulVec, coe_sl_mul_inv, one_mulVec] at hx1
    obtain ⟨q₁, h₁, he⟩ := hx1
    have hd : (((q₁⁻¹ * ⟨x, hx⟩ : ↥(c134Q G₀ L))) : G) ∈ C.Wμ (e₀ F) := by
      rw [C.mem_W_iff, C.mul, C.e_inv]
      simp [he]
    have hc2 := C.mul_comm_of_mem_Wμ e₀_ne_zero hd hwW
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hc2
    calc x * w = q₁ * ((q₁ : G)⁻¹ * x) * w := by group
      _ = q₁ * (w * ((q₁ : G)⁻¹ * x)) := by rw [mul_assoc, hc2]
      _ = w * q₁ * ((q₁ : G)⁻¹ * x) := by rw [← mul_assoc, h₁]
      _ = w * x := by group
  exact hw0 (by rw [hy, (C.ker w).mpr hwU]; rfl)

end Adapted

end Hyp135

end CFSG.Quasithin.H13.Ch4.C135

end
