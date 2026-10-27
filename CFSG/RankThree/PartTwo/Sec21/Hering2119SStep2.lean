module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119SNAGroup
public import CFSG.RankThree.PartTwo.Sec21.Hering2119SLine
public import CFSG.RankThree.PartTwo.Sec21.Hering2119SQuat

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119S

open Module

section LinLine

variable {G : Type} [Group G] [Finite G] (D : Subgroup G) [Fact (IsElem3 D)]

@[expose] noncomputable def epsE (n : Subgroup.normalizer (D : Set G)) : Vec D →ₗ[F3] Vec D :=
  (conjLinHom D n : Vec D →ₗ[F3] Vec D) - LinearMap.id

@[expose] noncomputable def imgY (Y : Subgroup G) : Subgroup (Vec D ≃ₗ[F3] Vec D) :=
  (Y.subgroupOf (Subgroup.normalizer (D : Set G))).map (conjLinHom D)

theorem mem_imgY {Y : Subgroup G} {g : Vec D ≃ₗ[F3] Vec D} :
    g ∈ imgY D Y ↔ ∃ n : Subgroup.normalizer (D : Set G), (n : G) ∈ Y ∧ conjLinHom D n = g := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n, hn, rfl⟩

theorem epsE_apply (n : Subgroup.normalizer (D : Set G)) (v : Vec D) :
    conjLinHom D n v = v + epsE D n v := by
  simp [epsE]

theorem toD_epsE (n : Subgroup.normalizer (D : Set G)) (v : Vec D) :
    ((Vec.toD (epsE D n v) : D) : G) =
      (n : G) * (Vec.toD v : D) * (n : G)⁻¹ * ((Vec.toD v : D) : G)⁻¹ := by
  have : epsE D n v = conjLinHom D n v + -v := by simp [epsE, sub_eq_add_neg]
  rw [this, Vec.toD_add, Vec.toD_neg]
  rfl

structure LinFacts (M Y : Subgroup G) (n : Subgroup.normalizer (D : Set G)) : Prop where
  hεε : ∀ v, epsE D n (epsE D n v) = 0
  hk : ∀ v, epsE D n v = 0 → v ∈ LinearMap.range (epsE D n)
  hW : ∀ v, v ∈ LinearMap.range (epsE D n) ↔ ((Vec.toD v : D) : G) ∈ M
  huK : conjLinHom D n ∈ imgY D Y
  hcomm : ∀ g ∈ imgY D Y, ∀ v, g (epsE D n v) = epsE D n (g v)
  htrans : ∀ w w' : Vec D, w ∈ LinearMap.range (epsE D n) → w' ∈ LinearMap.range (epsE D n) →
    w ≠ 0 → w' ≠ 0 → ∃ g ∈ imgY D Y, g w = w'
  hord3 : ∃ s ∈ imgY D Y, s ^ 3 = 1 ∧ ∃ w ∈ LinearMap.range (epsE D n), s w ≠ w
  hW9 : Nat.card (LinearMap.range (epsE D n)) = 9

theorem line_lin {M Y : Subgroup G} {e : G} (hD81 : Nat.card D = 81) (h : LineAbs D M Y e) :
    LinFacts D M Y ⟨e, h.heN⟩ := by
  classical
  haveI : Finite (Vec D) := inferInstanceAs (Finite (Additive D))
  have hD : IsElem3 D := Fact.out
  set N : Subgroup G := Subgroup.normalizer (D : Set G) with hNdef
  let ρ : N →* (Vec D ≃ₗ[F3] Vec D) := conjLinHom D
  let eN : N := ⟨e, h.heN⟩
  let ε : Vec D →ₗ[F3] Vec D := epsE D eN
  have toD_ε : ∀ v : Vec D, ((Vec.toD (ε v) : D) : G) =
      e * (Vec.toD v : D) * e⁻¹ * ((Vec.toD v : D) : G)⁻¹ := toD_epsE D eN
  let Mv : Submodule F3 (Vec D) := Vec.sub D M
  have hmemMv : ∀ v : Vec D, v ∈ Mv ↔ ((Vec.toD v : D) : G) ∈ M := fun v => Iff.rfl
  have hker : ∀ v, ε v = 0 ↔ v ∈ Mv := by
    intro v
    rw [hmemMv]
    have hv := (Vec.toD v).2
    constructor
    · intro h0
      apply h.hkerM _ hv
      rw [← toD_ε v, h0, Vec.toD_zero]
      rfl
    · intro hm
      apply Vec.toD_injective
      apply Subtype.ext
      rw [toD_ε v, Vec.toD_zero]
      have := h.hMc _ hm
      rw [this]
      simp
  have hrange_le : LinearMap.range ε ≤ Mv := by
    rintro _ ⟨v, rfl⟩
    rw [hmemMv, toD_ε]
    exact h.hεM _ (Vec.toD v).2
  have hMv9 : Nat.card Mv = 9 := by
    rw [← h.hM9]
    exact Nat.card_congr
      { toFun := fun v => ⟨((Vec.toD v.1 : D) : G), v.2⟩
        invFun := fun m => ⟨Vec.ofD ⟨m.1, h.hMD m.2⟩, m.2⟩
        left_inv := fun v => rfl
        right_inv := fun m => rfl }
  have hkercard : Nat.card (LinearMap.ker ε) = 9 := by
    rw [← hMv9]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun v => by rw [LinearMap.mem_ker, hker v])
  have hVcard : Nat.card (Vec D) = 81 := by
    rw [← hD81]
    exact Nat.card_congr (Additive.toMul)
  have hrange9 : Nat.card (LinearMap.range ε) = 9 := by
    have h' := AddSubgroup.card_ker_mul_card_range ε.toAddMonoidHom
    have h1 : Nat.card (ε.toAddMonoidHom).ker = 9 := by
      rw [← hkercard]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun v => by
        rw [LinearMap.mem_ker]; rfl)
    have h2 : Nat.card (ε.toAddMonoidHom).range = Nat.card (LinearMap.range ε) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun v => by
        rw [LinearMap.mem_range]; rfl)
    rw [h1, h2, hVcard] at h'
    omega
  have hrange_eq : LinearMap.range ε = Mv := by
    have h' := AddSubgroup.eq_of_le_of_card_ge (H := (LinearMap.range ε).toAddSubgroup)
      (K := Mv.toAddSubgroup) hrange_le (by
        show Nat.card Mv ≤ Nat.card (LinearMap.range ε)
        rw [hMv9, hrange9])
    exact Submodule.toAddSubgroup_injective h'
  have hmemR : ∀ v, v ∈ LinearMap.range ε ↔ ((Vec.toD v : D) : G) ∈ M := by
    intro v; rw [hrange_eq]; exact hmemMv v
  have hρker : ∀ n : N, (n : G) ∈ Subgroup.centralizer (D : Set G) → ρ n = 1 := fun n hn =>
    (conjLinHom_eq_one_iff D n).mpr hn
  refine ⟨fun v => (hker _).mpr (hrange_eq ▸ LinearMap.mem_range_self ε v),
    fun v hv => hrange_eq ▸ (hker v).mp hv, hmemR, ?_, ?_, ?_, ?_, hrange9⟩
  · exact (mem_imgY D).mpr ⟨eN, h.heY, rfl⟩
  ·
    intro g hg v
    obtain ⟨n, hn, rfl⟩ := (mem_imgY D).mp hg
    obtain ⟨k, hkM, hw⟩ := h.hcent n hn
    have hkD : k ∈ D := h.hMD hkM
    let kN : N := ⟨k, Subgroup.le_normalizer hkD⟩
    have hkC : ρ kN = 1 :=
      hρker kN (Subgroup.mem_centralizer_iff.mpr fun x hx => hD.comm x hx k hkD)
    have e1 : n * eN = eN * kN * n := by
      apply Subtype.ext
      change (n : G) * e = e * k * (n : G)
      rw [← hw]
      group
    have hcu : ρ n * ρ eN = ρ eN * ρ n := by
      calc ρ n * ρ eN = ρ (n * eN) := by rw [map_mul]
        _ = ρ (eN * kN * n) := by rw [e1]
        _ = ρ eN * ρ n := by rw [map_mul, map_mul, hkC, mul_one]
    have hv : ρ eN (ρ n v) = ρ n (ρ eN v) := by
      have := congrArg (fun f : Vec D ≃ₗ[F3] Vec D => f v) hcu
      exact this.symm
    simp only [ε, epsE, LinearMap.sub_apply, LinearEquiv.coe_coe, LinearMap.id_apply, map_sub]
    rw [hv]
  · intro w w' hw hw' hw0 hw'0
    have hwM := (hmemR w).mp hw
    have hw'M := (hmemR w').mp hw'
    have hw1 : ((Vec.toD w : D) : G) ≠ 1 := fun h' => hw0 (by
      apply Vec.toD_injective
      rw [Vec.toD_zero]
      exact Subtype.ext h')
    have hw'1 : ((Vec.toD w' : D) : G) ≠ 1 := fun h' => hw'0 (by
      apply Vec.toD_injective
      rw [Vec.toD_zero]
      exact Subtype.ext h')
    obtain ⟨m, hmY, hmw⟩ := h.htrans _ hwM _ hw'M hw1 hw'1
    refine ⟨ρ ⟨m, h.hYN hmY⟩, (mem_imgY D).mpr ⟨_, hmY, rfl⟩, ?_⟩
    apply Vec.toD_injective
    apply Subtype.ext
    rw [toD_conjLinHom]
    exact hmw
  · obtain ⟨q, hqY, hq3, m, hmM, hqm⟩ := h.hq
    refine ⟨ρ ⟨q, h.hYN hqY⟩, (mem_imgY D).mpr ⟨_, hqY, rfl⟩, ?_, Vec.ofD ⟨m, h.hMD hmM⟩, ?_, ?_⟩
    · rw [← map_pow]
      have : (⟨q, h.hYN hqY⟩ : N) ^ 3 = 1 := by
        apply Subtype.ext
        simpa using hq3
      rw [this, map_one]
    · exact (hmemR _).mpr hmM
    · intro h'
      apply hqm
      have := congrArg (fun v : Vec D => ((Vec.toD v : D) : G)) h'
      change q * m * q⁻¹ = m at this
      exact this

theorem bound_lin {M Y : Subgroup G} {e : G} (h : LineAbs D M Y e) :
    ∀ X : Subgroup (Vec D ≃ₗ[F3] Vec D), X ≤ (conjLinHom D).range → IsPGroup 3 X →
      conjLinHom D ⟨e, h.heN⟩ ∈ X →
      (∀ x ∈ X, x * conjLinHom D ⟨e, h.heN⟩ = conjLinHom D ⟨e, h.heN⟩ * x) →
        Nat.card X ≤ 81 := by
  classical
  intro X hXr hX3 heX hXcomm
  set N : Subgroup G := Subgroup.normalizer (D : Set G) with hNdef
  let ρ : N →* (Vec D ≃ₗ[F3] Vec D) := conjLinHom D
  let eN : N := ⟨e, h.heN⟩
  obtain ⟨S, hS3, heS, hSX, hcard⟩ := exists_pgroup_lift ρ X hXr hX3 eN heX
    (Subtype.ext (by simpa using h.he3))
  let S' : Subgroup G := S.map N.subtype
  have hS'3 : IsPGroup 3 S' := hS3.map _
  have heS' : e ∈ S' := ⟨eN, heS, rfl⟩
  have hS'comm : ∀ x ∈ S', x * e * x⁻¹ * e⁻¹ ∈ Subgroup.centralizer (D : Set G) := by
    rintro _ ⟨t, ht, rfl⟩
    have h1 := hXcomm _ (hSX t ht)
    have h2 : ρ (t * eN * t⁻¹ * eN⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      change ρ t * ρ eN * (ρ t)⁻¹ * (ρ eN)⁻¹ = 1
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
      exact h1
    exact (conjLinHom_eq_one_iff D _).mp h2
  have hb := h.hbound S' hS'3 heS' hS'comm
  have hkerS : (S' ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) =
      (S ⊓ ρ.ker : Subgroup N).map N.subtype := by
    ext g
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, hg⟩
      exact ⟨t, ⟨ht, (conjLinHom_eq_one_iff D t).mpr hg⟩, rfl⟩
    · rintro ⟨t, ⟨ht, htk⟩, rfl⟩
      exact ⟨⟨t, ht, rfl⟩, (conjLinHom_eq_one_iff D t).mp htk⟩
  have hc1 : Nat.card S' = Nat.card S := Subgroup.card_map_of_injective N.subtype_injective
  have hc2 : Nat.card (S' ⊓ Subgroup.centralizer (D : Set G) : Subgroup G) =
      Nat.card (S ⊓ ρ.ker : Subgroup N) := by
    rw [hkerS]
    exact Subgroup.card_map_of_injective N.subtype_injective
  rw [hc1, hc2] at hb
  have hpos : 0 < Nat.card (S ⊓ ρ.ker : Subgroup N) := Nat.card_pos
  have h1 : Nat.card X * Nat.card (S ⊓ ρ.ker : Subgroup N) ≤ Nat.card S := hcard
  nlinarith

theorem vec_card (hD81 : Nat.card D = 81) : Nat.card (Vec D) = 81 := by
  rw [← hD81]
  exact Nat.card_congr (Additive.toMul)

theorem imgY_le_range (Y : Subgroup G) : imgY D Y ≤ (conjLinHom D).range := by
  rintro _ ⟨n, -, rfl⟩
  exact ⟨n, rfl⟩

theorem imgY_mono {S Y : Subgroup G} (h : S ≤ Y) : imgY D S ≤ imgY D Y := by
  rintro _ ⟨n, hn, rfl⟩
  exact ⟨n, Subgroup.mem_subgroupOf.mpr (h (Subgroup.mem_subgroupOf.mp hn)), rfl⟩

theorem imgY_isPGroup {p : ℕ} {S : Subgroup G} (hS : IsPGroup p S) : IsPGroup p (imgY D S) :=
  (hS.comap_subtype (K := Subgroup.normalizer (D : Set G))).map _

theorem toD_conj2 (n m : Subgroup.normalizer (D : Set G)) (v : Vec D) :
    ((Vec.toD (conjLinHom D n (conjLinHom D m v)) : D) : G) =
      (n : G) * ((m : G) * (Vec.toD v : D) * (m : G)⁻¹) * (n : G)⁻¹ := by
  rw [toD_conjLinHom, toD_conjLinHom]

theorem toD_neg_coe (v : Vec D) : ((Vec.toD (-v) : D) : G) = ((Vec.toD v : D) : G)⁻¹ := by
  rw [Vec.toD_neg]; rfl

theorem lin_sq {M : Subgroup G} (n : Subgroup.normalizer (D : Set G))
    (h : ∀ m ∈ M, (n : G) * ((n : G) * m * (n : G)⁻¹) * (n : G)⁻¹ = m⁻¹) (w : Vec D)
    (hw : ((Vec.toD w : D) : G) ∈ M) : conjLinHom D n (conjLinHom D n w) = -w := by
  apply Vec.toD_injective
  apply Subtype.ext
  rw [toD_conj2, toD_neg_coe]
  exact h _ hw

theorem lin_anti {M : Subgroup G} (n m : Subgroup.normalizer (D : Set G))
    (h : ∀ x ∈ M, (n : G) * ((m : G) * x * (m : G)⁻¹) * (n : G)⁻¹ =
      ((m : G) * ((n : G) * x * (n : G)⁻¹) * (m : G)⁻¹)⁻¹) (w : Vec D)
    (hw : ((Vec.toD w : D) : G) ∈ M) :
    conjLinHom D n (conjLinHom D m w) = -conjLinHom D m (conjLinHom D n w) := by
  apply Vec.toD_injective
  apply Subtype.ext
  rw [toD_conj2, toD_neg_coe, toD_conj2]
  exact h _ hw

theorem quat_of_line {M Y : Subgroup G} {e : G} (hD81 : Nat.card D = 81) (h : LineAbs D M Y e) :
    ∃ (S : Subgroup G) (a b : Subgroup.normalizer (D : Set G)), IsPGroup 2 S ∧ S ≤ Y ∧
      S ≤ Subgroup.centralizer ({e} : Set G) ∧ (a : G) ∈ S ∧ (b : G) ∈ S ∧
      QRelE (conjLinHom D a) (conjLinHom D b) ∧
      ∀ k ∈ imgY D Y, (∃ y ∈ q8 (conjLinHom D a) (conjLinHom D b), k * conjLinHom D a = y * k) ∧
        (∃ y ∈ q8 (conjLinHom D a) (conjLinHom D b), k * conjLinHom D b = y * k) := by
  classical
  haveI : Finite (Vec D) := inferInstanceAs (Finite (Additive D))
  obtain ⟨S, hS2, hSY, hSe, a, ha, b, hb, hra, hrb, hrab⟩ := h.quat
  have lf := line_lin D hD81 h
  let aN : Subgroup.normalizer (D : Set G) := ⟨a, h.hYN (hSY ha)⟩
  let bN : Subgroup.normalizer (D : Set G) := ⟨b, h.hYN (hSY hb)⟩
  have hq := quat_line (vec_card D hD81) (epsE D ⟨e, h.heN⟩) lf.hεε lf.hk (imgY D Y) lf.hcomm
    (conjLinHom D ⟨e, h.heN⟩) (epsE_apply D _) lf.huK lf.htrans lf.hord3
    (fun X hXK => bound_lin D h X (hXK.trans (imgY_le_range D Y)))
    (imgY D S) (imgY_mono D hSY) (imgY_isPGroup D hS2) (conjLinHom D aN) (conjLinHom D bN)
    ((mem_imgY D).mpr ⟨aN, ha, rfl⟩) ((mem_imgY D).mpr ⟨bN, hb, rfl⟩)
    (fun w hw => lin_sq D aN hra w ((lf.hW w).mp hw))
    (fun w hw => lin_sq D bN hrb w ((lf.hW w).mp hw))
    (fun w hw => lin_anti D aN bN hrab w ((lf.hW w).mp hw))
  exact ⟨S, aN, bN, hS2, hSY, hSe, ha, hb, hq.1, hq.2⟩

theorem pow_eps {V : Type*} [AddCommGroup V] [Module F3 V] (g : V ≃ₗ[F3] V)
    (ε : V →ₗ[F3] V) (hg : ∀ v, g v = v + ε v) (hε : ∀ v, ε (ε v) = 0) (j : ℕ) (v : V) :
    (g ^ j) v = v + (j : F3) • ε v := by
  induction j generalizing v with
  | zero => simp
  | succ j ih =>
    rw [pow_succ]
    show (g ^ j) (g v) = _
    rw [ih (g v), hg v, map_add, hε, add_zero]
    push_cast
    rw [add_smul, one_smul]
    abel

theorem sq_on_D (n : Subgroup.normalizer (D : Set G))
    (h : ∀ v, conjLinHom D n (conjLinHom D n v) = -v) :
    ∀ x ∈ D, (n : G) * ((n : G) * x * (n : G)⁻¹) * (n : G)⁻¹ = x⁻¹ := by
  intro x hx
  have h1 := congrArg (fun v : Vec D => ((Vec.toD v : D) : G)) (h (Vec.ofD ⟨x, hx⟩))
  simp only [toD_conj2, toD_neg_coe, Vec.toD_ofD] at h1
  exact h1

theorem anti_on_D (n m : Subgroup.normalizer (D : Set G))
    (h : ∀ v, conjLinHom D n (conjLinHom D m v) = -conjLinHom D m (conjLinHom D n v)) :
    ∀ x ∈ D, (n : G) * ((m : G) * x * (m : G)⁻¹) * (n : G)⁻¹ =
      ((m : G) * ((n : G) * x * (n : G)⁻¹) * (m : G)⁻¹)⁻¹ := by
  intro x hx
  have h1 := congrArg (fun v : Vec D => ((Vec.toD v : D) : G)) (h (Vec.ofD ⟨x, hx⟩))
  simp only [toD_conj2, toD_neg_coe, Vec.toD_ofD] at h1
  exact h1

theorem comm_on_D (n m : Subgroup.normalizer (D : Set G))
    (h : ∀ v, conjLinHom D n (conjLinHom D m v) = conjLinHom D m (conjLinHom D n v)) :
    ∀ x ∈ D, (n : G) * ((m : G) * x * (m : G)⁻¹) * (n : G)⁻¹ =
      (m : G) * ((n : G) * x * (n : G)⁻¹) * (m : G)⁻¹ := by
  intro x hx
  have h1 := congrArg (fun v : Vec D => ((Vec.toD v : D) : G)) (h (Vec.ofD ⟨x, hx⟩))
  simp only [toD_conj2, Vec.toD_ofD] at h1
  exact h1

end LinLine

section Step2

variable {G : Type} [Group G] [Finite G]

theorem step2_abs {D M₀ M₁ Y₀ Y₁ : Subgroup G} {e₀ e₁ : G} (hD : IsElem3 D)
    (hD81 : Nat.card D = 81) (h₀ : LineAbs D M₀ Y₀ e₀) (h₁ : LineAbs D M₁ Y₁ e₁)
    (he₁Y₀ : e₁ ∈ Y₀) (he₀Y₁ : e₀ ∈ Y₁)
    (hind : ∀ j : ℕ, e₁ * (e₀ ^ j)⁻¹ ∉ Subgroup.centralizer (D : Set G)) :
    ∃ (T : Subgroup G) (a₁ b₁ c₁ t : G), IsPGroup 2 T ∧
      T ≤ Subgroup.normalizer (D : Set G) ∧ a₁ ∈ T ∧ b₁ ∈ T ∧ c₁ ∈ T ∧ t ∈ T ∧
      e₀ * t = t * e₀ ∧ (∀ x ∈ D, t * x * t⁻¹ = x⁻¹) ∧
      (∀ x ∈ D, a₁ * (a₁ * x * a₁⁻¹) * a₁⁻¹ = x⁻¹) ∧
      (∀ x ∈ D, b₁ * (b₁ * x * b₁⁻¹) * b₁⁻¹ = x⁻¹) ∧
      (∀ x ∈ D, c₁ * (c₁ * x * c₁⁻¹) * c₁⁻¹ = x⁻¹) ∧
      (∀ x ∈ D, a₁ * (b₁ * x * b₁⁻¹) * a₁⁻¹ = (b₁ * (a₁ * x * a₁⁻¹) * b₁⁻¹)⁻¹) ∧
      (∀ x ∈ D, a₁ * (c₁ * x * c₁⁻¹) * a₁⁻¹ = c₁ * (a₁ * x * a₁⁻¹) * c₁⁻¹) ∧
      (∀ x ∈ D, b₁ * (c₁ * x * c₁⁻¹) * b₁⁻¹ = c₁ * (b₁ * x * b₁⁻¹) * c₁⁻¹) := by
  classical
  haveI : Fact (IsElem3 D) := ⟨hD⟩
  haveI : Finite (Vec D) := inferInstanceAs (Finite (Additive D))
  set N : Subgroup G := Subgroup.normalizer (D : Set G) with hNdef
  let ρ : N →* (Vec D ≃ₗ[F3] Vec D) := conjLinHom D
  obtain ⟨S₀, a, b, hS₀2, hS₀Y, hS₀e, haS, hbS, hQ₀, hnorm₀⟩ := quat_of_line D hD81 h₀
  obtain ⟨S₁, i, j, hS₁2, hS₁Y, hS₁e, hiS, hjS, hQ₁, hnorm₁⟩ := quat_of_line D hD81 h₁
  have lf₀ := line_lin D hD81 h₀
  have lf₁ := line_lin D hD81 h₁
  let eN₀ : N := ⟨e₀, h₀.heN⟩
  let eN₁ : N := ⟨e₁, h₁.heN⟩
  have hg₁K₀ : ρ eN₁ ∈ imgY D Y₀ := (mem_imgY D).mpr ⟨eN₁, he₁Y₀, rfl⟩
  have hg₀K₁ : ρ eN₀ ∈ imgY D Y₁ := (mem_imgY D).mpr ⟨eN₀, he₀Y₁, rfl⟩
  have haK : ρ a ∈ imgY D Y₀ := (mem_imgY D).mpr ⟨a, hS₀Y haS, rfl⟩
  have hbK : ρ b ∈ imgY D Y₀ := (mem_imgY D).mpr ⟨b, hS₀Y hbS, rfl⟩
  have hiK : ρ i ∈ imgY D Y₁ := (mem_imgY D).mpr ⟨i, hS₁Y hiS, rfl⟩
  have hjK : ρ j ∈ imgY D Y₁ := (mem_imgY D).mpr ⟨j, hS₁Y hjS, rfl⟩
  have hc : ∀ v, epsE D eN₀ (epsE D eN₁ v) = epsE D eN₁ (epsE D eN₀ v) := by
    intro v
    have h := lf₀.hcomm (ρ eN₁) hg₁K₀ v
    rw [epsE_apply D eN₁ (epsE D eN₀ v), epsE_apply D eN₁ v, map_add] at h
    exact (add_left_cancel h).symm
  have hind' : ∀ c : F3, epsE D eN₁ ≠ c • epsE D eN₀ := by
    intro c hc'
    apply hind c.val
    have h1 : ρ eN₁ = ρ eN₀ ^ c.val := by
      apply LinearEquiv.ext
      intro v
      rw [epsE_apply D eN₁ v, pow_eps (ρ eN₀) (epsE D eN₀) (epsE_apply D eN₀) lf₀.hεε c.val v,
        ZMod.natCast_zmod_val, hc']
      rfl
    have h2 : ρ (eN₁ * (eN₀ ^ c.val)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_pow, h1, mul_inv_cancel]
    exact (conjLinHom_eq_one_iff D _).mp h2
  have hpair := pair_linear (vec_card D hD81) (conjLinHom D).range (ρ eN₀) (ρ eN₁) (ρ a) (ρ b)
    (ρ i) (ρ j) (epsE D eN₀) (epsE D eN₁) (epsE_apply D eN₀) (epsE_apply D eN₁)
    ⟨eN₀, rfl⟩ ⟨eN₁, rfl⟩ ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨i, rfl⟩ ⟨j, rfl⟩ lf₀.hεε lf₀.hk lf₁.hεε hc hind'
    hQ₀ hQ₁ (lf₀.hcomm _ haK) (lf₀.hcomm _ hbK) (lf₁.hcomm _ hiK) (lf₁.hcomm _ hjK)
    (hnorm₀ _ hg₁K₀).1 (hnorm₀ _ hg₁K₀).2 (hnorm₁ _ hg₀K₁).1 (hnorm₁ _ hg₀K₁).2
    (bound_lin D h₀)
  obtain ⟨hIc, -, hJc, -⟩ := hpair
  set Q0 : Subgroup (Vec D ≃ₗ[F3] Vec D) := Subgroup.closure {ρ a, ρ b} with hQ0
  set Q1 : Subgroup (Vec D ≃ₗ[F3] Vec D) := Subgroup.zpowers (ρ i) with hQ1
  have haT₀ : ρ a ∈ imgY D S₀ := (mem_imgY D).mpr ⟨a, haS, rfl⟩
  have hbT₀ : ρ b ∈ imgY D S₀ := (mem_imgY D).mpr ⟨b, hbS, rfl⟩
  have hiT₁ : ρ i ∈ imgY D S₁ := (mem_imgY D).mpr ⟨i, hiS, rfl⟩
  have hQ0le : Q0 ≤ imgY D S₀ := by
    rw [hQ0, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact haT₀
    · exact hbT₀
  have hQ1le : Q1 ≤ imgY D S₁ := Subgroup.zpowers_le.mpr hiT₁
  have hQ02 : IsPGroup 2 Q0 := (imgY_isPGroup D hS₀2).to_le hQ0le
  have hQ12 : IsPGroup 2 Q1 := (imgY_isPGroup D hS₁2).to_le hQ1le
  have hQ0c : ∀ g ∈ Q0, g * ρ i = ρ i * g := by
    have : Q0 ≤ Subgroup.centralizer ({ρ i} : Set (Vec D ≃ₗ[F3] Vec D)) := by
      rw [hQ0, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hIc
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hJc
    exact fun g hg => Subgroup.mem_centralizer_singleton_iff.mp (this hg)
  have hQ0N : Q0 ≤ Subgroup.normalizer (Q1 : Set (Vec D ≃ₗ[F3] Vec D)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have hgc : g * ρ i = ρ i * g := hQ0c g hg
    have hconj : ∀ x ∈ Q1, g * x * g⁻¹ = x := by
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hk : g * (ρ i) ^ k = (ρ i) ^ k * g :=
        (Commute.zpow_right (show Commute g (ρ i) from hgc) k).eq
      rw [hk, mul_inv_cancel_right]
    intro x
    constructor
    · intro hx
      rw [hconj x hx]; exact hx
    · intro hx
      have hgy : g * (g * x * g⁻¹) = (g * x * g⁻¹) * g := mul_inv_eq_iff_eq_mul.mp (hconj _ hx)
      have key : x = g * x * g⁻¹ := by
        calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = g⁻¹ * ((g * x * g⁻¹) * g) := by rw [mul_assoc]
          _ = g⁻¹ * (g * (g * x * g⁻¹)) := by rw [hgy]
          _ = g * x * g⁻¹ := by group
      rw [← key] at hx
      exact hx
  have hR2 : IsPGroup 2 (Q0 ⊔ Q1 : Subgroup (Vec D ≃ₗ[F3] Vec D)) :=
    hQ02.to_sup_of_normal_right' hQ12 hQ0N
  have hRr : (Q0 ⊔ Q1 : Subgroup (Vec D ≃ₗ[F3] Vec D)) ≤ ρ.range := by
    refine sup_le ?_ ?_
    · rw [hQ0, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨a, rfl⟩
      · exact ⟨b, rfl⟩
    · exact Subgroup.zpowers_le.mpr ⟨i, rfl⟩
  set S₀' : Subgroup N := Subgroup.closure {a, b} with hS₀'
  have hS₀'le : S₀' ≤ S₀.subgroupOf N := by
    rw [hS₀', Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_subgroupOf.mpr haS
    · exact Subgroup.mem_subgroupOf.mpr hbS
  have hS₀'2 : IsPGroup 2 S₀' := (hS₀2.comap_subtype (K := N)).to_le hS₀'le
  have hS₀'R : ∀ s ∈ S₀', ρ s ∈ (Q0 ⊔ Q1 : Subgroup (Vec D ≃ₗ[F3] Vec D)) := by
    have : S₀' ≤ (Q0 ⊔ Q1).comap ρ := by
      rw [hS₀', Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inl rfl))
      · exact Subgroup.mem_sup_left (Subgroup.subset_closure (Or.inr rfl))
    exact fun s hs => this hs
  obtain ⟨T', hT'2, hS₀'T', hT'R⟩ := lift_two ρ _ hR2 hRr S₀' hS₀'2 hS₀'R
  obtain ⟨c, hcT', hcρ⟩ := hT'R (ρ i) (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have haT' : a ∈ T' := hS₀'T' (Subgroup.subset_closure (Or.inl rfl))
  have hbT' : b ∈ T' := hS₀'T' (Subgroup.subset_closure (Or.inr rfl))
  have hQ₁c : ∀ v, ρ c (ρ c v) = -v := by
    intro v; rw [hcρ]; exact hQ₁.II v
  have haa : ∀ v, ρ a (ρ a v) = -v := hQ₀.II
  have hbb : ∀ v, ρ b (ρ b v) = -v := hQ₀.JJ
  refine ⟨T'.map N.subtype, (a : G), (b : G), (c : G), (a : G) * (a : G), hT'2.map _,
    Subgroup.map_subtype_le T', ⟨a, haT', rfl⟩, ⟨b, hbT', rfl⟩, ⟨c, hcT', rfl⟩,
    ⟨a * a, T'.mul_mem haT' haT', rfl⟩, ?_, ?_, sq_on_D D a haa, sq_on_D D b hbb,
    sq_on_D D c hQ₁c, anti_on_D D a b hQ₀.IJ, comm_on_D D a c ?_, comm_on_D D b c ?_⟩
  · have h := Subgroup.mem_centralizer_singleton_iff.mp (hS₀e haS)
    calc e₀ * ((a : G) * (a : G)) = (e₀ * (a : G)) * (a : G) := by rw [mul_assoc]
      _ = ((a : G) * e₀) * (a : G) := by rw [h]
      _ = (a : G) * (e₀ * (a : G)) := by rw [mul_assoc]
      _ = (a : G) * ((a : G) * e₀) := by rw [h]
      _ = ((a : G) * (a : G)) * e₀ := by rw [mul_assoc]
  · intro x hx
    have := sq_on_D D a haa x hx
    rw [← this]
    group
  · intro v
    rw [hcρ]
    exact congrArg (fun f : Vec D ≃ₗ[F3] Vec D => f v) hIc
  · intro v
    rw [hcρ]
    exact congrArg (fun f : Vec D ≃ₗ[F3] Vec D => f v) hJc

end Step2

end CFSG.RankThree.PartTwo.Sec21.Hering2119S
