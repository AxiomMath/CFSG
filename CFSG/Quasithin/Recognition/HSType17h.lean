module

public import CFSG.Quasithin.Recognition.HSType17g
public import CFSG.Quasithin.Recognition.HSType17b
public import CFSG.Quasithin.Recognition.HSType17e
public import CFSG.Quasithin.Recognition.HSType17f

public section

namespace CFSG.Quasithin.HSType

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.GorensteinWalter CFSG.Quasithin.I4

section General

variable {G : Type} [Group G]

theorem nat_card_centralizer_conj (g t : G) :
    Nat.card (Subgroup.centralizer ({g * t * g⁻¹} : Set G)) =
      Nat.card (Subgroup.centralizer ({t} : Set G)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨g⁻¹ * x * g, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      invFun := fun x => ⟨g * x * g⁻¹, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      left_inv := fun x => Subtype.ext (by simp [mul_assoc])
      right_inv := fun x => Subtype.ext (by simp [mul_assoc]) }
  · have hx := Subgroup.mem_centralizer_singleton_iff.mp x.2
    calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hx]
      _ = t * (g⁻¹ * x * g) := by group
  · have hx := Subgroup.mem_centralizer_singleton_iff.mp x.2
    calc g * x * g⁻¹ * (g * t * g⁻¹) = g * (x * t) * g⁻¹ := by group
      _ = g * (t * x) * g⁻¹ := by rw [hx]
      _ = g * t * g⁻¹ * (g * x * g⁻¹) := by group

theorem exists_conj_mem_of_odd_index {X : Type*} [Group X] [Finite X] {P : Subgroup X}
    (hP : IsPGroup 2 P) (hodd : ¬ 2 ∣ P.index) {u : X} (hu : u * u = 1) :
    ∃ x : X, x * u * x⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hup : IsPGroup 2 (Subgroup.zpowers u) := by
    have hdvd : orderOf u ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one, sq]; exact hu)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  obtain ⟨S, hS⟩ := hup.exists_le_sylow
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq X S (hP.toSylow hodd)
  refine ⟨x, ?_⟩
  have hmem : x * u * x⁻¹ ∈ x • S := by
    rw [HSSetting.mem_smul_sylow', show x⁻¹ * (x * u * x⁻¹) * x = u by group]
    exact hS (Subgroup.mem_zpowers u)
  rw [hx] at hmem
  exact hmem

theorem card_opResidual_le_360
    [Finite G] {C T D : Subgroup G} {z : G} (hTC : T ≤ C) (hodd : ¬ 2 ∣ T.relIndex C)
    (hzT : ∀ x ∈ T, x * z = z * x) (hCz : ∀ x ∈ C, x * z = z * x → x ∈ T)
    (hD : opResidual 2 C ⊓ T = D) (eD : ↥D ≃* DihedralGroup 4) (hzD : z ∈ D)
    (hz : orderOf z = 2) (hinvD : ∀ d ∈ D, d * d = 1 → d ≠ 1 → ∃ g ∈ C, g * z * g⁻¹ = d) :
    Nat.card (opResidual 2 C) ≤ 360 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := opResidual 2 C with hX
  have hXC : X ≤ C := opResidual_le 2 C
  have hTnorm : T ≤ Subgroup.normalizer (X : Set G) := le_normalizer_opResidual hTC
  have hXT : X ⊔ T = C := opResidual_sup_eq hTC hodd
  have hDX : D ≤ X := by rw [← hD]; exact inf_le_left
  have hDT : D ≤ T := by rw [← hD]; exact inf_le_right
  have hprod : Nat.card C * Nat.card D = Nat.card X * Nat.card T := by
    have := card_sup_mul_card_inf_of_le_normalizer hTnorm
    rw [sup_comm, hXT, inf_comm, hD] at this
    rw [this, mul_comm]
  have hDodd : ¬ 2 ∣ (D.subgroupOf X).index := by
    have h1 := (D.subgroupOf X).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDX).toEquiv] at h1
    have h2 := (T.subgroupOf C).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTC).toEquiv] at h2
    have hD8 : Nat.card D = 8 := by rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
    have hTpos : 0 < Nat.card T := Nat.card_pos
    have : (D.subgroupOf X).index = T.relIndex C := by
      change (D.subgroupOf X).index = (T.subgroupOf C).index
      rw [hD8] at h1 hprod
      have e : Nat.card T * (8 * (D.subgroupOf X).index) =
          Nat.card T * (8 * (T.subgroupOf C).index) := by
        calc Nat.card T * (8 * (D.subgroupOf X).index) = Nat.card X * Nat.card T := by
              rw [← h1]; ring
          _ = Nat.card C * 8 := hprod.symm
          _ = Nat.card T * (8 * (T.subgroupOf C).index) := by rw [← h2]; ring
      have := Nat.eq_of_mul_eq_mul_left hTpos e
      omega
    rw [this]
    exact hodd
  have hDp : IsPGroup 2 (D.subgroupOf X) := by
    refine IsPGroup.of_card (n := 3) ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDX).toEquiv, Nat.card_congr eD.toEquiv,
      DihedralGroup.nat_card]
    norm_num
  set z' : ↥X := ⟨z, hDX hzD⟩ with hz'
  have hz'2 : orderOf z' = 2 := by rw [← Subgroup.orderOf_coe]; exact hz
  have hcen : ∀ x : ↥X, x ∈ Subgroup.centralizer ({z'} : Set ↥X) ↔ (x : G) ∈ D := by
    intro x
    rw [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hx
      have hxz : (x : G) * z = z * x := by
        have := congrArg Subtype.val hx
        simpa using this
      rw [← hD]
      exact ⟨x.2, hCz _ (hXC x.2) hxz⟩
    · intro hx
      exact Subtype.ext (hzT _ (hDT hx))
  let f : ↥(Subgroup.centralizer ({z'} : Set ↥X)) →* ↥D :=
    { toFun := fun x => ⟨((x : ↥X) : G), (hcen x).mp x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hf : Function.Bijective f := by
    refine ⟨fun a b hab => ?_, fun d => ?_⟩
    · have hab' := congrArg (fun w : ↥D => (w : G)) hab
      exact Subtype.ext (Subtype.ext hab')
    · exact ⟨⟨⟨d, hDX d.2⟩, (hcen ⟨d, hDX d.2⟩).mpr d.2⟩, rfl⟩
  have hC : Nonempty (Subgroup.centralizer ({z'} : Set ↥X) ≃* DihedralGroup (2 ^ 2)) :=
    ⟨(MulEquiv.ofBijective f hf).trans eD⟩
  have hconj : ∀ u : ↥X, orderOf u = 2 → IsConj z' u := by
    intro u hu
    have huu : u * u = 1 := by rw [← sq, ← hu]; exact pow_orderOf_eq_one u
    have hu1 : u ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hu; exact absurd hu (by norm_num)
    obtain ⟨x, hx⟩ := exists_conj_mem_of_odd_index hDp hDodd huu
    rw [Subgroup.mem_subgroupOf] at hx
    set d := ((x * u * x⁻¹ : ↥X) : G) with hd
    have hdd : d * d = 1 := by
      rw [hd, ← Subgroup.coe_mul,
        show x * u * x⁻¹ * (x * u * x⁻¹) = x * (u * u) * x⁻¹ by group, huu, mul_one,
        mul_inv_cancel, Subgroup.coe_one]
    have hd1 : d ≠ 1 := by
      intro h1
      apply hu1
      have : x * u * x⁻¹ = 1 := Subtype.ext h1
      calc u = x⁻¹ * (x * u * x⁻¹) * x := by group
        _ = 1 := by rw [this]; group
    obtain ⟨g, hgC, hg⟩ := hinvD d hx hdd hd1
    have hgXT : g ∈ ((X ⊔ T : Subgroup G) : Set G) := by rw [hXT]; exact hgC
    rw [Subgroup.coe_mul_of_right_le_normalizer_left X T hTnorm] at hgXT
    obtain ⟨a, ha, b, hb, rfl⟩ := hgXT
    have hbz : b * z * b⁻¹ = z := by rw [hzT b hb, mul_inv_cancel_right]
    have haz : a * z * a⁻¹ = d := by
      rw [← hg]
      calc a * z * a⁻¹ = a * (b * z * b⁻¹) * a⁻¹ := by rw [hbz]
        _ = a * b * z * (a * b)⁻¹ := by group
    refine isConj_iff.mpr ⟨x⁻¹ * ⟨a, ha⟩, Subtype.ext ?_⟩
    show (x : G)⁻¹ * a * z * ((x : G)⁻¹ * a)⁻¹ = u
    calc (x : G)⁻¹ * a * z * ((x : G)⁻¹ * a)⁻¹ = (x : G)⁻¹ * (a * z * a⁻¹) * x := by group
      _ = (x : G)⁻¹ * ((x : G) * u * (x : G)⁻¹) * x := by
          rw [haz, hd, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      _ = u := by group
  have hinv : ∀ u v : ↥X, orderOf u = 2 → orderOf v = 2 → IsConj u v := fun u v hu hv =>
    (isConj_comm.mp (hconj u hu)).trans (hconj v hv)
  obtain ⟨K, _, _, -, hq, ⟨e⟩⟩ := psl2_of_isConj ↥X hinv hz'2 (k := 2) (by norm_num) hC
  have hqK : Nat.card K = 7 ∨ Nat.card K = 9 := by
    rw [Nat.card_eq_fintype_card]
    norm_num at hq
    omega
  have hpp : IsOddPrimePower (Nat.card K) := by
    rcases hqK with h7 | h9
    · exact ⟨7, 1, by norm_num, by decide, le_refl _, by rw [h7]; norm_num⟩
    · exact ⟨3, 2, by norm_num, by decide, by norm_num, by rw [h9]; norm_num⟩
  have hcard := psl2_card_formula K hpp
  rw [Nat.card_congr e.toEquiv, hcard]
  rcases hqK with h7 | h9
  · rw [h7]; norm_num
  · rw [h9]; norm_num

end General

namespace HSSetting

variable {G : Type} [Group G] {z : G} {V : Subgroup G}

theorem card_centralizer_le_2880
    [Finite G] (h : HSSetting z V)
    (hQ8 : ∀ t : G, t * t = 1 → t ≠ 1 → (∀ g : G, g * z * g⁻¹ ≠ t) →
      ∃ E : Subgroup G, E ≤ Subgroup.centralizer ({t} : Set G) ∧
        Nonempty (↥E ≃* QuaternionGroup 2))
    {t : G} (htK : t ∈ hsK z) (htQ : t ∉ hsQ z) (htt : t * t = 1) :
    Nat.card (Subgroup.centralizer ({t} : Set G)) ≤ 2880 := by
  classical
  obtain ⟨t₁, ht₁K, ht₁Q, ht₁t, ht₁z, A, hAt, ⟨eA⟩, hzA, hAcl,
    ⟨s, hsA, hss, hs1, hsz, hszc, hsK⟩, τ, y, hττ, hτz, hτt, hyt, hyτ, hy3, g, hg⟩ :=
    h.exists_t_data
  suffices hmain : Nat.card (Subgroup.centralizer ({t₁} : Set G)) ≤ 2880 by
    obtain ⟨v, hvQ, hvt⟩ := h.exists_v_of_invol_K ht₁K ht₁Q ht₁t
    obtain ⟨k, -, hk⟩ := h.exists_K_conj_of_invol ht₁K ht₁Q ht₁t hvQ hvt htK htQ htt
    rw [← nat_card_centralizer_conj k t, hk]
    exact hmain
  set C := Subgroup.centralizer ({t₁} : Set G) with hC
  set T := hsH z ⊓ C with hT
  have hsmemH : s ∈ hsH z := Subgroup.mem_centralizer_singleton_iff.mpr hszc
  have hst : s * t₁ = t₁ * s := Subgroup.mem_centralizer_singleton_iff.mp (hAt hsA)
  obtain ⟨φ, -, hker, hφt, hφs⟩ := h.exists_quot_norm ht₁K ht₁Q ht₁t hsmemH hsK hss hst
  have hAX : A ≤ opResidual 2 C := by
    refine hAcl.trans ?_
    rw [Subgroup.closure_le]
    rintro x ⟨hxC, hx3⟩
    refine mem_opResidual_of_coprime hxC ?_
    rw [hx3]
    norm_num
  obtain ⟨D, ⟨eD⟩, hDcard, hDS, hDX, htD, hinvD, hsqD⟩ :=
    h.exists_D ht₁K ht₁Q ht₁t ht₁z hAt eA hzA hAX hsA hss hs1 hsz hszc hsK hker hφt hsmemH hφs
  have hτH : τ ∈ hsH z := Subgroup.mem_centralizer_singleton_iff.mpr hτz
  have hvT : t₁ * τ ∈ T := by
    refine ⟨(hsH z).mul_mem ht₁K.1 hτH, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [mul_assoc, hτt]
  have hvz : IsConj z (t₁ * τ) := isConj_iff.mpr ⟨g, hg⟩
  have hT64 := h.card_centralizer_H_of_invol_K ht₁K ht₁Q ht₁t
  have hvII : ∀ c ∈ C, c * z * c⁻¹ ≠ t₁ * τ := by
    intro c hcC hc
    have hyv : y * (t₁ * τ) = (t₁ * τ) * y := by
      calc y * (t₁ * τ) = (y * t₁) * τ := by group
        _ = (t₁ * y) * τ := by rw [hyt]
        _ = t₁ * (y * τ) := by group
        _ = t₁ * (τ * y) := by rw [hyτ]
        _ = (t₁ * τ) * y := by group
    have hyC : y ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr hyt
    have hmem : c⁻¹ * y * c ∈ T := by
      refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr ?_,
        C.mul_mem (C.mul_mem (C.inv_mem hcC) hyC) hcC⟩
      calc c⁻¹ * y * c * z = c⁻¹ * (y * (c * z * c⁻¹)) * c := by group
        _ = c⁻¹ * (y * (t₁ * τ)) * c := by rw [hc]
        _ = c⁻¹ * ((t₁ * τ) * y) * c := by rw [hyv]
        _ = c⁻¹ * ((c * z * c⁻¹) * y) * c := by rw [hc]
        _ = z * (c⁻¹ * y * c) := by group
    have ho : orderOf (⟨c⁻¹ * y * c, hmem⟩ : ↥T) = 3 := by
      rw [Subgroup.orderOf_mk, show c⁻¹ * y * c = MulAut.conj c⁻¹ y by
        simp, MulEquiv.orderOf_eq, hy3]
    have hdvd := orderOf_dvd_natCard (⟨c⁻¹ * y * c, hmem⟩ : ↥T)
    rw [ho, hT64] at hdvd
    norm_num at hdvd
  have ht₁1 : t₁ ≠ 1 := fun h1 => ht₁Q (h1 ▸ (hsQ z).one_mem)
  obtain ⟨E, hEC, ⟨eE⟩⟩ := hQ8 t₁ ht₁t ht₁1 ht₁z
  obtain ⟨e, heT, heS, he4, hez, he2⟩ :=
    h.exists_e_of_quaternion ht₁K ht₁Q ht₁t ht₁z hker hφt hsmemH hsK hss hst hφs hEC eE
  obtain ⟨hRD, hcardC⟩ := h.inf_T_eq_D ht₁K ht₁Q ht₁t ht₁z hker hφt hsmemH hsK hss hst hφs
    hDcard hDS hDX htD hinvD hvT hvz hvII heT heS he4 hez he2
  have hzD : z ∈ D := by
    have hr : (eD.symm (DihedralGroup.r 1) : G) * (eD.symm (DihedralGroup.r 1) : G) ≠ 1 := by
      intro h1
      have : eD.symm (DihedralGroup.r 1) * eD.symm (DihedralGroup.r 1) = 1 := Subtype.ext h1
      rw [← map_mul, MulEquiv.map_eq_one_iff] at this
      exact absurd this (by decide)
    have := hsqD _ (eD.symm (DihedralGroup.r 1)).2 hr
    rw [← this]
    exact D.mul_mem (eD.symm _).2 (eD.symm _).2
  have hX := card_opResidual_le_360 (C := C) (T := T) (D := D) (z := z) inf_le_right
    (h.not_two_dvd_relIndex_T ht₁K ht₁Q ht₁t ht₁z)
    (fun x hx => Subgroup.mem_centralizer_singleton_iff.mp hx.1)
    (fun x hxC hxz => ⟨Subgroup.mem_centralizer_singleton_iff.mpr hxz, hxC⟩)
    hRD eD hzD h.orderOf_z hinvD
  have hX' : Nat.card (opResidual 2 (Subgroup.centralizer ({t₁} : Set G))) ≤ 360 := hX
  show Nat.card (Subgroup.centralizer ({t₁} : Set G)) ≤ 2880
  rw [hcardC]
  omega

end HSSetting

end CFSG.Quasithin.HSType
