module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528URows

public section

namespace CFSG.Quasithin.H13.Sp4E

open CFSG.Assembly.LowTwoRank CFSG.Quasithin

variable {F : Type} [Field F]

theorem statedScalars_subgroupOf_statedSp_eq_bot [CharP F 2] :
    (StatedScalars (Fin 2 ⊕ Fin 2) F).subgroupOf (StatedSp 2 F) = ⊥ :=
  CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot

theorem isPSp4_top [Finite F] {m : ℕ} (hm : 2 ≤ m) (hF : Nat.card F = 2 ^ m) :
    IsPSp4 2 m ↥(⊤ : Subgroup ↥(StatedSp 2 F)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite F
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := m) (by rw [← Nat.card_eq_fintype_card]; exact hF)
  have h4 : 4 ≤ 2 ^ m :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_⟩, F, inferInstance, inferInstance, hF, ⟨?_⟩⟩
  · intro h
    have h2 : 2 ^ m = 2 := congrArg Prod.snd h
    omega
  · exact Subgroup.topEquiv.trans ((QuotientGroup.quotientMulEquivOfEq
      statedScalars_subgroupOf_statedSp_eq_bot).trans QuotientGroup.quotientBot).symm

theorem card_le_of_normal_sp4 [Finite F] {m : ℕ} (hm : 2 ≤ m) (hF : Nat.card F = 2 ^ m)
    {P : Subgroup ↥(StatedSp 2 F)} (hP : IsMaxParabolic2 ⊤ P) {N : Subgroup ↥(perfectCore P)}
    (hN : N.Normal) (hN2 : IsPGroup 2 N) : Nat.card N ≤ 2 ^ (3 * m) := by
  have := Fintype.ofFinite F
  obtain ⟨a, -, ha4, h1, -⟩ := card_perfectCore_of_classical hm (Or.inr (isPSp4_top hm hF)) hP
  rw [ha4 (isPSp4_top hm hF)] at h1
  have hle : N ≤ CFSG.pCore 2 ↥(perfectCore P) := le_sSup ⟨hN, hN2⟩
  have := Subgroup.card_le_of_le hle
  rw [h1] at this
  exact this

variable {G : Type} [Group G]

theorem card_le_card_inf_centralizer_mul [Finite G] {Q : Subgroup G}
    (hQQ : ⁅Q, Q⁆ ≤ centerOf Q) {x : G} (hx : x ∈ Q) :
    Nat.card Q ≤ Nat.card ↥(Q ⊓ Subgroup.centralizer ({x} : Set G)) * Nat.card (centerOf Q) := by
  have hc : ∀ y ∈ Q, x * y * x⁻¹ * y⁻¹ ∈ centerOf Q := fun y hy => by
    have := hQQ (Subgroup.commutator_mem_commutator hx hy)
    rwa [commutatorElement_def] at this
  let f : ↥Q →* ↥(centerOf Q) :=
    { toFun := fun y => ⟨x * y * x⁻¹ * (y : G)⁻¹, hc y y.2⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, _root_.mul_inv_rev]
        have hz := hc b b.2
        have hcomm : (a : G) * (x * b * x⁻¹ * (b : G)⁻¹) = (x * b * x⁻¹ * (b : G)⁻¹) * a :=
          (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 a a.2)
        calc x * (a * b) * x⁻¹ * ((b : G)⁻¹ * (a : G)⁻¹)
            = x * a * x⁻¹ * ((a : G)⁻¹ * ((a : G) * (x * b * x⁻¹ * (b : G)⁻¹)) * (a : G)⁻¹) := by
              group
          _ = x * a * x⁻¹ * ((a : G)⁻¹ * ((x * b * x⁻¹ * (b : G)⁻¹) * a) * (a : G)⁻¹) := by
              rw [hcomm]
          _ = x * a * x⁻¹ * (a : G)⁻¹ * (x * b * x⁻¹ * (b : G)⁻¹) := by group }
  have hker : f.ker = (Subgroup.centralizer ({x} : Set G)).subgroupOf Q := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : x * y * x⁻¹ * (y : G)⁻¹ = 1 := congrArg Subtype.val h
      have h2 : x * (y : G) = y * x := by
        calc x * (y : G) = (x * y * x⁻¹ * (y : G)⁻¹) * y * x := by group
          _ = y * x := by rw [h1, one_mul]
      exact h2.symm
    · intro h
      apply Subtype.ext
      show x * y * x⁻¹ * (y : G)⁻¹ = 1
      rw [← h]
      group
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hker,
    show Nat.card ↥((Subgroup.centralizer ({x} : Set G)).subgroupOf Q) =
      Nat.card ↥(Q ⊓ Subgroup.centralizer ({x} : Set G)) by
      rw [← Subgroup.card_map_of_injective Q.subtype_injective, Subgroup.subgroupOf_map_subtype,
        inf_comm]] at h1
  rw [h1, mul_comm]
  exact Nat.mul_le_mul_left _ (Subgroup.card_le_of_le le_top |>.trans_eq Subgroup.card_top)

theorem false_of_mem_centralizer_ext [Finite G] {K Q : Subgroup G} {m : ℕ} (hm : 2 ≤ m)
    (hQK : Q ≤ K) (hKQ : K ≤ Subgroup.normalizer (Q : Set G)) (hQ2 : IsPGroup 2 Q)
    (hQQ : ⁅Q, Q⁆ ≤ centerOf Q) (hZ : Nat.card (centerOf Q) = 2 ^ m)
    (hQc : Nat.card Q = (2 ^ m) ^ 5) {t q₀ : G} (hq₀ : q₀ ∈ Q)
    (hz : ∀ y ∈ Q, (t * q₀) * y * (t * q₀)⁻¹ = y) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = 2 ^ m) {P : Subgroup ↥(StatedSp 2 F)} (hP : IsMaxParabolic2 ⊤ P)
    (ι : ↥(K ⊓ Subgroup.centralizer ({t} : Set G)) ≃* ↥(perfectCore P)) : False := by
  set C := Subgroup.centralizer ({t} : Set G) with hC
  have hle : Q ⊓ Subgroup.centralizer ({q₀} : Set G) ≤ Q ⊓ C := by
    intro y hy
    obtain ⟨hyQ, hyc⟩ := Subgroup.mem_inf.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hyc
    refine Subgroup.mem_inf.mpr ⟨hyQ, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := hz y hyQ
    have h2 : t * y * t⁻¹ = y := by
      calc t * y * t⁻¹ = (t * q₀) * (q₀⁻¹ * y * q₀) * (t * q₀)⁻¹ := by group
        _ = (t * q₀) * y * (t * q₀)⁻¹ := by
            rw [show q₀⁻¹ * y * q₀ = y by rw [mul_assoc, hyc, ← mul_assoc, inv_mul_cancel, one_mul]]
        _ = y := h1
    calc y * t = (t * y * t⁻¹)⁻¹⁻¹ * t := by rw [h2, inv_inv]
      _ = t * y := by group
  have hQCK : Q ⊓ C ≤ K ⊓ C := inf_le_inf_right _ hQK
  set N := (Q ⊓ C).subgroupOf (K ⊓ C) with hN
  have hNn : N.Normal := by
    rw [hN, Subgroup.normal_subgroupOf_iff_le_normalizer hQCK]
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro y
    obtain ⟨hkK, hkC⟩ := Subgroup.mem_inf.mp hk
    have hkQ := Subgroup.mem_normalizer_iff.mp (hKQ hkK) y
    have hkC' := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hkC) y
    simp only [Subgroup.mem_inf]
    exact ⟨fun h => ⟨hkQ.mp h.1, hkC'.mp h.2⟩, fun h => ⟨hkQ.mpr h.1, hkC'.mpr h.2⟩⟩
  have hN2 : IsPGroup 2 N := by
    have : IsPGroup 2 ↥(Q ⊓ C) := hQ2.to_le inf_le_left
    exact this.of_equiv (Subgroup.subgroupOfEquivOfLe hQCK).symm
  have hNmap := card_le_of_normal_sp4 hm hF hP (hNn.map ι.toMonoidHom ι.surjective)
    (hN2.map ι.toMonoidHom)
  have hcardN : Nat.card N = Nat.card ↥(Q ⊓ C) := by
    rw [hN, ← Subgroup.card_map_of_injective (K ⊓ C).subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQCK]
  rw [Subgroup.card_map_of_injective ι.injective, hcardN] at hNmap
  have h1 := card_le_card_inf_centralizer_mul hQQ hq₀
  have h2 := Subgroup.card_le_of_le hle
  rw [hZ, hQc] at h1
  have h3 : (2 ^ m) ^ 5 ≤ 2 ^ (3 * m) * 2 ^ m := h1.trans (Nat.mul_le_mul_right _ (h2.trans hNmap))
  rw [← pow_mul, ← pow_add] at h3
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h3
  omega

end CFSG.Quasithin.H13.Sp4E
