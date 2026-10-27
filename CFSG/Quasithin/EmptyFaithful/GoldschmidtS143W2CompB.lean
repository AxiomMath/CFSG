module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2CompA

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
  CFSG.QuasithinUnique.Tight CFSG.QuasithinUnique.BenderBranch
  CFSG.ComponentClassification.AschbacherTightEmbedding

namespace S143

namespace InspW2

theorem fusionOddCore_eq_pPrimeCore (X : Type*) [Group X] :
    fusionOddCore X = CFSG.pPrimeCore 2 X := by
  unfold fusionOddCore CFSG.pPrimeCore
  congr 1
  ext N
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

theorem oddCoreIn_eq_map {G : Type*} [Group G] (H : Subgroup G) :
    oddCoreIn H = (CFSG.pPrimeCore 2 ↥H).map H.subtype := by
  unfold oddCoreIn
  rw [fusionOddCore_eq_pPrimeCore]

section OddCore

variable {G : Type*} [Group G] [Finite G] {H : Subgroup G}

theorem odd_orderOf_of_mem_oddCoreIn {y : G} (hy : y ∈ oddCoreIn H) : Odd (orderOf y) := by
  rw [oddCoreIn_eq_map] at hy
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
  have hodd : Odd (Nat.card (CFSG.pPrimeCore 2 ↥H)) :=
    Nat.coprime_two_left.mp CFSG.pPrimeCore_coprime_card
  have hdvd : orderOf (⟨y', hy'⟩ : CFSG.pPrimeCore 2 ↥H) ∣ Nat.card (CFSG.pPrimeCore 2 ↥H) :=
    orderOf_dvd_natCard _
  have h1 : orderOf y' = orderOf (⟨y', hy'⟩ : CFSG.pPrimeCore 2 ↥H) :=
    (Subgroup.orderOf_mk _ _).symm
  have h2 : orderOf ((y' : ↥H) : G) = orderOf y' := Subgroup.orderOf_coe y'
  rw [Subgroup.coe_subtype, h2, h1]
  exact hodd.of_dvd_nat hdvd

omit [Finite G] in
theorem conj_mem_oddCoreIn {u y : G} (hu : u ∈ H) (hy : y ∈ oddCoreIn H) :
    u * y * u⁻¹ ∈ oddCoreIn H := by
  rw [oddCoreIn_eq_map] at hy ⊢
  obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
  refine Subgroup.mem_map.mpr ⟨⟨u, hu⟩ * y' * ⟨u, hu⟩⁻¹, ?_, rfl⟩
  exact (inferInstance : (CFSG.pPrimeCore 2 ↥H).Normal).conj_mem _ hy' _

end OddCore

section Gw

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} {A : Subgroup G} {t d x : G}

theorem oddCore_Gw (h : Ctx T M g A t d x) : oddCoreIn (Gw d x) = ⊥ := by
  have hH := lemma115Hyp_Gw h
  have hinv := hH.inverts_oddCoreIn
  obtain ⟨a, ha, -, -, -, -, hxa, -⟩ := three_cycle_x h.c h.hD h.hd4 h.hx h.hx3
  have hx := h.x_mem_Gw
  rw [eq_bot_iff]
  intro y hy
  rw [Subgroup.mem_bot]
  have hy1 : x⁻¹ * y * x ∈ oddCoreIn (Gw d x) := by
    have := conj_mem_oddCoreIn ((Gw d x).inv_mem hx) hy
    simpa using this
  have ha_inv : ∀ v ∈ oddCoreIn (Gw d x), a⁻¹ * v * a = v⁻¹ := by
    intro v hv
    have hv1 : x⁻¹ * v * x ∈ oddCoreIn (Gw d x) := by
      have := conj_mem_oddCoreIn ((Gw d x).inv_mem hx) hv
      simpa using this
    have h0 := hinv _ hv1
    have e : a⁻¹ * v * a = x * ((d * d)⁻¹ * (x⁻¹ * v * x) * (d * d)) * x⁻¹ := by
      rw [ha]; group
    rw [e, h0]; group
  have hb : x * a * x⁻¹ = (d * d) * a := hxa
  have hza_inv : ((d * d) * a)⁻¹ * y * ((d * d) * a) = y⁻¹ := by
    have h0 := ha_inv _ hy1
    have e : ((d * d) * a)⁻¹ * y * ((d * d) * a) =
        x * (a⁻¹ * (x⁻¹ * y * x) * a) * x⁻¹ := by
      rw [← hb]; group
    rw [e, h0]; group
  have hza_cen : ((d * d) * a)⁻¹ * y * ((d * d) * a) = y := by
    have e : ((d * d) * a)⁻¹ * y * ((d * d) * a) = a⁻¹ * ((d * d)⁻¹ * y * (d * d)) * a := by
      group
    rw [e, hinv y hy, ha_inv _ (by simpa using (oddCoreIn (Gw d x)).inv_mem hy)]
    group
  have hyy : y = y⁻¹ := hza_cen.symm.trans hza_inv
  have hsq : orderOf y ∣ 2 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [pow_two]
    nth_rewrite 1 [hyy]
    exact inv_mul_cancel y
  have hodd := odd_orderOf_of_mem_oddCoreIn hy
  have : orderOf y = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hsq with h1 | h1
    · exact h1
    · rw [h1] at hodd; exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.mp this

end Gw

end InspW2

end S143

end CFSG.Quasithin
