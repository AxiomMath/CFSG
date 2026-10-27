module

public import CFSG.RankThree.GF2n.Tim78S3Conj

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG.CGT.Timmesfeld75 CFSG.Open

variable {G : Type} [Group G] [Finite G]

namespace NCPair

variable {U V : Subgroup G} (P : NCPair U V) (hCen : BenderCenterInput)
  (hU : UnitaryTwoGenerationInput)

section Swap

variable {y a x : G} (hy2 : y * y = 1) (hy1 : y ≠ 1) (hyV : conjSubgroup y U = V)
  (hya : y ∈ PartTwo.omegaOneSub (conjSubgroup a U)) (hx : x ∈ U ⊔ V)
  (hyC : conjSubgroup y (conjSubgroup x U) = conjSubgroup x U)

include hy2 hyV in
omit [Finite G] in
theorem conj_V_of_swap : conjSubgroup y V = U := by
  rw [← hyV, ← conjSubgroup_mul, hy2, conjSubgroup_one]

include P hy2 hyV in
omit [Finite G] in
theorem conj_omega_of_swap {u : G} :
    (u ∈ PartTwo.omegaOneSub U → y * u * y⁻¹ ∈ PartTwo.omegaOneSub V) ∧
      (u ∈ PartTwo.omegaOneSub V → y * u * y⁻¹ ∈ PartTwo.omegaOneSub U) := by
  have hmem : ∀ {W W' : Subgroup G}, (∀ x ∈ W, ∀ z ∈ W, x * z = z * x) →
      conjSubgroup y W = W' → u ∈ PartTwo.omegaOneSub W → y * u * y⁻¹ ∈ PartTwo.omegaOneSub W' := by
    intro W W' hWc hW hu
    rw [← hW, omegaOneSub_conj hWc, mem_conjSubgroup,
      show y⁻¹ * (y * u * y⁻¹) * y = u by group]
    exact hu
  exact ⟨hmem P.setup.comm hyV, hmem P.setup.comm₁ (conj_V_of_swap hy2 hyV)⟩

include P hCen hU hy2 hyV in
theorem conj_N_of_swap {n : G} (hn : n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) :
    y * n * y⁻¹ ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V := by
  obtain ⟨u, hu, v, hv, rfl⟩ := P.exists_mul hCen hU hn
  rw [show y * (u * v) * y⁻¹ = (y * v * y⁻¹) * (y * u * y⁻¹) by
    rw [show y * (u * v) * y⁻¹ = (y * u * y⁻¹) * (y * v * y⁻¹) by group]
    exact P.comm_N hCen hU
      (Subgroup.mem_sup_right ((P.conj_omega_of_swap hy2 hyV).1 hu))
      (Subgroup.mem_sup_left ((P.conj_omega_of_swap hy2 hyV).2 hv))]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ((P.conj_omega_of_swap hy2 hyV).2 hv))
    (Subgroup.mem_sup_right ((P.conj_omega_of_swap hy2 hyV).1 hu))

include P hCen hU hy1 hya hyC in
theorem comm_omega_of_swap {c : G} (hc : c ∈ PartTwo.omegaOneSub (conjSubgroup x U)) :
    y * c = c * y := by
  have hAc := Tim78.comm_conj P.setup.comm a
  obtain ⟨u, huU, hu2⟩ := P.setup.exp_ne
  have T : Setup210 (conjSubgroup a U) (conjSubgroup x U) :=
    { comm := hAc
      two := P.setup.two.map (MulAut.conj a).toMonoidHom
      exp_ne := ⟨a * u * a⁻¹, by
          rw [mem_conjSubgroup, show a⁻¹ * (a * u * a⁻¹) * a = u by group]
          exact huU, fun h => hu2 (by
          rw [conj_pow] at h
          calc u ^ 2 = a⁻¹ * (a * u ^ 2 * a⁻¹) * a := by group
            _ = 1 := by rw [h]; group)⟩
      ti := isTI_conjSubgroup P.setup.ti a
      conj := ⟨x * a⁻¹, by rw [← conjSubgroup_mul, inv_mul_cancel_right]⟩
      ne_bot := by
        intro hbot
        have hyN : y ∈ conjSubgroup a U ⊓ Subgroup.normalizer (conjSubgroup x U : Set G) :=
          Subgroup.mem_inf.mpr ⟨PartTwo.omegaOneSub_le _ hya, conjSubgroup_eq_self_iff.mp hyC⟩
        rw [hbot, Subgroup.mem_bot] at hyN
        exact hy1 hyN }
  exact (tim78_2_10_a hCen hU T).1 y hya c hc

include P hCen hU hy2 hy1 hyV hya hx hyC in
theorem mem_omega_of_swap {n : G} (hn : n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V)
    (hc : y * n = n * y) : n ∈ PartTwo.omegaOneSub (conjSubgroup x U) := by
  classical
  set N := PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V with hN
  set K : Subgroup G := N ⊓ Subgroup.centralizer ({y} : Set G) with hK
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hCK : PartTwo.omegaOneSub (conjSubgroup x U) ≤ K := fun c hc' =>
    Subgroup.mem_inf.mpr ⟨P.omega_conj_le_N hCen hU hx hc',
      Subgroup.mem_centralizer_singleton_iff.mpr
        (P.comm_omega_of_swap hCen hU hy1 hya hyC hc').symm⟩
  have hUV : U ⊓ V = ⊥ := P.setup.inf_eq_bot P.ne
  have hsurj : ∀ k ∈ K, ∃ u ∈ PartTwo.omegaOneSub U, k = u * (y * u * y⁻¹) := by
    intro k hk
    obtain ⟨hkN, hkC⟩ := Subgroup.mem_inf.mp hk
    rw [Subgroup.mem_centralizer_singleton_iff] at hkC
    obtain ⟨u, hu, v, hv, rfl⟩ := P.exists_mul hCen hU hkN
    have hu' := (P.conj_omega_of_swap hy2 hyV).1 hu
    have hv' := (P.conj_omega_of_swap hy2 hyV).2 hv
    have he : u * v = (y * v * y⁻¹) * (y * u * y⁻¹) := by
      calc u * v = (u * v * y) * y⁻¹ := by group
        _ = y * (u * v) * y⁻¹ := by rw [hkC]
        _ = (y * u * y⁻¹) * (y * v * y⁻¹) := by group
        _ = (y * v * y⁻¹) * (y * u * y⁻¹) := P.comm_N hCen hU (Subgroup.mem_sup_right hu')
            (Subgroup.mem_sup_left hv')
    have hw : (y * v * y⁻¹)⁻¹ * u ∈ U ⊓ V := by
      refine Subgroup.mem_inf.mpr ⟨U.mul_mem (U.inv_mem (PartTwo.omegaOneSub_le _ hv'))
        (PartTwo.omegaOneSub_le _ hu), ?_⟩
      have : (y * v * y⁻¹)⁻¹ * u = (y * u * y⁻¹) * v⁻¹ := by
        calc (y * v * y⁻¹)⁻¹ * u = (y * v * y⁻¹)⁻¹ * (u * v) * v⁻¹ := by group
          _ = (y * v * y⁻¹)⁻¹ * ((y * v * y⁻¹) * (y * u * y⁻¹)) * v⁻¹ := by rw [he]
          _ = (y * u * y⁻¹) * v⁻¹ := by group
      rw [this]
      exact V.mul_mem (PartTwo.omegaOneSub_le _ hu') (V.inv_mem (PartTwo.omegaOneSub_le _ hv))
    rw [hUV, Subgroup.mem_bot, inv_mul_eq_one] at hw
    refine ⟨u, hu, ?_⟩
    have hvu : v = y * u * y⁻¹ := by
      calc v = y⁻¹ * (y * v * y⁻¹) * y := by group
        _ = y⁻¹ * u * y := by rw [hw]
        _ = y * u * y⁻¹ := by rw [hyinv]
    rw [hvu]
  have hcard : Nat.card K ≤ Nat.card (PartTwo.omegaOneSub U) := by
    let f : ↥(PartTwo.omegaOneSub U) → ↥K := fun u => ⟨(u : G) * (y * u * y⁻¹), by
      refine Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ (Subgroup.mem_sup_left u.2)
        (Subgroup.mem_sup_right ((P.conj_omega_of_swap hy2 hyV).1 u.2)), ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := P.comm_N hCen hU (Subgroup.mem_sup_left u.2)
        (Subgroup.mem_sup_right ((P.conj_omega_of_swap hy2 hyV).1 u.2))
      calc (u : G) * (y * u * y⁻¹) * y = (y * u * y⁻¹) * u * y := by rw [h1]
        _ = y * ((u : G) * (y * u * y⁻¹)) := by rw [hyinv]; group⟩
    refine Nat.card_le_card_of_surjective f fun k => ?_
    obtain ⟨u, hu, hk⟩ := hsurj k k.2
    exact ⟨⟨u, hu⟩, Subtype.ext hk.symm⟩
  have hKeq : PartTwo.omegaOneSub (conjSubgroup x U) = K := by
    refine Subgroup.eq_of_le_of_card_ge hCK ?_
    rw [omegaOneSub_conj P.setup.comm, card_conjSubgroup]
    exact hcard
  rw [hKeq]
  exact Subgroup.mem_inf.mpr ⟨hn, Subgroup.mem_centralizer_singleton_iff.mpr hc.symm⟩

include P hCen hU hy2 hy1 hyV hya hx hyC in
theorem commutator_mem_omega_of_swap {n : G}
    (hn : n ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V) :
    y * n * y⁻¹ * n⁻¹ ∈ PartTwo.omegaOneSub (conjSubgroup x U) := by
  have hyn := P.conj_N_of_swap hCen hU hy2 hyV hn
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have ht : y * n * y⁻¹ * n⁻¹ ∈ PartTwo.omegaOneSub U ⊔ PartTwo.omegaOneSub V :=
    Subgroup.mul_mem _ hyn (Subgroup.inv_mem _ hn)
  refine P.mem_omega_of_swap hCen hU hy2 hy1 hyV hya hx hyC ht ?_
  have hnn : n⁻¹ = n := inv_eq_of_mul_eq_one_right (P.sq_N hCen hU hn)
  have hc := P.comm_N hCen hU hyn hn
  rw [hyinv] at hc ⊢
  rw [hnn]
  calc y * (y * n * y * n) = (y * y) * n * y * n := by group
    _ = n * y * n := by rw [hy2, one_mul]
    _ = n * (y * n * y) * y := by
        rw [show n * (y * n * y) * y = n * y * n * (y * y) by group, hy2, mul_one]
    _ = (y * n * y) * n * y := by rw [← hc]
    _ = y * n * y * n * y := by group

end Swap

end NCPair

end CFSG.RankThree.GF2n.Tim78
