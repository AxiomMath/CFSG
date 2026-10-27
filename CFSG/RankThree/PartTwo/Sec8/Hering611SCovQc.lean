module

public import CFSG.RankThree.PartTwo.Sec8.Hering611SCovQb
public import CFSG.RankThree.PartTwo.Sec8.Hering611SJ3CovTools
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

variable {P : Type*} [Group P] [Finite P] {σ : MulAut P} {Zh : Subgroup P}

private theorem qc_comm_left {z x y : P} (hz : ∀ g : P, z * g = g * z) :
    (z * x) * y * (z * x)⁻¹ * y⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have hzi : z⁻¹ * y⁻¹ = y⁻¹ * z⁻¹ := Commute.inv_inv (show Commute z y from hz y)
  have hc : z * (x * y * x⁻¹ * y⁻¹) = (x * y * x⁻¹ * y⁻¹) * z := hz _
  calc (z * x) * y * (z * x)⁻¹ * y⁻¹ = z * x * y * x⁻¹ * (z⁻¹ * y⁻¹) := by group
    _ = z * x * y * x⁻¹ * (y⁻¹ * z⁻¹) := by rw [hzi]
    _ = z * (x * y * x⁻¹ * y⁻¹) * z⁻¹ := by group
    _ = (x * y * x⁻¹ * y⁻¹) * z * z⁻¹ := by rw [hc]
    _ = x * y * x⁻¹ * y⁻¹ := by group

private theorem qc_comm_right {z x y : P} (hz : ∀ g : P, z * g = g * z) :
    x * (z * y) * x⁻¹ * (z * y)⁻¹ = x * y * x⁻¹ * y⁻¹ := by
  have hxz : x * z = z * x := (hz x).symm
  have hc : z * (x * y * x⁻¹ * y⁻¹) = (x * y * x⁻¹ * y⁻¹) * z := hz _
  calc x * (z * y) * x⁻¹ * (z * y)⁻¹ = (x * z) * y * x⁻¹ * y⁻¹ * z⁻¹ := by group
    _ = (z * x) * y * x⁻¹ * y⁻¹ * z⁻¹ := by rw [hxz]
    _ = z * (x * y * x⁻¹ * y⁻¹) * z⁻¹ := by group
    _ = (x * y * x⁻¹ * y⁻¹) * z * z⁻¹ := by rw [hc]
    _ = x * y * x⁻¹ * y⁻¹ := by group

private theorem qc_comm_both {z z' x y : P} (hz : ∀ g : P, z * g = g * z)
    (hz' : ∀ g : P, z' * g = g * z') :
    (z * x) * (z' * y) * (z * x)⁻¹ * (z' * y)⁻¹ = x * y * x⁻¹ * y⁻¹ :=
  (qc_comm_right (x := z * x) (y := y) hz').trans (qc_comm_left (x := x) (y := y) hz)

private theorem qc_exists_gen (h : CoverP P σ Zh) :
    ∃ u v : P, ∀ p : P, ∃ a ∈ Subgroup.closure ({u, v} : Set P), ∃ w ∈ covW Zh h.central,
      p = a * w := by
  haveI hWn : (covW Zh h.central).Normal := ⟨fun n hn g => conj_mem_covW h hn g⟩
  have hQ : Nat.card (P ⧸ covW Zh h.central) = 9 := by
    have h1 := Subgroup.card_mul_index (covW Zh h.central)
    rw [covW_card h, h.card_P] at h1
    show (covW Zh h.central).index = 9
    omega
  have hexp : ∀ q : P ⧸ covW Zh h.central, q ^ 3 = 1 := by
    intro q
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact pow_three_mem_covW h p
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Nontrivial (P ⧸ covW Zh h.central) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hQ]; norm_num)
  obtain ⟨ub, hub⟩ := exists_ne (1 : P ⧸ covW Zh h.central)
  obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective ub
  have hzc : Nat.card (Subgroup.zpowers (u : P ⧸ covW Zh h.central)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hexp _) hub]
  obtain ⟨vb, hvb⟩ : ∃ q : P ⧸ covW Zh h.central,
      q ∉ Subgroup.zpowers (u : P ⧸ covW Zh h.central) := by
    by_contra hcon
    have htop : Subgroup.zpowers (u : P ⧸ covW Zh h.central) = ⊤ :=
      eq_top_iff.mpr (fun q _ => Classical.byContradiction fun hq => hcon ⟨q, hq⟩)
    have h9 : Nat.card (⊤ : Subgroup (P ⧸ covW Zh h.central)) =
        Nat.card (P ⧸ covW Zh h.central) := Subgroup.card_top
    rw [← htop, hzc, hQ] at h9
    omega
  obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective vb
  have hH : Subgroup.closure ({(u : P ⧸ covW Zh h.central), (v : P ⧸ covW Zh h.central)} :
      Set (P ⧸ covW Zh h.central)) = ⊤ := by
    have hzH : Subgroup.zpowers (u : P ⧸ covW Zh h.central) ≤
        Subgroup.closure ({(u : P ⧸ covW Zh h.central), (v : P ⧸ covW Zh h.central)} :
          Set (P ⧸ covW Zh h.central)) :=
      Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert _ _))
    have hvH : (v : P ⧸ covW Zh h.central) ∈ Subgroup.closure
        ({(u : P ⧸ covW Zh h.central), (v : P ⧸ covW Zh h.central)} :
          Set (P ⧸ covW Zh h.central)) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _))
    generalize Subgroup.closure ({(u : P ⧸ covW Zh h.central), (v : P ⧸ covW Zh h.central)} :
      Set (P ⧸ covW Zh h.central)) = H at hzH hvH ⊢
    have hdvd : Nat.card H ∣ 9 := by
      have := Subgroup.card_subgroup_dvd_card H
      rwa [hQ] at this
    have h3dvd : 3 ∣ Nat.card H := by
      have := Subgroup.card_dvd_of_le hzH
      rwa [hzc] at this
    have hne3 : Nat.card H ≠ 3 := by
      intro h3
      have heq : Subgroup.zpowers (u : P ⧸ covW Zh h.central) = H :=
        Subgroup.eq_of_le_of_card_ge hzH (by omega)
      rw [← heq] at hvH
      exact hvb hvH
    have hH9 : Nat.card H = 9 := by
      have hle9 : Nat.card H ≤ 9 := Nat.le_of_dvd (by norm_num) hdvd
      generalize Nat.card H = n at hle9 hdvd h3dvd hne3 ⊢
      interval_cases n <;> omega
    exact Subgroup.eq_top_of_card_eq H (by rw [hH9, hQ])
  refine ⟨u, v, fun p => ?_⟩
  have hmap : (Subgroup.closure ({u, v} : Set P)).map (QuotientGroup.mk' (covW Zh h.central)) =
      Subgroup.closure ({(u : P ⧸ covW Zh h.central), (v : P ⧸ covW Zh h.central)} :
        Set (P ⧸ covW Zh h.central)) := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  have hp : (p : P ⧸ covW Zh h.central) ∈
      (Subgroup.closure ({u, v} : Set P)).map (QuotientGroup.mk' (covW Zh h.central)) := by
    rw [hmap, hH]
    exact Subgroup.mem_top _
  obtain ⟨a, ha, hpa⟩ := Subgroup.mem_map.mp hp
  refine ⟨a, ha, a⁻¹ * p, ?_, (mul_inv_cancel_left a p).symm⟩
  exact QuotientGroup.eq.mp (hpa : (a : P ⧸ covW Zh h.central) = p)

private theorem qc_commutator_le (h : CoverP P σ Zh) {u v : P}
    (hgen : ∀ p : P, ∃ a ∈ Subgroup.closure ({u, v} : Set P), ∃ w ∈ covW Zh h.central,
      p = a * w) :
    commutator P ≤ Subgroup.zpowers (u * v * u⁻¹ * v⁻¹) := by
  have hcomm := CFSG.AGLEmbedding.KFactProofs.J3Sylow.commutator_mem_zpowers_of_class_two
    (t₁ := u) (t₂ := v)
    (fun x _ y _ g _ => covW_le_center h (commutator_mem_covW h x y) g)
  rw [commutator_def]
  refine Subgroup.commutator_le.mpr ?_
  intro x _ y _
  obtain ⟨a, ha, w, hw, rfl⟩ := hgen x
  obtain ⟨a', ha', w', hw', rfl⟩ := hgen y
  have e : (a * w) * (a' * w') * (a * w)⁻¹ * (a' * w')⁻¹ = a * a' * a⁻¹ * a'⁻¹ := by
    rw [← covW_le_center h hw a, ← covW_le_center h hw' a']
    exact qc_comm_both (fun g => covW_le_center h hw g) (fun g => covW_le_center h hw' g)
  show (a * w) * (a' * w') * (a * w)⁻¹ * (a' * w')⁻¹ ∈ Subgroup.zpowers (u * v * u⁻¹ * v⁻¹)
  rw [e]
  exact hcomm a ha a' ha'

theorem commutator_facts (h : CoverP P σ Zh) :
    Nat.card (commutator P) = 3 ∧ Zh ⊓ commutator P = ⊥ ∧
      covW Zh h.central = Zh ⊔ commutator P := by
  obtain ⟨u, v, hgen⟩ := qc_exists_gen h
  have hcz : ∀ g : P, (u * v * u⁻¹ * v⁻¹) * g = g * (u * v * u⁻¹ * v⁻¹) :=
    fun g => covW_le_center h (commutator_mem_covW h u v) g
  have hc3 : (u * v * u⁻¹ * v⁻¹) ^ 3 = 1 := by
    have h1 : (u * v * u⁻¹ * v⁻¹) ^ 3 = u ^ 3 * v * (u ^ 3)⁻¹ * v⁻¹ :=
      (show Commute u (u * v * u⁻¹ * v⁻¹) from (hcz u).symm).commutatorElement_pow_left 3
    have h2 : u ^ 3 * v * (u ^ 3)⁻¹ * v⁻¹ = 1 := by
      rw [covW_le_center h (pow_three_mem_covW h u) v]
      group
    rw [h1]
    exact h2
  have hle := qc_commutator_le h hgen
  have hdvd : Nat.card (commutator P) ∣ 3 := by
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Nat.card_zpowers] at h1
    exact h1.trans (orderOf_dvd_of_pow_eq_one hc3)
  obtain ⟨x, y, hxy⟩ := h.nonab
  have hmem : x * y * x⁻¹ * y⁻¹ ∈ commutator P :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
  have hcard3 : Nat.card (commutator P) = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · exfalso
      have hbot : commutator P = ⊥ := Subgroup.card_eq_one.mp h1
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hxy (by rw [hmem]; exact Zh.one_mem)
    · exact h1
  have hZP : Zh ⊓ commutator P = ⊥ := by
    have hZc := h.card_Z
    have hKdvd : Nat.card (Zh ⊓ commutator P : Subgroup P) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : Zh ⊓ commutator P ≤ Zh)
      rwa [hZc] at this
    rcases (Nat.dvd_prime Nat.prime_three).mp hKdvd with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have e1 : Zh ⊓ commutator P = Zh :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
      have e2 : Zh ⊓ commutator P = commutator P :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
      have hPZ : commutator P = Zh := e2.symm.trans e1
      rw [hPZ] at hmem
      exact hxy hmem
  have hPW : commutator P ≤ covW Zh h.central := by
    rw [commutator_def]
    exact Subgroup.commutator_le.mpr (fun x _ y _ => commutator_mem_covW h x y)
  have hsupW : Zh ⊔ commutator P ≤ covW Zh h.central := sup_le (Zh_le_covW h) hPW
  haveI : Zh.Normal := Subgroup.normal_of_le_center h.central
  have hnorm : commutator P ≤ Subgroup.normalizer (Zh : Set P) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hcardsup : Nat.card (Zh ⊔ commutator P : Subgroup P) = 9 := by
    rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer Zh (commutator P)
      hnorm (disjoint_iff.mpr hZP), h.card_Z, hcard3]
  have hcov : Zh ⊔ commutator P = covW Zh h.central :=
    Subgroup.eq_of_le_of_card_ge hsupW (le_of_eq (by rw [covW_card h, hcardsup]))
  exact ⟨hcard3, hZP, hcov.symm⟩

end CFSG.RankThree.PartTwo.Sec8.Hering611
