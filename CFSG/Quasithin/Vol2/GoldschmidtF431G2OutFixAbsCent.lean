module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutFixAbs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Basic

section

public section

namespace CFSG.Quasithin.H13.F431.G2

open CFSG.QuasithinUnique

section Syl

variable {G : Type} [Group G] [Finite G]

theorem isSylowTwoOf_of_top {T N : Subgroup G} (hT : IsSylowTwoOf T ⊤) (hTN : T ≤ N) :
    IsSylowTwoOf T N := by
  refine isSylowTwoOf_of_card_eq hTN hT.isPGroup ?_
  refine le_antisymm (card_le_twoPart hTN hT.isPGroup) ?_
  rw [hT.card_eq]
  exact twoPart_mono le_top

theorem card_mul_le_card_mul_inf {Y S T : Subgroup G} (hYT : Y ≤ T) (hST : S ≤ T)
    (hTS : T ≤ Subgroup.normalizer (S : Set G)) :
    Nat.card Y * Nat.card S ≤ Nat.card T * Nat.card ↥(Y ⊓ S) := by
  have h := Lin2.card_sup_mul_card_inf (A := Y) (B := S) (hYT.trans hTS)
  have hsup : Nat.card ↥(Y ⊔ S) ≤ Nat.card T := Subgroup.card_le_of_le (sup_le hYT hST)
  calc Nat.card Y * Nat.card S = Nat.card ↥(Y ⊔ S) * Nat.card ↥(Y ⊓ S) := h.symm
    _ ≤ Nat.card T * Nat.card ↥(Y ⊓ S) := Nat.mul_le_mul_right _ hsup

theorem isSylowTwoOf_centralizer_inf {T N R : Subgroup G} {f : G} (hR : R.Normal)
    (hT : IsSylowTwoOf T ⊤) (hTN : T ≤ N) (hfT : f ∈ T) (hf2 : f ^ 2 = 1) (hfR : f ∉ R)
    (hinv : ∀ f' ∈ T, f' ∉ R → f' ^ 2 = 1 →
      Nat.card ↥(T ⊓ Subgroup.centralizer ({f'} : Set G)) ≤
        Nat.card ↥(T ⊓ Subgroup.centralizer ({f} : Set G))) :
    IsSylowTwoOf (T ⊓ Subgroup.centralizer ({f} : Set G))
      (Subgroup.centralizer ({f} : Set G) ⊓ N) := by
  have hTfM : T ⊓ Subgroup.centralizer ({f} : Set G) ≤ Subgroup.centralizer ({f} : Set G) ⊓ N :=
    fun x hx => ⟨hx.2, hTN hx.1⟩
  have hTf2 : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer ({f} : Set G)) :=
    hT.isPGroup.to_le inf_le_left
  obtain ⟨P, hTfP, hP⟩ := exists_isSylowTwoOf_of_le hTfM hTf2
  have hPN : P ≤ N := hP.le.trans inf_le_right
  have hPC : P ≤ Subgroup.centralizer ({f} : Set G) := hP.le.trans inf_le_left
  obtain ⟨S', hPS', hS'⟩ := exists_isSylowTwoOf_of_le hPN hP.isPGroup
  obtain ⟨h, -, hS'eq⟩ := (isSylowTwoOf_of_top hT hTN).exists_conj hS'
  have hconj : ∀ p ∈ P, h⁻¹ * p * h ∈ T := by
    intro p hp
    have hp' := hPS' hp
    rw [hS'eq] at hp'
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.1 hp'
    simpa [MulAut.conj_apply, mul_assoc] using ht
  have hfC : f ∈ Subgroup.centralizer ({f} : Set G) := Subgroup.mem_centralizer_iff.2
    (fun g hg => by rw [Set.mem_singleton_iff.1 hg])
  have hfP : f ∈ P := hTfP ⟨hfT, hfC⟩
  have hf'T : h⁻¹ * f * h ∈ T := hconj f hfP
  have hf'2 : (h⁻¹ * f * h) ^ 2 = 1 := by
    have : (h⁻¹ * f * h) ^ 2 = h⁻¹ * f ^ 2 * h := by
      rw [pow_two, pow_two]
      group
    rw [this, hf2]
    group
  have hf'R : h⁻¹ * f * h ∉ R := by
    intro hmem
    apply hfR
    have := hR.conj_mem _ hmem h
    simpa [mul_assoc] using this
  have hmem : ∀ p : P, h⁻¹ * p.1 * h ∈ T ⊓ Subgroup.centralizer ({h⁻¹ * f * h} : Set G) := by
    intro p
    refine ⟨hconj p.1 p.2, Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    rw [Set.mem_singleton_iff.1 hg]
    have hpf := Subgroup.mem_centralizer_iff.1 (hPC p.2) f rfl
    calc h⁻¹ * f * h * (h⁻¹ * p.1 * h) = h⁻¹ * (f * p.1) * h := by group
      _ = h⁻¹ * (p.1 * f) * h := by rw [hpf]
      _ = h⁻¹ * p.1 * h * (h⁻¹ * f * h) := by group
  have hcard : Nat.card P ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({f} : Set G)) := by
    calc Nat.card P ≤ Nat.card ↥(T ⊓ Subgroup.centralizer ({h⁻¹ * f * h} : Set G)) := by
          refine Nat.card_le_card_of_injective (fun p => ⟨h⁻¹ * p.1 * h, hmem p⟩) ?_
          intro p q hpq
          have := congrArg Subtype.val hpq
          simp only [mul_left_inj, mul_right_inj] at this
          exact Subtype.ext this
      _ ≤ _ := hinv _ hf'T hf'R hf'2
  have hPeq : P = T ⊓ Subgroup.centralizer ({f} : Set G) :=
    (Subgroup.eq_of_le_of_card_ge hTfP hcard).symm
  rw [← hPeq]
  exact hP

end Syl

end CFSG.Quasithin.H13.F431.G2

end

end

public section

namespace CFSG.Quasithin.H13.F431.G2.OutK

open CFSG.QuasithinUnique

section Cent

variable {X H : Type} [Group X] [Group H] [Finite H] {Φ : X →* H} {ψ : H} {α : MulAut X}

theorem OutProps.inf_centralizer_invol_eq (P : OutProps Φ ψ α) {U : Subgroup X}
    (hU : ∀ (k : ℕ) (x : X), (α ^ k) x ∈ U ↔ x ∈ U) :
    spT Φ ψ U ⊓ Subgroup.centralizer ({invol ψ} : Set H) =
      spT Φ ψ (fixSub (involAut ψ α) U) := by
  have hV : ∀ (k : ℕ) (x : X), (α ^ k) x ∈ fixSub (involAut ψ α) U ↔
      x ∈ fixSub (involAut ψ α) U := fixSub_stable hU _
  ext y
  constructor
  · rintro ⟨hyT, hyC⟩
    obtain ⟨u, hu, s, rfl⟩ := (P.mem_spT_iff hU).1 hyT
    have h1 := Subgroup.mem_centralizer_iff.1 hyC (invol ψ) rfl
    have hcomm : invol ψ * Φ u = Φ u * invol ψ := by
      refine mul_right_cancel (b := psi2 ψ ^ s) ?_
      calc invol ψ * Φ u * psi2 ψ ^ s = invol ψ * (Φ u * psi2 ψ ^ s) := by rw [mul_assoc]
        _ = Φ u * psi2 ψ ^ s * invol ψ := h1
        _ = Φ u * (psi2 ψ ^ s * invol ψ) := by rw [mul_assoc]
        _ = Φ u * (invol ψ * psi2 ψ ^ s) := by rw [psi2_pow_comm_invol]
        _ = Φ u * invol ψ * psi2 ψ ^ s := by rw [mul_assoc]
    have hδ : involAut ψ α u = u := by
      apply P.inj
      rw [← P.invol_act, hcomm, mul_inv_cancel_right]
    exact (P.mem_spT_iff hV).2 ⟨u, ⟨hu, hδ⟩, s, rfl⟩
  · intro hy
    obtain ⟨u, hu, s, rfl⟩ := (P.mem_spT_iff hV).1 hy
    refine ⟨(P.mem_spT_iff hU).2 ⟨u, hu.1, s, rfl⟩,
      Subgroup.mem_centralizer_iff.2 fun g hg => ?_⟩
    rw [Set.mem_singleton_iff.1 hg]
    calc invol ψ * (Φ u * psi2 ψ ^ s) = (invol ψ * Φ u) * psi2 ψ ^ s := by rw [mul_assoc]
      _ = (Φ u * invol ψ) * psi2 ψ ^ s := by rw [P.invol_mul_comm u hu.2]
      _ = Φ u * (invol ψ * psi2 ψ ^ s) := by rw [mul_assoc]
      _ = Φ u * (psi2 ψ ^ s * invol ψ) := by rw [psi2_pow_comm_invol]
      _ = Φ u * psi2 ψ ^ s * invol ψ := by rw [mul_assoc]

theorem OutProps.card_inf_centralizer_invol (P : OutProps Φ ψ α) {U : Subgroup X}
    (hU : ∀ (k : ℕ) (x : X), (α ^ k) x ∈ U ↔ x ∈ U) :
    Nat.card ↥(spT Φ ψ U ⊓ Subgroup.centralizer ({invol ψ} : Set H)) =
      Nat.card ↥(fixSub (involAut ψ α) U) * 2 ^ twoExp ψ := by
  rw [P.inf_centralizer_invol_eq hU]
  exact P.card_spT (fixSub_stable hU _)

theorem OutProps.exists_eq_mul_invol (P : OutProps Φ ψ α) (ha : 1 ≤ twoExp ψ) {U : Subgroup X}
    (hU : ∀ (k : ℕ) (x : X), (α ^ k) x ∈ U ↔ x ∈ U) {f' : H} (hT : f' ∈ spT Φ ψ U)
    (hR : f' ∉ Φ.range) (h2 : f' ^ 2 = 1) : ∃ u ∈ U, f' = Φ u * invol ψ := by
  obtain ⟨u, hu, s, rfl⟩ := (P.mem_spT_iff hU).1 hT
  obtain ⟨b, hb⟩ : ∃ b, twoExp ψ = b + 1 := ⟨twoExp ψ - 1, by omega⟩
  have hconj : psi2 ψ ^ s * Φ u = Φ ((α ^ (oddPart ψ * s)) u) * psi2 ψ ^ s := by
    have h := P.act_pow (oddPart ψ * s) u
    rw [← psi2_pow_eq] at h
    calc psi2 ψ ^ s * Φ u = psi2 ψ ^ s * Φ u * (psi2 ψ ^ s)⁻¹ * psi2 ψ ^ s := by group
      _ = Φ ((α ^ (oddPart ψ * s)) u) * psi2 ψ ^ s := by rw [h]
  have hsq : Φ (u * (α ^ (oddPart ψ * s)) u) * psi2 ψ ^ (s * 2) = 1 := by
    rw [← h2]
    calc Φ (u * (α ^ (oddPart ψ * s)) u) * psi2 ψ ^ (s * 2)
        = Φ u * Φ ((α ^ (oddPart ψ * s)) u) * ((psi2 ψ ^ s) * psi2 ψ ^ s) := by
          rw [map_mul, pow_mul (psi2 ψ) s 2, pow_two]
      _ = Φ u * (Φ ((α ^ (oddPart ψ * s)) u) * psi2 ψ ^ s) * psi2 ψ ^ s := by
          simp only [mul_assoc]
      _ = Φ u * (psi2 ψ ^ s * Φ u) * psi2 ψ ^ s := by rw [hconj]
      _ = (Φ u * psi2 ψ ^ s) ^ 2 := by rw [pow_two]; simp only [mul_assoc]
  have ht2 : psi2 ψ ^ (s * 2) ∈ Φ.range :=
    ⟨(u * (α ^ (oddPart ψ * s)) u)⁻¹, by rw [map_inv, eq_inv_of_mul_eq_one_right hsq]⟩
  have ht2' : psi2 ψ ^ (s * 2) = 1 := (P.psi2_pow_mem_range_iff _).1 ht2
  have hne : psi2 ψ ^ s ≠ 1 := fun h => hR ⟨u, by rw [h, mul_one]⟩
  have hord : orderOf (psi2 ψ) = 2 ^ (b + 1) := by rw [orderOf_psi2, hb]
  have hdvd : 2 ^ (b + 1) ∣ s * 2 := hord ▸ orderOf_dvd_of_pow_eq_one ht2'
  have hndvd : ¬ 2 ^ (b + 1) ∣ s := fun h => hne (orderOf_dvd_iff_pow_eq_one.1 (hord ▸ h))
  have hd2 : 2 ^ b ∣ s := by
    refine Nat.dvd_of_mul_dvd_mul_right (by norm_num : 0 < 2) ?_
    rwa [← pow_succ]
  obtain ⟨k, hk⟩ := hd2
  have hinv : psi2 ψ ^ s = invol ψ := by
    rcases Nat.even_or_odd k with ⟨j, hj⟩ | ⟨j, hj⟩
    · exact absurd ⟨j, by rw [hk, hj, pow_succ]; ring⟩ hndvd
    · have hs : s = 2 ^ (b + 1) * j + 2 ^ b := by rw [hk, hj, pow_succ]; ring
      have h1 : psi2 ψ ^ (2 ^ (b + 1)) = 1 := by rw [← hb]; exact psi2_pow_two_exp ψ
      rw [hs, pow_add, pow_mul, h1, one_pow, one_mul, invol, hb, Nat.add_sub_cancel]
  exact ⟨u, hu, by rw [hinv]⟩

variable [Finite X]

theorem OutProps.card_inf_centralizer_le (P : OutProps Φ ψ α) {U : Subgroup X}
    (hU : ∀ (k : ℕ) (x : X), (α ^ k) x ∈ U ↔ x ∈ U) (u : X) :
    Nat.card ↥(spT Φ ψ U ⊓ Subgroup.centralizer ({Φ u * invol ψ} : Set H)) ≤
      2 ^ twoExp ψ * (twistFix (involAut ψ α) U u).ncard := by
  set T := spT Φ ψ U with hTdef
  set S := U.map Φ with hSdef
  set Y := T ⊓ Subgroup.centralizer ({Φ u * invol ψ} : Set H) with hYdef
  have hST : S ≤ T := le_sup_left
  have hTS : T ≤ Subgroup.normalizer (S : Set H) :=
    sup_le Subgroup.le_normalizer (P.zpowers_psi2_le_normalizer hU)
  have hmain := card_mul_le_card_mul_inf (Y := Y) (S := S) (T := T) inf_le_left hST hTS
  have hT : Nat.card T = Nat.card U * 2 ^ twoExp ψ := P.card_spT hU
  have hS : Nat.card S = Nat.card U :=
    (Nat.card_congr (Subgroup.equivMapOfInjective U Φ P.inj).toEquiv).symm
  have hsub : ((Y ⊓ S : Subgroup H) : Set H) ⊆ Φ '' twistFix (involAut ψ α) U u := by
    rintro y ⟨⟨hyT, hyC⟩, hyS⟩
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hyS
    refine ⟨w, ⟨hw, ?_⟩, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.1 hyC (Φ u * invol ψ) rfl
    have h2 : Φ (u * involAut ψ α w) = Φ (w * u) := by
      rw [map_mul, map_mul, ← P.invol_act]
      calc Φ u * (invol ψ * Φ w * (invol ψ)⁻¹) = (Φ u * invol ψ) * Φ w * (invol ψ)⁻¹ := by group
        _ = (Φ w * (Φ u * invol ψ)) * (invol ψ)⁻¹ := by rw [h1]
        _ = Φ w * Φ u := by group
    have h3 := P.inj h2
    calc u * involAut ψ α w * u⁻¹ = w * u * u⁻¹ := by rw [h3]
      _ = w := mul_inv_cancel_right _ _
  have hYS : Nat.card ↥(Y ⊓ S) ≤ (twistFix (involAut ψ α) U u).ncard :=
    calc Nat.card ↥(Y ⊓ S) = ((Y ⊓ S : Subgroup H) : Set H).ncard := Nat.card_coe_set_eq _
      _ ≤ (Φ '' twistFix (involAut ψ α) U u).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ (twistFix (involAut ψ α) U u).ncard := Set.ncard_image_le (Set.toFinite _)
  rw [hT, hS] at hmain
  have hUpos : 0 < Nat.card U := Nat.card_pos
  have hY : Nat.card Y ≤ 2 ^ twoExp ψ * Nat.card ↥(Y ⊓ S) := by
    refine Nat.le_of_mul_le_mul_right ?_ hUpos
    calc Nat.card Y * Nat.card U ≤ Nat.card U * 2 ^ twoExp ψ * Nat.card ↥(Y ⊓ S) := hmain
      _ = 2 ^ twoExp ψ * Nat.card ↥(Y ⊓ S) * Nat.card U := by ring
  exact hY.trans (Nat.mul_le_mul_left _ hYS)

end Cent

end CFSG.Quasithin.H13.F431.G2.OutK
