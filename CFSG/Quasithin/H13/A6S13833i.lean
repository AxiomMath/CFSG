module

public import CFSG.Quasithin.H13.A6S13833g

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom

theorem piC_cube : ∀ k : Fin 15, piC (piC (piC k)) = k := by decide +kernel

theorem eq_mkT_of_N (g : Fin 15 → ZMod 2) (hN : ∀ k, g k + g (piC k) + g (piC (piC k)) = 0) :
    g = mkT ![g 0, g 5, g 2, g 6, g 3, g 7, g 4, g 8] := by
  have hp : piC 0 = 1 ∧ piC 1 = 5 ∧ piC 2 = 9 ∧ piC 9 = 6 ∧ piC 3 = 10 ∧ piC 10 = 7 ∧
      piC 4 = 11 ∧ piC 11 = 8 ∧ piC 12 = 12 ∧ piC 13 = 13 ∧ piC 14 = 14 := by decide
  obtain ⟨p0, p1, p2, p9, p3, p10, p4, p11, p12, p13, p14⟩ := hp
  have h0 := hN 0
  have h2 := hN 2
  have h3 := hN 3
  have h4 := hN 4
  have h12 := hN 12
  have h13 := hN 13
  have h14 := hN 14
  rw [p0, p1] at h0
  rw [p2, p9] at h2
  rw [p3, p10] at h3
  rw [p4, p11] at h4
  rw [p12, p12] at h12
  rw [p13, p13] at h13
  rw [p14, p14] at h14
  have key3 : ∀ x y z : ZMod 2, x + y + z = 0 → y = x + z := by decide
  have key1 : ∀ x : ZMod 2, x + x + x = 0 → x = 0 := by decide
  funext k
  fin_cases k
  · rfl
  · exact key3 _ _ _ h0
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact key3 _ _ _ h2
  · exact key3 _ _ _ h3
  · exact key3 _ _ _ h4
  · exact key1 _ h12
  · exact key1 _ h13
  · exact key1 _ h14

theorem ConI_zero (t : Fin 15 → ZMod 2) : ConI 0 t := by
  unfold ConI; simp

theorem ConI_sum {l : List (Fin 15 → ZMod 2)} {t : Fin 15 → ZMod 2} (h : ∀ s ∈ l, ConI s t) :
    ConI l.sum t := by
  induction l with
  | nil => exact ConI_zero t
  | cons s l ih =>
    rw [List.sum_cons]
    exact ConI_add (h s (by simp)) (ih fun s' hs' => h s' (by simp [hs']))


theorem conj_inv_mem_pCoreOf_LT {G : Type} [Group G] [Finite G] {L T : Subgroup G} {q l : G}
    (hq : q ∈ pCoreOf 2 (L ⊔ T)) (hl : l ∈ L) : l⁻¹ * q * l ∈ pCoreOf 2 (L ⊔ T) := by
  have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (L ⊔ T)
    (Subgroup.mem_sup_left (L.inv_mem hl))) q).mp hq
  rwa [inv_inv] at this

theorem zmod2_eq_of_zero_eq_add : ∀ x y : ZMod 2, 0 = x + y → x = y := by decide

theorem zmod2_cycle_sum : ∀ x y z : ZMod 2, x + y + (y + z) + (z + x) = 0 := by decide

theorem zmod2_add_add_eq_zero : ∀ a b c d : ZMod 2, a + b = c + d → a + c + (b + d) = 0 := by
  decide

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} (S : Setting4 G T L V)
include S

section NuQ

variable {ρ : ↥S.G1 →* Perm (Fin 6)}
  {β : ↥(conjClosure S.V3 S.G1) →* Multiplicative ↥(evenWeight 6)}
  (hβk : ∀ u, β u = 1 ↔ (u : G) ∈ fsuV1 T V)
  (hβe : ∀ (h : ↥S.G1) (u v : ↥(conjClosure S.V3 S.G1)), (v : G) = h * u * h⁻¹ →
    Multiplicative.toAdd (β v) = permWeight 6 (ρ h) (Multiplicative.toAdd (β u)))
  {u₁ : G} (hu₁ : u₁ ∈ S.U1c β) (hu₁V : u₁ ∉ fsuV1 T V)
include hβk hβe hu₁ hu₁V

theorem Fq_conj_inv {q : G} (hq : q ∈ pCoreOf 2 (L ⊔ T))
    (l : ↥(Subgroup.normalizer (V : Set G))) (k : Fin 15) :
    S.Fq u₁ ((l : G)⁻¹ * q * l) k = S.Fq u₁ q (dPerm (S.frame.ρ l) k) := by
  have h := S.Fq_conj hβk hβe hu₁ hu₁V hq (l := l⁻¹) k
  rw [map_inv, inv_inv] at h
  have e : ((l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G) * q *
      ((l⁻¹ : ↥(Subgroup.normalizer (V : Set G))) : G)⁻¹ = (l : G)⁻¹ * q * l := by
    simp only [Subgroup.coe_inv, inv_inv]
  rw [e] at h
  exact h

theorem ConI_cY_of_rel {ε : Fin 4 → ZMod 2} (hε : ε ≠ 0)
    (hrel : ∀ q ∈ pCoreOf 2 (L ⊔ T), ConI (rEps ε) (S.Fq u₁ q)) {q : G}
    (hq : q ∈ pCoreOf 2 (L ⊔ T)) (j : Fin 15) : ConI (cY j) (S.Fq u₁ q) := by
  have hF : ∀ q ∈ pCoreOf 2 (L ⊔ T), ∀ (σ : Perm (Fin 6)), Perm.sign σ = 1 →
      ∃ q' ∈ pCoreOf 2 (L ⊔ T), S.Fq u₁ q' = fun k => S.Fq u₁ q (dPerm σ k) := by
    intro q hq σ hσ
    obtain ⟨l, hlL, hl⟩ := (S.frame.image_L σ).2 (Perm.mem_alternatingGroup.2 hσ)
    refine ⟨(l : G)⁻¹ * q * l, conj_inv_mem_pCoreOf_LT hq hlL, ?_⟩
    funext k
    rw [S.Fq_conj_inv hβk hβe hu₁ hu₁V hq l k, hl]
  have h45 : ∀ q ∈ pCoreOf 2 (L ⊔ T), ConI c45 (S.Fq u₁ q) := by
    intro q hq
    obtain ⟨hsign, hsum⟩ := certEps_facts ε hε
    rw [← hsum]
    refine ConI_sum fun s hs => ?_
    obtain ⟨σ, hσ, rfl⟩ := List.mem_map.1 hs
    obtain ⟨q', hq', hq'F⟩ := hF q hq σ (hsign σ hσ)
    have h1 := hrel q' hq'
    rw [hq'F] at h1
    exact (ConI_comp σ _ _).1 h1
  obtain ⟨hsign, hcY⟩ := sigY_facts j
  rw [← hcY]
  obtain ⟨q', hq', hq'F⟩ := hF q hq (sigY j) hsign
  have h1 := h45 q' hq'
  rw [hq'F] at h1
  exact (ConI_comp (sigY j) _ _).1 h1

theorem relIndex_Q_C_le_four (hhat : ¬ IsHatA6 L) {ε : Fin 4 → ZMod 2} (hε : ε ≠ 0)
    (hrel : ∀ q ∈ pCoreOf 2 (L ⊔ T), ConI (rEps ε) (S.Fq u₁ q)) :
    (cfix (S.cL1 hhat : G) (pCoreOf 2 (L ⊔ T)) ⊔ (pCoreOf 2 (L ⊔ T) ⊓
      Subgroup.centralizer (S.U0c β : Set G))).relIndex (pCoreOf 2 (L ⊔ T)) ≤ 4 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c : G := (S.cL1 hhat : G) with hcdef
  set Q := pCoreOf 2 (L ⊔ T) with hQdef
  set C := Q ⊓ Subgroup.centralizer (S.U0c β : Set G) with hCdef
  set M := cfix c Q ⊔ C with hMdef
  have hc3 : c ^ 3 = 1 := S.cL1_cube hhat
  have hcL : c ∈ L := S.L1_le_L (S.cL1_mem hhat)
  have hρc : S.frame.ρ (S.cL1 hhat) = c012 := S.cL1_rho hhat
  have hcQ : ∀ q ∈ Q, c * q * c⁻¹ ∈ Q := fun q hq =>
    (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (L ⊔ T)
      (Subgroup.mem_sup_left hcL)) q).mp hq
  have hFc : ∀ q ∈ Q, S.Fq u₁ (c * q * c⁻¹) = fun k => S.Fq u₁ q (piC k) := by
    intro q hq
    funext k
    rw [S.Fq_conj hβk hβe hu₁ hu₁V hq (l := S.cL1 hhat) k, hρc]
    rfl
  have hFinv : ∀ q ∈ Q, S.Fq u₁ q⁻¹ = S.Fq u₁ q := by
    intro q hq
    funext k
    have h1 := S.Fq_mul hβk hβe hu₁ (Q.inv_mem hq) hq k
    rw [inv_mul_cancel] at h1
    have h0 : S.Fq u₁ 1 k = 0 := S.Fq_eq_zero_iff.2 (by group)
    rw [h0] at h1
    exact zmod2_eq_of_zero_eq_add _ _ h1
  let gq : G → Fin 15 → ZMod 2 := fun q => S.Fq u₁ (q⁻¹ * (c * q * c⁻¹))
  have hgq : ∀ q ∈ Q, gq q = fun k => S.Fq u₁ q k + S.Fq u₁ q (piC k) := by
    intro q hq
    funext k
    show S.Fq u₁ (q⁻¹ * (c * q * c⁻¹)) k = _
    rw [S.Fq_mul hβk hβe hu₁ (Q.inv_mem hq) (hcQ q hq) k, hFinv q hq, hFc q hq]
  have hmem4 : ∀ q ∈ Q, gq q ∈ list4 := by
    intro q hq
    have hq' : q⁻¹ * (c * q * c⁻¹) ∈ Q := Q.mul_mem (Q.inv_mem hq) (hcQ q hq)
    have hN : ∀ k, gq q k + gq q (piC k) + gq q (piC (piC k)) = 0 := by
      intro k
      rw [hgq q hq]
      show S.Fq u₁ q k + S.Fq u₁ q (piC k) + (S.Fq u₁ q (piC k) + S.Fq u₁ q (piC (piC k))) +
        (S.Fq u₁ q (piC (piC k)) + S.Fq u₁ q (piC (piC (piC k)))) = 0
      rw [piC_cube]
      exact zmod2_cycle_sum _ _ _
    have e := eq_mkT_of_N (gq q) hN
    rw [e]
    refine mkT_mem_list4 _ fun j => ?_
    rw [← e]
    exact S.ConI_cY_of_rel hβk hβe hu₁ hu₁V hε hrel hq' j
  have hcC : ∀ n ∈ C, c * n * c⁻¹ ∈ C := by
    intro n hn
    refine ⟨hcQ n hn.1, ?_⟩
    show c * n * c⁻¹ ∈ Subgroup.centralizer (S.U0c β : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hcN := S.LT_le_normalizer_U0c hβe hβk (Subgroup.mem_sup_left hcL)
    have hu' : c⁻¹ * u * c⁻¹⁻¹ ∈ S.U0c β :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcN) u).mp hu
    rw [inv_inv] at hu'
    have h1 := Subgroup.mem_centralizer_iff.mp hn.2 _ hu'
    calc u * (c * n * c⁻¹) = c * ((c⁻¹ * u * c) * n) * c⁻¹ := by group
      _ = c * (n * (c⁻¹ * u * c)) * c⁻¹ := by rw [h1]
      _ = c * n * c⁻¹ * u := by group
  have hC3 : ¬ 3 ∣ Nat.card C := by
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 ((pCoreOf_isPGroup 2 (L ⊔ T)).to_le
      (inf_le_left : C ≤ Q))
    rw [hm]
    intro h
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hfib : ∀ q ∈ Q, ∀ q' ∈ Q, gq q = gq q' → q⁻¹ * q' ∈ M := by
    intro q hq q' hq' he
    set y := q⁻¹ * q' with hydef
    have hy : y ∈ Q := Q.mul_mem (Q.inv_mem hq) hq'
    have hFy : ∀ k, S.Fq u₁ y k = S.Fq u₁ q k + S.Fq u₁ q' k := fun k => by
      rw [hydef, S.Fq_mul hβk hβe hu₁ (Q.inv_mem hq) hq' k, hFinv q hq]
    have hyq : y⁻¹ * (c * y * c⁻¹) ∈ Q := Q.mul_mem (Q.inv_mem hy) (hcQ y hy)
    have hgy : ∀ k, S.Fq u₁ (y⁻¹ * (c * y * c⁻¹)) k = 0 := by
      intro k
      have e1 : S.Fq u₁ (y⁻¹ * (c * y * c⁻¹)) k = S.Fq u₁ y k + S.Fq u₁ y (piC k) := by
        have := congrFun (hgq y hy) k
        exact this
      rw [e1, hFy, hFy]
      have h1 := congrFun he k
      rw [hgq q hq, hgq q' hq'] at h1
      exact zmod2_add_add_eq_zero _ _ _ _ h1
    have hyC : y⁻¹ * (c * y * c⁻¹) ∈ C :=
      ⟨hyq, (S.Fq_eq_zero_iff_mem_centralizer hβk hβe hu₁ hu₁V hyq).1 hgy⟩
    obtain ⟨n, hnC, hn⟩ := exists_comm_mul_of_conj_mem hc3 hC3 hcC hyC
    have hyn : y * n ∈ cfix c Q := by
      refine mem_cfix.2 ⟨Q.mul_mem hy hnC.1, ?_⟩
      calc c * (y * n) = c * (y * n) * c⁻¹ * c := by group
        _ = y * n * c := by rw [hn]
    have e : y = (y * n) * n⁻¹ := by group
    rw [e]
    exact M.mul_mem (Subgroup.mem_sup_left hyn) (Subgroup.mem_sup_right (C.inv_mem hnC))
  show (M.subgroupOf Q).index ≤ 4
  rw [Subgroup.index]
  let f : (↥Q ⧸ M.subgroupOf Q) → {t // t ∈ list4} := fun a => ⟨gq (a.out : G), hmem4 _ a.out.2⟩
  have hf : Function.Injective f := by
    intro a b hab
    have h := congrArg Subtype.val hab
    have h' := hfib _ a.out.2 _ b.out.2 h
    rw [← QuotientGroup.out_eq' a, ← QuotientGroup.out_eq' b, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa using h'
  have h4 : Nat.card {t // t ∈ list4} ≤ 4 := by
    have e : Nat.card {t // t ∈ list4} = list4.toFinset.card := by
      rw [← Nat.card_eq_finsetCard]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun t => by rw [List.mem_toFinset])
    rw [e]
    exact (List.toFinset_card_le list4).trans (by decide)
  exact (Nat.card_le_card_of_injective f hf).trans h4

end NuQ

end Setting4

end CFSG.Quasithin.H13.A6
