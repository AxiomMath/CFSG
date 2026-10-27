module

public import CFSG.Quasithin.Background.D1Statement

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.Quasithin

section Chief

variable {G : Type} [Group G]

private theorem inv_conj_eq_G6Chief {y x : G} (h : y ^ 3 * x * (y ^ 3)⁻¹ = x) :
    y⁻¹ * x * y = y * (y * x * y⁻¹) * y⁻¹ := by
  have h3 : y ^ 3 = y * y * y := by rw [pow_succ, pow_succ, pow_one]
  rw [h3] at h
  calc y⁻¹ * x * y = y⁻¹ * ((y * y * y) * x * (y * y * y)⁻¹) * y := by rw [h]
    _ = y * (y * x * y⁻¹) * y⁻¹ := by group

private theorem zpowers_conj_mem_G6Chief {y : G} {N : Set G} (h1 : ∀ x ∈ N, y * x * y⁻¹ ∈ N)
    (h2 : ∀ x ∈ N, y⁻¹ * x * y ∈ N) :
    ∀ g ∈ Subgroup.zpowers y, ∀ x ∈ N, g * x * g⁻¹ ∈ N := by
  intro g hg x hx
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  refine Int.induction_on m ?_ ?_ ?_
  · simpa using hx
  · intro i ih
    have e : y ^ ((i : ℤ) + 1) * x * (y ^ ((i : ℤ) + 1))⁻¹ =
        y * (y ^ (i : ℤ) * x * (y ^ (i : ℤ))⁻¹) * y⁻¹ := by group
    rw [e]
    exact h1 _ ih
  · intro i ih
    have e : y ^ (-(i : ℤ) - 1) * x * (y ^ (-(i : ℤ) - 1))⁻¹ =
        y⁻¹ * (y ^ (-(i : ℤ)) * x * (y ^ (-(i : ℤ)))⁻¹) * y := by group
    rw [e]
    exact h2 _ ih

theorem exists_chiefSeries_index_ge [Finite G] {V : Subgroup G}
    (hV : IsElemAbelian 2 V) {y : G} (hyV : ∀ v ∈ V, y * v * y⁻¹ ∈ V)
    (hy3 : ∀ v ∈ V, y ^ 3 * v * (y ^ 3)⁻¹ = v) :
    ∃ k : ℕ, IsChiefSeriesFrom (Subgroup.zpowers y) V V k ∧
      4 ^ k ≤ (Subgroup.centralizer ({y} : Set G)).relIndex V := by
  classical
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hV.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hsq : ∀ a ∈ V, a ^ 2 = 1 := hV.2
  set C : Subgroup G := Subgroup.centralizer ({y} : Set G) with hC
  let Inv : Subgroup G → Prop := fun N => N ≤ V ∧ ∀ x ∈ N, y * x * y⁻¹ ∈ N
  have hInv' : ∀ N, Inv N → ∀ x ∈ N, y⁻¹ * x * y ∈ N := by
    intro N hN x hx
    rw [inv_conj_eq_G6Chief (hy3 x (hN.1 hx))]
    exact hN.2 _ (hN.2 _ hx)
  have hNormal : ∀ N, Inv N → IsNormalIn (Subgroup.zpowers y) V N := fun N hN =>
    ⟨hN.1, zpowers_conj_mem_G6Chief (N := (N : Set G)) hN.2 (hInv' N hN)⟩
  have main : ∀ n : ℕ, ∀ N : Subgroup G, Nat.card N = n → Inv N →
      ∃ k : ℕ, IsChiefSeriesFrom (Subgroup.zpowers y) V N k ∧ 4 ^ k ≤ C.relIndex N := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro N hcard hN
    by_cases hbot : N = ⊥
    · subst hbot
      exact ⟨0, IsChiefSeriesFrom.bot, by simp [Subgroup.relIndex_bot_right]⟩
    · have hbot_lt : (⊥ : Subgroup G) < N := bot_lt_iff_ne_bot.mpr hbot
      obtain ⟨L, hLN, hLinv, hLmax⟩ : ∃ L : Subgroup G, L < N ∧ Inv L ∧
          ∀ K : Subgroup G, K < N → Inv K → L ≤ K → K ≤ L := by
        have hmem : (⊥ : Subgroup G) ∈ {K : Subgroup G | K < N ∧ Inv K} := by
          refine ⟨hbot_lt, bot_le, fun x hx => ?_⟩
          rw [Subgroup.mem_bot] at hx ⊢
          simp [hx]
        obtain ⟨L, -, hL⟩ := (Set.toFinite {K : Subgroup G | K < N ∧ Inv K}).exists_le_maximal hmem
        exact ⟨L, hL.1.1, hL.1.2, fun K hK hKinv hLK => hL.2 ⟨hK, hKinv⟩ hLK⟩
      have hNV : N ≤ V := hN.1
      have hLV : L ≤ V := hLinv.1
      have hlt : Nat.card L < n := by
        rw [← hcard]
        exact Subgroup.card_lt_of_lt hLN
      obtain ⟨k', hser, hk'⟩ := ih (Nat.card L) hlt L rfl hLinv
      have hstep : IsChiefStep (Subgroup.zpowers y) V L N := by
        refine ⟨hNormal N hN, hNormal L hLinv, hLN, ?_⟩
        intro K hK hLK hKN
        by_cases hKN' : K = N
        · exact Or.inr hKN'
        · left
          have hKinv : Inv K := ⟨hK.1, fun x hx => hK.2 y (Subgroup.mem_zpowers y) x hx⟩
          exact le_antisymm (hLmax K (lt_of_le_of_ne hKN hKN') hKinv hLK) hLK
      have e1 : C.relIndex L * Nat.card ↥(C ⊓ L) = Nat.card L := Subgroup.relIndex_mul_card C L
      have e2 : C.relIndex N * Nat.card ↥(C ⊓ N) = Nat.card N := Subgroup.relIndex_mul_card C N
      have e3 : L.relIndex N * Nat.card L = Nat.card N := by
        have := Subgroup.relIndex_mul_card L N
        rwa [inf_eq_left.mpr hLN.le] at this
      have hpa : 0 < Nat.card ↥(C ⊓ L) := Nat.card_pos
      have hpb : 0 < Nat.card ↥(C ⊓ N) := Nat.card_pos
      have hpι : 0 < L.relIndex N := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      by_cases hc : ∀ x ∈ N, y * x * y⁻¹ * x⁻¹ ∈ L
      ·
        have hcen : IsCentralStep (Subgroup.zpowers y) L N := by
          intro g hg x hx
          obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
          revert x
          refine Int.induction_on m ?_ ?_ ?_
          · intro x hx
            simpa using L.one_mem
          · intro i ih' x hx
            have hu := ih' x hx
            have e : y ^ ((i : ℤ) + 1) * x * (y ^ ((i : ℤ) + 1))⁻¹ * x⁻¹ =
                (y * (y ^ (i : ℤ) * x * (y ^ (i : ℤ))⁻¹ * x⁻¹) * y⁻¹) * (y * x * y⁻¹ * x⁻¹) := by
              group
            rw [e]
            exact L.mul_mem (hLinv.2 _ hu) (hc x hx)
          · intro i ih' x hx
            have hu := ih' x hx
            have h1 : y⁻¹ * x * y * x⁻¹ ∈ L := by
              have := hInv' L hLinv _ (hc x hx)
              have e2' : y⁻¹ * x * y * x⁻¹ = (y⁻¹ * (y * x * y⁻¹ * x⁻¹) * y)⁻¹ := by group
              rw [e2']
              exact L.inv_mem this
            have e : y ^ (-(i : ℤ) - 1) * x * (y ^ (-(i : ℤ) - 1))⁻¹ * x⁻¹ =
                (y⁻¹ * (y ^ (-(i : ℤ)) * x * (y ^ (-(i : ℤ)))⁻¹ * x⁻¹) * y) * (y⁻¹ * x * y * x⁻¹) := by
              group
            rw [e]
            exact L.mul_mem (hInv' L hLinv _ hu) h1
        refine ⟨k', IsChiefSeriesFrom.central hstep hcen hser, ?_⟩
        have hb1 : (C ⊓ L).relIndex (C ⊓ N) * Nat.card ↥(C ⊓ L) = Nat.card ↥(C ⊓ N) := by
          have := Subgroup.relIndex_mul_card (C ⊓ L) (C ⊓ N)
          rwa [inf_eq_left.mpr (inf_le_inf_left C hLN.le)] at this
        have hLCN : L ⊓ (C ⊓ N) = C ⊓ L := by
          ext z
          simp only [Subgroup.mem_inf]
          constructor
          · rintro ⟨hzL, hzC, -⟩
            exact ⟨hzC, hzL⟩
          · rintro ⟨hzC, hzL⟩
            exact ⟨hzL, hzC, hLN.le hzL⟩
        have hb2 : (C ⊓ L).relIndex (C ⊓ N) ≤ L.relIndex N := by
          have h1 : (C ⊓ L).relIndex (C ⊓ N) = L.relIndex (C ⊓ N) := by
            rw [← hLCN]
            exact Subgroup.inf_relIndex_right L (C ⊓ N)
          rw [h1]
          exact Subgroup.relIndex_le_of_le_right inf_le_right
            (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite).ne'
        have hb : Nat.card ↥(C ⊓ N) ≤ L.relIndex N * Nat.card ↥(C ⊓ L) := by
          rw [← hb1]
          exact Nat.mul_le_mul_right _ hb2
        have key : C.relIndex L * (L.relIndex N * Nat.card ↥(C ⊓ L)) ≤
            C.relIndex N * (L.relIndex N * Nat.card ↥(C ⊓ L)) := by
          calc C.relIndex L * (L.relIndex N * Nat.card ↥(C ⊓ L))
              = L.relIndex N * (C.relIndex L * Nat.card ↥(C ⊓ L)) := by ring
            _ = L.relIndex N * Nat.card L := by rw [e1]
            _ = Nat.card N := e3
            _ = C.relIndex N * Nat.card ↥(C ⊓ N) := e2.symm
            _ ≤ C.relIndex N * (L.relIndex N * Nat.card ↥(C ⊓ L)) := Nat.mul_le_mul_left _ hb
        exact le_trans hk' (Nat.le_of_mul_le_mul_right key (Nat.mul_pos hpι hpa))
      ·
        push Not at hc
        obtain ⟨x, hxN, hxc⟩ := hc
        refine ⟨k' + 1, IsChiefSeriesFrom.noncentral hstep ?_ hser, ?_⟩
        · intro hcen
          exact hxc (hcen y (Subgroup.mem_zpowers y) x hxN)
        ·
          let S : Subgroup G :=
            { carrier := {z | z ∈ V ∧ y * z * y⁻¹ * z⁻¹ ∈ L}
              one_mem' := ⟨V.one_mem, by simpa using L.one_mem⟩
              mul_mem' := by
                rintro a b ⟨haV, ha⟩ ⟨hbV, hb⟩
                refine ⟨V.mul_mem haV hbV, ?_⟩
                have e : y * (a * b) * y⁻¹ * (a * b)⁻¹ =
                    (y * a * y⁻¹ * a⁻¹) * (a * (y * b * y⁻¹ * b⁻¹) * a⁻¹) := by group
                rw [e]
                refine L.mul_mem ha ?_
                have hbc : y * b * y⁻¹ * b⁻¹ ∈ V := hLV hb
                have hcm := hcomm a haV _ hbc
                have e2 : a * (y * b * y⁻¹ * b⁻¹) * a⁻¹ = y * b * y⁻¹ * b⁻¹ := by
                  calc a * (y * b * y⁻¹ * b⁻¹) * a⁻¹ = (y * b * y⁻¹ * b⁻¹) * a * a⁻¹ := by rw [hcm]
                    _ = y * b * y⁻¹ * b⁻¹ := by group
                rw [e2]
                exact hb
              inv_mem' := by
                rintro a ⟨haV, ha⟩
                refine ⟨V.inv_mem haV, ?_⟩
                have e : y * a⁻¹ * y⁻¹ * a⁻¹⁻¹ = a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a := by group
                rw [e]
                have hc' : (y * a * y⁻¹ * a⁻¹)⁻¹ ∈ V := V.inv_mem (hLV ha)
                have hcm := hcomm a⁻¹ (V.inv_mem haV) _ hc'
                have e2 : a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a = (y * a * y⁻¹ * a⁻¹)⁻¹ := by
                  calc a⁻¹ * (y * a * y⁻¹ * a⁻¹)⁻¹ * a = (y * a * y⁻¹ * a⁻¹)⁻¹ * a⁻¹ * a := by rw [hcm]
                    _ = (y * a * y⁻¹ * a⁻¹)⁻¹ := by group
                rw [e2]
                exact L.inv_mem ha }
          have hLS : L ≤ S := fun l hl =>
            ⟨hLV hl, L.mul_mem (hLinv.2 l hl) (L.inv_mem hl)⟩
          have hCN : C ⊓ N ≤ L := by
            intro n hn
            obtain ⟨hnC, hnN⟩ := hn
            have hny : y * n * y⁻¹ = n := by
              have h1 := Subgroup.mem_centralizer_singleton_iff.mp hnC
              calc y * n * y⁻¹ = n * y * y⁻¹ := by rw [h1]
                _ = n := by group
            by_contra hnL
            have hnV : n ∈ V := hNV hnN
            have hK : L ⊔ Subgroup.zpowers n ≤
                (L ⊔ Subgroup.zpowers n).comap (MulAut.conj y).toMonoidHom := by
              refine sup_le (fun l hl => ?_) (Subgroup.zpowers_le.mpr ?_)
              · refine Subgroup.mem_comap.mpr ?_
                have := (le_sup_left : L ≤ L ⊔ Subgroup.zpowers n) (hLinv.2 l hl)
                simpa [MulAut.conj_apply] using this
              · refine Subgroup.mem_comap.mpr ?_
                have := (le_sup_right : Subgroup.zpowers n ≤ L ⊔ Subgroup.zpowers n)
                  (Subgroup.mem_zpowers n)
                simpa [MulAut.conj_apply, hny] using this
            have hKinv : Inv (L ⊔ Subgroup.zpowers n) :=
              ⟨sup_le hLV (Subgroup.zpowers_le.mpr hnV), fun z hz => by
                have := Subgroup.mem_comap.mp (hK hz)
                simpa [MulAut.conj_apply] using this⟩
            have hKN : L ⊔ Subgroup.zpowers n ≤ N := sup_le hLN.le (Subgroup.zpowers_le.mpr hnN)
            by_cases hKlt : L ⊔ Subgroup.zpowers n < N
            · exact hnL (hLmax _ hKlt hKinv le_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers n)))
            · have hKeq : L ⊔ Subgroup.zpowers n = N := eq_of_le_of_not_lt hKN hKlt
              have hnS : n ∈ S := ⟨hnV, by rw [hny]; simpa using L.one_mem⟩
              have hKS : L ⊔ Subgroup.zpowers n ≤ S := sup_le hLS (Subgroup.zpowers_le.mpr hnS)
              have hxK : x ∈ L ⊔ Subgroup.zpowers n := by rw [hKeq]; exact hxN
              exact hxc (hKS hxK).2
          have hxL : x ∉ L := by
            intro hxL
            exact hxc (L.mul_mem (hLinv.2 x hxL) (L.inv_mem hxL))
          have hyxN : y * x * y⁻¹ ∈ N := hN.2 x hxN
          have hyxL : y * x * y⁻¹ ∉ L := by
            intro h
            apply hxL
            have h' := hInv' L hLinv _ h
            have e : y⁻¹ * (y * x * y⁻¹) * y = x := by group
            rwa [e] at h'
          have hxy : x⁻¹ * (y * x * y⁻¹) ∉ L := by
            intro h
            apply hxc
            have hcm := hcomm x (hNV hxN) _ (hNV hyxN)
            have hc2 : (y * x * y⁻¹) * x⁻¹ = x⁻¹ * (y * x * y⁻¹) := by
              calc (y * x * y⁻¹) * x⁻¹ = x⁻¹ * (x * (y * x * y⁻¹)) * x⁻¹ := by group
                _ = x⁻¹ * ((y * x * y⁻¹) * x) * x⁻¹ := by rw [hcm]
                _ = x⁻¹ * (y * x * y⁻¹) := by group
            rw [hc2]
            exact h
          haveI : Fintype (↥N ⧸ L.subgroupOf N) := Fintype.ofFinite _
          have h3 : 3 ≤ L.relIndex N := by
            let q₀ : ↥N := 1
            let q₁ : ↥N := ⟨x, hxN⟩
            let q₂ : ↥N := ⟨y * x * y⁻¹, hyxN⟩
            have hne01 : (QuotientGroup.mk q₀ : ↥N ⧸ L.subgroupOf N) ≠ QuotientGroup.mk q₁ := by
              intro h
              have := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h)
              exact hxL (by simpa [q₀, q₁] using this)
            have hne02 : (QuotientGroup.mk q₀ : ↥N ⧸ L.subgroupOf N) ≠ QuotientGroup.mk q₂ := by
              intro h
              have := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h)
              exact hyxL (by simpa [q₀, q₂] using this)
            have hne12 : (QuotientGroup.mk q₁ : ↥N ⧸ L.subgroupOf N) ≠ QuotientGroup.mk q₂ := by
              intro h
              have := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h)
              exact hxy (by simpa [q₁, q₂] using this)
            have hcard3 : ({QuotientGroup.mk q₀, QuotientGroup.mk q₁, QuotientGroup.mk q₂} :
                Finset (↥N ⧸ L.subgroupOf N)).card = 3 :=
              Finset.card_eq_three.mpr ⟨_, _, _, hne01, hne02, hne12, rfl⟩
            calc 3 = ({QuotientGroup.mk q₀, QuotientGroup.mk q₁, QuotientGroup.mk q₂} :
                  Finset (↥N ⧸ L.subgroupOf N)).card := hcard3.symm
              _ ≤ Fintype.card (↥N ⧸ L.subgroupOf N) := Finset.card_le_univ _
              _ = L.relIndex N := by
                rw [← Nat.card_eq_fintype_card]
                rfl
          have hpow2 : ∃ c : ℕ, L.relIndex N = 2 ^ c := by
            have hN2 : IsPGroup 2 ↥N := fun g => ⟨1, by
              have := hsq (g : G) (hNV g.2)
              apply Subtype.ext
              simpa using this⟩
            haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
            obtain ⟨a', ha'⟩ := (IsPGroup.iff_card).mp hN2
            have hdvd : L.relIndex N ∣ 2 ^ a' := ⟨Nat.card L, by rw [← ha']; exact e3.symm⟩
            obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
            exact ⟨c, hc⟩
          have hι4 : 4 ≤ L.relIndex N := by
            obtain ⟨c, hc⟩ := hpow2
            rw [hc] at h3 ⊢
            rcases c with _ | _ | c
            · norm_num at h3
            · norm_num at h3
            · calc 4 = 2 ^ 2 := by norm_num
                _ ≤ 2 ^ (c + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
          have hCeq : C ⊓ N = C ⊓ L := le_antisymm (le_inf inf_le_left hCN) (inf_le_inf_left C hLN.le)
          have hab : Nat.card ↥(C ⊓ N) = Nat.card ↥(C ⊓ L) := by rw [hCeq]
          have hrN : C.relIndex N = L.relIndex N * C.relIndex L := by
            have h1 : C.relIndex N * Nat.card ↥(C ⊓ L) =
                (L.relIndex N * C.relIndex L) * Nat.card ↥(C ⊓ L) := by
              rw [← hab, e2, ← e3, ← e1, ← hab]
              ring
            exact Nat.eq_of_mul_eq_mul_right hpa h1
          calc 4 ^ (k' + 1) = 4 * 4 ^ k' := by ring
            _ ≤ L.relIndex N * C.relIndex L := Nat.mul_le_mul hι4 hk'
            _ = C.relIndex N := hrN.symm
  exact main _ V rfl ⟨le_rfl, hyV⟩

end Chief

end CFSG.Quasithin.H13.L319
