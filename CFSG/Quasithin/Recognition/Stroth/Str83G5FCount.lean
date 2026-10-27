module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5FChief
import CFSG.GroupTheory.CoprimeSectionStability

public section

namespace CFSG.Quasithin.Stroth.G5F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender CFSG.Blueprint CFSG.LieType.Ree

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}

private theorem d1_claim_aux (hF : Hyp111 L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hQ : Nat.card (Q1 L1 L2 S) < 2 ^ (16 * (2 * a + 1)))
    {D1 : Subgroup G} (hD1 : D1 ≤ borelOf L1 S) (hD1odd : Odd (Nat.card D1)) :
    ∀ R : Subgroup G, IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) R →
      (∃ k : ℕ, (R ⊓ Subgroup.centralizer (D1 : Set G)).relIndex R =
        2 ^ (4 * (2 * a + 1) * k)) ∧
      ∀ δ ∈ D1, δ ≠ 1 → R ⊓ Subgroup.centralizer ({δ} : Set G) =
        R ⊓ Subgroup.centralizer (D1 : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hD1L1 : D1 ≤ L1 := hD1.trans (F1.borelOf_le L1 S)
  have hD1H : D1 ≤ L1 ⊔ S := hD1L1.trans le_sup_left
  have hQ1S : Q1 L1 L2 S ≤ S :=
    F7.isSylowTwoOf_pCoreOf_le
      (F112W.isSylowTwoOf_parabolic (Hyp111R.of_hyp111 rankOneListedFacts hF))
  have hQ1H : Q1 L1 L2 S ≤ L1 ⊔ S := hQ1S.trans le_sup_right
  let Claim : Subgroup G → Prop := fun R =>
    (∃ k : ℕ, (R ⊓ Subgroup.centralizer (D1 : Set G)).relIndex R =
      2 ^ (4 * (2 * a + 1) * k)) ∧
    ∀ δ ∈ D1, δ ≠ 1 → R ⊓ Subgroup.centralizer ({δ} : Set G) =
      R ⊓ Subgroup.centralizer (D1 : Set G)
  change ∀ R : Subgroup G, IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) R → Claim R
  have key : ∀ n : ℕ, ∀ R : Subgroup G, Nat.card R = n →
      IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) R → Claim R := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro R hcard hR
      by_cases hRbot : R = ⊥
      · subst R
        refine ⟨⟨0, ?_⟩, ?_⟩
        · simp
        · intro δ hδ hδ1
          simp
      ·
        obtain ⟨L, -, hLmax⟩ := Finite.exists_le_maximal
          (p := fun K : Subgroup G => IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) K ∧ K < R)
          (a := ⊥) ⟨⟨bot_le, fun _ _ _ hx => by
            simpa using (Subgroup.mem_bot.mp hx)⟩, bot_lt_iff_ne_bot.mpr hRbot⟩
        have hLnorm : IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) L := hLmax.1.1
        have hLR : L < R := hLmax.1.2
        have hstep : IsChiefStep (L1 ⊔ S) (Q1 L1 L2 S) L R := by
          refine ⟨hR, hLnorm, hLR, ?_⟩
          intro K hK hLK hKR
          by_cases hKeq : K = R
          · exact Or.inr hKeq
          · exact Or.inl (le_antisymm (hLmax.2 ⟨hK, lt_of_le_of_ne hKR hKeq⟩ hLK) hLK)
        have hIH : Claim L :=
          ih (Nat.card L) (hcard ▸ Subgroup.card_lt_of_lt hLR) L rfl hLnorm
        have hR2 : IsPGroup 2 ↥R :=
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P1 L1 L2 S)).to_le hR.1
        have hRH : R ≤ L1 ⊔ S := hR.1.trans hQ1H
        have hRNL : R ≤ Subgroup.normalizer (L : Set G) :=
          hRH.trans (D14.le_normalizer_of_isNormalIn hLnorm)
        have hD1NR : D1 ≤ Subgroup.normalizer (R : Set G) :=
          hD1H.trans (D14.le_normalizer_of_isNormalIn hR)
        have hD1NL : D1 ≤ Subgroup.normalizer (L : Set G) :=
          hD1H.trans (D14.le_normalizer_of_isNormalIn hLnorm)
        have hsolvR : Group.IsSolvable ↥R := by
          haveI : Group.IsNilpotent ↥R := hR2.isNilpotent
          infer_instance
        rcases chief_dichotomy hF hB ha hSz hQ hstep with hcen | ⟨hrel, hfp⟩
        ·
          have hcenL : ∀ d ∈ D1, ∀ x ∈ R, d * x * d⁻¹ * x⁻¹ ∈ L :=
            fun d hd x hx => hcen d (hD1H hd) x hx
          have hcop : Nat.Coprime (Nat.card D1) (Nat.card R) := by
            obtain ⟨j, hj⟩ := hR2.exists_card_eq
            rw [hj]
            exact Nat.Coprime.pow_right j (Odd.coprime_two_right hD1odd)
          have hsupD : (R ⊓ Subgroup.centralizer (D1 : Set G)) ⊔ L = R := by
            refine le_antisymm (sup_le inf_le_left hLR.le) ?_
            intro x hx
            exact (CFSG.GroupTheory.CoprimeSection.mem_centralizer_sup_iff
              hLR.le hRNL hD1NR hD1NL hcop hsolvR hx).mp (hcenL · · x hx)
          have hcentz : ∀ δ : G, Subgroup.centralizer (Subgroup.zpowers δ : Set G) =
              Subgroup.centralizer ({δ} : Set G) := fun δ => by
            rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
          have hsupδ : ∀ δ ∈ D1, δ ≠ 1 →
              (R ⊓ Subgroup.centralizer ({δ} : Set G)) ⊔ L = R := by
            intro δ hδ _
            have hzle : Subgroup.zpowers δ ≤ D1 := Subgroup.zpowers_le.mpr hδ
            have hcopz : Nat.Coprime (Nat.card (Subgroup.zpowers δ)) (Nat.card R) := by
              rw [Nat.card_zpowers]
              obtain ⟨j, hj⟩ := hR2.exists_card_eq
              rw [hj]
              exact Nat.Coprime.pow_right j
                (Odd.coprime_two_right
                  (Odd.of_dvd_nat hD1odd (Subgroup.orderOf_dvd_natCard D1 hδ)))
            have hsupz : (R ⊓ Subgroup.centralizer (Subgroup.zpowers δ : Set G)) ⊔ L = R := by
              refine le_antisymm (sup_le inf_le_left hLR.le) ?_
              intro x hx
              exact (CFSG.GroupTheory.CoprimeSection.mem_centralizer_sup_iff
                hLR.le hRNL (hzle.trans hD1NR) (hzle.trans hD1NL) hcopz hsolvR hx).mp
                (fun d hd => hcenL d (hzle hd) x hx)
            rwa [hcentz δ] at hsupz
          have hidxD : (R ⊓ Subgroup.centralizer (D1 : Set G)).relIndex R =
              (L ⊓ Subgroup.centralizer (D1 : Set G)).relIndex L := by
            have h := CFSG.GroupTheory.CoprimeSection.index_centralizer_mul
              (D := D1) (N := R) (M := L) hLR.le hRNL
            rwa [hsupD, Subgroup.relIndex_self, mul_one] at h
          have hidxδ : ∀ δ ∈ D1, δ ≠ 1 →
              (R ⊓ Subgroup.centralizer ({δ} : Set G)).relIndex R =
                (L ⊓ Subgroup.centralizer ({δ} : Set G)).relIndex L := by
            intro δ hδ hδ1
            have h := CFSG.GroupTheory.CoprimeSection.index_centralizer_mul
              (D := Subgroup.zpowers δ) (N := R) (M := L) hLR.le hRNL
            rw [hcentz δ] at h
            rw [hsupδ δ hδ hδ1, Subgroup.relIndex_self, mul_one] at h
            exact h
          refine ⟨?_, ?_⟩
          · obtain ⟨k, hk⟩ := hIH.1
            exact ⟨k, by rw [hidxD, hk]⟩
          · intro δ hδ hδ1
            have hIHeq := hIH.2 δ hδ hδ1
            have hidxeq : (R ⊓ Subgroup.centralizer (D1 : Set G)).relIndex R =
                (R ⊓ Subgroup.centralizer ({δ} : Set G)).relIndex R := by
              calc (R ⊓ Subgroup.centralizer (D1 : Set G)).relIndex R
                  = (L ⊓ Subgroup.centralizer (D1 : Set G)).relIndex L := hidxD
                _ = (L ⊓ Subgroup.centralizer ({δ} : Set G)).relIndex L := by rw [hIHeq]
                _ = (R ⊓ Subgroup.centralizer ({δ} : Set G)).relIndex R :=
                  (hidxδ δ hδ hδ1).symm
            have hle : R ⊓ Subgroup.centralizer (D1 : Set G) ≤
                R ⊓ Subgroup.centralizer ({δ} : Set G) :=
              inf_le_inf_left R (Subgroup.centralizer_le (by
                intro x hx
                rw [Set.mem_singleton_iff] at hx
                rw [hx]
                exact hδ))
            have hcardeq : Nat.card ↥(R ⊓ Subgroup.centralizer (D1 : Set G)) =
                Nat.card ↥(R ⊓ Subgroup.centralizer ({δ} : Set G)) := by
              have h1 := Subgroup.relIndex_mul_card (R ⊓ Subgroup.centralizer (D1 : Set G)) R
              have h2 := Subgroup.relIndex_mul_card (R ⊓ Subgroup.centralizer ({δ} : Set G)) R
              rw [inf_eq_left.mpr inf_le_left] at h1 h2
              have hpos : (R ⊓ Subgroup.centralizer (D1 : Set G)).relIndex R ≠ 0 :=
                ne_zero_of_dvd_ne_zero Nat.card_pos.ne'
                  (Subgroup.relIndex_dvd_card _ _)
              apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hpos)
              rw [h1, ← h2, hidxeq]
            exact (Subgroup.eq_of_le_of_card_ge
              (H := R ⊓ Subgroup.centralizer (D1 : Set G))
              (K := R ⊓ Subgroup.centralizer ({δ} : Set G)) hle (le_of_eq hcardeq.symm)).symm
        ·
          have hfixmem : ∀ δ ∈ D1, δ ≠ 1 → R ⊓ Subgroup.centralizer ({δ} : Set G) ≤ L := by
            intro δ hδ hδ1 x hx
            have hxR : x ∈ R := hx.1
            have hxc : x ∈ Subgroup.centralizer ({δ} : Set G) := hx.2
            have hcomm : x * δ = δ * x := Subgroup.mem_centralizer_singleton_iff.mp hxc
            have hfix : δ * x * δ⁻¹ * x⁻¹ ∈ L := by
              have hconj : δ * x * δ⁻¹ = x := by
                calc δ * x * δ⁻¹ = x * δ * δ⁻¹ := by rw [← hcomm]
                  _ = x := by simp
              rw [hconj, mul_inv_cancel]
              exact L.one_mem
            exact hfp δ (hD1 hδ)
              (Odd.of_dvd_nat hD1odd (Subgroup.orderOf_dvd_natCard D1 hδ)) hδ1 x hxR hfix
          by_cases hD1bot : D1 = ⊥
          · subst D1
            refine ⟨⟨0, ?_⟩, ?_⟩
            · rw [Subgroup.centralizer_eq_top_iff_subset.mpr (by simp), inf_top_eq,
                Subgroup.relIndex_self]
              simp
            · intro δ hδ hδ1
              exact absurd (Subgroup.mem_bot.mp hδ) hδ1
          · obtain ⟨δ₀, hδ₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hD1bot
            have hδ₀D1 : (δ₀ : G) ∈ D1 := δ₀.2
            have hδ₀1' : (δ₀ : G) ≠ 1 := by
              intro h
              exact hδ₀1 (Subtype.ext h)
            have hCRD_le_L : R ⊓ Subgroup.centralizer (D1 : Set G) ≤ L :=
              (inf_le_inf_left R (Subgroup.centralizer_le (by
                intro x hx
                rw [Set.mem_singleton_iff] at hx
                rw [hx]
                exact hδ₀D1))).trans
                (hfixmem (δ₀ : G) hδ₀D1 hδ₀1')
            refine ⟨?_, ?_⟩
            · obtain ⟨k, hk⟩ := hIH.1
              have hsup : (R ⊓ Subgroup.centralizer (D1 : Set G)) ⊔ L = L :=
                sup_eq_right.mpr hCRD_le_L
              have h := CFSG.GroupTheory.CoprimeSection.index_centralizer_mul
                (D := D1) (N := R) (M := L) hLR.le hRNL
              rw [hsup] at h
              refine ⟨k + 1, ?_⟩
              calc (R ⊓ Subgroup.centralizer (D1 : Set G)).relIndex R
                  = (L ⊓ Subgroup.centralizer (D1 : Set G)).relIndex L *
                      L.relIndex R := h
                _ = 2 ^ (4 * (2 * a + 1) * k) * 2 ^ (4 * (2 * a + 1)) := by rw [hk, hrel]
                _ = 2 ^ (4 * (2 * a + 1) * k + 4 * (2 * a + 1)) := by rw [Nat.pow_add]
                _ = 2 ^ (4 * (2 * a + 1) * (k + 1)) := by congr 1
            · intro δ hδ hδ1
              have hCe : L ⊓ Subgroup.centralizer ({δ} : Set G) =
                  L ⊓ Subgroup.centralizer (D1 : Set G) := hIH.2 δ hδ hδ1
              have hCRδ_le_L : R ⊓ Subgroup.centralizer ({δ} : Set G) ≤ L :=
                hfixmem δ hδ hδ1
              have hcentle : Subgroup.centralizer (D1 : Set G) ≤
                  Subgroup.centralizer ({δ} : Set G) :=
                Subgroup.centralizer_le (by
                  intro x hx
                  rw [Set.mem_singleton_iff] at hx
                  rw [hx]
                  exact hδ)
              refine le_antisymm ?_ ?_
              · intro x hx
                have hxCL : x ∈ L ⊓ Subgroup.centralizer ({δ} : Set G) :=
                  ⟨hCRδ_le_L hx, hx.2⟩
                rw [hCe] at hxCL
                exact ⟨hLR.le hxCL.1, hxCL.2⟩
              · intro x hx
                exact ⟨hx.1, hcentle hx.2⟩
  exact fun R hR => key (Nat.card R) R rfl hR

theorem d1_claim (hF : Hyp111 L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hQ : Nat.card (Q1 L1 L2 S) < 2 ^ (16 * (2 * a + 1)))
    {D1 : Subgroup G} (hD1 : D1 ≤ borelOf L1 S) (hD1odd : Odd (Nat.card D1))
    {R : Subgroup G} (hR : IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) R) :
    (∃ k : ℕ, (R ⊓ Subgroup.centralizer (D1 : Set G)).relIndex R =
        2 ^ (4 * (2 * a + 1) * k)) ∧
      ∀ δ ∈ D1, δ ≠ 1 → R ⊓ Subgroup.centralizer ({δ} : Set G) =
        R ⊓ Subgroup.centralizer (D1 : Set G) :=
  d1_claim_aux hF hB ha hSz hQ hD1 hD1odd R hR

end CFSG.Quasithin.Stroth.G5F

end
