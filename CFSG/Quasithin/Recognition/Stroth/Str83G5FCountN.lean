module

public import CFSG.Quasithin.Recognition.Stroth.Str83G5FCount
public import CFSG.Quasithin.Recognition.Stroth.Str83G5FNOne

import CFSG.GroupTheory.CoprimeSectionStability
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin

public section

namespace CFSG.Quasithin.Stroth.G5F

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.GH74.Uniqueness.Bender CFSG.Blueprint CFSG.LieType.Ree

variable {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G} {a : ℕ}

theorem n1_claim (hF : Hyp111 L1 L2 S)
    (hB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) (ha : 1 ≤ a)
    (hSz : Nonempty (oTwoQuot ↥L1 ≃* Sz a))
    (hQ : Nat.card (Q1 L1 L2 S) < 2 ^ (16 * (2 * a + 1)))
    {D1 N1 : Subgroup G} (hD1 : D1 ≤ borelOf L1 S) (hD1odd : Odd (Nat.card D1))
    (hN1P : N1 ≤ P1 L1 L2 S) (hN1odd : Odd (Nat.card N1))
    (hN1L : ∀ x ∈ N1, ∀ l ∈ L1, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L1)
    (hD1N1 : D1 ≤ Subgroup.normalizer (N1 : Set G))
    {R : Subgroup G} (hR : IsNormalIn (L1 ⊔ S ⊔ N1) (Q1 L1 L2 S) R) :
    ∃ k : ℕ, (R ⊓ Subgroup.centralizer ((D1 ⊔ N1 : Subgroup G) : Set G)).relIndex
        (R ⊓ Subgroup.centralizer (N1 : Set G)) = 2 ^ (4 * (2 * a + 1) * k) := by
  classical
  obtain ⟨-, hQ1S, hLS, -⟩ := sz_vertex (K := GaloisField 2 (2 * a + 1))
    (GaloisField.card 2 (2 * a + 1) (by omega)) hF hB ha hSz
  have hD1L1 : D1 ≤ L1 := hD1.trans (show borelOf L1 S ≤ L1 from inf_le_left)
  have hD1X : D1 ≤ L1 ⊔ S ⊔ N1 := hD1L1.trans (le_sup_left.trans le_sup_left)
  have hN1X : N1 ≤ L1 ⊔ S ⊔ N1 := le_sup_right
  have hAX : D1 ⊔ N1 ≤ L1 ⊔ S ⊔ N1 := sup_le hD1X hN1X
  have hUX : Q1 L1 L2 S ≤ L1 ⊔ S ⊔ N1 := hQ1S.trans (le_sup_right.trans le_sup_left)
  have hcardAA : Nat.card ↥(D1 ⊔ N1) * Nat.card ↥(D1 ⊓ N1) = Nat.card D1 * Nat.card N1 :=
    CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hD1N1
  have hAodd : Odd (Nat.card ↥(D1 ⊔ N1)) :=
    Odd.of_dvd_nat (Nat.odd_mul.mpr ⟨hD1odd, hN1odd⟩) ⟨_, hcardAA.symm⟩
  have hmain : ∀ n : ℕ, ∀ R : Subgroup G, Nat.card R = n →
      IsNormalIn (L1 ⊔ S ⊔ N1) (Q1 L1 L2 S) R →
      ∃ k : ℕ, (R ⊓ Subgroup.centralizer ((D1 ⊔ N1 : Subgroup G) : Set G)).relIndex
        (R ⊓ Subgroup.centralizer (N1 : Set G)) = 2 ^ (4 * (2 * a + 1) * k) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro R hcard hR
      by_cases hbot : R = ⊥
      · subst hbot
        exact ⟨0, by simp [Subgroup.relIndex_bot_right]⟩
      ·
        have hRX : R ≤ L1 ⊔ S ⊔ N1 := hR.1.trans hUX
        have hR2 : IsPGroup 2 R :=
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (P1 L1 L2 S)).to_le hR.1
        have hRsolv : Group.IsSolvable ↥R := by
          haveI : Group.IsNilpotent ↥R := IsPGroup.isNilpotent (p := 2) hR2
          infer_instance
        obtain ⟨m, hm⟩ := hR2.exists_card_eq
        have hcopN1 : Nat.Coprime (Nat.card N1) (Nat.card R) := by
          rw [hm]
          exact Nat.Coprime.pow_right m (Odd.coprime_two_right hN1odd)
        have hcopA : Nat.Coprime (Nat.card ↥(D1 ⊔ N1)) (Nat.card R) := by
          rw [hm]
          exact Nat.Coprime.pow_right m (Odd.coprime_two_right hAodd)
        have hcopD1 : Nat.Coprime (Nat.card D1) (Nat.card R) := by
          rw [hm]
          exact Nat.Coprime.pow_right m (Odd.coprime_two_right hD1odd)
        have hRn : L1 ⊔ S ⊔ N1 ≤ Subgroup.normalizer (R : Set G) :=
          Subgroup.le_normalizer_iff.mpr hR.2
        have hN1R : N1 ≤ Subgroup.normalizer (R : Set G) := hN1X.trans hRn
        have hAR : (D1 ⊔ N1) ≤ Subgroup.normalizer (R : Set G) := hAX.trans hRn
        have hD1R : D1 ≤ Subgroup.normalizer (R : Set G) := hD1X.trans hRn
        let s : Set (Subgroup G) := {K | IsNormalIn (L1 ⊔ S ⊔ N1) (Q1 L1 L2 S) K ∧ K < R}
        have hbotNorm : IsNormalIn (L1 ⊔ S ⊔ N1) (Q1 L1 L2 S) ⊥ :=
          ⟨bot_le, fun g _ x hx => by
            simp only [Subgroup.mem_bot] at hx ⊢
            rw [hx]; simp⟩
        have hsne : s.Nonempty := ⟨⊥, ⟨hbotNorm, bot_lt_iff_ne_bot.mpr hbot⟩⟩
        obtain ⟨L, hL⟩ :=
          (Set.toFinite s).exists_maximalFor (fun K : Subgroup G => Nat.card K) s hsne
        have hLN : IsNormalIn (L1 ⊔ S ⊔ N1) (Q1 L1 L2 S) L := hL.1.1
        have hLRlt : L < R := hL.1.2
        have hLR : L ≤ R := hLRlt.le
        have hstep : IsChiefStep (L1 ⊔ S ⊔ N1) (Q1 L1 L2 S) L R := by
          refine ⟨hR, hLN, hLRlt, ?_⟩
          intro K hK hLK hKR
          by_cases hKR' : K = R
          · exact Or.inr hKR'
          · left
            have hKlt : K < R := lt_of_le_of_ne hKR hKR'
            have hcardK : Nat.card K ≤ Nat.card L := hL.le ⟨hK, hKlt⟩
            exact (Subgroup.eq_of_le_of_card_ge hLK hcardK).symm
        have hLS_le : L1 ⊔ S ≤ L1 ⊔ S ⊔ N1 := le_sup_left
        have hR' : IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) R :=
          ⟨hR.1, fun g hg x hx => hR.2 g (hLS_le hg) x hx⟩
        have hL' : IsNormalIn (L1 ⊔ S) (Q1 L1 L2 S) L :=
          ⟨hLN.1, fun g hg x hx => hLN.2 g (hLS_le hg) x hx⟩
        have hLlt : Nat.card L < n := by
          rw [← hcard]
          exact Subgroup.card_lt_of_lt hLRlt
        obtain ⟨kIH, hkIH⟩ := ih (Nat.card L) hLlt L rfl hLN
        have hLn : L1 ⊔ S ⊔ N1 ≤ Subgroup.normalizer (L : Set G) :=
          Subgroup.le_normalizer_iff.mpr hLN.2
        have hRLnorm : R ≤ Subgroup.normalizer (L : Set G) := hRX.trans hLn
        have hN1Ln : N1 ≤ Subgroup.normalizer (L : Set G) := hN1X.trans hLn
        have hALn : (D1 ⊔ N1) ≤ Subgroup.normalizer (L : Set G) := hAX.trans hLn
        have hD1Ln : D1 ≤ Subgroup.normalizer (L : Set G) := hD1X.trans hLn
        rcases n1_chief_dichotomy hF hLS hN1P hN1L hstep with hcent | hfpf
        ·
          have hCNsup_full : (R ⊓ Subgroup.centralizer (N1 : Set G)) ⊔ L = R := by
            refine le_antisymm (sup_le inf_le_left hLR) ?_
            intro r hr
            exact (CFSG.GroupTheory.CoprimeSection.mem_centralizer_sup_iff
              (D := N1) (N := R) (M := L) hLR hRLnorm hN1R hN1Ln hcopN1 hRsolv hr).mp
              (fun x hx => hcent x hx r hr)
          have hcondA : ∀ r ∈ R,
              (∀ a ∈ (D1 ⊔ N1 : Subgroup G), a * r * a⁻¹ * r⁻¹ ∈ L) ↔
              (∀ d ∈ D1, d * r * d⁻¹ * r⁻¹ ∈ L) := by
            intro r hr
            constructor
            · intro h d hd
              exact h d (Subgroup.mem_sup_left hd)
            · intro h a ha
              have ha' : a ∈ (↑(D1 ⊔ N1) : Set G) := ha
              rw [Subgroup.coe_mul_of_left_le_normalizer_right D1 N1 hD1N1] at ha'
              obtain ⟨d, hd, x, hx, hdx⟩ := ha'
              rw [← hdx]
              have hxL : x * r * x⁻¹ * r⁻¹ ∈ L := hcent x hx r hr
              have hdL : d * r * d⁻¹ * r⁻¹ ∈ L := h d hd
              have hconj : d * (x * r * x⁻¹ * r⁻¹) * d⁻¹ ∈ L :=
                (Subgroup.mem_normalizer_iff.mp (hD1Ln hd) _).mp hxL
              have e : d * x * r * (d * x)⁻¹ * r⁻¹ =
                  (d * (x * r * x⁻¹ * r⁻¹) * d⁻¹) * (d * r * d⁻¹ * r⁻¹) := by group
              rw [e]
              exact L.mul_mem hconj hdL
          have hCAsup_full :
              (R ⊓ Subgroup.centralizer ((D1 ⊔ N1 : Subgroup G) : Set G)) ⊔ L =
                (R ⊓ Subgroup.centralizer (D1 : Set G)) ⊔ L := by
            refine le_antisymm ?_ ?_
            · intro r hr
              have hrR : r ∈ R := (sup_le inf_le_left hLR) hr
              have hcond := (CFSG.GroupTheory.CoprimeSection.mem_centralizer_sup_iff
                (D := D1 ⊔ N1) (N := R) (M := L) hLR hRLnorm hAR hALn hcopA hRsolv hrR).mpr hr
              exact (CFSG.GroupTheory.CoprimeSection.mem_centralizer_sup_iff
                (D := D1) (N := R) (M := L) hLR hRLnorm hD1R hD1Ln hcopD1 hRsolv hrR).mp
                ((hcondA r hrR).mp hcond)
            · intro r hr
              have hrR : r ∈ R := (sup_le inf_le_left hLR) hr
              have hcond := (CFSG.GroupTheory.CoprimeSection.mem_centralizer_sup_iff
                (D := D1) (N := R) (M := L) hLR hRLnorm hD1R hD1Ln hcopD1 hRsolv hrR).mpr hr
              exact (CFSG.GroupTheory.CoprimeSection.mem_centralizer_sup_iff
                (D := D1 ⊔ N1) (N := R) (M := L) hLR hRLnorm hAR hALn hcopA hRsolv hrR).mp
                ((hcondA r hrR).mpr hcond)
          have hcardN1_full : Nat.card R *
                Nat.card ↥(L ⊓ Subgroup.centralizer (N1 : Set G)) =
              Nat.card ↥(R ⊓ Subgroup.centralizer (N1 : Set G)) * Nat.card L := by
            have h := CFSG.GroupTheory.CoprimeSection.card_centralizer_section
              (D := N1) (N := R) (M := L) hLR hRLnorm
            rw [hCNsup_full] at h
            exact h
          have hcardA_full :
              Nat.card ↥((R ⊓ Subgroup.centralizer (D1 : Set G)) ⊔ L) *
                Nat.card ↥(L ⊓ Subgroup.centralizer ((D1 ⊔ N1 : Subgroup G) : Set G)) =
              Nat.card ↥(R ⊓ Subgroup.centralizer ((D1 ⊔ N1 : Subgroup G) : Set G)) *
                Nat.card L := by
            have h := CFSG.GroupTheory.CoprimeSection.card_centralizer_section
              (D := D1 ⊔ N1) (N := R) (M := L) hLR hRLnorm
            rw [hCAsup_full] at h
            exact h
          set CN : Subgroup G := R ⊓ Subgroup.centralizer (N1 : Set G) with hCN
          set CA : Subgroup G :=
            R ⊓ Subgroup.centralizer ((D1 ⊔ N1 : Subgroup G) : Set G) with hCA
          set CD : Subgroup G := R ⊓ Subgroup.centralizer (D1 : Set G) with hCD
          set cN : Subgroup G := L ⊓ Subgroup.centralizer (N1 : Set G) with hcN
          set cA : Subgroup G :=
            L ⊓ Subgroup.centralizer ((D1 ⊔ N1 : Subgroup G) : Set G) with hcA
          set cD : Subgroup G := L ⊓ Subgroup.centralizer (D1 : Set G) with hcD
          set Y : Subgroup G := CD ⊔ L with hY
          have hCNsup : CN ⊔ L = R := by
            simpa only [hCN] using hCNsup_full
          have hcardN1 : Nat.card R * Nat.card cN = Nat.card CN * Nat.card L := by
            simpa only [hCN, hcN] using hcardN1_full
          have hcardA : Nat.card Y * Nat.card cA = Nat.card CA * Nat.card L := by
            simpa only [hY, hCD, hCA, hcA] using hcardA_full
          have hCA_le_CN : CA ≤ CN := by
            intro x hx
            exact ⟨hx.1, Subgroup.centralizer_le (s := (N1 : Set G))
              (t := ((D1 ⊔ N1 : Subgroup G) : Set G))
              (fun y hy => Subgroup.mem_sup_right hy) hx.2⟩
          have hcA_le_cN : cA ≤ cN := by
            intro x hx
            exact ⟨hx.1, Subgroup.centralizer_le (s := (N1 : Set G))
              (t := ((D1 ⊔ N1 : Subgroup G) : Set G))
              (fun y hy => Subgroup.mem_sup_right hy) hx.2⟩
          have hY_le_R : Y ≤ R := by
            rw [hY]
            exact sup_le (hCD.le.trans inf_le_left) hLR
          have hrelCA : CA.relIndex CN * Nat.card CA = Nat.card CN := by
            have h := Subgroup.relIndex_mul_card (H := CA) (K := CN)
            rwa [inf_eq_left.mpr hCA_le_CN] at h
          have hrelcA : cA.relIndex cN * Nat.card cA = Nat.card cN := by
            have h := Subgroup.relIndex_mul_card (H := cA) (K := cN)
            rwa [inf_eq_left.mpr hcA_le_cN] at h
          have hrelY : Y.relIndex R * Nat.card Y = Nat.card R := by
            have h := Subgroup.relIndex_mul_card (H := Y) (K := R)
            rwa [inf_eq_left.mpr hY_le_R] at h
          have hkey : Nat.card CN * Nat.card cA * Nat.card Y =
              Nat.card CA * Nat.card cN * Nat.card R := by
            have h1 : Nat.card CN * Nat.card L = Nat.card R * Nat.card cN := hcardN1.symm
            have h2 : Nat.card cA * Nat.card Y = Nat.card CA * Nat.card L := by
              rw [mul_comm]
              exact hcardA
            calc
              Nat.card CN * Nat.card cA * Nat.card Y
                  = Nat.card CN * (Nat.card cA * Nat.card Y) := by ring
              _ = Nat.card CN * (Nat.card CA * Nat.card L) := by rw [h2]
              _ = Nat.card CA * (Nat.card CN * Nat.card L) := by ring
              _ = Nat.card CA * (Nat.card R * Nat.card cN) := by rw [h1]
              _ = Nat.card CA * Nat.card cN * Nat.card R := by ring
          have hfactor_pos : 0 < Nat.card CA * Nat.card cA * Nat.card Y := by
            exact Nat.mul_pos (Nat.mul_pos Nat.card_pos Nat.card_pos) Nat.card_pos
          have hcount : CA.relIndex CN = cA.relIndex cN * Y.relIndex R := by
            have hLHS : CA.relIndex CN * (Nat.card CA * Nat.card cA * Nat.card Y) =
                Nat.card CN * Nat.card cA * Nat.card Y := by
              calc
                CA.relIndex CN * (Nat.card CA * Nat.card cA * Nat.card Y)
                    = (CA.relIndex CN * Nat.card CA) *
                        (Nat.card cA * Nat.card Y) := by ring
                _ = Nat.card CN * (Nat.card cA * Nat.card Y) := by rw [hrelCA]
                _ = Nat.card CN * Nat.card cA * Nat.card Y := by ring
            have hRHS : (cA.relIndex cN * Y.relIndex R) *
                  (Nat.card CA * Nat.card cA * Nat.card Y) =
                Nat.card CN * Nat.card cA * Nat.card Y := by
              calc
                (cA.relIndex cN * Y.relIndex R) *
                    (Nat.card CA * Nat.card cA * Nat.card Y)
                    = Nat.card CA * (cA.relIndex cN * Nat.card cA) *
                        (Y.relIndex R * Nat.card Y) := by ring
                _ = Nat.card CA * Nat.card cN * Nat.card R := by rw [hrelcA, hrelY]
                _ = Nat.card CN * Nat.card cA * Nat.card Y := hkey.symm
            exact Nat.mul_right_cancel hfactor_pos (hLHS.trans hRHS.symm)
          obtain ⟨kR, hkR⟩ := (d1_claim (D1 := D1) (R := R)
            hF hB ha hSz hQ hD1 hD1odd hR').1
          have hkR' : CD.relIndex R = 2 ^ (4 * (2 * a + 1) * kR) := by
            simpa only [hCD] using hkR
          obtain ⟨kL, hkL⟩ := (d1_claim (D1 := D1) (R := L)
            hF hB ha hSz hQ hD1 hD1odd hL').1
          have hkL' : cD.relIndex L = 2 ^ (4 * (2 * a + 1) * kL) := by
            simpa only [hcD] using hkL
          have hidx : CD.relIndex R = cD.relIndex L * Y.relIndex R := by
            have h := CFSG.GroupTheory.CoprimeSection.index_centralizer_mul
              (D := D1) (N := R) (M := L) hLR hRLnorm
            rwa [← hCD, ← hcD, ← hY] at h
          have hpowrel : 2 ^ (4 * (2 * a + 1) * kR) =
              2 ^ (4 * (2 * a + 1) * kL) * Y.relIndex R := by
            rw [← hkR', hidx, hkL']
          have hYrel : Y.relIndex R = 2 ^ (4 * (2 * a + 1) * (kR - kL)) := by
            have hdvd : 2 ^ (4 * (2 * a + 1) * kL) ∣ 2 ^ (4 * (2 * a + 1) * kR) :=
              ⟨Y.relIndex R, hpowrel⟩
            have hle : 4 * (2 * a + 1) * kL ≤ 4 * (2 * a + 1) * kR :=
              (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 2)).mp hdvd
            have hpos : 2 ^ (4 * (2 * a + 1) * kL) ≠ 0 :=
              (pow_pos (by norm_num : (0 : ℕ) < 2) _).ne'
            have hdiv : Y.relIndex R =
                2 ^ (4 * (2 * a + 1) * kR) / 2 ^ (4 * (2 * a + 1) * kL) :=
              Nat.eq_div_of_mul_eq_right hpos hpowrel.symm
            rw [hdiv, Nat.pow_div hle (by norm_num : (0 : ℕ) < 2),
              ← Nat.mul_sub_left_distrib]
          have hkIH' : cA.relIndex cN = 2 ^ (4 * (2 * a + 1) * kIH) := by
            simpa only [hcA, hcN] using hkIH
          refine ⟨kIH + (kR - kL), ?_⟩
          rw [hcount, hkIH', hYrel, ← pow_add]
          congr 1
          ring
        ·
          have hCN_le_L : R ⊓ Subgroup.centralizer (N1 : Set G) ≤ L := by
            intro r hr
            refine hfpf r hr.1 ?_
            intro x hx
            have hcomm : x * r = r * x := (Subgroup.mem_centralizer_iff.mp hr.2) x hx
            have h1 : x * r * x⁻¹ * r⁻¹ = 1 := by
              rw [hcomm]
              group
            rw [h1]
            exact L.one_mem
          have hCAsub : Subgroup.centralizer ((D1 ⊔ N1 : Subgroup G) : Set G) ≤
              Subgroup.centralizer (N1 : Set G) :=
            Subgroup.centralizer_le (s := (N1 : Set G))
              (t := ((D1 ⊔ N1 : Subgroup G) : Set G))
              (fun y hy => Subgroup.mem_sup_right hy)
          have hCN_eq : R ⊓ Subgroup.centralizer (N1 : Set G) =
              L ⊓ Subgroup.centralizer (N1 : Set G) := by
            refine le_antisymm ?_ ?_
            · intro r hr
              exact ⟨hCN_le_L hr, hr.2⟩
            · intro r hr
              exact ⟨hLR hr.1, hr.2⟩
          have hCA_eq : R ⊓ Subgroup.centralizer ((D1 ⊔ N1 : Subgroup G) : Set G) =
              L ⊓ Subgroup.centralizer ((D1 ⊔ N1 : Subgroup G) : Set G) := by
            refine le_antisymm ?_ ?_
            · intro r hr
              exact ⟨hCN_le_L ⟨hr.1, hCAsub hr.2⟩, hr.2⟩
            · intro r hr
              exact ⟨hLR hr.1, hr.2⟩
          exact ⟨kIH, by rw [hCA_eq, hCN_eq]; exact hkIH⟩
  exact hmain (Nat.card R) R rfl hR

end CFSG.Quasithin.Stroth.G5F

end
