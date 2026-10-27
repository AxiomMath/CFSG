module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ro
public import CFSG.LocalAnalysis.UniquenessCase.UC22K108H207

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22p22rS_sup_img_eq_top {K B : Subgroup G} (hBK : B ≤ normalizer (K : Set G)) :
    uc22p22rS K B hBK ⊔ uc22p22rImg hBK B = ⊤ := by
  rw [eq_top_iff]
  intro g _
  obtain ⟨γ, rfl⟩ := uc22p22rPi_surjective hBK g
  obtain ⟨k, hk, b, hb, hkb⟩ : (γ : G) ∈ (K : Set G) * (B : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left K B hBK, SetLike.mem_coe]
    exact γ.2
  have hkN : k ∈ K ⊔ B := Subgroup.mem_sup_left hk
  have hbN : b ∈ K ⊔ B := Subgroup.mem_sup_right hb
  rw [show γ = ⟨k, hkN⟩ * ⟨b, hbN⟩ from Subtype.ext hkb.symm, map_mul]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (uc22p22rPi_mem_S hBK ⟨k, hkN⟩ hk))
    (Subgroup.mem_sup_right ((uc22p22r_mem_img hBK).2 ⟨⟨b, hbN⟩, hb, rfl⟩))

theorem uc22p22r_le_of_k108H207_hall (hK : F10.K108H207) {K B T' M : Subgroup G} {x : G} {q : ℕ} (hq : q.Prime)
    (hq2 : q ≠ 2) (hxo : orderOf x = q) (hxB : x ∈ B)
    (hBK : B ≤ normalizer (K : Set G)) (hBc : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a) (hBo : Odd (Nat.card B))
    (hBr : ∀ r : ℕ, r.Prime → r ∣ Nat.card B → CFSG.Open.pRank r B ≤ 2)
    (hKq : CFSG.Open.IsQuasisimple (Bar2 K)) (hshape : F10.IsList207 (uc22p22rKt K))
    (hT' : CFSG.ABGLocalTools.IsSylowOf 2 T' K) (hperm : Permutes B T')
    (hT'M : T' ≤ M) (hBM : B ≤ M) (hO2 : pCoreOf 2 K ≤ M)
    (hZ : ∀ k : ↥K, uc22p22rPsi K k = 1 → (k : G) ∈ M)
    (h0 : ∀ Y : Subgroup G, Subgroup.zpowers x ≤ Y → Y ≤ M → ∀ n ∈ K ⊔ B, n ∈ normalizer (Y : Set G) →
      n ∈ M)
    (hstar : ∀ g ∈ K ⊔ B, (∀ y ∈ Subgroup.zpowers x, g⁻¹ * y * g ∈ M) → g ∈ M) : K ≤ M := by
  by_contra hKM
  have hxq : x ^ q = 1 := hxo ▸ pow_orderOf_eq_one x
  set X : Subgroup G := Subgroup.zpowers x with hXdef
  have hXB : X ≤ B := Subgroup.zpowers_le.2 hxB
  have hXq : Nat.card X = q := by rw [hXdef, Nat.card_zpowers, hxo]
  have hxM : x ∈ M := hBM hxB
  haveI hSn : (uc22p22rS K B hBK).Normal := uc22p22rS_normal hBK
  have h0B : ∀ Y : Subgroup G, B ≤ Y → Y ≤ M → ∀ n ∈ K ⊔ B, n ∈ normalizer (Y : Set G) → n ∈ M :=
    fun Y hBY hYM n hn hnY => h0 Y (hXB.trans hBY) hYM n hn hnY
  have hker : ∀ n : ↥(K ⊔ B), uc22p22rPi K B hBK n = 1 → (n : G) ∈ M := fun n hn =>
    uc22p22r_ker_le hBK hBc hKq hBM hZ h0B n ((uc22p22rPi_eq_one_iff hBK n).1 hn)
  have hxN : x ∈ K ⊔ B := Subgroup.mem_sup_right hxB
  have hρ1 := uc22p22r_rho_ne_one_of_le hBK hq hq2 hxB hxq hKq hO2 h0 hxM hKM
  have hXcard : Nat.card (uc22p22rImg hBK X) = q := by
    have hdvd : Nat.card (uc22p22rImg hBK X) ∣ q := by
      have h1 : Nat.card (uc22p22rImg hBK X) ∣ Nat.card (X.subgroupOf (K ⊔ B)) := by
        rw [uc22p22rImg_eq_map]
        exact Subgroup.card_map_dvd _ _
      have h2 : Nat.card (X.subgroupOf (K ⊔ B)) = q := by
        rw [← hXq]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hXB.trans le_sup_right)).toEquiv
      rwa [h2] at h1
    rcases (Nat.dvd_prime hq).1 hdvd with h | h
    · exfalso
      have hone : uc22p22rPi K B hBK ⟨x, hxN⟩ ∈ uc22p22rImg hBK X :=
        (uc22p22r_mem_img hBK).2 ⟨⟨x, hxN⟩, Subgroup.mem_zpowers x, rfl⟩
      have hsub : Subsingleton (uc22p22rImg hBK X) := Nat.card_eq_one_iff_unique.1 h |>.1
      have h2 : uc22p22rPi K B hBK ⟨x, hxN⟩ = 1 := by
        have := Subsingleton.elim (⟨_, hone⟩ : uc22p22rImg hBK X) 1
        exact congrArg Subtype.val this
      exact hρ1 ((uc22p22rPi_eq_one_iff hBK _).1 h2)
    · exact h
  have hshape' : F10.IsList207 ↥(uc22p22rS K B hBK) := hshape.of_mulEquiv (uc22p22rSEquiv hBK hKq)
  have hdvdB : Nat.card (uc22p22rImg hBK B) ∣ Nat.card B := by
    rw [uc22p22rImg_eq_map]
    refine (Subgroup.card_map_dvd _ _).trans (dvd_of_eq ?_)
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have hBh : F10.Hyp10 (uc22p22rImg hBK T') (uc22p22rImg hBK B) := by
    refine ⟨uc22p22r_sylow_img_odd hBK hBo hT', ?_, hBo.of_dvd_nat hdvdB,
      uc22p22r_permutes_img hBK hT'.le hperm, ?_⟩
    · refine ⟨⟨fun a b => ?_⟩⟩
      obtain ⟨n₁, hn₁, h₁⟩ := (uc22p22r_mem_img hBK).1 a.2
      obtain ⟨n₂, hn₂, h₂⟩ := (uc22p22r_mem_img hBK).1 b.2
      apply Subtype.ext
      show (a : uc22p22rGh K B hBK) * b = b * a
      rw [← h₁, ← h₂, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hBc _ hn₁ _ hn₂)
    · intro r hr hrd
      have h1 : CFSG.Open.pRank r (uc22p22rImg hBK B) ≤ CFSG.Open.pRank r (B.subgroupOf (K ⊔ B)) := by
        rw [uc22p22rImg_eq_map]
        exact uc22p22r_pRank_map_le hr (uc22p22rPi K B hBK) (fun a ha b hb => Subtype.ext (hBc _ ha _ hb))
      have h2 : CFSG.Open.pRank r (B.subgroupOf (K ⊔ B)) ≤ CFSG.Open.pRank r B := by
        have h3 := CFSG.SectionRank.pRank_le_map hr.one_lt (K ⊔ B).subtype (K ⊔ B).subtype_injective
          (B.subgroupOf (K ⊔ B))
        rwa [Subgroup.map_subgroupOf_eq_of_le le_sup_right] at h3
      exact h1.trans (h2.trans (hBr r hr (hrd.trans hdvdB)))
  have hM : uc22p22rS K B hBK ≤ uc22p22rImg hBK M :=
    hK (uc22p22rGh K B hBK) _ hSn (uc22p22rS_simple hBK hKq) (uc22p22rS_nonab hBK hKq)
      (uc22p22rS_centralizer hBK hKq) hshape' _ _ hBh (uc22p22rS_sup_img_eq_top hBK) _ _ (uc22p22r_img_mono hBK hXB)
      (hXcard ▸ hq) (hXcard ▸ hq.odd_of_ne_two hq2)
      (uc22p22r_img_mono hBK hT'M) (uc22p22r_img_mono hBK (hXB.trans hBM)) (by
        intro ĝ hĝ
        obtain ⟨γ, rfl⟩ := uc22p22rPi_surjective hBK ĝ
        have hγM : (γ : G) ∈ M := by
          apply hstar (γ : G) γ.2
          intro y hy
          have hyN : y ∈ K ⊔ B := Subgroup.mem_sup_right (hXB hy)
          have h1 := hĝ (uc22p22rPi K B hBK ⟨y, hyN⟩)
            ((uc22p22r_mem_img hBK).2 ⟨⟨y, hyN⟩, hy, rfl⟩)
          obtain ⟨m, hmM, hmπ⟩ := (uc22p22r_mem_img hBK).1 h1
          have h2 : uc22p22rPi K B hBK (m⁻¹ * (γ⁻¹ * ⟨y, hyN⟩ * γ)) = 1 := by
            simp only [map_mul, map_inv, hmπ]
            group
          have h3 := hker _ h2
          have h4 : (γ : G)⁻¹ * y * γ = (m : G) * ((m : G)⁻¹ * ((γ : G)⁻¹ * y * γ)) := by group
          rw [h4]
          exact M.mul_mem hmM (by simpa using h3)
        exact (uc22p22r_mem_img hBK).2 ⟨γ, hγM, rfl⟩)
  apply hKM
  intro k hk
  have hkN : k ∈ K ⊔ B := Subgroup.mem_sup_left hk
  have hmem : uc22p22rPi K B hBK ⟨k, hkN⟩ ∈ uc22p22rImg hBK M :=
    hM (uc22p22rPi_mem_S hBK ⟨k, hkN⟩ hk)
  obtain ⟨m, hmM, hmπ⟩ := (uc22p22r_mem_img hBK).1 hmem
  have h1 : uc22p22rPi K B hBK (m⁻¹ * ⟨k, hkN⟩) = 1 := by
    rw [map_mul, map_inv, hmπ, inv_mul_cancel]
  have h2 := hker _ h1
  have h3 : k = (m : G) * ((m : G)⁻¹ * k) := by group
  rw [h3]
  exact M.mul_mem hmM (by simpa using h2)

end CFSG.LocalAnalysis.UniquenessCase.UC22
