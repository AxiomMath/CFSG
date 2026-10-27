module

public import CFSG.Milestones.ASVolI.B610.FamD

public section

namespace CFSG.Quasithin.B610T

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G]

namespace burnsideB610_Fam

variable {H T V : Subgroup G} {hV : IsElemAbelian 2 V} {F : Type} [Field F] {ι : Type}
  {S : Finset ι} {X : ι → Subgroup G} {D : ∀ i, NatData (X i) V F}

theorem exists_offender_at [Finite G] {M : Subgroup G} (hFam : burnsideB610_Fam H T V hV F S X D)
    (hMP : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) {i : ι} (hi : i ∈ S) :
    ∃ A : Subgroup G, IsMaxElemAbelian T A ∧
      ¬ A ≤ Subgroup.centralizer ((⁅V, X i⁆ : Subgroup G) : Set G) := by
  have hT := hMP.isSylow
  have hHV : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  obtain ⟨A₀, hA₀, hA₀V⟩ : ∃ A₀, IsMaxElemAbelian T A₀ ∧
      ¬ A₀ ≤ Subgroup.centralizer (V : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hJ (iSup₂_le fun A hA => hcon A hA)
  obtain ⟨j, hj, hjA⟩ : ∃ j ∈ S, ¬ A₀ ≤ Subgroup.centralizer ((⁅V, X j⁆ : Subgroup G) : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hA₀V fun a ha => hFam.faith hred (hT.1 (hA₀.1 ha)) fun j hj => hcon j hj ha
  obtain ⟨t, ht, htj⟩ := hFam.orbitT hMP hj hi
  refine ⟨cjSub t A₀, isMaxElemAbelian_cjSub (Subgroup.le_normalizer ht) hA₀, fun hle => hjA ?_⟩
  have htV : t ∈ Subgroup.normalizer (V : Set G) := hHV (hT.1 ht)
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have h1 : t * a * t⁻¹ ∈ cjSub t A₀ := by
    rw [mem_cjSub]
    simpa [mul_assoc] using ha
  have h2 : t * w * t⁻¹ ∈ ⁅V, X i⁆ := by
    rw [← htj, burnsideB610_commutator_cjSub htV, mem_cjSub]
    simpa [mul_assoc] using hw
  have h3 := Subgroup.mem_centralizer_iff.mp (hle h1) _ h2
  have h4 : t * (w * a) * t⁻¹ = t * (a * w) * t⁻¹ := by
    calc t * (w * a) * t⁻¹ = (t * w * t⁻¹) * (t * a * t⁻¹) := by group
      _ = (t * a * t⁻¹) * (t * w * t⁻¹) := h3
      _ = t * (a * w) * t⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel h4)

theorem exists_pieces [Finite G] [Fintype F] [CharP F 2] [DecidableEq ι] {M : Subgroup G}
    {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) (hFam : burnsideB610_Fam H T V hV F S X D)
    (hMP : MinParabolic H T M) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) :
    ∃ Bf : ι → Subgroup G, ∀ i ∈ S, Bf i ≤ thompsonJ T ∧ Bf i ≤ X i ∧
      (∀ j ∈ S, j ≠ i → Bf i ≤ Subgroup.centralizer ((⁅V, X j⁆ : Subgroup G) : Set G)) ∧
      Nat.card ((D i).img (Bf i)) = 2 ^ n ∧
      rk ↥V ≤ rk ↥(V ⊓ Subgroup.centralizer (Bf i : Set G)) + n := by
  have key : ∀ i : ι, ∃ B : Subgroup G, i ∈ S → (B ≤ thompsonJ T ∧ B ≤ X i ∧
      (∀ j ∈ S, j ≠ i → B ≤ Subgroup.centralizer ((⁅V, X j⁆ : Subgroup G) : Set G)) ∧
      Nat.card ((D i).img B) = 2 ^ n ∧
      rk ↥V ≤ rk ↥(V ⊓ Subgroup.centralizer (B : Set G)) + n) := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨A, hA, hAi⟩ := hFam.exists_offender_at hMP hred hJ hi
      obtain ⟨B, hBA, hBX, hBc, hBq, hBr⟩ :=
        hFam.exists_piece hn hF hred hMP.isSylow hA hi hAi
      exact ⟨B, fun _ => ⟨hBA.trans (le_iSup₂_of_le A hA le_rfl), hBX, hBc, hBq, hBr⟩⟩
    · exact ⟨⊥, fun h => absurd h hi⟩
  choose Bf hBf using key
  exact ⟨Bf, fun i hi => hBf i hi⟩

theorem exists_mem_iSup_mul_inv [DecidableEq ι] (hFam : burnsideB610_Fam H T V hV F S X D)
    (hHV : H ≤ Subgroup.normalizer (V : Set G)) (Bf : ι → Subgroup G)
    (hBX : ∀ i ∈ S, Bf i ≤ X i)
    (hBc : ∀ i ∈ S, ∀ j ∈ S, j ≠ i →
      Bf i ≤ Subgroup.centralizer ((⁅V, X j⁆ : Subgroup G) : Set G)) {g : G}
    (hg : ∀ i ∈ S, ∃ b ∈ Bf i, g * b⁻¹ ∈ Subgroup.centralizer ((⁅V, X i⁆ : Subgroup G) : Set G)) :
    ∀ 𝒮 : Finset ι, 𝒮 ⊆ S → ∃ b ∈ ⨆ i ∈ 𝒮, Bf i,
      ∀ i ∈ 𝒮, g * b⁻¹ ∈ Subgroup.centralizer ((⁅V, X i⁆ : Subgroup G) : Set G) := by
  intro 𝒮
  induction 𝒮 using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨1, Subgroup.one_mem _, fun i hi => (Finset.notMem_empty i hi).elim⟩
  | insert Y 𝒮' hY ih =>
    intro hsub
    have hYS : Y ∈ S := hsub (Finset.mem_insert_self Y 𝒮')
    have h𝒮' : 𝒮' ⊆ S := fun i hi => hsub (Finset.mem_insert_of_mem hi)
    obtain ⟨b', hb', hb'c⟩ := ih h𝒮'
    obtain ⟨bY, hbY, hbYc⟩ := hg Y hYS
    refine ⟨bY * b', ?_, fun i hi => ?_⟩
    · rw [Finset.iSup_insert]
      exact Subgroup.mul_mem_sup hbY hb'
    · have e : g * (bY * b')⁻¹ = (g * b'⁻¹) * bY⁻¹ := by group
      rcases Finset.mem_insert.mp hi with rfl | hi'
      ·
        have hb'Y : b' ∈ Subgroup.centralizer ((⁅V, X i⁆ : Subgroup G) : Set G) := by
          refine (iSup₂_le fun j hj => ?_ : (⨆ j ∈ 𝒮', Bf j) ≤ _) hb'
          have hji : j ≠ i := fun h => hY (h ▸ hj)
          exact hBc j (h𝒮' hj) i hYS (Ne.symm hji)
        have hbYN : bY ∈ Subgroup.normalizer
            (Subgroup.centralizer ((⁅V, X i⁆ : Subgroup G) : Set G) : Set G) := by
          have h1 : bY ∈ Subgroup.normalizer ((⁅V, X i⁆ : Subgroup G) : Set G) :=
            burnsideB610_le_normalizer_commutator ((hFam.le i hYS).trans hHV)
              (hBX i hYS hbY)
          exact B6.le_normalizer_centralizer (le_refl _) h1
        have h2 : bY * b'⁻¹ * bY⁻¹ ∈ Subgroup.centralizer ((⁅V, X i⁆ : Subgroup G) : Set G) :=
          (Subgroup.mem_normalizer_iff.mp hbYN _).mp (Subgroup.inv_mem _ hb'Y)
        have e2 : g * (bY * b')⁻¹ = (g * bY⁻¹) * (bY * b'⁻¹ * bY⁻¹) := by group
        rw [e2]
        exact Subgroup.mul_mem _ hbYc h2
      · have hiY : i ≠ Y := fun h => hY (h ▸ hi')
        rw [e]
        exact Subgroup.mul_mem _ (hb'c i hi')
          (Subgroup.inv_mem _ (hBc Y hYS i (h𝒮' hi') hiY hbY))

theorem thompsonJ_le_pieces [Finite G] [Fintype F] [CharP F 2] [DecidableEq ι] {n : ℕ}
    (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n) (hFam : burnsideB610_Fam H T V hV F S X D)
    (hred : IsTwoReducedIn H V) (hT : IsSylowTwoOf T H) (Bf : ι → Subgroup G)
    (hBf : ∀ i ∈ S, Bf i ≤ thompsonJ T ∧ Bf i ≤ X i ∧
      (∀ j ∈ S, j ≠ i → Bf i ≤ Subgroup.centralizer ((⁅V, X j⁆ : Subgroup G) : Set G)) ∧
      Nat.card ((D i).img (Bf i)) = 2 ^ n) :
    thompsonJ T ≤ (⨆ i ∈ S, Bf i) ⊔ (H ⊓ Subgroup.centralizer (V : Set G)) := by
  have hHV : H ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := hT.1.trans hHV
  have hJT : thompsonJ T ≤ T := iSup₂_le fun A hA => hA.1
  have hJnLV : ∀ i ∈ S, thompsonJ T ≤ nLV (X i) V := fun i hi x hx =>
    ⟨hFam.thomp i hi hx, hTV (hJT hx)⟩
  have himgJ : ∀ i ∈ S, (D i).img (thompsonJ T) ⊓ CFSG.Quasithin.H.natImage (StatedSL 2 F) ≤
      (D i).img (Bf i) := by
    intro i hi
    obtain ⟨hBJ, hBX, -, hBq⟩ := hBf i hi
    have hXV : X i ≤ Subgroup.normalizer (V : Set G) := (hFam.le i hi).trans hHV
    have hP2 : IsPGroup 2 ((D i).img (thompsonJ T)) := by
      have h1 : IsPGroup 2 ((thompsonJ T).subgroupOf (nLV (X i) V)) :=
        (hT.2.1.to_le hJT).comap_of_injective _ (nLV (X i) V).subtype_injective
      exact h1.map _
    have hBle : (D i).img (Bf i) ≤
        (D i).img (thompsonJ T) ⊓ CFSG.Quasithin.H.natImage (StatedSL 2 F) :=
      le_inf (Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
          (hBJ (Subgroup.mem_subgroupOf.mp hx)))
        (burnsideB610_img_le_natImage_of_le (D i) hXV hBX)
    have hcard := (B42L2.card_le_of_isPGroup (inf_le_right :
      (D i).img (thompsonJ T) ⊓ CFSG.Quasithin.H.natImage (StatedSL 2 F) ≤ _)
      (hP2.to_le inf_le_left) hn (nl2w_card_natImage hF)).1
    exact le_of_eq (Subgroup.eq_of_le_of_card_ge hBle (by rw [hBq]; exact hcard)).symm
  refine iSup₂_le fun A hA => ?_
  by_cases hAV : A ≤ Subgroup.centralizer (V : Set G)
  · exact le_sup_of_le_right (le_inf (hA.1.trans hT.1) hAV)
  intro a haA
  have haJ : a ∈ thompsonJ T := (le_iSup₂_of_le A hA le_rfl : A ≤ thompsonJ T) haA
  have hg : ∀ i ∈ S, ∃ b ∈ Bf i,
      a * b⁻¹ ∈ Subgroup.centralizer ((⁅V, X i⁆ : Subgroup G) : Set G) := by
    intro i hi
    have hmem : (D i).act ⟨a, hJnLV i hi haJ⟩ ∈ (D i).img (Bf i) := by
      refine himgJ i hi ⟨⟨⟨a, hJnLV i hi haJ⟩, Subgroup.mem_subgroupOf.mpr haJ, rfl⟩, ?_⟩
      exact hFam.img_le_natImage hn hF hred hT hA hAV hi
        ⟨⟨a, hJnLV i hi haJ⟩, Subgroup.mem_subgroupOf.mpr haA, rfl⟩
    obtain ⟨b, hb, hab⟩ := hmem
    refine ⟨b, Subgroup.mem_subgroupOf.mp hb, ?_⟩
    have h1 : (D i).act (⟨a, hJnLV i hi haJ⟩ * b⁻¹) = 1 := by
      rw [map_mul, map_inv, hab, mul_inv_cancel]
    exact hFam.ker i hi _ h1
  obtain ⟨b, hb, hbc⟩ := hFam.exists_mem_iSup_mul_inv hHV Bf (fun i hi => (hBf i hi).2.1)
    (fun i hi => (hBf i hi).2.2.1) hg S subset_rfl
  have hbH : b ∈ H := (iSup₂_le fun i hi => ((hBf i hi).2.1.trans (hFam.le i hi)) :
    (⨆ i ∈ S, Bf i) ≤ H) hb
  have haH : a ∈ H := hT.1 (hA.1 haA)
  have habV : a * b⁻¹ ∈ Subgroup.centralizer (V : Set G) :=
    hFam.faith hred (H.mul_mem haH (H.inv_mem hbH)) hbc
  have e : a = (a * b⁻¹) * b := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ⟨H.mul_mem haH (H.inv_mem hbH), habV⟩)
    (Subgroup.mem_sup_left hb)

end burnsideB610_Fam

end CFSG.Quasithin.B610T
