module

public import CFSG.Quasithin.Vol2.Ch1Sec3L42L5Aut
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsL52Basic
public import CFSG.Quasithin.Vol2.Ch1EightFourInit
public import CFSG.Quasithin.Vol2.Ch1Sec3A5Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListL4L5
public import CFSG.Quasithin.Background.E1Defs

public section

namespace CFSG.Quasithin.L139L42

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.Open (pCoreOf)
open CFSG.QuasithinUnique.Vol2Native.A312L (eq_zero_or_eq_one_of_card_two bigBlockHom
  bigBlockHom_surjective bigBlockHom_coe unitriangular_of_bigBlockHom isPGroup_ker_of_unitriangular
  isPGroup_unitriangular_charTwo perfectCore_eq_bot_of_small exists_big_or_small
  sl_isSimple_of_card_two sl_nonabelian_of_card_two modO2EquivOfHom blockLeft_of_cut
  blockRight_of_cut maxBlock_eq_or_disjoint blkAt_zero mem_unitriangular_of_blocks)
open CFSG.QuasithinUnique.Vol2Native.L239.L52 (blkSLTwo blkSLTwo_coe blkAt_one_eq_one)

variable {F : Type} [Field F] [Finite F]

theorem card_sl_three (hF : Nat.card F = 2) :
    Nat.card (SpecialLinearGroup (Fin 3) F) = 168 := by
  have := Fintype.ofFinite F
  have hq : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
  rw [Matrix.card_SL_field, hq, Fin.prod_univ_three]
  norm_num

theorem card_sl_five (hF : Nat.card F = 2) :
    Nat.card (SpecialLinearGroup (Fin 5) F) = 9999360 := by
  have := Fintype.ofFinite F
  have hq : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card, hF]
  rw [Matrix.card_SL_field, hq, Fin.prod_univ_five]
  norm_num

theorem cuts_eq_of_psl42 (hF : Nat.card F = 2) {I : Set ℕ} (hI : ∀ c ∈ I, 1 ≤ c ∧ c < 5)
    (h4 : IsPSL 4 2 1 (ModO2 (perfectCore (flagStabilizer 5 F I)))) : I = {1} ∨ I = {4} := by
  have hcardF : Nat.card F = 2 ^ 1 := by rw [hF]; norm_num
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hcardF
  have h20160 := Ch1Four.card_of_isPSL_four_two h4
  rcases exists_big_or_small (n := 5) (I := I) with hsmall | ⟨a, m, h, hm3, ha, hb, hno⟩
  · exfalso
    have hbot := perfectCore_eq_bot_of_small hF (by norm_num) hsmall
    have hle : 20160 ≤ Nat.card ↥(perfectCore (flagStabilizer 5 F I)) :=
      h20160 ▸ Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
    rw [hbot, Subgroup.card_bot] at hle
    omega
  · have hS := sl_isSimple_of_card_two hF hm3
    have hsurj := bigBlockHom_surjective hF h hm3 ha hb hno
    have hker : IsPGroup 2 (bigBlockHom (K := F) I a m h ha hb).ker :=
      isPGroup_ker_of_unitriangular (by norm_num) _ fun x hx =>
        unitriangular_of_bigBlockHom hF le_rfl h hm3 ha hb hno x hx
    have eB := modO2EquivOfHom (sl_nonabelian_of_card_two hF hm3) _ hsurj hker
    have hc : Nat.card (SpecialLinearGroup (Fin m) F) = 20160 := by
      rw [← Nat.card_congr eB.toEquiv, h20160]
    have hm : m = 3 ∨ m = 4 ∨ m = 5 := by omega
    rcases hm with rfl | rfl | rfl
    · rw [card_sl_three hF] at hc
      omega
    · rcases (by omega : a = 0 ∨ a = 1) with rfl | rfl
      · right
        have h4I : 4 ∈ I := hb.resolve_left (by norm_num)
        ext c
        refine ⟨fun hc => ?_, fun hc => ?_⟩
        · have := hI c hc
          have := hno c hc
          simp only [Set.mem_singleton_iff]
          omega
        · rw [Set.mem_singleton_iff] at hc
          rw [hc]
          exact h4I
      · left
        have h1I : 1 ∈ I := ha.resolve_left (by norm_num)
        ext c
        refine ⟨fun hc => ?_, fun hc => ?_⟩
        · have := hI c hc
          have := hno c hc
          simp only [Set.mem_singleton_iff]
          omega
        · rw [Set.mem_singleton_iff] at hc
          rw [hc]
          exact h1I
    · rw [card_sl_five hF] at hc
      omega

theorem normalizer_eq_stabilizer (hF : Nat.card F = 2) {i : ℕ} (hi1 : 1 ≤ i) (hi5 : i < 5)
    (hne : perfectCore (stabilizer (flagSpace 5 F i)) ≠ ⊥) :
    Subgroup.normalizer ((perfectCore (stabilizer (flagSpace 5 F i)) : Subgroup _) :
      Set (SpecialLinearGroup (Fin 5) F)) = stabilizer (flagSpace 5 F i) := by
  have hle : stabilizer (flagSpace 5 F i) ≤
      Subgroup.normalizer ((perfectCore (stabilizer (flagSpace 5 F i)) : Subgroup _) :
        Set (SpecialLinearGroup (Fin 5) F)) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
  rcases eq_of_stabilizer_flagSpace_le _ hle with h | h
  · exact h
  · exfalso
    have hS := sl_isSimple_of_card_two hF (m := 5) (by norm_num)
    have hN : (perfectCore (stabilizer (flagSpace 5 F i))).Normal :=
      Subgroup.normalizer_eq_top_iff.mp h
    rcases hN.eq_bot_or_eq_top with hb | ht
    · exact hne hb
    · apply stabilizer_flagSpace_ne_top (n := 5) (K := F) hi1 hi5
      exact eq_top_iff.mpr (ht ▸ perfectCore_le _)

theorem exists_inner_of_mem_stabilizer (hF : Nat.card F = 2) {i : ℕ} (hi : i = 1 ∨ i = 4)
    {A : SpecialLinearGroup (Fin 5) F} (hA : A ∈ stabilizer (flagSpace 5 F i)) :
    ∃ b ∈ perfectCore (stabilizer (flagSpace 5 F i)),
      ∀ x ∈ perfectCore (stabilizer (flagSpace 5 F i)),
        (A * x * A⁻¹)⁻¹ * (b * x * b⁻¹) ∈
          pCoreOf 2 (perfectCore (stabilizer (flagSpace 5 F i))) := by
  classical
  have hcardF : Nat.card F = 2 ^ 1 := by rw [hF]; norm_num
  have : CharP F 2 := finite_field_prime_power_characteristic Nat.prime_two le_rfl hcardF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← flagStabilizer_singleton] at hA ⊢
  set Q := flagStabilizer 5 F {i} with hQ
  set B := perfectCore Q with hB
  obtain ⟨a, h, ha, hb, hno⟩ : ∃ (a : ℕ) (h : a + 4 ≤ 5), (a = 0 ∨ a ∈ ({i} : Set ℕ)) ∧
      (a + 4 = 5 ∨ a + 4 ∈ ({i} : Set ℕ)) ∧ ∀ c ∈ ({i} : Set ℕ), ¬ (a < c ∧ c < a + 4) := by
    rcases hi with rfl | rfl
    · exact ⟨1, le_rfl, Or.inr rfl, Or.inl rfl, by simp⟩
    · exact ⟨0, by norm_num, Or.inl rfl, Or.inr rfl, by simp⟩
  let φ : ↥Q →* SpecialLinearGroup (Fin 4) F :=
    blkSLTwo hF Q a 4 h (blockLeft_of_cut 4 ha) (blockRight_of_cut hb)
  let ψ := bigBlockHom (K := F) {i} a 4 h ha hb
  have hψ := bigBlockHom_surjective hF h (by norm_num) ha hb hno
  have hφker : ∀ u : ↥Q, φ u = 1 → (u : SpecialLinearGroup (Fin 5) F) ∈ unitriangular 5 F := by
    intro u hu
    refine mem_unitriangular_of_blocks u.2 fun a₂ m₂ h₂ ha₂ hb₂ hno₂ => ?_
    by_cases hm₂ : m₂ = 0
    · subst hm₂
      exact blkAt_zero a₂ h₂ _
    · rcases maxBlock_eq_or_disjoint h h₂ ha hb ha₂ hb₂ hno hno₂ with ⟨rfl, rfl⟩ | hd | hd
      · exact congrArg Subtype.val hu
      · have hm1 : m₂ = 1 := by omega
        subst hm1
        exact blkAt_one_eq_one hF Q a₂ h₂ (blockLeft_of_cut 1 ha₂) (blockRight_of_cut hb₂) u
      · have hm1 : m₂ = 1 := by omega
        subst hm1
        exact blkAt_one_eq_one hF Q a₂ h₂ (blockLeft_of_cut 1 ha₂) (blockRight_of_cut hb₂) u
  set N : Subgroup (SpecialLinearGroup (Fin 5) F) := φ.ker.map Q.subtype with hN
  have hNQ : N ≤ Q := Subgroup.map_subtype_le _
  have hN2 : IsPGroup 2 N := by
    have hU := isPGroup_unitriangular_charTwo (K := F) (n := 5) (by norm_num)
    refine hU.to_le ?_
    rintro _ ⟨u, hu, rfl⟩
    exact hφker u hu
  have hNnorm : ∀ y ∈ Q, ∀ z ∈ N, y * z * y⁻¹ ∈ N := by
    rintro y hy _ ⟨u, hu, rfl⟩
    refine ⟨⟨y, hy⟩ * u * ⟨y, hy⟩⁻¹, ?_, rfl⟩
    exact (MonoidHom.normal_ker φ).conj_mem u hu ⟨y, hy⟩
  have hBQ : B ≤ Q := perfectCore_le Q
  have hBnorm : ∀ y ∈ Q, ∀ z ∈ B, y * z * y⁻¹ ∈ B := fun y hy z hz =>
    (Subgroup.mem_normalizer_iff.mp
      ((Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore Q)) hy) z).mp hz
  have hNB : N ⊓ B ≤ pCoreOf 2 B := by
    refine CFSG.LieType.BorelTits.le_pCoreOf 2 inf_le_right ⟨fun z hz g => ?_⟩
      (hN2.to_le inf_le_left)
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    exact ⟨hNnorm _ (hBQ g.2) _ hz.1, hBnorm _ (hBQ g.2) _ hz.2⟩
  obtain ⟨b, hbA⟩ := hψ (φ ⟨A, hA⟩)
  have hbQ : (b : SpecialLinearGroup (Fin 5) F) ∈ Q := hBQ b.2
  set u : ↥Q := (⟨b, hbQ⟩ : ↥Q)⁻¹ * ⟨A, hA⟩ with hu
  have hφu : φ u = 1 := by
    have e1 : φ ⟨b, hbQ⟩ = ψ b := Subtype.ext rfl
    rw [hu, map_mul, map_inv, e1, hbA, inv_mul_cancel]
  have huN : (u : SpecialLinearGroup (Fin 5) F) ∈ N := ⟨u, hφu, rfl⟩
  have hAbu : A = (b : SpecialLinearGroup (Fin 5) F) * u := by
    rw [hu]
    simp
  refine ⟨b, b.2, fun x hx => ?_⟩
  set c : SpecialLinearGroup (Fin 5) F := (u : SpecialLinearGroup (Fin 5) F) * x⁻¹ *
    (u : SpecialLinearGroup (Fin 5) F)⁻¹ * x with hc
  have hcN : c ∈ N := by
    have h1 := hNnorm x⁻¹ (inv_mem (hBQ hx)) _ (inv_mem huN)
    rw [inv_inv] at h1
    have h2 := mul_mem huN h1
    rw [hc]
    simpa [mul_assoc] using h2
  have hcB : c ∈ B := by
    have h1 := hBnorm _ u.2 _ (inv_mem hx)
    exact mul_mem h1 hx
  have hcO : c ∈ pCoreOf 2 B := hNB ⟨hcN, hcB⟩
  have hbO := (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 B b.2) c).mp hcO
  have e : (A * x * A⁻¹)⁻¹ * ((b : SpecialLinearGroup (Fin 5) F) * x *
      ((b : SpecialLinearGroup (Fin 5) F))⁻¹) =
      (b : SpecialLinearGroup (Fin 5) F) * c * ((b : SpecialLinearGroup (Fin 5) F))⁻¹ := by
    rw [hAbu, hc]
    group
  rw [e]
  exact hbO

theorem exists_inner_l5 (hF : Nat.card F = 2) {P : Subgroup (SpecialLinearGroup (Fin 5) F)}
    (hUP : upperTriangular 5 F ≤ P) (h4 : IsPSL 4 2 1 (ModO2 (perfectCore P)))
    (β : MulAut (SpecialLinearGroup (Fin 5) F)) (hβ : ∀ x ∈ perfectCore P, β x ∈ perfectCore P) :
    ∃ b ∈ perfectCore P, ∀ x ∈ perfectCore P,
      (β x)⁻¹ * (b * x * b⁻¹) ∈ pCoreOf 2 (perfectCore P) := by
  obtain ⟨hPI, -⟩ := borel_overgroups P hUP
  have hI : ∀ c ∈ borelOvergroupCuts P, 1 ≤ c ∧ c < 5 := fun c hc => by
    obtain ⟨h1, h2, -⟩ := hc
    exact ⟨h1, h2⟩
  have h4' := h4
  rw [hPI] at h4'
  obtain ⟨i, hi, hPi⟩ : ∃ i, (i = 1 ∨ i = 4) ∧ P = stabilizer (flagSpace 5 F i) := by
    rcases cuts_eq_of_psl42 hF hI h4' with h | h
    · exact ⟨1, Or.inl rfl, by rw [hPI, h, flagStabilizer_singleton]⟩
    · exact ⟨4, Or.inr rfl, by rw [hPI, h, flagStabilizer_singleton]⟩
  subst hPi
  have hi1 : 1 ≤ i := by rcases hi with rfl | rfl <;> norm_num
  have hi5 : i < 5 := by rcases hi with rfl | rfl <;> norm_num
  have hne : perfectCore (stabilizer (flagSpace 5 F i)) ≠ ⊥ := by
    intro hb
    have h20160 := Ch1Four.card_of_isPSL_four_two h4
    have hle : 20160 ≤ Nat.card ↥(perfectCore (stabilizer (flagSpace 5 F i))) :=
      h20160 ▸ Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
    rw [hb, Subgroup.card_bot] at hle
    omega
  have hNB := normalizer_eq_stabilizer hF hi1 hi5 hne
  have hβiff : ∀ x, β x ∈ perfectCore (stabilizer (flagSpace 5 F i)) ↔
      x ∈ perfectCore (stabilizer (flagSpace 5 F i)) :=
    L139A5.apply_mem_iff_of_maps hβ
  have hβQ : ∀ g ∈ stabilizer (flagSpace 5 F i), β g ∈ stabilizer (flagSpace 5 F i) := by
    intro g hg
    rw [← hNB] at hg ⊢
    rw [Subgroup.mem_normalizer_iff] at hg ⊢
    intro y
    obtain ⟨x, rfl⟩ := β.surjective y
    rw [← map_inv, ← map_mul, ← map_mul, hβiff, hβiff]
    exact hg x
  obtain ⟨A, hA, rfl⟩ := exists_conj_of_preserves hF hi β hβQ
  exact exists_inner_of_mem_stabilizer hF hi hA

end CFSG.Quasithin.L139L42
