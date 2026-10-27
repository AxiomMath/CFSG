module

public import CFSG.RankThree.PartTwo.Sec21.FF84S3M1
public import CFSG.RankThree.PartTwo.Sec21.FF84S3M2
public import CFSG.RankThree.PartTwo.Sec21.FF84S3M3
public import CFSG.RankThree.PartTwo.Sec21.FF84S3Inputs
public import CFSG.RankThree.PartTwo.Sec21.FF84S32Syl

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S3

open CFSG CFSG.RankThree.PartTwo.Sec21

section Helpers
variable {G : Type} [Group G] [Finite G]

theorem card_Opp3_coprime (H : Subgroup G) : Nat.Coprime 3 (Nat.card (Opp 3 H)) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have e := (pPrimeCore 3 H).equivMapOfInjective H.subtype H.subtype_injective
  have h : Nat.card (Opp 3 H) = Nat.card (pPrimeCore 3 H) :=
    (Nat.card_congr e.toEquiv.symm)
  rw [h]
  exact pPrimeCore_coprime_card

theorem le_Opp3_of_normal_coprime (H M : Subgroup G)
    (hMH : M ≤ H) (hMn : (M.subgroupOf H).Normal) (hcop : Nat.Coprime 3 (Nat.card M)) :
    M ≤ Opp 3 H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.Coprime 3 (Nat.card (M.subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMH).toEquiv]
    exact hcop
  have hle : M.subgroupOf H ≤ pPrimeCore 3 H := by
    unfold pPrimeCore
    exact le_sSup ⟨hMn, hcard⟩
  intro m hm
  have hmem : (⟨m, hMH hm⟩ : H) ∈ M.subgroupOf H := hm
  exact Subgroup.mem_map.2 ⟨⟨m, hMH hm⟩, hle hmem, rfl⟩

theorem Opp3_le (H : Subgroup G) : Opp 3 H ≤ H := Subgroup.map_subtype_le _

theorem mem_Nor_Opp3 {H : Subgroup G} {g : G} (hg : g ∈ H) : g ∈ Nor (Opp 3 H) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact opp3_conj hg
  · intro hx
    have := opp3_conj (H.inv_mem hg) hx
    simpa [mul_assoc] using this

theorem coprime_of_le_Opp3 {H M : Subgroup G} (hM : M ≤ Opp 3 H) : Nat.Coprime 3 (Nat.card M) :=
  Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le hM) (card_Opp3_coprime H)

theorem Opp3_inf_zpowers {H : Subgroup G} {b : G} (hb : orderOf b = 3) :
    Opp 3 H ⊓ Subgroup.zpowers b = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxS, hxb⟩ := Subgroup.mem_inf.1 hx
  have hdvd : orderOf x ∣ 3 := hb ▸ orderOf_dvd_of_mem_zpowers hxb
  rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1
  · rw [Subgroup.mem_bot]
    exact orderOf_eq_one_iff.1 h1
  · exact absurd (dvd_of_eq h1.symm) (opp3_not_dvd hxS)

end Helpers

section Main
variable {G : Type} [Group G] [Finite G] {b : G} {L B : Subgroup G} {b₁ b₂ : G}

theorem b_mem_Cen_c (h : FF84Sec3 b L B b₁ b₂) : b ∈ Cen (b₁ * b₂) := B_le_Cen_c h (mem_B_b h)

theorem S2_Cb (h : FF84Sec3 b L B b₁ b₂) (hX : Opp 3 (Cen b) = ⊥) (hZ : Subgroup.center L = ⊥) :
    Opp 3 (Cen (b₁ * b₂)) ⊓ Cen b = ⊥ := by
  have hM3 := M3_O3'_Y h hX hZ
  have hle : Opp 3 (Cen (b₁ * b₂)) ⊓ Cen b ≤ Cen b ⊓ Cen (b₁ * b₂) :=
    le_inf inf_le_right (inf_le_left.trans (Opp3_le _))
  have hn : ((Opp 3 (Cen (b₁ * b₂)) ⊓ Cen b).subgroupOf (Cen b ⊓ Cen (b₁ * b₂))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨hn1, hn2⟩ := Subgroup.mem_inf.1 hn
    obtain ⟨hg1, hg2⟩ := Subgroup.mem_inf.1 g.2
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact opp3_conj hg2 hn1
    · exact mul_mem (mul_mem hg1 hn2) (inv_mem hg1)
  have := le_Opp3_of_normal_coprime _ _ hle hn
    (coprime_of_le_Opp3 (M := Opp 3 (Cen (b₁ * b₂)) ⊓ Cen b) inf_le_left)
  rw [hM3] at this
  exact le_bot_iff.1 this

theorem cen_E_of_cen_c_d (h : FF84Sec3 b L B b₁ b₂) {r : G} (hc : r ∈ Cen (b₁ * b₂))
    (hd : r ∈ Cen (b₁ * b₂ ^ 2)) : r ∈ CenS (B ⊓ L) := by
  have hb₂ : b₂ = (b₁ * b₂)⁻¹ * (b₁ * b₂ ^ 2) := by
    apply eq_inv_mul_of_mul_eq
    rw [mul_assoc, ← pow_two]
  have hb₁ : b₁ = (b₁ * b₂) * ((b₁ * b₂ ^ 2)⁻¹ * (b₁ * b₂)) := by group
  have h₂ : b₂ ∈ Cen r := by
    rw [hb₂]
    exact mul_mem (inv_mem ((Subgroup.mem_centralizer_singleton_iff).2
      ((Subgroup.mem_centralizer_singleton_iff.1 hc).symm)))
      ((Subgroup.mem_centralizer_singleton_iff).2 ((Subgroup.mem_centralizer_singleton_iff.1 hd).symm))
  have h₁ : b₁ ∈ Cen r := by
    rw [hb₁]
    have c' : (b₁ * b₂) ∈ Cen r :=
      (Subgroup.mem_centralizer_singleton_iff).2 ((Subgroup.mem_centralizer_singleton_iff.1 hc).symm)
    have d' : (b₁ * b₂ ^ 2) ∈ Cen r :=
      (Subgroup.mem_centralizer_singleton_iff).2 ((Subgroup.mem_centralizer_singleton_iff.1 hd).symm)
    exact mul_mem c' (mul_mem (inv_mem d') c')
  have hE : B ⊓ L ≤ Cen r := by
    rw [h.gen, Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact h₁
    · exact h₂
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact Subgroup.mem_centralizer_singleton_iff.1 (hE hz)

theorem S2_Cd (h : FF84Sec3 b L B b₁ b₂) (hX : Opp 3 (Cen b) = ⊥) (hZ : Subgroup.center L = ⊥) :
    Opp 3 (Cen (b₁ * b₂)) ⊓ Cen (b₁ * b₂ ^ 2) = ⊥ := by
  rw [eq_bot_iff]
  intro r hr
  obtain ⟨hrS, hrd⟩ := Subgroup.mem_inf.1 hr
  have hrc : r ∈ Cen (b₁ * b₂) := Opp3_le _ hrS
  have hrE := cen_E_of_cen_c_d h hrc hrd
  have hrN : r ∈ Nor (Subgroup.zpowers b) := (M2_norm h hZ).2 hrE
  have hrb : r * b * r⁻¹ ∈ Subgroup.zpowers b :=
    (Subgroup.mem_normalizer_iff.1 hrN b).1 (Subgroup.mem_zpowers b)
  have hcomm : r * b * r⁻¹ * b⁻¹ ∈ Subgroup.zpowers b :=
    mul_mem hrb (inv_mem (Subgroup.mem_zpowers b))
  have hcommS : r * b * r⁻¹ * b⁻¹ ∈ Opp 3 (Cen (b₁ * b₂)) := by
    have := mul_mem hrS (opp3_conj (b_mem_Cen_c h) (inv_mem hrS))
    rwa [show r * (b * r⁻¹ * b⁻¹) = r * b * r⁻¹ * b⁻¹ by group] at this
  have h1 : r * b * r⁻¹ * b⁻¹ = 1 := by
    have := Opp3_inf_zpowers (H := Cen (b₁ * b₂)) h.hyp.ord
    have hmem : r * b * r⁻¹ * b⁻¹ ∈ Opp 3 (Cen (b₁ * b₂)) ⊓ Subgroup.zpowers b :=
      Subgroup.mem_inf.2 ⟨hcommS, hcomm⟩
    rw [this, Subgroup.mem_bot] at hmem
    exact hmem
  have hrCb : r ∈ Cen b := by
    rw [mem_Cen_iff]
    calc r * b * r⁻¹ = (r * b * r⁻¹ * b⁻¹) * b := by group
      _ = b := by rw [h1, one_mul]
  have := S2_Cb h hX hZ
  have hmem : r ∈ Opp 3 (Cen (b₁ * b₂)) ⊓ Cen b := Subgroup.mem_inf.2 ⟨hrS, hrCb⟩
  rwa [this] at hmem

theorem S2_elemab (hH : LemmaH) (h : FF84Sec3 b L B b₁ b₂) (hX : Opp 3 (Cen b) = ⊥)
    (hZ : Subgroup.center L = ⊥) :
    IsPGroup 2 (Opp 3 (Cen (b₁ * b₂))) ∧ IsElementaryAbelian 2 (Opp 3 (Cen (b₁ * b₂))) := by
  obtain ⟨K, hKle, hK60, hKs, hdK, -, -, hKinv⟩ := M1_K h hZ
  have hKc : K ≤ Cen (b₁ * b₂) := hKle.trans inf_le_right
  have hd3 : orderOf (b₁ * b₂ ^ 2) = 3 := orderOf_eq_prime (d_pow3 h) (d_ne_one h)
  have hnd : ¬ 3 ∣ Nat.card (Opp 3 (Cen (b₁ * b₂))) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (card_Opp3_coprime _)
  obtain ⟨hcomm, hsq, r, hr⟩ := hH G K (Opp 3 (Cen (b₁ * b₂))) ⊥ (b₁ * b₂ ^ 2) hK60 hKs hnd
    (fun k hk => mem_Nor_Opp3 (hKc hk)) bot_le (Subgroup.le_normalizer_of_normal)
    (by rw [Subgroup.bot_subgroupOf]; infer_instance) hdK hd3 (by
      rintro u hu ⟨n, hn, hun⟩
      rw [Subgroup.mem_bot] at hn
      subst hn
      rw [mul_one] at hun
      have hud : u ∈ Opp 3 (Cen (b₁ * b₂)) ⊓ Cen (b₁ * b₂ ^ 2) := by
        refine Subgroup.mem_inf.2 ⟨hu, ?_⟩
        rw [mem_Cen_iff]
        have e := mul_inv_eq_iff_eq_mul.1 hun
        calc u * (b₁ * b₂ ^ 2) * u⁻¹ = ((b₁ * b₂ ^ 2) * u) * u⁻¹ := by rw [e]
          _ = b₁ * b₂ ^ 2 := by group
      rw [S2_Cd h hX hZ] at hud
      exact hud)
  have hcard : Nat.card (Opp 3 (Cen (b₁ * b₂))) = 2 ^ (4 * r) := by
    rw [hr, Subgroup.card_bot, one_mul, pow_mul]
    norm_num
  refine ⟨IsPGroup.of_card hcard, ?_⟩
  refine { toIsMulCommutative := ⟨⟨fun x y => ?_⟩⟩, exponent_dvd_p := ?_ }
  · have := hcomm x.1 x.2 y.1 y.2
    rw [Subgroup.mem_bot] at this
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (x : G) * (y : G) = ((x : G) * (y : G) * (x : G)⁻¹ * (y : G)⁻¹) * ((y : G) * (x : G)) := by
          group
      _ = (y : G) * (x : G) := by rw [this, one_mul]
  · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 ?_
    intro y
    apply Subtype.ext
    have := hsq y.1 y.2
    rw [Subgroup.mem_bot] at this
    simpa using this

end Main

end CFSG.RankThree.PartTwo.Sec21.FF84.S3

end
