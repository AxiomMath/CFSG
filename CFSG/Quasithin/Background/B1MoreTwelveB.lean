module

public import CFSG.Quasithin.Background.B1Solvable
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.B1MoreElevenA
public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19

public section

namespace CFSG.Quasithin

open CFSG.Open
open CFSG.Quasithin.EmptyFaithfulMultiple

namespace B1Red

section Six

variable {Y : Type*} [Group Y]

theorem exists_normal_card_three_of_card_six [Finite Y] (h6 : Nat.card Y = 6) :
    ∃ P : Subgroup Y, P.Normal ∧ Nat.card ↥P = 3 ∧ ∀ y, y ∈ P ↔ y ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Y) 3
    (show 3 ∣ Nat.card Y by rw [h6]; norm_num)
  have hcard : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hindex : (Subgroup.zpowers x).index = 2 := by
    have := Subgroup.index_mul_card (H := Subgroup.zpowers x)
    rw [hcard, h6] at this
    omega
  have hnorm : (Subgroup.zpowers x).Normal := Subgroup.normal_of_index_eq_two hindex
  refine ⟨Subgroup.zpowers x, hnorm, hcard, fun y => ⟨fun hy => ?_, fun hy => ?_⟩⟩
  · have h1 := pow_card_eq_one' (G := ↥(Subgroup.zpowers x)) (x := ⟨y, hy⟩)
    rw [hcard] at h1
    exact congrArg Subtype.val h1
  · have h2 : y ^ 2 ∈ Subgroup.zpowers x := by
      have := Subgroup.pow_index_mem (Subgroup.zpowers x) y
      rwa [hindex] at this
    have e : y = (y ^ 2) ^ 2 := by
      calc y = y ^ 3 * y := by rw [hy, one_mul]
        _ = (y ^ 2) ^ 2 := by group
    rw [e]
    exact Subgroup.pow_mem _ h2 2

theorem oddCore_eq_of_card_six [Finite Y] (h6 : Nat.card Y = 6) :
    ∃ P : Subgroup Y, CFSG.oddCore Y = P ∧ Nat.card ↥P = 3 ∧ ∀ y, y ∈ P ↔ y ^ 3 = 1 := by
  obtain ⟨P, hPn, hP3, hPy⟩ := exists_normal_card_three_of_card_six h6
  refine ⟨P, le_antisymm ?_ ?_, hP3, hPy⟩
  · refine sSup_le fun N hN => ?_
    intro n hn
    rw [hPy]
    have hdvd : orderOf n ∣ Nat.card N := by
      have := orderOf_dvd_natCard (⟨n, hn⟩ : N)
      rwa [Subgroup.orderOf_mk] at this
    have hodd : Odd (orderOf n) := Odd.of_dvd_nat hN.2 hdvd
    have h6' : orderOf n ∣ 3 * 2 := by
      rw [show 3 * 2 = Nat.card Y by rw [h6]]
      exact orderOf_dvd_natCard n
    have hcop : Nat.Coprime (orderOf n) 2 := Nat.coprime_two_right.2 hodd
    exact orderOf_dvd_iff_pow_eq_one.1 (hcop.dvd_of_dvd_mul_right h6')
  · exact le_sSup ⟨hPn, by rw [hP3]; decide⟩

end Six

section Six'

variable {Γ : Type*} [Group Γ] {G : Subgroup Γ}

theorem mem_oddCoreOfSub_iff_of_card_six (h6 : Nat.card ↥G = 6) {y : Γ} :
    y ∈ oddCoreOfSub G ↔ y ∈ G ∧ y ^ 3 = 1 := by
  have : Finite ↥G := Nat.finite_of_card_ne_zero (by rw [h6]; norm_num)
  obtain ⟨P, hP, -, hPy⟩ := oddCore_eq_of_card_six h6
  unfold oddCoreOfSub
  rw [hP]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p.2, congrArg Subtype.val ((hPy p).1 hp)⟩
  · rintro ⟨hyG, hy3⟩
    exact ⟨⟨y, hyG⟩, (hPy _).2 (Subtype.ext hy3), rfl⟩

theorem card_oddCoreOfSub_of_card_six (h6 : Nat.card ↥G = 6) : Nat.card ↥(oddCoreOfSub G) = 3 := by
  have : Finite ↥G := Nat.finite_of_card_ne_zero (by rw [h6]; norm_num)
  obtain ⟨P, hP, hP3, -⟩ := oddCore_eq_of_card_six h6
  unfold oddCoreOfSub
  rw [hP, Subgroup.card_map_of_injective G.subtype_injective, hP3]

theorem oddCoreOfSub_le (G : Subgroup Γ) : oddCoreOfSub G ≤ G := Subgroup.map_subtype_le _

theorem sup_zpowers_eq_of_card_six {F : Subgroup Γ} (h6 : Nat.card ↥G = 6) (hFG : F ≤ G)
    (hF3 : Nat.card ↥F = 3) {s : Γ} (hsG : s ∈ G) (hsF : s ∉ F) :
    F ⊔ Subgroup.zpowers s = G := by
  have : Finite ↥G := Nat.finite_of_card_ne_zero (by rw [h6]; norm_num)
  have hSG : F ⊔ Subgroup.zpowers s ≤ G := sup_le hFG (Subgroup.zpowers_le.2 hsG)
  have : Finite ↥(F ⊔ Subgroup.zpowers s) :=
    Finite.of_injective (Subgroup.inclusion hSG) (Subgroup.inclusion_injective hSG)
  have hd1 : Nat.card ↥(F ⊔ Subgroup.zpowers s) ∣ 6 := by
    rw [← h6]
    exact Subgroup.card_dvd_of_le hSG
  have hd2 : 3 ∣ Nat.card ↥(F ⊔ Subgroup.zpowers s) := by
    rw [← hF3]
    exact Subgroup.card_dvd_of_le le_sup_left
  have hne : Nat.card ↥(F ⊔ Subgroup.zpowers s) ≠ 3 := by
    intro h3
    have hFS : F = F ⊔ Subgroup.zpowers s :=
      Subgroup.eq_of_le_of_card_ge (le_sup_left) (by rw [h3, hF3])
    exact hsF (hFS ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers s))
  have hpos : 0 < Nat.card ↥(F ⊔ Subgroup.zpowers s) := Nat.card_pos
  have hle : Nat.card ↥(F ⊔ Subgroup.zpowers s) ≤ 6 := Nat.le_of_dvd (by norm_num) hd1
  have h6' : Nat.card ↥(F ⊔ Subgroup.zpowers s) = 6 := by
    obtain ⟨c, hc⟩ := hd2
    have hc2 : c ≤ 2 := by omega
    interval_cases c <;> omega
  exact Subgroup.eq_of_le_of_card_ge hSG (by rw [h6, h6'])

end Six'

section SL2

theorem sl2_conj_inv_aux : ∀ g h : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
    g ^ 3 = 1 → g ≠ 1 → h ^ 2 = 1 → h ≠ 1 → h * g * h⁻¹ = g⁻¹ := by decide

theorem conj_inv_of_mulEquiv {Y : Type*} [Group Y]
    (e : Y ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) {f t : Y} (hf3 : f ^ 3 = 1)
    (hf1 : f ≠ 1) (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) : t * f * t⁻¹ = f⁻¹ := by
  apply e.injective
  have := sl2_conj_inv_aux (e f) (e t) (by rw [← map_pow, hf3, map_one])
    (fun h => hf1 (e.injective (by rw [h, map_one]))) (by rw [← map_pow, ht2, map_one])
    (fun h => ht1 (e.injective (by rw [h, map_one])))
  simpa [map_mul, map_inv] using this

end SL2

section Blocks

variable {W : Type*} [CommGroup W] [Finite W]

theorem exists_blocks (hV : ∀ v : W, v ^ 2 = 1) {X : Subgroup (MulAut W)}
    (hsolv : Group.IsSolvable ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut W), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥) :
    ∃ 𝓗 : Finset (Subgroup (MulAut W)), IsTransvectionBlocks (ffJ X) 𝓗 ∧
      ∀ A : Subgroup (MulAut W), IsFFStarOffender X A →
        ∃ a : Subgroup (MulAut W) → Subgroup (MulAut W),
          (∀ H ∈ 𝓗, a H = ⊥ ∨ CFSG.QuasithinUnique.IsSylowTwoOf (a H) H) ∧
            (∃ H ∈ 𝓗, a H ≠ ⊥) ∧ A = ⨆ H ∈ 𝓗, a H := by
  have hJX := B1.closure_transvectionsIn_le X
  have hsolvJ : Group.IsSolvable ↥(Subgroup.closure (transvectionsIn X)) :=
    B1.solvable_of_le hJX hsolv
  have hOJ := B1.normal_two_subgroups_trivial_of_normal hJX
    (fun x hx j hj => B1.closure_transvectionsIn_normal x hx j hj) hO2
  have hcl : Subgroup.closure (transvectionsIn (Subgroup.closure (transvectionsIn X))) =
      Subgroup.closure (transvectionsIn X) := by
    apply le_antisymm
    · exact (Subgroup.closure_le _).2 fun t ht => ht.1
    · exact Subgroup.closure_mono fun t ht => ⟨Subgroup.subset_closure ht, ht.2⟩
  obtain ⟨𝓗, hb⟩ := transvection_structure hV hsolvJ hOJ hcl
  have hff : ffJ X = ⨆ H ∈ 𝓗, H := hb.ffJ_eq hV hsolv hO2
  have hJ : Subgroup.closure (transvectionsIn X) = ffJ X := by rw [← hb.iSup_eq, hff]
  refine ⟨𝓗, by rw [← hJ]; exact hb, fun A hA => ?_⟩
  exact (hb.offender_iff hV hsolv hO2 A).1 hA

end Blocks

end B1Red

namespace IsTransvectionBlocks

open CFSG.Quasithin.B1Red

section Factors

variable {W : Type*} [CommGroup W] {J : Subgroup (MulAut W)}
  {𝓗 : Finset (Subgroup (MulAut W))}

theorem nonempty_mulEquiv_sl2 [Finite W] (hV : ∀ v : W, v ^ 2 = 1)
    (hb : IsTransvectionBlocks J 𝓗) {G : Subgroup (MulAut W)} (hG : G ∈ 𝓗) :
    Nonempty (↥G ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) := by
  obtain ⟨e, -, -⟩ := actsAsNaturalL2_of_full hV (hb.card_comm G hG) (hb.le_stabSub hG)
    (hb.inf_centSub hG) (hb.autSub_eq_top G hG)
  exact ⟨e⟩

theorem mem_oddCoreOfSub_iff_of_mem (hb : IsTransvectionBlocks J 𝓗)
    {G : Subgroup (MulAut W)} (hG : G ∈ 𝓗) {y : MulAut W} :
    y ∈ oddCoreOfSub G ↔ y ∈ G ∧ y ^ 3 = 1 :=
  mem_oddCoreOfSub_iff_of_card_six (hb.card_eq G hG)

theorem card_oddCoreOfSub_of_mem (hb : IsTransvectionBlocks J 𝓗)
    {G : Subgroup (MulAut W)} (hG : G ∈ 𝓗) : Nat.card ↥(oddCoreOfSub G) = 3 :=
  card_oddCoreOfSub_of_card_six (hb.card_eq G hG)

theorem conj_eq_inv_of_mem_oddCoreOfSub [Finite W] (hV : ∀ v : W, v ^ 2 = 1)
    (hb : IsTransvectionBlocks J 𝓗) {G : Subgroup (MulAut W)} (hG : G ∈ 𝓗) {t f : MulAut W}
    (htG : t ∈ transvectionsIn G) (hf : f ∈ oddCoreOfSub G) (hf1 : f ≠ 1) :
    t * f * t⁻¹ = f⁻¹ := by
  obtain ⟨e⟩ := hb.nonempty_mulEquiv_sl2 hV hG
  obtain ⟨htG', ht1, w, htw⟩ := htG
  have ht2 : t ^ 2 = 1 := by rw [pow_two]; exact B1.tv_sq hV htw ht1
  obtain ⟨hfG, hf3⟩ := (hb.mem_oddCoreOfSub_iff_of_mem hG).1 hf
  have := conj_inv_of_mulEquiv e (f := ⟨f, hfG⟩) (t := ⟨t, htG'⟩)
    (Subtype.ext hf3) (fun h => hf1 (congrArg Subtype.val h)) (Subtype.ext ht2)
    (fun h => ht1 (congrArg Subtype.val h))
  exact congrArg Subtype.val this

theorem not_commute_of_mem_oddCoreOfSub [Finite W] (hV : ∀ v : W, v ^ 2 = 1)
    (hb : IsTransvectionBlocks J 𝓗) {G : Subgroup (MulAut W)} (hG : G ∈ 𝓗) {t f : MulAut W}
    (htG : t ∈ transvectionsIn G) (hf : f ∈ oddCoreOfSub G) (hf1 : f ≠ 1) : t * f ≠ f * t := by
  intro hcomm
  have h1 := hb.conj_eq_inv_of_mem_oddCoreOfSub hV hG htG hf hf1
  have h2 : t * f * t⁻¹ = f := by rw [hcomm]; group
  rw [h2] at h1
  obtain ⟨-, hf3⟩ := (hb.mem_oddCoreOfSub_iff_of_mem hG).1 hf
  apply hf1
  have h3 : f * f = 1 := by
    calc f * f = f * f⁻¹ := by rw [← h1]
      _ = 1 := by group
  calc f = f ^ 3 * (f * f)⁻¹ := by group
    _ = 1 := by rw [hf3, h3]; group

end Factors

end IsTransvectionBlocks

end CFSG.Quasithin
