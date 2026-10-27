module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKM24
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKHe
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKRu
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.In23ExamKFusion
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
public meta import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
import all CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicHe
import all CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Lin2 CFSG.QuasithinUnique.Lin2.FusionCert
open CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Blueprint.NativeSporadic (Carrier)

namespace Sec1216Ctr

@[expose] def SylowCenterLeTwo (X : Type) [Group X] : Prop :=
  ∀ U : Subgroup X, IsSylowTwoOf U ⊤ → ∀ c ∈ U, ∀ d ∈ U, (∀ u ∈ U, c * u = u * c) →
    (∀ u ∈ U, d * u = u * d) → c ≠ 1 → d ≠ 1 → c = d

theorem SylowCenterLeTwo.of_mulEquiv {X Y : Type} [Group X] [Group Y] [Finite X] (e : X ≃* Y)
    (h : SylowCenterLeTwo Y) : SylowCenterLeTwo X := by
  intro U hU c hc d hd hcc hdc hc1 hd1
  have hUY : IsSylowTwoOf (U.map e.toMonoidHom) ⊤ :=
    CFSG.Quasithin.A312.isSylowTwoOf_top_map e.toMonoidHom e.surjective hU
  have hcen : ∀ x ∈ U, (∀ u ∈ U, x * u = u * x) →
      ∀ w ∈ U.map e.toMonoidHom, e x * w = w * e x := by
    rintro x - hx _ ⟨u, hu, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hx u hu]
  have := h _ hUY (e c) ⟨c, hc, rfl⟩ (e d) ⟨d, hd, rfl⟩ (hcen c hc hcc) (hcen d hd hdc)
    (fun h1 => hc1 (e.map_eq_one_iff.mp h1)) (fun h1 => hd1 (e.map_eq_one_iff.mp h1))
  exact e.injective this

section Main

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)]

theorem sylowCenterLeTwo_of_fusionCheck {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (a b : Γ) (gens : List Γ)
    (Ts : Array (List ℕ)) (par cl : Array ℕ) (k m : ℕ) (hcard : Nat.card Γ = 2 ^ k * m)
    (hm : Odd m) (hEnum : BaseEnumOK n B (genTabs n gens) (genTabsInv n gens) Ts par cl)
    (hsize : Ts.size = 2 ^ k) {zi : ℕ} {wits : List (List ℕ × List ℕ × ℕ)}
    {gws : List (List ℕ)}
    (hcheck : fusionCheck n B (tab n a).toArray (tab n b).toArray (genTabs n gens) Ts par cl zi
      wits gws = true) :
    SylowCenterLeTwo Γ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨ι, hcay, hιQ, hsurj, -⟩ :=
    RankCert.exists_cayley_of_baseEnum hB hbase gens Ts par cl hEnum
  set Q : Subgroup Γ := Subgroup.closure {x | x ∈ gens} with hQ
  have hcardQ : Nat.card Q = 2 ^ k := by
    rw [hQ, benum_card hB hbase gens Ts par cl hEnum, hsize]
  have hQp2 : IsPGroup 2 Q := IsPGroup.of_card hcardQ
  have hQindex : Q.index = m := by
    have h1 := Q.card_mul_index
    rw [hcardQ, hcard] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hQsyl : IsSylowTwoOf Q ⊤ := K1.isSylowTwoOf_top_iff.mpr ⟨hQp2, by
    rw [hQindex]; exact fun hd => (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr hd)⟩
  have hgl : (genTabs n gens).length = gens.length := by simp [genTabs]
  simp only [fusionCheck, hgl, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq,
    beq_iff_eq, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true'] at hcheck
  obtain ⟨⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, hcen⟩, -⟩, -⟩ := hcheck
  set mulI := RankCert.mulIdx gens.length gens.length par cl Ts.size with hmulI
  have hmul : ∀ i k, i < Ts.size → k < Ts.size →
      mulI i k < Ts.size ∧ ι (mulI i k) = ι i * ι k :=
    fun i k hi hk => hcay.mulIdx_spec Ts.size i k (le_of_lt hi) hi hk
  set z : Γ := ι zi with hz
  have hgen_idx : ∀ j < gens.length, cl[j]! < Ts.size ∧ ι cl[j]! = gens.getD j 1 := by
    intro j hj
    obtain ⟨h1, h2⟩ := hcay.step 0 hcay.pos j hj
    simp only [Nat.zero_mul, Nat.zero_add] at h1 h2
    exact ⟨h1, by rw [h2, hcay.zero, mul_one]⟩
  have hcenQ : ∀ c ∈ Q, (∀ q ∈ Q, c * q = q * c) → c = 1 ∨ c = z := by
    intro c hc hcc
    obtain ⟨i, hiN, rfl⟩ := hsurj c hc
    have hall : (List.range gens.length).all (fun j => mulI cl[j]! i == mulI i cl[j]!) = true := by
      rw [List.all_eq_true]
      intro j hj
      rw [List.mem_range] at hj
      obtain ⟨hclj, -⟩ := hgen_idx j hj
      obtain ⟨h1, h2⟩ := hmul cl[j]! i hclj hiN
      obtain ⟨h3, h4⟩ := hmul i cl[j]! hiN hclj
      rw [beq_iff_eq]
      apply hcay.inj _ h1 _ h3
      rw [h2, h4]
      exact (hcc (ι cl[j]!) (hιQ _ hclj)).symm
    rcases hcen i hiN with (h1 | h1) | h1
    · rw [hall] at h1
      exact absurd h1 (by simp)
    · left
      rw [h1, hcay.zero]
    · right
      rw [h1]
  intro U hU c hc d hd hcc hdc hc1 hd1
  obtain ⟨g₀, hg₀⟩ := Vol2Native.A312L.exists_conj_of_isSylowTwoOf hU hQsyl
  have hmemQ : ∀ x ∈ U, g₀ * x * g₀⁻¹ ∈ Q := fun x hx => by
    rw [← hg₀]
    exact ⟨x, hx, rfl⟩
  have hcenQ' : ∀ x ∈ U, (∀ u ∈ U, x * u = u * x) → x ≠ 1 → g₀ * x * g₀⁻¹ = z := by
    intro x hx hxc hx1
    have hcomm : ∀ q ∈ Q, g₀ * x * g₀⁻¹ * q = q * (g₀ * x * g₀⁻¹) := by
      intro q hq
      rw [← hg₀] at hq
      obtain ⟨u, hu, rfl⟩ := hq
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      calc g₀ * x * g₀⁻¹ * (g₀ * u * g₀⁻¹) = g₀ * (x * u) * g₀⁻¹ := by group
        _ = g₀ * (u * x) * g₀⁻¹ := by rw [hxc u hu]
        _ = g₀ * u * g₀⁻¹ * (g₀ * x * g₀⁻¹) := by group
    rcases hcenQ _ (hmemQ x hx) hcomm with h | h
    · exact absurd (conj_eq_one_iff.mp h) hx1
    · exact h
  have h1 := (hcenQ' c hc hcc hc1).trans (hcenQ' d hd hdc hd1).symm
  have h2 : g₀⁻¹ * (g₀ * c * g₀⁻¹) * g₀ = g₀⁻¹ * (g₀ * d * g₀⁻¹) * g₀ := by rw [h1]
  simpa [mul_assoc] using h2

theorem sylowCenterLeTwo_of_fusionCertS {B : List ℕ} (hB : ∀ b ∈ B, b < n)
    (hbase : ∀ g : Γ, (∀ b ∈ B, act n g b = b) → g = 1) (a b : Γ) (prog : List (ℕ × ℕ))
    (hv : slpValidAux prog 2 = true) (qp : List (ℕ × ℕ)) (Ts : Array (List ℕ)) (par cl : Array ℕ)
    (k zi : ℕ) (wits : List (List ℕ × List ℕ × ℕ)) (gws : List (List ℕ)) (m : ℕ)
    (hcard : Nat.card Γ = 2 ^ k * m) (hm : Odd m)
    (hcert : FusionCertS n B (tab n a).toArray (tab n b).toArray prog qp Ts par cl k zi wits gws) :
    SylowCenterLeTwo Γ := by
  obtain ⟨hqp, hinvt, hEnum, hsize, hcheck⟩ := hcert
  set T := slpTabsA (tab n a).toArray (tab n b).toArray prog with hT
  have hinv := slp_foldl_inv (n := n) prog #[a, b] #[(tab n a).toArray, (tab n b).toArray]
    (by simp) (by
      intro i hi
      have hi' : i < 2 := by simpa using hi
      interval_cases i <;> simp) hv
  have hE : ∀ i < T.size, tab n ((slpElts a b prog).getD i 1) = (T[i]!).toList := hinv.2
  have hE' : ∀ i < T.size, (tab n ((slpElts a b prog).getD i 1)).toArray = T[i]! := by
    intro i hi
    rw [hE i hi, Array.toArray_toList]
  have hinv_of : ∀ x y : Γ,
      (∀ q < n, img (tab n y).toArray (img (tab n x).toArray q) = q) → y = x⁻¹ := by
    intro x y hxy
    apply eq_inv_of_mul_eq_one_left
    apply hbase
    intro b hb
    rw [act_mul _ _ (hB b hb)]
    have := hxy b (hB b hb)
    simpa only [img_tab] using this
  set gens : List Γ := qp.map fun p => (slpElts a b prog).getD p.1 1 with hgens
  have hG : genTabs n gens = qp.map fun p => T[p.1]! := by
    simp only [genTabs, hgens, List.map_map]
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp_apply]
    exact hE' p.1 (hqp p hp).1
  have hGi : genTabsInv n gens = qp.map fun p => T[p.2]! := by
    simp only [genTabsInv, hgens, List.map_map]
    apply List.map_congr_left
    intro p hp
    simp only [Function.comp_apply]
    have h1 : (slpElts a b prog).getD p.2 1 = ((slpElts a b prog).getD p.1 1)⁻¹ := by
      apply hinv_of
      rw [hE' p.1 (hqp p hp).1, hE' p.2 (hqp p hp).2]
      exact hinvt p hp
    rw [← h1]
    exact hE' p.2 (hqp p hp).2
  rw [← hG, ← hGi] at hEnum
  rw [← hG] at hcheck
  exact sylowCenterLeTwo_of_fusionCheck hB hbase a b gens Ts par cl k m hcard hm hEnum hsize hcheck

end Main

section M24

open CFSG.Sporadic.Mathieu (m24a m24b card_M24)

theorem m24_group_sylowCenterLeTwo :
    SylowCenterLeTwo ↥CFSG.Blueprint.NativeSporadic.M24 :=
  sylowCenterLeTwo_of_fusionCertS (n := 24) (B := List.range 24)
    (fun b hb => List.mem_range.mp hb) base_of_faithful m24a m24b m24Prog m24_valid m24Qp
    m24Enum.1 m24Enum.2.1 m24Enum.2.2 10 m24ZI m24Wit m24GW 239085
    (by rw [card_M24]; norm_num) (by decide) (by
      rw [m24_tab_a, m24_tab_b]
      exact m24_fusionCert)

theorem m24_sylowCenterLeTwo :
    SylowCenterLeTwo (Carrier .M24) := by
  have h := m24_group_sylowCenterLeTwo
  exact h

end M24

section He

open CFSG.Sporadic.He

theorem he_group_sylowCenterLeTwo :
    SylowCenterLeTwo ↥J := by
  have ha : tab 8330 (a : J) = heTa.toList := by
    rw [tab_eq_of_rep (n := 8330) _ (a : J) rep_alpha]
    simp [heTa, orb]
  have hb : tab 8330 (b : J) = heTb.toList := by
    rw [tab_eq_of_rep (n := 8330) _ (b : J) rep_beta]
    simp [heTb, orb]
  exact sylowCenterLeTwo_of_fusionCertS (n := 8330) (B := heB) he_base_lt he_base_property
    (a : J) (b : J) heProg he_valid heQp heEnum.1 heEnum.2.1 heEnum.2.2 10 heZI heWit heGW 3935925
    (by rw [card_J]; norm_num) (by decide) (by
      rw [ha, hb, Array.toArray_toList, Array.toArray_toList]
      exact he_fusionCert)

theorem he_sylowCenterLeTwo :
    SylowCenterLeTwo (Carrier .He) := by
  have h : SylowCenterLeTwo CFSG.Blueprint.NativeSporadic.He :=
    SylowCenterLeTwo.of_mulEquiv (X := CFSG.Blueprint.NativeSporadic.He) (Y := ↥J) heEquivJ
      he_group_sylowCenterLeTwo
  exact h

end He

section Ru

open CFSG.Sporadic.SmallF2
open CFSG.Sporadic.Ru.Native (ruData)

theorem ru_group_sylowCenterLeTwo :
    SylowCenterLeTwo ↥(J ruData) := by
  have hF : Facts ruData 3 := CFSG.Sporadic.Ru.ruFacts
  have ha : tab ruData.n (a ruData) = ruTa.toList := by
    rw [tab_eq_of_rep (n := ruData.n) _ (a ruData) (rep_a hF.toBaseFacts)]
    simp [ruTa]
  have hb : tab ruData.n (b ruData) = ruTb.toList := by
    rw [tab_eq_of_rep (n := ruData.n) _ (b ruData) (rep_b hF.toBaseFacts)]
    simp [ruTb]
  have hcard0 : Nat.card (J ruData) = 145926144000 :=
    (Nat.card_congr (seedEquiv hF.toBaseFacts).toEquiv).symm.trans CFSG.Sporadic.Ru.card_Ru
  have hcard : Nat.card (J ruData) = 2 ^ 14 * 8906625 := by
    rw [hcard0]; norm_num
  exact sylowCenterLeTwo_of_fusionCertS (n := ruData.n) (B := ruB) (base_lt hF)
    (base_property hF) (a ruData) (b ruData) ruProg ru_valid ruQp ruEnum.1 ruEnum.2.1 ruEnum.2.2
    14 ruZI ruWit ruGW 8906625 hcard (by decide) (by
      rw [ha, hb, Array.toArray_toList, Array.toArray_toList]
      exact ru_fusionCert)

theorem ru_sylowCenterLeTwo :
    SylowCenterLeTwo (Carrier .Ru) := by
  have hF : Facts ruData 3 := CFSG.Sporadic.Ru.ruFacts
  have h : SylowCenterLeTwo CFSG.Blueprint.NativeSporadic.Ru :=
    SylowCenterLeTwo.of_mulEquiv (X := CFSG.Blueprint.NativeSporadic.Ru) (Y := ↥(J ruData))
      (seedEquiv hF.toBaseFacts) ru_group_sylowCenterLeTwo
  exact h

end Ru

end Sec1216Ctr

end CFSG.Quasithin.H13
