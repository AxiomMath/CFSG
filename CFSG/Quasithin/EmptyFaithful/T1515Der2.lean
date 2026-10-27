module

public import CFSG.Quasithin.EmptyFaithful.S1414Group
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.EmptyFaithful.T1515B

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem normalizer_le_normalizer_oPrimeResidualOf1516 (p : ℕ) (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (oPrimeResidualOf p X : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ y ∈ oPrimeResidualOf p X,
      g * y * g⁻¹ ∈ oPrimeResidualOf p X := by
    intro g hg y hy
    induction hy using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hxX, k, hk⟩ := hx
      refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxX, k, ?_⟩
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hk
    | one => simp
    | mul x y _ _ ihx ihy => simpa [mul_assoc] using (oPrimeResidualOf p X).mul_mem ihx ihy
    | inv x _ ih => simpa [mul_assoc] using (oPrimeResidualOf p X).inv_mem ih
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key g hg x hx, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using this

omit [Finite G] in
private theorem le_oddCoreIn1516 {H K : Subgroup G} (hKH : K ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (K : Set G)) (hodd : Odd (Nat.card K)) :
    K ≤ oddCoreIn H := by
  have hnormal : (K.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mpr hnorm
  have hodd' : Odd (Nat.card (K.subgroupOf H)) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv]
  have hle : K.subgroupOf H ≤ fusionOddCore H := le_sSup ⟨hnormal, hodd'⟩
  intro k hk
  exact ⟨⟨k, hKH hk⟩, hle hk, rfl⟩

theorem central_three_elt_eq_one1516 {Z₁ L : Subgroup G} (hL : L = oPrimeResidualOf 3 (g1_1516 Z₁))
    (hO : oddCoreIn (g1_1516 Z₁) = ⊥) {x : G} (hxL : x ∈ L)
    (hxC : x ∈ Subgroup.centralizer (L : Set G)) (hx3 : ∃ k : ℕ, orderOf x = 3 ^ k) : x = 1 := by
  obtain ⟨k, hk⟩ := hx3
  set G1 := g1_1516 Z₁ with hG1
  have hLG : L ≤ G1 := by
    rw [hL]
    exact oPrimeResidualOf_le1516 3 G1
  have hLN : G1 ≤ Subgroup.normalizer (L : Set G) := by
    rw [hL]
    exact (Subgroup.le_normalizer : G1 ≤ Subgroup.normalizer (G1 : Set G)).trans
      (normalizer_le_normalizer_oPrimeResidualOf1516 3 G1)
  set P : Set G := {z | ∃ g ∈ G1, z = g * x * g⁻¹} with hP
  have hxP : x ∈ P := ⟨1, G1.one_mem, by simp⟩
  have hPL : ∀ z ∈ P, z ∈ L := by
    rintro z ⟨g, hg, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hLN hg) x).mp hxL
  have hPC : ∀ z ∈ P, z ∈ Subgroup.centralizer (L : Set G) := by
    rintro z ⟨g, hg, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : g⁻¹ * l * g ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hLN (G1.inv_mem hg)) l).mp hl
    have h := Subgroup.mem_centralizer_iff.mp hxC _ hl'
    calc l * (g * x * g⁻¹) = g * (g⁻¹ * l * g * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * l * g)) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * l := by group
  have hPord : ∀ z ∈ P, orderOf z = 3 ^ k := by
    rintro z ⟨g, hg, rfl⟩
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hk
  have hPcomm : P ⊆ (Subgroup.centralizer P : Set G) := fun z hz => by
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_iff.mp (hPC z hz) w (hPL w hw)
  have hNle : Subgroup.closure P ≤ Subgroup.centralizer (Subgroup.closure P : Set G) := by
    rw [Subgroup.centralizer_closure]
    exact (Subgroup.closure_le _).mpr hPcomm
  have hNcomm : ∀ a ∈ Subgroup.closure P, ∀ b ∈ Subgroup.closure P, a * b = b * a :=
    fun a ha b hb => Subgroup.mem_centralizer_iff.mp (hNle hb) a ha
  have hNexp : ∀ y ∈ Subgroup.closure P, y ^ 3 ^ k = 1 := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem z hz => rw [← hPord z hz]; exact pow_orderOf_eq_one z
    | one => simp
    | mul a b ha hb iha ihb => rw [Commute.mul_pow (hNcomm a ha b hb), iha, ihb, one_mul]
    | inv a _ ih => rw [inv_pow, ih, inv_one]
  have hNnorm : G1 ≤ Subgroup.normalizer (Subgroup.closure P : Set G) := by
    have key : ∀ g ∈ G1, ∀ y ∈ Subgroup.closure P, g * y * g⁻¹ ∈ Subgroup.closure P := by
      intro g hg y hy
      induction hy using Subgroup.closure_induction with
      | mem z hz =>
        obtain ⟨h, hh, rfl⟩ := hz
        refine Subgroup.subset_closure ⟨g * h, G1.mul_mem hg hh, ?_⟩
        group
      | one => simp
      | mul a b _ _ iha ihb => simpa [mul_assoc] using (Subgroup.closure P).mul_mem iha ihb
      | inv a _ ih => simpa [mul_assoc] using (Subgroup.closure P).inv_mem ih
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨key g hg y, fun hy => ?_⟩
    have := key g⁻¹ (G1.inv_mem hg) _ hy
    simpa [mul_assoc] using this
  have hNG : Subgroup.closure P ≤ G1 := (Subgroup.closure_le G1).mpr fun z hz => hLG (hPL z hz)
  have hNp : IsPGroup 3 (Subgroup.closure P) := fun y => ⟨k, Subtype.ext (by simpa using hNexp y y.2)⟩
  have hNodd : Odd (Nat.card (Subgroup.closure P)) := by
    obtain ⟨n, hn⟩ := hNp.exists_card_eq
    rw [hn]
    exact Odd.pow (by decide)
  have hle : Subgroup.closure P ≤ oddCoreIn G1 := le_oddCoreIn1516 hNG hNnorm hNodd
  rw [hO] at hle
  exact Subgroup.mem_bot.mp (hle (Subgroup.subset_closure hxP))

theorem not_oTwoUpper_normalizer_le_centralizer1516 {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hM : IsMf T Mc M) (hS : Setting1516 T Mc M Z₁ Z₂ V₁ V₂)
    (hsmall : Ce15Small T Mc M) (h15 : Lemma1515Concl T Mc M) (h19 : Lemma1519Concl T Mc M)
    (h17 : Lemma15117Concl T M Z₁) (hL1 : L = oPrimeResidualOf 3 (g1_1516 Z₁))
    (hLc : ∀ x ∈ L, x ∈ Subgroup.centralizer (L : Set G) → (∃ k : ℕ, orderOf x = 3 ^ k) → x = 1) :
    ¬ oTwoUpper (g1_1516 Z₁ ⊓ Subgroup.normalizer (thompsonJ (s1516 T Z₁) : Set G)) ≤
      Subgroup.centralizer (L : Set G) := by
  intro hle
  set V := V154 T Mc M with hVdef
  set S := s1516 T Z₁ with hSdef
  set G1 := g1_1516 Z₁ with hG1
  set X : Subgroup G := M ⊓ G1 with hXdef
  obtain ⟨⟨-, hYnMZ, -, -⟩, -⟩ := hS.y_facts hsmall
  obtain ⟨y, hyX, ⟨k, hyk⟩, hyMZ⟩ :
      ∃ y ∈ X, (∃ k : ℕ, orderOf y = 3 ^ k) ∧ y ∉ mZ1516 Mc Z₁ := by
    by_contra hcon
    refine hYnMZ ((Subgroup.closure_le _).mpr fun y hy => ?_)
    by_contra hy'
    exact hcon ⟨y, hy.1, hy.2, hy'⟩
  have hMN : M ≤ Subgroup.normalizer (V : Set G) := le_normalizer_V154 T Mc M
  have hTM : T ≤ M := hM.1.1.2
  set N : Subgroup G := M ⊓ Subgroup.centralizer (V : Set G) with hNdef
  have hNX : N ≤ X := fun x hx => ⟨hx.1, Subgroup.centralizer_le hS.z1_le_V hx.2⟩
  have hNmz : N ≤ mZ1516 Mc Z₁ := fun x hx =>
    ⟨Subgroup.centralizer_le hS.z1_le_V hx.2, h15.centralizer_le hx.2⟩
  have hMNN : M ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_inf151 Subgroup.le_normalizer
      (hMN.trans (normalizer_le_normalizer_centralizer _))
  have hXN : X ≤ Subgroup.normalizer (N : Set G) := inf_le_left.trans hMNN
  have hJN : thompsonJ S ≤ N := by
    rw [h17.jS]
    exact le_inf ((thompsonJ_le_self151 T).trans hTM)
      (le_centralizer_of_commutator_eq_bot h19.one_commute)
  have hSyl : IsSylowTwoOf S X := by
    have := h17.sylow
    rwa [inf_comm] at this
  obtain ⟨n, hnN, y', hy', hyy⟩ := S1414.frattini_decomp hSyl hNX hXN hJN y hyX
  have hy'X : y' ∈ X := hy'.1
  have hy'J : y' ∈ Subgroup.normalizer (thompsonJ S : Set G) := hy'.2
  have hyN : y ∈ Subgroup.normalizer (V : Set G) := hMN hyX.1
  have hy'N : y' ∈ Subgroup.normalizer (V : Set G) := hMN hy'X.1
  have hnN' : n ∈ Subgroup.normalizer (V : Set G) := hMN hnN.1
  have hact : conjAct V ⟨y, hyN⟩ = conjAct V ⟨y', hy'N⟩ := by
    have h1 : (⟨y, hyN⟩ : Subgroup.normalizer (V : Set G)) = ⟨n, hnN'⟩ * ⟨y', hy'N⟩ :=
      Subtype.ext hyy
    have h2 : conjAct V ⟨n, hnN'⟩ = 1 := A4.conjAct_eq_one_iff.mpr hnN.2
    rw [h1, map_mul, h2, one_mul]
  have hy_nc : y ∉ Subgroup.centralizer (V : Set G) := fun hc => hyMZ (hNmz ⟨hyX.1, hc⟩)
  have hσ_ne : conjAct V ⟨y, hyN⟩ ≠ 1 := fun h => hy_nc (A4.conjAct_eq_one_iff.mp h)
  obtain ⟨j, hj1, hjord⟩ : ∃ j : ℕ, 1 ≤ j ∧ orderOf (conjAct V ⟨y, hyN⟩) = 3 ^ j := by
    have h1 : orderOf (conjAct V ⟨y, hyN⟩) ∣
        orderOf (⟨y, hyN⟩ : Subgroup.normalizer (V : Set G)) := orderOf_map_dvd _ _
    have h2 : orderOf (⟨y, hyN⟩ : Subgroup.normalizer (V : Set G)) = orderOf y :=
      (Subgroup.orderOf_coe _).symm
    have hdvd : orderOf (conjAct V ⟨y, hyN⟩) ∣ 3 ^ k := by
      rw [h2, hyk] at h1
      exact h1
    obtain ⟨j, -, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    refine ⟨j, ?_, hjeq⟩
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · exfalso
      apply hσ_ne
      rw [h0, pow_zero] at hjeq
      exact orderOf_eq_one_iff.mp hjeq
    · exact h0
  obtain ⟨a, m, hm3, hord⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos y').ne' 3 (by norm_num)
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hord
    exact (orderOf_pos y').ne' hord
  set y₁ : G := y' ^ m with hy₁
  have hy₁ord : orderOf y₁ = 3 ^ a := by
    rw [hy₁, orderOf_pow_of_dvd hm0 ⟨3 ^ a, by rw [hord, mul_comm]⟩, hord,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hy₁X : y₁ ∈ X := Subgroup.pow_mem _ hy'X m
  have hy₁J : y₁ ∈ Subgroup.normalizer (thompsonJ S : Set G) := Subgroup.pow_mem _ hy'J m
  have hy₁N : y₁ ∈ Subgroup.normalizer (V : Set G) := Subgroup.pow_mem _ hy'N m
  have hσ₁ : conjAct V ⟨y₁, hy₁N⟩ = (conjAct V ⟨y, hyN⟩) ^ m := by
    rw [hact, ← map_pow]
    rfl
  have hcop : Nat.Coprime (orderOf (conjAct V ⟨y, hyN⟩)) m := by
    rw [hjord]
    exact Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3)
  have hσ₁ne : conjAct V ⟨y₁, hy₁N⟩ ≠ 1 := by
    rw [hσ₁]
    intro h1
    have h2 := Nat.Coprime.orderOf_pow (y := conjAct V ⟨y, hyN⟩) hcop
    rw [h1, orderOf_one, hjord] at h2
    have h3 : 3 ^ j = 3 ^ 0 := by rw [← h2, pow_zero]
    have h4 := Nat.pow_right_injective (by norm_num : 2 ≤ 3) h3
    omega
  have hy₁Y : y₁ ∈ oPrimeResidualOf 3 X := Subgroup.subset_closure ⟨hy₁X, a, hy₁ord⟩
  have hy₁L : y₁ ∈ L := by
    rw [hL1]
    exact oPrimeResidualOf_mono1516 3 (inf_le_right : X ≤ G1) hy₁Y
  have hy₁O : y₁ ∈ oTwoUpper (G1 ⊓ Subgroup.normalizer (thompsonJ S : Set G)) :=
    mem_oTwoUpper_of_odd ⟨hy₁X.2, hy₁J⟩ (by rw [hy₁ord]; exact Odd.pow (by decide))
  have hy₁C : y₁ ∈ Subgroup.centralizer (L : Set G) := hle hy₁O
  have hy₁1 : y₁ = 1 := hLc y₁ hy₁L hy₁C ⟨a, hy₁ord⟩
  apply hσ₁ne
  have h3 : (⟨y₁, hy₁N⟩ : Subgroup.normalizer (V : Set G)) = 1 := Subtype.ext hy₁1
  rw [h3, map_one]

@[expose] def M11TypesDisjoint1522 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsSporadic .M11 ↥L →
    ¬ IsAltBlockType L 7 ∧ ¬ (IsLnBlock L 3 ∨ IsAltBlockType L 6 ∨ IsG2Block L) ∧
    ¬ (CharTwo L ∧ (IsPSL 4 2 1 (↥L ⧸ CFSG.pCore 2 ↥L) ∨ IsPSL 5 2 1 (↥L ⧸ CFSG.pCore 2 ↥L))) ∧
    ¬ (IsPSU 3 3 1 ↥L ∨ IsTits ↥L ∨ Is3D4 2 1 ↥L) ∧
    ¬ (IsSporadic .J2 (↥L ⧸ Subgroup.center ↥L) ∨ IsSporadic .He (↥L ⧸ Subgroup.center ↥L) ∨
      IsSporadic .M12 (↥L ⧸ Subgroup.center ↥L) ∨ IsSporadic .M22 (↥L ⧸ Subgroup.center ↥L) ∨
      IsSporadic .M23 (↥L ⧸ Subgroup.center ↥L) ∨ IsSporadic .M24 (↥L ⧸ Subgroup.center ↥L)) ∧
    ¬ (IsPSL 4 2 1 ↥L ∨ IsPSL 5 2 1 ↥L)

theorem lemma_15_1_25_two (hD : M11TypesDisjoint1522) {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (hC : Ctx1515 T Mc M Z₁ Z₂ V₁ V₂) (h15 : Lemma1515Concl T Mc M) (h19 : Lemma1519Concl T Mc M)
    (hO : oddCoreIn (g1_1516 Z₁) = ⊥)
    (h17 : Lemma15117Concl T M Z₁) (h22 : Lemma15122Concl T Mc M Z₁ L)
    (h24 : Lemma15124Concl T Mc M Z₁ V₁ V₂ L) (hL1 : L = oPrimeResidualOf 3 (g1_1516 Z₁)) :
    ¬ IsSporadic .M11 ↥L := by
  intro hM11
  obtain ⟨d1, d2, d3, d4, d5, d7⟩ := hD G L hM11
  have hsmall : Ce15Small T Mc M := by
    rcases h24.one with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  rcases h22 with h | h | h | h | h | h | h
  · exact d1 h.1
  · exact d2 h.1
  · exact d3 ⟨h.1, h.2.1⟩
  · exact d4 h.1
  · exact d5 h.1
  · exact not_oTwoUpper_normalizer_le_centralizer1516 hC.mf hC.setting hsmall h15 h19 h17 hL1
      (fun x hxL hxC hx3 => central_three_elt_eq_one1516 hL1 hO hxL hxC hx3) h.2.2
  · exact d7 h.1

end CFSG.Quasithin
