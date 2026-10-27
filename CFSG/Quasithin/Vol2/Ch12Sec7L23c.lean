module

public import CFSG.Quasithin.Vol2.Ch12Sec7L23b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits E3
open scoped IsMulCommutative

namespace S127

variable {G : Type} [Group G] [Finite G]

theorem modules_g_of_1222 (h1222 : Stmt12_2_2) {T L V : Subgroup G} (h : Hyp1271 G T L V) :
    CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) ∧
      Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 ∧
      Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
        alternatingGroup (Fin 6)) ∧
      L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L ∧ Nat.card V = 2 ^ 6 ∧
      IsIrreducibleUnder L V := by
  have hy := h.hyp
  obtain ⟨-, -, hall⟩ := ((h1222 G T hy.simple hy.nonabelian hy.qtke hy.sylow).resolve_left
    hy.notAlt) L hy.maximal hy.faithful hy.quasisimple
  obtain ⟨-, -, -, ⟨_, hmod⟩⟩ := hall V hy.irrPlus
  have hQ := card_quot_of_hatA6Quot h.hatA6
  have hsl : ∀ n : ℕ, (n = 3 ∨ n = 4 ∨ n = 5) →
      ¬ 135 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)) := by
    intro n hn
    rcases hn with rfl | rfl | rfl <;> rw [Matrix.card_SL_field, ZMod.card] <;> decide
  rcases hmod with ⟨n, hn, ⟨e⟩, -⟩ | ⟨⟨e⟩, -, -⟩ | ⟨⟨e⟩, -, -⟩ |
      ⟨m, hm5, hm8, ⟨φ, hφ, hker⟩, -⟩ | ⟨-, φ, hφ, hker⟩ | ⟨hU, -⟩ | hg
  · exact absurd (dvd_card_quot_pCore h.hatA6 e) (hsl n hn)
  · exact absurd (dvd_card_quot_pCore h.hatA6 e) (hsl 3 (Or.inl rfl))
  · exact absurd (dvd_card_quot_pCore h.hatA6 e) (hsl 5 (Or.inr (Or.inr rfl)))
  · exfalso
    apply card_alternating_ne hm5 hm8
    rw [← hQ, ← hker]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv).symm
  · exfalso
    apply card_alternating_ne (n := 7) (by norm_num) (by norm_num)
    rw [← hQ, ← hker]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv).symm
  · exfalso
    rcases hU with ⟨-, hU⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
    · have h135 := dvd_card_quot_pCore h.hatA6 (MulEquiv.refl _)
      rw [F420.card_of_u33 hU] at h135
      exact absurd h135 (by decide)
    all_goals exact absurd h0 (by norm_num)
  · exact hg

theorem XOf_le (L : Subgroup G) : XOf L ≤ L :=
  (oTwoUpper_le _).trans (Subgroup.map_subtype_le _)

theorem commutator_mem_centralizer_of_mem_XOf (h1222 : Stmt12_2_2) {T L V : Subgroup G}
    (h : Hyp1271 G T L V) {x : G} (hx : x ∈ XOf L) {l : G} (hl : l ∈ L) :
    x * l * x⁻¹ * l⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  have hxZ : x ∈ oTwoZIn L := oTwoUpper_le _ hx
  unfold oTwoZIn preimageModTwoCore at hxZ
  obtain ⟨y, hy, rfl⟩ := hxZ
  rw [SetLike.mem_coe, Subgroup.mem_comap] at hy
  have hc : (QuotientGroup.mk (y * ⟨l, hl⟩ * y⁻¹ * (⟨l, hl⟩ : ↥L)⁻¹) :
      ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
    have h1 := Subgroup.mem_center_iff.1 hy (QuotientGroup.mk ⟨l, hl⟩)
    simp only [QuotientGroup.mk'_apply] at h1
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv, ← h1]
    group
  rw [QuotientGroup.eq_one_iff] at hc
  have hO : ((y * ⟨l, hl⟩ * y⁻¹ * (⟨l, hl⟩ : ↥L)⁻¹ : ↥L) : G) ∈ pCoreOf 2 L :=
    ⟨_, by exact hc, rfl⟩
  rw [← inf_centralizer_eq_of_1222 h1222 h] at hO
  simpa using hO.2

theorem fpf_of_mem_XOf (h1222 : Stmt12_2_2) {T L V : Subgroup G} (h : Hyp1271 G T L V) {x : G}
    (hx : x ∈ XOf L) (hxV : x ∉ Subgroup.centralizer (V : Set G)) {w : G} (hw : w ∈ V)
    (hxw : x * w * x⁻¹ = w) : w = 1 := by
  obtain ⟨-, -, -, -, -, hirr⟩ := modules_g_of_1222 h1222 h
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := h.hyp.irrPlus.2.2.1
  set W := V ⊓ Subgroup.centralizer ({x} : Set G) with hWdef
  have key : ∀ l ∈ L, ∀ u ∈ W, l * u * l⁻¹ ∈ W := by
    intro l hl u hu
    obtain ⟨huV, huC⟩ := Subgroup.mem_inf.1 hu
    have hlu : l * u * l⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.1 (hLV hl) u).1 huV
    refine Subgroup.mem_inf.2 ⟨hlu, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc := commutator_mem_centralizer_of_mem_XOf h1222 h hx hl
    have hcu := Subgroup.mem_centralizer_iff.1 hc _ hlu
    have hxu : x * u = u * x := (Subgroup.mem_centralizer_singleton_iff.1 huC).symm
    calc l * u * l⁻¹ * x
        = (x * l * x⁻¹ * l⁻¹) * (l * u * l⁻¹) * (x * l * x⁻¹ * l⁻¹)⁻¹ * x := by rw [← hcu]; group
      _ = x * (l * (x⁻¹ * u * x) * l⁻¹) := by group
      _ = x * (l * u * l⁻¹) := by
          rw [show x⁻¹ * u * x = u by rw [mul_assoc, ← hxu]; group]
  have hWL : L ≤ Subgroup.normalizer (W : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨key l hl u, fun hu => ?_⟩
    have := key l⁻¹ (L.inv_mem hl) _ hu
    rwa [show l⁻¹ * (l * u * l⁻¹) * l⁻¹⁻¹ = u by group] at this
  rcases hirr.2 W inf_le_left hWL with hW | hW
  · have : w ∈ W := Subgroup.mem_inf.2 ⟨hw, by
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc w * x = x * w * x⁻¹ * x := by rw [hxw]
        _ = x * w := by group⟩
    rwa [hW, Subgroup.mem_bot] at this
  · exfalso
    apply hxV
    refine Subgroup.mem_centralizer_iff.2 fun v hv => ?_
    have : v ∈ W := hW ▸ hv
    exact Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 this).2

theorem centralizer_z_le (h1222 : Stmt12_2_2) (h2 : Lemma12_7_2) (h128 : Stmt12_2_8)
    {T L V : Subgroup G} {t z : G} (hS : Setting1274 G T L V t z) :
    L ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.centralizer (V1 T L V : Set G) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hcomm, -, -⟩ := card_eq_of_1222 h1222 hS.hyp
  have := hcomm
  obtain ⟨-, -, ⟨hV1pt, -⟩, -, -, ⟨-, hset, -, -⟩, -⟩ := h2 G T L V hS.hyp
  have hXmem : XOf L ∈ {I : Subgroup G | I ≤ P1 T L V ∧ T ≤ Subgroup.normalizer (I : Set G) ∧
      oTwoUpper I = I ∧ (pCoreOf 2 I).relIndex I = 3} := by
    rw [hset]
    exact Set.mem_insert_of_mem _ rfl
  obtain ⟨-, -, -, hX3⟩ := hXmem
  have h3X : 3 ∣ Nat.card (XOf L) := by
    rw [← hX3]
    exact Dvd.intro _ (Subgroup.relIndex_mul_card (H := pCoreOf 2 (XOf L)) (K := XOf L))
  obtain ⟨⟨x, hxX⟩, hx3⟩ := exists_prime_orderOf_dvd_card' 3 h3X
  rw [Subgroup.orderOf_mk] at hx3
  have hxM : x ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer (XOf_le L hxX)
  have hxV : x ∉ Subgroup.centralizer (V : Set G) :=
    fun hc => not_orderOf_three_of_mem_centralizer h1222 h128 hS.hyp hxM hc hx3
  have hx2X : x ^ 2 ∈ XOf L := Subgroup.pow_mem _ hxX 2
  have hx23 : orderOf (x ^ 2) = 3 := by
    rw [orderOf_pow' _ (by norm_num), hx3]
    norm_num
  have hx2V : x ^ 2 ∉ Subgroup.centralizer (V : Set G) := fun hc =>
    not_orderOf_three_of_mem_centralizer h1222 h128 hS.hyp (Subgroup.pow_mem _ hxM 2) hc hx23
  have hzV : z ∈ V := (Subgroup.mem_inf.1 hS.z_mem).1
  have hzV1 : z ∈ V1 T L V := hS.z_mem
  have hV1V : V1 T L V ≤ V := hV1pt.1.1
  have hXV1 : XOf L ≤ Subgroup.normalizer (V1 T L V : Set G) := hV1pt.1.2
  set a := x * z * x⁻¹ with ha
  set b := x ^ 2 * z * (x ^ 2)⁻¹ with hb
  have haV1 : a ∈ V1 T L V := (Subgroup.mem_normalizer_iff.1 (hXV1 hxX) z).1 hzV1
  have hbV1 : b ∈ V1 T L V := (Subgroup.mem_normalizer_iff.1 (hXV1 hx2X) z).1 hzV1
  have hz1 := hS.z_ne_one
  have hfx : ∀ {u : G}, u ∈ XOf L → u ∉ Subgroup.centralizer (V : Set G) →
      u * z * u⁻¹ ≠ z := fun hu huV h => hz1 (fpf_of_mem_XOf h1222 hS.hyp hu huV hzV h)
  have hconj1 : ∀ u : G, u * z * u⁻¹ ≠ 1 := fun u h => hz1 (by
    have : z = u⁻¹ * (u * z * u⁻¹) * u := by group
    rw [this, h]
    group)
  have hza : z ≠ a := fun h => hfx hxX hxV h.symm
  have hzb : z ≠ b := fun h => hfx hx2X hx2V h.symm
  have hab : a ≠ b := by
    intro h
    apply hfx hxX hxV
    calc x * z * x⁻¹ = x⁻¹ * b * x := by rw [hb]; group
      _ = x⁻¹ * a * x := by rw [h]
      _ = z := by rw [ha]; group
  have ha1 : a ≠ 1 := hconj1 x
  have hb1 : b ≠ 1 := hconj1 (x ^ 2)
  have hV1S : ∀ w ∈ V1 T L V, w = 1 ∨ w = z ∨ w = a ∨ w = b := by
    intro w hw
    by_contra hne
    simp only [not_or] at hne
    obtain ⟨hw1, hwz, hwa, hwb⟩ := hne
    have h1 : (1 : G) ∉ ({z, a, b, w} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hz1, Ne.symm ha1, Ne.symm hb1, Ne.symm hw1⟩
    have h2 : z ∉ ({a, b, w} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hza, hzb, Ne.symm hwz⟩
    have h3 : a ∉ ({b, w} : Finset G) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨hab, Ne.symm hwa⟩
    have hF : ({1, z, a, b, w} : Finset G).card = 5 := by
      rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
        Finset.card_insert_of_notMem h3, Finset.card_pair (Ne.symm hwb)]
    have hsub : (↑({1, z, a, b, w} : Finset G) : Set G) ⊆ (V1 T L V : Set G) := by
      intro u hu
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl | rfl | rfl
      · exact (V1 T L V).one_mem
      · exact hzV1
      · exact haV1
      · exact hbV1
      · exact hw
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [Set.ncard_coe_finset, hF] at hle
    have h4 : (V1 T L V : Set G).ncard = 4 := by
      rw [← Nat.card_coe_set_eq]
      exact hV1pt.2
    omega
  have hfix : ∀ y ∈ L ⊓ Subgroup.centralizer ({z} : Set G), ∀ u ∈ XOf L,
      y * (u * z * u⁻¹) = (u * z * u⁻¹) * y := by
    intro y hy u hu
    obtain ⟨hyL, hyz⟩ := Subgroup.mem_inf.1 hy
    have hyz' : y * z = z * y := Subgroup.mem_centralizer_singleton_iff.1 hyz
    have hc := commutator_mem_centralizer_of_mem_XOf h1222 hS.hyp (Subgroup.inv_mem _ hu) hyL
    rw [inv_inv] at hc
    have hcz := Subgroup.mem_centralizer_iff.1 hc z hzV
    have e1 : y * (u * z * u⁻¹) * y⁻¹ =
        u * ((u⁻¹ * y * u * y⁻¹) * (y * z * y⁻¹) * (u⁻¹ * y * u * y⁻¹)⁻¹) * u⁻¹ := by group
    have e2 : y * z * y⁻¹ = z := by rw [hyz', mul_inv_cancel_right]
    have e3 : (u⁻¹ * y * u * y⁻¹) * z * (u⁻¹ * y * u * y⁻¹)⁻¹ = z := by
      rw [← hcz, mul_inv_cancel_right]
    rw [e2, e3] at e1
    calc y * (u * z * u⁻¹) = y * (u * z * u⁻¹) * y⁻¹ * y := by group
      _ = u * z * u⁻¹ * y := by rw [e1]
  intro y hy
  refine Subgroup.mem_centralizer_iff.2 fun w hw => ?_
  rcases hV1S w hw with rfl | rfl | rfl | rfl
  · rw [one_mul, mul_one]
  · exact (Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 hy).2).symm
  · exact (hfix y hy x hxX).symm
  · exact (hfix y hy (x ^ 2) hx2X).symm

end S127

end CFSG.Quasithin.H13
