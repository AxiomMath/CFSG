module

public import CFSG.Quasithin.H13.L32A727i
public import CFSG.Quasithin.H13.L32A727l
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.H13.L32A727f
public import CFSG.Quasithin.H13.L32A727g

public section

namespace CFSG.Quasithin.H13.L32A.R727

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

omit [Finite G] in
theorem l1_star_le_of_odd {S : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hl1H : l1 T L V ≤ H)
    (hS : ∀ y ∈ modO2Image H (l1 T L V), Odd (orderOf y) → y ∈ S) :
    modO2Image H (l1 T L V) ≤ S := by
  have hle : l1 T L V ≤ pre H S := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    have hxl : x ∈ l1 T L V := Subgroup.subset_closure hx
    have hxH : x ∈ H := hl1H hxl
    refine (mem_pre ⟨x, hxH⟩).mpr (hS _ ⟨⟨x, hxH⟩, Subgroup.mem_subgroupOf.mpr hxl, rfl⟩ ?_)
    have h1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩) ∣ orderOf x := by
      rw [← Subgroup.orderOf_mk x hxH]
      exact orderOf_map_dvd _ _
    exact Odd.of_dvd_nat hx.2 h1
  exact (modO2Image_mono' hle).trans (modO2Image_pre _).le

theorem exists_card_l1_star_dvd (S : Setting147 G T L V H) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) :
    ∃ a : ℕ, Nat.card ↥(modO2Image H (l1 T L V)) ∣ 3 * 2 ^ a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hl1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hdvd : Nat.card ↥(modO2Image H (l1 T L V)) ∣ Nat.card ↥(l1 T L V) := by
    have h1 := Subgroup.card_map_dvd ((l1 T L V).subgroupOf H)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hl1H).toEquiv] at h1
  have hidx := (M76.relIndex_l1_T S h1222 h1332 h1334).1
  have hcard : Nat.card ↥(l1 T L V) = 3 * Nat.card ↥(pCoreOf 2 (l1 T L V)) := by
    have h1 := Subgroup.relIndex_mul_card (H := pCoreOf 2 (l1 T L V)) (K := l1 T L V)
    rw [inf_eq_left.mpr (pCoreOf_le 2 (l1 T L V)), hidx] at h1
    exact h1.symm
  obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 (l1 T L V)).exists_card_eq
  exact ⟨a, by rw [hcard, ha] at hdvd; exact hdvd⟩

theorem pow_three_of_odd (S : Setting147 G T L V H) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) {y : ↥H ⧸ CFSG.pCore 2 ↥H}
    (hy : y ∈ modO2Image H (l1 T L V)) (hodd : Odd (orderOf y)) : y ^ 3 = 1 := by
  obtain ⟨a, hdvd⟩ := exists_card_l1_star_dvd S h1222 h1332 h1334
  have hxd : orderOf y ∣ 3 * 2 ^ a := (Subgroup.orderOf_dvd_natCard _ hy).trans hdvd
  have h2 : ¬ 2 ∣ orderOf y := fun h => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  have hcop : Nat.Coprime (orderOf y) (2 ^ a) :=
    Nat.Coprime.pow_right a ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).symm
  exact orderOf_dvd_iff_pow_eq_one.mp (hcop.dvd_of_dvd_mul_right hxd)

theorem theta_eq_neg_one (S : Setting147 G T L V H) (h76 : Lemma14_7_6)
    (hs : Group.IsSolvable (↥H ⧸ CFSG.pCore 2 ↥H))
    {X : Subgroup ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))}
    (hXf : ∀ α : MulAut ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)), (orderOf α).Coprime 3 →
      (∀ x ∈ X, x⁻¹ * α x ∈ frattiniIn X) → α = 1)
    (Θ : (↥H ⧸ CFSG.pCore 2 ↥H) →* GL (Fin 2) (ZMod 3))
    (hΘ : ∀ g, Θ g = 1 → ∀ x ∈ X, x⁻¹ * MulAut.conjNormal g x ∈ frattiniIn X)
    {j : ↥H ⧸ CFSG.pCore 2 ↥H} (hjL : j ∈ modO2Image H (l1 T L V)) (hj2 : orderOf j = 2) :
    Θ j = -1 := by
  have : (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).Normal := CFSG.pCore_normal
  have hl1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hdetL : modO2Image H (l1 T L V) ≤ (Matrix.GeneralLinearGroup.det.comp Θ).ker := by
    refine l1_star_le_of_odd hl1H fun y _ hodd => ?_
    rw [MonoidHom.mem_ker]
    have hu1 : (Matrix.GeneralLinearGroup.det.comp Θ) y ^ orderOf y = 1 := by
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    have hu2 : (Matrix.GeneralLinearGroup.det.comp Θ) y ^ 2 = 1 := by
      have h : ∀ v : (ZMod 3)ˣ, v ^ 2 = 1 := by decide
      exact h _
    have h2 : ¬ 2 ∣ orderOf y := fun h =>
      (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
    have hg : Nat.gcd (orderOf y) 2 = 1 :=
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr h2).symm
    have h1 := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hu1) (orderOf_dvd_of_pow_eq_one hu2)
    rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at h1
    exact h1
  have hjj : j ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hj2)
  have hΘjj : Θ j * Θ j = 1 := by
    rw [← map_mul, ← sq, show j ^ 2 = 1 by simpa using hjj, map_one]
  have hdet : ((Θ j : GL (Fin 2) (ZMod 3)) : Matrix (Fin 2) (Fin 2) (ZMod 3)).det = 1 := by
    have h := MonoidHom.mem_ker.mp (hdetL hjL)
    have := congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) h
    simpa using this
  have hj1 : j ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hj2
    norm_num at hj2
  have hΘ1 : Θ j ≠ 1 := by
    intro h
    obtain ⟨x, hx, hxF⟩ := not_fix_frattini S h76 hs hXf hjj hj1
    exact hxF (hΘ j h x hx)
  rcases A1c.GL2_eq_one_or_neg_one_of_sq_eq_one (by decide : (2 : ZMod 3) ≠ 0) hΘjj hdet with
    h | h
  · exact absurd h hΘ1
  · exact h

theorem eq_one_of_theta (S : Setting147 G T L V H) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h76 : Lemma14_7_6) (hs : Group.IsSolvable (↥H ⧸ CFSG.pCore 2 ↥H))
    {X : Subgroup ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))}
    (hXf : ∀ α : MulAut ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)), (orderOf α).Coprime 3 →
      (∀ x ∈ X, x⁻¹ * α x ∈ frattiniIn X) → α = 1)
    (hL3 : ¬ IsPGroup 3 ↥(modO2Image H (l1 T L V))) {G' : Type*} [Group G']
    (Θ : (↥H ⧸ CFSG.pCore 2 ↥H) →* G')
    (hΘ : ∀ g, Θ g = 1 → ∀ x ∈ X, x⁻¹ * MulAut.conjNormal g x ∈ frattiniIn X)
    {n : ↥H ⧸ CFSG.pCore 2 ↥H} (hn : n ∈ modO2Image H (l1 T L V)) (hΘn : Θ n = 1) : n = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).Normal := CFSG.pCore_normal
  set L1s := modO2Image H (l1 T L V) with hL1s
  have hl1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  obtain ⟨a, hdvd⟩ := exists_card_l1_star_dvd S h1222 h1332 h1334
  set N := L1s ⊓ Θ.ker with hN
  have hN3 : ∀ m ∈ N, m ^ 3 = 1 := by
    intro m hm
    by_contra hm3
    have hm' : (m ^ 3) ^ 2 ^ a = 1 := by
      rw [← pow_mul]
      exact orderOf_dvd_iff_pow_eq_one.mp ((Subgroup.orderOf_dvd_natCard L1s hm.1).trans hdvd)
    obtain ⟨x, hx, hxF⟩ := not_fix_frattini S h76 hs hXf hm' hm3
    exact hxF (hΘ _ (by rw [map_pow, MonoidHom.mem_ker.mp hm.2, one_pow]) x hx)
  have hNp : IsPGroup 3 ↥N := fun m => ⟨1, Subtype.ext (by simpa using hN3 m m.2)⟩
  by_contra hn1
  have hnN : n ∈ N := ⟨hn, MonoidHom.mem_ker.mpr hΘn⟩
  have hN3le : 3 ≤ Nat.card N := by
    obtain ⟨e, he⟩ := hNp.exists_card_eq
    have he0 : e ≠ 0 := by
      rintro rfl
      rw [pow_zero, Subgroup.card_eq_one] at he
      rw [he] at hnN
      exact hn1 (Subgroup.mem_bot.mp hnN)
    rw [he]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr he0)
  have hL1N : L1s ≤ N := by
    refine l1_star_le_of_odd hl1H fun y hy hodd => ?_
    have hy3 := pow_three_of_odd S h1222 h1332 h1334 hy hodd
    have hkerN : ∀ g, g ∈ Subgroup.normalizer (Θ.ker : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := fun g => by
      rw [Subgroup.normalizer_eq_top_iff.mpr (MonoidHom.normal_ker Θ)]
      exact Subgroup.mem_top g
    have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer (N : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy, hkerN y⟩
    have hc := TJ1.card_sup_mul_card_inf hyN
    have hyc : Nat.card (Subgroup.zpowers y) ∣ 3 := by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hy3
    obtain ⟨e, he⟩ := hNp.exists_card_eq
    have hsup3 : ∃ f, Nat.card ↥(Subgroup.zpowers y ⊔ N) = 3 ^ f := by
      have hd : Nat.card ↥(Subgroup.zpowers y ⊔ N) ∣ 3 ^ (1 + e) := by
        rw [pow_add, pow_one, ← he]
        exact (Dvd.intro _ hc).trans (Nat.mul_dvd_mul_right hyc _)
      obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
      exact ⟨f, hf⟩
    obtain ⟨f, hf⟩ := hsup3
    have hsupL : Subgroup.zpowers y ⊔ N ≤ L1s :=
      sup_le ((Subgroup.zpowers_le).mpr hy) inf_le_left
    have hfd : 3 ^ f ∣ 3 * 2 ^ a := hf ▸ (Subgroup.card_dvd_of_le hsupL).trans hdvd
    have hcop : Nat.Coprime (3 ^ f) (2 ^ a) := Nat.Coprime.pow f a (by norm_num)
    have hf3 : 3 ^ f ≤ 3 := Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_right hfd)
    have heq : N = Subgroup.zpowers y ⊔ N :=
      Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hf]; omega)
    rw [heq]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  exact hL3 (hNp.to_le hL1N)

theorem false_of_isPOnePlusTwo (S : Setting147 G T L V H) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h76 : Lemma14_7_6)
    (hs : Group.IsSolvable (↥H ⧸ CFSG.pCore 2 ↥H))
    {X : Subgroup ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))}
    (hXf : ∀ α : MulAut ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)), (orderOf α).Coprime 3 →
      (∀ x ∈ X, x⁻¹ * α x ∈ frattiniIn X) → α = 1)
    (hX : IsPOnePlusTwo 3 ↥X)
    (hKn : (X.map (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).subtype).Normal)
    (hL3 : ¬ IsPGroup 3 ↥(modO2Image H (l1 T L V))) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).Normal := CFSG.pCore_normal
  have hl1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  set K := X.map (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).subtype with hKdef
  have := hKn
  have hK : IsPOnePlusTwo 3 ↥K :=
    isPOnePlusTwo_of_mulEquiv (X.equivMapOfInjective _ (Subgroup.subtype_injective _)) hX
  obtain ⟨Θ, hΘ1, hΘneg⟩ := A1c.exists_actGL (p := 3) hK
  have hΦ : frattini ↥X = Subgroup.center ↥X := A1c.frattini_eq_center_of_isPOnePlusTwo hX
  have hΘ : ∀ g, Θ g = 1 → ∀ x ∈ X, x⁻¹ * MulAut.conjNormal g x ∈ frattiniIn X := by
    intro g hg x hx
    have hxK : (x : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ K := ⟨x, hx, rfl⟩
    have hz := (hΘ1 g).mp hg _ hxK
    rw [A1c.mem_centerOf_iff] at hz
    set z := g * (x : ↥H ⧸ CFSG.pCore 2 ↥H) * g⁻¹ * (x : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ with hzdef
    have hw : ((x⁻¹ * MulAut.conjNormal g x : ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))) :
        ↥H ⧸ CFSG.pCore 2 ↥H) = z := by
      rw [Subgroup.coe_mul, MulAut.conjNormal_apply, Subgroup.coe_inv]
      have hxz : (x : ↥H ⧸ CFSG.pCore 2 ↥H) * z = z * x := hz.2 _ hxK
      calc (x : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ * (g * x * g⁻¹)
          = (x : ↥H ⧸ CFSG.pCore 2 ↥H)⁻¹ * (z * x) := by rw [hzdef]; group
        _ = z := by rw [← hxz]; group
    obtain ⟨w, hwX, hwe⟩ := (show ((x⁻¹ * MulAut.conjNormal g x :
        ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ K from hw ▸ hz.1)
    have hw' : w = x⁻¹ * MulAut.conjNormal g x := Subgroup.subtype_injective _ hwe
    rw [frattiniIn, hΦ]
    refine ⟨⟨w, hwX⟩, Subgroup.mem_center_iff.mpr fun v => Subtype.ext ?_, hw'⟩
    have hvK : ((v : ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))) : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ K :=
      ⟨v, v.2, rfl⟩
    have h1 := hz.2 _ hvK
    apply Subgroup.subtype_injective (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))
    simp only [Subgroup.coe_mul, Subgroup.coe_subtype]
    rw [hw', hw]
    exact h1
  obtain ⟨j, hjL, hj2⟩ := exists_involution_l1_star S h1222 h1332 h1334 hL3
  have hΘj : Θ j = -1 := theta_eq_neg_one S h76 hs hXf Θ hΘ hjL hj2
  have ht : ∀ y ∈ K, j * y * j⁻¹ * y ∈ centerOf K := (hΘneg j).mp hΘj
  obtain ⟨b, hbL, hb3, hΘb⟩ :
      ∃ b ∈ modO2Image H (l1 T L V), b ^ 3 = 1 ∧ Θ b ≠ 1 := by
    by_contra h
    push Not at h
    have hle : modO2Image H (l1 T L V) ≤ Θ.ker := l1_star_le_of_odd hl1H fun y hy hodd =>
      MonoidHom.mem_ker.mpr (h y hy (pow_three_of_odd S h1222 h1332 h1334 hy hodd))
    have := MonoidHom.mem_ker.mp (hle hjL)
    rw [hΘj] at this
    exact A1c.neg_one_ne_one_GL_three this
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact hΘb (map_one Θ)
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hjb : j * b = b * j := by
    have hc : j * b * j⁻¹ * b⁻¹ = 1 := by
      refine eq_one_of_theta S h1222 h1332 h1334 h76 hs hXf hL3 Θ hΘ ?_ ?_
      · exact (modO2Image H (l1 T L V)).mul_mem ((modO2Image H (l1 T L V)).mul_mem
          ((modO2Image H (l1 T L V)).mul_mem hjL hbL) ((modO2Image H (l1 T L V)).inv_mem hjL))
          ((modO2Image H (l1 T L V)).inv_mem hbL)
      · rw [map_mul, map_mul, map_mul, map_inv, map_inv, hΘj,
          (Commute.neg_one_left (Θ b)).eq]
        group
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hc
    exact hc
  have hxV : ∃ y ∈ K, b * y * b⁻¹ * y⁻¹ ∉ centerOf K := by
    by_contra h
    push Not at h
    exact hΘb ((hΘ1 b).mpr h)
  have hx : b ∈ Subgroup.centralizer ({j} : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hjb.symm
  have h3 := A1c.two_lt_pRank_of_inverting_element (p := 3) (by norm_num) hK ht hx hbo hxV
  have h2 := pRank_star_le S
  omega

theorem inv_of_isElemAbelianOfRank (S : Setting147 G T L V H) (h76 : Lemma14_7_6)
    (hs : Group.IsSolvable (↥H ⧸ CFSG.pCore 2 ↥H))
    {X : Subgroup ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))}
    (hXf : ∀ α : MulAut ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)), (orderOf α).Coprime 3 →
      (∀ x ∈ X, x⁻¹ * α x ∈ frattiniIn X) → α = 1)
    (hX : IsElemAbelianOfRank 3 2 ↥X)
    (hKn : (X.map (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).subtype).Normal)
    {j : ↥H ⧸ CFSG.pCore 2 ↥H} (hjL : j ∈ modO2Image H (l1 T L V)) (hj2 : orderOf j = 2) :
    ∀ k ∈ X.map (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).subtype, j * k * j⁻¹ = k⁻¹ := by
  have : (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).Normal := CFSG.pCore_normal
  set K := X.map (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).subtype with hKdef
  have := hKn
  obtain ⟨eX⟩ := hX
  let e : ↥K ≃* Multiplicative (Fin 2 → ZMod 3) :=
    (X.equivMapOfInjective _ (Subgroup.subtype_injective _)).symm.trans eX
  let Θ : (↥H ⧸ CFSG.pCore 2 ↥H) →* GL (Fin 2) (ZMod 3) :=
    (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp MulAut.conjNormal
  have hΘ : ∀ g, Θ g = 1 → ∀ x ∈ X, x⁻¹ * MulAut.conjNormal g x ∈ frattiniIn X := by
    intro g hg x hx
    have h1 : (MulAut.conjNormal g : MulAut ↥K) = 1 :=
      (MulEquiv.map_eq_one_iff (CFSG.SectionRank.Ccomm.elemAutEquivGL e)).mp hg
    have h2 : g * (x : ↥H ⧸ CFSG.pCore 2 ↥H) * g⁻¹ = x := by
      have := congrArg (fun φ : MulAut ↥K => ((φ ⟨x, x, hx, rfl⟩ : ↥K) :
        ↥H ⧸ CFSG.pCore 2 ↥H)) h1
      simpa [MulAut.conjNormal_apply] using this
    have h3 : MulAut.conjNormal g x = x := Subtype.ext (by rw [MulAut.conjNormal_apply]; exact h2)
    rw [h3, inv_mul_cancel]
    exact Subgroup.one_mem _
  have hΘj := theta_eq_neg_one S h76 hs hXf Θ hΘ hjL hj2
  have hinv := (CFSG.SectionRank.Ccomm.elemAutEquivGL_eq_neg_one_iff e _).mp hΘj
  intro k hk
  have := congrArg Subtype.val (hinv ⟨k, hk⟩)
  simpa [MulAut.conjNormal_apply] using this

theorem eq_one_of_comm_of_sq (S : Setting147 G T L V H) (h76 : Lemma14_7_6)
    (hs : Group.IsSolvable (↥H ⧸ CFSG.pCore 2 ↥H))
    {X : Subgroup ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))}
    (hXf : ∀ α : MulAut ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)), (orderOf α).Coprime 3 →
      (∀ x ∈ X, x⁻¹ * α x ∈ frattiniIn X) → α = 1)
    {g : ↥H ⧸ CFSG.pCore 2 ↥H} (hg2 : g ^ 2 = 1)
    (hgK : ∀ k ∈ X.map (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).subtype, g * k = k * g) :
    g = 1 := by
  have : (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).Normal := CFSG.pCore_normal
  by_contra hg1
  obtain ⟨x, hx, hxF⟩ := not_fix_frattini S h76 hs hXf (k := 1) (by rw [pow_one]; exact hg2) hg1
  apply hxF
  have h1 : MulAut.conjNormal g x = x := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply, hgK (x : ↥H ⧸ CFSG.pCore 2 ↥H) ⟨x, hx, rfl⟩,
      mul_inv_cancel_right]
  rw [h1, inv_mul_cancel]
  exact Subgroup.one_mem _

theorem exists_move (S : Setting147 G T L V H) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h76 : Lemma14_7_6)
    (hs : Group.IsSolvable (↥H ⧸ CFSG.pCore 2 ↥H))
    {X : Subgroup ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))} (hXs : IsSupercritical 3 X)
    (hXf : ∀ α : MulAut ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)), (orderOf α).Coprime 3 →
      (∀ x ∈ X, x⁻¹ * α x ∈ frattiniIn X) → α = 1)
    (hX : IsElemAbelianOfRank 3 2 ↥X)
    (hKn : (X.map (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).subtype).Normal)
    (hL3 : ¬ IsPGroup 3 ↥(modO2Image H (l1 T L V))) {k : ↥H ⧸ CFSG.pCore 2 ↥H}
    (hk : k ∈ X.map (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).subtype) (hk1 : k ≠ 1) :
    ∃ b ∈ modO2Image H (l1 T L V), b ^ 3 = 1 ∧ b * k * b⁻¹ ∉ Subgroup.zpowers k := by
  have hl1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  obtain ⟨j, hjL, hj2⟩ := exists_involution_l1_star S h1222 h1332 h1334 hL3
  have hinv := inv_of_isElemAbelianOfRank S h76 hs hXf hX hKn hjL hj2 k hk
  have hk3 : k ^ 3 = 1 := by
    obtain ⟨x, hx, rfl⟩ := hk
    simpa using congrArg Subtype.val (hXs.pow_eq_one x hx)
  have hkinv := E9.ne_inv_of_three hk3 hk1
  by_contra h
  push Not at h
  have hle : modO2Image H (l1 T L V) ≤
      Subgroup.centralizer ({k} : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    refine l1_star_le_of_odd hl1H fun y hy hodd => ?_
    have hy3 := pow_three_of_odd S h1222 h1332 h1334 hy hodd
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases E9.conj_eq_or_inv hk3 hk1 (h y hy hy3) with e | e
    · exact mul_inv_eq_iff_eq_mul.mp e
    · exfalso
      apply hkinv
      calc k = y ^ 3 * k * (y ^ 3)⁻¹ := by rw [hy3]; group
        _ = y * (y * (y * k * y⁻¹) * y⁻¹) * y⁻¹ := by rw [pow_three']; group
        _ = y * (y * k⁻¹ * y⁻¹) * y⁻¹ := by rw [e]
        _ = y * (y * k * y⁻¹)⁻¹ * y⁻¹ := by group
        _ = k⁻¹ := by rw [e, inv_inv, e]
  have hjk : j * k = k * j := (Subgroup.mem_centralizer_singleton_iff).mp (hle hjL)
  apply hkinv
  calc k = j * k * j⁻¹ := by rw [hjk]; group
    _ = k⁻¹ := hinv

end CFSG.Quasithin.H13.L32A.R727
