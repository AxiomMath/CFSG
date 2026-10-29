module

public import CFSG.RankThree.PartTwo.Sec21.Hering2119TypeC
public import CFSG.RankThree.PartTwo.Sec21.Item2119End7Proof2126
public import CFSG.RankThree.PartTwo.Sec21.Item2119End5ProofPair
public import CFSG.RankThree.PartTwo.Sec6.Item68

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL)

namespace Hering2119

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_of_fix {L : Subgroup G} {c d e : G} {Le : Subgroup G}
    (hLe : IsLOf2125 L c d e Le) {h : G} (hh : h * e * h⁻¹ = e) :
    h ∈ Subgroup.normalizer (Le : Set G) := by
  obtain ⟨hLe1, hLe3, hLeU, -⟩ := hLe
  have h1 : Le.map (MulAut.conj h).toMonoidHom ∈ thetaComponentsAt 3 ((MulAut.conj h) e) :=
    map_mem_thetaComponentsAt (MulAut.conj h) hLe1
  rw [MulAut.conj_apply, hh] at h1
  have h2 : 3 ∣ Nat.card (Le.map (MulAut.conj h).toMonoidHom) := by
    rwa [Subgroup.card_map_of_injective (MulAut.conj h).injective]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hLeU _ h1 h2)

theorem two_pow_mul_odd_inj {a b r r' : ℕ} (hr : Odd r) (hr' : Odd r')
    (h : 2 ^ a * r = 2 ^ b * r') : a = b := by
  have key : ∀ {a b r r' : ℕ}, Odd r → 2 ^ a * r = 2 ^ b * r' → a < b → False := by
    intro a b r r' hr h hab
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hab
    have h2 : 2 ^ a * r = 2 ^ a * (2 ^ (c + 1) * r') := by rw [h]; ring
    have h3 : r = 2 ^ (c + 1) * r' := Nat.eq_of_mul_eq_mul_left (by positivity) h2
    have h4 : 2 ∣ r := by
      rw [h3]
      exact Dvd.dvd.mul_right (dvd_pow_self 2 (Nat.succ_ne_zero c)) _
    exact (Nat.not_even_iff_odd.mpr hr) (even_iff_two_dvd.mpr h4)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact key hr h hlt
  · exact key hr' h.symm hlt

theorem eq_max_of_equiv {n n' : ℕ} (hn' : 1 ≤ n')
    (e : projSL 3 (GaloisField 2 n) ≃* projSL 3 (GaloisField 2 n')) : n' = max n 1 := by
  obtain ⟨r, hr, h1⟩ := Item21LateProof.card_projSL3_eq n
  obtain ⟨r', hr', h2⟩ := Item21LateProof.card_projSL3_eq n'
  have h3 : 2 ^ (3 * max n 1) * r = 2 ^ (3 * max n' 1) * r' := by
    rw [← h1, ← h2]
    exact Nat.card_congr e.toEquiv
  have h4 := two_pow_mul_odd_inj hr hr' h3
  rw [max_eq_left hn'] at h4
  omega

section Lifting

open Item2119EndProof Item21Late2Proof Item21LateProof

theorem exists_mem_of_fix (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6) {A E U' K : Subgroup G}
    {e d : G} (hcfgK : Config2119 G A E U' e K) (hdA : d ∈ A) (hdK : d ∈ K) (hd1 : d ≠ 1)
    (hdT : Sec4.InducesTypeOn K d 1) (hed : e ∉ Subgroup.zpowers d) {u : G}
    (hu : u ∈ Subgroup.normalizer (A : Set G)) (hue : u * e * u⁻¹ = e)
    (hutriv : ∀ y ∈ A, y⁻¹ * (u * y * u⁻¹) ∈ Subgroup.zpowers d) :
    ∃ n ∈ K, n ∈ Subgroup.normalizer (A : Set G) ∧ ∀ y ∈ A, n * y * n⁻¹ = u * y * u⁻¹ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hpair := hcfgK.pair
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have h27 : Nat.card A = 27 := by rw [hcfgK.card]; norm_num
  have heA : e ∈ A := hpair.mem_E.2 hpairs.1.1
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have he3 : e ^ 3 = 1 := h3 e heA
  have he1 : e ≠ 1 := hpairs.2.1
  have hKC : K ≤ Subgroup.centralizer ({e} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt (lZeroStarAt_subset A e hpairs.2.2.1)
  have hfixe : ∀ {y : G}, y ∈ K → y * e * y⁻¹ = e := fun hy => by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hKC hy), mul_inv_cancel_right]
  obtain ⟨hcK, d₀, -, -, -, hTU, -, -, -, ⟨w, ⟨hwK, hwN⟩, hw3, hwd₀, hwA, hwmove⟩, t,
    ⟨htK, htN⟩, htd₀⟩ := frame_of h45 h66 hcfgK
  have hd₀ : d = d₀ ∨ d = d₀⁻¹ := hTU d ⟨hdA, hdK⟩ hd1 hdT
  have hZ₀ : Subgroup.zpowers d₀ = Subgroup.zpowers d := zpowers_eq_of_eq_or_eq_inv hd₀
  have hwd : w * d * w⁻¹ = d :=
    conj_eq_of_mem_zpowers hwd₀ (by rw [hZ₀]; exact Subgroup.mem_zpowers d)
  have htd : t * d * t⁻¹ = d⁻¹ := conj_eq_inv_of_eq_or_eq_inv hd₀ htd₀
  rw [hZ₀] at hwA
  obtain ⟨eS⟩ := hcfgK.star
  have hwS : A.normalizerMonoidHom ⟨w, hwN⟩ ∈ starOf A K :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hwK)
  have htS : A.normalizerMonoidHom ⟨t, htN⟩ ∈ starOf A K :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr htK)
  have hKle := le_trivOnQuot_of_perm3 hcomm h3 h27 eS heA hdA hd1 hed hwN htN hwS htS hw3
    (hfixe hwK) hwd hwA hwmove (hfixe htK) htd
  have htT : ∀ y ∈ A, y⁻¹ * (t * y * t⁻¹) ∈ Subgroup.zpowers d := fun y hy =>
    (mem_trivOnQuot_iff.mp (hKle htS)) ⟨y, hy⟩
  have hB9 := card_zpowers_sup_zpowers (hcomm d hdA e heA) hd3 he3 hd1 hed
  have hx₀ : ∃ x₀ ∈ A, x₀ ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers e := by
    by_contra h
    push Not at h
    have h10 := Subgroup.card_le_of_le (fun x hx => h x hx)
    rw [h27, hB9] at h10
    norm_num at h10
  obtain ⟨x₀, hx₀A, hx₀B⟩ := hx₀
  have hbasis : ∀ v : G, v * x₀ * v⁻¹ = x₀ → v * d * v⁻¹ = d → v * e * v⁻¹ = e →
      ∀ y ∈ A, v * y * v⁻¹ = y := fun v hv1 hv2 hv3 =>
    conj_eq_of_fix_basis hcomm h3 h27 heA hdA hx₀A hB9 hx₀B hv1 hv2 hv3
  obtain ⟨k, hk, hwx₀⟩ := exists_pow_lt_three_of_mem_zpowers hd3 (hwA x₀ hx₀A)
  have hwx₀' : w * x₀ * w⁻¹ = x₀ * d ^ k := by rw [← hwx₀]; group
  have hk0 : k ≠ 0 := by
    rintro rfl
    obtain ⟨y, hyA, hy⟩ := hwmove
    exact hy (hbasis w (by rw [hwx₀', pow_zero, mul_one]) hwd (hfixe hwK) y hyA)
  have hfix_d : ∀ v ∈ Subgroup.normalizer (A : Set G), v * e * v⁻¹ = e → v * d * v⁻¹ = d →
      (∀ y ∈ A, y⁻¹ * (v * y * v⁻¹) ∈ Subgroup.zpowers d) →
      ∃ n ∈ K, n ∈ Subgroup.normalizer (A : Set G) ∧ ∀ y ∈ A, n * y * n⁻¹ = v * y * v⁻¹ := by
    intro v hvN hve hvd hvtriv
    obtain ⟨i, hi, hvx₀⟩ := exists_pow_lt_three_of_mem_zpowers hd3 (hvtriv x₀ hx₀A)
    obtain ⟨m, hm⟩ := exists_pow_conj_eq hd3 hwd hk hk0 hwx₀' i hi
    have hwmd : ∀ z ∈ Subgroup.zpowers d, w ^ m * z * (w ^ m)⁻¹ = z := fun z hz =>
      conj_eq_of_mem_zpowers (by
        have := conj_pow_eq_of_conj_eq hwd m
        exact this) hz
    have hwme : w ^ m * e * (w ^ m)⁻¹ = e := conj_pow_eq_of_conj_eq (hfixe hwK) m
    have hwmN : w ^ m ∈ Subgroup.normalizer (A : Set G) := Subgroup.pow_mem _ hwN m
    refine ⟨w ^ m, Subgroup.pow_mem _ hwK m, hwmN, ?_⟩
    have hvx₀' : v * x₀ * v⁻¹ = x₀ * d ^ i := by rw [← hvx₀]; group
    have hzx : (w ^ m)⁻¹ * v * x₀ * ((w ^ m)⁻¹ * v)⁻¹ = x₀ := by
      calc (w ^ m)⁻¹ * v * x₀ * ((w ^ m)⁻¹ * v)⁻¹
          = (w ^ m)⁻¹ * (v * x₀ * v⁻¹) * ((w ^ m)⁻¹)⁻¹ := by group
        _ = (w ^ m)⁻¹ * (x₀ * d ^ i) * ((w ^ m)⁻¹)⁻¹ := by rw [hvx₀']
        _ = x₀ := by rw [← hm]; group
    have hzd : (w ^ m)⁻¹ * v * d * ((w ^ m)⁻¹ * v)⁻¹ = d := by
      calc (w ^ m)⁻¹ * v * d * ((w ^ m)⁻¹ * v)⁻¹
          = (w ^ m)⁻¹ * (v * d * v⁻¹) * ((w ^ m)⁻¹)⁻¹ := by group
        _ = (w ^ m)⁻¹ * (w ^ m * d * (w ^ m)⁻¹) * ((w ^ m)⁻¹)⁻¹ := by
            rw [hvd, hwmd d (Subgroup.mem_zpowers d)]
        _ = d := by group
    have hze : (w ^ m)⁻¹ * v * e * ((w ^ m)⁻¹ * v)⁻¹ = e := by
      calc (w ^ m)⁻¹ * v * e * ((w ^ m)⁻¹ * v)⁻¹
          = (w ^ m)⁻¹ * (v * e * v⁻¹) * ((w ^ m)⁻¹)⁻¹ := by group
        _ = (w ^ m)⁻¹ * (w ^ m * e * (w ^ m)⁻¹) * ((w ^ m)⁻¹)⁻¹ := by rw [hve, hwme]
        _ = e := by group
    have hz := hbasis ((w ^ m)⁻¹ * v) hzx hzd hze
    intro y hy
    have h1 := hz y hy
    calc w ^ m * y * (w ^ m)⁻¹ = w ^ m * ((w ^ m)⁻¹ * v * y * ((w ^ m)⁻¹ * v)⁻¹) * (w ^ m)⁻¹ := by
          rw [h1]
      _ = v * y * v⁻¹ := by group
  have hudA : u * d * u⁻¹ ∈ Subgroup.zpowers d := by
    have h1 := Subgroup.mul_mem _ (Subgroup.mem_zpowers d) (hutriv d hdA)
    rwa [mul_inv_cancel_left] at h1
  obtain ⟨j, hj, hjd⟩ := exists_pow_lt_three_of_mem_zpowers hd3 hudA
  have hj0 : j ≠ 0 := by
    rintro rfl
    apply hd1
    rw [pow_zero] at hjd
    calc d = u⁻¹ * (u * d * u⁻¹) * u := by group
      _ = 1 := by rw [hjd]; group
  have hj' : j = 1 ∨ j = 2 := by omega
  rcases hj' with rfl | rfl
  · exact hfix_d u hu hue (by rwa [pow_one] at hjd) hutriv
  ·
    have hud : u * d * u⁻¹ = d⁻¹ := by rw [hjd]; exact sq_eq_inv_of_pow_three hd3
    have hvd : u * t * d * (u * t)⁻¹ = d := by
      calc u * t * d * (u * t)⁻¹ = u * (t * d * t⁻¹) * u⁻¹ := by group
        _ = u * d⁻¹ * u⁻¹ := by rw [htd]
        _ = (u * d * u⁻¹)⁻¹ := by group
        _ = d := by rw [hud, inv_inv]
    have hve : u * t * e * (u * t)⁻¹ = e := by
      calc u * t * e * (u * t)⁻¹ = u * (t * e * t⁻¹) * u⁻¹ := by group
        _ = e := by rw [hfixe htK, hue]
    have hvN : u * t ∈ Subgroup.normalizer (A : Set G) := Subgroup.mul_mem _ hu htN
    have hvtriv : ∀ y ∈ A, y⁻¹ * (u * t * y * (u * t)⁻¹) ∈ Subgroup.zpowers d := by
      intro y hy
      have hty : t * y * t⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp htN y).mp hy
      have hδ := htT y hy
      have hδ' := hutriv y hy
      have hδ'' : u * (y⁻¹ * (t * y * t⁻¹)) * u⁻¹ ∈ Subgroup.zpowers d := by
        obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hδ
        rw [← hl, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hjd]
        exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers d) _) l
      have e1 : y⁻¹ * (u * t * y * (u * t)⁻¹) = (y⁻¹ * (u * y * u⁻¹)) *
          (u * (y⁻¹ * (t * y * t⁻¹)) * u⁻¹) := by group
      rw [e1]
      exact Subgroup.mul_mem _ hδ' hδ''
    obtain ⟨n', hn'K, hn'N, hn'⟩ := hfix_d (u * t) hvN hve hvd hvtriv
    refine ⟨n' * t⁻¹, Subgroup.mul_mem _ hn'K (Subgroup.inv_mem _ htK),
      Subgroup.mul_mem _ hn'N (Subgroup.inv_mem _ htN), fun y hy => ?_⟩
    have hy' : t⁻¹ * y * t ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htN) y).mp hy
      simpa using this
    have h1 := hn' _ hy'
    calc n' * t⁻¹ * y * (n' * t⁻¹)⁻¹ = n' * (t⁻¹ * y * t) * n'⁻¹ := by group
      _ = u * t * (t⁻¹ * y * t) * (u * t)⁻¹ := h1
      _ = u * y * u⁻¹ := by group

end Lifting

section Items


open Item2119End5Proof Item2119End4Proof in
theorem exists_config_Le (h211 : Item211) (h2115 : Item2115) (h2116 : Item2116) (h218 : Item218)
    (h2118 : Item2118) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h66 : Sec6.Item6_6)
    (hStar : Item2125Star) {A E U L U₀ X : Subgroup G} {c d a : G}
    (hE : Config2119End G A E U c L d U₀ a X) (h23 : Concl2123 L X c d)
    (h24 : Concl2124 A L X d) {Lf : G → Subgroup G}
    (hLf : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) {e : G} (he : e ∈ A)
    (hed : e ∉ Subgroup.zpowers d) : ∃ U' : Subgroup G, Config2119 G A E U' e (Lf e) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨U', K, hp⟩ := exists_sec21Pair h211 h2116 h45 h48 h66 hStar hE h23 h24 he hed
  have hcfg := hE.cfg
  have hpair := hcfg.pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have h27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hdA : d ∈ A := hE.mem_d.1
  have hd1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  obtain ⟨hde, hcfgK⟩ := config2119_of_pair h211 h2115 h218 h2118 h45 h66 hp h27 hdA hd1
    hE.normal_d
  obtain ⟨hdK, -⟩ := mem_and_type_of_pair h45 h66 hcfgK hdA hd1 hde hE.normal_d
  obtain ⟨-, -, hLeU, -, -, -, -⟩ := hLf e he hed
  have hK : K ∈ thetaComponentsAt 3 e := lZeroStarAt_subset A e hp.mem_pair.2.2.1
  have hK3 : 3 ∣ Nat.card K := by
    have h1 := orderOf_dvd_natCard (⟨d, hdK⟩ : K)
    rwa [Subgroup.orderOf_mk, orderOf_eq_prime hd3 hd1] at h1
  have hKe : K = Lf e := hLeU K hK hK3
  subst hKe
  exact ⟨U', hcfgK⟩

open Item2119End5Proof Item2119End4Proof in
theorem item2126LocB_of (h211 : Item211) (h2115 : Item2115) (h2116 : Item2116)
    (h218 : Item218) (h2118 : Item2118) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h66 : Sec6.Item6_6) (hStar : Item2125Star) {A E U L U₀ X : Subgroup G} {c d a : G}
    (hE : Config2119End G A E U c L d U₀ a X) (h23 : Concl2123 L X c d)
    (h24 : Concl2124 A L X d) {Lf : G → Subgroup G}
    (hLf : ∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) {n p : ℕ}
    (hLn : Nonempty (lBar L ≃* projSL 3 (GaloisField 2 n))) (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ 2 ^ n - 1) {P : Subgroup G} (hPe : IsElemAbelian p P) (hP2 : Nat.card P = p ^ 2)
    (hPC : P ≤ Subgroup.centralizer (A : Set G))
    (hPL : ∀ e ∈ A, e ∉ Subgroup.zpowers d → P ≤ Lf e)
    (hPθ : ∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ (x : G) (hx : x ∈ Lf e), x ∈ P →
      ((⟨x, hx⟩ : Lf e) : lBar (Lf e)) = 1 → x = 1) :
    ∀ e ∈ A, e ∉ Subgroup.zpowers d → ∀ g ∈ Subgroup.normalizer (A : Set G),
      g ∈ Subgroup.centralizer (P : Set G) → g * e * g⁻¹ = e → g * d * g⁻¹ = d →
      (∀ x ∈ A, x⁻¹ * (g * x * g⁻¹) ∈ Subgroup.zpowers d) →
        g ∈ Subgroup.centralizer (A : Set G) := by
  intro e he hed g hgA hgP hge hgd hgtriv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨U', hcfgK⟩ := exists_config_Le h211 h2115 h2116 h218 h2118 h45 h48 h66 hStar hE h23 h24
    hLf he hed
  have hLe := hLf e he hed
  have hpairK := hcfgK.pair
  have hAe : IsElemAbelian 3 A := hpairK.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ y ∈ A, y ^ 3 = 1 := hAe.2
  have h27 : Nat.card A = 27 := by rw [hcfgK.card]; norm_num
  have hAK : A ≤ Subgroup.normalizer (Lf e : Set G) := fun x hx =>
    mem_normalizer_of_fix hLe (by rw [hcomm x hx e he]; group)
  have hgK : g ∈ Subgroup.normalizer (Lf e : Set G) := mem_normalizer_of_fix hLe hge
  obtain ⟨n', hn'0, hn'e, ⟨eL'⟩⟩ := hE.cfg.lthree
  obtain ⟨eLn⟩ := hLn
  have hnn : n' = max n 1 := eq_max_of_equiv hn'0 (eLn.symm.trans eL')
  have hn2 : 2 ≤ n := by
    obtain ⟨k, hk⟩ := hn'e
    omega
  obtain ⟨eLe⟩ := hLe.2.2.2.1
  obtain ⟨ε, hε, hcore⟩ := exists_exp_of_centralizes hcfgK.typeC hAK hn2 (eLe.trans eLn) hp
    (by omega) hpd (hPL e he hed) hP2 (fun x hx => hPe.2 x hx)
    (fun x hx => hPθ e he hed x (hPL e he hed hx) hx)
    (fun x hx y hy => (Subgroup.mem_centralizer_iff.mp (hPC hx)) y hy) hgK hgA
    (fun x hx => ((Subgroup.mem_centralizer_iff.mp hgP) x hx).symm)
  have hpairs := mem_lThreeStarPairs_iff.mp hpairK.mem_pair
  have he1 : e ≠ 1 := hpairs.2.1
  have he3 : orderOf e = 3 := orderOf_eq_prime (h3 e he) he1
  have hKc : Lf e ∈ thetaComponentsAt 3 e := hLe.1
  have hLs : Lf e ∈ lStar A :=
    lZeroStar_subset_lStar A (lZeroStarAt_subset_lZeroStar A e hpairs.2.2.1)
  have hCA : A ⊓ Sec4.thetaQuotCentralizer (Lf e) = Subgroup.zpowers e := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr
      ⟨he, Sec6.mem_thetaQuotCentralizer_of_mem_thetaComponentsAt hKc⟩) ?_
    rw [Nat.card_zpowers, he3]
    exact Sec6.card_le_three_of_isCyclic (h66 G hpairK.standing A hpairK.mem_S (Lf e) hLs)
      fun y hy => h3 y hy.1
  have hdA : d ∈ A := hE.mem_d.1
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have hd1 : d ≠ 1 := hE.ne_one_d
  have he3' : e ^ 3 = 1 := h3 e he
  have key : ∀ x ∈ A, ∃ δ ∈ Subgroup.zpowers d, g * x * g⁻¹ = x * δ ∧
      g * x * g⁻¹ * (x ^ ε)⁻¹ ∈ Subgroup.zpowers e := by
    intro x hx
    have hgxA : g * x * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hgA x).mp hx
    have hy : g * x * g⁻¹ * (x ^ ε)⁻¹ ∈ Subgroup.zpowers e := by
      rw [← hCA]
      exact ⟨A.mul_mem hgxA (A.inv_mem (Subgroup.pow_mem _ hx ε)), hcore x hx⟩
    refine ⟨x⁻¹ * (g * x * g⁻¹), hgtriv x hx, by group, hy⟩
  rcases hε with rfl | rfl
  ·
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨δ, hδd, hgx, hy⟩ := key x hx
    have hδA : δ ∈ A := (Subgroup.zpowers_le.mpr hdA) hδd
    have hδe : δ ∈ Subgroup.zpowers e := by
      have h1 : g * x * g⁻¹ * (x ^ 1)⁻¹ = δ := by
        rw [hgx, pow_one, hcomm x hx δ hδA]
        group
      rw [← h1]
      exact hy
    have hδ1 : δ = 1 := by
      by_contra hδ1
      have he_in : e ∈ Subgroup.zpowers δ :=
        Item21Late2Proof.mem_zpowers_of_mem he3' hδe hδ1 (Subgroup.mem_zpowers e)
      exact hed ((Subgroup.zpowers_le.mpr hδd) he_in)
    rw [hδ1, mul_one] at hgx
    calc x * g = (g * x * g⁻¹) * g := by rw [hgx]
      _ = g * x := by group
  ·
    exfalso
    have hle : A ≤ Subgroup.zpowers d ⊔ Subgroup.zpowers e := by
      intro x hx
      obtain ⟨δ, hδd, hgx, hy⟩ := key x hx
      have hδA : δ ∈ A := (Subgroup.zpowers_le.mpr hdA) hδd
      have h1 : x⁻¹ = δ⁻¹ * (g * x * g⁻¹ * (x ^ 2)⁻¹) := by
        rw [hgx, hcomm x hx δ hδA]
        group
      have h2 : x⁻¹ ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers e := by
        rw [h1]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.mem_sup_left hδd))
          (Subgroup.mem_sup_right hy)
      simpa using Subgroup.inv_mem _ h2
    have h9 := Item21LateProof.card_zpowers_sup_zpowers (hcomm d hdA e he) hd3 he3' hd1 hed
    have h10 := Subgroup.card_le_of_le hle
    rw [h27, h9] at h10
    norm_num at h10

end Items

@[expose] def Item2126LocTorus : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G),
    Config2119End G A E U c L d U₀ a X → Concl2123 L X c d → Concl2124 A L X d →
      ∀ Lf : G → Subgroup G, (∀ e ∈ A, e ∉ Subgroup.zpowers d → IsLOf2125 L c d e (Lf e)) →
        ∀ n p : ℕ, Nonempty (lBar L ≃* projSL 3 (GaloisField 2 n)) → p.Prime → 3 < p →
          p ∣ 2 ^ n - 1 →
          ∃ P : Subgroup G, IsElemAbelian p P ∧ Nat.card P = p ^ 2 ∧
            P ≤ Subgroup.centralizer (A : Set G) ∧
            ∀ e ∈ A, e ∉ Subgroup.zpowers d →
              P ≤ Lf e ∧
              (∀ (x : G) (hx : x ∈ Lf e), x ∈ P →
                ((⟨x, hx⟩ : Lf e) : lBar (Lf e)) = 1 → x = 1) ∧
              ∀ P' : Subgroup G, P' ≤ Lf e → P' ≤ Subgroup.centralizer (A : Set G) →
                IsElemAbelian p P' → Nat.card P' = p ^ 2 → P' = P

section Assembly


theorem item2126Loc_of_torus (h211 : Item211) (h2115 : Item2115) (h2116 : Item2116)
    (h218 : Item218) (h2118 : Item2118) (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h66 : Sec6.Item6_6) (hStar : Item2125Star) (hT : Item2126LocTorus) : Item2126Loc := by
  intro G _ _ A E U c L d U₀ a X hE h23 h24 Lf hLf n p hLn hp hp3 hpd
  obtain ⟨P, hPe, hP2, hPC, hPK⟩ := hT G A E U c L d U₀ a X hE h23 h24 Lf hLf n p hLn hp hp3 hpd
  have hAe : IsElemAbelian 3 A := hE.cfg.pair.mem_S.1.1
  have hdA : d ∈ A := hE.mem_d.1
  have hd1 : d ≠ 1 := hE.ne_one_d
  have hB := item2126LocB_of h211 h2115 h2116 h218 h2118 h45 h48 h66 hStar hE h23 h24 hLf hLn hp
    hp3 hpd hPe hP2 hPC (fun e he hed => (hPK e he hed).1)
    (fun e he hed => (hPK e he hed).2.1)
  refine ⟨P, hPe, hP2, ?_, hB⟩
  intro e he hed τ hτ hτe
  have hτW : τ ∈ wStar A := by
    rw [← h24] at hτ
    exact sup_le (starOf_le_wStar A X) (starOf_le_wStar A L) hτ
  obtain ⟨⟨u, hu⟩, rfl⟩ := hτW
  have hutriv : ∀ y ∈ A, y⁻¹ * (u * y * u⁻¹) ∈ Subgroup.zpowers d := fun y hy =>
    (mem_trivOnQuot_iff.mp hτ) ⟨y, hy⟩
  have hue : u * e * u⁻¹ = e := congrArg Subtype.val hτe
  obtain ⟨U', hcfgK⟩ := exists_config_Le h211 h2115 h2116 h218 h2118 h45 h48 h66 hStar hE h23 h24
    hLf he hed
  have hLe := hLf e he hed
  obtain ⟨m, hmK, hmN, hm⟩ := exists_mem_of_fix h45 h66 hcfgK hdA hLe.2.2.2.2.1
    hd1 hLe.2.2.2.2.2.1 hed hu hue hutriv
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hPm : P.map (MulAut.conj m).toMonoidHom = P := by
    refine (hPK e he hed).2.2 _ ?_ ?_ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmK ((hPK e he hed).1 hx))
        (Subgroup.inv_mem _ hmK)
    · rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : m⁻¹ * y * m ∈ A := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmN) y).mp hy
        simpa using this
      have h1 : (m⁻¹ * y * m) * x = x * (m⁻¹ * y * m) :=
        (Subgroup.mem_centralizer_iff.mp (hPC hx) _ hy')
      change y * (m * x * m⁻¹) = m * x * m⁻¹ * y
      calc y * (m * x * m⁻¹) = m * ((m⁻¹ * y * m) * x) * m⁻¹ := by group
        _ = m * (x * (m⁻¹ * y * m)) * m⁻¹ := by rw [h1]
        _ = m * x * m⁻¹ * y := by group
    · exact Item2119End5Proof.isElemAbelian_map hPe _
    · rw [Subgroup.card_map_of_injective (MulAut.conj m).injective, hP2]
  have hmP : m ∈ Subgroup.normalizer (P : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hPm
  refine ⟨⟨m, hmN⟩, Subgroup.mem_subgroupOf.mpr hmP, ?_⟩
  ext y
  exact hm y y.2

end Assembly

end Hering2119

end CFSG.RankThree.PartTwo.Sec21
