module

public import CFSG.Quasithin.H13.L32A726S
public import CFSG.Quasithin.EmptyFaithful.SBd16Gen
public import CFSG.Quasithin.Background.C2Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_omegaOneCenter_726 {T : Subgroup G} {x : G}
    (hx : x ∈ quasithinOmegaOneCenter T) :
    x ∈ T ∧ x ∈ Subgroup.centralizer (T : Set G) ∧ x * x = 1 := by
  unfold quasithinOmegaOneCenter at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    obtain ⟨⟨hyT, hyc⟩, hy2⟩ := hy
    exact ⟨hyT, hyc, by rw [← pow_two]; exact hy2⟩
  | one => exact ⟨T.one_mem, Subgroup.one_mem _, mul_one 1⟩
  | mul a b _ _ ha hb =>
    refine ⟨T.mul_mem ha.1 hb.1, Subgroup.mul_mem _ ha.2.1 hb.2.1, ?_⟩
    have hab : a * b = b * a := (Subgroup.mem_centralizer_iff.mp ha.2.1 b hb.1).symm
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha.2.2, hb.2.2, one_mul]
  | inv a _ ha =>
    refine ⟨T.inv_mem ha.1, Subgroup.inv_mem _ ha.2.1, ?_⟩
    rw [← mul_inv_rev, ha.2.2, inv_one]

omit [Finite G] in
theorem mem_map_conj_726 {D : Subgroup G} {g y : G} :
    y ∈ D.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ D :=
  mem_conjByElt

omit [Finite G] in
theorem map_conj_eq_of_mem_normalizer_726 {D : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (D : Set G)) : D.map (MulAut.conj g).toMonoidHom = D := by
  rw [MulEquiv.toMonoidHom_eq_coe]
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hg

omit [Finite G] in
theorem exists_ne_one_of_inf_ne_bot_726 {D : Subgroup G} {g : G}
    (h : D ⊓ D.map (MulAut.conj g).toMonoidHom ≠ ⊥) :
    ∃ y ∈ D, g⁻¹ * y * g ∈ D ∧ y ≠ 1 := by
  obtain ⟨y, hy⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h
  exact ⟨y, (Subgroup.mem_inf.mp y.2).1, mem_map_conj_726.mp (Subgroup.mem_inf.mp y.2).2,
    fun h1 => hy (Subtype.ext h1)⟩

theorem not_isPGroup_of_simple_726 (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) :
    ¬ IsPGroup 2 G := by
  intro hp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Nontrivial G := by
    obtain ⟨a, b, hab⟩ := hnab
    exact nontrivial_of_ne (a * b) (b * a) hab
  have hZ : Nontrivial ↥(Subgroup.center G) := hp.center_nontrivial
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h] at hZ
    obtain ⟨a, b, hab⟩ := hZ.exists_pair_ne
    exact hab (Subtype.ext ((Subgroup.mem_bot.mp a.2).trans (Subgroup.mem_bot.mp b.2).symm))
  · obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center G := h ▸ Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

theorem normalizer_le_of_maxTwoLocal_726 {H : Subgroup G}
    (hM : CFSG.Assembly.Quasithin.quasithinIsMaxTwoLocal H) :
    Subgroup.normalizer (H : Set G) ≤ H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨P, hP1, hP2, hHP⟩, hmax⟩ := hM
  have hPO : P ≤ pCoreOf 2 H := by
    rw [hHP]
    exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hP2
  have hO1 : pCoreOf 2 H ≠ ⊥ := fun h => hP1 (le_bot_iff.mp (h ▸ hPO))
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 H : Set G)) :=
    ⟨pCoreOf 2 H, hO1, CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H, rfl⟩
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  calc Subgroup.normalizer (H : Set G) ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
        CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H
    _ = H := hmax _ hloc hHN

omit [Finite G] in
theorem eq_one_or_eq_of_mem_zpowers_726 {y h : G} (hy1 : y ≠ 1) (hy2 : y * y = 1)
    (hh : h ∈ Subgroup.zpowers y) : h = 1 ∨ h = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, rfl⟩ := hh
  have hord : orderOf y = 2 := orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  have hk : y ^ k = y ^ (k % 2) := by
    rw [← zpow_mod_orderOf y k, hord]
    rfl
  have h0 : 0 ≤ k % 2 := Int.emod_nonneg k (by norm_num)
  have h2 : k % 2 < 2 := Int.emod_lt_of_pos k (by norm_num)
  rcases (show k % 2 = 0 ∨ k % 2 = 1 by omega) with h | h
  · left
    show y ^ k = 1
    rw [hk, h, zpow_zero]
  · right
    show y ^ k = y
    rw [hk, h, zpow_one]

omit [Finite G] in
theorem isTwoLocal_centralizer_726 {y : G} (hy1 : y ≠ 1) (hy2 : y * y = 1) :
    IsTwoLocal (Subgroup.centralizer ({y} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨Subgroup.zpowers y, fun h => hy1 (Subgroup.zpowers_eq_bot.mp h), ?_, ?_⟩
  · refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (by rw [pow_two]; exact hy2) hy1
  · ext g
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro hgy x
      have hc : Commute g y := hgy
      constructor
      · intro hx
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
        refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
        rw [← hk, (hc.zpow_right k).eq, mul_inv_cancel_right]
      · intro hx
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
        refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
        have hc' : Commute g (y ^ k) := hc.zpow_right k
        calc y ^ k = g⁻¹ * (y ^ k) * g := by
              rw [mul_assoc, ← hc'.eq, ← mul_assoc, inv_mul_cancel, one_mul]
          _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [hk]
          _ = x := by group
    · intro h
      have h1 : g * y * g⁻¹ ∈ Subgroup.zpowers y := (h y).mp (Subgroup.mem_zpowers y)
      rcases eq_one_or_eq_of_mem_zpowers_726 hy1 hy2 h1 with h2 | h2
      · exfalso
        apply hy1
        calc y = g⁻¹ * (g * y * g⁻¹) * g := by group
          _ = 1 := by rw [h2]; group
      · calc g * y = g * y * g⁻¹ * g := by group
          _ = y * g := by rw [h2]

section Ctx

variable {T L V H D : Subgroup G}

theorem v1_ne_bot_726 (hc : Ctx726 G T L V H D) : fsuV1 T V ≠ ⊥ := by
  intro h
  have hH : H = ⊤ := by
    rw [hc.eq_hz, L32A.hz, h]
    ext g
    simp only [Subgroup.coe_bot, Subgroup.mem_top, iff_true]
    rw [Subgroup.mem_centralizer_iff]
    rintro x rfl
    group
  obtain ⟨P, hP1, hP2, hHP⟩ := hc.max_two_local.1
  have hsimple := hc.setting.hyp.hyp.h13.simple
  have hnab := hc.setting.hyp.hyp.h13.nonabelian
  have hPn : P.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, ← hHP, hH]
  have := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P with h1 | h1
  · exact hP1 h1
  · refine not_isPGroup_of_simple_726 hsimple hnab ?_
    rw [h1] at hP2
    exact hP2.of_equiv Subgroup.topEquiv

omit [Finite G] in
theorem mem_v1_726 {x : G} (hx : x ∈ fsuV1 T V) :
    x * x = 1 ∧ ∀ t ∈ T, t * x = x * t := by
  obtain ⟨-, hxc, hx2⟩ := mem_omegaOneCenter_726 (Subgroup.mem_inf.mp hx).2
  exact ⟨hx2, fun t ht => Subgroup.mem_centralizer_iff.mp hxc t ht⟩

theorem le_centralizer_H_726 (hc : Ctx726 G T L V H D) (hT : ∀ x ∈ D, ∀ t ∈ T, t * x = x * t) :
    H ≤ Subgroup.centralizer (D : Set G) := by
  rw [hc.eq_kt]
  refine sup_le (fun k hk => ?_) (fun t ht => ?_)
  · rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hc.d_comm x hx k hk
  · rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (hT x hx t ht).symm

theorem card_v1_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) (hdV : d ∉ fsuV1 T V) :
    Nat.card (fsuV1 T V) = 2 := by
  have hV1D := hc.v1_le_d
  have hdvd : Nat.card (fsuV1 T V) ∣ 4 := hc.card_d ▸ Subgroup.card_dvd_of_le hV1D
  have h1 : Nat.card (fsuV1 T V) ≠ 1 := fun h => v1_ne_bot_726 hc (Subgroup.card_eq_one.mp h)
  have h4 : Nat.card (fsuV1 T V) ≠ 4 := fun h =>
    hdV ((Subgroup.eq_of_le_of_card_ge hV1D (by rw [h, hc.card_d])) ▸ hdD)
  have hle : Nat.card (fsuV1 T V) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
  interval_cases h : Nat.card (fsuV1 T V) <;> simp_all

theorem inv_mul_mem_v1_726 (hc : Ctx726 G T L V H D) (hV2 : Nat.card (fsuV1 T V) = 2)
    {x y : G} (hx : x ∈ D) (hxV : x ∉ fsuV1 T V) (hy : y ∈ D) (hyV : y ∉ fsuV1 T V) :
    x⁻¹ * y ∈ fsuV1 T V := by
  have hV1D := hc.v1_le_d
  have hidx : ((fsuV1 T V).subgroupOf D).index = 2 := by
    have h := Subgroup.relIndex_mul_card (H := fsuV1 T V) (K := D)
    rw [inf_of_le_left hV1D, hV2, hc.card_d] at h
    rw [← Subgroup.relIndex]
    omega
  have key := (Subgroup.mul_mem_iff_of_index_two hidx (a := (⟨x, hx⟩ : ↥D)⁻¹) (b := ⟨y, hy⟩)).mpr
  have hxi : ((⟨x, hx⟩ : ↥D)⁻¹ ∈ (fsuV1 T V).subgroupOf D) ↔ False := by
    rw [Subgroup.inv_mem_iff, Subgroup.mem_subgroupOf]
    exact iff_false_intro hxV
  have hyi : ((⟨y, hy⟩ : ↥D) ∈ (fsuV1 T V).subgroupOf D) ↔ False := by
    rw [Subgroup.mem_subgroupOf]
    exact iff_false_intro hyV
  exact Subgroup.mem_subgroupOf.mp (key (by rw [hxi, hyi]))

end Ctx

theorem eq_sq_of_orderOf_four_726 {x v : G} (hx : orderOf x = 4) (hv : v ∈ Subgroup.zpowers x)
    (hv2 : v * v = 1) (hv1 : v ≠ 1) : v = x * x := by
  classical
  rw [mem_zpowers_iff_mem_range_orderOf, hx, Finset.mem_image] at hv
  obtain ⟨n, hn, rfl⟩ := hv
  rw [Finset.mem_range] at hn
  have hx4 : x ^ 4 = 1 := hx ▸ pow_orderOf_eq_one x
  have hx2 : x ^ 2 ≠ 1 := fun h => by
    have := orderOf_dvd_of_pow_eq_one h
    rw [hx] at this
    norm_num at this
  interval_cases n
  · exact absurd (pow_zero x) hv1
  · exfalso
    apply hx2
    rw [pow_two]
    simpa using hv2
  · rw [pow_two]
  · exfalso
    apply hx2
    calc x ^ 2 = x ^ 3 * x ^ 3 * (x ^ 4)⁻¹ := by group
      _ = 1 := by rw [hv2, hx4]; group

section Ctx

variable {T L V H D : Subgroup G}

theorem fusionIsTI_of_cyclic_726 (hc : Ctx726 G T L V H D) {x : G} (hxD : x ∈ D)
    (hx2 : x * x ≠ 1) : fusionIsTI D := by
  classical
  intro g hg
  by_contra hne
  apply hg
  apply map_conj_eq_of_mem_normalizer_726
  apply hc.d_normal
  have hx1 : x ≠ 1 := fun h => hx2 (by rw [h, mul_one])
  have hdvd : orderOf x ∣ 4 := hc.card_d ▸ Subgroup.orderOf_dvd_natCard D hxD
  have hord : orderOf x = 4 := by
    have h1 : orderOf x ≠ 1 := fun h => hx1 (orderOf_eq_one_iff.mp h)
    have h2 : orderOf x ≠ 2 := fun h => hx2 (by rw [← pow_two, ← h, pow_orderOf_eq_one])
    have h4 : orderOf x ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : orderOf x <;> simp_all
  have hDx : D = Subgroup.zpowers x :=
    (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hxD)
      (by rw [Nat.card_zpowers, hord, hc.card_d])).symm
  obtain ⟨y, hyD, hyDg, hy1⟩ := exists_ne_one_of_inf_ne_bot_726 hne
  have hinv : ∀ w ∈ D, w * w = 1 → w ≠ 1 → w = x * x := fun w hw hw2 hw1 =>
    eq_sq_of_orderOf_four_726 hord (hDx ▸ hw) hw2 hw1
  have hy4 : y * y * (y * y) = 1 := by
    have hyx : y ∈ Subgroup.zpowers x := hDx ▸ hyD
    have h := Subgroup.orderOf_dvd_natCard D hyD
    rw [hc.card_d] at h
    calc y * y * (y * y) = y ^ 4 := by rw [pow_succ, pow_succ, pow_succ, pow_one]; group
      _ = 1 := orderOf_dvd_iff_pow_eq_one.mp h
  set w := if y * y = 1 then y else y * y with hw
  have hwD : w ∈ D := by rw [hw]; split_ifs <;> [exact hyD; exact D.mul_mem hyD hyD]
  have hwDg : g⁻¹ * w * g ∈ D := by
    rw [hw]
    split_ifs
    · exact hyDg
    · have e : g⁻¹ * (y * y) * g = (g⁻¹ * y * g) * (g⁻¹ * y * g) := by group
      rw [e]
      exact D.mul_mem hyDg hyDg
  have hw2 : w * w = 1 := by rw [hw]; split_ifs with h <;> [exact h; exact hy4]
  have hw1 : w ≠ 1 := by rw [hw]; split_ifs with h <;> [exact hy1; exact h]
  have hwx := hinv w hwD hw2 hw1
  have hgwx : g⁻¹ * w * g = x * x := by
    refine hinv _ hwDg ?_ ?_
    · calc g⁻¹ * w * g * (g⁻¹ * w * g) = g⁻¹ * (w * w) * g := by group
        _ = 1 := by rw [hw2]; group
    · intro h
      apply hw1
      calc w = g * (g⁻¹ * w * g) * g⁻¹ := by group
        _ = 1 := by rw [h]; group
  rw [hc.eq_hz, L32A.hz, Subgroup.mem_centralizer_iff]
  intro v hv
  have hvD : v ∈ D := hc.v1_le_d hv
  by_cases hv1 : v = 1
  · rw [hv1]; group
  have hvx := hinv v hvD (mem_v1_726 hv).1 hv1
  rw [hvx, ← hwx]
  calc w * g = g * (g⁻¹ * w * g) := by group
    _ = g * w := by rw [hgwx, hwx]

theorem fusionIsTI_of_le_centralizer_726 (hc : Ctx726 G T L V H D) (hsq : ∀ x ∈ D, x * x = 1)
    (hT : ∀ x ∈ D, ∀ t ∈ T, t * x = x * t) : fusionIsTI D := by
  intro g hg
  by_contra hne
  apply hg
  apply map_conj_eq_of_mem_normalizer_726
  apply hc.d_normal
  obtain ⟨y, hyD, hyDg, hy1⟩ := exists_ne_one_of_inf_ne_bot_726 hne
  have hHC := le_centralizer_H_726 hc hT
  have hHy : H ≤ Subgroup.centralizer ({y} : Set G) := fun h hh => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((Subgroup.mem_centralizer_iff.mp (hHC hh)) y hyD).symm
  have hCy : Subgroup.centralizer ({y} : Set G) = H :=
    hc.max_two_local.2 _ (isTwoLocal_centralizer_726 hy1 (hsq y hyD)) hHy
  have hgH : conjByElt g H ≤ H := by
    intro u hu
    rw [mem_conjByElt] at hu
    rw [← hCy, Subgroup.mem_centralizer_singleton_iff]
    have h1 : g⁻¹ * y * g * (g⁻¹ * u * g) = g⁻¹ * u * g * (g⁻¹ * y * g) :=
      (Subgroup.mem_centralizer_iff.mp (hHC hu)) _ hyDg
    calc u * y = g * (g⁻¹ * u * g * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g * (g⁻¹ * u * g)) * g⁻¹ := by rw [h1]
      _ = y * u := by group
  have hcard : Nat.card (conjByElt g H) = Nat.card H := by
    rw [conjByElt, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have heq : conjByElt g H = H := Subgroup.eq_of_le_of_card_ge hgH (le_of_eq hcard.symm)
  apply normalizer_le_of_maxTwoLocal_726 hc.max_two_local
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe]
  exact heq

theorem fusionIsTI_of_main_726 (hc : Ctx726 G T L V H D)
    (hmain : ∀ d ∈ D, d ∉ fsuV1 T V → d * d = 1 → (∃ t ∈ T, t * d ≠ d * t) →
      Subgroup.centralizer ({d} : Set G) ≤ H ∧ ∀ g : G, ∀ v ∈ fsuV1 T V, g * v * g⁻¹ ≠ d) :
    fusionIsTI D := by
  classical
  by_cases hsq : ∀ x ∈ D, x * x = 1
  swap
  · push Not at hsq
    obtain ⟨x, hxD, hx2⟩ := hsq
    exact fusionIsTI_of_cyclic_726 hc hxD hx2
  by_cases hT : ∀ x ∈ D, ∀ t ∈ T, t * x = x * t
  · exact fusionIsTI_of_le_centralizer_726 hc hsq hT
  push Not at hT
  obtain ⟨d, hdD, t, htT, htd⟩ := hT
  have htH : t ∈ H := by rw [hc.eq_kt]; exact Subgroup.mem_sup_right htT
  have hHN : H ≤ Subgroup.normalizer (D : Set G) := hc.d_normal
  have hdV : d ∉ fsuV1 T V := fun h => htd ((mem_v1_726 h).2 t htT)
  have hV1D := hc.v1_le_d
  obtain ⟨⟨z, hzV⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (v1_ne_bot_726 hc)
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hz2 : z * z = 1 := (mem_v1_726 hzV).1
  have hztc : ∀ s ∈ T, s * z = z * s := (mem_v1_726 hzV).2
  have hcardV : Nat.card (fsuV1 T V) = 2 := by
    have hdvd : Nat.card (fsuV1 T V) ∣ 4 := hc.card_d ▸ Subgroup.card_dvd_of_le hV1D
    have h1 : Nat.card (fsuV1 T V) ≠ 1 := fun h =>
      v1_ne_bot_726 hc (Subgroup.card_eq_one.mp h)
    have h4 : Nat.card (fsuV1 T V) ≠ 4 := fun h =>
      hdV ((Subgroup.eq_of_le_of_card_ge hV1D (by rw [h, hc.card_d])) ▸ hdD)
    have hle : Nat.card (fsuV1 T V) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Nat.card (fsuV1 T V) <;> simp_all
  have hzpow : Subgroup.zpowers z = fsuV1 T V :=
    Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hzV)
      (by rw [hcardV, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact hz2) hz1'])
  have hV1 : ∀ v ∈ fsuV1 T V, v = 1 ∨ v = z := fun v hv =>
    eq_one_or_eq_of_mem_zpowers_726 hz1' hz2 (hzpow ▸ hv)
  have hd1 : d ≠ 1 := fun h => hdV (h ▸ (fsuV1 T V).one_mem)
  have hdz : d * z ∉ fsuV1 T V := fun h => hdV (by
    have := (fsuV1 T V).mul_mem h ((fsuV1 T V).inv_mem hzV)
    rwa [mul_inv_cancel_right] at this)
  have hdzD : d * z ∈ D := D.mul_mem hdD (hV1D hzV)
  have hD4 : ∀ x ∈ D, x = 1 ∨ x = z ∨ x = d ∨ x = d * z := by
    intro x hx
    by_contra hne
    push Not at hne
    obtain ⟨hx1, hxz, hxd, hxdz⟩ := hne
    have hzd : z ≠ d := fun h => hdV (h ▸ hzV)
    have hzdz : z ≠ d * z := fun h => hdz (h ▸ hzV)
    have hddz : d ≠ d * z := fun h => hz1' (by
      calc z = d⁻¹ * (d * z) := by group
        _ = 1 := by rw [← h]; group)
    have h1dz : (1 : G) ≠ d * z := fun h => hdz (h ▸ (fsuV1 T V).one_mem)
    let S : Finset G := {1, z, d, d * z, x}
    have hS : S.card = 5 := by
      simp only [S]
      rw [Finset.card_insert_of_notMem (by simp [hz1'.symm, hd1.symm, h1dz, hx1.symm]),
        Finset.card_insert_of_notMem (by simp [hzd, hzdz, hxz.symm]),
        Finset.card_insert_of_notMem (by simp [hddz, hxd.symm]),
        Finset.card_pair (Ne.symm hxdz)]
    have hsub : (S : Set G) ⊆ (D : Set G) := by
      intro w hw
      simp only [S, Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
        Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl
      · exact D.one_mem
      · exact hV1D hzV
      · exact hdD
      · exact hdzD
      · exact hx
    have hle : Nat.card (S : Set G) ≤ Nat.card (D : Set G) := Nat.card_mono (Set.toFinite _) hsub
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset, hS] at hle
    have : Nat.card (D : Set G) = 4 := hc.card_d
    omega
  have htdz : t * (d * z) ≠ d * z * t := by
    intro h
    apply htd
    have e1 : t * (d * z) = t * d * z := by group
    have e2 : d * z * t = d * t * z := by rw [mul_assoc, ← hztc t htT, ← mul_assoc]
    rw [e1, e2] at h
    exact mul_right_cancel h
  obtain ⟨hCd, hnd⟩ := hmain d hdD hdV (hsq d hdD) ⟨t, htT, htd⟩
  obtain ⟨hCdz, hndz⟩ := hmain (d * z) hdzD hdz (hsq _ hdzD) ⟨t, htT, htdz⟩
  have htdt : t⁻¹ * d * t = d * z := by
    have hmem : t⁻¹ * d * t ∈ D := by
      have := (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem htH)) d).mp hdD
      simpa using this
    rcases hD4 _ hmem with h | h | h | h
    · exfalso; apply hd1
      calc d = t * (t⁻¹ * d * t) * t⁻¹ := by group
        _ = 1 := by rw [h]; group
    · exfalso; apply hdV
      have : d = t * z * t⁻¹ := by
        calc d = t * (t⁻¹ * d * t) * t⁻¹ := by group
          _ = t * z * t⁻¹ := by rw [h]
      rw [this, hztc t htT]
      simpa using hzV
    · exfalso; apply htd
      calc t * d = t * (t⁻¹ * d * t) := by rw [h]
        _ = d * t := by group
    · exact h
  have htdzt : t⁻¹ * (d * z) * t = d := by
    have hz' : t⁻¹ * z * t = z := by
      have := hztc t htT
      calc t⁻¹ * z * t = t⁻¹ * (z * t) := by group
        _ = t⁻¹ * (t * z) := by rw [this]
        _ = z := by group
    calc t⁻¹ * (d * z) * t = (t⁻¹ * d * t) * (t⁻¹ * z * t) := by group
      _ = d * z * z := by rw [htdt, hz']
      _ = d := by rw [mul_assoc, hz2, mul_one]
  have hCz : Subgroup.centralizer ({z} : Set G) ≤ H := by
    intro g hg
    rw [hc.eq_hz, L32A.hz, Subgroup.mem_centralizer_iff]
    intro v hv
    rcases hV1 v hv with rfl | rfl
    · group
    · exact (Subgroup.mem_centralizer_singleton_iff.mp hg).symm
  have hM : ∀ x ∈ D, x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) ≤ Subgroup.normalizer (D : Set G) := by
    intro x hx hx1
    rcases hD4 x hx with rfl | rfl | rfl | rfl
    · exact absurd rfl hx1
    · exact hCz.trans hHN
    · exact hCd.trans hHN
    · exact hCdz.trans hHN
  have hz_not : ∀ g : G, g⁻¹ * z * g ≠ d ∧ g⁻¹ * z * g ≠ d * z := fun g =>
    ⟨fun h => hnd g⁻¹ z hzV (by rw [inv_inv]; exact h),
      fun h => hndz g⁻¹ z hzV (by rw [inv_inv]; exact h)⟩
  have hfus : ∀ x ∈ D, x ≠ 1 → ∀ y ∈ D, y ≠ 1 → (∃ g : G, g⁻¹ * x * g = y) →
      ∃ m ∈ Subgroup.normalizer (D : Set G), m⁻¹ * x * m = y := by
    intro x hx hx1 y hy hy1 ⟨g, hg⟩
    have hconj : ∀ a b : G, g⁻¹ * a * g = b → a = g * b * g⁻¹ := fun a b h => by
      rw [← h]; group
    rcases hD4 x hx with hx' | hx' | hx' | hx' <;> rcases hD4 y hy with hy' | hy' | hy' | hy' <;>
      rw [hx', hy'] at hg <;> rw [hx', hy'] <;> (try rw [hx'] at hx1) <;> (try rw [hy'] at hy1)
    all_goals first
      | exact absurd rfl hx1
      | exact absurd rfl hy1
      | (refine ⟨1, Subgroup.one_mem _, ?_⟩; group; done)
      | exact absurd hg (hz_not g).1
      | exact absurd hg (hz_not g).2
      | exact absurd (hconj _ _ hg).symm (hnd g z hzV)
      | exact absurd (hconj _ _ hg).symm (hndz g z hzV)
      | exact ⟨t, hHN htH, htdt⟩
      | exact ⟨t, hHN htH, htdzt⟩
  intro g hg
  by_contra hne
  apply hg
  obtain ⟨y, hyD, hyDg, hy1⟩ := exists_ne_one_of_inf_ne_bot_726 hne
  exact map_conj_eq_of_mem_normalizer_726
    (SBd16.normalizes_of_conj_mem hM hfus hyD hy1 hyDg)

end Ctx

end CFSG.Quasithin.H13.L32A
