module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporONLocal
public import CFSG.LocalAnalysis.UniquenessCase.UCFront10SporCo3Odd
public import CFSG.Sporadic.ONOddCore.Involutions

public noncomputable section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F10.ONK

open CFSG.ONSchreier Subgroup

theorem card_le_four_of_le_centralizer
    {x : Equiv.Perm (Fin N)} (hx : x ∈ onM) {r : ℕ}
    (hr : r = 5 ∨ r = 7) (hxr : orderOf x = r) {D : Subgroup (Equiv.Perm (Fin N))}
    (hDM : D ≤ onM) (hDx : D ≤ centralizer {x}) (hD : Nat.card D ∣ 512) :
    Nat.card D ≤ 4 := by
  classical
  have hrp : r.Prime := by rcases hr with rfl | rfl <;> norm_num
  have : Fact r.Prime := ⟨hrp⟩
  set x' : onM := ⟨x, hx⟩ with hx'def
  have hx' : orderOf x' = r := by rw [hx'def, orderOf_mk, hxr]
  set σ := rhoM x' with hσ
  have hσR : σ ∈ onM120Chain.originalSubgroup := by
    rw [← rhoM_range]
    exact ⟨x', rfl⟩
  have hσo : orderOf σ = r := by
    have hdvd : orderOf σ ∣ r := by
      rw [← hx']
      exact orderOf_map_dvd rhoM x'
    rcases (Nat.dvd_prime hrp).1 hdvd with h | h
    · exfalso
      have hk : x' ∈ rhoM.ker := MonoidHom.mem_ker.2 (orderOf_eq_one_iff.1 h)
      rw [rhoM_ker] at hk
      have h4 := orderOf_dvd_natCard (⟨x', hk⟩ : onQ.subgroupOf onM)
      rw [card_onQ_subgroupOf_M, orderOf_mk, hx'] at h4
      rcases hr with rfl | rfl <;> norm_num at h4
    · exact h
  obtain ⟨y, hyR, hyo, hyc⟩ := exists_onKY hr
  have hG : ¬ r ^ 2 ∣ Nat.card onM120Chain.originalSubgroup := by
    rw [card_onM120]
    rcases hr with rfl | rfl <;> decide
  obtain ⟨g, n, hn, hgn⟩ := Co3K.exists_conj_pow hrp hG
    (x := (⟨σ, hσR⟩ : onM120Chain.originalSubgroup)) (y := ⟨y, hyR⟩)
    (by rw [orderOf_mk, hσo]) (by rw [orderOf_mk, hyo])
  have hσg : σ = (g : Equiv.Perm (Fin 120)) * y ^ n * (g : Equiv.Perm (Fin 120))⁻¹ := by
    have h := congrArg Subtype.val hgn
    simpa using h
  have hnr : 0 < n % r ∧ n % r < r :=
    ⟨Nat.pos_of_ne_zero fun h => hn (Nat.dvd_of_mod_eq_zero h), Nat.mod_lt _ hrp.pos⟩
  have hyn : y ^ n = y ^ (n % r) := by rw [← hyo, pow_mod_orderOf]
  have hC := hyc (n % r) hnr.1 hnr.2
  set D' := D.subgroupOf onM with hD'
  have hcardD : Nat.card D' = Nat.card D := by
    rw [hD', Nat.card_congr (subgroupOfEquivOfLe hDM).toEquiv]
  let ψ : D' →* Equiv.Perm (Fin 120) := rhoM.comp D'.subtype
  have hker : Nat.card ψ.ker ≤ 4 := by
    have e : ψ.ker = rhoM.ker.subgroupOf D' := by
      ext d
      rfl
    rw [e, ← card_map_of_injective (K := rhoM.ker.subgroupOf D') D'.subtype_injective,
      subgroupOf_map_subtype, rhoM_ker, ← card_onQ_subgroupOf_M]
    exact card_le_of_le inf_le_left
  have hrange : ψ.range ≤ centralizer {σ} := by
    rintro _ ⟨d, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hd : ((d : onM) : Equiv.Perm (Fin N)) * x = x * (d : onM) :=
      mem_centralizer_singleton_iff.1 (hDx (mem_subgroupOf.1 d.2))
    have hd' : (d : onM) * x' = x' * (d : onM) := Subtype.ext hd
    change rhoM (d : onM) * rhoM x' = rhoM x' * rhoM (d : onM)
    rw [← map_mul, ← map_mul, hd']
  have hrangeR : ψ.range ≤ onM120Chain.originalSubgroup := by
    rintro _ ⟨d, rfl⟩
    rw [← rhoM_range]
    exact ⟨(d : onM), rfl⟩
  have hconj : ψ.range.map (MulAut.conj (g : Equiv.Perm (Fin 120))⁻¹).toMonoidHom ≤
      centralizer {y ^ (n % r)} ⊓ onM120Chain.originalSubgroup := by
    rintro _ ⟨w, hw, rfl⟩
    have hwσ : w * σ = σ * w := mem_centralizer_singleton_iff.1 (hrange hw)
    have hwR := hrangeR hw
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_, ?_⟩
    · rw [← hyn]
      set u := y ^ n
      set k : Equiv.Perm (Fin 120) := (g : Equiv.Perm (Fin 120))
      calc k⁻¹ * w * k * u = k⁻¹ * (w * (k * u * k⁻¹)) * k := by group
        _ = k⁻¹ * (w * σ) * k := by rw [hσg]
        _ = k⁻¹ * (σ * w) * k := by rw [hwσ]
        _ = u * (k⁻¹ * w * k) := by
          rw [hσg]
          group
    · exact mul_mem (mul_mem (inv_mem g.2) hwR) g.2
  have hinj : Function.Injective (MulAut.conj (g : Equiv.Perm (Fin 120))⁻¹).toMonoidHom :=
    (MulAut.conj _).injective
  have h1 : Nat.card ψ.range ∣ 512 :=
    (Dvd.intro_left _ (card_ker_mul_card_range ψ)).trans (hcardD ▸ hD)
  have h2 : Nat.card ψ.range ∣ r := by
    have h := card_dvd_of_le hconj
    rwa [hC, card_map_of_injective hinj] at h
  have h3 : Nat.card ψ.range = 1 := by
    have h := Nat.dvd_gcd h1 h2
    have hg : Nat.gcd 512 r = 1 := by rcases hr with rfl | rfl <;> norm_num
    rw [hg] at h
    exact Nat.dvd_one.1 h
  have hmul := card_ker_mul_card_range ψ
  rw [h3, mul_one, hcardD] at hmul
  rw [← hmul]
  exact hker

theorem false_of_le_normalizer
    {Q L : Subgroup (Equiv.Perm (Fin N))} (hQM : Q ≤ onM)
    (hLM : L ≤ onM) (hQL : Q ≤ normalizer (L : Set (Equiv.Perm (Fin N)))) (hL : L ≠ ⊥)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hr3 : r ≠ 3) (hLr : ∀ x ∈ L, x ^ r = 1)
    (hQ : Nat.card Q ∣ 512) (hQ256 : 256 ≤ Nat.card Q) : False := by
  have : Fact r.Prime := ⟨hr⟩
  have hLp : IsPGroup r L := fun g => ⟨1, Subtype.ext (by simp [hLr _ g.2])⟩
  obtain ⟨k, hk⟩ := hLp.exists_card_eq
  have hLM' : r ^ k ∣ 161280 := by
    rw [← hk, ← card_onM]
    exact card_dvd_of_le hLM
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero, card_eq_one] at hk
    exact hL hk
  have hr57 : r = 5 ∨ r = 7 := by
    have hdvd : r ∣ 2 ^ 9 * 3 ^ 2 * 5 * 7 := by
      have h := (dvd_pow_self r hk0).trans hLM'
      norm_num
      exact h
    rcases (Nat.Prime.dvd_mul hr).1 hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hr).1 h with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h))
            hr2
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1
            (hr.dvd_of_dvd_pow h)) hr3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h)
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr (by norm_num)).1 h)
  have hk1 : k = 1 := by
    by_contra hk1
    have h2 : r ^ 2 ∣ 161280 := (pow_dvd_pow r (by omega)).trans hLM'
    rcases hr57 with rfl | rfl <;> norm_num at h2
  rw [hk1, pow_one] at hk
  obtain ⟨⟨x, hxL⟩, hx1⟩ := ne_bot_iff_exists_ne_one.1 hL
  have hxo : orderOf x = r :=
    orderOf_eq_prime (hLr x hxL) (fun h => hx1 (Subtype.ext h))
  have hdiv := Co3K.card_dvd_pred_mul_card_inf_centralizer (hk ▸ hr : (Nat.card L).Prime) hQL
  rw [hk] at hdiv
  have hD4 : Nat.card ↥(Q ⊓ centralizer (L : Set (Equiv.Perm (Fin N)))) ≤ 4 :=
    card_le_four_of_le_centralizer (hLM hxL) hr57 hxo (inf_le_left.trans hQM)
      (inf_le_right.trans (centralizer_le (Set.singleton_subset_iff.2 hxL)))
      ((card_dvd_of_le inf_le_left).trans hQ)
  have hpos : 0 < (r - 1) * Nat.card ↥(Q ⊓ centralizer (L : Set (Equiv.Perm (Fin N)))) :=
    Nat.mul_pos (by rcases hr57 with rfl | rfl <;> norm_num) Nat.card_pos
  have hle := Nat.le_of_dvd hpos hdiv
  rcases hr57 with rfl | rfl <;> omega

theorem onT_mul_onz
    {t : Equiv.Perm (Fin N)}
    (ht : t ∈ onT) : t * onz = onz * t := by
  have h := onT_le_onM ht
  rw [onM_eq_centralizer_z] at h
  exact mem_centralizer_singleton_iff.1 (mem_inf.1 h).2

theorem onT_central_cases
    {x : Equiv.Perm (Fin N)}
    (hx : x ∈ onT) (hc : ∀ t ∈ onT, t * x = x * t) : x = 1 ∨ x = onz := by
  have hcent : x ∈ CFSG.centerIn onT := mem_inf.2 ⟨hx, mem_centralizer_iff.2 hc⟩
  rw [onT_centerIn] at hcent
  obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hcent
  rw [← zpow_mod_orderOf, orderOf_onz] at hk
  have hk2 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases hk2 with h | h
  · rw [h, zpow_zero] at hk
    exact Or.inl hk.symm
  · rw [h, zpow_one] at hk
    exact Or.inr hk.symm

theorem exists_onKe :
    ∃ e ∈ onT, e * e = 1 ∧ e ≠ 1 ∧ e ≠ onz ∧
      ∀ t ∈ onT, t * e = e * t ∨ t * e = e * onz * t := by
  obtain ⟨e32, he32, hsq, hne1, hnez, hcase⟩ := onK_e
  rw [← rhoT_range] at he32
  obtain ⟨e, rfl⟩ := he32
  have hinj := rhoT_injective
  refine ⟨e, e.2, ?_, fun h => hne1 ?_, fun h => hnez ?_, fun t ht => ?_⟩
  · have h : rhoT (e * e) = rhoT 1 := by rw [map_mul, map_one, hsq]
    exact congrArg Subtype.val (hinj h)
  · rw [show e = 1 from Subtype.ext h, map_one]
  · rw [show e = zT from Subtype.ext h, rhoT_z]
  · have hmem : rhoT ⟨t, ht⟩ ∈ onT32Chain.originalSubgroup := by
      rw [← rhoT_range]
      exact ⟨⟨t, ht⟩, rfl⟩
    rcases hcase _ hmem with h | h
    · left
      rw [← map_mul, ← map_mul] at h
      exact congrArg Subtype.val (hinj h)
    · right
      rw [← rhoT_z, ← map_mul, ← map_mul, ← map_mul] at h
      exact congrArg Subtype.val (hinj h)

theorem card_onT_inf_centralizer
    {e : Equiv.Perm (Fin N)} (heT : e ∈ onT)
    (he : ∀ t ∈ onT, t * e = e * t ∨ t * e = e * onz * t) :
    256 ≤ Nat.card ↥(onT ⊓ centralizer {e}) := by
  classical
  set e' : onT := ⟨e, heT⟩
  set ez' : onT := ⟨e * onz, onT.mul_mem heT onz_mem_T⟩
  have hconj : conjugatesOf e' ⊆ {e', ez'} := by
    intro y hy
    obtain ⟨c, rfl⟩ := isConj_iff.1 (show IsConj e' y from hy)
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases he c c.2 with h | h
    · left
      refine Subtype.ext ?_
      change (c : Equiv.Perm (Fin N)) * e * (c : Equiv.Perm (Fin N))⁻¹ = e
      rw [h, mul_inv_cancel_right]
    · right
      refine Subtype.ext ?_
      change (c : Equiv.Perm (Fin N)) * e * (c : Equiv.Perm (Fin N))⁻¹ = e * onz
      rw [h, mul_inv_cancel_right]
  have hidx : (centralizer {e'}).index ≤ 2 := by
    rw [index_centralizer_eq_ncard]
    calc (conjugatesOf e').ncard ≤ ({e', ez'} : Set onT).ncard := Set.ncard_le_ncard hconj
      _ ≤ ({ez'} : Set onT).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  have hmul := (centralizer {e'}).card_mul_index
  rw [card_onT] at hmul
  have hle : (centralizer {e'}).map onT.subtype ≤ onT ⊓ centralizer {e} := by
    rintro _ ⟨y, hy, rfl⟩
    refine mem_inf.2 ⟨y.2, mem_centralizer_singleton_iff.2 ?_⟩
    exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 hy)
  have h1 := card_le_of_le hle
  rw [card_map_of_injective onT.subtype_injective] at h1
  have h2 : 512 ≤ Nat.card (centralizer {e'}) * 2 := hmul ▸ Nat.mul_le_mul_left _ hidx
  omega

theorem false_of_normal_odd
    {A : Subgroup (Equiv.Perm (Fin N))} (hAP : A ≤ Pv)
    (hA : A ≠ ⊥) (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hr3 : r ≠ 3) (hAr : ∀ x ∈ A, x ^ r = 1)
    (hTA : onT ≤ normalizer (A : Set (Equiv.Perm (Fin N)))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, heT, hee, he1, hez, hec⟩ := exists_onKe
  have hconj : ∀ t ∈ onT, ∀ y ∈ A, t * y * t⁻¹ ∈ A := fun t ht y hy =>
    (mem_normalizer_iff.1 (hTA ht) y).1 hy
  have hconj' : ∀ t ∈ onT, ∀ y ∈ A, t⁻¹ * y * t ∈ A := fun t ht y hy => by
    have := hconj t⁻¹ (onT.inv_mem ht) y hy
    rwa [inv_inv] at this
  have hz : A ⊓ centralizer {onz} = ⊥ := by
    by_contra hne
    refine false_of_le_normalizer (Q := onT) (L := A ⊓ centralizer {onz}) onT_le_onM ?_ ?_ hne
      hr hr2 hr3 (fun x hx => hAr x (mem_inf.1 hx).1) (dvd_of_eq card_onT)
      (by rw [card_onT]; norm_num)
    · rw [onM_eq_centralizer_z]
      exact inf_le_inf_right _ hAP
    · intro t ht
      exact Co3K.mem_normalizer_inf_centralizer (hTA ht) (onT_mul_onz ht)
  have hinv : ∀ s ∈ onT, s * s = 1 → A ⊓ centralizer {s} = ⊥ → ∀ y ∈ A, s * y * s⁻¹ = y⁻¹ := by
    intro s hs hss hAs y hy
    have hs1 : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have hsy : s * y * s⁻¹ ∈ A := hconj s hs y hy
    have hw : y * (s * y * s⁻¹) ∈ A ⊓ centralizer {s} := by
      refine mem_inf.2 ⟨A.mul_mem hy hsy, mem_centralizer_singleton_iff.2 ?_⟩
      calc y * (s * y * s⁻¹) * s = y * s * y := by group
        _ = s * (s * y * s⁻¹ * y) := by
          have e : s * (s * y * s⁻¹ * y) = s * s * y * s⁻¹ * y := by group
          rw [e, hss, one_mul, hs1]
        _ = s * (y * (s * y * s⁻¹)) := by rw [hAc _ hsy _ hy]
    rw [hAs, mem_bot] at hw
    exact eq_inv_of_mul_eq_one_right hw
  obtain ⟨t₁, ht₁, ht₁e⟩ : ∃ t₁ ∈ onT, t₁ * e = e * onz * t₁ := by
    by_contra hno
    push Not at hno
    rcases onT_central_cases heT fun t ht => (hec t ht).resolve_right (hno t ht) with h | h
    · exact he1 h
    · exact hez h
  have he : A ⊓ centralizer {e} ≠ ⊥ := by
    intro he
    obtain ⟨⟨y, hyA⟩, hy1⟩ := ne_bot_iff_exists_ne_one.1 hA
    have hy1' : y ≠ 1 := fun h => hy1 (Subtype.ext h)
    have hzinv := hinv onz onz_mem_T onz_sq hz y hyA
    have heinv := hinv e heT hee he y⁻¹ (A.inv_mem hyA)
    rw [inv_inv] at heinv
    have hezy : e * onz * y = y * (e * onz) := by
      calc e * onz * y = e * (onz * y * onz⁻¹) * onz := by group
        _ = e * y⁻¹ * onz := by rw [hzinv]
        _ = e * y⁻¹ * e⁻¹ * (e * onz) := by group
        _ = y * (e * onz) := by rw [heinv]
    have h1 : t₁ * e * t₁⁻¹ = e * onz := by
      rw [ht₁e, mul_inv_cancel_right]
    have h2 : e = t₁⁻¹ * (e * onz) * t₁ := by
      rw [← h1]
      group
    have hw : t₁⁻¹ * y * t₁ ∈ A ⊓ centralizer {e} := by
      refine mem_inf.2 ⟨hconj' _ ht₁ y hyA, mem_centralizer_singleton_iff.2 ?_⟩
      rw [h2]
      calc t₁⁻¹ * y * t₁ * (t₁⁻¹ * (e * onz) * t₁)
          = t₁⁻¹ * (y * (e * onz)) * t₁ := by group
        _ = t₁⁻¹ * (e * onz * y) * t₁ := by rw [hezy]
        _ = t₁⁻¹ * (e * onz) * t₁ * (t₁⁻¹ * y * t₁) := by group
    rw [he, mem_bot] at hw
    apply hy1'
    calc y = t₁ * (t₁⁻¹ * y * t₁) * t₁⁻¹ := by group
      _ = 1 := by rw [hw]; group
  have he2 : orderOf e = 2 := orderOf_eq_prime (by rw [sq]; exact hee) he1
  obtain ⟨g₁, hg₁P, hg₁⟩ : ∃ g₁ ∈ Pv, g₁ * e * g₁⁻¹ = onz := by
    obtain ⟨g, hgP, hge⟩ :=
      CFSG.Sporadic.ONOddCore.cti_on_all_involutions_conjugate e (onT_le heT) he2
    exact ⟨g⁻¹, Pv.inv_mem hgP, by rw [hge]; group⟩
  set c : Equiv.Perm (Fin N) ≃* Equiv.Perm (Fin N) := MulAut.conj g₁ with hc
  have hmapM : ∀ H : Subgroup (Equiv.Perm (Fin N)), H ≤ Pv → H ≤ centralizer {e} →
      H.map c.toMonoidHom ≤ onM := by
    intro H hHP hHe
    rintro _ ⟨y, hy, rfl⟩
    rw [onM_eq_centralizer_z]
    have hye : y * e = e * y := mem_centralizer_singleton_iff.1 (hHe hy)
    simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine mem_inf.2 ⟨Pv.mul_mem (Pv.mul_mem hg₁P (hHP hy)) (Pv.inv_mem hg₁P),
      mem_centralizer_singleton_iff.2 ?_⟩
    rw [← hg₁]
    calc g₁ * y * g₁⁻¹ * (g₁ * e * g₁⁻¹) = g₁ * (y * e) * g₁⁻¹ := by group
      _ = g₁ * (e * y) * g₁⁻¹ := by rw [hye]
      _ = g₁ * e * g₁⁻¹ * (g₁ * y * g₁⁻¹) := by group
  have hcinj : Function.Injective c.toMonoidHom := c.injective
  set L₁ := A ⊓ centralizer {e}
  set Q₁ := onT ⊓ centralizer {e}
  have hQL : Q₁ ≤ normalizer (L₁ : Set (Equiv.Perm (Fin N))) := fun t ht =>
    Co3K.mem_normalizer_inf_centralizer (hTA (mem_inf.1 ht).1)
      (mem_centralizer_singleton_iff.1 (mem_inf.1 ht).2)
  refine false_of_le_normalizer (Q := Q₁.map c.toMonoidHom) (L := L₁.map c.toMonoidHom)
    (hmapM Q₁ (inf_le_left.trans onT_le) inf_le_right) (hmapM L₁ (inf_le_left.trans hAP)
      inf_le_right) ?_ ?_ hr hr2 hr3 ?_ ?_ ?_
  · rw [← map_equiv_normalizer_eq]
    exact Subgroup.map_mono hQL
  · rwa [Ne, map_eq_bot_iff_of_injective L₁ hcinj]
  · rintro _ ⟨y, hy, rfl⟩
    rw [← map_pow, hAr y (mem_inf.1 hy).1, map_one]
  · rw [card_map_of_injective hcinj, ← card_onT]
    exact card_dvd_of_le inf_le_left
  · rw [card_map_of_injective hcinj]
    exact card_onT_inf_centralizer heT hec

end CFSG.LocalAnalysis.UniquenessCase.UC22.F10.ONK
