module

public import CFSG.Quasithin.H13.L32AC50i
public import CFSG.Quasithin.H13.L32AC50h

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem false_of_four (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h29 : Thm14_7_29) (S : Setting147 G T L V H) {π : ↥H →* Equiv.Perm (Fin 7)}
    (hker : π.ker = CFSG.Open.pCore 2 ↥H) (hrange : π.range = alternatingGroup (Fin 7))
    (hPT : (T.subgroupOf H).map π = Alt7.taSub) {I : Subgroup G}
    (hIn : H ≤ Subgroup.normalizer (I : Set G)) {Δ : Finset (Fin 7)} (hΔ : Δ.card = 3)
    (hst : ∀ h : ↥H, (h : G) ∈ Subgroup.normalizer ((V ⊔ I : Subgroup G) : Set G) ↔
      ∀ i ∈ Δ, π h i ∈ Δ) : False := by
  have h13322 := stmt13_3_2_two_of h1332
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨_, -, hLTV, hV1c, hcomm, -⟩ := hMod G T L V S.hyp.hyp S.hyp.fsu
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 S.hyp h13322 hMod h1222
  have S' := Hyp147.set14 S.hyp h1222 h1332 h1334 hV2
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hL1H : L32A.l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hHG1 : H ≤ A6.g1 T V := S.hz.2.1
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hLTV
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_sup_left.trans hLTV
  have hNV : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L : Set G) := by
    have := lemma1433Five_of_inputs h1332 h1334 G T L V S.hyp.hyp S.hyp.fsu
    rw [this]
    exact inf_le_left
  have hTN : ∀ t ∈ T, t ∈ Subgroup.normalizer ((V ⊔ I : Subgroup G) : Set G) := fun t ht =>
    mem_normalizer_sup'' (hTV ht) (hIn (hTH ht))
  have hΔd : Δ = Alt7.d3 := Alt7.d3_unique Δ hΔ fun t ht i hi => by
    obtain ⟨t', ht', hπt⟩ : t ∈ (T.subgroupOf H).map π := by rw [hPT]; exact ht
    have := (hst t').mp (hTN _ ht')
    rw [hπt] at this
    exact this i hi
  subst hΔd
  set R := preim π Alt7.stabSub with hRdef
  have hmemR : ∀ h : ↥H, (h : G) ∈ R ↔
      (h : G) ∈ Subgroup.normalizer ((V ⊔ I : Subgroup G) : Set G) := by
    intro h
    rw [hst h, mem_preim]
    constructor
    · rintro ⟨hh, hs⟩
      exact hs.2
    · intro hs
      refine ⟨h.2, ?_, hs⟩
      have : π h ∈ π.range := ⟨h, rfl⟩
      rw [hrange] at this
      exact mem_alternatingGroup.mp this
  have hL1R : L32A.l1 T L V ⊔ T ≤ R := by
    refine sup_le (fun x hx => ?_) (fun t ht => ?_)
    · have hxL : x ∈ L := (oTwoUpper_le _).trans inf_le_left hx
      exact (hmemR ⟨x, hL1H hx⟩).mpr (mem_normalizer_sup'' (hLV hxL) (hIn (hL1H hx)))
    · exact (hmemR ⟨t, hTH ht⟩).mpr (hTN t ht)
  have hRH : R ≤ H := preim_le π _
  have hRM : R ≤ Subgroup.normalizer (L : Set G) := h29 G T L V S.hyp R hL1R
    (hRH.trans hHG1) (isSolvable_preim_stab hker hrange)
  have hRV : R ≤ Subgroup.normalizer (V : Set G) := by
    have h6 := lemma1433Six_of_inputs h1332 h1334 h1222 G T L V S.hyp.hyp S.hyp.fsu
      (fsuV1 T V) H inf_le_left (fun h => by
        rw [h, Subgroup.card_bot] at hV1c
        omega) hHG1
    intro r hr
    have : r ∈ H ⊓ Subgroup.normalizer (L : Set G) := ⟨hRH hr, hRM hr⟩
    rw [h6] at this
    exact this.2
  have hRV1 : R ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hRH.trans hHG1
  have hRL1 : R ≤ Subgroup.normalizer (L32A.l1 T L V : Set G) := by
    intro r hr
    have hr' : r ∈ Subgroup.normalizer ((L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) :
        Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨hxL, hxN⟩
        exact ⟨(Subgroup.mem_normalizer_iff.mp (hRM hr) x).mp hxL,
          Subgroup.mul_mem _ (Subgroup.mul_mem _ (hRV1 hr) hxN) (Subgroup.inv_mem _ (hRV1 hr))⟩
      · rintro ⟨hxL, hxN⟩
        refine ⟨(Subgroup.mem_normalizer_iff.mp (hRM hr) x).mpr hxL, ?_⟩
        have := Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ (hRV1 hr)) hxN)
          (hRV1 hr)
        simpa [mul_assoc] using this
    exact normalizer_le_normalizer_oTwoUpper _ hr'
  have hRO2 : ∀ (X : Subgroup G), R ≤ Subgroup.normalizer (X : Set G) →
      R ≤ Subgroup.normalizer (pCoreOf 2 X : Set G) := fun X hX r hr =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X (hX hr)
  obtain ⟨t, htT, htL, htn⟩ := exists_T_L_not_triv S' hNV
  obtain ⟨ψ, hψ⟩ := S'.exists_rep
  have hL1eq : L₁Of L (fsuV1 T V) = L32A.l1 T L V := oTwoRes_eq_oTwoUpper _
  obtain ⟨z, a, b, hz, hz1, ha, haV, hb, hbV⟩ := S'.exists_basis
  obtain ⟨x, hxL1, -, hxa, -⟩ := S'.exists_x hz hz1 ha haV hb hbV
  have hxn : x ∉ L32NSet14.trivSub V (fsuV1 T V) := fun h => by
    have h1 := h.2.2 a (S'.hV2.2.1 ha)
    rw [hxa] at h1
    apply hbV
    have h2 := Subgroup.mul_mem _ (S'.hV2.1 h1) ha
    rwa [inv_mul_cancel_right] at h2
  have hxl1 : x ∈ L32A.l1 T L V := hL1eq ▸ hxL1
  have hxX : x ∈ L32NSet14.nX T V := S'.L1_le_X hxL1
  have htX : t ∈ L32NSet14.nX T V := S'.T_le_X htT
  set ℓ := x ^ 4 with hℓ
  have hℓl1 : ℓ ∈ L32A.l1 T L V := Subgroup.pow_mem _ hxl1 _
  have hℓX : ℓ ∈ L32NSet14.nX T V := Subgroup.pow_mem _ hxX _
  have hψx3 := S'.cube_eq_one ψ hxL1
  have hψx : ψ ⟨x, hxX⟩ ≠ 1 := fun h => hxn ((hψ _).mp h)
  have hψℓ : ψ ⟨ℓ, hℓX⟩ = ψ ⟨x, hxX⟩ := by
    have e : (⟨ℓ, hℓX⟩ : ↥(L32NSet14.nX T V)) = ⟨x, hxX⟩ ^ 4 := Subtype.ext (by simp [hℓ])
    rw [e, map_pow, show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hψx3, one_mul, pow_one]
  have hψt : ψ ⟨t, htX⟩ ≠ 1 := fun h => htn ((hψ _).mp h)
  have hψt2 : ψ ⟨t, htX⟩ ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := S'.hH.sylow.1 ⟨t, htT⟩
    have hk' : ψ ⟨t, htX⟩ ^ 2 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨t, htX⟩ : ↥(L32NSet14.nX T V)) ^ 2 ^ k = 1 := Subtype.ext (by
        have := congrArg Subtype.val hk
        simpa using this)
      rw [this, map_one]
    have h6 := sl2_facts.1 (ψ ⟨t, htX⟩)
    have h1 := orderOf_dvd_of_pow_eq_one hk'
    have h2 := orderOf_dvd_of_pow_eq_one h6
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    have hj1 : j ≤ 1 := by
      by_contra hj2
      have : 2 ^ 2 ∣ 6 := (Nat.pow_dvd_pow 2 (by omega)).trans (hj ▸ h2)
      omega
    refine orderOf_dvd_iff_pow_eq_one.mp ?_
    rw [hj]
    exact Nat.pow_dvd_pow 2 hj1
  have hTl1 : T ≤ Subgroup.normalizer (L32A.l1 T L V : Set G) := T_le_normalizer_l1 h1332 S
  have hm1 : t * ℓ * t⁻¹ * ℓ ∈ L32A.l1 T L V :=
    Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hTl1 htT) ℓ).mp hℓl1) hℓl1
  have hmX : t * ℓ * t⁻¹ * ℓ ∈ L32NSet14.nX T V :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ htX hℓX)
      (Subgroup.inv_mem _ htX)) hℓX
  have hmtriv : t * ℓ * t⁻¹ * ℓ ∈ L32NSet14.trivSub V (fsuV1 T V) := by
    refine (hψ ⟨_, hmX⟩).mp ?_
    have e : (⟨t * ℓ * t⁻¹ * ℓ, hmX⟩ : ↥(L32NSet14.nX T V)) =
        ⟨t, htX⟩ * ⟨ℓ, hℓX⟩ * (⟨t, htX⟩ : ↥(L32NSet14.nX T V))⁻¹ * ⟨ℓ, hℓX⟩ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, hψℓ]
    exact sl2_facts.2 _ _ hψt2 hψx3 hψt
  have hmO2 : t * ℓ * t⁻¹ * ℓ ∈ pCoreOf 2 (L32A.l1 T L V) := by
    have h1 := S'.le_pCoreOf S'.L1_le_X (((oTwoRes_le _).trans inf_le_left).trans
      le_sup_left) (show t * ℓ * t⁻¹ * ℓ ∈ L₁Of L (fsuV1 T V) ⊓ L32NSet14.trivSub V (fsuV1 T V)
        from ⟨hL1eq ▸ hm1, hmtriv⟩)
    rwa [hL1eq] at h1
  have hO2l1R : pCoreOf 2 (L32A.l1 T L V) ≤ R := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans
    ((le_sup_left).trans hL1R)
  have hO2l1n := hRO2 _ hRL1
  have hO2l12 : IsPGroup 2 (pCoreOf 2 (L32A.l1 T L V)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hmH : t * ℓ * t⁻¹ * ℓ ∈ H := hRH (hO2l1R hmO2)
  have hm4 := map_mem_v4 hrange hO2l1R hO2l1n hO2l12 hmO2 hmH
  have htH : t ∈ H := hTH htT
  have hℓH : ℓ ∈ H := hL1H hℓl1
  have htR : t ∈ R := hL1R (Subgroup.mem_sup_right htT)
  have hℓR : ℓ ∈ R := hL1R (Subgroup.mem_sup_left hℓl1)
  set g := π ⟨t, htH⟩ with hg
  set y := π ⟨ℓ, hℓH⟩ with hy
  have hgs : g ∈ Alt7.stabList := Alt7.mem_stabList (mem_preim.mp htR).2
  have hys : y ∈ Alt7.stabList := Alt7.mem_stabList (mem_preim.mp hℓR).2
  have hπm : π ⟨t * ℓ * t⁻¹ * ℓ, hmH⟩ = g * y * g⁻¹ * y := by
    rw [hg, hy, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [hπm] at hm4
  have hy3 : y ^ 3 = 1 := by
    have e : (⟨ℓ, hℓH⟩ : ↥H) ^ 3 = ⟨x, hL1H hxl1⟩ ^ 12 := Subtype.ext (by
      simp only [Subgroup.coe_pow]
      rw [hℓ, ← pow_mul])
    rw [hy, ← map_pow, e, map_pow]
    exact Alt7.stab_exp _ (Alt7.mem_stabList (mem_preim.mp (hL1R (Subgroup.mem_sup_left
      hxl1))).2)
  have hy1 : y ≠ 1 := by
    intro h1
    obtain ⟨n, hn⟩ := two_elt_of_ker (h := ⟨ℓ, hℓH⟩) (MonoidHom.mem_ker.mpr h1) hker
    apply hψx
    rw [← hψℓ]
    have h2n : ψ ⟨ℓ, hℓX⟩ ^ 2 ^ n = 1 := by
      rw [← map_pow]
      have : (⟨ℓ, hℓX⟩ : ↥(L32NSet14.nX T V)) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn)
      rw [this, map_one]
    have h3 : ψ ⟨ℓ, hℓX⟩ ^ 3 = 1 := by rw [hψℓ]; exact hψx3
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_left n (by norm_num : Nat.Coprime 2 3)) (orderOf_dvd_of_pow_eq_one h2n)
      (orderOf_dvd_of_pow_eq_one h3))
  have hv4mul := Alt7.v4_closed.2.1
  have hv4inv := Alt7.v4_closed.2.2
  have hsq : ∀ u : Equiv.Perm (Fin 7), u ^ 3 = 1 → u ≠ 1 → u * u ∉ Alt7.v4List := by
    intro u hu3 hu1 hu
    apply hu1
    have h6 : (u * u) ^ 3 = 1 := by
      rw [← pow_two, ← pow_mul, show 2 * 3 = 3 * 2 by norm_num, pow_mul, hu3, one_pow]
    have h1 := Alt7.d3_v4 _ hu h6
    calc u = (u * u) * (u * u) * (u ^ 3)⁻¹ := by group
      _ = 1 := by rw [h1, hu3, inv_one, mul_one, mul_one]
  have hodd : ¬ Alt7.EvenOn g := by
    intro he
    have h1 := Alt7.d2a g hgs y hys hy3 he
    apply hsq y hy3 hy1
    have e : y * y = (g * y * g⁻¹ * y⁻¹)⁻¹ * (g * y * g⁻¹ * y) := by group
    rw [e]
    exact hv4mul _ (hv4inv _ h1) _ hm4
  have hAut : Nat.card (MulAut ↥V) = 168 := by
    have h1 := S'.card_autOn
    rw [autOn_eq_top_of_hyp1281One S'.h1281, Subgroup.card_top] at h1
    exact h1
  obtain ⟨c, hcH, hcR, hcC, hc3, hc1⟩ := exists_three_cent hker hrange hRV hAut
  set yc := π ⟨c, hcH⟩ with hyc
  have hcs : yc ∈ Alt7.stabList := Alt7.mem_stabList (mem_preim.mp hcR).2
  have h2b := Alt7.d2b g hgs yc hcs hc3 hodd
  have hcL : t * c * t⁻¹ * c⁻¹ ∈ L := by
    have h1 : c * t⁻¹ * c⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hRM hcR) _).mp
      (L.inv_mem htL)
    have e : t * c * t⁻¹ * c⁻¹ = t * (c * t⁻¹ * c⁻¹) := by group
    rw [e]
    exact L.mul_mem htL h1
  have hcCV : t * c * t⁻¹ * c⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
    have h1 : t * c * t⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have hv' : t⁻¹ * v * t ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hTV htT)) v).mp hv
        simpa using this
      have := Subgroup.mem_centralizer_iff.mp hcC _ hv'
      calc v * (t * c * t⁻¹) = t * ((t⁻¹ * v * t) * c) * t⁻¹ := by group
        _ = t * (c * (t⁻¹ * v * t)) * t⁻¹ := by rw [this]
        _ = t * c * t⁻¹ * v := by group
    exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hcC)
  have hcO2L : t * c * t⁻¹ * c⁻¹ ∈ pCoreOf 2 L := by
    rw [← S'.cent_eq]
    exact ⟨hcL, hcCV⟩
  have hO2LR : pCoreOf 2 L ⊓ R ≤ R := inf_le_right
  have hO2Ln : R ≤ Subgroup.normalizer ((pCoreOf 2 L ⊓ R : Subgroup G) : Set G) := by
    intro r hr
    rw [Subgroup.mem_normalizer_iff]
    intro u
    have h1 := Subgroup.mem_normalizer_iff.mp (hRO2 L hRM hr) u
    constructor
    · rintro ⟨hu1, hu2⟩
      exact ⟨h1.mp hu1, R.mul_mem (R.mul_mem hr hu2) (R.inv_mem hr)⟩
    · rintro ⟨hu1, hu2⟩
      refine ⟨h1.mpr hu1, ?_⟩
      have := R.mul_mem (R.mul_mem (R.inv_mem hr) hu2) hr
      simpa [mul_assoc] using this
  have hO2L2 : IsPGroup 2 (pCoreOf 2 L ⊓ R : Subgroup G) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_left
  have htcR : t * c * t⁻¹ * c⁻¹ ∈ R := R.mul_mem (R.mul_mem (R.mul_mem htR hcR) (R.inv_mem htR))
    (R.inv_mem hcR)
  have htcH : t * c * t⁻¹ * c⁻¹ ∈ H := hRH htcR
  have h4c := map_mem_v4 hrange hO2LR hO2Ln hO2L2 ⟨hcO2L, htcR⟩ htcH
  have hπtc : π ⟨t * c * t⁻¹ * c⁻¹, htcH⟩ = g * yc * g⁻¹ * yc⁻¹ := by
    rw [hg, hyc, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
    rfl
  rw [hπtc] at h4c
  apply hsq yc hc3 hc1
  have e : yc * yc = (g * yc * g⁻¹ * yc⁻¹)⁻¹ * (g * yc * g⁻¹ * yc) := by group
  rw [e]
  exact hv4mul _ (hv4inv _ h4c) _ h2b

end CFSG.Quasithin.H13.L32A.C
