module

public import CFSG.Quasithin.Vol2.Ch11SecB36Two
public import CFSG.Quasithin.Vol2.Ch11SecB22Two
public import CFSG.Quasithin.Vol2.Ch11SecB36Setup
public import CFSG.Quasithin.Vol2.Ch11SecBFacts36

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.Vol2.Ch11.SecA

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

theorem lt_rParam_VM (hFV : FactsVM) (h612 : ASInputs.AS_E_6_12) (h331 : Stmt3_3_1)
    (h1102 : Stmt11_0_2) (h1103 : Stmt11_0_3) (hyp : Hyp11 G T L I n) {V₁ V₂ : Subgroup G}
    (hfl : Flag36 L (fsuV T I) (VM T L I) ⊤ T V₁ V₂ n)
    (hr : ((2 * n : ℕ) : ℕ∞) ≤ E3.rParam (VM T L I))
    (hV3 : (fsuV T I ⊓ Subgroup.centralizer (L : Set G)).relIndex (fsuV T I) = 2 ^ (3 * n))
    (hCV₁ : Subgroup.centralizer (V₁ : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    ((2 * n : ℕ) : ℕ∞) < E3.rParam (VM T L I) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn := hfl.two_le
  rcases lt_or_eq_of_le hr with h | heq
  · exact h
  exfalso
  have hE61 := hypE61_VM h331 h1102 h1103 hyp
  have hMW : Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (VM T L I : Set G) :=
    (isTwoReducedIn_VM h1103 hyp).2.1
  have hcV := hfl.cV
  set M := Subgroup.normalizer (L : Set G) with hMdef
  set V := fsuV T I with hVdef
  set W := VM T L I with hWdef
  obtain ⟨U, hUW, hUC, hUm⟩ := exists_eq_rParam (heq ▸ ENat.natCast_ne_top (2 * n))
  have hUm' : E3.mQuot W U = 2 * n := by
    rw [← heq] at hUm
    exact_mod_cast hUm
  have hCM : ¬ Subgroup.centralizer (U : Set G) ≤ M := fun h => hUC (h.trans hMW)
  have hU1 : U ≠ ⊥ := by
    rintro rfl
    have h1 : Nat.card V = 2 ^ (3 * n) := by
      rw [← Subgroup.relIndex_bot_left, ← hcV, hV3]
    have h2 : Nat.card V ∣ Nat.card W := Subgroup.card_dvd_of_le hfl.le_W
    rw [h1] at h2
    have h4 : 3 * n ≤ padicValNat 2 (Nat.card W) :=
      (padicValNat_dvd_iff_le Nat.card_pos.ne').mp h2
    have h3 : E3.mQuot W ⊥ = padicValNat 2 (Nat.card W) := by
      unfold E3.mQuot
      rw [Subgroup.relIndex_bot_left]
    omega
  have hne : ¬ M ⊓ Subgroup.centralizer (U : Set G) = M ⊓ Subgroup.centralizer (W : Set G) := by
    intro heqC
    have h1 := (h612 G T M W U hE61 hU1 hUW heqC hCM).2
    rw [h1] at hr
    have : 2 * n ≤ 1 := by exact_mod_cast hr
    omega
  obtain ⟨x, ⟨hxM, hxU⟩, hxC⟩ : ∃ x ∈ M ⊓ Subgroup.centralizer (U : Set G),
      x ∉ Subgroup.centralizer (W : Set G) := by
    by_contra hall
    push Not at hall
    exact hne (le_antisymm (fun x hx => ⟨hx.1, hall x hx⟩)
      (inf_le_inf_left _ (Subgroup.centralizer_le hUW)))
  rcases exists_two_or_odd_pow (hMW hxM) hxC with ⟨k, ⟨e, he⟩, hk⟩ | ⟨k, p, hp, hp2, hkp, hk⟩
  swap
  · exact hk (hFV.oddCent G L V W ⊤ T V₁ V₂ n hfl U hUW hUm' (x ^ k)
      ⟨Subgroup.mem_top _, hMW (M.pow_mem hxM k)⟩ (Subgroup.pow_mem _ hxU k) p hp hp2 hkp)
  set y := x ^ k with hydef
  have hyN : y ∈ Subgroup.normalizer (W : Set G) := hMW (M.pow_mem hxM k)
  set φ := conjHomL W (Subgroup.normalizer (W : Set G)) le_rfl with hφdef
  have hker : ∀ z (hz : z ∈ Subgroup.normalizer (W : Set G)),
      φ ⟨z, hz⟩ = 1 ↔ z ∈ Subgroup.centralizer (W : Set G) := by
    intro z hz
    rw [← MonoidHom.mem_ker, ker_conjHomL, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨hz, h⟩⟩
  have hpow : ∀ j : ℕ, φ ⟨y ^ j, Subgroup.pow_mem _ hyN j⟩ = φ ⟨y, hyN⟩ ^ j := by
    intro j
    rw [← map_pow]
    rfl
  set d := orderOf (φ ⟨y, hyN⟩) with hddef
  have hd1 : d ≠ 1 := fun h => hk ((hker y hyN).mp (orderOf_eq_one_iff.mp h))
  have hdk : d ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one (by
    rw [← hpow]
    refine (hker _ _).mpr ?_
    rw [he]
    exact Subgroup.one_mem _)
  have h2d : 2 ∣ d := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdk
    rw [hj]
    rcases j with _ | j
    · exact absurd (by rw [hj, pow_zero]) hd1
    · exact dvd_pow_self 2 (Nat.succ_ne_zero j)
  set z := y ^ (d / 2) with hzdef
  have hzN : z ∈ Subgroup.normalizer (W : Set G) := Subgroup.pow_mem _ hyN _
  have hzord : orderOf (φ ⟨z, hzN⟩) = 2 := by
    rw [show φ ⟨z, hzN⟩ = φ ⟨y, hyN⟩ ^ (d / 2) from hpow (d / 2)]
    exact orderOf_pow_orderOf_div (orderOf_pos _).ne' h2d
  have hz2 : z ^ 2 ∈ Subgroup.centralizer (W : Set G) := by
    refine (hker _ (Subgroup.pow_mem _ hzN 2)).mp ?_
    rw [show (⟨z ^ 2, Subgroup.pow_mem _ hzN 2⟩ : ↥(Subgroup.normalizer (W : Set G))) =
      ⟨z, hzN⟩ ^ 2 from rfl, map_pow, ← hzord, pow_orderOf_eq_one]
  have hzC : z ∉ Subgroup.centralizer (W : Set G) := by
    intro h
    rw [(hker z hzN).mpr h, orderOf_one] at hzord
    exact absurd hzord (by norm_num)
  have hzU : z ∈ Subgroup.centralizer (U : Set G) :=
    Subgroup.pow_mem _ (Subgroup.pow_mem _ hxU k) _
  have hUz : U ≤ W ⊓ Subgroup.centralizer ({z} : Set G) := by
    intro u hu
    refine ⟨hUW hu, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
    rw [Set.mem_singleton_iff.mp hw]
    exact (Subgroup.mem_centralizer_iff.mp hzU u hu).symm
  have hle1 := E3.mQuot_mono (V := W) hUz
  have hle2 : 2 * n ≤ E3.mQuot W (W ⊓ Subgroup.centralizer ({z} : Set G)) := by
    have hzN' : Subgroup.zpowers z ≤ Subgroup.normalizer (W : Set G) :=
      Subgroup.zpowers_le.mpr hzN
    have hA1 : autI hfl.elemW (Subgroup.zpowers z) ≠ ⊥ := by
      rw [Ne, autI_eq_bot_iff hfl.elemW hzN']
      exact fun h => hzC (h (Subgroup.mem_zpowers z))
    have hA2 : IsPGroup 2 ↥(Subgroup.zpowers z) := by
      have hzk : z ^ 2 ^ e = 1 := by
        rw [hzdef, ← pow_mul, mul_comm, pow_mul, he, one_pow]
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hzk)
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have := E3.mParam_le_rkIdx_fixV (autI_mono hfl.elemW (le_top : Subgroup.zpowers z ≤ ⊤))
      (B6.isPGroup_autOn hA2 W) hA1
    rwa [E3.rkIdx_fixV_autI hfl.elemW hzN', inf_centralizer_zpowers,
      hFV.param G L V W ⊤ T V₁ V₂ n hfl] at this
  have hzm : E3.mQuot W (W ⊓ Subgroup.centralizer ({z} : Set G)) = 2 * n := by omega
  have hUeq : U = W ⊓ Subgroup.centralizer ({z} : Set G) := by
    have hadd := E3.mQuot_add hUz inf_le_left
    rw [hUm', hzm] at hadd
    have h0 : E3.mQuot (W ⊓ Subgroup.centralizer ({z} : Set G)) U = 0 := by omega
    exact (E3.mQuot_eq_zero_iff
      ((B2F.isPGroup_of_isElemAbelian hfl.elemW).to_le inf_le_left) hUz).mp h0
  obtain ⟨l, hl, hlU⟩ := hFV.rootInv G L V W ⊤ T V₁ V₂ n hfl z ⟨Subgroup.mem_top _, hzN⟩
    hz2 hzC hzm
  have hlM : l ∈ M := Subgroup.le_normalizer hl
  have h1 : Subgroup.centralizer (conjSubgroup V₁ l : Set G) ≤ M := by
    rw [← E3.conjSubgroup_centralizer]
    calc conjSubgroup (Subgroup.centralizer (V₁ : Set G)) l ≤ conjSubgroup M l :=
          E3.conjSubgroup_mono_left l hCV₁
      _ = M := conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hlM)
  apply hCM
  rw [hUeq]
  exact (Subgroup.centralizer_le hlU).trans h1

end CFSG.Quasithin.Vol2.Ch11.SecB
