module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522NeC2
public import CFSG.Quasithin.Vol2.Ch5Sec1Lem5111Rk2
public import CFSG.Quasithin.EmptyFaithful.S146zPOne
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312A
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_6A312Small
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalJ1Aut

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

@[expose] def FactL2qOddAutNormalizes : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q],
    (∃ q : ℕ, q.Prime ∧ q ^ 2 % 5 = 1 ∧ (q % 8 = 3 ∨ q % 8 = 5) ∧ IsPSL 2 q 1 Q) →
    ∀ P R : Subgroup Q, IsSylowTwoOf P ⊤ → ⁅R, R⁆ = R → R ≠ ⊥ → R ≠ ⊤ →
      P ≤ Subgroup.normalizer (R : Set Q) →
    ∀ α : MulAut Q, P.map α.toMonoidHom = P → Odd (orderOf α) → R.map α.toMonoidHom = R

section Wreath

variable {G : Type} [Group G]

theorem exists_odd_two_decomp [Finite G] (y : G) :
    ∃ r w : G, y = r * w ∧ Odd (orderOf r) ∧ (∃ e : ℕ, w ^ 2 ^ e = 1) ∧
      r ∈ Subgroup.zpowers y ∧ w ∈ Subgroup.zpowers y := by
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos y).ne'
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  have hb := Nat.gcd_eq_gcd_ab (2 ^ a) m
  rw [hcop.gcd_eq_one, Nat.cast_one] at hb
  have hy : ∀ k : ℤ, y ^ ((orderOf y : ℤ) * k) = 1 := fun k => by
    rw [zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]
  refine ⟨y ^ (((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) m), y ^ ((m : ℤ) * Nat.gcdB (2 ^ a) m),
    ?_, ?_, ⟨a, ?_⟩, Subgroup.zpow_mem_zpowers y _, Subgroup.zpow_mem_zpowers y _⟩
  · rw [← zpow_add, ← hb, zpow_one]
  · refine Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one ?_)
    rw [← zpow_natCast, ← zpow_mul]
    have e : ((2 ^ a : ℕ) : ℤ) * Nat.gcdA (2 ^ a) m * (m : ℤ) =
        (orderOf y : ℤ) * Nat.gcdA (2 ^ a) m := by
      rw [hn]
      push_cast
      ring
    rw [e, hy]
  · rw [← zpow_natCast, ← zpow_mul]
    have e : (m : ℤ) * Nat.gcdB (2 ^ a) m * ((2 ^ a : ℕ) : ℤ) =
        (orderOf y : ℤ) * Nat.gcdB (2 ^ a) m := by
      rw [hn]
      push_cast
      ring
    rw [e, hy]

theorem wreath_comm_mem {T₀ : Subgroup G} {t g : G}
    (ht : t ∈ Subgroup.normalizer (T₀ : Set G)) (ht2 : t * t ∈ T₀)
    (hg : g ∈ Subgroup.normalizer (T₀ : Set G))
    (hc : g * (t * g * t⁻¹) * g⁻¹ * (t * g * t⁻¹)⁻¹ ∈ T₀) :
    t * (g * (t * g * t⁻¹)) * t⁻¹ * (g * (t * g * t⁻¹))⁻¹ ∈ T₀ := by
  have hu : t * g * t⁻¹ ∈ Subgroup.normalizer (T₀ : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ ht hg) (Subgroup.inv_mem _ ht)
  have hm : g⁻¹ * (t * t) * g * (t * t)⁻¹ ∈ T₀ := by
    have h1 : g⁻¹ * (t * t) * g⁻¹⁻¹ ∈ T₀ :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) _).mp ht2
    rw [inv_inv] at h1
    exact T₀.mul_mem h1 (T₀.inv_mem ht2)
  have e : t * (g * (t * g * t⁻¹)) * t⁻¹ * (g * (t * g * t⁻¹))⁻¹ =
      (g * (t * g * t⁻¹) * g⁻¹ * (t * g * t⁻¹)⁻¹)⁻¹ *
        ((g * (t * g * t⁻¹)) * (g⁻¹ * (t * t) * g * (t * t)⁻¹) * (g * (t * g * t⁻¹))⁻¹) := by
    group
  rw [e]
  exact T₀.mul_mem (T₀.inv_mem hc)
    ((Subgroup.mem_normalizer_iff.mp (Subgroup.mul_mem _ hg hu) _).mp hm)

theorem mul_inv_mem_of_relIndex_two {T₀ T : Subgroup G}
    (hidx : T₀.relIndex T = 2) {x t : G} (hx : x ∈ T) (ht : t ∈ T) (hx0 : x ∉ T₀)
    (ht0 : t ∉ T₀) : x * t⁻¹ ∈ T₀ := by
  have h2 : (T₀.subgroupOf T).index = 2 := hidx
  have := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨x, hx⟩ : ↥T))
    (b := (⟨t, ht⟩ : ↥T)⁻¹)).mpr ⟨fun h' => absurd h' hx0, fun h' => absurd (by
      have h3 : ((⟨t, ht⟩ : ↥T)⁻¹ : ↥T).1 ∈ T₀ := h'
      simpa using T₀.inv_mem h3) ht0⟩
  exact this

theorem map_conj_eq_of_index_two [Finite G] {T₀ T : Subgroup G} {t d : G} (hT₀T : T₀ ≤ T)
    (hidx : T₀.relIndex T = 2) (htT : t ∈ T) (htT₀ : t ∉ T₀)
    (hd : d ∈ Subgroup.normalizer (T₀ : Set G)) (hc : t * d * t⁻¹ * d⁻¹ ∈ T₀) :
    T.map (MulAut.conj d).toMonoidHom = T := by
  have hdt : d * t * d⁻¹ ∈ T := by
    have e : d * t * d⁻¹ = (t * d * t⁻¹ * d⁻¹)⁻¹ * t := by group
    rw [e]
    exact T.mul_mem (hT₀T (T₀.inv_mem hc)) htT
  have hle : T.map (MulAut.conj d).toMonoidHom ≤ T := by
    rintro _ ⟨x, hx, rfl⟩
    show d * x * d⁻¹ ∈ T
    by_cases hx0 : x ∈ T₀
    · exact hT₀T ((Subgroup.mem_normalizer_iff.mp hd x).mp hx0)
    · have hxt := mul_inv_mem_of_relIndex_two hidx hx htT hx0 htT₀
      have e : d * x * d⁻¹ = (d * (x * t⁻¹) * d⁻¹) * (d * t * d⁻¹) := by group
      rw [e]
      exact T.mul_mem (hT₀T ((Subgroup.mem_normalizer_iff.mp hd _).mp hxt)) hdt
  exact Subgroup.eq_of_le_of_card_ge hle
    (Subgroup.card_map_of_injective (MulAut.conj d).injective).ge

theorem mem_normalizer_of_map_le_sup [Finite G] {A P : Subgroup G} (hA : ⁅A, A⁆ = A)
    (hP : IsPGroup 2 P) (hPA : P ≤ Subgroup.normalizer (A : Set G)) {a : G}
    (ha : A.map (MulAut.conj a).toMonoidHom ≤ A ⊔ P) :
    a ∈ Subgroup.normalizer (A : Set G) := by
  have hle : A.map (MulAut.conj a).toMonoidHom ≤ A :=
    le_of_perfect_of_le_sup (by rw [← Subgroup.map_commutator, hA]) ha hP hPA
  exact CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mpr
    (Subgroup.eq_of_le_of_card_ge hle (Subgroup.card_map_of_injective (MulAut.conj a).injective).ge)

theorem mem_normalizer_of_normalizer_sup_two [Finite G] {A P : Subgroup G} (hA : ⁅A, A⁆ = A)
    (hP : IsPGroup 2 P) (hPA : P ≤ Subgroup.normalizer (A : Set G)) {a : G}
    (ha : a ∈ Subgroup.normalizer ((A ⊔ P : Subgroup G) : Set G)) :
    a ∈ Subgroup.normalizer (A : Set G) := by
  refine mem_normalizer_of_map_le_sup hA hP hPA ?_
  rintro _ ⟨y, hy, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp ha y).mp (Subgroup.mem_sup_left hy)

end Wreath

theorem stmt5_2_2_ne_c2_conj_of (hL2 : FactL2qOddAutNormalizes)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (h38c : Vol2Native.A38ForSQTKCat)
    (h128 : Lemma128One) : Stmt5_2_2_ne_c2_conj := by
  intro G _ _ T M L V H B D L₂ Dp n p hyp hT₀ hL₂K hL₂C hKeq T₁ hT₁ hlt hT₁N C hOX hhat hL4 hJ
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have hloc : LocalSQTK G := (qtkeCore_of_cat h.nonabelian h.qtke).1
  set T₀ := T ⊓ Subgroup.normalizer (L₂ : Set G) with hT₀def
  set NT := Subgroup.normalizer (T₀ : Set G) with hNTdef
  set X := NT ⊔ H with hXdef
  have hHO : pCoreOf 2 H ≠ ⊥ := hyp.hStar.1.2
  have hTH : IsSylowTwoOf T H := h.isSylowTwoOf hyp.hStar.1.1
  have hTX : IsSylowTwoOf T X := h.isSylowTwoOf (hyp.hStar.1.1.trans le_sup_right)
  have hT2 : IsPGroup 2 T := h.sylow.1
  have hL₂H : L₂ ≤ H := A3.subnormal_le hL₂C.2.2.1
  have hL₂perf : ⁅L₂, L₂⁆ = L₂ := hL₂C.2.1
  have hCX : C ∈ cComp X := hhat.1
  have hCperf : ⁅C, C⁆ = C := hCX.2.1
  have hL₂Cle : L₂ ≤ C := hhat.2.1
  have hNC : ∀ g : G, g ∈ Subgroup.normalizer (C : Set G) ↔
      C.map (MulAut.conj g).toMonoidHom = C := fun g =>
    CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj
  have hNL : ∀ g : G, g ∈ Subgroup.normalizer (L₂ : Set G) ↔
      L₂.map (MulAut.conj g).toMonoidHom = L₂ := fun g =>
    CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj
  obtain ⟨K₂, tc⟩ := exists_twoComp h38c hloc hHO hTH hL₂C hKeq hL₂K
  have hTconj : ∀ s ∈ T, L₂.map (MulAut.conj s).toMonoidHom = L₂ ∨
      L₂.map (MulAut.conj s).toMonoidHom = K₂ := by
    intro s hs
    have hsH : s ∈ H := hTH.1 hs
    have h1 := map_conj_mem_cComp hL₂C hsH
    have h2 : L₂.map (MulAut.conj s).toMonoidHom ≤ oTwoUpper H := by
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper H hsH) y).mp (hL₂K.le hy)
    exact tc.cK _ (cComp_mem_of_le h1 h2 (oTwoUpper_le H))
  have hidx : T₀.relIndex T = 2 := relIndex_eq_two_of_orbit hT₀ hTconj
  obtain ⟨t, htT, htN⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L₂ : Set G) := by
    by_contra hall
    push Not at hall
    exact hT₀.ne (le_antisymm inf_le_left fun x hx => ⟨hx, hall x hx⟩)
  have htT₀ : t ∉ T₀ := fun h' => htN h'.2
  have htX : t ∈ X := hTX.1 htT
  have hT₀T : T₀ ≤ T := inf_le_left
  have hTNT : T ≤ NT := by
    have h2 : (T₀.subgroupOf T).index = 2 := hidx
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hT₀T).mp
      (Subgroup.normal_of_index_eq_two h2)
  have ht2 : t * t ∈ T₀ := by
    have h2 : (T₀.subgroupOf T).index = 2 := hidx
    exact (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨t, htT⟩ : ↥T))
      (b := (⟨t, htT⟩ : ↥T))).mpr Iff.rfl
  have hL₂loc : quasithinIsLocal T L₂ := isLocal_of_mem_cComp_of_sylow hTH hHO hL₂C
  have hne : L₂.map (MulAut.conj t).toMonoidHom ≠ L₂ := fun h' => htN ((hNL t).mpr h')
  obtain ⟨K', hK', hL₂K', hcard⟩ := P1469One.exists_cComp_two_conjugates h.qtke h.simple
    h.nonabelian h37 h38 h39 h128 hOX hTX (hL₂H.trans le_sup_right) hL₂loc htT hne
  have hK'C : K' = C := hhat.2.2 K' hK' hL₂K'
  rw [hK'C] at hcard
  have hidxC : ((Subgroup.normalizer (C : Set G)).subgroupOf X).index = 2 := by
    rw [← L3312.ncard_conjSubgroupsBy_eq_index]
    exact hcard
  have hT₀C : T₀ ≤ Subgroup.normalizer (C : Set G) := by
    intro x hx
    have h1 := map_conj_mem_cComp hCX (hTX.1 hx.1)
    have h2 : L₂ ≤ C.map (MulAut.conj x).toMonoidHom := by
      have h3 := Subgroup.map_mono (f := (MulAut.conj x).toMonoidHom) hL₂Cle
      rwa [(hNL x).mp hx.2] at h3
    exact (hNC x).mpr (hhat.2.2 _ h1 h2)
  have hnotle : ∀ S : Subgroup G, IsSylowTwoOf S X → ¬ S ≤ Subgroup.normalizer (C : Set G) := by
    intro S hS hSN
    have h1 : S.subgroupOf X ≤ (Subgroup.normalizer (C : Set G)).subgroupOf X :=
      fun x hx => hSN hx
    have h2 := Subgroup.index_dvd_of_le h1
    rw [hidxC] at h2
    exact hS.2.2 h2
  have htC : t ∉ Subgroup.normalizer (C : Set G) := by
    intro htC
    refine hnotle T hTX fun x hx => ?_
    by_cases hx0 : x ∈ T₀
    · exact hT₀C hx0
    · have hxt := mul_inv_mem_of_relIndex_two hidx hx htT hx0 htT₀
      have e : x = (x * t⁻¹) * t := by group
      rw [e]
      exact Subgroup.mul_mem _ (hT₀C hxt) htC
  have hTC : T ⊓ Subgroup.normalizer (C : Set G) = T₀ := by
    refine le_antisymm (fun x hx => ?_) (le_inf hT₀T hT₀C)
    by_contra hx0
    have hxt := mul_inv_mem_of_relIndex_two hidx hx.1 htT hx0 htT₀
    apply htC
    have e : t = (x * t⁻¹)⁻¹ * x := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (hT₀C hxt)) hx.2
  set N₀ := X ⊓ Subgroup.normalizer (C : Set G) with hN₀def
  have hN₀X : N₀ ≤ X := inf_le_left
  have hN₀eq : N₀.subgroupOf X = (Subgroup.normalizer (C : Set G)).subgroupOf X := by
    ext x
    exact ⟨fun h' => h'.2, fun h' => ⟨x.2, h'⟩⟩
  have hXN₀ : X ≤ Subgroup.normalizer (N₀ : Set G) := by
    have hn : (N₀.subgroupOf X).Normal := by
      rw [hN₀eq]
      exact Subgroup.normal_of_index_eq_two hidxC
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hN₀X).mp hn
  have hT₀syl : IsSylowTwoOf T₀ N₀ := by
    have h1 := A4.isSylowTwoOf_inf_normal hTX hN₀X hXN₀
    have h2 : T ⊓ N₀ = T₀ := by
      rw [hN₀def, ← inf_assoc, inf_eq_left.mpr hTX.1, hTC]
    rwa [h2] at h1
  have hTNTs : IsSylowTwoOf T NT := h.isSylowTwoOf hTNT
  have hT₁NTs : IsSylowTwoOf T₁ NT := isSylowTwoOf_of_quasithinIsSylowTwo hT₁ hT₁N
  obtain ⟨y, hyN, hyT⟩ := hTNTs.exists_conj hT₁NTs
  have hmapT : ∀ x ∈ T, T.map (MulAut.conj x).toMonoidHom = T := fun x hx =>
    CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj.mp (Subgroup.le_normalizer hx)
  obtain ⟨y', hy'N, hy'C, hy'T⟩ : ∃ y' ∈ NT, y' ∈ Subgroup.normalizer (C : Set G) ∧
      T₁ = T.map (MulAut.conj y').toMonoidHom := by
    by_cases hyC : y ∈ Subgroup.normalizer (C : Set G)
    · exact ⟨y, hyN, hyC, hyT⟩
    · refine ⟨y * t, Subgroup.mul_mem _ hyN (hTNT htT), ?_, ?_⟩
      · have hyX : y ∈ X := Subgroup.mem_sup_left hyN
        exact (Subgroup.mul_mem_iff_of_index_two hidxC (a := (⟨y, hyX⟩ : ↥X))
          (b := (⟨t, htX⟩ : ↥X))).mpr ⟨fun h' => absurd h' hyC, fun h' => absurd h' htC⟩
      · rw [hyT, map_mul, map_mulAut_mul, hmapT t htT]
  obtain ⟨r, w, hrw, hrodd, ⟨e, hwe⟩, hrz, hwz⟩ := exists_odd_two_decomp y'
  have hzle : Subgroup.zpowers y' ≤ NT ⊓ Subgroup.normalizer (C : Set G) :=
    Subgroup.zpowers_le.mpr ⟨hy'N, hy'C⟩
  have hrN : r ∈ NT := (hzle hrz).1
  have hrC : r ∈ Subgroup.normalizer (C : Set G) := (hzle hrz).2
  have hwN : w ∈ NT := (hzle hwz).1
  have hwC : w ∈ Subgroup.normalizer (C : Set G) := (hzle hwz).2
  have hwT₀ : w ∈ T₀ := by
    have hw2 : IsPGroup 2 (Subgroup.zpowers w) := by
      rintro ⟨g, hg⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      refine ⟨e, Subtype.ext ?_⟩
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      show (w ^ k) ^ 2 ^ e = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hwe, one_zpow]
    have hP : IsPGroup 2 ↥(Subgroup.zpowers w ⊔ T₀) :=
      IsPGroup.to_sup_of_normal_right' hw2 hT₀syl.2.1 (Subgroup.zpowers_le.mpr hwN)
    have hle : Subgroup.zpowers w ⊔ T₀ ≤ N₀ :=
      sup_le (Subgroup.zpowers_le.mpr ⟨Subgroup.mem_sup_left hwN, hwC⟩) hT₀syl.1
    have h1 := hT₀syl.eq_of_le le_sup_right hle hP
    rw [← h1]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers w)
  have hrT : T₁ = T.map (MulAut.conj r).toMonoidHom := by
    rw [hy'T, hrw, map_mul, map_mulAut_mul, hmapT w (hT₀T hwT₀)]
  have hTCsyl : IsSylowTwoOf (T ⊓ C) C :=
    A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hCX) hTX
  have hO₂TC : pCoreOf 2 C ≤ T ⊓ C := F7.isSylowTwoOf_pCoreOf_le hTCsyl
  have hTCT₀ : T ⊓ C ≤ T₀ := fun x hx => hTC ▸ ⟨hx.1, Subgroup.le_normalizer hx.2⟩
  have hO₂T₀ : pCoreOf 2 C ≤ T₀ := hO₂TC.trans hTCT₀
  have hO₂L₂ : pCoreOf 2 C ≤ Subgroup.normalizer (L₂ : Set G) := fun x hx => (hO₂T₀ hx).2
  set Pb := modO2Image C (T ⊓ C) with hPb
  set Rb := modO2Image C L₂ with hRb
  have hPbsyl : IsSylowTwoOf Pb ⊤ := Vol2.Ch11.SecS.isSylowTwoOf_modO2Image hTCsyl
  have hRbperf : ⁅Rb, Rb⁆ = Rb := Vol2.Ch11.SecS.modO2Image_perfect hL₂Cle hL₂perf
  have hRbne : Rb ≠ ⊥ := Vol2.Ch11.SecS.modO2Image_ne_bot hL₂Cle hL₂perf hL₂C.1
  have hRbtop : Rb ≠ ⊤ := by
    intro htop
    have hle := Vol2.Ch11.SecS.le_sup_of_modO2Image_eq_top hL₂Cle htop
    have hCL : C ≤ L₂ := le_of_perfect_of_le_sup hCperf hle (pCoreOf_isPGroup 2 C) hO₂L₂
    have hCeq : C = L₂ := le_antisymm hCL hL₂Cle
    rw [hCeq] at hJ
    have h60 : Nat.card (O2Q L₂) = 60 := by
      rcases hL4 with ⟨-, hc⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
      · rw [(Timmesfeld.card_statedClassicalModel_two hc).1 rfl]
        decide
      all_goals exact absurd h0 (by norm_num)
    rcases hJ with ⟨⟨e⟩⟩ | ⟨q, hq, hq5, hq8, hqL⟩
    · have h1 := Nat.card_congr e.toEquiv
      rw [h60, F134.card_carrier_J1] at h1
      norm_num at h1
    · have hq2 : q ≠ 2 := by
        rintro rfl
        norm_num at hq5
      have hdvd := Unc25G2.A312Sub.prime_dvd_card_psl_two hq hq2 hqL
      rw [h60] at hdvd
      have hq60 : q ≤ 60 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases q <;> revert hq5 hq8 hdvd <;> decide
  have hPbRb : Pb ≤ Subgroup.normalizer (Rb : Set (O2Q C)) :=
    Vol2.Ch11.SecS.modO2Image_le_normalizer fun x hx => (hTCT₀ hx).2
  have hrTC : r ∈ Subgroup.normalizer ((T ⊓ C : Subgroup G) : Set G) := by
    have e : T ⊓ C = T₀ ⊓ C :=
      le_antisymm (le_inf hTCT₀ inf_le_right) (inf_le_inf_right C hT₀T)
    rw [e]
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hrN, hrC⟩
  have hαP : Pb.map (alphaHom C ⟨r, hrC⟩).toMonoidHom = Pb :=
    map_alphaOf_modO2Image ⟨r, hrC⟩ hrTC
  have hαodd : Odd (orderOf (alphaHom C ⟨r, hrC⟩)) := by
    refine Odd.of_dvd_nat hrodd ?_
    have h1 := orderOf_map_dvd (alphaHom C) ⟨r, hrC⟩
    rwa [Subgroup.orderOf_mk] at h1
  rcases hJ with hJ1 | hL2q
  swap
  ·
    have hαR := hL2 (O2Q C) hL2q Pb Rb hPbsyl hRbperf hRbne hRbtop hPbRb
      (alphaHom C ⟨r, hrC⟩) hαP hαodd
    have hrL : r ∈ Subgroup.normalizer (L₂ : Set G) := by
      refine mem_normalizer_of_map_le_sup hL₂perf (pCoreOf_isPGroup 2 C) hO₂L₂ ?_
      rintro _ ⟨l, hl, rfl⟩
      have hrl : r * l * r⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp hrC l).mp (hL₂Cle hl)
      have h1 : (QuotientGroup.mk (⟨r * l * r⁻¹, hrl⟩ : ↥C) : O2Q C) ∈ Rb := by
        have h2 : (QuotientGroup.mk (⟨r * l * r⁻¹, hrl⟩ : ↥C) : O2Q C) =
            alphaHom C ⟨r, hrC⟩ (QuotientGroup.mk (⟨l, hL₂Cle hl⟩ : ↥C)) := by
          rw [alphaHom_mk]
        rw [h2, ← hαR]
        exact ⟨_, ⟨⟨l, hL₂Cle hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩, rfl⟩
      have h3 : ((⟨r * l * r⁻¹, hrl⟩ : ↥C) : G) ∈
          ((Rb.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥C))).map C.subtype) :=
        Subgroup.mem_map_of_mem C.subtype (show (⟨r * l * r⁻¹, hrl⟩ : ↥C) ∈
          Rb.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥C)) from h1)
      rw [hRb, Vol2.Ch11.SecS.map_comap_modO2Image hL₂Cle] at h3
      exact h3
    exact ⟨r, ⟨hrN, hrL⟩, hrT.symm⟩
  obtain ⟨gb, hgb, -⟩ := autInner_of_isSporadic_J1 hJ1 hPbsyl (alphaHom C ⟨r, hrC⟩) hαP
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gb
  have hgPb : (QuotientGroup.mk g : O2Q C) ∈ Subgroup.normalizer (Pb : Set (O2Q C)) := by
    rw [CFSG.LieType.Steinberg.mem_normalizer_iff_map_conj, ← hgb]
    exact hαP
  have hgT₀ : (g : G) ∈ NT := by
    refine mem_normalizer_of_conj_mem' fun x hx => ?_
    have hxC : x ∈ Subgroup.normalizer (C : Set G) := hT₀C hx
    have hxTC : x ∈ Subgroup.normalizer ((T ⊓ C : Subgroup G) : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer (hT₀T hx), hxC⟩
    have hβP : Pb.map (alphaHom C ⟨x, hxC⟩).toMonoidHom = Pb :=
      map_alphaOf_modO2Image ⟨x, hxC⟩ hxTC
    obtain ⟨k, hk⟩ := hT2 ⟨x, hT₀T hx⟩
    have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hβk : alphaHom C ⟨x, hxC⟩ ^ 2 ^ k = 1 := alphaHom_pow_eq_one ⟨x, hxC⟩ hxk
    obtain ⟨hb, hbβ, hbP⟩ := autInner_of_isSporadic_J1 hJ1 hPbsyl (alphaHom C ⟨x, hxC⟩) hβP
    have hbP' := hbP ⟨k, hβk⟩
    have hxg : x * (g : G)⁻¹ * x⁻¹ ∈ C :=
      (Subgroup.mem_normalizer_iff.mp hxC _).mp (C.inv_mem g.2)
    have h1 : (QuotientGroup.mk (⟨x * (g : G)⁻¹ * x⁻¹, hxg⟩ : ↥C) : O2Q C) =
        alphaHom C ⟨x, hxC⟩ (QuotientGroup.mk g⁻¹) := by
      rw [alphaHom_mk]
      rfl
    rw [hbβ, MulAut.conj_apply] at h1
    have hcP : (QuotientGroup.mk (g * ⟨x * (g : G)⁻¹ * x⁻¹, hxg⟩) : O2Q C) ∈ Pb := by
      rw [QuotientGroup.mk_mul, h1, QuotientGroup.mk_inv]
      have e : (QuotientGroup.mk g : O2Q C) * (hb * (QuotientGroup.mk g)⁻¹ * hb⁻¹) =
          ((QuotientGroup.mk g : O2Q C) * hb * (QuotientGroup.mk g)⁻¹) * hb⁻¹ := by group
      rw [e]
      exact Pb.mul_mem ((Subgroup.mem_normalizer_iff.mp hgPb hb).mp hbP') (Pb.inv_mem hbP')
    have hcT : ((g * ⟨x * (g : G)⁻¹ * x⁻¹, hxg⟩ : ↥C) : G) ∈ T ⊓ C := by
      have h2 : ((g * ⟨x * (g : G)⁻¹ * x⁻¹, hxg⟩ : ↥C) : G) ∈
          ((Pb.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥C))).map C.subtype) :=
        Subgroup.mem_map_of_mem C.subtype (show (g * ⟨x * (g : G)⁻¹ * x⁻¹, hxg⟩ : ↥C) ∈
          Pb.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥C)) from hcP)
      rw [hPb, Vol2.Ch11.SecS.map_comap_modO2Image inf_le_right, sup_eq_left.mpr hO₂TC] at h2
      exact h2
    have e : (g : G) * x * (g : G)⁻¹ = ((g * ⟨x * (g : G)⁻¹ * x⁻¹, hxg⟩ : ↥C) : G) * x := by
      simp only [Subgroup.coe_mul]
      group
    rw [e]
    exact T₀.mul_mem (hTCT₀ hcT) hx
  have hrinv : alphaHom C ⟨r⁻¹, Subgroup.inv_mem _ hrC⟩ =
      MulAut.conj (QuotientGroup.mk (g⁻¹) : O2Q C) := by
    have e : (⟨r⁻¹, Subgroup.inv_mem _ hrC⟩ : ↥(Subgroup.normalizer (C : Set G))) =
        (⟨r, hrC⟩ : ↥(Subgroup.normalizer (C : Set G)))⁻¹ := rfl
    rw [e, map_inv, hgb, ← map_inv, QuotientGroup.mk_inv]
  have htriv := forall_comm_of_alphaHom_eq_conj ⟨r⁻¹, Subgroup.inv_mem _ hrC⟩ g⁻¹ hrinv
  have hc'L : r * (g : G)⁻¹ ∈ Subgroup.normalizer (L₂ : Set G) := by
    have h1 : ((g⁻¹ : ↥C) : G)⁻¹ * r⁻¹ ∈
        Subgroup.normalizer ((L₂ ⊔ pCoreOf 2 C : Subgroup G) : Set G) :=
      mem_normalizer_of_forall_comm le_sup_right (sup_le hL₂Cle (pCoreOf_le 2 C)) htriv
    have h2 := mem_normalizer_of_normalizer_sup_two hL₂perf (pCoreOf_isPGroup 2 C) hO₂L₂ h1
    have h3 := Subgroup.inv_mem _ h2
    simpa using h3
  have hCtX : C.map (MulAut.conj t).toMonoidHom ∈ cComp X := map_conj_mem_cComp hCX htX
  have hCtne : C.map (MulAut.conj t).toMonoidHom ≠ C := fun h' => htC ((hNC t).mpr h')
  have hcomm := lemma_1_2_1_two h.qtke h.simple h.nonabelian h37 hOX hCtX hCX hCtne
  have huCt : t * (g : G) * t⁻¹ ∈ C.map (MulAut.conj t).toMonoidHom := ⟨g, g.2, rfl⟩
  have huN : t * (g : G) * t⁻¹ ∈ NT :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (hTNT htT) hgT₀) (Subgroup.inv_mem _ (hTNT htT))
  have hcommC : ∀ k ∈ C, (t * (g : G) * t⁻¹) * k * (t * (g : G) * t⁻¹)⁻¹ * k⁻¹ ∈ pCoreOf 2 C :=
    fun k hk => (hcomm.1 (Subgroup.commutator_mem_commutator huCt hk)).2
  have huL : t * (g : G) * t⁻¹ ∈ Subgroup.normalizer (L₂ : Set G) :=
    mem_normalizer_of_normalizer_sup_two hL₂perf (pCoreOf_isPGroup 2 C) hO₂L₂
      (mem_normalizer_of_forall_comm le_sup_right (sup_le hL₂Cle (pCoreOf_le 2 C)) hcommC)
  have hug : (t * (g : G) * t⁻¹) * (g : G) * (t * (g : G) * t⁻¹)⁻¹ * (g : G)⁻¹ ∈ T₀ :=
    hO₂T₀ (hcommC _ g.2)
  have hgu : (g : G) * (t * (g : G) * t⁻¹) * (g : G)⁻¹ * (t * (g : G) * t⁻¹)⁻¹ ∈ T₀ := by
    have e : (g : G) * (t * (g : G) * t⁻¹) * (g : G)⁻¹ * (t * (g : G) * t⁻¹)⁻¹ =
        ((t * (g : G) * t⁻¹) * (g : G) * (t * (g : G) * t⁻¹)⁻¹ * (g : G)⁻¹)⁻¹ := by group
    rw [e]
    exact T₀.inv_mem hug
  have hd : (g : G) * (t * (g : G) * t⁻¹) ∈ NT := Subgroup.mul_mem _ hgT₀ huN
  have hdT : T.map (MulAut.conj ((g : G) * (t * (g : G) * t⁻¹))).toMonoidHom = T :=
    map_conj_eq_of_index_two hT₀T hidx htT htT₀ hd (wreath_comm_mem (hTNT htT) ht2 hgT₀ hgu)
  have hdT' : T.map (MulAut.conj ((g : G) * (t * (g : G) * t⁻¹)))⁻¹.toMonoidHom = T := by
    conv_lhs => rw [← hdT]
    exact map_mulAut_inv_map _ _
  refine ⟨r * ((g : G) * (t * (g : G) * t⁻¹))⁻¹, ⟨Subgroup.mul_mem _ hrN (Subgroup.inv_mem _ hd),
    ?_⟩, ?_⟩
  · have e : r * ((g : G) * (t * (g : G) * t⁻¹))⁻¹ = (r * (g : G)⁻¹) * (t * (g : G) * t⁻¹)⁻¹ *
        ((t * (g : G) * t⁻¹) * (g : G) * (t * (g : G) * t⁻¹)⁻¹ * (g : G)⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc'L (Subgroup.inv_mem _ huL)) (hug.2)
  · rw [hrT, map_mul, map_inv, map_mulAut_mul, hdT']

end CFSG.Quasithin.H13
