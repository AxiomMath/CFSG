module

public import CFSG.LocalAnalysis.SteinbergSFBothTrivialHeisenberg

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace BothTrivialClosure

open Subgroup GomiFusion RootAxisTwoCore FullCenter FullCenterRadical FullCenterParabolic
  FullCenterTorus FullCenterWeyl FullCenterMutual BothTrivial BothTrivialHeisenberg
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open scoped Matrix Pointwise

section General

variable {G : Type*} [Group G]

theorem mul_self_of_elem {W : Subgroup G} (hW : IsElementaryAbelian 2 W) {w : G} (hw : w ∈ W) :
    w * w = 1 := by
  rw [← pow_two]
  exact elemPow_eq_one_of_isElementaryAbelian w hw

theorem maximal_elem_iff {E X B : Subgroup G} (hXE : X ≤ E) (hBE : B ≤ E)
    (hX : IsElementaryAbelian 2 X) (hB : IsElementaryAbelian 2 B)
    (hinv : ∀ e ∈ E, e * e = 1 → e ∈ X ∨ e ∈ B) (hXB : ¬ X ≤ B) (hBX : ¬ B ≤ X)
    (W : Subgroup G) :
    Maximal (fun W : Subgroup G => W ≤ E ∧ IsElementaryAbelian 2 W) W ↔ W = X ∨ W = B := by
  have dich : ∀ W : Subgroup G, W ≤ E → IsElementaryAbelian 2 W → W ≤ X ∨ W ≤ B :=
    fun W hWE hW => CFSG.QuasithinUnique.Setup.X7b.subgroup_le_of_subset_union fun w hw =>
      hinv w (hWE hw) (mul_self_of_elem hW hw)
  constructor
  · rintro ⟨⟨hWE, hW⟩, hmax⟩
    rcases dich W hWE hW with h1 | h1
    · exact Or.inl (le_antisymm h1 (hmax ⟨hXE, hX⟩ h1))
    · exact Or.inr (le_antisymm h1 (hmax ⟨hBE, hB⟩ h1))
  · rintro (rfl | rfl)
    · refine ⟨⟨hXE, hX⟩, fun W' hW' hle => ?_⟩
      rcases dich W' hW'.1 hW'.2 with h1 | h1
      · exact h1
      · exact absurd (hle.trans h1) hXB
    · refine ⟨⟨hBE, hB⟩, fun W' hW' hle => ?_⟩
      rcases dich W' hW'.1 hW'.2 with h1 | h1
      · exact absurd (hle.trans h1) hBX
      · exact h1

theorem card_le_two_of_dvd {V : Type*} [Group V] [Finite V] (hV : IsPGroup 2 V) {m : ℕ}
    (hm : Odd m) (hd : Nat.card V ∣ 2 * m) : Nat.card V ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := hV.exists_card_eq
  rw [ha] at hd ⊢
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.mpr hm)
  exact Nat.le_of_dvd (by norm_num) (hcop.dvd_of_dvd_mul_right hd)

theorem eq_of_card_le_two [Finite G] {H : Subgroup G} (hH : Nat.card H ≤ 2) {a b : G}
    (ha : a ∈ H) (hb : b ∈ H) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  classical
  by_contra hab
  have := Fintype.ofFinite H
  have h3 : ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset H).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair]
    · exact fun e => hab (congrArg Subtype.val e)
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun e => ha1 (congrArg Subtype.val e).symm,
        fun e => hb1 (congrArg Subtype.val e).symm⟩
  have h4 := Finset.card_le_univ ({1, ⟨a, ha⟩, ⟨b, hb⟩} : Finset H)
  rw [h3, Fintype.card_eq_nat_card] at h4
  omega

end General

section Standard

variable {M : Type*} [Group M] [Finite M] {K : Subgroup M} {τ : M}

theorem exists_sylow_le_two (hτK : τ ∈ centralizer (K : Set M)) (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1)
    (h2 : ∀ V : Subgroup M, V ≤ centralizer ({τ} : Set M) ⊓ centralizer (K : Set M) →
      IsPGroup 2 V → Nat.card V ≤ 2) :
    ∃ P : Sylow 2 ↥(centralizer (K : Set M)),
      (⟨τ, hτK⟩ : centralizer (K : Set M)) ∈ P ∧ Nat.card P ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Y := centralizer (K : Set M)
  set τ' : Y := ⟨τ, hτK⟩
  have hτ'1 : τ' ≠ 1 := fun e => hτ1 (congrArg Subtype.val e)
  have hτ'2 : IsPGroup 2 (zpowers τ') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_eq_prime (Subtype.ext (by simpa [pow_two] using hτ2)) hτ'1
  obtain ⟨P, hP⟩ := hτ'2.exists_le_sylow
  have hτP : τ' ∈ P := hP (mem_zpowers τ')
  refine ⟨P, hτP, ?_⟩
  set PM := (P : Subgroup Y).map Y.subtype with hPM
  have hPM2 : IsPGroup 2 PM := P.isPGroup'.map _
  have hPMY : PM ≤ Y := map_subtype_le _
  have hcard : Nat.card PM = Nat.card P := card_map_of_injective Y.subtype_injective
  have hC0 : Nat.card (PM ⊓ centralizer ({τ} : Set M) : Subgroup M) ≤ 2 :=
    h2 _ (le_inf inf_le_right (inf_le_left.trans hPMY)) (hPM2.to_le inf_le_left)
  have : Nontrivial P := ⟨⟨⟨τ', hτP⟩, 1, fun e => hτ'1 (congrArg Subtype.val e)⟩⟩
  have : Nontrivial (center P) := P.isPGroup'.center_nontrivial
  obtain ⟨z, hz1⟩ := exists_ne (1 : center P)
  have hzc : ∀ x : P, x * z = z * x := mem_center_iff.mp z.2
  have hzτ : ((((z : P) : Y) : M)) = τ := by
    refine eq_of_card_le_two hC0 ⟨⟨_, (z : P).2, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
      ⟨⟨τ', hτP, rfl⟩, mem_centralizer_singleton_iff.mpr rfl⟩ ?_ hτ1
    · have := congrArg (fun x : P => ((x : Y) : M)) (hzc ⟨τ', hτP⟩)
      exact this.symm
    · intro e
      exact hz1 (Subtype.ext (Subtype.ext (Subtype.ext e)))
  have hle : PM ≤ PM ⊓ centralizer ({τ} : Set M) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, mem_centralizer_singleton_iff.mpr ?_⟩
    have e : ((x : Y) : M) * (((z : P) : Y) : M) = (((z : P) : Y) : M) * ((x : Y) : M) :=
      congrArg (fun x : P => ((x : Y) : M)) (hzc ⟨x, hx⟩)
    rw [hzτ] at e
    exact e
  rw [← hcard]
  exact (card_le_of_le hle).trans hC0

theorem isPGroup_zpowers {Y : Type*} [Group Y] {y : Y} (hy2 : y * y = 1) :
    IsPGroup 2 (zpowers y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rintro ⟨_, k, rfl⟩
  refine ⟨1, Subtype.ext ?_⟩
  change (y ^ k) ^ 2 ^ 1 = 1
  rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, hy2,
    one_zpow]

theorem centralizer_le_normalizer' {K : Subgroup M} :
    centralizer (K : Set M) ≤ normalizer (K : Set M) := fun y hy =>
  mem_normalizer_of_conj_le fun k hk => by
    rw [← mem_centralizer_iff.mp hy k hk, mul_inv_cancel_right]
    exact hk

theorem normalizer_le_normalizer_centralizer' {K : Subgroup M} :
    normalizer (K : Set M) ≤ normalizer (centralizer (K : Set M) : Set M) := fun g hg =>
  mem_normalizer_of_conj_le fun y hy => mem_centralizer_iff.mpr fun k hk => by
    have hk' : g⁻¹ * k * g ∈ K := by
      have := (mem_normalizer_iff.mp (inv_mem hg) k).mp hk
      rwa [inv_inv] at this
    have h1 := mem_centralizer_iff.mp hy _ hk'
    calc k * (g * y * g⁻¹) = g * ((g⁻¹ * k * g) * y) * g⁻¹ := by group
      _ = g * (y * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
      _ = g * y * g⁻¹ * k := by group

variable (hτK : τ ∈ centralizer (K : Set M)) (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1)
  (h2 : ∀ V : Subgroup M, V ≤ centralizer ({τ} : Set M) ⊓ centralizer (K : Set M) →
    IsPGroup 2 V → Nat.card V ≤ 2)
include hτK hτ2 hτ1 h2

theorem card_le_two_of_le_centralizer {V : Subgroup M} (hV : V ≤ centralizer (K : Set M))
    (hV2 : IsPGroup 2 V) : Nat.card V ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, -, hP₀⟩ := exists_sylow_le_two hτK hτ2 hτ1 h2
  have hV' : IsPGroup 2 (V.subgroupOf (centralizer (K : Set M))) :=
    hV2.of_equiv (subgroupOfEquivOfLe hV).symm
  obtain ⟨P, hP⟩ := hV'.exists_le_sylow
  have h1 : Nat.card (V.subgroupOf (centralizer (K : Set M))) ≤ Nat.card P := card_le_of_le hP
  have h3 : Nat.card P = Nat.card P₀ := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  rw [Nat.card_congr (subgroupOfEquivOfLe hV).toEquiv] at h1
  omega

theorem exists_conj_eq_of_mem {u : M} (huK : u ∈ centralizer (K : Set M)) (hu2 : u * u = 1)
    (hu1 : u ≠ 1) : ∃ y ∈ centralizer (K : Set M), u = y * τ * y⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hτP₀, hP₀⟩ := exists_sylow_le_two hτK hτ2 hτ1 h2
  let u' : centralizer (K : Set M) := ⟨u, huK⟩
  obtain ⟨P, hP⟩ := (isPGroup_zpowers (y := u') (Subtype.ext hu2)).exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq (centralizer (K : Set M)) P₀ P
  have huP : u' ∈ ((y • P₀ : Sylow 2 (centralizer (K : Set M))) :
      Subgroup (centralizer (K : Set M))) := by
    rw [hy]
    exact hP (mem_zpowers u')
  rw [Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
    MulAut.conj_inv_apply] at huP
  have hcard : Nat.card ((P₀ : Subgroup (centralizer (K : Set M))).map
      (centralizer (K : Set M)).subtype) ≤ 2 := by
    rw [card_map_of_injective (centralizer (K : Set M)).subtype_injective]
    exact hP₀
  have e := eq_of_card_le_two hcard ⟨_, huP, rfl⟩ ⟨⟨τ, hτK⟩, hτP₀, rfl⟩ (fun e => hu1 (by
      have e' : (y : M)⁻¹ * u * y = 1 := e
      calc u = (y : M) * ((y : M)⁻¹ * u * y) * (y : M)⁻¹ := by group
        _ = 1 := by rw [e']; group)) hτ1
  refine ⟨y, y.2, ?_⟩
  have e' : (y : M)⁻¹ * u * y = τ := e
  rw [← e']
  group

theorem false_of_map_le (h4 : 4 ∣ Nat.card K) {g : M}
    (hle : K.map (MulAut.conj g).toMonoidHom ≤ centralizer (K : Set M)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K' := K.map (MulAut.conj g).toMonoidHom
  have hK' : Nat.card K' = Nat.card K := card_map_of_injective (MulAut.conj g).injective
  obtain ⟨V, hV⟩ := Sylow.exists_subgroup_card_pow_prime 2 (n := 2) (G := K')
    (by rw [hK']; exact h4)
  have h1 : Nat.card (V.map K'.subtype) = 4 := by
    rw [card_map_of_injective K'.subtype_injective, hV]
    norm_num
  have h3 := card_le_two_of_le_centralizer hτK hτ2 hτ1 h2 ((map_subtype_le V).trans hle)
    (IsPGroup.of_card (n := 2) (by rw [h1]; norm_num))
  omega

variable (hnorm : centralizer ({τ} : Set M) ≤ normalizer (K : Set M))
include hnorm


theorem centralizer_le_normalizer_of_mem {u : M} (huK : u ∈ centralizer (K : Set M))
    (hu2 : u * u = 1) (hu1 : u ≠ 1) :
    centralizer ({u} : Set M) ≤ normalizer (K : Set M) := by
  obtain ⟨y, hyK, rfl⟩ := exists_conj_eq_of_mem hτK hτ2 hτ1 h2 huK hu2 hu1
  intro c hc
  have h1 : y⁻¹ * c * y ∈ centralizer ({τ} : Set M) := by
    rw [mem_centralizer_singleton_iff] at hc ⊢
    calc y⁻¹ * c * y * τ = y⁻¹ * (c * (y * τ * y⁻¹)) * y := by group
      _ = y⁻¹ * ((y * τ * y⁻¹) * c) * y := by rw [hc]
      _ = τ * (y⁻¹ * c * y) := by group
  have hyN := centralizer_le_normalizer' hyK
  have h3 := mul_mem (mul_mem hyN (hnorm h1)) (inv_mem hyN)
  rwa [show y * (y⁻¹ * c * y) * y⁻¹ = c by group] at h3

theorem odd_card_inf [IsSimpleGroup K] (h4 : 4 ∣ Nat.card K) {g : M}
    (hg : g ∉ normalizer (centralizer (K : Set M) : Set M)) :
    Odd (Nat.card (centralizer (K : Set M) ⊓
      (centralizer (K : Set M)).map (MulAut.conj g).toMonoidHom : Subgroup M)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  rw [Nat.not_odd_iff_even] at hodd
  obtain ⟨⟨u, huI⟩, hu⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hodd)
  have huY : u ∈ centralizer (K : Set M) := (mem_inf.mp huI).1
  obtain ⟨y, hy, hyu⟩ := mem_map.mp (mem_inf.mp huI).2
  have hy' : g⁻¹ * u * g = y := by
    rw [← hyu]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hu2 : u * u = 1 := by
    have := pow_orderOf_eq_one (⟨u, huI⟩ : ↥(centralizer (K : Set M) ⊓
      (centralizer (K : Set M)).map (MulAut.conj g).toMonoidHom))
    rw [hu, pow_two] at this
    exact congrArg Subtype.val this
  have hu1 : u ≠ 1 := fun e => by
    have : (⟨u, huI⟩ : ↥(centralizer (K : Set M) ⊓
        (centralizer (K : Set M)).map (MulAut.conj g).toMonoidHom)) = 1 := Subtype.ext e
    rw [this, orderOf_one] at hu
    exact absurd hu (by norm_num)
  have hy2 : y * y = 1 := by
    rw [← hy', show g⁻¹ * u * g * (g⁻¹ * u * g) = g⁻¹ * (u * u) * g by group, hu2]
    group
  have hy1 : y ≠ 1 := fun e => hu1 (by
    rw [← hy'] at e
    calc u = g * (g⁻¹ * u * g) * g⁻¹ := by group
      _ = 1 := by rw [e]; group)
  have hCu := centralizer_le_normalizer_of_mem hτK hτ2 hτ1 h2 hnorm huY hu2 hu1
  have hCy := centralizer_le_normalizer_of_mem hτK hτ2 hτ1 h2 hnorm hy hy2 hy1
  set K' := K.map (MulAut.conj g).toMonoidHom with hK'def
  have hmemK' : ∀ {x : M}, x ∈ K' ↔ g⁻¹ * x * g ∈ K := fun {x} => by
    rw [hK'def, mem_map_equiv, MulAut.conj_symm_apply]
  have hKu : ∀ k ∈ K, k * u = u * k := fun k hk => (mem_centralizer_iff.mp huY k hk)
  have hK'u : ∀ k ∈ K', k * u = u * k := fun k hk => by
    have h1 := mem_centralizer_iff.mp hy _ (hmemK'.mp hk)
    rw [← hy'] at h1
    calc k * u = g * ((g⁻¹ * k * g) * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * u * g) * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
      _ = u * k := by group
  have hCuK' : ∀ c : M, c * u = u * c → ∀ k ∈ K', c * k * c⁻¹ ∈ K' := fun c hc k hk => by
    have h1 : g⁻¹ * c * g ∈ centralizer ({y} : Set M) := by
      rw [mem_centralizer_singleton_iff, ← hy']
      calc g⁻¹ * c * g * (g⁻¹ * u * g) = g⁻¹ * (c * u) * g := by group
        _ = g⁻¹ * (u * c) * g := by rw [hc]
        _ = g⁻¹ * u * g * (g⁻¹ * c * g) := by group
    have h2 := (mem_normalizer_iff.mp (hCy h1) _).mp (hmemK'.mp hk)
    rw [hmemK']
    rwa [show g⁻¹ * (c * k * c⁻¹) * g = g⁻¹ * c * g * (g⁻¹ * k * g) * (g⁻¹ * c * g)⁻¹ by group]
  have hCuK : ∀ c : M, c * u = u * c → ∀ k ∈ K, c * k * c⁻¹ ∈ K := fun c hc k hk =>
    (mem_normalizer_iff.mp (hCu (mem_centralizer_singleton_iff.mpr hc)) k).mp hk
  have hnormal : (K'.subgroupOf K).Normal := ⟨fun x hx k => by
    rw [mem_subgroupOf] at hx ⊢
    exact hCuK' _ (hKu _ k.2) _ hx⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K'.subgroupOf K) with hbot | htop
  ·
    refine false_of_map_le hτK hτ2 hτ1 h2 h4 (g := g) fun k' hk' => ?_
    refine mem_centralizer_iff.mpr fun k hk => ?_
    have hc1 : k * k' * k⁻¹ * k'⁻¹ ∈ K' :=
      mul_mem (hCuK' _ (hKu _ hk) _ hk') (inv_mem hk')
    have hc2 : k * k' * k⁻¹ * k'⁻¹ ∈ K := by
      rw [show k * k' * k⁻¹ * k'⁻¹ = k * (k' * k⁻¹ * k'⁻¹) by group]
      exact mul_mem hk (hCuK _ (hK'u _ hk') _ (inv_mem hk))
    have h3 : (⟨_, hc2⟩ : K) ∈ K'.subgroupOf K := mem_subgroupOf.mpr hc1
    rw [hbot, mem_bot] at h3
    have h4' : k * k' * k⁻¹ * k'⁻¹ = 1 := congrArg Subtype.val h3
    calc k * k' = k * k' * k⁻¹ * k'⁻¹ * (k' * k) := by group
      _ = k' * k := by rw [h4', one_mul]
  ·
    apply hg
    have hle : K ≤ K' := subgroupOf_eq_top.mp htop
    have heq : K = K' := eq_of_le_of_card_ge hle
      (card_map_of_injective (MulAut.conj g).injective).le
    refine normalizer_le_normalizer_centralizer' (mem_normalizer_of_conj_le fun k hk => ?_)
    rw [heq]
    exact ⟨k, hk, rfl⟩

theorem normalizer_centralizer_eq :
    normalizer (centralizer (K : Set M) : Set M) = normalizer (K : Set M) := by
  refine le_antisymm (fun g hg => ?_) normalizer_le_normalizer_centralizer'
  have e1 : g * τ * g⁻¹ ∈ centralizer (K : Set M) := (mem_normalizer_iff.mp hg τ).mp hτK
  have e2 : g * τ * g⁻¹ * (g * τ * g⁻¹) = 1 := by
    rw [show g * τ * g⁻¹ * (g * τ * g⁻¹) = g * (τ * τ) * g⁻¹ by group, hτ2]
    group
  have e3 : g * τ * g⁻¹ ≠ 1 := fun e => hτ1 (by
    calc τ = g⁻¹ * (g * τ * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group)
  obtain ⟨y, hy, hyτ⟩ := exists_conj_eq_of_mem hτK hτ2 hτ1 h2 e1 e2 e3
  have e4 : y⁻¹ * g ∈ centralizer ({τ} : Set M) := by
    rw [mem_centralizer_singleton_iff]
    calc y⁻¹ * g * τ = y⁻¹ * (g * τ * g⁻¹) * g := by group
      _ = y⁻¹ * (y * τ * y⁻¹) * g := by rw [hyτ]
      _ = τ * (y⁻¹ * g) := by group
  have e5 := mul_mem (centralizer_le_normalizer' hy) (hnorm e4)
  rwa [mul_inv_cancel_left] at e5

omit hnorm in
theorem commutator_map_ne_bot (h4 : 4 ∣ Nat.card K) (g : M) :
    ⁅K, K.map (MulAut.conj g).toMonoidHom⁆ ≠ ⊥ := fun hbot =>
  false_of_map_le hτK hτ2 hτ1 h2 h4 (g := g)
    (le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp hbot))

omit [Finite M] hτK hτ2 hτ1 h2 hnorm in
theorem isQuasisimple_of [IsSimpleGroup K] (hperf : commutator K = ⊤) :
    CFSG.Open.IsQuasisimple K := by
  refine ⟨hperf, ?_⟩
  have hcen : center K = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center K) with h | h
    · exact h
    · exfalso
      have hcomm : commutator K = ⊥ := by
        rw [commutator_def, commutator_eq_bot_iff_le_centralizer]
        intro x _
        exact mem_centralizer_iff.mpr fun y _ => (mem_center_iff.mp (h ▸ mem_top x) y)
      rw [hcomm] at hperf
      obtain ⟨a, b, hab⟩ := exists_pair_ne K
      have ha : a ∈ (⊥ : Subgroup K) := hperf ▸ mem_top a
      have hb : b ∈ (⊥ : Subgroup K) := hperf ▸ mem_top b
      exact hab ((mem_bot.mp ha).trans (mem_bot.mp hb).symm)
  exact ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot).isSimpleGroup

theorem standard_of [IsSimpleGroup K] (hperf : commutator K = ⊤) (h4 : 4 ∣ Nat.card K) :
    (∃ V : Sylow 2 ↥(centralizer (K : Set M)),
      (V : Subgroup _).map (centralizer (K : Set M)).subtype = zpowers τ) ∧
      CFSG.Open.standardComponentIsStandard K := by
  refine ⟨?_, isQuasisimple_of hperf, ?_, fun g hg => odd_card_inf hτK hτ2 hτ1 h2 hnorm h4 hg,
    normalizer_centralizer_eq hτK hτ2 hτ1 h2 hnorm, commutator_map_ne_bot hτK hτ2 hτ1 h2 h4⟩
  · obtain ⟨P, hτP, hP⟩ := exists_sylow_le_two hτK hτ2 hτ1 h2
    refine ⟨P, ?_⟩
    have hle : zpowers τ ≤ (P : Subgroup _).map (centralizer (K : Set M)).subtype :=
      zpowers_le.mpr ⟨⟨τ, hτK⟩, hτP, rfl⟩
    refine (eq_of_le_of_card_ge hle ?_).symm
    rw [card_map_of_injective (centralizer (K : Set M)).subtype_injective, Nat.card_zpowers,
      orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hτ2) hτ1]
    exact hP
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h := Subgroup.orderOf_dvd_natCard (centralizer (K : Set M)) hτK
    rw [orderOf_eq_prime (p := 2) (by rw [pow_two]; exact hτ2) hτ1] at h
    exact even_iff_two_dvd.mpr h

end Standard

section Quot

variable {G : Type*} [Group G]

abbrev BarM (X : Subgroup G) : Type _ :=
  ↥(normalizer (X : Set G)) ⧸ X.subgroupOf (normalizer (X : Set G))

abbrev barMap (X : Subgroup G) : ↥(normalizer (X : Set G)) →* BarM X :=
  QuotientGroup.mk' (X.subgroupOf (normalizer (X : Set G)))

abbrev barSub (X Y : Subgroup G) : Subgroup (BarM X) :=
  (Y.subgroupOf (normalizer (X : Set G))).map (barMap X)

theorem barMap_eq_iff {X : Subgroup G} {a b : ↥(normalizer (X : Set G))} :
    barMap X a = barMap X b ↔ (a : G)⁻¹ * b ∈ X := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, mem_subgroupOf]
  rfl

theorem barMap_eq_one_iff {X : Subgroup G} {a : ↥(normalizer (X : Set G))} :
    barMap X a = 1 ↔ (a : G) ∈ X := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]

theorem mem_barSub_iff {X Y : Subgroup G} (hXY : X ≤ Y) (m : ↥(normalizer (X : Set G))) :
    barMap X m ∈ barSub X Y ↔ (m : G) ∈ Y := by
  constructor
  · rintro ⟨m', hm', e⟩
    have h1 := barMap_eq_iff.mp e
    rw [show (m : G) = m' * ((m' : G)⁻¹ * m) by group]
    exact mul_mem (mem_subgroupOf.mp hm') (hXY h1)
  · intro hm
    exact ⟨m, mem_subgroupOf.mpr hm, rfl⟩

theorem card_barSub [Finite G] {X Y : Subgroup G} (hXY : X ≤ Y)
    (hY : Y ≤ normalizer (X : Set G)) : Nat.card (barSub X Y) * Nat.card X = Nat.card Y := by
  have h1 := BothTrivial.card_map_mk' (X.subgroupOf (normalizer (X : Set G)))
    (A := Y.subgroupOf (normalizer (X : Set G))) fun x hx => mem_subgroupOf.mpr
      (hXY (mem_subgroupOf.mp hx))
  rwa [Nat.card_congr (subgroupOfEquivOfLe (le_normalizer : X ≤ normalizer (X : Set G))).toEquiv,
    Nat.card_congr (subgroupOfEquivOfLe hY).toEquiv] at h1

theorem centralizer_eq_of {X N C₀ CU : Subgroup G} {Z : Subgroup (BarM X)} {t : G}
    (ht : t ∈ normalizer (X : Set G))
    (hcent : centralizer ({barMap X ⟨t, ht⟩} : Set (BarM X)) = barSub X N)
    (hC₀ : ∀ m : ↥(normalizer (X : Set G)), (m : G) ∈ N →
      ∃ c : ↥(normalizer (X : Set G)), (c : G) ∈ C₀ ∧ barMap X c = barMap X m)
    (hker : ∀ c : ↥(normalizer (X : Set G)), (c : G) ∈ C₀ →
      (∀ y : ↥(normalizer (X : Set G)), (y : G) ∈ CU → ((y : G) * c)⁻¹ * (c * y) ∈ X) →
        barMap X c ∈ Z)
    (hZ : Z ≤ centralizer ({barMap X ⟨t, ht⟩} : Set (BarM X)) ⊓
      centralizer (barSub X CU : Set (BarM X))) :
    centralizer ({barMap X ⟨t, ht⟩} : Set (BarM X)) ⊓
      centralizer (barSub X CU : Set (BarM X)) = Z := by
  refine le_antisymm (fun g hg => ?_) hZ
  obtain ⟨hgτ, hgK⟩ := mem_inf.mp hg
  rw [hcent] at hgτ
  obtain ⟨m, hm, rfl⟩ := hgτ
  obtain ⟨c, hcC, hcm⟩ := hC₀ m (mem_subgroupOf.mp hm)
  rw [← hcm] at hgK ⊢
  refine hker c hcC fun y hy => ?_
  have h1 := mem_centralizer_iff.mp hgK (barMap X y) ⟨y, mem_subgroupOf.mpr hy, rfl⟩
  rw [← map_mul, ← map_mul] at h1
  exact barMap_eq_iff.mp h1

end Quot

section Elementary

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {K : Type} [Field K] [CharP K 2]
  [Finite K] {n : ℕ} {φ : L ≃* antiSp K} {t : G}

local notation "𝐁[" i "]" => (zpowers t ⊔ pull φ (rootA K i) : Subgroup G)
local notation "𝐀[" i "]" => pull φ (rootA K i)
local notation "𝐔[" i "]" => pull φ (rootU K i)
local notation "𝐍[" i "]" => normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) :
  Subgroup G) : Set G)
set_option quotPrecheck false in
local notation "𝐃[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootU K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄[" i "]" => (CFSG.pCore 2 (normalizer
  (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G))).map
  (normalizer (((zpowers t ⊔ pull φ (rootA K i) : Subgroup G) : Subgroup G) : Set G)).subtype
set_option quotPrecheck false in
local notation "𝐄₀" => (𝐄[Axis.one] ⊓ 𝐄[Axis.two] : Subgroup G)
set_option quotPrecheck false in
local notation "𝐂" => centralizer ({t} : Set G)
set_option quotPrecheck false in
local notation "𝐅" => closure {x : G | ∃ e ∈ 𝐄₀, ∃ j ∈ pull φ (diagTorus K),
  x = e⁻¹ * (j⁻¹ * e * j)}
set_option quotPrecheck false in
local notation "𝐋[" i "]" => (𝐅 ⊔ 𝐀[i] : Subgroup G)
local notation "𝐰[" i "]" => ((φ.symm (weylElt K i) : L) : G)
set_option quotPrecheck false in
local notation "𝐗[" i "]" => (𝐅 ⊔ 𝐅.map (MulAut.conj 𝐰[i]⁻¹).toMonoidHom : Subgroup G)

omit [Finite G] [Finite K] in
theorem t_mem_B (i : Axis) : t ∈ 𝐁[i] := mem_sup_left (mem_zpowers t)

theorem B_le_E (h : FCHyp L K n φ t) (i : Axis) : 𝐁[i] ≤ 𝐄[i] := (h.B_le_D i).trans (h.D_le_E i)

theorem A_le_X (h : FCHyp L K n φ t) (i : Axis) : 𝐀[i] ≤ 𝐗[i] := (A_le_L i).trans (L_le_X h i)

theorem X_le_N (h : FCHyp L K n φ t) (i : Axis) : 𝐗[i] ≤ 𝐍[i] :=
  (X_le_E h i).trans (map_subtype_le _)

theorem X_inf_B (h : FCHyp L K n φ t) (i : Axis) : 𝐗[i] ⊓ 𝐁[i] = 𝐀[i] := by
  refine le_antisymm (fun x hx => ?_) (le_inf (A_le_X h i) le_sup_right)
  obtain ⟨hxX, hxB⟩ := mem_inf.mp hx
  rcases (mem_zpowers_sup_iff h.setup.t_mul_t
    (TwoCoreSetup.comm_pull (S := rootA K i) φ h.twoCore)).mp hxB with h1 | h1
  · exact h1
  · refine absurd ?_ (t_not_mem_X h i)
    have := mul_mem (A_le_X h i h1) (inv_mem hxX)
    rwa [mul_inv_cancel_right] at this

theorem X_inf_C (h : FCHyp L K n φ t) (i : Axis) : 𝐗[i] ⊓ 𝐂 = 𝐀[i] := by
  refine le_antisymm (fun x hx => ?_) (le_inf (A_le_X h i) (A_le_C h i))
  have hxB : x ∈ 𝐁[i] := by
    rw [← E_inf_C h i]
    exact ⟨X_le_E h i hx.1, hx.2⟩
  rw [← X_inf_B h i]
  exact ⟨hx.1, hxB⟩

theorem mem_X_or_B (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) {e : G} (he : e ∈ 𝐄[i]) (he2 : e * e = 1) : e ∈ 𝐗[i] ∨ e ∈ 𝐁[i] := by
  rcases mem_X_or_Hi h hbt i he (by rw [he2]; exact one_mem _) with h1 | h1
  · exact Or.inl h1
  · have htN : t ∈ normalizer (𝐋[i] : Set G) :=
      mem_normalizer_of_conj_le fun _ hl => conj_H_mem_L h i t_mem_H hl
    have hx : e ∈ 𝐋[i] ⊔ zpowers t := by
      rw [L_sup_t h i]
      exact h1
    rcases mem_or_mul_mem h.setup.t_mul_t htN hx with h2 | h2
    · exact Or.inl (L_le_X h i h2)
    · right
      have hsq : t * (t * e) * (t * (t * e)) = 1 := by
        rw [← mul_assoc t t, h.setup.t_mul_t, one_mul]
        exact he2
      have ha := mem_A_of_sq h hbt i h2 hsq
      have e1 : e = t * (t * e) := by rw [← mul_assoc, h.setup.t_mul_t, one_mul]
      rw [e1]
      exact mul_mem (t_mem_B i) (mem_sup_right ha)

omit [Finite G] [Finite K] in
theorem B_elem (h : FCHyp L K n φ t) (i : Axis) : IsElementaryAbelian 2 𝐁[i] :=
  isElementaryAbelian_of (fun _ hx _ hy => h.B_comm i hx hy) fun _ hx => h.B_mul_self i hx

omit [Finite G] [Finite K] in
theorem two_mul_pow_three_lt (h : FCHyp L K n φ t) : 2 * Nat.card K ^ 3 < Nat.card K ^ 6 := by
  have h4 := h.four_le_card
  have h1 : 4 ^ 3 ≤ Nat.card K ^ 3 := Nat.pow_le_pow_left h4 3
  have h3 : 0 < Nat.card K ^ 3 := by positivity
  calc 2 * Nat.card K ^ 3 < Nat.card K ^ 3 * Nat.card K ^ 3 :=
        Nat.mul_lt_mul_of_pos_right (by omega) h3
    _ = Nat.card K ^ 6 := by ring

theorem X_not_le_B (h : FCHyp L K n φ t) (i : Axis) : ¬ 𝐗[i] ≤ 𝐁[i] := fun hle => by
  have h1 := card_le_of_le hle
  rw [card_X h i, FCHyp.card_B h i] at h1
  have := two_mul_pow_three_lt h
  omega

theorem maximal_E (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) (W : Subgroup G) :
    Maximal (fun W : Subgroup G => W ≤ 𝐄[i] ∧ IsElementaryAbelian 2 W) W ↔
      W = 𝐗[i] ∨ W = 𝐁[i] :=
  maximal_elem_iff (X_le_E h i) (B_le_E h i) (X_elem h hbt i) (B_elem h i)
    (fun _ he he2 => mem_X_or_B h hbt i he he2) (X_not_le_B h i)
    (fun hle => t_not_mem_X h i (hle (t_mem_B i))) W

theorem normalizer_E_le_X (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : normalizer (𝐄[i] : Set G) ≤ normalizer (𝐗[i] : Set G) := by
  intro g hg
  have hWE : 𝐗[i].map (MulAut.conj g).toMonoidHom ≤ 𝐄[i] := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp hg x).mp (X_le_E h i hx)
  have hW2 : ∀ w ∈ 𝐗[i].map (MulAut.conj g).toMonoidHom, w * w = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, X_mul_self h hbt i hx]
    group
  rcases subgroup_le_of_subset_union (fun w hw => mem_X_or_B h hbt i (hWE hw) (hW2 w hw)) with
    hle | hle
  · exact mem_normalizer_of_conj_le fun x hx => hle ⟨x, hx, rfl⟩
  · exfalso
    have h1 := card_le_of_le hle
    rw [card_map_of_injective (MulAut.conj g).injective, card_X h i, FCHyp.card_B h i] at h1
    have := two_mul_pow_three_lt h
    omega

theorem normalizer_E_le_N (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : normalizer (𝐄[i] : Set G) ≤ 𝐍[i] := by
  intro g hg
  have hgX := normalizer_E_le_X h hbt i hg
  have hWE : 𝐁[i].map (MulAut.conj g).toMonoidHom ≤ 𝐄[i] := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_normalizer_iff.mp hg x).mp (B_le_E h i hx)
  have hW2 : ∀ w ∈ 𝐁[i].map (MulAut.conj g).toMonoidHom, w * w = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show g * x * g⁻¹ * (g * x * g⁻¹) = g * (x * x) * g⁻¹ by group, h.B_mul_self i hx]
    group
  rcases subgroup_le_of_subset_union (fun w hw => mem_X_or_B h hbt i (hWE hw) (hW2 w hw)) with
    hle | hle
  · exfalso
    have h1 : g * t * g⁻¹ ∈ 𝐗[i] := hle ⟨t, t_mem_B i, rfl⟩
    exact t_not_mem_X h i ((mem_normalizer_iff.mp hgX t).mpr h1)
  · exact mem_normalizer_of_conj_le fun x hx => hle ⟨x, hx, rfl⟩

omit [Finite K] in
theorem N_le_normalizer_E (i : Axis) : 𝐍[i] ≤ normalizer (𝐄[i] : Set G) := fun _ hg =>
  mem_normalizer_of_conj_le fun _ he => conj_mem_pCore_map hg he

theorem normalizer_E (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : normalizer (𝐄[i] : Set G) = 𝐍[i] :=
  le_antisymm (normalizer_E_le_N h hbt i) (N_le_normalizer_E i)

theorem N_le_normalizer_X (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : 𝐍[i] ≤ normalizer (𝐗[i] : Set G) :=
  (N_le_normalizer_E i).trans (normalizer_E_le_X h hbt i)

theorem t_mem_normalizer_X (h : FCHyp L K n φ t) (i : Axis) : t ∈ normalizer (𝐗[i] : Set G) :=
  D_le_normalizer_X h i (t_mem_D h i)

theorem X_mul_C0 (h : FCHyp L K n φ t) (i : Axis) :
    (𝐗[i] : Set G) * ((𝐂 ⊓ 𝐍[i] : Subgroup G) : Set G) = 𝐍[i] := by
  rw [← E_mul_C0 h i]
  apply Set.Subset.antisymm
  · rintro _ ⟨x, hx, c, hc, rfl⟩
    exact ⟨x, X_le_E h i hx, c, hc, rfl⟩
  · rintro _ ⟨e, he, c, hc, rfl⟩
    have he' : e ∈ (𝐗[i] : Set G) * (zpowers t : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ (zpowers_le.mpr (t_mem_normalizer_X h i)),
        (X_sup_t h i).2]
      exact he
    obtain ⟨x, hx, τ', hτ', rfl⟩ := he'
    have hτC : τ' ∈ 𝐂 ⊓ 𝐍[i] := (zpowers_le.mpr (mem_inf.mpr
      ⟨mem_centralizer_singleton_iff.mpr rfl, le_normalizer (t_mem_B i)⟩)) hτ'
    exact ⟨x, hx, τ' * c, mul_mem hτC hc, (mul_assoc _ _ _).symm⟩

theorem mem_N_iff (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) {m : G} (hm : m ∈ normalizer (𝐗[i] : Set G)) :
    m ∈ 𝐍[i] ↔ (m * t)⁻¹ * (t * m) ∈ 𝐗[i] := by
  rw [← normalizer_E h hbt i]
  have htt := h.setup.t_mul_t
  have hE : 𝐗[i] ⊔ zpowers t = 𝐄[i] := (X_sup_t h i).2
  constructor
  · intro hmE
    have h1 : m⁻¹ * t * m ∈ 𝐄[i] := by
      have := (mem_normalizer_iff.mp (inv_mem hmE) t).mp (t_mem_E h i)
      rwa [inv_inv] at this
    rw [← hE] at h1
    rcases mem_or_mul_mem htt (t_mem_normalizer_X h i) h1 with h2 | h2
    · refine absurd ?_ (t_not_mem_X h i)
      have := (mem_normalizer_iff.mp (inv_mem hm) t).mpr (by rwa [inv_inv])
      exact this
    · have e : (m * t)⁻¹ * (t * m) = t * (m⁻¹ * t * m) := by
        rw [mul_inv_rev, h.twoCore.t_inv]
        group
      rw [e]
      exact h2
  · intro hx
    have hle : 𝐗[i] ⊔ zpowers t ≤ (𝐗[i] ⊔ zpowers t).comap (MulAut.conj m⁻¹).toMonoidHom := by
      refine sup_le (fun x hx' => ?_) (zpowers_le.mpr ?_)
      · refine mem_sup_left ?_
        change m⁻¹ * x * m⁻¹⁻¹ ∈ 𝐗[i]
        exact (mem_normalizer_iff.mp (inv_mem hm) x).mp hx'
      · change m⁻¹ * t * m⁻¹⁻¹ ∈ 𝐗[i] ⊔ zpowers t
        rw [inv_inv, show m⁻¹ * t * m = t * ((m * t)⁻¹ * (t * m)) by group]
        exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hx)
    refine inv_mem_iff.mp (mem_normalizer_of_conj_le fun e he => ?_)
    rw [← hE] at he ⊢
    exact hle he

theorem centralizer_tau (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : centralizer ({barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩} : Set (BarM 𝐗[i])) =
      barSub 𝐗[i] 𝐍[i] := by
  ext x
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ x
  rw [mem_centralizer_singleton_iff]
  change barMap 𝐗[i] m * barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩ =
      barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩ * barMap 𝐗[i] m ↔ barMap 𝐗[i] m ∈ barSub 𝐗[i] 𝐍[i]
  rw [mem_barSub_iff (X_le_N h i), ← map_mul, ← map_mul, barMap_eq_iff,
    mem_N_iff h hbt i m.2]
  rfl

theorem quotient_C (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : ∃ _ : (𝐀[i].subgroupOf (𝐂 ⊓ 𝐍[i])).Normal,
      ∃ e : (↥(𝐂 ⊓ 𝐍[i]) ⧸ 𝐀[i].subgroupOf (𝐂 ⊓ 𝐍[i])) ≃*
        ↥(centralizer ({barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩} : Set (BarM 𝐗[i]))),
        ∀ (c : ↥(𝐂 ⊓ 𝐍[i])) (m : ↥(normalizer (𝐗[i] : Set G))), (c : G) = m →
          (e c : BarM 𝐗[i]) = barMap 𝐗[i] m := by
  have hCN : 𝐂 ⊓ 𝐍[i] ≤ normalizer (𝐗[i] : Set G) :=
    inf_le_right.trans (N_le_normalizer_X h hbt i)
  set ψ : ↥(𝐂 ⊓ 𝐍[i]) →* BarM 𝐗[i] := (barMap 𝐗[i]).comp (inclusion hCN) with hψ
  have hψc : ∀ c : ↥(𝐂 ⊓ 𝐍[i]), ψ c = barMap 𝐗[i] (inclusion hCN c) := fun _ => rfl
  have hker : ψ.ker = 𝐀[i].subgroupOf (𝐂 ⊓ 𝐍[i]) := by
    ext c
    rw [MonoidHom.mem_ker, mem_subgroupOf, hψc, barMap_eq_one_iff]
    change (c : G) ∈ 𝐗[i] ↔ _
    constructor
    · exact fun hc => (X_inf_C h i).le ⟨hc, (mem_inf.mp c.2).1⟩
    · exact fun hc => A_le_X h i hc
  have hrange : ψ.range =
      centralizer ({barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩} : Set (BarM 𝐗[i])) := by
    rw [centralizer_tau h hbt i]
    ext x
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨inclusion hCN c, mem_subgroupOf.mpr (mem_inf.mp c.2).2, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      have hm' : (m : G) ∈ (𝐗[i] : Set G) * ((𝐂 ⊓ 𝐍[i] : Subgroup G) : Set G) := by
        rw [X_mul_C0 h i]
        exact mem_subgroupOf.mp hm
      obtain ⟨x, hx, c, hc, hxc⟩ := hm'
      refine ⟨⟨c, hc⟩, ?_⟩
      rw [hψc, barMap_eq_iff]
      change c⁻¹ * (m : G) ∈ 𝐗[i]
      rw [← hxc, show c⁻¹ * (x * c) = c⁻¹ * x * c⁻¹⁻¹ by group]
      exact (mem_normalizer_iff.mp (inv_mem (hCN hc)) x).mp hx
  have hn : (𝐀[i].subgroupOf (𝐂 ⊓ 𝐍[i])).Normal := hker ▸ ψ.normal_ker
  refine ⟨hn, (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    ((QuotientGroup.quotientKerEquivRange ψ).trans (MulEquiv.subgroupCongr hrange)),
    fun c m hcm => ?_⟩
  have e1 : inclusion hCN c = m := Subtype.ext hcm
  change ψ c = barMap 𝐗[i] m
  rw [hψc, e1]

omit [Finite G] [Finite K] in
theorem CU_eq (i : Axis) : L ⊓ centralizer (𝐔[i] : Set G) = pull φ (rootC K i) :=
  (TwoCoreSetup.pull_rootC_eq φ i).symm

omit [Finite G] [Finite K] in
theorem CU_le_C (h : FCHyp L K n φ t) (i : Axis) : L ⊓ centralizer (𝐔[i] : Set G) ≤ 𝐂 :=
  inf_le_left.trans h.setup.L_le

theorem CU_le_normalizer_A (h : FCHyp L K n φ t) (i : Axis) :
    L ⊓ centralizer (𝐔[i] : Set G) ≤ normalizer (𝐀[i] : Set G) := by
  intro c hc
  rw [CU_eq] at hc
  obtain ⟨c', hc', rfl⟩ := exists_eq_symm_of_mem_pull hc
  refine mem_normalizer_of_conj_le fun a ha => ?_
  obtain ⟨a', ha', rfl⟩ := exists_eq_symm_of_mem_pull ha
  rw [symm_conj_eq, symm_mem_pull]
  exact (h.twoCore.axisStr i).A_normal_C c' hc' a' ha'

theorem CU_le_N (h : FCHyp L K n φ t) (i : Axis) : L ⊓ centralizer (𝐔[i] : Set G) ≤ 𝐍[i] :=
  fun _ hc => (h.twoCore.mem_normalizer_zpowers_sup_iff (CU_le_C h i hc) (pull_le φ _)).mpr
    (CU_le_normalizer_A h i hc)

theorem CU_le_normalizer_X (h : FCHyp L K n φ t) (i : Axis) :
    L ⊓ centralizer (𝐔[i] : Set G) ≤ normalizer (𝐗[i] : Set G) := fun _ hc =>
  normalizer_A_le h i ⟨hc.1, CU_le_normalizer_A h i hc⟩

theorem X_inf_CU (h : FCHyp L K n φ t) (i : Axis) :
    𝐗[i] ⊓ (L ⊓ centralizer (𝐔[i] : Set G)) = 𝐀[i] :=
  le_antisymm (fun _ hx => (X_inf_C h i).le ⟨hx.1, CU_le_C h i hx.2⟩)
    (le_inf (A_le_X h i) ((h.twoCore.A_le_rootC φ i).trans (CU_eq i).ge))

omit [Finite G] in
theorem s_mem_CU (h : FCHyp L K n φ t) (i : Axis) (M : SL₂ K) :
    ((φ.symm (sHom K i M) : L) : G) ∈ L ⊓ centralizer (𝐔[i] : Set G) := by
  rw [CU_eq]
  exact symm_mem_pull.mpr ((h.twoCore.axisStr i).s_mem_C M)

theorem equiv_K (h : FCHyp L K n φ t) (i : Axis) :
    ∃ e : SL₂ K ≃* ↥(barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G))),
      ∀ (M : SL₂ K) (m : ↥(normalizer (𝐗[i] : Set G))),
        (m : G) = ((φ.symm (sHom K i M) : L) : G) → (e M : BarM 𝐗[i]) = barMap 𝐗[i] m := by
  have hCU := CU_le_normalizer_X h i
  let σ₀ : SL₂ K →* ↥(normalizer (𝐗[i] : Set G)) :=
    (L.subtype.comp (φ.symm.toMonoidHom.comp (sHom K i))).codRestrict _
      fun M => hCU (s_mem_CU h i M)
  have hσ₀ : ∀ M, (σ₀ M : G) = ((φ.symm (sHom K i M) : L) : G) := fun _ => rfl
  let σ : SL₂ K →* ↥(barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G))) :=
    ((barMap 𝐗[i]).comp σ₀).codRestrict _
      fun M => ⟨σ₀ M, mem_subgroupOf.mpr (s_mem_CU h i M), rfl⟩
  have hσ : ∀ M, (σ M : BarM 𝐗[i]) = barMap 𝐗[i] (σ₀ M) := fun _ => rfl
  have hinj : Function.Injective σ := by
    rw [injective_iff_map_eq_one]
    intro M hM
    have h1 : (σ₀ M : G) ∈ 𝐗[i] := by
      rw [← barMap_eq_one_iff, ← hσ, hM]
      rfl
    have h2 : sHom K i M ∈ rootA K i := symm_mem_pull.mp
      ((X_inf_CU h i).le ⟨h1, s_mem_CU h i M⟩)
    exact ((h.twoCore.axisStr i).C_unique _ h2 1 (one_mem (rootA K i)) 1 M
      (by rw [map_one, mul_one, one_mul])).2.symm
  have hsurj : Function.Surjective σ := by
    rintro ⟨_, ⟨m, hm, rfl⟩⟩
    have hmCU : (m : G) ∈ pull φ (rootC K i) := by
      rw [← CU_eq]
      exact mem_subgroupOf.mp hm
    obtain ⟨c, hc, hcm⟩ := exists_eq_symm_of_mem_pull hmCU
    obtain ⟨a, ha, M, rfl⟩ := (h.twoCore.axisStr i).C_decomp c hc
    refine ⟨M, Subtype.ext ?_⟩
    rw [hσ, barMap_eq_iff, hσ₀, ← hcm, map_mul, coe_mul]
    rw [show (((φ.symm (sHom K i M) : L) : G))⁻¹ * (((φ.symm a : L) : G) *
      ((φ.symm (sHom K i M) : L) : G)) = (((φ.symm (sHom K i M) : L) : G))⁻¹ *
        ((φ.symm a : L) : G) * ((φ.symm (sHom K i M) : L) : G)⁻¹⁻¹ by group]
    refine A_le_X h i ((mem_normalizer_iff.mp (inv_mem (CU_le_normalizer_A h i
      (s_mem_CU h i M))) _).mp (symm_mem_pull.mpr ha))
  refine ⟨MulEquiv.ofBijective σ ⟨hinj, hsurj⟩, fun M m hm => ?_⟩
  change barMap 𝐗[i] (σ₀ M) = barMap 𝐗[i] m
  congr 1
  exact Subtype.ext hm.symm

theorem simple_K (h : FCHyp L K n φ t) (i : Axis) :
    IsSimpleGroup ↥(barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G))) := by
  have := sl2_isSimpleGroup (K := K) h.four_le_card
  obtain ⟨e, -⟩ := equiv_K h i
  exact e.symm.isSimpleGroup

theorem K_le_centralizer_tau (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G)) ≤
      centralizer ({barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩} : Set (BarM 𝐗[i])) := by
  rw [centralizer_tau h hbt i]
  rintro _ ⟨m, hm, rfl⟩
  exact ⟨m, mem_subgroupOf.mpr (CU_le_N h i (mem_subgroupOf.mp hm)), rfl⟩

theorem conj_C0_mem_CU (h : FCHyp L K n φ t) (i : Axis) {c : G} (hc : c ∈ 𝐂 ⊓ 𝐍[i]) {y : G}
    (hy : y ∈ L ⊓ centralizer (𝐔[i] : Set G)) : c * y * c⁻¹ ∈ L ⊓ centralizer (𝐔[i] : Set G) := by
  refine ⟨(mem_normalizer_iff.mp (h.setup.cent_le hc.1) y).mp hy.1, mem_centralizer_iff.mpr
    fun u hu => ?_⟩
  have hcU := FCHyp.N_le_normalizer_U h i hc.2
  have hu' : c⁻¹ * u * c ∈ 𝐔[i] := by
    have := (mem_normalizer_iff.mp (inv_mem hcU) u).mp hu
    rwa [inv_inv] at this
  have h1 := mem_centralizer_iff.mp hy.2 _ hu'
  calc u * (c * y * c⁻¹) = c * ((c⁻¹ * u * c) * y) * c⁻¹ := by group
    _ = c * (y * (c⁻¹ * u * c)) * c⁻¹ := by rw [h1]
    _ = c * y * c⁻¹ * u := by group

theorem exists_C0_of_mem_N (h : FCHyp L K n φ t) (i : Axis) {m : ↥(normalizer (𝐗[i] : Set G))}
    (hm : (m : G) ∈ 𝐍[i]) : ∃ c : ↥(normalizer (𝐗[i] : Set G)), (c : G) ∈ 𝐂 ⊓ 𝐍[i] ∧
      barMap 𝐗[i] c = barMap 𝐗[i] m := by
  have hm' : (m : G) ∈ (𝐗[i] : Set G) * ((𝐂 ⊓ 𝐍[i] : Subgroup G) : Set G) := by
    rw [X_mul_C0 h i]
    exact hm
  obtain ⟨x, hx, c, hc, hxc⟩ := hm'
  have hcm : c ∈ normalizer (𝐗[i] : Set G) := by
    have := mul_mem (inv_mem (le_normalizer hx)) m.2
    rwa [← hxc, inv_mul_cancel_left] at this
  refine ⟨⟨c, hcm⟩, hc, ?_⟩
  rw [barMap_eq_iff]
  change c⁻¹ * (m : G) ∈ 𝐗[i]
  rw [← hxc, show c⁻¹ * (x * c) = c⁻¹ * x * c⁻¹⁻¹ by group]
  exact (mem_normalizer_iff.mp (inv_mem hcm) x).mp hx

theorem K_normal (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : ((barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G))).subgroupOf
      (centralizer ({barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩} : Set (BarM 𝐗[i])))).Normal := by
  rw [normal_subgroupOf_iff (K_le_centralizer_tau h hbt i)]
  intro k g hk hg
  rw [centralizer_tau h hbt i] at hg
  obtain ⟨m, hm, rfl⟩ := hg
  obtain ⟨c, hc, hcm⟩ := exists_C0_of_mem_N h i (mem_subgroupOf.mp hm)
  obtain ⟨y, hy, rfl⟩ := hk
  rw [← hcm, ← map_inv, ← map_mul, ← map_mul]
  exact ⟨c * y * c⁻¹, mem_subgroupOf.mpr (conj_C0_mem_CU h i hc (mem_subgroupOf.mp hy)), rfl⟩

theorem centralizer_tau_le_normalizer (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis) :
    centralizer ({barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩} : Set (BarM 𝐗[i])) ≤
      normalizer (barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G)) : Set (BarM 𝐗[i])) :=
  have := K_normal h hbt i
  le_normalizer_of_normal_subgroupOf (K_le_centralizer_tau h hbt i)

omit [Finite G] in
theorem d_mem_normalizer_A (h : FCHyp L K n φ t) (i : Axis) (l : Kˣ) :
    ((φ.symm (dHom K i l) : L) : G) ∈ normalizer (𝐀[i] : Set G) := by
  have hN : dHom K i l ∈ normalizer (rootA K i : Set (antiSp K)) := by
    rw [← (h.twoCore.axisStr i).N_eq]
    simpa using (h.twoCore.axisStr i).ds_mem_N l 1
  rw [mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    obtain ⟨a', ha', rfl⟩ := exists_eq_symm_of_mem_pull ha
    rw [symm_conj_eq, symm_mem_pull]
    exact (mem_normalizer_iff.mp hN a').mp ha'
  · intro ha
    have haL : a ∈ L := by
      have := pull_le φ _ ha
      have hdL := (φ.symm (dHom K i l)).2
      have h1 := mul_mem (mul_mem (inv_mem hdL) this) hdL
      rwa [show (((φ.symm (dHom K i l) : L) : G))⁻¹ * (((φ.symm (dHom K i l) : L) : G) * a *
        ((φ.symm (dHom K i l) : L) : G)⁻¹) * ((φ.symm (dHom K i l) : L) : G) = a by group] at h1
    obtain ⟨a', rfl⟩ : ∃ a', ((φ.symm a' : L) : G) = a := ⟨φ ⟨a, haL⟩, by simp⟩
    rw [symm_conj_eq, symm_mem_pull] at ha
    exact symm_mem_pull.mpr ((mem_normalizer_iff.mp hN a').mpr ha)

theorem d_mem_N (h : FCHyp L K n φ t) (i : Axis) (l : Kˣ) :
    ((φ.symm (dHom K i l) : L) : G) ∈ 𝐍[i] :=
  (h.twoCore.mem_normalizer_zpowers_sup_iff (h.setup.L_le (φ.symm (dHom K i l)).2)
    (pull_le φ _)).mpr (d_mem_normalizer_A h i l)

theorem card_dbar (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : Nat.card (barSub 𝐗[i] (L.subtype.comp (φ.symm.toMonoidHom.comp
      (dHom K i))).range) = Nat.card K - 1 := by
  have hd : ∀ l, ((φ.symm (dHom K i l) : L) : G) ∈ normalizer (𝐗[i] : Set G) := fun l =>
    N_le_normalizer_X h hbt i (d_mem_N h i l)
  let δ₀ : Kˣ →* ↥(normalizer (𝐗[i] : Set G)) :=
    (L.subtype.comp (φ.symm.toMonoidHom.comp (dHom K i))).codRestrict _ hd
  have hδ₀ : ∀ l, (δ₀ l : G) = ((φ.symm (dHom K i l) : L) : G) := fun _ => rfl
  let δ : Kˣ →* BarM 𝐗[i] := (barMap 𝐗[i]).comp δ₀
  have hinj : Function.Injective δ := by
    rw [injective_iff_map_eq_one]
    intro l hl
    have h1 : (δ₀ l : G) ∈ 𝐗[i] := barMap_eq_one_iff.mp hl
    have h2 : dHom K i l ∈ rootA K i := by
      refine symm_mem_pull.mp ((X_inf_C h i).le ⟨h1, ?_⟩)
      exact h.setup.L_le (φ.symm (dHom K i l)).2
    have h3 := (h.twoCore.axisStr i).N_unique 1 (one_mem (rootA K i)) _ h2 l 1 1 1
      (by simp)
    exact h3.2.1
  have hrange : δ.range = barSub 𝐗[i] (L.subtype.comp (φ.symm.toMonoidHom.comp
      (dHom K i))).range := by
    ext x
    constructor
    · rintro ⟨l, rfl⟩
      exact ⟨δ₀ l, mem_subgroupOf.mpr ⟨l, rfl⟩, rfl⟩
    · rintro ⟨m, hm, rfl⟩
      obtain ⟨l, hl⟩ := mem_subgroupOf.mp hm
      exact ⟨l, congrArg (barMap 𝐗[i]) (Subtype.ext hl)⟩
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units]

omit [Finite G] in
theorem d_comm_s (h : FCHyp L K n φ t) (i : Axis) (l : Kˣ) (M : SL₂ K) :
    ((φ.symm (dHom K i l) : L) : G) * ((φ.symm (sHom K i M) : L) : G) =
      ((φ.symm (sHom K i M) : L) : G) * ((φ.symm (dHom K i l) : L) : G) := by
  rw [← coe_mul, ← coe_mul, ← map_mul, ← map_mul, (h.twoCore.axisStr i).s_comm_d M l]

theorem dbar_le_centralizer_K (h : FCHyp L K n φ t) (i : Axis) :
    barSub 𝐗[i] (L.subtype.comp (φ.symm.toMonoidHom.comp (dHom K i))).range ≤
      centralizer (barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G)) : Set (BarM 𝐗[i])) := by
  obtain ⟨e, he⟩ := equiv_K h i
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨l, hl⟩ := mem_subgroupOf.mp hm
  refine mem_centralizer_iff.mpr fun k hk => ?_
  obtain ⟨M, hM⟩ := e.surjective ⟨k, hk⟩
  have hsN : ((φ.symm (sHom K i M) : L) : G) ∈ normalizer (𝐗[i] : Set G) :=
    CU_le_normalizer_X h i (s_mem_CU h i M)
  have hk' : k = barMap 𝐗[i] ⟨_, hsN⟩ := by
    rw [← he M ⟨_, hsN⟩ rfl, hM]
  rw [hk', ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  change ((φ.symm (sHom K i M) : L) : G) * (m : G) = (m : G) * ((φ.symm (sHom K i M) : L) : G)
  rw [← hl]
  exact (d_comm_s h i l M).symm


theorem comm_s_mem_A (h : FCHyp L K n φ t) (i : Axis) {c : G} (hcC : c ∈ 𝐂)
    (hcX : c ∈ normalizer (𝐗[i] : Set G))
    (hcK : ∀ y : ↥(normalizer (𝐗[i] : Set G)), (y : G) ∈ L ⊓ centralizer (𝐔[i] : Set G) →
      ((y : G) * c)⁻¹ * (c * y) ∈ 𝐗[i]) (M : SL₂ K) :
    (((φ.symm (sHom K i M) : L) : G))⁻¹ * (c * ((φ.symm (sHom K i M) : L) : G) * c⁻¹) ∈ 𝐀[i] := by
  set y := ((φ.symm (sHom K i M) : L) : G)
  have h1 := hcK ⟨y, CU_le_normalizer_X h i (s_mem_CU h i M)⟩ (s_mem_CU h i M)
  have h2 : c * (((y : G) * c)⁻¹ * (c * y)) * c⁻¹ ∈ 𝐗[i] := (mem_normalizer_iff.mp hcX _).mp h1
  have hyC := h.setup.L_le (φ.symm (sHom K i M)).2
  refine (X_inf_C h i).le (mem_inf.mpr ⟨?_,
    mul_mem (inv_mem hyC) (mul_mem (mul_mem hcC hyC) (inv_mem hcC))⟩)
  rwa [show c * ((y * c)⁻¹ * (c * y)) * c⁻¹ = y⁻¹ * (c * y * c⁻¹) by group] at h2

theorem normAct_ker (h : FCHyp L K n φ t) (i : Axis) {c : G} (hcC : c ∈ 𝐂) (hcN : c ∈ 𝐍[i])
    (hcs : ∀ M : SL₂ K, (((φ.symm (sHom K i M) : L) : G))⁻¹ *
      (c * ((φ.symm (sHom K i M) : L) : G) * c⁻¹) ∈ 𝐀[i])
    {y : antiSp K} (hy : y ∈ centralizer (rootU K i : Set (antiSp K))) :
    y⁻¹ * normAct φ (⟨c, h.setup.cent_le hcC⟩ : normalizer (L : Set G)) y ∈ rootA K i := by
  obtain ⟨a, ha, M, rfl⟩ := (h.twoCore.axisStr i).C_decomp y hy
  refine (symm_mem_pull (φ := φ)).mp ?_
  have e1 : ((φ.symm ((a * sHom K i M)⁻¹ *
      normAct φ (⟨c, h.setup.cent_le hcC⟩ : normalizer (L : Set G)) (a * sHom K i M)) : L) : G) =
      (((φ.symm (sHom K i M) : L) : G))⁻¹ * ((((φ.symm a : L) : G))⁻¹ *
        (c * ((φ.symm a : L) : G) * c⁻¹)) * ((φ.symm (sHom K i M) : L) : G) *
      ((((φ.symm (sHom K i M) : L) : G))⁻¹ * (c * ((φ.symm (sHom K i M) : L) : G) * c⁻¹)) := by
    rw [map_mul, coe_mul, map_inv, coe_inv, normAct_symm_apply, map_mul, coe_mul]
    group
  rw [e1]
  have ha' : ((φ.symm a : L) : G) ∈ 𝐀[i] := symm_mem_pull.mpr ha
  have h3 : (((φ.symm a : L) : G))⁻¹ * (c * ((φ.symm a : L) : G) * c⁻¹) ∈ 𝐀[i] :=
    mul_mem (inv_mem ha') ((mem_normalizer_iff.mp (FCHyp.N_le_normalizer_A h i hcN) _).mp ha')
  have h4 := (mem_normalizer_iff.mp (inv_mem (CU_le_normalizer_A h i (s_mem_CU h i M))) _).mp h3
  rw [inv_inv] at h4
  exact mul_mem h4 (hcs M)

theorem exists_eq_of_ker (h : FCHyp L K n φ t) (i : Axis) {c : G} (hcC : c ∈ 𝐂) (hcN : c ∈ 𝐍[i])
    (hcs : ∀ M : SL₂ K, (((φ.symm (sHom K i M) : L) : G))⁻¹ *
      (c * ((φ.symm (sHom K i M) : L) : G) * c⁻¹) ∈ 𝐀[i]) :
    ∃ a ∈ rootA K i, ∃ (l : Kˣ) (k : ℤ),
      c = ((φ.symm a : L) : G) * ((φ.symm (dHom K i l) : L) : G) * t ^ k := by
  set α := normAct φ (⟨c, h.setup.cent_le hcC⟩ : normalizer (L : Set G))
  have hα : α ∈ autStab (rootU K i) :=
    (mem_normalizer_pull_iff φ (rootU K i) ⟨c, h.setup.cent_le hcC⟩).mp
      (FCHyp.N_le_normalizer_U h i hcN)
  obtain ⟨a, ha, l, hal⟩ := ((h.twoCore.axisAut i).kernel_action α hα).mp
    fun y hy => normAct_ker h i hcC hcN hcs hy
  have hcL := inv_mul_mem_centralizer φ ⟨c, h.setup.cent_le hcC⟩ (φ.symm (a * dHom K i l))
    (by rw [MulEquiv.apply_symm_apply]; exact hal)
  obtain ⟨k, hk⟩ := h.twoCore.mem_zpowers_of_mem hcL
    (mul_mem (inv_mem (h.setup.L_le (φ.symm (a * dHom K i l)).2)) hcC)
  refine ⟨a, ha, l, k, ?_⟩
  have e2 : c = ((φ.symm (a * dHom K i l) : L) : G) * t ^ k := by
    change t ^ k = ((φ.symm (a * dHom K i l) : L) : G)⁻¹ * c at hk
    rw [hk]
    group
  rw [e2, map_mul, coe_mul]

theorem barMap_mem_of (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) {c : ↥(normalizer (𝐗[i] : Set G))} {a : antiSp K} (ha : a ∈ rootA K i) {l : Kˣ}
    {k : ℤ} (hc : (c : G) = ((φ.symm a : L) : G) * ((φ.symm (dHom K i l) : L) : G) * t ^ k) :
    barMap 𝐗[i] c ∈ zpowers (barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩) ⊔
      barSub 𝐗[i] (L.subtype.comp (φ.symm.toMonoidHom.comp (dHom K i))).range := by
  have ha' : ((φ.symm a : L) : G) ∈ 𝐗[i] := A_le_X h i (symm_mem_pull.mpr ha)
  have hdN : ((φ.symm (dHom K i l) : L) : G) ∈ normalizer (𝐗[i] : Set G) :=
    N_le_normalizer_X h hbt i (d_mem_N h i l)
  have hc' : c = (⟨((φ.symm a : L) : G), le_normalizer ha'⟩ : ↥(normalizer (𝐗[i] : Set G))) *
      ⟨((φ.symm (dHom K i l) : L) : G), hdN⟩ * ⟨t, t_mem_normalizer_X h i⟩ ^ k :=
    Subtype.ext (by rw [hc]; rfl)
  have h1 : barMap 𝐗[i] ⟨((φ.symm a : L) : G), le_normalizer ha'⟩ = 1 :=
    barMap_eq_one_iff.mpr ha'
  have e : barMap 𝐗[i] c = barMap 𝐗[i] ⟨((φ.symm (dHom K i l) : L) : G), hdN⟩ *
      barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩ ^ k := by
    rw [hc', map_mul, map_mul, h1, one_mul, map_zpow]
  rw [e]
  exact mul_mem (mem_sup_right ⟨_, mem_subgroupOf.mpr ⟨l, rfl⟩, rfl⟩)
    (zpow_mem (mem_sup_left (mem_zpowers _)) k)

theorem centralizer_K (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) :
    centralizer ({barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩} : Set (BarM 𝐗[i])) ⊓
        centralizer (barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G)) : Set (BarM 𝐗[i])) =
      zpowers (barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩) ⊔
        barSub 𝐗[i] (L.subtype.comp (φ.symm.toMonoidHom.comp (dHom K i))).range := by
  refine centralizer_eq_of (t_mem_normalizer_X h i) (centralizer_tau h hbt i)
    (fun m hm => exists_C0_of_mem_N h i hm) (fun c hc hcK => ?_) (sup_le ?_ ?_)
  · obtain ⟨a, ha, l, k, hck⟩ := exists_eq_of_ker h i hc.1 hc.2
      (comm_s_mem_A h i hc.1 (N_le_normalizer_X h hbt i hc.2) hcK)
    exact barMap_mem_of h hbt i ha hck
  · refine zpowers_le.mpr ⟨mem_centralizer_singleton_iff.mpr rfl, mem_centralizer_iff.mpr
      fun k hk => mem_centralizer_singleton_iff.mp (K_le_centralizer_tau h hbt i hk)⟩
  · refine le_inf ?_ (dbar_le_centralizer_K h i)
    rw [centralizer_tau h hbt i]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨l, hl⟩ := mem_subgroupOf.mp hm
    refine ⟨m, mem_subgroupOf.mpr ?_, rfl⟩
    rw [← hl]
    exact d_mem_N h i l

theorem tau_mul_self (h : FCHyp L K n φ t) (i : Axis) :
    barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩ * barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩ = 1 := by
  rw [← map_mul]
  exact barMap_eq_one_iff.mpr (by rw [coe_mul, h.setup.t_mul_t]; exact one_mem _)

theorem tau_ne_one (h : FCHyp L K n φ t) (i : Axis) : barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩ ≠ 1 :=
  fun e => t_not_mem_X h i (barMap_eq_one_iff.mp e)

theorem dbar_le_centralizer_tau (h : FCHyp L K n φ t)
    (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥) (i : Axis) :
    barSub 𝐗[i] (L.subtype.comp (φ.symm.toMonoidHom.comp (dHom K i))).range ≤
      centralizer ({barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩} : Set (BarM 𝐗[i])) := by
  rw [centralizer_tau h hbt i]
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨l, hl⟩ := mem_subgroupOf.mp hm
  refine ⟨m, mem_subgroupOf.mpr ?_, rfl⟩
  rw [← hl]
  exact d_mem_N h i l

theorem tau_inf_dbar (h : FCHyp L K n φ t) (i : Axis) :
    zpowers (barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩) ⊓ barSub 𝐗[i] (L.subtype.comp
      (φ.symm.toMonoidHom.comp (dHom K i))).range = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨⟨k, hk⟩, hx⟩
  change barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩ ^ k = x at hk
  subst hk
  rcases zpow_eq_one_or_eq (tau_mul_self h i) k with h1 | h1
  · rw [h1]; exact one_mem _
  · exfalso
    rw [h1] at hx
    obtain ⟨m, hm, e⟩ := hx
    obtain ⟨l, hl⟩ := mem_subgroupOf.mp hm
    have h2 := barMap_eq_iff.mp e
    change (m : G)⁻¹ * t ∈ 𝐗[i] at h2
    rw [← hl] at h2
    have h3 : (((φ.symm (dHom K i l) : L) : G))⁻¹ * t ∈ 𝐀[i] :=
      (X_inf_C h i).le (mem_inf.mpr ⟨h2, mul_mem (inv_mem (h.setup.L_le
        (φ.symm (dHom K i l)).2)) (mem_centralizer_singleton_iff.mpr rfl)⟩)
    have h4 := mul_mem (φ.symm (dHom K i l)).2 (pull_le φ _ h3)
    rw [mul_inv_cancel_left] at h4
    exact h.twoCore.t_not_mem h4

theorem orderOf_tau (h : FCHyp L K n φ t) (i : Axis) :
    orderOf (barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (by rw [pow_two]; exact tau_mul_self h i) (tau_ne_one h i)

theorem card_centralizer_K (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) : Nat.card ↥(zpowers (barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩) ⊔
      barSub 𝐗[i] (L.subtype.comp (φ.symm.toMonoidHom.comp (dHom K i))).range) =
        2 * (Nat.card K - 1) := by
  have hcomm : ∀ x ∈ zpowers (barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩), ∀ y ∈ barSub 𝐗[i]
      (L.subtype.comp (φ.symm.toMonoidHom.comp (dHom K i))).range, x * y = y * x := by
    rintro _ ⟨k, rfl⟩ y hy
    exact (Commute.zpow_left (mem_centralizer_singleton_iff.mp
      (dbar_le_centralizer_tau h hbt i hy)).symm k).eq
  rw [card_sup_of_commute hcomm (tau_inf_dbar h i), Nat.card_zpowers, card_dbar h hbt i,
    orderOf_tau h i]

omit [CharP K 2] in
theorem card_SL₂ : Nat.card (SL₂ K) = Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  have := Fintype.ofFinite K
  have hq : 1 < Fintype.card K := Fintype.one_lt_card
  change Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = _
  rw [Matrix.card_SL_field, Fin.prod_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one,
    Nat.card_eq_fintype_card, show Fintype.card K ^ 2 - Fintype.card K =
      Fintype.card K * (Fintype.card K - 1) by rw [Nat.mul_sub_one, sq], ← mul_assoc,
    Nat.mul_div_cancel _ (by omega), mul_comm]

theorem card_K (h : FCHyp L K n φ t) (i : Axis) :
    Nat.card ↥(barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G))) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  obtain ⟨e, -⟩ := equiv_K h i
  rw [← Nat.card_congr e.toEquiv, card_SL₂]

omit [Finite G] [Finite K] in
theorem four_dvd_card (h : FCHyp L K n φ t) : 4 ∣ Nat.card K := by
  rw [h.setup.card_K]
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le h.setup.two_le
  rw [hm, pow_add]
  exact Dvd.dvd.mul_right (by norm_num) _

theorem commutator_K (h : FCHyp L K n φ t) (i : Axis) :
    commutator ↥(barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G))) = ⊤ := by
  obtain ⟨e, -⟩ := equiv_K h i
  have := sl2_isPerfect (K := K) h.four_le_card
  exact (Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective).commutator_eq_top

theorem card_le_two (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) (V : Subgroup (BarM 𝐗[i]))
    (hV : V ≤ centralizer ({barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩} : Set (BarM 𝐗[i])) ⊓
      centralizer (barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G)) : Set (BarM 𝐗[i])))
    (hV2 : IsPGroup 2 V) : Nat.card V ≤ 2 := by
  rw [centralizer_K h hbt i] at hV
  have hd := card_dvd_of_le hV
  rw [card_centralizer_K h hbt i] at hd
  exact card_le_two_of_dvd hV2 (odd_card_sub_one h) hd

theorem standard_K (h : FCHyp L K n φ t) (hbt : ∀ i : Axis, ⁅𝐀[i], 𝐅 ⊓ 𝐃[i.swap]⁆ = ⊥)
    (i : Axis) :
    (∃ V : Sylow 2 ↥(centralizer (barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G)) :
        Set (BarM 𝐗[i]))),
      (V : Subgroup _).map (centralizer (barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G)) :
        Set (BarM 𝐗[i]))).subtype = zpowers (barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩)) ∧
      CFSG.Open.standardComponentIsStandard (barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G))) := by
  have := simple_K h i
  have hτK : barMap 𝐗[i] ⟨t, t_mem_normalizer_X h i⟩ ∈
      centralizer (barSub 𝐗[i] (L ⊓ centralizer (𝐔[i] : Set G)) : Set (BarM 𝐗[i])) :=
    mem_centralizer_iff.mpr fun k hk =>
      mem_centralizer_singleton_iff.mp (K_le_centralizer_tau h hbt i hk)
  refine standard_of hτK (tau_mul_self h i) (tau_ne_one h i) (card_le_two h hbt i)
    (centralizer_tau_le_normalizer h hbt i) (commutator_K h i) ?_
  rw [card_K h i]
  exact Dvd.dvd.mul_right (four_dvd_card h) _

end Elementary

end BothTrivialClosure

end CFSG.LocalAnalysis.SymplecticFourStandard
