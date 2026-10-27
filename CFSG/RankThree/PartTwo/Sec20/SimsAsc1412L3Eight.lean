module

public import CFSG.RankThree.PartTwo.Sec3.ThompsonFamilyG
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Order

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup

section Abstract

open scoped commutatorElement

private theorem le_centralizer_of_stable {X : Type*} [Group X] {M A B : Subgroup X}
    (hM : ⁅M, M⁆ = M) (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hBA : B ≤ A)
    (hMA : ∀ m ∈ M, ∀ a ∈ A, m * a * m⁻¹ ∈ A) (hMB : ∀ m ∈ M, ∀ b ∈ B, m * b * m⁻¹ = b)
    (hst : ∀ m ∈ M, ∀ a ∈ A, m * a * m⁻¹ * a⁻¹ ∈ B) : M ≤ centralizer (A : Set X) := by
  have hkey : ∀ m ∈ M, ∀ m' ∈ M, ∀ a ∈ A,
      m * m' * a * (m * m')⁻¹ = m' * m * a * (m' * m)⁻¹ := by
    intro m hm m' hm' a ha
    obtain ⟨b₁, hb₁def⟩ : ∃ b₁, b₁ = m * a * m⁻¹ * a⁻¹ := ⟨_, rfl⟩
    obtain ⟨b₂, hb₂def⟩ : ∃ b₂, b₂ = m' * a * m'⁻¹ * a⁻¹ := ⟨_, rfl⟩
    have hb₁ : b₁ ∈ B := hb₁def ▸ hst m hm a ha
    have hb₂ : b₂ ∈ B := hb₂def ▸ hst m' hm' a ha
    have h1 : m * a * m⁻¹ = b₁ * a := by rw [hb₁def]; group
    have h2 : m' * a * m'⁻¹ = b₂ * a := by rw [hb₂def]; group
    have hmb₂ : m * b₂ * m⁻¹ = b₂ := hMB m hm b₂ hb₂
    have hm'b₁ : m' * b₁ * m'⁻¹ = b₁ := hMB m' hm' b₁ hb₁
    have hb : b₁ * b₂ = b₂ * b₁ := hA _ (hBA hb₁) _ (hBA hb₂)
    calc m * m' * a * (m * m')⁻¹ = m * (m' * a * m'⁻¹) * m⁻¹ := by group
      _ = m * (b₂ * a) * m⁻¹ := by rw [h2]
      _ = (m * b₂ * m⁻¹) * (m * a * m⁻¹) := by group
      _ = b₂ * (b₁ * a) := by rw [hmb₂, h1]
      _ = (b₂ * b₁) * a := by rw [mul_assoc]
      _ = (b₁ * b₂) * a := by rw [hb]
      _ = b₁ * (b₂ * a) := by rw [mul_assoc]
      _ = (m' * b₁ * m'⁻¹) * (m' * a * m'⁻¹) := by rw [hm'b₁, h2]
      _ = m' * (b₁ * a) * m'⁻¹ := by group
      _ = m' * (m * a * m⁻¹) * m'⁻¹ := by rw [h1]
      _ = m' * m * a * (m' * m)⁻¹ := by group
  have hcomm : ⁅M, M⁆ ≤ centralizer (A : Set X) := by
    rw [Subgroup.commutator_le]
    intro m hm m' hm'
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hmm' : (m' * m)⁻¹ ∈ M := M.inv_mem (M.mul_mem hm' hm)
    have ha'' : (m' * m)⁻¹ * a * ((m' * m)⁻¹)⁻¹ ∈ A := hMA _ hmm' a ha
    have h := hkey m hm m' hm' _ ha''
    have h2 : ⁅m, m'⁆ * a * ⁅m, m'⁆⁻¹ = a := by
      calc ⁅m, m'⁆ * a * ⁅m, m'⁆⁻¹
          = (m * m') * ((m' * m)⁻¹ * a * ((m' * m)⁻¹)⁻¹) * (m * m')⁻¹ := by
            rw [commutatorElement_def]; group
        _ = (m' * m) * ((m' * m)⁻¹ * a * ((m' * m)⁻¹)⁻¹) * (m' * m)⁻¹ := h
        _ = a := by group
    exact (mul_inv_eq_iff_eq_mul.1 h2).symm
  rw [← hM]
  exact hcomm

private theorem pow_four_eq_one_of_card_le_eight {V : Type*} [Group V] [Finite V]
    (hV : Nat.card V ≤ 8) {σ : MulAut V} {n : ℕ} (hσ : σ ^ 2 ^ n = 1) : σ ^ 4 = 1 := by
  classical
  have := Fintype.ofFinite V
  set τ : Equiv.Perm V := MulAut.toPerm V σ with hτ
  have hτn : τ ^ 2 ^ n = 1 := by rw [hτ, ← map_pow, hσ, map_one]
  have hord : orderOf τ ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hτn
  have hsupp : τ.support.card ≤ 7 := by
    have h1 : (1 : V) ∉ τ.support := by
      rw [Equiv.Perm.mem_support, not_not]
      exact map_one σ
    have h2 : τ.support ⊆ Finset.univ.erase 1 := fun x hx =>
      Finset.mem_erase.2 ⟨fun h => h1 (h ▸ hx), Finset.mem_univ x⟩
    calc τ.support.card ≤ (Finset.univ.erase (1 : V)).card := Finset.card_le_card h2
      _ = Fintype.card V - 1 := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      _ ≤ 7 := by rw [← Nat.card_eq_fintype_card]; omega
  have hcyc : ∀ c ∈ τ.cycleType, c ∣ 4 := by
    intro c hc
    have h1 : c ∣ 2 ^ n := (Equiv.Perm.dvd_of_mem_cycleType hc).trans hord
    have h7 : c ≤ 7 := by
      calc c ≤ τ.cycleType.sum := Multiset.le_sum_of_mem hc
        _ = τ.support.card := Equiv.Perm.sum_cycleType τ
        _ ≤ 7 := hsupp
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    have hj : j ≤ 2 := by
      by_contra hj
      have : 2 ^ 3 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact (Nat.pow_dvd_pow 2 hj)
  have h4 : orderOf τ ∣ 4 := by
    rw [← Equiv.Perm.lcm_cycleType]
    exact Multiset.lcm_dvd.2 hcyc
  have h44 : τ ^ 4 = 1 := orderOf_dvd_iff_pow_eq_one.1 h4
  have hinj : Function.Injective (MulAut.toPerm V) := fun a b hab =>
    MulEquiv.ext fun x => congrArg (fun f : Equiv.Perm V => f x) hab
  apply hinj
  rw [map_pow, map_one]
  exact h44

private def trivMod {X : Type*} [Group X] (I U : Subgroup X) [I.Normal] : Subgroup X where
  carrier := {g | g ∈ normalizer (U : Set X) ∧ ∀ x ∈ I, g * x * g⁻¹ * x⁻¹ ∈ U}
  mul_mem' := by
    rintro g g' ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨mul_mem hg hh, fun x hx => ?_⟩
    have h1 : g * g' * x * (g * g')⁻¹ * x⁻¹ =
        (g * (g' * x * g'⁻¹ * x⁻¹) * g⁻¹) * (g * x * g⁻¹ * x⁻¹) := by group
    rw [h1]
    exact U.mul_mem ((Subgroup.mem_normalizer_iff.1 hg _).1 (hh' x hx)) (hg' x hx)
  one_mem' := ⟨one_mem _, fun x _ => by simp⟩
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    refine ⟨inv_mem hg, fun x hx => ?_⟩
    have hx' : g⁻¹ * x * g ∈ I := by
      have := ‹I.Normal›.conj_mem x hx g⁻¹
      rwa [inv_inv] at this
    have h1 : g⁻¹ * x * (g⁻¹)⁻¹ * x⁻¹ =
        (g * (g⁻¹ * x * g) * g⁻¹ * (g⁻¹ * x * g)⁻¹)⁻¹ := by group
    rw [h1]
    exact U.inv_mem (hg' _ hx')

private theorem false_of_section {X : Type*} [Group X] [Finite X] {I U D P L : Subgroup X}
    [I.Normal] [L.Normal] (hI : Sec3.IsElemTwo I) (hUI : U ≤ I) (hU8 : Nat.card U ≤ 8)
    (hD : ∀ d ∈ D, d ∈ normalizer (U : Set X) ∧ ∀ x ∈ I, d * x * d⁻¹ * x⁻¹ ∈ U)
    (hP : P ≤ centralizer (I : Set X)) (hL : ⁅L, L⁆ = L)
    (hLI : ¬ L ≤ centralizer (I : Set X)) (hLD : L ≤ D ⊔ P)
    {y : X} (hy : ∃ n : ℕ, y ^ 2 ^ n = 1)
    (hTR : ∀ C : Subgroup X, C.Normal → y ^ 4 ∈ C → L ≤ C ⊔ P) : False := by
  have hPn : P ≤ normalizer (U : Set X) := by
    rw [Subgroup.le_normalizer_iff]
    intro p hp w hw
    have h1 : w * p = p * w := Subgroup.mem_centralizer_iff.1 (hP hp) w (hUI hw)
    rw [← h1, mul_inv_cancel_right]
    exact hw
  have hLT : L ≤ trivMod I U := by
    refine hLD.trans (sup_le (fun d hd => hD d hd) (fun p hp => ⟨hPn hp, fun x hx => ?_⟩))
    have h1 : x * p = p * x := Subgroup.mem_centralizer_iff.1 (hP hp) x hx
    rw [← h1]
    simp
  have hVU : ⁅L, I⁆ ≤ U := by
    rw [Subgroup.commutator_le]
    intro l hl x hx
    rw [commutatorElement_def]
    exact (hLT hl).2 x hx
  have hVI : ⁅L, I⁆ ≤ I := hVU.trans hUI
  have hV8 : Nat.card ↥(⁅L, I⁆ : Subgroup X) ≤ 8 := (Subgroup.card_le_of_le hVU).trans hU8
  obtain ⟨n, hn⟩ := hy
  have hσn : (MulAut.conjNormal y : MulAut ↥(⁅L, I⁆ : Subgroup X)) ^ 2 ^ n = 1 := by
    rw [← map_pow, hn, map_one]
  have hσ4 := pow_four_eq_one_of_card_le_eight hV8 hσn
  have hy4 : y ^ 4 ∈ (MulAut.conjNormal : X →* MulAut ↥(⁅L, I⁆ : Subgroup X)).ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hσ4
  have hLC := hTR _ inferInstance hy4
  have hCP : (MulAut.conjNormal : X →* MulAut ↥(⁅L, I⁆ : Subgroup X)).ker ⊔ P ≤
      centralizer ((⁅L, I⁆ : Subgroup X) : Set X) := by
    refine sup_le (fun g hg => ?_)
      (hP.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 hVI)))
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have h1 := congrArg (fun f : MulAut ↥(⁅L, I⁆ : Subgroup X) =>
      ((f ⟨v, hv⟩ : ↥(⁅L, I⁆ : Subgroup X)) : X)) (MonoidHom.mem_ker.1 hg)
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h1
    calc v * g = (g * v * g⁻¹) * g := by rw [h1]
      _ = g * v := by group
  have hLV : L ≤ centralizer ((⁅L, I⁆ : Subgroup X) : Set X) := hLC.trans hCP
  apply hLI
  refine le_centralizer_of_stable hL (fun a ha b hb => hI.1 a ha b hb) hVI
    (fun m _ a ha => ‹I.Normal›.conj_mem a ha m) (fun m hm b hb => ?_) (fun m hm a ha => ?_)
  · have h1 : b * m = m * b := Subgroup.mem_centralizer_iff.1 (hLV hm) b hb
    rw [← h1, mul_inv_cancel_right]
  · have h1 := Subgroup.commutator_mem_commutator hm ha
    rwa [commutatorElement_def] at h1

end Abstract

section Transport

open scoped commutatorElement

variable {G : Type} [Group G]

private abbrev img (Y N S : Subgroup G) [(N.subgroupOf Y).Normal] :
    Subgroup (↥Y ⧸ N.subgroupOf Y) :=
  (S.subgroupOf Y).map (QuotientGroup.mk' (N.subgroupOf Y))

variable {Y N : Subgroup G} [(N.subgroupOf Y).Normal]

private theorem mk_mem_img {S : Subgroup G} {g : ↥Y} (hg : (g : G) ∈ S) :
    QuotientGroup.mk' (N.subgroupOf Y) g ∈ img Y N S :=
  ⟨g, hg, rfl⟩

private theorem mk_eq_one_iff (g : ↥Y) :
    QuotientGroup.mk' (N.subgroupOf Y) g = 1 ↔ (g : G) ∈ N := by
  rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
  exact Iff.rfl

private theorem img_normal {S : Subgroup G} (hS : Y ≤ normalizer (S : Set G)) :
    (img Y N S).Normal := by
  haveI : (S.subgroupOf Y).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hS
  exact Subgroup.Normal.map this _ (QuotientGroup.mk'_surjective _)

private theorem img_mono {S S' : Subgroup G} (h : S ≤ S') : img Y N S ≤ img Y N S' :=
  Subgroup.map_mono fun _ hx => h hx

private theorem img_sup {S₁ S₂ S₃ : Subgroup G} (h₁ : S₁ ≤ Y) (h₂ : S₂ ≤ Y)
    (h₃ : S₃ ≤ S₁ ⊔ S₂) : img Y N S₃ ≤ img Y N S₁ ⊔ img Y N S₂ := by
  calc img Y N S₃ ≤ img Y N (S₁ ⊔ S₂) := img_mono h₃
    _ = img Y N S₁ ⊔ img Y N S₂ := by
        rw [img, Subgroup.subgroupOf_sup h₁ h₂, Subgroup.map_sup]

private theorem img_commutator {L : Subgroup G} (hLY : L ≤ Y) (hL : ⁅L, L⁆ = L) :
    ⁅img Y N L, img Y N L⁆ = img Y N L := by
  have h1 : ⁅L.subgroupOf Y, L.subgroupOf Y⁆ = L.subgroupOf Y := by
    apply Subgroup.map_injective Y.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hLY, hL]
  rw [img, ← Subgroup.map_commutator, h1]

private theorem card_img_le [Finite G] {S : Subgroup G} (hS : S ≤ Y) :
    Nat.card (img Y N S) ≤ Nat.card S := by
  have h1 : Nat.card (S.subgroupOf Y) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv
  rw [← h1]
  exact Nat.le_of_dvd Nat.card_pos (Subgroup.card_map_dvd _ _)

end Transport

section Series

open scoped commutatorElement

variable {G : Type} [Group G]

private def wSeries (P W : Subgroup G) : ℕ → Subgroup G
  | 0 => W
  | k + 1 => ⁅wSeries P W k, P⁆

private theorem normalizer_commutator_of_le {Y K₁ K₂ : Subgroup G}
    (h₁ : Y ≤ normalizer (K₁ : Set G)) (h₂ : Y ≤ normalizer (K₂ : Set G)) :
    Y ≤ normalizer ((⁅K₁, K₂⁆ : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro n hn g hg
  have h1 : ⁅K₁, K₂⁆ ≤ (⁅K₁, K₂⁆ : Subgroup G).comap (MulAut.conj n).toMonoidHom := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    show (MulAut.conj n) ⁅a, b⁆ ∈ ⁅K₁, K₂⁆
    rw [map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (Subgroup.le_normalizer_iff.1 h₁ n hn a ha)
      (Subgroup.le_normalizer_iff.1 h₂ n hn b hb)
  exact h1 hg

private theorem wSeries_normalizer {Y P W : Subgroup G} (hPn : Y ≤ normalizer (P : Set G))
    (hWn : Y ≤ normalizer (W : Set G)) : ∀ k, Y ≤ normalizer (wSeries P W k : Set G)
  | 0 => hWn
  | k + 1 => normalizer_commutator_of_le (wSeries_normalizer hPn hWn k) hPn

private theorem wSeries_succ_le {Y P W : Subgroup G} (hPY : P ≤ Y)
    (hPn : Y ≤ normalizer (P : Set G)) (hWn : Y ≤ normalizer (W : Set G)) (k : ℕ) :
    wSeries P W (k + 1) ≤ wSeries P W k :=
  Subgroup.le_normalizer_iff_commutator_le_left.1 (hPY.trans (wSeries_normalizer hPn hWn k))

private theorem wSeries_le {Y P W : Subgroup G} (hPY : P ≤ Y)
    (hPn : Y ≤ normalizer (P : Set G)) (hWn : Y ≤ normalizer (W : Set G)) :
    ∀ k, wSeries P W k ≤ W
  | 0 => le_rfl
  | k + 1 => (wSeries_succ_le hPY hPn hWn k).trans (wSeries_le hPY hPn hWn k)

private theorem wSeries_le_lowerCentralSeries {P W : Subgroup G} (hWP : W ≤ P) :
    ∀ k, wSeries P W k ≤ P.lowerCentralSeries k
  | 0 => hWP
  | k + 1 => Subgroup.commutator_mono_left (wSeries_le_lowerCentralSeries hWP k)

private theorem exists_wSeries_eq_bot [Finite G] {P W : Subgroup G} (hP2 : IsPGroup 2 P)
    (hWP : W ≤ P) : ∃ n, wSeries P W n = ⊥ := by
  obtain ⟨n, hn⟩ := (Subgroup.isNilpotent_iff_lowerCentralSeries P).1 hP2.isNilpotent
  exact ⟨n, le_bot_iff.1 ((wSeries_le_lowerCentralSeries hWP n).trans hn.le)⟩

private theorem exists_section [Finite G] {Y P W L₀ : Subgroup G} (hPY : P ≤ Y)
    (hP2 : IsPGroup 2 P) (hPn : Y ≤ normalizer (P : Set G)) (hWP : W ≤ P)
    (hW : Sec3.IsElemTwo W) (hWn : Y ≤ normalizer (W : Set G)) (hL₀Y : L₀ ≤ Y)
    (hL₀ : ⁅L₀, L₀⁆ = L₀) (hL₀W : ¬ L₀ ≤ centralizer (W : Set G)) :
    ∃ A N : Subgroup G, A ≤ W ∧ N ≤ A ∧ Y ≤ normalizer (A : Set G) ∧
      Y ≤ normalizer (N : Set G) ∧ (∀ a ∈ A, ∀ p ∈ P, a * p * a⁻¹ * p⁻¹ ∈ N) ∧
      ¬ ∀ a ∈ A, ∀ l ∈ L₀, l * a * l⁻¹ * a⁻¹ ∈ N := by
  classical
  obtain ⟨n, hn⟩ := exists_wSeries_eq_bot hP2 hWP
  have hex : ∃ m, L₀ ≤ centralizer (wSeries P W m : Set G) := by
    refine ⟨n, fun l _ => ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [hn, Subgroup.coe_bot, Set.mem_singleton_iff] at hh
    subst hh
    simp
  have hmspec : L₀ ≤ centralizer (wSeries P W (Nat.find hex) : Set G) := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hL₀W
    rw [h0] at hmspec
    exact hmspec
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hnk : ¬ L₀ ≤ centralizer (wSeries P W k : Set G) :=
    Nat.find_min hex (by omega)
  rw [hk] at hmspec
  have hle : wSeries P W k ≤ W := wSeries_le hPY hPn hWn k
  refine ⟨wSeries P W k, wSeries P W (k + 1), hle, wSeries_succ_le hPY hPn hWn k,
    wSeries_normalizer hPn hWn k, wSeries_normalizer hPn hWn (k + 1), ?_, ?_⟩
  · intro a ha p hp
    have h1 := Subgroup.commutator_mem_commutator ha hp
    rwa [commutatorElement_def] at h1
  · intro h
    apply hnk
    refine le_centralizer_of_stable hL₀ (fun a ha b hb => hW.1 a (hle ha) b (hle hb))
      (wSeries_succ_le hPY hPn hWn k)
      (fun m hm a ha =>
        Subgroup.le_normalizer_iff.1 (wSeries_normalizer hPn hWn k) m (hL₀Y hm) a ha)
      (fun m hm b hb => ?_) (fun m hm a ha => h a ha m hm)
    have h1 : b * m = m * b := Subgroup.mem_centralizer_iff.1 (hmspec hm) b hb
    rw [← h1, mul_inv_cancel_right]

end Series

section Reduction

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem false_of_section_reduction {Y P W L₀ A N : Subgroup G} (hPY : P ≤ Y)
    (hWP : W ≤ P) (hW : Sec3.IsElemTwo W) (hL₀Y : L₀ ≤ Y) (hL₀ : ⁅L₀, L₀⁆ = L₀)
    (hL₀n : Y ≤ normalizer (L₀ : Set G)) {u : Fin 3 → G} (hu : ∀ i, u i ∈ Y)
    (hu2 : ∀ i, (centralizer ({u i} : Set G)).relIndex W ≤ 2)
    (hL₀D : L₀ ≤ closure (Set.range u) ⊔ P) {y₀ : G} (hy₀ : y₀ ∈ Y)
    (hy₀2 : ∃ n : ℕ, y₀ ^ 2 ^ n = 1)
    (hTR : ∀ C : Subgroup G, C ≤ Y → Y ≤ normalizer (C : Set G) → y₀ ^ 4 ∈ C → L₀ ≤ C ⊔ P)
    (hAW : A ≤ W) (hNA : N ≤ A) (hAn : Y ≤ normalizer (A : Set G))
    (hNn : Y ≤ normalizer (N : Set G)) (hAPN : ∀ a ∈ A, ∀ p ∈ P, a * p * a⁻¹ * p⁻¹ ∈ N)
    (hnst : ¬ ∀ a ∈ A, ∀ l ∈ L₀, l * a * l⁻¹ * a⁻¹ ∈ N) : False := by
  have hAY : A ≤ Y := hAW.trans (hWP.trans hPY)
  have hAI : Sec3.IsElemTwo A :=
    ⟨fun a ha b hb => hW.1 a (hAW ha) b (hAW hb), fun a ha => hW.2 a (hAW ha)⟩
  have hDY : closure (Set.range u) ≤ Y :=
    (Subgroup.closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact hu i)
  obtain ⟨U, hUA, hUcard, hUD⟩ := exists_subgroup_normalized_closure hAI u
    (fun i => hAn (hu i)) (fun _ => 2) (fun i =>
      (Subgroup.relIndex_le_of_le_right hAW Subgroup.index_ne_zero_of_finite).trans (hu2 i))
  have hU8 : Nat.card U ≤ 8 := by simpa using hUcard
  have hUY : U ≤ Y := hUA.trans hAY
  haveI hNN : (N.subgroupOf Y).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hNn
  haveI : (img Y N A).Normal := img_normal hAn
  haveI : (img Y N L₀).Normal := img_normal hL₀n
  have hI : Sec3.IsElemTwo (img Y N A) := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hAI.1 _ ha _ hb)
    · rintro _ ⟨a, ha, rfl⟩
      rw [← map_mul]
      have : a * a = 1 := Subtype.ext (hAI.2 _ ha)
      rw [this, map_one]
  have hD1 : ∀ d ∈ img Y N (closure (Set.range u)), ∀ w ∈ img Y N U,
      d * w * d⁻¹ ∈ img Y N U := by
    rintro _ ⟨d, hd, rfl⟩ _ ⟨w, hw, rfl⟩
    rw [← map_inv, ← map_mul, ← map_mul]
    exact mk_mem_img ((Subgroup.mem_normalizer_iff.1 (hUD _ hd).2.1 _).1 hw)
  have hD : ∀ d ∈ img Y N (closure (Set.range u)),
      d ∈ normalizer ((img Y N U : Subgroup _) : Set _) ∧
        ∀ x ∈ img Y N A, d * x * d⁻¹ * x⁻¹ ∈ img Y N U := by
    intro d hd
    refine ⟨Subgroup.le_normalizer_iff.2 hD1 hd, ?_⟩
    obtain ⟨d', hd', rfl⟩ := hd
    rintro _ ⟨x, hx, rfl⟩
    have h1 : QuotientGroup.mk' (N.subgroupOf Y) d' * QuotientGroup.mk' (N.subgroupOf Y) x *
        (QuotientGroup.mk' (N.subgroupOf Y) d')⁻¹ * (QuotientGroup.mk' (N.subgroupOf Y) x)⁻¹ =
        QuotientGroup.mk' (N.subgroupOf Y) (d' * x * d'⁻¹ * x⁻¹) := by
      simp only [map_mul, map_inv]
    rw [h1]
    exact mk_mem_img ((hUD _ hd').2.2 _ hx)
  have hP : img Y N P ≤ centralizer ((img Y N A : Subgroup _) : Set _) := by
    rintro _ ⟨p, hp, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    have h1 := (mk_eq_one_iff (N := N) (a * p * a⁻¹ * p⁻¹)).2 (hAPN _ ha _ hp)
    simp only [map_mul, map_inv] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 (by rw [commutatorElement_def]; exact h1)
  have hLI : ¬ img Y N L₀ ≤ centralizer ((img Y N A : Subgroup _) : Set _) := by
    intro hle
    apply hnst
    intro a ha l hl
    have h1 := Subgroup.mem_centralizer_iff.1 (hle (mk_mem_img (S := L₀) (g := ⟨l, hL₀Y hl⟩) hl))
      _ (mk_mem_img (S := A) (g := ⟨a, hAY ha⟩) ha)
    have h2 : QuotientGroup.mk' (N.subgroupOf Y) (⟨l, hL₀Y hl⟩ * ⟨a, hAY ha⟩ * ⟨l, hL₀Y hl⟩⁻¹ *
        ⟨a, hAY ha⟩⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [← h1]
      group
    exact (mk_eq_one_iff _).1 h2
  have hy : ∃ n : ℕ, (QuotientGroup.mk' (N.subgroupOf Y) ⟨y₀, hy₀⟩) ^ 2 ^ n = 1 := by
    obtain ⟨n, hn⟩ := hy₀2
    refine ⟨n, ?_⟩
    rw [← map_pow]
    have : (⟨y₀, hy₀⟩ : ↥Y) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hn)
    rw [this, map_one]
  have hTR' : ∀ C : Subgroup (↥Y ⧸ N.subgroupOf Y), C.Normal →
      (QuotientGroup.mk' (N.subgroupOf Y) ⟨y₀, hy₀⟩) ^ 4 ∈ C → img Y N L₀ ≤ C ⊔ img Y N P := by
    intro C hC hy4
    have hCY : (C.comap (QuotientGroup.mk' (N.subgroupOf Y))).map Y.subtype ≤ Y := by
      rintro _ ⟨s, -, rfl⟩
      exact s.2
    have hCn : Y ≤ normalizer (((C.comap (QuotientGroup.mk' (N.subgroupOf Y))).map Y.subtype :
        Subgroup G) : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      rintro g hg _ ⟨s, hs, rfl⟩
      refine ⟨⟨g, hg⟩ * s * ⟨g, hg⟩⁻¹, ?_, rfl⟩
      show QuotientGroup.mk' (N.subgroupOf Y) (⟨g, hg⟩ * s * ⟨g, hg⟩⁻¹) ∈ C
      rw [map_mul, map_mul, map_inv]
      exact hC.conj_mem _ hs _
    have hy4' : y₀ ^ 4 ∈ (C.comap (QuotientGroup.mk' (N.subgroupOf Y))).map Y.subtype :=
      ⟨⟨y₀, hy₀⟩ ^ 4, by
        show QuotientGroup.mk' (N.subgroupOf Y) (⟨y₀, hy₀⟩ ^ 4) ∈ C
        rw [map_pow]
        exact hy4, by simp⟩
    have h := hTR _ hCY hCn hy4'
    have h2 : img Y N ((C.comap (QuotientGroup.mk' (N.subgroupOf Y))).map Y.subtype) ≤ C := by
      rintro _ ⟨x, ⟨s, hs, hsx⟩, rfl⟩
      have : s = x := Subtype.ext hsx
      rw [← this]
      exact hs
    exact (img_sup hCY hPY h).trans (sup_le_sup_right h2 _)
  exact false_of_section (I := img Y N A) (U := img Y N U) (D := img Y N (closure (Set.range u)))
    (P := img Y N P) (L := img Y N L₀) hI (img_mono hUA) ((card_img_le hUY).trans hU8) hD hP
    (img_commutator hL₀Y hL₀) hLI (img_sup hDY hPY hL₀D) hy hTR'

end Reduction

theorem false_of_case_eight1412 {G : Type} [Group G] [Finite G] {Y P W L₀ : Subgroup G}
    (hPY : P ≤ Y) (hP2 : IsPGroup 2 P) (hPn : Y ≤ normalizer (P : Set G))
    (hWP : W ≤ P) (hW : Sec3.IsElemTwo W) (hWn : Y ≤ normalizer (W : Set G))
    (hL₀Y : L₀ ≤ Y) (hL₀ : ⁅L₀, L₀⁆ = L₀) (hL₀n : Y ≤ normalizer (L₀ : Set G))
    (hL₀W : ¬ L₀ ≤ centralizer (W : Set G))
    {u : Fin 3 → G} (hu : ∀ i, u i ∈ Y)
    (hu2 : ∀ i, (centralizer ({u i} : Set G)).relIndex W ≤ 2)
    (hL₀D : L₀ ≤ closure (Set.range u) ⊔ P)
    {y₀ : G} (hy₀ : y₀ ∈ Y) (hy₀2 : ∃ n : ℕ, y₀ ^ 2 ^ n = 1)
    (hTR : ∀ C : Subgroup G, C ≤ Y → Y ≤ normalizer (C : Set G) → y₀ ^ 4 ∈ C →
      L₀ ≤ C ⊔ P) :
    False := by
  obtain ⟨A, N, hAW, hNA, hAn, hNn, hAPN, hnst⟩ :=
    exists_section hPY hP2 hPn hWP hW hWn hL₀Y hL₀ hL₀W
  exact false_of_section_reduction hPY hWP hW hL₀Y hL₀ hL₀n hu hu2 hL₀D hy₀ hy₀2 hTR hAW hNA hAn
    hNn hAPN hnst

end CFSG.RankThree.PartTwo.Sec20
