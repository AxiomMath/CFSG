module

public import CFSG.RankThree.PartTwo.Sec11.Item1121ProofWreath
public import CFSG.RankThree.PartTwo.Sec11.LaterSteps
public import CFSG.RankThree.PartTwo.Sec11.Steps
public import CFSG.RankThree.PartTwo.Sec11.Item1119ProofBasic
import CFSG.RankThree.PartTwo.Sec11.Item1119Proof
import CFSG.RankThree.PartTwo.Sec11.Item1116NoFifteen
import CFSG.RankThree.PartTwo.Sec11.Item1123Proof
import CFSG.RankThree.PartTwo.Sec11.Item1125Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Item1121Proof

section Image

variable {G : Type*} [Group G] {P : Subgroup G} (π : P →* W33)

noncomputable def piG (y : G) : W33 := by
  classical
  exact if hy : y ∈ P then π ⟨y, hy⟩ else 1

theorem piG_of_mem {y : G} (hy : y ∈ P) : piG π y = π ⟨y, hy⟩ := by
  classical
  simp [piG, hy]

theorem piG_mul {y z : G} (hy : y ∈ P) (hz : z ∈ P) : piG π (y * z) = piG π y * piG π z := by
  rw [piG_of_mem π (P.mul_mem hy hz), piG_of_mem π hy, piG_of_mem π hz, ← map_mul]
  rfl

theorem piG_inv {y : G} (hy : y ∈ P) : piG π y⁻¹ = (piG π y)⁻¹ := by
  rw [piG_of_mem π (P.inv_mem hy), piG_of_mem π hy, ← map_inv]
  rfl

theorem piG_one : piG π (1 : G) = 1 := by
  rw [piG_of_mem π P.one_mem]
  exact map_one π

theorem piG_pow {y : G} (hy : y ∈ P) (n : ℕ) : piG π (y ^ n) = piG π y ^ n := by
  rw [piG_of_mem π (P.pow_mem hy n), piG_of_mem π hy, ← map_pow]
  rfl

theorem piG_zpow {y : G} (hy : y ∈ P) (n : ℤ) : piG π (y ^ n) = piG π y ^ n := by
  rw [piG_of_mem π (P.zpow_mem hy n), piG_of_mem π hy, ← map_zpow]
  rfl

theorem piG_commutator {y z : G} (hy : y ∈ P) (hz : z ∈ P) :
    piG π (y * z * y⁻¹ * z⁻¹) = piG π y * piG π z * (piG π y)⁻¹ * (piG π z)⁻¹ := by
  rw [piG_mul π (P.mul_mem (P.mul_mem hy hz) (P.inv_mem hy)) (P.inv_mem hz),
    piG_mul π (P.mul_mem hy hz) (P.inv_mem hy), piG_mul π hy hz, piG_inv π hy, piG_inv π hz]

theorem piG_conj {y z : G} (hy : y ∈ P) (hz : z ∈ P) :
    piG π (y * z * y⁻¹) = piG π y * piG π z * (piG π y)⁻¹ := by
  rw [piG_mul π (P.mul_mem hy hz) (P.inv_mem hy), piG_mul π hy hz, piG_inv π hy]

theorem piG_comm_of_commutator {y z : G} (hy : y ∈ P) (hz : z ∈ P)
    (h : piG π (y * z * y⁻¹ * z⁻¹) = 1) : piG π y * piG π z = piG π z * piG π y := by
  rw [piG_commutator π hy hz] at h
  calc piG π y * piG π z = (piG π y * piG π z * (piG π y)⁻¹ * (piG π z)⁻¹) *
        (piG π z * piG π y) := by group
    _ = piG π z * piG π y := by rw [h, one_mul]

theorem piG_mem_of_mem_closure {T : Set G} (hT : Subgroup.closure T ≤ P) {H : Subgroup W33}
    (hH : ∀ t ∈ T, piG π t ∈ H) {y : G} (hy : y ∈ Subgroup.closure T) : piG π y ∈ H := by
  induction hy using Subgroup.closure_induction with
  | mem t ht => exact hH t ht
  | one => rw [piG_one]; exact H.one_mem
  | mul y z hy hz ihy ihz => rw [piG_mul π (hT hy) (hT hz)]; exact H.mul_mem ihy ihz
  | inv y hy ihy => rw [piG_inv π (hT hy)]; exact H.inv_mem ihy

theorem piG_mem_zpowers {y z : G} (hz : z ∈ P) (hy : y ∈ Subgroup.zpowers z) :
    piG π y ∈ Subgroup.zpowers (piG π z) := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  rw [piG_zpow π hz]
  exact Subgroup.zpow_mem_zpowers _ k

noncomputable def mapP (S : Subgroup G) : Subgroup W33 := (S.subgroupOf P).map π

theorem piG_mem_mapP {S : Subgroup G} (hSP : S ≤ P) {y : G} (hy : y ∈ S) :
    piG π y ∈ mapP π S := by
  rw [piG_of_mem π (hSP hy)]
  exact ⟨⟨y, hSP hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩

theorem exists_of_mem_mapP {S : Subgroup G} {w : W33} (hw : w ∈ mapP π S) :
    ∃ y ∈ S, piG π y = w := by
  obtain ⟨⟨y, hyP⟩, hy, rfl⟩ := hw
  exact ⟨y, Subgroup.mem_subgroupOf.mp hy, piG_of_mem π hyP⟩

theorem mapP_closure_le {T : Set G} (hT : Subgroup.closure T ≤ P) {H : Subgroup W33}
    (hH : ∀ t ∈ T, piG π t ∈ H) : mapP π (Subgroup.closure T) ≤ H := by
  intro w hw
  obtain ⟨y, hy, rfl⟩ := exists_of_mem_mapP π hw
  exact piG_mem_of_mem_closure π hT hH hy

theorem mapP_normal {S : Subgroup G} (hSP : S ≤ P) (hPS : P ≤ Subgroup.normalizer (S : Set G))
    (hπ : Function.Surjective π) : (mapP π S).Normal :=
  ((Subgroup.normal_subgroupOf_iff_le_normalizer hSP).mpr hPS).map π hπ

noncomputable def preU (M : Subgroup W33) : Subgroup G := (M.comap π).map P.subtype

theorem mem_preU {M : Subgroup W33} {y : G} : y ∈ preU π M ↔ y ∈ P ∧ piG π y ∈ M := by
  constructor
  · rintro ⟨⟨y, hy⟩, hyM, rfl⟩
    refine ⟨hy, ?_⟩
    show piG π y ∈ M
    rw [piG_of_mem π hy]
    exact hyM
  · rintro ⟨hy, hyM⟩
    exact ⟨⟨y, hy⟩, by rw [piG_of_mem π hy] at hyM; exact hyM, rfl⟩

theorem conj_mem_preU {M : Subgroup W33} (hM : M.Normal) {y u : G} (hy : y ∈ P)
    (hu : u ∈ preU π M) : y * u * y⁻¹ ∈ preU π M := by
  obtain ⟨huP, huM⟩ := (mem_preU π).mp hu
  refine (mem_preU π).mpr ⟨P.mul_mem (P.mul_mem hy huP) (P.inv_mem hy), ?_⟩
  rw [piG_conj π hy huP]
  exact hM.conj_mem _ huM _

theorem commutator_mem_preU {M : Subgroup W33} (hM : ⁅(⊤ : Subgroup W33), ⊤⁆ ≤ M) {y z : G}
    (hy : y ∈ P) (hz : z ∈ P) : y * z * y⁻¹ * z⁻¹ ∈ preU π M := by
  refine (mem_preU π).mpr ⟨P.mul_mem (P.mul_mem (P.mul_mem hy hz) (P.inv_mem hy))
    (P.inv_mem hz), ?_⟩
  rw [piG_commutator π hy hz]
  exact hM (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))

theorem normal_of_commutator_le {M : Subgroup W33} (hM : ⁅(⊤ : Subgroup W33), ⊤⁆ ≤ M) :
    M.Normal := by
  refine ⟨fun m hm n => ?_⟩
  have e : n * m * n⁻¹ = ⁅n, m⁆ * m := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact M.mul_mem (hM (Subgroup.commutator_mem_commutator (Subgroup.mem_top _)
    (Subgroup.mem_top _))) hm

end Image

theorem mul_comm_of_mem_closure {W : Type*} [Group W] {T : Set W}
    (hT : ∀ u ∈ T, ∀ v ∈ T, u * v = v * u) {u v : W} (hu : u ∈ Subgroup.closure T)
    (hv : v ∈ Subgroup.closure T) : u * v = v * u := by
  have hc : IsMulCommutative (Subgroup.closure T) :=
    Subgroup.isMulCommutative_closure (fun a ha b hb _ => hT a ha b hb)
  exact congrArg Subtype.val (hc.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)

theorem mul_comm_of_mem_closure_triple {W : Type*} [Group W] {u v w : W} (huv : u * v = v * u)
    (huw : u * w = w * u) (hvw : v * w = w * v) {y z : W}
    (hy : y ∈ Subgroup.closure ({u, v, w} : Set W))
    (hz : z ∈ Subgroup.closure ({u, v, w} : Set W)) :
    y * z = z * y := by
  refine mul_comm_of_mem_closure ?_ hy hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  rintro p (rfl | rfl | rfl) q (rfl | rfl | rfl)
  · rfl
  · exact huv
  · exact huw
  · exact huv.symm
  · rfl
  · exact hvw
  · exact huw.symm
  · exact hvw.symm
  · rfl

theorem mem_zpowers_pow_nine {G : Type*} [Group G] {x y : G} (hy3 : y ^ 3 = 1)
    (hyx : y ∈ Subgroup.zpowers x) (h27 : 27 ∣ orderOf x) : y ∈ Subgroup.zpowers (x ^ 9) := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyx
  have h1 : x ^ (m * 3) = 1 := by
    rw [zpow_mul]
    exact_mod_cast hy3
  have h2 : ((27 : ℕ) : ℤ) ∣ m * 3 :=
    (Int.natCast_dvd_natCast.mpr h27).trans (orderOf_dvd_iff_zpow_eq_one.mpr h1)
  obtain ⟨t, ht⟩ : (9 : ℤ) ∣ m := by omega
  refine Subgroup.mem_zpowers_iff.mpr ⟨t, ?_⟩
  rw [ht, ← zpow_natCast, ← zpow_mul]
  push_cast
  rfl

theorem exists_fin_three_zpow (γ : W33) (hγ : γ ^ 3 = 1) (k : ℤ) :
    ∃ i : Fin 3, γ ^ k = γ ^ (i : ℕ) := by
  have hγ' : γ ^ (3 : ℤ) = 1 := by exact_mod_cast hγ
  have h0 : 0 ≤ k % 3 := Int.emod_nonneg _ (by norm_num)
  refine ⟨⟨(k % 3).toNat, by omega⟩, ?_⟩
  rw [zpow_eq_zpow_emod k hγ', Fin.val_mk, ← zpow_natCast, Int.toNat_of_nonneg h0]

theorem right_zpow_eq_one {w : W33} (hw : w.right = 1) (k : ℤ) : (w ^ k).right = 1 := by
  have h1 : w ∈ (RegularWreathProduct.rightHom : W33 →* _).ker := MonoidHom.mem_ker.mpr hw
  exact MonoidHom.mem_ker.mp (Subgroup.zpow_mem _ h1 k)

section Data

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R Y : Subgroup G} {d x s r g : G}

theorem mem_P_facts (h : Sec11Data G A c L a R Y d x s r g) :
    r ∈ sec11P R g ∧ x ∈ sec11P R g ∧ s ∈ sec11P R g ∧ a ∈ sec11P R g ∧ c ∈ sec11P R g ∧
      d ∈ sec11P R g := by
  obtain ⟨hrR, hxR, hsR⟩ := Item1116Proof.mem_R h
  have hAR := Item1115Proof.A_le_R h.toHyp91
  exact ⟨Item1119Proof.R_le_P R g hrR, Item1119Proof.R_le_P R g hxR,
    Item1119Proof.R_le_P R g hsR, Item1119Proof.R_le_P R g (hAR h.a_mem),
    Item1119Proof.R_le_P R g (hAR h.mem_A),
    Item1119Proof.R_le_P R g (hAR (Item1115Proof.d_mem h).1)⟩

theorem d_mem_zpowers_pow_nine (h : Sec11Data G A c L a R Y d x s r g) (hx9 : 9 < orderOf x) :
    d ∈ Subgroup.zpowers (x ^ 9) := by
  have hx := Item1116Proof.exists_pow_eq_one_of_mem h (Item1116Proof.mem_R h).2.1
  have h27 : 27 ∣ orderOf x := by
    have := Item1125Proof.three_pow_succ_dvd_orderOf hx (m := 2) (by simpa using hx9)
    simpa using this
  exact mem_zpowers_pow_nine (Item1115Proof.d_mem h).2.2 (Item1115Proof.d_mem_zpowers_x h) h27

theorem piG_eq_one_of_mem_zpowers_d (h : Sec11Data G A c L a R Y d x s r g)
    (hx9 : 9 < orderOf x) (π : sec11P R g →* W33) {y : G} (hy : y ∈ Subgroup.zpowers d) :
    piG π y = 1 := by
  obtain ⟨-, hxP, -, -, -, hdP⟩ := mem_P_facts h
  have h1 := piG_mem_zpowers π (Subgroup.pow_mem _ hxP 9) (d_mem_zpowers_pow_nine h hx9)
  rw [piG_pow π hxP, pow_nine_eq_one, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h1
  have h2 := piG_mem_zpowers π hdP hy
  rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h2
  exact h2

theorem piG_cube_s_x (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π) :
    piG π s ^ 3 = 1 ∧ piG π x ^ 3 = 1 ∧ piG π a ^ 3 = 1 := by
  have h := hbig.toSec11Data
  obtain ⟨-, hxP, hsP, haP, -, -⟩ := mem_P_facts h
  set V := Subgroup.closure ({s, x, a} : Set G) with hV
  have hVP : V ≤ sec11P R g := by
    rw [hV, Subgroup.closure_le]
    rintro y (rfl | rfl | rfl)
    exacts [hsP, hxP, haP]
  have hPV : sec11P R g ≤ Subgroup.normalizer (V : Set G) := h1120 G A c L a R Y d x s r g hbig
  have hN := mapP_normal π hVP hPV hπ
  have hsx : piG π s * piG π x = piG π x * piG π s := by
    rw [← piG_mul π hsP hxP, ← piG_mul π hxP hsP, h.commute_s_x]
  have hxa : piG π x * piG π a = piG π a * piG π x :=
    piG_comm_of_commutator π hxP haP (piG_eq_one_of_mem_zpowers_d h hbig.orderOf_x_gt π
      (Item1119Proof.commutator_x_a_facts h45 h).1)
  have hsa : piG π s * piG π a = piG π a * piG π s := by
    rw [← piG_mul π hsP haP, ← piG_mul π haP hsP, h1115 G A c L a R Y d x s r g h]
  have hle : mapP π V ≤ Subgroup.closure {piG π s, piG π x, piG π a} :=
    mapP_closure_le π hVP (by
      rintro t (rfl | rfl | rfl) <;> exact Subgroup.subset_closure (by simp))
  have hab : ∀ u ∈ mapP π V, ∀ v ∈ mapP π V, u * v = v * u := fun u hu v hv =>
    mul_comm_of_mem_closure_triple hsx hsa hxa (hle hu) (hle hv)
  have h3 := pow_three_eq_one_of_abelian_normal hN hab
  exact ⟨h3 _ (piG_mem_mapP π hVP (Subgroup.subset_closure (by simp))),
    h3 _ (piG_mem_mapP π hVP (Subgroup.subset_closure (by simp))),
    h3 _ (piG_mem_mapP π hVP (Subgroup.subset_closure (by simp)))⟩

theorem mul_comm_of_mem_mapR (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π) : ∀ u ∈ mapP π R, ∀ v ∈ mapP π R, u * v = v * u := by
  have h := hbig.toSec11Data
  obtain ⟨hrP, hxP, hsP, -, -, -⟩ := mem_P_facts h
  obtain ⟨hrR, hxR, hsR⟩ := Item1116Proof.mem_R h
  obtain ⟨hs3, hx3, -⟩ := piG_cube_s_x h45 h1115 h1120 hbig π hπ
  have hRP : R ≤ sec11P R g := Item1119Proof.R_le_P R g
  have hr := Item1116Proof.exists_pow_eq_one_of_mem h hrR
  have hx := Item1116Proof.exists_pow_eq_one_of_mem h hxR
  have hs := Item1116Proof.exists_pow_eq_one_of_mem h hsR
  have key : ∀ y ∈ sec11P R g, piG π y ^ 3 = 1 → ∀ z ∈ Subgroup.zpowers (y ^ 3),
      piG π z = 1 := by
    intro y hy hy3 z hz
    have h1 := piG_mem_zpowers π (Subgroup.pow_mem _ hy 3) hz
    rw [piG_pow π hy, hy3, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h1
    exact h1
  have hrx : piG π r * piG π x = piG π x * piG π r :=
    piG_comm_of_commutator π hrP hxP (key x hxP hx3 _
      (Item1119Proof.conj_mul_inv_mem_zpowers_pow_three hx hr
        (Item1115Proof.mem_normalizer_zpowers_x h45 h hrR)))
  have hrs : piG π r * piG π s = piG π s * piG π r :=
    piG_comm_of_commutator π hrP hsP (key s hsP hs3 _
      (Item1119Proof.conj_mul_inv_mem_zpowers_pow_three hs hr
        (Item1115Proof.mem_normalizer_zpowers_s h45 h hrR)))
  have hxs : piG π x * piG π s = piG π s * piG π x := by
    rw [← piG_mul π hxP hsP, ← piG_mul π hsP hxP, h.commute_s_x]
  have hRc : Subgroup.closure ({r, x, s} : Set G) ≤ sec11P R g := h.R_eq ▸ hRP
  have hle : mapP π R ≤ Subgroup.closure {piG π r, piG π x, piG π s} := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_mapP π hw
    rw [h.R_eq] at hy
    exact piG_mem_of_mem_closure π hRc (by
      rintro t (rfl | rfl | rfl) <;> exact Subgroup.subset_closure (by simp)) hy
  intro u hu v hv
  exact mul_comm_of_mem_closure_triple hrx hrs hxs (hle hu) (hle hv)

theorem exists_mul_zpow_of_mem_P (h : Sec11Data G A c L a R Y d x s r g) {y : G}
    (hy : y ∈ sec11P R g) : ∃ u ∈ R, ∃ k : ℤ, y = u * g ^ k := by
  have hle : Subgroup.zpowers g ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.zpowers_le.mpr h.g_mem_normalizer
  have hy' : y ∈ ((R ⊔ Subgroup.zpowers g : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hle] at hy'
  obtain ⟨u, hu, w, hw, rfl⟩ := Set.mem_mul.mp hy'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ⟨u, hu, k, rfl⟩

theorem g_pow_three (hbig : Sec11Big G A c L a R Y d x s r g) : g ^ 3 = 1 :=
  hbig.orderOf_g ▸ pow_orderOf_eq_one g

theorem piG_g_pow_three (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33) :
    piG π g ^ 3 = 1 := by
  rw [← piG_pow π (Item1119Proof.g_mem_P R g), g_pow_three hbig, piG_one]

theorem card_W_le_mapR (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π) : 81 ≤ 3 * Nat.card (mapP π R) := by
  have h := hbig.toSec11Data
  have hRP : R ≤ sec11P R g := Item1119Proof.R_le_P R g
  have hgP := Item1119Proof.g_mem_P R g
  let f : mapP π R × Fin 3 → W33 := fun p => (p.1 : W33) * piG π g ^ (p.2 : ℕ)
  have hf : Function.Surjective f := by
    intro w
    obtain ⟨⟨y, hy⟩, rfl⟩ := hπ w
    obtain ⟨u, hu, k, rfl⟩ := exists_mul_zpow_of_mem_P h hy
    obtain ⟨i, hi⟩ := exists_fin_three_zpow (piG π g) (piG_g_pow_three hbig π) k
    refine ⟨(⟨piG π u, piG_mem_mapP π hRP hu⟩, i), ?_⟩
    simp only [f]
    rw [← hi, ← piG_zpow π hgP, ← piG_mul π (hRP hu) (Subgroup.zpow_mem _ hgP k),
      piG_of_mem π]
  have h1 := Nat.card_le_card_of_surjective f hf
  rw [card_wreath, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h1
  omega

theorem right_eq_one_of_mem_mapR (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π) : ∀ w ∈ mapP π R, w.right = 1 :=
  right_eq_one_of_abelian_of_card (mul_comm_of_mem_mapR h45 h1115 h1120 hbig π hπ)
    (by have := card_W_le_mapR hbig π hπ; omega)

theorem right_piG_g_ne_one (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π) : (piG π g).right ≠ 1 := by
  intro hg1
  have h := hbig.toSec11Data
  have hRP : R ≤ sec11P R g := Item1119Proof.R_le_P R g
  have hgP := Item1119Proof.g_mem_P R g
  obtain ⟨⟨y, hy⟩, hyw⟩ := hπ (⟨1, wreathT⟩ : W33)
  obtain ⟨u, hu, k, rfl⟩ := exists_mul_zpow_of_mem_P h hy
  have h1 : (π ⟨u * g ^ k, hy⟩).right = wreathT := by rw [hyw]
  rw [← piG_of_mem π hy, piG_mul π (hRP hu) (Subgroup.zpow_mem _ hgP k), piG_zpow π hgP,
    right_mul, right_eq_one_of_mem_mapR h45 h1115 h1120 hbig π hπ _ (piG_mem_mapP π hRP hu),
    one_mul] at h1
  rw [right_zpow_eq_one hg1 k] at h1
  exact absurd h1.symm (by decide)

theorem orderOf_right_piG_g (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π) : orderOf (piG π g).right = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (pow_three_zmod _) (right_piG_g_ne_one h45 h1115 h1120 hbig π hπ)

theorem mem_R_of_right_eq_one (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π) {y : G} (hy : y ∈ sec11P R g) (hy1 : (piG π y).right = 1) :
    y ∈ R := by
  have h := hbig.toSec11Data
  have hRP : R ≤ sec11P R g := Item1119Proof.R_le_P R g
  have hgP := Item1119Proof.g_mem_P R g
  obtain ⟨u, hu, k, rfl⟩ := exists_mul_zpow_of_mem_P h hy
  rw [piG_mul π (hRP hu) (Subgroup.zpow_mem _ hgP k), piG_zpow π hgP, right_mul,
    right_eq_one_of_mem_mapR h45 h1115 h1120 hbig π hπ _ (piG_mem_mapP π hRP hu), one_mul] at hy1
  have h2 : (piG π g ^ k).right = (piG π g).right ^ k := map_zpow RegularWreathProduct.rightHom _ k
  rw [h2] at hy1
  have h3 : ((3 : ℕ) : ℤ) ∣ k := by
    rw [← orderOf_right_piG_g h45 h1115 h1120 hbig π hπ]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hy1
  obtain ⟨t, rfl⟩ := h3
  rw [zpow_mul, zpow_natCast, g_pow_three hbig, one_zpow, mul_one]
  exact hu

theorem pow_three_mem_R (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π) {y : G} (hy : y ∈ sec11P R g) : y ^ 3 ∈ R :=
  mem_R_of_right_eq_one h45 h1115 h1120 hbig π hπ (Subgroup.pow_mem _ hy 3)
    (by rw [piG_pow π hy]; exact right_pow_three _)

theorem false_of_closure_eq (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π)
    (hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}) : False := by
  have h := hbig.toSec11Data
  obtain ⟨-, hxP, hsP, haP, -, -⟩ := mem_P_facts h
  obtain ⟨-, hxR, hsR⟩ := Item1116Proof.mem_R h
  have haR : a ∈ R := Item1115Proof.A_le_R h.toHyp91 h.a_mem
  have hRP : R ≤ sec11P R g := Item1119Proof.R_le_P R g
  have hgP := Item1119Proof.g_mem_P R g
  have hR : R = Subgroup.closure {a, x, s} := Item1116NoFifteen.R_eq_of_closure_eq h hrs
  have hRc : Subgroup.closure ({a, x, s} : Set G) ≤ sec11P R g := by rw [← hR]; exact hRP
  obtain ⟨hs3, hx3, -⟩ := piG_cube_s_x h45 h1115 h1120 hbig π hπ
  have hB := right_eq_one_of_mem_mapR h45 h1115 h1120 hbig π hπ
  have hγ := right_piG_g_ne_one h45 h1115 h1120 hbig π hπ
  have h27 : 27 ≤ Nat.card (mapP π R) := by have := card_W_le_mapR hbig π hπ; omega
  have hsa : s * a = a * s := h1115 G A c L a R Y d x s r g h
  have hsx := h.commute_s_x
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have hag : a * g = g * a := (Subgroup.mem_centralizer_singleton_iff.mp
    (Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt_Y h.g_mem.1)).symm
  have haZ : piG π a ∈ Subgroup.zpowers wreathZ :=
    mem_zpowers_wreathZ_of_commute (hB _ (piG_mem_mapP π hRP haR)) hγ
      (by rw [← piG_mul π haP hgP, hag, piG_mul π hgP haP])
  have hsC : ∀ y ∈ R, y * s = s * y := by
    intro y hy
    rw [hR] at hy
    have hle : Subgroup.closure ({a, x, s} : Set G) ≤ Subgroup.centralizer {s} := by
      rw [Subgroup.closure_le]
      rintro t (rfl | rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hsa.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hsx.symm
      · exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  set z := g * s * g⁻¹ with hz
  have hzR : z ∈ R := (Subgroup.mem_normalizer_iff.mp h.g_mem_normalizer s).mp hsR
  have hzC : ∀ y ∈ R, y * z = z * y := by
    intro y hy
    have hy' : g⁻¹ * y * g ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ h.g_mem_normalizer) y).mp hy
      rwa [inv_inv] at this
    have h1 := hsC _ hy'
    calc y * z = g * ((g⁻¹ * y * g) * s) * g⁻¹ := by rw [hz]; group
      _ = g * (s * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = z * y := by rw [hz]; group
  have haN : a ∈ Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G) :=
    h.R_le_normalizer_V h45 haR
  have hzR' : z ∈ Subgroup.closure ({a, x, s} : Set G) := hR ▸ hzR
  obtain ⟨k, v, hv, hzv⟩ := Item1123Proof.exists_zpow_mul_of_mem_closure haN hzR'
  have hvx : v * x = x * v :=
    Item1115Proof.commute_of_mem_closure_pair hsx hv (Subgroup.subset_closure (by simp))
  have hak : a ^ k = 1 := by
    by_contra hk1
    have h3k : ¬ (3 : ℤ) ∣ k := by
      rintro ⟨t, rfl⟩
      apply hk1
      rw [zpow_mul]
      norm_cast
      rw [ha3, one_zpow]
    have hax : a ^ k * x = x * a ^ k := by
      have h1 := hzC x hxR
      rw [hzv] at h1
      have h2 : x * a ^ k * v = a ^ k * x * v := by
        calc x * a ^ k * v = x * (a ^ k * v) := by group
          _ = a ^ k * v * x := h1
          _ = a ^ k * (v * x) := by group
          _ = a ^ k * (x * v) := by rw [hvx]
          _ = a ^ k * x * v := by group
      exact (mul_right_cancel h2).symm
    have hamem := Item1116Proof.mem_zpowers_zpow_of_not_dvd ⟨1, by rw [pow_one]; exact ha3⟩ h3k
    apply Item1115Proof.not_commute_a_x h
    have hC : Subgroup.zpowers (a ^ k) ≤ Subgroup.centralizer {x} :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hax)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hC hamem)
  rw [hak, one_mul] at hzv
  obtain ⟨m, n, hmn⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hsx hv
  have hxn : x ^ n * a = a * x ^ n := by
    have h1 := hzC a haR
    rw [hzv, hmn] at h1
    have hsma : s ^ m * a = a * s ^ m := (Commute.zpow_left (hsa : Commute s a) m).eq
    have h2 : s ^ m * (a * x ^ n) = s ^ m * (x ^ n * a) := by
      calc s ^ m * (a * x ^ n) = (s ^ m * a) * x ^ n := by group
        _ = (a * s ^ m) * x ^ n := by rw [hsma]
        _ = a * (s ^ m * x ^ n) := by group
        _ = s ^ m * x ^ n * a := h1
        _ = s ^ m * (x ^ n * a) := by group
    exact (mul_left_cancel h2).symm
  have h3n : (3 : ℤ) ∣ n := by
    by_contra h3n
    have hxmem := Item1116Proof.mem_zpowers_zpow_of_not_dvd
      (Item1116Proof.exists_pow_eq_one_of_mem h hxR) h3n
    apply Item1115Proof.not_commute_a_x h
    have hC : Subgroup.zpowers (x ^ n) ≤ Subgroup.centralizer {a} :=
      Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxn)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hC hxmem)).symm
  have hpz : piG π z ∈ Subgroup.zpowers (piG π s) := by
    have hx3' : piG π x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
    rw [hzv, hmn, piG_mul π (Subgroup.zpow_mem _ hsP m) (Subgroup.zpow_mem _ hxP n),
      piG_zpow π hsP, piG_zpow π hxP]
    obtain ⟨t, rfl⟩ := h3n
    rw [zpow_mul, hx3', one_zpow, mul_one]
    exact Subgroup.zpow_mem_zpowers _ m
  have hγ3 : ∃ k : ℕ, piG π g ^ 3 ^ k = 1 := ⟨1, by rw [pow_one]; exact piG_g_pow_three hbig π⟩
  have hgs : piG π g * piG π s * (piG π g)⁻¹ = piG π s := by
    refine conj_eq_self_of_threeElement hs3 hγ3 ?_
    rw [← piG_conj π hgP hsP]
    exact hpz
  have hsZ : piG π s ∈ Subgroup.zpowers wreathZ :=
    mem_zpowers_wreathZ_of_commute (hB _ (piG_mem_mapP π hRP hsR)) hγ (by
      calc piG π s * piG π g = (piG π g * piG π s * (piG π g)⁻¹) * piG π g := by rw [hgs]
        _ = piG π g * piG π s := by group)
  have hZx : wreathZ * piG π x = piG π x * wreathZ := commute_wreathZ_left _
  have hZle : Subgroup.zpowers wreathZ ≤ Subgroup.closure {wreathZ, piG π x} :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))
  have hle : mapP π R ≤ Subgroup.closure {wreathZ, piG π x} := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_mapP π hw
    rw [hR] at hy
    exact piG_mem_of_mem_closure π hRc (by
      rintro t (rfl | rfl | rfl)
      · exact hZle haZ
      · exact Subgroup.subset_closure (by simp)
      · exact hZle hsZ) hy
  have h9 := (Subgroup.card_le_of_le hle).trans
    (card_closure_pair_le_nine hZx wreathZ_pow_three hx3)
  omega

theorem piG_r_pow_three (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π) : piG π r ^ 3 = 1 :=
  pow_three_eq_one_of_right_eq_one (right_eq_one_of_mem_mapR h45 h1115 h1120 hbig π hπ _
    (piG_mem_mapP π (Item1119Proof.R_le_P R g) (Item1116Proof.mem_R hbig.toSec11Data).1))

theorem closure_s_x_le_P (h : Sec11Data G A c L a R Y d x s r g) :
    Subgroup.closure ({s, x} : Set G) ≤ sec11P R g := by
  obtain ⟨-, hxP, hsP, -, -, -⟩ := mem_P_facts h
  rw [Subgroup.closure_le]
  rintro t (rfl | rfl)
  exacts [hsP, hxP]

theorem closure_s_x_a_le_P (h : Sec11Data G A c L a R Y d x s r g) :
    Subgroup.closure ({s, x, a} : Set G) ≤ sec11P R g := by
  obtain ⟨-, hxP, hsP, haP, -, -⟩ := mem_P_facts h
  rw [Subgroup.closure_le]
  rintro t (rfl | rfl | rfl)
  exacts [hsP, hxP, haP]

theorem piG_a_mem_closure (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π)
    (hrs : Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s}) :
    piG π a ∈ Subgroup.closure {piG π s, piG π x} := by
  have h := hbig.toSec11Data
  obtain ⟨hrP, -, -, -, -, -⟩ := mem_P_facts h
  obtain ⟨hrR, -, -⟩ := Item1116Proof.mem_R h
  have hr3 := piG_r_pow_three h45 h1115 h1120 hbig π hπ
  have hrN : r ^ 3 ∈ Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G) :=
    Subgroup.pow_mem _ (h.R_le_normalizer_V h45 hrR) 3
  obtain ⟨k, v, hv, hav⟩ := Item1123Proof.exists_zpow_mul_of_mem_closure hrN
    (h.mem_closure_pow_three_of_closure_ne h45 hrs)
  have hsxP := closure_s_x_le_P h
  have hr3P : r ^ 3 ∈ sec11P R g := Subgroup.pow_mem _ hrP 3
  rw [hav, piG_mul π (Subgroup.zpow_mem _ hr3P k) (hsxP hv), piG_zpow π hr3P, piG_pow π hrP, hr3,
    one_zpow, one_mul]
  exact piG_mem_of_mem_closure π hsxP (by
    rintro t (rfl | rfl) <;> exact Subgroup.subset_closure (by simp)) hv

theorem mapV_le_closure (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π)
    (hrs : Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s}) :
    mapP π (Subgroup.closure {s, x, a}) ≤ Subgroup.closure {piG π s, piG π x} :=
  mapP_closure_le π (closure_s_x_a_le_P hbig.toSec11Data) (by
    rintro t (rfl | rfl | rfl)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact piG_a_mem_closure h45 h1115 h1120 hbig π hπ hrs)

theorem card_mapR_le (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π) :
    Nat.card (mapP π R) ≤ 3 * Nat.card (mapP π (Subgroup.closure {s, x, a})) := by
  have h := hbig.toSec11Data
  obtain ⟨hrP, -, -, -, -, -⟩ := mem_P_facts h
  obtain ⟨hrR, -, -⟩ := Item1116Proof.mem_R h
  have hRP : R ≤ sec11P R g := Item1119Proof.R_le_P R g
  have hr3 := piG_r_pow_three h45 h1115 h1120 hbig π hπ
  set V := Subgroup.closure ({s, x, a} : Set G) with hV
  have hVP := closure_s_x_a_le_P h
  have hsxV : Subgroup.closure ({s, x} : Set G) ≤ V := by
    rw [hV]
    exact Subgroup.closure_mono (by intro t ht; rcases ht with rfl | rfl <;> simp)
  have haR : a ∈ R := Item1115Proof.A_le_R h.toHyp91 h.a_mem
  obtain ⟨-, hxR, hsR⟩ := Item1116Proof.mem_R h
  have hVR : V ≤ R := by
    rw [hV, Subgroup.closure_le]
    rintro t (rfl | rfl | rfl)
    exacts [hsR, hxR, haR]
  have hVRm : mapP π V ≤ mapP π R := Subgroup.map_mono (fun y hy => hVR hy)
  have hrm := piG_mem_mapP π hRP hrR
  let f : Fin 3 × mapP π V → mapP π R := fun p =>
    ⟨piG π r ^ (p.1 : ℕ) * p.2, Subgroup.mul_mem _ (Subgroup.pow_mem _ hrm _) (hVRm p.2.2)⟩
  have hf : Function.Surjective f := by
    rintro ⟨w, hw⟩
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_mapP π hw
    have hrN := h.R_le_normalizer_V h45 hrR
    rw [h.R_eq] at hy
    obtain ⟨k, v, hv, rfl⟩ := Item1123Proof.exists_zpow_mul_of_mem_closure hrN hy
    obtain ⟨i, hi⟩ := exists_fin_three_zpow (piG π r) hr3 k
    refine ⟨(i, ⟨piG π v, piG_mem_mapP π hVP (hsxV hv)⟩), ?_⟩
    apply Subtype.ext
    simp only [f]
    rw [piG_mul π (Subgroup.zpow_mem _ hrP k) (closure_s_x_le_P h hv), piG_zpow π hrP, hi]
  have h1 := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h1
  exact h1

theorem card_mapV_eq_nine (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π)
    (hrs : Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s}) :
    Nat.card (mapP π (Subgroup.closure {s, x, a})) = 9 := by
  have h := hbig.toSec11Data
  obtain ⟨-, hxP, hsP, -, -, -⟩ := mem_P_facts h
  obtain ⟨hs3, hx3, -⟩ := piG_cube_s_x h45 h1115 h1120 hbig π hπ
  have hsx : piG π s * piG π x = piG π x * piG π s := by
    rw [← piG_mul π hsP hxP, ← piG_mul π hxP hsP, h.commute_s_x]
  have h1 := (Subgroup.card_le_of_le (mapV_le_closure h45 h1115 h1120 hbig π hπ hrs)).trans
    (card_closure_pair_le_nine hsx hs3 hx3)
  have h2 := card_mapR_le h45 h1115 h1120 hbig π hπ
  have h3 := card_W_le_mapR hbig π hπ
  omega

theorem commutator_le_mapV (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π)
    (hrs : Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s}) :
    ⁅(⊤ : Subgroup W33), ⊤⁆ ≤ mapP π (Subgroup.closure {s, x, a}) :=
  commutator_le_of_normal_card_nine (mapP_normal π (closure_s_x_a_le_P hbig.toSec11Data)
    (h1120 G A c L a R Y d x s r g hbig) hπ) (card_mapV_eq_nine h45 h1115 h1120 hbig π hπ hrs)

theorem piG_r_not_mem_mapV (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π)
    (hrs : Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s}) :
    piG π r ∉ mapP π (Subgroup.closure {s, x, a}) := by
  intro hr
  have h := hbig.toSec11Data
  have hVP := closure_s_x_a_le_P h
  have hRP : R ≤ sec11P R g := Item1119Proof.R_le_P R g
  have hRc : Subgroup.closure ({r, x, s} : Set G) ≤ sec11P R g := h.R_eq ▸ hRP
  have hle : mapP π R ≤ mapP π (Subgroup.closure {s, x, a}) := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_mapP π hw
    rw [h.R_eq] at hy
    exact piG_mem_of_mem_closure π hRc (by
      rintro t (rfl | rfl | rfl)
      · exact hr
      · exact piG_mem_mapP π hVP (Subgroup.subset_closure (by simp))
      · exact piG_mem_mapP π hVP (Subgroup.subset_closure (by simp))) hy
  have h1 := Subgroup.card_le_of_le hle
  rw [card_mapV_eq_nine h45 h1115 h1120 hbig π hπ hrs] at h1
  have h3 := card_W_le_mapR hbig π hπ
  omega

theorem mem_mapV_of_mem_sup (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π) {w : W33}
    (hw : w ∈ mapP π (Subgroup.closure {s, x, a}) ⊔ Subgroup.zpowers (piG π g))
    (hw1 : w.right = 1) : w ∈ mapP π (Subgroup.closure {s, x, a}) := by
  have h := hbig.toSec11Data
  set N := mapP π (Subgroup.closure ({s, x, a} : Set G)) with hNdef
  have hN : N.Normal := mapP_normal π (closure_s_x_a_le_P h) (h1120 G A c L a R Y d x s r g hbig) hπ
  have hγN : piG π g ∈ Subgroup.normalizer (N : Set W33) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hN]
    trivial
  rw [sup_comm] at hw
  obtain ⟨k, m, hm, rfl⟩ := Item1119Proof.exists_zpow_mul_of_mem_sup hγN hw
  have hNB : ∀ v ∈ N, v.right = 1 := by
    intro v hv
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_mapP π hv
    have haR : a ∈ R := Item1115Proof.A_le_R h.toHyp91 h.a_mem
    obtain ⟨-, hxR, hsR⟩ := Item1116Proof.mem_R h
    have hVR : Subgroup.closure ({s, x, a} : Set G) ≤ R := by
      rw [Subgroup.closure_le]
      rintro t (rfl | rfl | rfl)
      exacts [hsR, hxR, haR]
    exact right_eq_one_of_mem_mapR h45 h1115 h1120 hbig π hπ _
      (piG_mem_mapP π (Item1119Proof.R_le_P R g) (hVR hy))
  rw [right_mul, hNB m hm, mul_one] at hw1
  have h2 : (piG π g ^ k).right = (piG π g).right ^ k := map_zpow RegularWreathProduct.rightHom _ k
  rw [h2] at hw1
  have h3 : ((3 : ℕ) : ℤ) ∣ k := by
    rw [← orderOf_right_piG_g h45 h1115 h1120 hbig π hπ]
    exact orderOf_dvd_iff_zpow_eq_one.mpr hw1
  obtain ⟨t, rfl⟩ := h3
  have hg3' : piG π g ^ ((3 : ℕ) : ℤ) = 1 := by exact_mod_cast piG_g_pow_three hbig π
  rw [zpow_mul, hg3', one_zpow, one_mul]
  exact hm

theorem piG_r_not_mem_mapM (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π)
    (hrs : Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s}) :
    piG π r ∉ mapP π (Subgroup.closure {s, x, a}) ⊔ Subgroup.zpowers (piG π g) := fun hr =>
  piG_r_not_mem_mapV h45 h1115 h1120 hbig π hπ hrs
    (mem_mapV_of_mem_sup h45 h1115 h1120 hbig π hπ hr
      (right_eq_one_of_mem_mapR h45 h1115 h1120 hbig π hπ _ (piG_mem_mapP π
        (Item1119Proof.R_le_P R g) (Item1116Proof.mem_R hbig.toSec11Data).1)))

theorem commutator_le_mapM (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π)
    (hrs : Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s}) :
    ⁅(⊤ : Subgroup W33), ⊤⁆ ≤ mapP π (Subgroup.closure {s, x, a}) ⊔ Subgroup.zpowers (piG π g) :=
  (commutator_le_mapV h45 h1115 h1120 hbig π hπ hrs).trans le_sup_left

theorem mem_mapM_of_pow_three (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π)
    (hrs : Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s}) {w : W33}
    (hw : w.right ≠ 1) (hw3 : w ^ 3 = 1) :
    w ∈ mapP π (Subgroup.closure {s, x, a}) ⊔ Subgroup.zpowers (piG π g) :=
  mem_sup_zpowers_of_pow_three_eq_one (commutator_le_mapV h45 h1115 h1120 hbig π hπ hrs)
    (right_piG_g_ne_one h45 h1115 h1120 hbig π hπ) (piG_g_pow_three hbig π) hw hw3

theorem preU_facts (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π)
    (hrs : Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s}) :
    let U := preU π (mapP π (Subgroup.closure {s, x, a}) ⊔ Subgroup.zpowers (piG π g))
    (∀ y ∈ sec11P R g, ∀ u ∈ U, y * u * y⁻¹ ∈ U) ∧
      (∀ y ∈ sec11P R g, ∀ z ∈ sec11P R g, y * z * y⁻¹ * z⁻¹ ∈ U) ∧ r ∉ U ∧
      Subgroup.closure {s, x} ≤ U ∧
      (∀ z ∈ sec11P R g, z ^ 3 = 1 → z ∉ R → z ∈ U) := by
  intro U
  have h := hbig.toSec11Data
  obtain ⟨-, hxP, hsP, -, -, -⟩ := mem_P_facts h
  have hVP := closure_s_x_a_le_P h
  set M := mapP π (Subgroup.closure ({s, x, a} : Set G)) ⊔ Subgroup.zpowers (piG π g) with hM
  have hcomm := commutator_le_mapM h45 h1115 h1120 hbig π hπ hrs
  have hMn := normal_of_commutator_le hcomm
  refine ⟨fun y hy u hu => conj_mem_preU π hMn hy hu,
    fun y hy z hz => commutator_mem_preU π hcomm hy hz, fun hr => ?_, ?_, ?_⟩
  · exact piG_r_not_mem_mapM h45 h1115 h1120 hbig π hπ hrs ((mem_preU π).mp hr).2
  · rw [Subgroup.closure_le]
    rintro t (rfl | rfl)
    · exact (mem_preU π).mpr ⟨hsP, Subgroup.mem_sup_left
        (piG_mem_mapP π hVP (Subgroup.subset_closure (by simp)))⟩
    · exact (mem_preU π).mpr ⟨hxP, Subgroup.mem_sup_left
        (piG_mem_mapP π hVP (Subgroup.subset_closure (by simp)))⟩
  · intro z hz hz3 hzR
    refine (mem_preU π).mpr ⟨hz, mem_mapM_of_pow_three h45 h1115 h1120 hbig π hπ hrs ?_ ?_⟩
    · exact fun h1 => hzR (mem_R_of_right_eq_one h45 h1115 h1120 hbig π hπ hz h1)
    · rw [← piG_pow π hz, hz3, piG_one]

theorem card_mapR_le_closure_r_s (h45 : Sec4.Item4_5) (h1115 : Item1115) (h1120 : Item1120)
    (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π) :
    Nat.card (mapP π R) ≤ 3 * Nat.card (Subgroup.closure {piG π r, piG π s}) := by
  have h := hbig.toSec11Data
  obtain ⟨hrP, hxP, hsP, -, -, -⟩ := mem_P_facts h
  obtain ⟨hrR, hxR, hsR⟩ := Item1116Proof.mem_R h
  have hRP : R ≤ sec11P R g := Item1119Proof.R_le_P R g
  obtain ⟨-, hx3, -⟩ := piG_cube_s_x h45 h1115 h1120 hbig π hπ
  have hab := mul_comm_of_mem_mapR h45 h1115 h1120 hbig π hπ
  have hrm := piG_mem_mapP π hRP hrR
  have hxm := piG_mem_mapP π hRP hxR
  have hsm := piG_mem_mapP π hRP hsR
  have hRc : Subgroup.closure ({r, x, s} : Set G) ≤ sec11P R g := h.R_eq ▸ hRP
  have hle : mapP π R ≤ Subgroup.closure {piG π r, piG π s, piG π x} := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_mapP π hw
    rw [h.R_eq] at hy
    exact piG_mem_of_mem_closure π hRc (by
      rintro t (rfl | rfl | rfl) <;> exact Subgroup.subset_closure (by simp)) hy
  let f : Subgroup.closure ({piG π r, piG π s} : Set W33) × Fin 3 →
      Subgroup.closure ({piG π r, piG π s, piG π x} : Set W33) := fun p =>
    ⟨(p.1 : W33) * piG π x ^ (p.2 : ℕ), Subgroup.mul_mem _
      (Subgroup.closure_mono (by intro t ht; rcases ht with rfl | rfl <;> simp) p.1.2)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)⟩
  have hf : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨i, j, k, rfl⟩ := exists_zpow_triple_of_mem_closure (hab _ hrm _ hsm) (hab _ hrm _ hxm)
      (hab _ hsm _ hxm) hz
    obtain ⟨k', hk'⟩ := exists_fin_three_zpow (piG π x) hx3 k
    refine ⟨(⟨piG π r ^ i * piG π s ^ j, Subgroup.mul_mem _
      (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) i)
      (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) j)⟩, k'), ?_⟩
    apply Subtype.ext
    simp only [f]
    rw [hk']
  have h1 := Nat.card_le_card_of_surjective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h1
  exact (Subgroup.card_le_of_le hle).trans (by omega)

theorem r_mul_a_ne (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117) (h1115 : Item1115)
    (h1120 : Item1120) (hbig : Sec11Big G A c L a R Y d x s r g) (π : sec11P R g →* W33)
    (hπ : Function.Surjective π)
    (hrs : Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s}) : r * a ≠ a * r := by
  intro hra
  have h := hbig.toSec11Data
  obtain ⟨hrP, hxP, hsP, -, -, -⟩ := mem_P_facts h
  obtain ⟨hrR, hxR, hsR⟩ := Item1116Proof.mem_R h
  have hRP : R ≤ sec11P R g := Item1119Proof.R_le_P R g
  have hsa : s * a = a * s := h1115 G A c L a R Y d x s r g h
  have hsx := h.commute_s_x
  obtain ⟨hs3, hx3, -⟩ := piG_cube_s_x h45 h1115 h1120 hbig π hπ
  have hr3 := piG_r_pow_three h45 h1115 h1120 hbig π hπ
  set T := R ⊓ Subgroup.centralizer (A : Set G) with hT
  have hTR : T ≤ R := inf_le_left
  have hTP : T ≤ sec11P R g := hTR.trans hRP
  have hPA := h.sec11P_le_normalizer_A h113
  have hPR : sec11P R g ≤ Subgroup.normalizer (R : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr h.g_mem_normalizer)
  have hPT : sec11P R g ≤ Subgroup.normalizer (T : Set G) := by
    intro y hy
    refine Subgroup.mem_normalizer_fintype fun t ht => ?_
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hPR hy) t).mp ht.1, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hb' : y⁻¹ * b * y ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hPA hy)) b).mp hb
      rwa [inv_inv] at this
    have h1 := Subgroup.mem_centralizer_iff.mp ht.2 _ hb'
    calc b * (y * t * y⁻¹) = y * ((y⁻¹ * b * y) * t) * y⁻¹ := by group
      _ = y * (t * (y⁻¹ * b * y)) * y⁻¹ := by rw [h1]
      _ = y * t * y⁻¹ * b := by group
  have hN := mapP_normal π hTP hPT hπ
  have hcen : ∀ y : G, c * y = y * c → a * y = y * a → d * y = y * d →
      y ∈ Subgroup.centralizer (A : Set G) := by
    intro y hyc hya hyd
    have hle : A ≤ Subgroup.centralizer {y} := by
      rw [h.closure_eq, Subgroup.closure_le]
      rintro t (rfl | rfl | rfl)
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hyc
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hya
      · exact Subgroup.mem_centralizer_singleton_iff.mpr hyd
    exact Subgroup.mem_centralizer_iff.mpr fun b hb =>
      Subgroup.mem_centralizer_singleton_iff.mp (hle hb)
  have hRc : ∀ y ∈ R, c * y = y * c := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (Item1119Proof.R_le_centralizer_c h hy)).symm
  have hRd : ∀ y ∈ R, d * y = y * d := fun y hy =>
    (Item1119Proof.commute_d h113 h117 h (hRP hy)).symm
  have hrT : r ∈ T := ⟨hrR, hcen r (hRc r hrR) hra.symm (hRd r hrR)⟩
  have hsT : s ∈ T := ⟨hsR, hcen s (hRc s hsR) hsa.symm (hRd s hsR)⟩
  have hle : mapP π T ≤ Subgroup.closure {piG π r, piG π s} := by
    intro w hw
    obtain ⟨y, hy, rfl⟩ := exists_of_mem_mapP π hw
    have hya : y * a = a * y := (Subgroup.mem_centralizer_iff.mp hy.2 a h.a_mem).symm
    have hyR : y ∈ Subgroup.closure ({r, x, s} : Set G) := h.R_eq ▸ hy.1
    obtain ⟨α, v, hv, rfl⟩ :=
      Item1123Proof.exists_zpow_mul_of_mem_closure (h.R_le_normalizer_V h45 hrR) hyR
    obtain ⟨γ', β, rfl⟩ := Sec12.exists_zpow_mul_zpow_of_mem_closure_pair hsx hv
    have hra' : r ^ α * a = a * r ^ α := (Commute.zpow_left (hra : Commute r a) α).eq
    have hsa' : s ^ γ' * a = a * s ^ γ' := (Commute.zpow_left (hsa : Commute s a) γ').eq
    have hxa : x ^ β * a = a * x ^ β := by
      have h2 : r ^ α * s ^ γ' * (x ^ β * a) = r ^ α * s ^ γ' * (a * x ^ β) := by
        calc r ^ α * s ^ γ' * (x ^ β * a) = r ^ α * (s ^ γ' * x ^ β) * a := by group
          _ = a * (r ^ α * (s ^ γ' * x ^ β)) := hya
          _ = (a * r ^ α) * s ^ γ' * x ^ β := by group
          _ = (r ^ α * a) * s ^ γ' * x ^ β := by rw [hra']
          _ = r ^ α * (a * s ^ γ') * x ^ β := by group
          _ = r ^ α * (s ^ γ' * a) * x ^ β := by rw [hsa']
          _ = r ^ α * s ^ γ' * (a * x ^ β) := by group
      exact mul_left_cancel h2
    have h3β : (3 : ℤ) ∣ β := by
      by_contra h3β
      have hxmem := Item1116Proof.mem_zpowers_zpow_of_not_dvd
        (Item1116Proof.exists_pow_eq_one_of_mem h hxR) h3β
      apply Item1115Proof.not_commute_a_x h
      have hC : Subgroup.zpowers (x ^ β) ≤ Subgroup.centralizer {a} :=
        Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hxa)
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hC hxmem)).symm
    obtain ⟨t, rfl⟩ := h3β
    have hx3' : piG π x ^ (3 : ℤ) = 1 := by exact_mod_cast hx3
    rw [piG_mul π (Subgroup.zpow_mem _ hrP α) (Subgroup.mul_mem _ (Subgroup.zpow_mem _ hsP _)
        (Subgroup.zpow_mem _ hxP _)),
      piG_mul π (Subgroup.zpow_mem _ hsP _) (Subgroup.zpow_mem _ hxP _), piG_zpow π hrP,
      piG_zpow π hsP, piG_zpow π hxP, zpow_mul, hx3', one_zpow, mul_one]
    exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) α)
      (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) γ')
  have hrs' : piG π r * piG π s = piG π s * piG π r :=
    mul_comm_of_mem_mapR h45 h1115 h1120 hbig π hπ _ (piG_mem_mapP π hRP hrR) _
      (piG_mem_mapP π hRP hsR)
  have h9le := card_closure_pair_le_nine hrs' hr3 hs3
  have h27 := card_mapR_le_closure_r_s h45 h1115 h1120 hbig π hπ
  have h81 := card_W_le_mapR hbig π hπ
  have hge : Subgroup.closure {piG π r, piG π s} ≤ mapP π T := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    exacts [piG_mem_mapP π hTP hrT, piG_mem_mapP π hTP hsT]
  have hTeq := le_antisymm hle hge
  have hNcard : Nat.card (mapP π T) = 9 := by rw [hTeq]; omega
  have hVn := mapP_normal π (closure_s_x_a_le_P h) (h1120 G A c L a R Y d x s r g hbig) hπ
  have heq := eq_of_normal_card_nine hN hVn hNcard (card_mapV_eq_nine h45 h1115 h1120 hbig π hπ hrs)
  exact piG_r_not_mem_mapV h45 h1115 h1120 hbig π hπ hrs (heq ▸ piG_mem_mapP π hTP hrT)

end Data

end Item1121Proof

end CFSG.RankThree.PartTwo.Sec11
