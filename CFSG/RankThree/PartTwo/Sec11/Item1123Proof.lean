module

public import CFSG.RankThree.PartTwo.Sec11.Skeleton
import CFSG.RankThree.PartTwo.Sec11.Item1115Proof
import CFSG.RankThree.PartTwo.Sec11.Item1125Proof
public import CFSG.RankThree.PartTwo.Sec11.Item1115
public import CFSG.RankThree.PartTwo.Sec11.Transitivity

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

namespace Item1123Proof

section Elementary

variable {G : Type} [Group G]

theorem conj_mul_inv_mem_of_pow_three_mem {N : Subgroup G} {g y : G}
    (hgN : g ∈ Subgroup.normalizer (N : Set G)) (hyN : y ∈ Subgroup.normalizer (N : Set G))
    (hy3 : y ^ 3 ∈ N) (hg3 : ∃ k : ℕ, g ^ 3 ^ k = 1) {k : ℤ}
    (hk : (y ^ k)⁻¹ * (g * y * g⁻¹) ∈ N) : g * y * g⁻¹ * y⁻¹ ∈ N := by
  set M := Subgroup.normalizer (N : Set G) with hM
  set N' := N.subgroupOf M with hN'
  have : N'.Normal := Subgroup.normal_in_normalizer
  set g' : M := ⟨g, hgN⟩ with hg'
  set y' : M := ⟨y, hyN⟩ with hy'
  have hy'3 : ((y' : M ⧸ N') ^ 3) = 1 := by
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact hy3
  have hg'3 : ∃ k : ℕ, ((g' : M ⧸ N')) ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hg3
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have e : ((g' ^ 3 ^ k : M) : G) = 1 := by
      rw [Subgroup.coe_pow]
      exact hk
    rw [e]
    exact N.one_mem
  have hconj : (g' : M ⧸ N') * (y' : M ⧸ N') * (g' : M ⧸ N')⁻¹ ∈
      Subgroup.zpowers (y' : M ⧸ N') := by
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    rw [← QuotientGroup.mk_zpow, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have e : (((y' ^ k)⁻¹ * (g' * y' * g'⁻¹) : M) : G) = (y ^ k)⁻¹ * (g * y * g⁻¹) := by
      simp [g', y']
    rw [e]
    exact hk
  have h := conj_eq_self_of_threeElement hy'3 hg'3 hconj
  rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
    Subgroup.mem_subgroupOf] at h
  have e : (((g' * y' * g'⁻¹)⁻¹ * y' : M) : G) = g * y⁻¹ * g⁻¹ * y := by
    simp only [g', y', Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e] at h
  have e' : g * y * g⁻¹ * y⁻¹ = y * (g * y⁻¹ * g⁻¹ * y)⁻¹ * y⁻¹ := by group
  rw [e']
  exact (Subgroup.mem_normalizer_iff.mp hyN _).mp (N.inv_mem h)

theorem exists_zpow_mul_of_mem_closure {w s x y : G}
    (hw : w ∈ Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G))
    (hy : y ∈ Subgroup.closure ({w, x, s} : Set G)) :
    ∃ k : ℤ, ∃ v ∈ Subgroup.closure ({s, x} : Set G), y = w ^ k * v := by
  have hcl : Subgroup.closure ({w, x, s} : Set G) =
      Subgroup.zpowers w ⊔ Subgroup.closure ({s, x} : Set G) := by
    rw [Set.insert_eq, Subgroup.closure_union, Subgroup.zpowers_eq_closure, Set.pair_comm]
  have hle : Subgroup.zpowers w ≤
      Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hw
  have hy' : y ∈ ((Subgroup.zpowers w ⊔ Subgroup.closure ({s, x} : Set G) : Subgroup G) :
      Set G) := by
    rw [← hcl]
    exact hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hy'
  obtain ⟨u, hu, v, hv, rfl⟩ := Set.mem_mul.mp hy'
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  exact ⟨k, v, hv, rfl⟩

theorem pow_three_mem_closure {r s x v : G}
    (hr : r ∈ Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G))
    (hv : v ∈ Subgroup.closure ({s, x} : Set G)) (k : ℤ) :
    (r ^ k * v) ^ 3 ∈ Subgroup.closure ({r ^ 3, x, s} : Set G) := by
  set V₃ := Subgroup.closure ({r ^ 3, x, s} : Set G) with hV₃
  have h1 := Item1115Proof.inv_pow_mul_pow_mem (Subgroup.zpow_mem _ hr k) hv 3
  have hle : Subgroup.closure ({s, x} : Set G) ≤ V₃ := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl <;> exact Subgroup.subset_closure (by simp)
  have hr3 : (r ^ k) ^ 3 ∈ V₃ := by
    have e : (r ^ k) ^ 3 = (r ^ 3) ^ k := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    rw [e]
    exact Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) k
  have e : (r ^ k * v) ^ 3 = (r ^ k) ^ 3 * (((r ^ k) ^ 3)⁻¹ * (r ^ k * v) ^ 3) := by group
  rw [e]
  exact V₃.mul_mem hr3 (hle h1)

theorem not_mem_closure_pow_three {r s x : G} (hr3 : ∃ k : ℕ, r ^ 3 ^ k = 1)
    (hr : r ∈ Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G))
    (hrV : r ∉ Subgroup.closure ({s, x} : Set G)) :
    r ∉ Subgroup.closure ({r ^ 3, x, s} : Set G) := by
  intro hmem
  obtain ⟨k, v, hv, he⟩ := exists_zpow_mul_of_mem_closure (Subgroup.pow_mem _ hr 3) hmem
  have hv' : r ^ (1 - 3 * k) ∈ Subgroup.closure ({s, x} : Set G) := by
    have e : r ^ (1 - 3 * k) = ((r ^ 3) ^ k)⁻¹ * r := by
      rw [← zpow_natCast, ← zpow_mul, ← zpow_neg, ← zpow_add_one]
      congr 1
      push_cast
      ring
    rw [e]
    nth_rewrite 2 [he]
    rw [inv_mul_cancel_left]
    exact hv
  exact hrV (Subgroup.zpowers_le.mpr hv'
    (Item1116Proof.mem_zpowers_zpow_of_not_dvd hr3 (by omega)))

variable [Finite G]

theorem mem_normalizer_closure_pow_three {r s x y : G}
    (hr : r ∈ Subgroup.normalizer ((Subgroup.closure {s, x} : Subgroup G) : Set G))
    (hyR : y ∈ Subgroup.normalizer ((Subgroup.closure {r, x, s} : Subgroup G) : Set G))
    (hys : y * s * y⁻¹ ∈ Subgroup.closure ({r ^ 3, x, s} : Set G))
    (hyx : y * x * y⁻¹ ∈ Subgroup.closure ({r ^ 3, x, s} : Set G)) :
    y ∈ Subgroup.normalizer ((Subgroup.closure {r ^ 3, x, s} : Subgroup G) : Set G) := by
  set V₃ := Subgroup.closure ({r ^ 3, x, s} : Set G) with hV₃
  have hle : V₃ ≤ V₃.comap (MulAut.conj y).toMonoidHom := by
    rw [hV₃, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    change y * z * y⁻¹ ∈ _
    rcases hz with rfl | rfl | rfl
    · have hyr : y * r * y⁻¹ ∈ Subgroup.closure ({r, x, s} : Set G) :=
        (Subgroup.mem_normalizer_iff.mp hyR r).mp (Subgroup.subset_closure (by simp))
      obtain ⟨k, v, hv, he⟩ := exists_zpow_mul_of_mem_closure hr hyr
      rw [← conj_pow, he]
      exact pow_three_mem_closure hr hv k
    · exact hyx
    · exact hys
  exact Subgroup.mem_normalizer_fintype fun z hz => hle hz

end Elementary

end Item1123Proof

section Data

variable {G : Type} [Group G] [Finite G]

theorem Sec11Data.mem_closure_pow_three_of_closure_ne (h45 : Sec4.Item4_5) {A : Subgroup G}
    {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g)
    (hrs : Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s}) :
    a ∈ Subgroup.closure ({r ^ 3, x, s} : Set G) := by
  obtain ⟨hrR, -, -⟩ := Item1116Proof.mem_R h
  obtain ⟨i, j, hij⟩ := Item1116Proof.exists_zpow_mul_zpow_of_mem_closure
    (Item1115Proof.mem_normalizer_zpowers_s h45 h hrR) h.a_mem_closure
  have h3i : (3 : ℤ) ∣ i := by
    by_contra h3
    apply hrs
    have hri : r ^ i ∈ Subgroup.closure ({a, s} : Set G) := by
      have e : r ^ i = a * (s ^ j)⁻¹ := by
        rw [hij]
        group
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.inv_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) j))
    have hr : r ∈ Subgroup.closure ({a, s} : Set G) :=
      Subgroup.zpowers_le.mpr hri (Item1116Proof.mem_zpowers_zpow_of_not_dvd
        (Item1116Proof.exists_pow_eq_one_of_mem h hrR) h3)
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact hr
      · exact Subgroup.subset_closure (by simp)
    · rw [Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact h.a_mem_closure
      · exact Subgroup.subset_closure (by simp)
  obtain ⟨i', rfl⟩ := h3i
  rw [hij, zpow_mul, zpow_ofNat]
  exact Subgroup.mul_mem _ (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) i')
    (Subgroup.zpow_mem _ (Subgroup.subset_closure (by simp)) j)

theorem Sec11Data.wreath_or_closure_eq (h45 : Sec4.Item4_5) (h113 : Item113) {A : Subgroup G}
    {c : G} {L : Subgroup G} {a : G} {R Y : Subgroup G} {d x s r g : G}
    (h : Sec11Data G A c L a R Y d x s r g)
    (hcdN : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G))
    (hNd : Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hgV : g ∈ Subgroup.normalizer ((Subgroup.closure {s, x, a} : Subgroup G) : Set G)) :
    (∃ (K : Subgroup (sec11P R g)) (_ : K.Normal), Nonempty (sec11P R g ⧸ K ≃* W33)) ∨
      Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s} := by
  by_cases hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}
  · exact Or.inr hrs
  left
  set V := Subgroup.closure ({s, x} : Set G) with hV
  set V₃ := Subgroup.closure ({r ^ 3, x, s} : Set G) with hV₃
  obtain ⟨hrR, hxR, hsR⟩ := Item1116Proof.mem_R h
  have hRV := h.R_le_normalizer_V h45
  have hrN : r ∈ Subgroup.normalizer (V : Set G) := hRV hrR
  have haV₃ : a ∈ V₃ := h.mem_closure_pow_three_of_closure_ne h45 hrs
  have hsV₃ : s ∈ V₃ := Subgroup.subset_closure (by simp)
  have hxV₃ : x ∈ V₃ := Subgroup.subset_closure (by simp)
  have hr3V₃ : r ^ 3 ∈ V₃ := Subgroup.subset_closure (by simp)
  have hVV₃ : V ≤ V₃ := by
    rw [hV, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    exacts [hsV₃, hxV₃]
  have hsxaV₃ : Subgroup.closure ({s, x, a} : Set G) ≤ V₃ := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    exacts [hsV₃, hxV₃, haV₃]
  have hR : R = Subgroup.closure {r, x, s} := h.R_eq
  have hNV₃ : ∀ y, y ∈ Subgroup.normalizer (R : Set G) → y ∈ Subgroup.normalizer (V : Set G) →
      y ∈ Subgroup.normalizer (V₃ : Set G) := by
    intro y hyR hyV
    refine Item1123Proof.mem_normalizer_closure_pow_three hrN (hR ▸ hyR) ?_ ?_
    · exact hVV₃ ((Subgroup.mem_normalizer_iff.mp hyV s).mp (Subgroup.subset_closure (by simp)))
    · exact hVV₃ ((Subgroup.mem_normalizer_iff.mp hyV x).mp (Subgroup.subset_closure (by simp)))
  have hRV₃ : R ≤ Subgroup.normalizer (V₃ : Set G) := fun y hy =>
    hNV₃ y (Subgroup.le_normalizer hy) (hRV hy)
  have hgV₃ : g ∈ Subgroup.normalizer (V₃ : Set G) := by
    refine Item1123Proof.mem_normalizer_closure_pow_three hrN (hR ▸ h.g_mem_normalizer) ?_ ?_
    · exact hsxaV₃ ((Subgroup.mem_normalizer_iff.mp hgV s).mp (Subgroup.subset_closure (by simp)))
    · exact hsxaV₃ ((Subgroup.mem_normalizer_iff.mp hgV x).mp (Subgroup.subset_closure (by simp)))
  have hV₃P : V₃ ≤ sec11P R g := by
    rw [hV₃, Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact le_sup_left (a := R) (R.pow_mem hrR 3)
    · exact le_sup_left (a := R) hxR
    · exact le_sup_left (a := R) hsR
  have hgr : g * r * g⁻¹ * r⁻¹ ∈ V₃ := by
    have hgrR : g * r * g⁻¹ ∈ Subgroup.closure ({r, x, s} : Set G) :=
      hR ▸ (Subgroup.mem_normalizer_iff.mp h.g_mem_normalizer r).mp hrR
    obtain ⟨k, v, hv, he⟩ := Item1123Proof.exists_zpow_mul_of_mem_closure hrN hgrR
    refine Item1123Proof.conj_mul_inv_mem_of_pow_three_mem hgV₃ (hRV₃ hrR) hr3V₃ h.pow_eq_one
      (k := k) ?_
    rw [he, inv_mul_cancel_left]
    exact hVV₃ hv
  have hPT : sec11P R g ≤ Subgroup.closure {r, g, s, x} := by
    refine sup_le ?_ ?_
    · rw [hR, Subgroup.closure_le]
      rintro y (rfl | rfl | rfl) <;> exact Subgroup.subset_closure (by simp)
    · rw [Subgroup.zpowers_le]
      exact Subgroup.subset_closure (by simp)
  have hTN : ∀ y ∈ ({r, g, s, x} : Set G), y ∈ Subgroup.normalizer (V₃ : Set G) := by
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with rfl | rfl | rfl | rfl
    exacts [hRV₃ hrR, hgV₃, hRV₃ hsR, hRV₃ hxR]
  have hPP : ⁅sec11P R g, sec11P R g⁆ ≤ V₃ := by
    refine (Subgroup.commutator_mono hPT hPT).trans (commutator_closure_le ?_ ?_)
    · rw [Subgroup.closure_le]
      exact hTN
    · intro y hy z hz
      have hyN := hTN y hy
      have hzN := hTN z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy hz
      rcases hy with rfl | rfl | rfl | rfl
      · rcases hz with rfl | rfl | rfl | rfl
        · rw [commutatorElement_self]
          exact V₃.one_mem
        · have e : ⁅y, z⁆ = (z * y * z⁻¹ * y⁻¹)⁻¹ := by
            rw [commutatorElement_def]
            group
          rw [e]
          exact V₃.inv_mem hgr
        · exact commutator_mem_of_mem_right hyN hsV₃
        · exact commutator_mem_of_mem_right hyN hxV₃
      · rcases hz with rfl | rfl | rfl | rfl
        · rw [commutatorElement_def]
          exact hgr
        · rw [commutatorElement_self]
          exact V₃.one_mem
        · exact commutator_mem_of_mem_right hyN hsV₃
        · exact commutator_mem_of_mem_right hyN hxV₃
      · exact commutator_mem_of_mem_left hsV₃ hzN
      · exact commutator_mem_of_mem_left hxV₃ hzN
  have hNV : Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer (V₃ : Set G) := by
    rintro n ⟨hnH, hnP⟩
    have hnL := h.toSec11Std.normalizer_le_normalizer_L h45 hnH
    have hnR : n ∈ Subgroup.normalizer (R : Set G) := by
      have h1 := Subgroup.inf_normalizer_le_normalizer_inf ⟨hnP, Subgroup.le_normalizer hnL⟩
      rwa [h.inf_normalizer_L h45 h113] at h1
    exact hNV₃ n hnR (h.normalizer_P_le_normalizer_V h45 h113 ⟨hnH, hnP⟩)
  have hcen : ∀ n ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G), n * r * n⁻¹ * r⁻¹ ∈ V₃ :=
    fun n hn => hVV₃ (h.commutator_mem_V h45 h113 outAbelian1016 hrR n hn)
  have hrP : r ∈ sec11P R g := le_sup_left (a := R) hrR
  rcases rank3II_11_14_mem h hcdN hNd (h.htrans hcdN hNd) hV₃P hPP hNV hrP hcen with hW | hr
  · exact hW
  · exact absurd hr (Item1123Proof.not_mem_closure_pow_three
      (Item1116Proof.exists_pow_eq_one_of_mem h hrR) hrN h.r_not_mem_V)

end Data

section Main

@[expose] def Item1121N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers d : Set G) →
      ∀ (K : Subgroup (sec11P R g)) [K.Normal], IsEmpty (sec11P R g ⧸ K ≃* W33)

@[expose] def Item1123N : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer ((Subgroup.closure {c, d} : Subgroup G) : Set G) →
      Subgroup.normalizer ((sec11P R g : Subgroup G) : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers d : Set G) →
        Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}

theorem item1123N_of (h45 : Sec4.Item4_5) (h113 : Item113) (h1120 : Item1120)
    (h1121 : Item1121N) : Item1123N := by
  intro G _ _ A c L a R Y d x s r g h hcdN hNd
  have hgV := h1120 G A c L a R Y d x s r g h
    ((le_sup_right : Subgroup.zpowers g ≤ sec11P R g) (Subgroup.mem_zpowers g))
  rcases h.toSec11Data.wreath_or_closure_eq h45 h113 hcdN hNd hgV with ⟨K, hK, ⟨e⟩⟩ | hrs
  · exact ((h1121 G A c L a R Y d x s r g h hcdN hNd K).false e).elim
  · exact hrs

theorem sec11BigNever_of_item1123N (h113 : Item113) (h117 : Item117) (h1117 : Item1117)
    (h1119 : Item1119) (h1123 : Item1123N) (h1125 : Item1125) (hinv : Inverter1118) :
    Sec11BigNever := by
  intro G _ _ A c L a R Y d x s r g hbig
  obtain ⟨c₁, L₁, a₁, R₁, Y₁, x₁, s₁, r₁, g₁, hbig₁, hcdN⟩ :=
    h1119 G A c L a R Y d x s r g hbig
  have hNd := hbig₁.toSec11Data.normalizer_sec11P_le_normalizer_zpowers_d h113 h117 hcdN
  obtain ⟨a₂, Y₂, r₂, g₂, hbig₂, hP, j, hj, hjinv⟩ :=
    hinv G A c₁ L₁ a₁ R₁ Y₁ d x₁ s₁ r₁ g₁ hbig₁ hcdN hNd
  rw [← hP] at hcdN hNd
  have hrs := h1123 G A c₁ L₁ a₂ R₁ Y₂ d x₁ s₁ r₂ g₂ hbig₂ hcdN hNd
  have hsc : Subgroup.zpowers s₁ ≠ Subgroup.zpowers c₁ := by
    intro hsc
    have h9 := (h1117 G A c₁ L₁ a₂ R₁ Y₂ d x₁ s₁ r₂ g₂ hbig₂.toSec11Data hsc hrs).2
    have h9' := hbig₂.orderOf_x_gt
    omega
  exact h1125 G A c₁ L₁ a₂ R₁ Y₂ d x₁ s₁ r₂ g₂ hbig₂ hcdN hNd hsc hrs ⟨j, hj, hjinv⟩

theorem sec11BigNever_of_item1120 (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117)
    (h1117 : Item1117) (h1119 : Item1119) (h1120 : Item1120) (h1121 : Item1121N)
    (hinv : Inverter1118) : Sec11BigNever :=
  sec11BigNever_of_item1123N h113 h117 h1117 h1119 (item1123N_of h45 h113 h1120 h1121)
    (item1125_of h45 h113) hinv

theorem item1123_of (h45 : Sec4.Item4_5) (h113 : Item113) (h117 : Item117) (h1117 : Item1117)
    (h1119 : Item1119) (h1120 : Item1120) (h1121 : Item1121N) (hinv : Inverter1118) :
    Item1123 := fun G _ _ A c L a R Y d x s r g h =>
  (sec11BigNever_of_item1120 h45 h113 h117 h1117 h1119 h1120 h1121 hinv
    G A c L a R Y d x s r g h).elim

end Main

end CFSG.RankThree.PartTwo.Sec11
