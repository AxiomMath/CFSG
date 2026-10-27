module

public import CFSG.LocalAnalysis.StandardType.GGF4N2Calibration
public import CFSG.LocalAnalysis.StandardType.GGF4N2JModelExclusions
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRestGen
import CFSG.ClassicalInvolution.Phan.Blocks
import CFSG.LocalAnalysis.StandardType.GGF4N2MixedPower

public section

namespace CFSG.StandardType.F4Over

open Multiplicative SpCoord CFSG.Open CFSG.StandardType.N2KCoordinate
  CFSG.SeitzReduction.LinearPilot CFSG.LocalAnalysis.ComponentInitial.LinearFlag

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def bA (k : Fin 4) : Fin 6 := ⟨2 * (k.val % 3), by omega⟩

@[expose] def bB (k : Fin 4) : Fin 6 := ⟨2 * (k.val % 3) + 1, by omega⟩

theorem bA_ne_bB (k : Fin 4) : bA k ≠ bB k := by
  intro h
  have := congrArg Fin.val h
  simp only [bA, bB] at this
  omega

@[expose] noncomputable def blk (k : Fin 4) : SL2F4 →* SL6F4 := pairEmbed (K := F4) (bA_ne_bB k)

theorem blk_two : blk 2 = coordBlock45 := rfl

@[expose] def blkSwap (a b : Fin 4) : Equiv.Perm (Fin 6) :=
  Equiv.swap (bA a) (bA b) * Equiv.swap (bB a) (bB b)

theorem blkSwap_inv : ∀ a b : Fin 4, (blkSwap a b)⁻¹ = blkSwap a b := by decide

theorem blkSwap_bA : ∀ a b k : Fin 4, a ≠ 3 → b ≠ 3 → k ≠ 3 →
    blkSwap a b (bA k) = bA (Equiv.swap a b k) := by decide

theorem blkSwap_bB : ∀ a b k : Fin 4, a ≠ 3 → b ≠ 3 → k ≠ 3 →
    blkSwap a b (bB k) = bB (Equiv.swap a b k) := by decide

theorem blk_disjoint : ∀ i k : Fin 4, i ≠ 3 → k ≠ 3 → i ≠ k →
    Disjoint ({bA i, bB i} : Finset (Fin 6)) {bA k, bB k} := by decide

theorem pairEmbed_eq_of_eq {a b a' b' : Fin 6} (hab : a ≠ b) (hab' : a' ≠ b') (ha : a = a')
    (hb : b = b') (A : SL2F4) : pairEmbed (K := F4) hab A = pairEmbed (K := F4) hab' A := by
  subst ha
  subst hb
  rfl

theorem blk_mem (k : Fin 4) (A : SL2F4) : blk k A ∈ blockSpecialLinear {bA k, bB k} := by
  rw [← range_pairEmbed (K := F4) (bA_ne_bB k)]
  exact ⟨A, rfl⟩

theorem blk_commute {i k : Fin 4} (hi : i ≠ 3) (hk : k ≠ 3) (hik : i ≠ k) (A B : SL2F4) :
    Commute (blk i A) (blk k B) :=
  commute_blockSpecialLinear_of_disjoint (blk_disjoint i k hi hk hik) (blk_mem i A) (blk_mem k B)

theorem blk_conj {a b k : Fin 4} (ha : a ≠ 3) (hb : b ≠ 3) (hk : k ≠ 3) (A : SL2F4) :
    signedPermutation 6 F4 (blkSwap a b) * blk k A * (signedPermutation 6 F4 (blkSwap a b))⁻¹ =
      blk (Equiv.swap a b k) A := by
  rw [← MulAut.conj_apply, blk, signedPermutation_conj_pairEmbed _ (blkSwap_inv a b)
    (bA_ne_bB k) A]
  exact pairEmbed_eq_of_eq _ _ (blkSwap_bA a b k ha hb hk) (blkSwap_bB a b k ha hb hk) A

theorem val_lt_three_of_ne {k : Fin 4} (hk : k ≠ 3) : k.val < 3 := by
  have h4 := k.2
  have h3 : k.val ≠ 3 := fun h => hk (Fin.ext h)
  omega

theorem mem_blk_pair_iff {k : Fin 4} (hk : k ≠ 3) (r : Fin 6) :
    r ∈ ({bA k, bB k} : Finset (Fin 6)) ↔ 2 * k.val ≤ r.val ∧ r.val < 2 * k.val + 2 := by
  have hk3 := val_lt_three_of_ne hk
  have hbA : (bA k).val = 2 * k.val := by
    show 2 * (k.val % 3) = 2 * k.val
    rw [Nat.mod_eq_of_lt hk3]
  have hbB : (bB k).val = 2 * k.val + 1 := by
    show 2 * (k.val % 3) + 1 = 2 * k.val + 1
    rw [Nat.mod_eq_of_lt hk3]
  rw [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, Fin.ext_iff, hbA, hbB]
  omega

theorem blockSL2_eq_blk {k : Fin 4} (hk : k ≠ 3) (h : 2 * k.val < 5) (A : SL2F4) :
    CFSG.ClassicalInvolution.WeakCT.blockSL2 F4 5 ⟨2 * k.val, h⟩ A = blk k A := by
  have hk3 := val_lt_three_of_ne hk
  have hbA : (bA k).val = 2 * k.val := by
    show 2 * (k.val % 3) = 2 * k.val
    rw [Nat.mod_eq_of_lt hk3]
  have hidx : ∀ (s : Fin 6), (2 * k.val ≤ s.val ∧ s.val < 2 * k.val + 2) →
      ∀ (h' : s.val - 2 * k.val < 2),
        (⟨s.val - 2 * k.val, h'⟩ : Fin 2) = if s = bA k then 0 else 1 := by
    intro s hs h'
    by_cases h0 : s = bA k
    · rw [if_pos h0]
      apply Fin.ext
      have : s.val = 2 * k.val := by rw [h0, hbA]
      show s.val - 2 * k.val = 0
      omega
    · rw [if_neg h0]
      apply Fin.ext
      have : s.val ≠ 2 * k.val := fun h => h0 (Fin.ext (by rw [h, hbA]))
      show s.val - 2 * k.val = 1
      omega
  apply Subtype.ext
  ext r c
  change CFSG.ClassicalInvolution.Phan.blockMat 6 (2 * k.val) (A : Matrix (Fin 2) (Fin 2) F4) r c =
    (pairEmbed (K := F4) (bA_ne_bB k) A : Matrix (Fin 6) (Fin 6) F4) r c
  rw [CFSG.ClassicalInvolution.Phan.blockMat_apply, pairEmbed_apply]
  have hr := mem_blk_pair_iff hk r
  have hc := mem_blk_pair_iff hk c
  by_cases hrc : (2 * k.val ≤ r.val ∧ r.val < 2 * k.val + 2) ∧
      (2 * k.val ≤ c.val ∧ c.val < 2 * k.val + 2)
  · rw [dif_pos hrc, if_pos ⟨hr.2 hrc.1, hc.2 hrc.2⟩, hidx r hrc.1, hidx c hrc.2]
  · rw [dif_neg hrc, if_neg (fun h => hrc ⟨hr.1 h.1, hc.1 h.2⟩)]

section Chart

variable {G : Type} [Group G] [Finite G]

theorem exists_ggConjAut_eq_of_apply_coord {Bs : Subgroup G} (κ : V5 ≃* ↥Bs) {φ : MulAut ↥Bs}
    {h : G} (hφ : ∀ k, ((φ (κ (e5 k)) : ↥Bs) : G) = h * ((κ (e5 k) : ↥Bs) : G) * h⁻¹) :
    ∃ hN : h ∈ Subgroup.normalizer (Bs : Set G), ggConjAut Bs hN = φ := by
  have hext : Bs.subtype.comp (φ.toMonoidHom.comp κ.toMonoidHom) =
      (MulAut.conj h).toMonoidHom.comp (Bs.subtype.comp κ.toMonoidHom) :=
    hom_ext_mulSingle fun k => hφ k
  have hall : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = h * b * h⁻¹ := fun b => by
    have := DFunLike.congr_fun hext (κ.symm b)
    simpa using this
  have hN : h ∈ Subgroup.normalizer (Bs : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨b, hb, rfl⟩
      change h * b * h⁻¹ ∈ Bs
      rw [← hall ⟨b, hb⟩]
      exact (φ ⟨b, hb⟩).2
    · rw [Subgroup.card_map_of_injective (MulAut.conj h).injective]
  exact ⟨hN, MulEquiv.ext fun b => Subtype.ext (hall b).symm⟩

theorem mem_ggAutomizer_of_apply_coord {H Bs : Subgroup G} (κ : V5 ≃* ↥Bs) {φ : MulAut ↥Bs}
    {h : G} (hH : h ∈ H)
    (hφ : ∀ k, ((φ (κ (e5 k)) : ↥Bs) : G) = h * ((κ (e5 k) : ↥Bs) : G) * h⁻¹) :
    φ ∈ ggAutomizer H Bs := by
  obtain ⟨hN, hφN⟩ := exists_ggConjAut_eq_of_apply_coord κ hφ
  rw [← hφN]
  exact ggConjAut_mem_ggAutomizer hH hN

theorem exists_ggConjAut_eq_permAut {Bs : Subgroup G} (κ : V5 ≃* ↥Bs) (σ : Equiv.Perm (Fin 4))
    {ν : G} (hν : ∀ k, ν * ((κ (e5 k) : ↥Bs) : G) * ν⁻¹ = ((κ (e5 (σ k)) : ↥Bs) : G)) :
    ∃ hN : ν ∈ Subgroup.normalizer (Bs : Set G),
      ggConjAut Bs hN = MulAut.congr κ (permAut σ) :=
  exists_ggConjAut_eq_of_apply_coord κ fun k => by rw [congr_permAut_apply, hν]

theorem permAut_one : (permAut 1 : MulAut V5) = 1 :=
  MulEquiv.ext fun f => by rw [permAut_apply, inv_one]; rfl

theorem ggF4_calibration_C1 {Bs K : Subgroup G} (ψ₁ : SL6F4 →* G) (hK : ψ₁.range = K)
    (κ : V5 ≃* ↥Bs) {t a : SL2F4} (hat : a * t * a⁻¹ = t⁻¹)
    (hn : ∀ k : Fin 4, k ≠ 3 → ((κ (e5 k) : ↥Bs) : G) = ψ₁ (blk k t))
    (h3 : ((κ (e5 3) : ↥Bs) : G) ∈ Subgroup.centralizer (K : Set G)) :
    (∀ i : Fin 4, i ≠ 3 → MulAut.congr κ (sgnAut i) ∈ ggAutomizer K Bs) ∧
      ∀ a b : Fin 4, a ≠ 3 → b ≠ 3 →
        MulAut.congr κ (permAut (Equiv.swap a b)) ∈ ggAutomizer K Bs := by
  have hK' : ∀ M, ψ₁ M ∈ K := fun M => hK ▸ ⟨M, rfl⟩
  have hfix3 : ∀ M, ψ₁ M * ((κ (e5 3) : ↥Bs) : G) * (ψ₁ M)⁻¹ = ((κ (e5 3) : ↥Bs) : G) := by
    intro M
    rw [(Subgroup.mem_centralizer_iff.mp h3) _ (hK' M), mul_inv_cancel_right]
  have hconj : ∀ M N, ψ₁ M * ψ₁ N * (ψ₁ M)⁻¹ = ψ₁ (M * N * M⁻¹) := fun M N => by
    rw [map_mul, map_mul, map_inv]
  refine ⟨fun i hi => mem_ggAutomizer_of_apply_coord κ (hK' (blk i a)) fun k => ?_,
    fun b c hb hc => ?_⟩
  · rw [congr_sgnAut_apply]
    by_cases hk3 : k = 3
    · subst hk3
      rw [if_neg (Ne.symm hi), hfix3]
    · rw [hn k hk3, hconj]
      by_cases hki : k = i
      · subst hki
        have hM : blk k a * blk k t * (blk k a)⁻¹ = (blk k t)⁻¹ := by
          rw [← map_inv (blk k) a, ← map_mul, ← map_mul, hat, map_inv]
        rw [if_pos rfl, Subgroup.coe_inv, hn k hk3, hM, map_inv]
      · rw [if_neg hki, hn k hk3, (blk_commute hi hk3 (Ne.symm hki) a t).eq, mul_inv_cancel_right]
  · by_cases hbc : b = c
    · subst hbc
      rw [Equiv.swap_self, show (Equiv.refl (Fin 4) : Equiv.Perm (Fin 4)) = 1 from rfl, permAut_one,
        map_one]
      exact Subgroup.one_mem _
    · refine mem_ggAutomizer_of_apply_coord κ (hK' (signedPermutation 6 F4 (blkSwap b c)))
        fun k => ?_
      rw [congr_permAut_apply]
      by_cases hk3 : k = 3
      · subst hk3
        rw [Equiv.swap_apply_of_ne_of_ne (Ne.symm hb) (Ne.symm hc), hfix3]
      · have hsk : Equiv.swap b c k ≠ 3 := by
          intro h
          have h' := congrArg (Equiv.swap b c) h
          rw [Equiv.swap_apply_self, Equiv.swap_apply_of_ne_of_ne (Ne.symm hb) (Ne.symm hc)] at h'
          exact hk3 h'
        rw [hn _ hsk, hn k hk3, hconj, blk_conj hb hc hk3]

theorem exists_coord_native {Bs K : Subgroup G} (hEl : IsElemAbelian 5 Bs) (ψ₁ : SL6F4 →* G)
    (hBsK : Bs ⊓ K = coordinateTorus.map ψ₁) {y n₃ : G}
    (hBs : Bs = Subgroup.zpowers y ⊔ (Bs ⊓ K)) (hn₃ : Subgroup.zpowers n₃ = Subgroup.zpowers y)
    (hcard : Nat.card Bs = 5 ^ 4) :
    ∃ κ : V5 ≃* ↥Bs, (∀ k : Fin 4, k ≠ 3 → ((κ (e5 k) : ↥Bs) : G) = ψ₁ (blk k coordA2)) ∧
      ((κ (e5 3) : ↥Bs) : G) = n₃ := by
  let n : Fin 4 → G := ![ψ₁ (blk 0 coordA2), ψ₁ (blk 1 coordA2), ψ₁ (blk 2 coordA2), n₃]
  have hTB : coordinateTorus.map ψ₁ ≤ Bs := by
    rw [← hBsK]
    exact inf_le_left
  have hn3B : n₃ ∈ Bs := by
    rw [hBs]
    refine Subgroup.mem_sup_left ?_
    rw [← hn₃]
    exact Subgroup.mem_zpowers n₃
  have h0 : blk 0 coordA2 ∈ coordinateTorus := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
  have h1 : blk 1 coordA2 ∈ coordinateTorus :=
    Subgroup.mem_sup_right (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
  have h2 : blk 2 coordA2 ∈ coordinateTorus :=
    Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hnB : ∀ k, n k ∈ Bs := by
    intro k
    fin_cases k
    · exact hTB (Subgroup.mem_map_of_mem ψ₁ h0)
    · exact hTB (Subgroup.mem_map_of_mem ψ₁ h1)
    · exact hTB (Subgroup.mem_map_of_mem ψ₁ h2)
    · exact hn3B
  have hle : ∀ k, Subgroup.zpowers (n k) ≤ ⨆ j, Subgroup.zpowers (n j) := fun k =>
    le_iSup (fun j => Subgroup.zpowers (n j)) k
  have hgen : Bs ≤ ⨆ k, Subgroup.zpowers (n k) := by
    rw [hBs, hBsK, ← hn₃, coordinateTorus_eq_blocks, Subgroup.map_sup, Subgroup.map_sup,
      MonoidHom.map_zpowers, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    exact sup_le (hle 3) (sup_le (hle 0) (sup_le (hle 1) (hle 2)))
  obtain ⟨κ, hκ⟩ := exists_coord hEl n hnB hgen hcard
  refine ⟨κ, fun k hk => ?_, hκ 3⟩
  rw [hκ k]
  fin_cases k
  · rfl
  · rfl
  · rfl
  · exact absurd rfl hk

theorem swap_mem_zpowers {Bs L : Subgroup G} {x g y v n₃ nₘ : G}
    (hBsL : Bs = Subgroup.zpowers x ⊔ (Bs ⊓ L)) (hgx : g * x * g⁻¹ = x)
    (hinv : ∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹) (hyB : y ∈ Bs)
    (hgy : g * y * g⁻¹ ∈ Subgroup.zpowers v) (hyo : orderOf y = 5) (hvo : orderOf v = 5)
    (hn₃ : Subgroup.zpowers n₃ = Subgroup.zpowers y)
    (hnₘ : Subgroup.zpowers nₘ = Subgroup.zpowers v) :
    g * nₘ * g⁻¹ ∈ Subgroup.zpowers n₃ ∧ g * n₃ * g⁻¹ ∈ Subgroup.zpowers nₘ := by
  have hg2 : Bs ≤ Subgroup.centralizer ({g * g} : Set G) := by
    rw [hBsL]
    refine sup_le (Subgroup.zpowers_le.2 ?_) fun b hb => ?_
    · have h : g * g * x = x * (g * g) := by
        calc g * g * x = g * (g * x * g⁻¹) * g⁻¹ * (g * g) := by group
          _ = x * (g * g) := by rw [hgx, hgx]
      rw [Subgroup.mem_centralizer_singleton_iff]
      first | exact h | exact h.symm
    · have hb' : g * b⁻¹ * g⁻¹ = b := by
        rw [show g * b⁻¹ * g⁻¹ = (g * b * g⁻¹)⁻¹ by group, hinv b hb, inv_inv]
      have h : g * g * b = b * (g * g) := by
        calc g * g * b = g * (g * b * g⁻¹) * g⁻¹ * (g * g) := by group
          _ = b * (g * g) := by rw [hinv b hb, hb']
      rw [Subgroup.mem_centralizer_singleton_iff]
      first | exact h | exact h.symm
  have hgy2 : g * (g * y * g⁻¹) * g⁻¹ = y := by
    have h := Subgroup.mem_centralizer_singleton_iff.1 (hg2 hyB)
    have h' : g * g * y = y * (g * g) := by first | exact h | exact h.symm
    calc g * (g * y * g⁻¹) * g⁻¹ = (g * g) * y * (g * g)⁻¹ := by group
      _ = y := by rw [h', mul_inv_cancel_right]
  have hzv : Subgroup.zpowers (g * y * g⁻¹) = Subgroup.zpowers v := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hgy) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hvo, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hyo]
  constructor
  · have hm : nₘ ∈ Subgroup.zpowers (g * y * g⁻¹) := by
      rw [hzv, ← hnₘ]
      exact Subgroup.mem_zpowers nₘ
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hm
    rw [hn₃, ← MulAut.conj_apply, map_zpow, MulAut.conj_apply, hgy2]
    exact Subgroup.zpow_mem_zpowers y j
  · have hm : n₃ ∈ Subgroup.zpowers y := by
      rw [← hn₃]
      exact Subgroup.mem_zpowers n₃
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hm
    rw [hnₘ, ← hzv, ← MulAut.conj_apply g (y ^ j), map_zpow]
    exact Subgroup.zpow_mem_zpowers (g * y * g⁻¹) j

end Chart

section Frame

theorem ggF4N2_mixed_native_frame {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {Rd Ra : Prop} (hR : GGSecFiveRestGen 5 B Bs x L D J Rd Ra)
    (hNbr : GGNbr 5 B x D J y K) (hL : GGCentralImage .POmegaMinus 4 2 L)
    (hK : GGCentralImage .PSL 6 2 K) {ψ₁ : SL6F4 →* G} (h₁ : ψ₁.ker ≤ Subgroup.center _)
    (hK₁ : ψ₁.range = K) {g : G} (hinv : ∀ b ∈ Bs ⊓ L, g * b * g⁻¹ = b⁻¹)
    (hxg : g * x * g⁻¹ = x) {rho : Bs →* SL6F4} (hTor : rho.range = coordinateTorus)
    (hRhoKer : rho.ker = (Subgroup.zpowers y).subgroupOf Bs)
    (hT45 : ∀ hx : x ∈ Bs, rho ⟨x, hx⟩ ∈ coordT45) (hPow : ∀ b : Bs, rho b ^ 5 = 1)
    (hPoint : ∀ (b : Bs) (k : G), k ∈ K → ψ₁ (rho b) * k * (ψ₁ (rho b))⁻¹ = b * k * b⁻¹)
    (hRangeK : (ψ₁.comp rho).range = Bs ⊓ K) {v : G} (hvDK : v ∈ D ⊓ K) (hvo : orderOf v = 5)
    (hDyv : D = Subgroup.zpowers y ⊔ Subgroup.zpowers v) (hgy : g * y * g⁻¹ ∈ Subgroup.zpowers v)
    {n₃ : G} (hn₃ : Subgroup.zpowers n₃ = Subgroup.zpowers y) :
    ∃ κ : V5 ≃* ↥Bs, (∀ k : Fin 4, k ≠ 3 → ((κ (e5 k) : ↥Bs) : G) = ψ₁ (blk k coordA2)) ∧
      ((κ (e5 3) : ↥Bs) : G) = n₃ ∧
      (∀ i : Fin 4, i ≠ 3 → MulAut.congr κ (sgnAut i) ∈ ggAutomizer K Bs) ∧
      (∀ a b : Fin 4, a ≠ 3 → b ≠ 3 →
        MulAut.congr κ (permAut (Equiv.swap a b)) ∈ ggAutomizer K Bs) ∧
      Subgroup.zpowers ((κ (e5 2) : ↥Bs) : G) = Subgroup.zpowers v ∧
      g * ((κ (e5 2) : ↥Bs) : G) * g⁻¹ ∈ Subgroup.zpowers ((κ (e5 3) : ↥Bs) : G) ∧
      g * ((κ (e5 3) : ↥Bs) : G) * g⁻¹ ∈ Subgroup.zpowers ((κ (e5 2) : ↥Bs) : G) ∧
      x ∈ Bs ∧ x ≠ 1 ∧
      x ∈ Subgroup.zpowers ((κ (e5 2) : ↥Bs) : G) ⊔ Subgroup.zpowers ((κ (e5 3) : ↥Bs) : G) := by
  have hEl : IsElemAbelian 5 Bs := hR.1.2.1.2.1
  obtain ⟨hxBs, hxy, hyo, hDxy, -, -⟩ := ggF4N2_x_data hR hNbr
  have hBs : Bs = Subgroup.zpowers y ⊔ (Bs ⊓ K) := (ggF4N2_exists_actual_torus_data hR hNbr hL hK).1
  have hyBs : y ∈ Bs := by
    rw [hBs]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers y)
  have hBsK : Bs ⊓ K = coordinateTorus.map ψ₁ := by
    rw [← hRangeK, MonoidHom.range_comp, hTor]
  obtain ⟨κ, hκ, hκ3⟩ := exists_coord_native hEl ψ₁ hBsK hBs hn₃ (ggF4N2Rank hR hL).1
  have hyC : Subgroup.zpowers y ≤ Subgroup.centralizer (K : Set G) := by
    rw [← inf_centralizer_eq_zpowers_of_sHat hNbr.1]
    exact inf_le_right
  have h3C : ((κ (e5 3) : ↥Bs) : G) ∈ Subgroup.centralizer (K : Set G) := by
    rw [hκ3]
    refine hyC ?_
    rw [← hn₃]
    exact Subgroup.mem_zpowers n₃
  obtain ⟨a, ha⟩ := CFSG.RankThree.PartOne.KF132.exists_inv_conj_sl2 coordA2
  have hC1 := ggF4_calibration_C1 ψ₁ hK₁ κ ha hκ h3C
  have hDBs : D ≤ Bs := by
    rw [hDxy, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hxBs
    · exact hyBs
  have hρy : rho ⟨y, hyBs⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hRhoKer, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers y
  have hρD : D ≤ (coordT45.comap rho).map Bs.subtype := by
    rw [hDxy, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨⟨_, hxBs⟩, hT45 hxBs, rfl⟩
    · refine ⟨⟨_, hyBs⟩, ?_, rfl⟩
      change rho ⟨_, hyBs⟩ ∈ coordT45
      rw [hρy]
      exact Subgroup.one_mem _
  have hK' : ∀ M, ψ₁ M ∈ K := fun M => hK₁ ▸ ⟨M, rfl⟩
  have hsurj : Function.Surjective (ψ₁.codRestrict K hK') := by
    intro k
    obtain ⟨M, hM⟩ : (k : G) ∈ ψ₁.range := hK₁ ▸ k.2
    exact ⟨M, Subtype.ext hM⟩
  have hker : (ψ₁.codRestrict K hK').ker ≤ Subgroup.center _ := by
    rw [MonoidHom.ker_codRestrict]
    exact h₁
  obtain ⟨b, hbT, hbv⟩ := hρD hvDK.1
  have hv5 : v ^ 5 = 1 := by
    rw [← hvo]
    exact pow_orderOf_eq_one v
  have hψv : ψ₁ (rho b) = v := by
    have h := psi_rho_eq_of_conj (ψ₁.codRestrict K hK') hsurj hker rho
      (fun b k => hPoint b k k.2) hPow (b := b) (by rw [← hbv] at hvDK; exact hvDK.2)
      (by rw [← hbv] at hv5; exact hv5)
    rw [← hbv]
    exact h
  have hvn : v ∈ Subgroup.zpowers ((κ (e5 2) : ↥Bs) : G) := by
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_comap.1 hbT)
    rw [← hψv, ← hj, map_zpow, ← blk_two, ← hκ 2 (by decide)]
    exact Subgroup.zpow_mem_zpowers _ j
  have hz2 : Subgroup.zpowers ((κ (e5 2) : ↥Bs) : G) = Subgroup.zpowers v := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hvn) ?_).symm
    rw [Nat.card_zpowers, Nat.card_zpowers, hvo]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hEl.2 _ (κ (e5 2)).2))
  have hz3 : Subgroup.zpowers ((κ (e5 3) : ↥Bs) : G) = Subgroup.zpowers y := by
    rw [hκ3, hn₃]
  have hsw := swap_mem_zpowers (ggF4N2Bstar_split hR hL).1 hxg hinv hyBs hgy hyo hvo hz3 hz2
  have hxD : x ∈ D := by
    rw [hDxy]
    exact Subgroup.subset_closure (Set.mem_insert x _)
  rw [hDyv, sup_comm] at hxD
  refine ⟨κ, hκ, hκ3, hC1.1, hC1.2, hz2, hsw.1, hsw.2, hxBs,
    fun h => hxy (by rw [h]; exact Subgroup.one_mem _), ?_⟩
  rwa [hz2, hz3]

end Frame

end CFSG.StandardType.F4Over

end
