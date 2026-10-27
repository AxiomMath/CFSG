module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameUDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDefs
public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompSUTwo
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr
public import CFSG.LocalAnalysis.StandardType.GGSpFrameConfig
public import CFSG.LocalAnalysis.StandardType.GGSpJoinLeviCount

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover
open scoped BigOperators

variable {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

omit [Finite G] in
private theorem ggQTUn_centralizer_inv (y : G) :
    Subgroup.centralizer ({y⁻¹} : Set G) = Subgroup.centralizer ({y} : Set G) := by
  ext g
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have key : ∀ a : G, g * a = a * g → g * a⁻¹ = a⁻¹ * g := by
    intro a ha
    have h2 : a * g⁻¹ = g⁻¹ * a := by
      calc a * g⁻¹ = g⁻¹ * (g * a) * g⁻¹ := by group
        _ = g⁻¹ * (a * g) * g⁻¹ := by rw [ha]
        _ = g⁻¹ * a := by group
    calc g * a⁻¹ = (a * g⁻¹)⁻¹ := by group
      _ = (g⁻¹ * a)⁻¹ := by rw [h2]
      _ = a⁻¹ * g := by group
  exact ⟨fun h => by simpa using key y⁻¹ h, key y⟩

omit [Finite G] in
private theorem ggQTUn_closure_pair_inv (x y : G) :
    Subgroup.closure ({x, y⁻¹} : Set G) = Subgroup.closure ({x, y} : Set G) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    refine Set.insert_subset ?_ ?_
    · exact Subgroup.subset_closure (by simp)
    · have hy : y ∈ Subgroup.closure ({x, y} : Set G) := Subgroup.subset_closure (by simp)
      simpa using (Subgroup.closure ({x, y} : Set G)).inv_mem hy
  · rw [Subgroup.closure_le]
    refine Set.insert_subset ?_ ?_
    · exact Subgroup.subset_closure (by simp)
    · have hy : y⁻¹ ∈ Subgroup.closure ({x, y⁻¹} : Set G) := Subgroup.subset_closure (by simp)
      simpa using (Subgroup.closure ({x, y⁻¹} : Set G)).inv_mem hy

private theorem ggQTUn_sHat_inv {p : ℕ} {y : G} {K : Subgroup G}
    (h : LargeEvenSHat p B y K) : LargeEvenSHat p B y⁻¹ K := by
  have hz : Subgroup.zpowers y⁻¹ = Subgroup.zpowers y := Subgroup.zpowers_inv
  have hc := ggQTUn_centralizer_inv y
  unfold LargeEvenSHat at h ⊢
  obtain ⟨hBmax, hyB, hy1, hKC, hPC, hiff⟩ := h
  refine ⟨hBmax, ?_, ?_, ?_, ?_, ?_⟩
  · rwa [inv_mem_iff]
  · intro h
    exact hy1 (inv_eq_one.mp h)
  · rwa [hc]
  · rwa [hc]
  · intro b
    rw [hz]
    exact hiff b

omit [Finite G] in
private theorem ggQTUn_neighbor_inv {p : ℕ} {y : G} {K : Subgroup G}
    (h : LargeEvenNeighbor p x y K D J) : LargeEvenNeighbor p x y⁻¹ K D J := by
  have hc := ggQTUn_centralizer_inv y
  have hcl := ggQTUn_closure_pair_inv x y
  unfold LargeEvenNeighbor at h ⊢
  obtain ⟨hD, hlayer, hcomm⟩ := h
  refine ⟨?_, ?_, hcomm⟩
  · rw [hD, hcl]
  · rwa [hc]

theorem GGNbr.inv {p : ℕ} {y : G} {K : Subgroup G} (h : GGNbr p B x D J y K) :
    GGNbr p B x D J y⁻¹ K := by
  unfold GGNbr at h ⊢
  exact ⟨ggQTUn_sHat_inv h.1, ggQTUn_neighbor_inv h.2⟩

private theorem ggQTUn_nbr_facts {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hnbr : GGNbr p B x D J y K) :
    y ∈ Bs ∧ y ∈ Subgroup.centralizer (K : Set G) ∧ y ∈ D ∧
      y ∉ Subgroup.zpowers x ∧ x ≠ 1 := by
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hxD : x ∈ D := hcfg.2.2.1.2.2.2.1
  have hDcard : Nat.card D = p ^ 2 := hcfg.2.2.1.2.2.1
  have hDab : IsElemAbelian p D := hcfg.2.2.1.2.1
  have hyK : y ∈ Subgroup.centralizer (K : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mp (hnbr.1.2.2.2.1 hk)
  refine ⟨hcfg.2.1.1 hnbr.1.2.1, hyK, ?_, ?_, hS.2.2.1⟩
  · rw [hnbr.2.1]
    exact Subgroup.subset_closure (by simp)
  · intro hy
    have hD_le : D ≤ Subgroup.zpowers x := by
      rw [hnbr.2.1, Subgroup.closure_le]
      rintro z (rfl | rfl)
      · exact Subgroup.mem_zpowers _
      · exact hy
    have hzp_le : Subgroup.zpowers x ≤ D := Subgroup.zpowers_le.mpr hxD
    have hD_eq : D = Subgroup.zpowers x := le_antisymm hD_le hzp_le
    have hxp : x ^ p = 1 := hDab.2 x hxD
    have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one hxp
    have horder : orderOf x = p ^ 2 := by
      rw [← Nat.card_zpowers, ← hD_eq, hDcard]
    have hp2dvd : p ^ 2 ∣ p := by
      rw [← horder]
      exact hdvd
    have hp2le : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hp2dvd
    nlinarith [hp.two_le]

private theorem ggQTUn_x_not_mem_centralizer {p : ℕ} {B : Subgroup G} {x : G}
    {D J : Subgroup G} {y : G} {K : Subgroup G} (hnbr : GGNbr p B x D J y K) :
    x ∉ Subgroup.centralizer (K : Set G) := by
  intro hx
  apply hnbr.2.2.2
  have hz : Subgroup.zpowers x ≤ Subgroup.centralizer (K : Set G) :=
    Subgroup.zpowers_le.mpr hx
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hz)]
  exact bot_le

omit [Finite G] in
private theorem ggQTUn_mem_suPairs {X L : Subgroup G} {x : G} {n : ℕ} {K : Type}
    [Field K] [Finite K] (C : GGQTwoXInLUCoord Bs X L x n K) {b : G} (hb : b ∈ Bs) :
    (b, diagHom (n + 1)
        (fun i => C.ω ^ ((C.ι (Additive.ofMul ⟨b, hb⟩) : Fin (n + 1) → ZMod 3) i).val)) ∈
      SUTorus.suPairs C.φ := by
  obtain ⟨t, htmat, htφ⟩ := C.diag ⟨b, hb⟩
  rw [SUTorus.mem_suPairs]
  refine ⟨?_, ?_⟩
  · rw [← htmat]
    exact Subgroup.le_normalizer t.2
  · intro u v hv
    have hv' : v = t * u * t⁻¹ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      calc (v : GL (Fin (n + 1)) K)
          = diagHom (n + 1) (fun i =>
              C.ω ^ ((C.ι (Additive.ofMul ⟨b, hb⟩) : Fin (n + 1) → ZMod 3) i).val) *
              (u : GL (Fin (n + 1)) K) *
              (diagHom (n + 1) (fun i =>
                C.ω ^ ((C.ι (Additive.ofMul ⟨b, hb⟩) : Fin (n + 1) → ZMod 3) i).val))⁻¹ := hv
        _ = (t : GL (Fin (n + 1)) K) * (u : GL (Fin (n + 1)) K) *
              (t : GL (Fin (n + 1)) K)⁻¹ := by rw [htmat]
    rw [hv', map_mul, map_mul, map_inv, htφ]

private theorem ggQTUn_coord_add {n : ℕ} (hn3 : 3 ∣ n) (hn6 : 6 ≤ n)
    {f : Fin (n + 1) → ZMod 3}
    (hconst : ∀ i j, i ≠ 0 → i ≠ 1 → j ≠ 0 → j ≠ 1 → f i = f j)
    (hsum : ∑ i, f i = 0) :
    ∀ i2 : Fin (n + 1), i2 ≠ 0 → i2 ≠ 1 → f i2 = f 0 + f 1 := by
  classical
  intro i2 hi2ne0 hi2ne1
  set T : Finset (Fin (n + 1)) := (Finset.univ.erase 0).erase 1 with hT
  have hsum0 : (∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), f i) + f 0 = ∑ i, f i :=
    Finset.sum_erase_add (s := Finset.univ) (f := f) (a := 0) (Finset.mem_univ 0)
  have hmem1 : (1 : Fin (n + 1)) ∈ Finset.univ.erase 0 := by
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ 1⟩
    intro h
    have hv : (1 : Fin (n + 1)).val = (0 : Fin (n + 1)).val := congrArg Fin.val h
    rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega : 1 < n + 1)] at hv
    omega
  have hsum1 : (∑ i ∈ T, f i) + f 1 = ∑ i ∈ Finset.univ.erase (0 : Fin (n + 1)), f i := by
    rw [hT]
    exact Finset.sum_erase_add (s := Finset.univ.erase 0) (f := f) (a := 1) hmem1
  have hsplit : ∑ i, f i = f 0 + f 1 + ∑ i ∈ T, f i := by
    rw [← hsum0, ← hsum1]
    ring
  have hTcard : T.card = n - 1 := by
    rw [hT]
    rw [Finset.card_erase_of_mem hmem1]
    rw [Finset.card_erase_of_mem (Finset.mem_univ 0)]
    simp
  have hTval : ∀ i ∈ T, f i = f i2 := by
    intro i hi
    rw [hT] at hi
    simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hi
    exact hconst i i2 hi.2 hi.1 hi2ne0 hi2ne1
  have hTsum : ∑ i ∈ T, f i = T.card • f i2 := by
    rw [Finset.sum_congr rfl hTval, Finset.sum_const]
  rw [hsplit, hTsum, hTcard] at hsum
  have hncast : (n : ZMod 3) = 0 := by
    obtain ⟨k, hk⟩ := hn3
    have h3 : (3 : ZMod 3) = 0 := by decide
    rw [hk]
    push_cast
    rw [mul_comm, h3, mul_zero]
  have hnm1 : ((n - 1 : ℕ) : ZMod 3) = -1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), hncast]
    rfl
  have hsum' : f 0 + f 1 + (2 : ZMod 3) * f i2 = 0 := by
    have h := hsum
    rw [nsmul_eq_mul, hnm1] at h
    rwa [show (-1 : ZMod 3) = 2 from rfl] at h
  have h2c : (2 : ZMod 3) * f i2 + f i2 = 0 := by
    calc (2 : ZMod 3) * f i2 + f i2
        = (2 : ZMod 3) * f i2 + (1 : ZMod 3) * f i2 := by rw [one_mul]
      _ = ((2 : ZMod 3) + 1) * f i2 := by rw [add_mul]
      _ = (3 : ZMod 3) * f i2 := by rw [show (2 : ZMod 3) + 1 = 3 from rfl]
      _ = 0 := by rw [show (3 : ZMod 3) = 0 from rfl, zero_mul]
  have hc : f i2 = f 0 + f 1 := by
    have h := congrArg (fun z => z + f i2) hsum'
    rw [zero_add] at h
    rw [add_assoc (f 0 + f 1) ((2 : ZMod 3) * f i2) (f i2), h2c, add_zero] at h
    exact h.symm
  exact hc

private theorem ggQTUn_omega_pow_val_injective {K : Type} [Field K] [Finite K]
    (ω : Kˣ) (hω : ω ≠ 1) (hcard : Nat.card K = 4) :
    ∀ a b : ZMod 3, ω ^ a.val = ω ^ b.val → a = b := by
  classical
  have hcardU : Nat.card Kˣ = 3 := by
    rw [Nat.card_units, hcard]
  have hω3 : ω ^ 3 = 1 := by
    have h := pow_card_eq_one' (x := ω)
    rwa [hcardU] at h
  have ho : orderOf ω = 3 := orderOf_eq_prime hω3 hω
  intro a b hab
  rw [pow_eq_pow_iff_modEq, ho] at hab
  have hval : a.val = b.val :=
    Nat.ModEq.eq_of_lt_of_lt hab (ZMod.val_lt a) (ZMod.val_lt b)
  exact ZMod.val_injective 3 hval

theorem ggQTwoXInLU_nbr {n : ℕ} {K : Type} [Field K] [Finite K]
    (hS : GGQTwoSetting 3 B Bs x L D J) (hn3 : 3 ∣ n) (hn6 : 6 ≤ n)
    (C : GGQTwoXInLUCoord Bs (ggG0 3 B x L D J) L x n K)
    (hJ : J = (TableBUE.blockSU (K := K) (n := 1) ((Finset.univ.erase 0).erase 1)).map C.φ)
    (hD : ∀ b : ↥Bs, (b : G) ∈ D ↔ ∀ i j : Fin (n + 1), i ≠ 0 → i ≠ 1 → j ≠ 0 → j ≠ 1 →
        (C.ι (Additive.ofMul b) : Fin (n + 1) → ZMod 3) i =
          (C.ι (Additive.ofMul b) : Fin (n + 1) → ZMod 3) j) :
    ∃ (y : G) (hy : y ∈ Bs),
      GGNbr 3 B x D J y ((TableBUE.blockSU (K := K) (n := 1) (Finset.univ.erase 1)).map C.φ) ∧
      ((C.ι (Additive.ofMul ⟨y, hy⟩) : ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) =
        fun i => if i = 1 then 0 else -1 := by
  classical
  have _ := hJ
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hstd : LargeEvenStandardType 3 B x L := hcfg.1.2.2.2.2.2.2.2
  have hstdSub : LargeEvenStdSub 3 B x L D J := hcfg.2.2
  obtain ⟨y₀, K₀, hnb⟩ := exists_ggNbr hstd hstdSub
  obtain ⟨hy₀Bs, hy₀K₀, hy₀D, hy₀x, hx1⟩ := ggQTUn_nbr_facts hcfg hnb
  let f : Fin (n + 1) → ZMod 3 :=
    fun i => (C.ι (Additive.ofMul ⟨y₀, hy₀Bs⟩) : Fin (n + 1) → ZMod 3) i
  let δ : Fin (n + 1) → Kˣ := fun i => C.ω ^ (f i).val
  have hpair : (y₀, diagHom (n + 1) δ) ∈ SUTorus.suPairs C.φ := by
    simpa [δ, f] using ggQTUn_mem_suPairs C hy₀Bs
  have hsum : ∑ i, f i = 0 := by
    have hmem := LinearMap.mem_ker.mp (C.ι (Additive.ofMul ⟨y₀, hy₀Bs⟩)).2
    rw [LinearMap.sum_apply] at hmem
    simpa [f] using hmem
  have hconst : ∀ i j, i ≠ 0 → i ≠ 1 → j ≠ 0 → j ≠ 1 → f i = f j := by
    intro i j hi0 hi1 hj0 hj1
    exact (hD ⟨y₀, hy₀Bs⟩).mp hy₀D i j hi0 hi1 hj0 hj1
  have hcompC : IsComponentOf K₀ (Subgroup.centralizer ({y₀} : Set G)) :=
    (isComponentOf_of_isNeighborOf hstd (isNeighborOf_of_ggNbr hstdSub hnb)).1
  have hK₀G0 : K₀ ≤ ggG0 3 B x L D J := le_ggG0_of_ggNbr hnb
  have hcomp : IsComponentOf K₀ (C.φ.range ⊓ Subgroup.centralizer ({y₀} : Set G)) := by
    rw [C.range_eq]
    exact CFSG.Assembly.IsComponentOf.of_le_of_le hcompC (le_inf hK₀G0 hcompC.1) inf_le_right
  obtain ⟨I, hI4, hIconst, hKeq⟩ :=
    SUTorus.exists_blockSU_of_isComponentOf_two (m := n) C.field C.ker_le hpair hcomp
  have hIconstf : ∀ i ∈ I, ∀ j ∈ I, f i = f j := by
    intro i hi j hj
    exact ggQTUn_omega_pow_val_injective C.ω C.ω_ne_one C.field.card (f i) (f j)
      (by simpa [δ] using hIconst i hi j hj)
  have hex : ∃ j ∈ I, j ≠ 0 ∧ j ≠ 1 := by
    by_contra h
    push Not at h
    have hsub : I ⊆ ({0, 1} : Finset (Fin (n + 1))) := by
      intro j hj
      by_cases hj0 : j = 0
      · simp [hj0]
      · have hj1 : j = 1 := h j hj hj0
        simp [hj1]
    have hcard := Finset.card_le_card hsub
    have h2 : ({0, 1} : Finset (Fin (n + 1))).card = 2 := by
      rw [Finset.card_insert_of_notMem]
      · simp
      · simp
        omega
    omega
  obtain ⟨j, hjI, hj0, hj1⟩ := hex
  have hadd : f j = f 0 + f 1 := ggQTUn_coord_add hn3 hn6 hconst hsum j hj0 hj1
  by_cases h1 : f 1 = 0
  · have hf0ne : f 0 ≠ 0 := by
      intro h0
      have hfz : ∀ i, f i = 0 := by
        intro i
        by_cases hi0 : i = 0
        · rw [hi0, h0]
        · by_cases hi1 : i = 1
          · rw [hi1, h1]
          · have h := ggQTUn_coord_add hn3 hn6 hconst hsum i hi0 hi1
            rwa [h0, h1, add_zero] at h
      have hcoord : C.ι (Additive.ofMul ⟨y₀, hy₀Bs⟩) = C.ι 0 := by
        ext i
        simpa [f] using hfz i
      have hzero : Additive.ofMul (⟨y₀, hy₀Bs⟩ : ↥Bs) = 0 := C.ι.injective hcoord
      have hone : (⟨y₀, hy₀Bs⟩ : ↥Bs) = 1 := Additive.ofMul.injective hzero
      exact hnb.1.2.2.1 (congrArg Subtype.val hone)
    have hIsub : I ⊆ Finset.univ.erase (1 : Fin (n + 1)) := by
      intro i hi
      rw [Finset.mem_erase]
      refine ⟨?_, Finset.mem_univ i⟩
      intro hi1
      have hfi : f i = f j := hIconstf i hi j hjI
      have hfj0 : f j = 0 := by
        rw [hi1, h1] at hfi
        exact hfi.symm
      have h0 : f 0 = 0 := by
        have h := hadd
        rw [h1, add_zero] at h
        rw [hfj0] at h
        exact h.symm
      exact hf0ne h0
    have hKleK' : K₀ ≤
        (TableBUE.blockSU (K := K) (n := 1) (Finset.univ.erase 1)).map C.φ := by
      rw [hKeq]
      exact Subgroup.map_mono (SUTorus.blockSU_mono hIsub)
    have hδ0 : ∀ i, i ≠ 1 → δ i = δ 0 := by
      intro i hi1
      by_cases hi0 : i = 0
      · rw [hi0]
      · have hfi : f i = f 0 := by
          have h := ggQTUn_coord_add hn3 hn6 hconst hsum i hi0 hi1
          rwa [h1, add_zero] at h
        simp only [δ]
        rw [hfi]
    have hdiag : LinTorus.diagClass ({y₀} : Set G) (fun _ => δ) 0 =
        Finset.univ.erase (1 : Fin (n + 1)) := by
      ext i
      rw [LinTorus.mem_diagClass, Finset.mem_erase]
      constructor
      · intro h
        refine ⟨?_, Finset.mem_univ i⟩
        intro hi1
        have h' : δ i = δ 0 := h y₀ (by simp)
        rw [hi1] at h'
        have h0 : f 0 = 0 := by
          have h0' : (0 : ZMod 3) = f 0 :=
            ggQTUn_omega_pow_val_injective C.ω C.ω_ne_one C.field.card 0 (f 0)
              (by simpa [δ, h1] using h')
          exact h0'.symm
        exact hf0ne h0
      · rintro ⟨hi1, -⟩
        intro e he
        simpa using hδ0 i hi1
    have hcardV : (Finset.univ.erase (1 : Fin (n + 1))).card = n := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ,
        Fintype.card_fin]
      omega
    have hsub : IsSubnormal
        ((TableBUE.blockSU (K := K) (n := 1) (Finset.univ.erase 1)).map C.φ)
        (C.φ.range ⊓ Subgroup.centralizer ({y₀} : Set G)) := by
      have hδ' : ∀ e ∈ ({y₀} : Set G),
          (e, diagHom (n + 1) ((fun _ => δ) e)) ∈ SUTorus.suPairs C.φ := by
        intro e he
        rw [Set.mem_singleton_iff] at he
        subst e
        simpa using hpair
      have h := SUTorus.isSubnormal_map_blockSU (ψ := C.φ) (S := ({y₀} : Set G))
        (δ := fun _ => δ) C.ker_le hδ' 0
      simpa [hdiag] using h
    have hq : CFSG.Assembly.IsQuasisimple
        ((TableBUE.blockSU (K := K) (n := 1) (Finset.univ.erase 1)).map C.φ) := by
      apply SUTorus.isQuasisimple_map_blockSU C.field C.ker_le
      · rw [hcardV]
        omega
      · intro hc
        have h3 : n = 3 := by
          have := congrArg Prod.fst hc
          simpa [hcardV] using this
        omega
    have hδconst : ∀ i ∈ Finset.univ.erase (1 : Fin (n + 1)),
        ∀ j' ∈ Finset.univ.erase (1 : Fin (n + 1)), δ i = δ j' := by
      intro i hi j' hj'
      rw [Finset.mem_erase] at hi hj'
      rw [hδ0 i hi.1, hδ0 j' hj'.1]
    have hK'comp : IsComponentOf
        ((TableBUE.blockSU (K := K) (n := 1) (Finset.univ.erase 1)).map C.φ)
        (C.φ.range ⊓ Subgroup.centralizer ({y₀} : Set G)) := by
      refine ⟨?_, hsub, hq⟩
      refine le_inf (Subgroup.map_le_range C.φ _) ?_
      intro z hz
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp
        (SUTorus.mem_centralizer_map_blockSU (I := Finset.univ.erase 1) hpair hδconst) z hz
    have hle' : ((TableBUE.blockSU (K := K) (n := 1) (Finset.univ.erase 1)).map C.φ) ≤ K₀ := by
      rcases isComponentOf_le_or_commutator_eq_bot hK'comp hcomp.2.1 with hle | hcomm
      · exact hle
      · exfalso
        have hperf : ⁅K₀, K₀⁆ = K₀ := commutator_self_eq_of_isQuasisimple hcomp.2.2
        have hmono : ⁅K₀, K₀⁆ ≤
            ⁅((TableBUE.blockSU (K := K) (n := 1) (Finset.univ.erase 1)).map C.φ), K₀⁆ :=
          Subgroup.commutator_mono hKleK' le_rfl
        rw [hcomm, hperf] at hmono
        have hbot : K₀ = ⊥ := le_bot_iff.mp hmono
        exact (commutator_ne_bot_of_isQuasisimple hcomp.2.2) (by simpa [hperf] using hbot)
    have hKeqK' : K₀ =
        (TableBUE.blockSU (K := K) (n := 1) (Finset.univ.erase 1)).map C.φ :=
      le_antisymm hKleK' hle'
    have h01 : (0 : Fin (n + 1)) ≠ 1 := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_zero, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < n + 1)] at hv
      omega
    have hcases : f 0 = -1 ∨ f 0 = 1 := by
      have h : ∀ a : ZMod 3, a ≠ 0 → a = -1 ∨ a = 1 := by decide
      exact h (f 0) hf0ne
    rcases hcases with hf0m | hf0p
    · refine ⟨y₀, hy₀Bs, ?_, ?_⟩
      · have h := hnb
        rwa [hKeqK'] at h
      · change f = fun i => if i = 1 then 0 else -1
        funext i
        by_cases hi1 : i = 1
        · rw [hi1, h1]
          simp
        · by_cases hi0 : i = 0
          · rw [hi0, hf0m, if_neg h01]
          · have hfi : f i = f 0 := by
              have h := ggQTUn_coord_add hn3 hn6 hconst hsum i hi0 hi1
              rwa [h1, add_zero] at h
            rw [hfi, hf0m]
            simp [hi1]
    · refine ⟨y₀⁻¹, Bs.inv_mem hy₀Bs, ?_, ?_⟩
      · have h := GGNbr.inv hnb
        rwa [hKeqK'] at h
      · have hinv : Additive.ofMul (⟨y₀⁻¹, Bs.inv_mem hy₀Bs⟩ : ↥Bs) =
            -Additive.ofMul (⟨y₀, hy₀Bs⟩ : ↥Bs) := rfl
        have hcoord : ((C.ι (Additive.ofMul ⟨y₀⁻¹, Bs.inv_mem hy₀Bs⟩) :
            ↥(GGQTwoXInLAug n)) : Fin (n + 1) → ZMod 3) = fun i => -f i := by
          funext i
          have hsum0 : C.ι (Additive.ofMul (⟨y₀⁻¹, Bs.inv_mem hy₀Bs⟩ : ↥Bs)) +
              C.ι (Additive.ofMul (⟨y₀, hy₀Bs⟩ : ↥Bs)) = 0 := by
            rw [← map_add]
            have h : Additive.ofMul (⟨y₀⁻¹, Bs.inv_mem hy₀Bs⟩ : ↥Bs) +
                Additive.ofMul (⟨y₀, hy₀Bs⟩ : ↥Bs) = 0 := by
              rw [← ofMul_mul]
              simp
            rw [h, map_zero]
          have h2 : (C.ι (Additive.ofMul ⟨y₀⁻¹, Bs.inv_mem hy₀Bs⟩) :
                Fin (n + 1) → ZMod 3) i +
              (C.ι (Additive.ofMul ⟨y₀, hy₀Bs⟩) : Fin (n + 1) → ZMod 3) i = 0 := by
            simpa using congrArg (fun v : ↥(GGQTwoXInLAug n) =>
              (v : Fin (n + 1) → ZMod 3) i) hsum0
          exact eq_neg_of_add_eq_zero_left (show (C.ι (Additive.ofMul
            ⟨y₀⁻¹, Bs.inv_mem hy₀Bs⟩) : Fin (n + 1) → ZMod 3) i + f i = 0 by
              simpa [f] using h2)
        rw [hcoord]
        change (fun i => -f i) = fun i => if i = 1 then 0 else -1
        funext i
        by_cases hi1 : i = 1
        · rw [hi1, h1]
          simp only [if_true]
          exact neg_zero
        · by_cases hi0 : i = 0
          · rw [hi0, hf0p, if_neg h01]
          · have hfi : f i = f 0 := by
              have h := ggQTUn_coord_add hn3 hn6 hconst hsum i hi0 hi1
              rwa [h1, add_zero] at h
            rw [hfi, hf0p]
            simp [hi1]
  · have h0notI : (0 : Fin (n + 1)) ∉ I := by
      intro h0I
      have hfi : f 0 = f j := hIconstf 0 h0I j hjI
      have h : f 0 = f 0 + f 1 := hfi.trans hadd
      have h' : f 0 + 0 = f 0 + f 1 := by
        rw [add_zero]
        exact h
      exact h1 (add_left_cancel h').symm
    have hIsub : I ⊆ Finset.univ.erase (0 : Fin (n + 1)) := by
      intro i hi
      rw [Finset.mem_erase]
      exact ⟨by rintro rfl; exact h0notI hi, Finset.mem_univ i⟩
    have hKle : K₀ ≤
        (TableBUE.blockSU (K := K) (n := 1) (Finset.univ.erase 0)).map C.φ := by
      rw [hKeq]
      exact Subgroup.map_mono (SUTorus.blockSU_mono hIsub)
    have hxcoord : (C.ι (Additive.ofMul ⟨x, C.mem_x⟩) : Fin (n + 1) → ZMod 3) =
        fun i => if i = 0 then 0 else -1 := C.ι_x
    have hτconst : ∀ i ∈ Finset.univ.erase (0 : Fin (n + 1)),
        ∀ j ∈ Finset.univ.erase (0 : Fin (n + 1)),
        C.ω ^ ((C.ι (Additive.ofMul ⟨x, C.mem_x⟩) : Fin (n + 1) → ZMod 3) i).val =
          C.ω ^ ((C.ι (Additive.ofMul ⟨x, C.mem_x⟩) : Fin (n + 1) → ZMod 3) j).val := by
      intro i hi j' hj'
      rw [Finset.mem_erase] at hi hj'
      rw [hxcoord]
      simp [hi.1, hj'.1]
    have hxcent := SUTorus.mem_centralizer_map_blockSU (ggQTUn_mem_suPairs C C.mem_x)
      (I := Finset.univ.erase (0 : Fin (n + 1))) hτconst
    have hxK₀ : x ∈ Subgroup.centralizer (K₀ : Set G) :=
      Subgroup.centralizer_le (s := (K₀ : Set G))
        (t := (((TableBUE.blockSU (K := K) (n := 1) (Finset.univ.erase 0)).map C.φ :
          Subgroup G) : Set G)) (by intro z hz; exact hKle hz) hxcent
    exact absurd hxK₀ (ggQTUn_x_not_mem_centralizer hnb)

end CFSG.StandardType

end
