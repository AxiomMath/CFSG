module

public import CFSG.Quasithin.Vol2.Ch12Sec6L26r
public import CFSG.Quasithin.Vol2.Ch12Sec6L26m
public import CFSG.Quasithin.Vol2.Ch12Sec6L26p

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.G6 CFSG.QuasithinUnique
  CFSG.LieType.BorelTits CFSG.Quasithin.F7 S126 S126L1a S126P S126E S126F S126L19 S126L19a
  S126L24 Equiv
open scoped commutatorElement

namespace S126L211

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem le_centralizer_of_fix (h1224 : Lemma12_6_24) (h1226' : Stmt12_2_6)
    (h1262 : Theorem12_6_2) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G}
    (hHz : S126.InHz T L F.V1 H) {v : G} (hv : v ∈ V) (hvH : v ∈ H) (hvQ : v ∉ pCoreOf 2 H)
    {x₀ : G} (hx₀ : F.Nonsing x₀) {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hKp : ⁅K, K⁆ = K)
    (hfix : ∀ y : ↥H, (y : ↥H ⧸ CFSG.pCore 2 ↥H) ∈ K →
      (y : G) * x₀ * (y : G)⁻¹ * x₀⁻¹ ∈ F.V1) :
    K ≤ Subgroup.centralizer ({((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H)} : Set _) := by
  classical
  obtain ⟨h, hidx, -, -, -⟩ := S126L26.setup126 h1224 F hH hZ hHz
  have hV : ¬ V ≤ pCoreOf 2 H := fun hle => hvQ (hle hv)
  obtain ⟨hx₀V, -⟩ := id hx₀
  have hV1H : F.V1 ≤ H := h.V₁_le_V.trans h.V_le_H
  have hcen : ∀ z ∈ F.V1, ∀ a : ↥H, z * a = a * z := fun z hz a =>
    Subgroup.mem_centralizer_iff.mp (h.H_le_centralizer a.2) z hz
  set Y : Subgroup ↥H := K.comap (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) with hY
  have hYc : ∀ y : ↥H, y ∈ Y → (y : G) * x₀ * (y : G)⁻¹ * x₀⁻¹ ∈ F.V1 := fun y hy => hfix y hy
  let φ : ↥Y →* ↥F.V1 :=
    { toFun := fun y => ⟨((y : ↥H) : G) * x₀ * ((y : ↥H) : G)⁻¹ * x₀⁻¹, hYc y y.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        have hb := hYc b b.2
        show ((a : ↥H) : G) * (b : ↥H) * x₀ * (((a : ↥H) : G) * (b : ↥H))⁻¹ * x₀⁻¹ =
          (((a : ↥H) : G) * x₀ * ((a : ↥H) : G)⁻¹ * x₀⁻¹) *
            (((b : ↥H) : G) * x₀ * ((b : ↥H) : G)⁻¹ * x₀⁻¹)
        have e1 : ((a : ↥H) : G) * (b : ↥H) * x₀ * (((a : ↥H) : G) * (b : ↥H))⁻¹ * x₀⁻¹ =
            ((a : ↥H) : G) * (((b : ↥H) : G) * x₀ * ((b : ↥H) : G)⁻¹ * x₀⁻¹) *
              ((a : ↥H) : G)⁻¹ * (((a : ↥H) : G) * x₀ * ((a : ↥H) : G)⁻¹ * x₀⁻¹) := by group
        have ha := hYc a a.2
        rw [e1, ← hcen _ hb (a : ↥H), mul_inv_cancel_right]
        exact hcen _ hb ⟨_, hV1H ha⟩ }
  have hV1c : ∀ a b : ↥F.V1, a * b = b * a := fun a b =>
    Subtype.ext (hcen _ a.2 ⟨_, hV1H b.2⟩)
  rw [← hKp, Subgroup.commutator_le]
  intro a ha b hb
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective b
  have hy : y ∈ Y := ha
  have hy' : y' ∈ Y := hb
  have hφ : φ ⁅(⟨y, hy⟩ : ↥Y), ⟨y', hy'⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hV1c _ _
  have h1 : ⁅(y : G), (y' : G)⁆ * x₀ * ⁅(y : G), (y' : G)⁆⁻¹ * x₀⁻¹ = 1 := by
    have := congrArg Subtype.val hφ
    simpa [φ, commutatorElement_def] using this
  set cy := ⁅(y : G), (y' : G)⁆ with hcy
  have hyC : cy ∈ Subgroup.centralizer ({x₀} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h2 : cy * x₀ * cy⁻¹ = x₀ := by
      have := mul_eq_one_iff_eq_inv.mp h1
      rwa [inv_inv] at this
    calc cy * x₀ = cy * x₀ * cy⁻¹ * cy := by group
      _ = x₀ * cy := by rw [h2]
  have hyH : cy ∈ H := by
    rw [hcy, commutatorElement_def]
    exact H.mul_mem (H.mul_mem (H.mul_mem y.2 y'.2) (H.inv_mem y.2)) (H.inv_mem y'.2)
  have hyM := h1262 G T L V F hH x₀ hx₀ hyC
  have hyNV : cy ∈ H ⊓ Subgroup.normalizer (V : Set G) := by
    rw [← (h1226' G T L V hH.hyp).2 F.V1 H h.V₁_ne_bot h.V₁_le_V h.H_normalizes_V₁]
    exact ⟨hyH, hyM⟩
  have hyCV : cy ∈ centralizerMod (pCoreOf 2 H) H V := by
    rw [(h.F95_3 hidx hV).1, (h.F95_3 hidx hV).2]
    exact hyNV
  have e : ⁅((y : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H), ((y' : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H)⁆ =
      ((⟨cy, hyH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) := by
    have : (⟨cy, hyH⟩ : ↥H) = ⁅y, y'⁆ := Subtype.ext (by simp [hcy, commutatorElement_def])
    rw [this]
    simp [commutatorElement_def]
  rw [e]
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    ((S126L26.mk_comm_iff (⟨cy, hyH⟩ : ↥H) ⟨v, hvH⟩).mpr (hyCV.2.2 v hv))

theorem ev_pv_block : ∀ i j : Fin 8, (i.val < 4 ↔ j.val < 4) → Ev (B5FinS8.pv i j) := by decide

omit [Finite G] in
theorem exists_nonsing_comm [Finite G] (h1222 : Stmt12_2_2) (F : Frame126 T L V)
    (hH : Hyp126 G T L V) (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {c : G}
    (hcL : c ∈ Li L F.V1) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) :
    ∃ y ∈ F.V5, F.Nonsing (y⁻¹ * c * y * c⁻¹) := by
  obtain ⟨-, hXV, hXV1, -⟩ := sup_le_normalizers h1222 F hH
  have hinj := beta_injective F hZ
  have hcL' : c ∈ L := S126L19b.L1_le_L F hcL
  have hcV : c ∈ Subgroup.normalizer (V : Set G) := hXV (Subgroup.mem_sup_left hcL)
  have hc1' : c ∈ Subgroup.normalizer (F.V1 : Set G) := hXV1 (Subgroup.mem_sup_left hcL)
  set σ := S126T2.psiP F hH ⟨c, hcL'⟩ with hσ
  have hact : ActsAs F c σ := S126T2.actsAs_psiP F hH ⟨c, hcL'⟩
  have hσ3 : σ ^ 3 = 1 := by
    have h1 := hact.pow hcV 3
    rw [hc3] at h1
    exact h1.unique (ActsAs.one F) (Subgroup.one_mem _)
  have hσ1 : σ ≠ 1 := by
    intro h1
    rw [h1] at hact
    have hcC := mem_centralizer_of_actsAs_one' hinj hcV hact
    obtain ⟨n, hn⟩ := S126T2.isPGroup_CL h1222 hH ⟨c, hcL', hcC⟩
    have h2 : c ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    exact hc1 (S126L26.eq_one_of_two_three' h2 hc3)
  have hb : ∀ i : Fin 8, (i.val < 4 ↔ (σ i).val < 4) := by
    rcases blocks_of_mem_V1 F hc1' hact with hb | hb
    · exact hb
    · exfalso
      have h0 : (σ (σ (σ 0))).val < 4 := by
        have h3 : (σ ^ 3) 0 = σ (σ (σ 0)) := by rw [pow_succ, pow_succ, pow_one]; rfl
        rw [← h3, hσ3]
        decide
      have h1 : 4 ≤ (σ 0).val := (hb 0).mp (by decide)
      have h2 : (σ (σ 0)).val < 4 := by
        by_contra hs
        push Not at hs
        have := (hb (σ 0)).mpr hs
        omega
      have h4 : 4 ≤ (σ (σ (σ 0))).val := (hb _).mp h2
      omega
  obtain ⟨i, hi⟩ : ∃ i, σ i ≠ i := by
    by_contra hcon
    push Not at hcon
    exact hσ1 (Equiv.ext hcon)
  set j := σ i with hj
  set k := σ j with hk
  have hij : i ≠ j := fun h => hi h.symm
  have hjk : j ≠ k := fun h => hi (σ.injective h.symm)
  have hik : i ≠ k := by
    intro h
    apply hi
    have h3 : (σ ^ 3) i = σ k := by
      rw [pow_succ, pow_succ, pow_one]
      rfl
    rw [hσ3, ← h] at h3
    exact h3.symm
  have hev : Ev (B5FinS8.pv i j) := ev_pv_block i j (hb i)
  obtain ⟨y, hy⟩ := F.β_surj (QuotientGroup.mk (pe i j))
  have hy5 : (y : G) ∈ F.V5 := (mem_preV y.2).2 (by rw [hy]; exact (mem_W5_iff (pe i j)).2 hev)
  refine ⟨y, hy5, ?_⟩
  set w : ↥V := ⟨c * y * c⁻¹, conj_mem hcV y⟩ with hw
  have hx₀V : (y : G)⁻¹ * c * y * c⁻¹ ∈ V := by
    have e : (y : G)⁻¹ * c * y * c⁻¹ = ((y⁻¹ * w : ↥V) : G) := by
      rw [hw]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact (y⁻¹ * w).2
  refine ⟨hx₀V, ?_⟩
  have e : (⟨(y : G)⁻¹ * c * y * c⁻¹, hx₀V⟩ : ↥V) = y⁻¹ * w := by
    apply Subtype.ext
    rw [hw]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e, map_mul, map_inv, hact y w rfl, hy, S126L20a.dAct_pe, ← QuotientGroup.mk_inv,
    ← QuotientGroup.mk_mul]
  have e2 : (pe i j)⁻¹ * pe (σ i) (σ j) = pe i k := by
    have hinv : (pe i j)⁻¹ = pe i j := by
      apply Subtype.ext
      apply Multiplicative.toAdd.injective
      funext l
      show -(B5FinS8.pv i j l) = B5FinS8.pv i j l
      exact ZModModule.neg_eq_self _
    rw [hinv]
    exact S126L23c.pe_mul_pe i j k
  rw [e2]
  exact ⟨pe i k, rfl, wt_pv i k hik⟩

theorem false_of_cent (h1222 : Stmt12_2_2) (h1224 : Lemma12_6_24) (h1226' : Stmt12_2_6)
    (h1262 : Theorem12_6_2) (hF : FactL211Loc12626) (F : Frame126 T L V) (hH : Hyp126 G T L V)
    (hZ : V ⊓ Subgroup.centralizer (L : Set G) = ⊥) {H : Subgroup G}
    (hHz : S126.InHz T L F.V1 H) {v : G} (hv : v ∈ V) (hvH : v ∈ H) (hvQ : v ∉ pCoreOf 2 H)
    {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hKl : IsPSL 2 11 1 ↥K)
    (hvnc : ∃ k ∈ K, ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) * k ≠
      k * ((⟨v, hvH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H))
    {c : G} (hcL : c ∈ Li L F.V1) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hcK : ∀ hcH : c ∈ H, ∀ k ∈ K, ((⟨c, hcH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) * k =
      k * ((⟨c, hcH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H))
    (hOV : ∀ l ∈ L, ∀ o ∈ L ⊓ Subgroup.centralizer (V : Set G), l * o * l⁻¹ * o⁻¹ ∈ V) :
    False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hidx, -, hcard5, hC5⟩ := S126L26.setup126 h1224 F hH hZ hHz
  have hinj := beta_injective F hZ
  have hyp := hH.hyp
  obtain ⟨-, hXV, hXV1, -⟩ := sup_le_normalizers h1222 F hH
  obtain ⟨⟨hKcard, hKs⟩, -, -, -, -, -, -⟩ := hF ↥K hKl
  have hcH : c ∈ H := h.L₁T_le_H (Subgroup.mem_sup_left hcL)
  have hcL' : c ∈ L := S126L19b.L1_le_L F hcL
  have hcV : c ∈ Subgroup.normalizer (V : Set G) := hXV (Subgroup.mem_sup_left hcL)
  have hUH : conjClosure F.V5 H ≤ H := h.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 H)
  have hV1H : F.V1 ≤ H := h.V₁_le_V.trans h.V_le_H
  set W := tildeOf F.V1 (conjClosure F.V5 H) with hW
  have hWe := h.isElemAbelian_tilde
  have hWc : ∀ a b : ↥W, a * b = b * a := fun a b => hWe.1.is_comm.comm a b
  have hW2 : ∀ w : ↥W, w ^ 2 = 1 := fun w =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hWe.2 w.1 w.2)
  set ρ := S126L26.rhoBar h with hρ
  set cb : ↥H ⧸ CFSG.pCore 2 ↥H := ((⟨c, hcH⟩ : ↥H) : ↥H ⧸ CFSG.pCore 2 ↥H) with hcb
  have hcb3 : cb ^ 3 = 1 := by
    rw [hcb, ← QuotientGroup.mk_pow]
    have : (⟨c, hcH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hc3)
    rw [this, QuotientGroup.mk_one]
  have hρ3 : ∀ w, ρ cb (ρ cb (ρ cb w)) = w := fun w => by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul,
      show cb * cb * cb = cb ^ 3 by rw [pow_succ, sq], hcb3, map_one, MulAut.one_apply]
  let f : ↥W →* ↥W :=
    { toFun := fun w => w⁻¹ * ρ cb w
      map_one' := by simp
      map_mul' := fun a b => by
        rw [map_mul, mul_inv_rev]
        simp only [mul_assoc]
        rw [hWc b⁻¹ (a⁻¹ * (ρ cb a * ρ cb b)), mul_assoc, mul_assoc,
          hWc (ρ cb b) b⁻¹] }
  have hf : ∀ w, f w = w⁻¹ * ρ cb w := fun w => rfl
  set A := f.range with hA
  have hAc : ∀ a ∈ A, ρ cb a ∈ A := by
    rintro _ ⟨w, rfl⟩
    refine ⟨ρ cb w, ?_⟩
    rw [hf, hf, map_mul, map_inv]
  have hAk : ∀ k ∈ K, ∀ a ∈ A, ρ k a ∈ A := by
    intro k hk
    rintro _ ⟨w, rfl⟩
    refine ⟨ρ k w, ?_⟩
    rw [hf, hf, map_mul, map_inv]
    congr 1
    rw [← MulAut.mul_apply, ← MulAut.mul_apply, ← map_mul, ← map_mul, hcK hcH k hk]
  have hAfix : ∀ a ∈ A, ρ cb a = a → a = 1 := by
    rintro _ ⟨w, rfl⟩ hfx
    rw [hf] at hfx ⊢
    exact S126Cop.eq_one_of_fix hW2 (ρ cb).toMonoidHom hρ3 hfx
  obtain ⟨y, hy5, hx₀N⟩ := exists_nonsing_comm h1222 F hH hZ hcL hc3 hc1
  have hyU : y ∈ conjClosure F.V5 H := le_conjClosure F.V5 H hy5
  have hyH : y ∈ H := hUH hyU
  set yt : ↥W := ⟨toTilde h.H_normalizes_V₁ ⟨y, hyH⟩,
    (mem_tildeOf_iff h.H_normalizes_V₁ hUH).mpr ⟨⟨y, hyH⟩, hyU, rfl⟩⟩ with hyt
  have hx₀H : y⁻¹ * c * y * c⁻¹ ∈ H :=
    H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem hyH) hcH) hyH) (H.inv_mem hcH)
  have hx₀e : ((f yt : ↥W) : SecQuot (Subgroup.normalizer (F.V1 : Set G)) F.V1) =
      toTilde h.H_normalizes_V₁ ⟨y⁻¹ * c * y * c⁻¹, hx₀H⟩ := by
    have e : (⟨y⁻¹ * c * y * c⁻¹, hx₀H⟩ : ↥H) =
        (⟨y, hyH⟩ : ↥H)⁻¹ * ⟨c, hcH⟩ * ⟨y, hyH⟩ * (⟨c, hcH⟩ : ↥H)⁻¹ := rfl
    rw [hf, Subgroup.coe_mul, Subgroup.coe_inv, hρ, hcb, S126L26.rhoBar_mk, S126L26.rhoU_apply, hyt,
      e]
    simp only [map_mul, map_inv]
    group
  have hKmove : ∃ k ∈ K, ρ k (f yt) ≠ f yt := by
    by_contra hcon
    push Not at hcon
    have hKp : ⁅K, K⁆ = K := S126C.perfect_L211 hF hKl
    have hle := le_centralizer_of_fix h1224 h1226' h1262 F hH hZ hHz hv hvH hvQ hx₀N hKp
      (fun y' hy' => by
        have h1 := hcon _ hy'
        have h2 := congrArg (fun z : ↥W => (z : SecQuot (Subgroup.normalizer (F.V1 : Set G))
          F.V1)) h1
        simp only [hρ, S126L26.rhoBar_mk, S126L26.rhoU_apply, hx₀e] at h2
        have h3 : toTilde h.H_normalizes_V₁ y' * toTilde h.H_normalizes_V₁ ⟨_, hx₀H⟩ =
            toTilde h.H_normalizes_V₁ ⟨_, hx₀H⟩ * toTilde h.H_normalizes_V₁ y' := by
          calc _ = toTilde h.H_normalizes_V₁ y' * toTilde h.H_normalizes_V₁ ⟨_, hx₀H⟩ *
                (toTilde h.H_normalizes_V₁ y')⁻¹ * toTilde h.H_normalizes_V₁ y' := by group
            _ = _ := by rw [h2]
        exact (toTilde_comm_iff h.H_normalizes_V₁).mp h3)
    obtain ⟨k, hk, hvk⟩ := hvnc
    exact hvk (Subgroup.mem_centralizer_singleton_iff.mp (hle hk)).symm
  have : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 11 (by rw [hKcard]; norm_num)
  have hgmove : ∃ a ∈ A, ρ (g : ↥H ⧸ CFSG.pCore 2 ↥H) a ≠ a := by
    by_contra hcon
    push Not at hcon
    let N : Subgroup ↥K :=
      { carrier := {k | ∀ a ∈ A, ρ (k : ↥H ⧸ CFSG.pCore 2 ↥H) a = a}
        one_mem' := fun a _ => by simp
        mul_mem' := fun {k k'} hk hk' a ha => by
          rw [Subgroup.coe_mul, map_mul, MulAut.mul_apply, hk' a ha, hk a ha]
        inv_mem' := fun {k} hk a ha => by
          have h1 := hk a ha
          calc ρ ((k⁻¹ : ↥K) : ↥H ⧸ CFSG.pCore 2 ↥H) a =
              ρ ((k⁻¹ : ↥K) : ↥H ⧸ CFSG.pCore 2 ↥H) (ρ (k : ↥H ⧸ CFSG.pCore 2 ↥H) a) := by rw [h1]
            _ = a := by
                rw [← MulAut.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one,
                  MulAut.one_apply] }
    have hNn : N.Normal := by
      refine ⟨fun k hk x a ha => ?_⟩
      have hxa : ρ ((x⁻¹ : ↥K) : ↥H ⧸ CFSG.pCore 2 ↥H) a ∈ A := hAk _ (x⁻¹).2 a ha
      have h1 := hk _ hxa
      calc ρ ((x * k * x⁻¹ : ↥K) : ↥H ⧸ CFSG.pCore 2 ↥H) a =
          ρ (x : ↥H ⧸ CFSG.pCore 2 ↥H) (ρ (k : ↥H ⧸ CFSG.pCore 2 ↥H)
            (ρ ((x⁻¹ : ↥K) : ↥H ⧸ CFSG.pCore 2 ↥H) a)) := by
            simp only [Subgroup.coe_mul, map_mul, MulAut.mul_apply]
        _ = ρ (x : ↥H ⧸ CFSG.pCore 2 ↥H) (ρ ((x⁻¹ : ↥K) : ↥H ⧸ CFSG.pCore 2 ↥H) a) := by rw [h1]
        _ = a := by
            rw [← MulAut.mul_apply, ← map_mul, Subgroup.coe_inv, mul_inv_cancel, map_one,
              MulAut.one_apply]
    have hgN : g ∈ N := fun a ha => hcon a ha
    have := hKs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hN | hN
    · rw [hN, Subgroup.mem_bot] at hgN
      rw [hgN, orderOf_one] at hg
      exact absurd hg (by norm_num)
    · obtain ⟨k, hk, hkm⟩ := hKmove
      have hkN : (⟨k, hk⟩ : ↥K) ∈ N := hN ▸ Subgroup.mem_top _
      exact hkm (hkN (f yt) ⟨yt, rfl⟩)
  have hmapA : A.map (ρ (g : ↥H ⧸ CFSG.pCore 2 ↥H)).toMonoidHom = A := by
    apply le_antisymm
    · rintro _ ⟨a, ha, rfl⟩
      exact hAk _ g.2 a ha
    · intro a ha
      refine ⟨ρ ((g⁻¹ : ↥K) : ↥H ⧸ CFSG.pCore 2 ↥H) a, hAk _ (g⁻¹).2 a ha, ?_⟩
      show ρ (g : ↥H ⧸ CFSG.pCore 2 ↥H) (ρ ((g⁻¹ : ↥K) : ↥H ⧸ CFSG.pCore 2 ↥H) a) = a
      rw [← MulAut.mul_apply, ← map_mul, Subgroup.coe_inv, mul_inv_cancel, map_one,
        MulAut.one_apply]
  let rg : MulAut ↥A :=
    ((ρ (g : ↥H ⧸ CFSG.pCore 2 ↥H)).subgroupMap A).trans (MulEquiv.subgroupCongr hmapA)
  have hrg : ∀ a : ↥A, ((rg a : ↥A) : ↥W) = ρ (g : ↥H ⧸ CFSG.pCore 2 ↥H) a := fun a => rfl
  have hrgpow : ∀ n : ℕ, ∀ a : ↥A, (((rg ^ n) a : ↥A) : ↥W) =
      ρ ((g : ↥H ⧸ CFSG.pCore 2 ↥H) ^ n) a := by
    intro n
    induction n with
    | zero => intro a; simp
    | succ n ih =>
      intro a
      rw [pow_succ, MulAut.mul_apply, ih, pow_succ, map_mul, MulAut.mul_apply, hrg]
  have hg11 : (g : ↥H ⧸ CFSG.pCore 2 ↥H) ^ 11 = 1 := by
    rw [← Subgroup.coe_pow, ← hg, pow_orderOf_eq_one, Subgroup.coe_one]
  have hrg11 : rg ^ 11 = 1 := by
    ext a
    rw [hrgpow, hg11, map_one, MulAut.one_apply, MulAut.one_apply]
  have hrg1 : rg ≠ 1 := by
    intro h1
    obtain ⟨a, ha, ham⟩ := hgmove
    apply ham
    have := congrArg (fun φ : MulAut ↥A => ((φ ⟨a, ha⟩ : ↥A) : ↥W)) h1
    simpa [hrg] using this
  have hA2 : IsPGroup 2 ↥A := fun a => ⟨1, Subtype.ext (by simpa using hW2 a)⟩
  have hAge := S126Cop.two_pow_ten_le hA2 rg hrg11 hrg1
  set X : Subgroup G :=
    ((A.map W.subtype).comap (toTilde h.H_normalizes_V₁)).map H.subtype with hX
  have hmemX : ∀ x : G, x ∈ X ↔ ∃ hx : x ∈ H, toTilde h.H_normalizes_V₁ ⟨x, hx⟩ ∈ A.map W.subtype :=
    fun x => ⟨fun ⟨x', hx', hxe⟩ => hxe ▸ ⟨x'.2, hx'⟩, fun ⟨hx, hxA⟩ => ⟨⟨x, hx⟩, hxA, rfl⟩⟩
  have hXH : X ≤ H := fun x hx => ((hmemX x).mp hx).1
  have hV1X : F.V1 ≤ X := fun z hz => (hmemX z).mpr ⟨hV1H hz, ⟨1, A.one_mem, by
    simp only [map_one]
    exact ((toTilde_eq_one_iff h.H_normalizes_V₁).mpr hz).symm⟩⟩
  have hXt : tildeOf F.V1 X = A.map W.subtype := by
    apply le_antisymm
    · intro t ht
      obtain ⟨x, hxX, rfl⟩ := (mem_tildeOf_iff h.H_normalizes_V₁ hXH).mp ht
      obtain ⟨hx, hxA⟩ := (hmemX x).mp hxX
      exact hxA
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨u, hu, hue⟩ := (mem_tildeOf_iff h.H_normalizes_V₁ hUH).mp a.2
      refine (mem_tildeOf_iff h.H_normalizes_V₁ hXH).mpr ⟨u, (hmemX u).mpr ⟨u.2, ?_⟩, hue⟩
      rw [hue]
      exact ⟨a, ha, rfl⟩
  have hXcard : Nat.card A * 2 = Nat.card X := by
    have := S126L26.card_tildeOf_mul h.card_V₁ hV1X (hXH.trans h.H_normalizes_V₁)
    rw [hXt, Subgroup.card_map_of_injective W.subtype_injective] at this
    exact this
  have hXU : X ≤ conjClosure F.V5 H := by
    intro x hx
    obtain ⟨hxH, a, -, hae⟩ := (hmemX x).mp hx
    obtain ⟨u, hu, hue⟩ := (mem_tildeOf_iff h.H_normalizes_V₁ hUH).mp a.2
    have h1 : (u : G)⁻¹ * x ∈ F.V1 := by
      have := secMk_eq_secMk_iff.mp (hue.trans hae)
      exact this
    have e : x = u * ((u : G)⁻¹ * x) := by group
    rw [e]
    exact (conjClosure F.V5 H).mul_mem hu (le_conjClosure F.V5 H (h.V₁_le_Vp h1))
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hyp.normalizes
  have hQT : pCoreOf 2 H ≤ T :=
    pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h.sylow (le_sup_right.trans hHz.1.1))
  have hUT : conjClosure F.V5 H ≤ T := h.conjClosure_Vp_le_pCoreOf.trans hQT
  have hVL : V ≤ L := by
    rw [← hyp.irrPlus.2.2.2.1, Subgroup.commutator_le]
    intro v' hv' l hl
    rw [commutatorElement_def]
    exact L.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTL (h.V_le_T hv')) l).mp hl) (L.inv_mem hl)
  have hXL : X ≤ L := by
    intro x hx
    obtain ⟨hxH, a, ha, hae⟩ := (hmemX x).mp hx
    obtain ⟨w, rfl⟩ := ha
    obtain ⟨u, hu, hue⟩ := (mem_tildeOf_iff h.H_normalizes_V₁ hUH).mp w.2
    have huH : (u : G) ∈ H := u.2
    have hwH : (u : G)⁻¹ * c * u * c⁻¹ ∈ H :=
      H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem huH) hcH) huH) (H.inv_mem hcH)
    have hfw : ((f w : ↥W) : SecQuot (Subgroup.normalizer (F.V1 : Set G)) F.V1) =
        toTilde h.H_normalizes_V₁ ⟨(u : G)⁻¹ * c * u * c⁻¹, hwH⟩ := by
      have e : (⟨(u : G)⁻¹ * c * u * c⁻¹, hwH⟩ : ↥H) = u⁻¹ * ⟨c, hcH⟩ * u * (⟨c, hcH⟩ : ↥H)⁻¹ :=
        rfl
      rw [hf, Subgroup.coe_mul, Subgroup.coe_inv, hρ, hcb, S126L26.rhoBar_mk,
        S126L26.rhoU_apply, ← hue, e]
      simp only [map_mul, map_inv]
      group
    have h1 : ((u : G)⁻¹ * c * u * c⁻¹)⁻¹ * x ∈ F.V1 := by
      have := secMk_eq_secMk_iff.mp ((hfw.symm.trans hae))
      exact this
    have hcomL : (u : G)⁻¹ * c * u * c⁻¹ ∈ L := by
      have huN : (u : G)⁻¹ ∈ Subgroup.normalizer (L : Set G) :=
        Subgroup.inv_mem _ (hTL (hUT hu))
      have h2 : (u : G)⁻¹ * c * (u : G)⁻¹⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp huN c).mp hcL'
      rw [inv_inv] at h2
      exact L.mul_mem h2 (L.inv_mem hcL')
    have e : x = ((u : G)⁻¹ * c * u * c⁻¹) * (((u : G)⁻¹ * c * u * c⁻¹)⁻¹ * x) := by group
    rw [e]
    exact L.mul_mem hcomL (hVL (h.V₁_le_V h1))
  have hQR : pCoreOf 2 H ≤ Ri T L F.V1 :=
    le_pCoreOf_of_le_normalizer 2 (hQT.trans le_sup_right)
      (hHz.1.1.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
  have hXR : X ≤ Ri T L F.V1 := hXU.trans (h.conjClosure_Vp_le_pCoreOf.trans hQR)
  have hR1T : Ri T L F.V1 ≤ T :=
    pCoreOf_le_of_le_normalizer hyp.sylow (le_sup_right.trans Subgroup.le_normalizer)
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := le_sup_right.trans hXV
  have hpsiX : Nat.card ↥((X.subgroupOf L).map (S126L19a.psi F hH)) ≤ 16 := by
    have hle : (X.subgroupOf L).map (S126L19a.psi F hH) ≤
        E16.comap (alternatingGroup (Fin 8)).subtype := by
      rintro _ ⟨x, hx, rfl⟩
      show S126T2.psiP F hH x ∈ E16
      exact S126L1b.mem_E16 F hTV hR1T (hXR (Subgroup.mem_subgroupOf.mp hx))
        (S126T2.actsAs_psiP F hH x)
    calc Nat.card ↥((X.subgroupOf L).map (S126L19a.psi F hH)) ≤
        Nat.card ↥(E16.comap (alternatingGroup (Fin 8)).subtype) := Subgroup.card_le_of_le hle
      _ = Nat.card ↥((E16.comap (alternatingGroup (Fin 8)).subtype).map
            (alternatingGroup (Fin 8)).subtype) :=
          (Subgroup.card_map_of_injective (Subgroup.subtype_injective _)).symm
      _ ≤ Nat.card E16 := Subgroup.card_le_of_le (Subgroup.map_comap_le _ _)
      _ ≤ 16 := card_E16_le
  have hceq := S126L19a.card_eq F hH hXL
  set Y := X ⊓ Subgroup.centralizer (V : Set G) with hYdef
  have hcX : ∀ x ∈ X, c * x * c⁻¹ ∈ X := by
    intro x hx
    obtain ⟨hxH, a, ha, hae⟩ := (hmemX x).mp hx
    have hcxH : c * x * c⁻¹ ∈ H := H.mul_mem (H.mul_mem hcH hxH) (H.inv_mem hcH)
    refine (hmemX _).mpr ⟨hcxH, ρ cb a, hAc a ha, ?_⟩
    have e : (⟨c * x * c⁻¹, hcxH⟩ : ↥H) = ⟨c, hcH⟩ * ⟨x, hxH⟩ * (⟨c, hcH⟩ : ↥H)⁻¹ := rfl
    show ((ρ cb a : ↥W) : SecQuot (Subgroup.normalizer (F.V1 : Set G)) F.V1) = _
    rw [hρ, hcb, S126L26.rhoBar_mk, S126L26.rhoU_apply, e, map_mul, map_mul, map_inv]
    congr 2
  have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (Y : Set G) := by
    apply Subgroup.zpowers_le.mpr
    have key : ∀ y ∈ Y, c * y * c⁻¹ ∈ Y := fun y hy =>
      ⟨hcX y hy.1, conj_mem_centralizer hcV hy.2⟩
    have hc2 : c⁻¹ = c * c := by
      rw [inv_eq_iff_mul_eq_one, ← hc3, pow_succ, sq, mul_assoc]
    have key' : ∀ y ∈ Y, c⁻¹ * y * c⁻¹⁻¹ ∈ Y := by
      intro y hy
      have e : c⁻¹ * y * c⁻¹⁻¹ = c * (c * y * c⁻¹) * c⁻¹ := by
        calc c⁻¹ * y * c⁻¹⁻¹ = (c * c) * y * (c * c)⁻¹ := by rw [← hc2]
          _ = c * (c * y * c⁻¹) * c⁻¹ := by group
      rw [e]
      exact key _ (key y hy)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => key y hy, fun hy => ?_⟩
    have := key' _ hy
    simpa [mul_assoc] using this
  have hY2 : IsPGroup 2 Y := (S126T2.isPGroup_CL h1222 hH).to_le (inf_le_inf_right _ hXL)
  have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers c)) (Nat.card Y) := by
    obtain ⟨n, hn⟩ := hY2.exists_card_eq
    rw [hn, Nat.card_zpowers]
    exact Nat.Coprime.pow_right n (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one hc3)
      (by norm_num))
  have hYsolv : Group.IsSolvable ↥Y := by
    have := hY2.isNilpotent
    infer_instance
  have hYfac := S126Cop.le_comm_sup_inf hcN hYsolv hcop
  have hYc : ⁅Y, Subgroup.zpowers c⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro o ho x hx
    have hxL : x ∈ L := (Subgroup.zpowers_le.mpr hcL') hx
    have h1 := hOV x hxL o ⟨hXL ho.1, ho.2⟩
    have e : ⁅o, x⁆ = (x * o * x⁻¹ * o⁻¹)⁻¹ := by simp only [commutatorElement_def]; group
    rw [e]
    exact V.inv_mem h1
  have hYC : Y ⊓ Subgroup.centralizer (Subgroup.zpowers c : Set G) ≤ F.V1 := by
    rintro y ⟨hyY, hyC⟩
    obtain ⟨hyH, a, ha, hae⟩ := (hmemX y).mp hyY.1
    have hyc : c * y * c⁻¹ = y := by
      have := Subgroup.mem_centralizer_iff.mp hyC c (Subgroup.mem_zpowers c)
      rw [this]
      group
    have hae' : (a : SecQuot (Subgroup.normalizer (F.V1 : Set G)) F.V1) =
        toTilde h.H_normalizes_V₁ ⟨y, hyH⟩ := hae
    have hfa : ρ cb a = a := by
      apply Subtype.ext
      have e : (⟨c * y * c⁻¹, H.mul_mem (H.mul_mem hcH hyH) (H.inv_mem hcH)⟩ : ↥H) =
          ⟨c, hcH⟩ * ⟨y, hyH⟩ * (⟨c, hcH⟩ : ↥H)⁻¹ := rfl
      rw [hρ, hcb, S126L26.rhoBar_mk, S126L26.rhoU_apply, hae', ← map_inv, ← map_mul, ← map_mul,
        ← e]
      congr 1
      exact Subtype.ext hyc
    have ha1 := hAfix a ha hfa
    have h1 : toTilde h.H_normalizes_V₁ ⟨y, hyH⟩ = 1 := by
      rw [← hae', ha1]
      rfl
    exact (toTilde_eq_one_iff h.H_normalizes_V₁).mp h1
  have hYV : Y ≤ V := hYfac.trans (sup_le hYc (hYC.trans h.V₁_le_V))
  have hV64 : Nat.card V = 64 := by
    rw [S126L20.card_V F, hZ, Subgroup.card_bot, mul_one]
  have hY64 : Nat.card Y ≤ 64 := hV64 ▸ Subgroup.card_le_of_le hYV
  have h1 : Nat.card A * 2 ≤ 16 * 64 := by
    rw [hXcard, hceq]
    exact Nat.mul_le_mul hpsiX hY64
  omega






end S126L211

end CFSG.Quasithin.H13
