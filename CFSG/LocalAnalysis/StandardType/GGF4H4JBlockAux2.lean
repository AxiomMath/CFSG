module

public import CFSG.LocalAnalysis.StandardType.GGTypeACompatDiagProof

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear Matrix

section Local

@[expose] def GGTypeALocalCfg {G : Type} [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G)
    (x : G) (L D J : Subgroup G) (n f : ℕ)
    (y : G) (K : Subgroup G) : Prop :=
  GGConfig p B Bs x L D J ∧ GGInnerDiagOn Bs L ∧
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSL (n + 1) 2 f ∧ p ∣ 2 ^ f - 1 ∧
    3 ≤ n ∧ GGNbr p B x D J y K

section Facts

theorem GGTypeALocalCfg.prime {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G} (hL : GGTypeALocalCfg p B Bs x L D J n f y K) : p.Prime := by
  obtain ⟨⟨hI, -, -⟩, -, -, -, -, -⟩ := hL
  exact hI.2.2.2.2.2.1.1

theorem GGTypeALocalCfg.ne_two {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G} (hL : GGTypeALocalCfg p B Bs x L D J n f y K) : p ≠ 2 := by
  obtain ⟨⟨hI, -, -⟩, -, -, -, -, -⟩ := hL
  exact hI.2.2.2.2.2.1.2.1

theorem GGTypeALocalCfg.isElemAbelian {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G} (hL : GGTypeALocalCfg p B Bs x L D J n f y K) :
    IsElemAbelian p Bs := by
  obtain ⟨⟨-, hBs, -⟩, -, -, -, -, -⟩ := hL
  exact hBs.2.1

theorem GGTypeALocalCfg.bs_centralizer {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G} (hL : GGTypeALocalCfg p B Bs x L D J n f y K) :
    ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := by
  obtain ⟨⟨-, hBs, -⟩, -, -, -, -, -⟩ := hL
  exact hBs.2.2.2

theorem GGTypeALocalCfg.exponent {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G} (hL : GGTypeALocalCfg p B Bs x L D J n f y K) :
    ∀ b ∈ Bs, b ^ p = 1 := by
  obtain ⟨⟨-, hBs, -⟩, -, -, -, -, -⟩ := hL
  exact hBs.2.1.2

theorem GGTypeALocalCfg.x_mem {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G} (hL : GGTypeALocalCfg p B Bs x L D J n f y K) : x ∈ Bs := by
  obtain ⟨⟨hI, hBs, -⟩, -, -, -, -, -⟩ := hL
  exact hBs.1 hI.2.2.2.2.2.2.1.2.1

theorem GGTypeALocalCfg.y_mem {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G} (hL : GGTypeALocalCfg p B Bs x L D J n f y K) : y ∈ Bs := by
  obtain ⟨⟨-, hBs, -⟩, -, -, -, -, hnbr⟩ := hL
  exact hBs.1 hnbr.1.2.1

theorem GGTypeALocalCfg.nbr {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G} (hL : GGTypeALocalCfg p B Bs x L D J n f y K) :
    GGNbr p B x D J y K := by
  obtain ⟨-, -, -, -, -, hnbr⟩ := hL
  exact hnbr

theorem GGTypeALocalCfg.dvd_two_pow_sub_one {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G} (hL : GGTypeALocalCfg p B Bs x L D J n f y K) :
    p ∣ 2 ^ f - 1 := by
  obtain ⟨-, -, -, hpq, -, -⟩ := hL
  exact hpq

theorem GGTypeALocalCfg.three_le {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G} (hL : GGTypeALocalCfg p B Bs x L D J n f y K) : 3 ≤ n := by
  obtain ⟨-, -, -, -, hn, -⟩ := hL
  exact hn

theorem GGTypeALocalCfg.one_le_f {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G} (hL : GGTypeALocalCfg p B Bs x L D J n f y K) : 1 ≤ f := by
  obtain ⟨-, -, hmod, -, -, -⟩ := hL
  exact hmod.1.2.1

theorem GGTypeALocalCfg.two_eq_zero {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G} (hL : GGTypeALocalCfg p B Bs x L D J n f y K) :
    (2 : GaloisField 2 f) = 0 :=
  two_eq_zero_of_card (GaloisField.card 2 f (by have := hL.one_le_f; omega)) hL.one_le_f

theorem GGTypeALocalCfg.dvd_natCard_units {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G} (hL : GGTypeALocalCfg p B Bs x L D J n f y K) :
    p ∣ Nat.card (GaloisField 2 f)ˣ := by
  have hf : 1 ≤ f := hL.one_le_f
  have hpq : p ∣ 2 ^ f - 1 := hL.dvd_two_pow_sub_one
  rw [Nat.card_units, GaloisField.card 2 f (by omega)]
  exact hpq

theorem GGTypeALocalCfg.x_comm_of_mem_L {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G} (hL : GGTypeALocalCfg p B Bs x L D J n f y K) :
    ∀ l ∈ L, x * l = l * x := by
  obtain ⟨⟨hI, -, -⟩, -, -, -, -, -⟩ := hL
  intro l hl
  exact (Subgroup.mem_centralizer_singleton_iff.mp
    (hI.2.2.2.2.2.2.1.2.2.2.1.1 hl)).symm

theorem GGTypeALocalCfg.mem_zpowers_x_of_comm_L {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G} (hL : GGTypeALocalCfg p B Bs x L D J n f y K) :
    ∀ g ∈ Bs, (∀ l ∈ L, g * l = l * g) → g ∈ Subgroup.zpowers x := by
  obtain ⟨⟨hI, hBs, -⟩, -, -, -, -, -⟩ := hL
  have hp : p.Prime := hI.2.2.2.2.2.1.1
  have hSstar := hI.2.2.2.2.2.2.1
  have hxne : x ≠ 1 := hSstar.2.2.1
  have hxBs : x ∈ Bs := hBs.1 hSstar.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hSstar.2.2.2.1.1
  have hxpow : x ^ p = 1 := hBs.2.1.2 x hxBs
  have hxord : orderOf x = p := by
    have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hxpow hxne
  intro g hg hgc
  let S : Subgroup G := Bs ⊓ Subgroup.centralizer (L : Set G)
  have hxS : x ∈ S := ⟨hxBs, Subgroup.mem_centralizer_iff.mpr (fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hLx hl))⟩
  have hgS : g ∈ S := ⟨hg, Subgroup.mem_centralizer_iff.mpr (fun l hl =>
    (hgc l hl).symm)⟩
  have hSp : IsPGroup p ↥S := fun s => ⟨1, by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one, pow_one]
    exact hBs.2.1.2 (s : G) s.2.1⟩
  have hScyc : IsCyclic ↥S := hSstar.2.2.2.2 S inf_le_right hSp
  obtain ⟨s, hs⟩ := hScyc.exists_generator
  have hmap : (Subgroup.zpowers s).map S.subtype = Subgroup.zpowers (s : G) :=
    MonoidHom.map_zpowers S.subtype s
  have hSeq : S = Subgroup.zpowers (s : G) := by
    apply le_antisymm
    · intro z hz
      have hz' : z ∈ (Subgroup.zpowers s).map S.subtype :=
        ⟨⟨z, hz⟩, hs ⟨z, hz⟩, rfl⟩
      rwa [hmap] at hz'
    · rw [Subgroup.zpowers_le]
      exact s.2
  have hs_pow : s ^ p = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    exact hBs.2.1.2 (s : G) s.2.1
  have hsord_dvd : orderOf s ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hs_pow
  have hsord : orderOf s = p := by
    rcases (Nat.dvd_prime hp).mp hsord_dvd with h1 | hp'
    · exfalso
      have hs1 : s = 1 := orderOf_eq_one_iff.mp h1
      have hxmem : (⟨x, hxS⟩ : S) ∈ Subgroup.zpowers s := hs ⟨x, hxS⟩
      rw [hs1] at hxmem
      have hxe : (⟨x, hxS⟩ : S) = 1 := by simpa using hxmem
      exact hxne (Subtype.ext_iff.mp hxe)
    · exact hp'
  have hcardS : Nat.card S = p := by
    have hord : orderOf (s : G) = orderOf s :=
      orderOf_injective S.subtype Subtype.coe_injective s
    rw [hSeq, Nat.card_zpowers, hord, hsord]
  have hcardx : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, hxord]
  have hzxle : Subgroup.zpowers x ≤ S := Subgroup.zpowers_le.mpr hxS
  have heq : Subgroup.zpowers x = S :=
    Subgroup.eq_of_le_of_card_ge hzxle (by rw [hcardS, hcardx])
  rw [heq]
  exact hgS

theorem GGTypeALocalCfg.not_y_comm_L {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G} (hL : GGTypeALocalCfg p B Bs x L D J n f y K) :
    ¬ ∀ l ∈ L, y * l = l * y := by
  intro hcomm
  have hp : p.Prime := hL.prime
  have hyzx : y ∈ Subgroup.zpowers x :=
    hL.mem_zpowers_x_of_comm_L y hL.y_mem hcomm
  have hDle : D ≤ Subgroup.zpowers x := by
    rw [hL.nbr.2.1, Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact Subgroup.mem_zpowers _
    · exact hyzx
  have hcardD : Nat.card D = p ^ 2 := hL.1.2.2.1.2.2.1
  have hxne : x ≠ 1 := hL.1.1.2.2.2.2.2.2.1.2.2.1
  have hxpow : x ^ p = 1 := hL.exponent x hL.x_mem
  have hxord : orderOf x = p := by
    have : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hxpow hxne
  have hcardx : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, hxord]
  have hle : Nat.card D ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hDle
  rw [hcardD, hcardx] at hle
  nlinarith [hp.two_le]

theorem GGTypeALocalCfg.exists_lift_L {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G} (hL : GGTypeALocalCfg p B Bs x L D J n f y K) :
    1 ≤ f ∧ ∃ φ₁ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ₁.range = L ∧
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) := by
  have hp : p.Prime := hL.prime
  have hf1 : 1 ≤ f := hL.one_le_f
  have hn3 : 3 ≤ n := hL.three_le
  have hpq : p ∣ 2 ^ f - 1 := hL.dvd_two_pow_sub_one
  have hf : 2 ≤ f := by
    by_contra hlt
    have hf' : f = 1 := by omega
    rw [hf'] at hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp hpq)
  have hperf : commutator L = ⊤ := hL.1.1.2.2.2.2.2.2.2.1.1
  exact ⟨hf1,
    exists_slLift_of_classicalModel (by omega) hf (by omega) hperf hL.2.2.1⟩

theorem GGTypeALocalCfg.card_bstar_ge_three {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {f : ℕ} {y : G} {K : Subgroup G}
    (hL : GGTypeALocalCfg p B Bs x L D J 3 f y K) :
    p ^ ((3 + 1) / p + 3) ≤ Nat.card Bs := by
  have hcfg : GGConfig p B Bs x L D J := hL.1
  have hp : p.Prime := hL.prime
  have hp2 : p ≠ 2 := hL.ne_two
  have hp3 : 3 ≤ p := by have h2 := hp.two_le; omega
  have hf1 : 1 ≤ f := hL.one_le_f
  have hr4 : 4 ≤ LargeEvenTwoLocalRank p G := hcfg.1.2.2.2.2.2.1.2.2.2
  have hBcard : Nat.card B = p ^ LargeEvenTwoLocalRank p G :=
    hcfg.1.2.2.2.2.2.2.1.1.2.1
  have hBBs : Nat.card B ≤ Nat.card Bs := Subgroup.card_le_of_le hcfg.2.1.1
  obtain ⟨-, φ₁, hφL, hker⟩ := hL.exists_lift_L
  have hpq : p ∣ 2 ^ f - 1 := hL.dvd_two_pow_sub_one
  have hpK : p ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [GaloisField.card 2 f (by omega)]
    exact hpq
  have hr : 3 - 1 ≤ LargeEvenTwoLocalRank p G :=
    RootPlaneA.sub_one_le_twoLocalRank (F := GaloisField 2 f) hp hpK (by omega) hker
  have hdvd : ¬ p ∣ 3 + 1 := by
    intro h
    have h2 : p ∣ 2 := by
      have h4 : p ∣ 2 * 2 := by simpa using h
      rcases (Nat.Prime.dvd_mul hp).mp h4 with h' | h' <;> exact h'
    have hpeq : p = 2 := by
      have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
      have hge : 2 ≤ p := hp.two_le
      omega
    exact hp2 hpeq
  have hrle : (3 + 1) / p + 3 ≤ LargeEvenTwoLocalRank p G :=
    succ_div_add_three_le_of_not_dvd (by omega) hp3 hdvd hr4 hr
  exact (Nat.pow_le_pow_right hp.pos hrle).trans (hBcard.symm.trans_le hBBs)

end Facts

section Certs

theorem GGTypeALocalCfg.exists_diagLift_L {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G}
    (hMp : GGInnerDiagMpInput)
    (hL : GGTypeALocalCfg p B Bs x L D J n f y K)
    (hbig : p ^ ((n + 1) / p + 3) ≤ Nat.card Bs) :
    ∃ φ : SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f) →* G, φ.range = L ∧
      φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin (n + 1)) (GaloisField 2 f)) ∧
      ∀ b ∈ Bs, GGActsDiag φ b := by
  have hn3 : 3 ≤ n := hL.three_le
  obtain ⟨hf, φ₀, hrange, hker⟩ := hL.exists_lift_L
  have hA := exists_mem_ggInducedPairs_of_innerDiagOn hMp (n := n) (f := f) (by omega)
    hL.2.2.1.1 hL.2.1 hker hrange
  exact exists_lift_actsDiag_of_bstar hL.prime hL.ne_two hf hL.dvd_two_pow_sub_one
    hL.isElemAbelian hL.1.bstar_inf_centralizer_L hbig hker hrange hA

theorem GGTypeALocalCfg.bstar_inf_centralizer_J_le {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {n f : ℕ} {y : G} {K : Subgroup G}
    (hMp : GGInnerDiagMpInput)
    (hL : GGTypeALocalCfg p B Bs x L D J n f y K)
    (hbig : p ^ ((n + 1) / p + 3) ≤ Nat.card Bs) :
    Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D := by
  obtain ⟨φ, hrange, hker, hdiag⟩ :=
    GGTypeALocalCfg.exists_diagLift_L hMp hL hbig
  have hxB : x ∈ Bs := hL.x_mem
  have hyB : y ∈ Bs := hL.y_mem
  obtain ⟨dx, hdx⟩ := hdiag x hxB
  obtain ⟨dy, hdy⟩ := hdiag y hyB
  have hb : ∀ k : Fin 2, (![x, y] k, InnerDiagA.diagGL (![dx, dy] k)) ∈
      LinFusion.ggInducedPairs φ := by
    intro k
    fin_cases k
    · exact ggActsVec_iff_mem_ggInducedPairs.1 hdx
    · exact ggActsVec_iff_mem_ggInducedPairs.1 hdy
  have hrng : Set.range ![x, y] = {x, y} := by
    ext g
    simp [Fin.exists_fin_two, eq_comm]
    tauto
  have hDc : Subgroup.centralizer (D : Set G) = Subgroup.centralizer (Set.range ![x, y]) := by
    rw [hL.nbr.2.1, Subgroup.centralizer_closure, hrng]
  have hJc : IsComponentOf J (φ.range ⊓ Subgroup.centralizer (Set.range ![x, y])) := by
    rw [hrange, ← hDc]
    exact hL.1.2.2.1.2.2.2.2.2.1
  obtain ⟨i, hI, -, hJi⟩ := (LinSemisimple.isComponentOf_iff_exists_eq_map_blockSpecialLinear
    hker hb).1 hJc
  obtain ⟨T, hT1, hT2, hTJ, hBT⟩ := exists_twoSubgroup_le_map_blockSpecialLinear hker
    (fun b hb' => hdiag b (hL.1.2.1.1 hb')) hI
  exact ggStdSubBstarCentralizer_of_twoSubgroup hL.1 ⟨T, hT1, hT2, hJi ▸ hTJ, hBT⟩

end Certs

theorem ggF4JBx_exists_lift_L_lowerBlock {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {f : ℕ} {y : G} {K : Subgroup G}
    (hMp : GGInnerDiagMpInput)
    (hL : GGTypeALocalCfg p B Bs x L D J 3 f y K) :
    ∃ φ₁ : SpecialLinearGroup (Fin 4) (GaloisField 2 f) →* G, φ₁.range = L ∧
      φ₁.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 4) (GaloisField 2 f)) ∧
      (∀ b ∈ Bs, GGActsDiag φ₁ b) ∧
      (φ₁.comp (slLowerBlockHom 3 (GaloisField 2 f))).range = J := by
  have hbig : p ^ ((3 + 1) / p + 3) ≤ Nat.card Bs := hL.card_bstar_ge_three
  obtain ⟨φ, hrange, hker, hdiag⟩ :=
    GGTypeALocalCfg.exists_diagLift_L hMp hL hbig
  have hCJ := GGTypeALocalCfg.bstar_inf_centralizer_J_le hMp hL hbig
  have hfull : p ∣ 3 + 1 → p ^ (3 + 1) ≤ Nat.card Bs := by
    intro h
    exact absurd h (by
      intro h4
      have h2 : p ∣ 2 := by
        have h4' : p ∣ 2 * 2 := by simpa using h4
        rcases (Nat.Prime.dvd_mul hL.prime).mp h4' with h' | h' <;> exact h'
      have hpeq : p = 2 := by
        have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
        have hge : 2 ≤ p := hL.prime.two_le
        omega
      exact hL.ne_two hpeq)
  have hD : ∀ r, ∃ g ∈ Bs, ∃ τ : (GaloisField 2 f)ˣ, τ ≠ 1 ∧ GGActsVec φ g (diagAt r τ) :=
    fun r => exists_actsVec_diagAt_of_bstar hL.two_eq_zero hL.prime hL.dvd_natCard_units
      hL.isElemAbelian hL.bs_centralizer hker hdiag
      (by rw [hrange]; exact (hL.1.card_bstar_inf_centralizer_L).le) hfull r
  have hJc : IsComponentOf J (φ.range ⊓ Subgroup.centralizer (D : Set G)) := by
    rw [hrange]
    exact hL.1.2.2.1.2.2.2.2.2.1
  obtain ⟨r, hr⟩ := exists_eq_map_blockSpecialLinear_erase hL.prime hL.isElemAbelian hker hdiag hD
    hL.x_mem hL.y_mem (fun s => hL.x_comm_of_mem_L (φ s) (hrange ▸ ⟨s, rfl⟩))
    (fun h => hL.not_y_comm_L fun l hl => by
      rw [← hrange] at hl
      obtain ⟨s, rfl⟩ := hl
      exact h s)
    hL.nbr.2.1 hJc hCJ
  obtain ⟨φ', hr', hk', hd', hJ'⟩ := exists_lift_lowerBlock_eq hL.two_eq_zero hker hdiag r
  exact ⟨φ', hr'.trans hrange, hk', hd', hJ'.trans hr.symm⟩

end Local

end CFSG.StandardType

end
