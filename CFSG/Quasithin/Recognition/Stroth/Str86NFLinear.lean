module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Recognition.Stroth.Str86Props

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem exists_fixed_mod_subgroup {P Z : Subgroup G} {g : G}
    (hZP : Z ≤ P)
    (hNZ : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Z : Set G))
    (hZc : Z ≤ Subgroup.centralizer (P : Set G))
    (hgP : g ∈ Subgroup.normalizer (P : Set G))
    (hP2 : IsPGroup 2 P) (hg2 : ∃ n : ℕ, orderOf g = 2 ^ n)
    (hPne : P ≠ Z) :
    ∃ x ∈ P, x ∉ Z ∧ ⁅g, x⁆ ∈ Z := by
  classical
  let K : Subgroup ↥P := Z.subgroupOf P
  have hKle : K ≤ Subgroup.center ↥P := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro w
    have hzZ : ((z : ↥P) : G) ∈ Z := hz
    have hcomm := hZc hzZ (w : G) w.2
    exact Subtype.ext (by simpa [mul_comm] using hcomm)
  haveI hKnormal : K.Normal := Subgroup.normal_of_le_center hKle
  have hKne : K ≠ ⊤ := by
    intro htop
    apply hPne
    refine le_antisymm ?_ hZP
    intro p hp
    have : (⟨p, hp⟩ : ↥P) ∈ K := by rw [htop]; exact Subgroup.mem_top _
    exact this
  haveI hquotne : Nontrivial (↥P ⧸ K) := QuotientGroup.nontrivial_iff.mpr hKne
  haveI : MulAction.QuotientAction (Subgroup.normalizer (P : Set G)) K :=
    ⟨fun b a a' h => by
      have hbZ : (b : G) ∈ Subgroup.normalizer (Z : Set G) := hNZ b.2
      have hmem : (((a⁻¹ * a') : ↥P) : G) ∈ Z := h
      have hconj : (b : G) * (((a⁻¹ * a') : ↥P) : G) * (b : G)⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp hbZ _).mp hmem
      show (((b • a)⁻¹ * (b • a') : ↥P) : G) ∈ Z
      change ((b • a : ↥P) : G)⁻¹ * ((b • a' : ↥P) : G) ∈ Z
      have hba : ((b • a : ↥P) : G) = (b : G) * (a : G) * (b : G)⁻¹ := rfl
      have hba' : ((b • a' : ↥P) : G) = (b : G) * (a' : G) * (b : G)⁻¹ := rfl
      rw [hba, hba']
      simpa [mul_assoc] using hconj⟩
  let H : Subgroup G := Subgroup.zpowers g
  have hHP : H ≤ Subgroup.normalizer (P : Set G) := by
    intro h hh
    rw [Subgroup.mem_zpowers_iff] at hh
    obtain ⟨n, rfl⟩ := hh
    exact Subgroup.zpow_mem _ hgP n
  let f : H →* Subgroup.normalizer (P : Set G) := Subgroup.inclusion hHP
  letI : MulAction H (↥P ⧸ K) := MulAction.compHom _ f
  have hH2 : IsPGroup 2 H := by
    obtain ⟨n, hn⟩ := hg2
    exact IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have hquot2 : IsPGroup 2 (↥P ⧸ K) := hP2.to_quotient K
  have hdvd : 2 ∣ Nat.card (↥P ⧸ K) := by
    obtain ⟨n, hn⟩ := hquot2.exists_card_eq
    rcases n with _ | n
    · exfalso
      have hsub : Subsingleton (↥P ⧸ K) := (Nat.card_eq_one_iff_unique.mp (by simpa using hn)).1
      exact (not_subsingleton (↥P ⧸ K)) hsub
    · rw [hn]
      exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  have h1 : (1 : ↥P ⧸ K) ∈ MulAction.fixedPoints H (↥P ⧸ K) := by
    rw [MulAction.mem_fixedPoints]
    intro h
    rw [MulAction.compHom_smul_def]
    rw [← QuotientGroup.mk_one, MulAction.Quotient.smul_mk, smul_one]
  obtain ⟨q, hq, hq1⟩ := hH2.exists_fixed_point_of_prime_dvd_card_of_fixed_point _ hdvd h1
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  have hxK : x ∉ K := by
    intro hx
    apply hq1
    exact ((QuotientGroup.eq_one_iff x).mpr hx).symm
  refine ⟨x, x.2, fun h => hxK h, ?_⟩
  have hfix := MulAction.mem_fixedPoints.mp hq (⟨g, Subgroup.mem_zpowers g⟩ : H)
  rw [MulAction.compHom_smul_def] at hfix
  rw [MulAction.Quotient.smul_mk] at hfix
  have hmem : ((f ⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.normalizer (P : Set G)) • x) / x ∈ K :=
    QuotientGroup.eq_iff_div_mem.mp hfix
  have hmemZ : ((((f ⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.normalizer (P : Set G)) • x) / x :
      ↥P) : G) ∈ Z := hmem
  have hfg : ((f ⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.normalizer (P : Set G)) : G) = g := rfl
  have hsmul : (((f ⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.normalizer (P : Set G)) • x :
      ↥P) : G) = g * (x : G) * g⁻¹ := by
    change ((f ⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.normalizer (P : Set G)) : G) *
      (x : G) * ((f ⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.normalizer (P : Set G)) : G)⁻¹ =
        g * (x : G) * g⁻¹
    rw [hfg]
  have hmemZ' : (((f ⟨g, Subgroup.mem_zpowers g⟩ : Subgroup.normalizer (P : Set G)) • x :
      ↥P) : G) * (x : G)⁻¹ ∈ Z := by
    simpa [div_eq_mul_inv] using hmemZ
  rw [hsmul] at hmemZ'
  simpa [commutatorElement_def, div_eq_mul_inv] using hmemZ'

private def fixedModSubgroup (P Z : Subgroup G) (g : G)
    (hZc : Z ≤ Subgroup.centralizer (P : Set G)) : Subgroup G where
  carrier := {x | x ∈ P ∧ ⁅g, x⁆ ∈ Z}
  one_mem' := ⟨P.one_mem, by simp⟩
  mul_mem' := by
    rintro x y ⟨hxP, hxZ⟩ ⟨hyP, hyZ⟩
    refine ⟨P.mul_mem hxP hyP, ?_⟩
    rw [commutatorElement_mul_right_eq_mul_conj]
    have hconj : x * ⁅g, y⁆ * x⁻¹ ∈ Z := by
      have hcomm : x * ⁅g, y⁆ = ⁅g, y⁆ * x :=
        Subgroup.mem_centralizer_iff.mp (hZc hyZ) x hxP
      rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
      exact hyZ
    rw [show ⁅g, x⁆ * x * ⁅g, y⁆ * x⁻¹ = ⁅g, x⁆ * (x * ⁅g, y⁆ * x⁻¹) by group]
    exact Z.mul_mem hxZ hconj
  inv_mem' := by
    rintro x ⟨hxP, hxZ⟩
    refine ⟨P.inv_mem hxP, ?_⟩
    rw [commutatorElement_inv_right]
    rw [show ⁅x, g⁆ = ⁅g, x⁆⁻¹ from (commutatorElement_inv (g₁ := g) (g₂ := x)).symm]
    have hcomm : x * ⁅g, x⁆⁻¹ = ⁅g, x⁆⁻¹ * x :=
      Subgroup.mem_centralizer_iff.mp (hZc (Z.inv_mem hxZ)) x hxP
    have hcalc : x⁻¹ * ⁅g, x⁆⁻¹ * x = ⁅g, x⁆⁻¹ := by
      calc
        x⁻¹ * ⁅g, x⁆⁻¹ * x = x⁻¹ * (⁅g, x⁆⁻¹ * x) := by group
        _ = x⁻¹ * (x * ⁅g, x⁆⁻¹) := by rw [hcomm]
        _ = ⁅g, x⁆⁻¹ := by group
    rw [hcalc]
    exact Z.inv_mem hxZ

private theorem le_fixedModSubgroup {P Z : Subgroup G} {g : G}
    (hZP : Z ≤ P) (hNZ : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Z : Set G))
    (hgP : g ∈ Subgroup.normalizer (P : Set G))
    (hZc : Z ≤ Subgroup.centralizer (P : Set G)) :
    Z ≤ fixedModSubgroup P Z g hZc := by
  intro z hz
  refine ⟨hZP hz, ?_⟩
  have hgz : g * z * g⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp (hNZ hgP) z).mp hz
  rw [commutatorElement_def]
  exact Z.mul_mem hgz (Z.inv_mem hz)

private theorem commutator_conj_mem {P Z : Subgroup G} {g l x : G}
    (hPZ : P ≤ Subgroup.normalizer (Z : Set G))
    (hlP : l ∈ Subgroup.normalizer (P : Set G))
    (hlZ : l ∈ Subgroup.normalizer (Z : Set G))
    (hxP : x ∈ P)
    (hgxZ : ⁅g, x⁆ ∈ Z)
    (hglP : ⁅g, l⁆ ∈ P)
    (hder : ⁅P, P⁆ ≤ Z) :
    ⁅g, l * x * l⁻¹⁆ ∈ Z := by
  have hyP : l * x * l⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hlP x).mp hxP
  have huZ : g * l * g⁻¹ ∈ Subgroup.normalizer (Z : Set G) := by
    have hgl_eq : g * l * g⁻¹ = ⁅g, l⁆ * l := by
      rw [commutatorElement_def]
      group
    rw [hgl_eq]
    exact Subgroup.mul_mem _ (hPZ hglP) hlZ
  have huzZ : (g * l * g⁻¹) * ⁅g, x⁆ * (g * l * g⁻¹)⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp huZ ⁅g, x⁆).mp hgxZ
  have hqyZ : ⁅⁅g, l⁆, l * x * l⁻¹⁆ ∈ Z :=
    hder (Subgroup.commutator_mem_commutator hglP hyP)
  have hkey : ⁅g, l * x * l⁻¹⁆ =
      ((g * l * g⁻¹) * ⁅g, x⁆ * (g * l * g⁻¹)⁻¹) * ⁅⁅g, l⁆, l * x * l⁻¹⁆ := by
    rw [commutatorElement_def]
    group
  rw [hkey]
  exact Z.mul_mem huzZ hqyZ

private theorem fixedModSubgroup_le_normalizer {P Z L : Subgroup G} {g : G}
    (hZP : Z ≤ P)
    (hNZ : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Z : Set G))
    (hZc : Z ≤ Subgroup.centralizer (P : Set G))
    (hLP : L ≤ Subgroup.normalizer (P : Set G))
    (hPZ : P ≤ Subgroup.normalizer (Z : Set G))
    (hgP : g ∈ Subgroup.normalizer (P : Set G))
    (hcomm : ∀ l ∈ L, ⁅g, l⁆ ∈ P)
    (hder : ⁅P, P⁆ ≤ Z) :
    L ≤ Subgroup.normalizer (fixedModSubgroup P Z g hZc : Set G) := by
  have hconj : ∀ l ∈ L, ∀ x ∈ fixedModSubgroup P Z g hZc,
      l * x * l⁻¹ ∈ fixedModSubgroup P Z g hZc := by
    intro l hl x hx
    have hlP : l ∈ Subgroup.normalizer (P : Set G) := hLP hl
    have hlZ : l ∈ Subgroup.normalizer (Z : Set G) := hNZ hlP
    refine ⟨(Subgroup.mem_normalizer_iff.mp hlP x).mp hx.1, ?_⟩
    exact commutator_conj_mem hPZ hlP hlZ hx.1 hx.2 (hcomm l hl) hder
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨hconj l hl x, fun hx => by
    have := hconj l⁻¹ (L.inv_mem hl) (l * x * l⁻¹) hx
    simpa [mul_assoc] using this⟩

private theorem fixedModSubgroup_bot_le_normalizer {P Z L : Subgroup G} {g : G}
    (hZc : Z ≤ Subgroup.centralizer (P : Set G))
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G))
    (hLP : L ≤ Subgroup.normalizer (P : Set G))
    (hcomm : ∀ l ∈ L, ⁅g, l⁆ ∈ P) :
    L ≤ Subgroup.normalizer (fixedModSubgroup Z ⊥ g bot_le : Set G) := by
  have hconj : ∀ l ∈ L, ∀ x ∈ fixedModSubgroup Z ⊥ g bot_le,
      l * x * l⁻¹ ∈ fixedModSubgroup Z ⊥ g bot_le := by
    intro l hl x hx
    refine ⟨(Subgroup.mem_normalizer_iff.mp (hLZ hl) x).mp hx.1, ?_⟩
    have hgx : g * x * g⁻¹ = x := by
      have h1 : ⁅g, x⁆ = 1 := by simpa using hx.2
      rw [commutatorElement_def] at h1
      calc g * x * g⁻¹ = (g * x * g⁻¹ * x⁻¹) * x := by group
        _ = x := by rw [h1, one_mul]
    have hqP : ⁅g, l⁆ ∈ P := hcomm l hl
    have hlZ : l ∈ Subgroup.normalizer (Z : Set G) := hLZ hl
    have hyZ : l * x * l⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hlZ x).mp hx.1
    have hcent : ⁅g, l⁆ * (l * x * l⁻¹) = (l * x * l⁻¹) * ⁅g, l⁆ :=
      Subgroup.mem_centralizer_iff.mp (hZc hyZ) ⁅g, l⁆ hqP
    have hkey : g * (l * x * l⁻¹) * g⁻¹ = l * x * l⁻¹ := by
      have hgl : g * l * g⁻¹ = ⁅g, l⁆ * l := by
        rw [commutatorElement_def]
        group
      calc
        g * (l * x * l⁻¹) * g⁻¹
            = (g * l * g⁻¹) * (g * x * g⁻¹) * (g * l * g⁻¹)⁻¹ := by group
        _ = (⁅g, l⁆ * l) * x * (⁅g, l⁆ * l)⁻¹ := by rw [hgl, hgx]
        _ = ⁅g, l⁆ * (l * x * l⁻¹) * ⁅g, l⁆⁻¹ := by group
        _ = l * x * l⁻¹ := by
          rw [hcent]
          group
    rw [commutatorElement_def]
    rw [Subgroup.mem_bot]
    calc g * (l * x * l⁻¹) * g⁻¹ * (l * x * l⁻¹)⁻¹
        = (l * x * l⁻¹) * (l * x * l⁻¹)⁻¹ := by rw [hkey]
      _ = 1 := by group
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact ⟨hconj l hl x, fun hx => by
    have := hconj l⁻¹ (L.inv_mem hl) (l * x * l⁻¹) hx
    simpa [mul_assoc] using this⟩

theorem str86NF_linear {L1 L2 S : Subgroup G} {k : ℕ} (hk : 2 ≤ k)
    (hZ2 : Nat.card (Z2 L1 L2 S) = (2 ^ k) ^ 4)
    (hQ2' : ⁅Q2 L1 L2 S, Q2 L1 L2 S⁆ ≤ Z2 L1 L2 S)
    (hQ2irr : ∀ N : Subgroup G, Z2 L1 L2 S ≤ N → N ≤ Q2 L1 L2 S →
      L2 ≤ Subgroup.normalizer (N : Set G) → N = Z2 L1 L2 S ∨ N = Q2 L1 L2 S)
    (hZ2irr : ∀ N : Subgroup G, ⊥ < N → N ≤ Z2 L1 L2 S →
      L2 ≤ Subgroup.normalizer (N : Set G) → N = Z2 L1 L2 S) :
    Str86NF L2 (Q2 L1 L2 S) (Z2 L1 L2 S) := by
  classical
  set P : Subgroup G := Q2 L1 L2 S with hP
  set Z : Subgroup G := Z2 L1 L2 S with hZ
  have hZP : Z ≤ P := by
    rw [hP, hZ]
    exact A4.omegaOneCenterOf_le (Q2 L1 L2 S)
  have hNZ : Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Z : Set G) := by
    rw [hP, hZ]
    exact A4.normalizer_le_normalizer_omegaOneCenterOf (Q2 L1 L2 S)
  have hZc : Z ≤ Subgroup.centralizer (P : Set G) := by
    rw [hP, hZ]
    exact (A4.omegaOneCenterOf_le_centerOf (Q2 L1 L2 S)).trans
      (A4.centerOf_le_centralizer (Q2 L1 L2 S))
  have hP2 : IsPGroup 2 P := by
    rw [hP]
    exact pCoreOf_isPGroup 2 (P2 L1 L2 S)
  have hQ2P2 : Q2 L1 L2 S ≤ P2 L1 L2 S := pCoreOf_le 2 (P2 L1 L2 S)
  have hP2N : P2 L1 L2 S ≤ Subgroup.normalizer (P : Set G) := by
    rw [hP]
    exact le_normalizer_pCoreOf 2 (P2 L1 L2 S)
  have hPNZ : P ≤ Subgroup.normalizer (Z : Set G) := by
    rw [hP, hZ]
    exact hQ2P2.trans (hP2N.trans hNZ)
  have hL2N : L2 ≤ Subgroup.normalizer (P : Set G) :=
    (le_sup_left : L2 ≤ L2 ⊔ bigB L1 L2 S).trans hP2N
  have hL2Z : L2 ≤ Subgroup.normalizer (Z : Set G) := hL2N.trans hNZ
  intro g hg2 hgL hgN hcomm
  constructor
  · intro x hxP
    by_cases hPne : P = Z
    · have hxZ : x ∈ Z := hPne ▸ hxP
      have hgZ : g ∈ Subgroup.normalizer (Z : Set G) := hNZ hgN
      have h1 : g * x * g⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp hgZ x).mp hxZ
      have h2 : x⁻¹ ∈ Z := Z.inv_mem hxZ
      have h3 : g * x * g⁻¹ * x⁻¹ ∈ Z := Z.mul_mem h1 h2
      exact h3
    · obtain ⟨x0, hx0P, hx0Z, hx0comm⟩ :=
        exists_fixed_mod_subgroup hZP hNZ hZc hgN hP2 hg2 hPne
      let C : Subgroup G := fixedModSubgroup P Z g hZc
      have hZC : Z ≤ C := le_fixedModSubgroup hZP hNZ hgN hZc
      have hCne : C ≠ Z := by
        intro hCeq
        have hx0C : x0 ∈ C := ⟨hx0P, hx0comm⟩
        rw [hCeq] at hx0C
        exact hx0Z hx0C
      have hCN : L2 ≤ Subgroup.normalizer (C : Set G) :=
        fixedModSubgroup_le_normalizer hZP hNZ hZc hL2N hPNZ hgN
          (fun l hl => by simpa [commutatorElement_def, ← hP] using hcomm l hl)
          (by rw [hP, hZ]; exact hQ2')
      have hCQ : C ≤ P := fun y hy => hy.1
      rcases hQ2irr C hZC hCQ hCN with hCeq | hCeq
      · exact absurd hCeq hCne
      · have hxC : x ∈ C := by
          rw [hCeq]
          exact hxP
        have hxZ := hxC.2
        rwa [commutatorElement_def] at hxZ
  · intro z hzZ
    have hZcard : 1 < Nat.card Z := by
      rw [hZ, hZ2]
      have hbase : 1 < 2 ^ k := by
        calc 1 < 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
      exact one_lt_pow' hbase (by norm_num)
    have hZne : Z ≠ ⊥ := by
      intro hbot
      have h1 : Nat.card Z = 1 := by rw [hbot, Subgroup.card_bot]
      omega
    have hZ2P : IsPGroup 2 Z := by
      rw [hZ]
      refine IsPGroup.of_card (n := k * 4) ?_
      rw [hZ2, ← pow_mul]
    have hbotNZ : Subgroup.normalizer (Z : Set G) ≤
        Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := by
      intro h _
      rw [Subgroup.mem_normalizer_iff]
      intro x
      simp
    have hbotZc : (⊥ : Subgroup G) ≤ Subgroup.centralizer (Z : Set G) := bot_le
    obtain ⟨z0, hz0Z, hz0bot, hz0comm⟩ :=
      exists_fixed_mod_subgroup (P := Z) (Z := ⊥) (g := g) bot_le hbotNZ hbotZc
        (hNZ hgN) hZ2P hg2 hZne
    let Cz : Subgroup G := fixedModSubgroup Z ⊥ g hbotZc
    have hbotCz : ⊥ < Cz := by
      rw [bot_lt_iff_ne_bot]
      intro hCzbot
      have hz0Cz : z0 ∈ Cz := ⟨hz0Z, hz0comm⟩
      rw [hCzbot] at hz0Cz
      exact hz0bot (Subgroup.mem_bot.mp hz0Cz)
    have hCzZ : Cz ≤ Z := fun x hx => hx.1
    have hCzN : L2 ≤ Subgroup.normalizer (Cz : Set G) :=
      fixedModSubgroup_bot_le_normalizer hZc hL2Z hL2N
        (fun l hl => by simpa [commutatorElement_def, ← hP] using hcomm l hl)
    have hCzEq : Cz = Z := hZ2irr Cz hbotCz hCzZ hCzN
    have hzCz : z ∈ Cz := by
      rw [hCzEq]
      exact hzZ
    have hcomm1 : ⁅g, z⁆ = 1 := by simpa using hzCz.2
    rw [commutatorElement_def] at hcomm1
    calc
      g * z = (g * z * g⁻¹ * z⁻¹) * (z * g) := by group
      _ = z * g := by rw [hcomm1, one_mul]

end CFSG.Quasithin.Stroth

end
